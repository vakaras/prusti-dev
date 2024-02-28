use super::HeapEncoder;
use crate::encoder::errors::{SpannedEncodingError, SpannedEncodingResult};
use vir_crate::{
    common::{
        builtin_constants::MEMORY_BLOCK_PREDICATE_NAME,
        expression::{BinaryOperationHelpers, ExpressionIterator, UnaryOperationHelpers},
    },
    low::{self as vir_low, expression::visitors::ExpressionFallibleFolder},
};

impl<'p, 'v: 'p, 'tcx: 'v> HeapEncoder<'p, 'v, 'tcx> {
    pub(super) fn purify_snap_function_calls_in_expressions(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        expressions: Vec<vir_low::Expression>,
        expression_evaluation_state_label: Option<String>,
        initial_path_condition: Vec<vir_low::Expression>,
        position: vir_low::Position,
        is_in_frame_check: bool,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
        let mut purified_expressions = Vec::new();
        for expression in expressions {
            let purified_expression = self.purify_snap_function_calls_in_expression(
                statements,
                expression,
                expression_evaluation_state_label.clone(),
                initial_path_condition.clone(),
                position,
                is_in_frame_check,
            )?;
            purified_expressions.push(purified_expression);
        }
        Ok(purified_expressions)
    }

    /// If `is_in_frame_check` is true, then variables bound by quantifiers are skolemized out.
    pub(super) fn purify_snap_function_calls_in_expression(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        expression: vir_low::Expression,
        expression_evaluation_state_label: Option<String>,
        initial_path_condition: Vec<vir_low::Expression>,
        position: vir_low::Position,
        is_in_frame_check: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let mut purifier = Purifier {
            expression_evaluation_state_label,
            heap_encoder: self,
            statements,
            path_condition: initial_path_condition,
            position,
            is_in_frame_check,
            inside_trigger: false,
        };
        purifier.fallible_fold_expression(expression)
    }
}

struct Purifier<'e, 'p, 'v: 'p, 'tcx: 'v> {
    /// The state in which we should evaluate the heap expressions. If `None`,
    /// takes the latest heap._
    expression_evaluation_state_label: Option<String>,
    heap_encoder: &'e mut HeapEncoder<'p, 'v, 'tcx>,
    statements: &'e mut Vec<vir_low::Statement>,
    path_condition: Vec<vir_low::Expression>,
    position: vir_low::Position,
    is_in_frame_check: bool,
    inside_trigger: bool,
}

impl<'e, 'p, 'v: 'p, 'tcx: 'v> Purifier<'e, 'p, 'v, 'tcx> {
    fn current_heap_version(
        &mut self,
        predicate_name: &str,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let heap_version = if let Some(expression_evaluation_state_label) =
            &self.expression_evaluation_state_label
        {
            self.heap_encoder
                .get_heap_version_at_label(predicate_name, expression_evaluation_state_label)?
        } else {
            self.heap_encoder
                .get_current_heap_version_for(predicate_name)?
        };
        Ok(heap_version)
    }

    fn snap_function_range_call(
        &mut self,
        function_name: &str,
        predicate_name: &str,
        mut arguments: Vec<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let heap_version = self.current_heap_version(predicate_name)?;
        arguments.push(heap_version);
        // FIXME: Generate the definitional axiom.
        let heap_function_name = self.heap_encoder.heap_range_function_name(predicate_name);
        let Some(function_decl) = self.heap_encoder.functions.get(function_name) else {
            unreachable!();
        };
        let return_type = function_decl.return_type.clone();
        Ok(vir_low::Expression::domain_function_call(
            "HeapFunctions",
            heap_function_name,
            arguments,
            return_type,
        ))
    }

    fn snap_function_call(
        &mut self,
        predicate_name: &str,
        mut arguments: Vec<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let heap_version = self.current_heap_version(predicate_name)?;
        arguments.push(heap_version);
        let heap_function_name = self.heap_encoder.heap_function_name(predicate_name);
        let return_type = self
            .heap_encoder
            .get_snapshot_type_for_predicate(predicate_name)
            .unwrap();
        Ok(vir_low::Expression::domain_function_call(
            "HeapFunctions",
            heap_function_name,
            arguments,
            return_type,
        ))
    }
}

impl<'e, 'p, 'v: 'p, 'tcx: 'v> ExpressionFallibleFolder for Purifier<'e, 'p, 'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn fallible_fold_func_app_enum(
        &mut self,
        func_app: vir_low::expression::FuncApp,
    ) -> Result<vir_low::Expression, Self::Error> {
        let function = self.heap_encoder.functions[&func_app.function_name];
        assert_eq!(function.parameters.len(), func_app.arguments.len());
        let arguments = func_app
            .arguments
            .clone()
            .into_iter()
            .map(|argument| self.fallible_fold_expression(argument))
            .collect::<Result<Vec<_>, _>>()?;
        let path_condition = self.path_condition.iter().cloned().conjoin();
        let replacements = function.parameters.iter().zip(arguments.iter()).collect();
        let pres = function
            .pres
            .iter()
            .cloned()
            .conjoin()
            .substitute_variables(&replacements);
        let pres = self.fallible_fold_expression(pres)?;
        let assert_precondition = vir_low::Expression::implies(path_condition, pres);
        eprintln!("assert_precondition: {}", assert_precondition);
        if !self.inside_trigger {
            // Do not assert preconditions inside triggers.
            self.heap_encoder.encode_function_precondition_assert(
                self.statements,
                assert_precondition,
                self.position,
                self.expression_evaluation_state_label.clone(),
            )?;
        }
        match function.kind {
            vir_low::FunctionKind::MemoryBlockBytes => {
                self.snap_function_call(MEMORY_BLOCK_PREDICATE_NAME, arguments)
            }
            vir_low::FunctionKind::CallerFor => {
                let inlined_function = function
                    .body
                    .clone()
                    .unwrap()
                    .substitute_variables(&replacements);
                Ok(inlined_function)
            }
            vir_low::FunctionKind::SnapRange => {
                let predicate_name = self
                    .heap_encoder
                    .get_predicate_name_for_function(&func_app.function_name)?;
                self.snap_function_range_call(&func_app.function_name, &predicate_name, arguments)
            }
            vir_low::FunctionKind::Snap => {
                let predicate_name = self
                    .heap_encoder
                    .get_predicate_name_for_function(&func_app.function_name)?;
                let validity_function = {
                    // FIXME: This is a hack, put it into OwnedPredicateInfo instead.
                    match function.posts[0].clone() {
                        vir_low::Expression::DomainFuncApp(domain_func_app) => {
                            assert!(domain_func_app.function_name.starts_with("valid$Snap$"));
                            assert_eq!(domain_func_app.arguments.len(), 1);
                            domain_func_app
                        }
                        _ => unreachable!(),
                    }
                };
                let call = self.snap_function_call(&predicate_name, arguments)?;
                let ensures_validity = vir_low::Expression::domain_function_call(
                    "HeapFunctions",
                    format!("ensures${}", validity_function.function_name),
                    vec![call],
                    func_app.return_type,
                );
                Ok(ensures_validity)
            }
        }
    }

    fn fallible_fold_binary_op(
        &mut self,
        mut binary_op: vir_low::expression::BinaryOp,
    ) -> Result<vir_low::expression::BinaryOp, Self::Error> {
        binary_op.left = self.fallible_fold_expression_boxed(binary_op.left)?;
        if binary_op.op_kind == vir_low::BinaryOpKind::Implies {
            self.path_condition.push((*binary_op.left).clone());
        }
        binary_op.right = self.fallible_fold_expression_boxed(binary_op.right)?;
        if binary_op.op_kind == vir_low::BinaryOpKind::Implies {
            self.path_condition.pop();
        }
        Ok(binary_op)
    }

    fn fallible_fold_conditional(
        &mut self,
        mut conditional: vir_low::expression::Conditional,
    ) -> Result<vir_low::expression::Conditional, Self::Error> {
        conditional.guard = self.fallible_fold_expression_boxed(conditional.guard)?;
        self.path_condition.push((*conditional.guard).clone());
        conditional.then_expr = self.fallible_fold_expression_boxed(conditional.then_expr)?;
        self.path_condition.pop();
        self.path_condition
            .push(vir_low::Expression::not((*conditional.guard).clone()));
        conditional.else_expr = self.fallible_fold_expression_boxed(conditional.else_expr)?;
        self.path_condition.pop();
        Ok(conditional)
    }

    fn fallible_fold_labelled_old_enum(
        &mut self,
        mut labelled_old: vir_low::expression::LabelledOld,
    ) -> Result<vir_low::Expression, Self::Error> {
        std::mem::swap(
            &mut labelled_old.label,
            &mut self.expression_evaluation_state_label,
        );
        let mut labelled_old = self.fallible_fold_labelled_old(labelled_old)?;
        std::mem::swap(
            &mut labelled_old.label,
            &mut self.expression_evaluation_state_label,
        );
        Ok(vir_low::Expression::LabelledOld(labelled_old))
    }

    fn fallible_fold_quantifier_enum(
        &mut self,
        quantifier: vir_low::Quantifier,
    ) -> Result<vir_low::Expression, Self::Error> {
        self.heap_encoder
            .create_quantifier_variables_remap(&quantifier.variables)?;
        let quantifier = self.fallible_fold_quantifier(quantifier)?;
        self.heap_encoder.bound_variable_remap_stack.pop();
        Ok(vir_low::Expression::Quantifier(quantifier))
    }

    fn fallible_fold_variable_decl(
        &mut self,
        variable_decl: vir_low::VariableDecl,
    ) -> Result<vir_low::VariableDecl, Self::Error> {
        if self.is_in_frame_check {
            if let Some(remap) = self
                .heap_encoder
                .bound_variable_remap_stack
                .get(&variable_decl)
            {
                return Ok(remap.clone());
            }
        }
        Ok(variable_decl)
    }

    fn fallible_fold_trigger(
        &mut self,
        mut trigger: vir_low::Trigger,
    ) -> Result<vir_low::Trigger, Self::Error> {
        assert!(!self.inside_trigger);
        self.inside_trigger = true;
        for term in std::mem::take(&mut trigger.terms) {
            let term = self.fallible_fold_expression(term)?;
            trigger.terms.push(term);
        }
        self.inside_trigger = false;
        Ok(trigger)
    }
}
