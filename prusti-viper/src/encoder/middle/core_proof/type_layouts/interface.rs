use crate::encoder::{
    errors::SpannedEncodingResult,
    high::{type_layouts::HighTypeLayoutsEncoderInterface, types::HighTypeEncoderInterface},
    middle::core_proof::{
        lowerer::{Lowerer, DomainsLowererInterface},
        snapshots::{
            IntoBuiltinMethodSnapshot, IntoProcedureSnapshot, IntoSnapshot, SnapshotValuesInterface, SnapshotValidityInterface,
        },
    },
};
use rustc_hash::FxHashSet;
use vir_crate::{
    low as vir_low,
    middle::{self as vir_mid, operations::const_generics::WithConstArguments},
};

#[derive(Default)]
pub(in super::super) struct TypeLayoutsState {
    encoded_size_functions: FxHashSet<String>,
}

pub(in super::super) trait TypeLayoutsInterface {
    fn size_type_mid(&mut self) -> SpannedEncodingResult<vir_mid::Type>;
    fn size_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
    fn size_constant(
        &mut self,
        value: impl Into<vir_mid::expression::ConstantValue>,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_type_size_expression2(
        &mut self,
        ty: &vir_mid::Type,
        generics: &impl WithConstArguments,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    /// The size multiplied by `repetitions`.
    fn encode_type_size_expression_repetitions(
        &mut self,
        ty: &vir_mid::Type,
        generics: &impl WithConstArguments,
        repetitions: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_type_padding_size_expression(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_size_function_call_with_axioms(
        &mut self,
        function_name: String,
        arguments: Vec<vir_low::Expression>,
        position: vir_low::Position,
    )-> SpannedEncodingResult<vir_low::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> TypeLayoutsInterface for Lowerer<'p, 'v, 'tcx> {
    fn size_type_mid(&mut self) -> SpannedEncodingResult<vir_mid::Type> {
        Ok(vir_mid::Type::Int(vir_mid::ty::Int::Usize))
    }
    fn size_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        self.size_type_mid()?.to_snapshot(self)
    }
    fn size_constant(
        &mut self,
        value: impl Into<vir_mid::expression::ConstantValue>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        vir_mid::Expression::constant_no_pos(value.into(), self.size_type_mid()?)
            .to_procedure_snapshot(self)
    }
    fn encode_type_size_expression2(
        &mut self,
        ty: &vir_mid::Type,
        generics: &impl WithConstArguments,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let size_type = self.size_type_mid()?;
        let size = vir_mid::Expression::builtin_func_app_no_pos(
            vir_mid::BuiltinFunc::Size,
            vec![ty.clone()],
            generics.get_const_arguments(),
            size_type,
        );
        size.to_builtin_method_snapshot(self)
    }
    fn encode_type_size_expression_repetitions(
        &mut self,
        ty: &vir_mid::Type,
        generics: &impl WithConstArguments,
        repetitions: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let size = self.encode_type_size_expression2(ty, generics)?;
        let size_type = self.size_type_mid()?;
        self.construct_binary_op_snapshot(
            vir_mid::BinaryOpKind::Mul,
            &size_type,
            &size_type,
            repetitions,
            size,
            position,
        )
    }
    fn encode_type_padding_size_expression(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let mir_type = self.encoder.decode_type_mid(ty)?;
        let size = self
            .encoder
            .encode_type_padding_size_expression_mid(mir_type)?;
        size.to_builtin_method_snapshot(self)
    }
    fn encode_size_function_call_with_axioms(
        &mut self,
        function_name: String,
        arguments: Vec<vir_low::Expression>,
        position: vir_low::Position,
    )-> SpannedEncodingResult<vir_low::Expression> {
        let return_type = self.size_type()?;
        let call = self.create_domain_func_app(
            "Size",
            function_name.clone(),
            arguments,
            return_type,
            position,
        )?;
        if !self.type_layouts_state.encoded_size_functions.contains(&function_name) {
            self.type_layouts_state.encoded_size_functions.insert(function_name.clone());
            let size_type = self.size_type_mid()?;
            let body = self.encode_snapshot_valid_call_for_type(call.clone(), &size_type)?;
            let axiom = vir_low::DomainAxiomDecl::new(None, format!("{function_name}$valid"), body);
            self.declare_axiom("Size", axiom)?;
        }
        Ok(call)
    }
}
