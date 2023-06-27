pub(super) mod inline_functions;
pub(super) mod remove_predicates;
pub(super) mod remove_unvisited_blocks;
pub(super) mod custom_heap_encoding;
pub(super) mod desugar_fold_unfold;
pub(super) mod desugar_method_calls;
pub(super) mod desugar_conditionals;
pub(super) mod symbolic_execution;
pub(super) mod symbolic_execution_new;
pub(super) mod clean_old;
pub(super) mod clean_labels;
pub(super) mod clean_variables;
pub(super) mod merge_statements;
pub(super) mod desugar_implications;
pub(super) mod expand_quantifiers;
pub(super) mod encoder_context;
pub(super) mod make_all_jumps_nondeterministic;
pub(super) mod merge_consequent_blocks;
pub(super) mod case_splits;
