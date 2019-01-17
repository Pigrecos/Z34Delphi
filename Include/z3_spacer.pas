unit z3_spacer;
{ This unit is automatically generated by Chet:
  https://github.com/neslib/Chet }

interface

uses z3;

(**
        \brief Pose a query against the asserted rules at the given level.

        \code
           query ::= (exists (bound-vars) query)
                 |  literals
        \endcode

        query returns
        - \c Z3_L_FALSE if the query is unsatisfiable.
        - \c Z3_L_TRUE if the query is satisfiable. Obtain the answer by calling #Z3_fixedpoint_get_answer.
        - \c Z3_L_UNDEF if the query was interrupted, timed out or otherwise failed.

        def_API('Z3_fixedpoint_query_from_lvl', INT, (_in(CONTEXT), _in(FIXEDPOINT), _in(AST), _in(UINT)))
 *)
function Z3_fixedpoint_query_from_lvl(c: Z3_context; d: Z3_fixedpoint; query: Z3_ast; lvl: Cardinal): Z3_lbool; cdecl;
  external z3_dll name _PU + 'Z3_fixedpoint_query_from_lvl';

(**
       \brief Retrieve a bottom-up (from query) sequence of ground facts

       The previous call to #Z3_fixedpoint_query must have returned \c Z3_L_TRUE.

       def_API('Z3_fixedpoint_get_ground_sat_answer', AST, (_in(CONTEXT), _in(FIXEDPOINT)))
 *)
function Z3_fixedpoint_get_ground_sat_answer(c: Z3_context; d: Z3_fixedpoint): Z3_ast; cdecl;
  external z3_dll name _PU + 'Z3_fixedpoint_get_ground_sat_answer';

(**
       \brief Obtain the list of rules along the counterexample trace.

       def_API('Z3_fixedpoint_get_rules_along_trace', AST_VECTOR, (_in(CONTEXT), _in(FIXEDPOINT)))
 *)
function Z3_fixedpoint_get_rules_along_trace(c: Z3_context; d: Z3_fixedpoint): Z3_ast_vector; cdecl;
  external z3_dll name _PU + 'Z3_fixedpoint_get_rules_along_trace';

(**
       \brief Obtain the list of rules along the counterexample trace.

       def_API('Z3_fixedpoint_get_rule_names_along_trace', SYMBOL, (_in(CONTEXT), _in(FIXEDPOINT)))
 *)
function Z3_fixedpoint_get_rule_names_along_trace(c: Z3_context; d: Z3_fixedpoint): Z3_symbol; cdecl;
  external z3_dll name _PU + 'Z3_fixedpoint_get_rule_names_along_trace';

(**
       \brief Add an invariant for the predicate \c pred.
       Add an assumed invariant of predicate \c pred.

       Note: this functionality is Spacer specific.

       def_API('Z3_fixedpoint_add_invariant', VOID, (_in(CONTEXT), _in(FIXEDPOINT), _in(FUNC_DECL), _in(AST)))
 *)
procedure Z3_fixedpoint_add_invariant(c: Z3_context; d: Z3_fixedpoint; pred: Z3_func_decl; &property: Z3_ast); cdecl;
  external z3_dll name _PU + 'Z3_fixedpoint_add_invariant';

(**
       Retrieve reachable states of a predicate.
       Note: this functionality is Spacer specific.

       def_API('Z3_fixedpoint_get_reachable', AST, (_in(CONTEXT), _in(FIXEDPOINT), _in(FUNC_DECL)))
 *)
function Z3_fixedpoint_get_reachable(c: Z3_context; d: Z3_fixedpoint; pred: Z3_func_decl): Z3_ast; cdecl;
  external z3_dll name _PU + 'Z3_fixedpoint_get_reachable';

(**
       \brief Project variables given a model

       def_API('Z3_qe_model_project', AST, (_in(CONTEXT), _in(MODEL), _in(UINT), _in_array(2, APP), _in(AST)))
 *)
function Z3_qe_model_project(c: Z3_context; m: Z3_model; num_bounds: Cardinal; bound: PZ3_app; body: Z3_ast): Z3_ast; cdecl;
  external z3_dll name _PU + 'Z3_qe_model_project';

(**
       \brief Project variables given a model

       def_API('Z3_qe_model_project_skolem', AST, (_in(CONTEXT), _in(MODEL), _in(UINT), _in_array(2, APP), _in(AST), _in(AST_MAP)))
 *)
function Z3_qe_model_project_skolem(c: Z3_context; m: Z3_model; num_bounds: Cardinal; bound: PZ3_app; body: Z3_ast; map: Z3_ast_map): Z3_ast; cdecl;
  external z3_dll name _PU + 'Z3_qe_model_project_skolem';

(**
       \brief Extrapolates a model of a formula

       def_API('Z3_model_extrapolate', AST, (_in(CONTEXT), _in(MODEL), _in(AST)))
 *)
function Z3_model_extrapolate(c: Z3_context; m: Z3_model; fml: Z3_ast): Z3_ast; cdecl;
  external z3_dll name _PU + 'Z3_model_extrapolate';

(**
       \brief Best-effort quantifier elimination

       def_API ('Z3_qe_lite', AST, (_in(CONTEXT), _in(AST_VECTOR), _in(AST)))
 *)
function Z3_qe_lite(c: Z3_context; vars: Z3_ast_vector; body: Z3_ast): Z3_ast; cdecl;
  external z3_dll name _PU + 'Z3_qe_lite';

implementation

end.