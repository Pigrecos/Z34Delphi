unit UntMain;

interface

uses
  Winapi.Windows, Winapi.Messages, System.SysUtils, System.Variants, System.Classes, Vcl.Graphics,
  Vcl.Controls, Vcl.Forms, Vcl.Dialogs, Vcl.StdCtrls, Vcl.Buttons,
  z3, Vcl.ComCtrls, Vcl.ExtCtrls;

type
  TMain = class(TForm)
    pnl1: TPanel;
    pnlBtn: TPanel;
    btnStart: TBitBtn;
    reLog: TRichEdit;
    procedure btnStartClick(Sender: TObject);
    procedure reLogChange(Sender: TObject);
  private
    procedure prove(ctx: Z3_context; s: Z3_solver; f: Z3_ast; is_valid: Boolean);
    procedure StartMain;
    procedure simple_example;
    procedure demorgan;
    procedure find_model_example1;
    procedure check(ctx: Z3_context; s: Z3_solver; expected_result: Z3_lbool);
    procedure find_model_example2;
    procedure prove_example1;
    procedure prove_example2;
    procedure push_pop_example1;
    procedure quantifier_example1;
    procedure check2(ctx: Z3_context; s: Z3_solver; expected_result: Z3_lbool);

    function  display_model(c: Z3_context; m: Z3_model): AnsiString;
    function  display_symbol(c: Z3_context; s: Z3_symbol): AnsiString;
    function  display_ast(c: Z3_context; v: Z3_ast): AnsiString;
    function  display_sort(c: Z3_context; ty: Z3_sort): AnsiString;
    function display_function_interpretations(c: Z3_context;
      m: Z3_model): AnsiString;
    procedure assert_inj_axiom(ctx: Z3_context; s: Z3_solver; f: Z3_func_decl;
      i: Cardinal);
    procedure array_example1;
    procedure array_example2;
    procedure array_example3;
    procedure tuple_example1;
    procedure bitvector_example1;
    procedure bitvector_example2;
    procedure eval_example1;
    procedure two_contexts_example1;
    procedure error_code_example1;
    procedure error_code_example2;
    procedure parser_example2;
    procedure parser_example3;
    procedure assert_comm_axiom(ctx: Z3_context; s: Z3_solver; f: Z3_func_decl);
    procedure parser_example5;
    procedure numeral_example;
    procedure ite_example;
    procedure enum_example;
    procedure list_example;
    procedure tree_example;
    procedure forest_example;
    procedure binary_tree_example;
    procedure unsat_core_and_proof_example;
    { Private declarations }
  public
    { Public declarations }
  end;

var
  Main: TMain;

implementation
       uses z3_ast_containers;

{$R *.dfm}

procedure TMain.reLogChange(Sender: TObject);
begin
    SendMessage(reLog.handle, WM_VSCROLL, SB_BOTTOM, 0);
end;

procedure LOG_MSG(msg: PAnsiChar);
begin
    Z3_append_log(msg)
end;

(**
   \brief exit gracefully in case of error.
*)
function exitf(messag : AnsiString): AnsiString;
begin
   Result := Format('BUG: %s.',[messag]);
end;

(**
   \brief exit if unreachable code was reached.
*)
procedure unreachable;
begin
    exitf('unreachable code was reached');
end;

(**
   \brief Simpler error handler.
 *)
procedure error_handler(c : Z3_context; e: Z3_error_code) ; cdecl;
begin
    var s : AnsiString := Format('Error code: %d',[ Ord(e) ])+ sLineBreak;
    exitf(s + 'incorrect use of Z3');
end;


procedure throw_z3_error(c : Z3_context; e: Z3_error_code) ;cdecl

begin
    var s : AnsiString := Format('Error code: %d',[ Ord(e) ])+ sLineBreak;
    exitf(s + 'longjmp');
end;


procedure nothrow_z3_error(c : Z3_context; e: Z3_error_code) ; cdecl;
begin
    ShowMessage(Format('Z3 error: %s.', [Z3_get_error_msg(c, e)]));
end;


(**

   \brief Display Z3 version in the standard output.
*)
function display_version:AnsiString;
begin
    var major, minor, build, revision : Cardinal;
    Z3_get_version(@major, @minor, @build, @revision);
    result := format('Z3 %d.%d.%d.%d',[ major, minor, build, revision]);
end;

(**
   \brief Create a logical context.

   Enable model construction. Other configuration parameters can be passed in the cfg variable.

   Also enable tracing to stderr and register custom error handler.
*)
function mk_context_custom(cfg :Z3_config ; err: Z3_error_handler ):Z3_context;
var
  ctx : Z3_context;
begin
    Z3_set_param_value(cfg, 'model', 'true');

    ctx := Z3_mk_context(cfg);
    Z3_set_error_handler(ctx, err);

    Result := ctx;
end;


(**
   \brief Create a logical context.

   Enable model construction only.

   Also enable tracing to stderr and register standard error handler.
*)
function mk_context:Z3_context;
var
  cfg : Z3_config;
  ctx : Z3_context;

begin
    cfg := Z3_mk_config;
    ctx := mk_context_custom(cfg, error_handler);
    Z3_del_config(cfg);

    Result := ctx;
end;

(**
   \brief Create a logical context.

   Enable fine-grained proof construction.
   Enable model construction.

   Also enable tracing to stderr and register standard error handler.
*)
function mk_proof_context: Z3_context;
var
  cfg : Z3_config;
  ctx : Z3_context;

begin
    cfg := Z3_mk_config();
    Z3_set_param_value(cfg, 'proof', 'true');
    ctx := mk_context_custom(cfg, throw_z3_error);
    Z3_del_config(cfg);
    Result := ctx;
end;

function mk_solver(ctx: Z3_context): Z3_solver;
var
  s : Z3_solver;
begin
    s := Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    Result := s;
end;

procedure del_solver(ctx: Z3_context; s: Z3_solver) ;
begin
    Z3_solver_dec_ref(ctx, s);
end;

(**
   \brief Create a variable using the given name and type.
*)
function mk_var(ctx: Z3_context; name: AnsiString; ty: Z3_sort): Z3_ast;
begin
    var s : Z3_symbol := Z3_mk_string_symbol(ctx, PAnsiChar(name));
    Result := Z3_mk_const(ctx, s, ty);
end;

(**
   \brief Create a boolean variable using the given name.
*)
function mk_bool_var(ctx: Z3_context;name: AnsiString): Z3_ast;
begin
    var ty : Z3_sort := Z3_mk_bool_sort(ctx);
    Result :=  mk_var(ctx, name, ty);
end;

(**
   \brief Create an integer variable using the given name.
*)
function mk_int_var(ctx: Z3_context;name: AnsiString) : Z3_ast;
begin
    var ty : Z3_sort := Z3_mk_int_sort(ctx);
    Result :=  mk_var(ctx, name, ty);
end;

(**
   \brief Create a Z3 integer node using a C int.
*)
function mk_int(ctx : Z3_context; v: Integer) : Z3_ast;
begin
    var ty : Z3_sort := Z3_mk_int_sort(ctx);
    Result := Z3_mk_int(ctx, v, ty);
end;

(**
   \brief Create a real variable using the given name.
*)
function mk_real_var(ctx: Z3_context; name: AnsiString): Z3_ast;
begin
    var ty : Z3_sort := Z3_mk_real_sort(ctx);
    Result           := mk_var(ctx, name, ty);
end;


(**
   \brief Create the unary function application: <tt>(f x)</tt>.
*)
function mk_unary_app(ctx: Z3_context; f: Z3_func_decl; x: Z3_ast): Z3_ast;
var
  args : array[0..0] of Z3_ast;
begin
    args[0] := x;
    Result := Z3_mk_app(ctx, f, 1, @args[0]);
end;

(**
   \brief Create the binary function application: <tt>(f x y)</tt>.
*)
function mk_binary_app(ctx: Z3_context; f : Z3_func_decl; x: Z3_ast; y: Z3_ast): Z3_ast;
var
  args : array[0..1] of Z3_ast;
begin
    args[0] := x;
    args[1] := y;
    Result := Z3_mk_app(ctx, f, 2, @args[0]);
end;

(**
   \brief Check whether the logical context is satisfiable, and compare the result with the expected result.
   If the context is satisfiable, then display the model.
*)
procedure TMain.check(ctx: Z3_context; s: Z3_solver; expected_result: Z3_lbool);
var
 stmp : AnsiString ;
begin
    var m   : Z3_model  := 0;
    var res : Z3_lbool  := Z3_solver_check(ctx, s);
    case res of
      Z3_L_FALSE:
          reLog.Lines.Append('unsat.');
      Z3_L_UNDEF: begin
          reLog.Lines.Append('unknown');
	        m := Z3_solver_get_model(ctx, s);
	        if (m) <> nil then
             Z3_model_inc_ref(ctx, m);
          reLog.Lines.Append(Format('potential model:'+sLineBreak+'%s', [Z3_model_to_string(ctx, m)]));
      end;
      Z3_L_TRUE: begin
	        m := Z3_solver_get_model(ctx, s);
	        if (m) <> nil then
             Z3_model_inc_ref(ctx, m);
          stmp := Z3_model_to_string(ctx, m);
          reLog.Lines.Append(Format('sat.'+ sLineBreak+'%s', [Z3_model_to_string(ctx, m)]));
      end;
    end;

    if (res <> expected_result) then
         reLog.Lines.Append(exitf('unexpected result'));

    if (m) <> nil then
        Z3_model_dec_ref(ctx, m);
end;

(**
   \brief Display a symbol in the given output stream.
*)
function TMain.display_symbol(c : Z3_context;  s: Z3_symbol):AnsiString;
begin
    Result := '';
    case Z3_get_symbol_kind(c, s) of
     Z3_INT_SYMBOL   : Result := Format('#%d', [Z3_get_symbol_int   (c, s)]);
     Z3_STRING_SYMBOL: Result := Format('%s',  [Z3_get_symbol_string(c, s)]);
    else
        unreachable;
    end;
end;

(**
   \brief Display the given type.
*)
function TMain.display_sort(c: Z3_context;  ty:Z3_sort): AnsiString;
begin
    Result := '';

    case Z3_get_sort_kind(c, ty) of
      Z3_UNINTERPRETED_SORT: Result := Result + display_symbol(c, Z3_get_sort_name(c, ty));
      Z3_BOOL_SORT         : Result := Result + 'bool';
      Z3_INT_SORT          : Result := Result + 'int';
      Z3_REAL_SORT         : Result := Result + 'real';
      Z3_BV_SORT           : Result := Result + Format('bv%d', [Z3_get_bv_sort_size(c, ty)]);
      Z3_ARRAY_SORT: begin
          Result := Result + '[';
          Result := Result + display_sort(c, Z3_get_array_sort_domain(c, ty));
          Result := Result + '->';
          Result := Result + display_sort(c, Z3_get_array_sort_range(c, ty));
          Result := Result + ']';
      end;
      Z3_DATATYPE_SORT: begin
          if Z3_get_datatype_sort_num_constructors(c, ty) <> 1 then
          begin
              Result := Result + Format('%s', [Z3_sort_to_string(c,ty)]);
          end else
          begin
              var num_fields : Cardinal := Z3_get_tuple_sort_num_fields(c, ty);
              var i : Integer;
              Result := Result +  '(';
              for i := 0 to num_fields - 1 do
              begin
                  var field : Z3_func_decl := Z3_get_tuple_sort_field_decl(c, ty, i);
                  if (i > 0) then
                      Result := Result +  ', ';

                  Result := Result + display_sort(c, Z3_get_range(c, field));
              end;
              Result := Result +  ')';
          end;
      end;
      else begin
          Result := Result + '"unknown[';
          Result := Result + display_symbol(c, Z3_get_sort_name(c, ty));
          Result := Result +']';
      end;
    end;

end;

(**
   \brief Custom ast pretty printer.

   This function demonstrates how to use the API to navigate terms.
*)
function TMain.display_ast(c: Z3_context; v: Z3_ast): AnsiString ;
begin
    Result := '';

    case Z3_get_ast_kind(c, v) of
     Z3_NUMERAL_AST:begin
        var t : Z3_sort;
        Result := Result + Format('%s', [Z3_get_numeral_string(c, v)]);
        t := Z3_get_sort(c, v);
        Result := Result + ':';
        Result := Result + display_sort(c, t);
     end;
     Z3_APP_AST:begin
        var i         : Cardinal;
        var app       : Z3_app       := Z3_to_app(c, v);
        var num_fields: Cardinal     := Z3_get_app_num_args(c, app);
        var d         : Z3_func_decl := Z3_get_app_decl(c, app);

        Result := Result + Format('%s', [Z3_func_decl_to_string(c, d)]);

        if (num_fields > 0) then
        begin
            Result := Result + '[';
            for i := 0 to num_fields - 1 do
            begin
                if (i > 0) then
                    Result := Result +', ';

                Result := Result + display_ast(c, Z3_get_app_arg(c, app, i));
            end;
            Result := Result + ']';
        end;
     end;
     Z3_QUANTIFIER_AST: Result := Result +'quantifier#unknown' ;

    else
     Result := Result + '#unknown';
    end;
end;

(**
   \brief Custom function interpretations pretty printer.
*)
function TMain.display_function_interpretations(c: Z3_context; m: Z3_model): AnsiString;
var
  num_functions : Cardinal;
  i             : Integer;
begin
    Result := '';

    Result := 'function interpretations:' + sLineBreak;

    num_functions := Z3_model_get_num_funcs(c, m);

    for i := 0 to num_functions - 1 do
    begin
        var fdecl      : Z3_func_decl;
        var name       : Z3_symbol;
        var func_else  : Z3_ast;
        var num_entries: Cardinal := 0;
        var j          : Integer  := 0;
        var finterp    : Z3_func_interp_opt;

        fdecl  := Z3_model_get_func_decl(c, m, i);
        finterp:= Z3_model_get_func_interp(c, m, fdecl);
        //  inc ref
	      Z3_func_interp_inc_ref(c, finterp);
        name   := Z3_get_decl_name(c, fdecl);
        Result := Result + display_symbol(c, name);
        Result := Result + ' = {';
        if finterp <> nil then
          num_entries := Z3_func_interp_get_num_entries(c, finterp);

        for j := 0 to num_entries - 1 do
        begin
            var num_args    : Cardinal;
            var k           : Integer;
            var fentry      : Z3_func_entry := Z3_func_interp_get_entry(c, finterp, j);
            // inc ref
	          Z3_func_entry_inc_ref(c, fentry);
            if (j > 0) then
                Result := Result + ', ';

            num_args := Z3_func_entry_get_num_args(c, fentry);
            Result := Result + '(';
            for k := 0 to num_args - 1 do
            begin
                if (k > 0) then
                     Result := Result +', ';

                Result := Result + display_ast(c, Z3_func_entry_get_arg(c, fentry, k));
            end;
            Result := Result + '|->';
            Result := Result + display_ast(c, Z3_func_entry_get_value(c, fentry));
            Result := Result +')';
            //  dec ref
	          Z3_func_entry_dec_ref(c, fentry);
        end;
        if (num_entries > 0) then
             Result := Result +', ';

        Result := Result + '(else|->';
        func_else := Z3_func_interp_get_else(c, finterp);
        Result := Result + display_ast(c, func_else);
        Result := Result  +')}'+ sLineBreak;
        // dec ref
	      Z3_func_interp_dec_ref(c, finterp);
    end;
end;


(**
   \brief Custom model pretty printer.
*)
function TMain.display_model(c: Z3_context; m: Z3_model): AnsiString;
begin
    var num_constants : Cardinal;
    var i             : Integer ;

    Result := '';

    if (m = nil) then Exit;

    num_constants := Z3_model_get_num_consts(c, m);
    for i := 0 to num_constants - 1 do
    begin
        var name : Z3_symbol;
        var cnst : Z3_func_decl := Z3_model_get_const_decl(c, m, i);
        var a, v : Z3_ast;
        var ok   : Boolean;

        name   := Z3_get_decl_name(c, cnst);

        Result := Result + display_symbol(c, name);
        Result := Result + ' = ';

        a := Z3_mk_app(c, cnst, 0, 0);
        v := a;
        ok := Z3_model_eval(c, m, a, True, @v);

        Result := Result + display_ast(c, v);
        Result := Result + sLineBreak;;
    end;
    Result := Result + display_function_interpretations(c, m);
end;


(**
   \brief Similar to #check, but uses #display_model instead of #Z3_model_to_string.
*)
procedure TMain.check2(ctx : Z3_context; s: Z3_solver; expected_result: Z3_lbool);
begin
    var m   : Z3_model  := 0;
    var res : Z3_lbool  := Z3_solver_check(ctx, s);
    case res of
     Z3_L_FALSE:
        reLog.Lines.Append('unsat');
     Z3_L_UNDEF:begin
        reLog.Lines.Append('unknown');
        reLog.Lines.Append('potential model:');
        m := Z3_solver_get_model(ctx, s);
	      if (m <> nil) then
          Z3_model_inc_ref(ctx, m);
         reLog.Lines.Append(display_model(ctx, m));
     end;
     Z3_L_TRUE:begin
        reLog.Lines.Append('sat');
        m := Z3_solver_get_model(ctx, s);
	      if (m <> nil) then
          Z3_model_inc_ref(ctx, m);
         reLog.Lines.Append(display_model(ctx, m));
     end;
    end;
    if (res <> expected_result) then
        exitf('unexpected result');

    if (m <> nil)  then
       Z3_model_dec_ref(ctx, m);

end;

(**
   \brief Prove that the constraints already asserted into the logical
   context implies the given formula.  The result of the proof is
   displayed.

   Z3 is a satisfiability checker. So, one can prove \c f by showing
   that <tt>(not f)</tt> is unsatisfiable.

   The context \c ctx is not modified by this function.
*)
procedure TMain.prove(ctx: Z3_context; s: Z3_solver; f: Z3_ast; is_valid: Boolean);
begin
    var m     : Z3_model  := 0;
    var not_f : Z3_ast;

    (* save the current state of the context *)
    Z3_solver_push(ctx, s);

    not_f := Z3_mk_not(ctx, f);
    Z3_solver_assert(ctx, s, not_f);

    case Z3_solver_check(ctx, s) of
     Z3_L_FALSE: begin
        (* proved *)
        reLog.Lines.Append('valid');
        if  not is_valid then
            exitf('unexpected result');
     end;
     Z3_L_UNDEF:begin
        (* Z3 failed to prove/disprove f. *)
        reLog.Lines.Append('unknown');
        m := Z3_solver_get_model(ctx, s);
        if (m <> nil) then
        begin
	          Z3_model_inc_ref(ctx, m);
            (* m should be viewed as a potential counterexample. *)
  	        reLog.Lines.Append(Format('potential counter example:' +sLineBreak + '%s', [Z3_model_to_string(ctx, m)]));
        end;
        if is_valid  then
            exitf('unexpected result');
     end;
     Z3_L_TRUE:begin
        (* disproved *)
        reLog.Lines.Append('invalid');
        m := Z3_solver_get_model(ctx, s);
        if (m <> nil) then
        begin
	          Z3_model_inc_ref(ctx, m);
            (* the model returned by Z3 is a counterexample *)
            reLog.Lines.Append(Format('counter example:'+ sLineBreak+ '%s', [Z3_model_to_string(ctx, m)]))
        end;
        if (is_valid) then
            exitf('unexpected result');
     end;
    end;
    if (m <> nil) then
       Z3_model_dec_ref(ctx, m);

    (* restore scope *)
    Z3_solver_pop(ctx, s, 1);
end;

(**
   \brief Assert the axiom: function f is injective in the i-th argument.

   The following axiom is asserted into the logical context:
   \code
   forall (x_0, ..., x_n) finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i
   \endcode

   Where, \c finv is a fresh function declaration.
*)
procedure TMain.assert_inj_axiom(ctx: Z3_context; s: Z3_solver; f : Z3_func_decl; i: Cardinal);
var
  sz, j : Cardinal;
  finv_domain, finv_range : Z3_sort;
  finv                    : Z3_func_decl ;
  types                   : array of Z3_sort;   (* types of the quantified variables *)
  names                   : array of Z3_symbol; (* names of the quantified variables *)
  xs                      : array of Z3_ast;    (* arguments for the application f(x_0, ..., x_i, ..., x_{n-1}) *)
  x_i, fxs, finv_fxs, eq  : Z3_ast;
  p                       : Z3_pattern;
  q                       : Z3_ast;
begin
    sz := Z3_get_domain_size(ctx, f);

    if (i >= sz) then
        exitf('failed to create inj axiom');

    (* declare the i-th inverse of f: finv *)
    finv_domain := Z3_get_range(ctx, f);
    finv_range  := Z3_get_domain(ctx, f, i);
    finv        := Z3_mk_fresh_func_decl(ctx, 'inv', 1, @finv_domain, finv_range);

    (* allocate temporary arrays *)
    SetLength(types, sz);
    SetLength(names, sz);
    SetLength(xs,    sz);

    (* fill types, names and xs *)
    for j := 0 to sz - 1 do  types[j] := Z3_get_domain(ctx, f, j);
    for j := 0 to sz - 1 do  names[j] := Z3_mk_int_symbol(ctx, j);
    for j := 0 to sz - 1 do  xs[j]    := Z3_mk_bound(ctx, j, types[j]);

    x_i := xs[i];

    (* create f(x_0, ..., x_i, ..., x_{n-1}) *)
    fxs         := Z3_mk_app(ctx, f, sz, @xs[0]);

    (* create f_inv(f(x_0, ..., x_i, ..., x_{n-1})) *)
    finv_fxs    := mk_unary_app(ctx, finv, fxs);

    (* create finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i *)
    eq          := Z3_mk_eq(ctx, finv_fxs, x_i);

    (* use f(x_0, ..., x_i, ..., x_{n-1}) as the pattern for the quantifier *)
    p           := Z3_mk_pattern(ctx, 1, @fxs);
    reLog.Lines.Append(Format('pattern: %s', [Z3_pattern_to_string(ctx, p)]));
    reLog.Lines.Append('');

    (* create & assert quantifier *)
    q          := Z3_mk_forall(ctx,
                                 0,  (* using default weight *)
                                 1,  (* number of patterns *)
                                 @p, (* address of the "array" of patterns *)
                                 sz, (* number of quantified variables *)
                                 @types[0],
                                 @names[0],
                                 eq);
    reLog.Lines.Append('assert axiom:');
    reLog.Lines.Append(Format('%s', [Z3_ast_to_string(ctx, q)]));
    Z3_solver_assert(ctx, s, q);

    (* free temporary arrays *)
    SetLength(types, 0);
    SetLength(names, 0);
    SetLength(xs,    0);
end;

(**
   \brief Assert the axiom: function f is commutative.

   This example uses the SMT-LIB parser to simplify the axiom construction.
*)
procedure TMain.assert_comm_axiom(ctx: Z3_context; s: Z3_solver; f: Z3_func_decl);
var
  t             : Z3_sort;
  f_name, t_name: Z3_symbol ;
  q             : Z3_ast_vector ;
  i             : Cardinal;
Begin

    t := Z3_get_range(ctx, f);

    if (Z3_get_domain_size(ctx, f) <> 2) or
       (Z3_get_domain(ctx, f, 0) <> t) or
       (Z3_get_domain(ctx, f, 1) <> t) then
         exitf('function must be binary, and argument types must be equal to return type');


    (* Inside the parser, function f will be referenced using the symbol 'f'. *)
    f_name := Z3_mk_string_symbol(ctx, 'f');

    (* Inside the parser, type t will be referenced using the symbol 'T'. *)
    t_name := Z3_mk_string_symbol(ctx, 'T');

    q := Z3_parse_smtlib2_string(ctx,
                           '(assert (forall ((x T) (y T)) (= (f x y) (f y x))))',
                           1, @t_name, @t,
                           1, @f_name, @f);
    reLog.Lines.Append(Format('assert axiom:'+ sLineBreak + '%s', [Z3_ast_vector_to_string(ctx, q)]));
    for i := 0 to Z3_ast_vector_size(ctx, q)  - 1 do
        Z3_solver_assert(ctx, s, Z3_ast_vector_get(ctx, q, i));

end;

(**
   \brief Z3 does not support explicitly tuple updates. They can be easily implemented
   as macros. The argument \c t must have tuple type.
   A tuple update is a new tuple where field \c i has value \c new_val, and all
   other fields have the value of the respective field of \c t.

   <tt>update(t, i, new_val)</tt> is equivalent to
   <tt>mk_tuple(proj_0(t), ..., new_val, ..., proj_n(t))</tt>
*)
function mk_tuple_update(c: Z3_context; t: Z3_ast; i: Cardinal; new_val: Z3_ast): Z3_ast;
var
  ty            : Z3_sort;
  mk_tuple_decl : Z3_func_decl;
  num_fields, j : Cardinal;
  new_fields    : array of Z3_ast;
  res           : Z3_ast;
begin
    ty := Z3_get_sort(c, t);

    if (Z3_get_sort_kind(c, ty) <> Z3_DATATYPE_SORT) then
        exitf('argument must be a tuple');

    num_fields := Z3_get_tuple_sort_num_fields(c, ty);

    if (i >= num_fields) then
        exitf('invalid tuple update, index is too big');

    SetLength(new_fields, num_fields);
    for j := 0 to num_fields - 1 do
    begin
        if i = j then
        begin
            (* use new_val at position i *)
            new_fields[j] := new_val;
        end else
        begin
            (* use field j of t *)
            var proj_decl : Z3_func_decl := Z3_get_tuple_sort_field_decl(c, ty, j);
            new_fields[j]                := mk_unary_app(c, proj_decl, t);
        end;
    end;
    mk_tuple_decl := Z3_get_tuple_sort_mk_decl(c, ty);
    res           := Z3_mk_app(c, mk_tuple_decl, num_fields, @new_fields[0]);

    SetLength(new_fields,0);
    result := res;
end;

(**********************Procedure start********)
(**
   \brief "Hello world" example: create a Z3 logical context, and delete it.
*)
procedure TMain.simple_example;
var
  ctx : Z3_context;
begin
    LOG_MSG('simple_example');

    reLog.Lines.Append(sLineBreak + 'simple_example');

    ctx := mk_context;

    (* delete logical context *)
    Z3_del_context(ctx);
end;

(**
  Demonstration of how Z3 can be used to prove validity of
  De Morgan's Duality Law: {e not(x and y) <-> (not x) or ( not y) }
*)
procedure TMain.demorgan;
var
    cfg      : Z3_config;
    ctx      : Z3_context;
    s        : Z3_solver;
    bool_sort: Z3_sort;
    symbol_x,
    symbol_y : Z3_symbol;
    x, y,
    not_x,
    not_y,
    x_and_y,
    ls, rs,
    conjecture,
    negated_conjecture : Z3_ast;
    args               : array[0..1] of Z3_ast;
begin
    reLog.Lines.Append(sLineBreak + 'DeMorgan');
    LOG_MSG('DeMorgan');

    cfg                := Z3_mk_config();
    ctx                := Z3_mk_context(cfg);
    Z3_del_config(cfg);
    bool_sort          := Z3_mk_bool_sort(ctx);
    symbol_x           := Z3_mk_int_symbol(ctx, 0);
    symbol_y           := Z3_mk_int_symbol(ctx, 1);
    x                  := Z3_mk_const(ctx, symbol_x, bool_sort);
    y                  := Z3_mk_const(ctx, symbol_y, bool_sort);

    (* De Morgan - with a negation around *)
    (* !(!(x && y) <-> (!x || !y)) *)
    not_x              := Z3_mk_not(ctx, x);
    not_y              := Z3_mk_not(ctx, y);
    args[0]            := x;
    args[1]            := y;
    x_and_y            := Z3_mk_and(ctx, 2, @args[0]);
    ls                 := Z3_mk_not(ctx, x_and_y);
    args[0]            := not_x;
    args[1]            := not_y;
    rs                 := Z3_mk_or(ctx, 2, @args[0]);
    conjecture         := Z3_mk_iff(ctx, ls, rs);
    negated_conjecture := Z3_mk_not(ctx, conjecture);

    s := mk_solver(ctx);
    Z3_solver_assert(ctx, s, negated_conjecture);
    case Z3_solver_check(ctx, s) of
      Z3_L_FALSE:
        (* The negated conjecture was unsatisfiable, hence the conjecture is valid *)
        reLog.Lines.Append('DeMorgan is valid');

      Z3_L_UNDEF:
        (* Check returned undef *)
        reLog.Lines.Append('Undef');
      Z3_L_TRUE:
        (* The negated conjecture was satisfiable, hence the conjecture is not valid *)
        reLog.Lines.Append('DeMorgan is not valid');

    end;
    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

(**
   \brief Find a model for <tt>x xor y</tt>.
*)
procedure TMain.find_model_example1;
var
  ctx           : Z3_context;
  x, y, x_xor_y : Z3_ast;
  s             : Z3_solver;
begin
    reLog.Lines.Append(sLineBreak + 'find_model_example1');
    LOG_MSG('find_model_example1');

    ctx     := mk_context();
    s       := mk_solver(ctx);

    x       := mk_bool_var(ctx, 'x');
    y       := mk_bool_var(ctx, 'y');
    x_xor_y := Z3_mk_xor(ctx, x, y);

    Z3_solver_assert(ctx, s, x_xor_y);

    reLog.Lines.Append('model for: x xor y');
    check(ctx, s, Z3_L_TRUE);

    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

(**
   \brief Find a model for <tt>x < y + 1, x > 2</tt>.
   Then, assert <tt>not(x = y)</tt>, and find another model.
*)
procedure TMain.find_model_example2;
var
  ctx            : Z3_context;
  x, y, one, two,
  y_plus_one     : Z3_ast;
  x_eq_y         : Z3_ast;
  args           : array[0..1] of Z3_ast;
  c1, c2, c3     : Z3_ast;
  s              : Z3_solver;
begin
    reLog.Lines.Append(sLineBreak + 'find_model_example2');
    LOG_MSG('find_model_example2');

    ctx        := mk_context();
    s          := mk_solver(ctx);
    x          := mk_int_var(ctx, 'x');
    y          := mk_int_var(ctx, 'y');
    one        := mk_int(ctx, 1);
    two        := mk_int(ctx, 2);

    args[0]    := y;
    args[1]    := one;
    y_plus_one := Z3_mk_add(ctx, 2, @args[0]);

    c1         := Z3_mk_lt(ctx, x, y_plus_one);
    c2         := Z3_mk_gt(ctx, x, two);

    Z3_solver_assert(ctx, s, c1);
    Z3_solver_assert(ctx, s, c2);

    reLog.Lines.Append('model for: x < y + 1, x > 2');
    check(ctx, s, Z3_L_TRUE);

    (* assert not(x = y) *)
    x_eq_y     := Z3_mk_eq(ctx, x, y);
    c3         := Z3_mk_not(ctx, x_eq_y);
    Z3_solver_assert(ctx, s,c3);

    reLog.Lines.Append('model for: x < y + 1, x > 2, not(x = y)');
    check(ctx, s, Z3_L_TRUE);

    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

(**
   \brief Prove <tt>x = y implies g(x) = g(y)</tt>, and
   disprove <tt>x = y implies g(g(x)) = g(y)</tt>.

   This function demonstrates how to create uninterpreted types and
   functions.
*)
procedure TMain.prove_example1;
var
  ctx    : Z3_context;
  s      : Z3_solver;
  U_name,
  g_name,
  x_name,
  y_name : Z3_symbol;
  U      : Z3_sort;
  g_domain : array[0..0] of Z3_sort;
  g      : Z3_func_decl;
  x, y,
  gx, ggx,
  gy     : Z3_ast;
  eq, f  : Z3_ast;
begin
    reLog.Lines.Append(sLineBreak + 'prove_example1');
    LOG_MSG('prove_example1');

    ctx        := mk_context();
    s          := mk_solver(ctx);

    (* create uninterpreted type. *)
    U_name     := Z3_mk_string_symbol(ctx, 'U');
    U          := Z3_mk_uninterpreted_sort(ctx, U_name);

    (* declare function g *)
    g_name      := Z3_mk_string_symbol(ctx, 'g');
    g_domain[0] := U;
    g           := Z3_mk_func_decl(ctx, g_name, 1, @g_domain[0], U);

    (* create x and y *)
    x_name      := Z3_mk_string_symbol(ctx, 'x');
    y_name      := Z3_mk_string_symbol(ctx, 'y');
    x           := Z3_mk_const(ctx, x_name, U);
    y           := Z3_mk_const(ctx, y_name, U);
    (* create g(x), g(y) *)
    gx          := mk_unary_app(ctx, g, x);
    gy          := mk_unary_app(ctx, g, y);

    (* assert x = y *)
    eq          := Z3_mk_eq(ctx, x, y);
    Z3_solver_assert(ctx, s, eq);

    (* prove g(x) = g(y) *)
    f           := Z3_mk_eq(ctx, gx, gy);
    reLog.Lines.Append('prove: x = y implies g(x) = g(y)');
    prove(ctx, s, f, true);

    (* create g(g(x)) *)
    ggx         := mk_unary_app(ctx, g, gx);

    (* disprove g(g(x)) = g(y) *)
    f           := Z3_mk_eq(ctx, ggx, gy);
    reLog.Lines.Append('disprove: x = y implies g(g(x)) = g(y)');
    prove(ctx, s, f, false);

    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

(**
   \brief Prove <tt>not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0 </tt>.
   Then, show that <tt>z < -1</tt> is not implied.

   This example demonstrates how to combine uninterpreted functions and arithmetic.
*)
procedure TMain.prove_example2;
var
  ctx      : Z3_context;
  s        : Z3_solver;
  int_sort : Z3_sort;
  g_name   : Z3_symbol;
  g_domain : array[0..0] of Z3_sort;
  g        : Z3_func_decl;
  args     : array[0..1] of Z3_ast;
  x, y, z,
  zero,
  minus_one,
  x_plus_z,
  gx, gy,
  gz, gx_gy,
  ggx_gy   : Z3_ast;
  eq, c1,
  c2, c3, f: Z3_ast;
begin

    reLog.Lines.Append(sLineBreak + 'prove_example2');
    LOG_MSG('prove_example2');

    ctx        := mk_context();
    s          := mk_solver(ctx);

    (* declare function g *)
    int_sort    := Z3_mk_int_sort(ctx);
    g_name      := Z3_mk_string_symbol(ctx, 'g');
    g_domain[0] := int_sort;
    g           := Z3_mk_func_decl(ctx, g_name, 1, @g_domain[0], int_sort);

    (* create x, y, and z *)
    x           := mk_int_var(ctx, 'x');
    y           := mk_int_var(ctx, 'y');
    z           := mk_int_var(ctx, 'z');

    (* create gx, gy, gz *)
    gx          := mk_unary_app(ctx, g, x);
    gy          := mk_unary_app(ctx, g, y);
    gz          := mk_unary_app(ctx, g, z);

    (* create zero *)
    zero        := mk_int(ctx, 0);

    (* assert not(g(g(x) - g(y)) = g(z)) *)
    args[0]     := gx;
    args[1]     := gy;
    gx_gy       := Z3_mk_sub(ctx, 2, @args[0]);
    ggx_gy      := mk_unary_app(ctx, g, gx_gy);
    eq          := Z3_mk_eq(ctx, ggx_gy, gz);
    c1          := Z3_mk_not(ctx, eq);
    Z3_solver_assert(ctx, s, c1);

    (* assert x + z <= y *)
    args[0]     := x;
    args[1]     := z;
    x_plus_z    := Z3_mk_add(ctx, 2, @args[0]);
    c2          := Z3_mk_le(ctx, x_plus_z, y);
    Z3_solver_assert(ctx, s, c2);

    (* assert y <= x *)
    c3          := Z3_mk_le(ctx, y, x);
    Z3_solver_assert(ctx, s, c3);

    (* prove z < 0 *)
    f           := Z3_mk_lt(ctx, z, zero);
    reLog.Lines.Append('prove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0');
    prove(ctx, s, f, true);

    (* disprove z < -1 *)
    minus_one   := mk_int(ctx, -1);
    f           := Z3_mk_lt(ctx, z, minus_one);
    reLog.Lines.Append('disprove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < -1');
    prove(ctx, s, f, false);

    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

(**
   \brief Show how push & pop can be used to create "backtracking"
   points.

   This example also demonstrates how big numbers can be created in Z3.
*)
procedure TMain.push_pop_example1;
var
  ctx     : Z3_context ;
  s       : Z3_solver ;
  int_sort: Z3_sort;
  x_sym,
  y_sym   : Z3_symbol ;
  x, y,
  big_number,
  three   : Z3_ast ;
  c1, c2,
  c3      : Z3_ast;
begin
    reLog.Lines.Append(sLineBreak + 'push_pop_example1');
    LOG_MSG('push_pop_example1');

    ctx        := mk_context();
    s          := mk_solver(ctx);

    (* create a big number *)
    int_sort   := Z3_mk_int_sort(ctx);
    big_number := Z3_mk_numeral(ctx, '1000000000000000000000000000000000000000000000000000000', int_sort);

    (* create number 3 *)
    three      := Z3_mk_numeral(ctx, '3', int_sort);

    (* create x *)
    x_sym      := Z3_mk_string_symbol(ctx, 'x');
    x          := Z3_mk_const(ctx, x_sym, int_sort);

    (* assert x >= "big number" *)
    c1         := Z3_mk_ge(ctx, x, big_number);
    reLog.Lines.Append('assert: x >= "big number"');
    Z3_solver_assert(ctx, s, c1);

    (* create a backtracking point *)
    reLog.Lines.Append('push');
    Z3_solver_push(ctx, s);

    reLog.Lines.Append(Format('number of scopes: %d', [Z3_solver_get_num_scopes(ctx, s)]));

    (* assert x <= 3 *)
    c2         := Z3_mk_le(ctx, x, three);
    reLog.Lines.Append('assert: x <= 3');
    Z3_solver_assert(ctx, s, c2);

    (* context is inconsistent at this point *)
    check2(ctx, s, Z3_L_FALSE);

    (* backtrack: the constraint x <= 3 will be removed, since it was
       asserted after the last Z3_solver_push. *)
    reLog.Lines.Append('pop');
    Z3_solver_pop(ctx, s, 1);

    reLog.Lines.Append(Format('number of scopes: %d', [Z3_solver_get_num_scopes(ctx, s)]));


    (* the context is consistent again. *)
    check2(ctx, s, Z3_L_TRUE);

    (* new constraints can be asserted... *)

    (* create y *)
    y_sym      := Z3_mk_string_symbol(ctx, 'y');
    y          := Z3_mk_const(ctx, y_sym, int_sort);

    (* assert y > x *)
    c3         := Z3_mk_gt(ctx, y, x);
    reLog.Lines.Append('assert: y > x');
    Z3_solver_assert(ctx, s, c3);

    (* the context is still consistent. *)
    check2(ctx, s, Z3_L_TRUE);

    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

(**
   \brief Prove that <tt>f(x, y) = f(w, v) implies y = v</tt> when
   \c f is injective in the second argument.

   \sa assert_inj_axiom.
*)
procedure TMain.quantifier_example1;
var
  cfg                  : Z3_config;
  ctx                  : Z3_context;
  s                    : Z3_solver;
  int_sort             : Z3_sort;
  f_name               : Z3_symbol;
  f_domain             : array[0..1] of Z3_sort;
  f                    : Z3_func_decl;
  x, y, w, v, fxy, fwv : Z3_ast;
  p1, p2, p3, not_p3   : Z3_ast;
begin
    reLog.Lines.Append('quantifier_example1');
    LOG_MSG('quantifier_example1');

    cfg := Z3_mk_config();
    (* If quantified formulas are asserted in a logical context, then
       Z3 may return L_UNDEF. In this case, the model produced by Z3 should be viewed as a potential/candidate model.
    *)

    (*
       The current model finder for quantified formulas cannot handle injectivity.
       So, we are limiting the number of iterations to avoid a long "wait".
    *)
    Z3_global_param_set('smt.mbqi.max_iterations', '10');
    ctx := mk_context_custom(cfg, error_handler);
    Z3_del_config(cfg);
    s := mk_solver(ctx);

    (* declare function f *)
    int_sort    := Z3_mk_int_sort(ctx);
    f_name      := Z3_mk_string_symbol(ctx, 'f');
    f_domain[0] := int_sort;
    f_domain[1] := int_sort;
    f           := Z3_mk_func_decl(ctx, f_name, 2, @f_domain[0], int_sort);

    (* assert that f is injective in the second argument. *)
    assert_inj_axiom(ctx, s, f, 1);

    (* create x, y, v, w, fxy, fwv *)
    x           := mk_int_var(ctx, 'x');
    y           := mk_int_var(ctx, 'y');
    v           := mk_int_var(ctx, 'v');
    w           := mk_int_var(ctx, 'w');
    fxy         := mk_binary_app(ctx, f, x, y);
    fwv         := mk_binary_app(ctx, f, w, v);

    (* assert f(x, y) = f(w, v) *)
    p1          := Z3_mk_eq(ctx, fxy, fwv);
    Z3_solver_assert(ctx, s, p1);

    (* prove f(x, y) = f(w, v) implies y = v *)
    p2          := Z3_mk_eq(ctx, y, v);
    reLog.Lines.Append('prove: f(x, y) = f(w, v) implies y = v');
    prove(ctx, s, p2, true);

    (* disprove f(x, y) = f(w, v) implies x = w *)
    (* using check2 instead of prove *)
    p3          := Z3_mk_eq(ctx, x, w);
    not_p3      := Z3_mk_not(ctx, p3);
    Z3_solver_assert(ctx, s, not_p3);
    reLog.Lines.Append('disprove: f(x, y) = f(w, v) implies x = w');
    reLog.Lines.Append('that is: not(f(x, y) = f(w, v) implies x = w) is satisfiable');
    check2(ctx, s, Z3_L_UNDEF);
    reLog.Lines.Append(Format('reason for last failure: %s',  [Z3_solver_get_reason_unknown(ctx, s)]));
    del_solver(ctx, s);
    Z3_del_context(ctx);
    (* reset global parameters set by this function *)
    Z3_global_param_reset_all;
end;

(**
   \brief Prove <tt>store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3))</tt>.

   This example demonstrates how to use the array theory.
*)
procedure TMain.array_example1;
var
  ds                   : array[0..2] of  Z3_ast;
  int_sort, array_sort : Z3_sort;
  a1, a2, i1, v1, i2, v2, i3 : Z3_ast;
  st1, st2, sel1, sel2       : Z3_ast;
  antecedent, consequent     : Z3_ast;
  thm                        : Z3_ast;
begin
    var ctx                 : Z3_context := mk_context;
    var s                   : Z3_solver  := mk_solver(ctx);

    reLog.Lines.Append(sLineBreak+ 'array_example1');
    LOG_MSG('array_example1');

    int_sort    := Z3_mk_int_sort(ctx);
    array_sort  := Z3_mk_array_sort(ctx, int_sort, int_sort);

    a1          := mk_var(ctx, 'a1', array_sort);
    a2          := mk_var(ctx, 'a2', array_sort);
    i1          := mk_var(ctx, 'i1', int_sort);
    i2          := mk_var(ctx, 'i2', int_sort);
    i3          := mk_var(ctx, 'i3', int_sort);
    v1          := mk_var(ctx, 'v1', int_sort);
    v2          := mk_var(ctx, 'v2', int_sort);

    st1         := Z3_mk_store(ctx, a1, i1, v1);
    st2         := Z3_mk_store(ctx, a2, i2, v2);

    sel1        := Z3_mk_select(ctx, a1, i3);
    sel2        := Z3_mk_select(ctx, a2, i3);

    (* create antecedent *)
    antecedent  := Z3_mk_eq(ctx, st1, st2);

    (* create consequent: i1 = i3 or  i2 = i3 or select(a1, i3) = select(a2, i3) *)
    ds[0]       := Z3_mk_eq(ctx, i1, i3);
    ds[1]       := Z3_mk_eq(ctx, i2, i3);
    ds[2]       := Z3_mk_eq(ctx, sel1, sel2);
    consequent  := Z3_mk_or(ctx, 3, @ds[0]);

    (* prove store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3)) *)
    thm         := Z3_mk_implies(ctx, antecedent, consequent);
    reLog.Lines.Append('prove: store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3))');
    reLog.Lines.Append(Format('%s', [Z3_ast_to_string(ctx, thm)]));
    prove(ctx, s, thm, true);

    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

(**
   \brief Show that <tt>distinct(a_0, ... , a_n)</tt> is
   unsatisfiable when \c a_i's are arrays from boolean to
   boolean and n > 4.

   This example also shows how to use the \c distinct construct.
*)
procedure TMain.array_example2;
var
  ctx        : Z3_context ;
  s          : Z3_solver;
  bool_sort,
  array_sort : Z3_sort;
  a          : array[0..4] of Z3_ast;
  d          : Z3_ast;
  i, n       : Integer;
begin
    reLog.Lines.Append(sLineBreak+ 'array_example2');
    LOG_MSG('array_example2');

    for n := 2 to 5 do
    begin
        reLog.Lines.Append(Format('n = %d', [n]));
        ctx := mk_context();
        s   := mk_solver(ctx);

        bool_sort   := Z3_mk_bool_sort(ctx);
        array_sort  := Z3_mk_array_sort(ctx, bool_sort, bool_sort);

        (* create arrays *)
        for i := 0 to n - 1 do
        begin
            var ss : Z3_symbol := Z3_mk_int_symbol(ctx, i);
            a[i]               := Z3_mk_const(ctx, ss, array_sort);
        end;

        (* assert distinct(a[0], ..., a[n]) *)
        d := Z3_mk_distinct(ctx, n, @a[0]);
        reLog.Lines.Append(Format('%s', [Z3_ast_to_string(ctx, d)]));
        Z3_solver_assert(ctx, s, d);

        (* context is satisfiable if n < 5 *)
        if    (n) < 5 then check2(ctx, s, Z3_L_TRUE )
        else                 check2(ctx, s, Z3_L_FALSE );

	      del_solver(ctx, s);
        Z3_del_context(ctx);
    end;
end;

(**
   \brief Simple array type construction/deconstruction example.
*)
procedure TMain.array_example3;
var
   bool_sort, int_sort, array_sort : Z3_sort;
   domain, range                   : Z3_sort;
begin
    reLog.Lines.Append(sLineBreak+ 'array_example3');
    LOG_MSG('array_example3');

    var ctx : Z3_context := mk_context;
    var s   : Z3_solver  := mk_solver(ctx);

    bool_sort  := Z3_mk_bool_sort(ctx);
    int_sort   := Z3_mk_int_sort(ctx);
    array_sort := Z3_mk_array_sort(ctx, int_sort, bool_sort);

    if Z3_get_sort_kind(ctx, array_sort) <> Z3_ARRAY_SORT then
        exitf('type must be an array type');

    domain := Z3_get_array_sort_domain(ctx, array_sort);
    range  := Z3_get_array_sort_range(ctx, array_sort);

    reLog.Lines.Append('domain: '+ display_sort(ctx, domain));

    reLog.Lines.Append('range:  '+ display_sort(ctx, range));
    reLog.Lines.Append('');

	if (int_sort <> domain) or (bool_sort <> range) then
       exitf('invalid array type');


    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

(**
   \brief Simple tuple type example. It creates a tuple that is a pair of real numbers.
*)
procedure TMain.tuple_example1;
var
    real_sort, pair_sort  : Z3_sort;
    mk_tuple_name         : Z3_symbol;
    mk_tuple_decl         : Z3_func_decl  ;
    proj_names            : array[0..1] of Z3_symbol;
    proj_sorts            : array[0..1] of Z3_sort;
    proj_decls            : array[0..1] of Z3_func_decl;
    antecedents           : array[0..1] of Z3_ast;
    get_x_decl, get_y_decl: Z3_func_decl;
Begin
    reLog.Lines.Append(sLineBreak+ 'tuple_example1');
    LOG_MSG('tuple_example1');

    var ctx : Z3_context := mk_context();
    var s   : Z3_solver  := mk_solver(ctx);


    real_sort := Z3_mk_real_sort(ctx);

    (* Create pair (tuple) type *)
    mk_tuple_name := Z3_mk_string_symbol(ctx, 'mk_pair');
    proj_names[0] := Z3_mk_string_symbol(ctx, 'get_x');
    proj_names[1] := Z3_mk_string_symbol(ctx, 'get_y');
    proj_sorts[0] := real_sort;
    proj_sorts[1] := real_sort;
    (* Z3_mk_tuple_sort will set mk_tuple_decl and proj_decls *)
    pair_sort     := Z3_mk_tuple_sort(ctx, mk_tuple_name, 2, @proj_names[0], @proj_sorts[0], @mk_tuple_decl, @proj_decls[0]);
    get_x_decl    := proj_decls[0]; (* function that extracts the first element of a tuple. *)
    get_y_decl    := proj_decls[1]; (* function that extracts the second element of a tuple. *)

    reLog.Lines.Append('tuple_sort: '+ display_sort(ctx, pair_sort));
    reLog.Lines.Append('');

     begin
        (* prove that get_x(mk_pair(x,y)) == 1 implies x = 1*)
        var app1, app2, x, y, one : Z3_ast;
        var eq1, eq2, eq3, thm    : Z3_ast;

        x    := mk_real_var(ctx, 'x');
        y    := mk_real_var(ctx, 'y');
        app1 := mk_binary_app(ctx, mk_tuple_decl, x, y);
        app2 := mk_unary_app(ctx, get_x_decl, app1);
        one  := Z3_mk_numeral(ctx, '1', real_sort);
        eq1  := Z3_mk_eq(ctx, app2, one);
        eq2  := Z3_mk_eq(ctx, x, one);
        thm  := Z3_mk_implies(ctx, eq1, eq2);
        reLog.Lines.Append('prove: get_x(mk_pair(x, y)) = 1 implies x = 1');
        prove(ctx, s, thm, true);

        (* disprove that get_x(mk_pair(x,y)) == 1 implies y = 1*)
        eq3  := Z3_mk_eq(ctx, y, one);
        thm  := Z3_mk_implies(ctx, eq1, eq3);
        reLog.Lines.Append('disprove: get_x(mk_pair(x, y)) = 1 implies y = 1');
        prove(ctx, s, thm, false);
     end;

     begin
        (* prove that get_x(p1) = get_x(p2) and get_y(p1) = get_y(p2) implies p1 = p2 *)
        var p1, p2, x1, x2, y1, y2      : Z3_ast;
        var antecedent, consequent, thm : Z3_ast;

        p1             := mk_var(ctx, 'p1', pair_sort);
        p2             := mk_var(ctx, 'p2', pair_sort);
        x1             := mk_unary_app(ctx, get_x_decl, p1);
        y1             := mk_unary_app(ctx, get_y_decl, p1);
        x2             := mk_unary_app(ctx, get_x_decl, p2);
        y2             := mk_unary_app(ctx, get_y_decl, p2);
        antecedents[0] := Z3_mk_eq(ctx, x1, x2);
        antecedents[1] := Z3_mk_eq(ctx, y1, y2);
        antecedent     := Z3_mk_and(ctx, 2, @antecedents[0]);
        consequent     := Z3_mk_eq(ctx, p1, p2);
        thm            := Z3_mk_implies(ctx, antecedent, consequent);
        reLog.Lines.Append('prove: get_x(p1) = get_x(p2) and get_y(p1) = get_y(p2) implies p1 = p2');
        prove(ctx, s, thm, true);

        (* disprove that get_x(p1) = get_x(p2) implies p1 = p2 *)
        thm            := Z3_mk_implies(ctx, antecedents[0], consequent);
        reLog.Lines.Append('disprove: get_x(p1) = get_x(p2) implies p1 = p2');
        prove(ctx, s, thm, false);
     end;

     begin
        (* demonstrate how to use the mk_tuple_update function *)
        (* prove that p2 = update(p1, 0, 10) implies get_x(p2) = 10 *)
        var p1, p2, one, ten, updt, x, y : Z3_ast;
        var antecedent, consequent, thm  : Z3_ast;

        p1             := mk_var(ctx, 'p1', pair_sort);
        p2             := mk_var(ctx, 'p2', pair_sort);
        one            := Z3_mk_numeral(ctx, '1', real_sort);
        ten            := Z3_mk_numeral(ctx, '10', real_sort);
        updt           := mk_tuple_update(ctx, p1, 0, ten);
        antecedent     := Z3_mk_eq(ctx, p2, updt);
        x              := mk_unary_app(ctx, get_x_decl, p2);
        consequent     := Z3_mk_eq(ctx, x, ten);
        thm            := Z3_mk_implies(ctx, antecedent, consequent);
        reLog.Lines.Append('prove: p2 = update(p1, 0, 10) implies get_x(p2) = 10');
        prove(ctx, s, thm, true);

        (* disprove that p2 = update(p1, 0, 10) implies get_y(p2) = 10 *)
        y              := mk_unary_app(ctx, get_y_decl, p2);
        consequent     := Z3_mk_eq(ctx, y, ten);
        thm            := Z3_mk_implies(ctx, antecedent, consequent);
        reLog.Lines.Append('disprove: p2 = update(p1, 0, 10) implies get_y(p2) = 10');
        prove(ctx, s, thm, false);
     end;


    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

(**
   \brief Simple bit-vector example. This example disproves that x - 10 <= 0 IFF x <= 10 for (32-bit) machine integers
*)
procedure TMain.bitvector_example1;
var
  bv_sort : Z3_sort;
  x, zero, ten, x_minus_ten, c1, c2, thm : Z3_ast;
begin
    var ctx : Z3_context := mk_context;
    var s   : Z3_solver  := mk_solver(ctx);

    reLog.Lines.Append(sLineBreak+ 'bitvector_example1');
    LOG_MSG('bitvector_example1');

    bv_sort   := Z3_mk_bv_sort(ctx, 32);

    x           := mk_var(ctx, 'x', bv_sort);
    zero        := Z3_mk_numeral(ctx, '0', bv_sort);
    ten         := Z3_mk_numeral(ctx, '10', bv_sort);
    x_minus_ten := Z3_mk_bvsub(ctx, x, ten);
    (* bvsle is signed less than or equal to *)
    c1          := Z3_mk_bvsle(ctx, x, ten);
    c2          := Z3_mk_bvsle(ctx, x_minus_ten, zero);
    thm         := Z3_mk_iff(ctx, c1, c2);
    reLog.Lines.Append('disprove: x - 10 <= 0 IFF x <= 10 for (32-bit) machine integers');
    prove(ctx, s, thm, false);

    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

(**
   \brief Find x and y such that: x ^ y - 103 == x * y
*)
procedure TMain.bitvector_example2;
begin
    var ctx : Z3_context := mk_context;
    var s   : Z3_solver  := mk_solver(ctx);

    reLog.Lines.Append(sLineBreak+ 'bitvector_example2');
    LOG_MSG('bitvector_example2');
    reLog.Lines.Append('find values of x and y, such that x ^ y - 103 == x * y');

    (* construct x ^ y - 103 == x * y *)
    var bv_sort : Z3_sort := Z3_mk_bv_sort(ctx, 32);
    var x       : Z3_ast  := mk_var(ctx, 'x', bv_sort);
    var y       : Z3_ast  := mk_var(ctx, 'y', bv_sort);
    var x_xor_y : Z3_ast  := Z3_mk_bvxor(ctx, x, y);
    var c103    : Z3_ast  := Z3_mk_numeral(ctx, '103', bv_sort);
    var lhs     : Z3_ast  := Z3_mk_bvsub(ctx, x_xor_y, c103);
    var rhs     : Z3_ast  := Z3_mk_bvmul(ctx, x, y);
    var ctr     : Z3_ast  := Z3_mk_eq(ctx, lhs, rhs);

    (* add the constraint <tt>x ^ y - 103 == x * y<\tt> to the logical context *)
    Z3_solver_assert(ctx, s, ctr);

    (* find a model (i.e., values for x an y that satisfy the constraint *)
    check(ctx, s, Z3_L_TRUE);

    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

(**
   \brief Demonstrate how to use #Z3_eval.
*)
procedure TMain.eval_example1;
var
  x, y, two : Z3_ast;
  c1, c2    : Z3_ast;
  args      : array[0..1] of Z3_ast;
begin
    var ctx : Z3_context := mk_context;
    var s   : Z3_solver  := mk_solver(ctx);
    var m   : Z3_model   := 0;

    reLog.Lines.Append('');
    reLog.Lines.Append('eval_example1');
    LOG_MSG('eval_example1');

    x          := mk_int_var(ctx, 'x');
    y          := mk_int_var(ctx, 'y');
    two        := mk_int(ctx, 2);

    (* assert x < y *)
    c1         := Z3_mk_lt(ctx, x, y);
    Z3_solver_assert(ctx, s, c1);

    (* assert x > 2 *)
    c2         := Z3_mk_gt(ctx, x, two);
    Z3_solver_assert(ctx, s, c2);

    (* find model for the constraints above *)
    if Z3_solver_check(ctx, s) = Z3_L_TRUE then
    begin
        var x_plus_y : Z3_ast;
        var v        : Z3_ast ;
        args[0] := x;
        args[1] := y;
        m := Z3_solver_get_model(ctx, s);
        // inc ref
	      if m <> nil then
          Z3_model_inc_ref(ctx, m);
        reLog.Lines.Append(Format('MODEL:' + sLineBreak+ '%s', [Z3_model_to_string(ctx, m)]));
        x_plus_y := Z3_mk_add(ctx, 2, @args[0]);
        reLog.Lines.Append(sLineBreak + 'evaluating x+y');
        if Z3_model_eval(ctx, m, x_plus_y, True, @v) then
        begin
            reLog.Lines.Append('result = ' +  display_ast(ctx, v));
        end else
        begin
            exitf('failed to evaluate: x+y');
        end;
    end else
    begin
        exitf('the constraints are satisfiable');
    end;
    // dec ref
    if m <> nil then
      Z3_model_dec_ref(ctx, m);
    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

(**
   \brief Several logical context can be used simultaneously.
*)
procedure TMain.two_contexts_example1;
var
  ctx1, ctx2 : Z3_context;
  x1, x2     : Z3_ast ;
begin
    reLog.Lines.Append(sLineBreak+ 'two_contexts_example1');
    LOG_MSG('two_contexts_example1');

    (* using the same (default) configuration to initialized both logical contexts. *)
    ctx1 := mk_context();
    ctx2 := mk_context();

    x1 := Z3_mk_const(ctx1, Z3_mk_int_symbol(ctx1,0), Z3_mk_bool_sort(ctx1));
    x2 := Z3_mk_const(ctx2, Z3_mk_int_symbol(ctx2,0), Z3_mk_bool_sort(ctx2));

    Z3_del_context(ctx1);

    (* ctx2 can still be used. *)
    reLog.Lines.Append(Format('%s', [Z3_ast_to_string(ctx2, x2)]));

    Z3_del_context(ctx2);
end;

(**
   \brief Demonstrates how error codes can be read instead of registering an error handler.
 *)
procedure TMain.error_code_example1;
var
  cfg : Z3_config;
  ctx : Z3_context;
  s   : Z3_solver;
  x   : Z3_ast;
  m   : Z3_model;
  v   : Z3_ast;
  x_decl : Z3_func_decl;
  str  : AnsiString;
begin

    reLog.Lines.Append(sLineBreak+ 'error_code_example1');
    LOG_MSG('error_code_example1');

    (* Do not register an error handler, as we want to use Z3_get_error_code manually *)
    cfg := Z3_mk_config;
    ctx := mk_context_custom(cfg, nil);
    Z3_del_config(cfg);
    s := mk_solver(ctx);

    x          := mk_bool_var(ctx, 'x');
    x_decl     := Z3_get_app_decl(ctx, Z3_to_app(ctx, x));
    Z3_solver_assert(ctx, s, x);

    if (Z3_solver_check(ctx, s) <> Z3_L_TRUE) then
        exitf('unexpected result');

    m := Z3_solver_get_model(ctx, s);
    // inc ref
    if m <> nil  then
      Z3_model_inc_ref(ctx, m);
    if not Z3_model_eval(ctx, m, x, True, @v)  then
        exitf('did not obtain value for declaration.');

    if (Z3_get_error_code(ctx) = Z3_OK) then
        reLog.Lines.Append('last call succeeded.');

    (* The following call will fail since the value of x is a boolean *)
    str := Z3_get_numeral_string(ctx, v);
    if (Z3_get_error_code(ctx) <> Z3_OK) then
        reLog.Lines.Append('last call failed.');

    // dec ref
    if m <> nil then
      Z3_model_dec_ref(ctx, m);
    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

(**
   \brief Demonstrates how error handlers can be used.
*)
procedure TMain.error_code_example2;
var
  cfg : Z3_config;
  ctx : Z3_context;
  e   : Z3_error_code;
  l   : Boolean;
label
    err  ;
begin
    reLog.Lines.Append(sLineBreak+ 'error_code_example2');
    LOG_MSG('error_code_example2');

    ctx := nil;

    l := True;

    if l then
    begin
        var x, y, app : Z3_ast;

        cfg := Z3_mk_config();
        ctx := mk_context_custom(cfg, nothrow_z3_error);
        Z3_del_config(cfg);

        x   := mk_int_var(ctx, 'x');
        y   := mk_bool_var(ctx, 'y');
        reLog.Lines.Append('before Z3_mk_iff');
        (* the next call will produce an error *)
        app := Z3_mk_iff(ctx, x, y);
        e   := Z3_get_error_code(ctx);

        if e <> Z3_OK  then goto err;

        unreachable;
        Z3_del_context(ctx);
    end else
    begin
    err:
        reLog.Lines.Append(Format('Z3 error: %s.', [Z3_get_error_msg(ctx, e)]));
        if ctx <> nil then
            Z3_del_context(ctx);
    end;
end;

(**
   \brief Demonstrates how to initialize the parser symbol table.
 *)
procedure TMain.parser_example2;
var
  x, y : Z3_ast;
  names: array[0..1] of Z3_symbol ;
  decls: array[0..2] of Z3_func_decl;
  f    : Z3_ast_vector;
  i    : Cardinal;
begin
    var ctx : Z3_context := mk_context;
    var s   : Z3_solver  := mk_solver(ctx);

    reLog.Lines.Append(sLineBreak+ 'parser_example2');
    LOG_MSG('parser_example2');

    (* Z3_enable_arithmetic doesn't need to be invoked in this example
       because it will be implicitly invoked by mk_int_var.
    *)

    x        := mk_int_var(ctx, 'x');
    decls[0] := Z3_get_app_decl(ctx, Z3_to_app(ctx, x));
    y        := mk_int_var(ctx, 'y');
    decls[1] := Z3_get_app_decl(ctx, Z3_to_app(ctx, y));

    names[0] := Z3_mk_string_symbol(ctx, 'a');
    names[1] := Z3_mk_string_symbol(ctx, 'b');

    f := Z3_parse_smtlib2_string(ctx,
                           '(assert (> a b))',
                           0, 0, 0,
                           (* 'x' and 'y' declarations are inserted as 'a' and 'b' into the parser symbol table. *)
                           2, @names[0], @decls[0]);
    reLog.Lines.Append(Format('formula: %s', [Z3_ast_vector_to_string(ctx, f)]));
    reLog.Lines.Append(Format('assert axiom:'+ sLineBreak +'%s', [Z3_ast_vector_to_string(ctx, f)]));
    for i := 0 to Z3_ast_vector_size(ctx, f) -1 do
        Z3_solver_assert(ctx, s, Z3_ast_vector_get(ctx, f, i));

    check(ctx, s, Z3_L_TRUE);

    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

(**
   \brief Demonstrates how to initialize the parser symbol table.
 *)
procedure TMain.parser_example3;
var
  cfg     : Z3_config;
  ctx     : Z3_context;
  s       : Z3_solver;
  int_sort: Z3_sort;
  g_name  : Z3_symbol;
  g_domain: array[0..1] of Z3_sort;
  g       : Z3_func_decl;
  thm     : Z3_ast_vector;
begin
    reLog.Lines.Append(sLineBreak+ 'parser_example3');
    LOG_MSG('parser_example3');

    cfg := Z3_mk_config();
    (* See quantifier_example1 *)
    Z3_set_param_value(cfg, 'model', 'true');
    ctx := mk_context_custom(cfg, error_handler);
    Z3_del_config(cfg);
    s := mk_solver(ctx);

    (* declare function g *)
    int_sort    := Z3_mk_int_sort(ctx);
    g_name      := Z3_mk_string_symbol(ctx, 'g');
    g_domain[0] := int_sort;
    g_domain[1] := int_sort;
    g           := Z3_mk_func_decl(ctx, g_name, 2, @g_domain[0], int_sort);

    assert_comm_axiom(ctx, s, g);

    thm := Z3_parse_smtlib2_string(ctx,
                           '(assert (forall ((x Int) (y Int)) (=> (= x y) (= (g x 0) (g 0 y)))))',
                           0, 0, 0,
                           1, @g_name, @g);
    reLog.Lines.Append(Format('formula: %s', [Z3_ast_vector_to_string(ctx, thm)]));
    prove(ctx, s, Z3_ast_vector_get(ctx, thm, 0), true);

    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

(**
   \brief Demonstrates how to handle parser errors using Z3 error handling support.
*)
procedure TMain.parser_example5;
var
  cfg     : Z3_config;
  ctx     : Z3_context;
  s       : Z3_solver;
  e       : Z3_error_code;
  l   : Boolean;
label
    err  ;
begin
    reLog.Lines.Append(sLineBreak+ 'parser_example5');
    LOG_MSG('parser_example5');

    ctx := nil;
    s   := nil;

    l := True;

    if l then
    begin
        cfg := Z3_mk_config();
        ctx := mk_context_custom(cfg, nothrow_z3_error);
        s   := mk_solver(ctx);
        Z3_del_config(cfg);

        Z3_parse_smtlib2_string(ctx,
                               (* the following string has a parsing error: missing parenthesis *)
                               '(declare-const x Int) declare-const y Int) (assert (and (> x y) (> x 0)))',
                               0, 0, 0,
                               0, 0, 0);
        e := Z3_get_error_code(ctx);
        if e <> Z3_OK then
           goto err;
        unreachable;
	      del_solver(ctx, s);
        Z3_del_context(ctx);
    end else
    begin
    err:
        reLog.Lines.Append(Format('Z3 error: %s.', [Z3_get_error_msg(ctx, e)]));
        if ctx <> nil then
        begin
	          del_solver(ctx, s);
            Z3_del_context(ctx);
        end;
    end;
end;

(**
    \brief Demonstrate different ways of creating rational numbers: decimal and fractional representations.
*)
procedure TMain.numeral_example;
var
  ctx     : Z3_context;
  s       : Z3_solver;
  n1, n2  : Z3_ast;
  real_ty : Z3_sort;
begin
    reLog.Lines.Append(sLineBreak+ 'numeral_example');
    LOG_MSG('numeral_example');

    ctx        := mk_context();
    s          := mk_solver(ctx);

    real_ty    := Z3_mk_real_sort(ctx);

    n1 := Z3_mk_numeral(ctx, '1/2', real_ty);
    n2 := Z3_mk_numeral(ctx, '0.5', real_ty);
    reLog.Lines.Append(Format('Numerals n1:%s n2:%s', [Z3_ast_to_string(ctx, n1), Z3_ast_to_string(ctx, n2)]));
    prove(ctx, s, Z3_mk_eq(ctx, n1, n2), true);

    n1 := Z3_mk_numeral(ctx, '-1/3', real_ty);
    n2 := Z3_mk_numeral(ctx, '-0.33333333333333333333333333333333333333333333333333', real_ty);
    reLog.Lines.Append(Format('Numerals n1:%s n2:%s', [string(Z3_ast_to_string(ctx, n1)), Z3_ast_to_string(ctx, n2)]));
    prove(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, n1, n2)), true);

    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

(**
   \brief Test ite-term (if-then-else terms).
*)
procedure TMain.ite_example;
var
  ctx               : Z3_context;
  f, one, zero, ite : Z3_ast;
begin
    reLog.Lines.Append(sLineBreak+ 'ite_example');
    LOG_MSG('ite_example');

    ctx := mk_context();

    f    := Z3_mk_false(ctx);
    one  := mk_int(ctx, 1);
    zero := mk_int(ctx, 0);
    ite  := Z3_mk_ite(ctx, f, one, zero);

    reLog.Lines.Append(Format('term: %s', [Z3_ast_to_string(ctx, ite)]));

    (* delete logical context *)
    Z3_del_context(ctx);
end;

(**
   \brief Create a list datatype.
*)
procedure TMain.list_example;
var
  int_ty, int_list   : Z3_sort;
  nil_decl,
  is_nil_decl,
  cons_decl,
  is_cons_decl,
  head_decl,
  tail_decl          : Z3_func_decl;
  &nil, l1, l2, x,
  y, u, v, fml, fml1 : Z3_ast;
  ors                : array[0..1] of Z3_ast;
begin
    reLog.Lines.Append(sLineBreak+ 'list_example');
    LOG_MSG('list_example');

    var  ctx : Z3_context := mk_context();
    var  s   : Z3_solver  := mk_solver(ctx);

    int_ty := Z3_mk_int_sort(ctx);

    int_list := Z3_mk_list_sort(ctx,
                                Z3_mk_string_symbol(ctx, 'int_list'),
                                int_ty,
                                @nil_decl,
                                @is_nil_decl,
                                @cons_decl,
                                @is_cons_decl,
                                @head_decl,
                                @tail_decl);

    &nil := Z3_mk_app(ctx, nil_decl, 0, 0);
    l1   := mk_binary_app(ctx, cons_decl, mk_int(ctx, 1), &nil);
    l2   := mk_binary_app(ctx, cons_decl, mk_int(ctx, 2), &nil);

    (* nil != cons(1, nil) *)
    prove(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, &nil, l1)), true);

    (* cons(2,nil) != cons(1, nil) *)
    prove(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, l1, l2)), true);

    (* cons(x,nil) = cons(y, nil) => x = y *)
    x := mk_var(ctx, 'x', int_ty);
    y := mk_var(ctx, 'y', int_ty);
    l1 := mk_binary_app(ctx, cons_decl, x, &nil);
	  l2 := mk_binary_app(ctx, cons_decl, y, &nil);
    prove(ctx, s, Z3_mk_implies(ctx, Z3_mk_eq(ctx,l1,l2), Z3_mk_eq(ctx, x, y)), true);

    (* cons(x,u) = cons(x, v) => u = v *)
    u := mk_var(ctx, 'u', int_list);
    v := mk_var(ctx, 'v', int_list);
    l1:= mk_binary_app(ctx, cons_decl, x, u);
	  l2:= mk_binary_app(ctx, cons_decl, y, v);
    prove(ctx, s, Z3_mk_implies(ctx, Z3_mk_eq(ctx,l1,l2), Z3_mk_eq(ctx, u, v)), true);
    prove(ctx, s, Z3_mk_implies(ctx, Z3_mk_eq(ctx,l1,l2), Z3_mk_eq(ctx, x, y)), true);

    (* is_nil(u) or is_cons(u) *)
    ors[0] := Z3_mk_app(ctx, is_nil_decl, 1, @u);
    ors[1] := Z3_mk_app(ctx, is_cons_decl, 1, @u);
    prove(ctx, s, Z3_mk_or(ctx, 2, @ors[0]), true);

    (* occurs check u != cons(x,u) *)
    prove(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, u, l1)), true);

    (* destructors: is_cons(u) => u = cons(head(u),tail(u)) *)
    fml1 := Z3_mk_eq(ctx, u, mk_binary_app(ctx, cons_decl, mk_unary_app(ctx, head_decl, u), mk_unary_app(ctx, tail_decl, u)));
    fml  := Z3_mk_implies(ctx, Z3_mk_app(ctx, is_cons_decl, 1, @u), fml1);
    reLog.Lines.Append(Format('Formula %s', [Z3_ast_to_string(ctx, fml)]));
    prove(ctx, s, fml, true);

    prove(ctx, s, fml1, false);

    (* delete logical context *)
    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

(**
   \brief Create a binary tree datatype.
*)
procedure TMain.tree_example;
var
  cell                     : Z3_sort;
  nil_decl, is_nil_decl,
  cons_decl, is_cons_decl,
  car_decl, cdr_decl       : Z3_func_decl;
  &nil, l1, l2, x, y,
  u, v, fml, fml1          : Z3_ast;
  head_tail                : array of Z3_symbol  ;
  sorts                    : array of Z3_sort;
  sort_refs                : array of Cardinal;
  nil_con, cons_con        : Z3_constructor;
  constructors             : array[0..1] of Z3_constructor;
  cons_accessors           : array[0..1] of Z3_func_decl;
  ors                      : array[0..1] of Z3_ast;
begin
    reLog.Lines.Append(sLineBreak+ 'tree_example');
    LOG_MSG('tree_example');

    var ctx : Z3_context := mk_context();
    var s   : Z3_solver  := mk_solver(ctx);

    head_tail := [ Z3_mk_string_symbol(ctx, 'car'), Z3_mk_string_symbol(ctx, 'cdr') ];
    sorts     := [ 0, 0 ];
    sort_refs := [ 0, 0 ];

    nil_con  := Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, 'nil'), Z3_mk_string_symbol(ctx, 'is_nil'), 0, 0, 0, 0);
    cons_con := Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, 'cons'), Z3_mk_string_symbol(ctx, 'is_cons'), 2, @head_tail[0], @sorts[0], @sort_refs[0]);
    constructors[0] := nil_con;
    constructors[1] := cons_con;

    cell := Z3_mk_datatype(ctx, Z3_mk_string_symbol(ctx, 'cell'), 2, @constructors[0]);

    Z3_query_constructor(ctx, nil_con, 0, @nil_decl, @is_nil_decl, 0);
    Z3_query_constructor(ctx, cons_con, 2, @cons_decl, @is_cons_decl, @cons_accessors[0]);
    car_decl := cons_accessors[0];
    cdr_decl := cons_accessors[1];

    Z3_del_constructor(ctx,nil_con);
    Z3_del_constructor(ctx,cons_con);


    &nil := Z3_mk_app(ctx, nil_decl, 0, 0);
    l1   := mk_binary_app(ctx, cons_decl, &nil, &nil);
    l2   := mk_binary_app(ctx, cons_decl, l1, &nil);

    (* nil != cons(nil, nil) *)
    prove(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, &nil, l1)), true);

    (* cons(x,u) = cons(x, v) => u = v *)
    u  := mk_var(ctx, 'u', cell);
    v  := mk_var(ctx, 'v', cell);
    x  := mk_var(ctx, 'x', cell);
    y  := mk_var(ctx, 'y', cell);
    l1 := mk_binary_app(ctx, cons_decl, x, u);
    l2 := mk_binary_app(ctx, cons_decl, y, v);
    prove(ctx, s, Z3_mk_implies(ctx, Z3_mk_eq(ctx,l1,l2), Z3_mk_eq(ctx, u, v)), true);
    prove(ctx, s, Z3_mk_implies(ctx, Z3_mk_eq(ctx,l1,l2), Z3_mk_eq(ctx, x, y)), true);

    (* is_nil(u) or is_cons(u) *)
    ors[0] := Z3_mk_app(ctx, is_nil_decl,  1, @u);
    ors[1] := Z3_mk_app(ctx, is_cons_decl, 1, @u);
    prove(ctx, s, Z3_mk_or(ctx, 2, @ors[0]), true);

    (* occurs check u != cons(x,u) *)
    prove(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, u, l1)), true);

    (* destructors: is_cons(u) => u = cons(car(u),cdr(u)) *)
    fml1 := Z3_mk_eq(ctx, u, mk_binary_app(ctx, cons_decl, mk_unary_app(ctx, car_decl, u), mk_unary_app(ctx, cdr_decl, u)));
    fml  := Z3_mk_implies(ctx, Z3_mk_app(ctx, is_cons_decl, 1, @u), fml1);
    reLog.Lines.Append(Format('Formula %s', [Z3_ast_to_string(ctx, fml)]));
    prove(ctx, s, fml, true);

    prove(ctx, s, fml1, false);

    (* delete logical context *)
    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

(**
   \brief Create a forest of trees.

   forest ::= nil | cons(tree, forest)
   tree   ::= nil | cons(forest, forest)
*)

procedure TMain.forest_example;
var
  tree, forest               : Z3_sort;
  nil1_decl, is_nil1_decl,
  cons1_decl, is_cons1_decl,
  car1_decl, cdr1_decl       : Z3_func_decl;
  nil2_decl, is_nil2_decl,
  cons2_decl, is_cons2_decl,
  car2_decl, cdr2_decl       : Z3_func_decl;
  nil1, nil2, t1, t2, t3,
  t4, f1, f2, f3, l1, l2,
  x, y, u, v                 : Z3_ast;
  head_tail                  : array of Z3_symbol;
  sorts                      : array of Z3_sort;
  sort_refs                  : array of Cardinal;
  sort_names                 : array of Z3_symbol;
  nil1_con, cons1_con,
  nil2_con, cons2_con        : Z3_constructor;
  constructors1,
  constructors2              : array[0..1] of Z3_constructor;
  cons_accessors             : array[0..1] of Z3_func_decl;
  ors                        : array[0..1] of Z3_ast;
  clists                     : array[0..1] of Z3_constructor_list;
  clist1, clist2             : Z3_constructor_list;

begin
    reLog.Lines.Append(sLineBreak+ 'forest_example');
    LOG_MSG('forest_example');

    var ctx : Z3_context := mk_context();
    var s   : Z3_solver  := mk_solver(ctx);

    head_tail  := [ Z3_mk_string_symbol(ctx, 'car'), Z3_mk_string_symbol(ctx, 'cdr') ];
    sorts      := [ 0, 0 ];
    sort_refs  := [ 0, 0 ];
    sort_names := [ Z3_mk_string_symbol(ctx, 'forest'), Z3_mk_string_symbol(ctx, 'tree') ];

    (* build a forest *)
    nil1_con         := Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, 'nil1'), Z3_mk_string_symbol(ctx, 'is_nil1'), 0, 0, 0, 0);
    sort_refs[0]     := 1; (* the car of a forest is a tree *)
    sort_refs[1]     := 0;
    cons1_con        := Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, 'cons1'), Z3_mk_string_symbol(ctx, 'is_cons1'), 2, @head_tail[0], @sorts[0], @sort_refs[0]);
    constructors1[0] := nil1_con;
    constructors1[1] := cons1_con;

    (* build a tree *)
    nil2_con         := Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, 'nil2'), Z3_mk_string_symbol(ctx, 'is_nil2'),0, 0, 0, 0);
    sort_refs[0]     := 0; (* both branches of a tree are forests *)
    sort_refs[1]     := 0;
    cons2_con        := Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, 'cons2'), Z3_mk_string_symbol(ctx, 'is_cons2'),2, @head_tail[0], @sorts[0], @sort_refs[0]);
    constructors2[0] := nil2_con;
    constructors2[1] := cons2_con;

    clist1 := Z3_mk_constructor_list(ctx, 2, @constructors1[0]);
    clist2 := Z3_mk_constructor_list(ctx, 2, @constructors2[0]);

    clists[0] := clist1;
    clists[1] := clist2;

    Z3_mk_datatypes(ctx, 2, @sort_names[0], @sorts[0], @clists[0]);
    forest := sorts[0];
    tree   := sorts[1];

    Z3_query_constructor(ctx, nil1_con, 0, @nil1_decl, @is_nil1_decl, 0);
    Z3_query_constructor(ctx, cons1_con, 2, @cons1_decl, @is_cons1_decl, @cons_accessors[0]);
    car1_decl := cons_accessors[0];
    cdr1_decl := cons_accessors[1];

    Z3_query_constructor(ctx, nil2_con, 0, @nil2_decl, @is_nil2_decl, 0);
    Z3_query_constructor(ctx, cons2_con, 2, @cons2_decl, @is_cons2_decl, @cons_accessors[0]);
    car2_decl := cons_accessors[0];
    cdr2_decl := cons_accessors[1];

    Z3_del_constructor_list(ctx, clist1);
    Z3_del_constructor_list(ctx, clist2);
    Z3_del_constructor(ctx,nil1_con);
    Z3_del_constructor(ctx,cons1_con);
    Z3_del_constructor(ctx,nil2_con);
    Z3_del_constructor(ctx,cons2_con);

    nil1 := Z3_mk_app(ctx, nil1_decl, 0, 0);
    nil2 := Z3_mk_app(ctx, nil2_decl, 0, 0);
    f1 := mk_binary_app(ctx, cons1_decl, nil2, nil1);
    t1 := mk_binary_app(ctx, cons2_decl, nil1, nil1);
    t2 := mk_binary_app(ctx, cons2_decl, f1, nil1);
    t3 := mk_binary_app(ctx, cons2_decl, f1, f1);
    t4 := mk_binary_app(ctx, cons2_decl, nil1, f1);
    f2 := mk_binary_app(ctx, cons1_decl, t1, nil1);
    f3 := mk_binary_app(ctx, cons1_decl, t1, f1);


    (* nil != cons(nil,nil) *)
    prove(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, nil1, f1)), true);
    prove(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, nil2, t1)), true);


    (* cons(x,u) = cons(x, v) => u = v *)
    u  := mk_var(ctx, 'u', forest);
    v  := mk_var(ctx, 'v', forest);
    x  := mk_var(ctx, 'x', tree);
    y  := mk_var(ctx, 'y', tree);
    l1 := mk_binary_app(ctx, cons1_decl, x, u);
    l2 := mk_binary_app(ctx, cons1_decl, y, v);
    prove(ctx, s, Z3_mk_implies(ctx, Z3_mk_eq(ctx,l1,l2), Z3_mk_eq(ctx, u, v)), true);
    prove(ctx, s, Z3_mk_implies(ctx, Z3_mk_eq(ctx,l1,l2), Z3_mk_eq(ctx, x, y)), true);

    (* is_nil(u) or is_cons(u) *)
    ors[0] := Z3_mk_app(ctx, is_nil1_decl, 1, @u);
    ors[1] := Z3_mk_app(ctx, is_cons1_decl, 1, @u);
    prove(ctx, s, Z3_mk_or(ctx, 2, @ors[0]), true);

    (* occurs check u != cons(x,u) *)
    prove(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, u, l1)), true);

    (* delete logical context *)
    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

(**
   \brief Create a binary tree datatype of the form
        BinTree ::=   nil
                    | node(value : Int, left : BinTree, right : BinTree)
*)
procedure TMain.binary_tree_example;
var
  cell             : Z3_sort;
  nil_con, node_con: Z3_constructor;
  nil_decl,                    (* nil : BinTree   (constructor) *)
  is_nil_decl,                 (* is_nil : BinTree -> Bool (tester, return true if the given BinTree is a nil) *)
  node_decl,                   (* node : Int, BinTree, BinTree -> BinTree  (constructor) *)
  is_node_decl,                (* is_node : BinTree -> Bool (tester, return true if the given BinTree is a node) *)
  value_decl,                  (* value : BinTree -> Int  (accessor for nodes) *)
  left_decl,                   (* left : BinTree -> BinTree (accessor for nodes, retrieves the left child of a node) *)
  right_decl   : Z3_func_decl; (* right : BinTree -> BinTree (accessor for nodes, retrieves the right child of a node) *)
  node_accessor_names     : array of Z3_symbol;
  node_accessor_sorts     : array of Z3_sort;
  node_accessor_sort_refs : array of Cardinal ;
  args1,args2,args3       : array of Z3_ast;
  constructors            : array[0..1]of Z3_constructor;
  node_accessors          : array[0..2]of Z3_func_decl;
begin
    reLog.Lines.Append(sLineBreak+ 'binary_tree_example');
    LOG_MSG('binary_tree_example');

    var ctx : Z3_context := mk_context();
    var s   : Z3_solver  := mk_solver(ctx);

    node_accessor_names    := [ Z3_mk_string_symbol(ctx, 'value'), Z3_mk_string_symbol(ctx, 'left'), Z3_mk_string_symbol(ctx, 'right') ];
    node_accessor_sorts    := [ Z3_mk_int_sort(ctx), 0, 0 ];
    node_accessor_sort_refs:= [ 0, 0, 0 ];

    (* nil_con and node_con are auxiliary datastructures used to create the new recursive datatype BinTree *)
    nil_con  := Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, 'nil'), Z3_mk_string_symbol(ctx, 'is-nil'), 0, 0, 0, 0);
    node_con := Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, 'node'), Z3_mk_string_symbol(ctx, 'is-cons'),
                                 3, @node_accessor_names[0], @node_accessor_sorts[0], @node_accessor_sort_refs[0]);
    constructors[0] := nil_con;
    constructors[1] := node_con;

    (* create the new recursive datatype *)
    cell := Z3_mk_datatype(ctx, Z3_mk_string_symbol(ctx, 'BinTree'), 2, @constructors[0]);

    (* retrieve the new declarations: constructors (nil_decl, node_decl), testers (is_nil_decl, is_cons_del), and
       accessors (value_decl, left_decl, right_decl *)
    Z3_query_constructor(ctx, nil_con, 0, @nil_decl, @is_nil_decl, 0);
    Z3_query_constructor(ctx, node_con, 3, @node_decl, @is_node_decl,@ node_accessors[0]);
    value_decl := node_accessors[0];
    left_decl  := node_accessors[1];
    right_decl := node_accessors[2];

    (* delete auxiliary/helper structures *)
    Z3_del_constructor(ctx, nil_con);
    Z3_del_constructor(ctx, node_con);

    (* small example using the recursive datatype BinTree *)
    begin
        (* create nil *)
        var &nil : Z3_ast := Z3_mk_app(ctx, nil_decl, 0, 0);
        (* create node1 ::= node(10, nil, nil) *)
        args1             := [ mk_int(ctx, 10), &nil, &nil ];
        var node1: Z3_ast := Z3_mk_app(ctx, node_decl, 3, @args1[0]);
        (* create node2 ::= node(30, node1, nil) *)
        args2             := [ mk_int(ctx, 30), node1, &nil ];
        var node2: Z3_ast := Z3_mk_app(ctx, node_decl, 3, @args2[0]);
        (* create node3 ::= node(20, node2, node1); *)
        args3             := [ mk_int(ctx, 20), node2, node1 ];
        var node3: Z3_ast := Z3_mk_app(ctx, node_decl, 3, @args3[0]);

        (* prove that nil != node1 *)
        prove(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, &nil, node1)), true);

        (* prove that nil = left(node1) *)
        prove(ctx, s, Z3_mk_eq(ctx, &nil, mk_unary_app(ctx, left_decl, node1)), true);

        (* prove that node1 = right(node3) *)
        prove(ctx, s, Z3_mk_eq(ctx, node1, mk_unary_app(ctx, right_decl, node3)), true);

        (* prove that !is-nil(node2) *)
        prove(ctx, s, Z3_mk_not(ctx, mk_unary_app(ctx, is_nil_decl, node2)), true);

        (* prove that value(node2) >= 0 *)
        prove(ctx, s, Z3_mk_ge(ctx, mk_unary_app(ctx, value_decl, node2), mk_int(ctx, 0)), true);
    end;

    (* delete logical context *)
    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

(**
   \brief Create an enumeration data type.
*)
procedure TMain.enum_example;
var
  fruit          : Z3_sort;
  enum_names     : array[0..2] of Z3_symbol;
  enum_consts    : array[0..2] of Z3_func_decl;
  enum_testers   : array[0..2] of Z3_func_decl;
  apple, orange,
  banana, fruity : Z3_ast;
  ors            : array[0..2] of Z3_ast;
begin
    reLog.Lines.Append(sLineBreak+ 'enum_example');
    LOG_MSG('enum_example');

    var ctx  : Z3_context := mk_context();
    var s    : Z3_solver  := mk_solver(ctx);
    var name : Z3_symbol  := Z3_mk_string_symbol(ctx, 'fruit');

    enum_names[0] := Z3_mk_string_symbol(ctx,'apple');
    enum_names[1] := Z3_mk_string_symbol(ctx,'banana');
    enum_names[2] := Z3_mk_string_symbol(ctx,'orange');

    fruit := Z3_mk_enumeration_sort(ctx, name, 3, @enum_names[0], @enum_consts[0], @enum_testers[0]);

    reLog.Lines.Append(Format('%s', [Z3_func_decl_to_string(ctx, enum_consts[0])]));
    reLog.Lines.Append(Format('%s', [Z3_func_decl_to_string(ctx, enum_consts[1])]));
    reLog.Lines.Append(Format('%s', [Z3_func_decl_to_string(ctx, enum_consts[2])]));

    reLog.Lines.Append(Format('%s', [Z3_func_decl_to_string(ctx, enum_testers[0])]));
    reLog.Lines.Append(Format('%s', [Z3_func_decl_to_string(ctx, enum_testers[1])]));
    reLog.Lines.Append(Format('%s', [Z3_func_decl_to_string(ctx, enum_testers[2])]));

    apple  := Z3_mk_app(ctx, enum_consts[0], 0, 0);
    banana := Z3_mk_app(ctx, enum_consts[1], 0, 0);
    orange := Z3_mk_app(ctx, enum_consts[2], 0, 0);

    (* Apples are different from oranges *)
    prove(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, apple, orange)), true);

    (* Apples pass the apple test *)
    prove(ctx, s, Z3_mk_app(ctx, enum_testers[0], 1, @apple), true);

    (* Oranges fail the apple test *)
    prove(ctx, s, Z3_mk_app(ctx, enum_testers[0], 1, @orange), false);
    prove(ctx, s, Z3_mk_not(ctx, Z3_mk_app(ctx, enum_testers[0], 1, @orange)), true);

    fruity := mk_var(ctx, 'fruity', fruit);

    (* If something is fruity, then it is an apple, banana, or orange *)
    ors[0] := Z3_mk_eq(ctx, fruity, apple);
    ors[1] := Z3_mk_eq(ctx, fruity, banana);
    ors[2] := Z3_mk_eq(ctx, fruity, orange);

    prove(ctx, s, Z3_mk_or(ctx, 3, @ors[0]), true);

    (* delete logical context *)
    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

(**
   \brief Prove a theorem and extract, and print the proof.

   This example illustrates the use of #Z3_check_assumptions.
*)
procedure TMain.unsat_core_and_proof_example;
var
  ctx : Z3_context;
  s   : Z3_solver;
  assumptions : array of Z3_ast;
  args1,args2,
  args3       : array of Z3_ast;
  g1,g2,g3,g4 : array of Z3_ast;
  res         : Z3_lbool;
  proof       : Z3_ast;
  m           : Z3_model;
  i           : Cardinal ;
  core        : Z3_ast_vector ;
begin
    reLog.Lines.Append(sLineBreak+ 'unsat_core_and_proof_example');
    LOG_MSG('unsat_core_and_proof_example');

    ctx := mk_proof_context();
    s   := mk_solver(ctx);
    var pa : Z3_ast := mk_bool_var(ctx, 'PredA');
    var pb : Z3_ast := mk_bool_var(ctx, 'PredB');
    var pc : Z3_ast := mk_bool_var(ctx, 'PredC');
    var pd : Z3_ast := mk_bool_var(ctx, 'PredD');
    var p1 : Z3_ast := mk_bool_var(ctx, 'P1');
    var p2 : Z3_ast := mk_bool_var(ctx, 'P2');
    var p3 : Z3_ast := mk_bool_var(ctx, 'P3');
    var p4 : Z3_ast := mk_bool_var(ctx, 'P4');
    assumptions := [ Z3_mk_not(ctx, p1), Z3_mk_not(ctx, p2), Z3_mk_not(ctx, p3), Z3_mk_not(ctx, p4) ];

    args1           := [ pa, pb, pc ];
    var f1 : Z3_ast := Z3_mk_and(ctx, 3, @args1[0]);

    args2           := [ pa, Z3_mk_not(ctx, pb), pc ];
    var f2 : Z3_ast := Z3_mk_and(ctx, 3, @args2[0]);

    args3           := [ Z3_mk_not(ctx, pa), Z3_mk_not(ctx, pc) ];
    var f3 : Z3_ast := Z3_mk_or(ctx, 2, @args3[0]);
    var f4 : Z3_ast := pd;

    g1 := [ f1, p1 ];
    g2 := [ f2, p2 ];
    g3 := [ f3, p3 ];
    g4 := [ f4, p4 ];

    m  := 0;

    Z3_solver_assert(ctx, s, Z3_mk_or(ctx, 2, @g1[0]));
    Z3_solver_assert(ctx, s, Z3_mk_or(ctx, 2, @g2[0]));
    Z3_solver_assert(ctx, s, Z3_mk_or(ctx, 2, @g3[0]));
    Z3_solver_assert(ctx, s, Z3_mk_or(ctx, 2, @g4[0]));

    res := Z3_solver_check_assumptions(ctx, s, 4, @assumptions[0]);

    case res of
        Z3_L_FALSE: begin
          core  := Z3_solver_get_unsat_core(ctx, s);
          proof := Z3_solver_get_proof(ctx, s);
          reLog.Lines.Append('unsat');
          reLog.Lines.Append(Format('proof: %s', [string(Z3_ast_to_string(ctx, proof))]));

          reLog.Lines.Append('core:');
          for i := 0 to Z3_ast_vector_size(ctx, core) - 1do
            reLog.Lines.Append(Format('%s', [Z3_ast_to_string(ctx, Z3_ast_vector_get(ctx, core, i))]));

          reLog.Lines.Append('');
        end;
        Z3_L_UNDEF: begin
          reLog.Lines.Append('unknown');
          reLog.Lines.Append('potential model:');
          m := Z3_solver_get_model(ctx, s);
          if m <> nil then
             Z3_model_inc_ref(ctx, m);
          display_model(ctx,  m);
        end;
        Z3_L_TRUE: begin
          reLog.Lines.Append('sat');
          m := Z3_solver_get_model(ctx, s);
          if m <> nil then
            Z3_model_inc_ref(ctx, m);
          display_model(ctx, m);
       end;
    end;

    (* delete logical context *)
    if m <> nil then
       Z3_model_dec_ref(ctx, m);
    del_solver(ctx, s);
    Z3_del_context(ctx);
end;

procedure TMain.StartMain;
begin
    Z3_open_log('z3.log');
    reLog.Clear;

    reLog.Lines.Append(display_version);
    simple_example();
    demorgan();
    find_model_example1();
    find_model_example2();
    prove_example1();
    prove_example2();
    push_pop_example1();
    quantifier_example1();
    array_example1();
    array_example2();
    array_example3();
    tuple_example1();
    bitvector_example1();
    bitvector_example2();
    eval_example1();
    two_contexts_example1();
    error_code_example1();
    error_code_example2();
    parser_example2();
    parser_example3();
    parser_example5();
    numeral_example();
    ite_example();
    list_example();
    tree_example();
    forest_example();
    binary_tree_example();
    enum_example();
    unsat_core_and_proof_example();
   { incremental_example1();
    reference_counter_example();
    smt2parser_example();
    substitute_example();
    substitute_vars_example();
    fpa_example();
    mk_model_example();  }

    Z3_close_log;
end;

procedure TMain.btnStartClick(Sender: TObject);
begin
   StartMain
end;

end.
