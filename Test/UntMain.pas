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
    { Private declarations }
  public
    { Public declarations }
  end;

var
  Main: TMain;

implementation


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


procedure throw_z3_error(c : Z3_context; e: Z3_error_code) ;

begin
    var s : AnsiString := Format('Error code: %d',[ Ord(e) ])+ sLineBreak;
    exitf(s + 'longjmp');
end;


procedure nothrow_z3_error(c : Z3_context; e: Z3_error_code) ;

begin
    // no-op
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
     Z3_QUANTIFIER_AST: Result := Result +'quantifier' ;

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

    reLog.Lines.Append('');
    reLog.Lines.Append('array_example1');
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
   { array_example2();
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
    incremental_example1();
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
