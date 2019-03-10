{*******************************************************}
{                                                       }
{       Z3 Wrapper Class for Delphi                     }
{                                                       }
{       Unit and class for Z3 Solver                    }
{                                                       }
{       Copyright (C) 2019 Pigrecos(Max)                }
{       All rights reserved.                            }
{       MIT License                                     }
{*******************************************************}

unit Z3.Solver;

interface
 uses
   System.SysUtils,
   z3,
   z3_fpa,
   Z3.Func,
   Z3.Context,
   Z3.Par_Desc,
   Z3.Stats,
   Z3.Model,
   Z3.Arr,
   Z3.Def;

type
  simple = record
  end;

  translate = record
  end;

  TSolver = class(Z3Object)
       m_solver: Z3_solver;
       procedure  init(s: Z3_solver);
    public

        constructor Create(c: TContext); overload;
        constructor Create(c: TContext; Sm: simple); overload;
        constructor Create(c: TContext; s: Z3_solver); overload;
        constructor Create(c: TContext; logic: PAnsiChar); overload;
        constructor Create(c: TContext; const src: TSolver; tr : translate); overload;
        constructor Create(const s: TSolver); overload;
        destructor  Destroy;

        function ToZ3_solver:Z3_solver;
        function Assign(const s: TSolver):TSolver;
        procedure &set(const p: TParams); overload;
        procedure &set(const k: PAnsiChar; v: Boolean);overload;
        procedure &set(const k: PAnsiChar; v: Cardinal);overload;
        procedure &set(const k: PAnsiChar; v: Double); overload;
        procedure &set(const k: PAnsiChar; const v: TSymbol); overload;
        procedure &set(const k: PAnsiChar; const v: PAnsiChar);overload;
        procedure push;
        procedure pop(n : Cardinal = 1);
        procedure reset;
        procedure add(const e: TExpr); overload;
        procedure add(const e: TExpr; const p: TExpr); overload;
        procedure add(const e: TExpr; const p: PAnsiChar); overload;
        // fails for some compilers:
        // void add(expr_vector const& v) { check_context(*this, v); for (expr e : v) add(e); }
        procedure from_file(ffile: PAnsiChar);
        procedure from_string(s: PAnsiChar);

        function check: check_result; overload;
        function check(n: Cardinal; const assumptions: array of TExpr): check_result; overload;
        function check(assumptions: TExpr_vector):check_result ;  overload;
        function get_model: TModel;
        function consequences(assumptions: TExpr_vector; vars: TExpr_vector; conseq: TExpr_vector):check_result;
        function reason_unknown: AnsiString;
        function statistics: TStats;
        function unsat_core: TExpr_vector;
        function assertions: TExpr_vector;
        function non_units:  TExpr_vector;
        function units: TExpr_vector;
        function trail: TExpr_vector; overload;
        function trail(levels: TZ3Array<Cardinal>): TExpr_vector ; overload;
        function proof: TExpr;
        function ToStr(const s: TSolver): AnsiString;overload;
        function ToStr: AnsiString;overload;
        function to_smt2(status : AnsiString = 'unknown' ): AnsiString;
        function dimacs: AnsiString;
        function get_param_descrs: TParam_descrs;
        function cube(vars: TExpr_vector; cutoff: Cardinal): TExpr_vector ;
  end;


implementation

{ TSolver }

constructor TSolver.Create(c: TContext);
begin
   inherited Create(c);
   init(Z3_mk_solver(c.ToZ3_Context))
end;

constructor TSolver.Create(c: TContext; Sm: simple);
begin
    inherited Create(c);
    init(Z3_mk_simple_solver(c.ToZ3_Context))
end;

constructor TSolver.Create(c: TContext; logic: PAnsiChar);
begin
   inherited Create(c);
   init( Z3_mk_solver_for_logic(c.ToZ3_Context, c.str_symbol(logic)) );
end;

constructor TSolver.Create(c: TContext; const src: TSolver; tr: translate);
begin
   inherited Create(c);
   init(Z3_solver_translate(src.ctx.ToZ3_Context, src.ToZ3_solver, c))
end;

constructor TSolver.Create(c: TContext; s: Z3_solver);
begin
   inherited Create(c);
   init(s)
end;

constructor TSolver.Create(const s: TSolver);
begin
   inherited Create(s);
   init(s.m_solver)
end;

destructor TSolver.Destroy;
begin
   Z3_solver_dec_ref(ctx.ToZ3_Context, m_solver)
end;

procedure TSolver.init(s: Z3_solver);
begin
   m_solver := s;
   Z3_solver_inc_ref(ctx.ToZ3_Context, s)
end;

procedure TSolver.add(const e: TExpr);
begin
    assert(e.is_bool);
    Z3_solver_assert(ctx.ToZ3_Context, m_solver, e.ToZ3_ast);
    check_error;
end;

procedure TSolver.add(const e, p: TExpr);
begin
  assert(e.is_bool);
  assert(p.is_bool);
  assert(p.is_const);
  Z3_solver_assert_and_track(ctx.ToZ3_Context, m_solver, e.ToZ3_ast, p.ToZ3_ast);
  check_error;

end;

procedure TSolver.add(const e: TExpr; const p: PAnsiChar);
begin
     add(e, ctx.bool_const(p));
end;

function TSolver.assertions: TExpr_vector;
begin
   var r : Z3_ast_vector := Z3_solver_get_assertions(ctx.ToZ3_Context, m_solver);
   check_error;
   Result := Texpr_vector.Create(ctx, r);
end;

function TSolver.Assign(const s: TSolver): TSolver;
begin
  Z3_solver_inc_ref(s.ctx.ToZ3_Context, s.m_solver);
  Z3_solver_dec_ref(ctx.ToZ3_Context, m_solver);
  m_ctx    := s.m_ctx;
  m_solver := s.m_solver;
  Result := Self
end;

function TSolver.check(assumptions: TExpr_vector): check_result;
var
  _assumptions : TZ3Array<Z3_ast>;
  n            : Cardinal;
  r            : Z3_lbool;
  i            : Integer;
begin
    n := assumptions.size();
    _assumptions := TZ3Array<Z3_ast>.Create(n);
    for i := 0 to  n - 1 do
    begin
        check_context(Self, assumptions.Items[i]);
        _assumptions.Items[i] := assumptions.Items[i];
    end;
    r := Z3_solver_check_assumptions(ctx.ToZ3_Context, m_solver, n, _assumptions.ptr);
    check_error;
    Result :=  to_check_result(r);
end;

function TSolver.check(n: Cardinal; const assumptions: array of TExpr): check_result;
var
  _assumptions : TZ3Array<Z3_ast>;
  r            : Z3_lbool;
  i            : Integer;
begin
   _assumptions := TZ3Array<Z3_ast>.Create(n);
   for i := 0 to n - 1 do
   begin
        check_context(Self, assumptions[i]);
        _assumptions.Items[i] := assumptions[i].ToZ3_ast;
   end;
   r := Z3_solver_check_assumptions(ctx.ToZ3_Context, m_solver, n, _assumptions.ptr);
   check_error;
   Result := to_check_result(r);

end;

function TSolver.check: check_result;
begin
    var r : Z3_lbool := Z3_solver_check(ctx.ToZ3_Context, m_solver);
    check_error;
    Result :=  to_check_result(r);
end;

function TSolver.consequences(assumptions, vars, conseq: TExpr_vector): check_result;
begin
  var r : Z3_lbool := Z3_solver_get_consequences(ctx.ToZ3_Context, m_solver, assumptions.ToZ3_ast_vector, vars.ToZ3_ast_vector, conseq.ToZ3_ast_vector);
  check_error;
  Result := to_check_result(r);

end;

function TSolver.reason_unknown: AnsiString;
begin
  var r : Z3_string := Z3_solver_get_reason_unknown(ctx.ToZ3_Context, m_solver);
  check_error;
  Result := AnsiString(r);
end;

function TSolver.statistics: TStats;
begin
    var r : Z3_stats := Z3_solver_get_statistics(ctx.ToZ3_Context, m_solver);
    check_error;
    Result := TStats.Create(ctx, r);
end;

function TSolver.cube(vars: TExpr_vector; cutoff: Cardinal): TExpr_vector;
begin
  var r : Z3_ast_vector := Z3_solver_cube(ctx.ToZ3_Context, m_solver, vars.ToZ3_ast_vector, cutoff);
  check_error;
  Result := TExpr_vector.Create(ctx, r);
end;

function TSolver.dimacs: AnsiString;
begin
    Result := AnsiString(Z3_solver_to_dimacs_string(ctx.ToZ3_Context, m_solver) );
end;

procedure TSolver.from_file(ffile: PAnsiChar);
begin
   Z3_solver_from_file(ctx.ToZ3_Context, m_solver, ffile);
   ctx.check_parser_error;
end;

procedure TSolver.from_string(s: PAnsiChar);
begin
   Z3_solver_from_string(ctx.ToZ3_Context, m_solver, s);
   ctx.check_parser_error;
end;

function TSolver.get_model: TModel;
begin
   var m : Z3_model := Z3_solver_get_model(ctx.ToZ3_Context, m_solver);
   check_error;
   Result := TModel.Create(ctx, m);
end;

function TSolver.get_param_descrs: TParam_descrs;
begin
   Result := TParam_descrs.Create( ctx, Z3_solver_get_param_descrs(ctx.ToZ3_Context, m_solver)  );
end;

function TSolver.non_units: TExpr_vector;
begin
    var r : Z3_ast_vector := Z3_solver_get_non_units(ctx.ToZ3_Context, m_solver);
    check_error;
    Result := TExpr_vector.Create(ctx, r);
end;

procedure TSolver.pop(n: Cardinal);
begin
    Z3_solver_pop(ctx.ToZ3_Context, m_solver, n);
    check_error;
end;

function TSolver.proof: TExpr;
begin
    var r : Z3_ast := Z3_solver_get_proof(ctx.ToZ3_Context, m_solver);
    check_error;
    Result := TExpr.Create(ctx, r);
end;

procedure TSolver.push;
begin
   Z3_solver_push(ctx.ToZ3_Context, m_solver);
   check_error;
end;

procedure TSolver.reset;
begin
    Z3_solver_reset(ctx.ToZ3_Context, m_solver);
    check_error;
end;

procedure TSolver.&set(const k: PAnsiChar; v: Cardinal);
var
  p : TParams;
begin
    p := TParams.Create(ctx);
    p.&set(k, v);
    &set(p);
end;

procedure TSolver.&set(const k: PAnsiChar; v: Double);
var
  p : TParams;
begin
    p := TParams.Create(ctx);
    p.&set(k, v);
    &set(p);
end;

procedure TSolver.&set(const k, v: PAnsiChar);
var
  p : TParams;
begin
    p := TParams.Create(ctx);
    p.&set(k, v);
    &set(p);
end;

procedure TSolver.&set(const k: PAnsiChar; const v: TSymbol);
var
  p : TParams;
begin
    p := TParams.Create(ctx);
    p.&set(k, v);
    &set(p);
end;

procedure TSolver.&set(const k: PAnsiChar; v: Boolean);
var
  p : TParams;
begin
    p := TParams.Create(ctx);
    p.&set(k, v);
    &set(p);
end;

procedure TSolver.&set(const p: TParams);
begin
    Z3_solver_set_params(ctx.ToZ3_Context, m_solver, p.ToZ3_params);
    check_error;
end;

function TSolver.ToStr: AnsiString;
begin
    Result := ToStr(Self);
end;

function TSolver.ToStr(const s: TSolver): AnsiString;
begin
    Result := AnsiString (Z3_solver_to_string(s.ctx.ToZ3_Context, s.ToZ3_solver));
end;

function TSolver.ToZ3_solver: Z3_solver;
begin
   Result := m_solver;
end;

function TSolver.to_smt2(status: AnsiString ): AnsiString;
var
  fml      : Z3_ast;
  fmls     : array of Z3_ast;
  sz       : Cardinal;
  es       : TZ3Array<Z3_ast>;
  i        : Integer;
begin
    es := assertions.ToArray;
    sz   := es.size;
    SetLength(fmls,sz);
    for i := 0 to sz - 1 do
      fmls[i] := es.ToBaseArray[i];


    if (Integer(sz) > 0) then
    begin
        Dec(sz);
        fml := fmls[sz];

    end else
    begin
        fml := ctx.bool_val(true);
    end;
    Result := Z3_benchmark_to_smtlib_string(
                                             ctx.ToZ3_Context,
                                             '',
                                             '',
                                             PAnsiChar(status),
                                             '',
                                             sz,
                                             @fmls,
                                             fml);

end;

function TSolver.trail: TExpr_vector;
begin
   var r : Z3_ast_vector := Z3_solver_get_trail(ctx.ToZ3_Context, m_solver);
   check_error;
   Result := TExpr_vector.Create(ctx, r);
end;

function TSolver.trail(levels: TZ3Array<Cardinal>): TExpr_vector;
begin
  var r : Z3_ast_vector := Z3_solver_get_trail(ctx.ToZ3_Context, m_solver);
  check_error;
  Result := TExpr_vector.Create(ctx, r);
  var sz : Cardinal := result.size;
  levels.resize(sz);
  { TODO -oMax -c : Verivicare array o puntatore ad array 19/02/2019 18:48:16 }
  Z3_solver_get_levels(ctx.ToZ3_Context, m_solver, r, sz, levels.Ptr);
  check_error;
end;

function TSolver.units: TExpr_vector;
begin
   var r : Z3_ast_vector := Z3_solver_get_units(ctx.ToZ3_Context, m_solver);
   check_error;
   Result := TExpr_vector.Create(ctx, r);
end;

function TSolver.unsat_core: TExpr_vector;
begin
   var r : Z3_ast_vector := Z3_solver_get_unsat_core(ctx.ToZ3_Context, m_solver);
   check_error;
   Result := TExpr_vector.Create(ctx, r);
end;

end.
