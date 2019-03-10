{*******************************************************}
{                                                       }
{       Z3 Wrapper Class for Delphi                     }
{                                                       }
{       Unit and class for  Z3_goal                     }
{                           Z3_apply_result,            }
{                           Z3_tactic                   }
{                                                       }
{       Copyright (C) 2019 Pigrecos(Max)                }
{       All rights reserved.                            }
{       MIT License                                     }
{*******************************************************}

unit Z3.Tactic;

interface
  uses
     System.SysUtils,
     z3,
     Z3.Def,
     Z3.Context,
     Z3.Par_Desc,
     Z3.Arr,
     Z3.Model,
     Z3.Solver;
type

  TGoal = class(Z3Object)
     m_goal: Z3_goal;

     procedure Init(s: Z3_goal);
  private
    function GetExp(index: Cardinal): TExpr;
  public
    constructor Create (c: TContext;models: Boolean = true; unsat_cores: Boolean = false; proofs: Boolean =false); overload;
    constructor Create(c: TContext; s: Z3_goal); overload;
    constructor Create(const s: TGoal);   overload;
    destructor Destroy; override;

    function   ToZ3_Goal: Z3_goal;
    function   Assign(const s: TGoal):TGoal;
    procedure  add(const f: TExpr);
    function   size: Cardinal;
    function   precision: Z3_goal_prec;
    function   inconsistent: Boolean;
    function   depth: Cardinal;
    procedure  reset;
    function   num_exprs: Cardinal;
    function   is_decided_sat: Boolean;
    function   is_decided_unsat: Boolean;
    function   convert_model(const m: TModel): TModel;
    function   get_model: TModel;
    function   as_expr: TExpr;
    function   dimacs: AnsiString;
    function   ToStr(g: TGoal):AnsiString; overload;
    function   ToStr:AnsiString; overload;

    property Items[index: Cardinal] :TExpr read GetExp;

  end;

  TApply_result = class(Z3Object)
    m_apply_result : Z3_apply_result;
    procedure Init(s: Z3_apply_result);
  private
    function GetGoal(index: Cardinal): TGoal;

  public
    constructor Create(c: TContext; s: Z3_apply_result);overload;
    constructor Create(const s: TApply_result); overload;
    destructor Destroy; override;

    function   ToZ3_apply: Z3_apply_result;
    function   Assign(const s: TApply_result):TApply_result;
    function   size: Cardinal ;
    function   ToStr(r: TApply_result ): AnsiString; overload;
    function   ToStr: AnsiString; overload;

    property Items[index: Cardinal] :TGoal read GetGoal;
  end;

  TTactic = class(Z3Object)
     m_tactic : Z3_tactic;
     procedure Init(s: Z3_tactic);
  public
    constructor Create(c: TContext; name: PAnsiChar);overload;
    constructor Create(c: TContext; s: Z3_tactic); overload;
    constructor Create(const s: TTactic);overload;
    destructor Destroy; override;

    function   ToZ3_tactic: Z3_tactic;
    function   Assign(const s: TTactic):TTactic;
    function   mk_solver: TSolver;
    function   apply(const g: TGoal): TApply_result;
    function   ToApplyRes(const g: TGoal): TApply_result;
    function   help: AnsiString;
  end;

  // for TTactic
  function   T_OpAnd(const t1: TTactic;const t2: TTactic): TTactic;
  function   T_OpOr(const  t1: TTactic; const t2: TTactic): TTactic;
  function   &repeat(const t : TTactic; max: Cardinal=SizeOf(Cardinal)): TTactic;
  function   &with(const   t : TTactic; const p: TParams): TTactic;
  function   try_for(const t : TTactic; ms: Cardinal): TTactic;
  function   par_or(n: Cardinal; const tactics: TArray<TTactic>): TTactic;
  function   par_and_then(const t1: TTactic; const t2: TTactic): TTactic;
  function   get_param_descrs(t :TTactic): TParam_descrs;


implementation
    uses Z3.Func;

function T_OpAnd(const t1, t2: TTactic): TTactic;
begin
    check_context(t1, t2);
    var r : Z3_tactic := Z3_tactic_and_then(t1.ctx.ToZ3_Context, t1.ToZ3_tactic, t2.ToZ3_tactic);
    t1.check_error;
    Result := TTactic.Create(t1.ctx, r);
end;

function T_OpOr(const t1, t2: TTactic): TTactic;
begin
    check_context(t1, t2);
    var r : Z3_tactic := Z3_tactic_or_else(t1.ctx.ToZ3_Context, t1.ToZ3_tactic, t2.ToZ3_tactic);
    t1.check_error;
    Result := TTactic.Create(t1.ctx, r);
end;

function &repeat(const t: TTactic; max: Cardinal= SizeOf(Cardinal)): TTactic;
begin
   var r : Z3_tactic := Z3_tactic_repeat(t.ctx.ToZ3_Context, t.ToZ3_tactic, max);
   t.check_error;
   Result := TTactic.Create(t.ctx, r);
end;

function &with(const t: TTactic; const p: TParams): TTactic;
begin
  var r : Z3_tactic := Z3_tactic_using_params(t.ctx.ToZ3_Context, t.ToZ3_tactic, p.ToZ3_params);
  t.check_error;
  Result := TTactic.Create(t.ctx, r);
end;

function try_for(const t: TTactic; ms: Cardinal): TTactic;
begin
    var r : Z3_tactic := Z3_tactic_try_for(t.ctx.ToZ3_Context, t.ToZ3_tactic, ms);
    t.check_error;
    Result := TTactic.Create(t.ctx, r)
end;

function par_or(n: Cardinal; const tactics: TArray<TTactic>): TTactic;
begin
    if (n = 0) then
        raise TZ3Exception.Create('a non-zero number of tactics need to be passed to par_or');

    var buffer : TZ3Array<Z3_tactic> :=  TZ3Array<Z3_tactic>.Create(n);
    var i : Integer;
    for i := 0 to n-1 do
      buffer.Items[i] := tactics[i].ToZ3_tactic;

    Result := TTactic.Create( tactics[0].ctx.ToZ3_Context, Z3_tactic_par_or(tactics[0].ctx.ToZ3_Context, n, buffer.ptr) );
end;

function par_and_then(const t1, t2: TTactic): TTactic;
begin
   check_context(t1, t2);
   var r : Z3_tactic := Z3_tactic_par_and_then(t1.ctx.ToZ3_Context, t1.ToZ3_tactic, t2.ToZ3_tactic);
   t1.check_error;
   Result := TTactic.Create(t1.ctx, r);
end;

function get_param_descrs(t :TTactic): TParam_descrs;
begin
    Result := TParam_Descrs.Create(t.ctx, Z3_tactic_get_param_descrs(t.ctx.ToZ3_Context, t.m_tactic)  );
end;

{ TGoal }

constructor TGoal.Create(const s: TGoal);
begin
    inherited Create(s);
    init(s.m_goal);
end;

constructor TGoal.Create(c: TContext; s: Z3_goal);
begin
   inherited Create(c);
   init(s);
end;

constructor TGoal.Create(c: TContext; models, unsat_cores, proofs: Boolean);
begin
    inherited Create(c);
    init(Z3_mk_goal(c.ToZ3_Context, models, unsat_cores, proofs));
end;

destructor TGoal.Destroy;
begin
  Z3_goal_dec_ref(ctx.ToZ3_Context, m_goal);
  inherited;
end;

function TGoal.ToZ3_Goal: Z3_goal;
begin
    Result := m_goal
end;

function TGoal.Assign(const s: TGoal): TGoal;
begin
    Z3_goal_inc_ref(s.ctx.ToZ3_Context, s.m_goal);
    Z3_goal_dec_ref(ctx.ToZ3_Context, m_goal);
    m_ctx := s.m_ctx;
    m_goal:= s.m_goal;
    Result := Self;
end;

procedure TGoal.Init(s: Z3_goal);
begin
    m_goal := s;
    Z3_goal_inc_ref(ctx.ToZ3_Context, s)
end;

procedure TGoal.add(const f: TExpr);
begin
   check_context(Self, f);
   Z3_goal_assert(ctx.ToZ3_Context, m_goal, f.ToZ3_ast);
   check_error;
end;

function TGoal.as_expr: TExpr;
begin
    var n : Cardinal := size;
    if n = 0 then
       Result := ctx.bool_val(True)
    else if n = 1 then
       Result := Items[0]
    else begin
         var args : TZ3Array<Z3_ast> := TZ3Array<Z3_ast>.Create(n);
         var i : Integer;
         for i := 0 to n - 1 do
           args.Items[i] := items[i].ToZ3_ast;

         Result := TExpr.Create(ctx,Z3_mk_and(ctx.ToZ3_Context,n,args.ptr));
    end;

end;

function TGoal.convert_model(const m: TModel): TModel;
begin
    check_context(Self, m);
    var new_m : Z3_model := Z3_goal_convert_model(ctx.ToZ3_Context, m_goal, m.ToZ3_model);
    check_error;
    Result := TModel.Create(ctx, new_m);
end;

function TGoal.depth: Cardinal;
begin
    Result :=  Z3_goal_depth(ctx.ToZ3_Context, m_goal)
end;

function TGoal.GetExp(index: Cardinal): TExpr;
begin
    assert(Integer(index) >= 0);
    var r : Z3_ast := Z3_goal_formula(ctx.ToZ3_Context, m_goal, index);
    check_error;
    Result := TExpr.Create(ctx, r);
end;

function TGoal.get_model: TModel;
begin
    var new_m : Z3_model := Z3_goal_convert_model(ctx.ToZ3_Context, m_goal, nil);
    check_error;
    Result := TModel.Create(ctx, new_m);
end;

function TGoal.inconsistent: Boolean;
begin
    Result := Z3_goal_inconsistent(ctx.ToZ3_Context, m_goal);
end;

function TGoal.is_decided_sat: Boolean;
begin
    Result :=  Z3_goal_is_decided_sat(ctx.ToZ3_Context, m_goal);
end;

function TGoal.is_decided_unsat: Boolean;
begin
    Result := Z3_goal_is_decided_unsat(ctx.ToZ3_Context, m_goal);
end;

function TGoal.num_exprs: Cardinal;
begin
   Result := Z3_goal_num_exprs(ctx.ToZ3_Context, m_goal);
end;

function TGoal.precision: Z3_goal_prec;
begin
   Result := Z3_goal_precision(ctx.ToZ3_Context, m_goal);
end;

procedure TGoal.reset;
begin
   Z3_goal_reset(ctx.ToZ3_Context, m_goal);
end;

function TGoal.size: Cardinal;
begin
   Result :=  Z3_goal_size(ctx.ToZ3_Context, m_goal);
end;

function TGoal.dimacs: AnsiString;
begin
   Result := AnsiString(Z3_goal_to_dimacs_string(ctx.ToZ3_Context, m_goal));
end;

function TGoal.ToStr(g: TGoal): AnsiString;
begin
   Result := AnsiString(Z3_goal_to_string(g.ctx.ToZ3_Context, g.ToZ3_Goal));
end;

function TGoal.ToStr: AnsiString;
begin
    Result := ToStr(Self);
end;


{ TApply_result }

constructor TApply_result.Create(c: TContext; s: Z3_apply_result);
begin
   inherited Create(c);
   init(s);
end;

constructor TApply_result.Create(const s: TApply_result);
begin
    inherited Create(s);
    init(s.m_apply_result);
end;

destructor TApply_result.Destroy;
begin
  Z3_apply_result_dec_ref(ctx.ToZ3_Context, m_apply_result);
  inherited;
end;

procedure TApply_result.Init(s: Z3_apply_result);
begin
   m_apply_result := s;
   Z3_apply_result_inc_ref(ctx.ToZ3_Context, s)
end;

function TApply_result.ToZ3_apply: Z3_apply_result;
begin
    Result := m_apply_result;
end;

function TApply_result.Assign(const s: TApply_result): TApply_result;
begin
    Z3_apply_result_inc_ref(s.ctx.ToZ3_Context, s.m_apply_result);
    Z3_apply_result_dec_ref(ctx.ToZ3_Context, m_apply_result);
    m_ctx          := s.m_ctx;
    m_apply_result := s.m_apply_result;
    Result         := Self;
end;

function TApply_result.GetGoal(index: Cardinal): TGoal;
begin
   assert(Integer(index) >= 0);
   var r : Z3_goal := Z3_apply_result_get_subgoal(ctx.ToZ3_Context, m_apply_result, index);
   check_error;
   Result := TGoal.Create(ctx, r);
end;

function TApply_result.size: Cardinal;
begin
  Result := Z3_apply_result_get_num_subgoals(ctx.ToZ3_Context, m_apply_result);
end;

function TApply_result.ToStr(r: TApply_result ): AnsiString;
begin
    Result := AnsiString(Z3_apply_result_to_string(r.ctx.ToZ3_Context, r.ToZ3_apply));
end;

function TApply_result.ToStr: AnsiString;
begin
    Result := ToStr(Self);
end;

{ TTactic }

constructor TTactic.Create(const s: TTactic);
begin
   inherited Create(s);
    init(s.m_tactic);
end;

constructor TTactic.Create(c: TContext; name: PAnsiChar);
begin
  inherited Create(c);
  var  r : Z3_tactic := Z3_mk_tactic(c.ToZ3_Context, name);
  check_error;
  init(r);
end;

constructor TTactic.Create(c: TContext; s: Z3_tactic);
begin
  inherited Create(c);
  init(s);
end;

destructor TTactic.Destroy;
begin
  Z3_tactic_dec_ref(ctx.ToZ3_Context, m_tactic);
  inherited;
end;

procedure TTactic.Init(s: Z3_tactic);
begin
   m_tactic := s;
   Z3_tactic_inc_ref(ctx.ToZ3_Context, s);
end;

function TTactic.Assign(const s: TTactic): TTactic;
begin
   Z3_tactic_inc_ref(s.ctx.ToZ3_Context, s.m_tactic);
   Z3_tactic_dec_ref(ctx.ToZ3_Context, m_tactic);
   m_ctx    := s.m_ctx;
   m_tactic := s.m_tactic;
   Result   := Self;
end;

function TTactic.ToZ3_tactic: Z3_tactic;
begin
    Result := m_tactic;
end;

function TTactic.ToApplyRes(const g: TGoal): TApply_result;
begin
   Result := apply(g)
end;

function TTactic.apply(const g: TGoal): TApply_result;
begin
    check_context(Self, g);
    var r : Z3_apply_result := Z3_tactic_apply(ctx.ToZ3_Context, m_tactic, g.ToZ3_Goal);
    check_error;
    Result := TApply_result.Create(ctx, r);
end;

function TTactic.help: AnsiString;
begin
    var r : AnsiString := AnsiString( Z3_tactic_get_help(ctx.ToZ3_Context, m_tactic) );
    check_error;
    Result := r;
end;

function TTactic.mk_solver: TSolver;
begin
    var r : Z3_solver := Z3_mk_solver_from_tactic(ctx.ToZ3_Context, m_tactic);
    check_error;
    Result := TSolver.Create(ctx, r);
end;

end.
