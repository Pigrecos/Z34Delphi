{*******************************************************}
{                                                       }
{       Z3 Wrapper Class for Delphi                     }
{                                                       }
{       Unit and class for  Z3_func_entry,              }
{                           Z3_func_interp              }
{                           Z3_model                    }
{                                                       }
{       Copyright (C) 2019 Pigrecos(Max)                }
{       All rights reserved.                            }
{       MIT License                                     }
{*******************************************************}

unit Z3.Model;

interface
 uses
   System.SysUtils,
   z3,
   z3_fpa,
   Z3.Func,
   Z3.Context,
   Z3.Arr,
   Z3.Def;

type
   TFunc_entry = class(Z3Object)
       m_entry : Z3_func_entry;

       procedure init(e: Z3_func_entry);
    private
       function GetItem(Index: Cardinal): TExpr;
    public
        constructor Create(c: TContext; e: Z3_func_entry); overload;
        constructor Create(const s: TFunc_entry);  overload;
        destructor Destroy ;

        function ToZ3_func_entry:Z3_func_entry;
        function Assign(const s: TFunc_entry):TFunc_entry ;
        function value: TExpr;
        function num_args: Cardinal;

        property arg[Index: Cardinal]: TExpr read GetItem ;
   end;

   TFunc_interp = class(Z3Object)
        m_interp : Z3_func_interp;
        procedure init(e: Z3_func_interp);
    public
        constructor Create(c: TContext; e: Z3_func_interp);overload;
        constructor Create(const s: TFunc_interp); overload;
        destructor Destroy;
        function ToZ3_func_interp: Z3_func_interp;
        function Assign(const  s:TFunc_interp): TFunc_interp;

        function else_value: TExpr;
        function num_entries: Cardinal;
        function entry(i: Cardinal): TFunc_entry;
        procedure add_entry(const args: TExpr_vector; value: TExpr);
        procedure set_else(value: TExpr);
    end;

    translate = record
    end;

   TModel = class(Z3Object)
        m_model: Z3_model;
        procedure init(m: Z3_model);
    private
        function GetItem(Index: Cardinal): TFunc_decl;
    public
        constructor Create(c: TContext); overload;
        constructor Create(c: TContext; m: Z3_model); overload;
        constructor Create(const s: TModel);  overload;
        constructor Create(src: TModel; dst: TContext; tr: translate); overload;
        destructor Destroy;
        function ToZ3_model:Z3_model;
        function Assign(const s: TModel):TModel;
        function eval(const n: TExpr; model_completion: Boolean = false): TExpr;
        function num_consts: Cardinal;
        function num_funcs: Cardinal;
        function get_const_decl(i: Cardinal): TFunc_decl;
        function get_func_decl(i: Cardinal): TFunc_decl;
        function size: Cardinal;
        // returns interpretation of constant declaration c.
        // If c is not assigned any value in the model it returns
        // an expression with a null ast reference.
        function get_const_interp(c: TFunc_decl): TExpr;
        function get_func_interp(f: TFunc_decl): TFunc_interp;
        // returns true iff the model contains an interpretation
        // for function f.
        function has_interp(f: TFunc_decl): Boolean;
        function add_func_interp(f: TFunc_decl; else_val: TExpr): TFunc_interp;
        procedure add_const_interp(f: TFunc_decl; value: TExpr);
        function ToStr(m: TModel) : AnsiString;overload;
        function ToStr: AnsiString;overload;

        property Item[Index: Cardinal]: TFunc_decl read GetItem ;
   end;


implementation

{ TFunc_entry }

constructor TFunc_entry.Create(c: TContext; e: Z3_func_entry);
begin
    inherited Create(c);
    init(e);
end;

constructor TFunc_entry.Create(const s: TFunc_entry);
begin
   inherited Create(s);
   init(s.m_entry)
end;

destructor TFunc_entry.Destroy;
begin
     Z3_func_entry_dec_ref(ctx.ToZ3_Context, m_entry);

     inherited;
end;

procedure TFunc_entry.init(e: Z3_func_entry);
begin
    m_entry := e;
    Z3_func_entry_inc_ref(ctx.ToZ3_Context, m_entry)
end;

function TFunc_entry.Assign(const s: TFunc_entry): TFunc_entry;
begin
  Z3_func_entry_inc_ref(s.ctx.ToZ3_Context, s.m_entry);
  Z3_func_entry_dec_ref(ctx.ToZ3_Context, m_entry);
  m_ctx   := s.m_ctx;
  m_entry := s.m_entry;
  Result := Self;

end;

function TFunc_entry.GetItem(Index: Cardinal): TExpr;
begin
   var r : Z3_ast := Z3_func_entry_get_arg(ctx.ToZ3_Context, m_entry, Index);
   check_error;
   Result := TExpr.Create(ctx, r);
end;

function TFunc_entry.num_args: Cardinal;
begin
   var r : Cardinal := Z3_func_entry_get_num_args(ctx.ToZ3_Context, m_entry);
   check_error;
   Result := r;
end;

function TFunc_entry.ToZ3_func_entry: Z3_func_entry;
begin
    Result := m_entry;
end;

function TFunc_entry.value: TExpr;
begin
     var r : Z3_ast := Z3_func_entry_get_value(ctx.ToZ3_Context, m_entry);
     check_error;
     Result := TExpr.Create(ctx, r);
end;

{ TFunc_interp }

constructor TFunc_interp.Create(c: TContext; e: Z3_func_interp);
begin
   inherited Create(c);
   init(e)
end;

constructor TFunc_interp.Create(const s: TFunc_interp);
begin
    inherited Create(s);
    init(s.m_interp)
end;

destructor TFunc_interp.Destroy;
begin
   Z3_func_interp_dec_ref(ctx.ToZ3_Context, m_interp)
end;

procedure TFunc_interp.init(e: Z3_func_interp);
begin
   m_interp := e;
   Z3_func_interp_inc_ref(ctx.ToZ3_Context, m_interp);
end;

procedure TFunc_interp.add_entry(const args: TExpr_vector; value: TExpr);
begin
   Z3_func_interp_add_entry(ctx.ToZ3_Context, m_interp, args.ToZ3_ast_vector, value.ToZ3_ast);
   check_error;
end;

function TFunc_interp.Assign(const s: TFunc_interp): TFunc_interp;
begin
   Z3_func_interp_inc_ref(s.ctx.ToZ3_Context, s.m_interp);
   Z3_func_interp_dec_ref(ctx.ToZ3_Context, m_interp);
   m_ctx := s.m_ctx;
   m_interp := s.m_interp;
   Result  := Self;
end;

function TFunc_interp.else_value: TExpr;
begin
   var r : Z3_ast := Z3_func_interp_get_else(ctx.ToZ3_Context, m_interp);
   check_error;
   Result := TExpr.Create(ctx, r);
end;

function TFunc_interp.entry(i: Cardinal): TFunc_entry;
begin
   var e : Z3_func_entry := Z3_func_interp_get_entry(ctx.ToZ3_Context, m_interp, i);
   check_error;
   Result := TFunc_entry.Create(ctx, e);
end;

function TFunc_interp.num_entries: Cardinal;
begin
   var r : Cardinal := Z3_func_interp_get_num_entries(ctx.ToZ3_Context, m_interp);
   check_error;
   Result := r;
end;

procedure TFunc_interp.set_else(value: TExpr);
begin
   Z3_func_interp_set_else(ctx.ToZ3_Context, m_interp, value.ToZ3_ast);
   check_error;
end;

function TFunc_interp.ToZ3_func_interp: Z3_func_interp;
begin
   Result :=  m_interp;
end;

{ TModel }

constructor TModel.Create(c: TContext);
begin
    inherited Create(c);
    init(Z3_mk_model(c.ToZ3_Context))
end;

constructor TModel.Create(c: TContext; m: Z3_model);
begin
   inherited Create(c);
   init(m)
end;

constructor TModel.Create(const s: TModel);
begin
    inherited Create(s);
    init(s.m_model)
end;

constructor TModel.Create(src: TModel; dst: TContext; tr: translate);
begin
    inherited Create(dst);
    init( Z3_model_translate(src.ctx.ToZ3_Context, src.ToZ3_model, dst) );
end;

destructor TModel.Destroy;
begin
   Z3_model_dec_ref(ctx.ToZ3_Context, m_model)
end;

procedure TModel.init(m: Z3_model);
begin
   m_model := m;
   Z3_model_inc_ref(ctx.ToZ3_Context, m)
end;

procedure TModel.add_const_interp(f: TFunc_decl; value: TExpr);
begin
  Z3_add_const_interp(ctx.ToZ3_Context, m_model, f.ToZ3_func_decl, value.ToZ3_ast);
  check_error;
end;

function TModel.add_func_interp(f: TFunc_decl; else_val: TExpr): TFunc_interp;
begin
  var r : Z3_func_interp := Z3_add_func_interp(ctx.ToZ3_Context, m_model, f.ToZ3_func_decl, else_val.ToZ3_ast);
  check_error;
  Result := TFunc_interp.Create(ctx, r);
end;

function TModel.Assign(const s: TModel): TModel;
begin
  Z3_model_inc_ref(s.ctx.ToZ3_Context, s.m_model);
  Z3_model_dec_ref(ctx.ToZ3_Context, m_model);
  m_ctx := s.m_ctx;
  m_model := s.m_model;
  Result := Self;
end;

function TModel.eval(const n: TExpr; model_completion: Boolean): TExpr;
begin
  check_context(Self, n);
  var r : Z3_ast := nil;
  var status : Boolean := Z3_model_eval(ctx.ToZ3_Context, m_model, n.ToZ3_ast, model_completion, @r);
  check_error;
  if (status = false and ctx.enable_exceptions) then
      TZ3Exception.Create('failed to evaluate expression');
  Result := TExpr.Create(ctx, r);

end;

function TModel.GetItem(Index: Cardinal): TFunc_decl;
begin
  assert(integer(Index) >= 0);
  if Index <  num_consts then  Result := get_const_decl(Index)
  else                     Result := get_func_decl(Index - num_consts);
end;

function TModel.get_const_decl(i: Cardinal): TFunc_decl;
begin
   var r : Z3_func_decl  := Z3_model_get_const_decl(ctx.ToZ3_Context, m_model, i);
   check_error;
   Result := TFunc_decl.Create(ctx, r);
end;

function TModel.get_func_decl(i: Cardinal): TFunc_decl;
begin
  var r : Z3_func_decl  := Z3_model_get_func_decl(ctx.ToZ3_Context, m_model, i);
  check_error;
  Result := TFunc_decl.Create(ctx, r);
end;

function TModel.get_const_interp(c: TFunc_decl): TExpr;
begin
  check_context(self, c);
  var r : Z3_ast := Z3_model_get_const_interp(ctx.ToZ3_Context, m_model, c.ToZ3_func_decl);
  check_error;
  Result := TExpr.Create(ctx, r);
end;

function TModel.get_func_interp(f: TFunc_decl): TFunc_interp;
begin
  check_context(self, f);
  var r : Z3_func_interp := Z3_model_get_func_interp(ctx.ToZ3_Context, m_model, f.ToZ3_func_decl);
  check_error;
  Result := TFunc_interp.Create(ctx, r);
end;

function TModel.has_interp(f: TFunc_decl): Boolean;
begin
  check_context(self, f);
  Result := Z3_model_has_interp(ctx.ToZ3_Context, m_model, f.ToZ3_func_decl);
end;

function TModel.num_consts: Cardinal;
begin
   Result := Z3_model_get_num_consts(ctx.ToZ3_Context, m_model);
end;

function TModel.num_funcs: Cardinal;
begin
   Result := Z3_model_get_num_funcs(ctx.ToZ3_Context, m_model);
end;

function TModel.size: Cardinal;
begin
    Result := num_consts + num_funcs;
end;

function TModel.ToStr: AnsiString;
begin
    Result := ToStr(self)
end;

function TModel.ToStr(m: TModel): AnsiString;
begin
    Result := Z3_model_to_string(m.ctx.ToZ3_Context, m.ToZ3_model);
end;

function TModel.ToZ3_model: Z3_model;
begin
   Result := m_model;
end;

end.
