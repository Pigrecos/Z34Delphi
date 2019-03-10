{*******************************************************}
{                                                       }
{       Z3 Wrapper Class for Delphi                     }
{                                                       }
{       Unit and class for Z3 param Descr               }
{                                                       }
{       Copyright (C) 2019 Pigrecos(Max)                }
{       All rights reserved.                            }
{       MIT License                                     }
{*******************************************************}

unit Z3.Par_Desc;

interface
 uses
   System.SysUtils,
   z3,
   Z3.Context;

Type
  TParam_Descrs = class(Z3Object)
        m_descrs : Z3_param_descrs ;
    public
        constructor Create(c: TContext; d: Z3_param_descrs); overload;
        constructor Create(const o: TParam_descrs);overload;
        destructor  Destroy;

        function Assign(const o: TParam_descrs):TParam_descrs;
        function simplify_param_descrs(c: TContext): TParam_descrs;

        function size: Cardinal ;
        function name(i: Cardinal): TSymbol;
        function kind(const s: TSymbol): Z3_param_kind;
        function documentation(const s: TSymbol): AnsiString;
        function ToStr:AnsiString;overload;
        function ToStr(const d: TParam_descrs):AnsiString;overload;
    end;

implementation

{ TParam_Descrs }

constructor TParam_Descrs.Create(c: TContext; d: Z3_param_descrs);
begin
   inherited Create(c);
   m_descrs := d ;
   Z3_param_descrs_inc_ref(c, d)
end;

constructor TParam_Descrs.Create(const o: TParam_descrs);
begin
   inherited Create(o.ctx);
   m_descrs := o.m_descrs;
   Z3_param_descrs_inc_ref(ctx.ToZ3_Context, m_descrs);
end;

destructor TParam_Descrs.Destroy;
begin
  Z3_param_descrs_dec_ref(ctx.ToZ3_Context, m_descrs)
end;

function TParam_Descrs.Assign(const o: TParam_descrs): TParam_descrs;
begin
   Z3_param_descrs_inc_ref(o.ctx.ToZ3_Context, o.m_descrs);
   Z3_param_descrs_dec_ref(ctx.ToZ3_Context, m_descrs);
   m_descrs := o.m_descrs;
   m_ctx := o.m_ctx;
   Result := Self
end;

function TParam_Descrs.documentation(const s: TSymbol): AnsiString;
begin
   var r : AnsiString := AnsiString( Z3_param_descrs_get_documentation(ctx.ToZ3_Context, m_descrs, s.ToZ3_symbol) );
   check_error();
   Result := r;
end;

function TParam_Descrs.kind(const s: TSymbol): Z3_param_kind;
begin
  Result := Z3_param_descrs_get_kind(ctx.ToZ3_Context, m_descrs, s);
end;

function TParam_Descrs.name(i: Cardinal): TSymbol;
begin
  Result := TSymbol.Create(ctx, Z3_param_descrs_get_name(ctx.ToZ3_Context, m_descrs, i));
end;

function TParam_Descrs.simplify_param_descrs(c: TContext): TParam_descrs;
begin
    Result := TParam_descrs.Create(c, Z3_simplify_get_param_descrs(c));
end;

function TParam_Descrs.size: Cardinal;
begin
   Result := Z3_param_descrs_size(ctx.ToZ3_Context, m_descrs);
end;

function TParam_Descrs.ToStr: AnsiString;
begin
  Result := Z3_param_descrs_to_string(ctx.ToZ3_Context, m_descrs)
end;

function TParam_Descrs.ToStr(const d: TParam_descrs): AnsiString;
begin
    Result := d.ToStr;
end;

end.
