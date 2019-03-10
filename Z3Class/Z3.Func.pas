{*******************************************************}
{                                                       }
{       Z3 Wrapper Class for Delphi                     }
{                                                       }
{       Unit for Common Function for All Module         }
{                                                       }
{       Copyright (C) 2019 Pigrecos(Max)                }
{       All rights reserved.                            }
{       MIT License                                     }
{*******************************************************}

unit Z3.Func;



interface
  uses
   System.SysUtils,
   z3,
   z3_fpa,
   Z3.Context,
   Z3.Arr,
   Z3.Def;


       function Z3_MK_BIN(a,b: TExpr;BinOp:FBinOp): TExpr;
       function Z3_MK_UN (a: TExpr;UnOp: FUnOp) : TExpr;

       function MK_EXPR1(_fn: FUnOp; _arg: TAst): TExpr;
       function MK_EXPR2(_fn: FBinOp; _arg1,_arg2: TAst): TExpr;

       function    to_check_result(l: Z3_lbool): check_result;
       function    check_resultToStr(r:check_result): AnsiString;
       procedure   check_context(const  a, b: Z3Object);
       function    to_sort(c: TContext; s: Z3_sort): TSort;
       function    Eq(const a, b: TAst): Boolean;
       (*
        \brief Return an expression representing <tt>not(a)</tt>.

          \pre a.is_bool()
       *)
       function OpNot(const a: TExpr): TExpr;

       function is_int(const e: TExpr): TExpr;

       function implies(const a: TExpr; const b: TExpr): TExpr; overload;
       function implies(const a: TExpr; b: Boolean): TExpr; overload;
       function implies(a: Boolean; const b: TExpr): TExpr;  overload;
       (*  \brief Power operator  *)
       function pw(const a: TExpr; const b: TExpr): TExpr; overload;
       function pw(const a: TExpr; b: Integer): TExpr;  overload;
       function pw(a: Integer; const b: TExpr): TExpr; overload;
       (* \brief mod operator *)
       function &mod(const a: TExpr; const b: TExpr): TExpr; overload;
       function &mod(const a: TExpr; b: Integer): TExpr;   overload;
       function &mod(a: Integer; const b: TExpr): TExpr;  overload;
       (* \brief rem operator *)
       function rem(const a: TExpr; const b: TExpr): TExpr; overload;
       function rem(const a: TExpr; b: Integer): TExpr;  overload;
       function rem(a: Integer; const b: TExpr): TExpr;  overload;
       (**
          \brief Return an expression representing <tt>a and b</tt>.

          \pre a.is_bool()
          \pre b.is_bool()
       *)
       function OpAnd(const a: TExpr; const b: TExpr): TExpr;overload;
       (*
           \brief Return an expression representing <tt>a and b</tt>.
           The C++ Boolean value \c b is automatically converted into a Z3 Boolean constant.

           \pre a.is_bool()
       *)
       function OpAnd(const a: TExpr; b: Boolean):TExpr; overload;
       (*
           \brief Return an expression representing <tt>a and b</tt>.
           The C++ Boolean value \c a is automatically converted into a Z3 Boolean constant.

           \pre b.is_bool()
       *)
       function OpAnd(a: Boolean; const b: TExpr): TExpr; overload;

       (*
           \brief Return an expression representing <tt>a or b</tt>.

           \pre a.is_bool()
           \pre b.is_bool()
       *)
       function OpOr(const a: TExpr; const b: TExpr): TExpr; overload;
       (*
           \brief Return an expression representing <tt>a or b</tt>.
           The C++ Boolean value \c b is automatically converted into a Z3 Boolean constant.

           \pre a.is_bool()
       *)
       function OpOr(const a: TExpr; b: Boolean): TExpr; overload;
       (*
           \brief Return an expression representing <tt>a or b</tt>.
           The C++ Boolean value \c a is automatically converted into a Z3 Boolean constant.

           \pre b.is_bool()
        *)
       function OpOr(a: Boolean; const b: TExpr): TExpr; overload;

       function mk_or(const args: TExpr_vector): TExpr; overload;
       function mk_and(const args: TExpr_vector): TExpr; overload;

       function ite(const c: TExpr; const t: TExpr; const e: TExpr): TExpr; overload;

       function distinct(const args: TExpr_vector): TExpr; overload;
       function concat(const a: TExpr; const b: TExpr): TExpr; overload;
       function concat(const args: TExpr_vector): TExpr; overload;

       function OpEq(const a: TExpr; const b: TExpr): TExpr; overload;
       function OpEq(const a: TExpr; b: Integer): TExpr; overload;
       function OpEq(a: Integer; const b: TExpr): TExpr; overload;

       function OpNotEq(const a : TExpr; const b: TExpr): TExpr; overload;
       function OpNotEq(const a: TExpr; b: Integer): TExpr; overload;
       function OpNotEq(a: Integer; const b: TExpr): TExpr; overload;

       function OpAdd(const a: TExpr; const b: TExpr): TExpr; overload;
       function OpAdd(const a: TExpr; b: Integer): TExpr; overload;
       function OpAdd(a: Integer; const b: TExpr): TExpr; overload;

       function sum(const args: TExpr_vector): TExpr; overload;

       function OpMul(const a: TExpr; const b: TExpr): TExpr; overload;
       function OpMul(const a: TExpr;b: Integer): TExpr; overload;
       function OpMul(a: Integer; const b: TExpr): TExpr; overload;

       function OpDiv(const a: TExpr;const b: TExpr): TExpr; overload;
       function OpDiv(const a: TExpr; b: Integer): TExpr; overload;
       function OpDiv(a: Integer;const b: TExpr): TExpr; overload;

       function OpMinus(const a: TExpr): TExpr; overload;

       function OpMinus(const a: TExpr; const b: TExpr): TExpr; overload;
       function OpMinus(const a: TExpr; b: Integer): TExpr; overload;
       function OpMinus(a: Integer;const b: TExpr): TExpr; overload;

       function OpMinOrEq(const a: TExpr;const b: TExpr): TExpr; overload;
       function OpMinOrEq(const a: TExpr; b: Integer): TExpr; overload;
       function OpMinOrEq(a: Integer;const b: TExpr): TExpr; overload;

       function OpMajOrEq(const a: TExpr;const b: TExpr): TExpr; overload;
       function OpMajOrEq(const a: TExpr; b: Integer): TExpr; overload;
       function OpMajOrEq(a: Integer;const b: TExpr): TExpr; overload;

       function OpMinor(const a: TExpr;const b: TExpr): TExpr; overload;
       function OpMinor(const a: TExpr; b: Integer): TExpr; overload;
       function OpMinor(a: Integer;const b: TExpr): TExpr; overload;

       function OpMajor(const a: TExpr;const b: TExpr): TExpr; overload;
       function OpMajor(const a: TExpr; b: Integer): TExpr; overload;
       function OpMajor(a: Integer;const b: TExpr): TExpr; overload;

       function pble   (const es : TExpr_vector; const coeffs : Integer; bound: Integer): TExpr;
       function pbge   (const es : TExpr_vector; const coeffs : Integer; bound: Integer): TExpr;
       function pbeq   (const es : TExpr_vector; const coeffs : Integer; bound: Integer): TExpr;
       function atmost (const es : TExpr_vector; bound: Cardinal): TExpr;
       function atleast(const es : TExpr_vector; bound: Cardinal): TExpr;

       function OpAndbv(const a: TExpr; const b: TExpr): TExpr;overload;
       function OpAndbv(const a: TExpr;b: Integer): TExpr;overload;
       function OpAndbv(a: Integer; const b: TExpr): TExpr;overload;

       function OpXorbv(const a: TExpr; const b: TExpr): TExpr; overload;
       function OpXorbv(const a: TExpr;b: Integer): TExpr; overload;
       function OpXorbv(a: Integer; const b: TExpr): TExpr;overload;

       function OpOrbv(const a: TExpr; const b: TExpr): TExpr; overload;
       function OpOrbv(const a: TExpr;b: Integer): TExpr; overload;
       function OpOrbv(a: Integer; const b: TExpr): TExpr;overload;

       function nand(const a: TExpr; const b: TExpr): TExpr;
       function nor(const a: TExpr; const b: TExpr): TExpr;
       function xnor(const a: TExpr; const b: TExpr): TExpr;

       function min(const a: TExpr; const b: TExpr): TExpr;
       function max(const a: TExpr; const b: TExpr): TExpr;

       function abs(const a: TExpr): TExpr;
       function sqrt(const a : TExpr; const rm: TExpr): TExpr;

       function OpNotbv(const a: TExpr): TExpr;

       (*
           \brief FloatingPoint fused multiply-add.
       *)
       function fma(const a : TExpr; const b: TExpr; const c: TExpr;const rm: TExpr): TExpr;

       function range(const lo: TExpr; const hi: TExpr): TExpr;
       //
       function to_real(const a: TExpr): TExpr;
       function &function(const name: TSymbol;   arity: Cardinal; const domain: TSort; const range: TSort): TFunc_decl; overload;
       function &function(const name: PAnsiChar; arity: Cardinal; const domain: TSort; const range: TSort): TFunc_decl; overload;
       function &function(const name: PAnsiChar; const domain: TSort; const range: TSort): TFunc_decl;overload;
       function &function(const name: PAnsiChar; const d1: TSort; const d2: TSort; const range: TSort): TFunc_decl; overload;
       function &function(const name: PAnsiChar; const d1: TSort; const d2: TSort; const d3: TSort; const range: TSort) : TFunc_decl;overload;
       function &function(const name: PAnsiChar; const d1: TSort; const d2: TSort; const d3: TSort; const d4: TSort; const  range: TSort): TFunc_decl; overload;
       function &function(const name: PAnsiChar; const d1: TSort; const d2: TSort; const d3: TSort; const d4: TSort; const d5: TSort; const range: TSort): TFunc_decl; overload;
       function &function(const name: PAnsiChar; const domain: TSort_vector; const range: TSort): TFunc_decl; overload;
       function &function(const name: AnsiString;const domain: TSort_vector; const range: TSort): TFunc_decl; overload;
       //
       function recfun(const name: TSymbol;   arity: Cardinal; const domain: TSort; const range: TSort): TFunc_decl; overload;
       function recfun(const name: PAnsiChar; arity: Cardinal; const domain: Tsort; const range: TSort): TFunc_decl;overload;
       function recfun(const name: PAnsiChar; const d1: TSort; const range: TSort): TFunc_decl; overload;
       function recfun(const name: PAnsiChar; const d1: TSort; const d2: TSort; const range: TSort): TFunc_decl;overload;
       //
       function select(const a: TExpr;const  i: TExpr): TExpr;overload;
       function select(const a: TExpr;       i:Integer) : TExpr;  overload;
       function select(const a: TExpr; const i: TExpr_vector) : TExpr; overload;
       //
       function store (const a: TExpr; const i: TExpr;const          v: TExpr): TExpr;  overload;
       function store (const a: TExpr;       i: Integer; const       v: TExpr): TExpr; overload;
       function store (const a: TExpr;       i: TExpr;               v: Integer): TExpr; overload;
       function store (const a: TExpr;       i: Integer;             v: Integer): TExpr; overload;
       function store(const  a: TExpr; const i: TExpr_vector; const  v: TExpr): TExpr;  overload;
       //
       function as_array(f: TFunc_decl): TExpr;
       function const_array(const d: TSort; const v: TExpr): TExpr;
       function empty_set(const s: TSort): TExpr;
       function full_set(const s: TSort): TExpr;
       function set_add(const s: TExpr; const e: TExpr): TExpr;
       function set_del(const s: TExpr; const e: TExpr): TExpr;
       function set_union(const a: TExpr; const b: TExpr): TExpr;
       function set_intersect(const a: TExpr; const b: TExpr) : TExpr;
       function set_difference(const a: TExpr; const b: TExpr) : TExpr;
       function set_complement(const a: TExpr): TExpr;
       function set_member(const s: TExpr; const e: TExpr): TExpr;
       function set_subset(const a: TExpr; const b: TExpr): TExpr;
      // sequence and regular expression operations.
      // union is +
      // concat is overloaded to handle sequences and regular expressions

       function empty(const s: TSort): TExpr;
       function suffixof(const a: TExpr; const b: TExpr): TExpr;
       function prefixof(const a: TExpr; const b: TExpr): TExpr;
       function indexof(const s: TExpr; const substr: TExpr; const offset: TExpr) : TExpr;
       function to_re(const s: TExpr): TExpr;
       function in_re(const s: TExpr; const re: TExpr) : TExpr;
       function plus(const re: TExpr): TExpr;
       function option(const re: TExpr) : TExpr;
       function star(const re: TExpr): TExpr;
       function re_empty(const s: TSort) : TExpr;
       function re_full(const s: TSort): TExpr;
       function re_intersect(const args: TExpr_vector ): TExpr;
       function re_complement(const a: TExpr) : TExpr;

       procedure set_param(const param: PAnsiChar; const value: PAnsiChar);overload;
       procedure set_param(const param: PAnsiChar; value: Boolean); overload;
       procedure set_param(const param: PAnsiChar; value: Integer);  overload;
       procedure reset_params;


      (**
         \brief Wraps a Z3_ast as an expr object. It also checks for errors.
         This function allows the user to use the whole C API with the C++ layer defined in this file.
      *)
      function to_expr(c: TContext; a: Z3_ast): TExpr ;
      function to_func_decl(c: TContext; f: Z3_func_decl): TFunc_decl ;

      (**
         \brief unsigned less than or equal to operator for bitvectors.
      *)
      function ule(const a: TExpr;const b: TExpr): TExpr;overload;
      function ule(const a: TExpr; b: Integer): TExpr; overload;
      function ule(a: Integer; const b: TExpr): TExpr ;overload;
      (**
         \brief unsigned less than operator for bitvectors.
      *)
      function ult(const a: TExpr; const b: TExpr): TExpr; overload;
      function ult(const a: TExpr; b: Integer): TExpr;overload;
      function ult(a: Integer; const b: TExpr): TExpr; overload;
      (**
         \brief unsigned greater than or equal to operator for bitvectors.
      *)
      function uge(const a: TExpr; const b: TExpr): TExpr; overload;
      function uge(const a: TExpr; b: Integer) : TExpr;overload;
      function uge(a: Integer; const b: TExpr): TExpr;overload;
      (**
         \brief unsigned greater than operator for bitvectors.
      *)
      function ugt(const a: TExpr; const b: TExpr): TExpr;overload;
      function ugt(const a: TExpr; b: Integer): TExpr ;overload;
      function ugt(a: Integer; const b: TExpr): TExpr;overload;
      (**
         \brief unsigned division operator for bitvectors.
      *)
      function udiv(const a: TExpr; const b: TExpr): TExpr ;overload;
      function udiv(const a: TExpr; b: Integer): TExpr ;overload;
      function udiv(a: Integer; const b: TExpr): TExpr; overload;

      (**
         \brief signed remainder operator for bitvectors
      *)
      function srem(const a: TExpr; const b: TExpr): TExpr;overload;
      function srem(const a: TExpr; b: Integer): TExpr ; overload;
      function srem(a: Integer; const b: TExpr): TExpr ;overload;

      (**
         \brief signed modulus operator for bitvectors
      *)
      function smod(const a: TExpr; const b: TExpr): TExpr ; overload;
      function smod(const a: TExpr; b: Integer): TExpr ; overload;
      function smod(a: Integer; const b: TExpr): TExpr; overload;

      (**
         \brief unsigned reminder operator for bitvectors
      *)
      function urem(const a: TExpr; const b: TExpr): TExpr ;overload;
      function urem(const a: TExpr; b: Integer): TExpr; overload;
      function urem(a: Integer; const b: TExpr): TExpr; overload;

      (**
         \brief shift left operator for bitvectors
      *)
      function &shl(const a: TExpr; const b: TExpr): TExpr; overload;
      function &shl(const a: TExpr; b: Integer): TExpr ; overload;
      function &shl(a: Integer; const b: TExpr) : TExpr; overload;

      (**
         \brief logic shift right operator for bitvectors
      *)
      function lshr(const a: TExpr; const b: TExpr): TExpr ; overload;
      function lshr(const a: TExpr; b: Integer): TExpr;  overload;
      function lshr(a: Integer; const b: TExpr): TExpr ;overload;

      (**
         \brief arithmetic shift right operator for bitvectors
      *)
      function ashr(const a: TExpr; const b: TExpr): TExpr ; overload;
      function ashr(const a: TExpr; b: Integer): TExpr ;  overload;
      function ashr(a: Integer; const b: TExpr): TExpr ; overload;

      (**
         \brief Extend the given bit-vector with zeros to the (unsigned) equivalent bitvector of size m+i, where m is the size of the given bit-vector.
      *)
      function zext(const a: TExpr; i: Cardinal): TExpr ;

      (**
         \brief Sign-extend of the given bit-vector to the (signed) equivalent bitvector of size m+i, where m is the size of the given bit-vector.
      *)
      function sext(const a: TExpr; i: Cardinal): TExpr ;

      // Basic functions for creating quantified formulas.
      // The C API should be used for creating quantifiers with patterns, weights, many variables, etc.
      function forall(const x : TExpr; const b :TExpr): TExpr;overload;
      function forall(const x1: TExpr; const x2:TExpr;  const b :TExpr): TExpr; overload;
      function forall(const x1: TExpr; const x2:TExpr;  const x3:TExpr; const b : TExpr): TExpr;overload;
      function forall(const x1: TExpr; const x2:TExpr;  const x3:TExpr; const x4: TExpr; const b: TExpr): TExpr;overload;
      function forall(const xs: TExpr_vector; const b: TExpr): TExpr;overload;

      function exists(const x :TExpr; const b :TExpr): TExpr;overload;
      function exists(const x1:TExpr; const x2:TExpr; const b :TExpr): TExpr;overload;
      function exists(const x1:TExpr; const x2:TExpr; const x3:TExpr; const b: TExpr): TExpr;overload;
      function exists(const x1:TExpr; const x2:TExpr; const x3:TExpr; const x4: TExpr; const b: TExpr): TExpr; overload;
      function exists(const xs: TExpr_vector; const b: TExpr): TExpr;overload;

      function lambda(const x:TExpr; const b: TExpr): TExpr;overload;
      function lambda(const x1: TExpr; const x2:TExpr; const b : TExpr): TExpr;overload;
      function lambda(const x1: TExpr; const x2:TExpr; const x3: TExpr; const b: TExpr): TExpr;overload;
      function lambda(const x1: TExpr; const x2:TExpr; const x3: TExpr; const x4:TExpr; const b: TExpr): TExpr; overload;
      function lambda(const xs: TExpr_vector; const  b: TExpr): TExpr;overload;
      

implementation

function Z3_MK_BIN(a,b: TExpr;BinOp:FBinOp): TExpr;
begin
    check_context(a, b);
    var r : Z3_ast := binop(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
    a.check_error;
    Result := TExpr.Create(a.ctx, r);
end;

function Z3_MK_UN (a: TExpr;UnOp: FUnOp) : TExpr;
begin
    var r : Z3_ast := UnOp(a.ctx.ToZ3_Context, a.ToZ3_ast);
    a.check_error;
    Result := TExpr.Create(a.ctx, r);
end;

function MK_EXPR1(_fn: FUnOp; _arg: TAst): TExpr;
begin
    var r : Z3_ast := _fn(_arg.ctx.ToZ3_Context, _arg.ToZ3_ast);
    _arg.check_error;
    Result := TExpr.Create(_arg.ctx, r);
end;

function MK_EXPR2(_fn: FBinOp; _arg1,_arg2: TAst): TExpr;
begin
   check_context(_arg1, _arg2);
   var r : Z3_ast := _fn( _arg1.ctx.ToZ3_Context, _arg1.ToZ3_ast, _arg2.ToZ3_ast);
   _arg1.check_error;
   Result := TExpr.Create(_arg1.ctx, r);
end;

function to_check_result(l: Z3_lbool): check_result;
begin
    if      (l = Z3_L_TRUE) then Result := sat
    else if (l = Z3_L_FALSE)then Result := unsat
    else                         Result := unknown;
end;

function check_resultToStr(r:check_result): AnsiString;
begin
  if      (r = unsat) then Result := 'unsat'
  else if (r = sat)   then Result := 'sat'
  else                     Result := 'unknown';

end;

function to_sort(c: TContext; s: Z3_sort): TSort; inline;
begin
    c.check_error;
    Result := TSort.Create(c, s)
end;

procedure check_context(const a, b: Z3Object);
var
  x, y : NativeUInt;
begin
    x := nativeUInt(Pointer(a.ctx));
    y := nativeUInt(Pointer(a.ctx));
    Assert(x = y,'Z3Object.check_context error');
end;

function Eq(const a, b: TAst): Boolean;
begin
    Result := Z3_is_eq_ast(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast)
end;

procedure set_param(const param: PAnsiChar; const value: PAnsiChar);
begin
   Z3_global_param_set(param, value)
end;

procedure set_param(const param: PAnsiChar; value: Boolean);
begin
    if value then Z3_global_param_set(param,'true')
    else          Z3_global_param_set(param,'false')
end;

procedure set_param(const param: PAnsiChar; value: Integer);
var
  s : AnsiString;
begin
 s := IntToStr(value);
 Z3_global_param_set(param, @s[1])
end;

procedure reset_params;
begin
   Z3_global_param_reset_all
end;


{ Psudo Operatori }

function OpNot(const a: TExpr): TExpr;
begin
    assert(a.is_bool);
    Result := Z3_MK_UN(a, Z3_mk_not);
end;

function is_int(const e: TExpr): TExpr;
begin
   Result := Z3_MK_UN(e, Z3_mk_is_int);
end;

function implies(const a: TExpr; const b: TExpr): TExpr;
begin
    assert(a.is_bool and b.is_bool);
     Result := Z3_MK_BIN(a, b, Z3_mk_implies)
end;

function implies(const a: TExpr; b: Boolean): TExpr;
begin
    Result := implies(a, a.ctx.bool_val(b));
end;

function implies(a: Boolean; const b: TExpr): TExpr;
begin
    Result := implies(b.ctx.bool_val(a), b);
end;

function pw(const a: TExpr; const b: TExpr): TExpr;
begin
     Result := Z3_MK_BIN(a, b, Z3_mk_power);
end;

function pw(const a: TExpr; b: Integer): TExpr;
begin
    Result := pw(a, a.ctx.num_val(b, a.get_sort));
end;

function pw(a: Integer; const b: TExpr): TExpr;
begin
    Result := pw(b.ctx.num_val(a, b.get_sort), b);
end;

function &mod(const a: TExpr; const b: TExpr): TExpr;
begin
     Result := Z3_MK_BIN(a, b, Z3_mk_mod);
end;

function &mod(const a: TExpr; b: Integer): TExpr;
begin
   Result := &mod(a, a.ctx.num_val(b, a.get_sort));
end;

function &mod(a: Integer; const b: TExpr): TExpr;
begin
   Result := &mod(b.ctx.num_val(a, b.get_sort), b);
end;

function rem(const a: TExpr; const b: TExpr): TExpr;
begin
    if (a.is_fpa)  and b.is_fpa then Result := Z3_MK_BIN(a, b, Z3_mk_fpa_rem)
    else                             Result := Z3_MK_BIN(a, b, Z3_mk_rem);
end;

function rem(const a: TExpr; b: Integer): TExpr;
begin
    Result := rem(a, a.ctx.num_val(b, a.get_sort));
end;

function rem(a: Integer; const b: TExpr): TExpr;
begin
    Result := rem(b.ctx.num_val(a, b.get_sort), b);
end;

function OpAnd(const a: TExpr; const b: TExpr): TExpr;
begin
    check_context(a, b);
    assert(a.is_bool and b.is_bool);
    var args : TArray<Z3_ast> := [ a.ToZ3_ast, b.ToZ3_ast ];
    var r : Z3_ast := Z3_mk_and(a.ctx.ToZ3_Context, 2, @args[0]);
    a.check_error;
    Result := TExpr.Create(a.ctx, r);
end;

function OpAnd(const a: TExpr; b: Boolean):TExpr;
begin
    Result := OpAnd( a, a.ctx.bool_val(b) );
end;

function OpAnd(a: Boolean; const b: TExpr): TExpr;
begin
   Result := OpAnd(b.ctx.bool_val(a) ,b);
end;

function OpOr(const a: TExpr; const b: TExpr): TExpr;
begin
   check_context(a, b);
   assert(a.is_bool and b.is_bool);
   var args : TArray<Z3_ast> := [ a.ToZ3_ast, b.ToZ3_ast ];
   var r : Z3_ast := Z3_mk_or(a.ctx.ToZ3_Context, 2, @args[0]);
   a.check_error;
   Result := TExpr.Create(a.ctx, r);
end;

function OpOr(const a: TExpr; b: Boolean): TExpr;
begin
    Result :=  OpOr(a, a.ctx.bool_val(b));
end;

function OpOr(a: Boolean; const b: TExpr): TExpr;
begin
   Result := opOr(b.ctx.bool_val(a), b);
end;

function mk_or(const args: TExpr_vector): TExpr;
begin
    var _args : TZ3Array<Z3_ast> := args.ToArray;
    var r : Z3_ast := Z3_mk_or(args.ctx.ToZ3_Context, _args.size, _args.ptr);
    args.check_error;
    Result := TExpr.Create(args.ctx, r);
end;

function mk_and(const args: TExpr_vector): TExpr;
begin
   var _args : TZ3Array<Z3_ast> := args.ToArray;
   var r : Z3_ast := Z3_mk_and(args.ctx.ToZ3_Context, _args.size, _args.ptr);
   args.check_error;
   Result := TExpr.Create(args.ctx, r);
end;

function ite(const c: TExpr; const t: TExpr; const e: TExpr): TExpr;
begin
   check_context(c, t);
   check_context(c, e);
   assert(c.is_bool);
   var r : Z3_ast := Z3_mk_ite(c.ctx.ToZ3_Context, c.ToZ3_ast, t.ToZ3_ast, e.ToZ3_ast);
   c.check_error;
   Result := TExpr.Create(c.ctx, r);
end;

function distinct(const args: TExpr_vector): TExpr;
begin
    assert(args.size > 0);
    var ctx : TContext := args.Items[0].ctx;
    var _args : TZ3Array<Z3_ast> := args.ToArray;
    var r : Z3_ast := Z3_mk_distinct(ctx.ToZ3_Context, _args.size, _args.ptr);
    ctx.check_error;
    Result := TExpr.Create(ctx, r);
end;

function concat(const a: TExpr; const b: TExpr): TExpr;
begin
  check_context(a, b);
  var r : Z3_ast ;
  if Z3_is_seq_sort(a.ctx.ToZ3_Context, a.get_sort) then
  begin
      var _args : TArray<Z3_ast> := [ a.ToZ3_ast, b.ToZ3_ast ];
      r := Z3_mk_seq_concat(a.ctx.ToZ3_Context, 2, @_args[0]);
  end
  else if Z3_is_re_sort(a.ctx.ToZ3_Context, a.get_sort) then
  begin
      var _args : TArray<Z3_ast> := [ a.ToZ3_ast, b.ToZ3_ast ];
      r := Z3_mk_re_concat(a.ctx.ToZ3_Context, 2, @_args[0]);
  end else
  begin
      r := Z3_mk_concat(a.ctx.ToZ3_Context, a.Create.ToZ3_ast, b.ToZ3_ast);
  end;
  a.ctx.check_error;
  Result := TExpr.Create(a.ctx, r);

end;

function concat(const args: TExpr_vector): TExpr;
var
  i : Integer;
begin
    var r : Z3_ast ;
    assert(args.size() > 0);
    if (args.size = 1) then Exit(args.Items[0]);

    var ctx : TContext := args.Items[0].ctx;
    var _args : TZ3Array<Z3_ast> := args.ToArray;

    if      Z3_is_seq_sort(ctx.ToZ3_Context, args.Items[0].get_sort)then     r := Z3_mk_seq_concat(ctx.ToZ3_Context, _args.size, _args.ptr)
    else if Z3_is_re_sort(ctx.ToZ3_Context, args.Items[0].get_sort) then     r := Z3_mk_re_concat (ctx.ToZ3_Context, _args.size, _args.ptr)
    else begin
        r := _args.Items[args.size - 1];
        for i := args.size-1 to  0 do
        begin
            r := Z3_mk_concat(ctx.ToZ3_Context, _args.Items[i], r);
            ctx.check_error;
        end;
    end;
    ctx.check_error;
    Result := TExpr.Create(ctx, r);

end;

function OpEq(const a: TExpr; const b: TExpr): TExpr;
begin
    check_context(a, b);
    var r : Z3_ast := Z3_mk_eq(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
    a.check_error;
    Result :=  TExpr.Create(a.ctx, r);
end;

function OpEq(const a: TExpr; b: Integer): TExpr;
begin
    assert(a.is_arith or a.is_bv or a.is_fpa);
    Result := OpEq( a, a.ctx.num_val(b, a.get_sort) );
end;

function OpEq(a: Integer; const b: TExpr): TExpr;
begin
   assert(b.is_arith or b.is_bv or b.is_fpa);
   Result := OpEq(b.ctx.num_val(a, b.get_sort), b);
end;

function OpNotEq(const a : TExpr; const b: TExpr): TExpr;
begin
   check_context(a, b);
   var args : TArray<Z3_ast> := [ a.ToZ3_ast, b.ToZ3_ast ];
   var r : Z3_ast := Z3_mk_distinct(a.ctx.ToZ3_Context, 2, @args[0]);
   a.check_error;
   Result :=  TExpr.Create(a.ctx, r);
end;

function OpNotEq(const a: TExpr; b: Integer): TExpr;
begin
   assert(a.is_arith or a.is_bv or a.is_fpa);
   Result := OpNotEq(a, a.ctx.num_val(b, a.get_sort));
end;

function OpNotEq(a: Integer; const b: TExpr): TExpr;
begin
    assert(b.is_arith or b.is_bv or b.is_fpa);
    Result := OpNotEq(b.ctx.num_val(a, b.get_sort), b);
end;

function OpAdd(const a: TExpr; const b: TExpr): TExpr;
var
  r   : Z3_ast;
  args: TArray<Z3_ast>;
begin
    check_context(a, b);
    r := nil;
    if (a.is_arith and b.is_arith) then
    begin
        args := [ a.ToZ3_ast, b.ToZ3_ast ];
        r := Z3_mk_add(a.ctx.ToZ3_Context, 2, @args[0]);
    end
    else if (a.is_bv and b.is_bv) then
    begin
        r := Z3_mk_bvadd(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
    end
    else if (a.is_seq and b.is_seq) then
    begin
        Exit(concat(a, b));
    end
    else if (a.is_re and b.is_re) then
    begin
        args := [ a, b ];
        r := Z3_mk_re_union(a.ctx.ToZ3_Context, 2,@args[0]);
    end
    else if (a.is_fpa and b.is_fpa) then
    begin
        r := Z3_mk_fpa_add(a.ctx.ToZ3_Context, a.ctx.fpa_rounding_mode, a.ToZ3_ast, b.ToZ3_ast);
    end else
    begin
        // operator is not supported by given arguments.
        assert(false);
    end;
    a.check_error;
    Result := TExpr.Create(a.ctx, r);

end;

function OpAdd(const a: TExpr; b: Integer): TExpr;
begin
   Result := OpAdd(a ,a.ctx.num_val(b, a.get_sort));
end;

function OpAdd(a: Integer; const b: TExpr): TExpr;
begin
   Result := OpAdd(b.ctx.num_val(a, b.get_sort),  b);
end;

function sum(const args: TExpr_vector): TExpr;
var
  _args : TZ3Array<Z3_ast>;
begin
   assert(args.size > 0);
   var ctx : TContext := args.Items[0].ctx;
   _args := args.ToArray;
   var r : Z3_ast := Z3_mk_add(ctx.ToZ3_Context, _args.size, _args.ptr);
   ctx.check_error;
   Result := TExpr.Create(ctx, r);
end;

function OpMul(const a: TExpr; const b: TExpr): TExpr;
var
  r    : Z3_ast;
  args : TArray<Z3_ast>;
begin
  check_context(a, b);
  r := nil;
  if (a.is_arith and b.is_arith) then
  begin
      args := [ a.ToZ3_ast, b.ToZ3_ast ];
      r := Z3_mk_mul(a.ctx.ToZ3_Context, 2, @args[0]);
  end
  else if (a.is_bv and b.is_bv) then
  begin
      r := Z3_mk_bvmul(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
  end
  else if (a.is_fpa and b.is_fpa) then
  begin
      r := Z3_mk_fpa_mul(a.ctx.ToZ3_Context, a.ctx.fpa_rounding_mode(), a.ToZ3_ast, b.ToZ3_ast);
  end else
  begin
      // operator is not supported by given arguments.
      assert(false);
  end;
  a.check_error;
  Result := TExpr.Create(a.ctx, r);
end;

function OpMul(const a: TExpr;b: Integer): TExpr;
begin
   Result := OpMul(a, a.ctx.num_val(b, a.get_sort));
end;

function OpMul(a: Integer; const b: TExpr): TExpr;
begin
   Result := OpMul(b.ctx.num_val(a, b.get_sort), b);
end;

function OpDiv(const a: TExpr;const b: TExpr): TExpr;
var
  r : Z3_ast;
begin
  check_context(a, b);
  r := nil;
  if (a.is_arith and b.is_arith) then
  begin
      r := Z3_mk_div(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
  end
  else if (a.is_bv and b.is_bv) then
  begin
      r := Z3_mk_bvsdiv(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
  end
  else if (a.is_fpa and b.is_fpa) then
  begin
      r := Z3_mk_fpa_div(a.ctx.ToZ3_Context, a.ctx.fpa_rounding_mode, a.ToZ3_ast, b.ToZ3_ast);
  end else
  begin
      // operator is not supported by given arguments.
      assert(false);
  end;
  a.check_error();
  Result := TExpr.Create(a.ctx, r);

end;

function OpDiv(const a: TExpr; b: Integer): TExpr;
begin
   Result := OpDiv(a, a.ctx.num_val(b, a.get_sort));
end;

function OpDiv(a: Integer;const b: TExpr): TExpr;
begin
   Result := OpDiv(b.ctx.num_val(a, b.get_sort), b);
end;

function OpMinus(const a: TExpr): TExpr;
var
  r : Z3_ast;
begin
    r := nil;
    if (a.is_arith) then
    begin
        r := Z3_mk_unary_minus(a.ctx.ToZ3_Context, a.ToZ3_ast);
    end
    else if (a.is_bv) then
    begin
        r := Z3_mk_bvneg(a.ctx.ToZ3_Context, a.ToZ3_ast);
    end
    else if (a.is_fpa) then
    begin
        r := Z3_mk_fpa_neg(a.ctx.ToZ3_Context, a.ToZ3_ast);
    end else
    begin
        // operator is not supported by given arguments.
        assert(false);
    end;
    a.check_error;
    Result := TExpr.Create(a.ctx, r);
end;

function OpMinus(const a: TExpr; const b: TExpr): TExpr;
var
  r    : Z3_ast;
  args : TArray<Z3_ast> ;
begin
  check_context(a, b);
  r := nil;
  if (a.is_arith and b.is_arith) then
  begin
      args := [ a.ToZ3_ast, b.ToZ3_ast ];
      r := Z3_mk_sub(a.ctx.ToZ3_Context, 2, @args[0]);
  end
  else if (a.is_bv and b.is_bv) then
  begin
      r := Z3_mk_bvsub(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
  end
  else if (a.is_fpa and b.is_fpa) then
  begin
      r := Z3_mk_fpa_sub(a.ctx.ToZ3_Context, a.ctx.fpa_rounding_mode, a.ToZ3_ast, b.ToZ3_ast);
  end else
  begin
      // operator is not supported by given arguments.
      assert(false);
  end ;
  a.check_error();
  Result := TExpr.Create(a.ctx, r);

end;

function OpMinus(const a: TExpr; b: Integer): TExpr;
begin
    Result := OpMinus(a, a.ctx.num_val(b, a.get_sort));
end;

function OpMinus(a: Integer;const b: TExpr): TExpr;
begin
    Result := OpMinus(b.ctx.num_val(a, b.get_sort), b);
end;

function OpMinOrEq(const a: TExpr;const b: TExpr): TExpr;
var
  r    : Z3_ast;
begin
  check_context(a, b);
  r := nil;
  if (a.is_arith and b.is_arith) then
  begin
      r := Z3_mk_le(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
  end
  else if (a.is_bv and b.is_bv) then
  begin
      r := Z3_mk_bvsle(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
  end
  else if (a.is_fpa and b.is_fpa) then
  begin
      r := Z3_mk_fpa_leq(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
  end else
  begin
      // operator is not supported by given arguments.
      assert(false);
  end;
  a.check_error;
  Result := TExpr.Create(a.ctx, r);
end;

function OpMinOrEq(const a: TExpr; b: Integer): TExpr;
begin
   Result := OpMinOrEq(a, a.ctx.num_val(b, a.get_sort));
end;

function OpMinOrEq(a: Integer;const b: TExpr): TExpr;
begin
     Result := OpMinOrEq(b.ctx.num_val(a, b.get_sort) , b);
end;

function OpMajOrEq(const a: TExpr;const b: TExpr): TExpr;
var
  r    : Z3_ast;
begin
  check_context(a, b);
  r := nil;
  if (a.is_arith and b.is_arith) then
  begin
      r := Z3_mk_ge(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
  end
  else if (a.is_bv and b.is_bv) then
  begin
      r := Z3_mk_bvsge(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
  end else
  begin
      // operator is not supported by given arguments.
      assert(false);
  end;
  a.check_error;
  Result := TExpr.Create(a.ctx, r);
end;

function OpMajOrEq(const a: TExpr; b: Integer): TExpr;
begin
    Result :=  OpMajOrEq(a,a.ctx.num_val(b, a.get_sort));
end;

function OpMajOrEq(a: Integer;const b: TExpr): TExpr;
begin
    Result :=  OpMajOrEq(b.ctx.num_val(a, b.get_sort), b);
end;

function OpMinor(const a: TExpr;const b: TExpr): TExpr;
var
  r    : Z3_ast;
begin
  check_context(a, b);
  r := nil;
  if (a.is_arith and b.is_arith) then
  begin
      r := Z3_mk_lt(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
  end
  else if (a.is_bv and b.is_bv) then
  begin
      r := Z3_mk_bvslt(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
  end
  else if (a.is_fpa and b.is_fpa) then
  begin
      r := Z3_mk_fpa_lt(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
  end else
  begin
      // operator is not supported by given arguments.
      assert(false);
  end;
  a.check_error;
  Result := TExpr.Create(a.ctx, r);

end;

function OpMinor(const a: TExpr; b: Integer): TExpr;
begin
    Result :=  OpMinor(a, a.ctx.num_val(b, a.get_sort));
end;

function OpMinor(a: Integer;const b: TExpr): TExpr;
begin
   Result := OpMinor(b.ctx.num_val(a, b.get_sort), b);
end;

function OpMajor(const a: TExpr;const b: TExpr): TExpr;
var
  r    : Z3_ast;
begin
  check_context(a, b);
  r := nil;
  if (a.is_arith and b.is_arith) then
  begin
      r := Z3_mk_gt(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
  end
  else if (a.is_bv and b.is_bv) then
  begin
      r := Z3_mk_bvsgt(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
  end
  else if (a.is_fpa and b.is_fpa) then
  begin
      r := Z3_mk_fpa_gt(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
  end else
  begin
      // operator is not supported by given arguments.
      assert(false);
  end;
  a.check_error;
  Result := TExpr.Create(a.ctx, r);

end;

function OpMajor(const a: TExpr; b: Integer): TExpr;
begin
  Result :=  OpMajor(a, a.ctx.num_val(b, a.get_sort));
end;

function OpMajor(a: Integer;const b: TExpr): TExpr;
begin
   Result := OpMajor(b.ctx.num_val(a, b.get_sort), b);
end;

function pble(const es : TExpr_vector; const coeffs : Integer; bound: Integer): TExpr;
begin
    assert(es.size > 0);
    var ctx : TContext := es.Items[0].ctx;
    var _es : TZ3Array<Z3_ast> := es.ToArray;
    var    r: Z3_ast  := Z3_mk_pble(ctx.ToZ3_Context, _es.size, _es.ptr, @coeffs, bound);
    ctx.check_error;
    Result := TExpr.Create(ctx, r);
end;

function pbge(const es : TExpr_vector; const coeffs : Integer; bound: Integer): TExpr;
begin
    assert(es.size > 0);
    var ctx : TContext := es.Items[0].ctx;
    var _es : TZ3Array<Z3_ast> := es.ToArray;
    var    r: Z3_ast  := Z3_mk_pbge(ctx.ToZ3_Context, _es.size, _es.ptr, @coeffs, bound);
    ctx.check_error;
    Result := TExpr.Create(ctx, r);
end;

function pbeq(const es : TExpr_vector; const coeffs : Integer; bound: Integer): TExpr;
begin
   assert(es.size > 0);
   var ctx : TContext := es.Items[0].ctx;
   var _es : TZ3Array<Z3_ast> := es.ToArray;
   var    r: Z3_ast  := Z3_mk_pbeq(ctx.ToZ3_Context, _es.size, _es.ptr, @coeffs, bound);
   ctx.check_error;
   Result := TExpr.Create(ctx, r);
end;

function atmost(const es : TExpr_vector; bound: Cardinal): TExpr;
begin
   assert(es.size > 0);
   var ctx : TContext := es.Items[0].ctx;
   var _es : TZ3Array<Z3_ast> := es.ToArray;
   var    r: Z3_ast  := Z3_mk_atmost(ctx.ToZ3_Context, _es.size, _es.ptr, bound);
   ctx.check_error;
   Result := TExpr.Create(ctx, r);
end;

function atleast(const es : TExpr_vector; bound: Cardinal): TExpr;
begin
   assert(es.size > 0);
   var ctx : TContext := es.Items[0].ctx;
   var _es : TZ3Array<Z3_ast> := es.ToArray;
   var    r: Z3_ast  := Z3_mk_atleast(ctx.ToZ3_Context, _es.size, _es.ptr, bound);
   ctx.check_error;
   Result := TExpr.Create(ctx, r);
end;

function OpAndbv(const a: TExpr; const b: TExpr): TExpr;overload;
begin
    check_context(a, b);
    var r : Z3_ast := Z3_mk_bvand(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
    Result := TExpr.Create(a.ctx, r);
end;

function OpAndbv(const a: TExpr;b: Integer): TExpr;overload;
begin
    Result := OpAndbv(a, a.ctx.num_val(b, a.get_sort));
end;

function OpAndbv(a: Integer; const b: TExpr): TExpr;overload;
begin
   Result := OpAndbv(b.ctx.num_val(a, b.get_sort) ,b);
end;

function OpXorbv(const a: TExpr; const b: TExpr): TExpr; overload;
begin
   check_context(a, b);
   var r : Z3_ast := Z3_mk_bvxor(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
   Result := TExpr.Create(a.ctx, r);
end;

function OpXorbv(const a: TExpr;b: Integer): TExpr; overload;
begin
    Result := OpXorbv(a, a.ctx.num_val(b, a.get_sort));
end;

function OpXorbv(a: Integer; const b: TExpr): TExpr;overload;
begin
    Result := OpXorbv(b.ctx.num_val(a, b.get_sort) ,b);
end;

function OpOrbv(const a: TExpr; const b: TExpr): TExpr; overload;
begin
   check_context(a, b);
   var r : Z3_ast := Z3_mk_bvor(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
   Result := TExpr.Create(a.ctx, r);
end;

function OpOrbv(const a: TExpr;b: Integer): TExpr; overload;
begin
     Result := OpOrbv(a, a.ctx.num_val(b, a.get_sort));
end;

function OpOrbv(a: Integer; const b: TExpr): TExpr;overload;
begin
  Result := OpOrbv(b.ctx.num_val(a, b.get_sort) ,b);
end;

function nand(const a: TExpr; const b: TExpr): TExpr;
begin
   check_context(a, b);
   var r : Z3_ast := Z3_mk_bvnand(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
   Result := TExpr.Create(a.ctx, r);
end;

function nor(const a: TExpr; const b: TExpr): TExpr;
begin
  check_context(a, b);
  var r : Z3_ast := Z3_mk_bvnor(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
  Result := TExpr.Create(a.ctx, r);
end;

function xnor(const a: TExpr; const b: TExpr): TExpr;
begin
   check_context(a, b);
   var r : Z3_ast := Z3_mk_bvxnor(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
   Result := TExpr.Create(a.ctx, r);
end;

function min(const a: TExpr; const b: TExpr): TExpr;
var
 r : Z3_ast;
begin
  check_context(a, b);
  if (a.is_arith) then
  begin
      r := Z3_mk_ite(a.ctx.ToZ3_Context, Z3_mk_ge(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast), b.ToZ3_ast, a.ToZ3_ast);
  end
  else if (a.is_bv) then
  begin
      r := Z3_mk_ite(a.ctx.ToZ3_Context, Z3_mk_bvuge(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast), b.ToZ3_ast, a.ToZ3_ast);
  end else
  begin
      assert(a.is_fpa);
      r := Z3_mk_fpa_min(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
  end;
  Result := TExpr.Create(a.ctx, r);
end;

function max(const a: TExpr; const b: TExpr): TExpr;
var
 r : Z3_ast;
begin
  check_context(a, b);
  if (a.is_arith) then
  begin
      r := Z3_mk_ite(a.ctx.ToZ3_Context, Z3_mk_ge(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast), a.ToZ3_ast, b.ToZ3_ast);
  end
  else if (a.is_bv) then
  begin
      r := Z3_mk_ite(a.ctx.ToZ3_Context, Z3_mk_bvuge(a.ctx.ToZ3_Context, a, b), a.ToZ3_ast, b.ToZ3_ast);
  end else
  begin
      assert(a.is_fpa);
      r := Z3_mk_fpa_max(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
  end;
  Result := TExpr.Create(a.ctx, r);

end;

function abs(const a: TExpr): TExpr;
var
 r    : Z3_ast;
 zero : TExpr;
begin
  if (a.is_int) then
  begin
      zero := a.ctx.int_val(0);
      r    := Z3_mk_ite(a.ctx.ToZ3_Context, Z3_mk_ge(a.ctx.ToZ3_Context, a.ToZ3_ast, zero.ToZ3_ast), a.ToZ3_ast, OpMinus(a).ToZ3_ast);
  end
  else if (a.is_real) then
  begin
      zero := a.ctx.real_val(0);
      r    := Z3_mk_ite(a.ctx.ToZ3_Context, Z3_mk_ge(a.ctx.ToZ3_Context, a.ToZ3_ast, zero.ToZ3_ast), a, OpMinus(a).ToZ3_ast);
  end else
  begin
      r := Z3_mk_fpa_abs(a.ctx.ToZ3_Context, a.ToZ3_ast);
  end;
  Result := TExpr.Create(a.ctx, r);

end;

function sqrt(const a : TExpr; const rm: TExpr): TExpr;
begin

  check_context(a, rm);
  assert(a.is_fpa);
  var r : Z3_ast := Z3_mk_fpa_sqrt(a.ctx.ToZ3_Context, rm.ToZ3_ast, a.ToZ3_ast);
  Result := TExpr.Create(a.ctx, r);

end;

function OpNotbv(const a: TExpr): TExpr;
begin
    var r : Z3_ast := Z3_mk_bvnot(a.ctx.ToZ3_Context, a.ToZ3_app);
    Result := TExpr.Create(a.ctx, r);
end;

function fma(const a : TExpr; const b: TExpr; const c: TExpr;const rm: TExpr): TExpr;
begin
  check_context(a, b);
  check_context(a, c);
  check_context(a, rm);
  assert(a.is_fpa and b.is_fpa and c.is_fpa);
  var r : Z3_ast := Z3_mk_fpa_fma(a.ctx.ToZ3_Context, rm.ToZ3_ast, a.ToZ3_ast, b.ToZ3_ast, c.ToZ3_ast);
  a.check_error;
  Result := TExpr.Create(a.ctx, r);
end;

function range(const lo: TExpr; const hi: TExpr): TExpr;
begin
  check_context(lo, hi);
  var r : Z3_ast := Z3_mk_re_range(lo.ctx.ToZ3_Context, lo.ToZ3_ast, hi.ToZ3_ast);
  lo.check_error;
  Result := TExpr.Create(lo.ctx, r);
end;

//
function to_real(const a: TExpr): TExpr;
begin
    var r : Z3_ast := Z3_mk_int2real(a.ctx.ToZ3_Context, a.ToZ3_ast);
    a.check_error;
    Result := TExpr.Create(a.ctx, r);
end;

function &function(const name: TSymbol;   arity: Cardinal; const domain: TSort; const range: TSort): TFunc_decl; overload;
begin
    Result := range.ctx.&function(name, arity, domain, range);
end;

function &function(const name: PAnsiChar; arity: Cardinal; const domain: TSort; const range: TSort): TFunc_decl; overload;
begin
    Result := range.ctx.&function(name, arity, domain, range);
end;

function &function(const name: PAnsiChar; const domain: TSort; const range: TSort): TFunc_decl;overload;
begin
   Result := range.ctx.&function(name, domain, range);
end;

function &function(const name: PAnsiChar; const d1: TSort; const d2: TSort; const range: TSort): TFunc_decl; overload;
begin
   Result := range.ctx.&function(name, d1, d2, range);
end;

function &function(const name: PAnsiChar; const d1: TSort; const d2: TSort; const d3: TSort; const range: TSort) : TFunc_decl;overload;
begin
   Result := range.ctx.&function(name, d1, d2, d3, range);
end;

function &function(const name: PAnsiChar; const d1: TSort; const d2: TSort; const d3: TSort; const d4: TSort; const  range: TSort): TFunc_decl; overload;
begin
   Result := range.ctx.&function(name, d1, d2, d3, d4, range);
end;

function &function(const name: PAnsiChar; const d1: TSort; const d2: TSort; const d3: TSort; const d4: TSort; const d5: TSort; const range: TSort): TFunc_decl; overload;
begin
   Result := range.ctx.&function(name, d1, d2, d3, d4, d5, range);
end;

function &function(const name: PAnsiChar; const domain: TSort_vector; const range: TSort): TFunc_decl; overload;
begin
   Result := range.ctx.&function(name, domain, range);
end;

function &function(const name: AnsiString;const domain: TSort_vector; const range: TSort): TFunc_decl; overload;
begin
   Result := range.ctx.&function(PAnsiChar(name), domain, range);
end;

function recfun(const name: TSymbol;   arity: Cardinal; const domain: TSort; const range: TSort): TFunc_decl; overload;
begin
   Result := range.ctx.recfun(name, arity, domain, range);
end;

function recfun(const name: PAnsiChar; arity: Cardinal; const domain: Tsort; const range: TSort): TFunc_decl;overload;
begin
   Result := range.ctx.recfun(name, arity, domain, range);
end;

function recfun(const name: PAnsiChar; const d1: TSort; const range: TSort): TFunc_decl; overload;
begin
   Result := range.ctx.recfun(name, d1, range);
end;

function recfun(const name: PAnsiChar; const d1: TSort; const d2: TSort; const range: TSort): TFunc_decl;overload;
begin
   Result := range.ctx.recfun(name, d1, d2, range);
end;

function select(const a: TExpr;const  i: TExpr): TExpr;overload;
begin
  check_context(a, i);
  var r : Z3_ast := Z3_mk_select(a.ctx.ToZ3_Context, a.ToZ3_ast, i.ToZ3_ast);
  a.check_error;
  Result := TExpr.Create(a.ctx, r);
end;

function select(const a: TExpr;       i:Integer) : TExpr;  overload;
begin
  Result := select(a, a.ctx.num_val(i, a.get_sort.array_domain));
end;

function select(const a: TExpr; const i: TExpr_vector) : TExpr; overload;
begin
  check_context(a, i);
  var idxs : TZ3Array<Z3_ast>  := i.ToArray;
  var r : Z3_ast := Z3_mk_select_n(a.ctx.ToZ3_Context, a.ToZ3_ast, idxs.size, idxs.ptr);
  a.check_error;
  Result := TExpr.Create(a.ctx, r);
end;

function store (const a: TExpr; const i: TExpr;const          v: TExpr): TExpr;  overload;
begin
  check_context(a, i);
  check_context(a, v);
  var r : Z3_ast := Z3_mk_store(a.ctx.ToZ3_Context, a.ToZ3_ast, i.ToZ3_ast, v.ToZ3_ast);
  a.check_error();
  Result := TExpr.Create(a.ctx, r);
end;

function store (const a: TExpr;       i: Integer; const       v: TExpr): TExpr; overload;
begin
   Result := store(a, a.ctx.num_val(i, a.get_sort.array_domain), v);
end;

function store (const a: TExpr;       i: TExpr;               v: Integer): TExpr; overload;
begin
   Result := store(a, i, a.ctx.num_val(v, a.get_sort.array_range));
end;

function store (const a: TExpr;       i: Integer;             v: Integer): TExpr; overload;
begin
  Result := store(a, a.ctx.num_val(i, a.get_sort.array_domain), a.ctx.num_val(v, a.get_sort.array_range));
end;

function store(const  a: TExpr; const i: TExpr_vector; const  v: TExpr): TExpr;  overload;
begin
  check_context(a, i);
  check_context(a, v);
  var idxs : TZ3Array<Z3_ast> := i.ToArray;
  var r : Z3_ast := Z3_mk_store_n(a.ctx.ToZ3_Context, a.ToZ3_ast, idxs.size, idxs.ptr, v.ToZ3_ast);
  a.check_error;
  Result := TExpr.Create(a.ctx, r);
end;

function as_array(f: TFunc_decl): TExpr;
begin
  var r : Z3_ast := Z3_mk_as_array(f.ctx.ToZ3_Context, f.ToZ3_func_decl);
  f.check_error;
  Result := TExpr.Create(f.ctx, r);
end;

function const_array(const d: TSort; const v: TExpr): TExpr;
begin
  Result := MK_EXPR2(Z3_mk_const_array, d, v);
end;

function empty_set(const s: TSort): TExpr;
begin
  Result := MK_EXPR1(Z3_mk_empty_set, s);
end;

function full_set(const s: TSort): TExpr;
begin
   Result := MK_EXPR1(Z3_mk_full_set, s);
end;

function set_add(const s: TExpr; const e: TExpr): TExpr;
begin
   Result := MK_EXPR2(Z3_mk_set_add, s, e);
end;

function set_del(const s: TExpr; const e: TExpr): TExpr;
begin
  Result := MK_EXPR2(Z3_mk_set_del, s, e);
end;

function set_union(const a: TExpr; const b: TExpr): TExpr;
var
 es : TArray<Z3_ast>;
begin
  check_context(a, b);
  es := [ a, b ];
  var r : Z3_ast  := Z3_mk_set_union(a.ctx.ToZ3_Context, 2, @es[0]);
  a.check_error;
  Result := TExpr.Create(a.ctx, r);
end;

function set_intersect(const a: TExpr; const b: TExpr) : TExpr;
var
 es : TArray<Z3_ast>;
begin
  check_context(a, b);
  es := [ a, b ];
  var r : Z3_ast := Z3_mk_set_intersect(a.ctx.ToZ3_Context, 2, @es[0]);
  a.check_error;
  Result := TExpr.Create(a.ctx, r);
end;

function set_difference(const a: TExpr; const b: TExpr) : TExpr;
begin
  Result := MK_EXPR2(Z3_mk_set_difference, a, b);
end;

function set_complement(const a: TExpr): TExpr;
begin
   Result := MK_EXPR1(Z3_mk_set_complement, a);
end;

function set_member(const s: TExpr; const e: TExpr): TExpr;
begin
  Result := MK_EXPR2(Z3_mk_set_member, s, e);
end;

function set_subset(const a: TExpr; const b: TExpr): TExpr;
begin
  Result := MK_EXPR2(Z3_mk_set_subset, a, b);
end;

function empty(const s: TSort): TExpr;
begin
  var r : Z3_ast := Z3_mk_seq_empty(s.ctx.ToZ3_Context, s.ToZ3_Sort);
  s.check_error;
  Result := TExpr.Create(s.ctx, r);
end;

function suffixof(const a: TExpr; const b: TExpr): TExpr;
begin
  check_context(a, b);
  var r : Z3_ast := Z3_mk_seq_suffix(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
  a.check_error;
  Result := TExpr.Create(a.ctx, r);
end;

function prefixof(const a: TExpr; const b: TExpr): TExpr;
begin
  check_context(a, b);
  var r : Z3_ast := Z3_mk_seq_prefix(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast);
  a.check_error();
  Result := TExpr.Create(a.ctx, r);
end;

function indexof(const s: TExpr; const substr: TExpr; const offset: TExpr) : TExpr;
begin
  check_context(s, substr);
  check_context(s, offset);
  var r : Z3_ast := Z3_mk_seq_index(s.ctx.ToZ3_Context, s.ToZ3_ast, substr.ToZ3_ast, offset.ToZ3_ast);
  s.check_error;
  Result := TExpr.Create(s.ctx, r);
end;

function to_re(const s: TExpr): TExpr;
begin
  Result := MK_EXPR1(Z3_mk_seq_to_re, s);
end;

function in_re(const s: TExpr; const re: TExpr) : TExpr;
begin
  Result := MK_EXPR2(Z3_mk_seq_in_re, s, re);
end;

function plus(const re: TExpr): TExpr;
begin
  Result := MK_EXPR1(Z3_mk_re_plus, re);
end;

function option(const re: TExpr) : TExpr;
begin
  Result := MK_EXPR1(Z3_mk_re_option, re);
end;

function star(const re: TExpr): TExpr;
begin
  Result := MK_EXPR1(Z3_mk_re_star, re);
end;

function re_empty(const s: TSort) : TExpr;
begin
  var r : Z3_ast := Z3_mk_re_empty(s.ctx.ToZ3_Context, s.ToZ3_Sort);
  s.check_error;
  Result := TExpr.Create(s.ctx, r);
end;

function re_full(const s: TSort): TExpr;
begin
  var r : Z3_ast := Z3_mk_re_full(s.ctx.ToZ3_Context, s.ToZ3_Sort);
  s.check_error;
  Result := TExpr.Create(s.ctx, r);
end;

function re_intersect(const args: TExpr_vector ): TExpr;
var
 _args : TZ3Array<Z3_ast>;
begin
  assert(args.size() > 0);
  var ctx : TContext := args.Items[0].ctx;
  _args := args.ToArray;
  var r : Z3_ast := Z3_mk_re_intersect(ctx.ToZ3_Context, _args.size, _args.ptr);
  ctx.check_error;
  Result := Texpr.Create(ctx, r);

end;

function re_complement(const a: TExpr) : TExpr;
begin
  Result := MK_EXPR1(Z3_mk_re_complement, a);
end;

function to_expr(c: TContext; a: Z3_ast): TExpr ;
begin
    c.check_error;
    assert(
           (Z3_get_ast_kind(c.ToZ3_Context, a) = Z3_APP_AST) or
           (Z3_get_ast_kind(c.ToZ3_Context, a) = Z3_NUMERAL_AST) or
           (Z3_get_ast_kind(c.ToZ3_Context, a) = Z3_VAR_AST) or
           (Z3_get_ast_kind(c.ToZ3_Context, a) = Z3_QUANTIFIER_AST)
           );
    Result := TExpr.Create(c, a);

end;

function to_func_decl(c: TContext; f: Z3_func_decl): TFunc_decl ;
begin
  c.check_error;
  Result := TFunc_decl.Create(c, f);
end;

function ule(const a: TExpr;const b: TExpr): TExpr;overload;
begin
   Result := to_expr(a.ctx, Z3_mk_bvule(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast));
end;

function ule(const a: TExpr; b: Integer): TExpr; overload;
begin
    Result :=  ule(a, a.ctx.num_val(b, a.get_sort));
end;

function ule(a: Integer; const b: TExpr): TExpr ;overload;
begin
    Result := ule(b.ctx.num_val(a, b.get_sort), b);
end;

function ult(const a: TExpr; const b: TExpr): TExpr; overload;
begin
   Result := to_expr(a.ctx, Z3_mk_bvult(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast));
end;

function ult(const a: TExpr; b: Integer): TExpr;overload;
begin
   Result := ult(a, a.ctx.num_val(b, a.get_sort));
end;

function ult(a: Integer; const b: TExpr): TExpr; overload;
begin
   Result := ult(b.ctx.num_val(a, b.get_sort), b);
end;

function uge(const a: TExpr; const b: TExpr): TExpr; overload;
begin
   Result := to_expr(a.ctx, Z3_mk_bvuge(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast));
end;

function uge(const a: TExpr; b: Integer) : TExpr;overload;
begin
  Result := uge(a, a.ctx.num_val(b, a.get_sort));
end;

function uge(a: Integer; const b: TExpr): TExpr;overload;
begin
  Result := uge(b.ctx.num_val(a, b.get_sort), b);
end;

function ugt(const a: TExpr; const b: TExpr): TExpr;
begin
   Result := to_expr(a.ctx, Z3_mk_bvugt(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast));
end;

function ugt(const a: TExpr; b: Integer): TExpr ;
begin
   Result := ugt(a, a.ctx.num_val(b, a.get_sort));
end;

function ugt(a: Integer; const b: TExpr): TExpr;
begin
  Result := ugt(b.ctx.num_val(a, b.get_sort), b);
end;

function udiv(const a: TExpr; const b: TExpr): TExpr ;
begin
   Result := to_expr(a.ctx, Z3_mk_bvudiv(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast));
end;

function udiv(const a: TExpr; b: Integer): TExpr ;
begin
    Result := udiv(a, a.ctx.num_val(b, a.get_sort));
end;

function udiv(a: Integer; const b: TExpr): TExpr;
begin
   Result := udiv(b.ctx.num_val(a, b.get_sort), b);
end;

function srem(const a: TExpr; const b: TExpr): TExpr;
begin
  Result := to_expr(a.ctx, Z3_mk_bvsrem(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast));
end;

function srem(const a: TExpr; b: Integer): TExpr ;
begin
   Result := srem(a, a.ctx.num_val(b, a.get_sort));
end;

function srem(a: Integer; const b: TExpr): TExpr ;
begin
   Result := srem(b.ctx.num_val(a, b.get_sort), b);
end;

function smod(const a: TExpr; const b: TExpr): TExpr ;
begin
   Result := to_expr(a.ctx, Z3_mk_bvsmod(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast));
end;

function smod(const a: TExpr; b: Integer): TExpr ;
begin
   Result := smod(a, a.ctx.num_val(b, a.get_sort));
end;

function smod(a: Integer; const b: TExpr): TExpr;
begin
   Result := smod(b.ctx.num_val(a, b.get_sort), b);
end;

function urem(const a: TExpr; const b: TExpr): TExpr ;
begin
   Result := to_expr(a.ctx, Z3_mk_bvurem(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast));
end;

function urem(const a: TExpr; b: Integer): TExpr;
begin
    Result := urem(a, a.ctx.num_val(b, a.get_sort));
end;

function urem(a: Integer; const b: TExpr): TExpr;
begin
   Result := urem(b.ctx.num_val(a, b.get_sort), b);
end;

function &shl(const a: TExpr; const b: TExpr): TExpr;
begin
   Result := to_expr(a.ctx, Z3_mk_bvshl(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast));
end;

function &shl(const a: TExpr; b: Integer): TExpr ;
begin
  Result := &shl(a, a.ctx.num_val(b, a.get_sort));
end;

function &shl(a: Integer; const b: TExpr) : TExpr;
begin
   Result := &shl(b.ctx.num_val(a, b.get_sort), b);
end;

function lshr(const a: TExpr; const b: TExpr): TExpr ;
begin
    Result := to_expr(a.ctx, Z3_mk_bvlshr(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast));
end;

function lshr(const a: TExpr; b: Integer): TExpr;
begin
   Result := lshr(a, a.ctx.num_val(b, a.get_sort));
end;

function lshr(a: Integer; const b: TExpr): TExpr ;
begin
   Result := lshr(b.ctx.num_val(a, b.get_sort), b);
end;

function ashr(const a: TExpr; const b: TExpr): TExpr ;
begin
  Result := to_expr(a.ctx, Z3_mk_bvashr(a.ctx.ToZ3_Context, a.ToZ3_ast, b.ToZ3_ast));
end;

function ashr(const a: TExpr; b: Integer): TExpr ;
begin
   Result := ashr(a, a.ctx.num_val(b, a.get_sort));
end;

function ashr(a: Integer; const b: TExpr): TExpr ;
begin
   Result := ashr(b.ctx.num_val(a, b.get_sort), b);
end;

function zext(const a: TExpr; i: Cardinal): TExpr ;
begin
   Result := to_expr(a.ctx, Z3_mk_zero_ext(a.ctx.ToZ3_Context, i, a.ToZ3_ast));
end;

function sext(const a: TExpr; i: Cardinal): TExpr ;
begin
   Result := to_expr(a.ctx, Z3_mk_sign_ext(a.ctx.ToZ3_Context, i, a.ToZ3_ast));
end;

function forall(const x : TExpr; const b :TExpr): TExpr;overload;
begin
  check_context(x, b);
  var vars : Tarray<Z3_app> := [ x.ToZ3_app ];
  var r : Z3_ast := Z3_mk_forall_const(b.ctx.ToZ3_Context, 0, 1, @vars[0], 0, 0, b.ToZ3_ast);
  b.check_error;
  Result := TExpr.Create(b.ctx, r);
end;

function forall(const x1: TExpr; const x2:TExpr;  const b :TExpr): TExpr; overload;
begin
  check_context(x1, b);
  check_context(x2, b);
  var vars : Tarray<Z3_app> := [ x1.ToZ3_app, x2.ToZ3_app];
  var r : Z3_ast := Z3_mk_forall_const(b.ctx.ToZ3_Context, 0, 2, @vars[0], 0, 0, b.ToZ3_ast);
  b.check_error;
  Result := TExpr.Create(b.ctx, r);
end;

function forall(const x1: TExpr; const x2:TExpr;  const x3:TExpr; const b : TExpr): TExpr;overload;
begin
  check_context(x1, b);
  check_context(x2, b);
  check_context(x3, b);
  var vars : Tarray<Z3_app> := [x1.ToZ3_app, x2.ToZ3_app, x3.ToZ3_app ];
  var r : Z3_ast := Z3_mk_forall_const(b.ctx.ToZ3_Context, 0, 3, @vars[0], 0, 0, b.ToZ3_ast);
  b.check_error;
  Result := TExpr.Create(b.ctx, r);
end;

function forall(const x1: TExpr; const x2:TExpr;  const x3:TExpr; const x4: TExpr; const b: TExpr): TExpr;overload;
begin
  check_context(x1, b);
  check_context(x2, b);
  check_context(x3, b);
  check_context(x4, b);
  var vars : Tarray<Z3_app> := [x1.ToZ3_app, x2.ToZ3_app, x3.ToZ3_app, x4.ToZ3_app ];
  var r : Z3_ast := Z3_mk_forall_const(b.ctx.ToZ3_Context, 0, 4, @vars[0], 0, 0, b.ToZ3_ast);
  b.check_error;
  Result := TExpr.Create(b.ctx, r);
end;

function forall(const xs: TExpr_vector; const b: TExpr): TExpr;overload;
begin
  var vars : TZ3Array<Z3_app> := xs.ToArray;
  var r : Z3_ast := Z3_mk_forall_const(b.ctx.ToZ3_Context, 0, vars.size, vars.ptr, 0, 0, b.ToZ3_ast);
  b.check_error;
  Result := TExpr.Create(b.ctx, r);
end;

function exists(const x :TExpr; const b :TExpr): TExpr;overload;
begin
  (*
  check_context(x, b);
  Z3_app vars[] = {(Z3_app) x};
  Z3_ast r = Z3_mk_exists_const(b.ctx(), 0, 1, vars, 0, 0, b); b.check_error(); Result := TExpr.Create(b.ctx, r);
    *)
end;

function exists(const x1:TExpr; const x2:TExpr; const b :TExpr): TExpr;overload;
begin
 (*
  check_context(x1, b); check_context(x2, b);
  Z3_app vars[] = {(Z3_app) x1, (Z3_app) x2};
  Z3_ast r = Z3_mk_exists_const(b.ctx(), 0, 2, vars, 0, 0, b); b.check_error(); Result := TExpr.Create(b.ctx, r);
    *)
end;

function exists(const x1:TExpr; const x2:TExpr; const x3:TExpr; const b: TExpr): TExpr;overload;
begin
  (*
  check_context(x1, b); check_context(x2, b); check_context(x3, b);
  Z3_app vars[] = {(Z3_app) x1, (Z3_app) x2, (Z3_app) x3 };
  Z3_ast r = Z3_mk_exists_const(b.ctx(), 0, 3, vars, 0, 0, b); b.check_error(); Result := TExpr.Create(b.ctx, r);
    *)
end;

function exists(const x1:TExpr; const x2:TExpr; const x3:TExpr; const x4: TExpr; const b: TExpr): TExpr; overload;
begin
  (*
  check_context(x1, b); check_context(x2, b); check_context(x3, b); check_context(x4, b);
  Z3_app vars[] = {(Z3_app) x1, (Z3_app) x2, (Z3_app) x3, (Z3_app) x4 };
  Z3_ast r = Z3_mk_exists_const(b.ctx(), 0, 4, vars, 0, 0, b); b.check_error(); Result := TExpr.Create(b.ctx, r);
    *)
end;

function exists(const xs: TExpr_vector; const b: TExpr): TExpr;overload;
begin
  {
    array<Z3_app> vars(xs);
    Z3_ast r = Z3_mk_exists_const(b.ctx(), 0, vars.size(), vars.ptr(), 0, 0, b); b.check_error(); Result := TExpr.Create(b.ctx, r);
    }
end;

function lambda(const x:TExpr; const b: TExpr): TExpr;overload;
begin
   (*
    check_context(x, b);
    Z3_app vars[] = {(Z3_app) x};
    Z3_ast r = Z3_mk_lambda_const(b.ctx(), 1, vars, b); b.check_error(); Result := TExpr.Create(b.ctx, r);
    *)
end;

function lambda(const x1: TExpr; const x2:TExpr; const b : TExpr): TExpr;overload;
begin
   (*
    check_context(x1, b); check_context(x2, b);
    Z3_app vars[] = {(Z3_app) x1, (Z3_app) x2};
    Z3_ast r = Z3_mk_lambda_const(b.ctx(), 2, vars, b); b.check_error(); Result := TExpr.Create(b.ctx, r);
    *)
end;

function lambda(const x1: TExpr; const x2:TExpr; const x3: TExpr; const b: TExpr): TExpr;overload;
begin
 (*
  check_context(x1, b); check_context(x2, b); check_context(x3, b);
  Z3_app vars[] = {(Z3_app) x1, (Z3_app) x2, (Z3_app) x3 };
  Z3_ast r = Z3_mk_lambda_const(b.ctx(), 3, vars, b); b.check_error(); Result := TExpr.Create(b.ctx, r);
    *)
end;

function lambda(const x1: TExpr; const x2:TExpr; const x3: TExpr; const x4:TExpr; const b: TExpr): TExpr; overload;
begin
 (*
  check_context(x1, b); check_context(x2, b); check_context(x3, b); check_context(x4, b);
  Z3_app vars[] = {(Z3_app) x1, (Z3_app) x2, (Z3_app) x3, (Z3_app) x4 };
  Z3_ast r = Z3_mk_lambda_const(b.ctx(), 4, vars, b); b.check_error(); Result := TExpr.Create(b.ctx, r);
    *)
end;

function lambda(const xs: TExpr_vector; const  b: TExpr): TExpr;overload;
begin
   {
  array<Z3_app> vars(xs);
  Z3_ast r = Z3_mk_lambda_const(b.ctx(), vars.size(), vars.ptr(), b); b.check_error(); Result := TExpr.Create(b.ctx, r);
    }
end;

end.
