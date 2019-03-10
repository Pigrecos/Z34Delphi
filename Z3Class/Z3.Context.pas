{*******************************************************}
{                                                       }
{       Z3 Wrapper Class for Delphi                     }
{                                                       }
{       Unit and class for  Z3 Object                   }
{                           Z3_context,                 }
{                           Z3_symbol                   }
{                           Z3_params                   }
{                           Z3_ast                      }
{                            - Expr                     }
{                            - Z3_Sort                  }
{                            - Z3_func_decl             }
{                           Z3_ast_vector               }
{                            - Expr_vector              }
{                            - Sort_vector              }
{                            - Func_decl_vector         }
{                                                       }
{       Copyright (C) 2019 Pigrecos(Max)                }
{       All rights reserved.                            }
{       MIT License                                     }
{*******************************************************}


unit Z3.Context;

interface
     uses System.SysUtils,
          z3,
          z3_ast_containers,
          z3_fpa,
          z3.Def,
          Z3.Arr,
          Z3.Config;

type
   FUnOp   = function(c: Z3_context; arg1: Z3_ast): Z3_ast ; cdecl;
   FBinOp  = function(c: Z3_context; arg1: Z3_ast; arg2: Z3_ast): Z3_ast ; cdecl;

   TSymbol      = class;
   TSort        = class;
   TSort_vector = class;

   TFunc_decl        = class;
   TFunc_decl_vector = class;

   TExpr       = class ;
   TExpr_vector= class;
  (**
     \brief A Context manages all other Z3 objects, global configuration options, etc.
  *)
  TContext = class
    private
       m_enable_exceptions : Boolean;
       m_rounding_mode     : rounding_mode;
       m_ctx               : Z3_context ;
       procedure init(c: TConfig);
    public
        constructor  Create; overload;
        constructor  Create(c: TConfig);overload;
        constructor  Create(s: TContext); overload;
        destructor   Destroy;
        function ToZ3_Context: Z3_Context;
        (*
           \brief Auxiliary method used to check for API usage errors.
        *)
        function  check_error:Z3_error_code;
        procedure check_parser_error ;
        (*
           \brief The C++ API uses by defaults exceptions on errors.
           For applications that don't work well with exceptions (there should be only few)
           you have the ability to turn off exceptions. The tradeoffs are that applications
           have to be very careful about using check_error() after calls that may result in an
           erroneous state.
         *)
        procedure set_enable_exceptions(f: Boolean);
        function enable_exceptions:Boolean;
        (*
           \brief Update global parameter \c param with string \c value.
        *)
        procedure &set(const param : PAnsiChar; const value: PAnsiChar); overload;
        (*
           \brief Update global parameter \c param with Boolean \c value.
        *)
        procedure &set(const param : PAnsiChar; value: Boolean) ; overload;
        (*
           \brief Update global parameter \c param with Integer \c value.
        *)
        procedure &set(const param : PAnsiChar; value: Integer);overload;
         (*
           \brief Interrupt the current procedure being executed by any object managed by this context.
           This is a soft interruption: there is no guarantee the object will actually stop.
        *)
        procedure interrupt;
        (*
           \brief Create a Z3 symbol based on the given string.
        *)
        function str_symbol(const s: PAnsiChar): TSymbol;
        (*
           \brief Create a Z3 symbol based on the given integer.
        *)
        function int_symbol(n: Integer): TSymbol;
        (*
           \brief Return the Boolean sort.
        *)
        function bool_sort: TSort;
        (*
           \brief Return the integer sort.
        *)
        function int_sort:TSort;
        (*
           \brief Return the Real sort.
        *)
        function real_sort: TSort;
        (*
           \brief Return the Bit-vector sort of size \c sz. That is, the sort for bit-vectors of size \c sz.
        *)
        function bv_sort(sz: Cardinal):TSort;
        (*
           \brief Return the sort for ASCII strings.
         *)
        function string_sort: TSort;
        (*
           \brief Return a sequence sort over base sort \c s.
         *)
        function seq_sort(s: TSort): TSort;
        (*
           \brief Return a regular expression sort over sequences \c seq_sort.
         *)
        function re_sort(s: TSort):TSort;
        (*
           \brief Return an array sort for arrays from \c d to \c r.

           Example: Given a context \c c, <tt>c.array_sort(c.int_sort(), c.bool_sort())</tt> is an array sort from integer to Boolean.
        *)
        function array_sort(d, r: TSort):TSort; overload ;
        function array_sort(const d:TSort_vector; r:TSort):TSort;overload;
        (*
           \brief Return a floating point sort.
           \c ebits is a number of exponent bits,
           \c sbits	is a number of significand bits,
           \pre where ebits must be larger than 1 and sbits must be larger than 2.
         *)
        function fpa_sort(ebits, sbits: Cardinal):TSort;overload;
        (*
           \brief Return a FloatingPoint sort with given precision bitwidth (16, 32, 64 or 128).
         *)
        // template<size_t precision>
        function  fpa_sort(precision: Byte):TSort;overload;
        (*
           \brief Return a RoundingMode sort.
         *)
        function fpa_rounding_mode():TSort;
        (*
           \brief Sets RoundingMode of FloatingPoints.
         *)
        procedure set_rounding_mode(rm: rounding_mode);
        (*
           \brief Return an enumeration sort: enum_names[0], ..., enum_names[n-1].
           \c cs and \c ts are output parameters. The method stores in \c cs the constants corresponding to the enumerated elements,
           and in \c ts the predicates for testing if terms of the enumeration sort correspond to an enumeration.
        *)
        function enumeration_sort(const name: PAnsiChar; n: Cardinal; const enum_names: array of AnsiString; cs: TFunc_decl_vector; ts: TFunc_decl_vector):TSort;

        (*
           \brief Return a tuple constructor.
           \c name is the name of the returned constructor,
           \c n are the number of arguments, \c names and \c sorts are their projected sorts.
           \c projs is an output parameter. It contains the set of projection functions.
        *)
        function tuple_sort(const name: PAnsiChar; n: Cardinal; const names: array of AnsiString; Sorts: array of TSort; projs: TFunc_decl_vector): TFunc_decl;
        (*
           \brief create an uninterpreted sort with the name given by the string or symbol.
         *)
        function uninterpreted_Sort(const name: PAnsiChar):TSort; overload;
        function uninterpreted_sort(const name: TSymbol):TSort;overload;

        function &function(const name: TSymbol;   arity: Cardinal; const domain: array of TSort;const range: TSort):TFunc_decl;overload;
        function &function(const name: PAnsiChar; arity: Cardinal; const domain: array of TSort;const range: TSort):TFunc_decl;overload;
        function &function(const name: TSymbol;                    const domain: TSort_vector;  const range: TSort):TFunc_decl;overload;
        function &function(const name: PAnsiChar;                  const domain: TSort_vector;  const range: TSort):TFunc_decl;overload;
        function &function(const name: PAnsiChar;                  const domain: TSort;         const range: TSort):TFunc_decl;overload;
        function &function(const name: PAnsiChar; const d1: TSort; const d2: TSort; const range: TSort):TFunc_decl;overload;
        function &function(const name: PAnsiChar; const d1: TSort; const d2: TSort; const d3: TSort; const range: TSort):TFunc_decl;overload;
        function &function(const name: PAnsiChar; const d1: TSort; const d2: TSort; const d3: TSort; const d4: TSort; const range: TSort):TFunc_decl;overload;
        function &function(const name: PAnsiChar; const d1: TSort; const d2: TSort; const d3: TSort; const d4: TSort; const d5: TSort; const range: TSort):TFunc_decl;overload;

        function recfun(const name: TSymbol;   arity: Cardinal; const domain: array of TSort;  const range: TSort):TFunc_decl; overload;
        function recfun(const name: PAnsiChar; arity: Cardinal; const domain: array of TSort;  const range: TSort):TFunc_decl; overload;
        function recfun(const name: PAnsiChar;                  const d1: TSort;  const range: TSort):TFunc_decl; overload;
        function recfun(const name: PAnsiChar; const d1: TSort; const d2: TSort;  const range: TSort):TFunc_decl; overload;

        procedure      recdef(fun: TFunc_decl; const args: TExpr_vector; const body: TExpr);

        function constant  (const name: TSymbol;   const s: TSort):TExpr;overload;
        function constant  (const name: PAnsiChar; const s: TSort):TExpr;overload;
        function bool_const(const name: PAnsiChar):TExpr;
        function int_const (const name: PAnsiChar):TExpr;
        function real_const(const name: PAnsiChar):TExpr;
        function bv_const  (const name: PAnsiChar; sz: Cardinal):TExpr;
        function fpa_const (const name: PAnsiChar; ebits, sbits: Cardinal):TExpr; overload;

        //template<size_t precision>
        function fpa_const(const name: PAnsiChar; Precision: Byte):TExpr; overload;

        function bool_val(b: Boolean):TExpr;

        function int_val(n: Integer):TExpr;overload;
        function int_val(n: Cardinal):TExpr; overload;
        function int_val(n: int64):TExpr; overload;
        function int_val(n: uint64):TExpr; overload;
        function int_val(n: PAnsiChar):TExpr;overload;

        function real_val(n, d: Integer):TExpr; overload;
        function real_val(n: Integer):TExpr;  overload;
        function real_val(n: Cardinal):TExpr; overload;
        function real_val(n: Int64):TExpr; overload;
        function real_val(n: UInt64):TExpr; overload;
        function real_val(n: PAnsiChar):TExpr;overload;

        function bv_val(n: Integer;  sz: Cardinal):TExpr; overload;
        function bv_val(n: Cardinal; sz: Cardinal):TExpr;overload;
        function bv_val(n: int64;    sz: Cardinal):TExpr; overload;
        function bv_val(n: uint64;   sz: Cardinal):TExpr; overload;
        function bv_val(n: PAnsiChar;sz: Cardinal):TExpr; overload;
        function bv_val(n: Cardinal; const bits: Boolean):TExpr;overload;

        function fpa_val(n: double):TExpr; overload;
        function fpa_val(n: Single):TExpr; overload;

        function string_val(s: PAnsiChar):TExpr; overload;
        function string_val(s: AnsiString):TExpr;overload;

        function num_val(n: Integer; const s: TSort):TExpr;
        (*
           \brief parsing
         *)
        function parse_string(s:   PAnsiChar) :TExpr_vector; overload;
        function parse_file(ffile: PAnsiChar) :TExpr_vector; overload;

        function parse_string(s: PAnsiChar; const Sorts: TSort_vector; const decls: TFunc_decl_vector):TExpr_vector; overload;
        function parse_file  (s: PAnsiChar; const Sorts: TSort_vector; const decls: TFunc_decl_vector):TExpr_vector; overload;
  end;


 Z3Object  = class
    protected
       m_ctx : TContext;
    public
       constructor Create(c: TContext); overload;
       constructor Create(s: Z3Object);overload;
       function    ctx: TContext;
       function    check_error: Z3_error_code;


  end;

  TSymbol = class(Z3Object)
    private
     m_sym : Z3_symbol;
    public
     constructor Create(c: TContext; s: Z3_symbol);overload;
     constructor Create(const s: TSymbol); overload;
     function kind: Z3_symbol_kind;
     function ToStr: AnsiString;overload;
     function ToStr(s: TSymbol): AnsiString;overload;
     function To_int:Integer;

     function ToZ3_symbol:Z3_symbol;  // sostituisce conversione implicita
  end;

  TParams = class(Z3Object)
        m_params: Z3_params;
    public
        constructor Create(c: TContext);overload;
        constructor Create(const s: TParams);overload;
        destructor Destroy;
        function ToZ3_params: Z3_params;
        //params & operator=(params const & s)
        procedure &set(const k: PAnsiChar; b: Boolean) ; overload;
        procedure &set(const k: PAnsiChar; n: Cardinal); overload;
        procedure &set(const k: PAnsiChar; n: Double) ; overload;
        procedure &set(const k: PAnsiChar; const s: TSymbol);overload;
        procedure &set(const k: PAnsiChar; s: PAnsiChar);overload;
        function ToStr(const p: TParams): AnsiString;
  end;

  TAst = class(Z3Object)
    protected
       m_ast : Z3_ast;
    public
       constructor Create(c: TContext);overload;
       constructor Create(c: TContext; n : Z3_ast); overload;
       constructor Create(n : TAst); overload;
       destructor  Destroy; override;
       function ToZ3_ast:Z3_ast;                   //operator Z3_ast() const { return m_ast; }
       function NotNil: Boolean;                   // operator bool() const { return m_ast != 0; }
       function Assign(const s: TAst):TAst;        // ast & operator=(ast const & s)
       function Kind: Z3_ast_kind;
       function Hash:Cardinal;
       function ToStr:AnsiString;
  end;

  (**
     \brief A Z3 expression is used to represent formulas and terms. For Z3, a formula is any expression of sort Boolean.
      Every expression has a sort.
   *)
  TExpr = class(TAst)
    public
       constructor Create(c: TContext);overload;
       constructor Create(c: TContext; n : Z3_ast); overload;
       constructor Create(n : TExpr); overload;
       function Assign(const s: TExpr):TExpr;

       (*
          \brief Return the sort of this expression.
       *)
       function get_sort: TSort;

       (*
          \brief Return true if this is a Boolean expression.
       *)
       function is_bool:Boolean;
       (*
          \brief Return true if this is an integer expression.
       *)
       function is_int:Boolean;
       (*
          \brief Return true if this is a real expression.
       *)
       function is_real:Boolean;
       (*
          \brief Return true if this is an integer or real expression.
       *)
       function is_arith:Boolean;
       (*
          \brief Return true if this is a Bit-vector expression.
       *)
       function is_bv:Boolean;
       (*
          \brief Return true if this is a Array expression.
       *)
       function is_array:Boolean;
       (*
           \brief Return true if this is a Datatype expression.
       *)
       function is_datatype:Boolean;
       (*
           \brief Return true if this is a Relation expression.
       *)
       function is_relation:Boolean;
       (*
           \brief Return true if this is a sequence expression.
       *)
       function is_seq:Boolean;
       (*
           \brief Return true if this is a regular expression.
       *)
       function is_re:Boolean;

       (*
           \brief Return true if this is a Finite-domain expression.

           \remark Finite-domain is special kind of interpreted sort:
           is_bool, is_bv and is_finite_domain are mutually
           exclusive.

       *)
       function is_finite_domain:Boolean;
       (*
            \brief Return true if this is a FloatingPoint expression. .
       *)
       function is_fpa:Boolean;

       (*
           \brief Return true if this expression is a numeral.
           Specialized functions also return representations for the numerals as
           small integers, 64 bit integers or rational or decimal strings.
       *)
       function is_numeral:Boolean; overload;
       function is_numeral_i64(var i: int64):Boolean; overload;
       function is_numeral_u64(var i: uint64):Boolean; overload;
       function is_numeral_i(var i: Integer):Boolean; overload;
       function is_numeral_u(var i: Cardinal):Boolean; overload;
       function is_numeral(var s: AnsiString):Boolean; overload;
       function is_numeral(var s:AnsiString; precision: Cardinal):Boolean; overload;
       function is_numeral(var d: Double):Boolean; overload;
       (*
          \brief Return true if this expression is an application.
       *)
       function is_app:Boolean;
       (*
           \brief Return true if this expression is a constant (i.e., an application with 0 arguments).
       *)
       function is_const:Boolean;
       (*
          \brief Return true if this expression is a quantifier.
       *)
       function is_quantifier:Boolean;

       (*
          \brief Return true if this expression is a universal quantifier.
       *)
       function is_forall:Boolean;
       (*
          \brief Return true if this expression is an existential quantifier.
       *)
       function is_exists:Boolean;
       (*
           \brief Return true if this expression is a lambda expression.
       *)
       function is_lambda:Boolean;
       (*

           \brief Return true if this expression is a variable.
       *)
       function is_var:Boolean;
       (*
           \brief Return true if expression is an algebraic number.
       *)
       function is_algebraic:Boolean;

       (*
           \brief Return true if this expression is well sorted (aka type correct).
       *)
       function is_well_sorted:Boolean;

       (*
           \brief Return string representation of numeral or algebraic number
           This method assumes the expression is numeral or algebraic

           \pre is_numeral || is_algebraic
       *)
       function get_decimal_string(precision : Integer ):AnsiString;
       (*
           \brief retrieve unique identifier for expression.
       *)
       function id:Cardinal;

       (*
           \brief Return int value of numeral, throw if result cannot fit in
           machine int

           It only makes sense to use this function if the caller can ensure that
           the result is an integer or if exceptions are enabled.
           If exceptions are disabled, then use the is_numeral_i function.

           \pre is_numeral
       *)
       function  get_numeral_int: Integer;

       (*
          \brief Return uint value of numeral, throw if result cannot fit in
          machine uint

          It only makes sense to use this function if the caller can ensure that
          the result is an integer or if exceptions are enabled.
          If exceptions are disabled, then use the is_numeral_u function.
          \pre is_numeral
       *)
       function get_numeral_uint:Cardinal;

       (*
          \brief Return \c int64_t value of numeral, throw if result cannot fit in
          \c int64_t.

          \pre is_numeral
       *)
       function get_numeral_int64:int64;

       (*
          \brief Return \c uint64_t value of numeral, throw if result cannot fit in
          \c uint64_t.

          \pre is_numeral
       *)
       function get_numeral_uint64: uint64;

       function bool_value: Z3_lbool;

       function numerator:TExpr ;

       function denominator:TExpr ;

       function ToZ3_app: Z3_app; //operator Z3_app const

       (*
           \brief Return a RoundingMode sort.
        *)
       function fpa_rounding_mode: TSort;

       (*
           \brief Return the declaration associated with this application.
           This method assumes the expression is an application.

           \pre is_app
       *)
       function decl: TFunc_decl;
       (*
           \brief Return the number of arguments in this application.
           This method assumes the expression is an application.

           \pre is_app
       *)
       function num_args:Cardinal;
       (*
           \brief Return the i-th argument of this application.
           This method assumes the expression is an application.

           \pre is_app
           \pre i < num_args
       *)
       function arg(i: Cardinal):TExpr;

       (*
           \brief Return the 'body' of this quantifier.

           \pre is_quantifier
       *)
       function body:TExpr;

       function is_true:Boolean;
       function is_false:Boolean;
       function is_not:Boolean;
       function is_and:Boolean;
       function is_or:Boolean;
       function is_xor:Boolean;
       function is_implies:Boolean;
       function is_eq:Boolean;
       function is_ite:Boolean;

       function rotate_left(i: Cardinal): TExpr;
       function rotate_right(i: Cardinal): TExpr;
       function &repeat(i: Cardinal):  TExpr;

       function extract(hi, lo: Cardinal): TExpr;overload;
       function lo: Cardinal;
       function hi:Cardinal;

       (*
          \brief sequence and regular expression operations.
          + is overloaded as sequence concatenation and regular expression union.
           concat is overloaded to handle sequences and regular expressions
       *)
       function extract(const offset: TExpr; const length: TExpr): TExpr;overload;
       function replace(const src: TExpr; const dst: TExpr): TExpr;
       function &unit: TExpr;
       function contains(const s: TExpr): TExpr;
       function at(const index: TExpr): TExpr;
       function length: TExpr;
       function stoi: TExpr;
       function itos: TExpr;
       (*
           \brief create a looping regular expression.
       *)
       function loop(lo: Cardinal): TExpr;  overload;
       function loop(lo, hi:Cardinal): TExpr; overload;


       (*
           \brief Return a simplified version of this expression.
       *)
       function simplify: TExpr;overload ;
       (*
          \brief Return a simplified version of this expression. The parameter \c p is a set of parameters for the Z3 simplifier.
       *)
       function simplify(const p: TParams): TExpr; overload ;

       (*
          \brief Apply substitution. Replace src expressions by dst.
       *)
       function substitute(const src: TExpr_vector; const dst: TExpr_vector): TExpr; overload;

       (*
          \brief Apply substitution. Replace bound variables by expressions.
       *)
       function substitute(const dst: TExpr_vector): TExpr; overload;




  end;

  (**
     \brief A Z3 sort (aka type). Every expression (i.e., formula or term) in Z3 has a sort.
  *)
  TSort = class(TAst)
     public
       constructor Create(c: TContext);overload;
       constructor Create(c: TContext; a: Z3_ast);overload;
       constructor Create(s: TSort);overload;

       (*
           \brief retrieve unique identifier for func_decl.
       *)
       function id: Cardinal;

       (*
          \brief Return the internal sort kind.
       *)
       function sort_kind:Z3_sort_kind;
       (**
          \brief Return name of sort.
       *)
       function name : TSymbol;
       (*
            \brief Return true if this sort is the Boolean sort.
       *)
       function is_bool: Boolean;
       (*
           \brief Return true if this sort is the Integer sort.
       *)
       function is_int: Boolean;
       (*
           \brief Return true if this sort is the Real sort.
       *)
       function is_real: Boolean;
       (*
           \brief Return true if this sort is the Integer or Real sort.
       *)
       function is_arith: Boolean;
       (*
           \brief Return true if this sort is a Bit-vector sort.
       *)
       function is_bv: Boolean;
       (*
           \brief Return true if this sort is a Array sort.
       *)
       function is_array: Boolean;
       (*
           \brief Return true if this sort is a Datatype sort.
       *)
       function is_datatype: Boolean;
       (*
           \brief Return true if this sort is a Relation sort.
       *)
       function is_relation: Boolean;
       (*
           \brief Return true if this sort is a Sequence sort.
       *)
       function is_seq: Boolean;
       (*
           \brief Return true if this sort is a regular expression sort.
       *)
       function is_re: Boolean;
       (*
           \brief Return true if this sort is a Finite domain sort.
       *)
       function is_finite_domain: Boolean;
       (*
           \brief Return true if this sort is a Floating point sort.
       *)
       function is_fpa: Boolean;

       (*
          \brief Return the size of this Bit-vector sort.
         \pre is_bv
       *)
       function bv_size: Cardinal;
       function fpa_ebits: Cardinal;
       function fpa_sbits: Cardinal;
       (*
          \brief Return the domain of this Array sort.

          \pre is_array
       *)
       function array_domain: TSort;
        (*
            \brief Return the range of this Array sort.

            \pre is_array
        *)
       function array_range: TSort;

       Function ToZ3_Sort:Z3_sort;  // sostituisce conversione implicita
  end;

  (**
     \brief Function declaration (aka function definition). It is the signature of interpreted and uninterpreted functions in Z3.
      The basic building block in Z3 is the function application.
   *)
  TFunc_decl = class(TAst)
      public
        constructor Create(c: TContext); overload;
        constructor Create(c: TContext; n: Z3_func_decl);overload;
        constructor Create(const s: TFunc_decl); overload;
        function ToZ3_func_decl:Z3_func_decl;
        //func_decl & operator=(func_decl const & s) { return static_cast<func_decl&>(ast::operator=(s)); }

        (*
           \brief retrieve unique identifier for func_decl.
         *)
        function id: Cardinal;

        function arity: Cardinal;
        function domain(i: Cardinal):TSort;
        function range: TSort;
        function name:TSymbol;
        function decl_kind: Z3_decl_kind;

        function is_const: Boolean;

        function FunOf : TExpr; overload;
        function FunOf(n: Cardinal; const args:array of TExpr): TExpr;overload;
        function FunOf(const args: TExpr_vector): TExpr; overload;
        function FunOf(const  a: TExpr): TExpr;overload;
        function FunOf(a: Integer): TExpr; overload;
        function FunOf(const a1: TExpr; const a2: TExpr): TExpr; overload;
        function FunOf(const a1: TExpr; a2: Integer): TExpr; overload;
        function FunOf(a1: Integer; const a2: TExpr): TExpr;overload;
        function FunOf(const a1: TExpr; const a2: TExpr; const a3: TExpr): TExpr;overload;
        function FunOf(const a1: TExpr; const a2: TExpr; const a3: TExpr; const a4: TExpr): TExpr;overload;
        function FunOf(const a1: TExpr; const a2: TExpr; const a3: TExpr; const a4: TExpr; const a5: TExpr): TExpr;overload;
  end;

    TAst_vector_tpl<T: TAst> = class(Z3Object)
     private
       m_vector : Z3_ast_vector;
       procedure  init(v: Z3_ast_vector);
       function GetItem(Index: Cardinal): T; virtual; abstract;
     public
       constructor Create(c: TContext);overload;
       constructor Create(c: TContext; v: Z3_ast_vector);overload;
       constructor Create(s: TAst_vector_tpl<T>); overload;
       destructor  Destroy; override;
       function    Size:Cardinal;
       procedure   push_back(e: T );
       procedure   resize(sz: Cardinal);
       function    back: T ;
       procedure   pop_back;
       function    empty: Boolean;
       function    Assign(s : TAst_vector_tpl<T>):TAst_vector_tpl<T> ;
       function    &Set(idx: Cardinal; a: TAst): TAst_vector_tpl<T>;
       function    ToZ3_ast_vector:Z3_ast_vector;  // sostituisce conversione implicita
       function    ToStr: AnsiString; overload;
       function    ToStr(v : TAst_vector_tpl<T>): AnsiString;overload;

       { TODO -oMax -c : adding class iterator 18/02/2019 18:09:25 }
       property Items[Index: Cardinal]: T read GetItem ;
  end;

  TSort_vector     = class (TAst_vector_tpl<TSort>)
     private
       function GetItem(Index: Cardinal): TSort;  override;
     public
       function ToArray: TZ3Array<Z3_sort>;
  end;

  TExpr_vector      = class (TAst_vector_tpl<TExpr>)
       function GetItem(Index: Cardinal): TExpr; override;
     public
       function ToArray: TZ3Array<Z3_ast>;
  end;

  TFunc_decl_vector = class (TAst_vector_tpl<TFunc_decl>)
       function GetItem(Index: Cardinal): TFunc_decl; override;
     public
       function ToArray: TZ3Array<Z3_func_decl>;
  end;


implementation
       uses Z3.Func;

{TContext }

constructor TContext.Create(c: TConfig);
begin
    init(c);
end;

constructor TContext.Create;
begin
     init( TConfig.Create);
end;

constructor TContext.Create(s:TContext);
begin
    m_enable_exceptions := s.m_enable_exceptions;
    m_rounding_mode     := s.m_rounding_mode ;
    m_ctx               := s.m_ctx;
end;

destructor TContext.Destroy;
begin
    Z3_del_context(m_ctx)
end;

procedure TContext.init(c: TConfig);
begin
    m_ctx := Z3_mk_context_rc(c.ToZ3_config);
    m_enable_exceptions := true;
    m_rounding_mode := RNA;
    Z3_set_error_handler(m_ctx, nil);
    Z3_set_ast_print_mode(m_ctx, Z3_PRINT_SMTLIB2_COMPLIANT);
end;

procedure TContext.interrupt;
begin
     Z3_interrupt(m_ctx)
end;

procedure TContext.&set(const param, value: PAnsiChar);
begin
    Z3_update_param_value(m_ctx, param, value)
end;

procedure TContext.&set(const param: PAnsiChar; value: Boolean);
begin
    if value then Z3_update_param_value(m_ctx, param, 'true' )
    else          Z3_update_param_value(m_ctx, param, 'false' )
end;

procedure TContext.&set(const param: PAnsiChar; value: Integer);
var
  s : AnsiString;
begin
    s := AnsiString(IntToStr(value));
    Z3_update_param_value(m_ctx, param, @s[1])
end;

procedure TContext.set_enable_exceptions(f: Boolean);
begin
    m_enable_exceptions := f
end;

function TContext.enable_exceptions: Boolean;
begin
    Result := m_enable_exceptions
end;

function TContext.check_error: Z3_error_code;
var
  e : Z3_error_code;
begin
    e := Z3_get_error_code(m_ctx);
    if (e <> Z3_OK) and (enable_exceptions) then
          raise   TZ3Exception.Create(Z3_get_error_msg(m_ctx, e));
    Result := e;

end;

procedure TContext.check_parser_error;
begin
    check_error
end;


function TContext.bool_const(const name: PAnsiChar): TExpr;
begin
    Result := constant(name, bool_sort);
end;

function TContext.bool_val(b: Boolean): TExpr;
begin
     if b  then Result := TExpr.Create(self, Z3_mk_true(m_ctx))
     else       Result := TExpr.Create(self, Z3_mk_false(m_ctx))
end;

function TContext.bv_const(const name: PAnsiChar; sz: Cardinal): TExpr;
begin
    Result:= constant(name, bv_sort(sz));
end;

function TContext.bv_val(n: PAnsiChar; sz: Cardinal): TExpr;
begin
     var s : TSort  := bv_sort(sz);
     var r : Z3_ast := Z3_mk_numeral(m_ctx, n, s.ToZ3_Sort);
     check_error;
     Result := TExpr.Create(Self, r);
end;

function TContext.bv_val(n: uint64; sz: Cardinal): TExpr;
begin
    var s : Tsort := bv_sort(sz);
    var r : Z3_ast:= Z3_mk_unsigned_int64(m_ctx, n, s.ToZ3_Sort);
    check_error;
    Result := TExpr.Create(Self, r);
end;

function TContext.bv_val(n: int64; sz: Cardinal): TExpr;
begin
    var  s : TSort := bv_sort(sz);
    var  r : Z3_ast:= Z3_mk_int64(m_ctx, n, s.ToZ3_Sort);
    check_error;
    Result := TExpr.Create(Self, r);
end;

function TContext.bv_val(n, sz: Cardinal): TExpr;
begin
     var s : TSort := bv_sort(sz);
     var r : Z3_ast:= Z3_mk_unsigned_int(m_ctx, n, s.ToZ3_Sort);
     check_error;
     Result := TExpr.Create(Self, r);
end;

function TContext.bv_val(n: Integer; sz: Cardinal): TExpr;
begin
    var s : TSort := bv_sort(sz);
    var r : Z3_ast:= Z3_mk_int(m_ctx, n, s.ToZ3_Sort);
    check_error;
    Result := TExpr.Create(Self, r);
end;

function TContext.bv_val(n: Cardinal; const bits: Boolean): TExpr;
begin
     { TODO -oMax -c : Verificare 19/02/2019 10:00:06 }
     Assert(False ,'Verificare!!!!!');
     var  _bits : TZ3Array<Boolean> := TZ3Array<Boolean>.Create(n);
     //for var i : Cardinal := 0 to n - 1 do
     //   _bits[i] = bits[i] ? 1 : 0;
     var r : Z3_ast  := Z3_mk_bv_numeral(m_ctx, n, _bits.ptr);
     check_error;
     Result := TExpr.Create(Self, r);

end;

function TContext.constant(const name: TSymbol; const s: TSort): TExpr;
begin
    var r : Z3_ast := Z3_mk_const(m_ctx, name, s.ToZ3_Sort);
    check_error;
    Result := TExpr.Create( self, r);
end;

function TContext.constant(const name: PAnsiChar; const s: TSort): TExpr;
begin
    var r : Z3_ast  := Z3_mk_const(m_ctx, name, s.ToZ3_Sort);
    check_error;
    Result := TExpr.Create(Self, r)
end;

function TContext.int_val(n: Integer): TExpr;
begin
    var r : Z3_ast := Z3_mk_int(m_ctx, n, int_sort.ToZ3_Sort);
    check_error;
    Result := TExpr.Create(Self, r);
end;

function TContext.int_val(n: Cardinal): TExpr;
begin
    var r : Z3_ast := Z3_mk_unsigned_int(m_ctx, n, int_sort.ToZ3_Sort);
    check_error;
    Result := TExpr.Create(Self, r);
end;

function TContext.int_val(n: int64): TExpr;
begin
    var r : Z3_ast := Z3_mk_int64(m_ctx, n, int_sort.ToZ3_Sort);
    check_error;
    Result := TExpr.Create(Self, r);
end;

function TContext.int_val(n: uint64): TExpr;
begin
    var r : Z3_ast := Z3_mk_unsigned_int64(m_ctx, n, int_sort.ToZ3_Sort);
    check_error;
    Result := TExpr.Create(Self, r);
end;

function TContext.int_val(n: PAnsiChar): TExpr;
begin
     var r : Z3_ast := Z3_mk_numeral(m_ctx, n, int_sort.ToZ3_Sort);
     check_error;
     Result := TExpr.Create(Self, r);
end;

function TContext.num_val(n: Integer; const s: TSort): TExpr;
begin
    var r : Z3_ast := Z3_mk_int(m_ctx, n, s.ToZ3_Sort);
    check_error;
    Result := TExpr.Create(self, r);
end;

function TContext.fpa_const(const name: PAnsiChar; Precision: Byte): TExpr;
begin
    Result := constant(name, fpa_sort(Precision));
end;

function TContext.fpa_const(const name: PAnsiChar; ebits, sbits: Cardinal): TExpr;
begin
    Result := constant(name, fpa_sort(ebits, sbits));
end;

function TContext.fpa_val(n: Single): TExpr;
begin
    var s : TSort := fpa_sort(32);
    var r : Z3_ast:= Z3_mk_fpa_numeral_float(m_ctx, n, s.ToZ3_Sort);
    check_error;
    Result := TExpr.Create(Self, r);
end;

function TContext.fpa_val(n: double): TExpr;
begin
    var s : TSort := fpa_sort(64);
    var r : Z3_ast:= Z3_mk_fpa_numeral_double(m_ctx, n, s.ToZ3_Sort);
    check_error;
    Result := TExpr.Create(Self, r);
end;

function TContext.real_const(const name: PAnsiChar): TExpr;
begin
    Result := constant(name, real_sort);
end;

function TContext.real_val(n: PAnsiChar): TExpr;
begin
     Var r : Z3_ast := Z3_mk_numeral(m_ctx, n, real_sort.ToZ3_Sort);
     check_error;
     Result := TExpr.Create(Self, r);
end;

function TContext.real_val(n: UInt64): TExpr;
begin
    var r : Z3_ast := Z3_mk_unsigned_int64(m_ctx, n, real_sort.ToZ3_Sort);
    check_error;
    Result := TExpr.Create(Self, r);
end;

function TContext.real_val(n: Int64): TExpr;
begin
    var r : Z3_ast := Z3_mk_int64(m_ctx, n, real_sort.ToZ3_Sort);
    check_error;
    Result := TExpr.Create(Self, r);
end;

function TContext.real_val(n: Integer): TExpr;
begin
     var r : Z3_ast := Z3_mk_int(m_ctx, n, real_sort.ToZ3_Sort);
     check_error;
     Result := TExpr.Create(Self, r);
end;

function TContext.real_val(n: Cardinal): TExpr;
begin
    var r : Z3_ast := Z3_mk_unsigned_int(m_ctx, n, real_sort.ToZ3_Sort);
    check_error;
    Result := TExpr.Create(Self, r);
end;

function TContext.real_val(n, d: Integer): TExpr;
begin
    var r : Z3_ast := Z3_mk_real(m_ctx, n, d);
    check_error;
    Result := TExpr.Create(Self, r);
end;

function TContext.int_const(const name: PAnsiChar): TExpr;
begin
    Result := constant(name, int_sort);
end;

function TContext.string_val(s: AnsiString): TExpr;
begin
    var r : Z3_ast := Z3_mk_string(m_ctx, @s);
    check_error;
    Result := TExpr.Create(Self, r);
end;

function TContext.string_val(s: PAnsiChar): TExpr;
begin
    var r : Z3_ast := Z3_mk_string(m_ctx, s);
    check_error;
    Result := TExpr.Create(Self, r);
end;

procedure TContext.recdef(fun: TFunc_decl; const args: TExpr_vector; const body: TExpr);
var
  vars : TZ3Array<Z3_ast>;
begin
    check_context(fun, args);
    check_context(fun, body);
    vars := args.ToArray;
    Z3_add_rec_def(fun.ctx.ToZ3_Context, fun.ToZ3_func_decl, vars.size, vars.ptr, body.ToZ3_ast);
end;

function TContext.recfun(const name: TSymbol; arity: Cardinal; const domain: array of TSort;  const range: TSort): TFunc_decl;
var
  args : TZ3Array<Z3_sort>;
  i    : Integer;
begin
    args := TZ3Array<Z3_sort>.Create(arity);
    for i := 0  to arity -1 do
    begin
        check_context(domain[i], range);
        args.Items[i] := domain[i];
    end;
    var f : Z3_func_decl := Z3_mk_rec_func_decl(m_ctx, name.ToZ3_symbol, arity, args.ptr, range.ToZ3_Sort);
    check_error;
    Result := TFunc_decl.Create(Self, f);
end;

function TContext.recfun(const name: PAnsiChar; arity: Cardinal; const domain: array of TSort; const range: TSort): TFunc_decl;
begin
    Result := recfun(str_symbol(name), arity, domain, range);
end;


function TContext.recfun(const name: PAnsiChar; const d1, d2, range: TSort): TFunc_decl;
var
  dom : array of TSort;
begin
    dom := [ d1, d2 ];
    Result := recfun(str_symbol(name), 2, dom, range);
end;

function TContext.recfun(const name: PAnsiChar; const d1: TSort; const range: TSort): TFunc_decl;
begin
     Result := recfun(str_symbol(name), 1, [d1], range);
end;

function TContext.&function(const name: PAnsiChar; const domain: TSort; const range: TSort): TFunc_decl;
var
  args : array of Z3_sort;
begin
    check_context(domain, range);
    args := [ domain.ToZ3_Sort ];
    var f : Z3_func_decl := Z3_mk_func_decl(m_ctx, str_symbol(name).ToZ3_symbol, 1, @args[0], range.ToZ3_Sort);
    check_error;
    Result := TFunc_decl.Create(self, f);
end;

function TContext.&function(const name: PAnsiChar; const d1, d2, range: TSort): TFunc_decl;
var
  args : array of Z3_sort;
begin
    check_context(d1, range);
    check_context(d2, range);
    args := [d1.ToZ3_Sort, d2.ToZ3_Sort ];
    var f : Z3_func_decl := Z3_mk_func_decl(m_ctx, str_symbol(name).ToZ3_symbol, 2, @args[0], range.ToZ3_Sort);
    check_error;
    Result := TFunc_decl.Create(self, f);
end;

function TContext.&function(const name: PAnsiChar; const d1, d2, d3, range: TSort): TFunc_decl;
var
  args : array of Z3_sort;
begin
    check_context(d1, range);
    check_context(d2, range);
    check_context(d3, range);
    args := [ d1.ToZ3_Sort, d2.ToZ3_Sort, d3.ToZ3_Sort ];
    var f : Z3_func_decl := Z3_mk_func_decl(m_ctx, str_symbol(name).ToZ3_symbol, 3, @args[0], range.ToZ3_Sort);
    check_error;
    Result := TFunc_decl.Create(self, f);
end;

function TContext.&function(const name: PAnsiChar; const d1, d2, d3, d4, range: TSort): TFunc_decl;
var
  args : array of Z3_sort;
begin
    check_context(d1, range);
    check_context(d2, range);
    check_context(d3, range);
    check_context(d4, range);
    args := [ d1.ToZ3_Sort, d2.ToZ3_Sort, d3.ToZ3_Sort, d4.ToZ3_Sort ];
    var f : Z3_func_decl := Z3_mk_func_decl(m_ctx, str_symbol(name).ToZ3_symbol, 4, @args[0], range.ToZ3_Sort);
    check_error;
    Result := TFunc_decl.Create(self, f);
end;

function TContext.&function(const name: PAnsiChar; const d1, d2, d3, d4, d5, range: TSort): TFunc_decl;
var
  args : array of Z3_sort;
begin
    check_context(d1, range);
    check_context(d2, range);
    check_context(d3, range);
    check_context(d4, range);
    check_context(d5, range);
    args := [ d1.ToZ3_Sort, d2.ToZ3_Sort, d3.ToZ3_Sort, d4.ToZ3_Sort, d5.ToZ3_Sort ];
    var f : Z3_func_decl := Z3_mk_func_decl(m_ctx, str_symbol(name).ToZ3_symbol, 5, @args[0], range.ToZ3_Sort);
    check_error;
    Result := TFunc_decl.Create(self, f);
end;

function TContext.&function(const name: TSymbol; arity: Cardinal; const domain: array of TSort; const range: TSort): TFunc_decl;
var
  args : TZ3Array<Z3_sort>;
  i    : Integer;
begin
    args := TZ3Array<Z3_sort>.Create(arity);
    for i := 0 to arity - 1 do
    begin
        check_context(domain[i], range);
        args.Items[i] := domain[i];
    end;
    var f : Z3_func_decl := Z3_mk_func_decl(m_ctx, name.ToZ3_symbol, arity, args.ptr, range.ToZ3_Sort);
    check_error;
    Result := TFunc_decl.Create(self, f);

end;

function TContext.&function(const name: PAnsiChar; arity: Cardinal; const domain: array of TSort; const range: TSort): TFunc_decl;
begin
    Result := &function(range.ctx.str_symbol(name), arity, domain, range);
end;

function TContext.&function(const name: PAnsiChar; const domain: TSort_vector; const range: TSort): TFunc_decl;
begin
    Result := &function(range.ctx.str_symbol(name), domain, range);
end;

function TContext.&function(const name: TSymbol; const domain: TSort_vector; const range: TSort): TFunc_decl;
var
  args : TZ3Array<Z3_sort>;
  i    : Integer;
begin
    args := TZ3Array<Z3_sort>.Create(domain.size);
    for i := 0 to domain.size - 1 do
    begin
        check_context(domain.Items[i], range);
        args.Items[i] := domain.Items[i];
    end;
    var f : Z3_func_decl := Z3_mk_func_decl(m_ctx, name.ToZ3_symbol, domain.size, args.ptr, range.ToZ3_Sort);
    check_error;
    Result := TFunc_decl.Create(self, f);
end;

function TContext.str_symbol(const s: PAnsiChar): TSymbol;
 var
   r : Z3_symbol ;
begin
    r := Z3_mk_string_symbol(m_ctx, s);
    check_error;
    Result :=  TSymbol.Create(Self, r);
end;

function TContext.ToZ3_Context: Z3_Context;
begin
   result :=  m_ctx;
end;

function TContext.int_symbol(n: Integer): TSymbol;
var
  r : Z3_symbol;
begin
    r := Z3_mk_int_symbol(m_ctx, n);
    check_error;
    Result := TSymbol.Create(Self, r);
end;

function TContext.bool_Sort: TSort;
var
  s : Z3_Sort;
begin
     s := Z3_mk_bool_Sort(m_ctx);
     check_error;
     Result := TSort.Create(Self, s);
end;

function TContext.int_Sort: TSort;
var
  s : Z3_Sort;
begin
    s := Z3_mk_int_Sort(m_ctx);
    check_error;
    Result := TSort.Create(Self, s);
end;

function TContext.real_Sort: TSort;
var
  s : Z3_Sort;
begin
    s := Z3_mk_real_Sort(m_ctx);
    check_error;
    Result := TSort.Create(Self, s);
end;

function TContext.bv_Sort(sz: Cardinal): TSort;
var
  s : Z3_Sort;
begin
    s := Z3_mk_bv_Sort(m_ctx, sz);
    check_error;
    Result := TSort.Create(Self, s);
end;

function TContext.string_Sort: TSort;
var
  s : Z3_Sort;
begin
    s := Z3_mk_string_Sort(m_ctx);
    check_error;
    Result := TSort.Create(Self, s);
end;

function TContext.seq_Sort(s: TSort): TSort;
var
  r : Z3_Sort;
begin
    r := Z3_mk_seq_Sort(m_ctx, s.ToZ3_Sort);
    check_error;
    Result := TSort.Create(Self, r)
end;

function TContext.re_Sort(s: TSort): TSort;
var
  r : Z3_Sort;
begin
     r := Z3_mk_re_Sort(m_ctx, s.ToZ3_Sort);
     check_error;
     Result := TSort.Create(Self, r)
end;

function TContext.fpa_Sort(ebits, sbits: Cardinal): TSort;
var
  s : Z3_Sort;
begin
    s := Z3_mk_fpa_Sort(m_ctx, ebits, sbits);
    check_error;
    Result := TSort.Create(Self, s);
end;

function TContext.fpa_Sort(precision: Byte): TSort;
begin
    case precision of
      16:  Result := fpa_Sort(5, 11);
      32:  Result := fpa_Sort(8, 24);
      64:  Result := fpa_Sort(11, 53);
      128: Result := fpa_Sort(15, 113);
    else  begin
             TZ3Exception.Create('Precison Out of Limit.');
             Result := fpa_Sort(5, 11);
          end;
    end;
end;

function TContext.fpa_rounding_mode: TSort;
begin
    case m_rounding_mode of
      RNA: Result := TSort.Create(Self, Z3_mk_fpa_rna(m_ctx));
      RNE: Result := TSort.Create(Self, Z3_mk_fpa_rne(m_ctx));
      RTP: Result := TSort.Create(Self, Z3_mk_fpa_rtp(m_ctx));
      RTN: Result := TSort.Create(Self, Z3_mk_fpa_rtn(m_ctx));
      RTZ: Result := TSort.Create(Self, Z3_mk_fpa_rtz(m_ctx));
    else
      Result :=  TSort.Create(Self);
    end;
end;

function TContext.array_Sort(d, r: TSort): TSort;
begin
     var s : Z3_Sort := Z3_mk_array_Sort(m_ctx, d, r);
     check_error;
     Result := TSort.Create(Self, s);
end;

function TContext.array_Sort(const d: TSort_vector; r: TSort): TSort;
var
  dom : TZ3Array<Z3_Sort>;
begin
    dom := d.ToArray;

    var s   : Z3_Sort  := Z3_mk_array_Sort_n(m_ctx, dom.size, dom.ptr, r);

    check_error;
    Result := TSort.Create(Self, s);

end;

function TContext.enumeration_Sort(const name: PAnsiChar; n: Cardinal;  const enum_names: array of AnsiString; cs, ts: TFunc_decl_vector): TSort;
var
  _enum_names : TZ3Array<Z3_symbol>;
  _cs, _ts    : TZ3Array<Z3_func_decl>;
  _name       : Z3_symbol;
  s           : TSort;
  i : Integer;
begin
    _enum_names := TZ3Array<Z3_symbol>.Create(n);

    for i := 0 to  n -1 do
       _enum_names.Items[i] := Z3_mk_string_symbol(Self, @enum_names[i]);

     _cs := TZ3Array<Z3_func_decl>.Create(n);
     _ts := TZ3Array<Z3_func_decl>.Create(n);

     _name := Z3_mk_string_symbol(self, name);
     s     := to_Sort( Self , Z3_mk_enumeration_Sort(Self, _name, n, _enum_names.ptr, _cs.ptr, _ts.ptr) );
     check_error;
     for i := 0  to n - 1 do
     begin
         cs.push_back(TFunc_decl.Create(Self, _cs.Items[i]));
         ts.push_back(TFunc_decl.Create(Self, _ts.Items[i]));
     end;
     Result := s;

end;

function TContext.tuple_Sort(const name: PAnsiChar; n: Cardinal; const names: array of AnsiString; Sorts: array of TSort; projs: TFunc_decl_vector): TFunc_decl;
var
  _names   : TZ3Array<Z3_symbol>;
  _Sorts   : TZ3Array<Z3_Sort>;
  _projs   : TZ3Array<Z3_func_decl>;
  _ignore_s: TSort;
  _name    : Z3_symbol;
  tuple    : Z3_func_decl;
  i        : Integer;
begin
    _names := TZ3Array<Z3_symbol>.Create(n);
    _Sorts := TZ3Array<Z3_Sort>.Create(n);

    for i := 0 to  n - 1 do
    begin
        _names.Items[i] := Z3_mk_string_symbol(Self, @names[i]);
        _Sorts.Items[i] := Sorts[i].ToZ3_Sort;
    end;
    _projs    := TZ3Array<Z3_func_decl>.Create(n);
    _name     := Z3_mk_string_symbol(Self, name);
    _ignore_s := to_Sort(Self, Z3_mk_tuple_Sort(Self, _name, n, _names.ptr, _Sorts.ptr, @tuple, _projs.ptr));
    check_error;
    for i := 0 to n -1 do
      projs.push_back(TFunc_decl.Create(Self, _projs.Items[i]) );

    Result := TFunc_decl.Create(Self, tuple);

end;

function TContext.uninterpreted_Sort(const name: PAnsiChar): TSort;
begin
    var _name : Z3_symbol := Z3_mk_string_symbol(Self, name);
    Result                :=  to_Sort(Self, Z3_mk_uninterpreted_Sort(Self, _name));

end;

function TContext.uninterpreted_Sort(const name: TSymbol): TSort;
begin
    Result := to_Sort(Self, Z3_mk_uninterpreted_Sort(Self, name));
end;

procedure TContext.set_rounding_mode(rm: rounding_mode);
begin
    m_rounding_mode := rm
end;

function TContext.parse_file(ffile: PAnsiChar): TExpr_vector;
begin
   var r : Z3_ast_vector := Z3_parse_smtlib2_file(Self, ffile, 0, 0, 0, 0, 0, 0);
   check_error;
   Result := TExpr_vector.Create(Self, r);
end;

function TContext.parse_file(s: PAnsiChar; const Sorts: TSort_vector; const decls: TFunc_decl_vector): TExpr_vector;
var
  sort_names : TZ3Array<Z3_symbol> ;
  decl_names : TZ3Array<Z3_symbol> ;
  sorts1     : TZ3Array<Z3_sort> ;
  decls1     : TZ3Array<Z3_func_decl> ;
  i          : Integer;
begin
    sort_names := TZ3Array<Z3_symbol>.Create(sorts.size);
    decl_names := TZ3Array<Z3_symbol>.Create(decls.size);

    sorts1     := Sorts.ToArray ;
    decls1     := decls.ToArray;
    for i := 0 to sorts.size - 1 do
       sort_names.Items[i] := sorts.Items[i].name;

    for i := 0 to decls.size - 1 do
       decl_names.Items[i] := decls.Items[i].name;

    var r : Z3_ast_vector  := Z3_parse_smtlib2_file(Self, s, sorts.size, sort_names.ptr, sorts1.ptr, decls.size, decl_names.ptr, decls1.ptr);
    check_error;
    Result := TExpr_vector.Create(Self, r);

end;

function TContext.parse_string(s: PAnsiChar): TExpr_vector;
begin
     var r : Z3_ast_vector := Z3_parse_smtlib2_string(Self, s, 0, 0, 0, 0, 0, 0);
     check_error;
     Result := TExpr_vector.Create(Self, r);
end;

function TContext.parse_string(s: PAnsiChar; const Sorts: TSort_vector;  const decls: TFunc_decl_vector): TExpr_vector;
var
  sort_names : TZ3Array<Z3_symbol> ;
  decl_names : TZ3Array<Z3_symbol> ;
  sorts1     : TZ3Array<Z3_sort> ;
  decls1     : TZ3Array<Z3_func_decl> ;
  i          : Integer;
begin
    sort_names := TZ3Array<Z3_symbol>.Create(sorts.size);
    decl_names := TZ3Array<Z3_symbol>.Create(decls.size);

    sorts1     := Sorts.ToArray ;
    decls1     := decls.ToArray;
    for i := 0 to sorts.size - 1 do
       sort_names.Items[i] := sorts.Items[i].name;

    for i := 0 to decls.size - 1 do
       decl_names.Items[i] := decls.Items[i].name;

    var r : Z3_ast_vector := Z3_parse_smtlib2_string(Self, s, sorts.size, sort_names.ptr, sorts1.ptr, decls.size, decl_names.ptr, decls1.ptr);
    check_error;
    Result := TExpr_vector.Create(Self, r);
end;

{ Z3Object }

constructor Z3Object.Create(c: TContext);
begin
    m_ctx := TContext.Create(c)
end;

constructor Z3Object.Create(s: Z3Object);
begin
    m_ctx := TContext.Create(s.m_ctx)
end;

function Z3Object.ctx: TContext;
begin
    Result := m_ctx;
end;

function Z3Object.check_error: Z3_error_code;
begin
    Result := m_ctx.check_error;
end;

{ TSymbol }

constructor TSymbol.Create(c:TContext; s: Z3_symbol);
begin
    inherited Create(c);
    m_sym := s;
end;

constructor TSymbol.Create(const s: TSymbol);
begin
    inherited Create(s);
    m_sym := s.m_sym;
end;

function TSymbol.ToZ3_symbol:Z3_symbol;
begin
    Result := m_sym;
end;

function TSymbol.kind: Z3_symbol_kind;
begin
    Result := Z3_get_symbol_kind(ctx.ToZ3_Context, m_sym);
end;

function TSymbol.ToStr: AnsiString;
begin
    assert(kind = Z3_STRING_SYMBOL,'Error not "Z3_STRING_SYMBOL"');
    Result := Z3_get_symbol_string(ctx.ToZ3_Context, m_sym);
end;

function TSymbol.To_int: Integer;
begin
    assert(kind = Z3_INT_SYMBOL,'Error not "Z3_INT_SYMBOL"');
    Result := Z3_get_symbol_int(ctx.ToZ3_Context, m_sym);
end;

function TSymbol.ToStr(s: TSymbol): AnsiString;
begin
    Result := '';
    if  s.kind = Z3_INT_SYMBOL then  Result := 'k!' + IntToStr(s.to_int)
    else                             Result := s.ToStr;
end;

{ TAst }

constructor TAst.Create(c: TContext);
begin
    inherited Create(c);
    m_ast := nil;
end;

constructor TAst.Create(c: TContext; n: Z3_ast);
begin
    inherited Create(c);
    m_ast := n;
    Z3_inc_ref(ctx.ToZ3_Context, m_ast)
end;

constructor TAst.Create(n: TAst);
begin
    inherited Create(Z3Object(n));
    m_ast := n.m_ast;
    Z3_inc_ref(ctx.ToZ3_Context, m_ast)
end;

destructor TAst.Destroy;
begin
    if m_ast <> nil then
      Z3_inc_ref(ctx.ToZ3_Context, m_ast)

end;

function TAst.Assign(const s: TAst): TAst;
begin
    Z3_inc_ref(s.ctx.ToZ3_Context, s.m_ast);
    if m_ast <> nil then
       Z3_dec_ref(ctx.ToZ3_Context, m_ast);

    m_ctx := s.m_ctx;
    m_ast := s.m_ast;

    Result := Self;
end;

function TAst.Hash: Cardinal;
begin
    var r : Cardinal  := Z3_get_ast_hash(ctx.ToZ3_Context, m_ast);
    check_error;
    Result := r
end;

function TAst.NotNil: Boolean;
begin
    Result := m_ast <> nil
end;

function TAst.Kind: Z3_ast_kind;
begin
    var r : Z3_ast_kind  := Z3_get_ast_kind(ctx.ToZ3_Context, m_ast);
    check_error;
    Result := r
end;

function TAst.ToZ3_ast: Z3_ast;
begin
    Result := m_ast;
end;

function TAst.ToStr: AnsiString;
begin
    Result := Z3_ast_to_string(ctx.ToZ3_Context, m_ast);
end;

{ TExpr }

constructor TExpr.Create(c: TContext);
begin
     inherited Create(c);
end;

constructor TExpr.Create(c: TContext; n: Z3_ast);
begin
    inherited Create(c,n);
end;

function TExpr.at(const index: TExpr): TExpr;
begin
    check_context(Self, index);
    var r : Z3_ast := Z3_mk_seq_at(ctx.ToZ3_Context, Self.ToZ3_ast, index.ToZ3_ast);
    check_error;
    Result  := TExpr.Create(ctx, r);

end;

function TExpr.Assign(const s: TExpr): TExpr;
begin
    Result := TExpr( inherited Assign(s.ToZ3_ast) );
end;


function TExpr.arg(i: Cardinal): TExpr;
begin
     var r : Z3_ast := Z3_get_app_arg(ctx.ToZ3_Context, Self.ToZ3_app, i);
     check_error;
     Result := TExpr.Create(ctx, r);
end;

function TExpr.&repeat(i: Cardinal): TExpr;
begin
     var r : Z3_ast := Z3_mk_repeat(ctx.ToZ3_Context, i, Self.ToZ3_ast);
     ctx.check_error;
     Result := TExpr.Create(ctx, r);
end;

function TExpr.&unit: TExpr;
begin
  var r : Z3_ast := Z3_mk_seq_unit(ctx.ToZ3_Context, Self.ToZ3_ast);
  check_error;
  Result := TExpr.Create(ctx, r);

end;

function TExpr.body: TExpr;
begin
    assert(is_quantifier);
    var r : Z3_ast := Z3_get_quantifier_body(ctx.ToZ3_Context, Self.ToZ3_ast);
    check_error;
    Result := TExpr.Create(ctx, r);
end;

function TExpr.bool_value: Z3_lbool;
begin
    Result := Z3_get_bool_value(ctx.ToZ3_Context, m_ast);
end;

function TExpr.contains(const s: TExpr): TExpr;
begin
    check_context(Self, s);
    var r : Z3_ast := Z3_mk_seq_contains(ctx.ToZ3_Context, Self.ToZ3_ast, s.ToZ3_ast);
    check_error;
    Result := TExpr.Create(ctx, r);
end;

constructor TExpr.Create(n: TExpr);
begin
    inherited Create(n)
end;

function TExpr.decl: TFunc_decl;
begin
    var f : Z3_func_decl := Z3_get_app_decl(ctx.ToZ3_Context, Self.ToZ3_app);
    check_error;
    Result := TFunc_decl.Create(ctx, f);
end;

function TExpr.denominator: TExpr;
begin
   assert(is_numeral);
   var r : Z3_ast := Z3_get_denominator(ctx.ToZ3_Context, m_ast);
   check_error;
   Result := TExpr.Create(ctx,r);
end;

function TExpr.extract(const offset, length: TExpr): TExpr;
begin
  check_context(Self, offset);
  check_context(offset, length);
  var r : Z3_ast := Z3_mk_seq_extract(ctx.ToZ3_Context, Self.ToZ3_ast, offset.ToZ3_ast, length.ToZ3_ast);
  check_error;
  Result := TExpr.Create(ctx, r);
end;

function TExpr.extract(hi, lo: Cardinal): TExpr;
begin
    var r : Z3_ast := Z3_mk_extract(ctx.ToZ3_Context, hi, lo, Self.ToZ3_ast);
    ctx.check_error;
    Result  := TExpr.Create(ctx, r);
end;

function TExpr.fpa_rounding_mode: TSort;
begin
   assert(is_fpa);
   var s : Z3_sort := ctx.fpa_rounding_mode;
   check_error;
   Result := TSort.Create(ctx, s);
end;

function TExpr.get_decimal_string(precision: Integer): AnsiString;
begin
  assert(is_numeral or is_algebraic);
  Result := Z3_get_numeral_decimal_string(ctx.ToZ3_Context, m_ast, precision);
end;

function TExpr.get_numeral_int: Integer;
begin
  Result := 0;
  if not is_numeral_i(result) then
  begin
      assert(ctx.enable_exceptions);
      if not ctx.enable_exceptions then Exit(0);
      TZ3Exception.Create('numeral does not fit in machine int');
  end;
end;

function TExpr.get_numeral_int64: int64;
begin
  assert(is_numeral);
  Result := 0;
  if not is_numeral_i64(result) then
  begin
      assert(ctx.enable_exceptions);
      if not ctx.enable_exceptions then Exit(0);
      TZ3Exception.Create('numeral does not fit in machine int64_t');
  end;
end;

function TExpr.get_numeral_uint: Cardinal;
begin
  assert(is_numeral);
  Result := 0;
  if not is_numeral_u(result) then
  begin
      assert(ctx.enable_exceptions);
      if not ctx.enable_exceptions then Exit(0);
      TZ3Exception.Create('numeral does not fit in machine uint');
  end;
end;

function TExpr.get_numeral_uint64: uint64;
begin
  assert(is_numeral);
  Result := 0;
  if not is_numeral_u64(result) then
  begin
      assert(ctx.enable_exceptions);
      if not ctx.enable_exceptions then Exit(0);
      TZ3Exception.Create('numeral does not fit in machine uint64_t');
  end;
end;

function TExpr.get_sort: TSort;
begin
     var s : Z3_sort := Z3_get_sort(m_ctx.ToZ3_Context, m_ast);
     check_error;
     Result := TSort.create(m_ctx, s);
end;

function TExpr.hi: Cardinal;
begin
     assert((is_app) and (Z3_get_decl_num_parameters(ctx.ToZ3_Context, decl.ToZ3_func_decl) = 2));
     Result := Cardinal (Z3_get_decl_int_parameter(ctx.ToZ3_Context, decl.ToZ3_func_decl, 0));
end;

function TExpr.id: Cardinal;
begin
     var r : Cardinal := Z3_get_ast_id(ctx.ToZ3_Context, m_ast);
     check_error;
     Result := r;
end;

function TExpr.is_algebraic: Boolean;
begin
    Result := Z3_is_algebraic_number(ctx.ToZ3_Context, m_ast);
end;

function TExpr.is_and: Boolean;
begin
    Result := (is_app) and (Z3_OP_AND = decl.decl_kind);
end;

function TExpr.is_app: Boolean;
begin
    Result := (kind = Z3_APP_AST) or (kind = Z3_NUMERAL_AST);
end;

function TExpr.is_arith: Boolean;
begin
    Result := get_sort.is_arith;
end;

function TExpr.is_array: Boolean;
begin
    Result := get_sort.is_array;
end;

function TExpr.is_bool: Boolean;
begin
     Result := get_sort.is_bool;
end;

function TExpr.is_bv: Boolean;
begin
     Result := get_sort().is_bv;
end;

function TExpr.is_const: Boolean;
begin
    Result := (is_app) and (num_args = 0);
end;

function TExpr.is_datatype: Boolean;
begin
   Result := get_sort.is_datatype;
end;

function TExpr.is_eq: Boolean;
begin
   Result := (is_app) and (Z3_OP_EQ = decl.decl_kind);
end;

function TExpr.is_exists: Boolean;
begin
    Result := Z3_is_quantifier_exists(ctx.ToZ3_Context, m_ast);
end;

function TExpr.is_false: Boolean;
begin
   Result := (is_app) and (Z3_OP_FALSE = decl.decl_kind);
end;

function TExpr.is_finite_domain: Boolean;
begin
    Result := get_sort.is_finite_domain;
end;

function TExpr.is_forall: Boolean;
begin
    Result := Z3_is_quantifier_forall(ctx.ToZ3_Context, m_ast);
end;

function TExpr.is_fpa: Boolean;
begin
    Result := get_sort.is_fpa;
end;

function TExpr.is_implies: Boolean;
begin
    Result := (is_app) and (Z3_OP_IMPLIES  = decl.decl_kind);
end;

function TExpr.is_int: Boolean;
begin
    Result := get_sort.is_int;
end;

function TExpr.is_ite: Boolean;
begin
    Result := (is_app) and (Z3_OP_ITE  = decl.decl_kind);
end;

function TExpr.is_lambda: Boolean;
begin
    Result := Z3_is_lambda(ctx.ToZ3_Context, m_ast);
end;

function TExpr.is_not: Boolean;
begin
   Result := (is_app) and (Z3_OP_NOT  = decl.decl_kind);
end;

function TExpr.is_numeral: Boolean;
begin
   Result := kind = Z3_NUMERAL_AST;
end;

function TExpr.is_numeral(var s: AnsiString): Boolean;
begin
     if not is_numeral then Exit(false);
     s := Z3_get_numeral_string(ctx.ToZ3_Context, m_ast);
     check_error;
     Result := true;
end;

function TExpr.is_numeral(var s: AnsiString; precision: Cardinal): Boolean;
begin
    if not is_numeral then Exit(false);
    s := Z3_get_numeral_decimal_string(ctx.ToZ3_Context, m_ast, precision);
    check_error;
    Result := true;
end;

function TExpr.is_numeral(var d: Double): Boolean;
begin
    if not is_numeral then Exit(false);
    d := Z3_get_numeral_double(ctx.ToZ3_Context, m_ast);
    check_error;
    Result := true;
end;

function TExpr.is_numeral_i(var i: Integer): Boolean;
begin
    var r : Boolean := Z3_get_numeral_int(ctx.ToZ3_Context, m_ast, @i);
    check_error;
    Result := r;
end;

function TExpr.is_numeral_i64(var i: int64): Boolean;
begin
   var r : Boolean := Z3_get_numeral_int64(ctx.ToZ3_Context, m_ast, @i);
   check_error;
   Result := r;
end;

function TExpr.is_numeral_u(var i: Cardinal): Boolean;
begin
    var r : Boolean := Z3_get_numeral_uint(ctx.ToZ3_Context, m_ast, @i);
    check_error;
    Result := r;
end;

function TExpr.is_numeral_u64(var i: uint64): Boolean;
begin
     var r : Boolean := Z3_get_numeral_uint64(ctx.ToZ3_Context, m_ast, @i);
     check_error;
     Result := r;
end;

function TExpr.is_or: Boolean;
begin
    Result := (is_app) and (Z3_OP_OR  = decl.decl_kind);
end;

function TExpr.is_quantifier: Boolean;
begin
    Result := kind = Z3_QUANTIFIER_AST;
end;

function TExpr.is_re: Boolean;
begin
  Result := get_sort().is_re;
end;

function TExpr.is_real: Boolean;
begin
   Result := get_sort.is_real;
end;

function TExpr.is_relation: Boolean;
begin
   Result := get_sort.is_relation;
end;

function TExpr.is_seq: Boolean;
begin
   Result := get_sort.is_seq;
end;

function TExpr.is_true: Boolean;
begin
   Result := (is_app) and (Z3_OP_TRUE  = decl.decl_kind);
end;

function TExpr.is_var: Boolean;
begin
   Result := kind = Z3_VAR_AST;
end;

function TExpr.is_well_sorted: Boolean;
begin
   var r : Boolean := Z3_is_well_sorted(ctx.ToZ3_Context, m_ast);
   check_error;
   Result := r;
end;

function TExpr.is_xor: Boolean;
begin
    Result := (is_app) and (Z3_OP_XOR  = decl.decl_kind);
end;

function TExpr.itos: TExpr;
begin
  var  r : Z3_ast := Z3_mk_int_to_str(ctx.ToZ3_Context, Self.ToZ3_ast);
  check_error;
  Result := TExpr.Create(ctx, r);
end;

function TExpr.length: TExpr;
begin
  var r : Z3_ast := Z3_mk_seq_length(ctx.ToZ3_Context,Self.ToZ3_ast);
  check_error;
  Result := TExpr.Create(ctx, r);
end;

function TExpr.lo: Cardinal;
begin
   assert((is_app) and (Z3_get_decl_num_parameters(ctx.ToZ3_Context, decl.ToZ3_func_decl) = 2));
   Result := Cardinal ( Z3_get_decl_int_parameter(ctx.ToZ3_Context, decl.ToZ3_func_decl, 1) );
end;

function TExpr.loop(lo, hi: Cardinal): TExpr;
begin
  var r : Z3_ast := Z3_mk_re_loop(ctx.ToZ3_Context, m_ast, lo, hi);
  check_error;
  Result := TExpr.Create(ctx, r);
end;

function TExpr.loop(lo: Cardinal): TExpr;
begin
  var r : Z3_ast := Z3_mk_re_loop(ctx.ToZ3_Context, m_ast, lo, 0);
  check_error;
  Result := TExpr.Create(ctx, r);

end;

function TExpr.numerator: TExpr;
begin
  assert(is_numeral);
  var r : Z3_ast := Z3_get_numerator(ctx.ToZ3_Context, m_ast);
  check_error;
  Result := TExpr.Create(ctx,r);
end;

function TExpr.num_args: Cardinal;
begin
    var r : Cardinal := Z3_get_app_num_args(ctx.ToZ3_Context, Self.ToZ3_app);
    check_error;
    Result := r;
end;

function TExpr.replace(const src, dst: TExpr): TExpr;
begin
  check_context(Self, src);
  check_context(src, dst);
  var r : Z3_ast := Z3_mk_seq_replace(ctx.ToZ3_Context, Self.ToZ3_ast, src.ToZ3_ast, dst.ToZ3_ast);
  check_error;
  Result := TExpr.Create(ctx, r);
end;

function TExpr.rotate_left(i: Cardinal): TExpr;
begin
    var r :Z3_ast := Z3_mk_rotate_left(ctx.ToZ3_Context, i, Self.ToZ3_ast);
    ctx.check_error;
    Result := TExpr.Create(ctx, r);
end;

function TExpr.rotate_right(i: Cardinal): TExpr;
begin
   var r :Z3_ast := Z3_mk_rotate_right(ctx.ToZ3_Context, i, Self.ToZ3_ast);
   ctx.check_error;
   Result := TExpr.Create(ctx, r);
end;

function TExpr.simplify: TExpr;
begin
   var r :Z3_ast := Z3_simplify(ctx.ToZ3_Context, m_ast);
   check_error;
   Result := TExpr.Create(ctx, r);
end;

function TExpr.simplify(const p: TParams): TExpr;
begin
    var r :Z3_ast := Z3_simplify_ex(ctx.ToZ3_Context, m_ast, p.ToZ3_params);
    check_error;
    Result := TExpr.Create(ctx, r);
end;

function TExpr.stoi: TExpr;
begin
  var r :Z3_ast := Z3_mk_str_to_int(ctx.ToZ3_Context, Self.ToZ3_ast);
  check_error;
  Result := TExpr.Create(ctx, r);

end;

function TExpr.substitute(const src, dst: TExpr_vector): TExpr;
var
  i : Integer;
begin
  assert(src.size = dst.size);

  var _src : TZ3Array<Z3_ast> := TZ3Array<Z3_ast>.Create(src.size);
  var _dst : TZ3Array<Z3_ast> := TZ3Array<Z3_ast>.Create(dst.size);

  for i := 0 to src.size -1 do
  begin
      _src.Items[i] := src.Items[i].ToZ3_ast;
      _dst.Items[i] := dst.Items[i].ToZ3_ast;
  end;
  var r : Z3_ast := Z3_substitute(ctx.ToZ3_Context, m_ast, src.size, _src.ptr, _dst.ptr);
  check_error;
  Result := TExpr.Create(ctx, r);

end;

function TExpr.substitute(const dst: TExpr_vector): TExpr;
var
  i : Integer;
begin

  var _dst : TZ3Array<Z3_ast> := TZ3Array<Z3_ast>.Create(dst.size);
  for i := 0 to  dst.size - 1 do
      _dst.Items[i] := dst.Items[i].ToZ3_ast;

  var r : Z3_ast := Z3_substitute_vars(ctx.ToZ3_Context, m_ast, dst.size, _dst.ptr);
  check_error;
  Result := TExpr.Create(ctx, r);

end;

function TExpr.ToZ3_app: Z3_app;
begin
     assert(is_app);
     Result := Z3_app(m_ast);
end;

{ TSort }

constructor TSort.Create(c:TContext; a: Z3_ast);
begin
     inherited Create(c,a);
end;

constructor TSort.Create(c:TContext);
begin
    inherited Create(c);
end;

constructor TSort.Create(s: TSort);
begin
    inherited Create(s);
end;

function TSort.ToZ3_Sort: Z3_sort;
begin
    Result := m_ast;
end;

function TSort.name: TSymbol;
begin
   var s : Z3_symbol := Z3_get_sort_name(ctx.ToZ3_Context, m_ast);
   check_error;
   Result := TSymbol.Create(ctx, s);
end;

function TSort.array_domain: TSort;
begin
    assert(is_array);
    var s : Z3_sort := Z3_get_array_sort_domain(ctx.ToZ3_Context, m_ast);
    check_error;
    Result := TSort.Create(ctx, s);
end;

function TSort.array_range: TSort;
begin
     assert(is_array);
     var s : Z3_sort := Z3_get_array_sort_range(ctx.ToZ3_Context, m_ast);
     check_error;
     Result := TSort.Create(ctx, s);
end;

function TSort.bv_size: Cardinal;
begin
    assert(is_bv);
    var r : Cardinal := Z3_get_bv_sort_size(ctx.ToZ3_Context, m_ast);
    check_error;
    Result := r;
end;

function TSort.fpa_ebits: Cardinal;
begin
    assert(is_fpa);
    var r : Cardinal := Z3_fpa_get_ebits(ctx.ToZ3_Context, m_ast);
    check_error;
    Result := r;
end;

function TSort.fpa_sbits: Cardinal;
begin
    assert(is_fpa);
    var r : Cardinal := Z3_fpa_get_sbits(ctx.ToZ3_Context, m_ast);
    check_error;
    Result := r;
end;

function TSort.id: Cardinal;
begin
    var r : Cardinal := Z3_get_sort_id(ctx.ToZ3_Context, m_ast);
    check_error;
    Result := r;
end;

function TSort.is_arith: Boolean;
begin
    Result := (is_int) or (is_real)
end;

function TSort.is_array: Boolean;
begin
    Result := sort_kind = Z3_ARRAY_SORT;
end;

function TSort.is_bool: Boolean;
begin
    Result := sort_kind = Z3_BOOL_SORT;
end;

function TSort.is_bv: Boolean;
begin
    Result := sort_kind = Z3_BV_SORT;
end;

function TSort.is_datatype: Boolean;
begin
    Result := sort_kind = Z3_DATATYPE_SORT;
end;

function TSort.is_finite_domain: Boolean;
begin
    Result := sort_kind = Z3_FINITE_DOMAIN_SORT;
end;

function TSort.is_fpa: Boolean;
begin
    Result := sort_kind = Z3_FLOATING_POINT_SORT;
end;

function TSort.is_int: Boolean;
begin
    Result := sort_kind = Z3_INT_SORT;
end;

function TSort.is_re: Boolean;
begin
    Result := sort_kind = Z3_RE_SORT;
end;

function TSort.is_real: Boolean;
begin
    Result := sort_kind = Z3_REAL_SORT;
end;

function TSort.is_relation: Boolean;
begin
    Result := sort_kind = Z3_RELATION_SORT;
end;

function TSort.is_seq: Boolean;
begin
    Result := sort_kind = Z3_SEQ_SORT;
end;

function TSort.sort_kind: Z3_sort_kind;
begin
    Result := Z3_get_sort_kind(m_ctx.ToZ3_Context,m_ast );
end;

{ ast_vector_tpl<T> }

constructor TAst_vector_tpl<T>.Create(c: TContext);
begin
     inherited Create(c);
     init( Z3_mk_ast_vector(c.ToZ3_Context));
end;

constructor TAst_vector_tpl<T>.Create(c: TContext; v: Z3_ast_vector);
begin
    inherited Create(c);
    Init(v)
end;

function TAst_vector_tpl<T>.Assign(s: TAst_vector_tpl<T>): TAst_vector_tpl<T>;
begin
    Z3_ast_vector_inc_ref(s.ctx.ToZ3_Context, s.m_vector);
    Z3_ast_vector_dec_ref(ctx.ToZ3_Context, m_vector);
    m_ctx    := s.m_ctx;
    m_vector := s.m_vector;
    Result := Self;
end;

function TAst_vector_tpl<T>.back: T;
begin
    Result := Items[ Size - 1 ]
end;

function TAst_vector_tpl<T>.&Set(idx: Cardinal; a: TAst): TAst_vector_tpl<T>;
begin
    Z3_ast_vector_set(ctx.ToZ3_Context, m_vector, idx, a.ToZ3_ast );
    Result := Self;
end;

constructor TAst_vector_tpl<T>.Create(s: TAst_vector_tpl<T>);
begin
    inherited Create(s) ;
    m_vector := s.m_vector;
    Z3_ast_vector_inc_ref(ctx.ToZ3_Context, m_vector);
end;

destructor TAst_vector_tpl<T>.Destroy;
begin
     Z3_ast_vector_dec_ref(ctx.ToZ3_Context, m_vector);
end;

function TAst_vector_tpl<T>.empty: Boolean;
begin
    Result := size = 0;
end;

procedure TAst_vector_tpl<T>.init(v: Z3_ast_vector);
begin
     Z3_ast_vector_inc_ref(ctx.ToZ3_Context, v);
     m_vector := v;
end;

procedure TAst_vector_tpl<T>.pop_back;
begin
     assert(size > 0);
     resize(size - 1);
end;

procedure TAst_vector_tpl<T>.push_back(e: T);
begin
     Z3_ast_vector_push(ctx.ToZ3_Context, m_vector, e.ToZ3_ast );
     check_error;
end;

procedure TAst_vector_tpl<T>.resize(sz: Cardinal);
begin
     Z3_ast_vector_resize(ctx.ToZ3_Context, m_vector, sz);
     check_error;
end;

function TAst_vector_tpl<T>.Size: Cardinal;
begin
    Result := Z3_ast_vector_size(ctx.ToZ3_Context, m_vector);
end;

function TAst_vector_tpl<T>.ToZ3_ast_vector: Z3_ast_vector;
begin
    Result := m_vector
end;

function TAst_vector_tpl<T>.ToStr(v: TAst_vector_tpl<T>): AnsiString;
begin
   Result := Z3_ast_vector_to_string(v.ctx.ToZ3_Context, v.ToZ3_ast_vector);
end;

function TAst_vector_tpl<T>.ToStr: AnsiString;
begin
   Result := ToStr(Self)
end;


{ TFunc_decl }

constructor TFunc_decl.Create(const s: TFunc_decl);
begin
   inherited Create(s);
end;

constructor TFunc_decl.Create(c: TContext);
begin
    inherited Create(c);
end;

constructor TFunc_decl.Create(c: TContext; n: Z3_func_decl);
begin
    inherited Create(c,Z3_ast(n))
end;

function TFunc_decl.arity: Cardinal;
begin
    Result := Z3_get_arity(ctx.ToZ3_Context, Self.ToZ3_func_decl);
end;

function TFunc_decl.decl_kind: Z3_decl_kind;
begin
   Result := Z3_get_decl_kind(ctx.ToZ3_Context, Self.ToZ3_func_decl);
end;

function TFunc_decl.domain(i: Cardinal): TSort;
begin
    assert(i < arity);
    var r : Z3_sort := Z3_get_domain(ctx.ToZ3_Context, self.ToZ3_func_decl, i);
    check_error;
    Result := TSort.Create(ctx, r);
end;

function TFunc_decl.id: Cardinal;
begin
    var r : Cardinal := Z3_get_func_decl_id(ctx.ToZ3_Context, Self.ToZ3_func_decl);
    check_error;
    Result := r;
end;

function TFunc_decl.is_const: Boolean;
begin
    Result := arity = 0;
end;

function TFunc_decl.name: TSymbol;
begin
    var s : Z3_symbol := Z3_get_decl_name(ctx.ToZ3_Context, Self.ToZ3_func_decl);
    check_error;
    Result := TSymbol.Create(ctx, s);
end;

function TFunc_decl.range: TSort;
begin
    var r : Z3_sort := Z3_get_range(ctx.ToZ3_Context, Self.ToZ3_func_decl);
    check_error;
    Result := TSort.Create(ctx, r);
end;

function TFunc_decl.FunOf(const args: TExpr_vector): TExpr;
var
  i : Cardinal;
begin
    var _args : TZ3Array<Z3_ast> :=  TZ3Array<Z3_ast>.Create(args.size);
    for i := 0 to args.size - 1 do
    begin
        check_context(Self, args.Items[i].ToZ3_ast);
        _args.Items[i] := args.Items[i].ToZ3_ast;
    end;
    var r : Z3_ast  := Z3_mk_app(ctx.ToZ3_Context, Self.ToZ3_func_decl, args.size, _args.ptr);
    check_error;
    Result := TExpr.Create(ctx, r);
end;

function TFunc_decl.FunOf(n: Cardinal; const args: array of TExpr): TExpr;
var
  i : Cardinal;
begin
    var _args : TZ3Array<Z3_ast> :=  TZ3Array<Z3_ast>.Create(n);
    for i := 0 to  n-1  do
    begin
        check_context(Self,  args[i].ToZ3_ast);
        _args.Items[i] := args[i].ToZ3_ast;
    end;

    var r : Z3_ast := Z3_mk_app(ctx.ToZ3_Context, Self.ToZ3_func_decl, n, _args.ptr);
    check_error;
    Result := TExpr.Create(ctx, r);
end;

function TFunc_decl.FunOf: TExpr;
begin
   var r : Z3_ast := Z3_mk_app(ctx.ToZ3_Context, Self.ToZ3_func_decl, 0, 0);
   ctx.check_error;
   Result := TExpr.Create(ctx, r);
end;

function TFunc_decl.FunOf(const a: TExpr): TExpr;
var
  args : TArray<Z3_ast> ;
begin
   check_context(Self, a);
   args :=  [a.ToZ3_ast] ;
   var r : Z3_ast := Z3_mk_app(ctx.ToZ3_Context, Self.ToZ3_func_decl, 1, @args[0]);
   ctx.check_error;
   Result := TExpr.Create(ctx, r);
end;

function TFunc_decl.FunOf(a: Integer): TExpr;
var
  args : TArray<Z3_ast> ;
begin
   args := [ ctx.num_val(a, domain(0)).ToZ3_ast ] ;
   var r : Z3_ast := Z3_mk_app(ctx.ToZ3_Context, Self.ToZ3_func_decl, 1, @args[0]);
   ctx.check_error;
   Result := TExpr.Create(ctx, r);
end;

function TFunc_decl.FunOf(const a1, a2: TExpr): TExpr;
begin

    check_context(self, a1);
    check_context(self, a2);
    var args : Tarray<Z3_ast> := [ a1.ToZ3_ast, a2.ToZ3_ast ];
    var r : Z3_ast := Z3_mk_app(ctx.ToZ3_Context, Self.ToZ3_func_decl, 2, @args[0]);
    ctx.check_error;
    Result := TExpr.Create(ctx, r);

end;

function TFunc_decl.FunOf(const a1: TExpr; a2: Integer): TExpr;
begin
    check_context(Self, a1);
    var args : Tarray<Z3_ast> := [ a1.ToZ3_ast, ctx.num_val(a2, domain(1)).ToZ3_ast ];
    var r : Z3_ast := Z3_mk_app(ctx.ToZ3_Context, Self.ToZ3_func_decl, 2,  @args[0]);
    ctx.check_error;
    Result := TExpr.Create(ctx, r);
end;

function TFunc_decl.FunOf(a1: Integer; const a2: TExpr): TExpr;
begin

    check_context(Self, a2);
    var args : Tarray<Z3_ast> := [ ctx.num_val(a1, domain(0)).ToZ3_ast, a2.ToZ3_ast ];
    var r : Z3_ast := Z3_mk_app(ctx.ToZ3_Context, Self.ToZ3_func_decl, 2, @args[0]);
    ctx.check_error;
    Result := TExpr.Create(ctx, r);
end;

function TFunc_decl.FunOf(const a1, a2, a3: TExpr): TExpr;
begin
   check_context(Self, a1);
   check_context(Self, a2);
   check_context(Self, a3);
   var args : Tarray<Z3_ast> := [ a1.ToZ3_ast, a2.ToZ3_ast, a3.ToZ3_ast ];
   var r : Z3_ast := Z3_mk_app(ctx.ToZ3_Context, Self.ToZ3_func_decl, 3, @args[0]);
   ctx.check_error;
   Result := TExpr.Create(ctx, r);
end;

function TFunc_decl.FunOf(const a1, a2, a3, a4: TExpr): TExpr;
begin
   check_context(Self, a1);
   check_context(Self, a2);
   check_context(Self, a3);
   check_context(Self, a4);
   var args : Tarray<Z3_ast> := [ a1.ToZ3_ast, a2.ToZ3_ast, a3.ToZ3_ast, a4.ToZ3_ast ];
   var r : Z3_ast := Z3_mk_app(ctx.ToZ3_Context, Self.ToZ3_func_decl, 4, @args[0]);
   ctx.check_error;
   Result := TExpr.Create(ctx, r);
end;

function TFunc_decl.FunOf(const a1, a2, a3, a4, a5: TExpr): TExpr;
begin
   check_context(Self, a1);
   check_context(Self, a2);
   check_context(Self, a3);
   check_context(Self, a4);
   check_context(Self, a5);
   var args : Tarray<Z3_ast> := [ a1.ToZ3_ast, a2.ToZ3_ast, a3.ToZ3_ast, a4.ToZ3_ast, a5.ToZ3_ast ];
   var r : Z3_ast := Z3_mk_app(ctx.ToZ3_Context, Self.ToZ3_func_decl, 5, @args[0]);
   ctx.check_error;
   Result := TExpr.Create(ctx, r);
end;

function TFunc_decl.ToZ3_func_decl: Z3_func_decl;
begin
   Result := m_ast;//Z3_func_decl(m_ast)
end;

{ TSort_vector }

function TSort_vector.GetItem(Index: Cardinal): TSort;
begin
    assert(Index < size);
     var r : Z3_ast := Z3_ast_vector_get(ctx.ToZ3_Context, m_vector, Index);
     check_error;

     Result := TSort.create(ctx, r);
end;

function TSort_vector.ToArray: TZ3Array<Z3_sort>;
begin
    Result         :=  TZ3Array<Z3_sort>.Create(Size);
    Result.m_size  := Size;
    for var i : Integer := 0 to Size - 1 do
        Result.m_array[i] := Items[i];
end;

{ TExpr_vector }

function TExpr_vector.GetItem(Index: Cardinal): TExpr;
begin
     assert(Index < size);
     var r : Z3_ast := Z3_ast_vector_get(ctx.ToZ3_Context, m_vector, Index);
     check_error;

     Result := TExpr.create(ctx, r);
end;

function TExpr_vector.ToArray: TZ3Array<Z3_ast>;
begin
    Result         :=  TZ3Array<Z3_ast>.Create(Size);
    Result.m_size  := Size;
    for var i : Integer := 0 to Size - 1 do
        Result.m_array[i] := Items[i];
end;

{ TFunc_decl_vector }

function TFunc_decl_vector.GetItem(Index: Cardinal): TFunc_decl;
begin
     assert(Index < size);
     var r : Z3_ast := Z3_ast_vector_get(ctx.ToZ3_Context, m_vector, Index);
     check_error;

     Result := TFunc_decl.create(ctx, r);
end;

function TFunc_decl_vector.ToArray: TZ3Array<Z3_func_decl>;
begin
    Result         :=  TZ3Array<Z3_func_decl>.Create(Size);
    Result.m_size  := Size;
    for var i : Integer := 0 to Size - 1 do
        Result.m_array[i] := Items[i];
end;

{ TParams }

constructor TParams.Create(const s: TParams);
begin
   inherited Create(s);
   m_params := s.m_params;
   Z3_params_inc_ref(ctx.ToZ3_Context, m_params);
end;

constructor TParams.Create(c: TContext);
begin
   inherited Create(c);
    m_params := Z3_mk_params(c.ToZ3_Context);
    Z3_params_inc_ref(ctx.ToZ3_Context, m_params);
end;

destructor TParams.Destroy;
begin
   Z3_params_dec_ref(ctx.ToZ3_Context, m_params);
end;

procedure TParams.&set(const k: PAnsiChar; b: Boolean);
begin
    Z3_params_set_bool(ctx.ToZ3_Context, m_params, ctx.str_symbol(k).ToZ3_symbol, b);
end;

procedure TParams.&set(const k: PAnsiChar; n: Cardinal);
begin
    Z3_params_set_uint(ctx.ToZ3_Context, m_params, ctx.str_symbol(k).ToZ3_symbol, n);
end;

procedure TParams.&set(const k: PAnsiChar; s: PAnsiChar);
begin
   Z3_params_set_symbol(ctx.ToZ3_Context, m_params, ctx.str_symbol(k).ToZ3_symbol, ctx.str_symbol(s).ToZ3_symbol);
end;

procedure TParams.&set(const k: PAnsiChar; const s: TSymbol);
begin
   Z3_params_set_symbol(ctx.ToZ3_Context, m_params, ctx.str_symbol(k).ToZ3_symbol, s.ToZ3_symbol);
end;

procedure TParams.&set(const k: PAnsiChar; n: Double);
begin
    Z3_params_set_double(ctx.ToZ3_Context, m_params, ctx.str_symbol(k).ToZ3_symbol, n);
end;

function TParams.ToStr(const p: TParams): AnsiString;
begin
   Result := Z3_params_to_string(p.ctx.ToZ3_Context, p.ToZ3_params)
end;

function TParams.ToZ3_params: Z3_params;
begin
   Result := m_params;
end;

end.
