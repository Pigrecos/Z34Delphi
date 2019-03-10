unit testAsmx86;
// Example of using Z3 to test for opaque predicates in x86 code
// www.zubcic.re / zubcic.tomislav@gmail.com
interface
 uses
    Winapi.Windows, Winapi.Messages, System.SysUtils,System.Classes,
    Capstone,
    CapstoneApi,
    CapstoneX86,
    z3,
    Z3.Context,
    Z3.Solver,
    Z3.Model,
    Z3.Func,
    Z3.Def;

type
  flag_t = (FLAG_OF,FLAG_ZF,FLAG_SF);
  PTExpr = ^TExpr;

  opaque_predicate_t =( undef,not_opaque_predicate_k = 0, opaque_predicate_taken_k, opaque_predicate_not_taken_k );

  x86_ctx = record
    eax  : TExpr;
    ebx  : TExpr;
    ecx  : TExpr;
    edx  : TExpr;
    esi  : TExpr;
    edi  : TExpr;
    ebp  : TExpr;

    &of  : TExpr;
    zf   : TExpr;
    sf   : TExpr;

    temp : array of TExpr;
  end;

  function Testx86(sBinFile:string): TStringList;

  var
    AsmList: TStringList;
implementation

function get_flag_expr(state: x86_ctx; flag: flag_t): TExpr;
var
  ret : TExpr;
begin

    case flag of
      FLAG_OF: ret := state.&of;
	    FLAG_ZF: ret := state.zf;
	    FLAG_SF: ret := state.sf;
	  else
		    raise Exception.Create('bad flag');
    end;

	  if ret <> nil then Result := ret
    else               raise Exception.Create('bad state');

end;

function get_val_expr(z3c: TContext; var state:x86_ctx; op:TCpuOperand):PTExpr;
var
  ret : PTExpr;
begin

    if op.Tipo = T_REG then
	  begin
        case TRegisters(op.reg.reg) of
          EAX: ret := @state.eax;
          EBX: ret := @state.ebx;
          ECX: ret := @state.ecx;
          EDX: ret := @state.edx;
          ESI: ret := @state.esi;
          EDI: ret := @state.edi;
          EBP: ret := @state.ebp;
        else
          raise Exception.Create('bad register');
    end;
        if ret <> nil then Result := ret
        else               raise Exception.Create('bad state');
	  end
    else if op.Tipo = T_IMM then
    begin
        state.temp := state.temp + [ z3c.bv_val(uint32(op.imm.U), 32) ];

        Result := @state.temp[ High(state.temp) ];
    end
    else
		 raise Exception.Create('bad operand type');
end;

procedure create_initial_state(z3c: TContext; var ctx: x86_ctx);
begin

    ctx.eax := TExpr.Create(z3c.bv_const('init_eax', 32));
    ctx.ebx := TExpr.Create(z3c.bv_const('init_ebx', 32));
    ctx.ecx := TExpr.Create(z3c.bv_const('init_ecx', 32));
    ctx.edx := TExpr.Create(z3c.bv_const('init_edx', 32));
    ctx.esi := TExpr.Create(z3c.bv_const('init_esi', 32));
    ctx.edi := TExpr.Create(z3c.bv_const('init_edi', 32));;
    ctx.ebp := TExpr.Create(z3c.bv_const('init_ebp', 32));

	  ctx.&of := TExpr.Create(z3c.bool_const('init_of'));
	  ctx.zf  := TExpr.Create(z3c.bool_const('init_zf'));
	  ctx.sf  := TExpr.Create(z3c.bool_const('init_sf'));
end;

procedure translate_xor(z3c: TContext; ins: TCpuIstruz; old_state:x86_ctx; var new_state:x86_ctx) ;
var
  e1,e2 :  TExpr;
  dst : PTExpr;
begin
	if ins.opCount = 2 then
	begin
		var  op1 : TCpuOperand := ins.operands[0];
		var  op2 : TCpuOperand := ins.operands[1];

		e1  := get_val_expr(z3c, old_state, op1)^;
		e2  := get_val_expr(z3c, old_state, op2)^;
		dst := get_val_expr(z3c, new_state, op1);

		dst^ := OpXorbv(e1, e2);

    AsmList.Append(Format('dst: %s', [dst.toString]));

		new_state.&of := z3c.bool_val(false) ;
		new_state.zf  := OpEq(dst^, 0);
		new_state.sf  := OpMinor(dst^, 0);
	end
	else
		 raise Exception.Create('bad operand count');
end;

procedure translate_and(z3c: TContext; ins: TCpuIstruz; old_state:x86_ctx; var new_state:x86_ctx) ;
var
  e1,e2 : TExpr;
  dst   : PTExpr;
begin
	if ins.opCount = 2 then
	begin
		var  op1 : TCpuOperand := ins.operands[0];
		var  op2 : TCpuOperand := ins.operands[1];

		e1  := get_val_expr(z3c, old_state, op1)^;
		e2  := get_val_expr(z3c, old_state, op2)^;
		dst := get_val_expr(z3c, new_state, op1);

	  dst^ := OpAndbv(e1, e2);

		new_state.&of := z3c.bool_val(false) ;
		new_state.zf  := OpEq(dst^, 0);
		new_state.sf  := OpMinor(dst^, 0);
	end
	else
		 raise Exception.Create('bad operand count');
end;

procedure translate_add(z3c: TContext; ins: TCpuIstruz; old_state:x86_ctx; var new_state:x86_ctx) ;
var
  e1,e2 : TExpr;
  dst : PTExpr;
begin
	if ins.opCount = 2 then
	begin
		var  op1 : TCpuOperand := ins.operands[0];
		var  op2 : TCpuOperand := ins.operands[1];

		e1  := get_val_expr(z3c, old_state, op1)^;
		e2  := get_val_expr(z3c, old_state, op2)^;
		dst := get_val_expr(z3c, new_state, op1);

		dst^ := OpAdd(e1, e2);

    var flag : TExpr     := OpAndbv(e1, z3c.bv_val(1 shl 31, 32));
    var flag1: TExpr     := OpAndbv(dst^,z3c.bv_val(1 shl 31, 32));

		new_state.&of := OpAnd(OpEq(flag,flag), OpNotEq(flag,flag1));
		new_state.zf  := OpEq(dst^, 0);
		new_state.sf  := OpMinor(dst^, 0);
	end
	else
		 raise Exception.Create('bad operand count');
end;

procedure translate_mov(z3c: TContext; ins: TCpuIstruz; old_state:x86_ctx; var new_state:x86_ctx) ;
var
  e1,e2 :TExpr;
  dst : PTExpr;
begin
	if ins.opCount = 2 then
	begin
		var  op1 : TCpuOperand := ins.operands[0];
		var  op2 : TCpuOperand := ins.operands[1];

		e2  := get_val_expr(z3c, old_state, op2)^;
		dst := get_val_expr(z3c, new_state, op1);

		dst^ := TExpr.Create(z3c, e2);
  end
	else
		 raise Exception.Create('bad operand count');
end;

procedure copy_changed_state(var old_state:x86_ctx; var new_state: x86_ctx) ;
begin
     if new_state.eax <> nil then  old_state.eax := new_state.eax ;
     if new_state.ebx <> nil then  old_state.ebx := new_state.ebx  ;
     if new_state.ecx <> nil then  old_state.ecx := new_state.ecx ;
     if new_state.edx <> nil then  old_state.edx := new_state.edx ;
     if new_state.esi <> nil then  old_state.esi := new_state.esi ;
     if new_state.edi <> nil then  old_state.edi := new_state.edi ;
     if new_state.ebp <> nil then  old_state.ebp := new_state.ebp ;
     if new_state.&of <> nil then  old_state.&of := new_state.&of ;
     if new_state.zf <> nil then  old_state.zf := new_state.zf ;
     if new_state.sf <> nil then  old_state.sf := new_state.sf ;
end;


procedure translate_instruction(z3c: TContext; var state: x86_ctx; ins: TCpuIstruz );
var
  new_state: x86_ctx;
begin
    ZeroMemory(@new_state,SizeOf(new_state));

     case  x86_insn(ins.opcode.mnem) of
       X86_INS_XOR: translate_xor(z3c, ins, state, new_state);
       X86_INS_AND: translate_and(z3c, ins, state, new_state);
       X86_INS_ADD: translate_add(z3c, ins, state, new_state);
       X86_INS_MOV: translate_mov(z3c, ins, state, new_state);
     else
        raise Exception.Create('x86 instruction translation not implemented');
     end;

      copy_changed_state(state, new_state);
end;

function test_condition(z3c: TContext;var state: x86_ctx; jcc: TCpuIstruz): opaque_predicate_t ;
var
  cc    : TExpr;
  s1,s2 : TSolver;
  stmp,
  stmp1 : AnsiString;
  m,m1  : TModel;
begin
    Result := undef;

    s1 := TSolver.Create(z3c);
    s2 := TSolver.Create(z3c);

    case x86_insn(jcc.opcode.mnem) of
       X86_INS_JO:  cc := get_flag_expr(state, FLAG_OF);
       X86_INS_JNO: cc := OpNot(get_flag_expr(state, FLAG_OF) );
       X86_INS_JE:	cc := get_flag_expr(state, FLAG_ZF);
       X86_INS_JNE: cc := OpNot(get_flag_expr(state, FLAG_ZF) );
       X86_INS_JS:  cc := get_flag_expr(state, FLAG_SF);
       X86_INS_JNS:	cc := OpNot(get_flag_expr(state,  FLAG_SF) );
       X86_INS_JL:  cc := OpNotEq(get_flag_expr(state, FLAG_SF), get_flag_expr(state, FLAG_OF));
       X86_INS_JLE: cc := OpOrbv(get_flag_expr(state, FLAG_ZF),
					                                (OpNotEq(get_flag_expr(state, FLAG_SF),
                                                   get_flag_expr(state, FLAG_OF)
                                                   )
                                           )
                               );
    else
		  raise Exception.Create('bad jcc');
	  end;

    s1.add(cc);
	  s2.add( OpNot(cc) );

    AsmList.Append(s1.ToStr);
    AsmList.Append(s2.ToStr);

    if  s1.check = unsat then Result := opaque_predicate_not_taken_k;
	  if  s2.check = unsat then Result := opaque_predicate_taken_k;

    if Result = undef then
       Result := not_opaque_predicate_k;

end;

function is_opaque_predicate(instructions: TListCpuIstruz; count: Uint64): opaque_predicate_t;
var
 state : x86_ctx;
 c     : TContext;
 ins_id: Integer;
 ins   : TCpuIstruz;
begin

    c := TContext.Create;

    create_initial_state(c, state);

	  for ins_id := 0 to  count do
	  begin
		     ins := instructions[ins_id];

		     translate_instruction(c, state,ins);
	  end;

	  Result := test_condition(c, state, instructions[count+1]);

    c.Free;
end;

function conditional_index(LisAsm: TListCpuIstruz): UInt64;
var
  i : Integer;
  opCode : Mnemonics;
begin
    Result := 0;
    for i := 0 to High(LisAsm) do
    begin
        opCode := LisAsm[i].opcode.mnem;
        case x86_insn(opCode) of
          X86_INS_JAE,
          X86_INS_JA,
          X86_INS_JBE,
          X86_INS_JB,
          X86_INS_JCXZ,
          X86_INS_JECXZ,
          X86_INS_JE,
          X86_INS_JGE,
          X86_INS_JG,
          X86_INS_JLE,
          X86_INS_JL,
          X86_INS_JMP,
          X86_INS_JNE,
          X86_INS_JNO,
          X86_INS_JNP,
          X86_INS_JNS,
          X86_INS_JO,
          X86_INS_JP,
          X86_INS_JRCXZ,
          X86_INS_JS:     Exit(i)
        else
          Result := (Ord(X86_INS_ENDING));
        end;
    end;

end;

function Testx86(sBinFile:string): TStringList;
var
  dis    : TCapstone;
  ms     : TMemoryStream;
  LisAsm : TListCpuIstruz;
  addr   : UInt64;
  i      : Integer;
  jcc_id : UInt64;
  res    : opaque_predicate_t;

begin


  dis     := TCapstone.Create;
  ms      := TMemoryStream.Create;
  AsmList := TStringList.Create;
  try
    (***load binary *)
    ms.LoadFromFile(sBinFile);
    addr  := 0;
    dis.DisAsmBlock(addr,ms.Memory,ms.Size,LisAsm);
    (****end load binary**)
    AsmList.Add('test_opaque_predicate :'+ ExtractFileName(sBinFile)) ;
    AsmList.Add('asm code');
    for i := 0 to High(LisAsm) do
      AsmList.Add(LisAsm[i].Istr_Str);
    AsmList.Add('');

    jcc_id := conditional_index(LisAsm);
    if jcc_id <> Ord(X86_INS_ENDING) then
    begin
        AsmList.Add('testing '+ LisAsm[jcc_id].Istr_Str);

        res := is_opaque_predicate(LisAsm, jcc_id - 1);

        case res of
          not_opaque_predicate_k:      AsmList.Add('not an opaque predicate');
          opaque_predicate_taken_k:    AsmList.Add('opaque predicate: always taken');
          opaque_predicate_not_taken_k:AsmList.Add('opaque predicate: never taken');
        end;

    end else
    begin
        AsmList.Add('testing not required');
    end;

  finally
    ms.Free;
    dis.Free;
    Result := AsmList;
  end;

end;

end.
