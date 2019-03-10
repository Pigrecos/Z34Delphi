program Z3_Delphi;

uses
  Vcl.Forms,
  UntMain in 'UntMain.pas' {Main},
  testAsmx86 in 'testAsmx86.pas',
  z3 in '..\Z3Api\z3.pas',
  z3__fixedpoint in '..\Z3Api\z3__fixedpoint.pas',
  z3_algebraic in '..\Z3Api\z3_algebraic.pas',
  z3_ast_containers in '..\Z3Api\z3_ast_containers.pas',
  z3_fpa in '..\Z3Api\z3_fpa.pas',
  z3_optimization in '..\Z3Api\z3_optimization.pas',
  z3_polynomial in '..\Z3Api\z3_polynomial.pas',
  z3_rcf in '..\Z3Api\z3_rcf.pas',
  z3_spacer in '..\Z3Api\z3_spacer.pas',
  Z3.Arr in '..\Z3Class\Z3.Arr.pas',
  Z3.Config in '..\Z3Class\Z3.Config.pas',
  Z3.Context in '..\Z3Class\Z3.Context.pas',
  Z3.Def in '..\Z3Class\Z3.Def.pas',
  Z3.Func in '..\Z3Class\Z3.Func.pas',
  Z3.Model in '..\Z3Class\Z3.Model.pas',
  Z3.Par_Desc in '..\Z3Class\Z3.Par_Desc.pas',
  Z3.Solver in '..\Z3Class\Z3.Solver.pas',
  Z3.Stats in '..\Z3Class\Z3.Stats.pas',
  Z3.Tactic in '..\Z3Class\Z3.Tactic.pas';

{$R *.res}

begin
  Application.Initialize;
  Application.MainFormOnTaskbar := True;
  Application.CreateForm(TMain, Main);
  Application.Run;
end.
