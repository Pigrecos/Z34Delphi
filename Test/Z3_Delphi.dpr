program Z3_Delphi;

uses
  Vcl.Forms,
  UntMain in 'UntMain.pas' {Main},
  z3 in '..\Include\z3.pas',
  z3__fixedpoint in '..\Include\z3__fixedpoint.pas',
  z3_algebraic in '..\Include\z3_algebraic.pas',
  z3_ast_containers in '..\Include\z3_ast_containers.pas',
  z3_fpa in '..\Include\z3_fpa.pas',
  z3_optimization in '..\Include\z3_optimization.pas',
  z3_polynomial in '..\Include\z3_polynomial.pas',
  z3_rcf in '..\Include\z3_rcf.pas',
  z3_spacer in '..\Include\z3_spacer.pas';

{$R *.res}

begin
  Application.Initialize;
  Application.MainFormOnTaskbar := True;
  Application.CreateForm(TMain, Main);
  Application.Run;
end.
