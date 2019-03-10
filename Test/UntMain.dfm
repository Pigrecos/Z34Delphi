object Main: TMain
  Left = 0
  Top = 0
  Caption = 'Main'
  ClientHeight = 465
  ClientWidth = 468
  Color = clBtnFace
  Font.Charset = DEFAULT_CHARSET
  Font.Color = clWindowText
  Font.Height = -11
  Font.Name = 'Tahoma'
  Font.Style = []
  OldCreateOrder = False
  PixelsPerInch = 96
  TextHeight = 13
  object pnl1: TPanel
    Left = 0
    Top = 0
    Width = 468
    Height = 424
    Align = alClient
    Caption = 'pnl1'
    TabOrder = 0
    ExplicitWidth = 458
    ExplicitHeight = 221
    object reLog: TRichEdit
      Left = 1
      Top = 1
      Width = 466
      Height = 422
      Align = alClient
      Font.Charset = ANSI_CHARSET
      Font.Color = clWindowText
      Font.Height = -11
      Font.Name = 'Tahoma'
      Font.Style = []
      Lines.Strings = (
        'reLog')
      ParentFont = False
      ScrollBars = ssBoth
      TabOrder = 0
      Zoom = 100
      OnChange = reLogChange
      ExplicitWidth = 456
      ExplicitHeight = 219
    end
  end
  object pnlBtn: TPanel
    Left = 0
    Top = 424
    Width = 468
    Height = 41
    Align = alBottom
    TabOrder = 1
    ExplicitTop = 221
    ExplicitWidth = 458
    object btnTestApi: TBitBtn
      Left = 1
      Top = 6
      Width = 89
      Height = 25
      Caption = 'Start Test API'
      TabOrder = 0
      OnClick = btnTestApiClick
    end
    object btnTestX86: TBitBtn
      Left = 227
      Top = 6
      Width = 88
      Height = 25
      Caption = 'Start x86 test'
      TabOrder = 1
      OnClick = btnTestX86Click
    end
    object btnTestClass: TBitBtn
      Left = 96
      Top = 6
      Width = 89
      Height = 25
      Caption = 'Start Test Class'
      TabOrder = 2
      OnClick = btnTestClassClick
    end
    object edtBinFile: TEdit
      Left = 319
      Top = 9
      Width = 121
      Height = 21
      TabOrder = 3
      Text = 'asmx86/test5.bin'
    end
  end
end
