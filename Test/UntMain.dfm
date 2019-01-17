object Main: TMain
  Left = 0
  Top = 0
  Caption = 'Main'
  ClientHeight = 262
  ClientWidth = 458
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
    Width = 458
    Height = 221
    Align = alClient
    Caption = 'pnl1'
    TabOrder = 0
    object reLog: TRichEdit
      Left = 1
      Top = 1
      Width = 456
      Height = 219
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
    end
  end
  object pnlBtn: TPanel
    Left = 0
    Top = 221
    Width = 458
    Height = 41
    Align = alBottom
    TabOrder = 1
    object btnStart: TBitBtn
      Left = 1
      Top = 6
      Width = 75
      Height = 25
      Caption = 'Start'
      TabOrder = 0
      OnClick = btnStartClick
    end
  end
end
