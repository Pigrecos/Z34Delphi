{*******************************************************}
{                                                       }
{       Z3 Wrapper Class for Delphi                     }
{                                                       }
{       Unit and class for Z3 Config                    }
{                                                       }
{       Copyright (C) 2019 Pigrecos(Max)                }
{       All rights reserved.                            }
{       MIT License                                     }
{*******************************************************}

unit Z3.Config;

interface
    uses  System.SysUtils,
          z3;

type
 (**
     \brief Z3 global configuration object.
  *)
  TConfig = class
     m_cfg : Z3_config    ;
    public
        constructor Create(const  s: TConfig); overload;
        constructor Create ;overload ;
        destructor Destroy;

        function ToZ3_config:Z3_config;
        (**
           \brief Set global parameter \c param with string \c value.
        *)
        procedure &set(param: PAnsiChar; value: PAnsiChar); overload;
        (**
           \brief Set global parameter \c param with Boolean \c value.
        *)
        procedure &set(param: PAnsiChar; value: Boolean);overload;
        (**
           \brief Set global parameter \c param with integer \c value.
        *)
        procedure &set(param: PAnsiChar; value: Integer); overload;
  end;


implementation

{ TConfig }

constructor TConfig.Create(const s: TConfig);
begin
    Self := s;
end;

constructor TConfig.Create;
begin
     m_cfg := Z3_mk_config;
end;

destructor TConfig.Destroy;
begin
     Z3_del_config(m_cfg);
end;

function TConfig.ToZ3_config: Z3_config;
begin
    Result := m_cfg
end;

procedure TConfig.&set(param: PAnsiChar; value: Integer);
var
 s : AnsiString;
begin
     s := AnsiString(IntToStr(value));
     Z3_set_param_value(m_cfg, param, @s);
end;

procedure TConfig.&set(param: PAnsiChar; value: Boolean);
var
 bVal : PAnsiChar;
begin
     if value then  bVal := 'true'
     else           bVal := 'false' ;

     Z3_set_param_value(m_cfg, param, bVal);
end;

procedure TConfig.&set(param, value: PAnsiChar);
begin
    Z3_set_param_value(m_cfg, param, value);
end;

end.
