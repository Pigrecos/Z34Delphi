{*******************************************************}
{                                                       }
{       Z3 Wrapper Class for Delphi                     }
{                                                       }
{       Unit for Global Definition                      }
{                                                       }
{       Copyright (C) 2019 Pigrecos(Max)                }
{       All rights reserved.                            }
{       MIT License                                     }
{*******************************************************}

unit Z3.Def;

interface
   uses System.SysUtils;

type

rounding_mode = (RNA, RNE, RTP, RTN, RTZ);
check_result  = ( unsat, sat, unknown );

  TZ3Exception     = class(Exception);
  unsigned         = Cardinal;


implementation

end.
