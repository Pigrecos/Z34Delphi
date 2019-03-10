{*******************************************************}
{                                                       }
{       Z3 Wrapper Class for Delphi                     }
{                                                       }
{       Unit and class for Z3 Stats                     }
{                                                       }
{       Copyright (C) 2019 Pigrecos(Max)                }
{       All rights reserved.                            }
{       MIT License                                     }
{*******************************************************}

unit Z3.Stats;

interface
 uses
   System.SysUtils,
   z3,
   Z3.Context;

Type
  TStats = class(Z3Object)
      m_stats : Z3_stats;
      procedure init(e: Z3_stats);
    public
        constructor Create(c: TContext);overload;
        constructor Create(c: TContext; e: Z3_stats);overload;
        constructor Create(const  s: TStats); overload;
        destructor  Destroy;
        function ToZ3_stats: Z3_stats;
        function Assigned(s: TStats):TStats;
        function size: Cardinal;
        function Key(i: Cardinal):AnsiString;
        function is_uint(i: Cardinal): Boolean;
        function is_double(i: Cardinal): Boolean;
        function uint_value(i: Cardinal): Cardinal;
        function double_value(i: Cardinal): double;
        function ToStr(const s: TStats):AnsiString;
    end;

implementation

{ TStats }

constructor TStats.Create(c: TContext);
begin
    inherited Create(c);
    m_stats := nil;
end;

constructor TStats.Create(c: TContext; e: Z3_stats);
begin
    inherited Create(c);
    init(e);
end;

constructor TStats.Create(const s: TStats);
begin
   inherited Create(s);
   init(s.m_stats);
end;

destructor TStats.Destroy;
begin
   if m_stats <> nil then
      Z3_stats_dec_ref(ctx.ToZ3_Context, m_stats)
end;

procedure TStats.init(e: Z3_stats);
begin
   m_stats := e;
   Z3_stats_inc_ref(ctx.ToZ3_Context, m_stats)
end;

function TStats.Assigned(s: TStats): TStats;
begin
  Z3_stats_inc_ref(s.ctx.ToZ3_Context, s.m_stats);
  if m_stats <> nil then
     Z3_stats_dec_ref(ctx.ToZ3_Context, m_stats);
  m_ctx   := s.m_ctx;
  m_stats := s.m_stats;
  Result := Self
end;

function TStats.double_value(i: Cardinal): double;
begin
  var r : Double := Z3_stats_get_double_value(ctx.ToZ3_Context, m_stats, i);
  check_error;
  Result := r;
end;

function TStats.uint_value(i: Cardinal): Cardinal;
begin
   var r : Cardinal := Z3_stats_get_uint_value(ctx.ToZ3_Context, m_stats, i);
   check_error();
   Result := r
end;

function TStats.is_double(i: Cardinal): Boolean;
begin
  var r : Boolean := Z3_stats_is_double(ctx.ToZ3_Context, m_stats, i);
  check_error;
  Result := r
end;

function TStats.is_uint(i: Cardinal): Boolean;
begin
  var r : Boolean := Z3_stats_is_uint(ctx.ToZ3_Context, m_stats, i);
  check_error;
  Result := r
end;

function TStats.Key(i: Cardinal): AnsiString;
begin
  var s : Z3_string := Z3_stats_get_key(ctx.ToZ3_Context, m_stats, i);
  check_error;
  Result := s;
end;

function TStats.size: Cardinal;
begin
    Result := Z3_stats_size(ctx.ToZ3_Context, m_stats)
end;

function TStats.ToStr(const s: TStats): AnsiString;
begin
   Result := Z3_stats_to_string(s.ctx.ToZ3_Context, s.ToZ3_stats)
end;

function TStats.ToZ3_stats: Z3_stats;
begin
    Result  := m_stats
end;

end.
