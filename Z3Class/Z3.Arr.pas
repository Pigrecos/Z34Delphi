{*******************************************************}
{                                                       }
{       Z3 Wrapper Class for Delphi                     }
{                                                       }
{       Unit and class for Z3 Array                     }
{                                                       }
{       Copyright (C) 2019 Pigrecos(Max)                }
{       All rights reserved.                            }
{       MIT License                                     }
{*******************************************************}

unit Z3.Arr;



interface

type

  TZ3Array<T> = class
       m_array : TArray<T>;
       m_size  : Cardinal;

  private
       function GetItem(Index: Cardinal): T;
       procedure SetItem(Index: Cardinal; const Value: T);
       function GetArray: TArray<T>;
    public

       constructor Create(sz : Cardinal); overload;
       constructor Create(s : TZ3Array<T>); overload;
       destructor  Destroy; override;
       procedure   Resize(sz: Cardinal);
       function    Size: Cardinal;
       function    Ptr: Pointer;

       property Items[Index: Cardinal]: T read GetItem write SetItem;
       property ToBaseArray: TArray<T> read GetArray;
  end;


implementation

{ TZ3Array<T> }

constructor TZ3Array<T>.Create(s: TZ3Array<T>);
begin
    m_array := s.m_array;
    m_size  := s.m_size;
end;

constructor TZ3Array<T>.Create(sz: Cardinal);
begin
    SetLength(m_array,sz);
    m_size  := sz;
end;

destructor TZ3Array<T>.Destroy;
begin
    SetLength(m_array,0);
    m_size :=0;
end;

function TZ3Array<T>.GetArray: TArray<T>;
begin
   Result := m_array;
end;

function TZ3Array<T>.GetItem(Index: Cardinal): T;
begin
    assert(Index < m_size);
    Result := m_array[Index]
end;

procedure TZ3Array<T>.SetItem(Index: Cardinal; const Value: T);
begin
    assert(Index < m_size);
    m_array[Index] := Value;
end;


function TZ3Array<T>.Ptr: Pointer;
begin
    assert(m_size > 0);
    Result := @m_array[0]
end;

procedure TZ3Array<T>.Resize(sz: Cardinal);
begin
    m_size := sz;
    SetLength(m_array,sz)
end;

function TZ3Array<T>.Size: Cardinal;
begin
    Result := m_size;
end;

end.
