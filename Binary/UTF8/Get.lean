module

public import Binary.Basic
public import Binary.Get

public section

namespace Binary.UTF8

@[always_inline]
private def byteToChar (b : UInt8) : Char :=
  Char.ofNat b.toNat

@[always_inline]
private def chars_to_string (xs : Array Char) : String :=
  String.ofList xs.toList

@[always_inline, specialize]
def satisfy (p : Char → Bool) : Get Char := do
  let b ← pending (getThe UInt8)
  let b1 := UInt8.toUInt32 b
  if b1 <= 127 then
    let c := Char.ofNat b.toNat
    if p c then
      return c
    else
      fail "unexpected byte"
  else if 194 ≤ b1 && b1 ≤ 223 then -- 2-byte sequence
    let b2 ← pending (getThe UInt8)
    let b2u := UInt8.toUInt32 b2
    if (b2u &&& 192) != 128 then fail "invalid utf8 continuation"
    let cp := ((b1 &&& 31) <<< 6) ||| (b2u &&& 63)
    let c := Char.ofNat cp.toNat
    if p c then
      return c
    else
      fail "unexpected byte"
  else if 224 ≤ b1 && b1 ≤ 239 then -- 3-byte sequence
    let b2 ← pending (getThe UInt8)
    let b3 ← pending (getThe UInt8)
    let b2u := UInt8.toUInt32 b2
    let b3u := UInt8.toUInt32 b3
    if (b2u &&& 192) != 128 || (b3u &&& 192) != 128 then fail "invalid utf8 continuation"
    -- prevent overlongs and surrogates
    if b1 == 224 && b2u < 160 then fail "overlong utf8 sequence"
    if b1 == 237 && b2u > 159 then fail "utf8 surrogate"
    let cp := ((b1 &&& 15) <<< 12) ||| ((b2u &&& 63) <<< 6) ||| (b3u &&& 63)
    let c := Char.ofNat cp.toNat
    if p c then
      return c
    else
      fail "unexpected byte"
  else if 240 ≤ b1 && b1 ≤ 244 then -- 4-byte sequence
    let b2 ← pending (getThe UInt8)
    let b3 ← pending (getThe UInt8)
    let b4 ← pending (getThe UInt8)
    let b2u := UInt8.toUInt32 b2
    let b3u := UInt8.toUInt32 b3
    let b4u := UInt8.toUInt32 b4
    if (b2u &&& 192) != 128 || (b3u &&& 192) != 128 || (b4u &&& 192) != 128 then
      fail "invalid utf8 continuation"
    if b1 == 240 && b2u < 144 then fail "overlong utf8 sequence"
    if b1 == 244 && b2u > 143 then fail "utf8 codepoint too large"
    let cp := ((b1 &&& 7) <<< 18) ||| ((b2u &&& 63) <<< 12) ||| ((b3u &&& 63) <<< 6) ||| (b4u &&& 63)
    let cpNat := cp.toNat
    if cpNat > 0x10FFFF then fail "utf8 codepoint out of range"
    let c := Char.ofNat cpNat
    if p c then
      return c
    else
      fail "unexpected byte"
  else
    fail "invalid utf8 leading byte"

@[always_inline]
def pchar (c : Char) : Get Char := satisfy (· == c)

@[always_inline]
def pstring (s : String) : Get String := do
  for c in s.toList do
    _ ← inline pchar c
  return s

@[always_inline]
def skipChar (c : Char) : Get Unit := pchar c *> pure ()

@[always_inline]
def skipString (s : String) : Get Unit := pstring s *> pure ()

@[always_inline, specialize]
def manyChars (p : Get Char) : Get String :=
  chars_to_string <$> many p

@[always_inline, specialize]
def many1Chars (p : Get Char) : Get String :=
  chars_to_string <$> many1 p
