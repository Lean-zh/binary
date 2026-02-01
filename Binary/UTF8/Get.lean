module

public import Binary.Basic
public import Binary.Get

public section

namespace Binary.UTF8

@[always_inline]
private def byteToChar (b : UInt8) : Char :=
  Char.ofNat b.toNat

-- @[always_inline]
-- private def charToString (c : Char) : String :=
--   String.ofList [c] -- TODO: how about `Char.toString`?

@[always_inline]
private def chars_to_string (xs : Array Char) : String :=
  String.ofList xs.toList

@[always_inline, specialize]
def satisfy (p : Char → Bool) : Get Char := do
  let b ← getThe UInt8
  let c := byteToChar b
  if p c then
    return c
  else
    fail "unexpected byte"

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

@[always_inline]
def notFollowedBy (p : Get α) : Get Unit := fun d =>
  match p d with
  | .success _ _ => DecodeResult.error (.userError "unexpected lookahead") d
  | .error _ _ => DecodeResult.success () d
  | .pending _ => DecodeResult.error (.userError "unexpected pending lookahead") d
