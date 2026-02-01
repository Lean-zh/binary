module

public import Binary.Basic
meta import Lean

namespace Binary

public section

@[always_inline]
def fail (msg : String) : Get α :=
  throw (.userError msg)

@[specialize]
def many (p : Get α) : Get (Array α) := do
  let mut data := #[]
  repeat
    let some x ← optional p | break
    data := data.push x
  return data

@[inline, specialize]
def many1 (p : Get α) : Get (Array α) := do
  let first ← p
  let rest ← many p
  return rest.insertIdx 0 first

@[always_inline, specialize]
def shouldBeEOI (includeUnExpected : Bool := false) : Get Unit := do
  let x ← remaining
  if x > 0 then
    if includeUnExpected then
      let some c ← peek? | unreachable!
      fail s!"unexpected '{Char.ofNat c.toNat}', expected EOI"
    else
      fail "expected EOI"

@[always_inline]
def notFollowedBy (p : Get α) : Get Unit := fun d =>
  match p d with
  | .success _ _ => DecodeResult.error (.userError "unexpected lookahead") d
  | .error _ _ => DecodeResult.success () d
  | .pending _ => DecodeResult.error (.userError "unexpected pending lookahead") d

-- TODO: refactor following definitions for performance

@[inline, specialize]
def takeAtLeast (n : Nat) (p : Get α) : Get (Array α) := do
  let mut r := Array.emptyWithCapacity n
  repeat
    if r.size == n then break
    let x ← p
    r := r.push x
  repeat
    let some x ← optional p | break
    r := r.push x
  return r

/-- inclusive -/
@[inline, specialize]
def takeUpTo (n : Nat) (p : Get α) : Get (Array α) := do
  let mut r := #[]
  repeat
    if r.size == n then break
    let some x ← optional p | break
    r := r.push x
  return r

/-- inclusive -/
@[inline, specialize]
def take1UpTo (n : Nat) (p : Get α) : Get (Array α) := do
  let x ← p
  let mut r := #[x]
  repeat
    if r.size == n then break
    let some x ← optional p | break
    r := r.push x
  return r

@[inline, specialize]
def takeN (n : Nat) (p : Get α) : Get (Array α) := do
  let mut r := Array.emptyWithCapacity 0
  repeat
    if r.size == n then break
    let x ← p
    r := r.push x
  return r

/--inclusive on both sides -/
@[inline, specialize]
def takeRange (min max : Nat) (p : Get α) : Get (Array α) := do
  let mut r := Array.emptyWithCapacity min
  repeat
    if r.size == min then break
    let x ← p
    r := r.push x
  repeat
    if r.size == max then break
    let some x ← optional p | break
    r := r.push x
  return r

@[inline, specialize]
def sepBy (x : Get α) (sep : Get Unit) : Get (Array α) := do
  let some l ← optional x | return #[]
  let mut t := #[l]
  repeat
    let some v ← optional (sep *> x) | break
    t := t.push v
  return t

@[inline, specialize]
def sepBy1 (x : Get α) (s : Get Unit) : Get (Array α) := do
  let l ← x
  let mut t := #[l]
  repeat
    let some v ← optional (s *> x) | break
    t := t.push v
  return t

@[inline, specialize]
def sepByUpTo (n : Nat) (x : Get α) (s : Get Unit) : Get (Array α) := do
  let some l ← optional x | return #[]
  let mut t := #[l]
  repeat
    if t.size ≥ n then break
    let some v ← optional (s *> x) | break
    t := t.push v
  return t

@[inline, specialize]
def sepBy1UpTo (n : Nat) (x : Get α) (s : Get Unit) : Get (Array α) := do
  let l ← x
  let mut t := #[l]
  repeat
    if t.size ≥ n then break
    let some v ← optional (s *> x) | break
    t := t.push v
  return t

end

public section

@[always_inline]
instance : Decode UInt8 where
  get d :=
    if h : d.offset < d.data.size then
      DecodeResult.success (d.data.get d.offset) {d with offset := d.offset + 1}
    else
      DecodeResult.mkEOI d

@[always_inline]
instance : Decode Int8 where
  get d :=
    if h : d.offset < d.data.size then
      DecodeResult.success (d.data.get d.offset).toInt8 {d with offset := d.offset + 1}
    else
      DecodeResult.mkEOI d

end

public section

/--
This function **exhaustively** reads in all bytes starting from the current offset.
The outermost caller **must** call `DecodeResult.terminate` to break from this function. -/
def exhaust : Get ByteArray := do
  let r ← remaining
  let data ← get_bytes r
  let mut rs := #[]
  repeat
    shrink
    let some x ← (optional <| pending <| getThe UInt8) | break
    let r ← remaining
    let xs ← get_bytes r
    rs := rs.push ⟨#[x]⟩
    rs := rs.push xs
  return rs.foldl (init := data) (· ++ ·)

end

namespace Primitive

variable {ω m} [Monad m] [STWorld ω m] [MonadLiftT (ST ω) m]

private meta def generate_prim (le : Bool) (unsigned : Bool) (type : Lean.TSyntax `ident) (size : Lean.TSyntax `num) : Lean.MacroM Lean.Command := do
  let len := size.getNat
    if len = 0 then
      Lean.Macro.throwErrorAt size "size cannot be 0"
    let newSize := Lean.TSyntax.mk <| size.raw.setArg 0 (size.raw[0].setAtomVal s!"{len - 1}")
    let d ← Lean.mkIdent <$> Lean.Macro.addMacroScope `d
    let d_offset ← `($(Lean.mkIdent `Decoder.offset) $d:ident)
    let d_data ← `($(Lean.mkIdent `Decoder.data) $d:ident)
    let d_data_size ← `($(Lean.mkIdent `ByteArray.size) ($(Lean.mkIdent `Decoder.data) $d:ident))
    let ns := List.range len
    let ts ← ns.mapM fun x => do
      let y ←
        if unsigned then
          `($(Lean.mkIdent `ByteArray.get) $d_data ($d_offset + $(Lean.Syntax.mkNatLit x):num))
        else
          `($(Lean.mkIdent `ByteArray.get) $d_data ($d_offset + $(Lean.Syntax.mkNatLit x):num) |>.toInt8)
      let y ←
        if unsigned then
          `($(Lean.mkIdent (Lean.Name.mkStr2 "UInt8" s!"to{type.getId.getString!}")) $y)
        else
          `($(Lean.mkIdent (Lean.Name.mkStr2 "Int8" s!"to{type.getId.getString!}")) $y)
      let shift := if le then x * 8 else (len - 1 - x) * 8
      `($y <<< $(Lean.Syntax.mkNatLit shift):num)
    let combined ←
      match ts with
      | [] => unreachable!
      | [x] => pure x
      | head :: tail => do
        tail.foldlM (init := head) fun (x : Lean.Term) y => do
          `($x ||| $y)
    let code ← `(command|
      @[always_inline]
      scoped instance : Decode $type where
        get $d:ident :=
          if h : $d_offset + $newSize:num < $d_data_size then
            let val := $combined
            DecodeResult.success val {$d with offset := $d_offset + $(Lean.Syntax.mkNatLit len):num}
          else
            DecodeResult.mkEOI d
      )
    return code

local syntax "prim_unsigned_le " ident num : command
local syntax "prim_unsigned_be " ident num : command
local syntax "prim_signed_le " ident num : command
local syntax "prim_signed_be " ident num : command

local macro_rules
  | `(command| prim_unsigned_le $type $size) => generate_prim true true type size
  | `(command| prim_unsigned_be $type $size) => generate_prim false true type size
  | `(command| prim_signed_le $type $size) => generate_prim true false type size
  | `(command| prim_signed_be $type $size) => generate_prim false false type size

public section

namespace LE

prim_unsigned_le UInt16 2
prim_unsigned_le UInt32 4
prim_unsigned_le UInt64 8

prim_signed_le Int16 2
prim_signed_le Int32 4
prim_signed_le Int64 8

@[always_inline]
scoped instance : Decode Float32 where
  get d := get (α := UInt32) d |>.map Float32.ofBits

@[always_inline]
scoped instance : Decode Float where
  get d := get (α := UInt64) d |>.map Float.ofBits

end LE

namespace BE

prim_unsigned_be UInt16 2
prim_unsigned_be UInt32 4
prim_unsigned_be UInt64 8

prim_signed_be Int16 2
prim_signed_be Int32 4
prim_signed_be Int64 8

@[always_inline]
scoped instance : Decode Float32 where
  get d := get (α := UInt32) d |>.map Float32.ofBits

@[always_inline]
scoped instance : Decode Float where
  get d := get (α := UInt64) d |>.map Float.ofBits

end BE

end

end Primitive
