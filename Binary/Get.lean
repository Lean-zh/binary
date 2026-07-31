module

public import Binary.Basic

namespace Binary

public section

@[always_inline]
def fail (msg : String) : Get α :=
  throw (.userError msg)

def many (p : Get α) : Get (Array α) := do
  let mut data := #[]
  repeat
    let some x ← optional p | break
    data := data.push x
  return data

@[inline]
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
@[inline]
def takeUpTo (n : Nat) (p : Get α) : Get (Array α) := do
  let mut r := Array.emptyWithCapacity n
  while true do
    if r.size == n then break
    let some x ← optional p | break
    r := r.push x
  return r

/-- inclusive -/
@[inline]
def take1UpTo (n : Nat) (p : Get α) : Get (Array α) := do
  let x ← p
  let mut r := (Array.emptyWithCapacity n).push x
  repeat
    if r.size == n then break
    let some x ← optional p | break
    r := r.push x
  return r

@[inline]
def takeN (n : Nat) (p : Get α) : Get (Array α) := do
  let mut r := Array.emptyWithCapacity n
  repeat
    if r.size == n then break
    let x ← p
    r := r.push x
  return r

/--inclusive on both sides -/
@[inline]
def takeRange (min max : Nat) (p : Get α) : Get (Array α) := do
  let mut r := Array.emptyWithCapacity max
  repeat
    if r.size == min then break
    let x ← p
    r := r.push x
  repeat
    if r.size == max then break
    let some x ← optional p | break
    r := r.push x
  return r

@[inline]
def sepBy (x : Get α) (sep : Get Unit) : Get (Array α) := do
  let some l ← optional x | return #[]
  let mut t := #[l]
  repeat
    let some v ← optional (sep *> x) | break
    t := t.push v
  return t

@[inline]
def sepBy1 (x : Get α) (s : Get Unit) : Get (Array α) := do
  let l ← x
  let mut t := #[l]
  repeat
    let some v ← optional (s *> x) | break
    t := t.push v
  return t

@[inline]
def sepByUpTo (n : Nat) (x : Get α) (s : Get Unit) : Get (Array α) := do
  let some l ← optional x | return #[]
  let mut t := (Array.emptyWithCapacity n).push l
  repeat
    if t.size ≥ n then break
    let some v ← optional (s *> x) | break
    t := t.push v
  return t

@[inline]
def sepBy1UpTo (n : Nat) (x : Get α) (s : Get Unit) : Get (Array α) := do
  let l ← x
  let mut t := (Array.emptyWithCapacity n).push l
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

public section

namespace LE

@[always_inline]
scoped instance : Decode UInt16 where
  get d :=
    if h : d.offset + 1 < d.data.size then
      let val :=
        (d.data[d.offset + 0]).toUInt16 |||
        (d.data[d.offset + 1]).toUInt16 <<< 8
      DecodeResult.success val {d with offset := d.offset + 2}
    else
      DecodeResult.mkEOI d

@[always_inline]
scoped instance : Decode UInt32 where
  get d :=
    if h : d.offset + 3 < d.data.size then
      let val :=
        (d.data.get (d.offset + 0)).toUInt32 |||
        (d.data.get (d.offset + 1)).toUInt32 <<< 8 |||
        (d.data.get (d.offset + 2)).toUInt32 <<< 16 |||
        (d.data.get (d.offset + 3)).toUInt32 <<< 24
      DecodeResult.success val {d with offset := d.offset + 4}
    else
      DecodeResult.mkEOI d

@[always_inline]
scoped instance : Decode UInt64 where
  get d :=
    if h : d.offset + 7 < d.data.size then
      let val :=
        (d.data.get (d.offset + 0)).toUInt64 |||
        (d.data.get (d.offset + 1)).toUInt64 <<< 8 |||
        (d.data.get (d.offset + 2)).toUInt64 <<< 16 |||
        (d.data.get (d.offset + 3)).toUInt64 <<< 24 |||
        (d.data.get (d.offset + 4)).toUInt64 <<< 32 |||
        (d.data.get (d.offset + 5)).toUInt64 <<< 40 |||
        (d.data.get (d.offset + 6)).toUInt64 <<< 48 |||
        (d.data.get (d.offset + 7)).toUInt64 <<< 56
      DecodeResult.success val {d with offset := d.offset + 8}
    else
      DecodeResult.mkEOI d

@[always_inline]
scoped instance : Decode Int16 where
  get := Int16.ofUInt16 <$> Decode.get (α := UInt16)

@[always_inline]
scoped instance : Decode Int32 where
  get := Int32.ofUInt32 <$> Decode.get (α := UInt32)

@[always_inline]
scoped instance : Decode Int64 where
  get := Int64.ofUInt64 <$> Decode.get (α := UInt64)

@[always_inline]
scoped instance : Decode Float32 where
  get d := get (α := UInt32) d |>.map Float32.ofBits

@[always_inline]
scoped instance : Decode Float where
  get d := get (α := UInt64) d |>.map Float.ofBits

end LE

namespace BE

@[always_inline]
scoped instance : Decode UInt16 where
  get d :=
    if h : d.offset + 1 < d.data.size then
      let val :=
        (d.data.get (d.offset + 0)).toUInt16 <<< 8 |||
        (d.data.get (d.offset + 1)).toUInt16
      DecodeResult.success val {d with offset := d.offset + 2}
    else
      DecodeResult.mkEOI d

@[always_inline]
scoped instance : Decode UInt32 where
  get d :=
    if h : d.offset + 3 < d.data.size then
      let val :=
        (d.data.get (d.offset + 0)).toUInt32 <<< 24 |||
        (d.data.get (d.offset + 1)).toUInt32 <<< 16 |||
        (d.data.get (d.offset + 2)).toUInt32 <<< 8 |||
        (d.data.get (d.offset + 3)).toUInt32
      DecodeResult.success val {d with offset := d.offset + 4}
    else
      DecodeResult.mkEOI d

@[always_inline]
scoped instance : Decode UInt64 where
  get d :=
    if h : d.offset + 7 < d.data.size then
      let val :=
        (d.data.get (d.offset + 0)).toUInt64 <<< 56 |||
        (d.data.get (d.offset + 1)).toUInt64 <<< 48 |||
        (d.data.get (d.offset + 2)).toUInt64 <<< 40 |||
        (d.data.get (d.offset + 3)).toUInt64 <<< 32 |||
        (d.data.get (d.offset + 4)).toUInt64 <<< 24 |||
        (d.data.get (d.offset + 5)).toUInt64 <<< 16 |||
        (d.data.get (d.offset + 6)).toUInt64 <<< 8 |||
        (d.data.get (d.offset + 7)).toUInt64
      DecodeResult.success val {d with offset := d.offset + 8}
    else
      DecodeResult.mkEOI d

@[always_inline]
scoped instance : Decode Int16 where
  get := Int16.ofUInt16 <$> Decode.get (α := UInt16)

@[always_inline]
scoped instance : Decode Int32 where
  get := Int32.ofUInt32 <$> Decode.get (α := UInt32)

@[always_inline]
scoped instance : Decode Int64 where
  get := Int64.ofUInt64 <$> Decode.get (α := UInt64)

@[always_inline]
scoped instance : Decode Float32 where
  get d := get (α := UInt32) d |>.map Float32.ofBits

@[always_inline]
scoped instance : Decode Float where
  get d := get (α := UInt64) d |>.map Float.ofBits

end BE

end

end Primitive
