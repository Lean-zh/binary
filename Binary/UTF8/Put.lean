module

public import Binary.Basic
public import Binary.Get

public section

namespace Binary.UTF8

@[always_inline]
def put_str (s : String) : Put := do
  put_bytes s.toUTF8

@[always_inline]
def put_char (c : Char) : Put := do
  put_str c.toString
