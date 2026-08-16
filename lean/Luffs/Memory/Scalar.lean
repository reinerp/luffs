import Luffs.Memory.Value

set_option autoImplicit false

namespace Luffs.Memory.Scalar

open Luffs.Memory

def byteOfBV8 (value : BitVec 8) : Byte := value.toFin
def bv8OfByte (value : Byte) : BitVec 8 := BitVec.ofFin value

@[simp] theorem bv8OfByte_byteOfBV8 (value : BitVec 8) :
    bv8OfByte (byteOfBV8 value) = value := by
  apply BitVec.eq_of_toNat_eq
  rfl

def encode8 (value : BitVec 8) : List Byte := [byteOfBV8 value]

def decode8 : List Byte -> Option (BitVec 8)
  | [value] => some (bv8OfByte value)
  | _ => none

def u8 : Codec (BitVec 8) where
  size := 1
  align := 1
  size_pos := by decide
  align_pos := by decide
  encode := encode8
  decode := decode8
  encode_length := by intro; rfl
  decode_encode := by intro; simp [encode8, decode8]

def low8 {width : Nat} (value : BitVec width) : BitVec 8 :=
  value.setWidth 8

def byteAt {width : Nat} (value : BitVec width) (shift : Nat) : Byte :=
  byteOfBV8 ((value >>> shift).setWidth 8)

def encode16 (value : BitVec 16) : List Byte :=
  [byteAt value 0, byteAt value 8]

def decode16 : List Byte -> Option (BitVec 16)
  | [b0, b1] => some ((bv8OfByte b0).setWidth 16 |||
      ((bv8OfByte b1).setWidth 16 <<< 8))
  | _ => none

theorem decode16_encode16 (value : BitVec 16) :
    decode16 (encode16 value) = some value := by
  simp only [decode16, encode16, byteAt, bv8OfByte_byteOfBV8]
  congr 1
  bv_decide

def u16 : Codec (BitVec 16) where
  size := 2
  align := 2
  size_pos := by decide
  align_pos := by decide
  encode := encode16
  decode := decode16
  encode_length := by intro; rfl
  decode_encode := decode16_encode16

def placeByte (width shift : Nat) (value : Byte) : BitVec width :=
  (bv8OfByte value).setWidth width <<< shift

def encode32 (value : BitVec 32) : List Byte :=
  [byteAt value 0, byteAt value 8, byteAt value 16, byteAt value 24]

def decode32 : List Byte -> Option (BitVec 32)
  | [b0, b1, b2, b3] => some (placeByte 32 0 b0 |||
      placeByte 32 8 b1 ||| placeByte 32 16 b2 ||| placeByte 32 24 b3)
  | _ => none

theorem decode32_encode32 (value : BitVec 32) :
    decode32 (encode32 value) = some value := by
  simp only [decode32, encode32, byteAt, placeByte, bv8OfByte_byteOfBV8]
  congr 1
  bv_decide

def u32 : Codec (BitVec 32) where
  size := 4
  align := 4
  size_pos := by decide
  align_pos := by decide
  encode := encode32
  decode := decode32
  encode_length := by intro; rfl
  decode_encode := decode32_encode32

def encode64 (value : BitVec 64) : List Byte :=
  [byteAt value 0, byteAt value 8, byteAt value 16, byteAt value 24,
   byteAt value 32, byteAt value 40, byteAt value 48, byteAt value 56]

def decode64 : List Byte -> Option (BitVec 64)
  | [b0, b1, b2, b3, b4, b5, b6, b7] => some
      (placeByte 64 0 b0 ||| placeByte 64 8 b1 |||
       placeByte 64 16 b2 ||| placeByte 64 24 b3 |||
       placeByte 64 32 b4 ||| placeByte 64 40 b5 |||
       placeByte 64 48 b6 ||| placeByte 64 56 b7)
  | _ => none

theorem decode64_encode64 (value : BitVec 64) :
    decode64 (encode64 value) = some value := by
  simp only [decode64, encode64, byteAt, placeByte, bv8OfByte_byteOfBV8]
  congr 1
  bv_decide

def u64 : Codec (BitVec 64) where
  size := 8
  align := 8
  size_pos := by decide
  align_pos := by decide
  encode := encode64
  decode := decode64
  encode_length := by intro; rfl
  decode_encode := decode64_encode64

def encode128 (value : BitVec 128) : List Byte :=
  [byteAt value 0, byteAt value 8, byteAt value 16, byteAt value 24,
   byteAt value 32, byteAt value 40, byteAt value 48, byteAt value 56,
   byteAt value 64, byteAt value 72, byteAt value 80, byteAt value 88,
   byteAt value 96, byteAt value 104, byteAt value 112, byteAt value 120]

def decode128 : List Byte -> Option (BitVec 128)
  | [b0, b1, b2, b3, b4, b5, b6, b7,
      b8, b9, b10, b11, b12, b13, b14, b15] => some
      (placeByte 128 0 b0 ||| placeByte 128 8 b1 |||
       placeByte 128 16 b2 ||| placeByte 128 24 b3 |||
       placeByte 128 32 b4 ||| placeByte 128 40 b5 |||
       placeByte 128 48 b6 ||| placeByte 128 56 b7 |||
       placeByte 128 64 b8 ||| placeByte 128 72 b9 |||
       placeByte 128 80 b10 ||| placeByte 128 88 b11 |||
       placeByte 128 96 b12 ||| placeByte 128 104 b13 |||
       placeByte 128 112 b14 ||| placeByte 128 120 b15)
  | _ => none

theorem decode128_encode128 (value : BitVec 128) :
    decode128 (encode128 value) = some value := by
  simp only [decode128, encode128, byteAt, placeByte, bv8OfByte_byteOfBV8]
  congr 1
  bv_decide

def u128 : Codec (BitVec 128) where
  size := 16
  align := 16
  size_pos := by decide
  align_pos := by decide
  encode := encode128
  decode := decode128
  encode_length := by intro; rfl
  decode_encode := decode128_encode128

/-- Signed integers use the identical two's-complement representation. The
`BitVec.toInt` interpretation supplies signed arithmetic semantics. -/
def i8 : Codec (BitVec 8) := u8
def i16 : Codec (BitVec 16) := u16
def i32 : Codec (BitVec 32) := u32
def i64 : Codec (BitVec 64) := u64
def i128 : Codec (BitVec 128) := u128

/-- The initial native target is 64-bit, matching Rust's `usize`/`isize` on
x86-64 and AArch64. Target-width parameterization is a later codegen layer. -/
def usize : Codec (BitVec 64) := u64
def isize : Codec (BitVec 64) := i64

end Luffs.Memory.Scalar
