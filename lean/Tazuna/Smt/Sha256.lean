import Tazuna.Linter

/-! SHA-256 (FIPS 180-4), for the answer cache's keys: a key names a script's whole text, so two scripts share an
answer only if their texts hash alike, which for SHA-256 no one has ever found. -/

namespace Tazuna.Smt.Sha256

def k : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def init : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

@[inline] def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- The 64 rounds from round `i` on, over the schedule `w`. The working variables are arguments rather than mutable
locals, so the compiled loop keeps them unboxed instead of allocating a tuple of them per round. -/
def rounds (w : Array UInt32) (i : Nat) (a b c d e f g h : UInt32) : Array UInt32 :=
  if i < 64 then
    let t1 := h + (rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25) + ((e &&& f) ^^^ (~~~e &&& g)) + k[i]! + w[i]!
    let t2 := (rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22) + ((a &&& b) ^^^ (a &&& c) ^^^ (b &&& c))
    rounds w (i + 1) (t1 + t2) a b c (d + t1) e f g
  else #[a, b, c, d, e, f, g, h]
termination_by 64 - i

/-- The state after the 64-byte block of `b` at `off`. -/
def compress (h : Array UInt32) (b : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for i in [0:16] do
    let j := off + 4 * i
    w := w.push ((b.get! j).toUInt32 <<< 24 ||| (b.get! (j + 1)).toUInt32 <<< 16 |||
      (b.get! (j + 2)).toUInt32 <<< 8 ||| (b.get! (j + 3)).toUInt32)
  for i in [16:64] do
    let w15 := w[i - 15]!
    let w2 := w[i - 2]!
    let s0 := rotr w15 7 ^^^ rotr w15 18 ^^^ (w15 >>> 3)
    let s1 := rotr w2 17 ^^^ rotr w2 19 ^^^ (w2 >>> 10)
    w := w.push (w[i - 16]! + s0 + w[i - 7]! + s1)
  let r := rounds w 0 h[0]! h[1]! h[2]! h[3]! h[4]! h[5]! h[6]! h[7]!
  return #[h[0]! + r[0]!, h[1]! + r[1]!, h[2]! + r[2]!, h[3]! + r[3]!, h[4]! + r[4]!, h[5]! + r[5]!, h[6]! + r[6]!,
    h[7]! + r[7]!]

/-- The message's last bytes from `off` on, then the padding: a one bit, zeros, and the length in bits. -/
def tail (b : ByteArray) (off : Nat) : ByteArray := Id.run do
  let mut t := b.extract off b.size
  t := t.push 0x80
  while t.size % 64 != 56 do
    t := t.push 0
  let bits := b.size * 8
  for i in [0:8] do
    t := t.push (UInt8.ofNat (bits >>> (8 * (7 - i))))
  return t

def hexDigit (n : UInt32) : Char := Char.ofNat (if n < 10 then 48 + n.toNat else 87 + n.toNat)

/-- The digest of the bytes, as 64 lowercase hex digits. -/
def hex (b : ByteArray) : String := Id.run do
  let full := b.size / 64
  let mut h := init
  for i in [0:full] do
    h := compress h b (64 * i)
  let t := tail b (64 * full)
  for i in [0:t.size / 64] do
    h := compress h t (64 * i)
  let mut s := ""
  for x in h do
    for i in [0:8] do
      s := s.push (hexDigit ((x >>> (4 * (7 - i).toUInt32)) &&& 0xf))
  return s

-- The FIPS 180-4 examples; the 56-byte one makes the padding take a block of its own.
#guard hex "".toUTF8 == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard hex "abc".toUTF8 == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard hex "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8 ==
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"

end Tazuna.Smt.Sha256
