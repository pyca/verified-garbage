module

public import VerifiedGarbage.Impl.Gcm.Clmul
public import VerifiedGarbage.Spec.Gcm

/-! # The bitvector operations used by GHASH multiplication with holes -/

@[expose] public section
namespace VG.Proof.Gcm.Holes

/-- The bits congruent to `i` modulo 4. -/
def K (i : Nat) : BitVec 64 := 0x1111111111111111#64 <<< i

/-- The words `zₜ` of the code: the products of the parts of `a` and `b` whose
classes add up to `t`, `b`'s parts in order. -/
def zc (a : BitVec 64) (bs : Nat → BitVec 64) (t : Nat) : BitVec 64 :=
  (a &&& K t) * bs 0 ^^^ (a &&& K ((t + 3) % 4)) * bs 1 ^^^ (a &&& K ((t + 2) % 4)) * bs 2 ^^^
    (a &&& K ((t + 1) % 4)) * bs 3

/-- The class `t` of each `zₜ`, together. -/
def holes (a : BitVec 64) (bs : Nat → BitVec 64) : BitVec 64 :=
  (zc a bs 0 &&& K 0) ||| (zc a bs 1 &&& K 1) ||| (zc a bs 2 &&& K 2) ||| (zc a bs 3 &&& K 3)

/-- The low half of a word. -/
def lo32 (x : BitVec 64) : BitVec 64 := (x <<< 32) >>> 32

/-- The high half of a word. -/
def hi32 (x : BitVec 64) : BitVec 64 := x >>> 32

/-- The 64-bit carry-less product, by three 32-bit ones: the low halves' product, -/
def pmL (x y : BitVec 64) : BitVec 64 := holes (lo32 x) fun j => lo32 y &&& K j

/-- the high halves', -/
def pmH (x y : BitVec 64) : BitVec 64 := holes (hi32 x) fun j => hi32 y &&& K j

/-- the middle term, -/
def pmM (x y : BitVec 64) : BitVec 64 :=
  (holes (lo32 x ^^^ hi32 x) fun j => (lo32 y ^^^ hi32 y) &&& K j) ^^^ pmL x y ^^^ pmH x y

/-- and its low and high words. -/
def pm (x y : BitVec 64) : BitVec 64 × BitVec 64 :=
  (pmL x y ^^^ pmM x y <<< 32, pmH x y ^^^ pmM x y >>> 32)

/-- What a fold adds to the lower word, -/
def foldLo (lo w : BitVec 64) : BitVec 64 := (((lo ^^^ w) ^^^ (w >>> 1)) ^^^ (w >>> 2)) ^^^ (w >>> 7)

/-- and to the higher. -/
def foldHi (hi w : BitVec 64) : BitVec 64 := ((hi ^^^ (w <<< 63)) ^^^ (w <<< 62)) ^^^ (w <<< 57)

/-- The reduction: `W₃` into `W₁, W₂`, then `W₂` into `W₀, W₁`. -/
def reduce (w0 w1 w2 w3 : BitVec 64) : BitVec 128 :=
  foldLo w0 (foldHi w2 w3) ++ foldHi (foldLo w1 w3) (foldHi w2 w3)

/-- The key's first word, `H · x⁻¹`: `H` shifted up a bit, `x⁻¹ = 1 + x + x⁶ + x¹²⁷` added if
its constant term was set. -/
def key0 (h0 h1 : BitVec 64) : BitVec 64 :=
  ((h0 <<< 1) ^^^ (h1 >>> 63)) ^^^ ((0#64 - (h0 >>> 63)) &&& VG.Impl.Gcm.Clmul.poly)

/-- … and its second. -/
def key1 (h0 h1 : BitVec 64) : BitVec 64 := (h1 <<< 1) ^^^ ((0#64 - (h0 >>> 63)) &&& 1#64)

/-- One block's product by the key `k` (`key0`, `key1`), as the code computes it. -/
def mulK (y0 y1 k0 k1 : BitVec 64) : BitVec 128 :=
  let l := pm y0 k0
  let h := pm y1 k1
  let m := pm (y0 ^^^ y1) (k0 ^^^ k1)
  reduce l.2 (l.1 ^^^ (m.2 ^^^ l.2 ^^^ h.2)) ((m.1 ^^^ l.1 ^^^ h.1) ^^^ h.2) h.1

/-- The product of these words is SP 800-38D multiplication for the original key.
The polynomial proof in `Holes` supplies this law at registration. -/
abbrev MulLaw : Prop :=
  ∀ y0 y1 h0 h1, mulK y0 y1 (key0 h0 h1) (key1 h0 h1) = Spec.Gcm.mul (y0 ++ y1) (h0 ++ h1)

end VG.Proof.Gcm.Holes
