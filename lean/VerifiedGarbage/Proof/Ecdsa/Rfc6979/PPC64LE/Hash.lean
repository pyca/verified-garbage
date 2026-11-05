module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Kit
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Layout
public import VerifiedGarbage.Proof.HmacTable.PPC64LE
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Deterministic ECDSA on PPC64LE: the curve and the hash function

What the proof needs of the curve (`RfcCurve`): `vg_ecdsa_<curve>_sign_k`,
which each candidate calls, with its contract (`Core`), the words of its
scalars and their sizes: scalars of `Q` bytes, a multiple of 4 and at most
64, whose order `n` has exactly `8 Q` bits and `2^(8 Q) < 2 n` (so that
`bits2octets` is one conditional subtraction), or, if `big`, P-521's (9
words, 66 bytes, 521 bits: longer than any digest); and the bits `sh` the
signature drops from its digest.

What it needs of the hash function, for any one of them (`RfcHash`): the
curve, the instance of the contract it implements (the curve's, the hash
function's HMAC, its output length, the bound on candidates), the hash
function's functions (`HVar`: HMAC's `init` and `finalize` and the
streaming `update`, which the table holds), the functions an indirect call
of a table's functions may reach (`f`, of which the table's are, `TabOK`, a
fact of the state), and the sizes the frame and `scratch` hold: the output
and block sizes of one of the hash functions of `shapes` (MD5's, SHA-1's or
the SHA-2 family's), and states and working space no larger than SHA-512's.

The code is the same for every hash function (`cfgOf`): the proof is
written for each one, with the table's digest length `D` and block size `B`
the values the frame holds.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (Fns)
open VG.Proof.HmacTable.PPC64LE (HVar)

/-- The digest lengths and block sizes of the hash functions with HMAC on
PPC64LE: MD5, SHA-1, SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and
SHA-512/256. -/
def shapes : List (Nat × Nat) := [(16, 64), (20, 64), (28, 64), (32, 64), (48, 128), (64, 128), (28, 128), (32, 128)]

/-- A curve, for RFC 6979 on PPC64LE. -/
structure RfcCurve where
  /-- `vg_ecdsa_<curve>_sign_k`, with its contract. -/
  C : Core
  /-- The 64-bit words of the scalars. -/
  w : Nat
  /-- Whether the scalars are longer than any hash function's output and `n`
  has fewer bits than they do (P-521's), so that `h` is the digest's integer
  and `core` takes it shifted (`Impl.Ecdsa.Rfc6979.PPC64LE.Cfg.big`). -/
  big : Bool
  sizes : if big then w = 9 ∧ C.E.curve.len = 66 ∧ Spec.Ecdsa.nBits C.E.curve = 521
    else (C.E.curve.len = 24 ∨ C.E.curve.len = 28 ∨ C.E.curve.len = 32 ∨ C.E.curve.len = 48 ∨
        C.E.curve.len = 64) ∧ w = (C.E.curve.len + 7) / 8 ∧ Spec.Ecdsa.nBits C.E.curve = 8 * C.E.curve.len ∧
      2 ^ (8 * C.E.curve.len) < 2 * C.E.curve.n
  /-- The bits the signature drops from its digest, `8 len - nBits`. -/
  sh : Nat
  sh_eq : sh = 8 * C.E.curve.len - Spec.Ecdsa.nBits C.E.curve

namespace RfcCurve

variable (R : RfcCurve)

/-- The bytes of the scalars. -/
abbrev Q : Nat := R.C.E.curve.len

theorem sizesA (h : R.big = false) :
    (R.Q = 24 ∨ R.Q = 28 ∨ R.Q = 32 ∨ R.Q = 48 ∨ R.Q = 64) ∧ R.w = (R.Q + 7) / 8 ∧
      Spec.Ecdsa.nBits R.C.E.curve = 8 * R.Q ∧ 2 ^ (8 * R.Q) < 2 * R.C.E.curve.n := by
  have := R.sizes; rw [h] at this; simp only [Q]; exact this

theorem sizesW (h : R.big = true) : R.w = 9 ∧ R.Q = 66 ∧ Spec.Ecdsa.nBits R.C.E.curve = 521 := by
  have := R.sizes; rw [h] at this; simp only [Q]; exact this

/-- The scalars' bytes fill their words, the last possibly in part. -/
theorem len_words : 24 ≤ R.Q ∧ R.Q ≤ 66 ∧ 8 * R.w ≤ R.Q + 7 ∧ R.Q ≤ 8 * R.w ∧ R.w ≤ 9 := by
  cases h : R.big
  · have := R.sizesA h; simp only [Q] at *; omega
  · have := R.sizesW h; simp only [Q] at *; omega

/-- Unless `big`, the scalars are a multiple of 4 bytes, at most 64. -/
theorem len4 (h : R.big = false) : R.Q % 4 = 0 ∧ R.Q ≤ 64 := by
  have := (R.sizesA h).1; simp only [Q] at *; omega

/-- If `big`, `sh` is P-521's 7. -/
theorem sh7 (h : R.big = true) : R.sh = 7 := by
  have := R.sizesW h; simp only [Q] at this; rw [R.sh_eq]; omega

/-- Unless `big`, `sh` is 0. -/
theorem sh0 (h : R.big = false) : R.sh = 0 := by
  have := R.sizesA h; simp only [Q] at this; rw [R.sh_eq]; omega

theorem n_pos : 0 < R.C.E.curve.n := by
  cases h : R.big
  · have := (R.sizesA h).2.2.2; have := Nat.two_pow_pos (8 * R.Q); omega
  · have h₁ := (R.sizesW h).2.2
    by_contra h₀
    have : R.C.E.curve.n = 0 := by omega
    simp only [Spec.Ecdsa.nBits, this] at h₁
    exact absurd h₁ (by decide)

end RfcCurve

/-- A curve and a hash function, for RFC 6979 on PPC64LE. -/
structure RfcHash where
  /-- The curve. -/
  R : RfcCurve
  /-- The instance of the contract, with the hash function fixed. -/
  I : Spec.Ecdsa.Rfc6979.Instance
  /-- The hash function's functions. -/
  v : HVar
  /-- The functions an indirect call of a table's functions may reach. -/
  f : Fns
  /-- The instance is of the curve, with this hash function's HMAC and its
  output length, and tries at least one candidate, as many as `li` loads. -/
  ecdsa : I.ecdsa = R.C.E
  hash : I.hash = v.l.ok.SH.H
  len : I.hashLen = v.H.D
  tries_pos : 0 < I.tries
  tries_lt : I.tries < 2 ^ 15
  /-- The sizes the frame and `scratch` hold. -/
  hDB : (v.H.D, v.H.B) ∈ shapes
  hS : v.H.S ≤ 192
  hScr : sWork + v.I.scratch * 8 ≤ sMsg
  hW : sWork + v.H.W ≤ sMsg

namespace RfcHash

variable (P : RfcHash)

/-- What the proof of HMAC's steps needs of the hash function. -/
def K : Kit :=
  Kit.ofStream P.v.H P.v.l.ok P.v.I P.v.hIS P.v.initV P.v.finV P.v.l.ct.upd P.hScr P.hW P.hS

@[simp] theorem K_H : P.K.H = P.v.H := rfl
@[simp] theorem K_hH : P.K.hH = P.v.l.ok := rfl
@[simp] theorem K_initC : P.K.initC = P.v.H.init := rfl
@[simp] theorem K_finC : P.K.finC = P.v.H.finalize := rfl

/-- HMAC with the hash function. -/
abbrev mac (K text : List Byte) : List Byte := Spec.Hmac.hmac P.v.l.ok.SH.H K text

/-- The words of the curve's scalars. -/
abbrev w : Nat := P.R.w

/-- The bytes of the curve's scalars. -/
abbrev Q : Nat := P.R.Q

theorem shape (h : (P.v.H.D, P.v.H.B) ∈ shapes) :
    16 ≤ P.v.H.D ∧ P.v.H.D ≤ 64 ∧ P.v.H.D % 4 = 0 ∧ P.v.H.D < P.v.H.B ∧ P.v.H.B ≤ 128 ∧ 64 ≤ P.v.H.B := by
  simp only [shapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega

/-- The sizes, as the proofs use them. -/
theorem sizes : P.v.H.S ≤ 192 ∧ sWork + P.v.I.scratch * 8 ≤ sMsg ∧ sWork + P.v.H.W ≤ sMsg ∧
    16 ≤ P.v.H.D ∧ P.v.H.D ≤ 64 ∧ P.v.H.D % 4 = 0 ∧ P.v.H.D < P.v.H.B ∧ P.v.H.B ≤ 128 ∧ 64 ≤ P.v.H.B ∧
    24 ≤ P.Q ∧ P.Q ≤ 66 ∧ 8 * P.w ≤ P.Q + 7 ∧ P.Q ≤ 8 * P.w ∧ P.w ≤ 9 := by
  have hs := P.shape P.hDB
  have hw := P.R.len_words
  exact ⟨P.hS, P.hScr, P.hW, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2, hw.1, hw.2.1,
    hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2⟩

/-- If `big`, P-521's sizes, longer than any digest. -/
theorem sizesW (h : P.R.big = true) : P.w = 9 ∧ P.Q = 66 ∧ P.v.H.D < P.Q := by
  have h₁ := P.R.sizesW h
  have h₂ := P.sizes.2.2.2.2.1
  exact ⟨h₁.1, h₁.2.1, by simp only [Q]; omega⟩

/-- The curve's scalars are `Q` bytes. -/
theorem curveLen : P.I.ecdsa.curve.len = P.Q := by rw [P.ecdsa]

end RfcHash

/-- Facts about the sizes of the hash function `‹RfcHash›`'s states, working
space, block and output, and the scalars, and the arithmetic they decide. -/
macro "nums" : tactic => `(tactic| first | omega |
  (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := RfcHash.sizes ‹RfcHash›;
    simp only [sWork, sMsg] at *; omega))

/-- The code, for the curve of `P` and the functions an indirect call may reach. -/
def cfgOf (P : RfcHash) : Cfg where
  f := P.f
  w := P.R.w
  len := P.R.Q
  big := P.R.big
  sh := P.R.sh
  n := P.R.C.E.curve.n
  tries := P.I.tries
  coreN := P.R.C.N
  coreC := P.R.C.C

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
