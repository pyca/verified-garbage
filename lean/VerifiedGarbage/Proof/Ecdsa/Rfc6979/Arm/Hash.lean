import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Layout
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Common
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Upd
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve

/-!
# Deterministic ECDSA on 32-bit ARM: the hash function

What the proof needs of the hash function, for any one of them (`RfcHash`),
as on AArch64 (`Proof/Ecdsa/Rfc6979/AArch64/Hash.lean`): the curve
(`RfcCurve`, with what is proven of `vg_ecdsa_<curve>_sign`, which each
candidate calls), the instance of the contract it implements (the curve's,
the hash function's HMAC, its output length, 8 candidates), the functions
PBKDF2's code calls and what its proofs know of them (`FnsOK`: HMAC's `init`
and `finalize` and the streaming `update`, verified), and the sizes the
frame and `scratch` are laid out for: the output and block sizes of SHA-256,
SHA-384 or SHA-512, no shorter than the curve's scalars (so that one `V`
makes a candidate), or SHA-512's for a `wide` curve, and states and working
space no larger than SHA-512's.
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.Pbkdf2.Whole.Arm (FnsOK)

/-- A curve and a hash function, for RFC 6979 on 32-bit ARM. -/
structure RfcHash where
  /-- The curve. -/
  R : RfcCurve
  /-- The instance of the contract. -/
  I : Spec.Ecdsa.Rfc6979.Instance
  /-- The functions PBKDF2's code calls, of the hash function. -/
  F : Impl.Pbkdf2.Whole.Arm.Fns
  ok : FnsOK F
  /-- The instance is of the curve, with this hash function's HMAC, its
  output length and 8 candidates. -/
  ecdsa : I.ecdsa = R.inst
  hash : I.hash = ok.hH.SH.H
  len : I.hashLen = F.H.D
  /-- The hash function's digests have `F.H.D` bytes. -/
  macLen : ∀ x, (ok.hH.SH.H.hash x).length = F.H.D
  tries : I.tries = 8
  /-- The sizes the frame and `scratch` hold: the output and block sizes of
  SHA-256, SHA-384 or SHA-512. -/
  hDB : (F.H.D = 32 ∧ F.H.B = 64) ∨ (F.H.D = 48 ∧ F.H.B = 128) ∨ (F.H.D = 64 ∧ F.H.B = 128)
  hS : F.H.S ≤ 192
  hWi : ok.Wi * 8 ≤ 1872
  hWf : ok.Wf * 8 ≤ 1872
  hWb : ok.hH.Wb ≤ 1872
  /-- The hash is no shorter than the scalars, or, for a `wide` curve, SHA-512's. -/
  hQ : if R.wide then F.H.D = 64 ∧ F.H.B = 128 else 8 * R.E.n ≤ F.H.D

namespace RfcHash

variable (P : RfcHash)

/-- HMAC with the hash function. -/
abbrev mac (K text : List Byte) : List Byte := Spec.Hmac.hmac P.ok.hH.SH.H K text

/-- The 64-bit words of the curve's scalars. -/
abbrev w : Nat := P.R.E.n

/-- Their 32-bit words, as the code handles them. -/
abbrev k : Nat := 2 * P.R.E.n

/-- The bytes of the curve's scalars. -/
abbrev Q : Nat := P.R.E.C.len

/-- The 32-bit words at the frame's top: the digest for `core` and the
candidate, if two `V`s make a candidate. -/
abbrev e : Nat := Impl.Ecdsa.Rfc6979.Arm.extra P.R.wide

/-- The sizes, as the proofs use them. -/
theorem sizes : P.F.H.S ≤ 192 ∧ P.ok.Wi * 8 ≤ 1872 ∧ P.ok.Wf * 8 ≤ 1872 ∧ P.ok.hH.Wb ≤ 1872 ∧
    32 ≤ P.F.H.D ∧ P.F.H.D ≤ 64 ∧ P.F.H.D % 8 = 0 ∧ P.F.H.D < P.F.H.B ∧ P.F.H.B ≤ 128 ∧
    P.ok.hH.SH.stateBytes = P.F.H.S ∧ P.ok.hH.SH.digestBytes = P.F.H.D ∧
    P.ok.hH.SH.H.blockSize = P.F.H.B := by
  refine ⟨P.hS, P.hWi, P.hWf, P.hWb, ?_, ?_, ?_, ?_, ?_, P.ok.hH.hS, P.ok.hH.hD, P.ok.hH.hB⟩ <;>
    rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp only [h, h'] <;> omega

/-- The sizes of the scalars, as the proofs use them. -/
theorem wsizes : 3 ≤ P.w ∧ P.w ≤ 9 ∧ P.k = 2 * P.w ∧ 8 ≤ P.Q ∧ P.Q ≤ P.F.H.D + 4 ∧ P.Q ≤ 8 * P.w ∧
    8 * P.w < P.Q + 8 ∧ P.e ≤ 36 := by
  have hw : 8 ≤ P.Q ∧ 8 * P.w < P.Q + 8 ∧ P.Q ≤ 8 * P.w := P.R.len_words
  have hQD : P.Q ≤ P.F.H.D + 4 := by
    have hQ := P.hQ
    cases hW : P.R.wide
    · have := P.R.sizesA hW; rw [hW] at hQ; simp only [Bool.false_eq_true, ite_false] at hQ
      show P.R.E.C.len ≤ _; omega
    · have := P.R.sizesW hW; rw [hW] at hQ; simp only [ite_true] at hQ
      show P.R.E.C.len ≤ _; omega
  exact ⟨P.R.n3, P.R.n9, rfl, hw.1, hQD, hw.2.2, hw.2.1, by
    simp only [e, Impl.Ecdsa.Rfc6979.Arm.extra]; split <;> omega⟩

/-- Unless `wide`, the scalars are `8 w` bytes, at most 6 words, and no longer than the digest. -/
theorem sizesA (h : P.R.wide = false) : P.Q = 8 * P.w ∧ P.w ≤ 6 ∧ P.Q ≤ P.F.H.D := by
  have hQ := P.hQ
  have := P.R.sizesA h
  rw [h] at hQ
  simp only [Bool.false_eq_true, ite_false] at hQ
  rcases this.1 with h' | h' | h' <;> simp only [Q, w] <;> omega

/-- If `wide`, P-521's sizes and SHA-512's. -/
theorem sizesW (h : P.R.wide = true) : P.w = 9 ∧ P.Q = 66 ∧ P.F.H.D = 64 ∧ P.F.H.B = 128 := by
  have hQ := P.hQ
  have := P.R.sizesW h
  rw [h] at hQ
  simp only [ite_true] at hQ
  exact ⟨this.1, this.2.1, hQ⟩

theorem mac_length (K t : List Byte) : (P.mac K t).length = P.F.H.D := by
  simp only [mac, Spec.Hmac.hmac, Spec.Hmac.hmacBlockKey, P.macLen]

/-- The digest is at least 32 bytes. -/
theorem len32 : 32 ≤ P.I.hashLen := by
  rw [P.len]; rcases P.hDB with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega

/-- The curve's scalars are `Q` bytes. -/
theorem curveLen : P.I.ecdsa.curve.len = P.Q := by rw [P.ecdsa, P.R.curve]

end RfcHash

/-- Facts about the sizes of the hash function `‹RfcHash›`'s states, working
space, block and output, and the arithmetic they decide. -/
macro "anums" : tactic => `(tactic| first | omega |
  (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := RfcHash.sizes ‹RfcHash›
   obtain ⟨_, _, _, _, _, _, _, _⟩ := RfcHash.wsizes ‹RfcHash›; omega))

/-- The code, with the hash function `P`. -/
def cfgOf (P : RfcHash) : Cfg where
  F := P.F
  w := 2 * P.R.E.n
  len := P.R.E.C.len
  wide := P.R.wide
  sh := P.R.sh
  n := P.R.E.C.n
  tries := 8
  coreN := P.R.coreN
  coreC := P.R.coreC

end VG.Proof.Ecdsa.Rfc6979.Arm
