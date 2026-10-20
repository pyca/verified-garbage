module

public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Common
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Sha256.X86.Lit

/-!
# Deterministic ECDSA on x86 (32-bit): the hash function

What the proof needs of the hash function, for any one of them (`RfcHash`),
as on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Hash.lean`): the curve
(`RfcCurve`, with what is proven of `vg_ecdsa_<curve>_sign`, which each
candidate calls), the instance of the contract it implements (the curve's,
the hash function's HMAC, its output length, its number of candidates), the functions
PBKDF2's code calls, verified (`FnsOK`: the streaming `update`, and HMAC's
`init` and `finalize`, which take their working space as an argument), and
the sizes the frame and `scratch` are laid out for: the output and block
sizes of SHA-224, SHA-256, SHA-384 or SHA-512, no shorter than the curve's scalars
(so that one `V` makes a candidate), and states and working space no larger
than SHA-512's. Each hash function's file builds one for each implementation
of its compression function.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Proof.Pbkdf2.Whole.X86 (FnsOK ReprOK)

/-- A curve and a hash function, for RFC 6979 on x86. -/
structure RfcHash where
  /-- The curve. -/
  R : RfcCurve
  /-- The instance of the contract. -/
  I : Spec.Ecdsa.Rfc6979.Instance
  /-- The functions the code calls, verified. -/
  F : Fns
  ok : FnsOK F
  /-- The instance is of the curve, with this hash function's HMAC and its
  output length. -/
  ecdsa : I.ecdsa = R.inst
  hash : I.hash = ok.hH.SH.H
  len : I.hashLen = F.H.D
  /-- The hash function's digests have `F.H.D` bytes. -/
  macLen : ∀ x, (ok.hH.SH.H.hash x).length = F.H.D
  /-- It tries at least one candidate, as many as a 32-bit immediate holds. -/
  tries_pos : 0 < I.tries
  tries_lt : I.tries < 2 ^ 32
  /-- The sizes the frame and `scratch` hold: the output and block sizes of
  SHA-224, SHA-256, SHA-384 or SHA-512, and states and working space no larger than
  SHA-512's. -/
  hDB : (F.H.D = 32 ∧ F.H.B = 64) ∨ (F.H.D = 48 ∧ F.H.B = 128) ∨ (F.H.D = 64 ∧ F.H.B = 128) ∨ (F.H.D = 28 ∧ F.H.B = 64)
  hS : F.H.S ≤ 192
  hWi : ok.Wi * 8 ≤ 1872
  hWf : ok.Wf * 8 ≤ 1872
  /-- The hash is no shorter than the scalars, or, for a `wide` curve, SHA-512's. -/
  hQ : if R.wide then F.H.D = 64 ∧ F.H.B = 128 else R.E.C.len ≤ F.H.D

namespace RfcHash

variable (P : RfcHash)

/-- HMAC with the hash function. -/
abbrev mac (K text : List Byte) : List Byte := Spec.Hmac.hmac P.ok.hH.SH.H K text

theorem reprOK : ReprOK P.ok.hH.SH := fun m m' p q msg hb =>
  P.ok.hH.repr m m' p q msg (fun i hi => hb i (by rw [P.ok.hH.hS]; exact hi))

/-- The 64-bit words of the curve's scalars. -/
abbrev w : Nat := P.R.E.n

/-- Their 32-bit words: seven for P-224, otherwise two per 64-bit word.
P-521 retains the padding its wide conversions use. -/
abbrev k : Nat := 2 * P.R.E.n - (if P.R.E.C.len = 28 then 1 else 0)

/-- The bytes of the curve's scalars. -/
abbrev Q : Nat := P.R.E.C.len

/-- The 32-bit words at the frame's top: the digest for `core` and the
candidate, if two `V`s make a candidate, or `h`, for 64-byte scalars. -/
abbrev e : Nat := Impl.Ecdsa.Rfc6979.X86.extra P.R.wide P.R.hHigh

/-- Where `h` is, from the stack's lowest byte: in the frame below the
count, or at its top for 64-byte scalars. -/
abbrev hB : Nat := if P.R.hHigh then 272 else 204

/-- The sizes, as the proofs use them. -/
theorem sizes : P.F.H.S ≤ 192 ∧ P.ok.Wi * 8 ≤ 1872 ∧ P.ok.Wf * 8 ≤ 1872 ∧ P.ok.hH.Wb ≤ 1872 ∧
    28 ≤ P.F.H.D ∧ P.F.H.D ≤ 64 ∧ P.F.H.D % 4 = 0 ∧ P.F.H.D < P.F.H.B ∧ P.F.H.B ≤ 128 ∧ 0 < P.F.H.S ∧
    3 ≤ P.w ∧ P.w ≤ 9 ∧ 6 ≤ P.k ∧ P.k ≤ 2 * P.w ∧ 8 ≤ P.Q ∧ P.Q ≤ P.F.H.D + 4 ∧ P.Q ≤ 8 * P.w ∧
    8 * P.w < P.Q + 8 ∧ P.e ≤ 36 := by
  have hWb := P.ok.hH.hWb
  have hW := P.ok.hH.hW
  have hS0 := P.ok.hH.hS0
  have hw : 8 ≤ P.Q ∧ 8 * P.w < P.Q + 8 ∧ P.Q ≤ 8 * P.w := P.R.len_words
  have hQD : P.Q ≤ P.F.H.D + 4 := by
    have hQ := P.hQ
    cases hW : P.R.wide
    · have := P.R.sizesA hW; rw [hW] at hQ; simp only [Bool.false_eq_true, ite_false] at hQ
      show P.R.E.C.len ≤ _; omega
    · have := P.R.sizesW hW; rw [hW] at hQ; simp only [ite_true] at hQ
      show P.R.E.C.len ≤ _; omega
  refine ⟨P.hS, P.hWi, P.hWf, by omega, ?_, ?_, ?_, ?_, ?_, hS0, P.R.n3, P.R.n9, (by have := P.R.len_words; have := P.R.n3; simp only [k]; split <;> omega), (by simp only [k, w]; omega), hw.1, hQD, hw.2.2,
    hw.2.1, by simp only [e, Impl.Ecdsa.Rfc6979.X86.extra]; split <;> (try split) <;> omega⟩ <;>
    rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp only [h, h'] <;> omega

/-- Unless `wide`, the scalars fill at most sixteen 32-bit words and are no
longer than the digest. -/
theorem sizesA (h : P.R.wide = false) : P.Q = 4 * P.k ∧ P.k ≤ 16 ∧ P.Q ≤ P.F.H.D := by
  have hQ := P.hQ
  have := P.R.sizesA h
  rw [h] at hQ
  simp only [Bool.false_eq_true, ite_false] at hQ
  rcases this.1 with h' | h' | h' | h' <;> simp only [Q, k] <;> split <;> omega

/-- The possible byte lengths of a single-candidate scalar. -/
theorem lengthsA (h : P.R.wide = false) : P.Q = 24 ∨ P.Q = 32 ∨ P.Q = 48 ∨ P.Q = 64 ∨ P.Q = 28 := by
  have := P.R.sizesA h
  simp only [Q]
  omega

/-- `h` fits its place: 48 bytes below the count, or, for 64-byte scalars
(in 8 64-bit words), the 64 at the frame's top. -/
theorem hFits (h : P.R.wide = false) : (P.w = 8 → P.Q = 64) ∧ (P.w ≠ 8 → P.Q ≤ 48) := by
  have := P.R.sizesA h
  simp only [Q, w]
  omega

/-- If `wide`, P-521's sizes and SHA-512's. -/
theorem sizesW (h : P.R.wide = true) : P.w = 9 ∧ P.Q = 66 ∧ P.F.H.D = 64 ∧ P.F.H.B = 128 := by
  have hQ := P.hQ
  have := P.R.sizesW h
  rw [h] at hQ
  simp only [ite_true] at hQ
  exact ⟨this.1, this.2.1, hQ⟩

/-- The digest is at least 28 bytes. -/
theorem len28 : 28 ≤ P.I.hashLen := by
  rw [P.len]; rcases P.hDB with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega

/-- The curve's scalars are `Q` bytes. -/
theorem curveLen : P.I.ecdsa.curve.len = P.Q := by rw [P.ecdsa, P.R.curve]

end RfcHash

/-- Facts about the sizes of the hash function `‹RfcHash›`'s states, working
space, block and output, and the arithmetic they decide. -/
tactic_template "nums" : tactic => `(tactic| first | omega |
  (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := RfcHash.sizes ‹RfcHash›; omega))

/-- The code, with the hash function `P`. -/
def cfgOf (P : RfcHash) : Cfg where
  F := P.F
  w := 2 * P.R.E.n - (if P.R.E.C.len = 28 then 1 else 0)
  len := P.R.E.C.len
  wide := P.R.wide
  sh := P.R.sh
  hHigh := P.R.hHigh
  n := P.R.E.C.n
  tries := P.I.tries
  coreN := P.R.coreN
  coreC := P.R.coreC

/-- Unless two `V`s make a candidate, `h` is at the frame's top just for
64-byte scalars. -/
theorem hHigh_q (P : RfcHash) (hw : P.R.wide = false) : P.R.hHigh = decide (P.Q = 64) := by
  have hF := P.hFits hw
  rw [P.R.hHigh_eq]
  by_cases h8 : P.R.E.n = 8
  · simp only [h8, decide_true, show P.Q = 64 from hF.1 h8]
  · have := hF.2 h8
    simp only [h8, decide_false, show P.Q ≠ 64 by omega]

/-- `h`'s place in the frame: `hB` less the 76 bytes below the frame. -/
theorem fHo_eq (P : RfcHash) : (cfgOf P).fHo = P.hB - 76 := by
  cases h : P.R.hHigh <;> simp [Cfg.fHo, cfgOf, RfcHash.hB, h, fX, fH]

/-- If two `V`s make a candidate, `h` is not at the frame's top. -/
theorem hHigh_wide (P : RfcHash) (hw : P.R.wide = true) : P.R.hHigh = false := by
  have hh := P.R.hHigh_eq
  simp only [show P.R.E.n = 9 from (P.R.sizesW hw).1, Nat.reduceEqDiff, decide_false] at hh
  exact hh

/-- If two `V`s make a candidate, `h`'s place is the one below the count,
which the code does not use. -/
theorem fHo_wide (P : RfcHash) (hw : P.R.wide = true) : (cfgOf P).fHo = 128 := by
  simp only [Cfg.fHo, cfgOf, hHigh_wide P hw, Bool.false_eq_true, ite_false, fH]

/-- `h`'s place in the frame, unless two `V`s make a candidate: at its top
for 64-byte scalars. -/
theorem fHo_q (P : RfcHash) (hw : P.R.wide = false) : (cfgOf P).fHo = if P.Q = 64 then 196 else 128 := by
  have hh := P.R.hHigh_eq
  have hF := P.hFits hw
  rw [fHo_eq]
  by_cases h8 : P.R.E.n = 8
  · have hq := hF.1 h8
    simp only [h8, decide_true] at hh
    simp only [RfcHash.hB, hh, ite_true, show P.Q = 64 from hq]
  · have hq := hF.2 h8
    simp only [h8, decide_false] at hh
    simp only [RfcHash.hB, hh, Bool.false_eq_true, ite_false, show P.Q ≠ 64 by omega]

end VG.Proof.Ecdsa.Rfc6979.X86
