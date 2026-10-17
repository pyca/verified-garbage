module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Layout
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Common
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Upd
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.X25519.Arm.Limbs

/-!
# Deterministic ECDSA on 32-bit ARM: the hash function

What the proof needs of the hash function a run uses, one of the code's
(`RfcHash`), as on AArch64 (`Proof/Ecdsa/Rfc6979/AArch64/Hash.lean`): the
curve (`RfcCurve`, with what is proven of `vg_ecdsa_<curve>_sign`, which each
candidate calls), the hash functions the code dispatches on (`hs`, whose
codes `Impl.Ecdsa.Rfc6979.Arm.code` differ) and the one of them the run's
`hash` names (`k`, with `HashId`'s hash function and output length), the
functions PBKDF2's code calls and what its proofs know of them (`FnsOK`:
HMAC's `init` and `finalize` and the streaming `update`, verified), and the
sizes the frame and `scratch` are laid out for: the output and block sizes
of SHA-1 or a SHA-2 function, and states and working space no larger than
SHA-512's.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.Pbkdf2.Whole.Arm (FnsOK)

/-- A curve and one of the code's hash functions, for RFC 6979 on 32-bit ARM. -/
structure RfcHash where
  /-- The curve. -/
  R : RfcCurve
  /-- The hash functions the code dispatches on, by their codes. -/
  hs : List Impl.Pbkdf2.Whole.Arm.Fns
  nodup : (hs.map code).Nodup
  codes : ∀ F ∈ hs, code F < 256
  /-- The run's: the number `hash` names it by, and the functions PBKDF2's code calls. -/
  k : Nat
  F : Impl.Pbkdf2.Whole.Arm.Fns
  mem : F ∈ hs
  ok : FnsOK F
  /-- It is the hash function `k` names, whose output has `F.H.D` bytes, and
  `k ≥ 4` iff its block has 128 bytes (which the prologue computes the
  code from). -/
  hash : Spec.HashId.hmac k = some ok.hH.SH.H
  len : ∃ H, Spec.HashId.mgf1 k = some H ∧ H.len = F.H.D
  blk : F.H.B / 128 = (k + 4) / 8
  hk : k < 8
  /-- The hash function's digests have `F.H.D` bytes. -/
  macLen : ∀ x, (ok.hH.SH.H.hash x).length = F.H.D
  /-- The sizes the frame and `scratch` hold: the output and block sizes of
  SHA-1 or a SHA-2 function. -/
  hDB : (F.H.D = 20 ∧ F.H.B = 64) ∨ (F.H.D = 28 ∧ F.H.B = 64) ∨ (F.H.D = 32 ∧ F.H.B = 64) ∨
    (F.H.D = 48 ∧ F.H.B = 128) ∨ (F.H.D = 64 ∧ F.H.B = 128) ∨ (F.H.D = 28 ∧ F.H.B = 128) ∨
    (F.H.D = 32 ∧ F.H.B = 128)
  hS : F.H.S ≤ 192
  hWi : ok.Wi * 8 ≤ 1872
  hWf : ok.Wf * 8 ≤ 1872
  hWb : ok.hH.Wb ≤ 1872

namespace RfcHash

variable (P : RfcHash)

/-- HMAC with the hash function. -/
abbrev mac (K text : List Byte) : List Byte := Spec.Hmac.hmac P.ok.hH.SH.H K text

/-- The 64-bit words of the curve's scalars. -/
abbrev w : Nat := P.R.E.n

/-- Their 32-bit words: seven for P-224, otherwise two per 64-bit word. -/
abbrev k32 : Nat := 2 * P.R.E.n - (if P.R.E.C.len = 28 then 1 else 0)

/-- The bytes of the curve's scalars. -/
abbrev Q : Nat := P.R.E.C.len

/-- The hash function's code, in `r6`. -/
abbrev c : Nat := code P.F

/-- The sizes, as the proofs use them. -/
theorem sizes : P.F.H.S ≤ 192 ∧ P.ok.Wi * 8 ≤ 1872 ∧ P.ok.Wf * 8 ≤ 1872 ∧ P.ok.hH.Wb ≤ 1872 ∧
    20 ≤ P.F.H.D ∧ P.F.H.D ≤ 64 ∧ P.F.H.D % 4 = 0 ∧ P.F.H.D < P.F.H.B ∧ P.F.H.B ≤ 128 ∧
    P.ok.hH.SH.stateBytes = P.F.H.S ∧ P.ok.hH.SH.digestBytes = P.F.H.D ∧
    P.ok.hH.SH.H.blockSize = P.F.H.B := by
  refine ⟨P.hS, P.hWi, P.hWf, P.hWb, ?_, ?_, ?_, ?_, ?_, P.ok.hH.hS, P.ok.hH.hD, P.ok.hH.hB⟩ <;>
    rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;>
    simp only [h, h'] <;> omega

/-- The sizes of the scalars, as the proofs use them. -/
theorem wsizes : 3 ≤ P.w ∧ P.w ≤ 9 ∧ 6 ≤ P.k32 ∧ P.k32 ≤ 2 * P.w ∧ 24 ≤ P.Q ∧ P.Q ≤ 66 ∧ P.Q ≤ 8 * P.w ∧
    8 * P.w < P.Q + 8 := by
  have hw : 8 ≤ P.Q ∧ 8 * P.w < P.Q + 8 ∧ P.Q ≤ 8 * P.w := P.R.len_words
  have := P.R.sizes
  refine ⟨P.R.n3, P.R.n9, (by have := P.R.len_words; have := P.R.n3; simp only [k32]; split <;> omega),
    (by simp only [k32, w]; omega), ?_, ?_, hw.2.2, hw.2.1⟩ <;>
    (cases h : P.R.wide <;> simp only [h, Bool.false_eq_true, ite_false, ite_true] at this <;>
      simp only [Q] <;> omega)

/-- Unless `wide`, the scalars fill at most sixteen 32-bit words. -/
theorem sizesA (h : P.R.wide = false) : P.Q = 4 * P.k32 ∧ P.k32 ≤ 16 := by
  have := P.R.sizesA h
  rcases this.1 with h' | h' | h' | h' <;> simp only [Q, k32] <;> split <;> omega

/-- If `wide`, P-521's sizes. -/
theorem sizesW (h : P.R.wide = true) : P.w = 9 ∧ P.Q = 66 := by
  have := P.R.sizesW h
  exact ⟨this.1, this.2.1⟩

theorem mac_length (K t : List Byte) : (P.mac K t).length = P.F.H.D := by
  simp only [mac, Spec.Hmac.hmac, Spec.Hmac.hmacBlockKey, P.macLen]

/-- The curve's scalars are `Q` bytes. -/
theorem curveLen : P.R.I.ecdsa.curve.len = P.Q := by rw [P.R.ecdsa, P.R.curve]

end RfcHash

/-- Facts about the sizes of the hash function `‹RfcHash›`'s states, working
space, block and output, and the arithmetic they decide. -/
tactic_template "anums" : tactic => `(tactic| first | omega |
  (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := RfcHash.sizes ‹RfcHash›
   obtain ⟨_, _, _, _, _, _, _, _⟩ := RfcHash.wsizes ‹RfcHash›; omega))

/-- The code, for the curve `R` and the hash functions `hs`. -/
def cfgR (R : RfcCurve) (hs : List Impl.Pbkdf2.Whole.Arm.Fns) : Cfg where
  hs := hs
  w := 2 * R.E.n - (if R.E.C.len = 28 then 1 else 0)
  len := R.E.C.len
  sh := R.sh
  n := R.E.C.n
  tries := R.I.tries
  coreN := R.coreN
  coreC := R.coreC

/-- The code, with the hash function `P`'s curve and hash functions. -/
abbrev cfgOf (P : RfcHash) : Cfg := cfgR P.R P.hs

end VG.Proof.Ecdsa.Rfc6979.Arm
