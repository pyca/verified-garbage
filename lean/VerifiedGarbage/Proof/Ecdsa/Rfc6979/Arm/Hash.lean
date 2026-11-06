module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Common
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve

/-!
# Deterministic ECDSA on 32-bit ARM: the hash function

What the proof needs of the hash function, for any one of them (`RfcHash`),
as on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Hash.lean`): the curve
(`RfcCurve`, with what is proven of `vg_ecdsa_<curve>_sign_k`, which each
candidate calls), the instance of the contract it implements (the curve's,
the hash function's HMAC, its output length, the bound on candidates), the
functions PBKDF2's code calls and what its proofs know of them (`FnsOK`:
HMAC's `init` and `finalize` and the streaming `update`, which the table
holds), the functions an indirect call of a table's functions may reach
(`f`), and the sizes the frame and `scratch` hold: the output and block
sizes of one of the hash functions of `shapes` (MD5's, SHA-1's or the SHA-2
family's), and states and working space no larger than SHA-512's.

The code is the same for every hash function (`cfgOf`): the proof is
written for each one, with the table's digest length `D` and block size `B`
the values the table holds.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.Pbkdf2.Whole.Arm (FnsOK)

/-- The digest lengths and block sizes of the hash functions with HMAC on
ARMv7: MD5, SHA-1, SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and
SHA-512/256. -/
def shapes : List (Nat × Nat) := [(16, 64), (20, 64), (28, 64), (32, 64), (48, 128), (64, 128), (28, 128), (32, 128)]

/-- A curve and a hash function, for RFC 6979 on 32-bit ARM. -/
structure RfcHash where
  /-- The curve. -/
  R : RfcCurve
  /-- The instance of the contract, with the hash function fixed. -/
  I : Proof.Ecdsa.Rfc6979.Instance
  /-- The functions PBKDF2's code calls, of the hash function. -/
  F : Impl.Pbkdf2.Whole.Arm.Fns
  ok : FnsOK F
  /-- The functions an indirect call of a table's functions may reach. -/
  f : Fns
  /-- The instance is of the curve, with this hash function's HMAC and its
  output length. -/
  ecdsa : I.ecdsa = R.inst
  hash : I.hash = ok.hH.SH.H
  len : I.hashLen = F.H.D
  /-- The hash function's digests have `F.H.D` bytes. -/
  macLen : ∀ x, (ok.hH.SH.H.hash x).length = F.H.D
  /-- It tries at least one candidate, as many as a 16-bit immediate holds. -/
  tries_pos : 0 < I.tries
  tries_lt : I.tries < 2 ^ 16
  /-- The sizes the frame and `scratch` hold. -/
  hDB : (F.H.D, F.H.B) ∈ shapes
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
abbrev k : Nat := 2 * P.R.E.n - (if P.R.E.C.len = 28 then 1 else 0)

/-- The bytes of the curve's scalars. -/
abbrev Q : Nat := P.R.E.C.len

theorem shape (h : (P.F.H.D, P.F.H.B) ∈ shapes) :
    16 ≤ P.F.H.D ∧ P.F.H.D ≤ 64 ∧ P.F.H.D % 4 = 0 ∧ P.F.H.D < P.F.H.B ∧ P.F.H.B ≤ 128 ∧ 64 ≤ P.F.H.B := by
  simp only [shapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega

/-- The sizes, as the proofs use them. -/
theorem sizes : P.F.H.S ≤ 192 ∧ P.ok.Wi * 8 ≤ 1872 ∧ P.ok.Wf * 8 ≤ 1872 ∧ P.ok.hH.Wb ≤ 1872 ∧
    16 ≤ P.F.H.D ∧ P.F.H.D ≤ 64 ∧ P.F.H.D % 4 = 0 ∧ P.F.H.D < P.F.H.B ∧ P.F.H.B ≤ 128 ∧ 64 ≤ P.F.H.B ∧
    P.ok.hH.SH.stateBytes = P.F.H.S ∧ P.ok.hH.SH.digestBytes = P.F.H.D ∧
    P.ok.hH.SH.H.blockSize = P.F.H.B := by
  have hs := P.shape P.hDB
  exact ⟨P.hS, P.hWi, P.hWf, P.hWb, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2,
    P.ok.hH.hS, P.ok.hH.hD, P.ok.hH.hB⟩

/-- The sizes of the scalars, as the proofs use them. -/
theorem wsizes : 3 ≤ P.w ∧ P.w ≤ 9 ∧ 6 ≤ P.k ∧ P.k ≤ 2 * P.w ∧ 8 ≤ P.Q ∧ P.Q ≤ 66 ∧ P.Q ≤ 8 * P.w ∧
    8 * P.w < P.Q + 8 := by
  have hw : 8 ≤ P.Q ∧ 8 * P.w < P.Q + 8 ∧ P.Q ≤ 8 * P.w := P.R.len_words
  have hQ : P.Q ≤ 66 := by
    cases hb : P.R.big
    · have := P.R.sizesA hb; simp only [Q]; omega
    · have := P.R.sizesW hb; simp only [Q]; omega
  exact ⟨P.R.n3, P.R.n9, (by have := P.R.len_words; have := P.R.n3; simp only [k]; split <;> omega),
    (by simp only [k, w]; omega), hw.1, hQ, hw.2.2, hw.2.1⟩

/-- Unless `big`, the scalars fill at most sixteen 32-bit words. -/
theorem sizesA (h : P.R.big = false) : P.Q = 4 * P.k ∧ P.k ≤ 16 ∧ P.Q ≤ 64 := by
  have := P.R.sizesA h
  rcases this.1 with h' | h' | h' | h' <;> simp only [Q, k] <;> split <;> omega

/-- If `big`, P-521's sizes, longer than any digest. -/
theorem sizesW (h : P.R.big = true) : P.w = 9 ∧ P.Q = 66 ∧ P.k = 18 ∧ P.F.H.D < P.Q := by
  have h₁ := P.R.sizesW h
  have h₂ := (P.shape P.hDB).2.1
  refine ⟨h₁.1, h₁.2.1, ?_, by simp only [Q]; omega⟩
  simp only [k, h₁.1, h₁.2.1]; decide

theorem mac_length (K t : List Byte) : (P.mac K t).length = P.F.H.D := by
  simp only [mac, Spec.Hmac.hmac, Spec.Hmac.hmacBlockKey, P.macLen]

/-- The curve's scalars are `Q` bytes. -/
theorem curveLen : P.I.ecdsa.curve.len = P.Q := by rw [P.ecdsa, P.R.curve]

end RfcHash

/-- Facts about the sizes of the hash function `‹RfcHash›`'s states, working
space, block and output, and of the scalars, and the arithmetic they decide. -/
tactic_template "anums" : tactic => `(tactic| first | omega |
  (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩ := RfcHash.sizes ‹RfcHash›
   obtain ⟨_, _, _, _, _, _, _, _⟩ := RfcHash.wsizes ‹RfcHash›; omega))

/-- The code, for the curve of `P` and the functions an indirect call may reach. -/
def cfgOf (P : RfcHash) : Cfg where
  f := P.f
  w := 2 * P.R.E.n - (if P.R.E.C.len = 28 then 1 else 0)
  len := P.R.E.C.len
  big := P.R.big
  sh := P.R.sh
  n := P.R.E.C.n
  tries := P.I.tries
  coreN := P.R.coreN
  coreC := P.R.coreC

theorem cfgOf_len (P : RfcHash) : (cfgOf P).len = P.Q := rfl

end VG.Proof.Ecdsa.Rfc6979.Arm
