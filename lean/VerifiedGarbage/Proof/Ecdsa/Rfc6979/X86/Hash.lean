module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Regs
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Common
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.X25519.X86.Column
public import VerifiedGarbage.Proof.Sha256.X86.Lit
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Tier

/-!
# Deterministic ECDSA on x86 (32-bit): the hash function

What the proof needs of a run (`RfcHash`): the curve (`RfcCurve`, with what
is proven of `vg_ecdsa_<curve>_sign`, which each candidate calls), the
instance of the contract (its curve and number of candidates), the hash
functions the code calls by their numbers (`fns`, a tier's), and the number
`k` of the run's: its functions, verified, and their sizes (`TierHash`),
`k`'s HMAC (`HashId.hmac`). The code (`cfgOf`) does not depend on `k`; the
instance of the run (`RfcHash.I`) is the contract's with `k`'s HMAC and
output length.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Proof.Pbkdf2.Whole.X86 (FnsOK ReprOK TierHash dbSizes)

/-- A curve, the hash functions the code calls, and the one of a run, for
RFC 6979 on x86. -/
structure RfcHash where
  /-- The curve. -/
  R : RfcCurve
  /-- The instance of the contract: its curve and number of candidates. -/
  I₀ : Spec.Ecdsa.Rfc6979.Instance
  ecdsa : I₀.ecdsa = R.inst
  /-- It tries at least one candidate, as many as a 32-bit immediate holds. -/
  tries_pos : 0 < I₀.tries
  tries_lt : I₀.tries < 2 ^ 32
  /-- The hash functions the code calls, by number. -/
  fns : List (Nat × Fns)
  nodup : (fns.map (·.1)).Nodup
  keys_lt : ∀ p ∈ fns, p.1 < 2 ^ 31
  /-- None of their functions writes `esp`. -/
  fnsSp : ∀ p ∈ fns, NoSp p.2.hiC ∧ NoSp p.2.H.updC ∧ NoSp p.2.hfC
  /-- The run's: its number, and its functions, verified. -/
  k : Nat
  T : TierHash
  mem : (k, T.F) ∈ fns
  hmac : Spec.HashId.hmac k = some T.ok.hH.SH.H

namespace RfcHash

variable (P : RfcHash)

abbrev F : Fns := P.T.F
abbrev ok : FnsOK P.F := P.T.ok

/-- The instance of the run: the contract's, with the hash function's HMAC
and output length. -/
abbrev I : Spec.Ecdsa.Rfc6979.Instance := { P.I₀ with hash := P.ok.hH.SH.H, hashLen := P.F.H.D }

theorem len : P.I.hashLen = P.F.H.D := rfl
theorem hash : P.I.hash = P.ok.hH.SH.H := rfl

theorem macLen : ∀ x, (P.ok.hH.SH.H.hash x).length = P.F.H.D := P.T.macLen

/-- HMAC with the hash function. -/
abbrev mac (K text : List Byte) : List Byte := Spec.Hmac.hmac P.ok.hH.SH.H K text

theorem reprOK : ReprOK P.ok.hH.SH := fun m m' p q msg hb =>
  P.ok.hH.repr m m' p q msg (fun i hi => hb i (by rw [P.ok.hH.hS]; exact hi))

/-- The 64-bit words of the curve's scalars. -/
abbrev w : Nat := P.R.E.n

/-- Their 32-bit words: seven for P-224, otherwise two per 64-bit word. -/
abbrev k32 : Nat := 2 * P.R.E.n - (if P.R.E.C.len = 28 then 1 else 0)

/-- The bytes of the curve's scalars. -/
abbrev Q : Nat := P.R.E.C.len

/-- The number of `V`s in a candidate. -/
abbrev nb : Nat := (8 * P.Q - P.R.sh + 8 * P.F.H.D - 1) / (8 * P.F.H.D)

theorem tdb : (P.F.H.D, P.F.H.B) ∈ dbSizes := P.T.hDB

theorem db : (P.F.H.D = 20 ∧ P.F.H.B = 64) ∨ (P.F.H.D = 28 ∧ P.F.H.B = 64) ∨ (P.F.H.D = 32 ∧ P.F.H.B = 64) ∨
    (P.F.H.D = 48 ∧ P.F.H.B = 128) ∨ (P.F.H.D = 64 ∧ P.F.H.B = 128) ∨ (P.F.H.D = 28 ∧ P.F.H.B = 128) ∨
    (P.F.H.D = 32 ∧ P.F.H.B = 128) := by
  have h := P.tdb
  simp only [dbSizes, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  exact h

/-- The sizes, as the proofs use them. -/
theorem sizes : P.F.H.S ≤ 192 ∧ P.ok.Wi * 8 ≤ 1872 ∧ P.ok.Wf * 8 ≤ 1872 ∧ P.ok.hH.Wb ≤ 1872 ∧
    20 ≤ P.F.H.D ∧ P.F.H.D ≤ 64 ∧ P.F.H.D % 4 = 0 ∧ P.F.H.D < P.F.H.B ∧ P.F.H.B ≤ 128 ∧ 0 < P.F.H.S ∧
    3 ≤ P.w ∧ P.w ≤ 9 ∧ 6 ≤ P.k32 ∧ P.k32 ≤ 2 * P.w ∧ 8 ≤ P.Q ∧ P.Q ≤ 66 ∧ P.Q ≤ 8 * P.w ∧
    8 * P.w < P.Q + 8 := by
  have hWb := P.ok.hH.hWb
  have hW := P.ok.hH.hW
  have hS0 := P.ok.hH.hS0
  have hw : 8 ≤ P.Q ∧ 8 * P.w < P.Q + 8 ∧ P.Q ≤ 8 * P.w := P.R.len_words
  have hQ : P.Q ≤ 66 := by
    cases hW : P.R.wide
    · have := P.R.sizesA hW; show P.R.E.C.len ≤ _; omega
    · have := P.R.sizesW hW; show P.R.E.C.len ≤ _; omega
  refine ⟨P.T.hS, P.T.hWi, P.T.hWf, by omega, ?_, ?_, ?_, ?_, ?_, hS0, P.R.n3, P.R.n9,
    (by have := P.R.len_words; have := P.R.n3; simp only [k32]; split <;> omega), (by simp only [k32, w]; omega),
    hw.1, hQ, hw.2.2, hw.2.1⟩ <;>
    rcases P.db with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp only [h, h'] <;> omega

/-- Unless `wide`, the scalars fill at most sixteen 32-bit words. -/
theorem sizesA (h : P.R.wide = false) : P.Q = 4 * P.k32 ∧ P.k32 ≤ 16 := by
  have := P.R.sizesA h
  rcases this.1 with h' | h' | h' | h' <;> simp only [Q, k32] <;> split <;> omega

/-- The possible byte lengths of the scalars, unless `wide`. -/
theorem lengthsA (h : P.R.wide = false) : P.Q = 24 ∨ P.Q = 32 ∨ P.Q = 48 ∨ P.Q = 64 ∨ P.Q = 28 := by
  have := P.R.sizesA h
  simp only [Q]
  omega

/-- If `wide`, P-521's sizes. -/
theorem sizesW (h : P.R.wide = true) : P.w = 9 ∧ P.Q = 66 ∧ P.R.sh = 7 := by
  have := P.R.sizesW h
  have h₁ := P.R.nBits_len
  exact ⟨this.1, this.2.1, by omega⟩

/-- `sh` is 0 unless `wide`. -/
theorem sh0 (h : P.R.wide = false) : P.R.sh = 0 := by
  have := P.R.sizesA h
  have h₁ := P.R.nBits_len
  omega

/-- The candidate's `V`s: at least one, at least `Q` bytes, and the last at
most 64 bytes in. -/
theorem nb_facts : 1 ≤ P.nb ∧ P.Q ≤ P.nb * P.F.H.D ∧ (P.nb - 1) * P.F.H.D ≤ 64 ∧ P.nb ≤ 4 := by
  have hs := P.sizes
  have hl := P.R.nBits_len
  have hsh : P.R.sh < 8 := by omega
  cases hW : P.R.wide
  · have h0 := P.sh0 hW
    simp only [nb, h0, Nat.sub_zero]
    rcases P.lengthsA hW with hQ | hQ | hQ | hQ | hQ <;>
      rcases P.db with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      simp only [hQ, h] <;> decide
  · obtain ⟨-, hQ, h7⟩ := P.sizesW hW
    simp only [nb, hQ, h7]
    rcases P.db with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp only [h] <;> decide

/-- The curve's scalars are `Q` bytes. -/
theorem curveLen : P.I.ecdsa.curve.len = P.Q := by
  show P.I₀.ecdsa.curve.len = _; rw [P.ecdsa, P.R.curve]

end RfcHash

/-- Facts about the sizes of the hash function `‹RfcHash›`'s states, working
space, block and output, and the arithmetic they decide. -/
tactic_template "nums" : tactic => `(tactic| first | omega |
  (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := RfcHash.sizes ‹RfcHash›; omega))

/-- What the layout of a run has of `P`. -/
structure Fits (P : RfcHash) (L : Lay P.I.hashLen) : Prop where
  q : L.q = P.Q
  bk : L.Bk = P.F.H.B
  nb : L.nb = P.nb
  cs : L.cs = P.R.E.combConsts
  hs : L.hs.toNat = P.k

/-- The code, for the curve `R`, the hash functions `fns`, the instance `I₀`. -/
def cfgAny (R : RfcCurve) (fns : List (Nat × Fns)) (I₀ : Spec.Ecdsa.Rfc6979.Instance) : Cfg where
  fns := fns
  w := 2 * R.E.n - (if R.E.C.len = 28 then 1 else 0)
  len := R.E.C.len
  sh := R.sh
  n := R.E.C.n
  tries := I₀.tries
  coreN := R.coreN
  coreC := R.coreC

/-- The code of a run. -/
abbrev cfgOf (P : RfcHash) : Cfg := cfgAny P.R P.fns P.I₀

theorem cfgOf_nb (P : RfcHash) : (cfgOf P).nb P.F.H.D = P.nb := rfl

end VG.Proof.Ecdsa.Rfc6979.X86
