module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Regs
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.PbkCalls
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Core
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Tier
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.MdStream.AArch64.Words
public import VerifiedGarbage.Proof.Pbkdf2.AArch64.Copy
public import VerifiedGarbage.Proof.Pbkdf2.Memory
public import VerifiedGarbage.Proof.Sha256.AArch64.Lit

/-!
# Deterministic ECDSA on AArch64: the hash function

What the proof needs of the hash function, for any one of a tier's
(`RfcHash`), as on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Hash.lean`): the
curve (`R`, with what is proven of its `vg_ecdsa_<curve>_sign`, which each
candidate calls), the curve's instance of the contract (`J`, its bound on
candidates), the tier `t` of hash functions the code calls through its
dispatches, and the number `k` of the one this run uses (one of
`hashIds`): its variant `v` (`t.hashes[k]`), its code `H`, what PBKDF2's
proofs know of it (`HashOK`) and its HMAC's functions, verified. The
instance `I` of the per-hash contract is `J` with that hash function: the
spec's result with `hash = k` is `I`'s (`anyResult_eq`). The sizes the frame
and `scratch` are laid out for follow from the tier's: an output of 20 to
64 bytes, a block of 64 or 128 (`blOf k`, as the code computes it), states
of at most 192 bytes and working space of at most 2048.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK MdHash Tier hmacInit_fdepth hmacFin_fdepth)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG finG)

/-- The `k`th element of a list mapped equal to `(List.range 8).map g`. -/
theorem map_range_get {α : Type _} {β : Type _} {l : List α} {f : α → β} {g : Nat → β}
    (h : l.map f = (List.range 8).map g) {k : Nat} (hk : k < l.length) : f l[k] = g k := by
  have := List.getElem_of_eq h (by simpa using hk)
  simpa using this

theorem tier_length (t : Tier) : t.hashes.length = 8 := by
  simpa using congrArg List.length t.hmac_ok

/-- The output length of the hash function `k` names, for MGF1. -/
def dlen (k : Nat) : Nat := match Spec.HashId.mgf1 k with | some G => G.len | none => 0

/-- The block size of the hash function `k` names, for HMAC. -/
def blen (k : Nat) : Nat := match Spec.HashId.hmac k with | some H => H.blockSize | none => 0

theorem dlen_vals : ∀ k ∈ Spec.Ecdsa.Rfc6979.hashIds,
    (dlen k = 20 ∨ dlen k = 28 ∨ dlen k = 32 ∨ dlen k = 48 ∨ dlen k = 64) ∧ dlen k < blen k ∧
      blen k = blOf k ∧ k < 8 := by
  decide

/-- A curve and one hash function of a tier, for RFC 6979 on AArch64. -/
structure RfcHash where
  /-- The curve. -/
  R : RfcCurve
  /-- The curve's instance of the contract (its hash function unused). -/
  J : Spec.Ecdsa.Rfc6979.Instance
  /-- The tier, and the number of the hash function. -/
  t : Tier
  k : Nat
  hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds
  /-- The instance is of the curve, and tries at least one candidate, as
  many as a 16-bit immediate holds. -/
  ecdsa : J.ecdsa = R.inst
  tries_pos : 0 < J.tries
  tries_lt : J.tries < 2 ^ 16

namespace RfcHash

variable (P : RfcHash)

theorem k8 : P.k < 8 := (dlen_vals P.k P.hk).2.2.2

theorem kLt : P.k < P.t.hashes.length := by rw [tier_length]; exact P.k8

/-- The hash function's variant. -/
abbrev v : MdHash := P.t.hashes[P.k]'P.kLt

/-- Its code. -/
abbrev H : Impl.Pbkdf2.Md.AArch64.Hash := P.v.H
abbrev ok : HashOK P.H := P.v.ok

/-- The instance of the per-hash contract: the curve's, with this hash function. -/
abbrev I : Spec.Ecdsa.Rfc6979.Instance := { P.J with hash := P.v.I.S.H, hashLen := P.H.D }

theorem hmacFn : some P.v.I.S.H = Spec.HashId.hmac P.k := by
  have := map_range_get P.t.hmac_ok P.kLt; exact this

theorem mgfFn : some P.v.mgf.G = Spec.HashId.mgf1 P.k := by
  have := map_range_get P.t.mgf_ok P.kLt; exact this

theorem hash : P.I.hash = P.ok.SH.H := by
  show P.v.I.S.H = P.v.ok.SH.H; rw [P.v.hSH]

theorem len : P.I.hashLen = P.H.D := rfl

theorem dEq : P.H.D = dlen P.k := by
  simp only [dlen, ← P.mgfFn]; exact P.v.mgf.len.symm

theorem bEq : P.H.P.B = blen P.k := by
  simp only [blen, ← P.hmacFn, ← P.v.hSH]; exact P.ok.hB.symm

theorem hI : Verified AArch64.target P.H.hmacInit (initG P.ok.SH P.H.W) := P.v.hmacInitG

theorem hId : P.H.hmacInit.aarch64Depth ≤ 1 := hmacInit_fdepth P.ok.stream.initDepth P.ok.comp.noFrames

theorem hF : Verified AArch64.target P.H.hmacFin (finG P.ok.SH P.H.W) := P.v.hmacFinG

theorem hFd : P.H.hmacFin.aarch64Depth ≤ 1 := hmacFin_fdepth P.ok.stream.finDepth P.ok.comp.noFrames

/-- HMAC with the hash function. -/
abbrev mac (K text : List Byte) : List Byte := Spec.Hmac.hmac P.ok.SH.H K text

/-- The words of the curve's scalars. -/
abbrev w : Nat := P.R.E.n

/-- The bytes of the curve's scalars. -/
abbrev Q : Nat := P.R.E.C.len

/-- The block size the code computes. -/
theorem bl_eq : P.H.P.B = blOf P.k := by rw [P.bEq]; exact (dlen_vals P.k P.hk).2.2.1

/-- The sizes, as the proofs use them. -/
theorem sizes : P.H.S ≤ 192 ∧ P.H.P.N + P.H.P.B ≤ 192 ∧ 8 * P.H.W ≤ 2048 ∧ P.ok.stream.Wb ≤ 2048 ∧
    P.H.stream.S ≤ 192 ∧ P.H.stream.D = P.H.D ∧ 20 ≤ P.H.D ∧ P.H.D ≤ 64 ∧ P.H.D % 4 = 0 ∧
    P.H.D < P.H.P.B ∧ P.H.P.B ≤ 128 ∧ 64 ≤ P.H.P.B := by
  have hN := P.ok.N_le
  have hB := P.ok.B_le
  have hB' := P.ok.sizes.B
  have hW := P.ok.W
  have hWb := P.ok.stream.hWb
  have hW' := P.ok.stream.hW
  have hv := dlen_vals P.k P.hk
  rw [← P.dEq, ← P.bEq] at hv
  simp only [Impl.Pbkdf2.Md.AArch64.Hash.stream] at hWb hW'
  refine ⟨by show P.H.P.N + P.H.P.B ≤ 192; omega, by omega, by omega, by omega,
    by show P.H.P.N + P.H.P.B ≤ 192; omega, rfl, ?_, ?_, ?_, hv.2.1, hB, by omega⟩ <;>
    rcases hv.1 with h | h | h | h | h <;> omega

/-- The sizes of the scalars, as the proofs use them. -/
theorem wsizes : 4 ≤ P.w ∧ P.w ≤ 9 ∧ 8 ≤ P.Q ∧ P.Q ≤ 66 ∧ P.Q ≤ 8 * P.w ∧ 8 * P.w ≤ P.Q + 8 := by
  have hw : 8 ≤ P.Q ∧ 8 * P.w ≤ P.Q + 8 ∧ P.Q ≤ 8 * P.w := P.R.len_words
  have hQ : P.Q ≤ 66 := by
    cases h : P.R.wide
    · have := P.R.sizesA h; simp only [Q]; rcases this.1 with h' | h' | h' <;> omega
    · have := P.R.sizesW h; simp only [Q]; omega
  exact ⟨P.R.n4, P.R.n9, hw.1, hQ, hw.2.2, hw.2.1⟩

/-- Unless `wide`, the scalars are `8 w` bytes (or 24 or 28 in 4 words), at most 8 words. -/
theorem sizesA (h : P.R.wide = false) : (P.Q = 8 * P.w ∨ P.w = 4 ∧ (P.Q = 28 ∨ P.Q = 24)) ∧ P.w ≤ 8 := by
  have := P.R.sizesA h
  rcases this.1 with h' | h' | h' <;> simp only [Q, w] <;> omega

/-- If `wide`, P-521's sizes: every hash is shorter than its scalars. -/
theorem sizesW (h : P.R.wide = true) : P.w = 9 ∧ P.Q = 66 := by
  have := P.R.sizesW h
  exact ⟨this.1, this.2.1⟩

/-- The digest is at least 20 bytes. -/
theorem len20 : 20 ≤ P.I.hashLen := P.sizes.2.2.2.2.2.2.1

/-- The curve's scalars are `Q` bytes. -/
theorem curveLen : P.I.ecdsa.curve.len = P.Q := by
  show P.J.ecdsa.curve.len = _; rw [P.ecdsa, P.R.curve]

/-- HMAC's output is the hash function's. -/
theorem mac_length (K t : List Byte) : (P.mac K t).length = P.H.D := by
  have := P.ok.sizes.DN
  simp only [RfcHash.mac, Spec.Hmac.hmac, Spec.Hmac.hmacBlockKey, P.ok.hash, List.length_take,
    Proof.MdStream.Md.hash, P.ok.md.digest_length]
  omega

end RfcHash

/-- Facts about the sizes of the hash function `‹RfcHash›`'s states, working
space, block and output, and the arithmetic they decide. -/
tactic_template "anums" : tactic => `(tactic| first | omega |
  (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := RfcHash.sizes ‹RfcHash›
   obtain ⟨_, _, _, _, _, _⟩ := RfcHash.wsizes ‹RfcHash›; omega))

/-- The code, for the curve `R`, the tier `t` and at most `tries` candidates. -/
def cfgT (R : RfcCurve) (t : Tier) (tries : Nat) : Cfg where
  hs := t.hashes.map (·.H)
  w := R.E.n
  len := R.E.C.len
  wide := R.wide
  sh := R.sh
  n := R.E.C.n
  tries := tries
  coreN := R.coreN
  coreC := R.coreC

/-- The code, for the curve and tier of `P`: whatever its hash function. -/
abbrev cfgOf (P : RfcHash) : Cfg := cfgT P.R P.t P.J.tries

/-- The code's hash function `P.k` is `P`'s. -/
theorem hs_k (P : RfcHash) : (cfgOf P).hs[P.k]? = some P.H := by
  simp only [cfgOf, cfgT, List.getElem?_map, List.getElem?_eq_getElem P.kLt, Option.map_some]

end VG.Proof.Ecdsa.Rfc6979.AArch64
