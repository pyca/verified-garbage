module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Spec.Hmac.Generic
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Deterministic ECDSA on PPC64LE: the functions it calls

What the proof needs of a hash function (`Kit`): its streaming functions
with what HMAC's proofs know of them (`HashOK`, for the streaming `update`),
and HMAC's `init` and `finalize` with their working space as an argument,
verified against the shared contracts of their instance (`Spec.Hmac`). The
calls of HMAC's `init` and `finalize` (`initCall`, `finCall`), whose
contracts' preconditions follow from the facts at the call, and of the
signature with a given `k` (`coreCall`), against the curve's contract.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)

/-- What the proof needs of a hash function. -/
structure Kit where
  /-- The streaming functions, of which the code calls `update`. -/
  H : Hash
  hH : HashOK H
  /-- HMAC's instance, whose `init_scratch` and `finalize_scratch` the code calls. -/
  I : Spec.Hmac.Instance
  hIS : I.S = hH.SH
  initC : Prog isa
  finC : Prog isa
  /-- The stack the contracts of HMAC's functions give them. -/
  kI : Nat
  kF : Nat
  initV : ∀ s, (Proof.Hmac.Instance.initScratchContract I PPC64LE.abi (kI + 1)).pre s → ∃ t s', Exec isa initC s t s' ∧
    abiPreserved s s' ∧ (Proof.Hmac.Instance.initScratchContract I PPC64LE.abi (kI + 1)).post s s'
  finV : ∀ s, (Proof.Hmac.Instance.finalizeScratchContract I PPC64LE.abi (kF + 1)).pre s → ∃ t s', Exec isa finC s t s' ∧
    abiPreserved s s' ∧ (Proof.Hmac.Instance.finalizeScratchContract I PPC64LE.abi (kF + 1)).post s s'
  initCT : ConstantTime isa (Proof.Hmac.Instance.initScratchContract I PPC64LE.abi (kI + 1)).pre
    (Proof.Hmac.Instance.initScratchContract I PPC64LE.abi (kI + 1)).pub initC
  finCT : ConstantTime isa (Proof.Hmac.Instance.finalizeScratchContract I PPC64LE.abi (kF + 1)).pre
    (Proof.Hmac.Instance.finalizeScratchContract I PPC64LE.abi (kF + 1)).pub finC
  updCT : ConstantTime isa (Proof.Hmac.Stream.PPC64LE.updK H.S H.W hH.SH.Repr).pre
    (Proof.Hmac.Stream.PPC64LE.updK H.S H.W hH.SH.Repr).pub H.updC
  hkI : kI + 1 ≤ 96
  hkF : kF + 1 ≤ 96
  dI : sdepth initC ≤ 96
  dF : sdepth finC ≤ 96
  /-- The working space of HMAC's functions, and of `update`, between the
  states and the message. -/
  hScr : Impl.Ecdsa.Rfc6979.PPC64LE.sWork + I.scratch * 8 ≤ Impl.Ecdsa.Rfc6979.PPC64LE.sMsg
  hW : Impl.Ecdsa.Rfc6979.PPC64LE.sWork + H.W ≤ Impl.Ecdsa.Rfc6979.PPC64LE.sMsg
  hS : H.S ≤ 192

namespace Kit

variable (P : Kit)

/-- The code's HMAC. -/
def hm : Impl.Ecdsa.Rfc6979.PPC64LE.Hm :=
  ⟨P.H.B, P.H.D, s!"vg_hmac_{P.I.rust}_init_scratch", P.initC, P.H.updN, P.H.updC, s!"vg_hmac_{P.I.rust}_finalize_scratch", P.finC⟩

theorem hStates : P.I.S.stateBytes = P.H.S := by rw [P.hIS]; exact P.hH.hS

theorem hDigest : P.I.S.digestBytes = P.H.D := by rw [P.hIS]; exact P.hH.hD

end Kit

theorem initPre (P : Kit) {s : State} {inner outer key scr : Addr} {kl : Nat}
    (h3 : s.gpr .r3 = inner) (h4 : s.gpr .r4 = outer) (h5 : s.gpr .r5 = key)
    (h6 : (s.gpr .r6).toNat = kl) (h7 : s.gpr .r7 = scr) (hkl : kl ≤ P.I.S.H.blockSize)
    (d₁ : Region.Disjoint ⟨inner, P.H.S⟩ ⟨outer, P.H.S⟩) (d₂ : Region.Disjoint ⟨inner, P.H.S⟩ ⟨key, kl⟩)
    (d₃ : Region.Disjoint ⟨inner, P.H.S⟩ ⟨scr, P.I.scratch * 8⟩)
    (d₄ : Region.Disjoint ⟨outer, P.H.S⟩ ⟨key, kl⟩)
    (d₅ : Region.Disjoint ⟨outer, P.H.S⟩ ⟨scr, P.I.scratch * 8⟩)
    (d₆ : Region.Disjoint ⟨key, kl⟩ ⟨scr, P.I.scratch * 8⟩)
    (hsp : 96 ≤ s.sp.toNat)
    (k₁ : (below s.sp 96).Disjoint ⟨inner, P.H.S⟩) (k₂ : (below s.sp 96).Disjoint ⟨outer, P.H.S⟩)
    (k₃ : (below s.sp 96).Disjoint ⟨key, kl⟩) (k₄ : (below s.sp 96).Disjoint ⟨scr, P.I.scratch * 8⟩)
    (n₁ : inner.toNat + P.H.S ≤ 2 ^ 64) (n₂ : outer.toNat + P.H.S ≤ 2 ^ 64) (n₃ : key.toNat + kl ≤ 2 ^ 64)
    (n₄ : scr.toNat + P.I.scratch * 8 ≤ 2 ^ 64)
    : (Proof.Hmac.Instance.initScratchContract P.I PPC64LE.abi (P.kI + 1)).pre (s.callEntry.withRegions [⟨key, kl⟩]
      [⟨inner, P.H.S⟩, ⟨outer, P.H.S⟩, ⟨scr, P.I.scratch * 8⟩]) := by
  have hS := P.hStates
  have hk := P.hkI
  sig_pre [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract,
    Proof.Hmac.initScratchSig, Spec.Hmac.initPre, PPC64LE.abi, PPC64LE.argRegs, stackBelow]
  simp only [h3, h4, h5, h6, h7, hS]
  have kb : ∀ {r : Region}, (below s.sp 96).Disjoint r →
      Region.Disjoint ⟨s.sp - BitVec.ofNat 64 (P.kI + 1), P.kI + 1⟩ r := fun h =>
    h.sub_left (below_sub hk (by omega_arith))
  exact ⟨by omega_arith, trivial, trivial, d₁, d₂, d₃, d₄, d₅, d₆, kb k₁, kb k₂, kb k₃, kb k₄, n₁, n₂, n₃, n₄, hkl⟩

/-- The call of HMAC's `init` with the key of `kl` bytes at `key`, the
states at `inner` and `outer` and the working space at `scr`. -/
theorem initCall (P : Kit) {s : State} {inner outer key scr : Addr} {kl : Nat}
    (h3 : s.gpr .r3 = inner) (h4 : s.gpr .r4 = outer) (h5 : s.gpr .r5 = key)
    (h6 : (s.gpr .r6).toNat = kl) (h7 : s.gpr .r7 = scr) (hkl : kl ≤ P.I.S.H.blockSize)
    (d₁ : Region.Disjoint ⟨inner, P.H.S⟩ ⟨outer, P.H.S⟩) (d₂ : Region.Disjoint ⟨inner, P.H.S⟩ ⟨key, kl⟩)
    (d₃ : Region.Disjoint ⟨inner, P.H.S⟩ ⟨scr, P.I.scratch * 8⟩)
    (d₄ : Region.Disjoint ⟨outer, P.H.S⟩ ⟨key, kl⟩)
    (d₅ : Region.Disjoint ⟨outer, P.H.S⟩ ⟨scr, P.I.scratch * 8⟩)
    (d₆ : Region.Disjoint ⟨key, kl⟩ ⟨scr, P.I.scratch * 8⟩)
    (hsp : 96 ≤ s.sp.toNat)
    (k₁ : (below s.sp 96).Disjoint ⟨inner, P.H.S⟩) (k₂ : (below s.sp 96).Disjoint ⟨outer, P.H.S⟩)
    (k₃ : (below s.sp 96).Disjoint ⟨key, kl⟩) (k₄ : (below s.sp 96).Disjoint ⟨scr, P.I.scratch * 8⟩)
    (n₁ : inner.toNat + P.H.S ≤ 2 ^ 64) (n₂ : outer.toNat + P.H.S ≤ 2 ^ 64) (n₃ : key.toNat + kl ≤ 2 ^ 64)
    (n₄ : scr.toNat + P.I.scratch * 8 ≤ 2 ^ 64)
    (hc : Covers ([⟨key, kl⟩] ++ [⟨inner, P.H.S⟩, ⟨outer, P.H.S⟩, ⟨scr, P.I.scratch * 8⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨inner, P.H.S⟩, ⟨outer, P.H.S⟩, ⟨scr, P.I.scratch * 8⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame ([⟨inner, P.H.S⟩, ⟨outer, P.H.S⟩, ⟨scr, P.I.scratch * 8⟩] ++ [below s.sp 96]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      P.I.S.Repr s'.mem inner
          (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.I.S.H (Spec.Sha256.bytesAt s.mem key kl)) Spec.Hmac.ipad) →
      P.I.S.Repr s'.mem outer
          (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.I.S.H (Spec.Sha256.bytesAt s.mem key kl)) Spec.Hmac.opad) →
      Q s') :
    WP isa (.call P.hm.initN P.hm.initC) s Q := by
  have hS := P.hStates
  have hk := P.hkI
  refine WP.callAny (k := Proof.Hmac.Instance.initScratchContract P.I PPC64LE.abi (P.kI + 1)) P.initV (rd := [⟨key, kl⟩])
    (wr := [⟨inner, P.H.S⟩, ⟨outer, P.H.S⟩, ⟨scr, P.I.scratch * 8⟩])
    (initPre P h3 h4 h5 h6 h7 hkl d₁ d₂ d₃ d₄ d₅ d₆ hsp k₁ k₂ k₃ k₄ n₁ n₂ n₃ n₄) hc hw ?_
    (by have := P.dI; omega_arith)
  · intro s' h₁ h₂ h₃ h₄ hcs hpost
    sig_post [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract,
      Proof.Hmac.initScratchSig, Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs, stackBelow] at hpost
    simp only [h3, h4, h5, h6] at hpost
    exact hQ s' h₁ h₂ h₃ (Frame.below_mono h₄ (by have := P.dI; omega_arith) (by omega_arith)) hcs hpost.1 hpost.2

theorem finPre (P : Kit) {s : State} {inner outer out scr : Addr}
    (h3 : s.gpr .r3 = inner) (h4 : s.gpr .r4 = outer) (h6 : s.gpr .r6 = out) (h7 : s.gpr .r7 = scr)
    (d₁ : Region.Disjoint ⟨inner, P.H.S⟩ ⟨outer, P.H.S⟩) (d₂ : Region.Disjoint ⟨inner, P.H.S⟩ ⟨out, P.H.D⟩)
    (d₃ : Region.Disjoint ⟨inner, P.H.S⟩ ⟨scr, P.I.scratch * 8⟩)
    (d₄ : Region.Disjoint ⟨outer, P.H.S⟩ ⟨out, P.H.D⟩)
    (d₅ : Region.Disjoint ⟨outer, P.H.S⟩ ⟨scr, P.I.scratch * 8⟩)
    (d₆ : Region.Disjoint ⟨out, P.H.D⟩ ⟨scr, P.I.scratch * 8⟩)
    (hsp : 96 ≤ s.sp.toNat)
    (k₁ : (below s.sp 96).Disjoint ⟨inner, P.H.S⟩) (k₂ : (below s.sp 96).Disjoint ⟨outer, P.H.S⟩)
    (k₃ : (below s.sp 96).Disjoint ⟨out, P.H.D⟩) (k₄ : (below s.sp 96).Disjoint ⟨scr, P.I.scratch * 8⟩)
    (n₁ : inner.toNat + P.H.S ≤ 2 ^ 64) (n₂ : outer.toNat + P.H.S ≤ 2 ^ 64) (n₃ : out.toNat + P.H.D ≤ 2 ^ 64)
    (n₄ : scr.toNat + P.I.scratch * 8 ≤ 2 ^ 64)
    : (Proof.Hmac.Instance.finalizeScratchContract P.I PPC64LE.abi (P.kF + 1)).pre (s.callEntry.withRegions [⟨outer, P.H.S⟩]
      [⟨inner, P.H.S⟩, ⟨out, P.H.D⟩, ⟨scr, P.I.scratch * 8⟩]) := by
  have hS := P.hStates
  have hD := P.hDigest
  have hk := P.hkF
  sig_pre [Proof.Hmac.Instance.finalizeScratchContract, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, PPC64LE.abi, PPC64LE.argRegs, stackBelow]
  simp only [h3, h4, h6, h7, hS, hD]
  have kb : ∀ {r : Region}, (below s.sp 96).Disjoint r →
      Region.Disjoint ⟨s.sp - BitVec.ofNat 64 (P.kF + 1), P.kF + 1⟩ r := fun h =>
    h.sub_left (below_sub hk (by omega_arith))
  exact ⟨by omega_arith, trivial, trivial, d₁, d₂, d₃, d₄, d₅, d₆, kb k₁, kb k₂, kb k₃, kb k₄, n₁, n₂, n₃, n₄⟩

/-- The call of HMAC's `finalize` with the states at `inner` and `outer`,
the count `cnt`, the MAC to `out` and the working space at `scr`. -/
theorem finCall (P : Kit) {s : State} {inner outer out scr : Addr}
    (h3 : s.gpr .r3 = inner) (h4 : s.gpr .r4 = outer) (h6 : s.gpr .r6 = out) (h7 : s.gpr .r7 = scr)
    (d₁ : Region.Disjoint ⟨inner, P.H.S⟩ ⟨outer, P.H.S⟩) (d₂ : Region.Disjoint ⟨inner, P.H.S⟩ ⟨out, P.H.D⟩)
    (d₃ : Region.Disjoint ⟨inner, P.H.S⟩ ⟨scr, P.I.scratch * 8⟩)
    (d₄ : Region.Disjoint ⟨outer, P.H.S⟩ ⟨out, P.H.D⟩)
    (d₅ : Region.Disjoint ⟨outer, P.H.S⟩ ⟨scr, P.I.scratch * 8⟩)
    (d₆ : Region.Disjoint ⟨out, P.H.D⟩ ⟨scr, P.I.scratch * 8⟩)
    (hsp : 96 ≤ s.sp.toNat)
    (k₁ : (below s.sp 96).Disjoint ⟨inner, P.H.S⟩) (k₂ : (below s.sp 96).Disjoint ⟨outer, P.H.S⟩)
    (k₃ : (below s.sp 96).Disjoint ⟨out, P.H.D⟩) (k₄ : (below s.sp 96).Disjoint ⟨scr, P.I.scratch * 8⟩)
    (n₁ : inner.toNat + P.H.S ≤ 2 ^ 64) (n₂ : outer.toNat + P.H.S ≤ 2 ^ 64) (n₃ : out.toNat + P.H.D ≤ 2 ^ 64)
    (n₄ : scr.toNat + P.I.scratch * 8 ≤ 2 ^ 64)
    (hc : Covers ([⟨outer, P.H.S⟩] ++ [⟨inner, P.H.S⟩, ⟨out, P.H.D⟩, ⟨scr, P.I.scratch * 8⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨inner, P.H.S⟩, ⟨out, P.H.D⟩, ⟨scr, P.I.scratch * 8⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame ([⟨inner, P.H.S⟩, ⟨out, P.H.D⟩, ⟨scr, P.I.scratch * 8⟩] ++ [below s.sp 96]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (∀ k0 text, k0.length = P.I.S.H.blockSize → k0.length + text.length < 2 ^ 64 →
        P.I.S.Repr s.mem inner (Spec.Hmac.xorPad k0 Spec.Hmac.ipad ++ text) →
        s.gpr .r5 = BitVec.ofNat 64 (P.I.S.H.blockSize + text.length) →
        P.I.S.Repr s.mem outer (Spec.Hmac.xorPad k0 Spec.Hmac.opad) →
        Spec.Sha256.bytesAt s'.mem out P.H.D = Spec.Hmac.hmacBlockKey P.I.S.H k0 text) → Q s') :
    WP isa (.call P.hm.finN P.hm.finC) s Q := by
  have hS := P.hStates
  have hD := P.hDigest
  have hk := P.hkF
  refine WP.callAny (k := Proof.Hmac.Instance.finalizeScratchContract P.I PPC64LE.abi (P.kF + 1)) P.finV (rd := [⟨outer, P.H.S⟩])
    (wr := [⟨inner, P.H.S⟩, ⟨out, P.H.D⟩, ⟨scr, P.I.scratch * 8⟩])
    (finPre P h3 h4 h6 h7 d₁ d₂ d₃ d₄ d₅ d₆ hsp k₁ k₂ k₃ k₄ n₁ n₂ n₃ n₄) hc hw ?_
    (by have := P.dF; omega_arith)
  · intro s' h₁ h₂ h₃ h₄ hcs hpost
    sig_post [Proof.Hmac.Instance.finalizeScratchContract, Proof.Hmac.finalizeScratchContract,
      Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, PPC64LE.abi, PPC64LE.argRegs, stackBelow] at hpost
    simp only [h3, h4, h6, hD] at hpost
    exact hQ s' h₁ h₂ h₃ (Frame.below_mono h₄ (by have := P.dF; omega_arith) (by omega_arith)) hcs hpost

/-- The signature with a given `k`, as the code calls it: the curve's
contract, its code and its name. -/
structure Core where
  E : Spec.Ecdsa.Instance
  C : Prog isa
  N : String
  V : ∀ s, (Proof.Ecdsa.Instance.signContract E PPC64LE.abi).pre s → ∃ t s', Exec isa C s t s' ∧ abiPreserved s s' ∧
    (Proof.Ecdsa.Instance.signContract E PPC64LE.abi).post s s'
  ct : ConstantTime isa (Proof.Ecdsa.Instance.signContract E PPC64LE.abi).pre (Proof.Ecdsa.Instance.signContract E PPC64LE.abi).pub C
  d : sdepth C ≤ 96

theorem corePre (R : Core) {s : State} {out d dg k scr : Addr}
    (h3 : s.gpr .r3 = out) (h4 : s.gpr .r4 = d) (h5 : s.gpr .r5 = dg) (h6 : s.gpr .r6 = k)
    (h7 : s.gpr .r7 = scr)
    (o₁ : Region.Disjoint ⟨out, 2 * R.E.curve.len⟩ ⟨d, R.E.curve.len⟩)
    (o₂ : Region.Disjoint ⟨out, 2 * R.E.curve.len⟩ ⟨dg, R.E.curve.len⟩)
    (o₃ : Region.Disjoint ⟨out, 2 * R.E.curve.len⟩ ⟨k, R.E.curve.len⟩)
    (o₄ : Region.Disjoint ⟨out, 2 * R.E.curve.len⟩ ⟨scr, 8192⟩)
    (c₁ : Region.Disjoint ⟨d, R.E.curve.len⟩ ⟨scr, 8192⟩) (c₂ : Region.Disjoint ⟨dg, R.E.curve.len⟩ ⟨scr, 8192⟩)
    (c₃ : Region.Disjoint ⟨k, R.E.curve.len⟩ ⟨scr, 8192⟩)
    (n₁ : out.toNat + 2 * R.E.curve.len ≤ 2 ^ 64) (n₂ : d.toNat + R.E.curve.len ≤ 2 ^ 64)
    (n₃ : dg.toNat + R.E.curve.len ≤ 2 ^ 64) (n₄ : k.toNat + R.E.curve.len ≤ 2 ^ 64)
    (n₅ : scr.toNat + 8192 ≤ 2 ^ 64)
    : (Proof.Ecdsa.Instance.signContract R.E PPC64LE.abi).pre (s.callEntry.withRegions
      [⟨d, R.E.curve.len⟩, ⟨dg, R.E.curve.len⟩, ⟨k, R.E.curve.len⟩] [⟨out, 2 * R.E.curve.len⟩, ⟨scr, 8192⟩]) := by
  sig_pre [Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig, Spec.Ecdsa.scratchWords,
    PPC64LE.abi, PPC64LE.argRegs, stackBelow]
  simp only [h3, h4, h5, h6, h7]
  exact ⟨trivial, trivial, o₁, o₂, o₃, o₄, c₁, c₂, c₃, n₁, n₂, n₃, n₄, n₅⟩

/-- The call of the signature with `k`: `out` of `2 Q` bytes, `d`, the
digest and `k` of `Q` each, the working space at `scr`. -/
theorem coreCall (R : Core) {s : State} {out d dg k scr : Addr}
    (h3 : s.gpr .r3 = out) (h4 : s.gpr .r4 = d) (h5 : s.gpr .r5 = dg) (h6 : s.gpr .r6 = k)
    (h7 : s.gpr .r7 = scr)
    (o₁ : Region.Disjoint ⟨out, 2 * R.E.curve.len⟩ ⟨d, R.E.curve.len⟩)
    (o₂ : Region.Disjoint ⟨out, 2 * R.E.curve.len⟩ ⟨dg, R.E.curve.len⟩)
    (o₃ : Region.Disjoint ⟨out, 2 * R.E.curve.len⟩ ⟨k, R.E.curve.len⟩)
    (o₄ : Region.Disjoint ⟨out, 2 * R.E.curve.len⟩ ⟨scr, 8192⟩)
    (c₁ : Region.Disjoint ⟨d, R.E.curve.len⟩ ⟨scr, 8192⟩) (c₂ : Region.Disjoint ⟨dg, R.E.curve.len⟩ ⟨scr, 8192⟩)
    (c₃ : Region.Disjoint ⟨k, R.E.curve.len⟩ ⟨scr, 8192⟩)
    (n₁ : out.toNat + 2 * R.E.curve.len ≤ 2 ^ 64) (n₂ : d.toNat + R.E.curve.len ≤ 2 ^ 64)
    (n₃ : dg.toNat + R.E.curve.len ≤ 2 ^ 64) (n₄ : k.toNat + R.E.curve.len ≤ 2 ^ 64)
    (n₅ : scr.toNat + 8192 ≤ 2 ^ 64)
    (hc : Covers ([⟨d, R.E.curve.len⟩, ⟨dg, R.E.curve.len⟩, ⟨k, R.E.curve.len⟩] ++
      [⟨out, 2 * R.E.curve.len⟩, ⟨scr, 8192⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨out, 2 * R.E.curve.len⟩, ⟨scr, 8192⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame ([⟨out, 2 * R.E.curve.len⟩, ⟨scr, 8192⟩] ++ [below s.sp 96]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (match Spec.Ecdsa.signWith R.E.curve (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem d R.E.curve.len))
          (Spec.Ecdsa.hashToInt R.E.curve (Spec.Ecdsa.bytesAt s.mem dg R.E.curve.len))
          (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem k R.E.curve.len)) with
        | some rs => (s'.gpr .r3).setWidth 32 = (1 : BitVec 32) ∧
            Spec.Ecdsa.bytesAt s'.mem out (2 * R.E.curve.len) = Spec.Ecdsa.encode R.E.curve rs
        | none => (s'.gpr .r3).setWidth 32 = (0 : BitVec 32) ∧
            Spec.Ecdsa.bytesAt s'.mem out (2 * R.E.curve.len) = List.replicate (2 * R.E.curve.len) 0) →
      Q s') :
    WP isa (.call R.N R.C) s Q := by
  refine WP.callAny (k := Proof.Ecdsa.Instance.signContract R.E PPC64LE.abi) R.V
    (rd := [⟨d, R.E.curve.len⟩, ⟨dg, R.E.curve.len⟩, ⟨k, R.E.curve.len⟩])
    (wr := [⟨out, 2 * R.E.curve.len⟩, ⟨scr, 8192⟩])
    (corePre R h3 h4 h5 h6 h7 o₁ o₂ o₃ o₄ c₁ c₂ c₃ n₁ n₂ n₃ n₄ n₅) hc hw ?_ (by have := R.d; omega_arith)
  · intro s' h₁ h₂ h₃ h₄ hcs hpost
    sig_post [Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig, Spec.Ecdsa.scratchWords,
      PPC64LE.abi, PPC64LE.argRegs, stackBelow] at hpost
    simp only [h3, h4, h5, h6] at hpost
    exact hQ s' h₁ h₂ h₃ (Frame.below_mono h₄ (by have := R.d; omega_arith) (by omega_arith)) hcs hpost

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
