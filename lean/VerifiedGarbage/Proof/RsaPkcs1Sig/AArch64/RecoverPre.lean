import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract
import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.Recover
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyFrame

/-!
# `vg_rsa_pkcs1_recover` on AArch64: the precondition

`PreR K s`: the shared contract's precondition (`recoverContract`, with the
stack `stk K` of `vg_rsa_pkcs1_verify`'s frame, which recovery shares, and
a callee using `K` bytes), by name (`preR_of`).
-/

namespace VG.Proof.RsaPkcs1Sig.AArch64.Rec

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Verify
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (stk stackArgs_three sR aR kR fb kb stackArgAddr_eq keep_of_frame)

/-- The buffers: `out`, `n`, `e` and the signature (the working space, the
arguments on the stack and the stack used are `vg_rsa_pkcs1_verify`'s). -/
abbrev oR (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
abbrev nR (s : State) : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
abbrev gR (s : State) : Region := ⟨s.gpr .x7, (stackArg s 0).toNat⟩

/-- What the code needs of `recoverContract.pre`, by name. -/
structure PreR (K : Nat) (s : State) : Prop where
  sp1 : stk K ≤ s.sp.toNat
  sp2 : s.sp.toNat + 24 ≤ 2 ^ 64
  hrd : Covers [nR s, eR s, gR s, aR s] s.rd
  hwo : oR s ∈ s.wr
  hws : sR s ∈ s.wr
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  og : (oR s).Disjoint (gR s)
  os : (oR s).Disjoint (sR s)
  oa : (oR s).Disjoint (aR s)
  ns : (nR s).Disjoint (sR s)
  es : (eR s).Disjoint (sR s)
  gs : (gR s).Disjoint (sR s)
  sa : (sR s).Disjoint (aR s)
  ko : (kR K s).Disjoint (oR s)
  kn : (kR K s).Disjoint (nR s)
  ke : (kR K s).Disjoint (eR s)
  kg : (kR K s).Disjoint (gR s)
  ks : (kR K s).Disjoint (sR s)
  ka : (kR K s).Disjoint (aR s)
  wo : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  wn : (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64
  we : (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64
  wg : (s.gpr .x7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  ws : (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .x3).toNat
  k2 : (s.gpr .x3).toNat ≤ 1024
  e1 : 1 ≤ (s.gpr .x5).toNat
  e2 : (s.gpr .x5).toNat ≤ (s.gpr .x3).toNat
  hh : ∃ h, Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .x6).setWidth 32).toNat = some h ∧ (s.gpr .x1).toNat = h.len
  hs : 16 * (s.gpr .x3).toNat ≤ (stackArg s 2).toNat

theorem preR_of {K : Nat} {s : State}
    (h : (Spec.RsaPkcs1Sig.recoverContract abi (stk K)).pre s) : PreR K s := by
  have e : stk K = (frameBytes + K - 1) + 1 := by unfold stk frameBytes; omega
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Sig.recoverContract, Spec.RsaPkcs1Sig.recoverSig, abi, argRegs, stackArgs_three,
    List.append_eq] at h
  sig_pre [Spec.RsaPkcs1Sig.recoverContract, Spec.RsaPkcs1Sig.recoverSig, abi, argRegs, stackArgs_three,
    List.append_eq] at h
  obtain ⟨sp1, sp2, hrd, hwr, on, oe, og, os, oa, ns, es, gs, sa, ko, kn, ke, kg, ks, ka, wo, wn, we, wg, ws,
    ⟨k1, k2⟩, e1, e2, hh, hs⟩ := h
  rw [← e] at sp1 ko kn ke kg ks ka
  exact ⟨sp1, sp2, by rw [hrd]; exact Covers.refl _, by rw [hwr]; simp, by rw [hwr]; simp, on, oe, og, os, oa,
    ns, es, gs, sa, ko, kn, ke, kg, ks, ka, wo, wn, we, wg, ws, k1, k2, e1, e2, hh,
    by unfold Spec.Rsa.scratchWords at hs; omega⟩

/-- The length of the hash value is at most `k`, and not 0. -/
theorem hlen {K : Nat} {s : State} (hp : PreR K s) :
    0 < (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ (s.gpr .x3).toNat := by
  obtain ⟨h, -, e⟩ := hp.hh
  have := hp.k1
  rw [e]; cases h <;> simp [Spec.RsaPkcs1Sig.Hash.len] <;> omega

theorem kb_toNat {K : Nat} {s : State} (hp : PreR K s) :
    (kb K s).toNat + stk K = s.sp.toNat ∧ s.sp.toNat + 24 ≤ 2 ^ 64 := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]
  constructor <;> omega

theorem fb_toNat {K : Nat} {s : State} (hp : PreR K s) : (fb s).toNat + frameBytes = s.sp.toNat := by
  have := hp.sp1
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold stk at this; omega

/-- The stack arguments are readable. -/
theorem arg_in {K : Nat} {s : State} (hp : PreR K s) {rs : List Region} (hrd : Covers s.rd rs) {j : Nat}
    (hj : j < 3) : InRegions rs (stackArgAddr s j) 8 :=
  hrd _ _ <| hp.hrd _ _ ⟨aR s, by simp, by
    rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩

/-- A stack argument, in memory changed only in the frame. -/
theorem arg_frame {K : Nat} {s : State} (hp : PreR K s) {m : Mem} (h : Frame [⟨fb s, frameBytes⟩] s.mem m)
    {j : Nat} (hj : j < 3) : m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (r := aR s) (by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega))
    (keep_of_frame hp.ka) (by decide)

end VG.Proof.RsaPkcs1Sig.AArch64.Rec
