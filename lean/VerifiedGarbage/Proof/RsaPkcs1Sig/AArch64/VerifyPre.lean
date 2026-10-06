import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract
import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.Verify
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee

/-!
# `vg_rsa_pkcs1_verify` on AArch64: the precondition

`PreV K s`: the shared contract's precondition (`verifyContract`, with the
stack `stk K` of the frame and a callee using `K` bytes), by name
(`preV_of`).
-/

namespace VG.Proof.RsaPkcs1Sig.AArch64.Ver

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Verify

/-- The stack `vg_rsa_pkcs1_verify` uses: its frame, and its callee's
stack. -/
def stk (K : Nat) : Nat := frameBytes + K

theorem stackArgs_three (s : State) :
    List.map (stackArg s) (List.range 3) = [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

/-- The buffers: `n`, `e`, the hash value, the signature, the working space,
the arguments on the stack, and the stack the function uses. -/
abbrev nR (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
abbrev dR (s : State) : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
abbrev gR (s : State) : Region := ⟨s.gpr .x7, (stackArg s 0).toNat⟩
abbrev sR (s : State) : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 24⟩
abbrev kR (K : Nat) (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 (stk K), stk K⟩

/-- `verifyContract.pre`, by name. -/
structure PreV (K : Nat) (s : State) : Prop where
  sp1 : stk K ≤ s.sp.toNat
  sp2 : s.sp.toNat + 24 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, dR s, gR s, aR s]
  hwr : s.wr = [sR s]
  ns : (nR s).Disjoint (sR s)
  es : (eR s).Disjoint (sR s)
  ds : (dR s).Disjoint (sR s)
  gs : (gR s).Disjoint (sR s)
  sa : (sR s).Disjoint (aR s)
  kn : (kR K s).Disjoint (nR s)
  ke : (kR K s).Disjoint (eR s)
  kd : (kR K s).Disjoint (dR s)
  kg : (kR K s).Disjoint (gR s)
  ks : (kR K s).Disjoint (sR s)
  ka : (kR K s).Disjoint (aR s)
  wn : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  we : (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64
  wd : (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64
  wg : (s.gpr .x7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  ws : (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .x1).toNat
  k2 : (s.gpr .x1).toNat ≤ 1024
  e1 : 1 ≤ (s.gpr .x3).toNat
  e2 : (s.gpr .x3).toNat ≤ (s.gpr .x1).toNat
  hs : 16 * (s.gpr .x1).toNat ≤ (stackArg s 2).toNat

theorem preV_of {K : Nat} {s : State}
    (h : (Spec.RsaPkcs1Sig.verifyContract abi (stk K)).pre s) : PreV K s := by
  have e : stk K = (frameBytes + K - 1) + 1 := by unfold stk frameBytes; omega
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Sig.verifyContract, Spec.RsaPkcs1Sig.verifySig, abi, argRegs, stackArgs_three,
    List.append_eq] at h
  sig_pre [Spec.RsaPkcs1Sig.verifyContract, Spec.RsaPkcs1Sig.verifySig, abi, argRegs, stackArgs_three,
    List.append_eq] at h
  obtain ⟨sp1, sp2, hrd, hwr, ns, es, ds, gs, sa, kn, ke, kd, kg, ks, ka, wn, we, wd, wg, ws, ⟨k1, k2⟩,
    e1, e2, hs⟩ := h
  rw [← e] at sp1 kn ke kd kg ks ka
  exact ⟨sp1, sp2, hrd, hwr, ns, es, ds, gs, sa, kn, ke, kd, kg, ks, ka, wn, we, wd, wg, ws, k1, k2, e1, e2,
    by unfold Spec.Rsa.scratchWords at hs; omega⟩

end VG.Proof.RsaPkcs1Sig.AArch64.Ver
