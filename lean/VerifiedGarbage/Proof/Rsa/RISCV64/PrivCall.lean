module

public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivPre
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# Calling `vg_rsa_private_checked` on RISC-V

Untrusted: everything here is checked by Lean. For its callers' proofs: the
shared contract's precondition from the facts by name (`pre_of_preP`, the
converse of `preP_of`), and its public data from the facts a caller fixes
(`pub_of`), as on PPC64LE (`Proof/Rsa/PPC64LE/PrivPre.lean`,
`Proof/Rsa/PPC64LE/PrivCT.lean`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Priv

open VG VG.RISCV64 VG.Impl.Rsa.RISCV64.Priv

theorem pre_of_preP {s : State} (h : PreP s) :
    (Spec.Rsa.privateCheckedContract RISCV64.abi frameBytes).pre s := by
  obtain ⟨sp16, sp1, sp2, hrd, hwr, on, oe, oi, op, oq, odp, odq, oqi, os, oa, ns, es, is, ps, qs, dps, dqs, qis, sa,
    ko, kn, ke, ki, kp, kq, kdp, kdq, kqi, ks, ka, wo, wn, we, wi, wp, wq, wdp, wdq, wqi, ws, k1, k2, h1, h7, e1,
    e2, p1, p2, q1, q2, h5, h9, h7', hs, al⟩ := h
  have e : frameBytes = 3247 + 1 := rfl
  rw [e]
  sig_pre [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_twelve, List.append_eq, List.range, List.range.loop]
  exact ⟨sp16, sp1, sp2, hrd, hwr, on, oe, oi, op, oq, odp, odq, oqi, os, oa, ns, es, is, ps,
    qs, dps, dqs, qis, sa, ko, kn, ke, ki, kp, kq, kdp, kdq, kqi, ks, ka, wo, wn, we, wi, wp, wq, wdp, wdq, wqi,
    ws, ⟨k1, k2⟩, h1, h7, e1, e2, p1, p2, q1, q2, h5, h9, h7', hs, al⟩

/-- The public data of `vg_rsa_private_checked`'s contract, from its facts. -/
theorem pub_of {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp) (hr : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r)
    (ha : ∀ i < 12, stackArg s₁ i = stackArg s₂ i)
    (hn : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a2) (s₁.gpr .a3).toNat =
      Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a2) (s₂.gpr .a3).toNat)
    (he : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a4) (s₁.gpr .a5).toNat =
      Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a4) (s₂.gpr .a5).toNat) :
    (Spec.Rsa.privateCheckedContract RISCV64.abi frameBytes).pub s₁ s₂ := by
  have e : frameBytes = 3247 + 1 := rfl
  rw [e]
  sig_pub [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_twelve, List.append_eq]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  exact ⟨hsp, by rw [hn, he], hr .a0 (by decide), hr .a1 (by decide), hr .a2 (by decide), hr .a3 (by decide),
    hr .a4 (by decide), hr .a5 (by decide), hr .a6 (by decide), hr .a7 (by decide), ha 0 (by decide),
    ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide), ha 5 (by decide), ha 6 (by decide),
    ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide), ha 11 (by decide)⟩

end VG.Proof.Rsa.RISCV64.Priv
