module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# `vg_ffdh_exchange` on RISC-V: the function

`vg_ffdh_exchange(out = a0, out_len = a1, domain = a2, domain_len = a3,
p_len = a4, x = a5, x_len = a6, peer = a7, peer_len, scratch, scratch_len)`,
the last three on the stack (`fnContract`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64

open VG VG.RISCV64

/-- The arguments on the stack: `peer_len`, `scratch` and `scratch_len`. -/
abbrev stackArgs (s : State) : Region := ⟨stackArgAddr s 0, 24⟩

/-- What timing may depend on: the domain, the peer and the status. -/
def exLeak (s : State) : List Nat :=
  let dom := Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat
  let yB := Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat
  dom.map (·.toNat) ++ yB.map (·.toNat) ++
    [if (Spec.Ffdh.exchangeOp (Spec.Ffdh.domainOf (s.gpr .a4).toNat dom)
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)) (Spec.Rsa.os2ip yB)).isSome
      then 1 else 0]

/-- `vg_ffdh_exchange`, on the registers and the stack. -/
def fnContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let dom : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let x : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
    let peer : Region := ⟨s.gpr .a7, (stackArg s 0).toNat⟩
    let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
    s.rd = [dom, x, peer, stackArgs s] ∧ s.wr = [out, scr] ∧
      out.Disjoint dom ∧ out.Disjoint x ∧ out.Disjoint peer ∧ out.Disjoint scr ∧ out.Disjoint (stackArgs s) ∧
      dom.Disjoint scr ∧ x.Disjoint scr ∧ peer.Disjoint scr ∧ scr.Disjoint (stackArgs s) ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64 ∧ (s.gpr .a7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Ffdh.pLenValid (s.gpr .a4).toNat ∧ Spec.Ffdh.domainLenValid (s.gpr .a4).toNat (s.gpr .a3).toNat ∧
      (s.gpr .a1).toNat = (s.gpr .a4).toNat ∧ (stackArg s 0).toNat = (s.gpr .a4).toNat ∧
      1 ≤ (s.gpr .a6).toNat ∧ (s.gpr .a6).toNat ≤ (s.gpr .a4).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .a4).toNat ≤ (stackArg s 2).toNat ∧
      (stackArg s 1).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s t :=
    let dom := Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat
    let a := Spec.Ffdh.domainOf (s.gpr .a4).toNat dom
    let y := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat)
    Spec.Ffdh.domainValid (s.gpr .a4).toNat dom = true → Spec.Ffdh.publicValid ⟨a, y⟩ = true →
      Spec.Rsa.written t.mem (s.gpr .a0) (s.gpr .a1).toNat ((t.gpr .a0).setWidth 32)
        (Spec.Ffdh.exchangeOp a (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)) y)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧
      s₁.gpr .a7 = s₂.gpr .a7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
      stackArg s₁ 2 = stackArg s₂ 2 ∧ exLeak s₁ = exLeak s₂

end VG.Proof.Ffdh.RISCV64
