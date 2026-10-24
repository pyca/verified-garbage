module

import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeBody
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# `vg_ffdh_exchange` on PPC64LE: the function

`vg_ffdh_exchange(out = r3, out_len = r4, domain = r5, domain_len = r6,
p_len = r7, x = r8, x_len = r9, peer = r10, peer_len, scratch, scratch_len)`,
the last three on the stack (`exContract`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Domain

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain

/-- The arguments on the stack: `peer_len`, `scratch` and `scratch_len`. -/
abbrev exStack (s : State) : Region := ⟨stackArgAddr s 0, 24⟩

/-- What timing may depend on: the domain, the peer and the status. -/
def exLeak (s : State) : List Nat :=
  let dom := Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat
  let yB := Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat
  dom.map (·.toNat) ++ yB.map (·.toNat) ++
    [if (Spec.Ffdh.exchangeOp (Spec.Ffdh.domainOf (s.gpr .r7).toNat dom)
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)) (Spec.Rsa.os2ip yB)).isSome then 1 else 0]

/-- `vg_ffdh_exchange`, on the registers and the stack. -/
def exContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let dom : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let x : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let peer : Region := ⟨s.gpr .r10, (stackArg s 0).toNat⟩
    let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
    s.sp.toNat + 32 + 8 * 11 ≤ 2 ^ 64 ∧ s.rd = [dom, x, peer, exStack s] ∧ s.wr = [out, scr] ∧
      out.Disjoint dom ∧ out.Disjoint x ∧ out.Disjoint peer ∧ out.Disjoint scr ∧ out.Disjoint (exStack s) ∧
      dom.Disjoint scr ∧ x.Disjoint scr ∧ peer.Disjoint scr ∧ scr.Disjoint (exStack s) ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (s.gpr .r10).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Ffdh.pLenValid (s.gpr .r7).toNat ∧ Spec.Ffdh.domainLenValid (s.gpr .r7).toNat (s.gpr .r6).toNat ∧
      (s.gpr .r4).toNat = (s.gpr .r7).toNat ∧ (stackArg s 0).toNat = (s.gpr .r7).toNat ∧
      1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ (s.gpr .r7).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .r7).toNat ≤ (stackArg s 2).toNat
  post s t :=
    let dom := Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat
    let a := Spec.Ffdh.domainOf (s.gpr .r7).toNat dom
    let y := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat)
    Spec.Ffdh.domainValid (s.gpr .r7).toNat dom = true → Spec.Ffdh.publicValid ⟨a, y⟩ = true →
      Spec.Rsa.written t.mem (s.gpr .r3) (s.gpr .r4).toNat ((t.gpr .r3).setWidth 32)
        (Spec.Ffdh.exchangeOp a (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)) y)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .r10 = s₂.gpr .r10 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
      stackArg s₁ 2 = stackArg s₂ 2 ∧
      exLeak s₁ = exLeak s₂

end VG.Proof.Ffdh.PPC64LE.Domain
