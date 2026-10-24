module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Derive
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# `vg_ffdh_derive_public` on PPC64LE: the function

`vg_ffdh_derive_public(y = r3, y_len = r4, domain = r5, domain_len = r6,
p_len = r7, x = r8, x_len = r9, scratch = r10, scratch_len)`, the last on the
stack (`dpContract`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Derive

open VG VG.PPC64LE

/-- The argument on the stack: `scratch_len`. -/
abbrev dpStack (s : State) : Region := ⟨stackArgAddr s 0, 8⟩

/-- What timing may depend on: the domain and the status. -/
def dpLeak (s : State) : List Nat :=
  let dom := Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat
  dom.map (·.toNat) ++ [Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf (s.gpr .r7).toNat dom)
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat))]

/-- `vg_ffdh_derive_public`, on the registers and the stack. -/
def dpContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let dom : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let x : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let scr : Region := ⟨s.gpr .r10, (stackArg s 0).toNat * 8⟩
    s.sp.toNat + 32 + 8 * 9 ≤ 2 ^ 64 ∧ s.rd = [dom, x, dpStack s] ∧ s.wr = [out, scr] ∧
      out.Disjoint dom ∧ out.Disjoint x ∧ out.Disjoint scr ∧ out.Disjoint (dpStack s) ∧
      dom.Disjoint scr ∧ x.Disjoint scr ∧ scr.Disjoint (dpStack s) ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (s.gpr .r10).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Ffdh.pLenValid (s.gpr .r7).toNat ∧ Spec.Ffdh.domainLenValid (s.gpr .r7).toNat (s.gpr .r6).toNat ∧
      (s.gpr .r4).toNat = (s.gpr .r7).toNat ∧ 1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ (s.gpr .r7).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .r7).toNat ≤ (stackArg s 0).toNat
  post s t :=
    let dom := Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat
    let a := Spec.Ffdh.domainOf (s.gpr .r7).toNat dom
    let x := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
    Spec.Ffdh.domainValid (s.gpr .r7).toNat dom = true →
      ((t.gpr .r3).setWidth 32).toNat = Spec.Ffdh.keyStatus a x ∧
        if Spec.Ffdh.keyStatus a x = 1 then
          Spec.Rsa.bytesAt t.mem (s.gpr .r3) (s.gpr .r7).toNat =
            Spec.Rsa.i2osp (Spec.Rsa.powMod a.g x a.p) (s.gpr .r7).toNat
        else Spec.Rsa.bytesAt t.mem (s.gpr .r3) (s.gpr .r7).toNat = List.replicate (s.gpr .r7).toNat 0
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .r10 = s₂.gpr .r10 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ dpLeak s₁ = dpLeak s₂

end VG.Proof.Ffdh.PPC64LE.Derive
