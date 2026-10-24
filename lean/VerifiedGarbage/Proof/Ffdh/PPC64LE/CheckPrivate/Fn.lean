module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.CheckPrivate
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# `vg_ffdh_check_private` on PPC64LE: the function

`vg_ffdh_check_private(domain = r3, domain_len = r4, p_len = r5, y = r6,
y_len = r7, x = r8, x_len = r9, scratch = r10, scratch_len)`, the last on the
stack (`kpContract`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.CheckPrivate

open VG VG.PPC64LE

/-- The argument on the stack: `scratch_len`. -/
abbrev kpStack (s : State) : Region := ⟨stackArgAddr s 0, 8⟩

/-- What timing may depend on: the domain, y and the status. -/
def kpLeak (s : State) : List Nat :=
  let dom := Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat
  let yB := Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat
  dom.map (·.toNat) ++ yB.map (·.toNat) ++ [Spec.Ffdh.privateStatus (Spec.Ffdh.domainOf (s.gpr .r5).toNat dom)
    (Spec.Rsa.os2ip yB) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat))]

/-- `vg_ffdh_check_private`, on the registers and the stack. -/
def kpContract : Contract isa where
  pre s :=
    let dom : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let y : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
    let x : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let scr : Region := ⟨s.gpr .r10, (stackArg s 0).toNat * 8⟩
    s.sp.toNat + 32 + 8 * 9 ≤ 2 ^ 64 ∧ s.rd = [dom, y, x, kpStack s] ∧ s.wr = [scr] ∧
      dom.Disjoint scr ∧ y.Disjoint scr ∧ x.Disjoint scr ∧ scr.Disjoint (kpStack s) ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (s.gpr .r10).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Ffdh.pLenValid (s.gpr .r5).toNat ∧ Spec.Ffdh.domainLenValid (s.gpr .r5).toNat (s.gpr .r4).toNat ∧
      (s.gpr .r7).toNat = (s.gpr .r5).toNat ∧ 1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ (s.gpr .r5).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .r5).toNat ≤ (stackArg s 0).toNat
  post s t :=
    let dom := Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat
    Spec.Ffdh.domainValid (s.gpr .r5).toNat dom = true →
      ((t.gpr .r3).setWidth 32).toNat = Spec.Ffdh.privateStatus (Spec.Ffdh.domainOf (s.gpr .r5).toNat dom)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat))
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat))
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .r10 = s₂.gpr .r10 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ kpLeak s₁ = kpLeak s₂

end VG.Proof.Ffdh.PPC64LE.CheckPrivate
