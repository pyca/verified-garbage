module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.GenerateKey
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# `vg_ffdh_generate_key` on PPC64LE: the function

`vg_ffdh_generate_key(x = r3, x_len = r4, y = r5, y_len = r6, domain = r7,
domain_len = r8, p_len = r9, rand = r10, rand_len, scratch, scratch_len)`,
the last three on the stack (`gkContract`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.GenerateKey

open VG VG.PPC64LE

/-- The arguments on the stack: `rand_len`, `scratch` and `scratch_len`. -/
abbrev gkStack (s : State) : Region := ⟨stackArgAddr s 0, 24⟩

/-- The scalar of an attempt: `rand` cut to the bound's bit length. -/
def gkScalar (s : State) : Nat :=
  let dom := Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat
  Spec.Ffdh.scalarOfOctets (Spec.Ffdh.domainOf (s.gpr .r9).toNat dom)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat)

/-- What timing may depend on: the domain and the status. -/
def gkLeak (s : State) : List Nat :=
  let dom := Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat
  dom.map (·.toNat) ++ [Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf (s.gpr .r9).toNat dom) (gkScalar s)]

/-- `vg_ffdh_generate_key`, on the registers and the stack. -/
def gkContract : Contract isa where
  pre s :=
    let x : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let y : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let dom : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
    let rand : Region := ⟨s.gpr .r10, (stackArg s 0).toNat⟩
    let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
    s.sp.toNat + 32 + 8 * 11 ≤ 2 ^ 64 ∧ s.rd = [dom, rand, gkStack s] ∧ s.wr = [x, y, scr] ∧
      x.Disjoint y ∧ x.Disjoint dom ∧ x.Disjoint rand ∧ x.Disjoint scr ∧ x.Disjoint (gkStack s) ∧
      y.Disjoint dom ∧ y.Disjoint rand ∧ y.Disjoint scr ∧ y.Disjoint (gkStack s) ∧
      dom.Disjoint scr ∧ rand.Disjoint scr ∧ scr.Disjoint (gkStack s) ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r10).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Ffdh.pLenValid (s.gpr .r9).toNat ∧ Spec.Ffdh.domainLenValid (s.gpr .r9).toNat (s.gpr .r8).toNat ∧
      (s.gpr .r4).toNat = (s.gpr .r9).toNat ∧ (s.gpr .r6).toNat = (s.gpr .r9).toNat ∧
      (stackArg s 0).toNat = (s.gpr .r9).toNat ∧ Spec.Rsa.scratchWords (s.gpr .r9).toNat ≤ (stackArg s 2).toNat
  post s t :=
    let dom := Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat
    let a := Spec.Ffdh.domainOf (s.gpr .r9).toNat dom
    let x := gkScalar s
    Spec.Ffdh.domainValid (s.gpr .r9).toNat dom = true →
      ((t.gpr .r3).setWidth 32).toNat = Spec.Ffdh.keyStatus a x ∧
        if Spec.Ffdh.keyStatus a x = 1 then
          Spec.Rsa.bytesAt t.mem (s.gpr .r3) (s.gpr .r9).toNat = Spec.Rsa.i2osp x (s.gpr .r9).toNat ∧
            Spec.Rsa.bytesAt t.mem (s.gpr .r5) (s.gpr .r9).toNat =
              Spec.Rsa.i2osp (Spec.Rsa.powMod a.g x a.p) (s.gpr .r9).toNat
        else Spec.Rsa.bytesAt t.mem (s.gpr .r3) (s.gpr .r9).toNat = List.replicate (s.gpr .r9).toNat 0 ∧
          Spec.Rsa.bytesAt t.mem (s.gpr .r5) (s.gpr .r9).toNat = List.replicate (s.gpr .r9).toNat 0
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .r10 = s₂.gpr .r10 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
      stackArg s₁ 2 = stackArg s₂ 2 ∧ gkLeak s₁ = gkLeak s₂

end VG.Proof.Ffdh.PPC64LE.GenerateKey
