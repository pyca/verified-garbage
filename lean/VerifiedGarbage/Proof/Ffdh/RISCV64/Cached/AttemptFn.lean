module

public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# `vg_ffdh_generate_key_cached` on RISC-V: the function

`vg_ffdh_generate_key_cached(x = a0, x_len = a1, y = a2, y_len = a3,
domain = a4, domain_len = a5, p_len = a6, rand = a7, rand_len, scratch,
scratch_len, ctx, ctx_len)`, the last five on the stack (`cgContract`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Cached

open VG VG.RISCV64

/-- The arguments on the stack: `rand_len`, `scratch`, `scratch_len`, `ctx`
and `ctx_len`. -/
abbrev cgStack (s : State) : Region := ⟨stackArgAddr s 0, 40⟩

/-- The domain's bytes. -/
abbrev cgDom (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat

/-- The parameters. -/
abbrev cgA (s : State) : Spec.Ffdh.Parameters := Spec.Ffdh.domainOf (s.gpr .a6).toNat (cgDom s)

/-- The scalar of an attempt: `rand` cut to the context's width. -/
abbrev cgScalar (s : State) : Nat :=
  Spec.Ffdh.vettedScalarOfOctets (cgA s) (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat)

/-- What timing may depend on: the domain and the status. -/
def cgLeak (s : State) : List Nat :=
  (cgDom s).map (·.toNat) ++ [Spec.Ffdh.keyStatus (cgA s) (cgScalar s)]

/-- `vg_ffdh_generate_key_cached`, on the registers and the stack. -/
def cgContract : Contract isa where
  pre s :=
    let x : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let y : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let dom : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
    let rand : Region := ⟨s.gpr .a7, (stackArg s 0).toNat⟩
    let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
    let ctx : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
    s.rd = [dom, rand, ctx, cgStack s] ∧ s.wr = [x, y, scr] ∧
      x.Disjoint y ∧ x.Disjoint dom ∧ x.Disjoint rand ∧ x.Disjoint scr ∧ x.Disjoint ctx ∧ x.Disjoint (cgStack s) ∧
      y.Disjoint dom ∧ y.Disjoint rand ∧ y.Disjoint scr ∧ y.Disjoint ctx ∧ y.Disjoint (cgStack s) ∧
      dom.Disjoint scr ∧ rand.Disjoint scr ∧ scr.Disjoint ctx ∧ scr.Disjoint (cgStack s) ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧ (s.gpr .a7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
      (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Ffdh.pLenValid (s.gpr .a6).toNat ∧ Spec.Ffdh.domainLenValid (s.gpr .a6).toNat (s.gpr .a5).toNat ∧
      (s.gpr .a1).toNat = (s.gpr .a6).toNat ∧ (s.gpr .a3).toNat = (s.gpr .a6).toNat ∧
      (stackArg s 0).toNat = (s.gpr .a6).toNat ∧ Spec.Rsa.scratchWords (s.gpr .a6).toNat ≤ (stackArg s 2).toNat ∧
      Spec.Ffdh.domainValid (s.gpr .a6).toNat (cgDom s) ∧
      Spec.Ffdh.generationContextAt s.mem (stackArg s 3) (stackArg s 4).toNat (s.gpr .a6).toNat (cgDom s) ∧
      (stackArg s 1).toNat % 8 = 0 ∧ (stackArg s 3).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s t :=
    let a := cgA s
    let x := cgScalar s
    ((t.gpr .a0).setWidth 32).toNat = Spec.Ffdh.keyStatus a x ∧
      if Spec.Ffdh.keyStatus a x = 1 then
        Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a6).toNat = Spec.Rsa.i2osp x (s.gpr .a6).toNat ∧
          Spec.Rsa.bytesAt t.mem (s.gpr .a2) (s.gpr .a6).toNat =
            Spec.Rsa.i2osp (Spec.Rsa.powMod a.g x a.p) (s.gpr .a6).toNat
      else Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a6).toNat = List.replicate (s.gpr .a6).toNat 0 ∧
        Spec.Rsa.bytesAt t.mem (s.gpr .a2) (s.gpr .a6).toNat = List.replicate (s.gpr .a6).toNat 0
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ cgLeak s₁ = cgLeak s₂ ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
      s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
      s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3 ∧
      stackArg s₁ 4 = stackArg s₂ 4

end VG.Proof.Ffdh.RISCV64.Cached
