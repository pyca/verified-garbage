module

public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Ops
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Rsa.KeyBits32
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! # The branchless odd-input mask -/

@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.GcdBatch
  VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass.X86

theorem evenMask_eq (x : BitVec 32) :
    (x &&& 1)-1 = if x.toNat % 2 = 0 then BitVec.allOnes 32 else 0 := by
  have h := VG.Proof.Rsa.KeyBits32.bv_and_one x
  rcases Nat.mod_two_eq_zero_or_one x.toNat with e | e
  · have z : x &&& 1 = 0 := BitVec.eq_of_toNat_eq (h.trans e)
    rw [z,e]; rfl
  · have z : x &&& 1 = 1 := BitVec.eq_of_toNat_eq (h.trans e)
    rw [z,e]; rfl

theorem evenMask_ok {s : State} {base : Addr} {size src : Nat}
    (hs : Scr s base size) (hc : src+4 ≤ size) :
    WP isa (.block (evenMask src)) s fun z =>
      z.gpr .ecx = (if w32 s.mem base src % 2 = 0 then BitVec.allOnes 32 else 0) ∧
      Keeps [.ecx] s z ∧ z.mem = s.mem := by
  unfold evenMask
  refine wp_movS (readSrc_sc hs hc) fun s₁ U₁ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₂ U₂ => ?_
  refine wp_subS rfl fun z U₃ _ => WP.block_nil ?_
  refine ⟨?_,(U₁.keeps.trans U₂.keeps).trans U₃.keeps,?_⟩
  · rw [U₃.gpr,U₂.gpr,ite_eq_left rfl,U₁.gpr]
    exact evenMask_eq _
  · rw [U₃.mem,U₂.mem,U₁.mem]

end VG.Proof.Rsa.X86.GcdBatch
