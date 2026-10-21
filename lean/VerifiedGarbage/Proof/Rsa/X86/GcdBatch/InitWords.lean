module

public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Mont.X86.Ops
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Rsa.KeyBits32

/-! # Zero extension and the branchless odd-input mask -/

@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.GcdBatch
  VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass.X86

 theorem copyExtend_ok {s : State} {base : Addr} {size n dst src : Nat}
    (hs : Scr s base size) (hd : dst+4*(n+1) ≤ size) (ha : src+4*n ≤ size)
    (sep : dst ≤ src ∨ src+4*n ≤ dst) :
    WP isa (.block (copyExtend n dst src)) s fun z =>
      val32 z.mem base dst (n+1) = val32 s.mem base src n ∧
      Keeps [.eax] s z ∧ Outside base dst (4*(n+1)) s.mem z.mem := by
  have nowrap := hs.nowrap
  unfold copyExtend
  refine WP.block_append (WP.mono (copy_ok n hs (by omega) ha sep) fun s₁ ⟨V₁,K₁,O₁⟩ => ?_)
  refine WP.mono (zeros_ok (hs.of_keeps K₁ (by decide)) (acc:=dst+4*n) (k:=1) (by omega))
    fun z ⟨O₂,V₂,K₂⟩ => ⟨?_,K₁.trans K₂,?_⟩
  · simp only [val32,Nat.mul_zero,Nat.add_zero] at V₂
    rw [val32_succ,O₂.val32 (by omega) (by omega),V₁]
    change _+2^(32*n)*w32 z.mem base (dst+4*n)=_
    rw [V₂,Nat.mul_zero,Nat.add_zero]
  · intro x hx
    rw [O₂ x (by omega),O₁ x (by omega)]

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
