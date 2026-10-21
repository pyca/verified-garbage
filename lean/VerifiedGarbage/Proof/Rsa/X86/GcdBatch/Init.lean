module

public import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.InitWords
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInput
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.X86.InvShift
import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
import VerifiedGarbage.Proof.Weierstrass.X86.InvHalf
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog

/-! # Initializing the signed RSA GCD operands -/

@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.GcdBatch
  VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Inv

local macro "apart" : tactic => `(tactic| (dsimp only [offset] at *; omega))

def initWrites (n : Nat) : List (Nat × Nat) :=
 [(offset n 3,3*(4*n+8)),(offset n 13,4*n+8)]

theorem init_ok {s : State} {base : Addr} {size n : Nat}
    (hs : Scr s base size) (hn : 16 ≤ n) (hz : offset n 15 ≤ size) :
    WP isa (.block (init n)) s fun z =>
      val32 z.mem base (offset n 4) (n+1) = val32 s.mem base (offset n 8) n ∧
      val32 z.mem base (offset n 5) (n+1) =
        VG.Proof.Rsa.Divstep.oddInput (val32 s.mem base (offset n 8) n) (val32 s.mem base (offset n 0) n) ∧
      w32 z.mem base (offset n 3) = 1 ∧ Keeps [.eax,.ecx] s z ∧ Unch base (initWrites n) s.mem z.mem := by
  have nowrap := hs.nowrap
  unfold init
  refine WP.block_append (WP.block_append (WP.block_append (WP.block_append
    (WP.block_append (WP.block_append (WP.mono
    (copyExtend_ok hs (n:=n) (dst:=offset n 4) (src:=offset n 8) (by apart) (by apart) (by apart))
    fun s₁ ⟨F₁,K₁,O₁⟩ => ?_))))))
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.mono (copyExtend_ok hs₁ (n:=n) (dst:=offset n 5) (src:=offset n 0)
    (by apart) (by apart) (by apart)) fun s₂ ⟨G₂,K₂,O₂⟩ => ?_
  rw [O₁.val32 (by apart) (by apart)] at G₂
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  refine WP.mono (evenMask_ok hs₂ (src:=offset n 0) (by apart)) fun s₃ ⟨C₃,K₃,M₃⟩ => ?_
  rw [O₂.w32 (by apart) (by apart),O₁.w32 (by apart) (by apart)] at C₃
  let c := decide (w32 s.mem base (offset n 0)%2=0)
  have C : s₃.gpr .ecx = if c then BitVec.allOnes 32 else 0 := by
    simpa only [c,decide_eq_true_eq] using C₃
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  refine WP.mono (maskCopy_ok c n hs₃ C (o:=offset n 13) (a:=offset n 8)
    (by apart) (by apart) (by apart)) fun s₄ ⟨T₄,K₄,O₄⟩ => ?_
  rw [M₃,O₂.val32 (by apart) (by apart),O₁.val32 (by apart) (by apart)] at T₄
  have hs₄ := hs₃.of_keeps K₄ (by decide)
  refine WP.mono (zeros_ok hs₄ (acc:=offset n 13+4*n) (k:=1) (by apart)) fun s₅ ⟨O₅,T₅,K₅⟩ => ?_
  have Tval : val32 s₅.mem base (offset n 13) (n+1) =
      if c then val32 s.mem base (offset n 8) n else 0 := by
    simp only [val32,Nat.mul_zero,Nat.add_zero] at T₅
    rw [val32_succ,O₅.val32 (by apart) (by apart),T₄,T₅,Nat.mul_zero,Nat.add_zero]
  have Gval : val32 s₅.mem base (offset n 5) (n+1) = val32 s.mem base (offset n 0) n := by
    rw [O₅.val32 (by apart) (by apart),O₄.val32 (by apart) (by apart),M₃,G₂]
  have hs₅ := hs₄.of_keeps K₅ (by decide)
  rw [addInPlace_eq]
  refine WP.mono (chainAddSelf_ok hs₅ n (acc:=offset n 5) (b:=offset n 13)
    (by apart) (by apart) (by apart)) fun s₆ ⟨O₆,⟨carry,_,V₆⟩,K₆⟩ => ?_
  rw [Tval,Gval] at V₆
  have xp := val32_lt s.mem base (offset n 0) n
  have mp := val32_lt s.mem base (offset n 8) n
  have sumBound : val32 s.mem base (offset n 0) n +
      (if c then val32 s.mem base (offset n 8) n else 0) < 2^(32*(n+1)) := by
    rw [pow32_succ]
    split <;> omega
  have carry0 : carry=false := by
    cases carry <;> simp_all only [Bool.toNat_true,Bool.toNat_false,Nat.mul_one,Nat.mul_zero,Nat.add_zero]
    omega
  rw [carry0] at V₆
  simp only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at V₆
  have inputLow : val32 s.mem base (offset n 0) n % 2 = w32 s.mem base (offset n 0)%2 := by
    obtain ⟨k,hk⟩ : ∃ k,n=k+1 := ⟨n-1,by omega⟩
    rw [hk,val32]
    omega
  have hs₆ := hs₅.of_keeps K₆ (by decide)
  refine WP.mono (setWord_ok (dst:=offset n 3) 1 hs₆ (by apart)) fun z ⟨D₇,K₇,O₇⟩ => ?_
  refine ⟨?_,?_,D₇,?_,?_⟩
  · rw [O₇.val32 (by apart) (by apart),O₆.val32 (by apart) (by apart),
      O₅.val32 (by apart) (by apart),O₄.val32 (by apart) (by apart),M₃,
      O₂.val32 (by apart) (by apart),F₁]
  · rw [O₇.val32 (by apart) (by apart),V₆]
    simp only [VG.Proof.Rsa.Divstep.oddInput,c,decide_eq_true_eq,inputLow]
  · have Kstart : Keeps [.eax,.ecx] s s₁ := K₁.mono (by decide)
    exact (((((Kstart.trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans
      (K₄.mono (by decide))).trans (K₅.mono (by decide))).trans (K₆.mono (by decide))).trans (K₇.mono (by decide))
  · intro x hx
    have hx3 := hx (offset n 3,3*(4*n+8)) (by simp [initWrites])
    have hx13 := hx (offset n 13,4*n+8) (by simp [initWrites])
    rw [O₇ x (by apart),O₆ x (by apart),O₅ x (by apart),O₄ x (by apart),M₃,
      O₂ x (by apart),O₁ x (by apart)]

end VG.Proof.Rsa.X86.GcdBatch
