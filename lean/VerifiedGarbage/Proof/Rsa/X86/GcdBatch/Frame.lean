module

public import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.FrameBase
public import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Init
public import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Batch
public import Init.Prelude
public import VerifiedGarbage.Proof.Mont.Words

/-! # The batched GCD stays within the existing inverse bank -/

@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.Impl.Rsa.X86.GcdBatch VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Rsa.X86.Keys


theorem init_own {base : Addr} {n : Nat} {m m' : Mem} (h : Unch base (initWrites n) m m') :
    Unch base (ownRanges n) m m' := by
  apply h.cover
  intro w hw
  simp only [initWrites,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl
  · refine ⟨(offset n 0,8*(4*n+8)),by simp [ownRanges],?_,?_⟩ <;> dsimp only [offset] <;> omega
  · refine ⟨(offset n 11,4*(4*n+8)),by simp [ownRanges],?_,?_⟩ <;> dsimp only [offset] <;> omega

theorem batch_own {base : Addr} {n : Nat} {m m' : Mem} (h : Unch base (batchWrites n) m m') :
    Unch base (ownRanges n) m m' := by
  apply h.cover
  intro w hw
  simp only [batchWrites,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl
  · refine ⟨(offset n 0,8*(4*n+8)),by simp [ownRanges],?_,?_⟩ <;> dsimp only [offset] <;> omega
  · refine ⟨(offset n 11,4*(4*n+8)),by simp [ownRanges],?_,?_⟩ <;> dsimp only [offset] <;> omega
  · exact ⟨(100,4),by simp [ownRanges],by decide,by decide⟩

theorem result_own {base : Addr} {n : Nat} {m m' : Mem} (h : Outside base (offset n 1) (4*n) m m') :
    Unch base (ownRanges n) m m' := by
  apply h.unch.cover
  intro w hw
  rw [List.mem_singleton] at hw
  subst w
  refine ⟨(offset n 0,8*(4*n+8)),by simp [ownRanges],?_,?_⟩ <;> dsimp only [offset] <;> omega

end VG.Proof.Rsa.X86.GcdBatch
