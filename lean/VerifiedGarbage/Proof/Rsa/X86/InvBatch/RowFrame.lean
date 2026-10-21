module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Inputs
import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Rows
public import Init.Prelude
public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Proof.Weierstrass.Unch

/-! # Matrix-row writes stay in their existing inverse scratch bank -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.Impl.Rsa.X86.InvBatch VG.Proof.Mont VG.Proof.Weierstrass

 theorem fg_cover {base : Addr} {w n row : Nat} {mem mem' : Mem} (_hn : 16≤n) (hw : w=2*n) (hr : row<2)
    (O : Unch base [(offset w 11,4*(n+3)),(offset w 12,4*n),(offset w row,4*(n+1))] mem mem') :
    Unch base (rowWrites w) mem mem' := by
  apply O.cover
  intro r h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl
  · refine ⟨(offset w 11,4*(4*w+8)),by simp [rowWrites],by omega,?_⟩
    dsimp only [offset] at *; omega
  · refine ⟨(offset w 11,4*(4*w+8)),by simp [rowWrites],?_,?_⟩ <;> dsimp only [offset] at * <;> omega
  · refine ⟨(offset w 0,2*(4*w+8)),by simp [rowWrites],?_,?_⟩
    all_goals rcases (show row=0 ∨ row=1 by omega) with rfl | rfl <;> dsimp only [offset] at * <;> omega

 theorem ab_cover {base : Addr} {w n row : Nat} {mem mem' : Mem} (_hn : 16≤n) (hw : w=2*n) (hr : row<2)
    (O : Unch base [(offset w 11,4*(n+2)),(offset w 12,4*(n+1)),
      (offset w 12,4*n),(offset w (13+row),4*n)] mem mem') :
    Unch base (rowWrites w) mem mem' := by
  apply O.cover
  intro r h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  all_goals
    refine ⟨(offset w 11,4*(4*w+8)),by simp [rowWrites],?_,?_⟩
    all_goals rcases (show row=0 ∨ row=1 by omega) with rfl | rfl <;> dsimp only [offset] at * <;> omega

end VG.Proof.Rsa.X86.InvBatch
