module
public import VerifiedGarbage.Proof.Rsa.X86.InvBatch.State
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
public import VerifiedGarbage.Proof.Mont.Words
/-! # A counter store preserves the encoded inversion state -/
@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.Impl.Rsa.X86.InvBatch VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass.X86.Inv
local macro "apart" : tactic => `(tactic| (dsimp only [offset] at *; omega))
 theorem StateAt.keep_counter {s t : State} {base : Addr} {size w n p iv : Nat} {st : VG.Proof.Divstep.W32.IState}
    (h : StateAt w n base p iv st s) (hs : Scr s base size) (_hn : 16≤n) (hw : w=2*n) (hz : offset w 15≤size)
    (O : Outside base 100 4 s.mem t.mem) : StateAt w n base p iv st t := by
  have nowrap := hs.nowrap
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [read32_unch O.unch (by intro r hr; rw [List.mem_singleton.mp hr]; apart) (by apart)]
    exact h.d
  · rw [O.val32 (by apart) (by apart)]; exact h.modulus
  · rw [O.w32 (by apart) (by apart)]; exact h.inverse
  · rw [O.val32 (by apart) (by apart)]; exact h.f
  · rw [O.val32 (by apart) (by apart)]; exact h.g
  · rw [O.val32 (by apart) (by apart)]; exact h.a
  · rw [O.val32 (by apart) (by apart)]; exact h.b
  · rw [O.w32 (by apart) (by apart)]; exact h.aTop
  · rw [O.w32 (by apart) (by apart)]; exact h.bTop

end VG.Proof.Rsa.X86.InvBatch
