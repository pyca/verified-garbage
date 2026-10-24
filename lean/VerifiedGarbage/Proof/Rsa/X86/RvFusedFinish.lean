module

public import VerifiedGarbage.Proof.Rsa.X86.RvFusedState
public import VerifiedGarbage.Proof.Rsa.X86.RvSquareStep
import VerifiedGarbage.Proof.Rsa.X86.RvOps
import VerifiedGarbage.Proof.Rsa.X86.RvSlots

/-! Moving the saved root to the factor-extraction interface. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

 theorem fusedFinish_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n : Nat}
    {st : VG.Proof.Rsa.Fused.State} (h : FI g s0 A AW V n st s) (count : V sCnt=0) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.fusedFinish s fun t =>
      ∃ z, z<n ∧ (∀ r, st.root=some r → z=r) ∧
        SI g s0 A AW V n 0 0 (z,st.done,st.root.isSome) t := by
  obtain ⟨z,zl,root,h⟩ := h
  unfold VG.Impl.Rsa.X86.RecoverRt.fusedFinish
  refine WP.seq (WP.mono (h.copy_w (o := mY) (a := 0) (by decide) (by decide)
    (by decide) (by decide)) fun u ⟨hu,_,_⟩ => ?_)
  refine wp_movS rfl fun v U _ => ?_
  have hv := hu.of_rest U.keeps (by decide) U.mem
  refine WP.block_append (WP.mono (hv.storeSlot (d := sK) (by decide) .eax) fun t ⟨ht,_,_⟩ => ?_)
  rw [U.gpr,show (0 : BitVec 32).toNat=0 from rfl] at ht
  refine WP.block_nil ⟨z,zl,root,ht.mono (fun j hj => ⟨by revert j; decide,?_⟩)
    (fun j hj => ⟨by simp only [List.mem_singleton] at hj; subst j; decide,rfl⟩)
    (fun d hd => ⟨by revert d; decide,?_⟩)⟩
  · simp only [liveSq,liveM,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · simp only [slotsSq,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | rfl | exact count

end VG.Proof.Rsa.X86.Recover
