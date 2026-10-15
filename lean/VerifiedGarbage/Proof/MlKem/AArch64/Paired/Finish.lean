module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Restore
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraPair
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Complete paired samples and restore the enclosing matrix loop -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

def finishCode : Prog isa := .seq
  (.ite (.zero .x .x6) Impl.MlKem.AArch64.Paired.extraPair (.block []))
  (.block (Impl.MlKem.AArch64.Paired.saved.zipIdx.reverse.map fun (r,i)=>
    .ldr .x r .x19 (1800+8*i)))

structure PairPost (A B : Spec.Sha3.State) (p a b : Addr) (s t : State) : Prop where
  keep : Keep pairRegs s t
  frame : Frame (stepWrites p a b) s.mem t.mem
  left : CoeffsUpTo t.mem a (accepted A 5).length (Sample.cv (accepted A 5)) (fun _=>0)
  reducedLeft : Reduced t.mem a
  right : CoeffsUpTo t.mem b (accepted B 5).length (Sample.cv (accepted B 5)) (fun _=>0)
  reducedRight : Reduced t.mem b
  status : t.gpr .x24=s.gpr .x24 &&& BitVec.ofNat 64
    (if (accepted A 5).length=256 ∧ (accepted B 5).length=256 then 1 else 0)

theorem finish_ok {A B : Spec.Sha3.State} {p a b c : Addr} {initial s : State}
    (hk : Keep pairWorkingRegs initial s) (hm : Frame (stepWrites p a b) initial.mem s.mem)
    (sv : Noise.Saved p initial s.mem) (h : Progress A B 3 p a b c s)
    (sy : s.syms "VG_MLKEM_REJ_SHUFFLE"=c)
    (hf : (s.gpr .x6).toNat=if (accepted A 3).length=256 ∧ (accepted B 3).length=256 then 1 else 0)
    (hs : s.gpr .x24=initial.gpr .x24) (hb : initial.gpr .x24=0 ∨ initial.gpr .x24=1) :
    WP isa finishCode s (PairPost A B p a b initial) := by
  refine WP.seq (WP.mono (finish_branch (fun _ ht st=>advance_ok ht st) h sy hf (by rw [hs]; exact hb))
    fun t ht=>?_)
  have kt : Keep pairWorkingRegs initial t := (hk.trans ht.keep).mono (by decide)
  have fine : Frame (stepWrites p a b) s.mem t.mem := ht.frame.sub (by
    intro r hr
    simp only [resumeWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact ⟨⟨p,2048⟩,by simp [stepWrites],Region.sub_prefix (by decide : 1712≤2048)⟩
    · exact ⟨polyRegion a,by simp [stepWrites],fun _ h=>h⟩
    · exact ⟨polyRegion b,by simp [stepWrites],fun _ h=>h⟩)
  have ft := hm.trans fine
  refine WP.mono (restore_ok kt (by rw [ht.keep.get .x19]; exact h.ptr)
    (ht.saved h.context sv) (by rw [ht.keep.wr]; exact h.context.scratch)) fun u ⟨ku,mu,u24⟩=>?_
  refine ⟨ku,?_,?_,?_,?_,?_,?_⟩
  · rw [mu]; exact ft
  · rw [mu]; exact ht.left
  · rw [mu]; exact ht.reducedLeft
  · rw [mu]; exact ht.right
  · rw [mu]; exact ht.reducedRight
  · rw [u24,ht.status,hs]

end VG.Proof.MlKem.AArch64.Paired
