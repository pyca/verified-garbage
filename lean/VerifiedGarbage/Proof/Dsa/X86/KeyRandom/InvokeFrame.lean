module

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckInvoke
import VerifiedGarbage.Proof.Framework.Offset

/-! Returning from either internal invocation restores the sampler's ready state. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.Proof.Mont

theorem Ready.returned {s₀ t u : State} (R : Ready s₀ t) (rd : u.rd=t.rd) (wr : u.wr=t.wr)
    (sp : u.gpr .esp=t.gpr .esp) (F : Frame (rWrites s₀) t.mem u.mem) : Ready s₀ u :=
  ⟨⟨by rw [sp]; exact R.rf.esp, by rw [wr]; exact R.rf.wr, by rw [wr]; exact R.rf.args,
    R.rf.nowrap⟩,rd.trans R.rd,wr.trans R.wr,R.frame.trans F⟩

theorem deriveFrame_outer {s₀ : State} {m m' : Mem} (F : Frame (callWrites s₀) m m') :
    Frame (rWrites s₀) m m' := by
  apply F.sub
  intro r hr
  simp only [callWrites,callWr,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact ⟨_,by simp [rWrites,rOut],fun _ h => h⟩
  · exact ⟨_,by simp [rWrites,rScratch],fun _ h => h⟩
  · exact ⟨rStack s₀,by simp [rWrites],stk_sub s₀ (by decide)⟩
  · refine ⟨rStack s₀,by simp [rWrites],?_⟩
    have H := Offset.sub_base (rLow s₀) (d := 0) (n := 24) (k := 144) (by decide)
    rwa [BitVec.add_zero] at H

theorem checkFrame_outer {s₀ : State} {m m' : Mem} (F : Frame (CheckCall.callWrites s₀) m m') :
    Frame (rWrites s₀) m m' := by
  apply F.sub
  intro r hr
  simp only [CheckCall.callWrites,CheckCall.callWr,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact ⟨_,by simp [rWrites,rScratch],fun _ h => h⟩
  · exact ⟨rStack s₀,by simp [rWrites],stk_sub s₀ (by decide)⟩
  · refine ⟨rStack s₀,by simp [rWrites],?_⟩
    have H := Offset.sub_base (rLow s₀) (d := 0) (n := 24) (k := 144) (by decide)
    rwa [BitVec.add_zero] at H

theorem invocation_below {s₀ t : State} (A : KeyABI s₀) (R : Ready s₀ t) :
    below (t.gpr .esp) 24=⟨rLow s₀,24⟩ := by
  have low : 24≤(t.gpr .esp).toNat := by have := esp_toNat A R; omega
  apply congrArg (fun base => Region.mk base 24)
  rw [Taint.sub_setWidth low,R.rf.esp]
  unfold rBase off
  bv_omega

end VG.Proof.Dsa.X86.KeyRandom
