module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.General
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GeneralFrame
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Calls
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.General

/-! Both buffer layouts use the same general record body and timing proof. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous

open VG VG.AArch64 DirectGather
open VG.Impl.AesGcm.AArch64.Contiguous

theorem general_ok (v : GcmImpl)
    (raw : Verified target (Impl.AesGcm.AArch64.DirectGather.framed v.calls) sharedGatherContract) {o : State} (c : Caller o)
    (keeps : (generalFrame v.calls).allInstrs keepsV = true)
    (depth : 16*(VG.Impl.AesGcm.AArch64.DirectGather.framed v.calls).aarch64Depth < 2^64) :
    WP isa (generalFrame v.calls) o fun u => abiPreserved o u ∧ result o u := by
  apply WP.withPreservedV (hc := keeps)
  apply WP.alloc (by decide) (by have := c.room; omega)
  refine WP.seq ((enter o c).mono ?_)
  intro t h
  obtain ⟨rd,wr⟩ := h.covers c
  refine WP.narrowF (raw.1 _ (h.pre c)) rd wr ?_ depth
  intro u _ _ sp _ ⟨abi,post⟩ m v fr
  refine ⟨⟨?_,?_⟩,result_frame c (by decide) (h.post c post) fr⟩
  · intro r hr
    have keep : ∀ q ∈ preserved, q ∉ [.x6,.x7,.x9,.x10] := by decide
    exact (abi.1 r hr).trans (h.regs r (keep r hr))
  · change u.sp+48#64=o.sp
    rw [sp,h.sp]; exact BitVec.sub_add_cancel _ _

theorem general_rel (v : GcmImpl)
    (raw : Verified target (Impl.AesGcm.AArch64.DirectGather.framed v.calls) sharedGatherContract) {a b : State} (ca : Caller a) (cb : Caller b)
    (pub : onePub 3 a b) (dit : a.dit=b.dit) :
    RelCT isa (Eq2 a b) (generalFrame v.calls) TT := by
  have sp := pub.2.2.2.2.2.2.2.2.1
  apply RelCT.alloc (R := TT)
  suffices body : RelCT isa (Eq2 (allocated 48 a) (allocated 48 b)) _ TT from
    body.mono (by rintro x y ⟨_,_,⟨rfl,rfl⟩,rfl,rfl⟩; exact ⟨rfl,rfl⟩) (fun _ _ h => h)
  have asp : (allocated 48 a).sp = (allocated 48 b).sp := by simp only [allocated,sp]
  refine rel_seq (rel_taint [] asp (by simp) ⟨_,by taint_decide⟩) (enter a ca) (enter b cb) ?_
  intro t u ht hu
  obtain ⟨tr,tw⟩ := ht.covers ca
  obtain ⟨ur,uw⟩ := hu.covers cb
  rintro _ _ τ υ _ _ ⟨rfl,rfl⟩ et eu
  obtain ⟨x,hx⟩ := trace_narrow raw.1 (ht.pre ca) tr tw et
  obtain ⟨y,hy⟩ := trace_narrow raw.1 (hu.pre cb) ur uw eu
  exact ⟨raw.2.1 _ _ _ _ _ _ (ht.pre ca) (hu.pre cb) (ht.public hu pub dit) hx hy,trivial⟩

end VG.Proof.AesGcm.AArch64.Contiguous
