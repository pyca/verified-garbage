import VerifiedGarbage.Proof.Weierstrass.X86.NafPrep
import VerifiedGarbage.Proof.Weierstrass.X86.RegFieldTiming

/-! The recoder's only data-dependent branches read the public residual's low word. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Weierstrass.X86 VG.Proof.Mont.X86 VG.Proof.Mont

def nafPrepτ (work : Nat) : VG.X86.Taint.T :=
  { nafτ [.edi,.esi] with slots := [(0,work,4)] }

structure NafPrepChecks (bits src work : Nat) : Prop where
  init : RegCT [.edi] (.block (Naf.init src work))
  step : ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (nafPrepτ work)) (Naf.step bits work)

structure NafPrepPair (base : Addr) (size bits work k j : Nat) (s t : State) : Prop where
  left : NafPrepState base size bits work k j s
  right : NafPrepState base size bits work k j t
  pub : NafPublic s t

theorem nafRegion_base {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hw : VG.X86.Taint.Wf (nafτ) s) :
    (VG.X86.Taint.region s 0).base=base := by
  have h := hw.bases (.edi,0,0) (List.mem_singleton_self _)
  simp only [addr,BitVec.add_zero] at h
  exact h.symm.trans hs.edi

theorem nafResidual_low {s t : State} {base : Addr} {work : Nat}
    (h : val32 s.mem base work 9=val32 t.mem base work 9) :
    s.mem.readW (off base work) 32=t.mem.readW (off base work) 32 := by
  apply BitVec.eq_of_toNat_eq
  have hs := (s.mem.readW (off base work) 32).isLt
  have ht := (t.mem.readW (off base work) 32).isLt
  change w32 s.mem base work+2^32*val32 s.mem base (work+4) 8=
    w32 t.mem base work+2^32*val32 t.mem base (work+4) 8 at h
  change w32 s.mem base work<2^32 at hs
  change w32 t.mem base work<2^32 at ht
  change w32 s.mem base work=w32 t.mem base work
  omega

theorem NafPrepPair.agree {base : Addr} {size bits work k j : Nat} {s t : State}
    (h : NafPrepPair base size bits work k j s t) (hw : work+4≤8192) :
    VG.X86.Taint.Agree (nafPrepτ work) s t := by
  have lo := nafResidual_low (h.left.value.trans h.right.value.symm)
  have pub := h.pub.agree (rs:=[.edi,.esi]) (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact h.pub.edi
    · exact h.left.count.trans h.right.count.symm)
  refine ⟨pub.rf,pub.wr,⟨pub.wf₁.lens,pub.wf₁.bases,pub.wf₁.wbases,pub.wf₁.args,pub.wf₁.argBases,pub.wf₁.stk,pub.wf₁.frames,pub.wf₁.room⟩,
    ⟨pub.wf₂.lens,pub.wf₂.bases,pub.wf₂.wbases,pub.wf₂.args,pub.wf₂.argBases,pub.wf₂.stk,pub.wf₂.frames,pub.wf₂.room⟩,?_,?_,pub.sp,pub.argMem⟩
  · intro p hp
    rw [List.mem_singleton.mp hp]
    exact hw
  · intro p hp i hlo hhi
    rw [List.mem_singleton.mp hp] at hlo hhi ⊢
    change work≤i at hlo
    change i<work+4 at hhi
    simp only [VG.X86.Taint.byteAddr,nafRegion_base h.left.scr h.pub.wf₁,
      nafRegion_base h.right.scr h.pub.wf₂]
    have hi : i=work+(i-work) := by omega
    rw [hi,←Offset.add_add]
    have hb : i-work<4 := by omega
    rw [Mem.readW_byte s.mem (off base work) hb,Mem.readW_byte t.mem (off base work) hb,lo]

end VG.Proof.Weierstrass.X86
