import VerifiedGarbage.Proof.Weierstrass.X86.NafPrep
import VerifiedGarbage.Proof.Weierstrass.X86.RegFieldTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ## `NafPrepTimingState` -/

section

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

end

/-! ## `NafPrepTiming` -/

section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Weierstrass.X86 VG.Proof.Mont.X86 VG.Proof.Mont

theorem nafPrepStep_relCT {bits src work : Nat} (hc : NafPrepChecks bits src work)
    {base : Addr} {size k j : Nat} (hb : bits+257≤size) (hw : work+36≤size) (hw8 : work+4≤8192)
    (hsep : bits+257≤work ∨ work+36≤bits) (hj : j<257)
    (hv : Naf5.residual k j≤2^256) :
    RelCT isa (NafPrepPair base size bits work k j) (Naf.step bits work) (fun s t =>
      NafPrepPair base size bits work k (j+1) s t ∧
      s.cf=some (decide (j+1<257)) ∧ t.cf=some (decide (j+1<257))) := by
  intro s t ts tt s' t' hp es et
  obtain ⟨_,_,xs,is,fs,ks,_⟩ := nafPrepStep_ok hp.left hb hw hsep hj hv
  obtain ⟨_,_,xt,it,ft,kt,_⟩ := nafPrepStep_ok hp.right hb hw hsep hj hv
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  exact ⟨hc.step _ _ _ _ _ _ trivial trivial (hp.agree hw8) es et,⟨is,it,hp.pub.keep ks kt (by decide) (by decide)⟩,fs,ft⟩

theorem nafPrepLoop_relCT {bits src work : Nat} (hc : NafPrepChecks bits src work)
    {base : Addr} {size k : Nat} (hb : bits+257≤size) (hw : work+36≤size) (hw8 : work+4≤8192)
    (hsep : bits+257≤work ∨ work+36≤bits) (hk : k<2^256) :
    RelCT isa (NafPrepPair base size bits work k 0) (.loop (Naf.step bits work) .b) (fun _ _ => True) := by
  let I := fun m s t => 1≤m ∧ m≤257 ∧ NafPrepPair base size bits work k (257-m) s t
  have step : ∀ m,RelCT isa (I m) (Naf.step bits work) (fun s t =>
      eval .b s=eval .b t ∧ (eval .b s=some false → True) ∧
      (eval .b s=some true → ∃ n<m,I n s t)) := by
    intro m
    by_cases hm : 1≤m ∧ m≤257
    · have hv := Naf5.residual_bound (Nat.le_of_lt hk) (j:=257-m) (by omega)
      have hv' : Naf5.residual k (257-m)≤2^256 := Nat.le_trans hv
        (Nat.pow_le_pow_right (by decide) (by omega))
      refine (nafPrepStep_relCT hc hb hw hw8 hsep (j:=257-m) (by omega) hv').mono
        (P':=I m) (fun _ _ h => h.2.2) ?_
      intro s t ⟨hp,fs,ft⟩
      refine ⟨fs.trans ft.symm,fun _ => trivial,fun he => ?_⟩
      have hn : 257-m+1<257 := by
        change s.cf=some true at he
        rw [fs] at he
        exact of_decide_eq_true (Option.some.inj he)
      refine ⟨m-1,by omega,by omega,by omega,?_⟩
      rw [show 257-(m-1)=257-m+1 from by omega]
      exact hp
    · exact RelCT.of_false (fun _ _ h => hm ⟨h.1,h.2.1⟩)
  exact (RelCT.loop I step 257).mono (fun _ _ h => ⟨by decide,by decide,h⟩) (fun _ _ h => h)

theorem nafPrep_relCT {bits work : Nat} {base : Addr} {size src : Nat}
    (hsrc : src+32≤size) (hb : bits+257≤size) (hw : work+36≤size) (hw8 : work+4≤8192)
    (hsrcWork : work≤src ∨ src+32≤work) (hsep : bits+257≤work ∨ work+36≤bits)
    (hc : NafPrepChecks bits src work) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ NafPublic s t ∧
      val32 s.mem base src 8=val32 t.mem base src 8)
      (Naf.prep bits src work) (fun _ _ => True) := by
  intro s t ts tt s' t' hp es et
  have hi : RelCT isa (fun a b => Scr a base size ∧ Scr b base size ∧ NafPublic a b ∧
      val32 a.mem base src 8=val32 s.mem base src 8 ∧ val32 b.mem base src 8=val32 s.mem base src 8)
      (.block (Naf.init src work)) (NafPrepPair base size bits work (val32 s.mem base src 8) 0) := by
    intro a b ta tb a' b' hab ea eb
    obtain ⟨_,_,xa,va,ca,ka,_⟩ := nafInit_ok hab.1 hsrc hw hsrcWork
    obtain ⟨_,_,xb,vb,cb,kb,_⟩ := nafInit_ok hab.2.1 hsrc hw hsrcWork
    obtain ⟨_,rfl⟩ := Exec.det ea xa
    obtain ⟨_,rfl⟩ := Exec.det eb xb
    have pub := hab.2.2.1.agree (rs:=[.edi]) (by
      intro r hr; rw [List.mem_singleton.mp hr]; exact hab.2.2.1.edi)
    refine ⟨hc.init _ _ _ _ _ _ trivial trivial pub ea eb,?_,?_,
      hab.2.2.1.keep ka kb (by decide) (by decide)⟩
    · refine ⟨hab.1.of_keeps ka (by decide),?_,ca,fun _ hi => (Nat.not_lt_zero _ hi).elim⟩
      rw [va,hab.2.2.2.1]; rfl
    · refine ⟨hab.2.1.of_keeps kb (by decide),?_,cb,fun _ hi => (Nat.not_lt_zero _ hi).elim⟩
      rw [vb,hab.2.2.2.2]; rfl
  exact (RelCT.seq hi (nafPrepLoop_relCT hc hb hw hw8 hsep (val32_lt ..))) _ _ _ _ _ _
    ⟨hp.1,hp.2.1,hp.2.2.1,rfl,hp.2.2.2.symm⟩ es et

end VG.Proof.Weierstrass.X86

end
