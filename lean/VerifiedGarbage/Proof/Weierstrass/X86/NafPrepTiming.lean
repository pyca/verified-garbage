import VerifiedGarbage.Proof.Weierstrass.X86.NafPrepTimingState
import VerifiedGarbage.Proof.Framework.RelCTAssoc

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
