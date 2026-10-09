import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyExtra

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Impl.Ecdsa.Verify.AArch64.P256Allocated (inverse saveExtra restoreExtra extra)

def invAllocatedOuterRegs : List Reg := invAllocatedRegs.filter fun r => r∉allocatedExtraRegs

def invAllocatedOuterW : List (Nat × Nat) := invAllocatedW ++ [(7800,32)]

 theorem invAllocated_save_mod {base : Addr} {size : Nat} {s a : State}
    (hs : Scr s base size) (hM : ModOkA invAllocatedCfg.M size invAllocatedModulus s.mem base)
    (ua : Outside base 7800 32 s.mem a.mem) :
    ModOkA invAllocatedCfg.M size invAllocatedModulus a.mem base := by
  refine ⟨hM.n0,hM.n10,hM.mo,hM.tmp,hM.sep,?_,hM.inv,hM.red, hM.call⟩
  rw [ua.wordsVal (by decide) (by omega_using [hM.mo,hs.nowrap])]
  exact hM.val

 theorem invAllocated_save_input {base : Addr} {size : Nat} {s a : State}
    (hs : Scr s base size) (_hsize : 8192≤size) (ua : Outside base 7800 32 s.mem a.mem) :
    wordsVal a.mem base invAllocatedCfg.base 4=wordsVal s.mem base invAllocatedCfg.base 4 :=
  ua.wordsVal (by decide) (by have := hs.nowrap; change 1248+8*4≤2^64; omega)

/-- The production inverse restores every extra callee-saved register used by allocation. -/
theorem invAllocated_inverse_ok {base : Addr} {size : Nat} [NeZero invAllocatedModulus]
    (hsize : 8192≤size) (hpr : invAllocatedModulus.Prime) (hT : InvToM invAllocatedModulus)
    (hL : InvLay invAllocatedCfg size) (hR : UnitMod invAllocatedModulus (2^256))
    {s : State} (hs : Scr s base size)
    (hM : ModOkA invAllocatedCfg.M size invAllocatedModulus s.mem base)
    (hX : wordsVal s.mem base invAllocatedCfg.base 4<invAllocatedModulus)
    (hC : InvOk invAllocatedCfg invAllocatedModulus) :
    WP isa inverse s fun t =>
      KeepRegs invAllocatedOuterRegs s t ∧ Unch base invAllocatedOuterW s.mem t.mem ∧
      wordsVal t.mem base invAllocatedCfg.acc 4<invAllocatedModulus ∧
      toM invAllocatedModulus (2^256) (wordsVal t.mem base invAllocatedCfg.acc 4)=
        toM invAllocatedModulus (2^256) (wordsVal s.mem base invAllocatedCfg.base 4) ^ (invAllocatedModulus-2) := by
  change WP isa (.seq (.block saveExtra) (.seq invAllocatedBody (.block restoreExtra))) s _
  refine WP.seq (WP.mono (allocatedSave_ok hs (by omega)) fun a ⟨ka,ua,sa⟩ => ?_)
  have ha := hs.of_keepRegs ka (by simp)
  have ma := invAllocated_save_mod hs hM ua
  have va := invAllocated_save_input hs hsize ua
  refine WP.seq (WP.mono (invAllocated_body_ok hsize hpr hT hL hR ha ma (by rw [va]; exact hX) hC)
    fun b ⟨kb,ub,lb,eb⟩ => ?_)
  have hb := ha.of_keepRegs kb (by decide)
  have sb := allocatedSaved_keep sa ub (by decide)
  refine WP.mono (allocatedRestore_ok hb (by omega) sb) fun t ⟨kt,vt⟩ =>
    ⟨allocatedRestore_frame ka kb kt vt,?_,?_,?_⟩
  · intro x hx
    rw [kt.mem,ub x (fun w hw => hx w (List.mem_append_left _ hw)),ua x (hx (7800,32) (List.mem_append_right _ (by simp)))]
  · rw [kt.mem]; exact lb
  · rw [kt.mem,eb,va]

/-- Relational timing for the complete production inverse, including extra-register saves. -/
theorem invAllocated_inverse_relCT {base : Addr} {size X : Nat} [NeZero invAllocatedModulus]
    (hsize : 8192≤size) (hpr : invAllocatedModulus.Prime) (hT : InvToM invAllocatedModulus)
    (hL : InvLay invAllocatedCfg size) (hR : UnitMod invAllocatedModulus (2^256))
    (hX : X<invAllocatedModulus) (hC : InvOk invAllocatedCfg invAllocatedModulus) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ s.sp=t.sp ∧
      ModOkA invAllocatedCfg.M size invAllocatedModulus s.mem base ∧
      ModOkA invAllocatedCfg.M size invAllocatedModulus t.mem base ∧
      wordsVal s.mem base invAllocatedCfg.base 4=X ∧ wordsVal t.mem base invAllocatedCfg.base 4=X)
      inverse (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  let Pre := fun s t : State => Scr s base size ∧ Scr t base size ∧ s.sp=t.sp ∧
      ModOkA invAllocatedCfg.M size invAllocatedModulus s.mem base ∧
      ModOkA invAllocatedCfg.M size invAllocatedModulus t.mem base ∧
      wordsVal s.mem base invAllocatedCfg.base 4=X ∧ wordsVal t.mem base invAllocatedCfg.base 4=X
  have hpub : ∀ s t,Pre s t → AArch64.Taint.Agree (Taint.ofRegs [.x0]) s t := by
    intro s t hp
    refine ⟨hp.2.2.1,?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs,List.mem_singleton] at hr
    subst r
    exact hp.1.x0.trans hp.2.1.x0.symm
  have hsave : RelCT isa Pre (.block saveExtra) Pre := by
    intro s t ts tt s' t' hp es et
    obtain ⟨_,_,xs,ks,us,_⟩ := allocatedSave_ok hp.1 (by omega)
    obtain ⟨_,_,xt,kt,ut,_⟩ := allocatedSave_ok hp.2.1 (by omega)
    obtain ⟨_,rfl⟩ := es.det xs
    obtain ⟨_,rfl⟩ := et.det xt
    refine ⟨invAllocated_save_ct _ _ _ _ _ _ trivial trivial (hpub s t hp) es et,
      hp.1.of_keepRegs ks (by simp),hp.2.1.of_keepRegs kt (by simp),
      ks.sp.trans (hp.2.2.1.trans kt.sp.symm),
      invAllocated_save_mod hp.1 hp.2.2.2.1 us,invAllocated_save_mod hp.2.1 hp.2.2.2.2.1 ut,?_,?_⟩
    · rw [invAllocated_save_input hp.1 hsize us]; exact hp.2.2.2.2.2.1
    · rw [invAllocated_save_input hp.2.1 hsize ut]; exact hp.2.2.2.2.2.2
  have hrestore : RelCT isa (AArch64.Taint.Agree (Taint.ofRegs [.x0])) (.block restoreExtra) (fun _ _ => True) := by
    intro s t ts tt s' t' hp es et
    exact ⟨invAllocated_restore_ct _ _ _ _ _ _ trivial trivial hp es et,trivial⟩
  have hfull : RelCT isa Pre inverse (fun _ _ => True) :=
    RelCT.seq hsave (RelCT.seq (invAllocated_body_relCT hsize hpr hT hL hR hX hC) hrestore)
  intro s t ts tt s' t' hp es et
  obtain ⟨trace,_⟩ := hfull _ _ _ _ _ _ hp es et
  obtain ⟨_,_,xs,ks,_,_,_⟩ := invAllocated_inverse_ok hsize hpr hT hL hR hp.1 hp.2.2.2.1
    (by rw [hp.2.2.2.2.2.1]; exact hX) hC
  obtain ⟨_,_,xt,kt,_,_,_⟩ := invAllocated_inverse_ok hsize hpr hT hL hR hp.2.1 hp.2.2.2.2.1
    (by rw [hp.2.2.2.2.2.2]; exact hX) hC
  obtain ⟨_,rfl⟩ := es.det xs
  obtain ⟨_,rfl⟩ := et.det xt
  refine ⟨trace,ks.sp.trans (hp.2.2.1.trans kt.sp.symm),?_⟩
  intro r hr
  simp only [Taint.mem_ofRegs,List.mem_singleton] at hr
  subst r
  rw [ks.gpr _ (by decide),kt.gpr _ (by decide)]
  exact hp.1.x0.trans hp.2.1.x0.symm

end VG.Proof.Weierstrass.AArch64
