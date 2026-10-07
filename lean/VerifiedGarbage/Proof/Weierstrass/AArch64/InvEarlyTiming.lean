import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyAllocatedMain
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Impl.Ecdsa.Verify.AArch64.P256Allocated (inverseBatch inverseNine inverseCheck)

def invAllocatedPrefix : Prog isa :=
  .seq (.block inverseNine.init) (.loop inverseBatch (.nonzero .x .x19))

def invAllocatedCheckedPrefix : Prog isa := .seq invAllocatedPrefix (.block inverseCheck)

def invAllocatedLast : Prog isa :=
  .seq (.block [.movz .x .x19 1 0]) (.seq inverseBatch (.block invAllocatedCfg.finish))

macro "inv_fixed_ct" : tactic => `(tactic|
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide))

 theorem invAllocated_prefix_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0])) invAllocatedCheckedPrefix := by inv_fixed_ct

 theorem invAllocated_last_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0])) invAllocatedLast := by inv_fixed_ct

 theorem invAllocated_finish_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0])) (.block inverseNine.finish) := by inv_fixed_ct

/-- Exact word equality follows from the invariant's signed residue representation. -/
theorem IInv.g_words_eq {P : InvCfg} {base : Addr} {I : Divstep.IState} {s t : State}
    (hs : IInv P base I s) (ht : IInv P base I t) :
    wordsVal s.mem base P.sG P.L=wordsVal t.mem base P.sG P.L := by
  have es := hs.g
  have et := ht.g
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast wordsVal_lt s.mem base P.sG P.L)] at es
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast wordsVal_lt t.mem base P.sG P.L)] at et
  exact_mod_cast es.trans et.symm

 theorem invAllocated_prefix_ok {base : Addr} {size X : Nat}
    (hsize : 8192≤size) (hpr : invAllocatedModulus.Prime) (hL : InvLay invAllocatedCfg size)
    {s : State} (hs : Scr s base size)
    (hM : ModOkA invAllocatedCfg.M size invAllocatedModulus s.mem base)
    (hX : X<invAllocatedModulus) (hval : wordsVal s.mem base invAllocatedCfg.base 4=X) :
    WP isa invAllocatedPrefix s fun t =>
      Scr t base size ∧ IInv invAllocatedCfg base
        (Divstep.invRun 59 invAllocatedModulus invAllocatedCfg.M.minv.toNat X 9) t ∧
      KeepRegs invAllocatedRegs s t := by
  have hl9 : InvLay inverseNine size := by rw [invAllocated_nine_eq]; exact hL.earlyCfg _ _
  rw [invAllocatedPrefix]
  refine WP.seq (WP.mono (init_ok hl9 hs hM (by decide)) fun a ⟨ia,a19,ka,ua⟩ => ?_)
  have ua' : Unch base invAllocatedBatchW s.mem a.mem := ua.cover (by decide)
  have ha := hs.of_keepRegs ka (by decide)
  have ma := invAllocated_mod hs hM ua'
  have ia' := IInv.of_earlyCfg (P:=invAllocatedCfg) (B:=9) (m:=invAllocatedModulus) ia
  change IInv invAllocatedCfg base ⟨1,invAllocatedModulus,wordsVal s.mem base invAllocatedCfg.base 4,0,1⟩ a at ia'
  rw [hval] at ia'
  refine WP.mono (invAllocated_loop_ok hsize hL ha ma hX (invAllocated_odd hpr)
      hpr.one_lt (B:=9) (by decide) (by decide) ia' a19) fun t ⟨it,kt,_⟩ =>
      ⟨ha.of_keepRegs kt (by decide),it,(ka.mono (by decide)).trans kt⟩

 theorem invAllocated_checked_prefix_ok {base : Addr} {size X : Nat}
    (hsize : 8192≤size) (hpr : invAllocatedModulus.Prime) (hL : InvLay invAllocatedCfg size)
    {s : State} (hs : Scr s base size)
    (hM : ModOkA invAllocatedCfg.M size invAllocatedModulus s.mem base)
    (hX : X<invAllocatedModulus) (hval : wordsVal s.mem base invAllocatedCfg.base 4=X) :
    WP isa invAllocatedCheckedPrefix s fun t => ∃ u,
      IInv invAllocatedCfg base (Divstep.invRun 59 invAllocatedModulus invAllocatedCfg.M.minv.toNat X 9) u ∧
      (t.gpr .x2=0 ↔ wordsVal u.mem base invAllocatedCfg.sG invAllocatedCfg.L=0) ∧
      KeepRegs invAllocatedRegs s t := by
  rw [invAllocatedCheckedPrefix]
  refine WP.seq (WP.mono (invAllocated_prefix_ok hsize hpr hL hs hM hX hval) fun u ⟨hu,iu,ku⟩ => ?_)
  exact WP.mono (earlyCheck_ok hu (n:=5) (a:=2312) (by decide) (by omega) (by decide))
    fun t ⟨eq,kt⟩ => ⟨u,iu,eq,ku.trans ((Keeps.regs kt).mono (by decide))⟩

/-- The canonical public signature scalar determines whether the tenth batch runs. -/
theorem invAllocated_body_relCT {base : Addr} {size X : Nat} [NeZero invAllocatedModulus]
    (hsize : 8192≤size) (hpr : invAllocatedModulus.Prime) (hT : InvToM invAllocatedModulus)
    (hL : InvLay invAllocatedCfg size) (hR : UnitMod invAllocatedModulus (2^256))
    (hX : X<invAllocatedModulus) (hC : InvOk invAllocatedCfg invAllocatedModulus) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ s.sp=t.sp ∧
      ModOkA invAllocatedCfg.M size invAllocatedModulus s.mem base ∧
      ModOkA invAllocatedCfg.M size invAllocatedModulus t.mem base ∧
      wordsVal s.mem base invAllocatedCfg.base 4=X ∧ wordsVal t.mem base invAllocatedCfg.base 4=X)
      invAllocatedBody (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
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
  let Post := fun s t : State => AArch64.Taint.Agree (Taint.ofRegs [.x0]) s t ∧ (s.gpr .x2=0 ↔ t.gpr .x2=0)
  have hc : RelCT isa Pre invAllocatedCheckedPrefix Post := by
    intro s t ts tt s' t' hp es et
    obtain ⟨_,_,xs,u,iu,zu,ku⟩ := invAllocated_checked_prefix_ok hsize hpr hL hp.1 hp.2.2.2.1 hX hp.2.2.2.2.2.1
    obtain ⟨_,_,xt,v,iv,zv,kv⟩ := invAllocated_checked_prefix_ok hsize hpr hL hp.2.1 hp.2.2.2.2.1 hX hp.2.2.2.2.2.2
    obtain ⟨_,rfl⟩ := es.det xs
    obtain ⟨_,rfl⟩ := et.det xt
    refine ⟨invAllocated_prefix_ct _ _ _ _ _ _ trivial trivial (hpub s t hp) es et,?_,?_⟩
    · refine ⟨ku.sp.trans (hp.2.2.1.trans kv.sp.symm),?_⟩
      intro r hr
      simp only [Taint.mem_ofRegs,List.mem_singleton] at hr
      subst r
      rw [ku.gpr _ (by decide),kv.gpr _ (by decide)]
      exact hp.1.x0.trans hp.2.1.x0.symm
    · rw [zu,zv,iu.g_words_eq iv]
  have hb : RelCT isa Post (.ite (.nonzero .x .x2) invAllocatedLast (.block inverseNine.finish)) (fun _ _ => True) := by
    apply RelCT.ite
    · intro s t hp
      change some (s.read .x .x2 != 0)=some (t.read .x .x2 != 0)
      rw [read_x,read_x]
      apply congrArg some
      apply Bool.eq_iff_iff.mpr
      simp only [bne_iff_ne,ne_eq,hp.2]
    · intro s t ts tt s' t' hp es et
      exact ⟨invAllocated_last_ct _ _ _ _ _ _ trivial trivial hp.1.1 es et,trivial⟩
    · intro s t ts tt s' t' hp es et
      exact ⟨invAllocated_finish_ct _ _ _ _ _ _ trivial trivial hp.1.1 es et,trivial⟩
  have hbody : RelCT isa Pre invAllocatedBody (fun _ _ => True) :=
    RelCT.assoc (RelCT.assoc (RelCT.seq hc hb))
  intro s t ts tt s' t' hp es et
  obtain ⟨trace,_⟩ := hbody _ _ _ _ _ _ hp es et
  obtain ⟨_,_,xs,ks,_,_,_⟩ := invAllocated_body_ok hsize hpr hT hL hR hp.1 hp.2.2.2.1
    (by rw [hp.2.2.2.2.2.1]; exact hX) hC
  obtain ⟨_,_,xt,kt,_,_,_⟩ := invAllocated_body_ok hsize hpr hT hL hR hp.2.1 hp.2.2.2.2.1
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
