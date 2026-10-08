import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafMulSetup
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafWindowChecks

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Impl.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.X86 Spec.Weierstrass

def nafSetB : Prog isa := .block (setConst p256Comb.n (p256Comb.sl EM) (p256Comb.mont p256Comb.C.b))
materialize_code nafSetB

theorem nafSetB_ct : ScratchCT nafSetB :=
  Taint.constantTime (A:=taint) _ (fun _ _ _ _ h => h) (by taint_decide)

theorem nafSetB_ok (hc : CfgOk p256Comb) {s : State} {base : Addr} (hs : Scr s base size) :
    WP isa nafSetB s fun t => Keeps powClob s t ∧ Scr t base size ∧
      val32 t.mem base (p256Comb.sl V) 8=val32 s.mem base (p256Comb.sl V) 8 := by
  have hp := hc.p_ge
  refine WP.mono (setConst_ok hs (sl_le p256Comb hc.n10 (i:=EM) (by decide))
    (Nat.lt_trans (Nat.mod_lt _ (by omega)) hc.p_lt)) fun t ⟨_,kt,ot⟩ => ?_
  have un : Unch base (slW p256Comb [EM]) s.mem t.mem := ot.unch
  have eq := sv_unch un hc.n10 hs.nowrap (i:=V) (by decide) (apart_slW (by decide))
  change wordsVal t.mem base (p256Comb.sl V) p256Comb.n=wordsVal s.mem base (p256Comb.sl V) p256Comb.n at eq
  rw [wordsVal_eq_val32,wordsVal_eq_val32] at eq
  exact ⟨kt.mono (by decide),hs.of_keeps kt (by decide),eq⟩

theorem nafSetup_relCT (hc : CfgOk p256Comb) {base : Addr} :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ NafPublic s t ∧
      val32 s.mem base (p256Comb.sl V) 8=val32 t.mem base (p256Comb.sl V) 8)
      (.seq nafSetB (Naf.prep 3580 (p256Comb.sl V) 3520)) (fun _ _ => True) := by
  have front : RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ NafPublic s t ∧
      val32 s.mem base (p256Comb.sl V) 8=val32 t.mem base (p256Comb.sl V) 8)
      nafSetB (fun s t => Scr s base size ∧ Scr t base size ∧ NafPublic s t ∧
      val32 s.mem base (p256Comb.sl V) 8=val32 t.mem base (p256Comb.sl V) 8) := by
    intro s t ts tt u v ⟨hs,ht,hp,hv⟩ es et
    have tr := nafSetB_ct _ _ _ _ _ _ trivial trivial (hp.agree (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact hp.edi
      · exact hp.esp)) es et
    obtain ⟨_,u',eu,ku,su,vu⟩ := nafSetB_ok hc hs
    obtain ⟨_,v',ev,kv,sv,vv⟩ := nafSetB_ok hc ht
    obtain ⟨-,rfl⟩ := Exec.det es eu
    obtain ⟨-,rfl⟩ := Exec.det et ev
    exact ⟨tr,su,sv,hp.keep ku kv (by decide) (by decide),vu.trans (hv.trans vv.symm)⟩
  exact front.seq (nafPrep_relCT (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) nafPrep_checks)

end VG.Proof.Ecdsa.Verify.X86
