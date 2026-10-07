import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.TablePreserve
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.TableCalc
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.TableControl
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.CacheStore

/-! One public table iteration: load, calculate, cache, store, and advance. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem table_step_ok {K : WinCfg} {base : Addr} {size m : Nat}
    (hL : SecretLay K size) (hm : UnitMod Spec.P256.p (2^(64*K.M.n)))
    (hC : Law Spec.P256.curve) (ha : AM3 Spec.P256.curve) (hO : PeerOrder Spec.P256.curve)
    (hm1 : 1≤m) (hm16 : m<16) (ht : K.tbl<2^31)
    {P : Point Spec.P256.curve} (hP : onCurve Spec.P256.curve P=true) (hne : P≠.infinity)
    {s₀ s : State} (hI : TableInv K Spec.P256.curve base size P s₀ s m) :
    WP isa (Impl.Ecdh.X86_64.Window5.tableStep K) s fun t =>
      TableInv K Spec.P256.curve base size P s₀ t (m+1) ∧
      t.zf=some (decide (m+1=16)) := by
  have h2 : 2≤m+1 := by omega
  have h16 : m+1≤16 := by omega
  have hp := tableParent_bounds h2 h16
  have hpm : tableParent (m+1)≤m := by omega
  have er : consecutiveFields K.R.x 3=jacCoords K.R := by
    simp [consecutiveFields,List.range_succ,jacCoords,hL.rxy,hL.rxz]
  have hd : ∀ x∈consecutiveFields K.R.x 3,x∈slots K := by
    rw [er]
    exact fun x hx => local_slots K x (r_local K x hx)
  have hr := hL.lay.le K.R.z (local_slots K _ (r_local K _ (by simp [jacCoords])))
  rw [hL.n,hL.rxz] at hr
  rw [Impl.Ecdh.X86_64.Window5.tableStep]
  apply WP.seq
  refine WP.mono (tableLoad_fields_ok hL.lay hL.n hI.field h2 h16 hI.counter ht
    hL.table_le (by omega) hL.r_table_sep hd
    (fun i hi => tableLive_entry K hp.1 hpm (by omega))) fun a ⟨ka,ia,va⟩ => ?_
  rw [er] at ka ia
  have va0 := va 0 (by decide)
  have va1 := va 1 (by decide)
  have va2 := va 2 (by decide)
  simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one,Nat.reduceMul,←hL.rxy,←hL.rxz] at va0 va1 va2
  have ja : InvJ Spec.P256.curve (tmv Spec.P256.curve K.M.n base a K.R.x)
      (tmv Spec.P256.curve K.M.n base a K.R.y) (tmv Spec.P256.curve K.M.n base a K.R.z)
      (mul (tableParent (m+1)) P) := by
    rw [va0,va1,va2]
    exact hI.table _ hp.1 hpm
  have keepa : ProgKeep K.M base (localWrites K) s a := ka.mono (r_local K)
  have ar : ∀ x∈winRo K,tmv Spec.P256.curve K.M.n base a x=tmv Spec.P256.curve K.M.n base s x :=
    fun x hx => (CounterKeep.of_progKeep keepa).field_eq hL.lay hI.field ia (local_slots K)
      (List.mem_append_left _ hx) (List.mem_append_right _ (List.mem_append_left _ hx)) (hL.ro x hx)
  have qa : InvJ Spec.P256.curve (tmv Spec.P256.curve K.M.n base a K.P.x)
      (tmv Spec.P256.curve K.M.n base a K.P.y) (tmv Spec.P256.curve K.M.n base a K.P.z) P := by
    rw [ar _ (by simp [winRo]),ar _ (by simp [winRo]),ar _ (by simp [winRo])]
    exact hI.peer
  have za : tmv Spec.P256.curve K.M.n base a K.P.z=1 := (ar _ (by simp [winRo])).trans hI.affine
  have ca : a.gpr .rbx=BitVec.ofNat 64 (m+1) := (ka.gpr _ (by rw [hL.n]; decide)).trans hI.counter
  apply WP.seq
  refine WP.mono (table_test_ok a ca h16) fun b ⟨zb,kb⟩ => ?_
  have ib := ia.of_keeps kb (by decide)
  have keepb : ProgKeep K.M base (localWrites K) a b :=
    ⟨fun r _ => kb.1 r (by simp),kb.2.2.1,kb.2.2.2,fun x _ _ => congrFun kb.2.1 x⟩
  have cb : b.gpr .rbx=BitVec.ofNat 64 (m+1) := (kb.1 _ (by simp)).trans ca
  apply WP.seq
  refine WP.mono (table_calc_ok hL hm hC ha hO h2 h16 ib (tableLive_read K m)
    zb hP hne ja qa za) fun c ⟨F,kc,ic,jc⟩ => ?_
  have cc : c.gpr .rbx=BitVec.ofNat 64 (m+1) := (kc.gpr _ (by rw [hL.n]; decide)).trans cb
  refine WP.seq (WP.mono (WP.seq_iff.mp (cache_store_ok hL hm (by omega) h16 ht ic
    (fun _ hx => List.mem_append_left _ hx) cc jc)) fun d hd => ?_)
  rw [WP.block_append_iff]
  refine WP.mono hd fun e ⟨ke,ie,je,z2,z3⟩ => ?_
  have ce : e.gpr .rbx=BitVec.ofNat 64 (m+1) := (ke.gpr _ (by rw [hL.n]; decide)).trans cc
  refine WP.mono (table_advance_ok e h16 ce) fun t ⟨ct,zt,kt⟩ => ?_
  have it := ie.of_keeps kt (by decide)
  have it' : Inv K.M base size Spec.P256.p (·∈slots K) (tableLive K (m+1))
      (tmv Spec.P256.curve K.M.n base t) t := by
    apply it.to_tmv.sub
    intro x hx
    have hh := tableLive_next K m x hx
    rcases List.mem_append.mp hh with hh|hh
    · exact List.mem_append_left _ (by simpa only [Impl.Ecdh.X86_64.Window5.tablePt,Nat.add_sub_cancel] using hh)
    · exact List.mem_append_right _ (List.mem_append_right _ hh)
  have tm : tmv Spec.P256.curve K.M.n base t=tmv Spec.P256.curve K.M.n base e := by
    funext x
    unfold tmv
    rw [kt.2.1]
  have keepc := (keepa.trans keepb).trans kc
  have keepe : ProgKeep K.M base (tableStepWrites K m) s e := by
    exact (keepc.mono (fun _ hx => List.mem_append_left _ hx)).trans
      (by simpa only [tableStepWrites,Impl.Ecdh.X86_64.Window5.tablePt,Nat.add_sub_cancel] using ke)
  refine ⟨hI.extend hL hm16 ((CounterKeep.of_progKeep keepe).trans (.of_keeps kt)) it' ?_ ?_ ct,?_⟩
  · rw [tm]
    exact je
  · rw [tm]
    exact ⟨z2,z3⟩
  · simpa only [show m+1+1=17 ↔ m+1=16 by omega] using zt

end VG.Proof.Ecdh.X86_64.Secret
