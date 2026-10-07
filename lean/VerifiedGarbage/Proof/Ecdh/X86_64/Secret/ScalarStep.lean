import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.ScalarState
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.ScalarControl
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.ScalarMath
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Double
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.AddValid

/-! One radix-32 iteration preserves the immutable table and advances the conditional accumulator. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem scalar_step_ok {K : WinCfg} {base : Addr} {size k j : Nat}
    (hL : SecretLay K size) (hm : UnitMod Spec.P256.p (2^(64*K.M.n)))
    (hC : Law Spec.P256.curve) (ha : AM3 Spec.P256.curve) (hO : PeerOrder Spec.P256.curve)
    (ht : K.tbl<2^31) (hOne : K.one<Spec.P256.p)
    (hOneVal : toM Spec.P256.p (2^(64*K.M.n)) K.one=1)
    (hj1 : 1≤j) (hj : j<K.J) {P : Point Spec.P256.curve}
    (hP : onCurve Spec.P256.curve P=true) (hne : P≠.infinity)
    {s₀ s : State} (hI : ScalarInv K Spec.P256.curve base size k P s₀ s j) :
    WP isa (Impl.Ecdh.X86_64.Window5.scalarStep K) s fun t =>
      ScalarInv K Spec.P256.curve base size k P s₀ t (j-1) ∧
      t.zf=some (decide (j-1=0)) := by
  have hj' : j-1<K.J := by omega
  have hj64 : j-1<4096 := by have := hL.J; omega
  have vr : ∀ x∈jacCoords K.R,x∈scalarLive K := fun _ hx => List.mem_append_left _ hx
  rw [Impl.Ecdh.X86_64.Window5.scalarStep]
  apply WP.seq
  refine WP.mono (scalar_prev_ok s hj1 hI.counter) fun a ⟨ca,ka⟩ => ?_
  have ia := hI.field.of_keeps ka (by decide)
  apply WP.seq
  refine WP.mono (doubles_ok hL.n hL.lay hm hC ha hL.double_nodup
    (fun x hx => local_slots K x (double_local K x hx)) ia vr hj64 ca
    (valid:=k<Spec.P256.curve.n) (fun _ => hC.onCurve_mul hP _) hI.acc)
    fun b ⟨F,kb,ib,jb⟩ => ?_
  have cb : b.gpr .rbx=BitVec.ofNat 64 (j-1) := (kb.gpr _ (by rw [hL.n]; decide)).trans ca
  have kab : CounterKeep K.M base (localWrites K) s b :=
    (CounterKeep.of_keeps ka).trans ((CounterKeep.of_progKeep kb).mono (double_local K))
  have db := TableData.keep hL hI.field ib (scalarLive_ro K) (scalarLive_ro K) kab hI.data
  have bb := hI.bits.keep hL hI.field.scr kab (fun _ hx => List.mem_append_left _ hx)
  have jbb : k<Spec.P256.curve.n → InvJ Spec.P256.curve (F K.R.x) (F K.R.y) (F K.R.z)
      (mul (32*Window5.winE (recoded K k) K.J (j-1+1)) P) := by
    intro hk
    have hh := jb hk
    rw [mul_composition hC hP] at hh
    simpa only [Nat.sub_add_cancel hj1] using hh
  apply WP.seq
  refine WP.mono (entry_ok (C:=Spec.P256.curve) hL hm ht hOne hOneVal ib (scalarLive_table K)
    (scalarLive_zero K) db.zero hj' cb bb db.table db.cache) fun c ⟨kc,ic,jc,c2,c3⟩ => ?_
  have cc : c.gpr .rbx=BitVec.ofNat 64 (j-1) := (kc.gpr _ (by rw [hL.n]; decide)).trans cb
  have cr : ∀ x∈jacCoords K.R,tmv Spec.P256.curve K.M.n base c x=F x :=
    fun x hx => (CounterKeep.of_progKeep kc).field_eq hL.lay ib ic
      (fun y hy => local_slots K y (hL.entry_local y hy)) (vr x hx)
      (List.mem_append_right _ (vr x hx)) (hL.entry_apart_r x hx)
  have jcr : k<Spec.P256.curve.n →
      InvJ Spec.P256.curve (tmv Spec.P256.curve K.M.n base c K.R.x)
        (tmv Spec.P256.curve K.M.n base c K.R.y) (tmv Spec.P256.curve K.M.n base c K.R.z)
        (mul (32*Window5.winE (recoded K k) K.J (j-1+1)) P) := by
    intro hk
    rw [cr _ (by simp [jacCoords]),cr _ (by simp [jacCoords]),cr _ (by simp [jacCoords])]
    exact jbb hk
  apply WP.seq
  refine WP.mono (add_valid_ok hL hm hC ha ic (entry_reads K hL) c2 c3
    (valid:=k<Spec.P256.curve.n) (fun _ => hC.onCurve_mul hP _)
    (fun _ => Window5.onCurve_winPt hC hP _ _) jcr (fun _ => jc)
    (fun hk hp _ => Window5.window_ne hO hP hne (by decide) (by decide) hk hj' hp))
    fun d ⟨G,kd,id,jd⟩ => ?_
  have cd : d.gpr .rbx=BitVec.ofNat 64 (j-1) := (kd.gpr _ (by rw [hL.n]; decide)).trans cc
  refine WP.mono (scalar_test_ok d hj64 cd) fun t ⟨zt,kt⟩ => ?_
  have it := id.of_keeps kt (by decide)
  have it' : Inv K.M base size Spec.P256.p (·∈slots K) (scalarLive K)
      (tmv Spec.P256.curve K.M.n base t) t :=
    it.to_tmv.sub (fun _ hx => List.mem_append_right _ hx)
  have kt' : CounterKeep K.M base (localWrites K) d t := .of_keeps
    ⟨fun r _ => kt.1 r (by simp),kt.2⟩
  have kst : CounterKeep K.M base (localWrites K) s t := kab.trans
    (((CounterKeep.of_progKeep kc).mono hL.entry_local).trans ((CounterKeep.of_progKeep kd).trans kt'))
  refine ⟨⟨it',TableData.keep hL hI.field it' (scalarLive_ro K) (scalarLive_ro K) kst hI.data,
    hI.bits.keep hL hI.field.scr kst (fun _ hx => List.mem_append_left _ hx),
    (kt.1 _ (by simp)).trans cd,?_,hI.keep.trans (kst.mono (fun _ hx => List.mem_append_left _ hx))⟩,zt⟩
  intro hk
  have jj := jd hk
  rw [Window5.win_add hC hP (by dsimp only [recoded]; omega) hj'] at jj
  exact it.point_tmv (p:=K.R) (fun x hx => List.mem_append_right _ (vr x hx)) jj

end VG.Proof.Ecdh.X86_64.Secret
