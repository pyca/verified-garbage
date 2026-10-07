import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.ScalarState
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointCopy
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointMask

/-! Initialize the accumulator from the highest recoded digit before the descending loop. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.X25519.X86_64 (Keeps)
open Spec.Weierstrass

theorem scalar_start_ok (s : State) {j : Nat} (hj : j<2^32) :
    WP isa (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 j))]) s fun t =>
      t.gpr .rbx=BitVec.ofNat 64 j ∧ Keeps [.rbx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc32,State.setReg32,
    Option.map_some,RegUpd.gpr_setReg,ite_true,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    omega
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg,hr,ite_false]

theorem top_digit_point {C : Curve} (hC : Law C) {P : Point C}
    (hP : onCurve C P=true) {k J : Nat} (hJ : 1≤J)
    (hfit : k+16*Window5.geom J<32^J) :
    Window5.winPt C P (k+16*Window5.geom J) (J-1)=
      mul (Window5.winE (k+16*Window5.geom J) J (J-1)) P := by
  have hh := Window5.win_add hC hP (J:=J) (k:=k+16*Window5.geom J) (by omega)
    (j:=J-1) (by omega)
  rw [Nat.sub_add_cancel hJ,Window5.winE_top hfit,Nat.mul_zero,mul_zero_pt'] at hh
  exact hh

theorem scalar_init_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat}
    (hL : SecretLay K size) (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C)
    (ht : K.tbl<2^31) (hOne : K.one<C.p) (hOneVal : toM C.p (2^(64*K.M.n)) K.one=1)
    (hfit : recoded K k<32^K.J) {P : Point C} (hP : onCurve C P=true)
    {s₀ s : State} {E : Nat → Fe C}
    (hI : Inv K.M base size C.p (·∈slots K) (tableLive K 16) E s)
    (hd : TableData K C E P) (hb : ScalarBits K base (recoded K k) s)
    (hk : CounterKeep K.M base (writes K) s₀ s) :
    WP isa (.block (([.mov32 .rbx (.imm (BitVec.ofNat 32 (K.J-1)))] : List Instr) ++
      ((digitCfg K).digit ++ Impl.Ecdh.X86_64.Window5.select K ++ (digitCfg K).negY) ++
      copyPt 4 K.R K.E)) s fun t => ScalarInv K C base size k P s₀ t (K.J-1) := by
  have hj : K.J-1<K.J := by have := hL.J; omega
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (scalar_start_ok s (j:=K.J-1) (by have := hL.J; omega)) fun a ⟨ca,ka⟩ => ?_
  have ia := hI.of_keeps ka (by decide)
  have ba : ScalarBits K base (recoded K k) a := by intro i hi; rw [ka.2.1]; exact hb i hi
  rw [WP.block_append_iff]
  refine WP.mono (entry_ok hL hm ht hOne hOneVal ia (fun _ hx => List.mem_append_right _ hx)
    (by simp [tableLive,winRo]) hd.zero hj ca ba hd.table hd.cache) fun b ⟨kb,ib,jb,_,_⟩ => ?_
  have ve : ∀ x∈jacCoords K.E,x∈entryWrites K := by
    intro x hx
    apply List.mem_append_left
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact List.mem_map.mpr ⟨0,by decide,by simp⟩
    · exact List.mem_map.mpr ⟨1,by decide,by simp [hL.exy]⟩
    · exact List.mem_map.mpr ⟨2,by decide,by simp [hL.exz]⟩
  rw [←hL.n]
  refine WP.mono (copyPointTransfer_ok hL.lay ib hL.rxy hL.rxz
    (fun x hx => local_slots K x (r_local K x hx))
    (fun x hx => List.mem_append_left _ (ve x hx))
    (fun x hx y hy he => hL.entry_apart_r y hy (he ▸ ve x hx))) fun t ⟨kt,it⟩ => ?_
  have vf := pointTransferEnv_values (tmv C K.M.n base b) K.R K.E hL.rxy hL.rxz
  simp only [Prod.mk.injEq] at vf
  have jp : InvJ C (pointTransferEnv (tmv C K.M.n base b) K.R K.E K.R.x)
      (pointTransferEnv (tmv C K.M.n base b) K.R K.E K.R.y)
      (pointTransferEnv (tmv C K.M.n base b) K.R K.E K.R.z)
      (mul (Window5.winE (recoded K k) K.J (K.J-1)) P) := by
    rw [vf.1,vf.2.1,vf.2.2,recoded,←top_digit_point hC hP hL.J.1 hfit]
    exact jb
  have it' : Inv K.M base size C.p (·∈slots K) (scalarLive K) (tmv C K.M.n base t) t := by
    apply it.to_tmv.sub
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (List.mem_append_right _ hx)
  have kst : CounterKeep K.M base (localWrites K) s t :=
    (CounterKeep.of_keeps ka).trans (((CounterKeep.of_progKeep kb).mono hL.entry_local).trans
      ((CounterKeep.of_progKeep kt).mono (r_local K)))
  refine ⟨it',TableData.keep hL hI it' (fun _ hx => hx) (scalarLive_ro K) kst hd,
    hb.keep hL hI.scr kst (fun _ hx => List.mem_append_left _ hx),?_,?_,
    hk.trans (kst.mono (fun _ hx => List.mem_append_left _ hx))⟩
  · exact (kt.gpr _ (by rw [hL.n]; decide)).trans ((kb.gpr _ (by rw [hL.n]; decide)).trans ca)
  · intro _
    exact it.point_tmv (p:=K.R) (fun _ hx => List.mem_append_left _ hx) jp

end VG.Proof.Ecdh.X86_64.Secret
