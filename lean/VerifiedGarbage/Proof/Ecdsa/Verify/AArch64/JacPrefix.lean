import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPublic
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPoints

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (SM' EM' RM' UM VM U V UX UY UZ)
variable {c : Cfg}

/-- Building the public scalar's bits preserves all initialized scalar and peer slots. -/
theorem bits_mid (hc : CfgOk c) {s₀ s : State} {base : Addr} {g : Reg → BitVec 64}
    (hM : Mid c s₀ base g s) :
    WP isa (bits (c.sl U) (bitsAt c.n 0) (8*c.n)) s (Mid c s₀ base g) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hM.scr.nowrap
  refine WP.mono_syms (bits_ok hM.scr h0 (by omega) (sl_le c h7 (i:=U) (by decide))
    (tbl_le h7) (sl_lt4096 h0 h7 (i:=U) (by decide)) (by have := bitsAt0_le c h7; omega)
    (Or.inl (by have := sl_below_bits c (i:=U) (by decide) 0 0; omega)))
    fun t ⟨_,kt,ot⟩ sy => ?_
  have ut : Unch base [(bitsAt c.n 0,64*c.n)] s.mem t.mem := ot.unch
  have eqv : ∀ {i},i<45 → sv c base t i=sv c base s i := fun hi =>
    sv_unch ut h7 hn hi (apart_tbl hi 0)
  refine ⟨hM.scr.of_keepRegs kt (by decide),kt.wr.trans hM.wr,kt.rd.trans hM.rd,
    hM.fixed.unch h7 hn (fixedOk_tbl 0) ut,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,sy.trans hM.syms,?_⟩
  · rw [eqv (by decide)]; exact hM.rx
  · rw [eqv (by decide)]; exact hM.ry
  · rw [eqv (by decide)]; exact hM.rz
  · rw [ut.word (fun w hw => ?_) (by have := sl_le c h7 (i:=FLAG) (by decide); omega)]
    · exact hM.flag
    · rw [List.mem_singleton.mp hw]
      exact Or.inl (by have := sl_below_bits c (i:=FLAG) (by decide) 0 0; omega)
  · rw [eqv (by decide)]; exact hM.px_lt
  · rw [eqv (by decide)]; exact hM.py_lt
  · rw [eqv (by decide)]; exact hM.px
  · rw [eqv (by decide)]; exact hM.py
  · rw [eqv (by decide)]; exact hM.rm_lt
  · rw [eqv (by decide)]; exact hM.rm
  · rw [eqv (by decide)]; exact hM.u_lt
  · rw [eqv (by decide)]; exact hM.u
  · rw [eqv (by decide)]; exact hM.v_lt
  · rw [eqv (by decide)]; exact hM.v
  · apply unch_whole (hM.unch.trans ut)
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rw [List.mem_singleton.mp hw]; exact Nat.zero_add size |>.le
    · rw [List.mem_singleton.mp hw]; exact tbl_le h7
  · rw [eqv (by decide)]; exact hM.k

/-- The public comb boundary retains the field and scalar data needed by the next loop. -/
def JacReady (c : Cfg) (s₀ s : State) : Prop :=
  CombReady c s₀ s ∧ ∃ g, Mid c s₀ (s₀.gpr .x3) g s

theorem jacPrefix_ok (hc : CfgOk c) {s₀ : State} (hp : VPre c s₀) :
    WP isa (verifyPrefix c) s₀ (JacReady c s₀) := by
  refine front_ok hc hp fun g s₁ _ hF => mid_ok hc hF fun s₂ hM => ?_
  obtain ⟨tr,t,e,r⟩ := bits_combReady hc hM hp.tbl
  obtain ⟨_,_,e',m⟩ := bits_mid hc hM
  obtain ⟨_,rfl⟩ := Exec.det e e'
  exact WP.seq ⟨tr,t,e,WP.block_nil ⟨r,g,m⟩⟩

end VG.Proof.Ecdsa.Verify.AArch64
