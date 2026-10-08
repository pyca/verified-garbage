import VerifiedGarbage.Proof.Weierstrass.X86.NafSum

/-! A zero digit is skipped; a nonzero digit contributes its signed odd multiple. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
  VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem nafMagnitude_byte (k j : Nat) : nafMagnitude (Naf5.byte k j)=Naf5.magnitude k j :=
  Naf5.byte_magnitude k j

theorem nafNegative_byte (k j : Nat) : nafNegative (Naf5.byte k j)=Naf5.negative k j :=
  Naf5.byte_negative k j

theorem nafDigit_ok {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk k j : Nat}
    (hL : NafLay K size) (hJ : K.J=65) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hj : j<257) {P : Point C} (hP : onCurve C P=true) {s : State}
    (h : NafCore K C base size P (Naf5.byte k) (2*Naf5.residual k (j+1)) s)
    (hc : s.gpr .esi=BitVec.ofNat 32 j) :
    WP isa (Naf.digit K F) s fun t => ProgKeep K.M base wk (winOther K) s t ∧
      NafCore K C base size P (Naf5.byte k) (Naf5.residual k j) t := by
  rw [Naf.digit]
  apply WP.seq
  refine WP.mono (nafRead_ok h.field.scr (by have:=hL.bits; omega) hc (h.stable.bits j hj))
    fun u ⟨u8,uz,ku⟩ => ?_
  have cu := h.of_keeps ku (by decide)
  have kp : ProgKeep K.M base wk (winOther K) s u := nafPrefix_keep ku (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> simp [clob])
  refine WP.ite (decide (Naf5.byte k j=0)) uz (fun hz => ?_) (fun hn => ?_)
  · have hm0 := (Naf5.byte_zero_iff k j).mp (of_decide_eq_true hz)
    have he : Naf5.residual k j=2*Naf5.residual k (j+1) := by
      have hh := Naf5.recurrence k j
      rw [hm0] at hh
      split at hh <;> omega
    apply WP.block_nil
    exact ⟨kp,he.symm ▸ cu⟩
  · have hm0 : Naf5.magnitude k j≠0 := fun he =>
      of_decide_eq_false hn ((Naf5.byte_zero_iff k j).mpr he)
    apply WP.seq
    refine WP.mono (nafEntry_ok hL hAcc hBitsWk hm
      (by rw [nafMagnitude_byte]; omega)
      (by rw [nafMagnitude_byte]; exact Naf5.magnitude_le k j)
      (by rw [nafMagnitude_byte]; exact (Naf5.magnitude_odd_or_zero k j).resolve_left hm0)
      cu u8) fun v ⟨kv,cv,iv,jv⟩ => ?_
    simp only [nafNegative_byte,nafMagnitude_byte] at jv
    exact WP.mono (nafAdd_ok hL hJ hAcc hBitsWk hm hC ha hOne hP
      (Naf5.onCurve_point hC hP k j) (Naf5.add_step hC hP k j) cv iv jv)
      fun t ⟨kt,ct⟩ => ⟨kp.trans (kv.trans kt),ct⟩

end VG.Proof.Weierstrass.X86
