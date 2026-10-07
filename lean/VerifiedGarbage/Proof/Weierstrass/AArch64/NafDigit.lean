import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSum
import VerifiedGarbage.Proof.Weierstrass.Naf5

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem nafMagnitude_byte (k j : Nat) : nafMagnitude (Naf5.byte k j)=Naf5.magnitude k j :=
  Naf5.byte_magnitude k j

theorem nafNegative_byte (k j : Nat) : nafNegative (Naf5.byte k j)=Naf5.negative k j :=
  Naf5.byte_negative k j

private theorem nafByteTest : ∀ b : BitVec 8,
    (b.setWidth 64 != 0)=decide (nafMagnitude b≠0) := by decide +kernel

theorem nafDigit_ok {K : WinCfg} {C : Curve} {base : Addr} {size k j : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits<4096) (hj : j<257)
    {P : Point C} (hP : onCurve C P=true) {s : State}
    (h : NafCore K C base size P (Naf5.byte k) (2*Naf5.residual k (j+1)) s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (Naf.digit K) s fun t =>
      ProgKeep K.M base (winOther K) s t ∧
      NafCore K C base size P (Naf5.byte k) (Naf5.residual k j) t := by
  rw [Naf.digit]
  apply WP.seq
  refine WP.mono (nafRead_ok h.field.scr hBits (by have := hL.bits; omega) h19
    (h.stable.bits j hj) .x2) fun u ⟨u2,ku⟩ => ?_
  have cu := h.of_keeps ku (by decide)
  have u19 : u.gpr .x19=BitVec.ofNat 64 j := (ku.gpr _ (by decide)).trans h19
  have kp : ProgKeep K.M base (winOther K) s u := keeps_prog ku (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp [clob])
  refine WP.ite (decide (Naf5.magnitude k j≠0)) (by
    change some (u.read .x .x2 != 0)=_
    rw [read_x,u2,nafByteTest,nafMagnitude_byte]) (fun hn => ?_) (fun hz => ?_)
  · have hm0 : Naf5.magnitude k j≠0 := of_decide_eq_true hn
    apply WP.seq
    refine WP.mono (nafEntry_ok hL hJ hAl hm hTbl hBits hj
      (by rw [nafMagnitude_byte]; omega) (by rw [nafMagnitude_byte]; exact Naf5.magnitude_le k j)
      (by rw [nafMagnitude_byte]; exact (Naf5.magnitude_odd_or_zero k j).resolve_left hm0)
      cu u19 u2) fun v ⟨kv,cv,iv,jv⟩ => ?_
    simp only [nafNegative_byte,nafMagnitude_byte] at jv
    exact WP.mono (nafAdd_ok hL hJ hAl hm hC ha hOne hP (Naf5.onCurve_point hC hP k j)
      (Naf5.add_step hC hP k j) cv iv jv) fun t ⟨kt,ct⟩ => ⟨kp.trans (kv.trans kt),ct⟩
  · have hm0 : Naf5.magnitude k j=0 := by simpa only [ne_eq,not_not] using of_decide_eq_false hz
    have he : Naf5.residual k j=2*Naf5.residual k (j+1) := by
      have hh := Naf5.recurrence k j
      rw [hm0] at hh
      split at hh <;> omega
    apply WP.block_nil
    exact ⟨kp,he.symm ▸ cu⟩

end VG.Proof.Weierstrass.AArch64
