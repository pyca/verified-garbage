module

import VerifiedGarbage.Proof.Ed448.PPC64LE.VDecodeY
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.PPC64LE.ScalarBit
import VerifiedGarbage.Proof.Ed448.PPC64LE.VDecode
import VerifiedGarbage.Proof.Ed448.DecodeBytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ed448.PPC64LE.VChecks
import VerifiedGarbage.Proof.X25519.PPC64LE.Pass

/-!
# Ed448's verification on PPC64LE: `S < L`

`checkS` checks that the 57 bytes of `S` (at `SG + 57`) are below `L`: its
low 448 bits plus `2⁴⁴⁸ - L` do not carry out (scalar reduction's
`subtract_ok`), and its byte 56 is 0 (`checkS_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame
open VG.Impl.X448.PPC64LE (X2 ACC)
open VG.Spec.X448 (P Fe)

theorem L_lt448 : Spec.Ed448.L < 256 ^ 56 := by decide +kernel

/-- 57 bytes are below `L` exactly when the last is 0 and the first 56 are. -/
theorem lt_L_iff (bs : List Byte) (h : bs.length = 57) :
    Spec.Ed448.decodeLE bs < Spec.Ed448.L ↔
      (bs.getD 56 0).toNat = 0 ∧ Spec.Ed448.decodeLE (bs.take 56) < Spec.Ed448.L := by
  rw [Proof.Ed448.decodeLE_57 bs h]
  have := L_lt448
  constructor
  · intro hl
    have h0 : (bs.getD 56 0).toNat = 0 := by
      by_contra hne
      have : 256 ^ 56 ≤ 256 ^ 56 * (bs.getD 56 0).toNat := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
      omega
    exact ⟨h0, by omega⟩
  · rintro ⟨h0, h1⟩
    rw [h0, Nat.mul_zero, Nat.add_zero]; exact h1

section
variable {b : Addr}

theorem checkS_ok {s : State} (hc : VCtx b s) :
    WP isa (.block checkS) s fun t => VCtx b t ∧ Rest [.r5, .r7, .r8, .r9] s t ∧
      Frame [FA b, ⟨b + BitVec.ofNat 64 BAD, 8⟩] s.mem t.mem ∧ FS t.mem b DK = FS s.mem b DK ∧
      (bad t.mem b = 0 ↔ bad s.mem b = 0 ∧
        Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 (SG + 57)) 57) < Spec.Ed448.L) := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hSG : SG = 3345 := rfl
  have hSD : SD = 56 := rfl
  have hX : X2 = 56 := rfl
  have hD : DY = 168 := rfl
  unfold checkS
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (copyIn_ok hc.ctx (p := SG + 57) (by omega) (by omega)) fun s1 h1 => ?_
  have hc1 : VCtx b s1 := hc.of_rest h1.rest (by decide) (by decide)
  refine wp_li (by decide) fun s2 u2 => ?_
  have hc2 : VCtx b s2 := hc1.of_rest (u2.rest (ws := [.r8]) (by decide)) (by decide) (by decide)
  refine WP.append (subtract_ok (o := DY) ⟨by decide, by decide⟩ hc2.ctx (by rw [u2.gpr]; rfl))
    fun s3 ⟨hr3, hf3, _, h83, _⟩ => ?_
  have hc3 : VCtx b s3 := hc2.of_rest hr3 (by decide) (by decide)
  refine WP.append (orBad_ok hc3 (r := .r8) (by decide)) fun s4 ⟨hr4, hf4, hb4⟩ => ?_
  have hc4 : VCtx b s4 := hc3.of_rest hr4 (by decide) (by decide)
  refine wp_lbz (a := b + BitVec.ofNat 64 (SG + 57 + 56)) (by decide) (by omega) (by rw [hc4.ctx.r6])
    (hc4.inR (by omega)) fun s5 u5 => ?_
  have hc5 : VCtx b s5 := hc4.of_rest (u5.rest (ws := [.r7]) (by decide)) (by decide) (by decide)
  refine WP.mono (orBad_ok hc5 (r := .r7) (by decide)) fun t ⟨hrt, hft, hbt⟩ => ?_
  -- The frames.
  have fC : Frame [FA b] s.mem s1.mem := h1.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by omega)⟩
  have fS : Frame [FA b] s2.mem s3.mem := hf3.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega)⟩
  have f3 : Frame [FA b] s.mem s3.mem := fC.trans (by rw [u2.mem] at fS; exact fS)
  have hrt' : Rest [.r5, .r7, .r8, .r9] s t := (h1.rest.mono (by decide)).trans
    (((u2.rest (ws := [.r8]) (by decide)).mono (by decide)).trans ((hr3.mono (by decide)).trans
      ((hr4.mono (by decide)).trans (((u5.rest (ws := [.r7]) (by decide)).mono (by decide)).trans
        (hrt.mono (by decide))))))
  refine ⟨hc.of_rest hrt' (by decide) (by decide), hrt', ?_, ?_, ?_⟩
  · refine (f3.mono (by simp)).trans ((hf4.mono (by simp)).trans ?_)
    rw [← u5.mem]; exact hft.mono (by simp)
  · -- `d` stays.
    have hK : DK = 336 := rfl
    have f : Frame [⟨b + BitVec.ofNat 64 DY, 4 * 14⟩, ⟨b + BitVec.ofNat 64 X2, 4 * 14⟩,
        ⟨b + BitVec.ofNat 64 SD, 56⟩, ⟨b + BitVec.ofNat 64 BAD, 8⟩] s.mem t.mem := by
      refine (h1.frame.mono (by simp)).trans ?_
      rw [u2.mem] at hf3
      refine (hf3.mono (by simp)).trans ((hf4.mono (by simp)).trans ?_)
      rw [← u5.mem]; exact hft.mono (by simp)
    have e := limb_frame (o := DK) f fun r hr k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega)
    rw [FS, V, val32_congr e]; rfl
  · -- The checks.
    have b3 : bad s3.mem b = bad s.mem b := by
      unfold bad
      rw [f3.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)]
    have hB : (s5.gpr .r7).toNat = (s.mem (b + BitVec.ofNat 64 (SG + 57 + 56))).toNat := by
      rw [u5.gpr, toNat_imm (Nat.lt_trans (BitVec.isLt _) (by decide)), hf4 _ fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact fun h => Offset.disjoint b (d := SG + 57 + 56) (n := 1) (e := BAD) (k := 8) (by omega)
            (by omega) (by omega) _ (Region.contains_self _ _) h,
        f3 _ fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact fun h => Offset.disjoint_base b (d := SG + 57 + 56) (n := 1) (k := ACC + 112) (by omega)
            (by omega) _ (Region.contains_self _ _) h]
    have hV : V s2.mem b DY = yw s.mem b (SG + 57) := by
      rw [u2.mem]; exact val32_congr fun j hj => (h1.vals j hj).1
    obtain ⟨e56, eB⟩ := bytes57 (b := b) s.mem (SG + 57)
    rw [hbt, u5.mem, hb4, b3, h83, hB, hV, lt_L_iff _ (by simp [Spec.Ed448.bytesAt]), e56, eB,
      Nat.or_eq_zero_iff, Nat.or_eq_zero_iff]
    have : (if Spec.Ed448.L ≤ yw s.mem b (SG + 57) then 1 else 0) = 0 ↔ yw s.mem b (SG + 57) < Spec.Ed448.L := by
      by_cases h : Spec.Ed448.L ≤ yw s.mem b (SG + 57)
      · rw [ite_eq_left h]; exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h (by omega)⟩
      · rw [ite_eq_right h]; exact ⟨fun _ => by omega, fun _ => rfl⟩
    rw [this]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h3, h2⟩, fun ⟨h1, h3, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

end

end VG.Proof.Ed448.PPC64LE
