module

import VerifiedGarbage.Proof.X448.PPC64LE.Slots
public import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.X448.PPC64LE.Setup
import VerifiedGarbage.Proof.X448.PPC64LE.Mul
import VerifiedGarbage.Proof.X25519.PPC64LE.Freeze
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.X448.PPC64LE.Field

/-!
# X448 on PPC64LE: the final reduction and the output

`freeze` stores the 56 bytes of the element at `X2`, reduced fully modulo `p`,
at `out` (`freeze_ok`).
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE

open VG VG.PPC64LE VG.Impl.X448.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X448 (P Fe bytesAt)
open VG.Proof.X25519 (leBytes leNum)

/-- Fourteen little-endian words in memory are the 56 bytes of their number. -/
theorem bytesAt_words14 (m : Mem) (p : Addr) {r : Nat → Nat} (h : ∀ j < 14, wd m p (4 * j) = r j) :
    bytesAt m p 56 = leBytes 56 (val32 r 14) := by
  have e : bytesAt m p 56 = leBytes 56 (leNum (bytesAt m p 56)) := by
    rw [Proof.X448.leNum_bytesAt_read]; exact Proof.X25519.bytesAt_leBytes m p 56
  rw [e, show (56 : Nat) = 4 * 14 from rfl, leNum_bytesAt4, val32_congr (f := uWord m p) h]

section
variable {b : Addr}

/-- The output of `freeze` from `s0`, after `j` limbs. -/
structure OutInv (O : Addr) (r : Nat → Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.r5, .r7] s0 s
  frame : Frame [⟨O, 4 * j⟩] s0.mem s.mem
  words : ∀ i < j, wd s.mem O (4 * i) = r i

theorem out_ok {s0 : State} (hc : Ctx b s0) {o : Addr} (h3 : s0.gpr .r3 = o)
    (hout : ∀ k < 14, InRegions s0.wr (o + BitVec.ofNat 64 (4 * k)) 4)
    (hdisj : Region.Disjoint ⟨b, 4096⟩ ⟨o, 56⟩) {sw : Nat} (hsw : sw ≤ 1)
    (h11 : s0.gpr .r11 = 0 - BitVec.ofNat 64 sw) :
    WP isa (.block ((List.range 14).flatMap outStep)) s0
      (OutInv o (fun k => sel sw (limb s0.mem b X2 k) (limb s0.mem b Y k)) s0 14) := by
  have hX : X2 = 56 := rfl
  have hY : Y = 896 := rfl
  refine wp_range_flatMap (M := isa) _ (fun k s hk h => ?_) 14 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hcs : Ctx b s := hc.of_rest h.rest (by decide)
  -- The words of the working space are as in `s0`.
  have hw : ∀ d, d + 4 ≤ 4096 → wd s.mem b d = wd s0.mem b d := fun d hd =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hdisj.sub_left (Offset.sub_base _ hd)).sub_right (Region.sub_prefix (by omega_using [hk]))
  unfold outStep
  refine lw0_ok hcs (d := X2 + 4 * k) (by omega_using [hX, hk]) fun t1 v1 => ?_
  refine lw0_ok (hcs.of_rest (v1.rest (ws := [.r5]) (by decide)) (by decide)) (d := Y + 4 * k)
    (by omega_using [hY, hk]) fun t2 v2 => ?_
  refine wp_xor fun t3 v3 => wp_and fun t4 v4 => wp_xor fun t5 v5 => ?_
  have hr5 : Rest [.r5, .r7] s t5 :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (v5.rest (by decide)))))
  have e3 : t5.gpr .r3 = o := by rw [hr5.gpr _ (by decide), h.rest.gpr _ (by decide), h3]
  have hwr : t5.wr = s0.wr := by rw [hr5.wr, h.rest.wr]
  refine wp_sw (a := o + BitVec.ofNat 64 (4 * k)) (by decide) (by omega_using [hk])
    (by rw [e3]) (by rw [hwr]; exact hout k hk)
    fun t6 v6 => WP.block_nil ?_
  -- The limb selected.
  have ev : ((t5.gpr .r5).setWidth 32).toNat = sel sw (limb s0.mem b X2 k) (limb s0.mem b Y k) := by
    have ex : t2.gpr .r5 = (s.mem.readW (b + BitVec.ofNat 64 (X2 + 4 * k)) 32).setWidth 64 := by
      rw [v2.other _ (by decide), v1.gpr]
    have ey : t2.gpr .r7 = (s.mem.readW (b + BitVec.ofNat 64 (Y + 4 * k)) 32).setWidth 64 := by
      rw [v2.gpr, v1.mem]
    have em : t3.gpr .r11 = 0 - BitVec.ofNat 64 sw := by
      rw [v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide), h.rest.gpr _ (by decide), h11]
    rw [v5.gpr, v4.other .r5 (by decide), v4.gpr, v3.other .r5 (by decide), v3.gpr, em, ex, ey]
    have hx := hw (X2 + 4 * k) (by omega_using [hX, hk])
    have hy := hw (Y + 4 * k) (by omega_using [hY, hk])
    unfold wd at hx hy
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [sel0r, lo32_ext, hx]; rfl
    · rw [sel1r, lo32_ext, hy]; rfl
  have hm6 : t6.mem = s.mem.writeW (o + BitVec.ofNat 64 (4 * k)) ((t5.gpr .r5).setWidth 32) := by
    rw [v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  refine ⟨h.rest.trans (hr5.trans (v6.rest _)), ?_, fun i hi => ?_⟩
  · rw [hm6]
    exact (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using []) (by omega_using [hk]))
  · rw [hm6]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega_using [hk, hi]) (by omega_using [hk])]; exact h.words i hi
    · rw [wd_write_self, ev]

theorem freeze_ok {s : State} (hc : Ctx b s) {o : Addr}
    (h3 : s.gpr .r3 = o) (hout : ∀ k < 14, InRegions s.wr (o + BitVec.ofNat 64 (4 * k)) 4)
    (hdisj : Region.Disjoint ⟨b, 4096⟩ ⟨o, 56⟩) :
    WP isa (.block freeze) s fun s' =>
      bytesAt s'.mem o 56 = leBytes 56 (V s.mem b X2 % P) ∧ Rest clob s s' ∧
      Frame [⟨b + BitVec.ofNat 64 Y, 56⟩, ⟨o, 56⟩] s.mem s'.mem ∧
      val32 (fun j => wd s'.mem o (4 * j)) 14 = V s.mem b X2 % P := by
  have hX : X2 = 56 := rfl
  have hY : Y = 896 := rfl
  have hA := ACC_eq
  have hl : ∀ k < 14, limb s.mem b X2 k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  obtain ⟨hS, hR, hv⟩ := freeze_facts hl
  obtain ⟨hf1, -, -⟩ := fold1_facts hl (c := 1) (by decide)
  simp only [freeze, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => ?_
  have hr2 : Rest [.r8, .r10] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  have e10 : (s2.gpr .r10).toNat = 1 := by rw [u2.gpr]; rfl
  refine WP.append (pass_ok (rb := .r6) (o := Y) (s0 := s2) (c := foldL (limb s.mem b X2) 1)
    (cin := 1) (by decide) (by decide) (by decide)
    (fun k hk => by rw [hc2.r6]; exact hc2.inW (by omega_using [hY, hk]))
    (by rw [u2.other _ (by decide), u1.gpr]; rfl) hf1 (by decide) ?_) fun s3 hp3 => ?_
  · intro k hk s' hp
    have hc' : Ctx b s' := hc2.of_rest hp.rest (by decide)
    have ew : wd s'.mem b (X2 + 4 * k) = limb s.mem b X2 k := by
      rw [wd_pass hc2 hp.frame (by omega_using [hX, hY, hk]) (by omega_using [hX, hk]) (by omega_using [hY, hk]), hm2]; rfl
    unfold foldSrc
    refine WP.append (ldSrc_ok hc' (by omega_using [hX, hk])) fun t ⟨h7, hr, hm⟩ => ?_
    by_cases h7k : k = 7
    · simp only [h7k, ite_true]
      refine wp_add fun t1 v1 => WP.block_nil ⟨?_, (hr.trans (v1.rest (by decide))).mono (by decide),
        by rw [v1.mem, hm]⟩
      have e : (t.gpr .r10).toNat = 1 := by rw [hr.gpr _ (by decide), hp.rest.gpr _ (by decide), e10]
      have := limb_lt s.mem b X2 k
      rw [v1.gpr, toNat_add_lt (by rw [h7, ew, e]; omega_using [this]), h7, ew, e, foldL, h7k]; rfl
    · simp only [h7k, ite_false]
      exact WP.block_nil ⟨by rw [h7, ew, foldL]; simp only [h7k, ite_false, Nat.add_zero],
        hr.mono (by decide), hm⟩
  have hc3 : Ctx b s3 := hc2.of_rest hp3.rest (by decide)
  have hpo3 : ∀ j < 14, wd s3.mem b (Y + 4 * j) = fold1 (limb s.mem b X2) 1 j :=
    fun j hj => by have := hp3.outs j hj; rwa [hc2.r6] at this
  have hpf3 : Frame [⟨b + BitVec.ofNat 64 Y, 56⟩] s2.mem s3.mem := by
    have := hp3.frame; rwa [hc2.r6] at this
  refine wp_li (by decide) fun s4 u4 => wp_sub fun s5 u5 => ?_
  have hr5 : Rest [.r4, .r11] s3 s5 := (u4.rest (by decide)).trans (u5.rest (by decide))
  have hc5 : Ctx b s5 := hc3.of_rest hr5 (by decide)
  have hm5 : s5.mem = s3.mem := by rw [u5.mem, u4.mem]
  have h11 : s5.gpr .r11 = 0 - BitVec.ofNat 64 (fold1C (limb s.mem b X2) 1) := by
    rw [u5.gpr, u4.gpr, u4.other _ (by decide)]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [hp3.r8, toNat_imm (by omega_using [hS])]; rfl
  have hx5 : ∀ k < 14, limb s5.mem b X2 k = limb s.mem b X2 k := by
    intro k hk
    rw [limb, hm5, wd_frame hpf3 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hX, hY, hk])) (by omega_using [hX, hk]) (by omega_using [hY]),
      hm2]; rfl
  have hy5 : ∀ k < 14, limb s5.mem b Y k = fold1 (limb s.mem b X2) 1 k := by
    intro k hk; rw [limb, hm5, hpo3 k hk]
  have hr45 : Rest [.r4, .r5, .r7, .r8, .r10, .r11] s s5 :=
    (hr2.mono (by decide)).trans ((hp3.rest.mono (by decide)).trans (hr5.mono (by decide)))
  refine WP.mono (out_ok hc5 (o := o) (by rw [hr45.gpr _ (by decide), h3]) (by rw [hr45.wr]; exact hout)
    hdisj hS h11) fun s6 h6' => ⟨?_, ?_, ?_, ?_⟩
  · rw [V, ← hv]
    refine bytesAt_words14 _ _ fun j hj => ?_
    rw [h6'.words j hj, hx5 j hj, hy5 j hj]; rfl
  · exact (hr45.mono (by decide)).trans (h6'.rest.mono (by decide))
  · have f1 : Frame [⟨b + BitVec.ofNat 64 Y, 56⟩, ⟨o, 56⟩] s2.mem s3.mem :=
      frame_sub1 hpf3 (Region.sub_prefix (Nat.le_refl _)) (List.mem_cons_self ..)
    have f2 : Frame [⟨b + BitVec.ofNat 64 Y, 56⟩, ⟨o, 56⟩] s5.mem s6.mem :=
      frame_sub1 h6'.frame (Region.sub_prefix (by omega_using []))
        (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    rw [hm5] at f2
    rw [← hm2]
    exact f1.trans f2
  · rw [V, ← hv]
    exact val32_congr fun j hj => by rw [h6'.words j hj, hx5 j hj, hy5 j hj]; rfl

end

end VG.Proof.X448.PPC64LE
