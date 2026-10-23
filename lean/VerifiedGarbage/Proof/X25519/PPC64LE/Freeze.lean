module

import VerifiedGarbage.Proof.X25519.PPC64LE.Invert
public import VerifiedGarbage.Proof.X25519.Bytes
public import VerifiedGarbage.Proof.X25519.PPC64LE.Slots
import VerifiedGarbage.Proof.X25519.PPC64LE.Setup
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
import VerifiedGarbage.Proof.X25519.PPC64LE.AddSub
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# X25519 on PPC64LE: the final reduction and the output

`freeze` stores the 32 bytes of the element at `X2`, reduced fully modulo `p`,
at `out` (`freeze_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE

open VG VG.PPC64LE VG.Impl.X25519.PPC64LE
open VG.Spec.X25519 (P Fe bytesAt)
open VG.Proof.X25519 (leBytes)

theorem sel0r (a c : BitVec 64) : a ^^^ ((c ^^^ a) &&& (0 - BitVec.ofNat 64 0)) = a := by simp

theorem sel1r (a c : BitVec 64) : a ^^^ ((c ^^^ a) &&& (0 - BitVec.ofNat 64 1)) = c := by
  have : (0 : BitVec 64) - BitVec.ofNat 64 1 = BitVec.allOnes 64 := by decide
  rw [this, BitVec.and_allOnes, BitVec.xor_comm c, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

section
variable {b : Addr}

/-- The start of `freeze`: bit 255 of `[X2]` cleared, 19 times it in `r8`. -/
theorem freezeA_ok {s : State} (hc : Ctx b s) :
    WP isa (.block freezeA) s fun s' =>
      (s'.gpr .r8).toNat = 19 * (limb s.mem b X2 7 / 2 ^ 31) ∧
      (∀ k < 8, limb s'.mem b X2 k = mask31 (limb s.mem b X2) k) ∧
      Frame [⟨b + BitVec.ofNat 64 X2, 32⟩] s.mem s'.mem ∧
      Rest [.r5, .r7, .r8] s s' := by
  have hX : X2 = 32 := rfl
  simp only [freezeA, low31, List.cons_append, List.nil_append]
  refine lw0_ok hc (d := X2 + 28) (by decide) fun s2 u2 => ?_
  refine wp_lsr (by decide) fun s3 u3 => wp_lsl (by decide) fun s4 u4 =>
    wp_lsr (by decide) fun s5 u5 => ?_
  have hr5 : Rest [.r7, .r8] s s5 :=
    (u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide))))
  have hc5 : Ctx b s5 := hc.of_rest hr5 (by decide)
  refine sw0_ok hc5 (d := X2 + 28) (by decide) fun s6 u6 => ?_
  refine wp_li (by decide) fun s7 u7 => wp_mul fun s8 u8 => WP.block_nil ?_
  have hl7 := limb_lt s.mem b X2 7
  have e2 : (s2.gpr .r7).toNat = limb s.mem b X2 7 := by rw [u2.gpr, toNat_ext32]; rfl
  have e5 : (s5.gpr .r7).toNat = limb s.mem b X2 7 % 2 ^ 31 := by
    rw [u5.gpr, u4.gpr, low31_val, u3.other .r7 (by decide), e2]
  have e3 : (s3.gpr .r8).toNat = limb s.mem b X2 7 / 2 ^ 31 := by
    rw [u3.gpr, toNat_shr, e2]
  have hm6 : s6.mem = s.mem.writeW (b + BitVec.ofNat 64 (X2 + 28)) ((s5.gpr .r7).setWidth 32) := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem]
  have t19 : (BitVec.ofNat 64 19).toNat = 19 := rfl
  refine ⟨?_, fun k hk => ?_, ?_, ?_⟩
  · rw [u8.gpr, u7.gpr, u7.other _ (by decide), u6.gpr, u5.other _ (by decide), u4.other _ (by decide),
      toNat_mul_lt (by rw [e3, t19]; omega_using [hl7]), e3, t19, Nat.mul_comm]
  · rw [limb, u8.mem, u7.mem, hm6]
    rcases Nat.lt_or_ge k 7 with h | h
    · rw [wd_write_other _ _ _ (by omega_using [h]) (by omega_using [hX, h]) (by omega_using [hX])]
      simp only [mask31, show k ≠ 7 by omega_using [h], ite_false]; rfl
    · rw [show X2 + 4 * k = X2 + 28 by omega_using [hk, h], wd_write_self, toNat_lo32, e5,
        show k = 7 by omega_using [hk, h], Nat.mod_eq_of_lt (by omega_using [])]; rfl
  · rw [u8.mem, u7.mem, hm6]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (d := X2 + 28) (n := 32 / 8) (Nat.le_add_right _ _) (by omega_using []) (by omega_using [hX]))
  · exact hr5.mono (by decide) |>.trans ((u6.rest _).trans ((u7.rest (by decide)).trans (u8.rest (by decide))))

/-- `freezeB`: the mask `-(bit 255 of [Y])` in `r11`, and bit 255 of `[Y]` cleared. -/
theorem freezeB_ok {s : State} (hc : Ctx b s) :
    WP isa (.block freezeB) s fun s' =>
      s'.gpr .r11 = 0 - BitVec.ofNat 64 (limb s.mem b Y 7 / 2 ^ 31) ∧
      (∀ k < 8, limb s'.mem b Y k = mask31 (limb s.mem b Y) k) ∧
      Frame [⟨b + BitVec.ofNat 64 Y, 32⟩] s.mem s'.mem ∧ Rest [.r4, .r7, .r11] s s' := by
  have hY : Y = 512 := rfl
  simp only [freezeB, low31, List.cons_append, List.nil_append]
  refine lw0_ok hc (d := Y + 28) (by decide) fun s1 u1 => ?_
  refine wp_lsr (by decide) fun s2 u2 => wp_li (by decide) fun s3 u3 =>
    wp_sub fun s4 u4 => wp_lsl (by decide) fun s5 u5 => wp_lsr (by decide) fun s6 u6 => ?_
  have hr6 : Rest [.r4, .r7, .r11] s s6 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  refine sw0_ok (hc.of_rest hr6 (by decide)) (d := Y + 28) (by decide) fun s7 u7 => WP.block_nil ?_
  have e1 : (s1.gpr .r7).toNat = limb s.mem b Y 7 := by rw [u1.gpr, toNat_ext32]; rfl
  have hm7 : s7.mem = s.mem.writeW (b + BitVec.ofNat 64 (Y + 28)) ((s6.gpr .r7).setWidth 32) := by
    rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨?_, fun k hk => ?_, ?_, hr6.trans (u7.rest _)⟩
  · rw [u7.gpr, u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.gpr, u3.other _ (by decide), u2.gpr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [toNat_shr, e1, toNat_imm (by have := limb_lt s.mem b Y 7; omega_using [this])]
  · rw [limb, hm7]
    rcases Nat.lt_or_ge k 7 with h | h
    · rw [wd_write_other _ _ _ (by omega_using [h]) (by omega_using [hY, h]) (by omega_using [hY])]
      simp only [mask31, show k ≠ 7 by omega_using [h], ite_false]; rfl
    · have hl7 := limb_lt s.mem b Y 7
      rw [show Y + 4 * k = Y + 28 by omega_using [hk, h], wd_write_self, toNat_lo32, u6.gpr, u5.gpr, low31_val,
        u4.other .r7 (by decide), u3.other .r7 (by decide), u2.other .r7 (by decide), e1,
        show k = 7 by omega_using [hk, h], Nat.mod_eq_of_lt (by omega_using [])]; rfl
  · rw [hm7]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (d := Y + 28) (n := 32 / 8) (Nat.le_add_right _ _) (by omega_using []) (by omega_using [hY]))

/-- The output of `freeze` from `s0`, after `j` limbs. -/
structure OutInv (O : Addr) (r : Nat → Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.r5, .r7] s0 s
  frame : Frame [⟨O, 4 * j⟩] s0.mem s.mem
  words : ∀ i < j, wd s.mem O (4 * i) = r i

theorem out_ok {s0 : State} (hc : Ctx b s0) {o : Addr} (h3 : s0.gpr .r3 = o)
    (hout : (⟨o, 32⟩ : Region) ∈ s0.wr)
    (hdisj : Region.Disjoint ⟨b, 4096⟩ ⟨o, 32⟩) {sw : Nat} (hsw : sw ≤ 1)
    (h11 : s0.gpr .r11 = 0 - BitVec.ofNat 64 sw) :
    WP isa (.block ((List.range 8).flatMap outStep)) s0
      (OutInv o (fun k => sel sw (limb s0.mem b X2 k) (limb s0.mem b Y k)) s0 8) := by
  have hX : X2 = 32 := rfl
  have hY : Y = 512 := rfl
  refine wp_range_flatMap (M := isa) _ (fun k s hk h => ?_) 8 (Nat.le_refl _) s0
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
    (by rw [e3]) (by rw [hwr]; exact in_base hout (by omega_using [hk]) (by omega_using [hk]))
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

theorem frame_sub1 {m m' : Mem} {r r' : Region} {rs : List Region} (h : Frame [r] m m') (hs : Region.Sub r r')
    (hr : r' ∈ rs) : Frame rs m m' :=
  h.sub fun x hx => ⟨r', hr, by rw [List.mem_singleton.mp hx]; exact hs⟩

theorem freeze_ok {s : State} (hc : Ctx b s) {o : Addr}
    (h3 : s.gpr .r3 = o) (hout : (⟨o, 32⟩ : Region) ∈ s.wr)
    (hdisj : Region.Disjoint ⟨b, 4096⟩ ⟨o, 32⟩) :
    WP isa (.block freeze) s fun s' =>
      bytesAt s'.mem o 32 = leBytes 32 (V s.mem b X2 % P) ∧ Rest clob s s' ∧
      Frame [FA b, ⟨o, 32⟩] s.mem s'.mem := by
  have hX : X2 = 32 := rfl
  have hY : Y = 512 := rfl
  have hl : ∀ k < 8, limb s.mem b X2 k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  obtain ⟨tA, tY, hS, hR, hv⟩ := freeze_facts hl
  obtain ⟨-, -, lm, c1⟩ := mask31_facts hl
  simp only [freeze, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (freezeA_ok hc) fun s1 ⟨h8, hl1, hf1, hr1⟩ => ?_
  have hc1 : Ctx b s1 := hc.of_rest hr1 (by decide)
  refine WP.append (pass_ok (rb := .r6) (o := X2) (s0 := s1) (c := mask31 (limb s.mem b X2))
    (cin := 19 * (limb s.mem b X2 7 / 2 ^ 31)) (by decide) (by decide) (by decide)
    (fun k hk => by rw [hc1.r6]; exact hc1.inW (by omega_using [hX, hk])) h8
    (fun k hk => by have := lm k hk; omega_using [this]) (by omega_using [c1]) ?_) fun s2 hp2 => ?_
  · intro k hk s' hp
    refine WP.mono (ldSrc_ok (hc1.of_rest hp.rest (by decide)) (o := X2) (k := k) (by omega_using [hX, hk]))
      fun t ht => ⟨?_, ht.2.1.mono (by decide), ht.2.2⟩
    rw [ht.1, wd_pass hc1 hp.frame (by omega_using []) (by omega_using [hX, hk]) (by omega_using [hX, hk])]
    exact hl1 k hk
  have hc2 : Ctx b s2 := hc1.of_rest hp2.rest (by decide)
  have hpo2 : ∀ j < 8, wd s2.mem b (X2 + 4 * j) = frA (limb s.mem b X2) j :=
    fun j hj => by have := hp2.outs j hj; rwa [hc1.r6] at this
  have hpf2 : Frame [⟨b + BitVec.ofNat 64 X2, 32⟩] s1.mem s2.mem := by
    have := hp2.frame; rwa [hc1.r6] at this
  refine wp_li (by decide) fun s3 u3 => ?_
  have hc3 : Ctx b s3 := hc2.of_rest (u3.rest (ws := [.r8]) (by decide)) (by decide)
  refine WP.append (pass_ok (rb := .r6) (o := Y) (s0 := s3) (c := frA (limb s.mem b X2))
    (cin := 19) (by decide) (by decide) (by decide)
    (fun k hk => by rw [hc3.r6]; exact hc3.inW (by omega_using [hY, hk]))
    (by rw [u3.gpr]; rfl) (fun k hk => by have := out_lt (mask31 (limb s.mem b X2)) (19 * (limb s.mem b X2 7 / 2 ^ 31)) k; unfold frA; omega_using [this]) (by decide) ?_) fun s4 hp4 => ?_
  · intro k hk s' hp
    refine WP.mono (ldSrc_ok (hc3.of_rest hp.rest (by decide)) (o := X2) (k := k) (by omega_using [hX, hk]))
      fun t ht => ⟨?_, ht.2.1.mono (by decide), ht.2.2⟩
    rw [ht.1, wd_pass hc3 hp.frame (by omega_using [hX, hY, hk]) (by omega_using [hX, hk]) (by omega_using [hY, hk]), u3.mem]
    exact hpo2 k hk
  have hc4 : Ctx b s4 := hc3.of_rest hp4.rest (by decide)
  have hpo4 : ∀ j < 8, wd s4.mem b (Y + 4 * j) = frY (limb s.mem b X2) j :=
    fun j hj => by have := hp4.outs j hj; rwa [hc3.r6] at this
  have hpf4 : Frame [⟨b + BitVec.ofNat 64 Y, 32⟩] s3.mem s4.mem := by
    have := hp4.frame; rwa [hc3.r6] at this
  have hx4 : ∀ k < 8, limb s4.mem b X2 k = frA (limb s.mem b X2) k := by
    intro k hk
    rw [limb, wd_frame hpf4 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hX, hY, hk])) (by omega_using [hX, hk]) (by omega_using [hY]),
      u3.mem, hpo2 k hk]
  refine WP.append (freezeB_ok hc4) fun s5 ⟨h11, hy5, hf5, hr5⟩ => ?_
  have hc5 : Ctx b s5 := hc4.of_rest hr5 (by decide)
  have hx5 : ∀ k < 8, limb s5.mem b X2 k = frA (limb s.mem b X2) k := by
    intro k hk
    rw [limb, wd_frame hf5 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hX, hY, hk])) (by omega_using [hX, hk]) (by omega_using [hY])]
    exact hx4 k hk
  have hy5' : ∀ k < 8, limb s5.mem b Y k = mask31 (frY (limb s.mem b X2)) k := by
    intro k hk
    rw [hy5 k hk]
    simp only [mask31]
    split
    · rename_i h; subst h; rw [limb, hpo4 7 (by decide)]
    · rw [limb, hpo4 k hk]
  have h11' : s5.gpr .r11 = 0 - BitVec.ofNat 64 (frS (limb s.mem b X2)) := by
    rw [h11, limb, hpo4 7 (by decide)]; rfl
  have hr45 : Rest [.r4, .r5, .r7, .r8, .r11] s s5 :=
    (hr1.mono (by decide)).trans ((hp2.rest.mono (by decide)).trans ((u3.rest (by decide)).trans
      ((hp4.rest.mono (by decide)).trans (hr5.mono (by decide)))))
  refine WP.mono (out_ok hc5 (o := o) (by rw [hr45.gpr _ (by decide), h3]) (by rw [hr45.wr]; exact hout)
    hdisj hS h11') fun s6 h6' => ⟨?_, ?_, ?_⟩
  · have hr : ∀ k < 8, sel (frS (limb s.mem b X2)) (limb s5.mem b X2 k)
        (limb s5.mem b Y k) = frR (limb s.mem b X2) k := fun k hk => by
      rw [hx5 k hk, hy5' k hk]; rfl
    rw [V, ← hv]
    refine Proof.X25519.bytesAt_leBytes_words32 _ _ _ fun j hj => ?_
    have := h6'.words j hj
    unfold wd at this
    rw [this, hr j hj, val32_div hR hj]
  · exact (hr45.mono (by decide)).trans (h6'.rest.mono (by decide))
  · have hfa : ∀ z, z + 32 ≤ ACC → Region.Sub ⟨b + BitVec.ofNat 64 z, 32⟩ (FA b) :=
      fun z h1 => Offset.sub_base _ (by rw [ACC_eq] at h1 ⊢; omega_using [h1])
    have hA := ACC_eq
    refine (frame_sub1 hf1 (hfa X2 (by omega_using [hX, hA])) (List.mem_cons_self ..)).trans ?_
    refine (frame_sub1 hpf2 (hfa X2 (by omega_using [hX, hA])) (List.mem_cons_self ..)).trans ?_
    rw [← u3.mem]
    refine (frame_sub1 hpf4 (hfa Y (by omega_using [hY, hA])) (List.mem_cons_self ..)).trans ?_
    refine (frame_sub1 hf5 (hfa Y (by omega_using [hY, hA])) (List.mem_cons_self ..)).trans ?_
    exact frame_sub1 h6'.frame (Region.sub_prefix (by omega_using [])) (List.mem_cons_of_mem _ (List.mem_singleton_self _))

end

end VG.Proof.X25519.PPC64LE
