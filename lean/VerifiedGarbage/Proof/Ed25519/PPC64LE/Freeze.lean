module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Freeze
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Field
import VerifiedGarbage.Proof.X25519.PPC64LE.Freeze
import VerifiedGarbage.Proof.X25519.PPC64LE.AddSub
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Field
public import VerifiedGarbage.Proof.X25519.PPC64LE.Field

/-!
# Ed25519 on PPC64LE: an element reduced fully

`freeze a` leaves at `FR` the limbs of the element of slot `a` modulo `p`
(`freeze_ok`): X25519's final reduction (`Proof/X25519/PPC64LE/Freeze.lean`,
its steps at `FR` and `FY`), with the result selected back into `FR`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X25519 (P)

theorem FR_eq : FR = 864 := rfl
theorem FY_eq : FY = 896 := rfl

section
variable {b : Addr}

/-- The slot's limbs copied to `FR`. -/
theorem freezeCopy_ok {s : State} (hc : Ctx b s) (a : Slot) :
    WP isa (.block (freezeCopy a)) s fun t =>
      Rest [.r7] s t ∧ Frame [⟨b + BitVec.ofNat 64 FR, 32⟩] s.mem t.mem ∧
      ∀ k < 8, limb t.mem b FR k = limb s.mem b (offset a) k := by
  have ha := slot_range a
  have hF := FR_eq
  refine WP.mono (fill_ok (o := FR) (src := fun k => [.load .w .r7 .r6 (offset a + 4 * k)])
    (f := limb s.mem b (offset a)) hc (by omega) fun k hk t h => ?_) fun t h => ⟨h.rest, h.frame, h.outs⟩
  refine lw0_ok (hc.of_rest h.rest (by decide)) (d := offset a + 4 * k) (by omega) fun u v =>
    WP.block_nil ⟨?_, v.rest (by decide), v.mem⟩
  rw [v.gpr, toNat_ext32, Nat.mod_eq_of_lt (BitVec.isLt _)]
  show wd t.mem b (offset a + 4 * k) = _
  refine wd_frame h.frame fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)

/-- A prefix of eight limb stores, each source writing `r5` and `r7`. -/
structure FillInv5 (b : Addr) (o : Nat) (s0 : State) (f : Nat → Nat) (k : Nat) (s : State) : Prop where
  rest : Rest [.r5, .r7] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, limb s.mem b o j = f j

theorem fill5_ok {o : Nat} {src : Nat → List Instr} {s0 : State}
    {f : Nat → Nat} (hc : Ctx b s0) (ho : o + 32 ≤ 4096)
    (hsrc : ∀ k < 8, ∀ s, FillInv5 b o s0 f k s →
      WP isa (.block (src k)) s fun t =>
        (t.gpr .r7).toNat % 2 ^ 32 = f k ∧ Rest [.r5, .r7] s t ∧ t.mem = s.mem) :
    WP isa (.block ((List.range 8).flatMap fun k =>
      src k ++ ([.store .w .r7 .r6 (o + 4 * k)] : List Instr))) s0 (FillInv5 b o s0 f 8) := by
  refine wp_range_flatMap (M := isa) (FillInv5 b o s0 f) (fun k s hk h => ?_)
    8 (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩
  refine WP.append (hsrc k hk s h) fun t ⟨hv, hr, hm⟩ => ?_
  refine sw0_ok ((hc.of_rest h.rest (by decide)).of_rest hr (by decide))
    (by omega) fun u hu => WP.block_nil ?_
  have em : u.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + 4 * k)) ((t.gpr .r7).setWidth 32) := by
    rw [hu.mem, hm]
  refine ⟨h.rest.trans (hr.trans (hu.rest _)), ?_, fun j hj => ?_⟩
  · rw [em]
    refine (h.frame.sub fun r hmem => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_add_right _ _)
        (by omega) (by omega))
    rw [List.mem_singleton.mp hmem]
    exact Region.sub_prefix (by omega)
  · rw [limb, em]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      exact h.outs j hj
    · rw [wd_write_self, toNat_lo32, hv]

/-- After `j` limbs of the selection from `s0`. -/
theorem freezeSelect_ok {s0 : State} (hc : Ctx b s0) {sw : Nat} (hsw : sw ≤ 1)
    (h11 : s0.gpr .r11 = 0 - BitVec.ofNat 64 sw) :
    WP isa (.block freezeSelect) s0 fun t =>
      Rest [.r5, .r7] s0 t ∧ Frame [⟨b + BitVec.ofNat 64 FR, 32⟩] s0.mem t.mem ∧
      ∀ k < 8, limb t.mem b FR k = sel sw (limb s0.mem b FR k) (limb s0.mem b FY k) := by
  have hF := FR_eq
  have hY := FY_eq
  refine WP.mono (fill5_ok (o := FR) (f := fun k => sel sw (limb s0.mem b FR k) (limb s0.mem b FY k)) hc
    (by omega) fun k hk t h => ?_) fun t h => ⟨h.rest, h.frame, h.outs⟩
  have hct : Ctx b t := hc.of_rest h.rest (by decide)
  have hw : ∀ d, d + 4 ≤ FR ∨ FR + 4 * k ≤ d → d + 4 ≤ 4096 → wd t.mem b d = wd s0.mem b d := fun d hd hd' =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ hd (by omega) (by omega)
  unfold selectSrc
  refine lw0_ok hct (d := FR + 4 * k) (by omega) fun t1 v1 => ?_
  refine lw0_ok (hct.of_rest (v1.rest (ws := [.r7]) (by decide)) (by decide)) (d := FY + 4 * k) (by omega)
    fun t2 v2 => ?_
  refine wp_xor fun t3 v3 => wp_and fun t4 v4 => wp_xor fun t5 v5 => WP.block_nil ⟨?_, ?_, ?_⟩
  · have em : t3.gpr .r11 = 0 - BitVec.ofNat 64 sw := by
      rw [v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide), h.rest.gpr _ (by decide), h11]
    have ex : t2.gpr .r7 = (t.mem.readW (b + BitVec.ofNat 64 (FR + 4 * k)) 32).setWidth 64 := by
      rw [v2.other _ (by decide), v1.gpr]
    have ey : t2.gpr .r5 = (t.mem.readW (b + BitVec.ofNat 64 (FY + 4 * k)) 32).setWidth 64 := by
      rw [v2.gpr, v1.mem]
    have hx := hw (FR + 4 * k) (.inr (by omega)) (by omega)
    have hy := hw (FY + 4 * k) (.inr (by omega)) (by omega)
    unfold wd at hx hy
    rw [v5.gpr, v4.other .r7 (by decide), v4.gpr, v3.other .r7 (by decide), v3.gpr, em, ex, ey]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [sel0r, toNat_ext32, hx]; exact Nat.mod_eq_of_lt (BitVec.isLt _)
    · rw [sel1r, toNat_ext32, hy]; exact Nat.mod_eq_of_lt (BitVec.isLt _)
  · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (v5.rest (by decide)))))
  · rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]

/-- **The element of slot `a` modulo `p`**, its limbs `frR` at `FR`. -/
theorem freeze_ok {s : State} (hc : Ctx b s) (a : Slot) :
    WP isa (.block (freeze a)) s fun t =>
      Rest [.r4, .r5, .r7, .r8, .r11] s t ∧ Frame [⟨b + BitVec.ofNat 64 FR, 64⟩] s.mem t.mem ∧
      (∀ k < 8, limb t.mem b FR k = frR (limb s.mem b (offset a)) k) ∧
      V t.mem b FR = V s.mem b (offset a) % P := by
  have hX := FR_eq
  have hY := FY_eq
  have hl : ∀ k < 8, limb s.mem b (offset a) k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  obtain ⟨tA, tY, hS, hR, hv⟩ := freeze_facts hl
  obtain ⟨-, -, lm, c1⟩ := mask31_facts hl
  unfold freeze freezeCore
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (freezeCopy_ok hc a) fun s0 ⟨r0, f0, l0⟩ => ?_
  have hc0 : Ctx b s0 := hc.of_rest r0 (by decide)
  have hl0 : limb s0.mem b FR = fun k => if k < 8 then limb s.mem b (offset a) k else limb s0.mem b FR k := by
    funext k; split
    · exact l0 k ‹_›
    · rfl
  refine WP.append (freezeA_ok (X2 := FR) (by omega) hc0) fun s1 ⟨h8, hl1, hf1, hr1⟩ => ?_
  have hl1' : ∀ k < 8, limb s1.mem b FR k = mask31 (limb s.mem b (offset a)) k := fun k hk => by
    rw [hl1 k hk]
    simp only [mask31]
    split
    · rename_i h; subst h; rw [l0 7 (by decide)]
    · rw [l0 k hk]
  have h8' : (s1.gpr .r8).toNat = 19 * (limb s.mem b (offset a) 7 / 2 ^ 31) := by rw [h8, l0 7 (by decide)]
  have hc1 : Ctx b s1 := hc0.of_rest hr1 (by decide)
  refine WP.append (pass_ok (rb := .r6) (o := FR) (s0 := s1) (c := mask31 (limb s.mem b (offset a)))
    (cin := 19 * (limb s.mem b (offset a) 7 / 2 ^ 31)) (by decide) (by decide) (by omega)
    (fun k hk => by rw [hc1.r6]; exact hc1.inW (by omega)) h8'
    (fun k hk => by have := lm k hk; omega) (by omega) ?_) fun s2 hp2 => ?_
  · intro k hk s' hp
    refine WP.mono (ldSrc_ok (hc1.of_rest hp.rest (by decide)) (o := FR) (k := k) (by omega))
      fun t ht => ⟨?_, ht.2.1.mono (by decide), ht.2.2⟩
    rw [ht.1, wd_pass hc1 hp.frame (by omega) (by omega) (by omega)]
    exact hl1' k hk
  have hc2 : Ctx b s2 := hc1.of_rest hp2.rest (by decide)
  have hpo2 : ∀ j < 8, wd s2.mem b (FR + 4 * j) = frA (limb s.mem b (offset a)) j :=
    fun j hj => by have := hp2.outs j hj; rwa [hc1.r6] at this
  have hpf2 : Frame [⟨b + BitVec.ofNat 64 FR, 32⟩] s1.mem s2.mem := by
    have := hp2.frame; rwa [hc1.r6] at this
  refine wp_li (by decide) fun s3 u3 => ?_
  have hc3 : Ctx b s3 := hc2.of_rest (u3.rest (ws := [.r8]) (by decide)) (by decide)
  refine WP.append (pass_ok (rb := .r6) (o := FY) (s0 := s3) (c := frA (limb s.mem b (offset a)))
    (cin := 19) (by decide) (by decide) (by omega)
    (fun k hk => by rw [hc3.r6]; exact hc3.inW (by omega))
    (by rw [u3.gpr]; rfl) (fun k hk => by
      have := out_lt (mask31 (limb s.mem b (offset a))) (19 * (limb s.mem b (offset a) 7 / 2 ^ 31)) k
      unfold frA; omega) (by decide) ?_) fun s4 hp4 => ?_
  · intro k hk s' hp
    refine WP.mono (ldSrc_ok (hc3.of_rest hp.rest (by decide)) (o := FR) (k := k) (by omega))
      fun t ht => ⟨?_, ht.2.1.mono (by decide), ht.2.2⟩
    rw [ht.1, wd_pass hc3 hp.frame (by omega) (by omega) (by omega), u3.mem]
    exact hpo2 k hk
  have hc4 : Ctx b s4 := hc3.of_rest hp4.rest (by decide)
  have hpo4 : ∀ j < 8, wd s4.mem b (FY + 4 * j) = frY (limb s.mem b (offset a)) j :=
    fun j hj => by have := hp4.outs j hj; rwa [hc3.r6] at this
  have hpf4 : Frame [⟨b + BitVec.ofNat 64 FY, 32⟩] s3.mem s4.mem := by
    have := hp4.frame; rwa [hc3.r6] at this
  have hx4 : ∀ k < 8, limb s4.mem b FR k = frA (limb s.mem b (offset a)) k := by
    intro k hk
    rw [limb, wd_frame hpf4 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega),
      u3.mem, hpo2 k hk]
  refine WP.append (freezeB_ok (Y := FY) (by omega) hc4) fun s5 ⟨h11, hy5, hf5, hr5⟩ => ?_
  have hc5 : Ctx b s5 := hc4.of_rest hr5 (by decide)
  have hx5 : ∀ k < 8, limb s5.mem b FR k = frA (limb s.mem b (offset a)) k := by
    intro k hk
    rw [limb, wd_frame hf5 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)]
    exact hx4 k hk
  have hy5' : ∀ k < 8, limb s5.mem b FY k = mask31 (frY (limb s.mem b (offset a))) k := by
    intro k hk
    rw [hy5 k hk]
    simp only [mask31]
    split
    · rename_i h; subst h; rw [limb, hpo4 7 (by decide)]
    · rw [limb, hpo4 k hk]
  have h11' : s5.gpr .r11 = 0 - BitVec.ofNat 64 (frS (limb s.mem b (offset a))) := by
    rw [h11, limb, hpo4 7 (by decide)]; rfl
  refine WP.mono (freezeSelect_ok hc5 hS h11') fun t ⟨rt, ft, lt⟩ => ⟨?_, ?_, ?_, ?_⟩
  · exact (r0.mono (by decide)).trans ((hr1.mono (by decide)).trans ((hp2.rest.mono (by decide)).trans
      ((u3.rest (by decide)).trans ((hp4.rest.mono (by decide)).trans ((hr5.mono (by decide)).trans
        (rt.mono (by decide)))))))
  · have hs1 : ∀ z, z = FR ∨ z = FY → Region.Sub ⟨b + BitVec.ofNat 64 z, 32⟩ ⟨b + BitVec.ofNat 64 FR, 64⟩ :=
      fun z hz => by rcases hz with rfl | rfl <;> exact Offset.sub _ (by omega) (by omega)
    refine (frame_sub1 f0 (hs1 FR (.inl rfl)) (List.mem_singleton_self _)).trans ?_
    refine (frame_sub1 hf1 (hs1 FR (.inl rfl)) (List.mem_singleton_self _)).trans ?_
    refine (frame_sub1 hpf2 (hs1 FR (.inl rfl)) (List.mem_singleton_self _)).trans ?_
    rw [← u3.mem]
    refine (frame_sub1 hpf4 (hs1 FY (.inr rfl)) (List.mem_singleton_self _)).trans ?_
    refine (frame_sub1 hf5 (hs1 FY (.inr rfl)) (List.mem_singleton_self _)).trans ?_
    exact frame_sub1 ft (hs1 FR (.inl rfl)) (List.mem_singleton_self _)
  · intro k hk
    rw [lt k hk, hx5 k hk, hy5' k hk]; rfl
  · rw [V, val32_congr (g := frR (limb s.mem b (offset a))) fun k hk => (lt k hk).trans (by rw [hx5 k hk, hy5' k hk]; rfl), hv]
    rfl

end

end VG.Proof.Ed25519.PPC64LE
