module

public import VerifiedGarbage.Proof.X448.PPC64LE.Ladder
public import VerifiedGarbage.Spec.X448.Contract
public import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseEncode
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseSel
import VerifiedGarbage.Proof.X448.PPC64LE.Freeze
import VerifiedGarbage.Proof.X448.PPC64LE.Mul
import VerifiedGarbage.Proof.X448.Field
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.X25519.PPC64LE.Pass
public import VerifiedGarbage.Proof.Ed448.PPC64LE.VChecks
public import VerifiedGarbage.Proof.X448.PPC64LE.Slots
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseInit
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseBits
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.WriteBytes

/-! ### `Ed448.PPC64LE.VDecodeY`, which this module and modules that import it used -/

section

/-!
# Ed448's verification on PPC64LE: the y-coordinate of a point

`decodeY p` copies the words of the 56 bytes at `p` into `DY` and `X2`,
checks that they are their full reduction (so `y < p`) and that bits 0–6
of byte 56 are 0, stores bit 7 at `SIGN`, and writes 1 to `DON`
(`decodeY_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Impl.X448.PPC64LE (X2 Y ACC freeze)
open VG.Spec.X448 (P)

/-- The number of the 56 bytes at `p`, as fourteen words. -/
def yw (m : Mem) (b : Addr) (p : Nat) : Nat := val32 (fun k => wd m b (p + 4 * k)) 14

section
variable {b : Addr}

/-- After `k` words of the copy. -/
structure CpInv (b : Addr) (p : Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.r7] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 DY, 4 * k⟩, ⟨b + BitVec.ofNat 64 X2, 4 * k⟩] s0.mem s.mem
  vals : ∀ j < k, limb s.mem b DY j = wd s0.mem b (p + 4 * j) ∧ limb s.mem b X2 j = wd s0.mem b (p + 4 * j)

theorem copyIn_ok {s0 : State} (hc : Ctx b s0) {p : Nat} (hp : p + 56 ≤ 4096) (hp' : 1064 ≤ p) :
    WP isa (.block ((List.range 14).flatMap fun k => [.load .w .r7 .r6 (p + 4 * k),
      .store .w .r7 .r6 (DY + 4 * k), .store .w .r7 .r6 (X2 + 4 * k)])) s0 (CpInv b p s0 14) := by
  have hX : X2 = 56 := rfl
  have hD : DY = 168 := rfl
  refine wp_range_flatMap (M := isa) (CpInv b p s0) (fun k s hk h => ?_) 14 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  obtain hcs : Ctx b s := hc.of_rest h.rest (by decide)
  obtain win : wd s.mem b (p + 4 * k) = wd s0.mem b (p + 4 * k) :=
    wd_frame h.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
      · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  refine lw0_ok hcs (d := p + 4 * k) (by omega_arith) fun t1 v1 => ?_
  obtain hc1 : Ctx b t1 := hcs.of_rest (v1.rest (ws := [.r7]) (by decide)) (by decide)
  refine sw0_ok hc1 (d := DY + 4 * k) (by omega_arith) fun t2 v2 => ?_
  refine sw0_ok (hc1.of_rest (v2.rest []) (by decide)) (d := X2 + 4 * k) (by omega_arith)
    fun t3 v3 => WP.block_nil ?_
  obtain ev : ((t1.gpr .r7).setWidth 32).toNat = wd s0.mem b (p + 4 * k) := by
    rw [v1.gpr, lo32_ext, ← win]; rfl
  obtain ev2 : t2.gpr .r7 = t1.gpr .r7 := by rw [v2.gpr]
  obtain hm3 : t3.mem = (s.mem.writeW (b + BitVec.ofNat 64 (DY + 4 * k)) ((t1.gpr .r7).setWidth 32)).writeW
      (b + BitVec.ofNat 64 (X2 + 4 * k)) ((t1.gpr .r7).setWidth 32) := by
    rw [v3.mem, ev2, v2.mem, v1.mem]
  refine ⟨h.rest.trans ((v1.rest (by decide)).trans ((v2.rest _).trans (v3.rest _))), ?_, fun j hj => ?_⟩
  · rw [hm3]
    refine ((h.frame.sub fun r hr => ?_).writeW (List.mem_cons_self ..) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_arith) (by omega_arith))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_arith) (by omega_arith))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by omega_arith)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega_arith)⟩
  · rw [limb, limb, hm3]
    rw [wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
        wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
        wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
      exact h.vals j hj
    · exact ⟨by rw [wd_write_self, ev], by rw [wd_write_self, ev]⟩

/-- The frame of decoding's first part. -/
abbrev yW (b : Addr) : List Region :=
  [FA b, ⟨b + BitVec.ofNat 64 OUT, 56⟩, ⟨b + BitVec.ofNat 64 BAD, 8⟩, ⟨b + BitVec.ofNat 64 SIGN, 1⟩]

/-- A byte at an offset in `[1064, 3520)` or from `3529` up to `4096` is outside `yW`. -/
theorem yW_byte {m m' : Mem} (hf : Frame (yW b) m m') {d : Nat} (hd : 1064 ≤ d)
    (hd' : d + 1 ≤ 3520 ∨ 3529 ≤ d ∧ d + 1 ≤ 4096) :
    m' (b + BitVec.ofNat 64 d) = m (b + BitVec.ofNat 64 d) := by
  obtain ⟨h1, h2, h3, h4⟩ := offs
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact fun h => Offset.disjoint_base b (d := d) (n := 1) (k := ACC + 112) (by omega_arith)
      (by omega_arith) _ (Region.contains_self _ _) h
  all_goals exact fun h => Offset.disjoint b (d := d) (n := 1) (by omega_arith) (by omega_arith) (by omega_arith) _ (Region.contains_self _ _) h

theorem yW_wd {m m' : Mem} (hf : Frame (yW b) m m') {d : Nat} (hd : 1064 ≤ d) (hd' : d + 4 ≤ 3520) :
    wd m' b d = wd m b d := by
  obtain ⟨h1, h2, h3, h4⟩ := offs
  refine wd_frame hf fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base b (by omega_arith) (by omega_arith)
  all_goals exact Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)

theorem toNat_and127 (x : Nat) (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x &&& BitVec.ofNat 64 127).toNat = x % 128 := by
  rw [BitVec.toNat_and, toNat_imm hx, toNat_imm (by decide),
    show (127 : Nat) = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem decodeY_ok {s : State} (hc : VCtx b s) {p : Nat} (hp : 1064 ≤ p) (hp' : p + 57 ≤ 3520) :
    WP isa (.block (decodeY p)) s fun t => VCtx b t ∧ Rest [.r4, .r5, .r7, .r8, .r9, .r10, .r11] s t ∧
      Frame (yW b) s.mem t.mem ∧ V t.mem b DY = yw s.mem b p ∧ V t.mem b DON = 1 ∧
      FS t.mem b DK = FS s.mem b DK ∧
      t.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 ((s.mem (b + BitVec.ofNat 64 (p + 56))).toNat / 128) ∧
      (bad t.mem b = 0 ↔ bad s.mem b = 0 ∧ yw s.mem b p < P ∧
        (s.mem (b + BitVec.ofNat 64 (p + 56))).toNat % 128 = 0) := by
  have hA := ACC_eq
  have hX : X2 = 56 := rfl
  have hD : DY = 168 := rfl
  have hY : Y = 896 := rfl
  unfold decodeY
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- The copy.
  refine WP.append (copyIn_ok hc.ctx (by omega_arith) hp) fun s1 h1 => ?_
  obtain hc1 : VCtx b s1 := hc.of_rest h1.rest (by decide) (by decide)
  obtain f1 : Frame (yW b) s.mem s1.mem := h1.frame.sub fun r hr => ⟨_, List.mem_cons_self .., by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by omega_arith)⟩
  -- The full reduction.
  refine WP.append (freeze_ok hc1.ctx hc1.r3 (fun k hk => by
      rw [Offset.add_add]; exact hc1.inW (by unfold OUT; omega_arith))
    ((Offset.disjoint_base b (d := OUT) (n := 56) (k := 4096) (by decide) (by decide)).symm))
    fun s2 ⟨_, hr2, hf2, hw2⟩ => ?_
  obtain hc2 : VCtx b s2 := hc1.of_rest hr2 (by decide) (by decide)
  obtain f2 : Frame (yW b) s1.mem s2.mem := hf2.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by omega_arith)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (Nat.le_refl _)⟩
  obtain hv1 : V s1.mem b X2 = yw s.mem b p := val32_congr fun j hj => (h1.vals j hj).2
  -- The comparison.
  refine WP.append (outSame_ok hc2 (p := p) (by omega_arith)) fun s3 ⟨hr3, hf3, hb3⟩ => ?_
  obtain hc3 : VCtx b s3 := hc2.of_rest hr3 (by decide) (by decide)
  obtain f3 : Frame (yW b) s2.mem s3.mem := hf3.mono fun r hr => by
    rw [List.mem_singleton.mp hr]; simp
  -- The last byte.
  refine wp_lbz (a := b + BitVec.ofNat 64 (p + 56)) (by decide) (by omega_arith) (by rw [hc3.ctx.r6])
    (hc3.inR (by omega_arith)) fun s4 u4 => wp_li (by decide) fun s5 u5 => wp_and fun s6 u6 => ?_
  obtain hr6 : Rest [.r7, .r8] s3 s6 :=
    (u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide)))
  obtain hm6 : s6.mem = s3.mem := by rw [u6.mem, u5.mem, u4.mem]
  obtain hc6 : VCtx b s6 := hc3.of_rest hr6 (by decide) (by decide)
  obtain hB : (s3.mem (b + BitVec.ofNat 64 (p + 56))).toNat = (s.mem (b + BitVec.ofNat 64 (p + 56))).toNat := by
    rw [yW_byte f3 (by omega_arith) (.inl (by omega_arith)), yW_byte f2 (by omega_arith) (.inl (by omega_arith)),
      yW_byte f1 (by omega_arith) (.inl (by omega_arith))]
  obtain e7 : (s6.gpr .r7).toNat = (s.mem (b + BitVec.ofNat 64 (p + 56))).toNat := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, toNat_imm (by omega_arith), hB]
  obtain e8 : (s6.gpr .r8).toNat = (s.mem (b + BitVec.ofNat 64 (p + 56))).toNat % 128 := by
    rw [u6.gpr, u5.gpr, u5.other _ (by decide), u4.gpr, hB, toNat_and127 _ (by omega_arith)]
  refine WP.append (orBad_ok hc6 (r := .r8) (by decide)) fun s7 ⟨hr7, hf7, hb7⟩ => ?_
  obtain hc7 : VCtx b s7 := hc6.of_rest hr7 (by decide) (by decide)
  -- The sign.
  refine wp_lsr (by decide) fun s8 u8 => ?_
  refine wp_stb (a := b + BitVec.ofNat 64 SIGN) (by decide) (by decide)
    (by rw [u8.other _ (by decide), hc7.ctx.r6]) (by rw [u8.wr]; exact hc7.inW (by decide)) fun s9 u9 => ?_
  obtain hc9 : VCtx b s9 := hc7.of_rest ((u8.rest (ws := [.r7]) (by decide)).trans (u9.rest _)) (by decide)
    (by decide)
  obtain hm9 : s9.mem = s7.mem.writeW (b + BitVec.ofNat 64 SIGN) ((s8.gpr .r7).setWidth 8) := by
    rw [u9.mem, u8.mem]
  refine WP.mono (constField_ok hc9.ctx (o := DON) (by decide) (v := 1) (by decide)) fun t ⟨hrt, hft, hvt⟩ => ?_
  obtain f9 : Frame (yW b) s7.mem t.mem := by
    refine (Frame.trans (m₂ := s9.mem) ?_ (hft.sub fun r hr => ⟨_, List.mem_cons_self .., by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by unfold DON; omega_arith)⟩))
    rw [hm9]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ (8 / 8))
  obtain f7 : Frame (yW b) s3.mem s7.mem := by
    rw [← hm6]; exact hf7.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp
  obtain hrt' : Rest [.r4, .r5, .r7, .r8, .r9, .r10, .r11] s t :=
    (h1.rest.mono (by decide)).trans ((hr2.mono (by decide)).trans ((hr3.mono (by decide)).trans
      ((hr6.mono (by decide)).trans ((hr7.mono (by decide)).trans (((u8.rest (ws := [.r7]) (by decide)).trans
        (u9.rest _)).trans hrt |>.mono (by decide))))))
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hDON : DON = 224 := rfl
  -- What changes after the copy.
  obtain fS : Frame [⟨b + BitVec.ofNat 64 SIGN, 1⟩] s7.mem s9.mem := by
    rw [hm9]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ (8 / 8))
  let L1 : List Region := [⟨b + BitVec.ofNat 64 Y, 56⟩, ⟨b + BitVec.ofNat 64 OUT, 56⟩,
    ⟨b + BitVec.ofNat 64 BAD, 8⟩, ⟨b + BitVec.ofNat 64 SIGN, 1⟩, ⟨b + BitVec.ofNat 64 DON, 56⟩]
  obtain g1 : Frame L1 s1.mem t.mem := by
    refine (hf2.mono fun r hr => ?_).trans ((hf3.mono fun r hr => ?_).trans ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp [L1]
    · rw [List.mem_singleton.mp hr]; simp [L1]
    rw [← hm6]
    refine (hf7.mono fun r hr => ?_).trans ((fS.mono fun r hr => ?_).trans (hft.mono fun r hr => ?_))
    all_goals (rw [List.mem_singleton.mp hr]; simp [L1])
  refine ⟨hc.of_rest hrt' (by decide) (by decide), hrt', f1.trans (f2.trans (f3.trans (f7.trans f9))), ?_, hvt, ?_, ?_, ?_⟩
  · -- `y` stays in `DY`.
    refine (val32_congr fun j hj => ?_).trans (val32_congr fun j hj => (h1.vals j hj).1)
    refine limb_frame g1 (fun r hr k hk => ?_) j hj
    simp only [L1, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  · -- `d` stays in `DK`.
    obtain g0 : Frame (⟨b + BitVec.ofNat 64 DY, 56⟩ :: ⟨b + BitVec.ofNat 64 X2, 56⟩ :: L1) s.mem t.mem :=
      (h1.frame.mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp).trans
        (g1.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
    obtain e := limb_frame (o := DK) g0 fun r hr k hk => by
      simp only [L1, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Offset.disjoint _ (by unfold DK; omega_arith) (by unfold DK; omega_arith) (by omega_arith)
    rw [FS, V, val32_congr e]; rfl
  · -- The sign.
    rw [hft _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint b (d := SIGN) (n := 1) (e := DON) (k := 56) (by omega_arith) (by omega_arith) (by omega_arith) _
        (Region.contains_self _ _) h, hm9, VG.WriteBytes.writeW8_apply, ite_eq_left rfl]
    refine stb_byte ?_
    rw [u8.gpr, BitVec.toNat_ushiftRight, hr7.gpr _ (by decide), e7, Nat.shiftRight_eq_div_pow]
  · -- The checks.
    obtain b2 : bad s2.mem b = bad s.mem b := by
      unfold bad
      rw [hf2.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        h1.frame.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    obtain bt : bad t.mem b = bad s7.mem b := by
      unfold bad
      rw [hft.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        fS.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    obtain b6 : bad s6.mem b = bad s3.mem b := by rw [bad, bad, hm6]
    rw [bt, hb7, b6, hb3, b2, e8, Nat.or_eq_zero_iff, Nat.or_eq_zero_iff, orw_eq_zero]
    obtain hin : ∀ k < 14, wd s2.mem b (p + 4 * k) = wd s.mem b (p + 4 * k) := fun k hk => by
      rw [yW_wd f2 (by omega_arith) (by omega_arith), yW_wd f1 (by omega_arith) (by omega_arith)]
    obtain hiff : (∀ k < 14, (wd s2.mem (b + BitVec.ofNat 64 OUT) (4 * k) ^^^ wd s2.mem b (p + 4 * k)) = 0) ↔
        yw s.mem b p < P := by
      obtain hP0 : P ≠ 0 := by have := P_eq; omega_arith
      obtain e1 : yw s.mem b p % P = val32 (fun j => wd s2.mem (b + BitVec.ofNat 64 OUT) (4 * j)) 14 := by
        rw [← hv1, hw2]
      obtain e2 : yw s.mem b p = val32 (fun k => wd s2.mem b (p + 4 * k)) 14 :=
        val32_congr fun k hk => (hin k hk).symm
      rw [← Nat.mod_eq_iff_lt hP0, e1]
      conv => rhs; rhs; rw [e2]
      rw [val32_inj (fun k _ => wd_lt _ _ _) (fun k _ => wd_lt _ _ _)]
      refine forall_congr' fun k => imp_congr_right fun hk => ?_
      rw [xor_eq_zero]
    rw [hiff]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

end

end VG.Proof.Ed448.PPC64LE

end

end

/-!
# Ed448's verification on PPC64LE: the checks of the candidate x-coordinate

`decodeCheck` checks `v x² = u` and that `x = 0` does not come with the sign
1 (at `SIGN`), and leaves `x` fully reduced at `OUT` (`decodeCheck_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Impl.X448.PPC64LE (X2 Y ACC freeze)
open VG.Spec.X448 (P Fe)

/-- `z - 1 >> 63` is 1 exactly when `z` is 0, for `z < 2³²`. -/
theorem isZero_shift {z : Nat} (hz : z < 2 ^ 32) :
    ((BitVec.ofNat 64 z - BitVec.ofNat 64 1) >>> 63).toNat = if z = 0 then 1 else 0 := by
  by_cases h : z = 0
  · subst h; decide
  · rw [ofNat_sub_one (by omega_arith) (by omega_arith), BitVec.toNat_ushiftRight, toNat_imm (by omega_arith),
      Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega_arith), ite_eq_right h]

/-- An element is 0 exactly when the words of its full reduction are. -/
theorem fs_zero {m : Mem} {b : Addr} {o : Nat} {w : Nat → Nat} (hw : val32 w 14 = V m b o % P) :
    FS m b o = 0 ↔ val32 w 14 = 0 := by
  rw [hw, FS, ← VG.Proof.X448.toFe_zero, VG.Proof.X448.toFe_eq_iff, Nat.zero_mod]

/-- The slots `decodeCheck` keeps. -/
def CQ : List Nat := [DXX, DV, DU, DY, DK, DTMP]

section
variable {b : Addr}

theorem decodeCheck_eq : decodeCheck = opsCode [.mul DTMP DXX DXX, .mul DTMP DV DTMP]
    (.block (Impl.X448.PPC64LE.sub X2 DTMP DU ++ freeze ++ outZero ++ copy X2 DXX ++ freeze ++ outOr ++
      ([.subi .r10 .r10 1, .lsr .d .r10 .r10 63, .lbz .r7 .r6 SIGN, .logic .and .r8 .r10 .r7] : List Instr) ++
        orBad .r8)) := rfl

theorem decodeCheck_ok {s : State} (hc : VCtx b s) {x v u : Fe} (hx : FS s.mem b DXX = x)
    (hv : FS s.mem b DV = v) (hu : FS s.mem b DU = u) {sg : Nat} (hsg : sg ≤ 1)
    (hs : s.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg) :
    WP isa decodeCheck s fun t => VCtx b t ∧ Rest work s t ∧
      Frame (yW b) s.mem t.mem ∧ (∀ q ∈ [DXX, DY, DK], FS t.mem b q = FS s.mem b q) ∧
      t.mem (b + BitVec.ofNat 64 SIGN) = s.mem (b + BitVec.ofNat 64 SIGN) ∧
      VG.Spec.X448.bytesAt t.mem (b + BitVec.ofNat 64 OUT) 56 = Proof.X25519.leBytes 56 x.val ∧
      (bad t.mem b = 0 ↔ bad s.mem b = 0 ∧ v * (x * x) = u ∧ ¬ (x = 0 ∧ sg = 1)) := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hA := ACC_eq
  have hX : X2 = 56 := rfl
  have hY : Y = 896 := rfl
  obtain h0 : Cur b s (s.gpr .r0) (s.gpr .r12) CQ (FS s.mem b) s := ⟨hc.ctx, Stp.refl _ _, rfl, rfl, fun _ _ => rfl⟩
  rw [decodeCheck_eq]
  refine ops_ok _ CQ _ s (by decide) h0 fun s1 h1 => ?_
  simp only [outZero, copy, List.append_assoc, List.cons_append, List.nil_append]
  obtain hc1 : VCtx b s1 := hc.of_rest h1.stp.rest (by decide) (by decide)
  -- `v x² - u` into `X2`.
  refine WP.append (subS (o := X2) (x := DTMP) (y := DU) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    h1.ctx h1.slots) fun s2 ⟨hr2, hf2, hS2⟩ => ?_
  obtain hc2 : VCtx b s2 := hc1.of_rest hr2 (by decide) (by decide)
  obtain e2 : FS s2.mem b X2 = v * (x * x) - u := by
    rw [hS2 X2 (by decide)]
    have hx' : FS s.mem b 672 = x := hx
    have hv' : FS s.mem b 448 = v := hv
    have hu' : FS s.mem b 392 = u := hu
    simp only [upd, runOps, FOp.out, FOp.val, X2, DTMP, DXX, DV, DU, Nat.reduceEqDiff, ↓reduceIte, hx', hv', hu']
  -- Its full reduction, checked to be 0.
  refine WP.append (freeze_ok hc2.ctx hc2.r3 (fun k hk => by rw [Offset.add_add]; exact hc2.inW (by omega_arith))
    ((Offset.disjoint_base b (d := OUT) (n := 56) (k := 4096) (by omega_arith) (by omega_arith)).symm))
    fun s3 ⟨_, hr3, hf3, hw3⟩ => ?_
  obtain hc3 : VCtx b s3 := hc2.of_rest hr3 (by decide) (by decide)
  obtain hdo : Region.Disjoint ⟨b, 4096⟩ ⟨b + BitVec.ofNat 64 OUT, 56⟩ :=
    (Offset.disjoint_base b (d := OUT) (n := 56) (k := 4096) (by omega_arith) (by omega_arith)).symm
  obtain hS3 := slots_freeze hf3 hdo hS2 (by decide)
  refine WP.append (outOr_ok hc3) fun s4 ⟨hr4, hm4, hv4⟩ => ?_
  obtain hc4 : VCtx b s4 := hc3.of_rest hr4 (by decide) (by decide)
  refine WP.append (orBad_ok hc4 (r := .r10) (by decide)) fun s5 ⟨hr5, hf5, hb5⟩ => ?_
  obtain hc5 : VCtx b s5 := hc4.of_rest hr5 (by decide) (by decide)
  obtain hS5 := SlotsOk.lo (m := s3.mem) (m' := s5.mem) (by rw [← hm4]; exact hf5) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact disj_hi (by omega_arith) (by omega_arith)) hS3 (by decide)
  -- `x` into `X2`, and its full reduction.
  refine wp_li (by decide) fun s6 u6 => ?_
  obtain hc6 : VCtx b s6 := hc5.of_rest (u6.rest (ws := [.r11]) (by decide)) (by decide) (by decide)
  refine WP.append (sel_ok (b := b) (o := X2) (q := DXX) (r := DXX) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc6.ctx (sw := 0) (by decide) (by rw [u6.gpr]; rfl)) fun s7 h7 => ?_
  obtain hc7 : VCtx b s7 := hc6.of_rest h7.rest (by decide) (by decide)
  obtain e7 : V s7.mem b X2 = V s6.mem b DXX := val32_congr fun j hj => h7.lo j hj
  refine WP.append (freeze_ok hc7.ctx hc7.r3 (fun k hk => by rw [Offset.add_add]; exact hc7.inW (by omega_arith))
    hdo) fun s8 ⟨hb8, hr8, hf8, hw8⟩ => ?_
  obtain hc8 : VCtx b s8 := hc7.of_rest hr8 (by decide) (by decide)
  refine WP.append (outOr_ok hc8) fun s9 ⟨hr9, hm9, hv9⟩ => ?_
  obtain hc9 : VCtx b s9 := hc8.of_rest hr9 (by decide) (by decide)
  -- Zero with the sign 1.
  refine wp_subi (by decide) (by decide) fun s10 u10 => wp_lsr (by decide) fun s11 u11 => ?_
  refine wp_lbz (a := b + BitVec.ofNat 64 SIGN) (by decide) (by omega_arith)
    (by rw [u11.other _ (by decide), u10.other _ (by decide), hc9.ctx.r6]) (by
      rw [u11.rd, u11.wr, u10.rd, u10.wr]; exact hc9.inR (by omega_arith)) fun s12 u12 => wp_and fun s13 u13 => ?_
  obtain hr13 : Rest [.r7, .r8, .r10] s9 s13 := (u10.rest (by decide)).trans ((u11.rest (by decide)).trans
    ((u12.rest (by decide)).trans (u13.rest (by decide))))
  obtain hm13 : s13.mem = s9.mem := by rw [u13.mem, u12.mem, u11.mem, u10.mem]
  obtain hc13 : VCtx b s13 := hc9.of_rest hr13 (by decide) (by decide)
  refine WP.mono (orBad_ok hc13 (r := .r8) (by decide)) fun t ⟨hrt, hft, hbt⟩ => ?_
  have hX' : DXX = 672 := rfl
  -- The registers.
  obtain hrw : Rest work s t := by
    refine h1.stp.rest.trans ((hr2.mono (by decide)).trans ((hr3.mono (by decide)).trans ?_))
    refine (hr4.mono (by decide)).trans ((hr5.mono (by decide)).trans ?_)
    refine ((u6.rest (ws := [.r11]) (by decide)).mono (by decide)).trans ((h7.rest.mono (by decide)).trans ?_)
    exact (hr8.mono (by decide)).trans ((hr9.mono (by decide)).trans ((hr13.mono (by decide)).trans
      (hrt.mono (by decide))))
  -- The memory.
  let L2 : List Region := [FA b, ⟨b + BitVec.ofNat 64 OUT, 56⟩, ⟨b + BitVec.ofNat 64 BAD, 8⟩]
  obtain sFA : ∀ {m m' : Mem} {o n : Nat}, o + n ≤ 1064 → Frame [⟨b + BitVec.ofNat 64 o, n⟩] m m' → Frame L2 m m' :=
    fun ho hf => hf.sub fun r hr => ⟨_, List.mem_cons_self .., by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega_arith)⟩
  obtain sYO : ∀ {m m' : Mem}, Frame [⟨b + BitVec.ofNat 64 Y, 56⟩, ⟨b + BitVec.ofNat 64 OUT, 56⟩] m m' →
      Frame L2 m m' := fun hf => hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by omega_arith)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (Nat.le_refl _)⟩
  obtain sB : ∀ {m m' : Mem}, Frame [⟨b + BitVec.ofNat 64 BAD, 8⟩] m m' → Frame L2 m m' :=
    fun hf => hf.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp [L2]
  obtain fs3 : Frame L2 s.mem s3.mem :=
    (h1.stp.frame.mono (by simp [L2])).trans ((hf2.mono (by simp [L2])).trans (sYO hf3))
  obtain f58 : Frame L2 s5.mem s8.mem := by
    rw [← u6.mem]; exact (sFA (o := X2) (n := 4 * 14) (by omega_arith) h7.frame).trans (sYO hf8)
  obtain f8t : Frame L2 s8.mem t.mem := by rw [← hm9, ← hm13]; exact sB hft
  obtain fst : Frame L2 s.mem t.mem := fs3.trans ((by rw [← hm4]; exact sB hf5 : Frame L2 s3.mem s5.mem).trans
    (f58.trans f8t))
  -- The slots kept, through `s5`.
  obtain k5 : ∀ q ∈ [DXX, DY, DK], FS s5.mem b q = FS s.mem b q := by
    intro q hq
    rw [hS5 q (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl | rfl <;> decide)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;>
      simp only [upd, runOps, FOp.out, X2, DTMP, DXX, DY, DK, Nat.reduceEqDiff, ↓reduceIte]
  obtain kt : ∀ q ∈ [DXX, DY, DK], FS t.mem b q = FS s5.mem b q := by
    intro q hq
    obtain hq' : (q = 672 ∨ q = 168 ∨ q = 336) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; exact hq
    obtain f : Frame [⟨b + BitVec.ofNat 64 X2, 56⟩, ⟨b + BitVec.ofNat 64 Y, 56⟩, ⟨b + BitVec.ofNat 64 OUT, 56⟩,
        ⟨b + BitVec.ofNat 64 BAD, 8⟩] s5.mem t.mem := by
      rw [← u6.mem]
      refine (h7.frame.mono (by simp)).trans ((hf8.mono ?_).trans ?_)
      · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp
      · rw [← hm9, ← hm13]; exact hft.mono (by simp)
    obtain e := limb_frame (o := q) f fun r hr k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    rw [FS, V, val32_congr e]; rfl
  obtain hxv : V s7.mem b X2 % P = x.val := by
    rw [e7, ← VG.Proof.X448.toFe_val, ← FS, show FS s6.mem b DXX = FS s5.mem b DXX by rw [u6.mem], k5 _ (by simp),
      hx]
  refine ⟨hc.of_rest hrw (by decide) (by decide), hrw, fst.mono (by simp [L2]), fun q hq => (kt q hq).trans (k5 q hq),
    ?_, ?_, ?_⟩
  · -- The sign.
    exact fst _ fun r hr => by
      simp only [L2, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact fun h => Offset.disjoint_base b (d := SIGN) (n := 1) (k := ACC + 112) (by omega_arith)
          (by omega_arith) _ (Region.contains_self _ _) h
      all_goals exact fun h => Offset.disjoint b (d := SIGN) (n := 1) (by omega_arith) (by omega_arith) (by omega_arith) _ (Region.contains_self _ _) h
  · -- `x` at `OUT`.
    rw [← hxv, ← hb8]
    simp only [VG.Spec.X448.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    obtain hi := List.mem_range.mp hi
    rw [Offset.add_add, hft _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint b (d := OUT + i) (n := 1) (e := BAD) (k := 8) (by omega_arith) (by omega_arith) (by omega_arith) _
        (Region.contains_self _ _) h, hm13, hm9]
  · -- The checks.
    obtain rB : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
        (∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 BAD, 8⟩ r) → bad m' b = bad m b := fun hf hd => by
      unfold bad; rw [hf.readW (Region.contains_self _ (64 / 8)) hd (by decide)]
    obtain b3 : bad s3.mem b = bad s.mem b := by
      rw [rB hf3 (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)),
        rB hf2 (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)),
        rB h1.stp.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by omega_arith) (by omega_arith))]
    obtain b13 : bad s13.mem b = bad s5.mem b := by
      obtain e1 : bad s13.mem b = bad s8.mem b := by rw [bad, bad, hm13, hm9]
      obtain e2 : bad s8.mem b = bad s7.mem b := rB hf8 (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
      obtain e3 : bad s7.mem b = bad s6.mem b :=
        rB h7.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
      obtain e4 : bad s6.mem b = bad s5.mem b := by rw [bad, bad, u6.mem]
      rw [e1, e2, e3, e4]
    obtain fs8 : Frame L2 s.mem s8.mem :=
      fs3.trans ((by rw [← hm4]; exact sB hf5 : Frame L2 s3.mem s5.mem).trans f58)
    obtain hsg12 : (s12.gpr .r7).toNat = sg := by
      rw [u12.gpr, toNat_imm (Nat.lt_trans (BitVec.isLt _) (by decide)), u11.mem, u10.mem, hm9]
      have : s8.mem (b + BitVec.ofNat 64 SIGN) = s.mem (b + BitVec.ofNat 64 SIGN) := by
        refine fs8 _ fun r hr => ?_
        simp only [L2, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact fun h => Offset.disjoint_base b (d := SIGN) (n := 1) (k := ACC + 112) (by omega_arith)
            (by omega_arith) _ (Region.contains_self _ _) h
        all_goals exact fun h => Offset.disjoint b (d := SIGN) (n := 1) (by omega_arith) (by omega_arith) (by omega_arith) _ (Region.contains_self _ _) h
      rw [this, hs, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    obtain hz := orw_lt (f := fun k => wd s8.mem (b + BitVec.ofNat 64 OUT) (4 * k)) (n := 14) fun k _ => wd_lt _ _ _
    obtain hz12 : (s12.gpr .r10).toNat =
        if orw (fun k => wd s8.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 = 0 then 1 else 0 := by
      rw [u12.other _ (by decide), u11.gpr, u10.gpr, ← isZero_shift hz]
      congr 3
      exact BitVec.eq_of_toNat_eq (by rw [hv9, toNat_imm (by omega_arith)])
    obtain hx7 : FS s7.mem b X2 = x := by
      rw [FS, e7, ← FS, show FS s6.mem b DXX = FS s5.mem b DXX by rw [u6.mem], k5 _ (by simp), hx]
    rw [hbt, b13, hb5, hm4, b3, hv4, u13.gpr, BitVec.toNat_and, hz12, hsg12, Nat.or_eq_zero_iff, Nat.or_eq_zero_iff,
      orw_eq_zero, ← val32_eq_zero, ← fs_zero hw3, e2, fin_sub_eq_zero]
    obtain hz0 : orw (fun k => wd s8.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 = 0 ↔ x = 0 := by
      rw [orw_eq_zero, ← val32_eq_zero, ← fs_zero hw8, hx7]
    obtain hr8 : ((if orw (fun k => wd s8.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 = 0 then 1 else 0) &&& sg = 0) ↔
        ¬ (x = 0 ∧ sg = 1) := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsg with rfl | rfl
      · rw [Nat.and_zero]; exact ⟨fun _ h => absurd h.2 (by decide), fun _ => rfl⟩
      · by_cases h : orw (fun k => wd s8.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 = 0
        · rw [ite_eq_left h]; exact ⟨fun h1 => absurd h1 (by decide), fun h2 => absurd ⟨hz0.mp h, rfl⟩ h2⟩
        · rw [ite_eq_right h]; exact ⟨fun _ h2 => h (hz0.mpr h2.1), fun _ => rfl⟩
    rw [hr8]; exact and_assoc
