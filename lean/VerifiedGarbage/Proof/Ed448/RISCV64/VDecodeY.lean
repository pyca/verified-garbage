module

public import VerifiedGarbage.Proof.Ed448.RISCV64.VChecks
public import VerifiedGarbage.Proof.X448.RISCV64.Slots
import VerifiedGarbage.Proof.X448.RISCV64.Mul
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseInit
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseBits
import VerifiedGarbage.Proof.X448.RISCV64.Freeze
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.X25519.RISCV64.Pass

/-!
# Ed448's verification on RISCV64: the y-coordinate of a point

`decodeY p` copies the words of the 56 bytes at `p` into `DY` and `X2`,
checks that they are their full reduction (so `y < p`) and that bits 0–6
of byte 56 are 0, stores bit 7 at `SIGN`, and writes 1 to `DON`
(`decodeY_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (X2 Y ACC freeze)
open VG.Spec.X448 (P)

/-- The number of the 56 bytes at `p`, as fourteen words. -/
def yw (m : Mem) (b : Addr) (p : Nat) : Nat := val32 (fun k => wd m b (p + 4 * k)) 14

section
variable {b : Addr}

/-- After `k` words of the copy. -/
structure CpInv (b : Addr) (p : Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.a4] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 DY, 4 * k⟩, ⟨b + BitVec.ofNat 64 X2, 4 * k⟩] s0.mem s.mem
  vals : ∀ j < k, limb s.mem b DY j = wd s0.mem b (p + 4 * j) ∧ limb s.mem b X2 j = wd s0.mem b (p + 4 * j)

theorem copyIn_ok {s0 : State} (hc : Ctx b s0) {p : Nat} (hp : p + 56 ≤ 2048) (hp' : 1064 ≤ p) (hp4 : p % 4 = 0) :
    WP isa (.block ((List.range 14).flatMap fun k => [.load .w .a4 .a3 (p + 4 * k),
      .store .w .a4 .a3 (DY + 4 * k), .store .w .a4 .a3 (X2 + 4 * k)])) s0 (CpInv b p s0 14) := by
  have hX : X2 = 56 := rfl
  have hD : DY = 168 := rfl
  refine wp_range_flatMap (M := isa) (CpInv b p s0) (fun k s hk h => ?_) 14 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  have hcs : Ctx b s := hc.of_rest h.rest (by decide)
  have win : wd s.mem b (p + 4 * k) = wd s0.mem b (p + 4 * k) :=
    wd_frame h.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
      · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  refine lw0_ok hcs (d := p + 4 * k) (by omega_arith) (by omega_arith) fun t1 v1 => ?_
  have hc1 : Ctx b t1 := hcs.of_rest (v1.rest (ws := [.a4]) (by decide)) (by decide)
  refine sw0_ok hc1 (d := DY + 4 * k) (by omega_arith) (by omega_arith) fun t2 v2 => ?_
  refine sw0_ok (hc1.of_rest (v2.rest []) (by decide)) (d := X2 + 4 * k) (by omega_arith) (by omega_arith)
    fun t3 v3 => WP.block_nil ?_
  have ev : ((t1.gpr .a4).setWidth 32).toNat = wd s0.mem b (p + 4 * k) := by
    rw [v1.gpr, lo32_ext, ← win]; rfl
  have ev2 : t2.gpr .a4 = t1.gpr .a4 := by rw [v2.gpr]
  have hm3 : t3.mem = (s.mem.writeW (b + BitVec.ofNat 64 (DY + 4 * k)) ((t1.gpr .a4).setWidth 32)).writeW
      (b + BitVec.ofNat 64 (X2 + 4 * k)) ((t1.gpr .a4).setWidth 32) := by
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

/-- A byte at an offset in `[1064, 1696)` or from `1705` up to `2048` is outside `yW`. -/
theorem yW_byte {m m' : Mem} (hf : Frame (yW b) m m') {d : Nat} (hd : 1064 ≤ d)
    (hd' : d + 1 ≤ 1696 ∨ 1705 ≤ d ∧ d + 1 ≤ 2048) :
    m' (b + BitVec.ofNat 64 d) = m (b + BitVec.ofNat 64 d) := by
  obtain ⟨h1, h2, h3, h4⟩ := offs
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact fun h => Offset.disjoint_base b (d := d) (n := 1) (k := ACC + 112) (by omega_arith)
      (by omega_arith) _ (Region.contains_self _ _) h
  all_goals exact fun h => Offset.disjoint b (d := d) (n := 1) (by omega_arith) (by omega_arith) (by omega_arith) _ (Region.contains_self _ _) h

theorem yW_wd {m m' : Mem} (hf : Frame (yW b) m m') {d : Nat} (hd : 1064 ≤ d) (hd' : d + 4 ≤ 1696) :
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

theorem decodeY_ok {s : State} (hc : VCtx b s) {p : Nat} (hp : 1064 ≤ p) (hp' : p + 57 ≤ 1696) (hp4 : p % 4 = 0) :
    WP isa (.block (decodeY p)) s fun t => VCtx b t ∧ Rest [.a1, .a2, .a4, .a5, .a6, .a7, .t0] s t ∧
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
  refine WP.append (copyIn_ok hc.ctx (by omega_arith) hp hp4) fun s1 h1 => ?_
  have hc1 : VCtx b s1 := hc.of_rest h1.rest (by decide) (by decide)
  have f1 : Frame (yW b) s.mem s1.mem := h1.frame.sub fun r hr => ⟨_, List.mem_cons_self .., by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by omega_arith)⟩
  -- The full reduction.
  refine WP.append (freeze_ok hc1.ctx hc1.a0 (fun k hk => by
      rw [Offset.add_add]; exact hc1.inW (by unfold OUT; omega_arith))
    ((Offset.disjoint_base b (d := OUT) (n := 56) (k := 2048) (by decide) (by decide)).symm))
    fun s2 ⟨_, hr2, hf2, hw2⟩ => ?_
  have hc2 : VCtx b s2 := hc1.of_rest hr2 (by decide) (by decide)
  have f2 : Frame (yW b) s1.mem s2.mem := hf2.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by omega_arith)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (Nat.le_refl _)⟩
  have hv1 : V s1.mem b X2 = yw s.mem b p := val32_congr fun j hj => (h1.vals j hj).2
  -- The comparison.
  refine WP.append (outSame_ok hc2 (p := p) (by omega_arith) hp4) fun s3 ⟨hr3, hf3, hb3⟩ => ?_
  have hc3 : VCtx b s3 := hc2.of_rest hr3 (by decide) (by decide)
  have f3 : Frame (yW b) s2.mem s3.mem := hf3.mono fun r hr => by
    rw [List.mem_singleton.mp hr]; simp
  -- The last byte.
  refine wp_lbz (a := b + BitVec.ofNat 64 (p + 56)) (by omega_arith) (by rw [hc3.ctx.a3])
    (hc3.inR (by omega_arith)) fun s4 u4 => wp_li (by decide) fun s5 u5 => wp_and fun s6 u6 => ?_
  have hr6 : Rest [.a4, .a5] s3 s6 :=
    (u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide)))
  have hm6 : s6.mem = s3.mem := by rw [u6.mem, u5.mem, u4.mem]
  have hc6 : VCtx b s6 := hc3.of_rest hr6 (by decide) (by decide)
  have hB : (s3.mem (b + BitVec.ofNat 64 (p + 56))).toNat = (s.mem (b + BitVec.ofNat 64 (p + 56))).toNat := by
    rw [yW_byte f3 (by omega_arith) (.inl (by omega_arith)), yW_byte f2 (by omega_arith) (.inl (by omega_arith)),
      yW_byte f1 (by omega_arith) (.inl (by omega_arith))]
  have e7 : (s6.gpr .a4).toNat = (s.mem (b + BitVec.ofNat 64 (p + 56))).toNat := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, toNat_imm (by omega_arith), hB]
  have e8 : (s6.gpr .a5).toNat = (s.mem (b + BitVec.ofNat 64 (p + 56))).toNat % 128 := by
    rw [u6.gpr, u5.gpr, u5.other _ (by decide), u4.gpr, hB, toNat_and127 _ (by omega_arith)]
  refine WP.append (orBad_ok hc6 (r := .a5) (by decide)) fun s7 ⟨hr7, hf7, hb7⟩ => ?_
  have hc7 : VCtx b s7 := hc6.of_rest hr7 (by decide) (by decide)
  -- The sign.
  refine wp_srl (by decide) fun s8 u8 => ?_
  refine wp_sb (a := b + BitVec.ofNat 64 SIGN) (by decide)
    (by rw [u8.other _ (by decide), hc7.ctx.a3]) (by rw [u8.wr]; exact hc7.inW (by decide)) fun s9 u9 => ?_
  have hc9 : VCtx b s9 := hc7.of_rest ((u8.rest (ws := [.a4]) (by decide)).trans (u9.rest _)) (by decide)
    (by decide)
  have hm9 : s9.mem = s7.mem.writeW (b + BitVec.ofNat 64 SIGN) ((s8.gpr .a4).setWidth 8) := by
    rw [u9.mem, u8.mem]
  refine WP.mono (constField_ok hc9.ctx (o := DON) (by decide) (by decide) (v := 1) (by decide)) fun t ⟨hrt, hft, hvt⟩ => ?_
  have f9 : Frame (yW b) s7.mem t.mem := by
    refine (Frame.trans (m₂ := s9.mem) ?_ (hft.sub fun r hr => ⟨_, List.mem_cons_self .., by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by unfold DON; omega_arith)⟩))
    rw [hm9]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ (8 / 8))
  have f7 : Frame (yW b) s3.mem s7.mem := by
    rw [← hm6]; exact hf7.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp
  have hrt' : Rest [.a1, .a2, .a4, .a5, .a6, .a7, .t0] s t :=
    (h1.rest.mono (by decide)).trans ((hr2.mono (by decide)).trans ((hr3.mono (by decide)).trans
      ((hr6.mono (by decide)).trans ((hr7.mono (by decide)).trans (((u8.rest (ws := [.a4]) (by decide)).trans
        (u9.rest _)).trans hrt |>.mono (by decide))))))
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hDON : DON = 224 := rfl
  -- What changes after the copy.
  have fS : Frame [⟨b + BitVec.ofNat 64 SIGN, 1⟩] s7.mem s9.mem := by
    rw [hm9]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ (8 / 8))
  let L1 : List Region := [⟨b + BitVec.ofNat 64 Y, 56⟩, ⟨b + BitVec.ofNat 64 OUT, 56⟩,
    ⟨b + BitVec.ofNat 64 BAD, 8⟩, ⟨b + BitVec.ofNat 64 SIGN, 1⟩, ⟨b + BitVec.ofNat 64 DON, 56⟩]
  have g1 : Frame L1 s1.mem t.mem := by
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
    have g0 : Frame (⟨b + BitVec.ofNat 64 DY, 56⟩ :: ⟨b + BitVec.ofNat 64 X2, 56⟩ :: L1) s.mem t.mem :=
      (h1.frame.mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp).trans
        (g1.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
    have e := limb_frame (o := DK) g0 fun r hr k hk => by
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
    have b2 : bad s2.mem b = bad s.mem b := by
      unfold bad
      rw [hf2.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        h1.frame.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    have bt : bad t.mem b = bad s7.mem b := by
      unfold bad
      rw [hft.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        fS.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    have b6 : bad s6.mem b = bad s3.mem b := by rw [bad, bad, hm6]
    rw [bt, hb7, b6, hb3, b2, e8, Nat.or_eq_zero_iff, Nat.or_eq_zero_iff, orw_eq_zero]
    have hin : ∀ k < 14, wd s2.mem b (p + 4 * k) = wd s.mem b (p + 4 * k) := fun k hk => by
      rw [yW_wd f2 (by omega_arith) (by omega_arith), yW_wd f1 (by omega_arith) (by omega_arith)]
    have hiff : (∀ k < 14, (wd s2.mem (b + BitVec.ofNat 64 OUT) (4 * k) ^^^ wd s2.mem b (p + 4 * k)) = 0) ↔
        yw s.mem b p < P := by
      have hP0 : P ≠ 0 := by have := P_eq; omega_arith
      have e1 : yw s.mem b p % P = val32 (fun j => wd s2.mem (b + BitVec.ofNat 64 OUT) (4 * j)) 14 := by
        rw [← hv1, hw2]
      have e2 : yw s.mem b p = val32 (fun k => wd s2.mem b (p + 4 * k)) 14 :=
        val32_congr fun k hk => (hin k hk).symm
      rw [← Nat.mod_eq_iff_lt hP0, e1]
      conv => rhs; rhs; rw [e2]
      rw [val32_inj (fun k _ => wd_lt _ _ _) (fun k _ => wd_lt _ _ _)]
      refine forall_congr' fun k => imp_congr_right fun hk => ?_
      rw [xor_eq_zero]
    rw [hiff]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

end

end VG.Proof.Ed448.RISCV64
