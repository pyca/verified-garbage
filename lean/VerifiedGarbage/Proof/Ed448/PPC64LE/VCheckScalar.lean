module

public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.PPC64LE.ScalarBit
import VerifiedGarbage.Proof.Ed448.DecodeBytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ed448.PPC64LE.VChecks
import VerifiedGarbage.Proof.X25519.PPC64LE.Pass
public import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseStep
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseEncode
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseSel
public import VerifiedGarbage.Proof.X448.PPC64LE.Slots
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.X25519.Bytes
public import VerifiedGarbage.Spec.X448.Contract
public import VerifiedGarbage.Proof.X448.PPC64LE.Invert
public import VerifiedGarbage.Impl.Ed448.PPC64LE.VerifyEquation
import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
public import VerifiedGarbage.Proof.Ed448.Ref
import VerifiedGarbage.Proof.Ed448.Recover
import VerifiedGarbage.Proof.Ed448.Root
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.X448.PPC64LE.Freeze
import VerifiedGarbage.Proof.X448.Field
import VerifiedGarbage.Proof.X448.Invert
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseInit
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Impl.Ed448.PPC64LE.ScalarBase

/-! ### `Ed448.PPC64LE.VSel`, which this module and modules that import it used -/

section

/-!
# Ed448 on PPC64LE: selections as updates of the slots

`sel o q r` as an update of the slots `qs` (`selG`): `o` (a slot of the field
area, separate from the others or one of them) gets `pick sw x y` for the
elements `x` and `y` at `q` and `r`, which may be anywhere in the working
space, `q` even `o` itself.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Impl.X448.PPC64LE (ACC)
open VG.Spec.X448 (Fe)

section
variable {b : Addr}

theorem fs_pick {m m' : Mem} {o q r : Nat} {sw : Nat} (hsw : sw ≤ 1)
    (h : ∀ j < 14, limb m' b o j = X25519.PPC64LE.sel sw (limb m b q j) (limb m b r j)) :
    FS m' b o = pick sw (FS m b q) (FS m b r) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
  · rw [FS, V, val32_congr (g := limb m b q) fun j hj => h j hj]; rfl
  · rw [FS, V, val32_congr (g := limb m b r) fun j hj => h j hj]; rfl

theorem selG {o q r : Nat} {qs : List Nat} {v : Nat → Fe} {x y : Fe} (hq : Sep1 o qs = true)
    (ho : o + 56 ≤ ACC) (hqf : q + 56 ≤ 4096) (hrf : r + 56 ≤ 4096)
    (hoq : o + 56 ≤ q ∨ q + 56 ≤ o ∨ o = q) (hor : o + 56 ≤ r ∨ r + 56 ≤ o)
    {s : State} (hc : Ctx b s) {sw : Nat} (hsw : sw ≤ 1) (h11 : s.gpr .r11 = 0 - BitVec.ofNat 64 sw)
    (hS : SlotsOk s.mem b qs v) (hx : FS s.mem b q = x) (hy : FS s.mem b r = y) :
    WP isa (.block (sel o q r)) s fun s' => Rest [.r5, .r7] s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem b (o :: qs) (upd v o (pick sw x y)) := by
  have hA := X448.PPC64LE.ACC_eq
  refine WP.mono (sel_ok (b := b) (o := o) (q := q) (r := r) (by omega_using [ho, hA]) hqf hrf hoq hor hc hsw h11)
    fun s' h => ⟨h.rest, ?_, fun q' hq' => ?_⟩
  · exact h.frame.sub fun x hx => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hx]; exact Offset.sub_base _ (by omega_using [ho])⟩
  · by_cases hqo : q' = o
    · subst hqo
      rw [upd_self, fs_pick hsw h.lo, hx, hy]
    · rw [upd_of_ne _ _ hqo]
      exact slots_after hq ho (frame_o (h.frame : Frame [⟨b + BitVec.ofNat 64 o, 56⟩] _ _)) hS
        ((List.mem_cons.mp hq').resolve_left hqo) hqo

end

end VG.Proof.Ed448.PPC64LE

end

end

/-! ### `Ed448.PPC64LE.VDecodeCheck`, which this module and modules that import it used -/

section

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

end
end VG.Proof.Ed448.PPC64LE
end

end

/-! ### `Ed448.PPC64LE.VDecode`, which this module and modules that import it used -/

section

/-! ### `Ed448.PPC64LE.VDecodeNeg`, which only this module used -/

section

/-!
# Ed448's verification on PPC64LE: the negated point

`decodeNeg xo yo` writes `-x'` to `xo` and `y` to `yo`, for `x'` the decoded
x-coordinate: `(x - x) - x` if the low bit of `x` (fully reduced at `OUT`) is
the sign, else `x` (`decodeNeg_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Impl.X448.PPC64LE (X2 Y ACC)
open VG.Spec.X448 (P Fe)

section
variable {b : Addr}

theorem xor_le_one' {x y : Nat} (hx : x ≤ 1) (hy : y ≤ 1) : x ^^^ y ≤ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with rfl | rfl <;> decide

/-- The slots of `-x'` and `y`, above the field area and below `PK`. -/
def NegOut (xo yo : Nat) : Prop :=
  1064 ≤ xo ∧ xo + 56 ≤ PK ∧ 1064 ≤ yo ∧ yo + 56 ≤ PK ∧ (xo + 56 ≤ yo ∨ yo + 56 ≤ xo)

theorem decodeNeg_ok {s : State} (hc : VCtx b s) {xo yo : Nat} (ho : NegOut xo yo) {x y : Fe}
    (hx : FS s.mem b DXX = x) (hy : FS s.mem b DY = y)
    (hout : VG.Spec.X448.bytesAt s.mem (b + BitVec.ofNat 64 OUT) 56 = Proof.X25519.leBytes 56 x.val)
    {sg : Nat} (hsg : sg ≤ 1) (hs : s.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg) :
    WP isa (.block (decodeNeg xo yo)) s fun t => VCtx b t ∧ Rest [.r4, .r5, .r7, .r8, .r9, .r10, .r11] s t ∧
      Frame [FA b, ⟨b + BitVec.ofNat 64 xo, 56⟩, ⟨b + BitVec.ofNat 64 yo, 56⟩] s.mem t.mem ∧
      FS t.mem b xo = pick (x.val % 2 ^^^ sg) ((x - x) - x) x ∧ FS t.mem b yo = y ∧
      FS t.mem b DK = FS s.mem b DK := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  obtain ⟨hx1, hx2, hy1, hy2, hxy⟩ := ho
  have hPK : PK = 3288 := rfl
  have hDY : DY = 168 := rfl
  have hA := ACC_eq
  unfold decodeNeg
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  obtain hS0 : SlotsOk s.mem b [DXX, DY, DK] (FS s.mem b) := fun _ _ => rfl
  refine WP.append (subS (o := DTMP) (x := DXX) (y := DXX) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    hc.ctx hS0) fun s1 ⟨hr1, hf1, hS1⟩ => ?_
  obtain hc1 : VCtx b s1 := hc.of_rest hr1 (by decide) (by decide)
  refine WP.append (subS (o := DNEG) (x := DTMP) (y := DXX) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    hc1.ctx hS1) fun s2 ⟨hr2, hf2, hS2⟩ => ?_
  obtain hc2 : VCtx b s2 := hc1.of_rest hr2 (by decide) (by decide)
  obtain hf12 : Frame [FA b] s.mem s2.mem := hf1.trans hf2
  -- The mask: the low bit of `x` against the sign.
  obtain hb2 : s2.mem (b + BitVec.ofNat 64 OUT) = BitVec.ofNat 8 x.val := by
    rw [hf12 _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint_base b (d := OUT) (n := 1) (k := ACC + 112) (by omega_arith) (by omega_arith) _
        (Region.contains_self _ _) h]
    exact byte0 hout
  obtain hs2 : s2.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg := by
    rw [hf12 _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint_base b (d := SIGN) (n := 1) (k := ACC + 112) (by omega_arith) (by omega_arith) _
        (Region.contains_self _ _) h]
    exact hs
  refine wp_lbz (a := b + BitVec.ofNat 64 OUT) (by decide) (by decide) (by rw [hc2.r3, BitVec.add_zero])
    (by rw [← BitVec.add_zero (b + BitVec.ofNat 64 OUT)]; exact (by rw [Offset.add_add]; exact hc2.inR (by omega_arith)))
    fun s3 u3 => wp_li (by decide) fun s4 u4 => wp_and fun s5 u5 => ?_
  refine wp_lbz (a := b + BitVec.ofNat 64 SIGN) (by decide) (by omega_arith)
    (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), hc2.ctx.r6])
    (by rw [u5.rd, u5.wr, u4.rd, u4.wr, u3.rd, u3.wr]; exact hc2.inR (by omega_arith)) fun s6 u6 => wp_xor fun s7 u7 => ?_
  refine wp_li (by decide) fun s8 u8 => wp_sub fun s9 u9 => ?_
  obtain hm9 : s9.mem = s2.mem := by rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem]
  obtain hr9 : Rest [.r7, .r8, .r9, .r11] s2 s9 := (u3.rest (by decide)).trans ((u4.rest (by decide)).trans
    ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans ((u7.rest (by decide)).trans
      ((u8.rest (by decide)).trans (u9.rest (by decide)))))))
  obtain hc9 : VCtx b s9 := hc2.of_rest hr9 (by decide) (by decide)
  obtain hsg' : sg < 2 ^ 64 := by omega_arith
  obtain hm : x.val % 2 ^^^ sg ≤ 1 := xor_le_one' (by omega_arith) hsg
  obtain e5 : (s5.gpr .r8).toNat = x.val % 2 := by
    rw [u5.gpr, BitVec.toNat_and, u4.other _ (by decide), u4.gpr, u3.gpr, hb2]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [Nat.and_one_is_mod]
    omega_arith
  obtain e6 : (s6.gpr .r7).toNat = sg := by
    rw [u6.gpr, u5.mem, u4.mem, u3.mem, hs2]
    simp only [BitVec.toNat_ofNat, Nat.reducePow]
    omega_arith
  obtain e7 : s7.gpr .r8 = BitVec.ofNat 64 (x.val % 2 ^^^ sg) := by
    apply BitVec.eq_of_toNat_eq
    rw [u7.gpr, BitVec.toNat_xor, u6.other _ (by decide), e5, e6, toNat_imm (by omega_arith)]
  obtain e11 : s9.gpr .r11 = 0 - BitVec.ofNat 64 (x.val % 2 ^^^ sg) := by
    rw [u9.gpr, u8.gpr, u8.other _ (by decide), e7]; rfl
  -- The selections.
  refine WP.append (sel_ok (b := b) (o := xo) (q := DNEG) (r := DXX) (by omega_arith) (by decide) (by decide)
    (by unfold DNEG; omega_arith) (by unfold DXX; omega_arith) hc9.ctx hm e11) fun s10 h10 => ?_
  obtain hc10 : VCtx b s10 := hc9.of_rest h10.rest (by decide) (by decide)
  refine WP.mono (sel_ok (b := b) (o := yo) (q := DY) (r := DY) (by omega_arith) (by decide) (by decide)
    (by unfold DY; omega_arith) (by unfold DY; omega_arith) hc10.ctx hm (by rw [h10.rest.gpr _ (by decide), e11]))
    fun t ht => ?_
  obtain hrt : Rest [.r4, .r5, .r7, .r8, .r9, .r10, .r11] s t :=
    (hr1.mono (by decide)).trans ((hr2.mono (by decide)).trans ((hr9.mono (by decide)).trans
      ((h10.rest.mono (by decide)).trans (ht.rest.mono (by decide)))))
  -- The values.
  obtain v2 : ∀ q ∈ [DNEG, DXX, DY, DK], FS s2.mem b q = upd (upd (FS s.mem b) DTMP (FS s.mem b DXX - FS s.mem b DXX))
      DNEG (upd (FS s.mem b) DTMP (FS s.mem b DXX - FS s.mem b DXX) DTMP -
        upd (FS s.mem b) DTMP (FS s.mem b DXX - FS s.mem b DXX) DXX) q := fun q hq => hS2 q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl | rfl | rfl <;> decide)
  have hx' : FS s.mem b 672 = x := hx
  have hy' : FS s.mem b 168 = y := hy
  obtain eN : FS s2.mem b DNEG = (x - x) - x := by
    rw [v2 DNEG (by simp)]; simp only [upd, DNEG, DTMP, DXX, Nat.reduceEqDiff, ↓reduceIte, hx']
  obtain eX : FS s2.mem b DXX = x := by
    rw [v2 DXX (by simp)]; simp only [upd, DNEG, DTMP, DXX, Nat.reduceEqDiff, ↓reduceIte, hx']
  obtain eY : FS s2.mem b DY = y := by
    rw [v2 DY (by simp)]; simp only [upd, DNEG, DTMP, DY, Nat.reduceEqDiff, ↓reduceIte, hy']
  obtain hxo : FS s10.mem b xo = pick (x.val % 2 ^^^ sg) ((x - x) - x) x := by
    rw [fs_pick hm h10.lo, hm9, eN, eX]
  obtain eK : FS s2.mem b DK = FS s.mem b DK := by
    rw [v2 DK (by simp)]; simp only [upd, DNEG, DTMP, DK, Nat.reduceEqDiff, ↓reduceIte]
  refine ⟨hc.of_rest hrt (by decide) (by decide), hrt, ?_, ?_, ?_, ?_⟩
  · refine (hf12.mono (by simp)).trans ?_
    rw [← hm9]
    exact (h10.frame.mono (by simp)).trans (ht.frame.mono (by simp))
  · -- `xo` is kept by the write of `yo`.
    rw [← hxo]
    obtain e := limb_frame (o := xo) ht.frame fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint b (d := xo + 4 * k) (n := 4) (e := yo) (k := 4 * 14) (by omega_arith) (by omega_arith) (by omega_arith)
    rw [FS, V, val32_congr e]; rfl
  · -- `y`, kept by the write of `xo`.
    rw [fs_pick hm ht.lo]
    obtain e := limb_frame (o := DY) h10.frame fun r hr k hk => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by unfold DY; omega_arith) (by omega_arith) (by omega_arith)
    rw [show FS s10.mem b DY = FS s9.mem b DY by rw [FS, V, val32_congr e]; rfl, hm9, eY]
    unfold pick X25519.PPC64LE.sel; split <;> rfl

  · -- `d`, kept by both writes.
    rw [← eK, ← hm9]
    obtain f : Frame [⟨b + BitVec.ofNat 64 xo, 4 * 14⟩, ⟨b + BitVec.ofNat 64 yo, 4 * 14⟩] s9.mem t.mem :=
      (h10.frame.mono (by simp)).trans (ht.frame.mono (by simp))
    obtain e := limb_frame (o := DK) f fun r hr k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by unfold DK; omega_arith) (by unfold DK; omega_arith) (by omega_arith)
    rw [FS, V, val32_congr e]; rfl

end

end VG.Proof.Ed448.PPC64LE

end

end

/-! ### `Ed448.PPC64LE.VDecodeX`, which only this module used -/

section

/-! ### `Ed448.PPC64LE.VRoot`, which only this module used -/

section

/-!
# Ed448 on PPC64LE: the square root's power

`root` computes `z^((p-3)/4)` into `R` for the element `z` at `Z2` by
square-and-multiply over the bits of `(p - 3) / 4` from 445 down to 0
(`rootQ_ok`), as X448's inversion computes `z^(p-2)`
(`Proof/X448/PPC64LE/Invert.lean`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Impl.X448.PPC64LE (R Z2 one)
open VG.Spec.X448 (P Fe)

/-! ## The bits of `(p - 3) / 4` -/

/-- The exponent `(p - 3) / 4`. -/
def RE : Nat := (P - 3) / 4

def rbitsB : Nat → Bool
  | 0 => true
  | t + 1 => (RE >>> t % 2 == if t = 222 then 0 else 1) && rbitsB t

theorem rbitsB_ok : rbitsB 446 = true := by decide +kernel

/-- Every bit of `RE = 2⁴⁴⁶ - 2²²² - 1` below 446 but bit 222 is 1. -/
theorem rbits : ∀ t < 446, RE >>> t % 2 = if t = 222 then 0 else 1 := by
  have : ∀ n, rbitsB n = true → ∀ t < n, RE >>> t % 2 = if t = 222 then 0 else 1 := by
    intro n; induction n with
    | zero => intro _ t ht; omega_using [ht]
    | succ n ih =>
      intro h t ht
      simp only [rbitsB, Bool.and_eq_true, beq_iff_eq] at h
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
      · exact ih h.2 t ht
      · exact h.1
  exact this 446 rbitsB_ok

theorem r446 : RE >>> 446 = 0 := by decide +kernel

section
variable {b : Addr}

/-- `z^(((p - 3) / 4) >> n)` in `R`, for `z` at `Z2`. -/
def rootV (v : Nat → Fe) (n : Nat) : Nat → Fe := upd v R (VG.Proof.X448.pw (v Z2) (RE >>> n))

/-- The loop invariant of `root` from `sI`, before the step for the bit `n - 1`. -/
structure RootInv (b : Addr) (sI : State) (a : BitVec 64) (qs : List Nat) (v : Nat → Fe) (n : Nat)
    (s : State) : Prop where
  cur : Cur b sI a (BitVec.ofNat 64 n) qs (rootV v n) s

theorem rootStep_ok {sI : State} {a : BitVec 64} {qs : List Nat} (hq : Sep1 R qs = true) (hR : R ∈ qs)
    (hZ : Z2 ∈ qs) {v : Nat → Fe} {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 446)
    {s : State} (h : RootInv b sI a qs v n s) :
    WP isa rootStep s fun s' => RootInv b sI a qs v (n - 1) s' ∧ (s'.gpr .r12 != 0) = decide (n - 1 ≠ 0) := by
  obtain ⟨hcur⟩ := h
  obtain hb := rbits (n - 1) (by omega_using [hn'])
  obtain he := shr_step RE (n - 1)
  rw [Nat.sub_add_cancel hn] at he
  unfold rootStep
  refine WP.seq (wp_subi (by decide) (by decide) fun s1 u1 => WP.block_nil ?_)
  obtain h1 : Cur b sI a (BitVec.ofNat 64 (n - 1)) qs (rootV v n) s1 := by
    refine ⟨hcur.ctx.of_rest (u1.rest (ws := [.r12]) (by decide)) (by decide),
      hcur.stp.trans (Stp.of_rest (u1.rest (ws := [.r12]) (by decide)) (by decide) u1.mem),
      by rw [u1.other _ (by decide), hcur.r0], ?_, by rw [u1.mem]; exact hcur.slots⟩
    rw [u1.gpr, hcur.r12, ofNat_sub_one hn (by omega_using [hn'])]
  refine WP.seq (WP.mono (opMul (o := R) (x := R) (y := R) hq (by decide) hR hR (by decide) (by decide) (by decide) h1)
    fun s2 h2 => ?_)
  obtain hsq : ∀ q ∈ qs, upd (rootV v n) R (rootV v n R * rootV v n R) q =
      upd v R (VG.Proof.X448.pw (v Z2) (2 * (RE >>> n))) q := by
    intro q _
    by_cases hq : q = R
    · subst hq; rw [upd_self, rootV, upd_self, upd_self, Nat.two_mul, ← VG.Proof.X448.pw_mul]
    · rw [upd_of_ne _ _ hq, rootV, upd_of_ne _ _ hq, upd_of_ne _ _ hq]
  obtain h2' := h2.congr (qs' := qs) (fun q hq' => List.mem_cons_of_mem _ hq') hsq
  refine WP.seq (WP.mono (cmp_ok (d := 222) (by omega_using [hn']) (by decide) h2') fun s3 ⟨h3, hz3⟩ => ?_)
  refine WP.mono (Q := Cur b sI a (BitVec.ofNat 64 (n - 1)) qs (rootV v (n - 1))) ?_ fun s4 h4 =>
    ⟨⟨h4⟩, by rw [h4.r12, ofNat_ne_zero (by omega_using [hn'])]⟩
  refine WP.ite _ hz3 (fun ht => WP.block_nil (h3.congr (fun q hq => hq) fun q _ => ?_)) (fun hf => ?_)
  · have h4 : n - 1 = 222 := by simpa using ht
    by_cases hq : q = R
    · subst hq; rw [upd_self, rootV, upd_self, he, hb, iteT h4, Nat.add_zero]
    · rw [upd_of_ne _ _ hq, rootV, upd_of_ne _ _ hq]
  · have h4 : n - 1 ≠ 222 := by simpa using hf
    refine WP.mono (opMul (o := R) (x := R) (y := Z2) hq (by decide) hR hZ (by decide) (by decide) (by decide) h3)
      fun s5 h5 => h5.congr (fun q hq' => List.mem_cons_of_mem _ hq') fun q _ => ?_
    by_cases hq : q = R
    · subst hq
      rw [upd_self, upd_self, upd_of_ne _ _ (by decide : Z2 ≠ R), rootV, upd_self, he, hb,
        iteF h4, ← VG.Proof.X448.pw_mul, VG.Proof.X448.pw_one]
    · rw [upd_of_ne _ _ hq, upd_of_ne _ _ hq, rootV, upd_of_ne _ _ hq]

theorem rootQ_ok {qs : List Nat} (hq : Sep1 R qs = true) (hR' : R ∈ qs) (hZ : Z2 ∈ qs)
    {a : BitVec 64} {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : ∀ q ∈ qs, q ≠ R → FS s.mem b q = v q) (h0 : s.gpr .r0 = a) :
    WP isa root s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b qs (upd v R (VG.Proof.X448.pw (v Z2) (RE))) := by
  have hR : R = 840 := rfl
  unfold root
  refine WP.seq ?_
  simp only [one, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => ?_
  obtain hr2 : Rest [.r4, .r5] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  obtain hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  refine sw0_ok hc2 (d := R) (by decide) fun s3 u3 => ?_
  refine WP.append (stores_ok (o := R + 4) (n := 13) (by decide) (hc2.of_rest (u3.rest []) (by decide)))
    fun s4 ⟨h4w, h4f, h4g, h4r⟩ => ?_
  refine wp_li (by decide) fun s5 u5 => WP.block_nil ?_
  obtain hr5 : Rest [.r4, .r5, .r12] s s5 :=
    (hr2.mono (by decide)).trans ((u3.rest _).trans ((h4r.mono (by decide)).trans (u5.rest (by decide))))
  obtain hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  -- The limbs of `R`: 1, then zeros.
  obtain hlimb : ∀ k < 14, limb s5.mem b R k = if k = 0 then 1 else 0 := by
    intro k hk
    rw [limb, u5.mem]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.mul_zero, Nat.add_zero, wd_frame h4f fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide),
        u3.mem, wd_write_self, toNat_lo32, u2.other _ (by decide), u1.gpr]; rfl
    · have := h4w (k - 1) (by omega_using [hk])
      rw [show R + 4 + 4 * (k - 1) = R + 4 * k by omega_using [hk0], u3.gpr, u2.gpr] at this
      rw [this]; simp only [show k ≠ 0 by omega_using [hk0], ite_false]; rfl
  obtain hf5 : Frame [⟨b + BitVec.ofNat 64 R, 56⟩] s.mem s5.mem := by
    rw [u5.mem, ← hm2]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) ((s2.gpr .r4).setWidth 32)
      (Offset.contains b (d := R) (n := 32 / 8) (e := R) (k := 56) (Nat.le_refl _) (by decide)
        (by decide))).trans ?_
    rw [← u3.mem]
    exact h4f.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩
  obtain hc5 : Ctx b s5 := hc.of_rest hr5 (by decide)
  obtain hst5 : Stp b s s5 := ⟨hr5.mono (by decide), hf5.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)⟩⟩
  obtain hS5 : SlotsOk s5.mem b qs (rootV v 446) := by
    have hA := ACC_eq
    intro q hq'
    by_cases hqR : q = R
    · subst hqR
      rw [FS, V, val32_congr hlimb, rootV, upd_self, r446, pw_zero, val32_single _ (by decide)]
      rfl
    · obtain ⟨h1, h3⟩ := sep1_get hq hq'
      obtain e := limb_frame (o := q) hf5 fun r hr k hk => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (by omega_using [hqR, h1, hk]) (by omega_using [hA, h3, hk]) (by omega_using [hR])
      rw [FS, V, val32_congr e, rootV, upd_of_ne _ _ hqR]; exact hS q hq' hqR
  obtain h446 : RootInv b s5 a qs v 446 s5 :=
    ⟨⟨hc5, Stp.refl _ _, by rw [hr5.gpr _ (by decide), h0], u5.gpr, hS5⟩⟩
  refine WP.mono (Q := RootInv b s5 a qs v 0) (WP.loop (M := isa)
    (fun m s' => 1 ≤ m ∧ m ≤ 446 ∧ RootInv b s5 a qs v m s') ?_ 446 s5 ⟨by decide, Nat.le_refl _, h446⟩)
    fun s' ⟨h'⟩ => ⟨hst5.trans h'.stp, h'.ctx, h'.slots.congr fun q _ => by
      simp only [rootV, Nat.shiftRight_zero]⟩
  rintro m s' ⟨h1, h2, hl⟩
  refine WP.mono (rootStep_ok hq hR' hZ h1 h2 hl) fun s'' ⟨hl', hz⟩ => ?_
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by rw [eval_nonzero, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp [hm], m - 1, by omega_using [hm], by omega_using [hm], by omega_using [h2], hl'⟩


end

end VG.Proof.Ed448.PPC64LE

end

end


/-!
# Ed448's verification on PPC64LE: the candidate x-coordinate

`decodeX` computes, from `y` at `DY`, `1` at `DON` and `d` at `DK`,
`u = y² - 1` (at `DU`), `v = d y² - 1` (at `DV`), `t = u³v` (at `DT`) and
`x = t (t (uv)²)^((p-3)/4)` (at `DXX`) (`decodeX_ok`), as `recoverRef` has
them.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Impl.X448.PPC64LE (R Z2)
open VG.Spec.X448 (P Fe)

/-- The field operations of `decodeX` before the power. -/
def xOps : List FOp :=
  [.mul DYY DY DY, .sub DU DYY DON, .mul DV DK DYY, .sub DV DV DON, .mul DT DU DU, .mul DT DT DU,
    .mul DT DT DV, .mul DW DU DV, .mul DW DW DW, .mul Z2 DT DW]

theorem decodeX_eq : decodeX = opsCode xOps (.seq root (Impl.X448.PPC64LE.mul DXX DT R)) := rfl

/-- The slots `decodeX` reads, and `R` and `Z2`. -/
def XQ : List Nat := [DY, DON, DK, R, Z2]

theorem xOps_ok : opsOk xOps XQ = true := by decide

/-- `u`, `v`, `t` and the candidate `x` for `y`. -/
def uOf (y : Fe) : Fe := y * y - 1
def vOf (y : Fe) : Fe := Spec.Ed448.d * (y * y) - 1
def tOf (y : Fe) : Fe := uOf y * uOf y * uOf y * vOf y
def xOf (y : Fe) : Fe :=
  tOf y * VG.Proof.X448.pw (tOf y * ((uOf y * vOf y) * (uOf y * vOf y))) RE

section
variable {b : Addr}

theorem decodeX_ok {s : State} (hc : Ctx b s) {y : Fe} (hy : FS s.mem b DY = y) (hon : FS s.mem b DON = 1)
    (hd : FS s.mem b DK = Spec.Ed448.d) :
    WP isa decodeX s fun t => Stp b s t ∧ Ctx b t ∧ FS t.mem b DXX = xOf y ∧ FS t.mem b DV = vOf y ∧
      FS t.mem b DU = uOf y ∧ FS t.mem b DY = y ∧ FS t.mem b DK = Spec.Ed448.d := by
  have hy' : FS s.mem b 168 = y := hy
  have hon' : FS s.mem b 224 = 1 := hon
  have hd' : FS s.mem b 336 = Spec.Ed448.d := hd
  obtain h0 : Cur b s (s.gpr .r0) (s.gpr .r12) XQ (FS s.mem b) s := ⟨hc, Stp.refl _ _, rfl, rfl, fun _ _ => rfl⟩
  rw [decodeX_eq]
  refine ops_ok xOps XQ _ s xOps_ok h0 fun s1 h1 => ?_
  refine WP.seq (WP.mono (rootQ_ok (qs := outsQ xOps XQ) (by decide) (by decide) (by decide) h1.ctx
    (fun q hq _ => h1.slots q hq) h1.r0) fun s2 ⟨hst2, hc2, hS2⟩ => ?_)
  refine WP.mono (mulS (o := DXX) (x := DT) (y := R) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hc2 hS2)
    fun t ⟨hrt, hft, hSt⟩ => ?_
  refine ⟨h1.stp.trans (hst2.trans ⟨hrt.mono (by decide), hft⟩), hc2.of_rest hrt (by decide), ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | rw [hSt DXX (by decide)] | rw [hSt DV (by decide)] | rw [hSt DU (by decide)]
    | rw [hSt DY (by decide)] | rw [hSt DK (by decide)]
  all_goals
    simp only [upd, runOps, xOps, FOp.out, FOp.val, DXX, DT, DV, DU, DY, DK, DW, DYY, DON, R, Z2,
      Nat.reduceEqDiff, ↓reduceIte, hy', hon', hd', xOf, tOf, uOf, vOf]
end

end VG.Proof.Ed448.PPC64LE

end

end


/-!
# Ed448's verification on PPC64LE: decoding a point

`decode p xo yo` decodes the 57 bytes at `p` (RFC 8032 §5.2.3): `BAD` stays 0
exactly when they encode a point, and then `xo` and `yo` hold the
coordinates of its negation (`decode_ok`), by `decodePoint_impl`.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame
open VG.Impl.X448.PPC64LE (X2 Y ACC)
open VG.Spec.X448 (P Fe)
open VG.Spec.Ed448 (Point)

theorem fin_neg_neg {n : Nat} [NeZero n] (x : Fin n) : 0 - (0 - x) = x := by grind

theorem fin_neg_sub {n : Nat} [NeZero n] (x : Fin n) : (x - x) - x = 0 - x := by rw [Fin.sub_self]

/-- The negation of the decoded x-coordinate, as `decodeNeg` selects it. -/
theorem neg_pick (x : Fe) {sg : Nat} (hsg : sg ≤ 1) :
    pick (x.val % 2 ^^^ sg) ((x - x) - x) x =
      0 - (if (x.val % 2 == 1) == (sg == 1) then x else (x - x) - x) := by
  rw [fin_neg_sub]
  rcases Nat.mod_two_eq_zero_or_one x.val with h | h <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsg with rfl | rfl <;>
    simp only [h, pick, X25519.PPC64LE.sel, Nat.reduceXor, ↓reduceIte, beq_self_eq_true,
      Nat.zero_ne_one, beq_iff_eq] <;> first | rfl | exact (fin_neg_neg x).symm

/-- The regions `decode` writes. -/
abbrev decW (b : Addr) (xo yo : Nat) : List Region :=
  yW b ++ [⟨b + BitVec.ofNat 64 xo, 56⟩, ⟨b + BitVec.ofNat 64 yo, 56⟩]

section
variable {b : Addr}

theorem decode_eq (p xo yo : Nat) : decode p xo yo =
    .seq (.block (decodeY p)) (.seq decodeX (.seq decodeCheck (.block (decodeNeg xo yo)))) := rfl

/-- The 57 bytes at `p` in terms of the words and the last byte. -/
theorem bytes57 (m : Mem) (p : Nat) :
    Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt m (b + BitVec.ofNat 64 p) 57).take 56) = yw m b p ∧
      ((Spec.Ed448.bytesAt m (b + BitVec.ofNat 64 p) 57).getD 56 0).toNat =
        (m (b + BitVec.ofNat 64 (p + 56))).toNat := by
  constructor
  · rw [show (57 : Nat) = 56 + 1 from rfl, Proof.Ed448.bytesAt_eq, Proof.X25519.bytesAt_add,
      List.take_left' (by simp [Spec.X25519.bytesAt]), Proof.Ed448.decodeLE_eq, show (56 : Nat) = 4 * 14 from rfl]
    rw [show Spec.X25519.bytesAt m (b + BitVec.ofNat 64 p) (4 * 14) =
      VG.Spec.X448.bytesAt m (b + BitVec.ofNat 64 p) (4 * 14) from rfl, leNum_bytesAt4]
    exact val32_congr fun k _ => wd_shift _ _ _ _
  · rw [getD_bytesAt _ _ (by decide), Offset.add_add]

theorem decode_ok (hR : Proof.Ed448.RecoverOk) {s : State} (hc : VCtx b s) {p : Nat} (hp : 1064 ≤ p)
    (hp' : p + 57 ≤ 3520) {xo yo : Nat} (ho : NegOut xo yo) (hd : FS s.mem b DK = Spec.Ed448.d) :
    WP isa (decode p xo yo) s fun t => VCtx b t ∧ Rest work s t ∧ Frame (decW b xo yo) s.mem t.mem ∧
      FS t.mem b DK = Spec.Ed448.d ∧
      (bad t.mem b = 0 ↔ bad s.mem b = 0 ∧
        (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 p) 57)).isSome) ∧
      ∀ pt, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 p) 57) = some pt →
        FS t.mem b xo = 0 - pt.X ∧ FS t.mem b yo = pt.Y ∧ pt.Z = 1 := by
  rw [decode_eq]
  refine WP.seq (WP.mono (decodeY_ok hc hp hp') fun s1 ⟨hc1, hr1, hf1, hy1, hon1, hk1, hs1, hb1⟩ => ?_)
  generalize hB : (s.mem (b + BitVec.ofNat 64 (p + 56))).toNat = B at hs1 hb1
  obtain hBl : B < 256 := by rw [← hB]; exact BitVec.isLt _
  obtain hsg : B / 128 ≤ 1 := by omega_using [hB]
  generalize hY : VG.Proof.X448.toFe (yw s.mem b p) = y
  obtain hy : FS s1.mem b DY = y := by rw [FS, hy1, hY]
  obtain hon : FS s1.mem b DON = 1 := by rw [FS, hon1]; rfl
  refine WP.seq (WP.mono (decodeX_ok hc1.ctx hy hon (hk1.trans hd))
    fun s2 ⟨hst2, hc2', hx2, hv2, hu2, hy2, hd2⟩ => ?_)
  obtain hc2 : VCtx b s2 := hc1.of_rest hst2.rest (by decide) (by decide)
  obtain hs2 : s2.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 (B / 128) := by
    rw [← hs1]
    exact hst2.frame _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint_base b (d := SIGN) (n := 1) (k := ACC + 112) (by decide) (by decide) _
        (Region.contains_self _ _) h
  refine WP.seq (WP.mono (decodeCheck_ok hc2 hx2 hv2 hu2 hsg hs2)
    fun s3 ⟨hc3, hr3, hf3, hk3, hs3, hout3, hb3⟩ => ?_)
  obtain hb2 : bad s2.mem b = bad s1.mem b := by
    unfold bad
    rw [hst2.frame.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by decide) (by decide)) (by decide)]
  refine WP.mono (decodeNeg_ok hc3 ho (x := xOf y) (y := y) (by rw [hk3 DXX (by simp), hx2])
    (by rw [hk3 DY (by simp), hy2]) hout3 hsg (by rw [hs3, hs2])) fun t ⟨hct, hrt, hft, hxt, hyt, hkt⟩ => ?_
  obtain ⟨ho1, ho2, ho3, ho4, ho5⟩ := ho
  have hPK : PK = 3288 := rfl
  obtain ⟨o1, o2, o3, o4⟩ := offs
  -- The code's view of `decodePoint`.
  obtain ⟨e56, eB⟩ := bytes57 (b := b) s.mem p
  rw [hB] at eB
  obtain hdp := Proof.Ed448.decodePoint_impl hR (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 p) 57)
    (by simp [Spec.Ed448.bytesAt]) _ B e56 eB y (uOf y) (vOf y) (tOf y) (xOf y) hY rfl rfl rfl (by
      rw [xOf, Proof.Ed448.rootPow_eq, VG.Proof.X448.pow_pw]; rfl)
  obtain hbt : bad t.mem b = bad s3.mem b := by
    unfold bad
    rw [hft.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint_base _ (by decide) (by decide)
      all_goals exact Offset.disjoint _ (by omega_arith) (by omega_using [o3]) (by omega_arith)) (by decide)]
  refine ⟨hct, hr1.mono (by decide) |>.trans (hst2.rest.trans (hr3.trans (hrt.mono (by decide)))), ?_,
    by rw [hkt, hk3 DK (by simp), hd2], ?_, ?_⟩
  · -- The frame.
    refine (hf1.mono (by simp [decW])).trans ((hst2.frame.mono (by simp [decW])).trans ((hf3.mono (by simp [decW])).trans
      (hft.mono ?_)))
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [decW]
  · -- The checks.
    rw [hbt, hb3, hb2, hb1, hdp]
    by_cases hC : (B % 128 = 0 ∧ yw s.mem b p < P) ∧ vOf y * (xOf y * xOf y) = uOf y ∧
        ¬ (xOf y = 0 ∧ B / 128 = 1)
    · rw [ite_eq_left hC, Option.isSome_some]
      exact ⟨fun h => ⟨h.1.1, rfl⟩, fun h => ⟨⟨h.1, hC.1.2, hC.1.1⟩, hC.2⟩⟩
    · rw [ite_eq_right hC, Option.isSome_none]
      exact ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => absurd ⟨⟨h3, h2⟩, h4⟩ hC, fun h => absurd h.2 (by decide)⟩
  · intro pt hpt
    rw [hdp] at hpt
    by_cases hC : (B % 128 = 0 ∧ yw s.mem b p < P) ∧ vOf y * (xOf y * xOf y) = uOf y ∧
        ¬ (xOf y = 0 ∧ B / 128 = 1)
    · rw [ite_eq_left hC] at hpt
      cases Option.some.inj hpt
      exact ⟨by rw [hxt, neg_pick _ hsg], hyt, rfl⟩
    · rw [ite_eq_right hC] at hpt
      exact absurd hpt (by simp)

end

end VG.Proof.Ed448.PPC64LE

end

end

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
    obtain h0 : (bs.getD 56 0).toNat = 0 := by
      by_contra hne
      have : 256 ^ 56 ≤ 256 ^ 56 * (bs.getD 56 0).toNat := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
      omega_arith
    exact ⟨h0, by omega_using [hl]⟩
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
  refine WP.append (copyIn_ok hc.ctx (p := SG + 57) (by omega_using [hSG]) (by omega_using [hSG])) fun s1 h1 => ?_
  obtain hc1 : VCtx b s1 := hc.of_rest h1.rest (by decide) (by decide)
  refine wp_li (by decide) fun s2 u2 => ?_
  obtain hc2 : VCtx b s2 := hc1.of_rest (u2.rest (ws := [.r8]) (by decide)) (by decide) (by decide)
  refine WP.append (subtract_ok (o := DY) ⟨by decide, by decide⟩ hc2.ctx (by rw [u2.gpr]; rfl))
    fun s3 ⟨hr3, hf3, _, h83, _⟩ => ?_
  obtain hc3 : VCtx b s3 := hc2.of_rest hr3 (by decide) (by decide)
  refine WP.append (orBad_ok hc3 (r := .r8) (by decide)) fun s4 ⟨hr4, hf4, hb4⟩ => ?_
  obtain hc4 : VCtx b s4 := hc3.of_rest hr4 (by decide) (by decide)
  refine wp_lbz (a := b + BitVec.ofNat 64 (SG + 57 + 56)) (by decide) (by omega_using [hSG]) (by rw [hc4.ctx.r6])
    (hc4.inR (by omega_using [hSG])) fun s5 u5 => ?_
  obtain hc5 : VCtx b s5 := hc4.of_rest (u5.rest (ws := [.r7]) (by decide)) (by decide) (by decide)
  refine WP.mono (orBad_ok hc5 (r := .r7) (by decide)) fun t ⟨hrt, hft, hbt⟩ => ?_
  -- The frames.
  obtain fC : Frame [FA b] s.mem s1.mem := h1.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by omega_arith)⟩
  obtain fS : Frame [FA b] s2.mem s3.mem := hf3.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega_using [hSD])⟩
  obtain f3 : Frame [FA b] s.mem s3.mem := fC.trans (by rw [u2.mem] at fS; exact fS)
  obtain hrt' : Rest [.r5, .r7, .r8, .r9] s t := (h1.rest.mono (by decide)).trans
    (((u2.rest (ws := [.r8]) (by decide)).mono (by decide)).trans ((hr3.mono (by decide)).trans
      ((hr4.mono (by decide)).trans (((u5.rest (ws := [.r7]) (by decide)).mono (by decide)).trans
        (hrt.mono (by decide))))))
  refine ⟨hc.of_rest hrt' (by decide) (by decide), hrt', ?_, ?_, ?_⟩
  · refine (f3.mono (by simp)).trans ((hf4.mono (by simp)).trans ?_)
    rw [← u5.mem]; exact hft.mono (by simp)
  · -- `d` stays.
    have hK : DK = 336 := rfl
    obtain f : Frame [⟨b + BitVec.ofNat 64 DY, 4 * 14⟩, ⟨b + BitVec.ofNat 64 X2, 4 * 14⟩,
        ⟨b + BitVec.ofNat 64 SD, 56⟩, ⟨b + BitVec.ofNat 64 BAD, 8⟩] s.mem t.mem := by
      refine (h1.frame.mono (by simp)).trans ?_
      rw [u2.mem] at hf3
      refine (hf3.mono (by simp)).trans ((hf4.mono (by simp)).trans ?_)
      rw [← u5.mem]; exact hft.mono (by simp)
    obtain e := limb_frame (o := DK) f fun r hr k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_using [hK, hk]) (by omega_arith)
    rw [FS, V, val32_congr e]; rfl
  · -- The checks.
    obtain b3 : bad s3.mem b = bad s.mem b := by
      unfold bad
      rw [f3.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by omega_using [o1, o3]) (by omega_using [o3])) (by decide)]
    obtain hB : (s5.gpr .r7).toNat = (s.mem (b + BitVec.ofNat 64 (SG + 57 + 56))).toNat := by
      rw [u5.gpr, toNat_imm (Nat.lt_trans (BitVec.isLt _) (by decide)), hf4 _ fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact fun h => Offset.disjoint b (d := SG + 57 + 56) (n := 1) (e := BAD) (k := 8) (by omega_using [o3, hSG])
            (by omega_using [hSG]) (by omega_using [o3]) _ (Region.contains_self _ _) h,
        f3 _ fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact fun h => Offset.disjoint_base b (d := SG + 57 + 56) (n := 1) (k := ACC + 112) (by omega_using [o1, hSG])
            (by omega_using [hSG]) _ (Region.contains_self _ _) h]
    obtain hV : V s2.mem b DY = yw s.mem b (SG + 57) := by
      rw [u2.mem]; exact val32_congr fun j hj => (h1.vals j hj).1
    obtain ⟨e56, eB⟩ := bytes57 (b := b) s.mem (SG + 57)
    rw [hbt, u5.mem, hb4, b3, h83, hB, hV, lt_L_iff _ (by simp [Spec.Ed448.bytesAt]), e56, eB,
      Nat.or_eq_zero_iff, Nat.or_eq_zero_iff]
    have : (if Spec.Ed448.L ≤ yw s.mem b (SG + 57) then 1 else 0) = 0 ↔ yw s.mem b (SG + 57) < Spec.Ed448.L := by
      by_cases h : Spec.Ed448.L ≤ yw s.mem b (SG + 57)
      · rw [ite_eq_left h]; exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h (by omega_using [h'])⟩
      · rw [ite_eq_right h]; exact ⟨fun _ => by omega_using [h], fun _ => rfl⟩
    rw [this]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h3, h2⟩, fun ⟨h1, h3, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

end

end VG.Proof.Ed448.PPC64LE
