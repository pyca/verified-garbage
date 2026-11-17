module

public import VerifiedGarbage.Proof.Ed448.RISCV64.BaseStep
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseEncode
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseSel
public import VerifiedGarbage.Proof.X448.RISCV64.Slots
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ed448.RISCV64.VChecks
public import VerifiedGarbage.Proof.X25519.Bytes
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.X25519.RISCV64.Pass
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
public import VerifiedGarbage.Impl.Ed448.RISCV64.VerifyEquation
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Invert
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
public import VerifiedGarbage.Proof.X448.RISCV64.Ladder
import VerifiedGarbage.Proof.X25519.RISCV64.Mul
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Ladder
public import VerifiedGarbage.Proof.Ed448.Ref
import VerifiedGarbage.Proof.Ed448.Recover
import VerifiedGarbage.Proof.Ed448.Root
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseBits
import VerifiedGarbage.Proof.X448.RISCV64.Freeze
import VerifiedGarbage.Proof.X448.Field
import VerifiedGarbage.Proof.X448.Invert
import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseInit
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Impl.Ed448.RISCV64.ScalarBase

/-! ### `Ed448.RISCV64.VSel`, which this module and modules that import it used -/

section

/-!
# Ed448 on RISCV64: selections as updates of the slots

`sel o q r` as an update of the slots `qs` (`selG`): `o` (a slot of the field
area, separate from the others or one of them) gets `pick sw x y` for the
elements `x` and `y` at `q` and `r`, which may be anywhere in the working
space, `q` even `o` itself.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (ACC)
open VG.Spec.X448 (Fe)

section
variable {b : Addr}

theorem fs_pick {m m' : Mem} {o q r : Nat} {sw : Nat} (hsw : sw ≤ 1)
    (h : ∀ j < 14, limb m' b o j = VG.Proof.X25519.sel sw (limb m b q j) (limb m b r j)) :
    FS m' b o = pick sw (FS m b q) (FS m b r) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
  · rw [FS, V, val32_congr (g := limb m b q) fun j hj => h j hj]; rfl
  · rw [FS, V, val32_congr (g := limb m b r) fun j hj => h j hj]; rfl

theorem selG {o q r : Nat} {qs : List Nat} {v : Nat → Fe} {x y : Fe} (hq : Sep1 o qs = true)
    (ho : o + 56 ≤ ACC) (hqf : q + 56 ≤ 2048) (hrf : r + 56 ≤ 2048)
    (hoq : o + 56 ≤ q ∨ q + 56 ≤ o ∨ o = q) (hor : o + 56 ≤ r ∨ r + 56 ≤ o)
    (hq4 : q % 4 = 0) (hr4 : r % 4 = 0) {s : State} (hc : Ctx b s) {sw : Nat} (hsw : sw ≤ 1) (h11 : s.gpr .t0 = 0 - BitVec.ofNat 64 sw)
    (hS : SlotsOk s.mem b qs v) (hx : FS s.mem b q = x) (hy : FS s.mem b r = y) :
    WP isa (.block (sel o q r)) s fun s' => Rest [.a2, .a4] s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem b (o :: qs) (upd v o (pick sw x y)) := by
  have hA := X448.RISCV64.ACC_eq
  refine WP.mono (sel_ok (b := b) (o := o) (q := q) (r := r) (by omega_using [ho, hA]) hqf hrf hoq hor (sep1_o hq) hq4 hr4 hc hsw h11)
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

end VG.Proof.Ed448.RISCV64

end

end

/-! ### `Ed448.RISCV64.VDecodeCheck`, which this module and modules that import it used -/

section

/-! ### `Ed448.RISCV64.VDecodeY`, which this module and modules that import it used -/

section

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
  obtain hcs : Ctx b s := hc.of_rest h.rest (by decide)
  obtain win : wd s.mem b (p + 4 * k) = wd s0.mem b (p + 4 * k) :=
    wd_frame h.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
      · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  refine lw0_ok hcs (d := p + 4 * k) (by omega_arith) (by omega_arith) fun t1 v1 => ?_
  obtain hc1 : Ctx b t1 := hcs.of_rest (v1.rest (ws := [.a4]) (by decide)) (by decide)
  refine sw0_ok hc1 (d := DY + 4 * k) (by omega_arith) (by omega_arith) fun t2 v2 => ?_
  refine sw0_ok (hc1.of_rest (v2.rest []) (by decide)) (d := X2 + 4 * k) (by omega_arith) (by omega_arith)
    fun t3 v3 => WP.block_nil ?_
  obtain ev : ((t1.gpr .a4).setWidth 32).toNat = wd s0.mem b (p + 4 * k) := by
    rw [v1.gpr, lo32_ext, ← win]; rfl
  obtain ev2 : t2.gpr .a4 = t1.gpr .a4 := by rw [v2.gpr]
  obtain hm3 : t3.mem = (s.mem.writeW (b + BitVec.ofNat 64 (DY + 4 * k)) ((t1.gpr .a4).setWidth 32)).writeW
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
  obtain hc1 : VCtx b s1 := hc.of_rest h1.rest (by decide) (by decide)
  obtain f1 : Frame (yW b) s.mem s1.mem := h1.frame.sub fun r hr => ⟨_, List.mem_cons_self .., by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by omega_arith)⟩
  -- The full reduction.
  refine WP.append (freeze_ok hc1.ctx hc1.a0 (fun k hk => by
      rw [Offset.add_add]; exact hc1.inW (by unfold OUT; omega_arith))
    ((Offset.disjoint_base b (d := OUT) (n := 56) (k := 2048) (by decide) (by decide)).symm))
    fun s2 ⟨_, hr2, hf2, hw2⟩ => ?_
  obtain hc2 : VCtx b s2 := hc1.of_rest hr2 (by decide) (by decide)
  obtain f2 : Frame (yW b) s1.mem s2.mem := hf2.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by omega_arith)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (Nat.le_refl _)⟩
  obtain hv1 : V s1.mem b X2 = yw s.mem b p := val32_congr fun j hj => (h1.vals j hj).2
  -- The comparison.
  refine WP.append (outSame_ok hc2 (p := p) (by omega_arith) hp4) fun s3 ⟨hr3, hf3, hb3⟩ => ?_
  obtain hc3 : VCtx b s3 := hc2.of_rest hr3 (by decide) (by decide)
  obtain f3 : Frame (yW b) s2.mem s3.mem := hf3.mono fun r hr => by
    rw [List.mem_singleton.mp hr]; simp
  -- The last byte.
  refine wp_lbz (a := b + BitVec.ofNat 64 (p + 56)) (by omega_arith) (by rw [hc3.ctx.a3])
    (hc3.inR (by omega_arith)) fun s4 u4 => wp_li (by decide) fun s5 u5 => wp_and fun s6 u6 => ?_
  obtain hr6 : Rest [.a4, .a5] s3 s6 :=
    (u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide)))
  obtain hm6 : s6.mem = s3.mem := by rw [u6.mem, u5.mem, u4.mem]
  obtain hc6 : VCtx b s6 := hc3.of_rest hr6 (by decide) (by decide)
  obtain hB : (s3.mem (b + BitVec.ofNat 64 (p + 56))).toNat = (s.mem (b + BitVec.ofNat 64 (p + 56))).toNat := by
    rw [yW_byte f3 (by omega_arith) (.inl (by omega_arith)), yW_byte f2 (by omega_arith) (.inl (by omega_arith)),
      yW_byte f1 (by omega_arith) (.inl (by omega_arith))]
  obtain e7 : (s6.gpr .a4).toNat = (s.mem (b + BitVec.ofNat 64 (p + 56))).toNat := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, toNat_imm (by omega_arith), hB]
  obtain e8 : (s6.gpr .a5).toNat = (s.mem (b + BitVec.ofNat 64 (p + 56))).toNat % 128 := by
    rw [u6.gpr, u5.gpr, u5.other _ (by decide), u4.gpr, hB, toNat_and127 _ (by omega_arith)]
  refine WP.append (orBad_ok hc6 (r := .a5) (by decide)) fun s7 ⟨hr7, hf7, hb7⟩ => ?_
  obtain hc7 : VCtx b s7 := hc6.of_rest hr7 (by decide) (by decide)
  -- The sign.
  refine wp_srl (by decide) fun s8 u8 => ?_
  refine wp_sb (a := b + BitVec.ofNat 64 SIGN) (by decide)
    (by rw [u8.other _ (by decide), hc7.ctx.a3]) (by rw [u8.wr]; exact hc7.inW (by decide)) fun s9 u9 => ?_
  obtain hc9 : VCtx b s9 := hc7.of_rest ((u8.rest (ws := [.a4]) (by decide)).trans (u9.rest _)) (by decide)
    (by decide)
  obtain hm9 : s9.mem = s7.mem.writeW (b + BitVec.ofNat 64 SIGN) ((s8.gpr .a4).setWidth 8) := by
    rw [u9.mem, u8.mem]
  refine WP.mono (constField_ok hc9.ctx (o := DON) (by decide) (by decide) (v := 1) (by decide)) fun t ⟨hrt, hft, hvt⟩ => ?_
  obtain f9 : Frame (yW b) s7.mem t.mem := by
    refine (Frame.trans (m₂ := s9.mem) ?_ (hft.sub fun r hr => ⟨_, List.mem_cons_self .., by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by unfold DON; omega_arith)⟩))
    rw [hm9]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ (8 / 8))
  obtain f7 : Frame (yW b) s3.mem s7.mem := by
    rw [← hm6]; exact hf7.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp
  obtain hrt' : Rest [.a1, .a2, .a4, .a5, .a6, .a7, .t0] s t :=
    (h1.rest.mono (by decide)).trans ((hr2.mono (by decide)).trans ((hr3.mono (by decide)).trans
      ((hr6.mono (by decide)).trans ((hr7.mono (by decide)).trans (((u8.rest (ws := [.a4]) (by decide)).trans
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

end VG.Proof.Ed448.RISCV64

end

end

/-!
# Ed448's verification on RISCV64: the checks of the candidate x-coordinate

`decodeCheck` checks `v x² = u` and that `x = 0` does not come with the sign
1 (at `SIGN`), and leaves `x` fully reduced at `OUT` (`decodeCheck_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (X2 Y ACC freeze)
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

theorem decodeCheck_eq : decodeCheck = R64.opsCode [.mul DTMP DXX DXX, .mul DTMP DV DTMP]
    (.block (Impl.X448.RISCV64.R64.sub X2 DTMP DU ++ freeze ++ outZero ++ copy X2 DXX ++ freeze ++ outOr ++
      ([.addi .a7 .a7 (-1), .shift .srl .d .a7 .a7 63, .load .b .a4 .a3 SIGN, .logic .and .a5 .a7 .a4] : List Instr) ++
        orBad .a5)) := rfl

theorem decodeCheck_ok {s : State} (hc : VCtx b s) {x v u : Fe} (hx : FS s.mem b DXX = x)
    (hv : FS s.mem b DV = v) (hu : FS s.mem b DU = u) {sg : Nat} (hsg : sg ≤ 1)
    (hs : s.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg) :
    WP isa decodeCheck s fun t => VCtx b t ∧ Rest R64.work s t ∧
      Frame (yW b) s.mem t.mem ∧ (∀ q ∈ [DXX, DY, DK], FS t.mem b q = FS s.mem b q) ∧
      t.mem (b + BitVec.ofNat 64 SIGN) = s.mem (b + BitVec.ofNat 64 SIGN) ∧
      VG.Spec.X448.bytesAt t.mem (b + BitVec.ofNat 64 OUT) 56 = Proof.X25519.leBytes 56 x.val ∧
      (bad t.mem b = 0 ↔ bad s.mem b = 0 ∧ v * (x * x) = u ∧ ¬ (x = 0 ∧ sg = 1)) := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hA := ACC_eq
  have hX : X2 = 56 := rfl
  have hY : Y = 896 := rfl
  obtain h0 : R64.Cur b s (s.gpr .t2) (s.gpr .t1) CQ (FS s.mem b) s := ⟨hc.ctx, R64.Stp.refl _ _, rfl, rfl, fun _ _ => rfl⟩
  rw [decodeCheck_eq]
  refine R64.ops_ok _ CQ _ s (by decide) h0 fun s1 h1 => ?_
  simp only [outZero, copy, List.append_assoc, List.cons_append, List.nil_append]
  obtain hc1 : VCtx b s1 := hc.of_rest h1.stp.rest (by decide) (by decide)
  -- `v x² - u` into `X2`.
  refine WP.append (R64.subS (o := X2) (x := DTMP) (y := DU) (by decide) (by decide) (by decide) (by decide)
    h1.ctx h1.slots) fun s2 ⟨hr2, hf2, hS2⟩ => ?_
  obtain hc2 : VCtx b s2 := hc1.of_rest hr2 (by decide) (by decide)
  obtain e2 : FS s2.mem b X2 = v * (x * x) - u := by
    rw [hS2 X2 (by decide)]
    have hx' : FS s.mem b 672 = x := hx
    have hv' : FS s.mem b 448 = v := hv
    have hu' : FS s.mem b 392 = u := hu
    simp only [upd, runOps, FOp.out, FOp.val, X2, DTMP, DXX, DV, DU, Nat.reduceEqDiff, ↓reduceIte, hx', hv', hu']
  -- Its full reduction, checked to be 0.
  refine WP.append (freeze_ok hc2.ctx hc2.a0 (fun k hk => by rw [Offset.add_add]; exact hc2.inW (by omega_arith))
    ((Offset.disjoint_base b (d := OUT) (n := 56) (k := 2048) (by omega_arith) (by omega_arith)).symm))
    fun s3 ⟨_, hr3, hf3, hw3⟩ => ?_
  obtain hc3 : VCtx b s3 := hc2.of_rest hr3 (by decide) (by decide)
  obtain hdo : Region.Disjoint ⟨b, 2048⟩ ⟨b + BitVec.ofNat 64 OUT, 56⟩ :=
    (Offset.disjoint_base b (d := OUT) (n := 56) (k := 2048) (by omega_arith) (by omega_arith)).symm
  obtain hS3 := slots_freeze hf3 hdo hS2 (by decide)
  refine WP.append (outOr_ok hc3) fun s4 ⟨hr4, hm4, hv4⟩ => ?_
  obtain hc4 : VCtx b s4 := hc3.of_rest hr4 (by decide) (by decide)
  refine WP.append (orBad_ok hc4 (r := .a7) (by decide)) fun s5 ⟨hr5, hf5, hb5⟩ => ?_
  obtain hc5 : VCtx b s5 := hc4.of_rest hr5 (by decide) (by decide)
  obtain hS5 := SlotsOk.lo (m := s3.mem) (m' := s5.mem) (by rw [← hm4]; exact hf5) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact disj_hi (by omega_arith) (by omega_arith)) hS3 (by decide)
  -- `x` into `X2`, and its full reduction.
  refine wp_li (by decide) fun s6 u6 => ?_
  obtain hc6 : VCtx b s6 := hc5.of_rest (u6.rest (ws := [.t0]) (by decide)) (by decide) (by decide)
  refine WP.append (sel_ok (b := b) (o := X2) (q := DXX) (r := DXX) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc6.ctx (sw := 0) (by decide) (by rw [u6.gpr]; rfl)) fun s7 h7 => ?_
  obtain hc7 : VCtx b s7 := hc6.of_rest h7.rest (by decide) (by decide)
  obtain e7 : V s7.mem b X2 = V s6.mem b DXX := val32_congr fun j hj => h7.lo j hj
  refine WP.append (freeze_ok hc7.ctx hc7.a0 (fun k hk => by rw [Offset.add_add]; exact hc7.inW (by omega_arith))
    hdo) fun s8 ⟨hb8, hr8, hf8, hw8⟩ => ?_
  obtain hc8 : VCtx b s8 := hc7.of_rest hr8 (by decide) (by decide)
  refine WP.append (outOr_ok hc8) fun s9 ⟨hr9, hm9, hv9⟩ => ?_
  obtain hc9 : VCtx b s9 := hc8.of_rest hr9 (by decide) (by decide)
  -- Zero with the sign 1.
  refine wp_subi (by decide) fun s10 u10 => wp_srl (by decide) fun s11 u11 => ?_
  refine wp_lbz (a := b + BitVec.ofNat 64 SIGN) (by omega_arith)
    (by rw [u11.other _ (by decide), u10.other _ (by decide), hc9.ctx.a3]) (by
      rw [u11.rd, u11.wr, u10.rd, u10.wr]; exact hc9.inR (by omega_arith)) fun s12 u12 => wp_and fun s13 u13 => ?_
  obtain hr13 : Rest [.a4, .a5, .a7] s9 s13 := (u10.rest (by decide)).trans ((u11.rest (by decide)).trans
    ((u12.rest (by decide)).trans (u13.rest (by decide))))
  obtain hm13 : s13.mem = s9.mem := by rw [u13.mem, u12.mem, u11.mem, u10.mem]
  obtain hc13 : VCtx b s13 := hc9.of_rest hr13 (by decide) (by decide)
  refine WP.mono (orBad_ok hc13 (r := .a5) (by decide)) fun t ⟨hrt, hft, hbt⟩ => ?_
  have hX' : DXX = 672 := rfl
  -- The registers.
  obtain hrw : Rest R64.work s t := by
    refine h1.stp.rest.trans ((hr2.mono (by decide)).trans ((hr3.mono (by decide)).trans ?_))
    refine (hr4.mono (by decide)).trans ((hr5.mono (by decide)).trans ?_)
    refine ((u6.rest (ws := [.t0]) (by decide)).mono (by decide)).trans ((h7.rest.mono (by decide)).trans ?_)
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
    obtain hsg12 : (s12.gpr .a4).toNat = sg := by
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
    obtain hz12 : (s12.gpr .a7).toNat =
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
end VG.Proof.Ed448.RISCV64
end

end

/-! ### `Ed448.RISCV64.VDecodeNeg`, which only this module used -/

section

/-!
# Ed448's verification on RISCV64: the negated point

`decodeNeg xo yo` writes `-x'` to `xo` and `y` to `yo`, for `x'` the decoded
x-coordinate: `(x - x) - x` if the low bit of `x` (fully reduced at `OUT`) is
the sign, else `x` (`decodeNeg_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (X2 Y ACC)
open VG.Spec.X448 (P Fe)

section
variable {b : Addr}

theorem xor_le_one' {x y : Nat} (hx : x ≤ 1) (hy : y ≤ 1) : x ^^^ y ≤ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with rfl | rfl <;> decide

/-- The slots of `-x'` and `y`, above the field area and below `PK`, at multiples of 4. -/
def NegOut (xo yo : Nat) : Prop :=
  1064 ≤ xo ∧ xo + 56 ≤ PK ∧ 1064 ≤ yo ∧ yo + 56 ≤ PK ∧ (xo + 56 ≤ yo ∨ yo + 56 ≤ xo) ∧
    xo % 4 = 0 ∧ yo % 4 = 0

theorem decodeNeg_ok {s : State} (hc : VCtx b s) {xo yo : Nat} (ho : NegOut xo yo) {x y : Fe}
    (hx : FS s.mem b DXX = x) (hy : FS s.mem b DY = y)
    (hout : VG.Spec.X448.bytesAt s.mem (b + BitVec.ofNat 64 OUT) 56 = Proof.X25519.leBytes 56 x.val)
    {sg : Nat} (hsg : sg ≤ 1) (hs : s.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg) :
    WP isa (.block (decodeNeg xo yo)) s fun t => VCtx b t ∧ Rest R64.clob64 s t ∧
      Frame [FA b, ⟨b + BitVec.ofNat 64 xo, 56⟩, ⟨b + BitVec.ofNat 64 yo, 56⟩] s.mem t.mem ∧
      FS t.mem b xo = pick (x.val % 2 ^^^ sg) ((x - x) - x) x ∧ FS t.mem b yo = y ∧
      FS t.mem b DK = FS s.mem b DK := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  obtain ⟨hx1, hx2, hy1, hy2, hxy, hx4, hy4⟩ := ho
  have hPK : PK = 1456 := rfl
  have hDY : DY = 168 := rfl
  have hA := ACC_eq
  unfold decodeNeg
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  obtain hS0 : SlotsOk s.mem b [DXX, DY, DK] (FS s.mem b) := fun _ _ => rfl
  refine WP.append (R64.subS (o := DTMP) (x := DXX) (y := DXX) (by decide) (by decide) (by decide) (by decide)
    hc.ctx hS0) fun s1 ⟨hr1, hf1, hS1⟩ => ?_
  obtain hc1 : VCtx b s1 := hc.of_rest hr1 (by decide) (by decide)
  refine WP.append (R64.subS (o := DNEG) (x := DTMP) (y := DXX) (by decide) (by decide) (by decide) (by decide)
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
  refine wp_lbz (a := b + BitVec.ofNat 64 OUT) (by decide) (by rw [hc2.a0, BitVec.add_zero])
    (by rw [← BitVec.add_zero (b + BitVec.ofNat 64 OUT)]; exact (by rw [Offset.add_add]; exact hc2.inR (by omega_arith)))
    fun s3 u3 => wp_li (by decide) fun s4 u4 => wp_and fun s5 u5 => ?_
  refine wp_lbz (a := b + BitVec.ofNat 64 SIGN) (by omega_arith)
    (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), hc2.ctx.a3])
    (by rw [u5.rd, u5.wr, u4.rd, u4.wr, u3.rd, u3.wr]; exact hc2.inR (by omega_arith)) fun s6 u6 => wp_xor fun s7 u7 => ?_
  refine wp_li (by decide) fun s8 u8 => wp_sub fun s9 u9 => ?_
  obtain hm9 : s9.mem = s2.mem := by rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem]
  obtain hr9 : Rest [.a4, .a5, .a6, .t0] s2 s9 := (u3.rest (by decide)).trans ((u4.rest (by decide)).trans
    ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans ((u7.rest (by decide)).trans
      ((u8.rest (by decide)).trans (u9.rest (by decide)))))))
  obtain hc9 : VCtx b s9 := hc2.of_rest hr9 (by decide) (by decide)
  obtain hsg' : sg < 2 ^ 64 := by omega_arith
  obtain hm : x.val % 2 ^^^ sg ≤ 1 := xor_le_one' (by omega_arith) hsg
  obtain e5 : (s5.gpr .a5).toNat = x.val % 2 := by
    rw [u5.gpr, BitVec.toNat_and, u4.other _ (by decide), u4.gpr, u3.gpr, hb2]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [Nat.and_one_is_mod]
    omega_arith
  obtain e6 : (s6.gpr .a4).toNat = sg := by
    rw [u6.gpr, u5.mem, u4.mem, u3.mem, hs2]
    simp only [BitVec.toNat_ofNat, Nat.reducePow]
    omega_arith
  obtain e7 : s7.gpr .a5 = BitVec.ofNat 64 (x.val % 2 ^^^ sg) := by
    apply BitVec.eq_of_toNat_eq
    rw [u7.gpr, BitVec.toNat_xor, u6.other _ (by decide), e5, e6, toNat_imm (by omega_arith)]
  obtain e11 : s9.gpr .t0 = 0 - BitVec.ofNat 64 (x.val % 2 ^^^ sg) := by
    rw [u9.gpr, u8.gpr, u8.other _ (by decide), e7]; rfl
  -- The selections.
  refine WP.append (sel_ok (b := b) (o := xo) (q := DNEG) (r := DXX) (by omega_arith) (by decide) (by decide)
    (by unfold DNEG; omega_arith) (by unfold DXX; omega_arith) hx4 (by decide) (by decide) hc9.ctx hm e11) fun s10 h10 => ?_
  obtain hc10 : VCtx b s10 := hc9.of_rest h10.rest (by decide) (by decide)
  refine WP.mono (sel_ok (b := b) (o := yo) (q := DY) (r := DY) (by omega_arith) (by decide) (by decide)
    (by unfold DY; omega_arith) (by unfold DY; omega_arith) hy4 (by decide) (by decide) hc10.ctx hm (by rw [h10.rest.gpr _ (by decide), e11]))
    fun t ht => ?_
  obtain hrt : Rest R64.clob64 s t :=
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
    unfold pick VG.Proof.X25519.sel; split <;> rfl

  · -- `d`, kept by both writes.
    rw [← eK, ← hm9]
    obtain f : Frame [⟨b + BitVec.ofNat 64 xo, 4 * 14⟩, ⟨b + BitVec.ofNat 64 yo, 4 * 14⟩] s9.mem t.mem :=
      (h10.frame.mono (by simp)).trans (ht.frame.mono (by simp))
    obtain e := limb_frame (o := DK) f fun r hr k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by unfold DK; omega_arith) (by unfold DK; omega_arith) (by omega_arith)
    rw [FS, V, val32_congr e]; rfl

end

end VG.Proof.Ed448.RISCV64

end

end

/-! ### `Ed448.RISCV64.VDecodeX`, which only this module used -/

section

/-! ### `Ed448.RISCV64.VRoot`, which only this module used -/

section

/-!
# Ed448 on RISCV64: the square root's power

`root` computes `z^((p-3)/4)` into `R` for the element `z` at `Z2`
(`rootQ_ok`) by X448's addition chain for the inversion as far as
`z^(2²²³ - 1)` (`R64.chain223Call_ok`), then 223 squarings and the product with
`z^(2²²² - 1)`, since `(p-3)/4 = (2²²³ - 1) 2²²³ + (2²²² - 1)` (`root_exp`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Impl.X448.RISCV64 (R Z2)
open VG.Impl.X448.RISCV64.R64 (T6)
open VG.Spec.X448 (P Fe)

/-- The exponent `(p - 3) / 4`. -/
def RE : Nat := (P - 3) / 4

/-- `(p - 3) / 4 = (2²²³ - 1) 2²²³ + (2²²² - 1)`. -/
theorem root_exp : (2 ^ 223 - 1) * 2 ^ 223 + (2 ^ 222 - 1) = RE := by decide +kernel

section
variable {b : Addr}

theorem rootQ_ok {qs : List Nat} (hq : R64.Sep8 R qs = true) (hZ : Z2 ∈ qs)
    (hT : R64.TempsOk qs = true) {a : BitVec 64} {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : ∀ q ∈ qs, q ≠ R → FS s.mem b q = v q) (h0 : s.gpr .t2 = a) :
    WP isa root s fun s' => R64.Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b qs (upd v R (VG.Proof.X448.pw (v Z2) RE)) := by
  obtain hZR : Z2 ≠ R := by decide
  obtain ⟨hfR, hfT, hC⟩ := R64.drop_R hq hT hc hS h0
  obtain hZf : Z2 ∈ qs.filter (· ≠ R) := by simp [hZ, hZR]
  unfold root
  refine WP.seq (WP.mono (R64.chain223Call_ok hfR hZf hfT hC) fun s1 h1 => ?_)
  obtain ⟨f6, _⟩ := R64.temps_get hfT (t := T6) (by decide)
  refine WP.seq (WP.mono (R64.sqnP (z := v Z2) (ea := 2 ^ 223 - 1) (by decide) (by decide) (by sep8)
    (by decide) (by simp) (by look) h1) fun s2 h2 => ?_)
  refine WP.mono (R64.opMulP (z := v Z2) (ea := (2 ^ 223 - 1) * 2 ^ 223) (eb := 2 ^ 222 - 1) (ee := RE)
    (by sep8) (by decide) (by simp) (by simp) (by look) (by look) root_exp h2) fun s3 ⟨c3, h3⟩ =>
    ⟨h3.stp, h3.ctx, fun q hq' => ?_⟩
  by_cases eR : q = R
  · subst eR
    rw [h3.slots _ List.mem_cons_self, upd_self, upd_self]
  · have hq'' : q ∈ qs.filter (· ≠ R) := by simp [hq', eR]
    obtain e6 : q ≠ T6 := fun e => (R64.temps_get hT (t := T6) (by decide)).2 (e ▸ hq')
    rw [h3.slots q (by repeat (first | exact hq'' | apply List.mem_cons_of_mem)), upd_of_ne _ _ eR]
    simp only [R64.chainV, upd_of_ne _ _ e6, upd_of_ne _ _ eR]

end

end VG.Proof.Ed448.RISCV64

end

end


/-!
# Ed448's verification on RISCV64: the candidate x-coordinate

`decodeX` computes, from `y` at `DY`, `1` at `DON` and `d` at `DK`,
`u = y² - 1` (at `DU`), `v = d y² - 1` (at `DV`), `t = u³v` (at `DT`) and
`x = t (t (uv)²)^((p-3)/4)` (at `DXX`) (`decodeX_ok`), as `recoverRef` has
them.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (R Z2)
open VG.Spec.X448 (P Fe)

/-- The field operations of `decodeX` before the power. -/
def xOps : List FOp :=
  [.mul DYY DY DY, .sub DU DYY DON, .mul DV DK DYY, .sub DV DV DON, .mul DT DU DU, .mul DT DT DU,
    .mul DT DT DV, .mul DW DU DV, .mul DW DW DW, .mul Z2 DT DW]

theorem decodeX_eq : decodeX = R64.opsCode xOps (.seq root (Impl.X448.RISCV64.R64.mul DXX DT R)) := rfl

/-- The slots `decodeX` reads, and `R` and `Z2`. -/
def XQ : List Nat := [DY, DON, DK, R, Z2]

theorem xOps_ok : R64.opsOk xOps XQ = true := by decide

/-- The slots kept across `root`: not `DYY` and `DW`, which its chain uses. -/
def RootQ : List Nat := [R, Z2, DT, DV, DU, DY, DK]

theorem RootQ_sub : ∀ q ∈ RootQ, q ∈ outsQ xOps XQ := by decide

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
    WP isa decodeX s fun t => R64.Stp b s t ∧ Ctx b t ∧ FS t.mem b DXX = xOf y ∧ FS t.mem b DV = vOf y ∧
      FS t.mem b DU = uOf y ∧ FS t.mem b DY = y ∧ FS t.mem b DK = Spec.Ed448.d := by
  have hy' : FS s.mem b 168 = y := hy
  have hon' : FS s.mem b 224 = 1 := hon
  have hd' : FS s.mem b 336 = Spec.Ed448.d := hd
  obtain h0 : R64.Cur b s (s.gpr .t2) (s.gpr .t1) XQ (FS s.mem b) s := ⟨hc, R64.Stp.refl _ _, rfl, rfl, fun _ _ => rfl⟩
  rw [decodeX_eq]
  refine R64.ops_ok xOps XQ _ s xOps_ok h0 fun s1 h1 => ?_
  refine WP.seq (WP.mono (rootQ_ok (qs := RootQ) (by decide) (by decide) (by decide) h1.ctx
    (fun q hq _ => h1.slots q (RootQ_sub q hq)) h1.t2) fun s2 ⟨hst2, hc2, hS2⟩ => ?_)
  refine WP.mono (R64.mulS (o := DXX) (x := DT) (y := R) (by decide) (by decide) (by decide) (by decide) hc2 hS2)
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

end VG.Proof.Ed448.RISCV64

end

end


/-!
# Ed448's verification on RISCV64: decoding a point

`decode p xo yo` decodes the 57 bytes at `p` (RFC 8032 §5.2.3): `BAD` stays 0
exactly when they encode a point, and then `xo` and `yo` hold the
coordinates of its negation (`decode_ok`), by `decodePoint_impl`.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (X2 Y ACC)
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
    simp only [h, pick, VG.Proof.X25519.sel, Nat.reduceXor, ↓reduceIte, beq_self_eq_true,
      Nat.zero_ne_one, beq_iff_eq] <;> first | rfl | exact (fin_neg_neg x).symm

/-- The regions `decode` writes. -/
abbrev decW (b : Addr) (xo yo : Nat) : List Region :=
  yW b ++ [⟨b + BitVec.ofNat 64 DECODE_RA, 8⟩, ⟨b + BitVec.ofNat 64 xo, 56⟩, ⟨b + BitVec.ofNat 64 yo, 56⟩]

section
variable {b : Addr}

theorem decode_eq (p xo yo : Nat) : decode p xo yo =
    .seq (.block (decodeY p)) (.seq decodeCoreCall (.block (decodeNeg xo yo))) := rfl

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

/-- The writes of the shared core and its return-address slot. -/
abbrev coreW (b : Addr) : List Region := yW b ++ [⟨b + BitVec.ofNat 64 DECODE_RA, 8⟩]

/-- The decoded candidate, sign, canonical bytes and accumulated checks. -/
def CoreFacts (b : Addr) (y : Fe) (sg : Nat) (m : Mem) (t : State) : Prop :=
  FS t.mem b DXX = xOf y ∧ FS t.mem b DY = y ∧ FS t.mem b DK = Spec.Ed448.d ∧
  t.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg ∧
  VG.Spec.X448.bytesAt t.mem (b + BitVec.ofNat 64 OUT) 56 = Proof.X25519.leBytes 56 (xOf y).val ∧
  (bad t.mem b = 0 ↔ bad m b = 0 ∧ vOf y * (xOf y * xOf y) = uOf y ∧ ¬ (xOf y = 0 ∧ sg = 1))

theorem decodeCore_ok {s : State} (hc : VCtx b s) {y : Fe} (hy : FS s.mem b DY = y)
    (hon : FS s.mem b DON = 1) (hd : FS s.mem b DK = Spec.Ed448.d) {sg : Nat}
    (hsg : sg ≤ 1) (hs : s.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg) :
    WP isa decodeCore s fun t => VCtx b t ∧ Rest R64.work s t ∧ Frame (yW b) s.mem t.mem ∧
      CoreFacts b y sg s.mem t := by
  unfold decodeCore
  refine WP.seq (WP.mono (decodeX_ok hc.ctx hy hon hd)
    fun s2 ⟨hst2, hc2', hx2, hv2, hu2, hy2, hd2⟩ => ?_)
  obtain hc2 : VCtx b s2 := hc.of_rest hst2.rest (by decide) (by decide)
  obtain hs2 : s2.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg := by
    rw [← hs]
    exact hst2.frame _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint_base b (d := SIGN) (n := 1) (k := ACC + 112) (by decide) (by decide) _
        (Region.contains_self _ _) h
  refine WP.mono (decodeCheck_ok hc2 hx2 hv2 hu2 hsg hs2)
    fun s3 ⟨hc3, hr3, hf3, hk3, hs3, hout3, hb3⟩ => ?_
  obtain hb2 : bad s2.mem b = bad s.mem b := by
    unfold bad
    rw [hst2.frame.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by decide) (by decide)) (by decide)]
  exact ⟨hc3, hst2.rest.trans hr3, (hst2.frame.mono (by simp [yW])).trans hf3,
    by rw [hk3 DXX (by simp), hx2], by rw [hk3 DY (by simp), hy2],
    by rw [hk3 DK (by simp), hd2], hs3.trans hs2, hout3, by rwa [hb2] at hb3⟩

/-- The shared decode call preserves its caller's return address, including
across its nested exponentiation call. -/
theorem decodeCoreCall_ok {s : State} (hc : VCtx b s) {y : Fe} (hy : FS s.mem b DY = y)
    (hon : FS s.mem b DON = 1) (hd : FS s.mem b DK = Spec.Ed448.d) {sg : Nat}
    (hsg : sg ≤ 1) (hs : s.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg) :
    WP isa decodeCoreCall s fun t => VCtx b t ∧ Rest R64.work s t ∧ Frame (coreW b) s.mem t.mem ∧
      CoreFacts b y sg s.mem t := by
  unfold decodeCoreCall
  refine WP.seq (R64.sd_ok hc.ctx (by decide) (by decide) fun s1 u1 => WP.block_nil ?_)
  obtain hc1 := hc.of_rest (u1.rest []) (by decide) (by decide)
  obtain fs : Frame [⟨b + BitVec.ofNat 64 DECODE_RA, 8⟩] s.mem s1.mem := by
    rw [u1.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have keepFS {q : Nat} (hq : q + 56 ≤ DECODE_RA) : FS s1.mem b q = FS s.mem b q := by
    obtain e := limb_frame fs (o := q) fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      have hRA : DECODE_RA = 1712 := rfl
      exact Offset.disjoint b (.inl (by omega_using [hq, hk])) (by omega_using [hq, hk, hRA]) (by decide)
    rw [FS, V, val32_congr e]; rfl
  obtain hsign : s1.mem (b + BitVec.ofNat 64 SIGN) = s.mem (b + BitVec.ofNat 64 SIGN) :=
    fs _ fun r hr hcon => by
      rw [List.mem_singleton.mp hr] at hcon
      exact Offset.disjoint b (d := SIGN) (n := 1) (e := DECODE_RA) (k := 8)
        (by decide) (by decide) (by decide) _ (Region.contains_self _ _) hcon
  obtain hbad : bad s1.mem b = bad s.mem b := by
    unfold bad
    rw [fs.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint b (by decide) (by decide) (by decide)) (by decide)]
  obtain hcE : VCtx b s1.callEntry := ⟨⟨hc1.ctx.a3, hc1.ctx.al, hc1.ctx.wr⟩, hc1.ws, hc1.a0⟩
  obtain ⟨tr, s2, he, hc2, hr2, hf2, facts⟩ := decodeCore_ok hcE
    ((keepFS (q := DY) (by decide)).trans hy) ((keepFS (q := DON) (by decide)).trans hon)
    ((keepFS (q := DK) (by decide)).trans hd) hsg (hsign.trans hs)
  obtain hra := hr2.gpr .ra (by decide)
  obtain hret : isa.ret s1.callEntry s2 = some s2 := by simp only [isa, ret, hra, ↓reduceIte]
  refine WP.seq ⟨_, s2, Exec.call (call_callEntry s1) he hret, ?_⟩
  obtain saved : s2.mem.readW (b + BitVec.ofNat 64 DECODE_RA) 64 = s.gpr .ra := by
    rw [hf2.readW (Region.contains_self _ (64 / 8)) ?_ (by decide), State.callEntry_mem,
      u1.mem, Mem.readW_writeW_self64]
    intro r hr
    simp only [yW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint_base b (by decide) (by decide)
    all_goals exact Offset.disjoint b (by decide) (by decide) (by decide)
  refine R64.ld_ok hc2.ctx (by decide) (by decide) fun s3 u3 => WP.block_nil ?_
  obtain rest : Rest R64.work s s3 := by
    refine ⟨?_, u3.rd.trans (hr2.rd.trans u1.rd), u3.wr.trans (hr2.wr.trans u1.wr),
      u3.sp.trans (hr2.sp.trans u1.sp)⟩
    intro r hr
    by_cases er : r = .ra
    · subst r; exact u3.gpr.trans saved
    · rw [u3.other r er, hr2.gpr r hr,
        State.callEntry_gpr s1 (by
          obtain hn : ∀ (r : Reg), r ∉ R64.work → r ≠ Reg.ra → r ∉ linkRegs := by
            intro r; cases r <;> simp [R64.work, linkRegs]
          exact hn r hr er), u1.gpr]
  refine ⟨hc2.of_rest (u3.rest (ws := [.ra]) (by decide)) (by decide) (by decide), rest, ?_, ?_⟩
  · rw [u3.mem]
    exact (fs.mono (by simp [coreW])).trans (hf2.mono (by simp [coreW]))
  · unfold CoreFacts at facts ⊢
    rw [u3.mem]
    simpa only [State.callEntry_mem, hbad] using facts

theorem decode_ok (hR : Proof.Ed448.RecoverOk) {s : State} (hc : VCtx b s) {p : Nat} (hp : 1064 ≤ p)
    (hp' : p + 57 ≤ 1696) (hp4 : p % 4 = 0) {xo yo : Nat} (ho : NegOut xo yo) (hd : FS s.mem b DK = Spec.Ed448.d) :
    WP isa (decode p xo yo) s fun t => VCtx b t ∧ Rest R64.work s t ∧ Frame (decW b xo yo) s.mem t.mem ∧
      FS t.mem b DK = Spec.Ed448.d ∧
      (bad t.mem b = 0 ↔ bad s.mem b = 0 ∧
        (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 p) 57)).isSome) ∧
      ∀ pt, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 p) 57) = some pt →
        FS t.mem b xo = 0 - pt.X ∧ FS t.mem b yo = pt.Y ∧ pt.Z = 1 := by
  rw [decode_eq]
  refine WP.seq (WP.mono (decodeY_ok hc hp hp' hp4) fun s1 ⟨hc1, hr1, hf1, hy1, hon1, hk1, hs1, hb1⟩ => ?_)
  generalize hB : (s.mem (b + BitVec.ofNat 64 (p + 56))).toNat = B at hs1 hb1
  obtain hBl : B < 256 := by rw [← hB]; exact BitVec.isLt _
  obtain hsg : B / 128 ≤ 1 := by omega_using [hB]
  generalize hY : VG.Proof.X448.toFe (yw s.mem b p) = y
  obtain hy : FS s1.mem b DY = y := by rw [FS, hy1, hY]
  obtain hon : FS s1.mem b DON = 1 := by rw [FS, hon1]; rfl
  refine WP.seq (WP.mono (decodeCoreCall_ok hc1 hy hon (hk1.trans hd) hsg hs1)
    fun s3 ⟨hc3, hr3, hf3, hx3, hy3, hd3, hs3, hout3, hb3⟩ => ?_)
  refine WP.mono (decodeNeg_ok hc3 ho hx3 hy3 hout3 hsg hs3)
    fun t ⟨hct, hrt, hft, hxt, hyt, hkt⟩ => ?_
  obtain ⟨ho1, ho2, ho3, ho4, ho5, -, -⟩ := ho
  have hPK : PK = 1456 := rfl
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
  refine ⟨hct, hr1.mono (by decide) |>.trans (hr3.trans (hrt.mono (by decide))), ?_,
    by rw [hkt, hd3], ?_, ?_⟩
  · -- The frame.
    refine (hf1.mono (by simp [decW])).trans ((hf3.mono (by simp [coreW, decW])).trans (hft.mono ?_))
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [decW]
  · -- The checks.
    rw [hbt, hb3, hb1, hdp]
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

end VG.Proof.Ed448.RISCV64
