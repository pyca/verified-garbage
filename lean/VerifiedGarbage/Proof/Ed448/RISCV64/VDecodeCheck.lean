module

public import VerifiedGarbage.Proof.Ed448.RISCV64.VDecodeY
public import VerifiedGarbage.Proof.X448.RISCV64.Ladder
public import VerifiedGarbage.Spec.X448.Contract
public import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseEncode
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseSel
import VerifiedGarbage.Proof.X448.RISCV64.Freeze
import VerifiedGarbage.Proof.X448.RISCV64.Mul
import VerifiedGarbage.Proof.X448.Field
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.X25519.RISCV64.Pass
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Ladder

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

theorem dcW_sub {b : Addr} : ∀ r ∈ [⟨b + BitVec.ofNat 64 Y, 56⟩, ⟨b + BitVec.ofNat 64 OUT, 56⟩],
    ∃ r' ∈ yW b, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (Nat.le_refl _)⟩

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
  have h0 : R64.Cur b s (s.gpr .t2) (s.gpr .t1) CQ (FS s.mem b) s := ⟨hc.ctx, R64.Stp.refl _ _, rfl, rfl, fun _ _ => rfl⟩
  rw [decodeCheck_eq]
  refine R64.ops_ok _ CQ _ s (by decide) h0 fun s1 h1 => ?_
  simp only [outZero, copy, List.append_assoc, List.cons_append, List.nil_append]
  have hc1 : VCtx b s1 := hc.of_rest h1.stp.rest (by decide) (by decide)
  -- `v x² - u` into `X2`.
  refine WP.append (R64.subS (o := X2) (x := DTMP) (y := DU) (by decide) (by decide) (by decide) (by decide)
    h1.ctx h1.slots) fun s2 ⟨hr2, hf2, hS2⟩ => ?_
  have hc2 : VCtx b s2 := hc1.of_rest hr2 (by decide) (by decide)
  have e2 : FS s2.mem b X2 = v * (x * x) - u := by
    rw [hS2 X2 (by decide)]
    have hx' : FS s.mem b 672 = x := hx
    have hv' : FS s.mem b 448 = v := hv
    have hu' : FS s.mem b 392 = u := hu
    simp only [upd, runOps, FOp.out, FOp.val, X2, DTMP, DXX, DV, DU, Nat.reduceEqDiff, ↓reduceIte, hx', hv', hu']
  -- Its full reduction, checked to be 0.
  refine WP.append (freeze_ok hc2.ctx hc2.a0 (fun k hk => by rw [Offset.add_add]; exact hc2.inW (by omega_arith))
    ((Offset.disjoint_base b (d := OUT) (n := 56) (k := 2048) (by omega_arith) (by omega_arith)).symm))
    fun s3 ⟨_, hr3, hf3, hw3⟩ => ?_
  have hc3 : VCtx b s3 := hc2.of_rest hr3 (by decide) (by decide)
  have hdo : Region.Disjoint ⟨b, 2048⟩ ⟨b + BitVec.ofNat 64 OUT, 56⟩ :=
    (Offset.disjoint_base b (d := OUT) (n := 56) (k := 2048) (by omega_arith) (by omega_arith)).symm
  have hS3 := slots_freeze hf3 hdo hS2 (by decide)
  refine WP.append (outOr_ok hc3) fun s4 ⟨hr4, hm4, hv4⟩ => ?_
  have hc4 : VCtx b s4 := hc3.of_rest hr4 (by decide) (by decide)
  refine WP.append (orBad_ok hc4 (r := .a7) (by decide)) fun s5 ⟨hr5, hf5, hb5⟩ => ?_
  have hc5 : VCtx b s5 := hc4.of_rest hr5 (by decide) (by decide)
  have hS5 := SlotsOk.lo (m := s3.mem) (m' := s5.mem) (by rw [← hm4]; exact hf5) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact disj_hi (by omega_arith) (by omega_arith)) hS3 (by decide)
  -- `x` into `X2`, and its full reduction.
  refine wp_li (by decide) fun s6 u6 => ?_
  have hc6 : VCtx b s6 := hc5.of_rest (u6.rest (ws := [.t0]) (by decide)) (by decide) (by decide)
  refine WP.append (sel_ok (b := b) (o := X2) (q := DXX) (r := DXX) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc6.ctx (sw := 0) (by decide) (by rw [u6.gpr]; rfl)) fun s7 h7 => ?_
  have hc7 : VCtx b s7 := hc6.of_rest h7.rest (by decide) (by decide)
  have e7 : V s7.mem b X2 = V s6.mem b DXX := val32_congr fun j hj => h7.lo j hj
  refine WP.append (freeze_ok hc7.ctx hc7.a0 (fun k hk => by rw [Offset.add_add]; exact hc7.inW (by omega_arith))
    hdo) fun s8 ⟨hb8, hr8, hf8, hw8⟩ => ?_
  have hc8 : VCtx b s8 := hc7.of_rest hr8 (by decide) (by decide)
  refine WP.append (outOr_ok hc8) fun s9 ⟨hr9, hm9, hv9⟩ => ?_
  have hc9 : VCtx b s9 := hc8.of_rest hr9 (by decide) (by decide)
  -- Zero with the sign 1.
  refine wp_subi (by decide) fun s10 u10 => wp_srl (by decide) fun s11 u11 => ?_
  refine wp_lbz (a := b + BitVec.ofNat 64 SIGN) (by omega_arith)
    (by rw [u11.other _ (by decide), u10.other _ (by decide), hc9.ctx.a3]) (by
      rw [u11.rd, u11.wr, u10.rd, u10.wr]; exact hc9.inR (by omega_arith)) fun s12 u12 => wp_and fun s13 u13 => ?_
  have hr13 : Rest [.a4, .a5, .a7] s9 s13 := (u10.rest (by decide)).trans ((u11.rest (by decide)).trans
    ((u12.rest (by decide)).trans (u13.rest (by decide))))
  have hm13 : s13.mem = s9.mem := by rw [u13.mem, u12.mem, u11.mem, u10.mem]
  have hc13 : VCtx b s13 := hc9.of_rest hr13 (by decide) (by decide)
  refine WP.mono (orBad_ok hc13 (r := .a5) (by decide)) fun t ⟨hrt, hft, hbt⟩ => ?_
  have hX' : DXX = 672 := rfl
  -- The registers.
  have hrw : Rest R64.work s t := by
    refine h1.stp.rest.trans ((hr2.mono (by decide)).trans ((hr3.mono (by decide)).trans ?_))
    refine (hr4.mono (by decide)).trans ((hr5.mono (by decide)).trans ?_)
    refine ((u6.rest (ws := [.t0]) (by decide)).mono (by decide)).trans ((h7.rest.mono (by decide)).trans ?_)
    exact (hr8.mono (by decide)).trans ((hr9.mono (by decide)).trans ((hr13.mono (by decide)).trans
      (hrt.mono (by decide))))
  -- The memory.
  let L2 : List Region := [FA b, ⟨b + BitVec.ofNat 64 OUT, 56⟩, ⟨b + BitVec.ofNat 64 BAD, 8⟩]
  have sFA : ∀ {m m' : Mem} {o n : Nat}, o + n ≤ 1064 → Frame [⟨b + BitVec.ofNat 64 o, n⟩] m m' → Frame L2 m m' :=
    fun ho hf => hf.sub fun r hr => ⟨_, List.mem_cons_self .., by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega_arith)⟩
  have sYO : ∀ {m m' : Mem}, Frame [⟨b + BitVec.ofNat 64 Y, 56⟩, ⟨b + BitVec.ofNat 64 OUT, 56⟩] m m' →
      Frame L2 m m' := fun hf => hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by omega_arith)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (Nat.le_refl _)⟩
  have sB : ∀ {m m' : Mem}, Frame [⟨b + BitVec.ofNat 64 BAD, 8⟩] m m' → Frame L2 m m' :=
    fun hf => hf.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp [L2]
  have fs3 : Frame L2 s.mem s3.mem :=
    (h1.stp.frame.mono (by simp [L2])).trans ((hf2.mono (by simp [L2])).trans (sYO hf3))
  have f58 : Frame L2 s5.mem s8.mem := by
    rw [← u6.mem]; exact (sFA (o := X2) (n := 4 * 14) (by omega_arith) h7.frame).trans (sYO hf8)
  have f8t : Frame L2 s8.mem t.mem := by rw [← hm9, ← hm13]; exact sB hft
  have fst : Frame L2 s.mem t.mem := fs3.trans ((by rw [← hm4]; exact sB hf5 : Frame L2 s3.mem s5.mem).trans
    (f58.trans f8t))
  -- The slots kept, through `s5`.
  have k5 : ∀ q ∈ [DXX, DY, DK], FS s5.mem b q = FS s.mem b q := by
    intro q hq
    rw [hS5 q (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl | rfl <;> decide)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;>
      simp only [upd, runOps, FOp.out, X2, DTMP, DXX, DY, DK, Nat.reduceEqDiff, ↓reduceIte]
  have kt : ∀ q ∈ [DXX, DY, DK], FS t.mem b q = FS s5.mem b q := by
    intro q hq
    have hq' : (q = 672 ∨ q = 168 ∨ q = 336) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; exact hq
    have f : Frame [⟨b + BitVec.ofNat 64 X2, 56⟩, ⟨b + BitVec.ofNat 64 Y, 56⟩, ⟨b + BitVec.ofNat 64 OUT, 56⟩,
        ⟨b + BitVec.ofNat 64 BAD, 8⟩] s5.mem t.mem := by
      rw [← u6.mem]
      refine (h7.frame.mono (by simp)).trans ((hf8.mono ?_).trans ?_)
      · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp
      · rw [← hm9, ← hm13]; exact hft.mono (by simp)
    have e := limb_frame (o := q) f fun r hr k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    rw [FS, V, val32_congr e]; rfl
  have hxv : V s7.mem b X2 % P = x.val := by
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
    have hi := List.mem_range.mp hi
    rw [Offset.add_add, hft _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint b (d := OUT + i) (n := 1) (e := BAD) (k := 8) (by omega_arith) (by omega_arith) (by omega_arith) _
        (Region.contains_self _ _) h, hm13, hm9]
  · -- The checks.
    have rB : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
        (∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 BAD, 8⟩ r) → bad m' b = bad m b := fun hf hd => by
      unfold bad; rw [hf.readW (Region.contains_self _ (64 / 8)) hd (by decide)]
    have b3 : bad s3.mem b = bad s.mem b := by
      rw [rB hf3 (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)),
        rB hf2 (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)),
        rB h1.stp.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by omega_arith) (by omega_arith))]
    have b13 : bad s13.mem b = bad s5.mem b := by
      have e1 : bad s13.mem b = bad s8.mem b := by rw [bad, bad, hm13, hm9]
      have e2 : bad s8.mem b = bad s7.mem b := rB hf8 (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
      have e3 : bad s7.mem b = bad s6.mem b :=
        rB h7.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
      have e4 : bad s6.mem b = bad s5.mem b := by rw [bad, bad, u6.mem]
      rw [e1, e2, e3, e4]
    have fs8 : Frame L2 s.mem s8.mem :=
      fs3.trans ((by rw [← hm4]; exact sB hf5 : Frame L2 s3.mem s5.mem).trans f58)
    have hsg12 : (s12.gpr .a4).toNat = sg := by
      rw [u12.gpr, toNat_imm (Nat.lt_trans (BitVec.isLt _) (by decide)), u11.mem, u10.mem, hm9]
      have : s8.mem (b + BitVec.ofNat 64 SIGN) = s.mem (b + BitVec.ofNat 64 SIGN) := by
        refine fs8 _ fun r hr => ?_
        simp only [L2, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact fun h => Offset.disjoint_base b (d := SIGN) (n := 1) (k := ACC + 112) (by omega_arith)
            (by omega_arith) _ (Region.contains_self _ _) h
        all_goals exact fun h => Offset.disjoint b (d := SIGN) (n := 1) (by omega_arith) (by omega_arith) (by omega_arith) _ (Region.contains_self _ _) h
      rw [this, hs, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    have hz := orw_lt (f := fun k => wd s8.mem (b + BitVec.ofNat 64 OUT) (4 * k)) (n := 14) fun k _ => wd_lt _ _ _
    have hz12 : (s12.gpr .a7).toNat =
        if orw (fun k => wd s8.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 = 0 then 1 else 0 := by
      rw [u12.other _ (by decide), u11.gpr, u10.gpr, ← isZero_shift hz]
      congr 3
      exact BitVec.eq_of_toNat_eq (by rw [hv9, toNat_imm (by omega_arith)])
    have hx7 : FS s7.mem b X2 = x := by
      rw [FS, e7, ← FS, show FS s6.mem b DXX = FS s5.mem b DXX by rw [u6.mem], k5 _ (by simp), hx]
    rw [hbt, b13, hb5, hm4, b3, hv4, u13.gpr, BitVec.toNat_and, hz12, hsg12, Nat.or_eq_zero_iff, Nat.or_eq_zero_iff,
      orw_eq_zero, ← val32_eq_zero, ← fs_zero hw3, e2, fin_sub_eq_zero]
    have hz0 : orw (fun k => wd s8.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 = 0 ↔ x = 0 := by
      rw [orw_eq_zero, ← val32_eq_zero, ← fs_zero hw8, hx7]
    have hr8 : ((if orw (fun k => wd s8.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 = 0 then 1 else 0) &&& sg = 0) ↔
        ¬ (x = 0 ∧ sg = 1) := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsg with rfl | rfl
      · rw [Nat.and_zero]; exact ⟨fun _ h => absurd h.2 (by decide), fun _ => rfl⟩
      · by_cases h : orw (fun k => wd s8.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 = 0
        · rw [ite_eq_left h]; exact ⟨fun h1 => absurd h1 (by decide), fun h2 => absurd ⟨hz0.mp h, rfl⟩ h2⟩
        · rw [ite_eq_right h]; exact ⟨fun _ h2 => h (hz0.mpr h2.1), fun _ => rfl⟩
    rw [hr8]; exact and_assoc
