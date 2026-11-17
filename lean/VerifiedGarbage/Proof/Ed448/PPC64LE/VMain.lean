module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.VCheckScalar
public import VerifiedGarbage.Proof.Ed448.PPC64LE.VJoint
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseMain
import VerifiedGarbage.Proof.Ed448.VerifyEq
import VerifiedGarbage.Proof.Ed448.Group.Decode
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.X25519.Bytes
public import VerifiedGarbage.Impl.Ed448.PPC64LE.VerifyEquation
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.X448.PPC64LE.Slots
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.X25519.PPC64LE.Pass
import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Ed448.PPC64LE.VChecks
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseInit
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseBits
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseSel
import VerifiedGarbage.Proof.X448.Field
import VerifiedGarbage.Proof.X448.PPC64LE.Invert
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseEncode
import VerifiedGarbage.Proof.X448.PPC64LE.Freeze
public import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseStep

/-! ### `Ed448.PPC64LE.VFinish`, which only this module used -/

section

/-!
# Ed448's verification on PPC64LE: the result

`vFinish` checks that `Q` is the neutral point, `X = 0` and `Y - Z = 0`
fully reduced, and returns 1 exactly when no check failed (`vFinish_ok`):
1 less the top bit of `BAD | -BAD` (`top_nz`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Impl.X448.PPC64LE (X2 Y Z2 ACC freeze)
open VG.Spec.X448 (P Fe)
open VG.Spec.Ed448 (Point)

/-- The top bit of `x | -x` is set exactly when `x` is not 0. -/
theorem top_nz (x : BitVec 64) : ((x ||| (0 - x)) >>> 63).toNat = if x = 0 then 0 else 1 := by
  by_cases h : x = 0
  · subst h; decide
  · rw [ite_eq_right h, BitVec.toNat_ushiftRight, BitVec.toNat_or, Nat.shiftRight_or_distrib]
    obtain hx : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    have hlt := x.isLt
    obtain hn : (0 - x).toNat = 2 ^ 64 - x.toNat := by
      rw [BitVec.toNat_sub]; simp; omega_using [hx]
    rw [hn, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    obtain h2 : (2 ^ 64 - x.toNat) / 2 ^ 63 ≤ 1 := by omega_using [hx]
    rcases Nat.lt_or_ge x.toNat (2 ^ 63) with h3 | h3
    · rw [Nat.div_eq_of_lt h3, show (2 ^ 64 - x.toNat) / 2 ^ 63 = 1 by omega_using [hx, h3]]; rfl
    · rw [show x.toNat / 2 ^ 63 = 1 by omega_using [h3]]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h2 with e | e <;> rw [e] <;> rfl

theorem bad_zero_iff {m : Mem} {b : Addr} : (m.readW (b + BitVec.ofNat 64 BAD) 64 = 0) ↔ bad m b = 0 := by
  unfold bad
  exact ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [h]; rfl)⟩

section
variable {b : Addr}

theorem vFinish_ok {s : State} (hc : VCtx b s) {Q : Point} (hS : SlotsOk s.mem b RQ (ptV Q Q)) :
    WP isa (.block vFinish) s fun t =>
      t.gpr .r3 = BitVec.ofNat 64 (if bad s.mem b = 0 ∧ Q.X = 0 ∧ Q.Y = Q.Z then 1 else 0) := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hA := X448.PPC64LE.ACC_eq
  have hY : Y = 896 := rfl
  obtain hdo : Region.Disjoint ⟨b, 4096⟩ ⟨b + BitVec.ofNat 64 OUT, 56⟩ :=
    (Offset.disjoint_base b (d := OUT) (n := 56) (k := 4096) (by omega_using [o2]) (by omega_using [o2])).symm
  unfold vFinish
  simp only [outZero, copy, List.append_assoc, List.cons_append]
  -- `X`.
  refine WP.append (freeze_ok hc.ctx hc.r3 (fun k hk => by rw [Offset.add_add]; exact hc.inW (by omega_using [o2, hk])) hdo)
    fun s1 ⟨_, hr1, hf1, hw1⟩ => ?_
  obtain hc1 : VCtx b s1 := hc.of_rest hr1 (by decide) (by decide)
  refine WP.append (outOr_ok hc1) fun s2 ⟨hr2, hm2, hv2⟩ => ?_
  obtain hc2 : VCtx b s2 := hc1.of_rest hr2 (by decide) (by decide)
  refine WP.append (orBad_ok hc2 (r := .r10) (by decide)) fun s3 ⟨hr3, hf3, hb3⟩ => ?_
  obtain hc3 : VCtx b s3 := hc2.of_rest hr3 (by decide) (by decide)
  obtain hS3 := SlotsOk.lo (m := s1.mem) (m' := s3.mem) (by rw [← hm2]; exact hf3) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact disj_hi (by omega_using [o3]) (by omega_using [o3])) (slots_freeze hf1 hdo hS (by decide))
    (by decide)
  -- `Y - Z`.
  refine WP.append (subS (o := TA) (x := RY) (y := RZ) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc3.ctx hS3)
    fun s4 ⟨hr4, hf4, hS4⟩ => ?_
  obtain hc4 : VCtx b s4 := hc3.of_rest hr4 (by decide) (by decide)
  refine wp_li (by decide) fun s5 u5 => ?_
  obtain hc5 : VCtx b s5 := hc4.of_rest (u5.rest (ws := [.r11]) (by decide)) (by decide) (by decide)
  have hS5 := hS4
  rw [← u5.mem] at hS5
  refine WP.append (selG (o := X2) (q := TA) (r := TA) (sw := 0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc5.ctx (by decide) (by rw [u5.gpr]; rfl) hS5 (hS5 TA (by decide)) (hS5 TA (by decide)))
    fun s6 ⟨hr6, hf6, hS6⟩ => ?_
  obtain hc6 : VCtx b s6 := hc5.of_rest hr6 (by decide) (by decide)
  refine WP.append (freeze_ok hc6.ctx hc6.r3 (fun k hk => by rw [Offset.add_add]; exact hc6.inW (by omega_using [o2, hk])) hdo)
    fun s7 ⟨_, hr7, hf7, hw7⟩ => ?_
  obtain hc7 : VCtx b s7 := hc6.of_rest hr7 (by decide) (by decide)
  refine WP.append (outOr_ok hc7) fun s8 ⟨hr8, hm8, hv8⟩ => ?_
  obtain hc8 : VCtx b s8 := hc7.of_rest hr8 (by decide) (by decide)
  refine WP.append (orBad_ok hc8 (r := .r10) (by decide)) fun s9 ⟨hr9, hf9, hb9⟩ => ?_
  obtain hc9 : VCtx b s9 := hc8.of_rest hr9 (by decide) (by decide)
  -- The result.
  refine wp_ldd (a := b + BitVec.ofNat 64 BAD) (by decide) (by decide) (by rw [hc9.ctx.r6]) (hc9.inR (by omega_using [o3]))
    fun t1 v1 => wp_li (by decide) fun t2 v2 => wp_sub fun t3 v3 => ?_
  refine wp_or fun t4 v4 => wp_lsr (by decide) fun t5 v5 => wp_li (by decide) fun t6 v6 => wp_sub fun t7 v7 => ?_
  refine WP.block_nil ?_
  -- `BAD` along the way.
  obtain rB : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
      (∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 BAD, 8⟩ r) → bad m' b = bad m b := fun hf hd => by
    unfold bad; rw [hf.readW (Region.contains_self _ (64 / 8)) hd (by decide)]
  obtain dYO : ∀ r ∈ [(⟨b + BitVec.ofNat 64 Y, 56⟩ : Region), ⟨b + BitVec.ofNat 64 OUT, 56⟩],
      Region.Disjoint ⟨b + BitVec.ofNat 64 BAD, 8⟩ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_using [o3]) (by omega_arith)
  obtain dFA : ∀ r ∈ [FA b], Region.Disjoint ⟨b + BitVec.ofNat 64 BAD, 8⟩ r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by omega_using [o1, o3]) (by omega_using [o3])
  obtain b1 : bad s1.mem b = bad s.mem b := rB hf1 dYO
  obtain b8 : bad s8.mem b = bad s3.mem b := by
    rw [bad, hm8, ← bad, rB hf7 dYO, rB hf6 dFA, bad, u5.mem, ← bad, rB hf4 dFA]
  obtain e9 : bad s9.mem b = bad s.mem b |||
      orw (fun k => wd s1.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 |||
      orw (fun k => wd s7.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 := by
    rw [hb9, b8, hb3, hv8, hv2, bad, hm2, ← bad, b1]
  -- The two elements.
  obtain hX : FS s.mem b X2 = Q.X := by
    rw [hS X2 (by decide)]; simp only [ptV, RX, X2, ↓reduceIte]
  obtain hYZ : FS s6.mem b X2 = Q.Y - Q.Z := by
    rw [hS6 X2 (by decide)]
    simp only [upd, ptV, pick, X25519.PPC64LE.sel, TA, RX, RY, RZ, X2, Z2, Nat.reduceEqDiff, ↓reduceIte]
  obtain i1 : orw (fun k => wd s1.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 = 0 ↔ Q.X = 0 := by
    rw [orw_eq_zero, ← val32_eq_zero, ← fs_zero hw1, hX]
  obtain i2 : orw (fun k => wd s7.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 = 0 ↔ Q.Y = Q.Z := by
    rw [orw_eq_zero, ← val32_eq_zero, ← fs_zero hw7, hYZ, fin_sub_eq_zero]
  -- The result.
  obtain ev : t3.gpr .r9 = s9.mem.readW (b + BitVec.ofNat 64 BAD) 64 := by
    rw [v3.other _ (by decide), v2.other _ (by decide), v1.gpr]
  obtain e8 : t3.gpr .r8 = 0 - s9.mem.readW (b + BitVec.ofNat 64 BAD) 64 := by
    rw [v3.gpr, v2.gpr, v2.other _ (by decide), v1.gpr]; rfl
  obtain hz : (t5.gpr .r9).toNat = if s9.mem.readW (b + BitVec.ofNat 64 BAD) 64 = 0 then 0 else 1 := by
    rw [v5.gpr, v4.gpr, ev, e8, top_nz]
  rw [v7.gpr, v6.gpr, v6.other _ (by decide)]
  obtain hc' : (bad s9.mem b = 0) ↔ (bad s.mem b = 0 ∧ Q.X = 0 ∧ Q.Y = Q.Z) := by
    rw [e9, Nat.or_eq_zero_iff, Nat.or_eq_zero_iff, i1, i2, and_assoc]
  apply BitVec.eq_of_toNat_eq
  by_cases h0 : bad s9.mem b = 0
  · rw [ite_eq_left (hc'.mp h0), ite_eq_left (bad_zero_iff.mpr h0)] at *
    rw [BitVec.toNat_sub, hz]; rfl
  · rw [ite_eq_right (fun h => h0 (hc'.mpr h)), ite_eq_right (fun h => h0 (bad_zero_iff.mp h))] at *
    rw [BitVec.toNat_sub, hz]; rfl

end

end VG.Proof.Ed448.PPC64LE

end

end

/-! ### `Ed448.PPC64LE.VSetup`, which only this module used -/

section

/-!
# Ed448's verification on PPC64LE: the setup

`vSetup` copies the inputs into the working space (`copyB_ok`), points `r3`
at `OUT`, clears `BAD`, and writes `d`, `B` and 1 (`vSetup_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame
open VG.Spec.X448 (P Fe)

section
variable {b : Addr}

/-- After `k` bytes of a copy from `src` to `o`. -/
structure CopyInv (b src : Addr) (o : Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.r7] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 o, k⟩] s0.mem s.mem
  bytes : ∀ i < k, s.mem (b + BitVec.ofNat 64 (o + i)) = s0.mem (src + BitVec.ofNat 64 i)

theorem copyB_ok {s0 : State} (hc : Ctx b s0) {rs : Reg} (hrs : rs ≠ .r0 ∧ rs ≠ .r7 ∧ rs ≠ .r6) {src : Addr}
    (h : s0.gpr rs = src) {n o : Nat} (hin : (⟨src, n⟩ : Region) ∈ s0.rd ++ s0.wr)
    (hd : Region.Disjoint ⟨src, n⟩ ⟨b + BitVec.ofNat 64 o, n⟩) (ho : o + n ≤ 4096) (hn : n < 2 ^ 15) :
    WP isa (.block (copyBytes rs o n)) s0 (CopyInv b src o s0 n) := by
  obtain ⟨h0, h7, h6⟩ := hrs
  refine wp_range_flatMap (M := isa) (CopyInv b src o s0) (fun k s hk h' => ?_) n (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  obtain hcs : Ctx b s := hc.of_rest h'.rest (by decide)
  refine wp_lbz (a := src + BitVec.ofNat 64 k) h0 (by omega_arith) (by rw [h'.rest.gpr _ (by simpa using h7), h])
    (by rw [h'.rest.rd, h'.rest.wr]; exact in_base hin (by omega_arith) (by omega_arith)) fun s1 u1 => ?_
  refine wp_stb (a := b + BitVec.ofNat 64 (o + k)) (by decide) (by omega_arith)
    (by rw [u1.other _ (by decide), h'.rest.gpr _ (by decide), hc.r6])
    (by rw [u1.wr, h'.rest.wr]; exact hc.inW (by omega_arith)) fun s2 u2 => WP.block_nil ?_
  obtain hm2 : s2.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + k)) ((s1.gpr .r7).setWidth 8) := by rw [u2.mem, u1.mem]
  obtain hsrc : s.mem (src + BitVec.ofNat 64 k) = s0.mem (src + BitVec.ofNat 64 k) :=
    h'.frame _ fun r hr hcon => by
      rw [List.mem_singleton.mp hr] at hcon
      exact hd _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) (Region.sub_prefix (by omega_arith) _ hcon)
  refine ⟨h'.rest.trans ((u1.rest (by decide)).trans (u2.rest _)), ?_, fun i hi => ?_⟩
  · rw [hm2]
    exact (h'.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_arith)⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_arith) (by omega_arith))
  · rw [hm2, VG.WriteBytes.writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [X448.PPC64LE.iteF (Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith))]; exact h'.bytes i hi
    · rw [X448.PPC64LE.iteT rfl, u1.gpr, ← hsrc]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      have := (s.mem (src + BitVec.ofNat 64 i)).isLt
      omega_arith

/-- The bytes of a region apart from a frame's regions stay. -/
theorem bytes_keep {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n < 2 ^ 64) :
    Spec.Ed448.bytesAt m' p n = Spec.Ed448.bytesAt m p n := by
  simp only [Spec.Ed448.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  obtain hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => hd r hr _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) hc

theorem bytes_copy {m m0 : Mem} {src : Addr} {o n : Nat}
    (h : ∀ i < n, m (b + BitVec.ofNat 64 (o + i)) = m0 (src + BitVec.ofNat 64 i)) :
    Spec.Ed448.bytesAt m (b + BitVec.ofNat 64 o) n = Spec.Ed448.bytesAt m0 src n := by
  simp only [Spec.Ed448.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  rw [Offset.add_add]; exact h i (List.mem_range.mp hi)

/-- The precondition, by register: `pk` in `r3`, the signature in `r4`, the
challenge in `r5` and `scratch` in `r6`. -/
structure VPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r3, 57⟩, ⟨s.gpr .r4, 114⟩, ⟨s.gpr .r5, 57⟩]
  wr : s.wr = [⟨s.gpr .r6, 8192⟩]
  pk_ws : (⟨s.gpr .r3, 57⟩ : Region).Disjoint ⟨s.gpr .r6, 8192⟩
  sig_ws : (⟨s.gpr .r4, 114⟩ : Region).Disjoint ⟨s.gpr .r6, 8192⟩
  ch_ws : (⟨s.gpr .r5, 57⟩ : Region).Disjoint ⟨s.gpr .r6, 8192⟩

/-- The regions the setup writes after the copy of `pk`. -/
abbrev setW (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 SG, 114⟩, ⟨b + BitVec.ofNat 64 CH, 57⟩, ⟨b + BitVec.ofNat 64 BAD, 8⟩,
    ⟨b + BitVec.ofNat 64 DK, 56⟩, ⟨b + BitVec.ofNat 64 ONE, 56⟩]

/-- `vSetup` but its first three instructions, which keep the return address and `r14`. -/
theorem vCopy_ok {s : State} (hp : VPre s) :
    WP isa (.block (copyBytes .r3 PK 57 ++ copyBytes .r4 SG 114 ++ copyBytes .r5 CH 57 ++
      ([.addi .r3 .r6 OUT, .li .r7 0, .store .d .r7 .r6 BAD] : List Instr) ++
      constField DK Spec.Ed448.d.val ++ constField ONE 1)) s fun t => VCtx (s.gpr .r6) t ∧ Rest [.r3, .r7] s t ∧
      Frame [⟨s.gpr .r6, 8192⟩] s.mem t.mem ∧
      Frame (⟨s.gpr .r6 + BitVec.ofNat 64 PK, 57⟩ :: setW (s.gpr .r6)) s.mem t.mem ∧
      Spec.Ed448.bytesAt t.mem (s.gpr .r6 + BitVec.ofNat 64 PK) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .r3) 57 ∧
      Spec.Ed448.bytesAt t.mem (s.gpr .r6 + BitVec.ofNat 64 SG) 114 = Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114 ∧
      Spec.Ed448.bytesAt t.mem (s.gpr .r6 + BitVec.ofNat 64 CH) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .r5) 57 ∧
      bad t.mem (s.gpr .r6) = 0 ∧ FS t.mem (s.gpr .r6) DK = Spec.Ed448.d ∧
      FS t.mem (s.gpr .r6) ONE = 1 := by
  obtain ⟨b, hb⟩ : ∃ b, b = s.gpr .r6 := ⟨_, rfl⟩
  rw [← hb]
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hPK : PK = 3288 := rfl
  have hSG : SG = 3345 := rfl
  have hCH : CH = 3459 := rfl
  have hDK : DK = 336 := rfl
  have hON : ONE = 3232 := rfl
  obtain hws : (⟨b, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr, hb]; simp
  obtain hc : Ctx b s := ⟨hb.symm, ⟨8192, by decide, hws⟩⟩
  obtain sub8 : ∀ {o n : Nat}, o + n ≤ 8192 → Region.Sub ⟨b + BitVec.ofNat 64 o, n⟩ ⟨b, 8192⟩ :=
    fun h => Offset.sub_base _ h
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- The copies.
  refine WP.append (copyB_ok hc (rs := .r3) (by decide) rfl (n := 57) (o := PK) (by rw [hp.rd]; simp)
    (hp.pk_ws.sub_right (by rw [← hb]; exact sub8 (by omega_arith))) (by omega_arith) (by decide)) fun s1 h1 => ?_
  obtain hc1 : Ctx b s1 := hc.of_rest h1.rest (by decide)
  refine WP.append (copyB_ok hc1 (rs := .r4) (by decide) (by rw [h1.rest.gpr _ (by decide)]) (n := 114) (o := SG)
    (by rw [h1.rest.rd, h1.rest.wr, hp.rd]; simp)
    (hp.sig_ws.sub_right (by rw [← hb]; exact sub8 (by omega_arith))) (by omega_arith) (by decide)) fun s2 h2 => ?_
  obtain hc2 : Ctx b s2 := hc1.of_rest h2.rest (by decide)
  refine WP.append (copyB_ok hc2 (rs := .r5) (by decide)
    (by rw [h2.rest.gpr _ (by decide), h1.rest.gpr _ (by decide)]) (n := 57) (o := CH)
    (by rw [h2.rest.rd, h2.rest.wr, h1.rest.rd, h1.rest.wr, hp.rd]; simp)
    (hp.ch_ws.sub_right (by rw [← hb]; exact sub8 (by omega_arith))) (by omega_arith) (by decide)) fun s3 h3 => ?_
  obtain hc3 : Ctx b s3 := hc2.of_rest h3.rest (by decide)
  -- `r3`, `BAD` and the constants.
  refine wp_addi (by decide) (by decide) fun s4 u4 => wp_li (by decide) fun s5 u5 => ?_
  obtain hr5 : Rest [.r3, .r7] s3 s5 := (u4.rest (by decide)).trans (u5.rest (by decide))
  obtain hc5 : Ctx b s5 := hc3.of_rest hr5 (by decide)
  refine wp_stdd (a := b + BitVec.ofNat 64 BAD) (by decide) (by decide) (by rw [hc5.r6])
    (by rw [hr5.wr, h3.rest.wr, h2.rest.wr, h1.rest.wr]; exact in_base hws (by omega_arith) (by omega_arith)) fun s6 u6 => ?_
  obtain hc6 : Ctx b s6 := hc5.of_rest (u6.rest []) (by decide)
  obtain hm6 : s6.mem = s3.mem.writeW (b + BitVec.ofNat 64 BAD) (BitVec.ofNat 64 0) := by
    rw [u6.mem, u5.gpr, u5.mem, u4.mem]
  refine WP.append (constField_ok hc6 (o := DK) (by decide) (fe_lt _)) fun s7 ⟨r7, f7, v7⟩ => ?_
  obtain hc7 := hc6.of_rest r7 (by decide)
  refine WP.mono (constField_ok hc7 (o := ONE) (by decide) (v := 1) (by decide)) fun t ⟨rt, ft, vt⟩ => ?_
  -- The frames.
  obtain fB : Frame [⟨b + BitVec.ofNat 64 BAD, 8⟩] s3.mem s6.mem := by
    rw [hm6]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ (64 / 8))
  let L3 : List Region := (setW b).drop 2
  let L2 : List Region := (setW b).drop 1
  obtain F3 : Frame L3 s3.mem t.mem := by
    refine (fB.mono (by simp [L3])).trans ((f7.mono (by simp [L3])).trans (ft.mono (by simp [L3])))
  obtain F2 : Frame L2 s2.mem t.mem :=
    (h3.frame.mono (by simp [L2])).trans (F3.mono fun r hr => by
      simp only [L3, L2, List.drop, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp [h])
  obtain F1 : Frame (setW b) s1.mem t.mem :=
    (h2.frame.mono (by simp)).trans (F2.mono fun r hr => by
      simp only [L2, List.drop, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h <;> simp [h])
  obtain sw : ∀ r ∈ setW b, Region.Sub r ⟨b, 8192⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact sub8 (by omega_arith)
  obtain hrt : Rest [.r3, .r7] s t := (h1.rest.mono (by decide)).trans ((h2.rest.mono (by decide)).trans
    ((h3.rest.mono (by decide)).trans (hr5.trans ((u6.rest _).trans ((r7.mono (by decide)).trans
      (rt.mono (by decide)))))))
  -- The values.
  refine ⟨⟨hc7.of_rest rt (by decide), by rw [hrt.wr]; exact hws, ?_⟩, hrt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rt.gpr _ (by decide), r7.gpr _ (by decide), u6.gpr,
      u5.other _ (by decide), u4.gpr, hc3.r6]
  · refine (h1.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact sub8 (by omega_arith)⟩).trans (F1.sub fun r hr => ⟨_, List.mem_singleton_self _, sw r hr⟩)
  · exact (h1.frame.mono (by simp)).trans (F1.mono fun r hr => List.mem_cons_of_mem _ hr)
  · rw [bytes_keep F1 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
      (by decide), bytes_copy h1.bytes]
  · rw [bytes_keep F2 (fun r hr => by
      simp only [L2, List.drop, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
      (by decide), bytes_copy h2.bytes,
      bytes_keep h1.frame (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hp.sig_ws.sub_right (by rw [← hb]; exact sub8 (by omega_arith))) (by decide)]
  · rw [bytes_keep F3 (fun r hr => by
      simp only [L3, List.drop, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
      (by decide), bytes_copy h3.bytes,
      bytes_keep h2.frame (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hp.ch_ws.sub_right (by rw [← hb]; exact sub8 (by omega_arith))) (by decide),
      bytes_keep h1.frame (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hp.ch_ws.sub_right (by rw [← hb]; exact sub8 (by omega_arith))) (by decide)]
  · have f6t : Frame (L3.drop 1) s6.mem t.mem := by
      refine (f7.mono (by simp [L3])).trans (ft.mono (by simp [L3]))
    unfold bad
    rw [f6t.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
        simp only [L3, List.drop, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      hm6, Mem.readW_writeW_self64]
    rfl
  · rw [FS, slot_keep ft (by omega_arith) (by omega_arith) (by omega_arith), v7, VG.Proof.X448.toFe_self]
  · rw [FS, vt, VG.Proof.X448.toFe_one]

end

end VG.Proof.Ed448.PPC64LE

end

end

/-!
# Ed448's verification equation on PPC64LE: the whole function

`vg_ed448_verify_equation` returns 1 exactly when `verifyEquation` holds
(`verifyEquation_correct`), given that `recoverX` is `recoverRef`
(`RecoverOk`, proven in `Proof/Ed448/Facts.lean` and passed in by the
registration): with `-A` and `-R` decoded, `S` checked, the digits of `S`
and `k` recoded and the two tables built, the joint loop leaves `Q`
representing `[S]B + [k](-A)` (`joint_ok`); `[4](Q + (-R))` is the neutral
point exactly when `[4]Q = [4]R`, the equation (`neutral_eq`). The return
address, `r14` and `r15`–`r31`, kept at `VLRS`, `VR14S` and `VNV`, which nothing
else writes, are loaded back.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Impl.X448.PPC64LE (ACC BITS nvR slotsOf stdsAt ldsAt)
open VG.PPC64LE.Spill (Saved saveMem_saved saveMem_frame_base)
open VG.Spec.X448 (P Fe)
open VG.Spec.Ed448 (Point)
open VG.Proof.Ed448 (Rep baseAff dZ)
open VG.Impl.Ed448.WnafWide (digitAt residual)
open VG.Proof.Ed448.PPC64LE.Comb (ptOf)

/-! ## The equation -/

theorem pointEqual_identity (q : Point) :
    Spec.Ed448.pointEqual q Spec.Ed448.identity = (decide (q.X = 0) && decide (q.Y = q.Z)) := by
  simp only [Spec.Ed448.pointEqual, Spec.Ed448.identity, Fin.mul_one, Fin.zero_mul, Fin.one_mul]
  rfl

/-- `[4](Q + (-R))` is neutral exactly when the equation holds, for `Q = [S]B + [k](-A)`. -/
theorem neutral_eq {pk sig ch : List Byte} (hl : pk.length = 57) (hs : sig.length = 114) (hc : ch.length = 57)
    {a r : Point} (ha : Spec.Ed448.decodePoint pk = some a) (hr : Spec.Ed448.decodePoint (sig.take 57) = some r)
    {Q : Point} (hQ : Rep Q (Spec.Ed448.decodeLE (sig.drop 57) • baseAff +
      Spec.Ed448.decodeLE ch • (-Proof.Ed448.toAffine a))) :
    Spec.Ed448.verifyEquation pk sig ch =
      (decide (Spec.Ed448.decodeLE (sig.drop 57) < Spec.Ed448.L) &&
        Spec.Ed448.pointEqual (Proof.Ed448.double (Proof.Ed448.double
          (Spec.Ed448.pointAdd Q (Proof.Ed448.negPoint r)))) Spec.Ed448.identity) := by
  obtain hR := Proof.Ed448.rep_toAffine (Proof.Ed448.decodePoint_valid hr)
  rw [Proof.Ed448.verifyEquation_some hl hs hc ha hr hQ hR]
  refine congrArg (decide (Spec.Ed448.decodeLE (sig.drop 57) < Spec.Ed448.L) && ·) ?_
  generalize Spec.Ed448.decodeLE (sig.drop 57) • baseAff + Spec.Ed448.decodeLE ch • (-Proof.Ed448.toAffine a) = x at hQ
  obtain h1 := Proof.Ed448.double_rep (Proof.Ed448.double_rep hQ)
  obtain h2 := Proof.Ed448.double_rep (Proof.Ed448.double_rep hR)
  obtain h3 := Proof.Ed448.double_rep (Proof.Ed448.double_rep (Proof.Ed448.pointAdd_rep hQ hR.neg))
  rw [Bool.eq_iff_iff, Proof.Ed448.pointEqual_rep h1 h2, Proof.Ed448.pointEqual_rep h3 Proof.Ed448.identity_rep,
    Proof.Ed448.four_smul, Proof.Ed448.four_smul, Proof.Ed448.four_smul, smul_add, smul_neg, add_neg_eq_zero]

/-! ## The digits -/

theorem residual_tail {k : Nat} (hk : k < Impl.Ed448.WnafWide.scalarLimit) :
    ∀ n, 464 ≤ n → residual false k n = 0
  | n, h => by
    induction n with
    | zero => omega
    | succ n ih =>
      rcases Nat.lt_or_ge n 464 with h' | h'
      · have e : n = 463 := by omega_using [h, h']
        subst e
        exact residual_464 hk
      · show Impl.Ed448.WnafWide.next false (residual false k n) = 0
        rw [ih h']; rfl

theorem digit_tail {k n : Nat} (hk : k < Impl.Ed448.WnafWide.scalarLimit) (hn : 464 ≤ n) : digitAt false k n = 0 := by
  unfold digitAt; rw [residual_tail hk n hn]; rfl

theorem bit_tail {k i : Nat} (hk : k < Impl.Ed448.WnafWide.scalarLimit) (hi : 456 ≤ i) :
    Proof.Ed448.WnafWide.bit k i = 0 := by
  unfold Proof.Ed448.WnafWide.bit; rw [Proof.Ed448.WnafWide.tail_quotient hk hi]

/-- The bits written by `bitsOf`. -/
theorem tbSet_bit {S K : Nat} (hS : S < Impl.Ed448.WnafWide.scalarLimit) (hK : K < Impl.Ed448.WnafWide.scalarLimit)
    (h : Nat) : tbSet 1 K (tbSet 0 S fun _ => 0) h =
      if h % 4 = 0 then Proof.Ed448.WnafWide.bit S (h / 4) else if h % 4 = 1 then Proof.Ed448.WnafWide.bit K (h / 4)
      else 0 := by
  unfold tbSet
  by_cases h0 : h % 4 = 0
  · rw [ite_eq_right (by omega_using [h0]), ite_eq_left h0]
    by_cases hi : h / 4 < 456
    · rw [ite_eq_left ⟨h0, hi⟩, Proof.Ed448.WnafWide.bit_shift]
    · rw [ite_eq_right (fun c => hi c.2), bit_tail hS (by omega_using [hi])]
  · rw [ite_eq_right h0]
    by_cases h1 : h % 4 = 1
    · rw [ite_eq_left h1]
      by_cases hi : h / 4 < 456
      · rw [ite_eq_left ⟨h1, hi⟩, Proof.Ed448.WnafWide.bit_shift]
      · rw [ite_eq_right (fun c => hi c.2), ite_eq_right (by omega_using [h0]), bit_tail hK (by omega_using [hi])]
    · rw [ite_eq_right h1, ite_eq_right (by omega_using [h1]), ite_eq_right (by omega_using [h0])]

theorem dig_eq {S K : Nat} (hS : S < Impl.Ed448.WnafWide.scalarLimit) (hK : K < Impl.Ed448.WnafWide.scalarLimit)
    (h : Nat) : recCur 1 K (recCur 0 S (tbSet 1 K (tbSet 0 S fun _ => 0)) 464) 464 h = digV S K h := by
  unfold recCur digV
  rw [tbSet_bit hS hK]
  rcases (by omega_using [] : h % 4 = 0 ∨ h % 4 = 1 ∨ h % 4 = 2 ∨ h % 4 = 3) with e | e | e | e <;>
    simp only [e, Nat.reduceEqDiff, false_and, ite_false, ite_true, true_and, Nat.reduceAdd]
  · by_cases hn : h / 4 < 464
    · rw [ite_eq_left hn]
    · rw [ite_eq_right hn, digit_tail hS (by omega_using [hn])]; rfl
  · by_cases hn : h / 4 < 464
    · rw [ite_eq_left hn]
    · rw [ite_eq_right hn, digit_tail hK (by omega_using [hn])]; rfl

section
variable {b : Addr}

/-! ## Frames -/

/-- An element whose slot is apart from a frame's regions stays. -/
theorem fs_disj {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {q : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 q, 56⟩ r) :
    FS m' b q = FS m b q := fsD hf hd

theorem disj_decW {d n xo yo : Nat} (h1 : 1064 ≤ d) (h2 : d + n ≤ 3520 ∨ 3529 ≤ d ∧ d + n ≤ 4096)
    (hxo : d + n ≤ xo ∨ xo + 56 ≤ d) (hyo : d + n ≤ yo ∨ yo + 56 ≤ d) (hx : xo + 56 ≤ 4096)
    (hy : yo + 56 ≤ 4096) :
    ∀ r ∈ decW b xo yo, Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  intro r hr
  simp only [decW, yW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  all_goals exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem disj_FAB {d n : Nat} (h1 : 1064 ≤ d) (h2 : d + n ≤ 8192) (h3 : d + n ≤ 3520 ∨ 3528 ≤ d) :
    ∀ r ∈ [FA b, ⟨b + BitVec.ofNat 64 BAD, 8⟩], Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem disj_one {d n e k : Nat} (h1 : d + n ≤ e ∨ e + k ≤ d) (h2 : d + n ≤ 8192) (h3 : e + k ≤ 8192) :
    ∀ r ∈ [(⟨b + BitVec.ofNat 64 e, k⟩ : Region)], Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ h1 (by omega_using [h2]) (by omega_using [h3])

theorem disj_FA {d n : Nat} (h1 : 1064 ≤ d) (h2 : d + n ≤ 8192) :
    ∀ r ∈ [FA b], Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint_base _ (by unfold ACC; omega_arith) (by omega_arith)

theorem disj_FAK {d n : Nat} (h1 : 1064 ≤ d) (h2 : d + n ≤ 4160) :
    ∀ r ∈ [FA b, KR b], Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base _ (by unfold ACC; omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (by unfold KT; omega_using [h2]) (by omega_using [h2]) (by unfold KT; omega_using [])

theorem bytes_take (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).take 57 = Spec.Ed448.bytesAt m p 57 := by
  rw [show (114 : Nat) = 57 + 57 from rfl, Proof.Ed448.bytesAt_eq, Proof.X25519.bytesAt_add,
    List.take_left' (by simp [Spec.X25519.bytesAt])]; rfl

theorem bytes_drop (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).drop 57 = Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  rw [show (114 : Nat) = 57 + 57 from rfl, Proof.Ed448.bytesAt_eq, Proof.X25519.bytesAt_add,
    List.drop_left' (by simp [Spec.X25519.bytesAt])]; rfl

theorem keyOk_BT {a : VG.Proof.EdwardsLaw.EPoint dZ} {m m' : Mem}
    (hf : Frame [⟨b + BitVec.ofNat 64 BT, 896⟩] m m') (h : KeyOk b a m) : KeyOk b a m' := fun i hi => by
  have hK : KT = 4160 := rfl
  have hB : BT = 5504 := rfl
  rw [kpt_keep hf fun o ho r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rw [List.mem_singleton.mp hr]
    rcases ho with rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega_using [hi, hK, hB]) (by omega_using [hi, hK]) (by omega_using [hB])]
  exact h i hi

theorem limit_of {bs : List Byte} (h : bs.length = 57) :
    Spec.Ed448.decodeLE bs < Impl.Ed448.WnafWide.scalarLimit := by
  have := Proof.Ed448.decodeLE_below h
  unfold Impl.Ed448.WnafWide.scalarLimit Impl.Ed448.WnafWide.pow2
  exact this

theorem bad_keep {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 BAD, 8⟩ r) : bad m' b = bad m b := by
  unfold bad
  rw [hf.readW (Region.contains_self _ (64 / 8)) hd (by decide)]

/-- A doubleword apart from a frame's regions stays. -/
theorem dw_disj {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {o : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 o, 8⟩ r) :
    m'.readW (b + BitVec.ofNat 64 o) 64 = m.readW (b + BitVec.ofNat 64 o) 64 :=
  hf.readW (Region.contains_self _ (64 / 8)) hd (by decide)

/-! ## The setup -/

theorem vSetup_ok {s : State} (hp : VPre s) :
    WP isa (.block vSetup) s fun t => VCtx (s.gpr .r6) t ∧ t.sp = s.sp ∧
      Spec.Ed448.bytesAt t.mem (s.gpr .r6 + BitVec.ofNat 64 PK) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .r3) 57 ∧
      Spec.Ed448.bytesAt t.mem (s.gpr .r6 + BitVec.ofNat 64 SG) 114 = Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114 ∧
      Spec.Ed448.bytesAt t.mem (s.gpr .r6 + BitVec.ofNat 64 CH) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .r5) 57 ∧
      bad t.mem (s.gpr .r6) = 0 ∧ FS t.mem (s.gpr .r6) DK = Spec.Ed448.d ∧ FS t.mem (s.gpr .r6) ONE = 1 ∧
      t.mem.readW (s.gpr .r6 + BitVec.ofNat 64 VLRS) 64 = s.lr ∧
      t.mem.readW (s.gpr .r6 + BitVec.ofNat 64 VR14S) 64 = s.gpr .r14 ∧
      ∀ i < 17, t.mem.readW (s.gpr .r6 + BitVec.ofNat 64 (VNV + 8 * i)) 64 = s.gpr (nvR i) := by
  obtain ⟨b, hb⟩ : ∃ b, b = s.gpr .r6 := ⟨_, rfl⟩
  rw [← hb]
  have hL : VLRS = 3536 := rfl
  have hR : VR14S = 3544 := rfl
  have hV : VNV = 3552 := rfl
  obtain hws : (⟨b, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr, hb]; simp
  obtain hc : Ctx b s := ⟨hb.symm, ⟨8192, by decide, hws⟩⟩
  rw [show vSetup = .mflr .r7 :: .store .d .r7 .r6 VLRS :: .store .d .r14 .r6 VR14S ::
      (stdsAt VNV (slotsOf nvR 17) ++ (copyBytes .r3 PK 57 ++ copyBytes .r4 SG 114 ++ copyBytes .r5 CH 57 ++
        [.addi .r3 .r6 OUT, .li .r7 0, .store .d .r7 .r6 BAD] ++
        constField DK Spec.Ed448.d.val ++ constField ONE 1)) by
      simp only [vSetup, List.cons_append, List.nil_append, List.append_assoc]]
  refine wp_mflr fun s1 u1 => ?_
  obtain hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.r7]) (by decide)) (by decide)
  refine Comb.wp_std (by decide) ⟨by omega_using [hL], by omega_using [hL]⟩ (by rw [hc1.r6]) (hc1.inW (by omega_using [hL])) fun s2 u2 => ?_
  obtain hc2 : Ctx b s2 := hc1.of_rest (u2.rest []) (by decide)
  refine Comb.wp_std (by decide) ⟨by omega_using [hR], by omega_using [hR]⟩ (by rw [hc2.r6]) (hc2.inW (by omega_using [hR])) fun s3 u3 => ?_
  obtain hr3 : Rest [.r7] s s3 := (u1.rest (by decide)).trans ((u2.rest _).trans (u3.rest _))
  obtain hm3 : s3.mem = (s.mem.writeW (b + BitVec.ofNat 64 VLRS) s.lr).writeW (b + BitVec.ofNat 64 VR14S)
      (s.gpr .r14) := by
    rw [u3.mem, u2.gpr, u2.mem, u1.gpr, u1.other Reg.r14 (by decide), u1.mem]
  obtain g : ∀ r, r ≠ Reg.r7 → s3.gpr r = s.gpr r := fun r h => hr3.gpr r (by simpa using h)
  obtain hp3 : VPre s3 := ⟨by rw [hr3.rd, g .r3 (by decide), g .r4 (by decide), g .r5 (by decide), hp.rd],
    by rw [hr3.wr, g .r6 (by decide), hp.wr], by rw [g .r3 (by decide), g .r6 (by decide)]; exact hp.pk_ws,
    by rw [g .r4 (by decide), g .r6 (by decide)]; exact hp.sig_ws,
    by rw [g .r5 (by decide), g .r6 (by decide)]; exact hp.ch_ws⟩
  -- `r15`–`r31` saved at `VNV`.
  obtain hc3 : Ctx b s3 := hc2.of_rest (u3.rest []) (by decide)
  refine stdsAt_ok (l := slotsOf nvR 17) (by decide) (slotsOf_fit (by decide) (by decide)) hc3
    fun s3' g' rd' wr' sp' mem' => ?_
  obtain hfS : Frame [⟨b + BitVec.ofNat 64 VNV, 136⟩] s3.mem s3'.mem := by
    rw [mem']; exact saveMem_frame_base (fun p hp => by obtain ⟨i, hi, rfl⟩ := slotsOf_mem hp; omega)
      (by decide) _ _ _
  obtain hsv : Saved (b + BitVec.ofNat 64 VNV) s3.gpr (slotsOf nvR 17) s3'.mem := by
    rw [mem']; exact saveMem_saved (by decide) _ _ _
  obtain hp3' : VPre s3' := ⟨by rw [rd', g']; exact hp3.rd, by rw [wr', g']; exact hp3.wr,
    by rw [g']; exact hp3.pk_ws, by rw [g']; exact hp3.sig_ws, by rw [g']; exact hp3.ch_ws⟩
  refine WP.mono (vCopy_ok hp3') fun t ⟨hct, hrt, _, hf2, e1, e2, e3, hbad, hd, hone⟩ => ?_
  rw [g'] at hct hf2 e1 e2 e3 hbad hd hone
  rw [g .r6 (by decide), ← hb] at hct hf2 e1 e2 e3 hbad hd hone
  rw [g .r3 (by decide)] at e1
  rw [g .r4 (by decide)] at e2
  rw [g .r5 (by decide)] at e3
  obtain fw0 : Frame [⟨b + BitVec.ofNat 64 VLRS, 16⟩] s.mem s3.mem := by
    rw [hm3]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [hL]))).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega_using [hL, hR]) (by omega_using [hL, hR]) (by omega_using [hL]))
  obtain fw : Frame [⟨b + BitVec.ofNat 64 VLRS, 152⟩] s.mem s3'.mem :=
    (fw0.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub b (by omega_using []) (by omega_using [])⟩).trans
    (hfS.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub b (by omega_using [hL, hV]) (by omega_using [hL, hV])⟩)
  obtain sub16 : Region.Sub ⟨b + BitVec.ofNat 64 VLRS, 152⟩ ⟨s.gpr .r6, 8192⟩ := by
    rw [← hb]; exact Offset.sub_base _ (by omega_using [hL])
  obtain kb : ∀ {p : Addr} {n : Nat}, Region.Disjoint ⟨p, n⟩ ⟨s.gpr .r6, 8192⟩ → n < 2 ^ 64 →
      Spec.Ed448.bytesAt s3'.mem p n = Spec.Ed448.bytesAt s.mem p n := fun h hn =>
    bytes_keep fw (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.sub_right sub16) hn
  obtain keepS : ∀ {o : Nat}, o + 8 ≤ VNV →
      s3'.mem.readW (b + BitVec.ofNat 64 o) 64 = s3.mem.readW (b + BitVec.ofNat 64 o) 64 := fun ho =>
    dw_disj hfS fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint b (.inl ho) (by omega_using [hV, ho]) (by omega_using [hV])
  obtain dS : ∀ {o : Nat}, 3536 ≤ o → o + 8 ≤ 3688 →
      ∀ r ∈ (⟨b + BitVec.ofNat 64 PK, 57⟩ :: setW b), Region.Disjoint ⟨b + BitVec.ofNat 64 o, 8⟩ r := by
    intro o h1 h2 r hr
    have hPK : PK = 3288 := rfl
    have hSG : SG = 3345 := rfl
    have hCH : CH = 3459 := rfl
    have hDK : DK = 336 := rfl
    have hON : ONE = 3232 := rfl
    obtain ⟨o1, o2, o3, o4⟩ := offs
    simp only [setW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  obtain hn7 : ∀ i < 17, nvR i ≠ .r7 := by decide
  refine ⟨hct, by rw [hrt.sp, sp', hr3.sp], by rw [e1, kb hp.pk_ws (by decide)], by rw [e2, kb hp.sig_ws (by decide)],
    by rw [e3, kb hp.ch_ws (by decide)], hbad, hd, hone, ?_, ?_, fun i hi => ?_⟩
  · rw [dw_disj hf2 (dS (by omega_using [hL]) (by omega_using [hL])), keepS (by omega_using [hL, hV]), hm3,
      Mem.readW_writeW_sep (Offset.sep _ (by omega_using [hL, hR]) (by omega_using [hL]) (by omega_using [hR])) (by decide), Mem.readW_writeW_self64]
  · rw [dw_disj hf2 (dS (by omega_using [hR]) (by omega_using [hR])), keepS (by omega_using [hR, hV]), hm3, Mem.readW_writeW_self64]
  · have h := hsv (nvR i, 8 * i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    rw [Offset.add_add] at h
    rw [dw_disj hf2 (dS (by omega_using [hV]) (by omega_using [hV, hi])), h, g _ (hn7 i hi)]

/-! ## Before the joint loop -/

/-- What the code before the joint loop leaves, for the inputs of `s`. -/
def PreOk (s u : State) : Prop :=
  VCtx (s.gpr .r6) u ∧ u.sp = s.sp ∧
    JFix (s.gpr .r6) (Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114).drop 57))
      (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .r5) 57)) u.mem ∧
    FS u.mem (s.gpr .r6) DK = Spec.Ed448.d ∧
    (bad u.mem (s.gpr .r6) = 0 ↔
      (Spec.Ed448.decodePoint ((Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114).take 57)).isSome ∧
      (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .r3) 57)).isSome ∧
      Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114).drop 57) < Spec.Ed448.L) ∧
    (∀ a, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .r3) 57) = some a →
      KeyOk (s.gpr .r6) (-Proof.Ed448.toAffine a) u.mem) ∧
    (∀ r, Spec.Ed448.decodePoint ((Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114).take 57) = some r →
      FS u.mem (s.gpr .r6) NRX = 0 - r.X ∧ FS u.mem (s.gpr .r6) NRY = r.Y ∧ r.Z = 1) ∧
    u.mem.readW (s.gpr .r6 + BitVec.ofNat 64 VLRS) 64 = s.lr ∧
    u.mem.readW (s.gpr .r6 + BitVec.ofNat 64 VR14S) 64 = s.gpr .r14 ∧
    ∀ i < 17, u.mem.readW (s.gpr .r6 + BitVec.ofNat 64 (VNV + 8 * i)) 64 = s.gpr (nvR i)

theorem pre_ok (hR : Proof.Ed448.RecoverOk) {s : State} (hp : VPre s) : WP isa vPrefix s (PreOk s) := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hTB : TB = 1064 := rfl
  have hKT : KT = 4160 := rfl
  have hBT : BT = 5504 := rfl
  have hSG : SG = 3345 := rfl
  have hPK : PK = 3288 := rfl
  have hCH : CH = 3459 := rfl
  have hNAX : NAX = 3008 := rfl
  have hNAY : NAY = 3064 := rfl
  have hNRX : NRX = 3120 := rfl
  have hNRY : NRY = 3176 := rfl
  have hONE : ONE = 3232 := rfl
  have hDK : DK = 336 := rfl
  have hL : VLRS = 3536 := rfl
  have hR14 : VR14S = 3544 := rfl
  have hV : VNV = 3552 := rfl
  unfold PreOk
  generalize hb : s.gpr .r6 = b
  unfold vPrefix
  refine WP.seq (WP.mono (vSetup_ok hp) fun s1 ⟨hc1, sp1, ePK, eSG, eCH, hb1, hd1, hone, lr1, r141, nv1⟩ => ?_)
  rw [hb] at hc1 ePK eSG eCH hb1 hd1 hone lr1 r141 nv1
  refine WP.seq (WP.mono (decode_ok hR hc1 (p := SG) (by decide) (by decide) (xo := NRX) (yo := NRY)
    ⟨by decide, by decide, by decide, by decide, by decide⟩ hd1) fun s2 ⟨hc2, hr2, hf2, hd2, hb2, hv2⟩ => ?_)
  refine WP.seq (WP.mono (decode_ok hR hc2 (p := PK) (by decide) (by decide) (xo := NAX) (yo := NAY)
    ⟨by decide, by decide, by decide, by decide, by decide⟩ hd2) fun s3 ⟨hc3, hr3, hf3, hd3, hb3, hv3⟩ => ?_)
  refine WP.seq (WP.mono (checkS_ok hc3) fun s4 ⟨hc4, hr4, hf4, hk4, hb4⟩ => ?_)
  refine WP.seq (WP.mono (bitsZero_ok hc4) fun s5 ⟨hc5, hr5, hf5, ht5⟩ => ?_)
  refine WP.seq (WP.mono (bitsOf_ok hc5 (src := SG + 57) (e := 0) (by decide) (by decide) (by decide) ht5)
    fun s6 ⟨hc6, hr6, hf6, ht6⟩ => ?_)
  refine WP.seq (WP.mono (bitsOf_ok hc6 (src := CH) (e := 1) (by decide) (by decide) (by decide) ht6)
    fun s7 ⟨hc7, hr7, hf7, ht7⟩ => ?_)
  -- What the digits' phases keep: everything outside `TB`.
  obtain dTB : ∀ {d n : Nat}, d + n ≤ 1064 ∨ 2936 ≤ d → d + n ≤ 8192 →
      ∀ r ∈ [(⟨b + BitVec.ofNat 64 TB, 1872⟩ : Region)], Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r :=
    fun h h' => disj_one (by omega_using [hTB, h]) h' (by omega_using [hTB])
  -- The inputs, as the phases read them.
  obtain kA : Spec.Ed448.bytesAt s2.mem (b + BitVec.ofNat 64 PK) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .r3) 57 := by
    rw [bytes_keep hf2 (disj_decW (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide)
      (by decide)) (by decide), ePK]
  obtain kR : Spec.Ed448.bytesAt s1.mem (b + BitVec.ofNat 64 SG) 57 =
      (Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114).take 57 := by rw [← eSG, bytes_take]
  obtain sS : ∀ {m : Mem}, Spec.Ed448.bytesAt m (b + BitVec.ofNat 64 SG + BitVec.ofNat 64 57) 57 =
      Spec.Ed448.bytesAt m (b + BitVec.ofNat 64 (SG + 57)) 57 := by intro m; rw [Offset.add_add]
  obtain kS3 : Spec.Ed448.bytesAt s3.mem (b + BitVec.ofNat 64 (SG + 57)) 57 =
      (Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114).drop 57 := by
    rw [bytes_keep hf3 (disj_decW (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide)
        (by decide)) (by decide),
      bytes_keep hf2 (disj_decW (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide)
        (by decide)) (by decide), ← eSG, bytes_drop, sS]
  obtain kS5 : Spec.Ed448.bytesAt s5.mem (b + BitVec.ofNat 64 (SG + 57)) 57 =
      (Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114).drop 57 := by
    rw [bytes_keep hf5 (dTB (by omega_using [hSG]) (by omega_using [hSG])) (by decide),
      bytes_keep hf4 (disj_FAB (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), kS3]
  obtain kK : Spec.Ed448.bytesAt s6.mem (b + BitVec.ofNat 64 CH) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .r5) 57 := by
    rw [bytes_keep hf6 (dTB (by omega_using [hCH]) (by omega_using [hCH])) (by decide), bytes_keep hf5 (dTB (by omega_using [hCH]) (by omega_using [hCH])) (by decide),
      bytes_keep hf4 (disj_FAB (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      bytes_keep hf3 (disj_decW (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide) (by decide))
        (by decide),
      bytes_keep hf2 (disj_decW (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide) (by decide))
        (by decide), eCH]
  rw [kS5] at ht6 ht7
  rw [kK] at ht7
  obtain hl4 : (Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114).length = 114 := by simp [Spec.Ed448.bytesAt]
  obtain hl5 : (Spec.Ed448.bytesAt s.mem (s.gpr .r5) 57).length = 57 := by simp [Spec.Ed448.bytesAt]
  obtain hSl := limit_of (bs := (Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114).drop 57) (by rw [List.length_drop, hl4])
  obtain hKl := limit_of hl5
  generalize hS : Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114).drop 57) = S at *
  generalize hK : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .r5) 57) = K at *
  refine WP.seq (WP.mono (recode_ok hc7 (e := 0) (k := S) (by decide) (fun i _ => by
      rw [tbSet_bit hSl hKl, ite_eq_left (by omega_using []), show (4 * i + 0) / 4 = i by omega_using []]) ht7)
    fun s8 ⟨hc8, hr8, hf8, ht8⟩ => ?_)
  refine WP.seq (WP.mono (recode_ok hc8 (e := 1) (k := K) (by decide) (fun i _ => by
      rw [recCur, ite_eq_right (by omega_using []), tbSet_bit hSl hKl, ite_eq_right (by omega_using []), ite_eq_left (by omega_using []),
        show (4 * i + 1) / 4 = i by omega_using []]) ht8)
    fun s9 ⟨hc9, hr9, hf9, ht9⟩ => ?_)
  obtain hdig : TbIs b s9.mem (digV S K) := fun h hh => by rw [ht9 h hh, dig_eq hSl hKl]
  -- The slots above the digits, from the checks to the digits.
  obtain k49 : ∀ {q : Nat}, 2936 ≤ q → q + 56 ≤ 3520 → FS s9.mem b q = FS s4.mem b q := fun h1 h2 => by
    rw [fs_disj hf9 (dTB (by omega_using [h1]) (by omega_using [h2])), fs_disj hf8 (dTB (by omega_using [h1]) (by omega_using [h2])),
      fs_disj hf7 (dTB (by omega_using [h1]) (by omega_using [h2])), fs_disj hf6 (dTB (by omega_using [h1]) (by omega_using [h2])),
      fs_disj hf5 (dTB (by omega_using [h1]) (by omega_using [h2]))]
  obtain k34 : ∀ {q : Nat}, 1064 ≤ q → q + 56 ≤ 3520 → FS s4.mem b q = FS s3.mem b q := fun h1 h2 =>
    fs_disj hf4 (disj_FAB (by omega_using [h1]) (by omega_using [h2]) (by omega_using [h2]))
  obtain kFS1 : ∀ {q : Nat}, 1064 ≤ q → q + 56 ≤ 3008 ∨ 3232 ≤ q → q + 56 ≤ 3520 → FS s3.mem b q = FS s1.mem b q :=
    fun h1 h2 h3 => by
      rw [fs_disj hf3 (disj_decW (by omega_arith) (by omega_arith) (by unfold NAX; omega_arith)
          (by unfold NAY; omega_arith) (by decide) (by decide)),
        fs_disj hf2 (disj_decW (by omega_arith) (by omega_arith) (by unfold NRX; omega_arith)
          (by unfold NRY; omega_arith) (by decide) (by decide))]
  obtain kR3 : ∀ {q : Nat}, q = NRX ∨ q = NRY → FS s3.mem b q = FS s2.mem b q := fun h => by
    rcases h with rfl | rfl <;>
      exact fs_disj hf3 (disj_decW (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  -- The saved doublewords, from the setup to the digits.
  obtain w19 : ∀ {o : Nat}, 3536 ≤ o → o + 8 ≤ 3688 →
      s9.mem.readW (b + BitVec.ofNat 64 o) 64 = s1.mem.readW (b + BitVec.ofNat 64 o) 64 := fun h1 h2 => by
    rw [dw_disj hf9 (dTB (by omega_using [h1]) (by omega_using [h2])), dw_disj hf8 (dTB (by omega_using [h1]) (by omega_using [h2])),
      dw_disj hf7 (dTB (by omega_using [h1]) (by omega_using [h2])), dw_disj hf6 (dTB (by omega_using [h1]) (by omega_using [h2])),
      dw_disj hf5 (dTB (by omega_using [h1]) (by omega_using [h2])), dw_disj hf4 (disj_FAB (by omega_using [h1]) (by omega_using [h2]) (by omega_using [h1])),
      dw_disj hf3 (disj_decW (by omega_using [h1]) (by omega_using [h1, h2]) (by unfold NAX; omega_using [h1]) (by unfold NAY; omega_using [h1]) (by decide)
        (by decide)),
      dw_disj hf2 (disj_decW (by omega_using [h1]) (by omega_using [h1, h2]) (by unfold NRX; omega_using [h1]) (by unfold NRY; omega_using [h1]) (by decide)
        (by decide))]
  -- `-A` and `d` before the tables.
  let A' : Point := ⟨FS s9.mem b NAX, FS s9.mem b NAY, FS s9.mem b ONE⟩
  obtain hpA : Pt s9.mem b NAX NAY ONE A' := ⟨rfl, rfl, rfl⟩
  obtain hd9 : FS s9.mem b DK = Spec.Ed448.d := by
    rw [fs_disj hf9 (dTB (by omega_using [hDK]) (by omega_using [hDK])), fs_disj hf8 (dTB (by omega_using [hDK]) (by omega_using [hDK])),
      fs_disj hf7 (dTB (by omega_using [hDK]) (by omega_using [hDK])), fs_disj hf6 (dTB (by omega_using [hDK]) (by omega_using [hDK])),
      fs_disj hf5 (dTB (by omega_using [hDK]) (by omega_using [hDK])), hk4, hd3]
  refine WP.seq (WP.mono (keyTable_ok hc9 hpA hd9) fun s10 hK10 => ?_)
  have ⟨hc10, hr10, hf10, _, _, _, hdk10, _⟩ := hK10
  refine WP.mono (baseTable_ok hc10) fun s11 ⟨hc11, hr11, hf11, hB11⟩ => ?_
  obtain dBT : ∀ {d n : Nat}, d + n ≤ 5504 → ∀ r ∈ [(⟨b + BitVec.ofNat 64 BT, 896⟩ : Region)],
      Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := fun h => disj_one (.inl (by omega_using [hBT, h])) (by omega_using [h]) (by omega_using [hBT])
  obtain hfx : JFix b S K s11.mem := ⟨fun h hh => by
      obtain e1 := hf11 (b + BitVec.ofNat 64 (TB + h)) fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact fun hc => (dBT (d := TB + h) (n := 1) (by omega_using [hTB, hh]) _ (List.mem_singleton_self _)) _
          (Region.contains_self _ _) hc
      obtain e2 := hf10 (b + BitVec.ofNat 64 (TB + h)) fun r hr => by
        exact fun hc => (disj_FAK (d := TB + h) (n := 1) (by omega_using [hTB]) (by omega_using [hTB, hh]) r hr) _ (Region.contains_self _ _) hc
      rw [e1, e2]; exact hdig h hh, hB11⟩
  obtain hd11 : FS s11.mem b DK = Spec.Ed448.d := by
    rw [fs_disj hf11 (dBT (by omega_using [hDK]))]; exact hdk10
  obtain k911 : ∀ {q : Nat}, 1064 ≤ q → q + 56 ≤ 4160 → FS s11.mem b q = FS s9.mem b q := fun h1 h2 => by
    rw [fs_disj hf11 (dBT (by omega_using [h2])), fs_disj hf10 (disj_FAK (by omega_using [h1]) (by omega_using [h2]))]
  obtain w911 : ∀ {o : Nat}, 3536 ≤ o → o + 8 ≤ 3688 →
      s11.mem.readW (b + BitVec.ofNat 64 o) 64 = s9.mem.readW (b + BitVec.ofNat 64 o) 64 := fun h1 h2 => by
    rw [dw_disj hf11 (dBT (by omega_using [h2])), dw_disj hf10 (disj_FAK (by omega_using [h1]) (by omega_using [h2]))]
  refine ⟨hc11, ?_, hfx, hd11, ?_, fun a hA => ?_, fun r hRr => ?_, ?_, ?_, fun i hi => ?_⟩
  · rw [hr11.sp, hr10.sp, hr9.sp, hr8.sp, hr7.sp, hr6.sp, hr5.sp, hr4.sp, hr3.sp, hr2.sp, sp1]
  · rw [bad_keep hf11 (dBT (by omega_using [o3])), bad_keep hf10 (disj_FAK (by omega_using [o3]) (by omega_using [o3])),
      bad_keep hf9 (dTB (by omega_using [o3]) (by omega_using [o3])), bad_keep hf8 (dTB (by omega_using [o3]) (by omega_using [o3])),
      bad_keep hf7 (dTB (by omega_using [o3]) (by omega_using [o3])), bad_keep hf6 (dTB (by omega_using [o3]) (by omega_using [o3])),
      bad_keep hf5 (dTB (by omega_using [o3]) (by omega_using [o3])), hb4, hb3, hb2, kA, kR, kS3, hS]
    simp only [hb1, true_and]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
  · obtain ⟨ax, ay, az⟩ := hv3 a (by rw [kA]; exact hA)
    obtain eA : A' = Proof.Ed448.negPoint a := by
      show (⟨FS s9.mem b NAX, FS s9.mem b NAY, FS s9.mem b ONE⟩ : Point) = ⟨0 - a.X, a.Y, a.Z⟩
      rw [k49 (by decide) (by decide), k49 (by decide) (by decide), k49 (by decide) (by decide),
        k34 (by decide) (by decide), k34 (by decide) (by decide), k34 (by decide) (by decide), ax, ay,
        kFS1 (by decide) (by decide) (by decide), hone, az]
    obtain hArep : Rep A' (-Proof.Ed448.toAffine a) := by
      rw [eA]; exact (Proof.Ed448.rep_toAffine (Proof.Ed448.decodePoint_valid hA)).neg
    exact keyOk_BT hf11 (keyOk_of hArep hK10)
  · obtain ⟨rx, ry, rz⟩ := hv2 r (by rw [kR]; exact hRr)
    rw [k911 (by decide) (by decide), k911 (by decide) (by decide), k49 (by decide) (by decide),
      k49 (by decide) (by decide), k34 (by decide) (by decide), k34 (by decide) (by decide),
      kR3 (.inl rfl), kR3 (.inr rfl), rx, ry, rz]
    exact ⟨rfl, rfl, rfl⟩
  · rw [w911 (by omega_using [hL]) (by omega_using [hL]), w19 (by omega_using [hL]) (by omega_using [hL]), lr1]
  · rw [w911 (by omega_using [hR14]) (by omega_using [hR14]), w19 (by omega_using [hR14]) (by omega_using [hR14]), r141]
  · rw [w911 (by omega_using [hV]) (by omega_using [hV, hi]), w19 (by omega_using [hV]) (by omega_using [hV, hi]), nv1 i hi]

/-! ## The whole function -/

theorem verifyEquation_correct (hR : Proof.Ed448.RecoverOk) {s : State} (hp : VPre s) :
    WP isa verifyEquation s fun t => ((t.gpr .r3).setWidth 32 =
      if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .r3) 57)
        (Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .r5) 57) then 1 else 0) ∧
      t.lr = s.lr ∧ t.gpr .r14 = s.gpr .r14 ∧ ∀ i < 17, t.gpr (nvR i) = s.gpr (nvR i) := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hL : VLRS = 3536 := rfl
  have hR14 : VR14S = 3544 := rfl
  have hV : VNV = 3552 := rfl
  obtain hl3 : (Spec.Ed448.bytesAt s.mem (s.gpr .r3) 57).length = 57 := by simp [Spec.Ed448.bytesAt]
  obtain hl4 : (Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114).length = 114 := by simp [Spec.Ed448.bytesAt]
  obtain hl5 : (Spec.Ed448.bytesAt s.mem (s.gpr .r5) 57).length = 57 := by simp [Spec.Ed448.bytesAt]
  obtain hSl := limit_of (bs := (Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114).drop 57) (by rw [List.length_drop, hl4])
  obtain hKl := limit_of hl5
  unfold verifyEquation
  refine WP.seq (WP.mono (pre_ok hR hp) fun u ⟨hcu, _, hfx, hdu, hbad, hkey, hnr, lru, r14u, nvu⟩ => ?_)
  generalize hb : s.gpr .r6 = b at hcu hfx hdu hbad hkey hnr lru r14u nvu
  generalize hS : Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114).drop 57) = S at *
  generalize hK : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .r5) 57) = K at *
  refine WP.seq (WP.mono (joint_ok hSl hKl hcu hfx hdu) fun s12 ⟨sL, _, fL, _, ⟨C12, d12, rep12⟩⟩ => ?_)
  refine WP.seq (WP.mono (addNegR_ok C12 d12) fun s13 ⟨C13, sl13⟩ => ?_)
  have hc13 : VCtx b s13 := C13.ctx
  obtain w13 : ∀ {o : Nat}, 3536 ≤ o → o + 8 ≤ 3688 →
      s13.mem.readW (b + BitVec.ofNat 64 o) 64 = u.mem.readW (b + BitVec.ofNat 64 o) 64 := fun h1 h2 => by
    rw [dw_keep_fa C13.frame (by unfold ACC; omega_using [h1]) (by omega_using [h2]), dw_keep_fa fL (by unfold ACC; omega_using [h1]) (by omega_using [h2])]
  simp only [vRestore, List.cons_append, List.nil_append]
  refine Comb.wp_ld (by decide) ⟨by omega_using [hL], by omega_using [hL]⟩ (by rw [hc13.ctx.r6]) (hc13.ctx.inR (by omega_using [hL]))
    fun s14 u14 => wp_mtlr fun s15 g15 m15 rd15 wr15 sp15 l15 =>
    wp_ldL (by decide) ⟨by omega_using [hR14], by omega_using [hR14]⟩ (by rw [g15, u14.other _ (by decide), hc13.ctx.r6])
      (by rw [rd15, wr15, u14.rd, u14.wr]; exact hc13.ctx.inR (by omega_using [hR14])) fun s16 u16 l16 => ?_
  obtain hr16 : Rest [.r7, .r14] s13 s16 :=
    ⟨fun r hr => by
      rw [u16.other r (by intro h; exact hr (by simp [h])), g15, u14.other r (by intro h; exact hr (by simp [h]))],
      by rw [u16.rd, rd15, u14.rd], by rw [u16.wr, wr15, u14.wr], by rw [u16.sp, sp15, u14.sp]⟩
  obtain hc16 : VCtx b s16 := hc13.of_rest hr16 (by decide) (by decide)
  obtain m16 : s16.mem = s13.mem := by rw [u16.mem, m15, u14.mem]
  obtain lr16 : s16.lr = s.lr := by
    rw [l16, l15, u14.gpr, w13 (by omega_using [hL]) (by omega_using [hL]), lru]
  obtain r14_16 : s16.gpr .r14 = s.gpr .r14 := by
    rw [u16.gpr, m15, u14.mem, w13 (by omega_using [hR14]) (by omega_using [hR14]), r14u]
  -- `r15`–`r31` loaded back.
  refine ldsAt_ok (l := slotsOf nvR 17) (by decide) (slotsOf_fit (by decide) (by decide)) (by decide)
    (by decide) hc16.ctx fun s17 _ r17 m17 l17 v17 => ?_
  obtain hc17 : VCtx b s17 := hc16.of_rest r17 (by decide) (by decide)
  obtain nv17 : ∀ i < 17, s17.gpr (nvR i) = s.gpr (nvR i) := fun i hi => by
    rw [v17 (nvR i, 8 * i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)]
    show s16.mem.readW (b + BitVec.ofNat 64 VNV + BitVec.ofNat 64 (8 * i)) 64 = _
    rw [Offset.add_add, m16, w13 (by omega_using [hV]) (by omega_using [hV, hi]), nvu i hi]
  have sl17 := sl13
  rw [← m16, ← m17] at sl17
  refine WP.mono (wp_keep_lr (wp_keep_nv (vFinish_ok hc17 sl17) (by decide +kernel)
      (by rw [← Code.allInstrs_eq]; decide +kernel)) (by decide +kernel)
    (by rw [← Code.allInstrs_eq]; decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel))
    fun t ⟨⟨ht, nt⟩, lt, rt⟩ => ⟨?_, by rw [lt, l17, lr16], by rw [rt, r17.gpr _ (by decide), r14_16],
      fun i hi => by rw [nt i hi, nv17 i hi]⟩
  rw [ht]
  obtain dF := disj_FA (b := b) (d := BAD) (n := 8) (by omega_using [o3]) (by omega_using [o3])
  obtain hb16 : bad s17.mem b = bad u.mem b := by
    rw [m17, m16, bad_keep C13.frame dF, bad_keep fL dF]
  obtain kU : ∀ {q : Nat}, 1064 ≤ q → q + 56 ≤ 3520 → FS s12.mem b q = FS u.mem b q := fun h1 h2 => by
    rw [fs_hi C12.frame (by unfold ACC; omega_using [h1]) (by omega_using [h2]), fs_hi fL (by unfold ACC; omega_using [h1]) (by omega_using [h2])]
  rw [hb16]
  obtain res : ∀ (c : Prop) [Decidable c] (v : Bool), (c ↔ v = true) →
      (BitVec.ofNat 64 (if c then 1 else 0)).setWidth 32 = if v then 1 else 0 := by
    intro c _ v h
    by_cases hc : c
    · rw [ite_eq_left hc, ite_eq_left (h.mp hc)]; rfl
    · rw [ite_eq_right hc, ite_eq_right (fun hv => hc (h.mpr hv))]; rfl
  refine res _ _ ?_
  cases hA : Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .r3) 57) with
  | none =>
    rw [Proof.Ed448.verifyEquation_none (.inl hA)]
    exact ⟨fun ⟨h, _⟩ => by have := (hbad.mp h).2.1; rw [hA] at this; exact absurd this (by decide),
      fun h => absurd h (by decide)⟩
  | some a =>
    cases hRr : Spec.Ed448.decodePoint ((Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114).take 57) with
    | none =>
      rw [Proof.Ed448.verifyEquation_none (.inr hRr)]
      exact ⟨fun ⟨h, _⟩ => by have := (hbad.mp h).1; rw [hRr] at this; exact absurd this (by decide),
        fun h => absurd h (by decide)⟩
    | some r =>
      obtain hQ := rep12 _ (keyOk_FA fL (hkey a hA))
      simp only [Impl.Ed448.WnafWide.residual, natCast_zsmul] at hQ
      obtain ⟨rx, ry, rz⟩ := hnr r hRr
      obtain eR : (⟨FS s12.mem b NRX, FS s12.mem b NRY, 1⟩ : Point) = Proof.Ed448.negPoint r := by
        show (⟨FS s12.mem b NRX, FS s12.mem b NRY, 1⟩ : Point) = ⟨0 - r.X, r.Y, r.Z⟩
        rw [kU (by decide) (by decide), kU (by decide) (by decide), rx, ry, rz]
      rw [← hS, ← hK] at hQ
      rw [neutral_eq hl3 hl4 hl5 hA hRr hQ, hS, pointEqual_identity, hbad]
      simp only [hA, hRr, Option.isSome_some, true_and, Bool.and_eq_true, decide_eq_true_eq]
      rw [eR]

end

end VG.Proof.Ed448.PPC64LE
