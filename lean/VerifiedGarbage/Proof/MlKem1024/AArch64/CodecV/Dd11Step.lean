module

public import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Dd11
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dd10Step
import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Widths
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdLoop

/-!
# ML-KEM-1024 on AArch64: an iteration of `dd11Body`

Bytes `44 k … 44 k + 43` of the input, in three registers (two loads of 16 bytes, a doubleword and a
word), to coefficients `32 k … 32 k + 31` of the output, a group of 88 bits at a time
(`dd11Group_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
  VG.Proof.MlKem.AArch64.CodecV VG.Proof.MlKem.AArch64.DD VG.Proof.MlKem1024.AArch64
  VG.Proof.MlKem1024.AArch64.CodecV
open VG.Spec.MlKem

/-- The constants of `dd11Body` besides those of `decV`. -/
abbrev K11 (s : State) : Prop := (Lanes (s.v .v18) fun _ => 2 ^ 22 - 1) ∧ (Lanes (s.v .v19) fun _ => 2 ^ 11 - 1) ∧
  ∀ g < 4, s.v (dd11IdxReg g) = idxVec (dd11Idx g)

theorem vbyte_setLane64_0 (x : BitVec 128) (w : BitVec 64) {j : Nat} (hj : j < 8) :
    vbyte (setLane x 64 0 w) j = w.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [setLane, vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    hi, decide_true, Bool.true_and, Nat.mul_zero, Nat.sub_zero, show 8 * j + i < 128 by omega_arith,
    show 8 * j + i < 64 by omega_arith, show ¬ 8 * j + i < 0 by omega_arith]
  simp

theorem vbyte_setLane32_2 (x : BitVec 128) (w : BitVec 32) {j : Nat} (hj : j < 16) :
    vbyte (setLane x 32 2 w) j = if 8 ≤ j ∧ j < 12 then w.extractLsb' (8 * (j - 8)) 8 else vbyte x j := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases h : 8 ≤ j ∧ j < 12
  · rw [ite_eq_left h]
    simp only [setLane, vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
      hi, decide_true, Bool.true_and, show 8 * j + i < 128 by omega_arith, show ¬ 8 * j + i < 32 * 2 by omega_arith,
      show 8 * j + i - 32 * 2 = 8 * (j - 8) + i by omega_arith, show 8 * (j - 8) + i < 32 by omega_arith,
      show 8 * (j - 8) + i < 128 by omega_arith]
    simp
  · rw [ite_eq_right h]
    simp only [setLane, vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
      hi, decide_true, Bool.true_and, show 8 * j + i < 128 by omega_arith]
    by_cases h' : 8 * j + i < 32 * 2
    · simp [h']
    · have : ¬ 8 * j + i - 32 * 2 < 32 := by omega_arith
      simp [h', this, BitVec.getLsbD_of_ge w (8 * j + i - 32 * 2) (by omega_arith)]

/-- The bytes of a group, from its 11 bytes. -/
theorem num11_eq (s₀ : State) (g : Nat) :
    num width11 s₀ g 11 = num11 fun j => byte width11 s₀ (11 * g + j) := by
  rw [num_succ, num_succ, num_succ, num_succ, num_succ, num_succ, num_succ, num_succ, num_succ, num_succ,
    num_succ, num, List.range_zero, List.map_nil, digits_nil]
  simp only [show width11.nb = 11 from rfl, Nat.add_zero, num11]
  omega_arith

/-- Coefficient `32 k + 8 g + m` of the output for `d = 11`. -/
theorem G11 (s₀ : State) {k g m : Nat} (hk : k < 8) (hg : g < 4) (hm : m < 8) :
    DD.G width11 s₀ (32 * k + 8 * g + m) =
      BitVec.ofNat 32 (df 11 (num11 (fun j => byte width11 s₀ (11 * (4 * k + g) + j)) / 2 ^ (11 * m) % 2 ^ 11)) := by
  rw [show 32 * k + 8 * g + m = width11.c * (4 * k + g) + m by simp [width11]; omega_arith,
    G_eq width11_ok s₀ (by simp [width11]; omega_arith) (by simp [width11]; omega_arith), ← num11_eq]
  simp only [show width11.d = 11 from rfl, show width11.nb = 11 from rfl, df]

theorem tableByte_frame {s u : State} (hu : ∀ r, r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v7 → u.v r = s.v r)
    {i : Nat} (hi : i < 48) : tableByte u.v .v4 i = tableByte s.v .v4 i := by
  unfold tableByte
  rcases (show i / 16 = 0 ∨ i / 16 = 1 ∨ i / 16 = 2 by omega_arith) with h | h | h <;> rw [h] <;>
    exact congrArg (fun x => vbyte x _) (hu _ (by decide) (by decide) (by decide) (by decide))

theorem step11 {s₀ : State} (hp : Pre width11 s₀) {k : Nat} (hk : k < 8) {s : State}
    (h : DInv width11 4 K11 s₀ k s) :
    WP isa (.block dd11Body) s fun t =>
      DInv width11 4 K11 s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 8) := by
  have x0 : s.gpr .x0 = bP s₀ + BitVec.ofNat 64 (44 * k) := by
    rw [h.x0, show width11.nb * 4 * k = 44 * k by simp [width11]; try omega_arith]
  have inr : ∀ o n, o + n ≤ 44 → InRegions (s.rd ++ s.wr) (bP s₀ + BitVec.ofNat 64 (44 * k + o)) n := fun o n hon => by
    rw [h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by simp [width11]; omega_arith) (by decide)))
  unfold dd11Body
  simp only [List.cons_append, List.append_assoc]
  refine wp_ldrq (by decide) (by rw [ptr_zero, x0]) (h.in16 width11_ok hp (by simp [width11]; omega_arith))
    fun s1 h1 => ?_
  refine wp_ldrq (a := bP s₀ + BitVec.ofNat 64 (44 * k + 16)) (by decide) (by rw [h1.gpr, x0, ptr_add])
    (by rw [h1.rd, h1.wr]; exact inr 16 16 (by decide)) fun s2 h2 => ?_
  refine wp_scalar (is := [.ldr .x .x9 .x0 32]) (by decide) (wp_ldrx (a := bP s₀ + BitVec.ofNat 64 (44 * k + 32))
    (by decide) (by rw [h2.gpr, h1.gpr, x0, ptr_add]) (by rw [h2.rd, h2.wr, h1.rd, h1.wr]; exact inr 32 8 (by decide))
    fun t o e => wp_nil (Q := fun t => Only [.x9] s2 t ∧ t.gpr .x9 = s2.mem.readW (bP s₀ + BitVec.ofNat 64 (44 * k + 32)) 64)
      ⟨o, e⟩) fun s3 ⟨o3, e3⟩ v3 => ?_
  refine wp_vop rfl fun s4 h4 => ?_
  refine wp_scalar (is := [.ldr .w .x9 .x0 40]) (by decide) (wp_ldrw (a := bP s₀ + BitVec.ofNat 64 (44 * k + 40))
    (by decide) (by rw [h4.gpr, o3.gpr .x0 (by decide), h2.gpr, h1.gpr, x0, ptr_add])
    (by rw [h4.rd, h4.wr, o3.rd, o3.wr, h2.rd, h2.wr, h1.rd, h1.wr]; exact inr 40 4 (by decide))
    fun t o e => wp_nil (Q := fun t => Only [.x9] s4 t ∧
      t.gpr .x9 = (s4.mem.readW (bP s₀ + BitVec.ofNat 64 (44 * k + 40)) 32).setWidth 64) ⟨o, e⟩)
    fun s5 ⟨o5, e5⟩ v5 => ?_
  refine wp_vop rfl fun s6 h6 => ?_
  have m6 : s6.mem = s.mem := by rw [h6.mem, o5.mem, h4.mem, o3.mem, h2.mem, h1.mem]
  -- the 44 bytes, as a table of three registers
  have tab : ∀ i < 44, (tableByte s6.v .v4 i).toNat = byte width11 s₀ (44 * k + i) := fun i hi => by
    unfold tableByte
    rcases (show i / 16 = 0 ∨ i / 16 = 1 ∨ i / 16 = 2 by omega_arith) with q | q | q <;> rw [q]
    · rw [show Nat.repeat VReg.succ 0 VReg.v4 = .v4 from rfl, h6.get .v4 (by decide), v5, h4.get .v4 (by decide),
        v3, h2.get .v4 (by decide), h1.v]
      exact vbyte_input width11_ok hp h.frame (by simp [width11]; omega_arith) (by omega_arith) |>.trans
        (by rw [show i % 16 = i by omega_arith])
    · rw [show Nat.repeat VReg.succ 1 VReg.v4 = .v5 from rfl, h6.get .v5 (by decide), v5, h4.get .v5 (by decide),
        v3, h2.v, h1.mem]
      rw [vbyte_input width11_ok hp h.frame (o := 44 * k + 16) (by simp [width11]; omega_arith) (by omega_arith)]
      congr 1; omega_arith
    · rw [show Nat.repeat VReg.succ 2 VReg.v4 = .v6 from rfl, h6.v, vbyte_setLane32_2 _ _ (by omega_arith)]
      by_cases hb : 8 ≤ i % 16 ∧ i % 16 < 12
      · rw [ite_eq_left hb, e5, h4.mem, o3.mem, h2.mem, h1.mem, readW32_byte _ _ (by omega_arith), ptr_add,
          show 44 * k + 40 + (i % 16 - 8) = 44 * k + i by omega_arith]
        exact hp.byte_eq h.frame (by simp [width11]; omega_arith) (by decide)
      · rw [ite_eq_right hb, v5, h4.v, vbyte_setLane64_0 _ _ (by omega_arith), e3, h2.mem, h1.mem]
        rw [show (s.mem.readW (bP s₀ + BitVec.ofNat 64 (44 * k + 32)) 64) =
          s.mem.read (bP s₀ + BitVec.ofNat 64 (44 * k + 32)) 8 from rfl, Mem.extractLsb'_read _ _ (by omega_arith),
          ptr_add, show 44 * k + 32 + i % 16 = 44 * k + i by omega_arith]
        exact hp.byte_eq h.frame (by simp [width11]; omega_arith) (by decide)
  -- the frame so far
  have g6 : ∀ r, r ≠ .x9 → s6.gpr r = s.gpr r := fun r hr => by
    rw [h6.gpr, o5.gpr r (by simpa using hr), h4.gpr, o3.gpr r (by simpa using hr), h2.gpr, h1.gpr]
  have v6 : ∀ r, r ≠ .v4 → r ≠ .v5 → r ≠ .v6 → s6.v r = s.v r := fun r a b c => by
    rw [h6.get r c, v5, h4.get r c, v3, h2.get r b, h1.get r a]
  have wr6 : s6.wr = s.wr := by rw [h6.wr, o5.wr, h4.wr, o3.wr, h2.wr, h1.wr]
  have x3 : s.gpr .x3 = coeffAddr (fP s₀) (32 * k) := by
    rw [h.x3, show width11.c * 4 * k = 32 * k by simp [width11]; try omega_arith]
  have out : CoeffsUpTo s6.mem (fP s₀) (32 * k) (DD.G width11 s₀) (old s₀) := by
    rw [m6, show 32 * k = width11.c * 4 * k by simp [width11]; try omega_arith]; exact h.out
  -- what the groups keep
  have keep : ∀ u : State, (∀ r, r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v7 → u.v r = s6.v r) →
      DConsts 11 u ∧ (Lanes (u.v .v18) fun _ => 2 ^ 22 - 1) ∧ (Lanes (u.v .v19) fun _ => 2 ^ 11 - 1) ∧
      (∀ g < 4, u.v (dd11IdxReg g) = idxVec (dd11Idx g)) ∧
      ∀ g < 4, ∀ j < 11, (tableByte u.v .v4 (11 * g + j)).toNat = byte width11 s₀ (11 * (4 * k + g) + j) := by
    intro u hu
    have hr : ∀ r, r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v4 → r ≠ .v5 → r ≠ .v6 → r ≠ .v7 → u.v r = s.v r :=
      fun r a b c d e f g' => by rw [hu r a b c g', v6 r d e f]
    have q : ∀ r, r ∉ [VReg.v1, .v2, .v3, .v4, .v5, .v6, .v7] → u.v r = s.v r := fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      obtain ⟨a, b, c, d, e, f, g'⟩ := hr'
      exact hr r a b c d e f g'
    refine ⟨⟨(q .v16 (by decide)).symm ▸ h.cs.q, (q .v17 (by decide)).symm ▸ h.cs.h⟩,
      (q .v18 (by decide)).symm ▸ h.K.1, (q .v19 (by decide)).symm ▸ h.K.2.1,
      fun g hg => ?_, fun g hg j hj => ?_⟩
    · rcases dd11IdxReg_eq hg with e | e | e | e <;> rw [e] <;>
        rw [hr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ← e] <;>
        exact h.K.2.2 g hg
    · rw [tableByte_frame hu (by omega_arith), tab _ (by omega_arith), show 44 * k + (11 * g + j) = 11 * (4 * k + g) + j by omega_arith]
  have hu6 : ∀ r, r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v7 → s6.v r = s6.v r := fun _ _ _ _ _ => rfl
  -- the four groups
  have grp : ∀ (g : Nat) (u : State), g < 4 → (∀ r, r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v7 → u.v r = s6.v r) →
      u.gpr = s6.gpr → u.wr = s.wr → CoeffsUpTo u.mem (fP s₀) (32 * k + 8 * g) (DD.G width11 s₀) (old s₀) →
      Frame [polyRegion (fP s₀)] s₀.mem u.mem → ∀ (is : List Instr) (Q : State → Prop),
      (∀ u', u'.gpr = u.gpr → u'.rd = u.rd → u'.wr = u.wr → u'.sp = u.sp →
        (∀ r, r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v7 → u'.v r = u.v r) →
        CoeffsUpTo u'.mem (fP s₀) (32 * k + 8 * g + 8) (DD.G width11 s₀) (old s₀) →
        Frame [polyRegion (fP s₀)] s₀.mem u'.mem → WP isa (.block is) u' Q) →
      WP isa (.block (dd11Group g ++ is)) u Q := by
    intro g u hg hu gu wu cu fu is Q kk
    obtain ⟨c, l18, l19, idx, tb⟩ := keep u hu
    exact dd11Group_ok hg c l18 l19 (idx g hg) (B := fun j => byte width11 s₀ (11 * (4 * k + g) + j)) (tb g hg)
      (fun i hi => by rw [wu]; exact h.out16 hp hi)
      (by rw [gu, g6 .x3 (by decide), x3, show 32 * g = 4 * (8 * g) by omega_arith, coeffAddr_off]) (by omega_arith) cu fu
      (fun m hm => G11 s₀ hk hg hm) kk
  refine grp 0 s6 (by decide) hu6 rfl wr6 (by rw [show 32 * k + 8 * 0 = 32 * k by omega_arith]; exact out)
    (by rw [m6]; exact h.frame) _ _ fun u1 g1 rd1 wr1 sp1 v1 o1 f1 => ?_
  refine grp 1 u1 (by decide) (fun r a b c d => by rw [v1 r a b c d]) (by rw [g1]) (by rw [wr1, wr6])
    (by rw [show 32 * k + 8 * 1 = 32 * k + 8 * 0 + 8 by omega_arith]; exact o1) f1 _ _
    fun u2 g2 rd2 wr2 sp2 v2 o2 f2 => ?_
  refine grp 2 u2 (by decide) (fun r a b c d => by rw [v2 r a b c d, v1 r a b c d]) (by rw [g2, g1])
    (by rw [wr2, wr1, wr6]) (by rw [show 32 * k + 8 * 2 = 32 * k + 8 * 1 + 8 by omega_arith]; exact o2) f2 _ _
    fun u3 g3 rd3 wr3 sp3 v3' o3' f3 => ?_
  refine grp 3 u3 (by decide) (fun r a b c d => by rw [v3' r a b c d, v2 r a b c d, v1 r a b c d])
    (by rw [g3, g2, g1]) (by rw [wr3, wr2, wr1, wr6])
    (by rw [show 32 * k + 8 * 3 = 32 * k + 8 * 2 + 8 by omega_arith]; exact o3') f3 _ _
    fun u4 g4 rd4 wr4 sp4 v4 o4 f4 => ?_
  have k4 : k < 256 / (width11.c * 4) := by simp [width11]; omega_arith
  have gg : ∀ r, r ≠ .x9 → u4.gpr r = s.gpr r := fun r hr => by rw [g4, g3, g2, g1, g6 r hr]
  refine WP.mono (dtail_ok (w := width11) (Ng := 4) (s₀ := s₀) k4 (by rw [gg .x0 (by decide), h.x0])
    (by rw [gg .x3 (by decide), h.x3]) (by rw [gg .x11 (by decide), h.x11]) (by decide) (by decide))
    fun u ⟨o, uv, u0, u3, u11, uc⟩ => ?_
  obtain ⟨c, l18, l19, idx, -⟩ := keep u4 fun r a b d e => by rw [v4 r a b d e, v3' r a b d e, v2 r a b d e,
    v1 r a b d e]
  refine ⟨⟨by rw [o.rd, rd4, rd3, rd2, rd1, h6.rd, o5.rd, h4.rd, o3.rd, h2.rd, h1.rd, h.rd],
    by rw [o.wr, wr4, wr3, wr2, wr1, wr6, h.wr],
    by rw [o.sp, sp4, sp3, sp2, sp1, h6.sp, o5.sp, h4.sp, o3.sp, h2.sp, h1.sp, h.sp], u0, u3, u11,
    ⟨by rw [uv]; exact c.q, by rw [uv]; exact c.h⟩,
    ⟨by rw [uv]; exact l18, by rw [uv]; exact l19, fun g hg => by rw [uv]; exact idx g hg⟩,
    ?_, by rw [o.mem]; exact f4⟩, by rw [show 256 / (width11.c * 4) = 8 from rfl] at uc; exact uc⟩
  rw [o.mem, show width11.c * 4 * (k + 1) = 32 * k + 8 * 3 + 8 by simp [width11]; omega_arith]
  exact o4

end VG.Proof.MlKem1024.AArch64.DD
