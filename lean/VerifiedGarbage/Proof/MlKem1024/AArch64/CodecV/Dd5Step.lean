module

public import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Dd5
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dd10Step
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Widths
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce10
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdLoop

/-!
# ML-KEM-1024 on AArch64: an iteration of `dd5Body`

Bytes `20 k … 20 k + 19` of the input, as four groups of 40 bits in doublewords (TBL, as for
`d = 10`), to coefficients `32 k … 32 k + 31` of the output.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
  VG.Proof.MlKem.AArch64.CodecV VG.Proof.MlKem.AArch64.DD VG.Proof.MlKem1024.AArch64
  VG.Proof.MlKem1024.AArch64.CodecV
open VG.Spec.MlKem

/-- The constants of `dd5Body` besides those of `decV`. -/
abbrev K5 (s : State) : Prop := (Lanes (s.v .v18) fun _ => 2 ^ 20 - 1) ∧ (Lanes (s.v .v19) fun _ => 2 ^ 10 - 1) ∧
  s.v .v20 = idxVec dd10Idx ∧ s.v .v21 = idxVec dd10IdxHi ∧ (Lanes (s.v .v22) fun _ => 2 ^ 5 - 1)

/-- The bytes of a group, from its five bytes. -/
theorem num5' (s₀ : State) (g : Nat) :
    num width5 s₀ g 5 = byte width5 s₀ (5 * g) + byte width5 s₀ (5 * g + 1) * 2 ^ 8 +
      byte width5 s₀ (5 * g + 2) * 2 ^ 16 + byte width5 s₀ (5 * g + 3) * 2 ^ 24 +
      byte width5 s₀ (5 * g + 4) * 2 ^ 32 := by
  rw [num_succ, num_succ, num_succ, num_succ, num_succ, num, List.range_zero, List.map_nil, digits_nil]
  simp only [show width5.nb = 5 from rfl, Nat.add_zero]
  omega

/-- Coefficient `32 k + m` of the output for `d = 5`. -/
theorem G5 (s₀ : State) {k m : Nat} (hk : k < 8) (hm : m < 32) :
    DD.G width5 s₀ (32 * k + m) = BitVec.ofNat 32 (df 5 (dig5 (fun l => num width5 s₀ (4 * k + l) 5) m)) := by
  rw [show 32 * k + m = width5.c * (4 * k + m / 8) + m % 8 by simp [width5]; omega,
    G_eq width5_ok s₀ (by simp [width5]; omega) (by simp [width5]; omega)]
  simp only [show width5.d = 5 from rfl, show width5.nb = 5 from rfl, df, dig5]

theorem step5 {s₀ : State} (hp : Pre width5 s₀) {k : Nat} (hk : k < 8) {s : State}
    (h : DInv width5 4 K5 s₀ k s) :
    WP isa (.block dd5Body) s fun t =>
      DInv width5 4 K5 s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 8) := by
  have x0 : s.gpr .x0 = bP s₀ + BitVec.ofNat 64 (20 * k) := by
    rw [h.x0, show width5.nb * 4 * k = 20 * k by simp [width5]; try omega]
  unfold dd5Body
  simp only [List.cons_append, List.append_assoc]
  refine wp_ldrq (by decide) (by rw [ptr_zero, x0]) (h.in16 width5_ok hp (by simp [width5]; omega))
    fun s1 h1 => ?_
  have in4 : InRegions (s1.rd ++ s1.wr) (bP s₀ + BitVec.ofNat 64 (20 * k + 16)) 4 := by
    rw [h1.rd, h1.wr, h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by simp [width5]; omega) (by decide)))
  refine wp_scalar (is := [.ldr .w .x9 .x0 16]) (by decide) (wp_ldrw (a := bP s₀ + BitVec.ofNat 64 (20 * k + 16))
    (by decide) (by rw [h1.gpr, x0, ptr_add]) in4 fun t o e =>
      wp_nil (Q := fun t => Only [.x9] s1 t ∧ t.gpr .x9 = (s1.mem.readW (bP s₀ + BitVec.ofNat 64 (20 * k + 16)) 32).setWidth 64)
      ⟨o, e⟩) fun s2 ⟨o2, e2⟩ v2 => ?_
  refine wp_vop rfl fun s3 h3 => wp_vop rfl fun s4 h4 => wp_vop rfl fun s5 h5 => ?_
  -- the 20 bytes, as a table of two registers
  have tab : ∀ i < 20, (if i < 16 then vbyte (s3.v .v4) i else vbyte (s3.v .v5) (i - 16)).toNat =
      byte width5 s₀ (20 * k + i) := fun i hi => by
    by_cases hi' : i < 16
    · rw [ite_eq_left hi', h3.get .v4 (by decide), v2, h1.v]
      exact vbyte_input width5_ok hp h.frame (by simp [width5]; omega) hi'
    · rw [ite_eq_right hi', h3.v, vbyte_setLane0 _ _ (by omega), e2, h1.mem, readW32_byte _ _ (by omega),
        ptr_add, show 20 * k + 16 + (i - 16) = 20 * k + i by omega]
      exact hp.byte_eq h.frame (by simp [width5]; omega) (by decide)
  have k20 : s3.v .v20 = idxVec dd10Idx := by
    rw [h3.get .v20 (by decide), v2, h1.get .v20 (by decide)]; exact h.K.2.2.1
  have k21 : s4.v .v21 = idxVec dd10IdxHi := by
    rw [h4.get .v21 (by decide), h3.get .v21 (by decide), v2, h1.get .v21 (by decide)]; exact h.K.2.2.2.1
  -- the groups
  let Gv : Nat → Nat := fun l => num width5 s₀ (4 * k + l) 5
  have lane (x : BitVec 128) (l : Nat) (gb : Nat)
      (hx : ∀ b < 8, (vbyte x (8 * l + b)).toNat = if b < 5 then byte width5 s₀ (5 * gb + b) else 0) :
      (vdword x l).toNat = num width5 s₀ gb 5 := by
    rw [num5']
    exact dword5 x l (fun b => byte width5 s₀ (5 * gb + b)) hx
  have D6 : DLanes (s5.v .v6) Gv := fun l hl => lane _ l _ fun b hb => by
    rw [h5.get .v6 (by decide), h4.v]
    have hk : (vbyte (s3.v .v20) (8 * l + b)).toNat = dd10Idx.getD (8 * l + b) 255 := by
      rw [k20, toNat_idxVec _ (by decide) (by omega)]
    rw [dd10Idx_eq _ (by omega), show (8 * l + b) % 8 = b by omega, show (8 * l + b) / 8 = l by omega] at hk
    by_cases h5' : b < 5
    · rw [ite_eq_left h5'] at hk ⊢
      rw [vbyte_tbl2 (by omega) hk (by omega), show VReg.v4.succ = .v5 from rfl, tab _ (by omega)]
      congr 1; omega
    · rw [ite_eq_right h5'] at hk ⊢
      rw [vbyte_tbl2_out (by omega) hk (by omega)]; rfl
  have D7 : DLanes (s5.v .v7) fun l => Gv (2 + l) := fun l hl => lane _ l _ fun b hb => by
    rw [h5.v]
    have hk : (vbyte (s4.v .v21) (8 * l + b)).toNat = dd10IdxHi.getD (8 * l + b) 255 := by
      rw [k21, toNat_idxVec _ (by decide) (by omega)]
    rw [dd10IdxHi_eq _ (by omega), show (8 * l + b) % 8 = b by omega, show (8 * l + b) / 8 = l by omega] at hk
    by_cases h5' : b < 5
    · rw [ite_eq_left h5'] at hk ⊢
      rw [vbyte_tbl2 (by omega) hk (by omega), show VReg.v4.succ = .v5 from rfl, h4.get .v4 (by decide),
        h4.get .v5 (by decide), tab _ (by omega)]
      congr 1; omega
    · rw [ite_eq_right h5'] at hk ⊢
      rw [vbyte_tbl2_out (by omega) hk (by omega)]; rfl
  -- the frame so far
  have g5 : ∀ r, r ≠ .x9 → s5.gpr r = s.gpr r := fun r hr => by
    rw [h5.gpr, h4.gpr, h3.gpr, o2.gpr r (by simpa using hr), h1.gpr]
  have v5 : ∀ r, r ≠ .v4 → r ≠ .v5 → r ≠ .v6 → r ≠ .v7 → s5.v r = s.v r := fun r a b c d => by
    rw [h5.get r d, h4.get r c, h3.get r b, v2, h1.get r a]
  have m5 : s5.mem = s.mem := by rw [h5.mem, h4.mem, h3.mem, o2.mem, h1.mem]
  have wr5 : s5.wr = s.wr := by rw [h5.wr, h4.wr, h3.wr, o2.wr, h1.wr]
  have cs5 : DConsts 5 s5 := ⟨by rw [v5 .v16 (by decide) (by decide) (by decide) (by decide)]; exact h.cs.q,
    by rw [v5 .v17 (by decide) (by decide) (by decide) (by decide)]; exact h.cs.h⟩
  have l18 : Lanes (s5.v .v18) fun _ => 2 ^ 20 - 1 := by
    rw [v5 .v18 (by decide) (by decide) (by decide) (by decide)]; exact h.K.1
  have l19 : Lanes (s5.v .v19) fun _ => 2 ^ 10 - 1 := by
    rw [v5 .v19 (by decide) (by decide) (by decide) (by decide)]; exact h.K.2.1
  have l22 : Lanes (s5.v .v22) fun _ => 2 ^ 5 - 1 := by
    rw [v5 .v22 (by decide) (by decide) (by decide) (by decide)]; exact h.K.2.2.2.2
  have x3 : s.gpr .x3 = coeffAddr (fP s₀) (32 * k) := by
    rw [h.x3, show width5.c * 4 * k = 32 * k by simp [width5]; try omega]
  have out : CoeffsUpTo s5.mem (fP s₀) (32 * k) (DD.G width5 s₀) (old s₀) := by
    rw [m5, show 32 * k = width5.c * 4 * k by simp [width5]; try omega]; exact h.out
  refine dd5Half_ok (Or.inl rfl) (o := 0) (by decide) cs5 l18 l19 l22 D6
    (fun i hi => by rw [wr5]; exact h.out16 hp hi) (by rw [g5 .x3 (by decide), x3, ptr_zero]) (by omega) out
    (by rw [m5]; exact h.frame) (fun m hm => G5 s₀ hk (by omega)) fun s6 g6 rd6 wr6 sp6 v6 o6 f6 => ?_
  have v6' : ∀ r : VReg, r ≠ .v6 → r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v4 → r ≠ .v5 → r ≠ .v7 →
      s6.v r = s.v r := fun r a b c d e f g' i => by rw [v6 r a b c d e, v5 r f g' a i]
  refine dd5Half_ok (Or.inr rfl) (o := 64) (by decide)
    ⟨by rw [v6 .v16 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact cs5.q,
     by rw [v6 .v17 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact cs5.h⟩
    (by rw [v6 .v18 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l18)
    (by rw [v6 .v19 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l19)
    (by rw [v6 .v22 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l22)
    (by rw [v6 .v7 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact D7)
    (fun i hi => by rw [wr6, wr5]; exact h.out16 hp hi)
    (by rw [g6, g5 .x3 (by decide), x3]; exact coeffAddr_off _ _ 16) (by omega) o6 f6
    (fun m hm => by
      rw [show 32 * k + 16 + m = 32 * k + (16 + m) by omega, G5 s₀ hk (by omega)]
      simp only [dig5]
      rw [show (16 + m) / 8 = 2 + m / 8 by omega, show (16 + m) % 8 = m % 8 by omega])
    fun s7 g7 rd7 wr7 sp7 v7 o7 f7 => ?_
  have k4 : k < 256 / (width5.c * 4) := by simp [width5]; omega
  have gg : ∀ r, r ≠ .x9 → s7.gpr r = s.gpr r := fun r hr => by rw [g7, g6, g5 r hr]
  refine WP.mono (dtail_ok (w := width5) (Ng := 4) (s₀ := s₀) k4 (by rw [gg .x0 (by decide), h.x0])
    (by rw [gg .x3 (by decide), h.x3]) (by rw [gg .x11 (by decide), h.x11]) (by decide) (by decide))
    fun u ⟨o, uv, u0, u3, u11, uc⟩ => ?_
  have hv : ∀ r, r ∉ [VReg.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7] → u.v r = s.v r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := hr
    rw [uv, v7 r a7 a0 a1 a2 a3, v6' r a6 a0 a1 a2 a3 a4 a5 a7]
  refine ⟨⟨by rw [o.rd, rd7, rd6, h5.rd, h4.rd, h3.rd, o2.rd, h1.rd, h.rd], by rw [o.wr, wr7, wr6, wr5, h.wr],
    by rw [o.sp, sp7, sp6, h5.sp, h4.sp, h3.sp, o2.sp, h1.sp, h.sp], u0, u3, u11,
    ⟨by rw [hv .v16 (by decide)]; exact h.cs.q, by rw [hv .v17 (by decide)]; exact h.cs.h⟩,
    ⟨by rw [hv .v18 (by decide)]; exact h.K.1, by rw [hv .v19 (by decide)]; exact h.K.2.1,
     by rw [hv .v20 (by decide)]; exact h.K.2.2.1, by rw [hv .v21 (by decide)]; exact h.K.2.2.2.1,
     by rw [hv .v22 (by decide)]; exact h.K.2.2.2.2⟩,
    ?_, by rw [o.mem]; exact f7⟩, by rw [show 256 / (width5.c * 4) = 8 from rfl] at uc; exact uc⟩
  rw [o.mem, show width5.c * 4 * (k + 1) = 32 * k + 16 + 16 by simp [width5]; omega]
  exact o7

end VG.Proof.MlKem1024.AArch64.DD
