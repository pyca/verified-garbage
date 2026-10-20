module

public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dd10
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce10
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdLoop
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec

/-!
# ML-KEM on AArch64: an iteration of `dd10Body`

Bytes `20 k … 20 k + 19` of the input, as four groups of 40 bits in doublewords (TBL), to
coefficients `16 k … 16 k + 15` of the output.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.CodecV
open VG.Spec.MlKem

/-- The constants of `dd10Body` besides those of `decV`. -/
abbrev K10 (s : State) : Prop := (Lanes (s.v .v18) fun _ => 2 ^ 20 - 1) ∧ (Lanes (s.v .v19) fun _ => 2 ^ 10 - 1) ∧
  s.v .v20 = idxVec dd10Idx ∧ s.v .v21 = idxVec dd10IdxHi

theorem dd10Idx_eq : ∀ i < 16, dd10Idx.getD i 255 = if i % 8 < 5 then 5 * (i / 8) + i % 8 else 255 := by
  decide
theorem dd10IdxHi_eq : ∀ i < 16, dd10IdxHi.getD i 255 = if i % 8 < 5 then 10 + 5 * (i / 8) + i % 8 else 255 := by
  decide

/-- TBL at an index past the table. -/
theorem vbyte_tbl2_out {s : State} {n m d : VReg} {i : Nat} (hi : i < 16) {k : Nat}
    (hk : (vbyte (s.v m) i).toNat = k) (hk' : 32 ≤ k) :
    vbyte (ofVBytes fun i => if (vbyte (s.v m) i).toNat < 16 * 2 then tableByte s.v n (vbyte (s.v m) i).toNat
      else if false then vbyte (s.v d) i else 0) i = 0 := by
  rw [vbyte_ofVBytes _ hi, hk, ite_eq_right (by omega)]; rfl

/-- A doubleword from its bytes. -/
theorem dword_of_bytes (x : BitVec 128) (l : Nat) :
    (vdword x l).toNat = (vbyte x (8 * l)).toNat + (vbyte x (8 * l + 1)).toNat * 2 ^ 8 +
      (vbyte x (8 * l + 2)).toNat * 2 ^ 16 + (vbyte x (8 * l + 3)).toNat * 2 ^ 24 +
      (vbyte x (8 * l + 4)).toNat * 2 ^ 32 + (vbyte x (8 * l + 5)).toNat * 2 ^ 40 +
      (vbyte x (8 * l + 6)).toNat * 2 ^ 48 + (vbyte x (8 * l + 7)).toNat * 2 ^ 56 := by
  have h0 := toNat_vbyte_dword x (l := l) (b := 0) (by decide)
  have h1 := toNat_vbyte_dword x (l := l) (b := 1) (by decide)
  have h2 := toNat_vbyte_dword x (l := l) (b := 2) (by decide)
  have h3 := toNat_vbyte_dword x (l := l) (b := 3) (by decide)
  have h4 := toNat_vbyte_dword x (l := l) (b := 4) (by decide)
  have h5 := toNat_vbyte_dword x (l := l) (b := 5) (by decide)
  have h6 := toNat_vbyte_dword x (l := l) (b := 6) (by decide)
  have h7 := toNat_vbyte_dword x (l := l) (b := 7) (by decide)
  simp only [Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at h0 h1 h2 h3 h4 h5 h6 h7
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  have := (vdword x l).isLt
  omega

/-- A doubleword whose bytes are five values and three zeros. -/
theorem dword5 (x : BitVec 128) (l : Nat) (F : Nat → Nat)
    (hx : ∀ b < 8, (vbyte x (8 * l + b)).toNat = if b < 5 then F b else 0) :
    (vdword x l).toNat = F 0 + F 1 * 2 ^ 8 + F 2 * 2 ^ 16 + F 3 * 2 ^ 24 + F 4 * 2 ^ 32 := by
  have hx0 := hx 0 (by decide)
  simp only [Nat.add_zero] at hx0
  rw [dword_of_bytes, hx0, hx 1 (by decide), hx 2 (by decide), hx 3 (by decide), hx 4 (by decide),
    hx 5 (by decide), hx 6 (by decide), hx 7 (by decide)]
  rw [ite_eq_left (show 0 < 5 by decide), ite_eq_left (show 1 < 5 by decide), ite_eq_left (show 2 < 5 by decide),
    ite_eq_left (show 3 < 5 by decide), ite_eq_left (show 4 < 5 by decide), ite_eq_right (show ¬ 5 < 5 by decide),
    ite_eq_right (show ¬ 6 < 5 by decide), ite_eq_right (show ¬ 7 < 5 by decide)]
  omega

/-- The bytes of a group, from its five bytes and three zeros. -/
theorem num5 (s₀ : State) (g : Nat) :
    num width10 s₀ g 5 = byte width10 s₀ (5 * g) + byte width10 s₀ (5 * g + 1) * 2 ^ 8 +
      byte width10 s₀ (5 * g + 2) * 2 ^ 16 + byte width10 s₀ (5 * g + 3) * 2 ^ 24 +
      byte width10 s₀ (5 * g + 4) * 2 ^ 32 := by
  rw [num_succ, num_succ, num_succ, num_succ, num_succ, num, List.range_zero, List.map_nil, digits_nil]
  simp only [show width10.nb = 5 from rfl, Nat.add_zero]
  omega

/-- Coefficient `16 k + m` of the output for `d = 10`. -/
theorem G10 (s₀ : State) {k m : Nat} (hk : k < 16) (hm : m < 16) :
    DD.G width10 s₀ (16 * k + m) = BitVec.ofNat 32 (df 10 (dig10 (fun l => num width10 s₀ (4 * k + l) 5) m)) := by
  rw [show 16 * k + m = width10.c * (4 * k + m / 4) + m % 4 by simp [width10]; omega,
    G_eq width10_ok s₀ (by simp [width10]; omega) (by simp [width10]; omega)]
  simp only [show width10.d = 10 from rfl, show width10.nb = 5 from rfl, df, dig10]

theorem vbyte_setLane0 (x : BitVec 128) (w : BitVec 32) {j : Nat} (hj : j < 4) :
    vbyte (setLane x 32 0 w) j = w.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [setLane, vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    hi, decide_true, Bool.true_and, Nat.mul_zero, Nat.sub_zero, show 8 * j + i < 128 by omega,
    show 8 * j + i < 32 by omega, show ¬ 8 * j + i < 0 by omega]
  simp

theorem readW32_byte (m : Mem) (a : Addr) {j : Nat} (hj : j < 4) :
    (((m.readW a 32).setWidth 64).setWidth 32).extractLsb' (8 * j) 8 = m (a + BitVec.ofNat 64 j) := by
  rw [← Mem.extractLsb'_read m a (n := 4) hj]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [Mem.readW, hi, show 8 * j + i < 32 by omega]

theorem step10 {s₀ : State} (hp : Pre width10 s₀) {k : Nat} (hk : k < 16) {s : State}
    (h : DInv width10 4 K10 s₀ k s) :
    WP isa (.block dd10Body) s fun t =>
      DInv width10 4 K10 s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 16) := by
  have x0 : s.gpr .x0 = bP s₀ + BitVec.ofNat 64 (20 * k) := by
    rw [h.x0, show width10.nb * 4 * k = 20 * k by simp [width10]; try omega]
  unfold dd10Body
  simp only [List.cons_append, List.append_assoc]
  refine wp_ldrq (by decide) (by rw [ptr_zero, x0]) (h.in16 width10_ok hp (by simp [width10]; omega))
    fun s1 h1 => ?_
  have in4 : InRegions (s1.rd ++ s1.wr) (bP s₀ + BitVec.ofNat 64 (20 * k + 16)) 4 := by
    rw [h1.rd, h1.wr, h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by simp [width10]; omega) (by decide)))
  refine wp_scalar (is := [.ldr .w .x9 .x0 16]) (by decide) (wp_ldrw (a := bP s₀ + BitVec.ofNat 64 (20 * k + 16))
    (by decide) (by rw [h1.gpr, x0, ptr_add]) in4 fun t o e =>
      wp_nil (Q := fun t => Only [.x9] s1 t ∧ t.gpr .x9 = (s1.mem.readW (bP s₀ + BitVec.ofNat 64 (20 * k + 16)) 32).setWidth 64)
      ⟨o, e⟩) fun s2 ⟨o2, e2⟩ v2 => ?_
  refine wp_vop rfl fun s3 h3 => wp_vop rfl fun s4 h4 => wp_vop rfl fun s5 h5 => ?_
  -- the 20 bytes, as a table of two registers
  have tab : ∀ i < 20, (if i < 16 then vbyte (s3.v .v4) i else vbyte (s3.v .v5) (i - 16)).toNat =
      byte width10 s₀ (20 * k + i) := fun i hi => by
    by_cases hi' : i < 16
    · rw [ite_eq_left hi', h3.get .v4 (by decide), v2, h1.v]
      exact vbyte_input width10_ok hp h.frame (by simp [width10]; omega) hi'
    · rw [ite_eq_right hi', h3.v, vbyte_setLane0 _ _ (by omega), e2, h1.mem, readW32_byte _ _ (by omega),
        ptr_add, show 20 * k + 16 + (i - 16) = 20 * k + i by omega]
      exact hp.byte_eq h.frame (by simp [width10]; omega) (by decide)
  have k20 : s3.v .v20 = idxVec dd10Idx := by
    rw [h3.get .v20 (by decide), v2, h1.get .v20 (by decide)]; exact h.K.2.2.1
  have k21 : s4.v .v21 = idxVec dd10IdxHi := by
    rw [h4.get .v21 (by decide), h3.get .v21 (by decide), v2, h1.get .v21 (by decide)]; exact h.K.2.2.2
  -- the groups
  let Gv : Nat → Nat := fun l => num width10 s₀ (4 * k + l) 5
  have lane (x : BitVec 128) (l : Nat) (gb : Nat)
      (hx : ∀ b < 8, (vbyte x (8 * l + b)).toNat = if b < 5 then byte width10 s₀ (5 * gb + b) else 0) :
      (vdword x l).toNat = num width10 s₀ gb 5 := by
    rw [num5]
    exact dword5 x l (fun b => byte width10 s₀ (5 * gb + b)) hx
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
  have cs5 : DConsts 10 s5 := ⟨by rw [v5 .v16 (by decide) (by decide) (by decide) (by decide)]; exact h.cs.q,
    by rw [v5 .v17 (by decide) (by decide) (by decide) (by decide)]; exact h.cs.h⟩
  have l18 : Lanes (s5.v .v18) fun _ => 2 ^ 20 - 1 := by
    rw [v5 .v18 (by decide) (by decide) (by decide) (by decide)]; exact h.K.1
  have l19 : Lanes (s5.v .v19) fun _ => 2 ^ 10 - 1 := by
    rw [v5 .v19 (by decide) (by decide) (by decide) (by decide)]; exact h.K.2.1
  have x3 : s.gpr .x3 = coeffAddr (fP s₀) (16 * k) := by
    rw [h.x3, show width10.c * 4 * k = 16 * k by simp [width10]; try omega]
  have out : CoeffsUpTo s5.mem (fP s₀) (16 * k) (DD.G width10 s₀) (old s₀) := by
    rw [m5, show 16 * k = width10.c * 4 * k by simp [width10]; try omega]; exact h.out
  refine dd10Half_ok (Or.inl rfl) (o := 0) (by decide) cs5 l18 l19 D6
    (fun i hi => by rw [wr5]; exact h.out16 hp hi) (by rw [g5 .x3 (by decide), x3, ptr_zero]) (by omega) out
    (by rw [m5]; exact h.frame) (fun m hm => G10 s₀ hk (by omega)) fun s6 g6 rd6 wr6 sp6 v6 o6 f6 => ?_
  refine dd10Half_ok (Or.inr rfl) (o := 32) (by decide)
    ⟨by rw [v6 .v16 (by decide) (by decide) (by decide) (by decide)]; exact cs5.q,
     by rw [v6 .v17 (by decide) (by decide) (by decide) (by decide)]; exact cs5.h⟩
    (by rw [v6 .v18 (by decide) (by decide) (by decide) (by decide)]; exact l18)
    (by rw [v6 .v19 (by decide) (by decide) (by decide) (by decide)]; exact l19)
    (by rw [v6 .v7 (by decide) (by decide) (by decide) (by decide)]; exact D7)
    (fun i hi => by rw [wr6, wr5]; exact h.out16 hp hi)
    (by rw [g6, g5 .x3 (by decide), x3]; exact coeffAddr_off _ _ 8) (by omega) o6 f6
    (fun m hm => by
      rw [show 16 * k + 8 + m = 16 * k + (8 + m) by omega, G10 s₀ hk (by omega)]
      simp only [dig10]
      rw [show (8 + m) / 4 = 2 + m / 4 by omega, show (8 + m) % 4 = m % 4 by omega])
    fun s7 g7 rd7 wr7 sp7 v7 o7 f7 => ?_
  have k4 : k < 256 / (width10.c * 4) := by simp [width10]; omega
  have gg : ∀ r, r ≠ .x9 → s7.gpr r = s.gpr r := fun r hr => by rw [g7, g6, g5 r hr]
  refine WP.mono (dtail_ok (w := width10) (Ng := 4) (s₀ := s₀) k4 (by rw [gg .x0 (by decide), h.x0])
    (by rw [gg .x3 (by decide), h.x3]) (by rw [gg .x11 (by decide), h.x11]) (by decide) (by decide))
    fun u ⟨o, uv, u0, u3, u11, uc⟩ => ?_
  have hv : ∀ r, r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v4 → r ≠ .v5 → r ≠ .v6 → r ≠ .v7 → u.v r = s.v r :=
    fun r a b c d e f g' => by rw [uv, v7 r g' a b c, v6 r f a b c, v5 r d e f g']
  refine ⟨⟨by rw [o.rd, rd7, rd6, h5.rd, h4.rd, h3.rd, o2.rd, h1.rd, h.rd], by rw [o.wr, wr7, wr6, wr5, h.wr],
    by rw [o.sp, sp7, sp6, h5.sp, h4.sp, h3.sp, o2.sp, h1.sp, h.sp], u0, u3, u11,
    ⟨by rw [hv .v16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.cs.q,
     by rw [hv .v17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.cs.h⟩,
    ⟨by rw [hv .v18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.K.1,
     by rw [hv .v19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.K.2.1,
     by rw [hv .v20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.K.2.2.1,
     by rw [hv .v21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.K.2.2.2⟩,
    ?_, by rw [o.mem]; exact f7⟩, by rw [show 256 / (width10.c * 4) = 16 from rfl] at uc; exact uc⟩
  rw [o.mem, show width10.c * 4 * (k + 1) = 16 * k + 8 + 8 by simp [width10]; omega]
  exact o7


end VG.Proof.MlKem.AArch64.DD
