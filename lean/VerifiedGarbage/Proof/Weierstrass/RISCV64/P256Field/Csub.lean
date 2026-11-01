module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Words
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
public import VerifiedGarbage.Proof.X25519.RISCV64.Instr
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# P-256's field on RISC-V: the final subtraction

`csub` (`Impl/Weierstrass/RISCV64/P256Field.lean`) stores `x mod p` at
`[t2]` for the number `x = X0 + … + 2¹⁹² X3 + 2²⁵⁶ XC` below `2p`
(`csub_ok`): `x + (2²⁵⁶ - p)` with carries (`sumN_ok`), whose carry out of 256
bits or `XC` is `x ≥ p`, then its low words or `x`'s by that mask
(`sel_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P256Field

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P256Field
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt dw_write_self dw_write_other al8)

/-- The registers `csub` writes. -/
abbrev clobC : List Reg := [.t0, .t6, .a0, .a4, .a5, .a6, .a7]

/-- The number of the words `x₀`–`x₃` of registers. -/
abbrev v4 (s : State) (r₀ r₁ r₂ r₃ : Reg) : Nat :=
  (s.gpr r₀).toNat + 2 ^ 64 * (s.gpr r₁).toNat + 2 ^ 128 * (s.gpr r₂).toNat + 2 ^ 192 * (s.gpr r₃).toNat

/-- The four doublewords at `O`. -/
abbrev d4 (m : Mem) (O : Addr) : Nat := dw m O 0 + 2 ^ 64 * dw m O 8 + 2 ^ 128 * dw m O 16 + 2 ^ 192 * dw m O 24

set_option linter.unusedSimpArgs false in
/-- `x + (2²⁵⁶ - p)` into `t6`, `a4`–`a6`, its carry into `a7`. -/
theorem sumN_ok {s : State} :
    WP isa (.block ([.addi .t6 X0 1, .sltu .a7 .t6 X0] ++
      [.li .t0 (-1), .shift .sll .d .t0 .t0 32] ++ csubWord .a4 X1 ++
      [.li .t0 (-1)] ++ csubWord .a5 X2 ++
      [.li .t0 (-1), .shift .srl .d .t0 .t0 32, .addi .t0 .t0 (-1)] ++ csubWord .a6 X3)) s fun s' =>
      v4 s' .t6 .a4 .a5 .a6 + 2 ^ 256 * (s'.gpr .a7).toNat = v4 s X0 X1 X2 X3 + (2 ^ 256 - P) ∧
      (s'.gpr .a7).toNat ≤ 1 ∧ Keeps clobC s s' := by
  simp only [List.append_assoc, List.cons_append, List.nil_append, csubWord]
  refine wp_addi (imm := 1) (by decide) fun sa ua => wp_sltu fun sb ub => wp_lim1 fun sc uc =>
    wp_sll (by decide) fun sd ud => ?_
  refine WP.block_append (WP.mono (adc_ok (d := .a4) (x := X1) (y := .t0) (c := .a7) (u := .a0))
    fun s1 ⟨e1, k1⟩ => ?_)
  refine wp_lim1 fun se ue => ?_
  refine WP.block_append (WP.mono (adc_ok (d := .a5) (x := X2) (y := .t0) (c := .a7) (u := .a0))
    fun s2 ⟨e2, k2⟩ => ?_)
  refine wp_lim1 fun sf uf => wp_srl (by decide) fun sg ug => wp_subi (imm := 1) (by decide) fun sh uh => ?_
  refine WP.mono (adc_ok (d := .a6) (x := X3) (y := .t0) (c := .a7) (u := .a0)) fun s3 ⟨e3, k3⟩ => ?_
  -- The carry out of `x₀ + 1`.
  have c0 : (sb.gpr .t6).toNat + 2 ^ 64 * (sb.gpr .a7).toNat = (s.gpr X0).toNat + 1 := by
    rw [ub.other _ (by decide), ub.gpr, ua.gpr, ua.other _ (by decide)]
    have := carry (BitVec.ofNat 64 1) (s.gpr X0)
    rw [BitVec.add_comm (BitVec.ofNat 64 1)] at this
    simp only [BitVec.toNat_ofNat] at this ⊢
    omega
  have hn1 : (sd.gpr .t0).toNat = 2 ^ 64 - 2 ^ 32 := by rw [ud.gpr, uc.gpr]; decide
  have hn2 : (se.gpr .t0).toNat = 2 ^ 64 - 1 := by rw [ue.gpr]; decide
  have hn3 : (sh.gpr .t0).toNat = 2 ^ 32 - 2 := by rw [uh.gpr, ug.gpr, uf.gpr]; decide
  have a7d : (sd.gpr .a7) = sb.gpr .a7 := by rw [ud.other _ (by decide), uc.other _ (by decide)]
  have x1d : sd.gpr X1 = s.gpr X1 := by
    rw [ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide)]
  have hc0 : (sb.gpr .a7).toNat ≤ 1 := by
    rw [ub.gpr]; exact sltu_le _
  have e1' := e1 (by rw [a7d]; exact hc0)
  rw [a7d, x1d, hn1] at e1'
  have b1 := (s1.gpr .a4).isLt
  have hc1 : (se.gpr .a7).toNat ≤ 1 := by rw [ue.other _ (by decide)]; omega
  have e2' := e2 hc1
  rw [hn2, ue.other _ (by decide), k1.1 _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
    ub.other _ (by decide), ua.other _ (by decide), ue.other .a7 (by decide)] at e2'
  have b2 := (s2.gpr .a5).isLt
  have hc2 : (sh.gpr .a7).toNat ≤ 1 := by
    rw [uh.other _ (by decide), ug.other _ (by decide), uf.other _ (by decide)]; omega
  have e3' := e3 hc2
  rw [hn3, uh.other X3 (by decide), ug.other X3 (by decide), uf.other X3 (by decide), k2.1 X3 (by decide),
    ue.other X3 (by decide), k1.1 X3 (by decide), ud.other X3 (by decide), uc.other X3 (by decide),
    ub.other X3 (by decide), ua.other X3 (by decide), uh.other .a7 (by decide), ug.other .a7 (by decide),
    uf.other .a7 (by decide)] at e3'
  have b3 := (s3.gpr .a6).isLt
  -- The registers at the end.
  have f6 : s3.gpr .t6 = sb.gpr .t6 := by
    rw [k3.1 _ (by decide), uh.other _ (by decide), ug.other _ (by decide), uf.other _ (by decide),
      k2.1 _ (by decide), ue.other _ (by decide), k1.1 _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide)]
  have f4 : s3.gpr .a4 = s1.gpr .a4 := by
    rw [k3.1 _ (by decide), uh.other _ (by decide), ug.other _ (by decide), uf.other _ (by decide),
      k2.1 _ (by decide), ue.other _ (by decide)]
  have f5 : s3.gpr .a5 = s2.gpr .a5 := by
    rw [k3.1 _ (by decide), uh.other _ (by decide), ug.other _ (by decide), uf.other _ (by decide)]
  have x2 : (se.gpr X2) = s.gpr X2 := by
    rw [ue.other _ (by decide), k1.1 _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide)]
  refine ⟨?_, by omega, ?_⟩
  · simp only [v4, f6, f4, f5, P]
    have := (s.gpr X0).isLt
    omega
  · exact ((((((((((upd_keeps ua).trans (upd_keeps ub)).trans (upd_keeps uc)).trans (upd_keeps ud)).trans
      k1).trans (upd_keeps ue)).trans k2).trans (upd_keeps uf)).trans (upd_keeps ug)).trans
      (upd_keeps uh) |>.trans k3).mono (by decide)

/-- A mask, zero or all ones. -/
def IsMask (m : BitVec 64) : Prop := m = 0 ∨ m = BitVec.allOnes 64

/-- `x ⊕ ((e ⊕ x) ∧ m)`: `e` under the mask all ones, `x` under zero. -/
theorem sel_mask {x e m : BitVec 64} (hm : IsMask m) :
    (e ^^^ x) &&& m ^^^ x = if m = BitVec.allOnes 64 then e else x := by
  rcases hm with rfl | rfl
  · have : (0 : BitVec 64) ≠ BitVec.allOnes 64 := by decide
    simp only [this, ↓reduceIte]
    ext i hi
    simp
  · simp only [BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, ↓reduceIte]

/-- The region of `o`'s four doublewords. -/
theorem out_contains (O : Addr) {j : Nat} (hj : j < 4) :
    (⟨O, 32⟩ : Region).Contains (O + BitVec.ofNat 64 (8 * j)) 8 := by
  have := Offset.contains O (d := 8 * j) (n := 8) (e := 0) (k := 32) (by omega) (by omega) (by omega)
  simpa using this

set_option linter.unusedSimpArgs false in
/-- `selWord x e j`: `[O + 8j] =` `e` under the mask `t0` all ones, else `x`. -/
theorem selWord_ok {s : State} {O : Addr} {x e : Reg} {j : Nat} (hj : j < 4) (ht2 : s.gpr .t2 = O)
    (hal : O.toNat % 8 = 0) (hw : InRegions s.wr (O + BitVec.ofNat 64 (8 * j)) 8) (hm : IsMask (s.gpr .t0))
    (hex : e ≠ x := by decide) (he0 : e ≠ .t0 := by decide) (he2 : e ≠ .t2 := by decide) :
    WP isa (.block (selWord x e j)) s fun s' =>
      s'.mem = s.mem.writeW (O + BitVec.ofNat 64 (8 * j))
        (if s.gpr .t0 = BitVec.allOnes 64 then s.gpr e else s.gpr x) ∧
      (∀ r, r ≠ e → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold selWord
  refine wp_xor fun s1 u1 => VG.Proof.X25519.RISCV64.wp_and fun s2 u2 => wp_xor fun s3 u3 => ?_
  have h3 : s3.gpr e = if s.gpr .t0 = BitVec.allOnes 64 then s.gpr e else s.gpr x := by
    rw [u3.gpr, u2.gpr, u1.gpr, u2.other _ hex.symm, u1.other _ hex.symm, u1.other _ he0.symm]
    exact sel_mask hm
  have g3 : ∀ r, r ≠ e → s3.gpr r = s.gpr r := fun r hr => by rw [u3.other _ hr, u2.other _ hr, u1.other _ hr]
  refine wp_sd (by omega) (by rw [g3 _ (Ne.symm he2), ht2]) (al8 hal (by omega))
    (by rw [u3.wr, u2.wr, u1.wr]; exact hw) fun s4 u4 => WP.block_nil ?_
  refine ⟨by rw [u4.mem, h3, u3.mem, u2.mem, u1.mem], fun r hr => by rw [u4.gpr, g3 _ hr], ?_, ?_, ?_⟩
  · rw [u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u4.wr, u3.wr, u2.wr, u1.wr]
  · rw [u4.sp, u3.sp, u2.sp, u1.sp]

/-- The mask of `a ∨ c`, for bits `a` and `c`. -/
theorem mask_of_bits {a c : BitVec 64} (ha : a.toNat ≤ 1) (hc : c.toNat ≤ 1) :
    IsMask (0 - (a ||| c)) ∧ (0 - (a ||| c) = BitVec.allOnes 64 ↔ a.toNat = 1 ∨ c.toNat = 1) := by
  have ha' : a = 0 ∨ a = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with h | h
    · exact .inl (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    · exact .inr (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  have hc' : c = 0 ∨ c = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h
    · exact .inl (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    · exact .inr (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  rcases ha' with rfl | rfl <;> rcases hc' with rfl | rfl <;> (unfold IsMask; decide)

/-- `csub`: `x mod p` at `[t2]`, for `x = X0 + … + 2¹⁹² X3 + 2²⁵⁶ XC` below `2p`. -/
theorem csub_ok {s : State} {O : Addr} (ht2 : s.gpr .t2 = O) (hal : O.toNat % 8 = 0)
    (hw : ∀ j < 4, InRegions s.wr (O + BitVec.ofNat 64 (8 * j)) 8) (hc : (s.gpr XC).toNat ≤ 1)
    (hx : v4 s X0 X1 X2 X3 + 2 ^ 256 * (s.gpr XC).toNat < 2 * P) :
    WP isa (.block csub) s fun s' =>
      d4 s'.mem O = (v4 s X0 X1 X2 X3 + 2 ^ 256 * (s.gpr XC).toNat) % P ∧
      Frame [⟨O, 32⟩] s.mem s'.mem ∧ (∀ r, r ∉ clobC → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e : csub = ([.addi .t6 X0 1, .sltu .a7 .t6 X0] ++
      [.li .t0 (-1), .shift .sll .d .t0 .t0 32] ++ csubWord .a4 X1 ++
      [.li .t0 (-1)] ++ csubWord .a5 X2 ++
      [.li .t0 (-1), .shift .srl .d .t0 .t0 32, .addi .t0 .t0 (-1)] ++ csubWord .a6 X3) ++
      ([.logic .or .a7 .a7 XC, .li .t0 0, .sub .t0 .t0 .a7] ++
      (selWord X0 .t6 0 ++ (selWord X1 .a4 1 ++ (selWord X2 .a5 2 ++ selWord X3 .a6 3)))) := by
    simp only [csub, List.append_assoc]
  rw [e]
  refine WP.block_append (WP.mono sumN_ok fun s1 ⟨v1, c1, k1⟩ => ?_)
  refine wp_or fun s2 u2 => wp_li (imm := 0) (by decide) fun s3 u3 => wp_sub fun s4 u4 => ?_
  have hm : IsMask (s4.gpr .t0) ∧ (s4.gpr .t0 = BitVec.allOnes 64 ↔
      (s1.gpr .a7).toNat = 1 ∨ (s.gpr XC).toNat = 1) := by
    rw [u4.gpr, u3.gpr, u3.other _ (by decide), u2.gpr, k1.1 XC (by decide)]
    exact mask_of_bits c1 hc
  have g4 : ∀ r, r ≠ .t0 → r ≠ .a7 → s4.gpr r = s1.gpr r := fun r h0 h7 => by
    rw [u4.other _ h0, u3.other _ h0, u2.other _ h7]
  have m4 : s4.mem = s1.mem := by rw [u4.mem, u3.mem, u2.mem]
  have w4 : s4.wr = s.wr := by rw [u4.wr, u3.wr, u2.wr, k1.2.2.2.1]
  have p4 : s4.gpr .t2 = O := by rw [g4 _ (by decide) (by decide), k1.1 _ (by decide), ht2]
  show WP isa (.block (selWord X0 .t6 0 ++ _)) s4 _
  refine WP.block_append (WP.mono (selWord_ok (x := X0) (e := .t6) (j := 0) (by decide) p4 hal
    (by rw [w4]; exact hw 0 (by decide)) hm.1) fun s5 ⟨m5, g5, r5, w5, sp5⟩ => ?_)
  have t5 : s5.gpr .t0 = s4.gpr .t0 := g5 _ (by decide)
  refine WP.block_append (WP.mono (selWord_ok (x := X1) (e := .a4) (j := 1) (by decide)
    (by rw [g5 _ (by decide), p4]) hal (by rw [w5, w4]; exact hw 1 (by decide)) (by rw [t5]; exact hm.1))
    fun s6 ⟨m6, g6, r6, w6, sp6⟩ => ?_)
  have t6 : s6.gpr .t0 = s4.gpr .t0 := by rw [g6 _ (by decide), t5]
  refine WP.block_append (WP.mono (selWord_ok (x := X2) (e := .a5) (j := 2) (by decide)
    (by rw [g6 _ (by decide), g5 _ (by decide), p4]) hal (by rw [w6, w5, w4]; exact hw 2 (by decide))
    (by rw [t6]; exact hm.1)) fun s7 ⟨m7, g7, r7, w7, sp7⟩ => ?_)
  have t7 : s7.gpr .t0 = s4.gpr .t0 := by rw [g7 _ (by decide), t6]
  refine WP.mono (selWord_ok (x := X3) (e := .a6) (j := 3) (by decide)
    (by rw [g7 _ (by decide), g6 _ (by decide), g5 _ (by decide), p4]) hal
    (by rw [w7, w6, w5, w4]; exact hw 3 (by decide)) (by rw [t7]; exact hm.1))
    fun s8 ⟨m8, g8, r8, w8, sp8⟩ => ?_
  -- The registers, from `s1` and `s`.
  have rt4 : ∀ r, r ∉ clobC → s4.gpr r = s.gpr r := fun r hr => by
    rw [g4 _ (fun h => hr (by simp [h])) (fun h => hr (by simp [h])), k1.1 r hr]
  have rt5 : ∀ r, r ∉ clobC → s5.gpr r = s.gpr r := fun r hr => by
    rw [g5 _ (fun h => hr (by simp [h])), rt4 r hr]
  have rt6 : ∀ r, r ∉ clobC → s6.gpr r = s.gpr r := fun r hr => by
    rw [g6 _ (fun h => hr (by simp [h])), rt5 r hr]
  have rt7 : ∀ r, r ∉ clobC → s7.gpr r = s.gpr r := fun r hr => by
    rw [g7 _ (fun h => hr (by simp [h])), rt6 r hr]
  have rt8 : ∀ r, r ∉ clobC → s8.gpr r = s.gpr r := fun r hr => by
    rw [g8 _ (fun h => hr (by simp [h])), rt7 r hr]
  have d0 : s4.gpr .t6 = s1.gpr .t6 := g4 _ (by decide) (by decide)
  have d1 : s5.gpr .a4 = s1.gpr .a4 := by rw [g5 _ (by decide), g4 _ (by decide) (by decide)]
  have d2 : s6.gpr .a5 = s1.gpr .a5 := by
    rw [g6 _ (by decide), g5 _ (by decide), g4 _ (by decide) (by decide)]
  have d3 : s7.gpr .a6 = s1.gpr .a6 := by
    rw [g7 _ (by decide), g6 _ (by decide), g5 _ (by decide), g4 _ (by decide) (by decide)]
  rw [t5] at m6
  rw [t6] at m7
  rw [t7] at m8
  rw [d0, rt4 X0 (by decide)] at m5
  rw [d1, rt5 X1 (by decide)] at m6
  rw [d2, rt6 X2 (by decide)] at m7
  rw [d3, rt7 X3 (by decide)] at m8
  rw [m7, m6, m5, m4] at m8
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at m8
  have hm1 : s1.mem = s.mem := k1.2.1
  refine ⟨?_, ?_, rt8, ?_, ?_, ?_⟩
  · rw [m8, d4, dw_write_other _ _ _ (by omega) (by omega) (by omega),
      dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_other _ _ _ (by omega) (by omega) (by omega),
      show O + BitVec.ofNat 64 0 = O + BitVec.ofNat 64 0 from rfl, dw_write_self,
      dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_other _ _ _ (by omega) (by omega) (by omega),
      dw_write_self, dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_self, dw_write_self]
    have hge := hm.2
    simp only [v4] at v1 hx ⊢
    have := (s.gpr X0).isLt; have := (s.gpr X1).isLt; have := (s.gpr X2).isLt; have := (s.gpr X3).isLt
    have := (s1.gpr .t6).isLt; have := (s1.gpr .a4).isLt; have := (s1.gpr .a5).isLt; have := (s1.gpr .a6).isLt
    by_cases h : s4.gpr .t0 = BitVec.allOnes 64
    · simp only [h, ↓reduceIte]
      have hg := hge.mp h
      rw [Nat.mod_eq_sub_mod (by simp only [P] at *; omega), Nat.mod_eq_of_lt (by simp only [P] at *; omega)]
      simp only [P] at *
      omega
    · simp only [h, ↓reduceIte]
      have hg : ¬ ((s1.gpr .a7).toNat = 1 ∨ (s.gpr XC).toNat = 1) := fun h' => h (hge.mpr h')
      rw [Nat.mod_eq_of_lt (by simp only [P] at *; omega)]
      omega
  · rw [m8, ← hm1]
    have c0 := out_contains O (j := 0) (by decide)
    have c1 := out_contains O (j := 1) (by decide)
    have c2 := out_contains O (j := 2) (by decide)
    have c3 := out_contains O (j := 3) (by decide)
    simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at c0 c1 c2 c3
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW
      (List.mem_singleton_self _) _ c1).writeW (List.mem_singleton_self _) _ c2).writeW
      (List.mem_singleton_self _) _ c3
  · rw [r8, r7, r6, r5, u4.rd, u3.rd, u2.rd, k1.2.2.1]
  · rw [w8, w7, w6, w5, w4]
  · rw [sp8, sp7, sp6, sp5, u4.sp, u3.sp, u2.sp, k1.2.2.2.2]

end VG.Proof.Weierstrass.RISCV64.P256Field
