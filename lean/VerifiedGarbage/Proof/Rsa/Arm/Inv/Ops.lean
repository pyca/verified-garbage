module

public import VerifiedGarbage.Impl.Rsa.Arm.Inverse
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.Arm.RowState
public import VerifiedGarbage.Proof.Rsa.Arm.Inv.Geo
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.Mac
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Reduce
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Arm.SubRow
import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasRow
import VerifiedGarbage.Proof.Bignum.Arm.CopyWords

/-! # The array operations of `inverse` on ARMv7, at `k + 1` (or `k`) words -/

@[expose] public section

/-! ## `macRow` on ARMv7: a multiply-accumulate row that keeps `r6`–`r9` -/

namespace VG.Proof.Rsa.Arm.Inv
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.Keys.Inv
open VG.Proof.X25519.Arm (Rest Upd ofNat_beq_zero wp_ldr wp_str wp_dp wp_subs op2_imm dpVal toNat_shr toNat_shl toNat_mul_lt)
open VG.Proof.Bignum.Arm (add_cross_value add_word_value partials_value RowCtx row_addr row_writable)
open VG.Proof.Mont

theorem low16 (y : BitVec 32) : (y &&& ~~~((y >>> 16) <<< 16)).toNat = y.toNat % 65536 := by
  have e : y &&& ~~~((y >>> 16) <<< 16) = y &&& ((0xffff : BitVec 16).setWidth 32) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have ones : ∀ j < 16, (0xffff : BitVec 16).getLsbD j = true := by decide
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
    by_cases h : i < 16
    · simp only [ones i h, h, decide_true, Bool.not_true, Bool.false_and, Bool.not_false, Bool.and_true]
    · have h16 : 16 + (i - 16) = i := by omega
      simp only [h, decide_false, Bool.not_false, Bool.true_and, h16,
        BitVec.getLsbD_of_ge (0xffff : BitVec 16) i (by omega)]
      cases y.getLsbD i <;> simp
  rw [e]; exact VG.Proof.X25519.Arm.toNat_and_mask16 y

/-- The carry of `lo + m`, as a word. -/
abbrev cy (lo m : BitVec 32) : BitVec 32 := if 2 ^ 32 ≤ lo.toNat + m.toNat then 1 else 0

theorem macMul_value (xl xh y c : BitVec 32) (h1 : xl.toNat < 65536) (h10 : xh.toNat < 65536) :
    (xl * (y &&& ~~~(y >>> 16 <<< 16)) + (xh * (y &&& ~~~(y >>> 16 <<< 16))) <<< 16 +
        (xl * (y >>> 16)) <<< 16 + c).toNat +
      (xh * (y >>> 16) + (xh * (y &&& ~~~(y >>> 16 <<< 16))) >>> 16 +
          cy (xl * (y &&& ~~~(y >>> 16 <<< 16))) ((xh * (y &&& ~~~(y >>> 16 <<< 16))) <<< 16) +
          (xl * (y >>> 16)) >>> 16 +
          cy (xl * (y &&& ~~~(y >>> 16 <<< 16)) + (xh * (y &&& ~~~(y >>> 16 <<< 16))) <<< 16)
            ((xl * (y >>> 16)) <<< 16) + (0 : BitVec 32) +
          cy (xl * (y &&& ~~~(y >>> 16 <<< 16)) + (xh * (y &&& ~~~(y >>> 16 <<< 16))) <<< 16 +
              (xl * (y >>> 16)) <<< 16) c).toNat * 2 ^ 32 =
      (xl.toNat + 65536 * xh.toNat) * y.toNat + c.toNat := by
  have yl := low16 y
  have yh : (y >>> 16).toNat = y.toNat / 65536 := toNat_shr y 16
  have hyl : (y &&& ~~~((y >>> 16) <<< 16)).toNat < 65536 := by rw [yl]; omega
  have hyh : (y >>> 16).toNat < 65536 := by rw [yh]; have := y.isLt; omega
  have lt (a b : Nat) (ha : a < 65536) (hb : b < 65536) : a * b < 2 ^ 32 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (by omega)) (by decide)
  have p0 := toNat_mul_lt (x := xl) (y := y &&& ~~~((y >>> 16) <<< 16)) (lt _ _ h1 hyl)
  have p1 := toNat_mul_lt (x := xh) (y := y &&& ~~~((y >>> 16) <<< 16)) (lt _ _ h10 hyl)
  have p2 := toNat_mul_lt (x := xh) (y := y >>> 16) (lt _ _ h10 hyh)
  have p3 := toNat_mul_lt (x := xl) (y := y >>> 16) (lt _ _ h1 hyh)
  rw [yl] at p0 p1
  rw [yh] at p2 p3
  generalize xl * (y &&& ~~~((y >>> 16) <<< 16)) = P0 at *
  generalize xh * (y &&& ~~~((y >>> 16) <<< 16)) = P1 at *
  generalize xh * (y >>> 16) = P2 at *
  generalize xl * (y >>> 16) = P3 at *
  have total : xl.toNat * (y.toNat % 65536) + xh.toNat * (y.toNat / 65536) * 2 ^ 32 +
      xh.toNat * (y.toNat % 65536) * 2 ^ 16 + xl.toNat * (y.toNat / 65536) * 2 ^ 16 =
      (xl.toNat + 65536 * xh.toNat) * y.toNat := by
    have hy' : y.toNat = y.toNat % 65536 + y.toNat / 65536 * 65536 := by omega
    generalize y.toNat % 65536 = b0 at *
    generalize y.toNat / 65536 = b1 at *
    rw [hy']; grind
  have hP : (xl.toNat + 65536 * xh.toNat) * y.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := by
    have hx : xl.toNat + 65536 * xh.toNat ≤ 2 ^ 32 - 1 := by omega
    exact Nat.mul_le_mul hx (by have := y.isLt; omega)
  generalize (xl.toNat + 65536 * xh.toNat) * y.toNat = Pr at total hP ⊢
  generalize xl.toNat * (y.toNat % 65536) = A0 at total p0
  generalize xh.toNat * (y.toNat % 65536) = A1 at total p1
  generalize xh.toNat * (y.toNat / 65536) = A2 at total p2
  generalize xl.toNat * (y.toNat / 65536) = A3 at total p3
  have b0 : A0 < 2 ^ 32 := p0 ▸ P0.isLt
  have b1 : A1 < 2 ^ 32 := p1 ▸ P1.isLt
  have b2 : A2 < 2 ^ 32 := p2 ▸ P2.isLt
  have b3 : A3 < 2 ^ 32 := p3 ▸ P3.isLt
  clear yl yh hyl hyh lt h1 h10
  have c1 := add_cross_value P0 P2 P1 (by rw [p0, p2, p1]; omega)
  have c2 := add_cross_value (P0 + (P1 <<< 16)) (P2 + (P1 >>> 16) + cy P0 (P1 <<< 16)) P3
    (by simp only [cy] at c1 ⊢; rw [c1, p0, p2, p1]; omega)
  have c3 := add_word_value (P0 + (P1 <<< 16) + (P3 <<< 16))
    (P2 + (P1 >>> 16) + cy P0 (P1 <<< 16) + (P3 >>> 16) + cy (P0 + (P1 <<< 16)) (P3 <<< 16)) c
    (by simp only [cy] at c1 c2 ⊢; rw [c2, c1, p0, p2, p1, p3]; have := c.isLt; omega)
  have z0 : ∀ x : BitVec 32, x + (0 : BitVec 32) = x := fun x => by simp
  simp only [cy, z0] at c1 c2 c3 ⊢
  rw [c3, c2, c1, p0, p1, p2, p3]
  omega

/-- `macMul`: `r5:r4 = (r1 + 2^16 r10) r2 + r11` for halves `r1`, `r10`. -/
theorem macMul_run (s : State) (h1 : (s.gpr .r1).toNat < 65536) (h10 : (s.gpr .r10).toNat < 65536) :
    ∃ t, runBlock isa macMul s = some t ∧
      (t.gpr .r4).toNat + (t.gpr .r5).toNat * 2 ^ 32 =
        ((s.gpr .r1).toNat + 65536 * (s.gpr .r10).toNat) * (s.gpr .r2).toNat + (s.gpr .r11).toNat ∧
      Rest [.r2, .r3, .r4, .r5] s t ∧ t.mem = s.mem := by
  have e0 : encodable 0 = true := by decide
  have s16 : (1 ≤ 16 ∧ 16 ≤ 31) = True := by decide
  obtain ⟨t, run⟩ : ∃ t, runBlock isa macMul s = some t := ⟨_, by
    simp only [macMul, runBlock_cons, runStep_some, runBlock_nil, reduceExec, Op2.eval,
      Option.map_some, e0, s16, ↓reduceIte]
    exact rfl⟩
  have ht := run
  simp only [macMul, runBlock_cons, runStep_some, runBlock_nil, reduceExec, Op2.eval,
    Option.map_some, e0, s16, ↓reduceIte, Option.some.injEq] at ht
  subst ht
  refine ⟨_, run, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl⟩
  · simp only [addFlags, gpr_setReg, c_setReg, reduceCtorEq, ↓reduceIte, decide_eq_true_eq]
    exact macMul_value _ _ _ _ h1 h10
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h2, h3, h4, h5⟩ := hr
    simp only [addFlags, gpr_setReg, h2, h3, h4, h5, ↓reduceIte]

abbrev macClob : List Reg := [.r0, .r2, .r3, .r4, .r5, .r11, .r12, .lr]

theorem macAcc_value (lo hi a : BitVec 32) (h : lo.toNat + hi.toNat * 2 ^ 32 + a.toNat < 2 ^ 64) :
    (lo + a).toNat + (hi + (0 : BitVec 32) + cy lo a).toNat * 2 ^ 32 = lo.toNat + hi.toNat * 2 ^ 32 + a.toNat := by
  have z0 : hi + (0 : BitVec 32) = hi := by simp
  rw [z0]; exact add_word_value lo hi a h

/-- One step of `macRow`: `r4 + 2^32 r11 = x [b] + [a] + r11`, stored at `a`, and the advance. -/
theorem macStep_ok (s : State) (a b : Addr) (h1 : (s.gpr .r1).toNat < 65536) (h10 : (s.gpr .r10).toNat < 65536)
    (ha : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (hb : State.addr (s.gpr .r12 + BitVec.ofNat 32 0) = b)
    (hread : InRegions (s.rd ++ s.wr) b 4) (hwrite : InRegions s.wr a 4) :
    WP isa (.block macStep) s fun t =>
      (t.gpr .r4).toNat + (t.gpr .r11).toNat * 2 ^ 32 =
        ((s.gpr .r1).toNat + 65536 * (s.gpr .r10).toNat) * (s.mem.readW b 32).toNat +
          (s.mem.readW a 32).toNat + (s.gpr .r11).toNat ∧
      t.mem = s.mem.writeW a (t.gpr .r4) ∧ t.gpr .r0 = s.gpr .r0 + 4 ∧ t.gpr .r12 = s.gpr .r12 + 4 ∧
      t.gpr .lr = s.gpr .lr - 1 ∧ t.z = (s.gpr .lr - 1 == 0) ∧ Rest macClob s t := by
  unfold macStep
  refine wp_ldr (by decide) hb hread fun s1 u1 => ?_
  rw [show (macMul.append macAcc).append macAdvance = macMul ++ (macAcc ++ macAdvance) from
    List.append_assoc _ _ _]
  apply WP.block_append_iff.mpr
  obtain ⟨s2, run2, v2, r2, m2⟩ := macMul_run s1 (by rw [u1.other .r1 (by decide)]; exact h1)
    (by rw [u1.other .r10 (by decide)]; exact h10)
  refine WP.of_runBlock ⟨s2, run2, ?_⟩
  rw [u1.gpr, u1.other .r1 (by decide), u1.other .r10 (by decide), u1.other .r11 (by decide)] at v2
  have p0 : s2.gpr .r0 = s.gpr .r0 := (r2.gpr _ (by decide)).trans (u1.other _ (by decide))
  have p12 : s2.gpr .r12 = s.gpr .r12 := (r2.gpr _ (by decide)).trans (u1.other _ (by decide))
  have plr : s2.gpr .lr = s.gpr .lr := (r2.gpr _ (by decide)).trans (u1.other _ (by decide))
  have mem2 : s2.mem = s.mem := m2.trans u1.mem
  have rw2 : s2.rd = s.rd ∧ s2.wr = s.wr := ⟨r2.rd.trans u1.rd, r2.wr.trans u1.wr⟩
  unfold macAcc
  refine wp_ldr (a := a) (by decide) (by rw [p0]; exact ha)
    (by rw [rw2.1, rw2.2]; rcases hwrite with ⟨R, hR, h⟩; exact ⟨R, List.mem_append_right _ hR, h⟩)
    fun s3 u3 => ?_
  have e0 : encodable 0 = true := by decide
  obtain ⟨s4, run4⟩ : ∃ t, runBlock isa [.adds .r4 .r4 (.reg .r2), .adc .r11 .r5 (.imm 0)] s3 = some t :=
    ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, Op2.eval, Option.map_some,
      e0, ↓reduceIte]; exact rfl⟩
  have h4 := run4
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, Op2.eval, Option.map_some,
      e0, ↓reduceIte, Option.some.injEq] at h4
  have g4 : ∀ r, r ≠ .r4 → r ≠ .r11 → s4.gpr r = s3.gpr r := fun r a b => by
    rw [← h4]; simp only [gpr_setReg, a, b, ↓reduceIte, addFlags]
  have v4 : s4.gpr .r4 = s3.gpr .r4 + s3.gpr .r2 ∧
      s4.gpr .r11 = s3.gpr .r5 + 0 + cy (s3.gpr .r4) (s3.gpr .r2) := by
    rw [← h4]; simp only [gpr_setReg, c_setReg, reduceCtorEq, ↓reduceIte, addFlags, cy, decide_eq_true_eq, true_and]
  have f4 : s4.mem = s3.mem ∧ s4.rd = s3.rd ∧ s4.wr = s3.wr ∧ s4.sp = s3.sp := by
    rw [← h4]; exact ⟨rfl, rfl, rfl, rfl⟩
  change WP isa (.block ([_, _] ++ _)) s3 _
  apply WP.block_append_iff.mpr
  refine WP.of_runBlock ⟨_, run4, ?_⟩
  have q0 : s4.gpr .r0 = s.gpr .r0 := (g4 _ (by decide) (by decide)).trans ((u3.other _ (by decide)).trans p0)
  refine wp_str (a := a) (by decide) (by rw [q0]; exact ha) (by rw [f4.2.2.1, u3.wr, rw2.2]; exact hwrite)
    fun s5 u5 => ?_
  refine wp_dp (op2_imm (by decide)) fun s6 u6 => ?_
  refine wp_dp (op2_imm (by decide)) fun s7 u7 => ?_
  refine wp_subs (op2_imm (by decide)) fun t u8 hz => WP.block_nil ?_
  have t4 : t.gpr .r4 = s4.gpr .r4 := by
    rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.gpr]
  have t11 : t.gpr .r11 = s4.gpr .r11 := by
    rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.gpr]
  have l7 : s7.gpr .lr = s.gpr .lr := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.gpr, g4 _ (by decide) (by decide),
      u3.other _ (by decide), plr]
  have a3 : s3.gpr .r2 = s.mem.readW a 32 := by rw [u3.gpr, mem2]
  have a4 : s3.gpr .r4 = s2.gpr .r4 := u3.other _ (by decide)
  have a5 : s3.gpr .r5 = s2.gpr .r5 := u3.other _ (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have bnd : (s2.gpr .r4).toNat + (s2.gpr .r5).toNat * 2 ^ 32 + (s.mem.readW a 32).toNat < 2 ^ 64 := by
      rw [v2]
      have := (s.mem.readW a 32).isLt
      have := (s.mem.readW b 32).isLt
      have := (s.gpr .r11).isLt
      have hx : (s.gpr .r1).toNat + 65536 * (s.gpr .r10).toNat ≤ 2 ^ 32 - 1 := by omega
      have := Nat.mul_le_mul hx (show (s.mem.readW b 32).toNat ≤ 2 ^ 32 - 1 by omega)
      generalize ((s.gpr .r1).toNat + 65536 * (s.gpr .r10).toNat) * (s.mem.readW b 32).toNat = P at *
      omega
    rw [t4, t11, v4.1, v4.2, a3, a4, a5, macAcc_value _ _ _ bnd, v2]
    omega
  · rw [u8.mem, u7.mem, u6.mem, u5.mem, f4.1, u3.mem, mem2, t4]
  · rw [u8.other _ (by decide), u7.other _ (by decide), u6.gpr, dpVal, u5.gpr, q0]
  · rw [u8.other _ (by decide), u7.gpr, dpVal, u6.other _ (by decide), u5.gpr, g4 _ (by decide) (by decide),
      u3.other _ (by decide), p12]
  · rw [u8.gpr, l7]
  · rw [hz, l7]
  · have r4 : Rest macClob s3 s4 := ⟨fun r hr => g4 r (by intro e; apply hr; simp [e]) (by intro e; apply hr; simp [e]),
      f4.2.1, f4.2.2.1, f4.2.2.2⟩
    exact (u1.rest (by decide)).trans ((r2.mono (by decide)).trans ((u3.rest (by decide)).trans (r4.trans
      ((u5.rest _).trans ((u6.rest (by decide)).trans ((u7.rest (by decide)).trans (u8.rest (by decide))))))))

/-- After `i` steps of `macRow`'s loop, from `s0` (the scalar split). -/
structure MacInv (s0 : State) (x : Nat) (base : BitVec 32) (o b n i : Nat) (s : State) : Prop where
  index : i ≤ n
  outPtr : s.gpr .r0 = base + BitVec.ofNat 32 (o + 4 * i)
  inPtr : s.gpr .r12 = base + BitVec.ofNat 32 (b + 4 * i)
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  outside : Outside (State.addr base) o (4 * i) s0.mem s.mem
  value : val32 s.mem (State.addr base) o i + 2 ^ (32 * i) * (s.gpr .r11).toNat =
    val32 s0.mem (State.addr base) o i + x * val32 s0.mem (State.addr base) b i + (s0.gpr .r11).toNat
  rest : Rest macClob s0 s

theorem macBody_ok {s0 s : State} {x : Nat} {base : BitVec 32} {size o b n i : Nat}
    (ctx : RowCtx s0 base size o b n) (inv : MacInv s0 x base o b n i s) (hi : i < n)
    (h1 : (s0.gpr .r1).toNat < 65536) (h10 : (s0.gpr .r10).toNat < 65536)
    (hx : (s0.gpr .r1).toNat + 65536 * (s0.gpr .r10).toNat = x) :
    WP isa (.block macStep) s fun t => MacInv s0 x base o b n (i + 1) t ∧ t.z = decide (i + 1 = n) := by
  have hn := ctx.nowrap
  have ho := ctx.outFits
  have hb := ctx.inFits
  have hs := ctx.separate
  have e1 : s.gpr .r1 = s0.gpr .r1 := inv.rest.gpr _ (by decide)
  have e10 : s.gpr .r10 = s0.gpr .r10 := inv.rest.gpr _ (by decide)
  have wa := row_writable ctx inv.rest.wr (d := o + 4 * i) (by omega)
  obtain ⟨R, hR, hc⟩ := row_writable ctx inv.rest.wr (d := b + 4 * i) (by omega)
  refine WP.mono (macStep_ok s _ _ (by rw [e1]; exact h1) (by rw [e10]; exact h10)
    (row_addr ctx inv.outPtr (by omega)) (row_addr ctx inv.inPtr (by omega))
    ⟨R, List.mem_append_right _ hR, hc⟩ wa) ?_
  rintro t ⟨hv, hm, p0, p12, plr, hz, hr⟩
  rw [e1, e10, hx] at hv
  have own := inv.outside.w32 (d := o + 4 * i) (by omega) (by omega)
  have src := inv.outside.w32 (d := b + 4 * i) (by omega) (by omega)
  change (t.gpr .r4).toNat + (t.gpr .r11).toNat * 2 ^ 32 =
    x * w32 s.mem (State.addr base) (b + 4 * i) + w32 s.mem (State.addr base) (o + 4 * i) + (s.gpr .r11).toNat at hv
  rw [own, src] at hv
  have wr := writeW32_outside s.mem (State.addr base) (d := o + 4 * i) (t.gpr .r4) (by omega)
  rw [← hm] at wr
  have low := wr.val32 (d := o) (k := i) (by omega) (by omega)
  have top : w32 t.mem (State.addr base) (o + 4 * i) = (t.gpr .r4).toNat := by rw [hm, w32_write_self]
  refine ⟨⟨by omega, ?_, ?_, ?_, (inv.outside.mono (Nat.le_refl _) (by omega)).trans
      (wr.mono (by omega) (by omega)), ?_, inv.rest.trans hr⟩, ?_⟩
  · rw [p0, inv.outPtr]
    change base + BitVec.ofNat 32 (o + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]; congr 2
  · rw [p12, inv.inPtr]
    change base + BitVec.ofNat 32 (b + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]; congr 2
  · rw [plr, inv.count]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), Nat.sub_sub]
  · rw [val32_succ, val32_succ, val32_succ, low, top, pow32_succ]
    have prior := inv.value
    generalize 2 ^ (32 * i) = P at *
    grind
  · rw [hz, inv.count]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [decide_eq_decide]; omega

/-- `macRow`: `lr = n > 0` words at `r12` (from `base + b`) times `r1`, plus `r11`, added into
those at `r0` (`base + o`), the carry out in `r11`. -/
theorem macRow_ok (s : State) {base : BitVec 32} {size o b n : Nat}
    (ctx : RowCtx s base size o b n) (hn : 0 < n)
    (hp0 : s.gpr .r0 = base + BitVec.ofNat 32 o) (hp12 : s.gpr .r12 = base + BitVec.ofNat 32 b)
    (hcount : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa macRow s fun t =>
      Outside (State.addr base) o (4 * n) s.mem t.mem ∧
      val32 t.mem (State.addr base) o n + 2 ^ (32 * n) * (t.gpr .r11).toNat =
        val32 s.mem (State.addr base) o n + (s.gpr .r1).toNat * val32 s.mem (State.addr base) b n +
          (s.gpr .r11).toNat ∧
      Rest (.r1 :: .r10 :: macClob) s t := by
  unfold macRow
  rw [WP.seq_iff]
  have s16 : (1 ≤ 16 ∧ 16 ≤ 31) = True := by decide
  obtain ⟨s1, run1⟩ : ∃ t, runBlock isa macSplit s = some t := ⟨_, by
    simp only [macSplit, runBlock_cons, runStep_some, runBlock_nil, reduceExec, Op2.eval, Option.map_some,
      s16, ↓reduceIte]; exact rfl⟩
  have h1 := run1
  simp only [macSplit, runBlock_cons, runStep_some, runBlock_nil, reduceExec, Op2.eval, Option.map_some,
      s16, ↓reduceIte, Option.some.injEq] at h1
  have g1 : ∀ r, r ≠ .r1 → r ≠ .r10 → s1.gpr r = s.gpr r := fun r a b => by
    rw [← h1]; simp only [gpr_setReg, a, b, ↓reduceIte]
  have x1 : s1.gpr .r1 = s.gpr .r1 &&& ~~~((s.gpr .r1 >>> 16) <<< 16) ∧ s1.gpr .r10 = s.gpr .r1 >>> 16 := by
    rw [← h1]; simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, and_self]
  have f1 : s1.mem = s.mem ∧ s1.rd = s.rd ∧ s1.wr = s.wr ∧ s1.sp = s.sp := by rw [← h1]; exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.of_runBlock ⟨s1, run1, ?_⟩
  have lo := low16 (s.gpr .r1)
  have hi : (s.gpr .r1 >>> 16).toNat = (s.gpr .r1).toNat / 65536 := toNat_shr _ 16
  have hl : (s1.gpr .r1).toNat < 65536 := by rw [x1.1, lo]; omega
  have hh : (s1.gpr .r10).toNat < 65536 := by rw [x1.2, hi]; have := (s.gpr .r1).isLt; omega
  have hx : (s1.gpr .r1).toNat + 65536 * (s1.gpr .r10).toNat = (s.gpr .r1).toNat := by
    rw [x1.1, x1.2, lo, hi]; omega
  have ctx1 : RowCtx s1 base size o b n := ⟨ctx.nowrap, ctx.outFits, ctx.inFits, ctx.separate, by
    rw [f1.2.2.1]; exact ctx.writable⟩
  refine WP.loop (M := isa) (fun k t => ∃ i, i + k = n ∧ 0 < k ∧ MacInv s1 (s.gpr .r1).toNat base o b n i t) ?_ n s1
    ⟨0, by omega, hn, by omega, ?_, ?_, ?_, Outside.refl _ _ _ _, ?_, Rest.refl _ _⟩
  · rintro k t ⟨i, hik, hk, hi⟩
    refine WP.mono (macBody_ok ctx1 hi (by omega) hl hh hx) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨by change some (!u.z) = some false; simp only [hz, he, decide_true, Bool.not_true], ?_, ?_, ?_⟩
      · rw [← f1.1]; exact he ▸ hu.outside
      · have v := he ▸ hu.value
        rw [f1.1, g1 .r11 (by decide) (by decide)] at v
        exact v
      · have r := hu.rest
        exact ⟨fun r' hr' => (r.gpr r' (fun h => hr' (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))).trans
            (g1 r' (fun e => hr' (by simp [e])) (fun e => hr' (by simp [e]))),
          r.rd.trans f1.2.1, r.wr.trans f1.2.2.1, r.sp.trans f1.2.2.2⟩
    · right
      exact ⟨by change some (!u.z) = some true; simp only [hz, he, decide_false, Bool.not_false],
        k - 1, by omega, i + 1, by omega, by omega, hu⟩
  · rw [g1 _ (by decide) (by decide), hp0]; simp
  · rw [g1 _ (by decide) (by decide), hp12]; simp
  · rw [g1 _ (by decide) (by decide), hcount]; simp
  · simp only [val32, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]

end VG.Proof.Rsa.Arm.Inv

namespace VG.Proof.Rsa.Arm.Inv
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.Keys.Inv
open VG.Proof.X25519.Arm
open VG.Proof.Bignum.Arm (subRow_ok selectAliasRow_ok copyWords_ok zero_ok)
open VG.Proof.Rsa.Arm.Keys (wp_ldrSlot)

/-- The words of `sel1` and `copy1`: `k`, or `k + 1`. -/
abbrev len1 (k : Nat) (low : Bool) : Nat := if low then k else k + 1

theorem cnt1_ok {s : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk s B Z W k N) {rest : List Instr}
    {Q : State → Prop} (kk : ∀ t, Upd s t .lr (BitVec.ofNat 32 (k + 1)) → WP isa (.block rest) t Q) :
    WP isa (.block (cnt1 :: rest)) s Q :=
  wp_dp (op2_imm (by decide)) fun t u => kk t (by
    have e : dpVal .add (s.gpr .r9) 1 = BitVec.ofNat 32 (k + 1) := by
      rw [dpVal, h.r9, BitVec.ofNat_add]; rfl
    exact e ▸ u)

theorem cntL_ok {s : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk s B Z W k N) (low : Bool)
    {rest : List Instr} {Q : State → Prop}
    (kk : ∀ t, Upd s t .lr (BitVec.ofNat 32 (len1 k low)) → WP isa (.block rest) t Q) :
    WP isa (.block ((if low then Instr.mov .lr (.reg .r9) else cnt1) :: rest)) s Q := by
  cases low
  · exact cnt1_ok h kk
  · exact wp_mov (op2_reg _ _) fun t u => kk t (by rw [h.r9] at u; exact u)

/-- `sub1 o a b`: `[o] = [a] - [b]`, `k + 1` words, the borrow in `r11`. -/
theorem sub1_ok {s : State} {B : BitVec 32} {Z W k N o a b : Nat} (h : Gk s B Z W k N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (hoa : o ≠ a) (hob : o ≠ b) :
    WP isa (sub1 o a b) s fun t => Gk t B Z W k N ∧ Keep B W [o] [] s.mem t.mem ∧
      nk t.mem B W o (k + 1) + nk s.mem B W b (k + 1) =
        nk s.mem B W a (k + 1) + 2 ^ (32 * (k + 1)) * (t.gpr .r11).toNat ∧
      (t.gpr .r11).toNat ≤ 1 ∧ Rest opRegs s t := by
  rw [sub1, WP.seq_iff]
  refine h.ptr3_ok (o := o) (a := a) (b := b) (by omega) (by omega) (by omega) fun s3 p0 p10 p12 r3 m3 h3 => ?_
  refine cnt1_ok h3 fun s4 u4 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u5 => WP.block_nil ?_
  have hu : Gk u B Z W k N := (h3.rest (u4.rest (ws := [.lr]) (by simp))).rest (u5.rest (ws := [.r11]) (by simp))
  have mu : u.mem = s.mem := u5.mem.trans (u4.mem.trans m3)
  have restU : Rest opRegs s u :=
    (r3.mono (by simp)).trans ((u4.rest (by simp)).trans (u5.rest (by simp)))
  refine WP.mono (subRow_ok u (hu.subCtx ho ha hb hoa hob (L := k + 1) (by have := h.kle; omega)) (by omega)
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p0])
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p10])
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p12])
    (by rw [u5.other _ (by decide), u4.gpr])
    (by rw [u5.gpr]; decide)) ?_
  intro t inv
  have v := inv.value
  rw [u5.gpr, mu] at v
  refine ⟨hu.rest inv.rest, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero, mu] using inv.outside)
      (by simp only [S]; have := h.kle; omega) (by simp), ?_, inv.borrow, restU.trans (inv.rest.mono (by simp))⟩
  simpa using v

/-- `sel1 o a b low`: `[o] = [b]` if `r11` is 1, `[a]` if it is 0 (`o` may be `a` or `b`). -/
theorem sel1_ok {s : State} {B : BitVec 32} {Z W k N o a b : Nat} (low : Bool) (h : Gk s B Z W k N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (bit : (s.gpr .r11).toNat ≤ 1) :
    WP isa (sel1 o a b low) s fun t => Gk t B Z W k N ∧ Keep B W [o] [] s.mem t.mem ∧
      nk t.mem B W o (len1 k low) =
        (if (s.gpr .r11).toNat = 0 then nk s.mem B W a (len1 k low) else nk s.mem B W b (len1 k low)) ∧
      Rest opRegs s t ∧ Outside (State.addr B) (arr W o) (4 * len1 k low) s.mem t.mem := by
  rw [sel1, WP.seq_iff]
  refine h.ptr3_ok (o := o) (a := a) (b := b) (by omega) (by omega) (by omega) fun s3 p0 p10 p12 r3 m3 h3 => ?_
  refine cntL_ok h3 low fun u u4 => WP.block_nil ?_
  have hu : Gk u B Z W k N := h3.rest (u4.rest (ws := [.lr]) (by simp))
  have mu : u.mem = s.mem := u4.mem.trans m3
  have restU : Rest opRegs s u := (r3.mono (by simp)).trans (u4.rest (by simp))
  have b11 : u.gpr .r11 = s.gpr .r11 := (u4.other _ (by decide)).trans (r3.gpr _ (by decide))
  have hL : len1 k low ≤ W + 2 := by have := h.kle; simp only [len1]; split <;> omega
  have hL0 : 0 < len1 k low := by have := h.kpos; simp only [len1]; split <;> omega
  refine WP.mono (selectAliasRow_ok u (hu.selCtx ho ha hb hL) hL0
    (by rw [u4.other _ (by decide), p0]) (by rw [u4.other _ (by decide), p10])
    (by rw [u4.other _ (by decide), p12]) u4.gpr (by rw [b11]; exact bit)) ?_
  intro t inv
  have v := inv.value
  rw [b11, mu] at v
  exact ⟨hu.rest inv.rest, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero, mu] using inv.outside)
      (by simp only [S]; omega) (by simp), v, restU.trans (inv.rest.mono (by simp)), by rw [← mu]; exact inv.outside⟩

/-- `copy1 o a low`: `[o] = [a]`. -/
theorem copy1_ok {s : State} {B : BitVec 32} {Z W k N o a : Nat} (low : Bool) (h : Gk s B Z W k N)
    (ho : o < N) (ha : a < N) (hN : N ≤ 256) (hoa : o ≠ a) :
    WP isa (copy1 o a low) s fun t => Gk t B Z W k N ∧ Keep B W [o] [] s.mem t.mem ∧
      nk t.mem B W o (len1 k low) = nk s.mem B W a (len1 k low) ∧ Rest opRegs s t ∧
      Outside (State.addr B) (arr W o) (4 * len1 k low) s.mem t.mem := by
  rw [copy1, WP.seq_iff]
  refine h.ptr3_ok (o := o) (a := a) (b := a) (by omega) (by omega) (by omega) fun s3 p0 p10 p12 r3 m3 h3 => ?_
  refine cntL_ok h3 low fun s4 u4 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u5 => WP.block_nil ?_
  have hu : Gk u B Z W k N := (h3.rest (u4.rest (ws := [.lr]) (by simp))).rest (u5.rest (ws := [.r11]) (by simp))
  have mu : u.mem = s.mem := u5.mem.trans (u4.mem.trans m3)
  have restU : Rest opRegs s u :=
    (r3.mono (by simp)).trans ((u4.rest (by simp)).trans (u5.rest (by simp)))
  have hL : len1 k low ≤ W + 2 := by have := h.kle; simp only [len1]; split <;> omega
  have hL0 : 0 < len1 k low := by have := h.kpos; simp only [len1]; split <;> omega
  refine WP.mono (copyWords_ok u (hu.subCtx ho ha ha hoa hoa hL) hL0
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p0])
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p10])
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p12])
    (by rw [u5.other _ (by decide), u4.gpr])) ?_
  intro t inv
  have v := inv.value
  rw [mu] at v
  refine ⟨hu.rest inv.rest, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero, mu] using inv.outside)
      (by simp only [S]; omega) (by simp), ?_, restU.trans (inv.rest.mono (by simp)), by rw [← mu]; exact inv.outside⟩
  change val32 _ _ _ _ = _; rw [v]; split <;> rfl

/-- `[o] = 0` for `L` words from `r0 = [o]`, `lr = L`, `r3 = 0`. -/
theorem zeroAt_ok {s : State} {B : BitVec 32} {Z W k N o L : Nat} (h : Gk s B Z W k N) (ho : o < N)
    (hL : L ≤ W + 2) (hL0 : 0 < L) (p0 : s.gpr .r0 = B + BitVec.ofNat 32 (arr W o))
    (pl : s.gpr .lr = BitVec.ofNat 32 L) (z3 : s.gpr .r3 = 0) :
    WP isa zero s fun t => Gk t B Z W k N ∧ Keep B W [o] [] s.mem t.mem ∧ nk t.mem B W o L = 0 ∧
      Rest [.r0, .lr] s t := by
  refine WP.mono (zero_ok s (h.zeroCtx ho hL) hL0 p0 pl z3) fun t inv => ?_
  exact ⟨h.rest inv.rest, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using inv.outside)
    (by simp only [S]; omega) (by simp), inv.value, inv.rest⟩

theorem zero1_ok {s : State} {B : BitVec 32} {Z W k N o : Nat} (h : Gk s B Z W k N) (ho : o < N)
    (hN : N ≤ 256) :
    WP isa (zero1 o) s fun t => Gk t B Z W k N ∧ Keep B W [o] [] s.mem t.mem ∧
      nk t.mem B W o (k + 1) = 0 ∧ Rest opRegs s t := by
  rw [zero1, WP.seq_iff]
  refine h.ptr_ok (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  refine cnt1_ok h1 fun s2 u2 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u3 => WP.block_nil ?_
  have hu : Gk u B Z W k N := (h1.rest (u2.rest (ws := [.lr]) (by simp))).rest (u3.rest (ws := [.r3]) (by simp))
  have mu : u.mem = s.mem := u3.mem.trans (u2.mem.trans m1)
  refine WP.mono (zeroAt_ok hu ho (by have := h.kle; omega) (by omega)
    (by rw [u3.other _ (by decide), u2.other _ (by decide), p1]) (by rw [u3.other _ (by decide), u2.gpr])
    u3.gpr) fun t ⟨ht, kt, vt, rt⟩ => ⟨ht, mu ▸ kt, vt, ((r1.mono (by simp)).trans ((u2.rest (by simp)).trans
      (u3.rest (by simp)))).trans (rt.mono (by simp))⟩

theorem zeroW_ok {s : State} {B : BitVec 32} {Z W k N o : Nat} (h : Gk s B Z W k N) (ho : o < N)
    (hN : N ≤ 256) :
    WP isa (zeroW o) s fun t => Gk t B Z W k N ∧ Keep B W [o] [] s.mem t.mem ∧
      nk t.mem B W o W = 0 ∧ Rest opRegs s t := by
  rw [zeroW, WP.seq_iff]
  refine h.ptr_ok (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u4 => WP.block_nil ?_
  have hu : Gk u B Z W k N := ((h1.rest (u2.rest (ws := [.lr]) (by simp))).rest (u3.rest (ws := [.lr]) (by simp))).rest
    (u4.rest (ws := [.r3]) (by simp))
  have mu : u.mem = s.mem := u4.mem.trans (u3.mem.trans (u2.mem.trans m1))
  have hW : 0 < W := Nat.lt_of_lt_of_le h.kpos h.kle
  have cnt : u.gpr .lr = BitVec.ofNat 32 W := by
    rw [u4.other _ (by decide), u3.gpr, dpVal, u2.gpr, h1.r7]
    apply BitVec.eq_of_toNat_eq
    have := h.wle
    rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (2 : BitVec 32).toNat = 2 from rfl]
    simp only [S, Nat.shiftRight_eq_div_pow]
    omega
  refine WP.mono (zeroAt_ok hu ho (by omega) hW
    (by rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), p1]) cnt u4.gpr)
    fun t ⟨ht, kt, vt, rt⟩ => ⟨ht, mu ▸ kt, vt, ((r1.mono (by simp)).trans ((u2.rest (by simp)).trans
      ((u3.rest (by simp)).trans (u4.rest (by simp))))).trans (rt.mono (by simp))⟩

/-! ## Words at a byte of an array -/

/-- The word at byte `d` of array `j`. -/
abbrev aw (m : Mem) (B : BitVec 32) (W j d : Nat) : Nat := w32 m (State.addr B) (arr W j + d)

theorem Gk.arrAddr {s : State} {B : BitVec 32} {Z W k N j d : Nat} (h : Gk s B Z W k N) (hj : j < N)
    {r : Reg} {o : Nat} (hr : s.gpr r = B + BitVec.ofNat 32 (arr W j + d))
    (ho : d + o + 4 ≤ S W) :
    State.addr (s.gpr r + BitVec.ofNat 32 o) = off (State.addr B) (arr W j + d + o) := by
  have := h.arr_fit hj
  rw [hr, Offset.add_add]
  exact h.addr (by omega)

/-- The sign of a word, as a bit. -/
theorem sign_bit (x : BitVec 32) : (x >>> 31).toNat = if 2 ^ 31 ≤ x.toNat then 1 else 0 := by
  rw [toNat_shr]; have := x.isLt; split <;> omega

/-- The magnitude of a word. -/
theorem abs_word (x : BitVec 32) :
    ((x ^^^ ((x >>> 31) - ((x >>> 31) <<< 1))) - ((x >>> 31) - ((x >>> 31) <<< 1))).toNat = x.toInt.natAbs := by
  have hs := sign_bit x
  rw [BitVec.toInt_eq_toNat_cond]
  have hx := x.isLt
  by_cases h : 2 ^ 31 ≤ x.toNat
  · have e1 : x >>> 31 = 1 := by apply BitVec.eq_of_toNat_eq; rw [hs]; simp [h]
    have ns : (x ^^^ BitVec.allOnes 32) - BitVec.allOnes 32 = -x := by
      rw [BitVec.xor_allOnes, BitVec.neg_eq_not_add]
      have : BitVec.allOnes 32 = -1 := by decide
      rw [this, BitVec.sub_neg]; rfl
    rw [e1, show (1 : BitVec 32) - (1 : BitVec 32) <<< 1 = BitVec.allOnes 32 by decide, ns]
    rw [BitVec.toNat_neg]
    have : ¬ 2 * x.toNat < 2 ^ 32 := by omega
    simp only [this, ↓reduceIte]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · have e1 : x >>> 31 = 0 := by apply BitVec.eq_of_toNat_eq; rw [hs]; simp [h]
    have z : (x ^^^ 0) - 0 = x := by simp
    rw [e1, show (0 : BitVec 32) - (0 : BitVec 32) <<< 1 = 0 by decide, z]
    have : 2 * x.toNat < 2 ^ 32 := by omega
    simp only [this, ↓reduceIte]
    omega

/-- `signOf c`: `r11` := the sign bit of the coefficient's word. -/
theorem signOf_ok {s : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk s B Z W k N) (c : Coef)
    (hc : c.arr < N) (hN : N ≤ 256) (hoff : c.off + 4 ≤ S W) (ho : c.off < 4096) {rest : List Instr}
    {Q : State → Prop}
    (kk : ∀ t, (t.gpr .r11).toNat = (if 2 ^ 31 ≤ aw s.mem B W c.arr c.off then 1 else 0) →
      t.mem = s.mem → Rest [.r1, .r11, .r12] s t → Gk t B Z W k N → WP isa (.block rest) t Q) :
    WP isa (.block (signOf c ++ rest)) s Q := by
  rw [signOf, List.append_assoc]
  refine h.ptr_ok (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  have fit := h.arr_fit hc
  refine wp_ldr ho (h1.arrAddr hc (d := 0) (by simpa using p1) (by omega))
    (h1.read (by omega)) fun s2 u2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t u3 => kk t ?_ (by rw [u3.mem, u2.mem, m1])
    ((r1.mono (by simp)).trans ((u2.rest (by simp)).trans (u3.rest (by simp))))
    ((h1.rest (u2.rest (ws := [.r1]) (by simp))).rest (u3.rest (ws := [.r11]) (by simp)))
  rw [u3.gpr, u2.gpr, sign_bit, m1]; simp

/-- The magnitude of a coefficient. -/
abbrev absC (m : Mem) (B : BitVec 32) (W : Nat) (c : Coef) : Nat :=
  (m.readW (off (State.addr B) (arr W c.arr + c.off)) 32).toInt.natAbs

/-- `absOf c`: `r1` := the magnitude of the coefficient's word, `r11 := 0`. -/
theorem absOf_ok {s : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk s B Z W k N) (c : Coef)
    (hc : c.arr < N) (hN : N ≤ 256) (hoff : c.off + 4 ≤ S W) (ho : c.off < 4096) {rest : List Instr}
    {Q : State → Prop}
    (kk : ∀ t, (t.gpr .r1).toNat = absC s.mem B W c →
      t.gpr .r11 = 0 → t.mem = s.mem → Rest [.r1, .r2, .r11, .r12] s t → Gk t B Z W k N →
      WP isa (.block rest) t Q) :
    WP isa (.block (absOf c ++ rest)) s Q := by
  rw [absOf, List.append_assoc]
  refine h.ptr_ok (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  have fit := h.arr_fit hc
  refine wp_ldr ho (h1.arrAddr hc (d := 0) (by simpa using p1) (by omega))
    (h1.read (by omega)) fun s2 u2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s4 u4 => ?_
  refine wp_dp (op2_reg _ _) fun s5 u5 => ?_
  refine wp_dp (op2_reg _ _) fun s6 u6 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u7 => kk t ?_ u7.gpr ?_ ?_ ?_
  · have x2 : s2.gpr .r1 = s.mem.readW (off (State.addr B) (arr W c.arr + 0 + c.off)) 32 := by rw [u2.gpr, m1]
    have e3 : s3.gpr .r11 = s2.gpr .r1 >>> 31 := u3.gpr
    have e4 : s4.gpr .r2 = (s2.gpr .r1 >>> 31) - ((s2.gpr .r1 >>> 31) <<< 1) := by
      rw [u4.gpr, dpVal, e3]
    have e5 : s5.gpr .r1 = s2.gpr .r1 ^^^ ((s2.gpr .r1 >>> 31) - ((s2.gpr .r1 >>> 31) <<< 1)) := by
      rw [u5.gpr, dpVal, u4.other .r1 (by decide), u3.other .r1 (by decide), e4]
    have e6 : t.gpr .r1 = (s2.gpr .r1 ^^^ ((s2.gpr .r1 >>> 31) - ((s2.gpr .r1 >>> 31) <<< 1))) -
        ((s2.gpr .r1 >>> 31) - ((s2.gpr .r1 >>> 31) <<< 1)) := by
      rw [u7.other _ (by decide), u6.gpr, dpVal, e5, u5.other .r2 (by decide), e4]
    rw [e6, abs_word, x2]
    simp only [Nat.add_zero]
  · rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, m1]
  · exact (r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans
      ((u5.rest (by simp)).trans ((u6.rest (by simp)).trans (u7.rest (by simp)))))))
  · exact (((((h1.rest (u2.rest (ws := [.r1]) (by simp))).rest (u3.rest (ws := [.r11]) (by simp))).rest
      (u4.rest (ws := [.r2]) (by simp))).rest (u5.rest (ws := [.r1]) (by simp))).rest
      (u6.rest (ws := [.r1]) (by simp))).rest (u7.rest (ws := [.r11]) (by simp))

/-- `macRow` on arrays, from its pointers and count set. -/
theorem macAt_ok {s : State} {B : BitVec 32} {Z W k N acc src : Nat} (h : Gk s B Z W k N)
    (ha : acc < N) (hs : src < N) (hne : acc ≠ src)
    (p0 : s.gpr .r0 = B + BitVec.ofNat 32 (arr W acc)) (p12 : s.gpr .r12 = B + BitVec.ofNat 32 (arr W src))
    (pl : s.gpr .lr = BitVec.ofNat 32 (k + 1)) :
    WP isa macRow s fun t => Gk t B Z W k N ∧ Keep B W [acc] [] s.mem t.mem ∧
      nk t.mem B W acc (k + 1) + 2 ^ (32 * (k + 1)) * (t.gpr .r11).toNat =
        nk s.mem B W acc (k + 1) + (s.gpr .r1).toNat * nk s.mem B W src (k + 1) + (s.gpr .r11).toNat ∧
      Rest opRegs s t := by
  refine WP.mono (macRow_ok s (h.rowCtx ha hs hne (L := k + 1) (by have := h.kle; omega)) (by omega) p0 p12 pl)
    fun t ⟨o, v, r⟩ => ⟨h.rest r, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using o)
      (by simp only [S]; have := h.kle; omega) (by simp), v, r.mono (by simp)⟩

/-- `mac1 acc src c`: `[acc] += |c| [src]`, `k + 1` words, the carry out in `r11`. -/
theorem mac1_ok {s : State} {B : BitVec 32} {Z W k N acc src : Nat} (c : Coef) (h : Gk s B Z W k N)
    (ha : acc < N) (hs : src < N) (hne : acc ≠ src) (hc : c.arr < N) (hN : N ≤ 256)
    (hoff : c.off + 4 ≤ S W) (ho : c.off < 4096) :
    WP isa (mac1 acc src c) s fun t => Gk t B Z W k N ∧ Keep B W [acc] [] s.mem t.mem ∧
      nk t.mem B W acc (k + 1) + 2 ^ (32 * (k + 1)) * (t.gpr .r11).toNat =
        nk s.mem B W acc (k + 1) + absC s.mem B W c * nk s.mem B W src (k + 1) ∧
      Rest opRegs s t := by
  rw [mac1, WP.seq_iff, List.append_assoc, List.append_assoc]
  refine h.ptr_ok (r := .r0) (j := acc) (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  refine absOf_ok h1 c hc hN hoff ho fun s2 a2 z2 m2 r2 h2 => ?_
  refine h2.ptr_ok (r := .r12) (j := src) (by decide) (by omega) fun s3 p3 r3 m3 h3 => ?_
  refine cnt1_ok h3 fun u u4 => WP.block_nil ?_
  have hu : Gk u B Z W k N := h3.rest (u4.rest (ws := [.lr]) (by simp))
  have mu : u.mem = s.mem := u4.mem.trans (m3.trans (m2.trans m1))
  refine WP.mono (macAt_ok hu ha hs hne
    (by rw [u4.other _ (by decide), r3.gpr _ (by decide), r2.gpr _ (by decide), p1])
    (by rw [u4.other _ (by decide), p3]) u4.gpr) fun t ⟨ht, kt, vt, rt⟩ => ?_
  have x1 : u.gpr .r1 = s2.gpr .r1 := (u4.other _ (by decide)).trans (r3.gpr _ (by decide))
  have c0 : u.gpr .r11 = 0 := (u4.other _ (by decide)).trans ((r3.gpr _ (by decide)).trans z2)
  rw [x1, c0, a2, mu, m1] at vt
  refine ⟨ht, mu ▸ kt, by rw [Nat.add_zero] at vt; exact vt, ?_⟩
  exact ((r1.mono (by simp)).trans ((r2.mono (by simp)).trans ((r3.mono (by simp)).trans
    (u4.rest (by simp))))).trans rt

/-- `shr1 o a`: `[o] = [a] >> 30`, signed, `k + 1` words. -/
theorem shr1_ok {s : State} {B : BitVec 32} {Z W k N o a : Nat} (h : Gk s B Z W k N)
    (ho : o < N) (ha : a < N) (hN : N ≤ 256) (hoa : o ≠ a) :
    WP isa (shr1 o a) s fun t => Gk t B Z W k N ∧ Keep B W [o] [] s.mem t.mem ∧
      nk t.mem B W o (k + 1) =
        ((nk s.mem B W a (k + 1) + 2 ^ (32 * (k + 1)) *
          (if 2 ^ 31 ≤ aw s.mem B W a (4 * k) then 2 ^ 32 - 1 else 0)) / 2 ^ 30) % 2 ^ (32 * (k + 1)) ∧
      Rest opRegs s t := by
  rw [shr1, WP.seq_iff, List.append_assoc]
  refine h.ptr_ok (r := .r0) (j := o) (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  refine h1.ptr_ok (r := .r12) (j := a) (by decide) (by omega) fun s2 p2 r2 m2 h2 => ?_
  refine wp_mov (op2_reg _ _) fun u u3 => WP.block_nil ?_
  have hu : Gk u B Z W k N := h2.rest (u3.rest (ws := [.lr]) (by simp))
  have mu : u.mem = s.mem := u3.mem.trans (m2.trans m1)
  refine WP.mono (shr30_ok u (hu.shrCtx ho ha hoa (L := k) (by have := h.kle; omega)) h.kpos
    (by rw [u3.other _ (by decide), r2.gpr _ (by decide), p1]) (by rw [u3.other _ (by decide), p2])
    (by rw [u3.gpr, h2.r9])) fun t ⟨o', v, r⟩ => ?_
  rw [mu] at v o'
  refine ⟨hu.rest r, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using o')
    (by simp only [S]; have := h.kle; omega) (by simp), v, ?_⟩
  exact ((r1.mono (by simp)).trans ((r2.mono (by simp)).trans (u3.rest (by simp)))).trans (r.mono (by simp))

/-- The digit of `redc`. -/
abbrev digit (lo iv : Nat) : Nat := lo * iv % 2 ^ 32 % 2 ^ 30

theorem bic_digit (x y : BitVec 32) : ((x * y) &&& ~~~(0xC0000000 : BitVec 32)).toNat = digit x.toNat y.toNat := by
  have e : ~~~(0xC0000000 : BitVec 32) = BitVec.ofNat 32 (2 ^ 30 - 1) := by decide
  rw [e, BitVec.toNat_and, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [show (2 ^ 30 - 1) % 2 ^ 32 = 2 ^ 30 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- `redc acc`: `[acc] += q [bP]` for the digit `q` of `[acc]`'s low word and the header word `sB`. -/
theorem redc_ok {s : State} {B : BitVec 32} {Z W k N acc : Nat} (h : Gk s B Z W k N)
    (ha : acc < N) (hp : bP < N) (hne : acc ≠ bP) (hN : N ≤ 256) :
    WP isa (redc acc) s fun t => Gk t B Z W k N ∧ Keep B W [acc] [] s.mem t.mem ∧
      nk t.mem B W acc (k + 1) + 2 ^ (32 * (k + 1)) * (t.gpr .r11).toNat =
        nk s.mem B W acc (k + 1) +
          digit (aw s.mem B W acc 0) (slot s.mem B sB) * nk s.mem B W bP (k + 1) ∧
      Rest opRegs s t := by
  rw [redc, WP.seq_iff]; simp only [List.append_assoc, List.cons_append, List.nil_append]
  have fit := h.arr_fit ha
  have hz := h.fits
  refine h.ptr_ok (r := .r0) (j := acc) (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  refine wp_ldr (by decide) (h1.arrAddr ha (d := 0) (by simpa using p1) (by simp only [S]; omega))
    (h1.read (by simp only [S] at fit; omega)) fun s2 u2 => ?_
  have hsl : sB + 4 ≤ Z := by have : hdr ≤ arr W 0 := Nat.le_add_right _ _; have := arr_mono (w := W) (Nat.zero_le N); simp only [sB, hdr] at *; omega
  refine wp_ldr (a := off (State.addr B) sB) (by decide) (by rw [u2.other _ (by decide), h1.r8]; exact h1.addr (by omega))
    (by rw [u2.rd, u2.wr]; exact h1.read hsl) fun s3 u3 => ?_
  refine VG.Proof.X25519.Arm.wp_mul fun s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun s6 u6 => ?_
  have h6 : Gk s6 B Z W k N := (((h1.rest (u2.rest (ws := [.r1]) (by simp))).rest (u3.rest (ws := [.r2]) (by simp))).rest
    (u4.rest (ws := [.r1]) (by simp))).rest (u5.rest (ws := [.r1]) (by simp)) |>.rest (u6.rest (ws := [.r11]) (by simp))
  refine h6.ptr_ok (r := .r12) (j := bP) (by decide) (by omega) fun s7 p7 r7 m7 h7 => ?_
  refine cnt1_ok h7 fun u u8 => WP.block_nil ?_
  have hu : Gk u B Z W k N := h7.rest (u8.rest (ws := [.lr]) (by simp))
  have mu : u.mem = s.mem := by rw [u8.mem, m7, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, m1]
  have q : (u.gpr .r1).toNat = digit (aw s.mem B W acc 0) (slot s.mem B sB) := by
    rw [u8.other _ (by decide), r7.gpr _ (by decide), u6.other _ (by decide), u5.gpr, dpVal, u4.gpr,
      u3.other .r1 (by decide), u3.gpr, u2.gpr, u2.mem, m1, bic_digit]
  have c0 : u.gpr .r11 = 0 := by rw [u8.other _ (by decide), r7.gpr _ (by decide), u6.gpr]
  refine WP.mono (macAt_ok hu ha hp hne
    (by rw [u8.other _ (by decide), r7.gpr _ (by decide), u6.other _ (by decide), u5.other _ (by decide),
      u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), p1])
    (by rw [u8.other _ (by decide), p7]) u8.gpr) fun t ⟨ht, kt, vt, rt⟩ => ?_
  rw [q, c0, mu] at vt
  refine ⟨ht, mu ▸ kt, by rw [Nat.add_zero] at vt; exact vt, ?_⟩
  exact ((r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans
    ((u5.rest (by simp)).trans ((u6.rest (by simp)).trans ((r7.mono (by simp)).trans (u8.rest (by simp))))))))).trans rt

/-! ## Composites -/

/-- The sign of a coefficient. -/
abbrev sgnC (m : Mem) (B : BitVec 32) (W : Nat) (c : Coef) : Prop := 2 ^ 31 ≤ aw m B W c.arr c.off

theorem Keep.aw {B : BitVec 32} {W : Nat} {js : List Nat} {m m' : Mem} (h : Keep B W js [] m m') {j d : Nat}
    (hd : d + 4 ≤ S W) (hj : ∀ x ∈ js, x ≠ j) (fit : arr W j + S W ≤ 2 ^ 64) : aw m' B W j d = aw m B W j d := by
  have := Outs.val32 (k := 1) (d := arr W j + d) h (fun r hr => ?_) (by omega)
  · simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨x, hx, rfl⟩ | ⟨e, he, rfl⟩
  · have := arr_disj (w := W) (hj x hx); dsimp only; omega
  · simp at he

/-- `cneg base t x c`: `[t] = [base] - [x]` (modulo `2^(32 (k + 1))`) where `c` is negative, else `[x]`. -/
theorem cneg_ok {s : State} {B : BitVec 32} {Z W k N base t x : Nat} (c : Coef) (h : Gk s B Z W k N)
    (hb : base < N) (ht : t < N) (hx : x < N) (hc : c.arr < N) (hN : N ≤ 256) (htb : t ≠ base) (htx : t ≠ x)
    (htc : t ≠ c.arr) (hoff : c.off + 4 ≤ S W) (ho : c.off < 4096) :
    WP isa (cneg base t x c) s fun u => Gk u B Z W k N ∧ Keep B W [t] [] s.mem u.mem ∧
      (sgnC s.mem B W c → ∃ b, nk u.mem B W t (k + 1) + nk s.mem B W x (k + 1) =
        nk s.mem B W base (k + 1) + 2 ^ (32 * (k + 1)) * b) ∧
      (¬ sgnC s.mem B W c → nk u.mem B W t (k + 1) = nk s.mem B W x (k + 1)) ∧ Rest opRegs s u := by
  simp only [cneg, seqs]
  rw [WP.seq_iff]
  refine WP.mono (sub1_ok h ht hb hx hN htb htx) fun s1 ⟨h1, k1, v1, _, r1⟩ => ?_
  rw [WP.seq_iff, ← List.append_nil (signOf c)]
  refine signOf_ok h1 c hc hN hoff ho fun s2 b2 m2 r2 h2 => WP.block_nil ?_
  have fx := h.fit64 hx
  have fc := h.fit64 hc
  have cw : aw s1.mem B W c.arr c.off = aw s.mem B W c.arr c.off := Keep.aw k1 hoff (by simpa using htc) fc
  have xw : nk s1.mem B W x (k + 1) = nk s.mem B W x (k + 1) :=
    Keep.nk k1 (by have := h.kle; omega) (by simpa using htx) (by simp) fx
  refine WP.mono (sel1_ok false h2 ht hx ht hN (by rw [b2]; split <;> decide)) fun u ⟨hu, ku, vu, ru, _⟩ => ?_
  rw [b2, m2] at vu
  simp only [len1, Bool.false_eq_true, ↓reduceIte] at vu
  simp only [cw, xw] at vu
  refine ⟨hu, k1.trans (m2 ▸ ku), fun hs => ?_, fun hs => ?_, r1.trans ((r2.mono (by simp)).trans ru)⟩
  · simp only [hs, ↓reduceIte, Nat.one_ne_zero] at vu
    exact ⟨(s1.gpr .r11).toNat, by rw [vu]; exact v1⟩
  · simp only [hs, ↓reduceIte] at vu
    exact vu

theorem absC_congr {m m' : Mem} {B : BitVec 32} {W : Nat} {c : Coef}
    (h : aw m' B W c.arr c.off = aw m B W c.arr c.off) : absC m' B W c = absC m B W c := by
  simp only [absC]; rw [BitVec.eq_of_toNat_eq h]

/-- What `cneg` leaves in `T`: `Bs - X` modulo `2^(32 L)` if `sg`, else `X`. -/
def CN (sg : Prop) (T X Bs L : Nat) : Prop := (sg → ∃ b, T + X = Bs + 2 ^ (32 * L) * b) ∧ (¬ sg → T = X)

/-- `lin base acc x y c₁ c₂`: `[acc] = |c₁| T₁ + |c₂| T₂` modulo `2^(32 (k + 1))`, `T₁` and `T₂` `cneg`'s of
`[x]` and `[y]`. -/
theorem lin_ok {s : State} {B : BitVec 32} {Z W k N base acc x y : Nat} (c₁ c₂ : Coef) (h : Gk s B Z W k N)
    (hN : 15 ≤ N) (hN' : N ≤ 256) (hb : base < N) (ha : acc < N) (hx : x < N) (hy : y < N)
    (h1 : c₁.arr < N) (h2 : c₂.arr < N)
    (hd : ∀ j ∈ [base, acc, x, y, c₁.arr, c₂.arr], j ≠ bT1 ∧ j ≠ bT2) (hac : acc ≠ c₁.arr ∧ acc ≠ c₂.arr)
    (o1 : c₁.off + 4 ≤ S W) (o2 : c₂.off + 4 ≤ S W) (o1' : c₁.off < 4096) (o2' : c₂.off < 4096) :
    WP isa (lin base acc x y c₁ c₂) s fun u => Gk u B Z W k N ∧ Keep B W [bT1, bT2, acc] [] s.mem u.mem ∧
      ∃ T₁ T₂ e, CN (sgnC s.mem B W c₁) T₁ (nk s.mem B W x (k + 1)) (nk s.mem B W base (k + 1)) (k + 1) ∧
        CN (sgnC s.mem B W c₂) T₂ (nk s.mem B W y (k + 1)) (nk s.mem B W base (k + 1)) (k + 1) ∧
        T₁ < 2 ^ (32 * (k + 1)) ∧ T₂ < 2 ^ (32 * (k + 1)) ∧
        nk u.mem B W acc (k + 1) + 2 ^ (32 * (k + 1)) * e = absC s.mem B W c₁ * T₁ + absC s.mem B W c₂ * T₂ ∧
      Rest opRegs s u := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hd
  obtain ⟨⟨b1, b2⟩, ⟨a1, a2⟩, ⟨x1, x2⟩, ⟨y1, y2⟩, ⟨c11, c12⟩, ⟨c21, c22⟩⟩ := hd
  have hL : k + 1 ≤ W + 2 := by have := h.kle; omega
  have fit := fun j (hj : j < N) => h.fit64 hj
  simp only [lin, seqs]
  rw [WP.seq_iff]
  have t1 : bT1 < N := Nat.lt_of_lt_of_le (by decide) hN
  have t2 : bT2 < N := Nat.lt_of_lt_of_le (by decide) hN
  refine WP.mono (cneg_ok c₁ h hb t1 hx h1 hN' (Ne.symm b1) (Ne.symm x1) (Ne.symm c11) o1 o1')
    fun s1 ⟨g1, k1, p1, n1, r1⟩ => ?_
  rw [WP.seq_iff]
  have e_by : nk s1.mem B W y (k + 1) = nk s.mem B W y (k + 1) :=
    Keep.nk k1 hL (by simpa using Ne.symm y1) (by simp) (fit _ hy)
  have e_bb : nk s1.mem B W base (k + 1) = nk s.mem B W base (k + 1) :=
    Keep.nk k1 hL (by simpa using Ne.symm b1) (by simp) (fit _ hb)
  have e_c2 : aw s1.mem B W c₂.arr c₂.off = aw s.mem B W c₂.arr c₂.off :=
    Keep.aw k1 o2 (by simpa using Ne.symm c21) (fit _ h2)
  have e_c1 : aw s1.mem B W c₁.arr c₁.off = aw s.mem B W c₁.arr c₁.off :=
    Keep.aw k1 o1 (by simpa using Ne.symm c11) (fit _ h1)
  refine WP.mono (cneg_ok c₂ g1 hb t2 hy h2 hN' (Ne.symm b2) (Ne.symm y2) (Ne.symm c22) o2 o2')
    fun s2 ⟨g2, k2, p2, n2, r2⟩ => ?_
  simp only [sgnC, e_c2, e_by, e_bb] at p2 n2
  have e_t1 : nk s2.mem B W bT1 (k + 1) = nk s1.mem B W bT1 (k + 1) :=
    Keep.nk k2 hL (by decide) (by simp) (fit _ t1)
  have e2_c1 : aw s2.mem B W c₁.arr c₁.off = aw s.mem B W c₁.arr c₁.off :=
    (Keep.aw k2 o1 (by simpa using Ne.symm c12) (fit _ h1)).trans e_c1
  have e2_c2 : aw s2.mem B W c₂.arr c₂.off = aw s.mem B W c₂.arr c₂.off :=
    (Keep.aw k2 o2 (by simpa using Ne.symm c22) (fit _ h2)).trans e_c2
  rw [WP.seq_iff]
  refine WP.mono (zero1_ok g2 ha hN') fun s3 ⟨g3, k3, z3, r3⟩ => ?_
  have e3_t1 : nk s3.mem B W bT1 (k + 1) = nk s1.mem B W bT1 (k + 1) :=
    (Keep.nk k3 hL (by simpa using a1) (by simp) (fit _ t1)).trans e_t1
  have e3_t2 : nk s3.mem B W bT2 (k + 1) = nk s2.mem B W bT2 (k + 1) :=
    Keep.nk k3 hL (by simpa using a2) (by simp) (fit _ t2)
  have e3_c1 : aw s3.mem B W c₁.arr c₁.off = aw s.mem B W c₁.arr c₁.off :=
    (Keep.aw k3 o1 (by simpa using hac.1) (fit _ h1)).trans e2_c1
  have e3_c2 : aw s3.mem B W c₂.arr c₂.off = aw s.mem B W c₂.arr c₂.off :=
    (Keep.aw k3 o2 (by simpa using hac.2) (fit _ h2)).trans e2_c2
  rw [WP.seq_iff]
  refine WP.mono (mac1_ok c₁ g3 ha t1 (Ne.symm a1).symm h1 hN' o1 o1') fun s4 ⟨g4, k4, v4, r4⟩ => ?_
  have e4_t2 : nk s4.mem B W bT2 (k + 1) = nk s2.mem B W bT2 (k + 1) :=
    (Keep.nk k4 hL (by simpa using a2) (by simp) (fit _ t2)).trans e3_t2
  have e4_c2 : aw s4.mem B W c₂.arr c₂.off = aw s.mem B W c₂.arr c₂.off :=
    (Keep.aw k4 o2 (by simpa using hac.2) (fit _ h2)).trans e3_c2
  refine WP.mono (mac1_ok c₂ g4 ha t2 (Ne.symm a2).symm h2 hN' o2 o2') fun u ⟨gu, ku, vu, ru⟩ => ?_
  refine ⟨gu, ((k1.mono).trans (k2.mono)).trans ((k3.mono.trans k4.mono).trans ku.mono), nk s1.mem B W bT1 (k + 1),
    nk s2.mem B W bT2 (k + 1), (s4.gpr .r11).toNat + (u.gpr .r11).toNat, ⟨p1, n1⟩, ⟨p2, n2⟩,
    val32_lt _ _ _ _, val32_lt _ _ _ _, ?_, r1.trans (r2.trans (r3.trans (r4.trans ru)))⟩
  rw [absC_congr e3_c1, e3_t1, z3] at v4
  rw [absC_congr e4_c2, e4_t2] at vu
  rw [Nat.mul_add, ← Nat.add_assoc]
  generalize 2 ^ (32 * (k + 1)) * (s4.gpr .r11).toNat = X at *
  generalize 2 ^ (32 * (k + 1)) * (u.gpr .r11).toNat = Y at *
  generalize absC s.mem B W c₁ * nk s1.mem B W bT1 (k + 1) = A₁ at *
  generalize absC s.mem B W c₂ * nk s2.mem B W bT2 (k + 1) = A₂ at *
  omega

theorem val32_low (m : Mem) (base : Addr) (d k : Nat) : val32 m base d k = val32 m base d (k + 1) % 2 ^ (32 * k) := by
  rw [val32_succ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val32_lt _ _ _ _)]

theorem len1_low (m : Mem) (B : BitVec 32) (W j k : Nat) (low : Bool) :
    nk m B W j (len1 k low) = nk m B W j (k + 1) % 2 ^ (32 * len1 k low) := by
  cases low
  · simp only [len1, Bool.false_eq_true, ↓reduceIte]; rw [Nat.mod_eq_of_lt (val32_lt _ _ _ _)]
  · simp only [len1, ↓reduceIte]; exact val32_low _ _ _ _

/-- `csub1 o a low`: `[o] = [a] - m` if `[a] ≥ m = [bP]`, else `[a]`. -/
theorem csub1_ok {s : State} {B : BitVec 32} {Z W k N o a : Nat} (low : Bool) (h : Gk s B Z W k N)
    (hN : 15 ≤ N) (hN' : N ≤ 256) (ho : o < N) (ha : a < N) (haT : a ≠ bT1) :
    WP isa (csub1 o a low) s fun u => Gk u B Z W k N ∧ Keep B W [bT1, o] [] s.mem u.mem ∧
      nk u.mem B W o (len1 k low) = (if nk s.mem B W a (k + 1) < nk s.mem B W bP (k + 1) then
        nk s.mem B W a (k + 1) else nk s.mem B W a (k + 1) - nk s.mem B W bP (k + 1)) % 2 ^ (32 * len1 k low) ∧
      Rest opRegs s u ∧ Outs (State.addr B) [(arr W o, 4 * len1 k low), (arr W bT1, S W)] s.mem u.mem := by
  have t1 : bT1 < N := Nat.lt_of_lt_of_le (by decide) hN
  have tp : bP < N := Nat.lt_of_lt_of_le (by decide) hN
  have hL : k + 1 ≤ W + 2 := by have := h.kle; omega
  simp only [csub1, seqs]
  rw [WP.seq_iff]
  refine WP.mono (sub1_ok h t1 ha tp hN' (Ne.symm haT) (by decide)) fun s1 ⟨g1, k1, v1, b1, r1⟩ => ?_
  have ea : nk s1.mem B W a (k + 1) = nk s.mem B W a (k + 1) :=
    Keep.nk k1 hL (by simpa using Ne.symm haT) (by simp) (h.fit64 ha)
  refine WP.mono (sel1_ok low g1 ho t1 ha hN' b1) fun u ⟨gu, ku, vu, ru, ou⟩ => ?_
  have out : Outs (State.addr B) [(arr W o, 4 * len1 k low), (arr W bT1, S W)] s.mem u.mem := by
    intro y hy
    have h1 := hy _ (List.mem_cons_self ..)
    have h2 := hy _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    rw [ou y h1]
    refine k1 y fun r hr => ?_
    simp only [ranges, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, List.append_nil, or_false] at hr
    subst hr; exact h2
  refine ⟨gu, k1.mono.trans ku.mono, ?_, r1.trans ru, out⟩
  rw [vu, len1_low s1.mem, len1_low s1.mem, ea]
  have hT := val32_lt s1.mem (State.addr B) (arr W bT1) (k + 1)
  have hA := val32_lt s.mem (State.addr B) (arr W a) (k + 1)
  have hP := val32_lt s.mem (State.addr B) (arr W bP) (k + 1)
  change nk s1.mem B W bT1 (k + 1) < _ at hT
  change nk s.mem B W a (k + 1) < _ at hA
  change nk s.mem B W bP (k + 1) < _ at hP
  generalize 2 ^ (32 * (k + 1)) = M at *
  generalize nk s1.mem B W bT1 (k + 1) = T at *
  generalize nk s.mem B W a (k + 1) = A at *
  generalize nk s.mem B W bP (k + 1) = P at *
  generalize (s1.gpr .r11).toNat = b at *
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
  · have : ¬ A < P := by omega
    simp only [this, ↓reduceIte]
    congr 1; omega
  · have : A < P := by omega
    simp only [this, ↓reduceIte, Nat.one_ne_zero]

end VG.Proof.Rsa.Arm.Inv
