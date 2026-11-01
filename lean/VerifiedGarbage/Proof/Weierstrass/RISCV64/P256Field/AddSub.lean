module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Ops
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.X448.RISCV64.R64.Product
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# P-256's field on RISC-V: sums and differences

`addCore` (`addCore_ok`): the operands' words loaded (`loadAB_ok`), their sum
with carries (below `2p`), reduced by `csub`. `subCore` (`subCore_ok`): their
difference with borrows, and `p` added back under the mask of the borrow, a
word at a time, each stored at `[t2]` (`addPWord_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P256Field

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P256Field
open VG.Proof.X25519.RISCV64 (Ctx Rest)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt clob64 dw_write_self dw_write_other al8 Keeps.rest)

/-- `s'` is `s` but for the registers `rs` and the memory. -/
def Keeps' (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

/-- The words of `[t4]` and `[t5]` in registers. -/
theorem loadAB_ok {W : Addr} {s : State} (hw : WsAt W s) {a bb : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ha : a + 32 ≤ 8192) (hb : bb + 32 ≤ 8192) :
    WP isa (.block loadAB) s fun s' =>
      v4 s' .a1 .t3 .t6 .a4 = d4 s.mem (W + BitVec.ofNat 64 a) ∧
      v4 s' .a5 .a6 .a7 .t0 = d4 s.mem (W + BitVec.ofNat 64 bb) ∧
      Rest [.a1, .t3, .t6, .a4, .a5, .a6, .a7, .t0] s s' ∧ s'.mem = s.mem := by
  have rA := hw.inR ha
  have rB := hw.inR hb
  have alA := al8 hw.al ha8
  have alB := al8 hw.al hb8
  simp only [off_add] at rA rB
  have rA0 := rA 0 (by decide); have rA1 := rA 1 (by decide); have rA2 := rA 2 (by decide)
  have rA3 := rA 3 (by decide)
  have rB0 := rB 0 (by decide); have rB1 := rB 1 (by decide); have rB2 := rB 2 (by decide)
  have rB3 := rB 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at rA0 rA1 rA2 rA3 rB0 rB1 rB2 rB3
  unfold loadAB
  refine wp_ld (off := 0) (a := W + BitVec.ofNat 64 a) (by decide) (by rw [h4]; simp) alA rA0 fun s1 u1 => ?_
  refine wp_ld (off := 8) (a := W + BitVec.ofNat 64 (a + 8)) (by decide) (by rw [u1.other _ (by decide), h4, off_add])
    (al8 hw.al (by omega)) (by rw [u1.rd, u1.wr]; exact rA1) fun s2 u2 => ?_
  refine wp_ld (off := 16) (a := W + BitVec.ofNat 64 (a + 16)) (by decide)
    (by rw [u2.other _ (by decide), u1.other _ (by decide), h4, off_add])
    (al8 hw.al (by omega)) (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact rA2) fun s3 u3 => ?_
  refine wp_ld (off := 24) (a := W + BitVec.ofNat 64 (a + 24)) (by decide)
    (by rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h4, off_add])
    (al8 hw.al (by omega)) (by rw [u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact rA3) fun s4 u4 => ?_
  have g4 : s4.gpr .t5 = s.gpr .t5 := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)]
  have p4 : s4.rd ++ s4.wr = s.rd ++ s.wr := by rw [u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]
  refine wp_ld (off := 0) (a := W + BitVec.ofNat 64 bb) (by decide) (by rw [g4, h5]; simp) alB
    (by rw [p4]; exact rB0) fun s5 u5 => ?_
  refine wp_ld (off := 8) (a := W + BitVec.ofNat 64 (bb + 8)) (by decide)
    (by rw [u5.other _ (by decide), g4, h5, off_add])
    (al8 hw.al (by omega)) (by rw [u5.rd, u5.wr, p4]; exact rB1) fun s6 u6 => ?_
  refine wp_ld (off := 16) (a := W + BitVec.ofNat 64 (bb + 16)) (by decide)
    (by rw [u6.other _ (by decide), u5.other _ (by decide), g4, h5, off_add])
    (al8 hw.al (by omega)) (by rw [u6.rd, u6.wr, u5.rd, u5.wr, p4]; exact rB2) fun s7 u7 => ?_
  refine wp_ld (off := 24) (a := W + BitVec.ofNat 64 (bb + 24)) (by decide)
    (by rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), g4, h5, off_add])
    (al8 hw.al (by omega)) (by rw [u7.rd, u7.wr, u6.rd, u6.wr, u5.rd, u5.wr, p4]; exact rB3)
    fun s8 u8 => WP.block_nil ?_
  have m8 : s8.mem = s.mem := by
    rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨?_, ?_, ?_, m8⟩
  · simp only [v4, d4, dw]
    rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide),
      u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr,
      u8.other .t3 (by decide), u7.other .t3 (by decide), u6.other .t3 (by decide), u5.other .t3 (by decide),
      u4.other .t3 (by decide), u3.other .t3 (by decide), u2.gpr, u1.mem,
      u8.other .t6 (by decide), u7.other .t6 (by decide), u6.other .t6 (by decide), u5.other .t6 (by decide),
      u4.other .t6 (by decide), u3.gpr, u2.mem, u1.mem,
      u8.other .a4 (by decide), u7.other .a4 (by decide), u6.other .a4 (by decide), u5.other .a4 (by decide),
      u4.gpr, u3.mem, u2.mem, u1.mem]
    simp only [off_add, Nat.add_zero]
  · simp only [v4, d4, dw]
    rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.gpr,
      u8.other .a6 (by decide), u7.other .a6 (by decide), u6.gpr, u5.mem,
      u8.other .a7 (by decide), u7.gpr, u6.mem, u5.mem, u8.gpr, u7.mem, u6.mem, u5.mem,
      u4.mem, u3.mem, u2.mem, u1.mem]
    simp only [off_add, Nat.add_zero]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans
      ((u7.rest (by decide)).trans (u8.rest (by decide))))))))

/-- `addCore`: `[t2] = ([t4] + [t5]) mod p`, for a sum below `2p`. -/
theorem addCore_ok {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ho8 : o % 8 = 0)
    (ha : a + 32 ≤ 8192) (hb : bb + 32 ≤ 8192) (ho : o + 32 ≤ 8192)
    (hab : d4 s.mem (W + BitVec.ofNat 64 a) + d4 s.mem (W + BitVec.ofNat 64 bb) < 2 * P) :
    WP isa (.block addCore) s fun s' =>
      d4 s'.mem (W + BitVec.ofNat 64 o) =
        (d4 s.mem (W + BitVec.ofNat 64 a) + d4 s.mem (W + BitVec.ofNat 64 bb)) % P ∧
      Frame [⟨W + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold addCore addWord
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (loadAB_ok hw h4 h5 ha8 hb8 ha hb) fun s1 ⟨vA, vB, r1, m1⟩ => ?_)
  refine WP.block_append (WP.mono (add1_ok (d := .a1) (y := .a5) (c := .a2)) fun s2 ⟨e2, k2⟩ => ?_)
  refine WP.block_append (WP.mono (adc_ok (d := .t3) (x := .t3) (y := .a6) (c := .a2) (u := .a5))
    fun s3 ⟨e3, k3⟩ => ?_)
  refine WP.block_append (WP.mono (adc_ok (d := .t4) (x := .t6) (y := .a7) (c := .a2) (u := .a5))
    fun s4 ⟨e4, k4⟩ => ?_)
  refine WP.block_append (WP.mono (adc_ok (d := .t5) (x := .a4) (y := .t0) (c := .a2) (u := .a5))
    fun s5 ⟨e5, k5⟩ => ?_)
  have b2 := (s2.gpr .a1).isLt
  have c2 : (s2.gpr .a2).toNat ≤ 1 := by have := (s1.gpr .a1).isLt; have := (s1.gpr .a5).isLt; omega
  have e3' := e3 c2
  rw [k2.1 .t3 (by decide), k2.1 .a6 (by decide)] at e3'
  have b3 := (s3.gpr .t3).isLt
  have c3 : (s3.gpr .a2).toNat ≤ 1 := by
    have := (s1.gpr .t3).isLt; have := (s1.gpr .a6).isLt; omega
  have e4' := e4 c3
  rw [k3.1 .t6 (by decide), k3.1 .a7 (by decide), k2.1 .t6 (by decide), k2.1 .a7 (by decide)] at e4'
  have b4 := (s4.gpr .t4).isLt
  have c4 : (s4.gpr .a2).toNat ≤ 1 := by
    have := (s1.gpr .t6).isLt; have := (s1.gpr .a7).isLt; omega
  have e5' := e5 c4
  rw [k4.1 .a4 (by decide), k4.1 .t0 (by decide), k3.1 .a4 (by decide), k3.1 .t0 (by decide),
    k2.1 .a4 (by decide), k2.1 .t0 (by decide)] at e5'
  have hr5 : Rest clobM s s5 := (r1.mono (by decide)).trans (((Keeps.rest k2).mono (by decide)).trans
    (((Keeps.rest k3).mono (by decide)).trans (((Keeps.rest k4).mono (by decide)).trans
    ((Keeps.rest k5).mono (by decide)))))
  have w5 : WsAt W s5 := hw.of_rest hr5 (by decide)
  have g5 : ∀ r, r ∉ clobM → s5.gpr r = s.gpr r := hr5.gpr
  have hsum : v4 s5 X0 X1 X2 X3 + 2 ^ 256 * (s5.gpr XC).toNat =
      d4 s.mem (W + BitVec.ofNat 64 a) + d4 s.mem (W + BitVec.ofNat 64 bb) := by
    rw [← vA, ← vB]
    simp only [v4, X0, X1, X2, X3, XC]
    rw [k5.1 .a1 (by decide), k4.1 .a1 (by decide), k3.1 .a1 (by decide), k5.1 .t3 (by decide),
      k4.1 .t3 (by decide), k5.1 .t4 (by decide)]
    omega
  refine WP.mono (csub_ok (O := W + BitVec.ofNat 64 o) (by rw [g5 _ (by decide), h2]) (al8 hw.al ho8)
    (w5.inW ho) (by show (s5.gpr .a2).toNat ≤ 1; have := e5'; omega) (by rw [hsum]; exact hab))
    fun s6 ⟨v6, f6, g6, rd6, wr6, sp6⟩ => ⟨by rw [v6, hsum], ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have m5 : s5.mem = s.mem := by rw [k5.2.1, k4.2.1, k3.2.1, k2.2.1, m1]
    rw [m5] at f6; exact f6
  · have sC : ∀ x ∈ clobC, x ∈ clobM := by decide
    rw [g6 r (fun h => hr (sC r h)), g5 r hr]
  · rw [rd6, hr5.rd]
  · rw [wr6, hr5.wr]
  · rw [sp6, hr5.sp]

set_option linter.unusedSimpArgs false in
/-- `d := d - y` and its borrow into `c`. -/
theorem sub1_ok {s : State} {d y c : Reg} (hdc : d ≠ c := by decide) (hcy : c ≠ y := by decide) :
    WP isa (.block [.sltu c d y, .sub d d y]) s fun s' =>
      (s'.gpr d).toNat + (s.gpr y).toNat = (s.gpr d).toNat + 2 ^ 64 * (s'.gpr c).toNat ∧
      (s'.gpr c).toNat ≤ 1 ∧ Keeps [d, c] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_sub, exec_sltu,
    RegUpd.gpr_write, hdc, hcy, Ne.symm hdc, Ne.symm hcy, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  have := sub_borrow (s.gpr d) (s.gpr y)
  have b := sltu_toNat (s.gpr d) (s.gpr y)
  refine ⟨by rw [this, b], by rw [b]; split <;> omega, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- The difference of the words in registers, `D + B = A + 2²⁵⁶ β`. -/
theorem diff_ok {s : State} :
    WP isa (.block ([.sltu .a2 .a1 .a5, .sub .a1 .a1 .a5] ++ subWord .t3 .t3 .a6 ++ subWord .t4 .t6 .a7 ++
      subWord .t5 .a4 .t0)) s fun s' =>
      v4 s' .a1 .t3 .t4 .t5 + v4 s .a5 .a6 .a7 .t0 = v4 s .a1 .t3 .t6 .a4 + 2 ^ 256 * (s'.gpr .a2).toNat ∧
      (s'.gpr .a2).toNat ≤ 1 ∧ Keeps [.a1, .a2, .t3, .a5, .a0, .t4, .t5] s s' := by
  unfold subWord
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (sub1_ok (d := .a1) (y := .a5) (c := .a2)) fun s1 ⟨e1, c1, k1⟩ => ?_)
  refine WP.block_append (WP.mono (sbb_ok (d := .t3) (x := .t3) (y := .a6) (c := .a2) (u := .a5) (v := .a0))
    fun s2 ⟨e2, k2⟩ => ?_)
  refine WP.block_append (WP.mono (sbb_ok (d := .t4) (x := .t6) (y := .a7) (c := .a2) (u := .a5) (v := .a0))
    fun s3 ⟨e3, k3⟩ => ?_)
  refine WP.mono (sbb_ok (d := .t5) (x := .a4) (y := .t0) (c := .a2) (u := .a5) (v := .a0))
    fun s4 ⟨e4, k4⟩ => ?_
  obtain ⟨e2, c2⟩ := e2 c1
  obtain ⟨e3, c3⟩ := e3 c2
  obtain ⟨e4, c4⟩ := e4 c3
  rw [k1.1 .t3 (by decide), k1.1 .a6 (by decide)] at e2
  rw [k2.1 .t6 (by decide), k2.1 .a7 (by decide), k1.1 .t6 (by decide), k1.1 .a7 (by decide)] at e3
  rw [k3.1 .a4 (by decide), k3.1 .t0 (by decide), k2.1 .a4 (by decide), k2.1 .t0 (by decide),
    k1.1 .a4 (by decide), k1.1 .t0 (by decide)] at e4
  refine ⟨?_, c4, ((k1.trans k2).trans (k3.trans k4)).mono (by decide)⟩
  simp only [v4]
  rw [k4.1 .a1 (by decide), k3.1 .a1 (by decide), k2.1 .a1 (by decide), k4.1 .t3 (by decide),
    k3.1 .t3 (by decide), k4.1 .t4 (by decide)]
  omega

/-- The words of `p` under the mask of a borrow `β`. -/
theorem pmask {β : BitVec 64} (hb : β.toNat ≤ 1) :
    (0 - β).toNat = (if β.toNat = 1 then 2 ^ 64 - 1 else 0) ∧
    ((0 - β) >>> 32).toNat = (if β.toNat = 1 then 2 ^ 32 - 1 else 0) ∧
    ((0 - β) <<< 32 ||| (0 - β) >>> 63).toNat = (if β.toNat = 1 then 2 ^ 64 - 2 ^ 32 + 1 else 0) := by
  have h : β = 0 ∨ β = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h | h
    · exact .inl (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    · exact .inr (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  rcases h with rfl | rfl <;> decide

/-- `a1 += t6`, the carry into `a7`, stored at `[t2]`. -/
theorem addP0_ok {s : State} {O : Addr} (ht2 : s.gpr .t2 = O) (hal : O.toNat % 8 = 0)
    (hw : InRegions s.wr O 8) :
    WP isa (.block (addPWord .a1 0)) s fun s' =>
      (s'.gpr .a1).toNat + 2 ^ 64 * (s'.gpr .a7).toNat = (s.gpr .a1).toNat + (s.gpr .t6).toNat ∧
      s'.mem = s.mem.writeW O (s'.gpr .a1) ∧ Keeps' [.a1, .a7] s s' := by
  unfold addPWord
  simp only [↓reduceIte, Nat.mul_zero, List.cons_append, List.nil_append]
  rw [show ([.add .a1 .a1 .t6, .sltu .a7 .a1 .t6, .store .d .a1 .t2 0] : List Instr) =
    [.add .a1 .a1 .t6, .sltu .a7 .a1 .t6] ++ [.store .d .a1 .t2 0] from rfl]
  refine WP.block_append (WP.mono (add1_ok (d := .a1) (y := .t6) (c := .a7)) fun s1 ⟨e1, k1⟩ => ?_)
  refine wp_sd (off := 0) (a := O) (by decide) (by rw [k1.1 .t2 (by decide), ht2]; simp) hal
    (by rw [k1.2.2.2.1]; exact hw) fun s2 u2 => WP.block_nil ?_
  refine ⟨by rw [u2.gpr]; exact e1, by rw [u2.mem, k1.2.1, u2.gpr], ?_⟩
  exact ⟨fun r hr => by rw [u2.gpr]; exact k1.1 r hr, by rw [u2.rd, k1.2.2.1], by rw [u2.wr, k1.2.2.2.1],
    by rw [u2.sp, k1.2.2.2.2]⟩

/-- `x += t6 + c` (`c` in `a7`), stored at `[t2 + 8j]`. -/
theorem addPStep_ok {s : State} {O : Addr} {x : Reg} {j : Nat} (hj : j < 4) (ht2 : s.gpr .t2 = O)
    (hal : O.toNat % 8 = 0) (hw : InRegions s.wr (O + BitVec.ofNat 64 (8 * j)) 8) (hj0 : 0 < j)
    (hc : (s.gpr .a7).toNat ≤ 1) (hx6 : x ≠ .t6 := by decide) (hx7 : x ≠ .a7 := by decide)
    (hx0 : x ≠ .a0 := by decide) (hx2 : x ≠ .t2 := by decide) :
    WP isa (.block (addPWord x j)) s fun s' =>
      (s'.gpr x).toNat + 2 ^ 64 * (s'.gpr .a7).toNat = (s.gpr x).toNat + (s.gpr .t6).toNat + (s.gpr .a7).toNat ∧
      s'.mem = s.mem.writeW (O + BitVec.ofNat 64 (8 * j)) (s'.gpr x) ∧ Keeps' [x, .a0, .a7] s s' := by
  unfold addPWord
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
  refine WP.block_append (WP.mono (adc_ok (d := x) (x := x) (y := .t6) (c := .a7) (u := .a0) hx6 hx7
      (Ne.symm hx0))
    fun s1 ⟨e1, k1⟩ => ?_)
  refine wp_sd (by omega) (by rw [k1.1 .t2 (by simp [Ne.symm hx2]), ht2]) (al8 hal (by omega))
    (by rw [k1.2.2.2.1]; exact hw) fun s2 u2 => WP.block_nil ?_
  refine ⟨by rw [u2.gpr]; exact e1 hc, by rw [u2.mem, k1.2.1, u2.gpr], ?_⟩
  exact ⟨fun r hr => by rw [u2.gpr]; exact k1.1 r hr, by rw [u2.rd, k1.2.2.1], by rw [u2.wr, k1.2.2.2.1],
    by rw [u2.sp, k1.2.2.2.2]⟩

/-- The value `subCore` stores. -/
theorem sub_final {A B D0 D1 D2 D3 β o0 o1 o2 o3 k0 k1 k2 k3 : Nat} (hA : A < P) (hB : B < P)
    (hD : D0 + 2 ^ 64 * D1 + 2 ^ 128 * D2 + 2 ^ 192 * D3 + B = A + 2 ^ 256 * β) (hβ : β ≤ 1)
    (b0 : o0 < 2 ^ 64) (b1 : o1 < 2 ^ 64) (b2 : o2 < 2 ^ 64) (b3 : o3 < 2 ^ 64)
    (c0 : D0 < 2 ^ 64) (c1 : D1 < 2 ^ 64) (c2 : D2 < 2 ^ 64) (c3 : D3 < 2 ^ 64)
    (e0 : o0 + 2 ^ 64 * k0 = D0 + (if β = 1 then 2 ^ 64 - 1 else 0))
    (e1 : o1 + 2 ^ 64 * k1 = D1 + (if β = 1 then 2 ^ 32 - 1 else 0) + k0)
    (e2 : o2 + 2 ^ 64 * k2 = D2 + 0 + k1)
    (e3 : o3 + 2 ^ 64 * k3 = D3 + (if β = 1 then 2 ^ 64 - 2 ^ 32 + 1 else 0) + k2) :
    o0 + 2 ^ 64 * (o1 + 2 ^ 64 * (o2 + 2 ^ 64 * o3)) = (A + P - B) % P := by
  have hPv : P = 115792089210356248762697446949407573530086143415290314195533631308867097853951 := by decide
  rcases (by omega : β = 0 ∨ β = 1) with rfl | rfl
  · simp only [Nat.zero_ne_one, ↓reduceIte, Nat.add_zero] at e0 e1 e2 e3
    have hAB : B ≤ A := by omega
    rw [show A + P - B = (A - B) + P by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [↓reduceIte] at e0 e1 e2 e3
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- `subCore`: `[t2] = ([t4] - [t5]) mod p`, for operands below `p`. -/
theorem subCore_ok {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ho8 : o % 8 = 0)
    (ha : a + 32 ≤ 8192) (hb : bb + 32 ≤ 8192) (ho : o + 32 ≤ 8192)
    (hA : d4 s.mem (W + BitVec.ofNat 64 a) < P) (hB : d4 s.mem (W + BitVec.ofNat 64 bb) < P) :
    WP isa (.block subCore) s fun s' =>
      d4 s'.mem (W + BitVec.ofNat 64 o) =
        (d4 s.mem (W + BitVec.ofNat 64 a) + P - d4 s.mem (W + BitVec.ofNat 64 bb)) % P ∧
      Frame [⟨W + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hW := hw.inW ho
  have w0 := hW 0 (by decide); have w1 := hW 1 (by decide); have w2 := hW 2 (by decide)
  have w3 := hW 3 (by decide)
  have alO := al8 hw.al ho8
  unfold subCore
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (loadAB_ok hw h4 h5 ha8 hb8 ha hb) fun s1 ⟨vA, vB, r1, m1⟩ => ?_)
  rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
  refine WP.block_append (WP.mono diff_ok fun s2 ⟨e2, c2, k2⟩ => ?_)
  refine wp_li (imm := 0) (by decide) fun s3 u3 => wp_sub fun s4 u4 => wp_mv fun s5 u5 => ?_
  have hβ := pmask c2
  have hm : s5.gpr .t0 = 0 - s2.gpr .a2 := by
    rw [u5.other _ (by decide), u4.gpr, u3.gpr, u3.other _ (by decide)]; rfl
  have g5 : ∀ r, r ≠ .t0 → r ≠ .t6 → s5.gpr r = s2.gpr r := fun r h0 h6 => by
    rw [u5.other _ h6, u4.other _ h0, u3.other _ h0]
  have t2_5 : s5.gpr .t2 = W + BitVec.ofNat 64 o := by
    rw [g5 _ (by decide) (by decide), k2.1 _ (by decide), r1.gpr _ (by decide), h2]
  have wr5 : s5.wr = s.wr := by rw [u5.wr, u4.wr, u3.wr, k2.2.2.2.1, r1.wr]
  show WP isa (.block (addPWord .a1 0 ++ _)) s5 _
  refine WP.block_append (WP.mono (addP0_ok (O := W + BitVec.ofNat 64 o) t2_5 alO (by rw [wr5]; simpa using w0))
    fun s6 ⟨e6, m6, k6⟩ => ?_)
  refine wp_srl (by decide) fun s7 u7 => ?_
  show WP isa (.block (addPWord .t3 1 ++ _)) s7 _
  have c6 : (s7.gpr .a7).toNat ≤ 1 := by rw [u7.other _ (by decide)]; have := (s6.gpr .a1).isLt; omega
  refine WP.block_append (WP.mono (addPStep_ok (O := W + BitVec.ofNat 64 o) (x := .t3) (j := 1) (by decide)
    (by rw [u7.other _ (by decide), k6.1 _ (by decide), t2_5]) alO (by rw [u7.wr, k6.2.2.1, wr5]; exact w1)
    (by decide) c6) fun s8 ⟨e8, m8, k8⟩ => ?_)
  refine wp_li (imm := 0) (by decide) fun s9 u9 => ?_
  show WP isa (.block (addPWord .t4 2 ++ _)) s9 _
  have c8 : (s9.gpr .a7).toNat ≤ 1 := by rw [u9.other _ (by decide)]; have := (s8.gpr .t3).isLt; omega
  refine WP.block_append (WP.mono (addPStep_ok (O := W + BitVec.ofNat 64 o) (x := .t4) (j := 2) (by decide)
    (by rw [u9.other _ (by decide), k8.1 _ (by decide), u7.other _ (by decide), k6.1 _ (by decide), t2_5]) alO
    (by rw [u9.wr, k8.2.2.1, u7.wr, k6.2.2.1, wr5]; exact w2) (by decide) c8) fun s10 ⟨e10, m10, k10⟩ => ?_)
  refine wp_sll (by decide) fun s11 u11 => wp_srl (by decide) fun s12 u12 => wp_or fun s13 u13 => ?_
  have c10 : (s13.gpr .a7).toNat ≤ 1 := by
    rw [u13.other _ (by decide), u12.other _ (by decide), u11.other _ (by decide)]
    have := (s10.gpr .t4).isLt; omega
  refine WP.mono (addPStep_ok (O := W + BitVec.ofNat 64 o) (x := .t5) (j := 3) (by decide)
    (by rw [u13.other _ (by decide), u12.other _ (by decide), u11.other _ (by decide), k10.1 _ (by decide),
      u9.other _ (by decide), k8.1 _ (by decide), u7.other _ (by decide), k6.1 _ (by decide), t2_5]) alO
    (by rw [u13.wr, u12.wr, u11.wr, k10.2.2.1, u9.wr, k8.2.2.1, u7.wr, k6.2.2.1, wr5]; exact w3) (by decide) c10)
    fun s14 ⟨e14, m14, k14⟩ => ?_
  obtain ⟨hp0, hp1, hp3⟩ := hβ
  -- The words of `p` under the mask.
  have q0 : (s5.gpr .t6).toNat = if (s2.gpr .a2).toNat = 1 then 2 ^ 64 - 1 else 0 := by
    rw [u5.gpr, ← hp0, ← hm, u5.other .t0 (by decide)]
  have t0_6 : s6.gpr .t0 = s5.gpr .t0 := k6.1 _ (by decide)
  have q1 : (s7.gpr .t6).toNat = if (s2.gpr .a2).toNat = 1 then 2 ^ 32 - 1 else 0 := by
    rw [u7.gpr, t0_6, hm, hp1]
  have q2 : (s9.gpr .t6).toNat = 0 := by rw [u9.gpr]; rfl
  have t0_10 : s10.gpr .t0 = s5.gpr .t0 := by
    rw [k10.1 _ (by decide), u9.other _ (by decide), k8.1 _ (by decide), u7.other _ (by decide), t0_6]
  have q3 : (s13.gpr .t6).toNat = if (s2.gpr .a2).toNat = 1 then 2 ^ 64 - 2 ^ 32 + 1 else 0 := by
    rw [u13.gpr, u12.other _ (by decide), u12.gpr, u11.gpr, u11.other _ (by decide), t0_10, hm, hp3]
  -- The words of the difference, through the steps.
  have d0 : s5.gpr .a1 = s2.gpr .a1 := g5 _ (by decide) (by decide)
  have d1 : s7.gpr .t3 = s2.gpr .t3 := by
    rw [u7.other _ (by decide), k6.1 _ (by decide), g5 _ (by decide) (by decide)]
  have d2 : s9.gpr .t4 = s2.gpr .t4 := by
    rw [u9.other _ (by decide), k8.1 _ (by decide), u7.other _ (by decide), k6.1 _ (by decide),
      g5 _ (by decide) (by decide)]
  have d3 : s13.gpr .t5 = s2.gpr .t5 := by
    rw [u13.other _ (by decide), u12.other _ (by decide), u11.other _ (by decide), k10.1 _ (by decide),
      u9.other _ (by decide), k8.1 _ (by decide), u7.other _ (by decide), k6.1 _ (by decide),
      g5 _ (by decide) (by decide)]
  have a7_7 : s7.gpr .a7 = s6.gpr .a7 := u7.other _ (by decide)
  have a7_9 : s9.gpr .a7 = s8.gpr .a7 := u9.other _ (by decide)
  have a7_13 : s13.gpr .a7 = s10.gpr .a7 := by
    rw [u13.other _ (by decide), u12.other _ (by decide), u11.other _ (by decide)]
  rw [d0, q0] at e6
  rw [d1, q1, a7_7] at e8
  rw [d2, q2, a7_9] at e10
  rw [d3, q3, a7_13] at e14
  -- The memory.
  have m5 : s5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, k2.2.1, m1]
  have hmem : s14.mem = (((s.mem.writeW (W + BitVec.ofNat 64 o) (s6.gpr .a1)).writeW
      (W + BitVec.ofNat 64 o + BitVec.ofNat 64 (8 * 1)) (s8.gpr .t3)).writeW
      (W + BitVec.ofNat 64 o + BitVec.ofNat 64 (8 * 2)) (s10.gpr .t4)).writeW
      (W + BitVec.ofNat 64 o + BitVec.ofNat 64 (8 * 3)) (s14.gpr .t5) := by
    rw [m14, u13.mem, u12.mem, u11.mem, m10, u9.mem, m8, u7.mem, m6, m5]
  have hrest : ∀ r, r ∉ clobM → s14.gpr r = s.gpr r := fun r hr => by
    have n : ∀ x ∈ [Reg.a1, .t3, .t6, .a4, .a5, .a6, .a7, .t0, .a2, .a0, .t4, .t5], x ∈ clobM := by decide
    have h' : ∀ x, x ∈ [Reg.a1, .t3, .t6, .a4, .a5, .a6, .a7, .t0, .a2, .a0, .t4, .t5] → r ≠ x := fun x hx e =>
      hr (e ▸ n x hx)
    rw [k14.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
        ⟨h' _ (by simp), h' _ (by simp), h' _ (by simp)⟩),
      u13.other _ (h' _ (by simp)), u12.other _ (h' _ (by simp)), u11.other _ (h' _ (by simp)),
      k10.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
        ⟨h' _ (by simp), h' _ (by simp), h' _ (by simp)⟩),
      u9.other _ (h' _ (by simp)),
      k8.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
        ⟨h' _ (by simp), h' _ (by simp), h' _ (by simp)⟩),
      u7.other _ (h' _ (by simp)),
      k6.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
        ⟨h' _ (by simp), h' _ (by simp)⟩),
      u5.other _ (h' _ (by simp)), u4.other _ (h' _ (by simp)), u3.other _ (h' _ (by simp)),
      k2.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
        ⟨h' _ (by simp), h' _ (by simp), h' _ (by simp), h' _ (by simp), h' _ (by simp), h' _ (by simp),
          h' _ (by simp)⟩),
      r1.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
        ⟨h' _ (by simp), h' _ (by simp), h' _ (by simp), h' _ (by simp), h' _ (by simp), h' _ (by simp),
          h' _ (by simp), h' _ (by simp)⟩)]
  refine ⟨?_, ?_, hrest, ?_, ?_, ?_⟩
  · rw [hmem, d4_add]
    simp only [Nat.mul_one, Nat.reduceMul, off_add, VG.Proof.X25519.RISCV64.R64.val4, Nat.mul_zero,
      Nat.add_zero]
    rw [dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_other _ _ _ (by omega) (by omega) (by omega),
      dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_self,
      dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_other _ _ _ (by omega) (by omega) (by omega),
      dw_write_self, dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_self, dw_write_self]
    exact sub_final hA hB (by rw [← vA, ← vB]; exact e2) c2 (BitVec.isLt _) (BitVec.isLt _)
      (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
      e6 e8 e10 e14
  · rw [hmem]
    have cc : ∀ k < 4, (⟨W + BitVec.ofNat 64 o, 32⟩ : Region).Contains
        (W + BitVec.ofNat 64 o + BitVec.ofNat 64 (8 * k)) 8 := fun k hk => out_contains _ hk
    have c0 := cc 0 (by decide)
    simp only [Nat.mul_zero] at c0
    rw [show W + BitVec.ofNat 64 o + BitVec.ofNat 64 0 = W + BitVec.ofNat 64 o by simp] at c0
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW
      (List.mem_singleton_self _) _ (cc 1 (by decide))).writeW (List.mem_singleton_self _) _
      (cc 2 (by decide))).writeW (List.mem_singleton_self _) _ (cc 3 (by decide))
  · rw [k14.2.1, u13.rd, u12.rd, u11.rd, k10.2.1, u9.rd, k8.2.1, u7.rd, k6.2.1, u5.rd, u4.rd, u3.rd,
      k2.2.2.1, r1.rd]
  · rw [k14.2.2.1, u13.wr, u12.wr, u11.wr, k10.2.2.1, u9.wr, k8.2.2.1, u7.wr, k6.2.2.1, wr5]
  · rw [k14.2.2.2, u13.sp, u12.sp, u11.sp, k10.2.2.2, u9.sp, k8.2.2.2, u7.sp, k6.2.2.2, u5.sp, u4.sp, u3.sp,
      k2.2.2.2.2, r1.sp]

end VG.Proof.Weierstrass.RISCV64.P256Field
