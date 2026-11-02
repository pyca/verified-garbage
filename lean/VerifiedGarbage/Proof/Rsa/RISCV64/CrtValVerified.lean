module

public import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValCorrect
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValCorrect
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_crt_values` on RISC-V: constant time, and verified

`crtValues_verified`: correct (`code_correct`), constant time (`code_ct`),
and the contract on the registers and the stack implied by the shared
contract (`cv_implies`).

Constant time, as the key checks' (`Proof/Rsa/RISCV64/KeyChkCT.lean`): two runs with the
same public data (`dataOf`: the arguments, the stack arguments and `n`) are
related by `Two` (`Proof/Bignum/RISCV64/PreCT.lean`) at each step, both
satisfying the same predicate for the same data, which fixes the registers
the next piece's addresses and branches read; the pieces by the taint
analysis, what each run satisfies after each by correctness (`two_post`).
The code is cut after each load whose value an address or a branch reads:
the working space's address, the stack arguments, `n`'s first byte, and
whether `n` is valid, which the one branch tests.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.CrtValues

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.RISCV64.Taint VG.Proof.Mont VG.Proof.Bignum.RISCV64
  VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (saved save restore mov)
open VG.Impl.Rsa.RISCV64.CrtValues (code entry nCheck valid fail)
open VG.Impl.Bignum.RISCV64.Precompute (check1 check2)
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint getD_of_lt)

/-! ## The public data -/

def dataOf (s : State) : List (BitVec 64) × List (BitVec 64) × List Nat × Addr :=
  (argRegs.map s.gpr, (List.range 8).map (stackArg s), (nB s).map (·.toNat), s.sp)

theorem pub_data {s₁ s₂ : State} (h : (Spec.Rsa.crtValuesContract RISCV64.abi).pub s₁ s₂) :
    dataOf s₁ = dataOf s₂ := by
  sig_pub [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_eight, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
  unfold dataOf
  rw [hl]
  simp only [argRegs, List.map_cons, List.map_nil, stackArgs_eight, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1,
    a2, a3, a4, a5, a6, a7, hsp]

structure Same (s₁ s₂ : State) : Prop where
  regs : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r
  args : ∀ i < 8, stackArg s₁ i = stackArg s₂ i
  sp : s₁.sp = s₂.sp
  n : nB s₁ = nB s₂

theorem same_of {s₁ s₂ : State} (h : dataOf s₁ = dataOf s₂) : Same s₁ s₂ := by
  simp only [dataOf, Prod.mk.injEq] at h
  obtain ⟨hr, ha, hb, hsp⟩ := h
  exact ⟨List.map_inj_left.mp hr, fun i hi => List.map_inj_left.mp ha i (List.mem_range.mpr hi), hsp,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hb⟩

/-- On entry, with the public data `d`. -/
def C0 (d : List (BitVec 64) × List (BitVec 64) × List Nat × Addr) (s : State) : Prop :=
  (Spec.Rsa.crtValuesContract RISCV64.abi).pre s ∧ dataOf s = d

theorem C0.same {d : List (BitVec 64) × List (BitVec 64) × List Nat × Addr} {x y : State} (hx : C0 d x)
    (hy : C0 d y) : Same x y := same_of (hx.2.trans hy.2.symm)

/-! ## `save`, in two parts -/

/-- The stores of `save`, and the base into `s11`. -/
def save2 : List Instr :=
  (List.range 12).flatMap (fun i => [.store .d (saved i) .t0 (8 * i)]) ++ [mov .s11 .t0]

theorem save_eq (o : Nat) (moves : List Instr) :
    save o ++ moves = ([.addSp .t0 0, .load .d .t0 .t0 o] : List Instr) ++ (save2 ++ moves) := by
  simp only [save, save2, List.append_assoc]

/-- `save`'s first part: the working space's address, the stack argument `i`, into `t0`. -/
theorem save1_ok (s₀ : State) {i : Nat} (hi : 8 * i < 2048)
    (hin : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ i) 8) (hal : (stackArgAddr s₀ i).toNat % 8 = 0) :
    WP isa (.block [.addSp .t0 0, .load .d .t0 .t0 (8 * i)]) s₀ fun s =>
      (s.gpr .t0 = stackArg s₀ i ∧ s.mem = s₀.mem ∧ s.sp = s₀.sp) ∧ Keep [.t0] s₀ s := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have e : s₀.sp + BitVec.ofNat 64 0 + BitVec.ofNat 64 (8 * i) = stackArgAddr s₀ i := by
    rw [add_ofNat_zero']; rfl
  have ha : ((s₀.write .t0 (s₀.sp + BitVec.ofNat 64 0)).gpr .t0 + BitVec.ofNat 64 (8 * i)).toNat % 8 = 0 := by
    rw [gpr_write_self, e]; exact hal
  have hin' : InRegions ((s₀.write .t0 (s₀.sp + BitVec.ofNat 64 0)).rd ++
      (s₀.write .t0 (s₀.sp + BitVec.ofNat 64 0)).wr)
      ((s₀.write .t0 (s₀.sp + BitVec.ofNat 64 0)).gpr .t0 + BitVec.ofNat 64 (8 * i)) 8 := by
    rw [gpr_write_self, e]; exact hin
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addSp (show 0 < 2048 by decide),
    exec_load_d hi ha hin', Option.some.injEq, exists_eq_left', gpr_write_self, e, mem_write, sp_write,
    and_true]
  first | rfl | exact ⟨rfl, rfl⟩

/-- `save`'s second part: the registers saved. -/
theorem save2_ok (s₀ : State) {B : Addr} {Z : Nat} (hs : Scr s₀ B Z) (hZ : 96 ≤ Z) {s₁ : State}
    (h : (s₁.gpr .t0 = B ∧ s₁.mem = s₀.mem ∧ s₁.sp = s₀.sp) ∧ Keep [.t0] s₀ s₁) :
    WP isa (.block save2) s₁ (Saved s₀ B) := by
  obtain ⟨⟨i0, im, isp⟩, k₁⟩ := h
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SI s₀ B)
    (fun k s hk h => save_step s₀ hs hZ hk h) 12 (Nat.le_refl _) s₁
    ⟨k₁, i0, isp, by rw [im]; exact Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s h => ?_)
  have hw : s.gpr .t0 = B := h.t0
  apply WP.of_runBlock
  simp only [mov, runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 0 by decide),
    BitVec.ofInt_ofNat, add_ofNat_zero', Option.some.injEq, exists_eq_left', hw]
  refine ⟨(h.keep.trans (Keep.write _ _ _)).mono (by decide), h.sp, ?_, ?_, h.out, h.saved⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (by decide)]; exact hw
  · rw [gpr_write, ite_eq_left_iff.mpr fun e => absurd rfl e]

/-! ## The states between the pieces -/

abbrev Dt : Type := List (BitVec 64) × List (BitVec 64) × List Nat × Addr

def S1 (d : Dt) (t : State) : Prop :=
  ∃ s0, C0 d s0 ∧ (t.gpr .t0 = bOf s0 ∧ t.mem = s0.mem ∧ t.sp = s0.sp) ∧ Keep [.t0] s0 t
def S2 (d : Dt) (v : State) : Prop := ∃ s0, C0 d s0 ∧ CB s0 s0.mem v
def S3 (d : Dt) (u : State) : Prop :=
  ∃ s0, C0 d s0 ∧ CB s0 s0.mem u ∧ u.gpr .s7 = off (s0.gpr .a6) 0 ∧ u.gpr .s8 = BitVec.ofNat 64 (kOf s0)
def S4 (d : Dt) (z : State) : Prop :=
  ∃ s0, C0 d s0 ∧ CB s0 s0.mem z ∧ (z.gpr .s0 = 0 ↔ ((nB s0).getD (kOf s0 - 1) 0).toNat % 2 = 1) ∧
    z.gpr .t4 = BitVec.ofNat 64 ((nB s0).getD 0 0).toNat ∧ z.gpr .s8 = BitVec.ofNat 64 (kOf s0)
def S5 (d : Dt) (z : State) : Prop :=
  ∃ s0, C0 d s0 ∧ CB s0 s0.mem z ∧ (z.gpr .s0 = 0 ↔ Spec.Rsa.modulusValid (Nv s0) (kOf s0) = true)
def S6 (d : Dt) (u : State) : Prop := ∃ s0, C0 d s0 ∧ CE s0 u

theorem nB_length (s0 : State) : (nB s0).length = kOf s0 := by simp [nB, Spec.Rsa.bytesAt]

/-- `n`'s bytes, read in the body. -/
theorem CB.nbyte {s0 u : State} (h : PreC s0) (c : CB s0 s0.mem u) {i : Nat} (hi : i < kOf s0) :
    u.mem (off (s0.gpr .a6) i) = (nB s0)[i]'(by rw [nB_length]; exact hi) := by
  rw [c.frame _ (bytes_past h.ns hi (by have := h.wn; omega_arith))]
  simp [nB, Spec.Rsa.bytesAt, off]

theorem CB.nrd {s0 u : State} (h : PreC s0) (c : CB s0 s0.mem u) :
    ∀ i < kOf s0, InRegions (u.rd ++ u.wr) (off (s0.gpr .a6) i) 1 := fun i hi => by
  rw [c.rd]; exact inRegions_left (bytes_in h.nR_rd (by have := h.wn; omega_arith) i hi)

/-- The body's public registers. -/
abbrev bodyRegs : List Reg := [.s1, .s2, .s3, .s4, .s5, .s6, .a0, .a1, .a2, .a3, .a6, .s11]

theorem CB.pins {s0 s1 x y : State} (sm : Same s0 s1) (cx : CB s0 s0.mem x) (cy : CB s1 s1.mem y) :
    ∀ r ∈ bodyRegs, x.gpr r = y.gpr r := by
  intro r hr
  simp only [bodyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [cx.s1, cy.s1, sm.regs _ (by decide)]
  · rw [cx.s2, cy.s2, sm.regs _ (by decide)]
  · rw [cx.s3, cy.s3, sm.args 0 (by decide)]
  · rw [cx.s4, cy.s4, sm.args 1 (by decide)]
  · rw [cx.s5, cy.s5, sm.args 2 (by decide)]
  · rw [cx.s6, cy.s6, sm.args 3 (by decide)]
  · rw [cx.a0, cy.a0, sm.args 4 (by decide)]
  · rw [cx.a1, cy.a1, sm.args 5 (by decide)]
  · rw [cx.a2, cy.a2, sm.regs _ (by decide)]
  · rw [cx.a3, cy.a3, sm.regs _ (by decide)]
  · rw [cx.a6, cy.a6, sm.regs _ (by decide)]
  · rw [cx.s11, cy.s11, bOf, bOf, sm.args 6 (by decide)]

/-! ## The pieces -/

theorem nCheck_eq : nCheck = .seq (.block [mov .s7 .s1, mov .s8 .s2]) (.seq (.block check1) check2) := rfl

theorem nMov_ok {s0 s : State} (c : CB s0 s0.mem s) :
    WP isa (.block [mov .s7 .s1, mov .s8 .s2]) s fun u =>
      (u.gpr .s7 = off (s0.gpr .a6) 0 ∧ u.gpr .s8 = BitVec.ofNat 64 (kOf s0) ∧ u.mem = s.mem) ∧
        Keep [.s7, .s8] s u := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [mov, c.s1, c.s2, add_ofNat_zero', BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem PreC.last_lt {s0 : State} (h : PreC s0) : kOf s0 - 1 < (nB s0).length := by
  rw [nB_length]; have := h.k1; show (s0.gpr .a7).toNat - 1 < (s0.gpr .a7).toNat; omega_arith

theorem PreC.zero_lt {s0 : State} (h : PreC s0) : 0 < (nB s0).length := by
  rw [nB_length]; have := h.k1; show 0 < (s0.gpr .a7).toNat; omega_arith

theorem argRegs_ne_t0 : ∀ r ∈ argRegs, r ∉ ([.t0] : List Reg) := by decide

theorem zero_of_eval0 {s : State} (h : isa.eval (.zero .s0) s = some true) : s.gpr .s0 = 0 := by
  rw [Steps.eval_zero] at h; simpa using h

theorem Same.mv {x y : State} (sm : Same x y) :
    (Spec.Rsa.modulusValid (Nv x) (kOf x) = true ↔ Spec.Rsa.modulusValid (Nv y) (kOf y) = true) := by
  simp only [Nv, sm.n, kOf, sm.regs .a7 (by decide)]

theorem code_rel [InvLaw] : RelCT isa (Two C0) code fun _ _ => True := by
  unfold code
  rw [entry_eq, save_eq]
  refine RelCT.seq (R := Two S2) (RelCT.block_append (RelCT.seq (R := Two S1) ?_ ?_)) ?_
  · -- `save`'s first part.
    refine two_post (two_taint [] (fun _ _ _ _ _ r hr => absurd hr List.not_mem_nil) (by taint_decide))
      fun a s c0 => ?_
    have h := preC_of c0.1
    exact WP.mono (save1_ok s (i := 6) (by decide) (arg_in (by rw [h.hrd]; simp) (by decide)) (arg_al h 6))
      fun t ⟨tt, k⟩ => ⟨s, c0, tt, k⟩
  · -- `save`'s second part and the moves.
    refine two_post (two_taint (.t0 :: argRegs) ?_ (by taint_decide)) fun a s ⟨s0, c0, ht⟩ => ?_
    · rintro a s₁ s₂ ⟨x, hx, ⟨tx, -, -⟩, kx⟩ ⟨y, hy, ⟨ty, -, -⟩, ky⟩ r hr
      have hs := hx.same hy
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [tx, ty, bOf, bOf, hs.args 6 (by decide)]
      · rw [kx.gpr (argRegs_ne_t0 r hr), ky.gpr (argRegs_ne_t0 r hr), hs.regs r hr]
    have h := preC_of c0.1
    have hz := h.zk
    rw [WP.block_append_iff]
    exact WP.mono (save2_ok s0 h.scr (by omega_arith) ht) fun u hu => WP.mono (moves_ok h hu) fun v c =>
      ⟨s0, c0, c⟩
  · rw [nCheck_eq]
    refine RelCT.seq (R := Two S5) (RelCT.seq (R := Two S3) ?_ (RelCT.seq (R := Two S4) ?_ ?_)) ?_
    · -- The moves to `check`.
      refine two_post (two_taint [.s1, .s2] ?_ (by taint_decide)) fun a v ⟨s0, c0, c⟩ => ?_
      · rintro a s₁ s₂ ⟨x, hx, cx⟩ ⟨y, hy, cy⟩ r hr
        exact CB.pins (hx.same hy) cx cy r (by revert r; decide)
      exact WP.mono (nMov_ok c) fun u ⟨⟨u7, u8, um⟩, ku⟩ => ⟨s0, c0, c.of_keep ku um, u7, u8⟩
    · -- `check`'s first part.
      refine two_post (two_taint [.s7, .s8] ?_ (by taint_decide)) fun a u ⟨s0, c0, c, u7, u8⟩ => ?_
      · rintro a s₁ s₂ ⟨x, hx, -, x7, x8⟩ ⟨y, hy, -, y7, y8⟩ r hr
        have hs := hx.same hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [x7, y7, hs.regs .a6 (by decide)]
        · rw [x8, y8, kOf, kOf, hs.regs .a7 (by decide)]
      have h := preC_of c0.1
      have hk := h.k1
      have hl := nB_length s0
      refine WP.mono (check1_ok (nb := nB s0) u7 u8 hk hl (c.nrd h) (fun i hi => c.nbyte h hi))
        fun z ⟨⟨z0, z4, zm⟩, kz⟩ => ⟨s0, c0, c.of_keep kz zm, by rw [z0, getD_of_lt h.last_lt],
          by rw [z4, getD_of_lt h.zero_lt], by rw [kz.gpr (by decide), u8]⟩
    · -- `check`'s second part.
      refine two_post (two_taint [.t4, .s8] ?_ (by taint_decide)) fun a z ⟨s0, c0, c, z0, z4, z8⟩ => ?_
      · rintro a s₁ s₂ ⟨x, hx, -, -, x4, x8⟩ ⟨y, hy, -, -, y4, y8⟩ r hr
        have hs := hx.same hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [x4, y4, hs.n]
        · rw [x8, y8, kOf, kOf, hs.regs .a7 (by decide)]
      have h := preC_of c0.1
      have hk := h.k1
      have hl := nB_length s0
      refine WP.mono (check2_ok (nb := nB s0) z8 hk h.k2 hl (by rw [z0, getD_of_lt h.last_lt])
        (by rw [z4, getD_of_lt h.zero_lt])) fun x ⟨x0, xm, kx⟩ => ⟨s0, c0, c.of_keep kx xm, x0⟩
    · -- The branch and the exit.
      refine RelCT.seq (R := Two S6) (RelCT.ite ?_ ?_ ?_) ?_
      · rintro s₁ s₂ ⟨a, ⟨x, hx, -, x0⟩, ⟨y, hy, -, y0⟩, -⟩
        rw [Steps.eval_zero, Steps.eval_zero]
        congr 1
        rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, x0, y0, (hx.same hy).mv]
      · -- A valid modulus.
        refine RelCT.mono (two_post (Φ := fun a s => S5 a s ∧ s.gpr .s0 = 0)
          (two_taint bodyRegs ?_ (by taint_decide)) ?_) ?_ fun _ _ h => h
        · rintro a s₁ s₂ ⟨⟨x, hx, cx, -⟩, -⟩ ⟨⟨y, hy, cy, -⟩, -⟩ r hr
          exact CB.pins (hx.same hy) cx cy r hr
        · rintro a t ⟨⟨s0, c0, c, -⟩, -⟩
          exact WP.mono (valid_ok (preC_of c0.1) c) fun u vp =>
            ⟨s0, c0, vp.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1.ce⟩
        · rintro s₁ s₂ ⟨⟨a, ⟨x, hx, cx, x0⟩, ⟨y, hy, cy, y0⟩, hsp⟩, hc⟩
          have z1 := zero_of_eval0 hc
          exact ⟨a, ⟨⟨x, hx, cx, x0⟩, z1⟩, ⟨⟨y, hy, cy, y0⟩, y0.mpr ((hx.same hy).mv.mp (x0.mp z1))⟩, hsp⟩
      · -- An invalid modulus.
        refine RelCT.mono (two_post (Φ := S5) (two_taint bodyRegs ?_ (by taint_decide)) ?_)
          (fun _ _ h => h.1) fun _ _ h => h
        · rintro a s₁ s₂ ⟨x, hx, cx, -⟩ ⟨y, hy, cy, -⟩ r hr
          exact CB.pins (hx.same hy) cx cy r hr
        · rintro a t ⟨s0, c0, c, -⟩
          exact WP.mono (fail_ok (preC_of c0.1) c) fun u ⟨ce, _⟩ => ⟨s0, c0, ce⟩
      · -- `restore`.
        refine two_taint [.s11] ?_ (by taint_decide)
        rintro a s₁ s₂ ⟨x, hx, ex⟩ ⟨y, hy, ey⟩ r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr
        rw [ex.s11, ey.s11, bOf, bOf, (hx.same hy).args 6 (by decide)]

theorem code_ct [InvLaw] : ConstantTime isa (Spec.Rsa.crtValuesContract RISCV64.abi).pre
    (Spec.Rsa.crtValuesContract RISCV64.abi).pub code :=
  RelCT.constantTime (code_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨dataOf s, ⟨hs, rfl⟩, ⟨ht, (pub_data hp).symm⟩, (same_of (pub_data hp)).sp⟩) fun _ _ h => h)

/-- `vg_rsa_crt_values`. -/
theorem crtValues_verified [InvLaw] : Verified RISCV64.target code (Spec.Rsa.crtValuesContract RISCV64.abi) :=
  Verified.of_correct code_correct code_ct cv_implies

end VG.Proof.Rsa.RISCV64.CrtValues
