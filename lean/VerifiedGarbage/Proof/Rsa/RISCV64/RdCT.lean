module

public import VerifiedGarbage.Proof.Rsa.RISCV64.RdFront
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.Rsa.RISCV64.RdFront
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkCT
import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValFront
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkCT
meta import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValFront
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on RISC-V: constant time

`code_ct`, as `crt_values`' (`Proof/Rsa/RISCV64/CrtValVerified.lean`): two
runs with the same public data (`dataOf`: the arguments, the stack
arguments, `n` and `e`) are related by `Two` (`Proof/Bignum/RISCV64/PreCT.lean`)
at each step, both satisfying the same predicate for the same data, which
fixes the registers the next piece's addresses and branches read; the
pieces by the taint analysis, what each run satisfies after each by
correctness (`two_post`). The code is cut after each load whose value an
address or a branch reads: the working space's address, the stack
arguments, `n`'s first byte, and whether `n` is valid, which the one branch
tests. Each branch is checked together with the exit (`RelCT.ite_seq`), so
nothing after the branch needs its correctness.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.RecDet

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.RISCV64.Taint VG.Proof.Mont VG.Proof.Bignum.RISCV64
  VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (saved save restore mov)
open VG.Impl.Rsa.RISCV64.RecoverDet (code entry nCheck valid fail)
open VG.Impl.Bignum.RISCV64.Precompute (check1 check2)
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint getD_of_lt)
open VG.Proof.Rsa.RISCV64.KeyCheck (save_eq save1_ok save2_ok)
open VG.Proof.Rsa.RISCV64.CrtValues (bytes_in inRegions_left)

/-- A branch followed by `r`, as each branch followed by `r`: it runs the
same and leaks the same trace. -/
theorem RelCT.ite_seq {M : ISA} {P Q : M.State → M.State → Prop} {c : M.Cond} {t e r : Prog M}
    (h : RelCT M P (.ite c (.seq t r) (.seq e r)) Q) : RelCT M P (.seq (.ite c t e) r) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
      cases a₁ with
      | iteT c₁ x₁ =>
        cases a₂ with
        | iteT c₂ x₂ => exact h _ _ _ _ _ _ hp (.iteT c₁ (.seq x₁ b₁)) (.iteT c₂ (.seq x₂ b₂))
        | iteF c₂ x₂ => exact h _ _ _ _ _ _ hp (.iteT c₁ (.seq x₁ b₁)) (.iteF c₂ (.seq x₂ b₂))
      | iteF c₁ x₁ =>
        cases a₂ with
        | iteT c₂ x₂ => exact h _ _ _ _ _ _ hp (.iteF c₁ (.seq x₁ b₁)) (.iteT c₂ (.seq x₂ b₂))
        | iteF c₂ x₂ => exact h _ _ _ _ _ _ hp (.iteF c₁ (.seq x₁ b₁)) (.iteF c₂ (.seq x₂ b₂))

/-! ## The public data -/

abbrev Dt : Type := List (BitVec 64) × List (BitVec 64) × List Nat × Addr

def dataOf (s : State) : Dt :=
  (argRegs.map s.gpr, (List.range 4).map (stackArg s), (nB s ++ eB s).map (·.toNat), s.sp)

theorem pub_data {s₁ s₂ : State} (h : (Spec.Rsa.recoverPrimesDetContract RISCV64.abi).pub s₁ s₂) :
    dataOf s₁ = dataOf s₂ := by
  sig_pub [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_four, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3⟩ := h
  unfold dataOf
  rw [hl]
  simp only [argRegs, List.map_cons, List.map_nil, stackArgs_four, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1,
    a2, a3, hsp]

structure Same (s₁ s₂ : State) : Prop where
  regs : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r
  args : ∀ i < 4, stackArg s₁ i = stackArg s₂ i
  sp : s₁.sp = s₂.sp
  n : nB s₁ = nB s₂

theorem nB_length (s0 : State) : (nB s0).length = kOf s0 := by simp [nB, Spec.Rsa.bytesAt]

theorem same_of {s₁ s₂ : State} (h : dataOf s₁ = dataOf s₂) : Same s₁ s₂ := by
  simp only [dataOf, Prod.mk.injEq] at h
  obtain ⟨hr, ha, hb, hsp⟩ := h
  have gr : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r := List.map_inj_left.mp hr
  rw [List.map_append, List.map_append] at hb
  obtain ⟨hn, -⟩ := List.append_inj hb (by simp only [List.length_map, nB_length, kOf, gr .a5 (by decide)])
  exact ⟨gr, fun i hi => List.map_inj_left.mp ha i (List.mem_range.mpr hi), hsp,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hn⟩

/-- On entry, with the public data `d`. -/
def C0 (d : Dt) (s : State) : Prop :=
  (Spec.Rsa.recoverPrimesDetContract RISCV64.abi).pre s ∧ dataOf s = d

theorem C0.same {d : Dt} {x y : State} (hx : C0 d x) (hy : C0 d y) : Same x y :=
  same_of (hx.2.trans hy.2.symm)

/-! ## The states between the pieces -/

def S1 (d : Dt) (t : State) : Prop :=
  ∃ s0, C0 d s0 ∧ (t.gpr .t0 = bOf s0 ∧ t.mem = s0.mem ∧ t.sp = s0.sp) ∧ Keep [.t0] s0 t
def S2 (d : Dt) (v : State) : Prop := ∃ s0, C0 d s0 ∧ CB s0 s0.mem v
def S3 (d : Dt) (u : State) : Prop :=
  ∃ s0, C0 d s0 ∧ CB s0 s0.mem u ∧ u.gpr .s7 = off (s0.gpr .a4) 0 ∧ u.gpr .s8 = BitVec.ofNat 64 (kOf s0)
def S4 (d : Dt) (z : State) : Prop :=
  ∃ s0, C0 d s0 ∧ CB s0 s0.mem z ∧ (z.gpr .s0 = 0 ↔ ((nB s0).getD (kOf s0 - 1) 0).toNat % 2 = 1) ∧
    z.gpr .t4 = BitVec.ofNat 64 ((nB s0).getD 0 0).toNat ∧ z.gpr .s8 = BitVec.ofNat 64 (kOf s0)
def S5 (d : Dt) (z : State) : Prop :=
  ∃ s0, C0 d s0 ∧ CB s0 s0.mem z ∧ (z.gpr .s0 = 0 ↔ Spec.Rsa.modulusValid (Nv s0) (kOf s0) = true)

theorem PreC.nL {s0 : State} (h : PreC s0) : kOf s0 ≤ 2 ^ 64 := by
  have := h.k2; show (s0.gpr .a5).toNat ≤ 2 ^ 64; omega_arith

/-- `n`'s bytes, read in the body. -/
theorem CB.nbyte {s0 u : State} (h : PreC s0) (c : CB s0 s0.mem u) {i : Nat} (hi : i < kOf s0) :
    u.mem (off (s0.gpr .a4) i) = (nB s0)[i]'(by rw [nB_length]; exact hi) := by
  have e := congrArg (fun l => l[i]?) (c.bytes h.ns h.nL)
  simp only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range hi, Option.map_some] at e
  simp only [nB, Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
  exact Option.some.inj e

theorem CB.nrd {s0 u : State} (h : PreC s0) (c : CB s0 s0.mem u) :
    ∀ i < kOf s0, InRegions (u.rd ++ u.wr) (off (s0.gpr .a4) i) 1 := fun i hi => by
  rw [c.rd]; exact inRegions_left (bytes_in (rs := s0.rd) (by rw [h.hrd]; simp) h.nL i hi)

/-- The body's public registers. -/
abbrev bodyRegs : List Reg := [.s1, .s2, .s3, .s4, .s5, .s6, .a0, .a1, .s11]

theorem CB.pins {s0 s1 x y : State} (sm : Same s0 s1) (cx : CB s0 s0.mem x) (cy : CB s1 s1.mem y) :
    ∀ r ∈ bodyRegs, x.gpr r = y.gpr r := by
  intro r hr
  simp only [bodyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [cx.s1, cy.s1, sm.regs _ (by decide)]
  · rw [cx.s2, cy.s2, sm.regs _ (by decide)]
  · rw [cx.s3, cy.s3, sm.regs _ (by decide)]
  · rw [cx.s4, cy.s4, sm.regs _ (by decide)]
  · rw [cx.s5, cy.s5, sm.regs _ (by decide)]
  · rw [cx.s6, cy.s6, sm.regs _ (by decide)]
  · rw [cx.a0, cy.a0, sm.args 0 (by decide)]
  · rw [cx.a1, cy.a1, sm.args 1 (by decide)]
  · rw [cx.s11, cy.s11, bOf, bOf, sm.args 2 (by decide)]

/-! ## The pieces -/

theorem nCheck_eq : nCheck = .seq (.block [mov .s7 .s1, mov .s8 .s2]) (.seq (.block check1) check2) := rfl

theorem nMov_ok {s0 s : State} (c : CB s0 s0.mem s) :
    WP isa (.block [mov .s7 .s1, mov .s8 .s2]) s fun u =>
      (u.gpr .s7 = off (s0.gpr .a4) 0 ∧ u.gpr .s8 = BitVec.ofNat 64 (kOf s0) ∧ u.mem = s.mem) ∧
        Keep [.s7, .s8] s u := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [mov, c.s1, c.s2, add_ofNat_zero', BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem PreC.last_lt {s0 : State} (h : PreC s0) : kOf s0 - 1 < (nB s0).length := by
  rw [nB_length]; have := h.k1; show (s0.gpr .a5).toNat - 1 < (s0.gpr .a5).toNat; omega_arith

theorem PreC.zero_lt {s0 : State} (h : PreC s0) : 0 < (nB s0).length := by
  rw [nB_length]; have := h.k1; show 0 < (s0.gpr .a5).toNat; omega_arith

theorem argRegs_ne_t0 : ∀ r ∈ argRegs, r ∉ ([.t0] : List Reg) := by decide

theorem Same.mv {x y : State} (sm : Same x y) :
    (Spec.Rsa.modulusValid (Nv x) (kOf x) = true ↔ Spec.Rsa.modulusValid (Nv y) (kOf y) = true) := by
  simp only [Nv, sm.n, kOf, sm.regs .a5 (by decide)]

theorem code_rel : RelCT isa (Two C0) code fun _ _ => True := by
  unfold code
  rw [entry_eq, save_eq]
  refine RelCT.seq (R := Two S2) (RelCT.block_append (RelCT.seq (R := Two S1) ?_ ?_)) ?_
  · -- `save`'s first part.
    refine two_post (two_taint [] (fun _ _ _ _ _ r hr => absurd hr List.not_mem_nil) (by taint_decide))
      fun a s c0 => ?_
    have h := preC_of c0.1
    exact WP.mono (save1_ok s (i := 2) (by decide) (arg_in (by rw [h.hrd]; simp) (by decide)) (arg_al h 2))
      fun t ⟨tt, k⟩ => ⟨s, c0, tt, k⟩
  · -- `save`'s second part and the moves.
    refine two_post (two_taint (.t0 :: argRegs) ?_ (by taint_decide)) fun a s ⟨s0, c0, ht⟩ => ?_
    · rintro a s₁ s₂ ⟨x, hx, ⟨tx, -, -⟩, kx⟩ ⟨y, hy, ⟨ty, -, -⟩, ky⟩ r hr
      have hs := hx.same hy
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [tx, ty, bOf, bOf, hs.args 2 (by decide)]
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
        · rw [x7, y7, hs.regs .a4 (by decide)]
        · rw [x8, y8, kOf, kOf, hs.regs .a5 (by decide)]
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
        · rw [x8, y8, kOf, kOf, hs.regs .a5 (by decide)]
      have h := preC_of c0.1
      have hk := h.k1
      have hl := nB_length s0
      refine WP.mono (check2_ok (nb := nB s0) z8 hk h.k2 hl (by rw [z0, getD_of_lt h.last_lt])
        (by rw [z4, getD_of_lt h.zero_lt])) fun x ⟨x0, xm, kx⟩ => ⟨s0, c0, c.of_keep kx xm, x0⟩
    · -- The branch, each side with the exit.
      refine RelCT.ite_seq (RelCT.ite ?_ ?_ ?_)
      · rintro s₁ s₂ ⟨a, ⟨x, hx, -, x0⟩, ⟨y, hy, -, y0⟩, -⟩
        rw [Steps.eval_zero, Steps.eval_zero]
        congr 1
        rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, x0, y0, (hx.same hy).mv]
      · -- A valid modulus.
        refine RelCT.mono (two_taint (Φ := S5) bodyRegs ?_ (by taint_decide)) (fun _ _ h => h.1)
          fun _ _ h => h
        rintro a s₁ s₂ ⟨x, hx, cx, -⟩ ⟨y, hy, cy, -⟩ r hr
        exact CB.pins (hx.same hy) cx cy r hr
      · -- An invalid modulus.
        refine RelCT.mono (two_taint (Φ := S5) bodyRegs ?_ (by taint_decide)) (fun _ _ h => h.1)
          fun _ _ h => h
        rintro a s₁ s₂ ⟨x, hx, cx, -⟩ ⟨y, hy, cy, -⟩ r hr
        exact CB.pins (hx.same hy) cx cy r hr

theorem code_ct : ConstantTime isa (Spec.Rsa.recoverPrimesDetContract RISCV64.abi).pre
    (Spec.Rsa.recoverPrimesDetContract RISCV64.abi).pub code :=
  RelCT.constantTime (code_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨dataOf s, ⟨hs, rfl⟩, ⟨ht, (pub_data hp).symm⟩, (same_of (pub_data hp)).sp⟩) fun _ _ h => h)

end VG.Proof.Rsa.RISCV64.RecDet
