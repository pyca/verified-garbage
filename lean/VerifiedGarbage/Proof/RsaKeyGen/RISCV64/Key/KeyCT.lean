module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.Lcm
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.DPart
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.Lcm
meta import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.DPart
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_keygen_key` on RISC-V: constant time

`key_ct`, as `recover_primes_det`'s (`Proof/Rsa/RISCV64/RdCT.lean`): two
runs with the same public data (`dataOf`: the arguments, the stack
arguments and `e`'s bytes, which the contract's leak includes) are related
by `Two` (`Proof/Bignum/RISCV64/PreCT.lean`) at each cut, both satisfying the
same predicate for the same data, which fixes the registers the next piece's
addresses and branches read; the pieces by the taint analysis, what each run
satisfies after each by correctness (`two_post`).

The code is cut after the working space's address (`save`'s load), after
the stack arguments' loads (`entry`), and before the one data branch,
`dPar`'s on `e`'s parity: everything before it (`pre`) runs to a state whose
flag `X3` is `e mod 2` (by the correctness of the pieces), so both runs load
the same value and take the same branch. Each branch is checked together
with everything after it (`RelCT.ite_seq`), so nothing after the branch needs
its correctness.
-/

-- separate module: the taint checks are not re-run with every change to the correctness proofs

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Key

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.RISCV64.Taint VG.Proof.Mont VG.Proof.Bignum.RISCV64
  VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (saved save restore mov seqs copy aZero)
open VG.Impl.RsaKeyGen.RISCV64.Key (code entry body setup loads consts primes lcmPart eFlags dOdd dOne
  dPar dPart dEven smallPart qinvPart crtPart nPart maskPart stores X3 X4 X5 X6 aD aS nArr aOne aTwo aThree aE
  aP aQ aPm aQm aDv aP0 aQ0)
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)
open VG.Proof.Rsa.RISCV64.KeyCheck (save_eq save1_ok save2_ok)

/-! ## The public data -/

abbrev Dt : Type := List (BitVec 64) × List (BitVec 64) × List Nat × Addr

def dataOf (s : State) : Dt :=
  (argRegs.map s.gpr, (List.range 10).map (stackArg s), (eB s).map (·.toNat), s.sp)

theorem pub_data {s₁ s₂ : State} (h : (Spec.RsaKeyGen.keyContract RISCV64.abi).pub s₁ s₂) :
    dataOf s₁ = dataOf s₂ := by
  sig_pub [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_ten, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  have he : (eB s₁).map (·.toNat) = (eB s₂).map (·.toNat) :=
    (List.append_inj hl (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range, a7])).1
  unfold dataOf
  rw [he]
  simp only [argRegs, List.map_cons, List.map_nil, stackArgs_ten, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1,
    a2, a3, a4, a5, a6, a7, a8, a9, hsp]

structure Same (s₁ s₂ : State) : Prop where
  regs : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r
  args : ∀ i < 10, stackArg s₁ i = stackArg s₂ i
  sp : s₁.sp = s₂.sp
  e : eB s₁ = eB s₂

theorem same_of {s₁ s₂ : State} (h : dataOf s₁ = dataOf s₂) : Same s₁ s₂ := by
  simp only [dataOf, Prod.mk.injEq] at h
  obtain ⟨hr, ha, hb, hsp⟩ := h
  exact ⟨List.map_inj_left.mp hr, fun i hi => List.map_inj_left.mp ha i (List.mem_range.mpr hi), hsp,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hb⟩

/-- On entry, with the public data `d`. -/
def C0 (d : Dt) (s : State) : Prop := (Spec.RsaKeyGen.keyContract RISCV64.abi).pre s ∧ dataOf s = d

theorem C0.same {d : Dt} {x y : State} (hx : C0 d x) (hy : C0 d y) : Same x y :=
  same_of (hx.2.trans hy.2.symm)

/-! ## The code, cut at the branch -/

/-- `dPar`'s load of `X3`. -/
abbrev ldX3 : Prog isa := .block [.load .d .t5 .s11 X3]

/-- Everything before `dPar`. -/
def pre : Prog isa := seqs [setup, loads, seqs consts, primes, lcmPart, eFlags, dOdd, dOne]

/-- Everything after `dPar`. -/
def post : Prog isa := .seq (seqs [smallPart, qinvPart, crtPart, nPart, maskPart, stores]) (.block restore)

/-- The body and the exit, as `pre`, `dPar` and `post`. -/
def shaped : Prog isa :=
  .seq pre (.seq ldX3 (.seq (.ite (.nonzero .t5) (copy aD aS) dEven) post))

theorem seq_inv {a b : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa (.seq a b) s t s') :
    ∃ t₁ t₂ m, Exec isa a s t₁ m ∧ Exec isa b m t₂ s' ∧ t = t₁ ++ t₂ := by
  cases h with
  | seq h₁ h₂ => exact ⟨_, _, _, h₁, h₂, rfl⟩

theorem exec_shaped {s s' : State} {t : List Leak} (h : Exec isa (.seq body (.block restore)) s t s') :
    Exec isa shaped s t s' := by
  simp only [body, consts, dPart, dPar, List.cons_append, List.nil_append, seqs] at h
  obtain ⟨_, _, _, g0, hR, rfl⟩ := seq_inv h
  obtain ⟨_, _, _, h1, g1, rfl⟩ := seq_inv g0
  obtain ⟨_, _, _, h2, g2, rfl⟩ := seq_inv g1
  obtain ⟨_, _, _, h3, g3, rfl⟩ := seq_inv g2
  obtain ⟨_, _, _, h4, g4, rfl⟩ := seq_inv g3
  obtain ⟨_, _, _, h5, g5, rfl⟩ := seq_inv g4
  obtain ⟨_, _, _, h6, g6, rfl⟩ := seq_inv g5
  obtain ⟨_, _, _, gD, hR1, rfl⟩ := seq_inv g6
  obtain ⟨_, _, _, h7, g7, rfl⟩ := seq_inv gD
  obtain ⟨_, _, _, h8, g8, rfl⟩ := seq_inv g7
  obtain ⟨_, _, _, h9, g9, rfl⟩ := seq_inv g8
  obtain ⟨_, _, _, hl, hi, rfl⟩ := seq_inv g9
  have e := Exec.seq (Exec.seq h1 (Exec.seq h2 (Exec.seq (Exec.seq h3 h4) (Exec.seq h5 (Exec.seq h6
    (Exec.seq h7 (Exec.seq h8 h9))))))) (Exec.seq hl (Exec.seq hi (Exec.seq hR1 hR)))
  simp only [List.append_assoc] at e ⊢
  exact e

/-- What two runs of a program agreeing on `c`'s runs agree on. -/
theorem RelCT.of_exec {P Q : State → State → Prop} {c c' : Prog isa}
    (hc : ∀ s t s', Exec isa c' s t s' → Exec isa c s t s') (h : RelCT isa P c Q) : RelCT isa P c' Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (hc _ _ _ e₁) (hc _ _ _ e₂)

/-- A branch followed by `r`, as each branch followed by `r`. -/
theorem RelCT.ite_seq' {P Q : State → State → Prop} {c : Cond} {t e r : Prog isa}
    (h : RelCT isa P (.ite c (.seq t r) (.seq e r)) Q) : RelCT isa P (.seq (.ite c t e) r) Q := by
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

/-! ## The states at the cuts -/

/-- After `save`'s load: the working space's address in `t0`. -/
def S1 (d : Dt) (t : State) : Prop :=
  ∃ s0, C0 d s0 ∧ (t.gpr .t0 = bOf s0 ∧ t.mem = s0.mem ∧ t.sp = s0.sp) ∧ Keep [.t0] s0 t

/-- After `entry`. -/
def S2 (d : Dt) (v : State) : Prop := ∃ s0, C0 d s0 ∧ CB s0 s0.mem v

/-- Before `dPar`: the flag `X3` is `e mod 2`. -/
def S3 (d : Dt) (t : State) : Prop :=
  ∃ s0, C0 d s0 ∧ ∃ V F, KE s0 V F t ∧ F X3 = Spec.Rsa.os2ip (eB s0) % 2

/-- After `dPar`'s load: `t5` is `e mod 2`. -/
def S4 (d : Dt) (t : State) : Prop :=
  ∃ s0, C0 d s0 ∧ ∃ V F, KE s0 V F t ∧ (t.gpr .t5).toNat = Spec.Rsa.os2ip (eB s0) % 2

/-- The registers `entry` leaves public: the pointers, the lengths and the working space's address. -/
abbrev cbPins : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .a0, .a1, .a7, .s11]

/-- And the working space's `w` and stride. -/
abbrev bodyPins : List Reg := cbPins ++ [.s9, .s10]

theorem CB.pins {s0 s1 x y : State} (sm : Same s0 s1) (cx : CB s0 s0.mem x) (cy : CB s1 s1.mem y) :
    ∀ r ∈ cbPins, x.gpr r = y.gpr r := by
  intro r hr
  simp only [cbPins, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [cx.rs0, cy.rs0, sm.regs _ (by decide)]
  · rw [cx.s1, cy.s1, sm.regs _ (by decide)]
  · rw [cx.s2, cy.s2, sm.regs _ (by decide)]
  · rw [cx.s3, cy.s3, sm.regs _ (by decide)]
  · rw [cx.s4, cy.s4, sm.args 0 (by decide)]
  · rw [cx.s5, cy.s5, sm.args 2 (by decide)]
  · rw [cx.s6, cy.s6, sm.args 4 (by decide)]
  · rw [cx.a0, cy.a0, sm.args 6 (by decide)]
  · rw [cx.a1, cy.a1, sm.regs _ (by decide)]
  · rw [cx.a7, cy.a7, sm.args 7 (by decide)]
  · rw [cx.s11, cy.s11, bOf, bOf, sm.args 8 (by decide)]

theorem St.pins {s0 s1 x y : State} {u u' : List Nat} (sm : Same s0 s1) (cx : St s0 u x) (cy : St s1 u' y) :
    ∀ r ∈ bodyPins, x.gpr r = y.gpr r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact CB.pins sm cx.cb cy.cb r hr
  · have hw : wOf s0 = wOf s1 := by simp only [wOf, pLen, sm.regs .a5 (by decide)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [cx.ws.s9, cy.ws.s9, hw]
    · rw [cx.ws.s10, cy.ws.s10, hw]

theorem pins_S2 : Pins S2 cbPins := fun _ _ _ ⟨_x, hx, cx⟩ ⟨_y, hy, cy⟩ => CB.pins (hx.same hy) cx cy

theorem pins_S3 : Pins S3 bodyPins := fun _ _ _ ⟨_x, hx, _, _, ex, _⟩ ⟨_y, hy, _, _, ey, _⟩ =>
  St.pins (hx.same hy) ex.st ey.st

theorem pins_S4 : Pins S4 bodyPins := fun _ _ _ ⟨_x, hx, _, _, ex, _⟩ ⟨_y, hy, _, _, ey, _⟩ =>
  St.pins (hx.same hy) ex.st ey.st

/-! ## Everything before the branch, by correctness -/

theorem pre_ok {s0 v : State} (h : PreC s0) (c : CB s0 s0.mem v) :
    WP isa pre v fun t => ∃ V F, KE s0 V F t ∧ F X3 = Spec.Rsa.os2ip (eB s0) % 2 := by
  have hpw : Spec.Rsa.os2ip (pB s0) < 2 ^ (8 * pLen s0) := os2ip_bytes_lt _ _ _
  have hqw : Spec.Rsa.os2ip (qB s0) < 2 ^ (8 * pLen s0) := os2ip_bytes_lt _ _ _
  have hew : Spec.Rsa.os2ip (eB s0) < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (os2ip_bytes_lt _ _ _) (Nat.pow_le_pow_right (by decide) (by have := h.e2; omega))
  unfold pre
  simp only [seqs]
  refine WP.seq (WP.mono (setup_ok h c) fun t1 c1 => ?_)
  refine WP.seq (WP.mono (loads_ok h c1) fun t2 ⟨c2, p2, q2, e2⟩ => ?_)
  refine WP.seq (WP.mono (consts_ok h c2 (by decide)) fun t3 ⟨c3, k3, o3⟩ => ?_)
  have z3 : nm s0 t3.mem aZero = 0 := c3.zero (j := aZero) (by decide) (by decide)
  refine WP.seq (WP.mono (primes_ok c3 k3.one z3) fun t4 ⟨c4, o4, p4, q4, pm4, qm4⟩ => ?_)
  have k4 : ∀ j, j < nArr → j ∉ primesArrs → j ∉ constArrs → nm s0 t4.mem j = nm s0 t2.mem j :=
    fun j hj h1 h2 => (o4 j hj h1).trans (o3 j hj h2)
  have one4 : nm s0 t4.mem aOne = 1 := by rw [o4 _ (by decide) (by decide)]; exact k3.one
  have two4 : nm s0 t4.mem aTwo = 2 := by rw [o4 _ (by decide) (by decide)]; exact k3.two
  have three4 : nm s0 t4.mem aThree = 3 := by rw [o4 _ (by decide) (by decide)]; exact k3.three
  have zero4 : nm s0 t4.mem aZero = 0 := by rw [o4 _ (by decide) (by decide)]; exact z3
  have pq4 : nm s0 t4.mem aP < 2 ^ (8 * pLen s0) ∧ nm s0 t4.mem aQ < 2 ^ (8 * pLen s0) := by
    have hp0 : nm s0 t3.mem aP0 = Spec.Rsa.os2ip (pB s0) := (o3 aP0 (by decide) (by decide)).trans p2
    have hq0 : nm s0 t3.mem aQ0 = Spec.Rsa.os2ip (qB s0) := (o3 aQ0 (by decide) (by decide)).trans q2
    rw [p4, q4, hp0, hq0]
    constructor <;> split <;> with_reducible assumption
  have hpm : nm s0 t4.mem aPm < 2 ^ (8 * pLen s0) := by rw [pm4]; have := pq4.1; omega
  have hqm : nm s0 t4.mem aQm < 2 ^ (8 * pLen s0) := by rw [qm4]; have := pq4.2; omega
  have hdv : word t4.mem (bOf s0) (arr (wOf s0) aDv + 8 * wOf s0) = 0 :=
    c4.word_zero (j := aDv) (by decide) (by decide) (by omega)
  refine WP.seq (WP.mono (lcmPart_ok h c4 one4 two4 three4 zero4 hpm hqm hdv) fun t5 ⟨c5, o5, _, dv5⟩ => ?_)
  have e5 := KE.of_st c5 dv5
  have v5 : ∀ j, j < nArr → j ∉ lcmArrs → j ∉ primesArrs → j ∉ constArrs →
      nm s0 t5.mem j = nm s0 t2.mem j := fun j hj h1 h2 h3 => (o5 j hj h1).trans (k4 j hj h2 h3)
  have one5 : nm s0 t5.mem aOne = 1 := by rw [o5 _ (by decide) (by decide)]; exact one4
  have two5 : nm s0 t5.mem aTwo = 2 := by rw [o5 _ (by decide) (by decide)]; exact two4
  have three5 : nm s0 t5.mem aThree = 3 := by rw [o5 _ (by decide) (by decide)]; exact three4
  have zero5 : nm s0 t5.mem aZero = 0 := by rw [o5 _ (by decide) (by decide)]; exact zero4
  have ve5 : nm s0 t5.mem aE = Spec.Rsa.os2ip (eB s0) := by
    rw [v5 _ (by decide) (by decide) (by decide) (by decide)]; exact e2
  refine WP.seq (WP.mono (eFlags_ok e5 one5 three5) fun t6 ⟨V6, F6, e6, o6, p6, x3, x4, x5⟩ => ?_)
  have ve6 : V6 aE = Spec.Rsa.os2ip (eB s0) := by rw [o6 _ (by decide)]; exact ve5
  have one6 : V6 aOne = 1 := by rw [o6 _ (by decide)]; exact one5
  have two6 : V6 aTwo = 2 := by rw [o6 _ (by decide)]; exact two5
  have three6 : V6 aThree = 3 := by rw [o6 _ (by decide)]; exact three5
  have zero6 : V6 aZero = 0 := by rw [o6 _ (by decide)]; exact zero5
  have hew6 : V6 aE < 2 ^ 64 := by rw [ve6]; exact hew
  have x3' : F6 X3 = V6 aE % 2 := by rw [x3, o6 aE (by decide)]
  have x5' : F6 X5 = if V6 aE < 3 then 1 else 0 := by rw [x5, o6 aE (by decide)]
  refine WP.seq (WP.mono (dOdd_ok h e6 hew6 one6 two6 three6 zero6 x3' x5')
    fun t7 ⟨V7, F7, e7, o7, p7, _, _, _, _, x6⟩ => ?_)
  have one7 : V7 aOne = 1 := by rw [o7 _ (by decide) (by decide), o6 _ (by decide)]; exact one5
  have b4 : F7 X4 ≤ 1 := by
    rw [p7 X4 (by decide) (by decide) (by decide) (by decide), x4]; split <;> omega
  have b6 : F7 X6 ≤ 1 := by rw [x6]; split <;> omega
  refine WP.mono (dOne_ok e7 one7 b4 b6) fun t ⟨V8, F8, e8, _, p8, _, _⟩ => ⟨V8, F8, e8, ?_⟩
  rw [p8 X3 (by decide) (by decide) (by decide), p7 X3 (by decide) (by decide) (by decide) (by decide), x3]
  exact congrArg (· % 2) ve5

/-! ## The two runs -/

theorem pre_rel : RelCT isa (Two S2) pre (Two S3) :=
  two_post (two_taint cbPins pins_S2 (by taint_decide)) fun _ v ⟨s0, c0, c⟩ =>
    WP.mono (pre_ok (preC_of c0.1) c) fun _ ⟨V, F, e, x3⟩ => ⟨s0, c0, V, F, e, x3⟩

theorem ld_rel : RelCT isa (Two S3) ldX3 (Two S4) :=
  two_post (two_taint bodyPins pins_S3 (by taint_decide)) fun _ _ ⟨s0, c0, V, F, e, x3⟩ =>
    WP.mono (ldX3_ok e) fun _ ⟨e', t5⟩ => ⟨s0, c0, V, F, e', t5.trans x3⟩

theorem shaped_rel : RelCT isa (Two S2) shaped fun _ _ => True := by
  refine RelCT.seq (R := Two S3) pre_rel (RelCT.seq (R := Two S4) ld_rel (RelCT.ite_seq' (RelCT.ite ?_ ?_ ?_)))
  · rintro s₁ s₂ ⟨a, ⟨x, hx, -, -, -, x5⟩, ⟨y, hy, -, -, -, y5⟩, -⟩
    rw [Steps.eval_nonzero, Steps.eval_nonzero, BitVec.eq_of_toNat_eq (x5.trans (by rw [(hx.same hy).e, y5]))]
  · exact RelCT.mono (two_taint (Φ := S4) bodyPins pins_S4 (by taint_decide)) (fun _ _ h => h.1)
      fun _ _ h => h
  · exact RelCT.mono (two_taint (Φ := S4) bodyPins pins_S4 (by taint_decide)) (fun _ _ h => h.1)
      fun _ _ h => h

theorem argRegs_ne_t0 : ∀ r ∈ argRegs, r ∉ ([.t0] : List Reg) := by decide

theorem key_rel : RelCT isa (Two C0) code fun _ _ => True := by
  unfold code
  rw [entry_eq, save_eq]
  refine RelCT.seq (R := Two S2) (RelCT.block_append (RelCT.seq (R := Two S1) ?_ ?_))
    (RelCT.of_exec (fun _ _ _ => exec_shaped) shaped_rel)
  · -- `save`'s first part.
    refine two_post (two_taint [] (fun _ _ _ _ _ r hr => absurd hr List.not_mem_nil) (by taint_decide))
      fun a s c0 => ?_
    have h := preC_of c0.1
    exact WP.mono (save1_ok s (i := 8) (by decide) (arg_in (by rw [h.hrd]; simp) (by decide)) (arg_al h 8))
      fun t ⟨tt, k⟩ => ⟨s, c0, tt, k⟩
  · -- `save`'s second part and the moves.
    refine two_post (two_taint (.t0 :: argRegs) ?_ (by taint_decide)) fun a s ⟨s0, c0, ht⟩ => ?_
    · rintro a s₁ s₂ ⟨x, hx, ⟨tx, -, -⟩, kx⟩ ⟨y, hy, ⟨ty, -, -⟩, ky⟩ r hr
      have hs := hx.same hy
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [tx, ty, bOf, bOf, hs.args 8 (by decide)]
      · rw [kx.gpr (argRegs_ne_t0 r hr), ky.gpr (argRegs_ne_t0 r hr), hs.regs r hr]
    have h := preC_of c0.1
    have hz := h.zk
    rw [WP.block_append_iff]
    exact WP.mono (save2_ok s0 h.scr (by omega_arith) ht) fun u hu => WP.mono (moves_ok h hu) fun v c =>
      ⟨s0, c0, c⟩

theorem key_ct : ConstantTime isa (Spec.RsaKeyGen.keyContract RISCV64.abi).pre
    (Spec.RsaKeyGen.keyContract RISCV64.abi).pub code :=
  RelCT.constantTime (key_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨dataOf s, ⟨hs, rfl⟩, ⟨ht, (pub_data hp).symm⟩, (same_of (pub_data hp)).sp⟩) fun _ _ h => h)

end VG.Proof.RsaKeyGen.RISCV64.Key
