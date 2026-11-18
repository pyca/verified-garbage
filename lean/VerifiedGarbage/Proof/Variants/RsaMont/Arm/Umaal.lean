module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCallFios2
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineFnBody
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTFnBody
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithLaw
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Bignum.Arm.Fios2.Value
public import VerifiedGarbage.Impl.Bignum.Arm.MontCallWith
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Bignum.Arm.MontCallContract
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.Bignum.Arm.DownRowUmaal
public import VerifiedGarbage.Proof.Framework.Arm.CallerTransform
public import VerifiedGarbage.Proof.Framework.SubstLocal
public import VerifiedGarbage.Impl.Bignum.Arm.Row
import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmetic
import VerifiedGarbage.Impl.Bignum.Arm.DownRow
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineLoop
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Bignum.Arm.Fios2
import VerifiedGarbage.Proof.Bignum.Arm.Fios2.Taint
public import VerifiedGarbage.Proof.Bignum.Arm.FiosState
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
import Init.Data.BitVec.Lemmas
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.FiosAdvance
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Bignum.Arm.Mac
import VerifiedGarbage.Proof.Bignum.Arm.FiosArithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.RoundMeta
import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishSteps
public import VerifiedGarbage.Proof.Bignum.Arm.Fios2.CT
public import VerifiedGarbage.Proof.Bignum.Arm.RoundCT
public import VerifiedGarbage.Impl.Bignum.Arm.MontPipeline

/-! ### `Bignum.Arm.MontCallFios2`, which only this module used -/

section

/-! ### `Bignum.Arm.MontCallWithContract`, which only this module used -/

section

/-! The shared reviewed Montgomery contract for a supplied dispatcher. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (wOf Operand)

theorem montCallWith_contract_correct (arithmetic : Prog isa) (law : CallArithmeticLaw arithmetic) (s : State) (h : (Proof.Rsa.Mont.mulContract abi 40).pre s) :
    ∃ tr t, Exec isa (MontCallWith.code arithmetic) s tr t ∧ abiPreserved s t ∧
      (Proof.Rsa.Mont.mulContract abi 40).post s t := by
  obtain ⟨input, ho, ha, hb⟩ := montCall_contract_pre s h
  obtain ⟨tr, t, run, preserved, post⟩ := montCallWithFn_ok arithmetic law s input ho ha hb
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  obtain argValue : stackArg s 0 = callStackB s := by simp [stackArg, stackArgAddr, callStackB]
  rw [argValue]
  exact post

theorem montCallWith_contract_ct (arithmetic : Prog isa) (law : CallArithmeticLaw arithmetic) : ConstantTime isa (Proof.Rsa.Mont.mulContract abi 40).pre
    (Proof.Rsa.Mont.mulContract abi 40).pub (MontCallWith.code arithmetic) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨is, ho, ha, hb⟩ := montCall_contract_pre s hs
  obtain ⟨it, _, _, _⟩ := montCall_contract_pre t ht
  sig_pub [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, width, p0, p1, p2, p3, pb⟩ := hp
  change [wOf s.mem (State.addr (s.gpr .r0))] = [wOf t.mem (State.addr (t.gpr .r0))] at width
  obtain wb := List.singleton_inj.mp width
  obtain bb : callStackB s = callStackB t := by simpa only [stackArg, stackArgAddr, Nat.mul_zero, BitVec.add_zero, callStackB] using pb
  rw [← wb, ← p0, ← p1, ← p2, ← p3, ← bb] at it
  exact (montCallWithFn_ct arithmetic law ho ha hb s t tr1 tr2 u v ⟨is, it, sp⟩ e1 e2).1

theorem montCallWith_verified (arithmetic : Prog isa) (law : CallArithmeticLaw arithmetic) :
    Verified target (MontCallWith.code arithmetic) (Proof.Rsa.Mont.mulContract abi 40) :=
  ⟨montCallWith_contract_correct arithmetic law, montCallWith_contract_ct arithmetic law,
    montCall_contract_sat⟩

theorem montCallWith_stack (arithmetic : Prog isa) (law : CallArithmeticLaw arithmetic) :
    FrameStack.armStack (MontCallWith.code arithmetic) ≤ 40 := by
  simp only [MontCallWith.code, FrameStack.armStack, law.stack]
  decide

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.UmaalArithmeticCaller`, which only this module used -/

section

/-! Generic callers inherit both row choices without changing named calls. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/RowCaller.lean`, which only this module imported.
section

/-! A row implementation can optimize inline caller arithmetic without touching calls. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem armStack_rowLocal (replacement : Prog isa)
    (stack : FrameStack.armStack replacement = 0) (c : Prog isa) :
    FrameStack.armStack (Code.substLocal row replacement c) ≤ FrameStack.armStack c := by
  induction c with
  | block _ => simp only [Code.substLocal]; split <;> simp [FrameStack.armStack, stack]
  | seq a b iha ihb =>
    simp only [Code.substLocal]; split
    · simp [stack]
    · simp only [FrameStack.armStack]; omega_using [iha, ihb]
  | ite _ t e iht ihe =>
    simp only [Code.substLocal]; split
    · simp [stack]
    · simp only [FrameStack.armStack]; omega_using [iht, ihe]
  | loop b _ ih =>
    simp only [Code.substLocal]; split
    · simp [stack]
    · simpa only [FrameStack.armStack] using ih
  | call _ _ _ => exact Nat.le_refl _
  | icall => exact Nat.le_refl _
  | frame i _ _ ih =>
    simp only [Code.substLocal]; split
    · simp [stack]
    · cases i <;> simp only [FrameStack.armStack] <;> omega_using [ih]

/-- Any verified call-free, frame-free row replacement supplies a caller decorator. -/
def rowCaller (replacement : Prog isa) (sim : Sim row replacement)
    (stack : FrameStack.armStack replacement = 0) (calls : replacement.calls = []) : CallerTransform where
  code := Code.substLocal row replacement
  sim := by intro c s tr s' h; exact Exec.substLocal sim h
  stack_le := armStack_rowLocal replacement stack
  calls_eq := fun _ => Code.calls_substLocal (by rfl) calls

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/RowUmaalCaller.lean`, which only this module imported.
section

/-! UMAAL arithmetic inherited by callers of the shared Montgomery backend. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG.Impl.Bignum.Arm

def umaalCaller : VG.Arm.CallerTransform := rowCaller rowU row_sim rfl rfl

end VG.Proof.Bignum.Arm
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem armStack_downLocal (c : Prog isa) :
    FrameStack.armStack (Code.substLocal DownRow.code DownRow.codeU c) ≤ FrameStack.armStack c := by
  induction c with
  | block _ => simp only [Code.substLocal]; split <;> simp [DownRowUmaal.codeU_stack, FrameStack.armStack]
  | seq a b iha ihb =>
    simp only [Code.substLocal]; split
    · simp [DownRowUmaal.codeU_stack]
    · simp only [FrameStack.armStack]; omega_using [iha, ihb]
  | ite _ t e iht ihe =>
    simp only [Code.substLocal]; split
    · simp [DownRowUmaal.codeU_stack]
    · simp only [FrameStack.armStack]; omega_using [iht, ihe]
  | loop b _ ih =>
    simp only [Code.substLocal]; split
    · simp [DownRowUmaal.codeU_stack]
    · simpa only [FrameStack.armStack] using ih
  | call _ _ _ => exact Nat.le_refl _
  | icall => exact Nat.le_refl _
  | frame i _ _ ih =>
    simp only [Code.substLocal]; split
    · simp [DownRowUmaal.codeU_stack]
    · cases i <;> simp only [FrameStack.armStack] <;> omega_using [ih]

def downCaller : CallerTransform where
  code := Code.substLocal DownRow.code DownRow.codeU
  sim := by intro c s tr t h;exact Exec.substLocal DownRowUmaal.code_sim h
  stack_le := armStack_downLocal
  calls_eq := fun c => Code.calls_substLocal (M := isa)
    (a := DownRow.code) (b := DownRow.codeU) (c := c) (by rfl) (by rfl)

def umaalArithmeticCaller : CallerTransform where
  code := fun c => downCaller.code (umaalCaller.code c)
  sim := by intro c s tr t h;exact downCaller.sim _ (umaalCaller.sim c h)
  stack_le := fun c => Nat.le_trans (downCaller.stack_le _) (umaalCaller.stack_le c)
  calls_eq := fun c => (downCaller.calls_eq _).trans (umaalCaller.calls_eq c)

end VG.Proof.Bignum.Arm

end

end


/-! The two-row round supplies the shared callable Montgomery backend. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem montCallFios2_law
    (law : MontPipeline.LoopLaw Fios2.round)
    (ctLaw : MontPipeline.LoopCTLaw Fios2.round) :
    CallArithmeticLaw MontCallFios2.arithmetic where
  correct := by
    intro s base len w o a b h ho ha hb
    obtain body := MontPipeline.fnBody_ok Fios2.round law s h.input.workspace h.input.layout
      ho ha hb h.input.ptr h.input.outIndex h.input.aIndex h.input.bIndex
      (by rw [h.input.width]; exact h.input.inverse)
      (by rw [h.input.width]; exact h.input.operand)
    simpa only [MontCallFios2.arithmetic, h.input.width] using body
  ct := by
    intro base len w o a b ho ha hb fit s t tr1 tr2 u v h e1 e2
    exact MontPipeline.fnBody_ct Fios2.round law ctLaw ho ha hb fit
      s t tr1 tr2 u v ⟨h.1.input, h.2.1.input⟩ e1 e2
  stack := rfl

def montCallFios2_backend
    (law : MontPipeline.LoopLaw Fios2.round)
    (ctLaw : MontPipeline.LoopCTLaw Fios2.round) : MontBackend where
  mul := MontCallFios2.code
  verified := montCallWith_verified _ (montCallFios2_law law ctLaw)
  correct := montCallWithFn_ok _ (montCallFios2_law law ctLaw)
  rawCT := montCallWithFn_ct _ (montCallFios2_law law ctLaw)
  stackOk := montCallWith_stack _ (montCallFios2_law law ctLaw)
  caller := umaalArithmeticCaller
  suffix := "_umaal"
  features := ["umaal"]

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.Fios2.Round`, which only this module used -/

section

/-! ### `Bignum.Arm.Fios2.Code`, which only this module used -/

section

/-! ### `Bignum.Arm.Fios2.First`, which only this module used -/

section

/-! The first words of both rows: each quotient cancels the low word it is
computed from, and the scan starts with nothing stored. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/Fios2/Cancel.lean`, which only this module imported.
section

/-! A quotient `q = m' u` cancels the low word of `u + q m`. -/

section
namespace VG.Proof.Bignum.Arm.Fios2

theorem cancel_low {u q inv lo hi : BitVec 32} {m c : Nat} (hq : q = inv * u)
    (h : lo.toNat + 2 ^ 32 * hi.toNat = m * q.toNat + u.toNat + c) (hc : c = 0)
    (hinv : (m * inv.toNat + 1) % 2 ^ 32 = 0) : lo = 0 := by
  apply BitVec.eq_of_toNat_eq
  obtain cancel := VG.Proof.Bignum.Arm.mont_low u.toNat inv.toNat m hinv
  obtain qN : q.toNat = u.toNat * inv.toNat % 2 ^ 32 := by
    rw [hq, BitVec.toNat_mul, Nat.mul_comm]
  rw [qN, hc, Nat.add_zero] at h
  have lr := lo.isLt
  change lo.toNat = 0
  rw [Nat.mul_comm m] at h
  omega

end VG.Proof.Bignum.Arm.Fios2
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mul wp_dp op2_imm dpVal)

/-- The registers `first` writes. -/
abbrev firstClobbers : List Reg := [.r2, .r3, .r5, .r6, .r7, .r8, .r10, .r11, .lr]

theorem first_ok (s : State) {base : BitVec 32} {size acc b mod n : Nat}
    (ctx : Fios.Ctx s base size acc b mod n) (positive : 4 ≤ n)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 acc)
    (source : s.gpr .r12 = base + BitVec.ofNat 32 b)
    (modulus : s.gpr .r4 = base + BitVec.ofNat 32 mod)
    (count : s.gpr .lr = BitVec.ofNat 32 n)
    (inv2 : s.gpr .r10 = s.gpr .r2)
    (c7 : s.gpr .r7 = 0) (c8 : s.gpr .r8 = 0) (c5 : s.gpr .r5 = 0) (c11 : s.gpr .r11 = 0)
    (inverse : (w32 s.mem (State.addr base) mod * (s.gpr .r2).toNat + 1) % 2 ^ 32 = 0) :
    WP isa VG.Impl.Bignum.Arm.Fios2.first s fun t =>
      Inv s (s.gpr .r1) (t.gpr .r2) (s.gpr .r9) (t.gpr .r10) base acc b mod n 0 0 t := by
  have nowrap := ctx.workspace.nowrap
  have outf := ctx.accFits
  have inf := ctx.bFits
  have modf := ctx.mFits
  have ws := ctx.workspace
  let K : List Reg := firstClobbers
  -- r6 := T₀
  rw [VG.Impl.Bignum.Arm.Fios2.first, WP.seq_iff]
  refine wp_ldr (a := off (State.addr base) (acc + 0)) (by decide) (ws.ea ptr (by omega_arith)) (ws.read (by omega_arith))
    fun s1 h1 => WP.block_nil ?_
  obtain k1 : Rest K s s1 := h1.rest (by decide)
  -- r6 + 2³² r7 := T₀ + B₀ a₀
  rw [WP.seq_iff]
  refine WP.mono (macAt_ok s1 (ws.congr k1.wr) ((k1.gpr .r12 (by decide)).trans source) (k := 0)
    (by omega_arith) (by decide) (c := .r7) (x := .r1) (by decide) (by decide) (by decide)) ?_
  rintro s2 ⟨x1, m2, r2⟩
  obtain k2 : Rest K s s2 := k1.trans (r2.mono (by decide))
  -- q₀ := m' (r6)
  rw [WP.seq_iff]
  refine wp_mul fun s3 h3 => WP.block_nil ?_
  obtain k3 : Rest K s s3 := k2.trans (h3.rest (by decide))
  -- r6 + 2³² r8 := q₀ M₀ + r6, low word 0
  rw [WP.seq_iff]
  refine WP.mono (macAt_ok s3 (ws.congr k3.wr) ((k3.gpr .r4 (by decide)).trans modulus) (k := 0)
    (by omega_arith) (by decide) (c := .r8) (x := .r2) (by decide) (by decide) (by decide)) ?_
  rintro s4 ⟨x2, m4, r4⟩
  obtain k4 : Rest K s s4 := k3.trans (r4.mono (by decide))
  -- r6 := T₁
  rw [WP.seq_iff]
  refine wp_ldr (a := off (State.addr base) (acc + 4)) (by decide)
    ((ws.congr k4.wr).ea ((k4.gpr .r0 (by decide)).trans ptr) (by omega_arith))
    ((ws.congr k4.wr).read (by omega_arith))
    fun s5 h5 => WP.block_nil ?_
  obtain k5 : Rest K s s5 := k4.trans (h5.rest (by decide))
  -- r6 + 2³² r7 := T₁ + B₁ a₀ + r7
  rw [WP.seq_iff]
  refine WP.mono (macAt_ok s5 (ws.congr k5.wr) ((k5.gpr .r12 (by decide)).trans source) (k := 4)
    (by omega_arith) (by decide) (c := .r7) (x := .r1) (by decide) (by decide) (by decide)) ?_
  rintro s6 ⟨x3, m6, r6⟩
  obtain k6 : Rest K s s6 := k5.trans (r6.mono (by decide))
  -- r6 + 2³² r8 := M₁ q₀ + r6 + r8: row i's output word 0
  rw [WP.seq_iff]
  refine WP.mono (macAt_ok s6 (ws.congr k6.wr) ((k6.gpr .r4 (by decide)).trans modulus) (k := 4)
    (by omega_arith) (by decide) (c := .r8) (x := .r2) (by decide) (by decide) (by decide)) ?_
  rintro s7 ⟨x4, m7, r7⟩
  obtain k7 : Rest K s s7 := k6.trans (r7.mono (by decide))
  -- r6 + 2³² r5 := B₀ a₁ + r6
  rw [WP.seq_iff]
  refine WP.mono (macAt_ok s7 (ws.congr k7.wr) ((k7.gpr .r12 (by decide)).trans source) (k := 0)
    (by omega_arith) (by decide) (c := .r5) (x := .r9) (by decide) (by decide) (by decide)) ?_
  rintro s8 ⟨x5, m8, r8⟩
  obtain k8 : Rest K s s8 := k7.trans (r8.mono (by decide))
  -- q₁ := m' (r6)
  rw [WP.seq_iff]
  refine wp_mul fun s9 h9 => WP.block_nil ?_
  obtain k9 : Rest K s s9 := k8.trans (h9.rest (by decide))
  -- r6 + 2³² r11 := M₀ q₁ + r6, low word 0
  rw [WP.seq_iff]
  refine WP.mono (macAt_ok s9 (ws.congr k9.wr) ((k9.gpr .r4 (by decide)).trans modulus) (k := 0)
    (by omega_arith) (by decide) (c := .r11) (x := .r10) (by decide) (by decide) (by decide)) ?_
  rintro s10 ⟨x6, m10, r10⟩
  obtain k10 : Rest K s s10 := k9.trans (r10.mono (by decide))
  -- the count
  refine wp_dp (op2_imm (by decide)) fun t ht => WP.block_nil ?_
  obtain kt : Rest K s t := k10.trans (ht.rest (by decide))
  have keep (r : Reg) (h : r ∉ K) : t.gpr r = s.gpr r := kt.gpr r h
  -- registers through the steps
  obtain q0t : t.gpr .r2 = s3.gpr .r2 := by
    rw [ht.other .r2 (by decide), r10.gpr .r2 (by decide), h9.other .r2 (by decide), r8.gpr .r2 (by decide),
      r7.gpr .r2 (by decide), r6.gpr .r2 (by decide), h5.other .r2 (by decide), r4.gpr .r2 (by decide)]
  obtain q1t : t.gpr .r10 = s9.gpr .r10 := by
    rw [ht.other .r10 (by decide), r10.gpr .r10 (by decide)]
  obtain q0 : s3.gpr .r2 = s.gpr .r2 * s2.gpr .r6 := by
    rw [h3.gpr, r2.gpr .r2 (by decide), h1.other .r2 (by decide)]
  obtain q1 : s9.gpr .r10 = s.gpr .r2 * s8.gpr .r6 := by
    rw [h9.gpr, r8.gpr .r10 (by decide), r7.gpr .r10 (by decide), r6.gpr .r10 (by decide),
      h5.other .r10 (by decide), r4.gpr .r10 (by decide), h3.other .r10 (by decide),
      r2.gpr .r10 (by decide), h1.other .r10 (by decide), inv2]
  -- memory: unchanged throughout
  obtain mem2 : s2.mem = s.mem := m2.trans h1.mem
  obtain mem4 : s4.mem = s.mem := m4.trans (h3.mem.trans mem2)
  obtain mem6 : s6.mem = s.mem := m6.trans (h5.mem.trans mem4)
  obtain mem7 : s7.mem = s.mem := m7.trans mem6
  obtain mem8 : s8.mem = s.mem := m8.trans mem7
  obtain mem10 : s10.mem = s.mem := m10.trans (h9.mem.trans mem8)
  obtain memt : t.mem = s.mem := ht.mem.trans mem10
  -- each product in terms of `s`, the quotients and the words in flight
  obtain s1r1 : s1.gpr .r1 = s.gpr .r1 := h1.other .r1 (by decide)
  obtain s5r1 : s5.gpr .r1 = s.gpr .r1 := by
    rw [h5.other .r1 (by decide), r4.gpr .r1 (by decide), h3.other .r1 (by decide), r2.gpr .r1 (by decide), s1r1]
  obtain s7r9 : s7.gpr .r9 = s.gpr .r9 := by
    rw [r7.gpr .r9 (by decide), r6.gpr .r9 (by decide), h5.other .r9 (by decide), r4.gpr .r9 (by decide),
      h3.other .r9 (by decide), r2.gpr .r9 (by decide), h1.other .r9 (by decide)]
  obtain s6r2 : s6.gpr .r2 = s3.gpr .r2 := by
    rw [r6.gpr .r2 (by decide), h5.other .r2 (by decide), r4.gpr .r2 (by decide)]
  obtain e1 : (s2.gpr .r6).toNat + 2 ^ 32 * (s2.gpr .r7).toNat =
      w32 s.mem (State.addr base) b * (s.gpr .r1).toNat + w32 s.mem (State.addr base) acc := by
    rw [h1.mem, s1r1, h1.gpr, h1.other .r7 (by decide), c7] at x1
    simpa only [Nat.add_zero, w32, show (0 : BitVec 32).toNat = 0 from rfl] using x1
  obtain x2' : (s4.gpr .r6).toNat + 2 ^ 32 * (s4.gpr .r8).toNat =
      w32 s.mem (State.addr base) mod * (s3.gpr .r2).toNat + (s2.gpr .r6).toNat + 0 := by
    rw [h3.mem, mem2, h3.other .r6 (by decide), h3.other .r8 (by decide), r2.gpr .r8 (by decide),
      h1.other .r8 (by decide), c8] at x2
    simpa only [Nat.add_zero, show (0 : BitVec 32).toNat = 0 from rfl] using x2
  obtain z1 : s4.gpr .r6 = 0 := cancel_low q0 x2' rfl inverse
  obtain e2 : 0 + 2 ^ 32 * (s4.gpr .r8).toNat =
      w32 s.mem (State.addr base) mod * (s3.gpr .r2).toNat + (s2.gpr .r6).toNat := by
    rw [z1, Nat.add_zero] at x2'
    exact x2'
  obtain e3 : (s6.gpr .r6).toNat + 2 ^ 32 * (s6.gpr .r7).toNat =
      w32 s.mem (State.addr base) (b + 4) * (s.gpr .r1).toNat + w32 s.mem (State.addr base) (acc + 4) +
        (s2.gpr .r7).toNat := by
    rw [h5.mem, s5r1, h5.gpr, mem4, h5.other .r7 (by decide), r4.gpr .r7 (by decide),
      h3.other .r7 (by decide)] at x3
    simpa only [w32] using x3
  obtain e4 : (s7.gpr .r6).toNat + 2 ^ 32 * (s7.gpr .r8).toNat =
      w32 s.mem (State.addr base) (mod + 4) * (s3.gpr .r2).toNat + (s6.gpr .r6).toNat +
        (s4.gpr .r8).toNat := by
    rw [mem6, s6r2, r6.gpr .r8 (by decide), h5.other .r8 (by decide)] at x4
    exact x4
  obtain e5 : (s8.gpr .r6).toNat + 2 ^ 32 * (s8.gpr .r5).toNat =
      w32 s.mem (State.addr base) b * (s.gpr .r9).toNat + (s7.gpr .r6).toNat := by
    rw [mem7, s7r9, r7.gpr .r5 (by decide), r6.gpr .r5 (by decide), h5.other .r5 (by decide),
      r4.gpr .r5 (by decide), h3.other .r5 (by decide), r2.gpr .r5 (by decide), h1.other .r5 (by decide),
      c5] at x5
    simpa only [Nat.add_zero, show (0 : BitVec 32).toNat = 0 from rfl] using x5
  obtain x6' : (s10.gpr .r6).toNat + 2 ^ 32 * (s10.gpr .r11).toNat =
      w32 s.mem (State.addr base) mod * (s9.gpr .r10).toNat + (s8.gpr .r6).toNat + 0 := by
    rw [h9.mem, mem8, h9.other .r6 (by decide), h9.other .r11 (by decide), r8.gpr .r11 (by decide),
      r7.gpr .r11 (by decide), r6.gpr .r11 (by decide), h5.other .r11 (by decide), r4.gpr .r11 (by decide),
      h3.other .r11 (by decide), r2.gpr .r11 (by decide), h1.other .r11 (by decide), c11] at x6
    simpa only [Nat.add_zero, show (0 : BitVec 32).toNat = 0 from rfl] using x6
  obtain z2 : s10.gpr .r6 = 0 := cancel_low q1 x6' rfl inverse
  obtain e6 : 0 + 2 ^ 32 * (s10.gpr .r11).toNat =
      w32 s.mem (State.addr base) mod * (s9.gpr .r10).toNat + (s8.gpr .r6).toNat := by
    rw [z2, Nat.add_zero] at x6'
    exact x6'
  obtain total := first_value e1 e2 e3 e4 e5 e6
  -- the carries at the end
  obtain t7 : t.gpr .r7 = s6.gpr .r7 := by
    rw [ht.other .r7 (by decide), r10.gpr .r7 (by decide), h9.other .r7 (by decide), r8.gpr .r7 (by decide),
      r7.gpr .r7 (by decide)]
  obtain t8 : t.gpr .r8 = s7.gpr .r8 := by
    rw [ht.other .r8 (by decide), r10.gpr .r8 (by decide), h9.other .r8 (by decide), r8.gpr .r8 (by decide)]
  obtain t5 : t.gpr .r5 = s8.gpr .r5 := by
    rw [ht.other .r5 (by decide), r10.gpr .r5 (by decide), h9.other .r5 (by decide)]
  obtain t11 : t.gpr .r11 = s10.gpr .r11 := ht.other .r11 (by decide)
  refine ⟨by omega_arith, by omega_arith, ?_, ?_, ?_, ?_, keep .r1 (by decide), rfl, keep .r9 (by decide), rfl,
    by rw [memt, Nat.mul_zero]; exact Outside.refl _ _ _ _, ?_, kt.mono (by decide)⟩
  · rw [keep .r0 (by decide), ptr, Nat.mul_zero, Nat.add_zero]
  · rw [keep .r12 (by decide), source, Nat.mul_zero, Nat.add_zero]
  · rw [keep .r4 (by decide), modulus, Nat.mul_zero, Nat.add_zero]
  · rw [ht.gpr, dpVal, r10.gpr .lr (by decide), h9.other .lr (by decide), r8.gpr .lr (by decide),
      r7.gpr .lr (by decide), r6.gpr .lr (by decide), h5.other .lr (by decide), r4.gpr .lr (by decide),
      h3.other .lr (by decide), r2.gpr .lr (by decide), h1.other .lr (by decide), count, Nat.sub_zero]
    exact BitVec.ofNat_sub_ofNat_of_le n 2 (by decide) (by omega_arith)
  · rw [carries, t7, t8, t5, t11, q0t, q1t]
    simp only [val32, Nat.zero_add, Nat.mul_zero, Nat.add_zero, show 32 * 2 = 64 from rfl]
    rw [show b + 4 = b + 4 from rfl] -- keep the offsets as `total` states them
    simpa only [Nat.mul_comm (w32 s.mem (State.addr base) b) (s.gpr .r9).toNat,
      Nat.mul_comm (w32 s.mem (State.addr base) mod) (s9.gpr .r10).toNat] using total

end VG.Proof.Bignum.Arm.Fios2

end

end

/-! ### `Bignum.Arm.Fios2.Loop`, which only this module used -/

section

/-! ### `Bignum.Arm.Fios2.StepInv`, which only this module used -/

section

/-! ### `Bignum.Arm.Fios2.Step`, which only this module used -/

section

/-! One step of the two-row scan: a word of row `i` and one of row `i + 1`. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str)

/-- With `r0`, `r12` and `r4` at offsets `d`, `bb` and `mm`: the word at
`d + k + 8` plus row `i`'s products with the words at `bb + k + 8` and
`mm + k + 8` and row `i + 1`'s with those at `bb + k + 4` and `mm + k + 4`,
plus the carries, is the word stored at `d + k` and the new carries. -/
theorem step_ok (s : State) {base : BitVec 32} {size d bb mm k : Nat}
    (ws : Workspace s base size) (hk : k + 8 < 4096)
    (fd : d + k + 12 ≤ size) (fb : bb + k + 12 ≤ size) (fm : mm + k + 12 ≤ size)
    (pd : s.gpr .r0 = base + BitVec.ofNat 32 d)
    (pb : s.gpr .r12 = base + BitVec.ofNat 32 bb)
    (pm : s.gpr .r4 = base + BitVec.ofNat 32 mm) :
    WP isa (VG.Impl.Bignum.Arm.Fios2.step k) s fun t =>
      (t.gpr .r6).toNat + 2 ^ 32 * carries t =
        w32 s.mem (State.addr base) (d + k + 8) +
        (s.gpr .r1).toNat * w32 s.mem (State.addr base) (bb + k + 8) +
        (s.gpr .r2).toNat * w32 s.mem (State.addr base) (mm + k + 8) +
        (s.gpr .r9).toNat * w32 s.mem (State.addr base) (bb + k + 4) +
        (s.gpr .r10).toNat * w32 s.mem (State.addr base) (mm + k + 4) + carries s ∧
      t.mem = s.mem.writeW (off (State.addr base) (d + k)) (t.gpr .r6) ∧
      Rest [.r3, .r5, .r6, .r7, .r8, .r11] s t := by
  rw [VG.Impl.Bignum.Arm.Fios2.step, WP.seq_iff]
  refine wp_ldr (a := off (State.addr base) (d + (k + 8))) (by omega_using [hk]) (ws.ea pd (by omega_using [fd]))
    (ws.read (by omega_using [fd])) fun u hu => WP.block_nil ?_
  obtain ru : Rest [.r3, .r5, .r6, .r7, .r8, .r11] s u := hu.rest (by decide)
  obtain wu := ws.congr ru.wr
  rw [WP.seq_iff]
  refine WP.mono (macAt_ok u wu ((ru.gpr .r12 (by decide)).trans pb) (by omega_using [fb]) (by omega_using [hk])
    (c := .r7) (x := .r1) (by decide) (by decide) (by decide)) ?_
  rintro v ⟨vv, vm, rv⟩
  obtain r1 := rv.trans (Rest.refl _ _) |>.mono (ws' := [.r3, .r5, .r6, .r7, .r8, .r11]) (by decide)
  obtain kv : Rest [.r3, .r5, .r6, .r7, .r8, .r11] s v := ru.trans r1
  rw [WP.seq_iff]
  refine WP.mono (macAt_ok v (ws.congr kv.wr) ((kv.gpr .r4 (by decide)).trans pm) (by omega_using [fm]) (by omega_using [hk])
    (c := .r8) (x := .r2) (by decide) (by decide) (by decide)) ?_
  rintro w ⟨ww, wm, rw'⟩
  obtain kw : Rest [.r3, .r5, .r6, .r7, .r8, .r11] s w := kv.trans (rw'.mono (by decide))
  rw [WP.seq_iff]
  refine WP.mono (macAt_ok w (ws.congr kw.wr) ((kw.gpr .r12 (by decide)).trans pb) (by omega_using [fb]) (by omega_using [hk])
    (c := .r5) (x := .r9) (by decide) (by decide) (by decide)) ?_
  rintro x ⟨xv, xm, rx⟩
  obtain kx : Rest [.r3, .r5, .r6, .r7, .r8, .r11] s x := kw.trans (rx.mono (by decide))
  rw [WP.seq_iff]
  refine WP.mono (macAt_ok x (ws.congr kx.wr) ((kx.gpr .r4 (by decide)).trans pm) (by omega_using [fm]) (by omega_using [hk])
    (c := .r11) (x := .r10) (by decide) (by decide) (by decide)) ?_
  rintro y ⟨yv, ym, ry⟩
  obtain ky : Rest [.r3, .r5, .r6, .r7, .r8, .r11] s y := kx.trans (ry.mono (by decide))
  obtain my : y.mem = s.mem := ym.trans (xm.trans (wm.trans (vm.trans hu.mem)))
  obtain py : y.gpr .r0 = base + BitVec.ofNat 32 d := (ky.gpr .r0 (by decide)).trans pd
  refine wp_str (a := off (State.addr base) (d + k)) (by omega_using [hk])
    (by simpa only [Nat.add_assoc] using (ws.congr ky.wr).ea py (imm := k) (by omega_using [fd]))
    (by rw [ky.wr]; exact ws.write (by omega_using [fd])) fun t ht => WP.block_nil ?_
  refine ⟨?_, by rw [ht.mem, my, ht.gpr], ky.trans (ht.rest _)⟩
  -- the carries and scalars through the four products
  obtain c8v : v.gpr .r8 = u.gpr .r8 := rv.gpr .r8 (by decide)
  obtain c5v : v.gpr .r5 = u.gpr .r5 := rv.gpr .r5 (by decide)
  obtain c11v : v.gpr .r11 = u.gpr .r11 := rv.gpr .r11 (by decide)
  obtain c7w : w.gpr .r7 = v.gpr .r7 := rw'.gpr .r7 (by decide)
  obtain c5w : w.gpr .r5 = v.gpr .r5 := rw'.gpr .r5 (by decide)
  obtain c11w : w.gpr .r11 = v.gpr .r11 := rw'.gpr .r11 (by decide)
  obtain c7x : x.gpr .r7 = w.gpr .r7 := rx.gpr .r7 (by decide)
  obtain c8x : x.gpr .r8 = w.gpr .r8 := rx.gpr .r8 (by decide)
  obtain c11x : x.gpr .r11 = w.gpr .r11 := rx.gpr .r11 (by decide)
  obtain c7y : y.gpr .r7 = x.gpr .r7 := ry.gpr .r7 (by decide)
  obtain c8y : y.gpr .r8 = x.gpr .r8 := ry.gpr .r8 (by decide)
  obtain c5y : y.gpr .r5 = x.gpr .r5 := ry.gpr .r5 (by decide)
  obtain s1 : u.gpr .r1 = s.gpr .r1 := ru.gpr .r1 (by decide)
  obtain s2 : v.gpr .r2 = s.gpr .r2 := (rv.gpr .r2 (by decide)).trans (ru.gpr .r2 (by decide))
  obtain s9 : w.gpr .r9 = s.gpr .r9 :=
    (rw'.gpr .r9 (by decide)).trans ((rv.gpr .r9 (by decide)).trans (ru.gpr .r9 (by decide)))
  obtain s10 : x.gpr .r10 = s.gpr .r10 :=
    (rx.gpr .r10 (by decide)).trans ((rw'.gpr .r10 (by decide)).trans
      ((rv.gpr .r10 (by decide)).trans (ru.gpr .r10 (by decide))))
  obtain u6 : (u.gpr .r6).toNat = w32 s.mem (State.addr base) (d + (k + 8)) := by
    rw [hu.gpr]
  obtain u7 : u.gpr .r7 = s.gpr .r7 := hu.other .r7 (by decide)
  obtain u8 : u.gpr .r8 = s.gpr .r8 := hu.other .r8 (by decide)
  obtain u5 : u.gpr .r5 = s.gpr .r5 := hu.other .r5 (by decide)
  obtain u11 : u.gpr .r11 = s.gpr .r11 := hu.other .r11 (by decide)
  rw [hu.mem, s1, u6, u7] at vv
  rw [vm, hu.mem, s2, c8v, u8] at ww
  rw [wm, vm, hu.mem, s9, c5w, c5v, u5] at xv
  rw [xm, wm, vm, hu.mem, s10, c11x, c11w, c11v, u11] at yv
  simp only [carries, ht.gpr, c7y, c7x, c7w, c8y, c8x, c5y]
  rw [Nat.mul_comm (s.gpr .r1).toNat, Nat.mul_comm (s.gpr .r2).toNat, Nat.mul_comm (s.gpr .r9).toNat,
    Nat.mul_comm (s.gpr .r10).toNat]
  simp only [Nat.add_assoc] at vv ww xv yv ⊢
  omega_using [vv, ww, xv, yv]

end VG.Proof.Bignum.Arm.Fios2

end

end


/-! A step of the two-row scan extends the invariant by a word. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem step_inv {s0 s : State} {a0 q0 a1 q1 base : BitVec 32} {size acc b mod n j p : Nat}
    (ctx : Fios.Ctx s0 base size acc b mod n) (inv : Inv s0 a0 q0 a1 q1 base acc b mod n j p s)
    (hj : j + 3 ≤ n) (hp : j ≤ p + 1) :
    WP isa (VG.Impl.Bignum.Arm.Fios2.step (4 * (j - p))) s fun t =>
      Inv s0 a0 q0 a1 q1 base acc b mod n (j + 1) p t := by
  have nowrap := ctx.workspace.nowrap
  have outf := ctx.accFits
  have inf := ctx.bFits
  have modf := ctx.mFits
  have lag := inv.lag
  obtain ws := ctx.workspace.congr inv.rest.wr
  refine WP.mono (step_ok s ws (k := 4 * (j - p)) (by omega_using [hp]) (by omega_using [hj, outf, lag]) (by omega_using [hj, inf, lag]) (by omega_using [hj, modf, lag])
    inv.outPtr inv.bPtr inv.mPtr) ?_
  rintro t ⟨value, mem, rest⟩
  have e (x : Nat) : x + 4 * p + 4 * (j - p) = x + 4 * j := by omega_using [lag]
  rw [e, e, e, inv.scalar0, inv.quotient0, inv.scalar1, inv.quotient1] at value
  rw [e] at mem
  obtain oldT := inv.outside.w32 (d := acc + 4 * j + 8) (by omega_using []) (by omega_using [hj, nowrap, outf])
  obtain oldB2 := inv.outside.w32 (d := b + 4 * j + 8) (by rcases ctx.accB with h | h <;> omega_arith) (by omega_using [hj, nowrap, inf])
  obtain oldM2 := inv.outside.w32 (d := mod + 4 * j + 8) (by rcases ctx.accM with h | h <;> omega_arith) (by omega_using [hj, nowrap, modf])
  obtain oldB1 := inv.outside.w32 (d := b + 4 * j + 4) (by rcases ctx.accB with h | h <;> omega_arith) (by omega_using [hj, nowrap, inf])
  obtain oldM1 := inv.outside.w32 (d := mod + 4 * j + 4) (by rcases ctx.accM with h | h <;> omega_arith) (by omega_using [hj, nowrap, modf])
  rw [oldT, oldB2, oldM2, oldB1, oldM1] at value
  obtain writes := writeW32_outside s.mem (State.addr base) (d := acc + 4 * j) (t.gpr .r6) (by omega_using [hj, nowrap, outf])
  rw [← mem] at writes
  obtain low := writes.val32 (d := acc) (k := j) (by omega_using []) (by omega_using [hj, nowrap, outf])
  obtain top : w32 t.mem (State.addr base) (acc + 4 * j) = (t.gpr .r6).toNat := by
    rw [mem, w32_write_self]
  obtain stored : val32 t.mem (State.addr base) acc (j + 1) =
      val32 s.mem (State.addr base) acc j + 2 ^ (32 * j) * (t.gpr .r6).toNat := by
    rw [val32_succ, low, top]
  have keep (r : Reg) (h : r ∉ [.r3, .r5, .r6, .r7, .r8, .r11]) : t.gpr r = s.gpr r := rest.gpr r h
  refine ⟨by omega_using [hj], by omega_using [hp, lag], (keep .r0 (by decide)).trans inv.outPtr,
    (keep .r12 (by decide)).trans inv.bPtr, (keep .r4 (by decide)).trans inv.mPtr,
    (keep .lr (by decide)).trans inv.count, (keep .r1 (by decide)).trans inv.scalar0,
    (keep .r2 (by decide)).trans inv.quotient0, (keep .r9 (by decide)).trans inv.scalar1,
    (keep .r10 (by decide)).trans inv.quotient1,
    (inv.outside.mono (Nat.le_refl _) (by omega_using [])).trans (writes.mono (by omega_using []) (by omega_using [])), ?_,
    inv.rest.trans (rest.mono (by decide))⟩
  refine value_extend inv.value ?_ stored
  rw [show acc + 4 * (j + 2) = acc + 4 * j + 8 by omega_using [], show b + 4 * (j + 2) = b + 4 * j + 8 by omega_using [],
    show mod + 4 * (j + 2) = mod + 4 * j + 8 by omega_using [], show b + 4 * (j + 1) = b + 4 * j + 4 by omega_using [],
    show mod + 4 * (j + 1) = mod + 4 * j + 4 by omega_using []]
  exact value

end VG.Proof.Bignum.Arm.Fios2

end

end


/-! The two-row scan's loop: two words an iteration over the middle `n - 2`. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

theorem body_ok {s0 s : State} {a0 q0 a1 q1 base : BitVec 32} {size acc b mod n j : Nat}
    (ctx : Fios.Ctx s0 base size acc b mod n) (inv : Inv s0 a0 q0 a1 q1 base acc b mod n j j s)
    (hj : j + 4 ≤ n) :
    WP isa VG.Impl.Bignum.Arm.Fios2.body s fun t =>
      Inv s0 a0 q0 a1 q1 base acc b mod n (j + 2) (j + 2) t ∧ t.z = decide (j + 2 + 2 = n) := by
  obtain small : n < 2 ^ 32 := by have := ctx.workspace.nowrap; have := ctx.accFits; omega_arith
  rw [VG.Impl.Bignum.Arm.Fios2.body, WP.seq_iff]
  obtain first := step_inv ctx inv (by omega_using [hj]) (by omega_using [])
  rw [show 4 * (j - j) = 0 by omega_using []] at first
  refine WP.mono first fun u iu => ?_
  rw [WP.seq_iff]
  obtain second := step_inv ctx iu (by omega_using [hj]) (by omega_using [])
  rw [show 4 * (j + 1 - j) = 4 by omega_using []] at second
  refine WP.mono second fun v iv => ?_
  refine WP.mono (Fios.advance_ok v 2 (Or.inr rfl)) ?_
  rintro t ⟨p0, p12, p4, count, zero, mem, rt⟩
  have keep (r : Reg) (h : r ∉ [.r0, .r12, .r4, .lr]) : t.gpr r = v.gpr r := rt.gpr r h
  refine ⟨⟨by omega_using [hj], by omega_using [], ?_, ?_, ?_, ?_, (keep .r1 (by decide)).trans iv.scalar0,
    (keep .r2 (by decide)).trans iv.quotient0, (keep .r9 (by decide)).trans iv.scalar1,
    (keep .r10 (by decide)).trans iv.quotient1, by rw [mem]; exact iv.outside, ?_,
    iv.rest.trans (rt.mono (by decide))⟩, ?_⟩
  · rw [p0, iv.outPtr, Offset.add_add]; congr 2
  · rw [p12, iv.bPtr, Offset.add_add]; congr 2
  · rw [p4, iv.mPtr, Offset.add_add]; congr 2
  · rw [count, iv.count, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using []) (by omega_using [hj])]; congr 1
  · simp only [carries, mem, keep .r7 (by decide), keep .r8 (by decide), keep .r5 (by decide),
      keep .r11 (by decide)]
    exact iv.value
  · rw [zero, iv.count, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using []) (by omega_using [hj]), ofNat_beq_zero (by omega_using [small])]
    simp only [show n - 2 - j - 2 = 0 ↔ j + 2 + 2 = n by omega_using [hj]]

theorem loop_ok {s0 s : State} {a0 q0 a1 q1 base : BitVec 32} {size acc b mod n : Nat}
    (ctx : Fios.Ctx s0 base size acc b mod n) (inv : Inv s0 a0 q0 a1 q1 base acc b mod n 0 0 s)
    (positive : 4 ≤ n) (even : n % 2 = 0) :
    WP isa VG.Impl.Bignum.Arm.Fios2.loop s (Inv s0 a0 q0 a1 q1 base acc b mod n (n - 2) (n - 2)) := by
  let I := fun k t => ∃ j, j + 2 + 2 * k = n ∧ 0 < k ∧ Inv s0 a0 q0 a1 q1 base acc b mod n j j t
  unfold VG.Impl.Bignum.Arm.Fios2.loop
  refine WP.loop (M := isa) I ?_ ((n - 2) / 2) s ?_
  · intro k t h
    obtain ⟨j, hjk, hk, hj⟩ := h
    refine WP.mono (body_ok ctx hj (by omega_using [hjk, hk])) ?_
    rintro u ⟨hu, hz⟩
    by_cases last : j + 2 + 2 = n
    · left
      refine ⟨?_, ?_⟩
      · change some (!u.z) = some false
        simp only [hz, last, decide_true, Bool.not_true]
      · have index : j + 2 = n - 2 := by omega_using [last]
        simpa only [index] using hu
    · right
      refine ⟨?_, k - 1, by omega_using [hk], j + 2, by omega_using [hjk, hk], by omega_using [hjk, hk, last], hu⟩
      change some (!u.z) = some true
      simp only [hz, last, decide_false, Bool.not_false]
  · exact ⟨0, by omega_using [positive, even], by omega_using [positive], inv⟩

end VG.Proof.Bignum.Arm.Fios2

end

end

/-! ### `Bignum.Arm.Fios2.Top`, which only this module used -/

section

/-! The tops of both rows: row `i`'s top words plus its carries, row `i + 1`'s
last word, and its top plus its carries, stored as three words. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_mov wp_dp op2_imm op2_reg dpVal)

theorem macFrame_rest {rs : List Reg} {s t : State} (h : MacFrame rs s t) : Rest rs s t :=
  ⟨h.regs, h.rd, h.wr, h.sp⟩

/-- With `r0`, `r12` and `r4` at offsets `d`, `bb` and `mm`, the three words
stored at `d`, `d + 4` and `d + 8` are row `i + 1`'s products with the words
at `bb + 4` and `mm + 4`, plus the words at `d + 8` and `d + 12` and the four
carries. -/
theorem top_ok (s : State) {base : BitVec 32} {size d bb mm : Nat}
    (ws : Workspace s base size) (fd : d + 16 ≤ size) (fb : bb + 8 ≤ size) (fm : mm + 8 ≤ size)
    (pd : s.gpr .r0 = base + BitVec.ofNat 32 d)
    (pb : s.gpr .r12 = base + BitVec.ofNat 32 bb)
    (pm : s.gpr .r4 = base + BitVec.ofNat 32 mm)
    (bound : w32 s.mem (State.addr base) (d + 8) + 2 ^ 32 * w32 s.mem (State.addr base) (d + 12) +
      (s.gpr .r7).toNat + (s.gpr .r8).toNat < 2 ^ 64) :
    WP isa VG.Impl.Bignum.Arm.Fios2.top s fun t =>
      ∃ v0 v1 v2 : BitVec 32,
        t.mem = ((s.mem.writeW (off (State.addr base) d) v0).writeW (off (State.addr base) (d + 4)) v1).writeW
          (off (State.addr base) (d + 8)) v2 ∧
        v0.toNat + 2 ^ 32 * (v1.toNat + 2 ^ 32 * v2.toNat) =
          w32 s.mem (State.addr base) (bb + 4) * (s.gpr .r9).toNat +
          w32 s.mem (State.addr base) (mm + 4) * (s.gpr .r10).toNat +
          (w32 s.mem (State.addr base) (d + 8) + 2 ^ 32 * w32 s.mem (State.addr base) (d + 12)) + carries s ∧
        t.gpr .r0 = base + BitVec.ofNat 32 (d + 12) ∧
        Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r11] s t := by
  have nowrap := ws.nowrap
  rw [VG.Impl.Bignum.Arm.Fios2.top, WP.seq_iff]
  -- the last words of b and m, and the top words of the accumulator
  refine wp_ldr (a := off (State.addr base) (bb + 4)) (by decide) (ws.ea pb (by omega_arith)) (ws.read (by omega_arith))
    fun s1 h1 => ?_
  refine wp_ldr (a := off (State.addr base) (mm + 4)) (by decide)
    (by rw [h1.other .r4 (by decide)]; exact ws.ea pm (by omega_arith))
    (by rw [h1.rd, h1.wr]; exact ws.read (by omega_arith)) fun s2 h2 => ?_
  refine wp_ldr (a := off (State.addr base) (d + 8)) (by decide)
    (by rw [h2.other .r0 (by decide), h1.other .r0 (by decide)]; exact ws.ea pd (by omega_arith))
    (by rw [h2.rd, h2.wr, h1.rd, h1.wr]; exact ws.read (by omega_arith)) fun s3 h3 => ?_
  refine wp_ldr (a := off (State.addr base) (d + 12)) (by decide)
    (by rw [h3.other .r0 (by decide), h2.other .r0 (by decide), h1.other .r0 (by decide)]
        exact ws.ea pd (by omega_arith))
    (by rw [h3.rd, h3.wr, h2.rd, h2.wr, h1.rd, h1.wr]; exact ws.read (by omega_arith))
    fun s4 h4 => WP.block_nil ?_
  obtain K4 : Rest [.r1, .r2, .r3, .r4] s s4 :=
    (h1.rest (by decide)).trans ((h2.rest (by decide)).trans ((h3.rest (by decide)).trans (h4.rest (by decide))))
  obtain m4 : s4.mem = s.mem := h4.mem.trans (h3.mem.trans (h2.mem.trans h1.mem))
  obtain b4 : s4.gpr .r1 = s.mem.readW (off (State.addr base) (bb + 4)) 32 := by
    rw [h4.other .r1 (by decide), h3.other .r1 (by decide), h2.other .r1 (by decide), h1.gpr]
  obtain mm4 : s4.gpr .r2 = s.mem.readW (off (State.addr base) (mm + 4)) 32 := by
    rw [h4.other .r2 (by decide), h3.other .r2 (by decide), h2.gpr, h1.mem]
  obtain t3 : s4.gpr .r3 = s.mem.readW (off (State.addr base) (d + 8)) 32 := by
    rw [h4.other .r3 (by decide), h3.gpr, h2.mem, h1.mem]
  obtain t4 : s4.gpr .r4 = s.mem.readW (off (State.addr base) (d + 12)) 32 := by
    rw [h4.gpr, h3.mem, h2.mem, h1.mem]
  obtain t3n : (s4.gpr .r3).toNat = w32 s.mem (State.addr base) (d + 8) := by rw [t3]
  obtain t4n : (s4.gpr .r4).toNat = w32 s.mem (State.addr base) (d + 12) := by rw [t4]
  obtain b4n : (s4.gpr .r1).toNat = w32 s.mem (State.addr base) (bb + 4) := by rw [b4]
  obtain mm4n : (s4.gpr .r2).toNat = w32 s.mem (State.addr base) (mm + 4) := by rw [mm4]
  -- row i's top: r4:r3 += r7, r8
  rw [WP.seq_iff]
  refine WP.mono (addWord_ok s4 .r7 (by
    rw [t3, t4, K4.gpr .r7 (by decide)]; simp only [w32] at bound; omega_arith)) ?_
  rintro s5 ⟨v5, f5⟩
  rw [WP.seq_iff]
  refine WP.mono (addWord_ok s5 .r8 (by
    rw [v5, t3, t4, K4.gpr .r7 (by decide), f5.regs .r8 (by decide), K4.gpr .r8 (by decide)]
    simp only [w32] at bound; omega_arith)) ?_
  rintro s6 ⟨v6, f6⟩
  -- row i + 1's last word
  rw [WP.seq_iff]
  refine WP.mono (Fios.umaal_ok s6 .r3 .r5 .r1 .r9 (by decide)) ?_
  rintro s7 ⟨v7, f7⟩
  rw [WP.seq_iff]
  refine WP.mono (Fios.umaal_ok s7 .r3 .r11 .r2 .r10 (by decide)) ?_
  rintro s8 ⟨v8, f8⟩
  obtain K8 : Rest [.r1, .r2, .r3, .r4, .r5, .r11] s s8 :=
    (K4.mono (by decide)).trans ((macFrame_rest f5).mono (by decide) |>.trans
      ((macFrame_rest f6).mono (by decide) |>.trans ((macFrame_rest f7).mono (by decide) |>.trans
        ((macFrame_rest f8).mono (by decide)))))
  obtain m8 : s8.mem = s.mem := f8.mem.trans (f7.mem.trans (f6.mem.trans (f5.mem.trans m4)))
  obtain p8 : s8.gpr .r0 = base + BitVec.ofNat 32 d := (K8.gpr .r0 (by decide)).trans pd
  obtain ws8 := ws.congr K8.wr
  -- store it, then row i + 1's top: r4:r3 := the high word, += r5, r11
  rw [WP.seq_iff]
  refine wp_str (a := off (State.addr base) d) (by decide)
    (by simpa only [Nat.add_zero] using ws8.ea p8 (imm := 0) (by omega_arith)) (ws8.write (by omega_arith)) fun s9 h9 => ?_
  refine wp_mov (op2_reg _ .r4) fun s10 h10 => ?_
  refine wp_mov (op2_imm (by decide)) fun s11 h11 => WP.block_nil ?_
  obtain hi11 : s11.gpr .r3 = s8.gpr .r4 := by rw [h11.other .r3 (by decide), h10.gpr, h9.gpr]
  have z11 : s11.gpr .r4 = 0 := h11.gpr
  obtain c5 : s11.gpr .r5 = s8.gpr .r5 := by rw [h11.other .r5 (by decide), h10.other .r5 (by decide), h9.gpr]
  obtain c11 : s11.gpr .r11 = s8.gpr .r11 := by
    rw [h11.other .r11 (by decide), h10.other .r11 (by decide), h9.gpr]
  rw [WP.seq_iff]
  refine WP.mono (addWord_ok s11 .r5 (by
    rw [hi11, z11, c5]; have := (s8.gpr .r5).isLt; change _ + 0 * _ + _ < _; omega_arith)) ?_
  rintro s12 ⟨v12, f12⟩
  rw [WP.seq_iff]
  refine WP.mono (addWord_ok s12 .r11 (by
    rw [v12, hi11, z11, c5, f12.regs .r11 (by decide), c11]
    have := (s8.gpr .r5).isLt; have := (s8.gpr .r11).isLt; change _ + 0 * _ + _ + _ < _; omega_arith)) ?_
  rintro s13 ⟨v13, f13⟩
  obtain f1213 := f12.trans f13
  obtain m13 : s13.mem = s9.mem := f1213.mem.trans (h11.mem.trans h10.mem)
  obtain p13 : s13.gpr .r0 = base + BitVec.ofNat 32 d := by
    rw [f1213.regs .r0 (by decide), h11.other .r0 (by decide), h10.other .r0 (by decide), h9.gpr, p8]
  obtain w13 : s13.wr = s.wr := by rw [f1213.wr, h11.wr, h10.wr, h9.wr, K8.wr]
  refine wp_str (a := off (State.addr base) (d + 4)) (by decide) ((ws.congr w13).ea p13 (by omega_arith))
    (by rw [w13]; exact ws.write (by omega_arith)) fun s14 h14 => ?_
  refine wp_str (a := off (State.addr base) (d + 8)) (by decide)
    (by rw [h14.gpr]; exact (ws.congr w13).ea p13 (by omega_arith))
    (by rw [h14.wr, w13]; exact ws.write (by omega_arith)) fun s15 h15 => ?_
  refine wp_dp (op2_imm (by decide)) fun t ht => WP.block_nil ?_
  refine ⟨s8.gpr .r3, s13.gpr .r3, s13.gpr .r4, ?_, ?_, ?_, ?_⟩
  · rw [ht.mem, h15.mem, h14.gpr, h14.mem, m13, h9.mem, m8]
  · -- the arithmetic
    obtain e7 : s6.gpr .r9 = s.gpr .r9 := by
      rw [f6.regs .r9 (by decide), f5.regs .r9 (by decide), K4.gpr .r9 (by decide)]
    obtain e10 : s7.gpr .r10 = s.gpr .r10 := by
      rw [f7.regs .r10 (by decide), f6.regs .r10 (by decide), f5.regs .r10 (by decide), K4.gpr .r10 (by decide)]
    obtain e1 : s6.gpr .r1 = s4.gpr .r1 := by rw [f6.regs .r1 (by decide), f5.regs .r1 (by decide)]
    obtain e2 : s7.gpr .r2 = s4.gpr .r2 := by
      rw [f7.regs .r2 (by decide), f6.regs .r2 (by decide), f5.regs .r2 (by decide)]
    obtain e5 : s6.gpr .r5 = s.gpr .r5 := by
      rw [f6.regs .r5 (by decide), f5.regs .r5 (by decide), K4.gpr .r5 (by decide)]
    obtain e11 : s7.gpr .r11 = s.gpr .r11 := by
      rw [f7.regs .r11 (by decide), f6.regs .r11 (by decide), f5.regs .r11 (by decide), K4.gpr .r11 (by decide)]
    obtain e8 : s5.gpr .r8 = s.gpr .r8 := (f5.regs .r8 (by decide)).trans (K4.gpr .r8 (by decide))
    obtain r4 : s8.gpr .r4 = s6.gpr .r4 := (f8.regs .r4 (by decide)).trans (f7.regs .r4 (by decide))
    rw [t3n, t4n, K4.gpr .r7 (by decide)] at v5
    rw [v5, e8] at v6
    rw [e1, b4n, e7, e5] at v7
    rw [e2, mm4n, e10, e11] at v8
    obtain r5' : s8.gpr .r5 = s7.gpr .r5 := f8.regs .r5 (by decide)
    rw [v12, hi11, z11, c5, f12.regs .r11 (by decide), c11] at v13
    unfold carries
    rw [r4] at v13
    rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero] at v13
    rw [r5'] at v13
    omega_arith
  · rw [ht.gpr, dpVal, h15.gpr, h14.gpr, p13]
    exact Offset.add_add _ _ _
  · have k11 : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r11] s s11 :=
      (K8.mono (by decide)).trans ((h9.rest _).trans ((h10.rest (by decide)).trans (h11.rest (by decide))))
    obtain k13 : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r11] s s13 :=
      k11.trans ((macFrame_rest f1213).mono (by decide))
    exact k13.trans ((h14.rest _).trans ((h15.rest _).trans (ht.rest (by decide))))

end VG.Proof.Bignum.Arm.Fios2

end

end


/-! The two-row scan: both rows' products and quotients, divided by `2⁶⁴`. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

/-- Three words stored at `d`, read back as a number below the words at `o`. -/
theorem three_words {m : Mem} {base : BitVec 32} {size o d k : Nat} (v0 v1 v2 : BitVec 32)
    (nowrap : base.toNat + size ≤ 2 ^ 32) (fit : d + 12 ≤ size) (hd : d = o + 4 * k) :
    val32 (((m.writeW (off (State.addr base) d) v0).writeW (off (State.addr base) (d + 4)) v1).writeW
        (off (State.addr base) (d + 8)) v2) (State.addr base) o (k + 3) =
      val32 m (State.addr base) o k + 2 ^ (32 * k) * (v0.toNat + 2 ^ 32 * (v1.toNat + 2 ^ 32 * v2.toNat)) := by
  obtain nb : (State.addr base).toNat + size ≤ 2 ^ 32 := by
    simpa only [VG.Proof.X25519.Arm.addr_toNat] using nowrap
  obtain w0 := writeW32_outside m (State.addr base) (d := d) v0 (by omega_arith)
  obtain w1 := writeW32_outside (m.writeW (off (State.addr base) d) v0) (State.addr base) (d := d + 4) v1 (by omega_arith)
  obtain w2 := writeW32_outside ((m.writeW (off (State.addr base) d) v0).writeW (off (State.addr base) (d + 4)) v1)
    (State.addr base) (d := d + 8) v2 (by omega_arith)
  obtain all : Outside (State.addr base) d 12 m _ :=
    (w0.mono (by omega_arith) (by omega_arith)).trans ((w1.mono (by omega_arith) (by omega_arith)).trans (w2.mono (by omega_arith) (by omega_arith)))
  rw [val32_append, all.val32 (by omega_arith) (by omega_arith), ← hd]
  congr 2
  simp only [val32, Nat.mul_zero, Nat.add_zero]
  rw [w32_write_ne nb (by omega_arith) (by omega_arith) (by omega_arith), w32_write_ne nb (by omega_arith) (by omega_arith) (by omega_arith),
    w32_write_self, w32_write_ne nb (by omega_arith) (by omega_arith) (by omega_arith), w32_write_self, w32_write_self]

theorem code_ok (s : State) {base : BitVec 32} {size acc b mod n : Nat}
    (ctx : Fios.Ctx s base size acc b mod n) (positive : 4 ≤ n) (even : n % 2 = 0)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 acc)
    (source : s.gpr .r12 = base + BitVec.ofNat 32 b)
    (modulus : s.gpr .r4 = base + BitVec.ofNat 32 mod)
    (count : s.gpr .lr = BitVec.ofNat 32 n)
    (inv2 : s.gpr .r10 = s.gpr .r2)
    (c7 : s.gpr .r7 = 0) (c8 : s.gpr .r8 = 0) (c5 : s.gpr .r5 = 0) (c11 : s.gpr .r11 = 0)
    (inverse : (w32 s.mem (State.addr base) mod * (s.gpr .r2).toNat + 1) % 2 ^ 32 = 0)
    (high : w32 s.mem (State.addr base) (acc + 4 * (n + 1)) = 0) :
    WP isa VG.Impl.Bignum.Arm.Fios2.code s fun t =>
      (∃ q0 q1 : BitVec 32, 2 ^ 64 * val32 t.mem (State.addr base) acc (n + 1) =
        val32 s.mem (State.addr base) acc (n + 2) +
        ((s.gpr .r1).toNat + 2 ^ 32 * (s.gpr .r9).toNat) * val32 s.mem (State.addr base) b n +
        (q0.toNat + 2 ^ 32 * q1.toNat) * val32 s.mem (State.addr base) mod n) ∧
      t.gpr .r0 = base + BitVec.ofNat 32 (acc + 4 * (n + 1)) ∧
      Outside (State.addr base) acc (4 * (n + 1)) s.mem t.mem ∧
      Rest roundClobbers s t := by
  have nowrap := ctx.workspace.nowrap
  have outf := ctx.accFits
  have inf := ctx.bFits
  have modf := ctx.mFits
  rw [VG.Impl.Bignum.Arm.Fios2.code, WP.seq_iff]
  refine WP.mono (first_ok s ctx positive ptr source modulus count inv2 c7 c8 c5 c11 inverse) fun u iu => ?_
  rw [WP.seq_iff]
  refine WP.mono (loop_ok ctx iu positive even) fun v iv => ?_
  let d := acc + 4 * (n - 2)
  obtain ws := ctx.workspace.congr iv.rest.wr
  obtain oldT0 := iv.outside.w32 (d := acc + 4 * n) (by omega_arith) (by omega_arith)
  obtain oldT1 := iv.outside.w32 (d := acc + 4 * (n + 1)) (by omega_arith) (by omega_arith)
  obtain oldB := iv.outside.w32 (d := b + 4 * (n - 1)) (by rcases ctx.accB with h | h <;> omega_arith) (by omega_arith)
  obtain oldM := iv.outside.w32 (d := mod + 4 * (n - 1)) (by rcases ctx.accM with h | h <;> omega_arith) (by omega_arith)
  obtain e8 : d + 8 = acc + 4 * n := by omega_arith
  obtain e12 : d + 12 = acc + 4 * (n + 1) := by omega_arith
  obtain eb : b + 4 * (n - 2) + 4 = b + 4 * (n - 1) := by omega_arith
  obtain em : mod + 4 * (n - 2) + 4 = mod + 4 * (n - 1) := by omega_arith
  obtain bound : w32 v.mem (State.addr base) (d + 8) + 2 ^ 32 * w32 v.mem (State.addr base) (d + 12) +
      (v.gpr .r7).toNat + (v.gpr .r8).toNat < 2 ^ 64 := by
    rw [e8, e12, oldT0, oldT1]
    have := (v.gpr .r7).isLt; have := (v.gpr .r8).isLt
    have := (s.mem.readW (off (State.addr base) (acc + 4 * n)) 32).isLt
    rw [high]
    simp only [w32] at *
    omega_arith
  refine WP.mono (top_ok v ws (d := d) (by omega_arith) (by omega_arith) (by omega_arith) iv.outPtr iv.bPtr iv.mPtr bound) ?_
  rintro t ⟨v0, v1, v2, mem, value, pt, rest⟩
  refine ⟨⟨u.gpr .r2, u.gpr .r10, ?_⟩, ?_, ?_, iv.rest.trans (rest.mono (by decide))⟩
  · rw [e8, e12, oldT0, oldT1, eb, em, oldB, oldM, iv.scalar1, iv.quotient1] at value
    obtain stored := three_words (m := v.mem) (o := acc) (k := n - 2) v0 v1 v2 nowrap (by omega_arith) rfl
    rw [← mem, show n - 2 + 3 = n + 1 by omega_arith] at stored
    have prior := iv.value
    -- the old numbers, split at their last words
    obtain eT : val32 s.mem (State.addr base) acc (n + 2) = val32 s.mem (State.addr base) acc n +
        2 ^ 64 * 2 ^ (32 * (n - 2)) * (w32 s.mem (State.addr base) (acc + 4 * n) +
          2 ^ 32 * w32 s.mem (State.addr base) (acc + 4 * (n + 1))) := by
      rw [val32_append s.mem _ acc n 2]
      congr 1
      rw [show 2 ^ 64 * 2 ^ (32 * (n - 2)) = 2 ^ (32 * n) by
        rw [← Nat.pow_add]; congr 1; omega_arith]
      simp only [val32, Nat.mul_zero, Nat.add_zero, show acc + 4 * n + 4 = acc + 4 * (n + 1) by omega_arith]
    obtain eB : val32 s.mem (State.addr base) b n = val32 s.mem (State.addr base) b (n - 2 + 1) +
        2 ^ 32 * 2 ^ (32 * (n - 2)) * w32 s.mem (State.addr base) (b + 4 * (n - 1)) := by
      rw [show n = (n - 2 + 1) + 1 by omega_arith, val32_succ, ← pow32_succ]
      congr 3 <;> omega_arith
    obtain eM : val32 s.mem (State.addr base) mod n = val32 s.mem (State.addr base) mod (n - 2 + 1) +
        2 ^ 32 * 2 ^ (32 * (n - 2)) * w32 s.mem (State.addr base) (mod + 4 * (n - 1)) := by
      rw [show n = (n - 2 + 1) + 1 by omega_arith, val32_succ, ← pow32_succ]
      congr 3 <;> omega_arith
    rw [show n - 2 + 2 = n by omega_arith, show n - 2 + 1 = n - 1 by omega_arith] at prior
    rw [show n - 2 + 1 = n - 1 by omega_arith] at eB eM
    rw [show 2 ^ (32 * n) = 2 ^ 64 * 2 ^ (32 * (n - 2)) by rw [← Nat.pow_add]; congr 1; omega_arith, eB, eM] at prior
    rw [stored, eT, eB, eM]
    unfold carries at prior value
    exact top_value prior value rfl
  · rw [pt, show d + 12 = acc + 4 * (n + 1) by omega_arith]
  · have nb : (State.addr base).toNat + size ≤ 2 ^ 32 := by
      simpa only [VG.Proof.X25519.Arm.addr_toNat] using nowrap
    rw [mem]
    obtain w0 := writeW32_outside v.mem (State.addr base) (d := d) v0 (by omega_arith)
    obtain w1 := writeW32_outside (v.mem.writeW (off (State.addr base) d) v0) (State.addr base) (d := d + 4) v1
      (by omega_arith)
    obtain w2 := writeW32_outside ((v.mem.writeW (off (State.addr base) d) v0).writeW
      (off (State.addr base) (d + 4)) v1) (State.addr base) (d := d + 8) v2 (by omega_arith)
    exact (iv.outside.mono (Nat.le_refl _) (by omega_arith)).trans ((w0.mono (by omega_arith) (by omega_arith)).trans
      ((w1.mono (by omega_arith) (by omega_arith)).trans (w2.mono (by omega_arith) (by omega_arith))))

end VG.Proof.Bignum.Arm.Fios2

end

end

/-! ### `Bignum.Arm.Fios2.Finish`, which only this module used -/

section

/-! The end of a two-row round: clear the top word, move the first operand's
pointer by two words and the remaining rounds down by two. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_dp wp_subs op2_imm dpVal)

theorem advanceOperand2_ok (s : State) {base : BitVec 32} {size tmp : Nat}
    (ws : Workspace s base size) (fit : tmp + 20 ≤ size)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp) :
    WP isa (.block VG.Impl.Bignum.Arm.Fios2.advanceOperand2) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) (tmp + 16))
        (s.mem.readW (off (State.addr base) (tmp + 16)) 32 + 8) ∧ Rest [.r4] s t := by
  unfold VG.Impl.Bignum.Arm.Fios2.advanceOperand2
  refine wp_ldr (by decide) (ws.ea ptr (by omega_using [fit])) (ws.read fit) fun u hu => ?_
  refine wp_dp (op2_imm (by decide)) fun v hv => ?_
  obtain wv := (ws.congr hu.wr).congr hv.wr
  obtain pv := (hv.other .r0 (by decide)).trans ((hu.other .r0 (by decide)).trans ptr)
  refine wp_str (by decide) (wv.ea pv (by omega_using [fit])) (wv.write fit) fun t ht => WP.block_nil ?_
  refine ⟨?_, ?_⟩
  · rw [ht.mem, hv.mem, hu.mem, hv.gpr, dpVal, hu.gpr]
  · exact (hu.rest (by simp)).trans ((hv.rest (by simp)).trans (ht.rest _))

theorem decrementRounds2_ok (s : State) {base : BitVec 32} {size tmp : Nat}
    (ws : Workspace s base size) (fit : tmp + 24 ≤ size)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp) :
    WP isa (.block VG.Impl.Bignum.Arm.Fios2.decrementRounds2) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) (tmp + 20))
        (s.mem.readW (off (State.addr base) (tmp + 20)) 32 - 2) ∧
      t.z = (s.mem.readW (off (State.addr base) (tmp + 20)) 32 - 2 == 0) ∧ Rest [.lr] s t := by
  unfold VG.Impl.Bignum.Arm.Fios2.decrementRounds2
  refine wp_ldr (by decide) (ws.ea ptr (by omega_using [fit])) (ws.read fit) fun u hu => ?_
  refine wp_subs (op2_imm (by decide)) fun v hv hz => ?_
  obtain wv := (ws.congr hu.wr).congr hv.wr
  obtain pv := (hv.other .r0 (by decide)).trans ((hu.other .r0 (by decide)).trans ptr)
  refine wp_str_z (by decide) (wv.ea pv (by omega_using [fit])) (wv.write fit) fun t ht htz => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [ht.mem, hv.mem, hu.mem, hv.gpr, hu.gpr]
  · rw [htz, hz, hu.gpr]
  · exact (hu.rest (by simp)).trans ((hv.rest (by simp)).trans (ht.rest _))

def finishMem2 (mem : Mem) (base : Addr) (top tmp : Nat) : Mem :=
  ((mem.writeW (off base top) (0 : BitVec 32)).writeW (off base (tmp + 16))
    (mem.readW (off base (tmp + 16)) 32 + 8)).writeW (off base (tmp + 20))
    (mem.readW (off base (tmp + 20)) 32 - 2)

theorem finish_ok (s : State) {base : BitVec 32} {size top tmp : Nat}
    (ws : Workspace s base size) (fit : tmp + 24 ≤ size) (htmp : tmp = top + 12)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 top) :
    WP isa (.block VG.Impl.Bignum.Arm.Fios2.finish) s fun t =>
      t.mem = finishMem2 s.mem (State.addr base) top tmp ∧
      t.gpr .r0 = base + BitVec.ofNat 32 tmp ∧
      t.z = (s.mem.readW (off (State.addr base) (tmp + 20)) 32 - 2 == 0) ∧
      Rest [.r0, .r3, .r4, .lr] s t := by
  have hn := ws.nowrap
  rw [VG.Impl.Bignum.Arm.Fios2.finish, List.append_assoc]
  apply WP.block_append_iff.mpr
  refine WP.mono (clearTop_ok s ws (by omega_using [fit, htmp]) ptr) ?_
  rintro u ⟨mem1, ptr1, keep1⟩
  rw [← htmp] at ptr1
  obtain wr1 := writeW32_outside s.mem (State.addr base) (d := top) (0 : BitVec 32) (by omega)
  rw [← mem1] at wr1
  obtain oldPtr := outside_read32 wr1 (d := tmp + 16) (by omega_using [htmp]) (by omega_using [fit, hn])
  obtain oldCount := outside_read32 wr1 (d := tmp + 20) (by omega_using [htmp]) (by omega_using [fit, hn])
  apply WP.block_append_iff.mpr
  refine WP.mono (advanceOperand2_ok u (ws.congr keep1.wr) (by omega_using [fit]) ptr1) ?_
  rintro v ⟨mem2, keep2⟩
  obtain wr2 := writeW32_outside u.mem (State.addr base) (d := tmp + 16)
    (u.mem.readW (off (State.addr base) (tmp + 16)) 32 + 8) (by omega_using [fit, hn])
  rw [← mem2] at wr2
  obtain oldCount2 := (outside_read32 wr2 (d := tmp + 20) (by omega_using []) (by omega_using [fit, hn])).trans oldCount
  refine WP.mono (decrementRounds2_ok v ((ws.congr keep1.wr).congr keep2.wr) fit
    ((keep2.gpr .r0 (by simp)).trans ptr1)) ?_
  rintro t ⟨mem3, zero, keep3⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem3, oldCount2, mem2, oldPtr, mem1, finishMem2]
  · rw [keep3.gpr .r0 (by simp), keep2.gpr .r0 (by simp), ptr1]
  · rw [zero, oldCount2]
  · exact (keep1.mono (by simp_all)).trans
      ((keep2.mono (by simp_all)).trans (keep3.mono (by simp_all)))

theorem finish_meta {mem : Mem} {base : BitVec 32} {size top tmp a b mod acc n i : Nat} {inv : BitVec 32}
    (nowrap : base.toNat + size ≤ 2 ^ 32) (fit : tmp + 32 ≤ size) (htmp : tmp = top + 12)
    (hdr : RoundMeta mem base tmp a b mod acc n i inv) (hi : i + 2 ≤ n) :
    RoundMeta (finishMem2 mem (State.addr base) top tmp) base tmp a b mod acc n (i + 2) inv := by
  obtain hb : (State.addr base).toNat + size ≤ 2 ^ 32 := by
    rw [VG.Proof.X25519.Arm.addr_toNat]
    exact nowrap
  have stable (d : Nat) (hd : d + 4 ≤ 32) (sep : d + 4 ≤ 16 ∨ 24 ≤ d) :
      (finishMem2 mem (State.addr base) top tmp).readW (off (State.addr base) (tmp + d)) 32 =
        mem.readW (off (State.addr base) (tmp + d)) 32 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (finishMem2 mem (State.addr base) top tmp) (State.addr base) (tmp + d) =
      w32 mem (State.addr base) (tmp + d)
    rw [finishMem2, w32_write_ne hb (by omega_using [fit]) (by omega_using [fit, hd]) (by omega_using [sep]),
      w32_write_ne hb (by omega_using [fit]) (by omega_using [fit, hd]) (by omega_using [sep]),
      w32_write_ne hb (by omega_using [fit, htmp]) (by omega_using [fit, hd]) (by omega_using [htmp])]
  obtain ap : (finishMem2 mem (State.addr base) top tmp).readW (off (State.addr base) (tmp + 16)) 32 =
      mem.readW (off (State.addr base) (tmp + 16)) 32 + 8 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (finishMem2 mem (State.addr base) top tmp) (State.addr base) (tmp + 16) = _
    rw [finishMem2, w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using []), w32_write_self]
  obtain count : (finishMem2 mem (State.addr base) top tmp).readW (off (State.addr base) (tmp + 20)) 32 =
      mem.readW (off (State.addr base) (tmp + 20)) 32 - 2 := by
    rw [finishMem2, Mem.readW_writeW_self32]
  refine ⟨(stable 0 (by decide) (by decide)).trans hdr.count,
    (stable 4 (by decide) (by decide)).trans hdr.bPtr,
    (stable 8 (by decide) (by decide)).trans hdr.mPtr,
    (stable 12 (by decide) (by decide)).trans hdr.inverse, ?_, ?_,
    (stable 28 (by decide) (by decide)).trans hdr.accPtr⟩
  · rw [ap, hdr.aPtr]
    change base + BitVec.ofNat 32 (a + 4 * i) + BitVec.ofNat 32 8 = _
    rw [Offset.add_add]
    congr 1
  · rw [count, hdr.remaining]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 2 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hi])]
    congr 1

theorem finish_value {mem : Mem} {base : Addr} {size acc top tmp n : Nat}
    (nowrap : base.toNat + size ≤ 2 ^ 32) (fit : tmp + 24 ≤ size)
    (htop : top = acc + 4 * (n + 1)) (htmp : tmp = top + 12) :
    val32 (finishMem2 mem base top tmp) base acc (n + 2) = val32 mem base acc (n + 1) ∧
      Outs base [(acc, 4 * (n + 2)), (tmp + 16, 8)] mem (finishMem2 mem base top tmp) := by
  obtain k1 := writeW32_outside mem base (d := top) (0 : BitVec 32) (by omega)
  obtain k2 := writeW32_outside (mem.writeW (off base top) (0 : BitVec 32)) base (d := tmp + 16)
    (mem.readW (off base (tmp + 16)) 32 + 8) (by omega_using [nowrap, fit])
  obtain k3 := writeW32_outside ((mem.writeW (off base top) (0 : BitVec 32)).writeW
    (off base (tmp + 16)) (mem.readW (off base (tmp + 16)) 32 + 8)) base (d := tmp + 20)
    (mem.readW (off base (tmp + 20)) 32 - 2) (by omega_using [nowrap, fit])
  obtain low1 := k1.val32 (d := acc) (k := n + 1) (by omega_using [htop]) (by omega)
  obtain low2 := k2.val32 (d := acc) (k := n + 1) (by omega_using [htop, htmp]) (by omega)
  obtain low3 := k3.val32 (d := acc) (k := n + 1) (by omega_using [htop, htmp]) (by omega)
  obtain hi2 := k2.w32 (d := top) (by omega_using [htmp]) (by omega)
  obtain hi3 := k3.w32 (d := top) (by omega_using [htmp]) (by omega)
  refine ⟨?_, ?_⟩
  · rw [show n + 2 = (n + 1) + 1 by omega_using [], val32_succ, finishMem2, low3, low2, low1,
      ← htop, hi3, hi2, w32_write_self]
    simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  · exact (Outs.of_outside (k1.mono (o' := acc) (n' := 4 * (n + 2)) (by omega_using [htop]) (by omega_using [htop])) (by simp)).trans
      ((Outs.of_outside (k2.mono (o' := tmp + 16) (n' := 8) (by omega_using []) (by omega_using [])) (by simp)).trans
        (Outs.of_outside (k3.mono (o' := tmp + 16) (n' := 8) (by omega_using []) (by omega_using [])) (by simp)))

end VG.Proof.Bignum.Arm.Fios2

end

end


/-! The two-row round meets the two-row round contract. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

/-- An accumulator below `2m`, for `m` of `n` words, has a zero top word. -/
theorem top_zero {mem : Mem} {base : Addr} {acc m n : Nat}
    (hT : val32 mem base acc (n + 2) < 2 * m) (hm : m < 2 ^ (32 * n)) :
    w32 mem base (acc + 4 * (n + 1)) = 0 := by
  rw [show n + 2 = (n + 1) + 1 by omega_using [], val32_succ] at hT
  obtain p : 2 ^ (32 * (n + 1)) = 2 ^ 32 * 2 ^ (32 * n) := pow32_succ n
  rw [p] at hT
  by_contra hne
  have : 2 ^ 32 * 2 ^ (32 * n) ≤ 2 ^ 32 * 2 ^ (32 * n) * w32 mem base (acc + 4 * (n + 1)) :=
    Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
  have : 2 * 2 ^ (32 * n) ≤ 2 ^ 32 * 2 ^ (32 * n) := Nat.mul_le_mul_right _ (by decide)
  omega_arith

theorem round_law : MontPipeline.PairLaw VG.Impl.Bignum.Arm.Fios2.round := by
  intro s base size tmp a b mod acc n i inv ctx even hdr hi ptr hT hB hInv
  have count := ctx.count
  have nowrap := ctx.workspace.nowrap
  have fits := ctx.tmpFits
  have layout := ctx.layout
  rw [VG.Impl.Bignum.Arm.Fios2.round, WP.seq_iff]
  refine WP.mono (args_ok s ctx hdr hi ptr) ?_
  rintro u ⟨a0, a1, p0, p12, p4, p2, p10, cnt, c7, c8, c5, c11, memU, restU⟩
  let c : Fios.Ctx u base size acc b mod n :=
    ⟨ctx.workspace.congr restU.wr, ctx.accFits, ctx.bFits, ctx.mFits, ctx.accB, ctx.accM⟩
  obtain split : val32 s.mem (State.addr base) mod n =
      w32 s.mem (State.addr base) mod + 2 ^ 32 * val32 s.mem (State.addr base) (mod + 4) (n - 1) := by
    calc
      _ = val32 s.mem (State.addr base) mod ((n - 1) + 1) := by congr 1; omega_using [hi]
      _ = _ := rfl
  obtain inverseLow : (w32 u.mem (State.addr base) mod * (u.gpr .r2).toNat + 1) % 2 ^ 32 = 0 := by
    rw [memU, p2]
    rw [split, Nat.add_mul, Nat.add_right_comm, Nat.mul_assoc, Nat.add_mul_mod_self_left] at hInv
    exact hInv
  obtain high : w32 u.mem (State.addr base) (acc + 4 * (n + 1)) = 0 := by
    rw [memU]
    exact top_zero hT (val32_lt s.mem (State.addr base) mod n)
  rw [WP.seq_iff]
  refine WP.mono (code_ok u c (by omega_using [count]) even p0 p12 p4 cnt (p10.trans p2.symm) c7 c8 c5 c11
    inverseLow high) ?_
  rintro v ⟨⟨q0, q1, value⟩, ptrV, outsideV, keepV⟩
  obtain a0n : (u.gpr .r1).toNat = w32 s.mem (State.addr base) (a + 4 * i) := by rw [a0]
  obtain a1n : (u.gpr .r9).toNat = w32 s.mem (State.addr base) (a + 4 * i + 4) := by rw [a1]
  rw [memU, a0n, a1n] at value
  rw [memU] at outsideV
  obtain hdrV := hdr.of_outside outsideV (by omega_using [layout]) (by omega_using [nowrap, fits])
  refine WP.mono (finish_ok (top := acc + 4 * (n + 1)) (tmp := tmp) v (ctx.workspace.congr (restU.trans keepV).wr)
    (by omega_using [fits]) (by omega_using [layout]) ptrV) ?_
  rintro t ⟨memT, ptrT, zero, keepT⟩
  obtain nowrap' : (State.addr base).toNat + size ≤ 2 ^ 32 := by
    simpa only [VG.Proof.X25519.Arm.addr_toNat] using nowrap
  obtain ⟨result, frame⟩ := finish_value (mem := v.mem) (acc := acc) (n := n) (tmp := tmp)
    nowrap' (by omega_using [fits]) rfl (by omega_using [layout])
  rw [← memT] at result frame
  obtain hq : q0.toNat + 2 ^ 32 * q1.toNat < 2 ^ 64 := by
    have := q0.isLt; have := q1.isLt; omega_using []
  obtain hA : w32 s.mem (State.addr base) (a + 4 * i) + 2 ^ 32 * w32 s.mem (State.addr base) (a + 4 * i + 4) <
      2 ^ 64 := by
    have := (s.mem.readW (off (State.addr base) (a + 4 * i)) 32).isLt
    have := (s.mem.readW (off (State.addr base) (a + 4 * i + 4)) 32).isLt
    simp only [w32]; omega_using []
  obtain value' : 2 ^ 64 * val32 t.mem (State.addr base) acc (n + 2) =
      val32 s.mem (State.addr base) acc (n + 2) +
        (w32 s.mem (State.addr base) (a + 4 * i) + 2 ^ 32 * w32 s.mem (State.addr base) (a + 4 * i + 4)) *
          val32 s.mem (State.addr base) b n +
        (q0.toNat + 2 ^ 32 * q1.toNat) * val32 s.mem (State.addr base) mod n := by
    rw [result, value]
  refine ⟨?_, ptrT, ⟨_, hq, value'⟩, MontPipeline.pair_lt value' hT hA hB hq, ?_, ?_, ?_⟩
  · rw [memT]
    exact finish_meta nowrap fits (by omega_using [layout]) hdrV hi
  · have enlarged : Outside (State.addr base) acc (4 * (n + 2)) s.mem v.mem :=
      outsideV.mono (Nat.le_refl _) (by omega_using [])
    exact (Outs.of_outside enlarged (by simp)).trans frame
  · rw [zero, hdrV.remaining]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 2 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hi]), ofNat_beq_zero (by omega)]
    simp only [show n - i - 2 = 0 ↔ i + 2 = n by omega_using [hi]]
  · exact restU.trans (keepV.trans (keepT.mono (by decide)))

end VG.Proof.Bignum.Arm.Fios2

end

end

/-! ### `Bignum.Arm.MontPipelinePairCT`, which only this module used -/

section

/-! The public schedule of a loop of two-row rounds. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.MontPipeline
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

/-- A two-row round has a public schedule for its public index and count. -/
def PairCTLaw (round : Prog isa) : Prop :=
  ∀ {base : BitVec 32} {size tmp a b mod acc n i : Nat}, n % 2 = 0 → i + 2 ≤ n →
    RelCT isa (fun s t => RoundReady base size tmp a b mod acc n i s ∧
      RoundReady base size tmp a b mod acc n i t) round (fun _ _ => True)

theorem pair_round_ready (round : Prog isa) (law : PairLaw round) {base : BitVec 32}
    {size tmp a b mod acc n i : Nat} (even : n % 2 = 0) (hi : i + 2 ≤ n)
    (s : State) (h : RoundReady base size tmp a b mod acc n i s) :
    WP isa round s fun t => RoundReady base size tmp a b mod acc n (i + 2) t ∧
      t.z = decide (i + 2 = n) := by
  obtain ⟨inv, hdr, inverse⟩ := h.secret
  refine WP.mono (law s h.ctx even hdr hi h.ptr h.bound h.operand inverse) ?_
  intro t post
  have nowrap := h.ctx.workspace.nowrap
  have fitsB := h.ctx.bFits
  have fitsM := h.ctx.mFits
  have accB := h.ctx.accB
  have accM := h.ctx.accM
  have tmpB := h.ctx.tmpB
  have tmpM := h.ctx.tmpM
  obtain oldB := post.outside.val32 (d := b) (k := n) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_using [nowrap, fitsB])
  obtain oldM := post.outside.val32 (d := mod) (k := n) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_using [nowrap, fitsM])
  refine ⟨⟨h.ctx.congr post.rest.wr, ⟨inv, post.hdr, ?_⟩, post.ptr, ?_, ?_⟩, post.zero⟩
  · rw [oldM]; exact inverse
  · rw [oldM]; exact post.bound
  · rw [oldB, oldM]; exact h.operand

theorem pair_rounds_ct (round : Prog isa) (law : PairLaw round) (ctLaw : PairCTLaw round)
    {base : BitVec 32} {size tmp a b mod acc n : Nat} (even : n % 2 = 0) :
    RelCT isa (fun s t => RoundReady base size tmp a b mod acc n 0 s ∧
      RoundReady base size tmp a b mod acc n 0 t) (VG.Impl.Bignum.Arm.MontPipeline.rounds round)
      (fun _ _ => True) := by
  let I := fun k s t => ∃ i, i + 2 * k = n ∧ 0 < k ∧
    RoundReady base size tmp a b mod acc n i s ∧ RoundReady base size tmp a b mod acc n i t
  obtain step : ∀ k, RelCT isa (I k) round fun s t => isa.eval .ne s = isa.eval .ne t ∧
      (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ j < k, I j s t) := by
    intro k
    apply RelCT.exists_
    intro i s t tr1 tr2 u v h e1 e2
    obtain ⟨hik, hk, hs, ht⟩ := h
    obtain hi : i + 2 ≤ n := by omega_using [hik, hk]
    obtain ⟨trace, posts⟩ := pair_posts (ctLaw even hi) (pair_round_ready round law even hi)
      s t tr1 tr2 u v ⟨hs, ht⟩ e1 e2
    obtain ⟨⟨hu, zu⟩, ⟨hv, zv⟩⟩ := posts
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!u.z) = some (!v.z)
      rw [zu, zv]
    · intro branch
      obtain ne : i + 2 ≠ n := by
        intro eq
        change some (!u.z) = some true at branch
        simp only [zu, eq, decide_true, Bool.not_true] at branch
        cases branch
      exact ⟨k - 1, by omega_using [hk], i + 2, by omega_using [hik, hk], by omega_using [hik, hk, ne], hu, hv⟩
  apply (RelCT.loop I step (n / 2)).mono _ (fun _ _ h => h)
  intro s t h
  have count := h.1.ctx.count
  exact ⟨0, by omega_using [even], by omega_using [count], h⟩

theorem PairCTLaw.loop {round : Prog isa} (law : PairLaw round) (ctLaw : PairCTLaw round) :
    LoopCTLaw round :=
  fun even => pair_rounds_ct round law ctLaw even

end VG.Proof.Bignum.Arm.MontPipeline

end

end


/-! One two-row UMAAL kernel supplies every caller of the shared Montgomery backend. -/

@[expose] public section
namespace VG.Proof.Variants.RsaMont.Arm.Umaal
open VG VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

def variant : MontBackend := montCallFios2_backend
  (MontPipeline.PairLaw.loop Fios2.round_law)
  (MontPipeline.PairCTLaw.loop Fios2.round_law fun _ hi => Fios2.round_ct hi)

end VG.Proof.Variants.RsaMont.Arm.Umaal
