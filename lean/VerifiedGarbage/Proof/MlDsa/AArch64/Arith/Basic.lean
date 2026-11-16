module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.MlDsa.Arith.Zq
public import VerifiedGarbage.Proof.MlDsa.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.MlDsa.Round.Mem

/-!
# ML-DSA on AArch64: symbolic execution

It uses the weakest preconditions and loops of ML-KEM's AArch64 proofs
(`Keep`, `count_loop`, `Proof/MlKem/AArch64/Wp.lean`), which are about the
ISA, not ML-KEM.

* `arun`: a block run by `simp`, one instruction at a time (`runBlock_cons`,
  `runStep_some`), with the state a chain of `State.write`s and memory
  updates whose registers `RegUpd.gpr_write` reads, so that a register of
  the result is the value last written to it. A block lemma takes the
  accesses it makes as hypotheses on the registers of its initial state.
* `WP.keep`: the registers no instruction of the code writes are kept
  (`writesOnly`, checked by evaluation).
* `wp_countdown`: a loop on `cbnz` of a counter that its body decrements.
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Arith

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Spec.MlDsa (q n Poly Zq)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs)

/-! ## The instructions, for `simp` -/

section
variable {s : State}

theorem exec_sub {sz : Size} {d n m : Reg} :
    exec (.sub sz d n m) s = some (s.write sz d (s.read sz n - s.read sz m)) := rfl

theorem exec_mul {sz : Size} {d n m : Reg} :
    exec (.mul sz d n m) s = some (s.write sz d (s.read sz n * s.read sz m)) := rfl

theorem exec_madd {sz : Size} {d n m a : Reg} :
    exec (.madd sz d n m a) s = some (s.write sz d (s.read sz a + s.read sz n * s.read sz m)) := rfl

theorem exec_lsl_x {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.lsl .x d n sh) s = some (s.write .x d (s.read .x n <<< sh)) := by
  simp [exec, Size.bits, h]

theorem exec_addImm_w {d n : Reg} {imm : Nat} (h : imm < 4096) :
    exec (.addImm .w d n imm) s = some (s.write .w d (s.read .w n + BitVec.ofNat _ imm)) := by
  simp [exec, h]

theorem exec_movz_x {d : Reg} {imm : BitVec 16} :
    exec (.movz .x d imm 0) s = some (s.write .x d (imm.setWidth 64)) := by
  simp only [exec, Size.bits, Nat.mul_zero, show (0 : Nat) < 64 from by decide, ite_true]
  exact congrArg (fun v => some (s.write .x d v)) (BitVec.shiftLeft_zero _)

theorem exec_movk_x {d : Reg} {imm : BitVec 16} {hw : Nat} (h : 16 * hw < 64) :
    exec (.movk .x d imm hw) s = some (s.write .x d ((s.gpr d &&& ~~~((0xFFFF : BitVec 64) <<< (16 * hw))) |||
      (imm.setWidth 64 <<< (16 * hw)))) := by
  simp [exec, Size.bits, h, State.read]

end

/-- `arun`: symbolic execution of a block by `simp` (see the module doc),
with extra lemmas (the block's accesses, …). -/
tactic_template "arun" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
                       apply WP.of_runBlock
                       set_option linter.unusedSimpArgs false in
                       simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil,
                         exec_ldr_w, exec_str_w, exec_add, exec_sub, exec_logic, exec_mul, exec_madd, exec_addImm_x,
                         exec_subImm_x, exec_addImm_w, exec_lsr_x, exec_lsl_x, exec_movz_w, exec_movk_w, exec_movz_x,
                         exec_movk_x, State.read, Size.bits, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
                         RegUpd.wr_write, RegUpd.sp_write, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left',
                         ite_true, ite_false, reduceCtorEq, true_and, and_true, List.cons_append, List.nil_append,
                         BitVec.add_zero, BitVec.setWidth_setWidth_of_le, movz_movk,
                         $ls,*]))

/-- `arun` with no extra lemmas. -/
tactic_template "arun" : tactic => `(tactic| arun [])

/-! ## What a block keeps -/

/-- Whether every instruction of `c` writes, if any register, one of `rs`. -/
noncomputable def writesOnly (rs : List Reg) (c : Prog isa) : Bool :=
  c.allInstrs fun i => (dsts i).all rs.contains

/-- A register that no instruction writes keeps its value (code without calls). -/
theorem WP.keep {c : Prog isa} {s : State} {Q : State → Prop} (rs : List Reg) (h : WP isa c s Q)
    (hc : writesOnly rs c = true) (hn : c.noCalls = true := by first | rfl | decide)
    (hv : c.allInstrs keepsV = true := by decide +kernel) :
    WP isa c s fun s' => Q s' ∧ Keep rs s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, ⟨fun r hr => Exec.gpr (fun i hi => ?_) he (.inl hn), (Exec.rdwr he).1,
    (Exec.rdwr he).2.1, (Exec.rdwr he).2.2, Exec.preservedV he hv⟩⟩
  unfold writesOnly at hc
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  exact clobbers_eq_false_of_all (hc i hi) (by simpa using hr)


/-! ## Loops -/

/-- A do-while loop on `cbnz cnt` whose body decrements `cnt`, from `N > 0`:
it runs `N` times. -/
theorem wp_countdown {body : Prog isa} {cnt : Reg} {N : Nat} (hN : N < 2 ^ 64) (hN0 : 0 < N)
    (Inv : Nat → State → Prop)
    (hbody : ∀ i < N, ∀ s, Inv i s → s.gpr cnt = BitVec.ofNat 64 (N - i) →
      WP isa body s fun s' => Inv (i + 1) s' ∧ s'.gpr cnt = s.gpr cnt - BitVec.ofNat 64 1)
    {s : State} (h0 : Inv 0 s) (hc : s.gpr cnt = BitVec.ofNat 64 N) :
    WP isa (.loop body (.nonzero .x cnt)) s (Inv N) := by
  refine WP.mono (count_loop (cr := cnt) hN0 (fun k s => Inv k s ∧ s.gpr cnt = BitVec.ofNat 64 (N - k))
    (fun k hk s ⟨hI, hc⟩ => WP.mono (hbody k hk s hI hc) fun s' ⟨hI', hc'⟩ => ⟨⟨hI', ?_⟩, ?_⟩)
    ⟨h0, by rw [hc, Nat.sub_zero]⟩) fun _ h => h.1
  · rw [hc', hc]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_using [hk]
  · rw [hc', hc, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_using [hN]

/-! ## `csub` -/

/-- `q`, as a 64-bit value. -/
abbrev Qv : BitVec 64 := BitVec.ofNat 64 8380417

theorem toNat_setWidth64 (v : BitVec 32) : (v.setWidth 64).toNat = v.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := v.isLt; omega_using [])]

/-! ## Constants -/

theorem q32 : (BitVec.ofNat 32 8380417).setWidth 64 = Qv := by decide

/-- A 16-bit immediate. -/
theorem imm16 {k : Nat} (h : k < 65536) : (BitVec.ofNat 16 k).setWidth 64 = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_using [h]

/-- `movW d v`: `d ← v`. -/
theorem movW_ok (d : Reg) (v : BitVec 32) (s : State) :
    WP isa (.block (movW d v)) s fun s' => (s'.gpr d = v.setWidth 64 ∧ s'.mem = s.mem) ∧ Keep [d] s s' := by
  refine WP.keep _ ?_ (by simp [writesOnly, Code.allInstrs, movW, dsts, dstOf, Option.toList]) (hv := by rfl)
  unfold movW
  arun
  exact congrArg (BitVec.setWidth 64) (movz_movk v)

/-! ## The contracts -/

/-- A polynomial, at `p`. -/
abbrev pR (p : Addr) : Region := ⟨p, 1024⟩

/-- An in-place transform, as `vg_mldsa_ntt(f = x0, scratch = x1)`: `f`
becomes `t f`. -/
def inPlaceK (t : Poly → Poly) : Contract isa where
  pre s :=
    s.rd = [] ∧ s.wr = [pR (s.gpr .x0), pR (s.gpr .x1)] ∧ (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x1)) ∧
    Reduced s.mem (s.gpr .x0)
  post s s' := PolyIs s'.mem (s.gpr .x0) (t (polyAt s.mem (s.gpr .x0)))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

/-- `vg_mldsa_add(f = x0, g = x1)` and `vg_mldsa_sub(f = x0, g = x1)`: `f`
becomes `t f g`. -/
def accK (t : Poly → Poly → Poly) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .x1)] ∧ s.wr = [pR (s.gpr .x0)] ∧ (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x1)) ∧
    Reduced s.mem (s.gpr .x0) ∧ Reduced s.mem (s.gpr .x1)
  post s s' := PolyIs s'.mem (s.gpr .x0) (t (polyAt s.mem (s.gpr .x0)) (polyAt s.mem (s.gpr .x1)))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

/-- The pointers `rs` and the stack pointer are public. -/
theorem agree_regs {rs : List Reg} {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs rs) s₁ s₂ :=
  VG.Proof.MlKem.AArch64.agree_of hsp h

/-- `sig_implies`, whose satisfiability witness may need `Reduced` of the
memory of zeros. -/
tactic_template "mldsa_implies " "[" ls:Lean.Parser.Tactic.simpLemma,* "]"
    " [" ws:Lean.Parser.Tactic.simpLemma,* "]" " using " w:term : tactic => `(tactic| exact
  { pre := by sig_implies_pre [$ls,*]
    post := by sig_implies_post [$ls,*]
    pub := by sig_implies_pub [$ls,*]
    sat := by
      refine ⟨$w, ?_⟩
      sig_pre [$ls,*]
      and_intros
      all_goals first
        | rfl
        | decide
        | exact Region.disjoint_of_sep (by decide)
        | exact VG.Proof.MlDsa.Round.reduced_zero _
        | (intro a h₁ h₂
           set_option linter.unusedSimpArgs false in
           simp only [Region.Contains, $ws,*] at h₁ h₂
           bv_omega) })

end VG.Proof.MlDsa.AArch64.Arith
