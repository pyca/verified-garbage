import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Env
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# AES-GCM-SIV on x86-64: running blocks

Untrusted: everything here is checked by Lean. `srun [facts]` runs a block
of the instructions the AES-GCM-SIV code uses from a state in which the
`facts` (register values and accessible memory) hold; and the reading of
conditions and sequences of programs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Proof.AesGcm.X86_64 (offset_nat imm_eq setWidth_imm ofNat_add_ofNat toNat_ofNat_of_lt)

/-- Runs a block of the instructions the AES-GCM-SIV code uses. -/
macro "srun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [imm_eq, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    readSrc32, execAlu, execAlu32, execShift, State.load64, State.store64, State.load32, State.store32,
    State.load8, State.store8, State.ea, State.setReg32, offset_nat, at_, imm, ptr, tagO, akO, ekO, hO, yO, cmO,
    ccO, bO, t2O, okO, roundsO, nonceO, aadO, alenO, dataO, lenO, skO, revO, ghO, scrO, List.cons_append,
    List.nil_append, List.append_assoc, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
    gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags,
    wr_setReg, wr_arithFlags, wr_setFlags, cf_setReg, cf_arithFlags, zf_setReg, zf_arithFlags,
    ite_true, ite_false, reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff,
    Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, setWidth_imm, and_self, and_true, true_and, $ts,*]) <;> try rfl)

theorem add_ofNat_assoc (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ofNat_add_ofNat]

theorem eval_e {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .e s = some b := h
theorem eval_ne {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .ne s = some !b := by
  show s.zf.map _ = _; rw [h]; rfl
theorem eval_b {s : State} {b : Bool} (h : s.cf = some b) : isa.eval .b s = some b := h

theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

theorem seq_assoc3 {a b c d : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b c)) d) s Q) : WP isa (.seq a (.seq b (.seq c d))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => WP.assoc h)

theorem seq_assoc4 {a b c d e : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b (.seq c d))) e) s Q) : WP isa (.seq a (.seq b (.seq c (.seq d e)))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => seq_assoc3 h)

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

end VG.Proof.AesGcmSiv.X86_64
