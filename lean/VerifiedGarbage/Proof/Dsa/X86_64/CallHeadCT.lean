module

public import VerifiedGarbage.Proof.Dsa.X86_64.CallFinishCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Call
import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave

/-! # Public argument binding for complete arithmetic calls -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure Call3Public extends PowerFinishPublic where
  parentInverse : BitVec 64
  extent : pWorkspace ≤ bytes.x.Z
  childLow : slot bytes.x.w 8 ≤ bytes.x.o
  childHigh : bytes.x.o + slot bytes.x.wx 8 + tabBytes bytes.x.wx ≤ bytes.x.Z
  offsetBound : bytes.x.o < 2 ^ 31
  outputPositive : 1 ≤ outputLen
  outputBound : outputLen < 2 ^ 31
  outputWidth : bytes.x.wx = (outputLen + 7) / 8

def Call3Pre (a b output : Operand) (p : Call3Public) (s : State) : Prop :=
  Good s p.x.B p.x.Z p.x.w p.parentInverse ∧
  ChildReady s.mem p.x.B p.x.o p.x.wx p.modulus p.minv ∧
  (∃ ba bb : List Byte, OperandBytes s p.x.B p.x.Z a ba ∧ OperandBytes s p.x.B p.x.Z b bb ∧
    ba.length = p.baseLen ∧ bb.length = p.bytes.len) ∧
  pointerValue s.mem p.x.B a.pointer = p.base ∧ pointerValue s.mem p.x.B b.pointer = p.bytes.ptr ∧
  pointerValue s.mem p.x.B output.pointer = p.output ∧
  word s.mem p.x.B output.length.offset = BitVec.ofNat 64 p.outputLen ∧
  (∀ j < p.outputLen, InRegions s.wr (p.output + BitVec.ofNat 64 j) 1) ∧
  (∀ j < p.outputLen, p.x.Z ≤ ofs p.x.B (p.output + BitVec.ofNat 64 j))

def callHead (a b output : Operand) (o : Nat) : List Instr :=
  Core.operand arg argLen a ++ Core.operand arg2 arg2Len b ++
    Core.operand result resultLen output ++ Core.enter o

/-- The head can use any workspace offset shared by the two executions. -/
theorem callHead_run {p : Call3Public} {s : State} {a b output : Operand}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    (h : Call3Pre a b output p s) :
    WP isa (.block (callHead a b output p.x.o)) s fun t =>
      PowerFinishPre p.toPowerFinishPublic t ∧ Frm p.x.B argumentRanges s.mem t.mem ∧ Keep coreRegs s t := by
  obtain ⟨hg, child, ⟨ba, bb, has, hbs, hbl, hel⟩, hp, hep, hop, hol, hout, hprefix⟩ := h
  have h256 : 256 ≤ slot p.x.w 8 := by unfold slot hdrBytes; omega
  have hlo : slot p.x.w 8 ≤ p.x.o := p.childLow
  have hhi : p.x.o + slot p.x.wx 8 + tabBytes p.x.wx ≤ p.x.Z := p.childHigh
  unfold callHead
  rw [WP.block_append_iff]
  refine WP.mono (arguments_ok hg child p.extent (by omega) (by omega) a b output ha hb ho)
    fun u ⟨hgu, hcu, hargs, _, hf, hk⟩ => ?_
  refine WP.mono (enter_ok hgu hcu.header p.childLow p.childHigh p.offsetBound)
    fun t ⟨hct, hmem, hkt⟩ => ?_
  have hft : Frm p.x.B argumentRanges s.mem t.mem := by rw [hmem]; exact hf
  have hkt' : Keep coreRegs s t := (hk.trans hkt).mono (by decide)
  have hargs' : Arguments t.mem s.mem p.x.B a b output := hmem ▸ hargs
  have childt : ChildReady t.mem p.x.B p.x.o p.x.wx p.modulus p.minv := hmem ▸ hcu
  refine ⟨⟨⟨hct, ⟨hct.good, childt.modulus, childt.inverse⟩,
    ba, bb, hargs'.1.trans hp, hargs'.2.1.trans has.length,
    hargs'.2.2.1.trans hep, hargs'.2.2.2.1.trans hbs.length, hbl, hel, ?_, ?_⟩,
    ⟨⟨p.minv, hct, hargs'.2.2.2.2.1.trans hop, hargs'.2.2.2.2.2.trans hol⟩,
      p.outputPositive, p.outputBound, p.outputWidth, ?_, hprefix⟩⟩, hft, hkt'⟩
  · rw [← hp]
    exact arguments_source hft hkt' (Nat.le_trans (by decide) p.extent) has.source
  · rw [← hep]
    exact arguments_source hft hkt' (Nat.le_trans (by decide) p.extent) hbs.source
  · intro j hj
    rw [hkt'.2.2]
    exact hout j hj

theorem callHead_ok {p : Call3Public} {s : State} {a b output : Operand}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    (h : Call3Pre a b output p s) :
    WP isa (.block (callHead a b output p.x.o)) s (PowerFinishPre p.toPowerFinishPublic) :=
  WP.mono (callHead_run ha hb ho h) (fun _ h => h.1)

/-- The pointer-binding block addresses only saved fields and header slots;
operand bytes are not inspected until the arithmetic call. -/
theorem callHead_ct {a b output : Operand} {o : Nat}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (callHead a b output o)) hc).isSome = true) :
    RelCT isa (Two (Call3Pre a b output)) (.block (callHead a b output o)) (fun _ _ => True) :=
  two_taint [.rdi] (pins_of (fun p _ => p.x.B) (by
    intro p s h r hr
    obtain rfl := List.mem_singleton.mp hr
    exact h.1.rdi)) hT

/-- Exponentiation from parent argument binding through result storage. -/
theorem corePow_ct (M : Mont) (Sq : MontS) {a b output : Operand} {o : Nat}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (callHead a b output o)) hc).isSome = true) :
    RelCT isa (Two fun p s => Call3Pre a b output p s ∧ p.x.o = o)
      (Core.pow Sq.mm M.mm o a b output) (fun _ _ => True) := by
  change RelCT isa _ (.seq (.block (callHead a b output o))
    (.seq (Arithmetic.power Sq.mm M.mm arg argLen arg2 arg2Len) (seqs Core.finish))) _
  refine RelCT.seq (two_post (Ψ := fun p s => PowerFinishPre p.toPowerFinishPublic s)
    (two_map (fun p : Call3Public => p) (fun _ _ h => h.1) (callHead_ct hT)) ?_)
    (two_map Call3Public.toPowerFinishPublic (fun _ _ h => h) (powerFinish_ct M Sq))
  intro p s ⟨h, heq⟩
  rw [← heq]
  exact callHead_ok ha hb ho h

structure Call3ProductPublic extends Call3Public where
  secondFits : (bytes.len + 7) / 8 ≤ bytes.x.wx

def Call3ProductPublic.finish (p : Call3ProductPublic) : ProductFinishPublic :=
  { p.toPowerCallPublic with secondFits := p.secondFits, output := p.output, outputLen := p.outputLen }

theorem coreProduct_ct (M : Mont) {a b output : Operand} {o : Nat}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (callHead a b output o)) hc).isSome = true) :
    RelCT isa (Two fun p : Call3ProductPublic => fun s => Call3Pre a b output p.toCall3Public s ∧ p.x.o = o)
      (Core.product M.mm o a b output) (fun _ _ => True) := by
  change RelCT isa _ (.seq (.block (callHead a b output o))
    (.seq (Arithmetic.product M.mm arg argLen arg2 arg2Len) (seqs Core.finish))) _
  refine RelCT.seq (two_post (Ψ := fun p s => ProductFinishPre p.finish s)
    (two_map Call3ProductPublic.toCall3Public (fun _ _ h => h.1) (callHead_ct hT)) ?_)
    (two_map Call3ProductPublic.finish (fun _ _ h => h) (productFinish_ct M))
  intro p s ⟨h, heq⟩
  rw [← heq]
  exact callHead_ok ha hb ho h

end VG.Proof.Dsa.X86_64
