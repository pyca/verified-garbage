module

public import VerifiedGarbage.Proof.Dsa.AArch64.CheckOperands
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import Batteries.Logic
public import VerifiedGarbage.Proof.Dsa.AArch64.CallFinishCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Call
import VerifiedGarbage.Proof.Dsa.AArch64.CallHeader
import VerifiedGarbage.Proof.Framework.Block

/-! ### `Dsa.AArch64.CallHeadCT`, which this module and modules that import it used -/

section

/-! # Public argument binding for complete arithmetic calls -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure Call3Public extends PowerFinishPublic where
  parentInverse : BitVec 64
  extent : pWorkspace ≤ bytes.x.Z
  childLow : slot bytes.x.w 8 ≤ bytes.x.o
  childHigh : bytes.x.o + slot bytes.x.wx 8 + tabBytes bytes.x.wx ≤ bytes.x.Z
  offsetBound : bytes.x.o < 2 ^ 16
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
  have h256 : 256 ≤ slot p.x.w 8 := by unfold slot hdrBytes; omega_using []
  have hlo : slot p.x.w 8 ≤ p.x.o := p.childLow
  have hhi : p.x.o + slot p.x.wx 8 + tabBytes p.x.wx ≤ p.x.Z := p.childHigh
  unfold callHead
  rw [WP.block_append_iff]
  refine WP.mono (arguments_ok hg child p.extent (by omega_using [h256, hlo]) (by omega_using [hhi]) a b output ha hb ho)
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
    rw [hkt'.wr]
    exact hout j hj

theorem callHead_ok {p : Call3Public} {s : State} {a b output : Operand}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    (h : Call3Pre a b output p s) :
    WP isa (.block (callHead a b output p.x.o)) s (PowerFinishPre p.toPowerFinishPublic) :=
  WP.mono (callHead_run ha hb ho h) (fun _ h => h.1)

/-- The pointer-binding block addresses only saved fields and header slots;
operand bytes are not inspected until the arithmetic call. -/
theorem callHead_ct {a b output : Operand} {o : Nat}
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (callHead a b output o)) hc).isSome = true) :
    RelCT isa (Two (Call3Pre a b output)) (.block (callHead a b output o)) (fun _ _ => True) :=
  two_taint [.x0] (pins_of (fun p _ => p.x.B) (by
    intro p s h r hr
    obtain rfl := List.mem_singleton.mp hr
    exact h.1.x0)) hT

/-- Exponentiation from parent argument binding through result storage. -/
theorem corePow_ct (M : Mont) {a b output : Operand} {o : Nat}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (callHead a b output o)) hc).isSome = true) :
    RelCT isa (Two fun p s => Call3Pre a b output p s ∧ p.x.o = o)
      (Core.pow M.mm o a b output) (fun _ _ => True) := by
  change RelCT isa _ (.seq (.block (callHead a b output o))
    (.seq (Arithmetic.power M.mm arg argLen arg2 arg2Len) (seqs Core.finish))) _
  refine RelCT.seq (two_post (Ψ := fun p s => PowerFinishPre p.toPowerFinishPublic s)
    (two_map (fun p : Call3Public => p) (fun _ _ h => h.1) (callHead_ct hT)) ?_)
    (two_map Call3Public.toPowerFinishPublic (fun _ _ h => h) (powerFinish_ct M))
  intro p s ⟨h, heq⟩
  rw [← heq]
  exact callHead_ok ha hb ho h

structure Call3ProductPublic extends Call3Public where
  secondFits : (bytes.len + 7) / 8 ≤ bytes.x.wx

def Call3ProductPublic.finish (p : Call3ProductPublic) : ProductFinishPublic :=
  { p.toPowerCallPublic with secondFits := p.secondFits, output := p.output, outputLen := p.outputLen }

theorem coreProduct_ct (M : Mont) {a b output : Operand} {o : Nat}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (callHead a b output o)) hc).isSome = true) :
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

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.CallAddCT`, which only this module used -/

section

/-! # Constant time of the complete parent-to-child scalar addition -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def CallAddPre (a b output : Operand) (p : Call3ProductPublic) (s : State) : Prop :=
  Call3Pre a b output p.toCall3Public s ∧ p.x.o = qWorkspace ∧
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem p.base p.baseLen) < p.modulus ∧
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem p.bytes.ptr p.bytes.len) < p.modulus

theorem callAddHead_ok {p : Call3ProductPublic} {s : State} {a b output : Operand}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    (h : CallAddPre a b output p s) :
    WP isa (.block (callHead a b output qWorkspace)) s (AddFinishPre p.finish) := by
  obtain ⟨h, heq, hbr, her⟩ := h
  rw [← heq]
  refine WP.mono (callHead_run ha hb ho h) fun t ⟨ht, hf, hk⟩ => ?_
  obtain ⟨_, _, ⟨ba, bb, has, hbs, hbl, hel⟩, hp, hep, _⟩ := h
  have hsa : Src s p.x.B p.x.Z p.base ba := hp ▸ has.source
  have hsb : Src s p.x.B p.x.Z p.bytes.ptr bb := hep ▸ hbs.source
  have hta := arguments_source hf hk (Nat.le_trans (by decide) p.extent) hsa
  have htb := arguments_source hf hk (Nat.le_trans (by decide) p.extent) hsb
  refine ⟨ht, ?_, ?_⟩
  · change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem p.base p.baseLen) < p.modulus
    rw [← hbl, sourceBytes_eq hta]
    rw [← hbl, sourceBytes_eq hsa] at hbr
    exact hbr
  · change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem p.bytes.ptr p.bytes.len) < p.modulus
    rw [← hel, sourceBytes_eq htb]
    rw [← hel, sourceBytes_eq hsb] at her
    exact her

theorem coreAdd_ct {a b output : Operand}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (callHead a b output qWorkspace)) hc).isSome = true) :
    RelCT isa (Two (CallAddPre a b output)) (Core.add a b output) (fun _ _ => True) := by
  change RelCT isa _ (.seq (.block (callHead a b output qWorkspace))
    (seqs ([Arithmetic.load aX arg argLen, Arithmetic.load aXm arg2 arg2Len,
      Crt.addMod aY aX aXm] ++ Core.finish))) _
  refine RelCT.seq (two_post (Ψ := fun p s => AddFinishPre p.finish s)
    (two_map Call3ProductPublic.toCall3Public (fun _ _ h => h.1) (callHead_ct hT))
    (fun _ _ h => callAddHead_ok ha hb ho h)) ?_
  exact RelCT.seqs_append (by simp) (by simp [Core.finish])
    (two_map Call3ProductPublic.finish (fun _ _ h => h) addFinish_ct)

end VG.Proof.Dsa.AArch64

end

end

/-! # Arithmetic timing in a persistent DSA execution workspace -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def ExecutionLayout.pointer (L : ExecutionLayout) : Pointer → Addr
  | .input f => L.fields f
  | .local d => off L.base d
  | .signatureS => L.fields .signature + L.fields .qLen

theorem Ready.publicPointer {L : ExecutionLayout} {s : State} (h : Ready L s)
    (p : Pointer) (hp : stablePointer p) : pointerValue s.mem L.base p = L.pointer p := by
  cases p with
  | input f => exact h.fields f hp
  | «local» _ => rfl
  | signatureS => exact congrArg₂ (· + ·) (h.fields .signature (by decide)) (h.fields .qLen (by decide))

structure ReadyCallPublic (side : ModulusSide) (d : Nat) where
  layout : ExecutionLayout
  baseLen : Nat
  exponentLen : Nat
  greater : 1 < side.value layout
  odd : side.value layout % 2 = 1
  basePositive : 1 ≤ baseLen
  baseFits : (baseLen + 7) / 8 ≤ side.words layout
  exponentPositive : 1 ≤ exponentLen
  exponentBound : exponentLen ≤ 1024
  outputStart : activeBytes ≤ d
  outputEnd : d + side.length layout ≤ usedBytes

def ReadyCallPublic.call {side : ModulusSide} {d : Nat} (p : ReadyCallPublic side d)
    (a b : Operand) : Call3Public where
  bytes := ⟨⟨p.layout.base, activeBytes, side.offset, outerWords, side.words p.layout⟩,
    p.layout.pointer b.pointer, p.exponentLen⟩
  minv := side.inverse p.layout
  modulus := side.value p.layout
  lower := (side.bounds p.layout).1
  fits := (side.bounds p.layout).2.1
  upper := by change outerWords < 2 ^ 30; decide
  greater := p.greater
  odd := p.odd
  base := p.layout.pointer a.pointer
  baseLen := p.baseLen
  width48 := (side.bounds p.layout).2.1
  basePositive := p.basePositive
  baseFits := p.baseFits
  expPositive := p.exponentPositive
  expLimit := p.exponentBound
  output := off p.layout.base d
  outputLen := side.length p.layout
  parentInverse := 0
  extent := by change pWorkspace ≤ activeBytes; decide
  childLow := (side.bounds p.layout).2.2.1
  childHigh := (side.bounds p.layout).2.2.2.2.1
  offsetBound := (side.bounds p.layout).2.2.2.1
  outputPositive := (side.bounds p.layout).2.2.2.2.2.1
  outputBound := (side.bounds p.layout).2.2.2.2.2.2
  outputWidth := rfl

def ReadyCallPre (side : ModulusSide) (d : Nat) (a b : Operand)
    (p : ReadyCallPublic side d) (s : State) : Prop := Ready p.layout s ∧
  ∃ ba bb : List Byte, OperandBytes s p.layout.base activeBytes a ba ∧
    OperandBytes s p.layout.base activeBytes b bb ∧ ba.length = p.baseLen ∧ bb.length = p.exponentLen

theorem readyCall_pre {side : ModulusSide} {d : Nat} {a b : Operand}
    {p : ReadyCallPublic side d} {s : State}
    (ha : stablePointer a.pointer) (hb : stablePointer b.pointer) (h : ReadyCallPre side d a b p s) :
    Call3Pre a b ⟨.local d, side.lengthField⟩ (p.call a b) s := by
  obtain ⟨hr, ba, bb, has, hbs, hbl, hel⟩ := h
  exact ⟨hr.parent, hr.child side, ⟨ba, bb, has, hbs, hbl, hel⟩,
    hr.publicPointer a.pointer ha, hr.publicPointer b.pointer hb, rfl, hr.length side,
    hr.local_write p.outputEnd, hr.local_out p.outputStart p.outputEnd⟩

theorem readyPow_ct (M : Mont) (side : ModulusSide) (d : Nat) (a b : Operand)
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer)
    (hd : d < 2 ^ 16)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block (callHead a b ⟨.local d, side.lengthField⟩ side.offset)) hc).isSome = true) :
    RelCT isa (Two (ReadyCallPre side d a b))
      (Core.pow M.mm side.offset a b ⟨.local d, side.lengthField⟩) (fun _ _ => True) :=
  two_map (fun p : ReadyCallPublic side d => p.call a b)
    (fun _ _ h => ⟨readyCall_pre hpa hpb h, rfl⟩)
    (corePow_ct M ha hb hd hT)

structure ReadyProductPublic (side : ModulusSide) (d : Nat) extends ReadyCallPublic side d where
  secondFits : (exponentLen + 7) / 8 ≤ side.words layout

def ReadyProductPublic.call {side : ModulusSide} {d : Nat} (p : ReadyProductPublic side d)
    (a b : Operand) : Call3ProductPublic :=
  { p.toReadyCallPublic.call a b with secondFits := p.secondFits }

theorem readyProduct_ct (M : Mont) (side : ModulusSide) (d : Nat) (a b : Operand)
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer)
    (hd : d < 2 ^ 16)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block (callHead a b ⟨.local d, side.lengthField⟩ side.offset)) hc).isSome = true) :
    RelCT isa (Two fun p : ReadyProductPublic side d => ReadyCallPre side d a b p.toReadyCallPublic)
      (Core.product M.mm side.offset a b ⟨.local d, side.lengthField⟩) (fun _ _ => True) :=
  two_map (fun p : ReadyProductPublic side d => p.call a b)
    (fun _ _ h => ⟨readyCall_pre hpa hpb h, rfl⟩)
    (coreProduct_ct M ha hb hd hT)

def ReadyAddPre (d : Nat) (a b : Operand) (p : ReadyProductPublic .q d) (s : State) : Prop :=
  ReadyCallPre .q d a b p.toReadyCallPublic s ∧
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (p.layout.pointer a.pointer) p.baseLen) < p.layout.subgroup ∧
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (p.layout.pointer b.pointer) p.exponentLen) < p.layout.subgroup

theorem readyAdd_ct (d : Nat) (a b : Operand)
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer)
    (hd : d < 2 ^ 16)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block (callHead a b (Core.scalar d) qWorkspace)) hc).isSome = true) :
    RelCT isa (Two (ReadyAddPre d a b)) (Core.add a b (Core.scalar d)) (fun _ _ => True) :=
  two_map (fun p : ReadyProductPublic .q d => p.call a b)
    (fun _ _ h => ⟨readyCall_pre hpa hpb h.1, rfl, h.2⟩)
    (coreAdd_ct ha hb hd hT)

end VG.Proof.Dsa.AArch64
