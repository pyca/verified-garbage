module

public import VerifiedGarbage.Proof.Dsa.AArch64.CallHeadCT
public import VerifiedGarbage.Proof.Dsa.AArch64.CheckOperands
import VerifiedGarbage.Proof.Dsa.AArch64.CallAddCT

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
