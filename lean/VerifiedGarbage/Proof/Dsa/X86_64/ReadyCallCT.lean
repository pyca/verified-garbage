module

public import VerifiedGarbage.Proof.Dsa.X86_64.CallHeadCT
public import VerifiedGarbage.Proof.Dsa.X86_64.CheckOperands
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import Batteries.Logic

/-! ### `Dsa.X86_64.CallAddCT`, which only this module used -/

section

/-! # Constant time of the complete parent-to-child scalar addition -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64 VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (callHead a b output qWorkspace)) hc).isSome = true) :
    RelCT isa (Two (CallAddPre a b output)) (Core.add a b output) (fun _ _ => True) := by
  change RelCT isa _ (.seq (.block (callHead a b output qWorkspace))
    (seqs ([Arithmetic.load aX arg argLen, Arithmetic.load aXm arg2 arg2Len,
      Crt.addMod aY aX aXm] ++ Core.finish))) _
  refine RelCT.seq (two_post (Ψ := fun p s => AddFinishPre p.finish s)
    (two_map Call3ProductPublic.toCall3Public (fun _ _ h => h.1) (callHead_ct hT))
    (fun _ _ h => callAddHead_ok ha hb ho h)) ?_
  exact RelCT.seqs_append (by simp) (by simp [Core.finish])
    (two_map Call3ProductPublic.finish (fun _ _ h => h) addFinish_ct)

end VG.Proof.Dsa.X86_64

end

end


/-! # Arithmetic timing in a persistent DSA execution workspace -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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

theorem readyPow_ct (M : Mont) (Sq : MontS) (side : ModulusSide) (d : Nat) (a b : Operand)
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer)
    (hd : d < 2 ^ 31)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi])
      (.block (callHead a b ⟨.local d, side.lengthField⟩ side.offset)) hc).isSome = true) :
    RelCT isa (Two (ReadyCallPre side d a b))
      (Core.pow Sq.mm M.mm side.offset a b ⟨.local d, side.lengthField⟩) (fun _ _ => True) :=
  two_map (fun p : ReadyCallPublic side d => p.call a b)
    (fun _ _ h => ⟨readyCall_pre hpa hpb h, rfl⟩)
    (corePow_ct M Sq ha hb hd hT)

structure ReadyProductPublic (side : ModulusSide) (d : Nat) extends ReadyCallPublic side d where
  secondFits : (exponentLen + 7) / 8 ≤ side.words layout

def ReadyProductPublic.call {side : ModulusSide} {d : Nat} (p : ReadyProductPublic side d)
    (a b : Operand) : Call3ProductPublic :=
  { p.toReadyCallPublic.call a b with secondFits := p.secondFits }

theorem readyProduct_ct (M : Mont) (side : ModulusSide) (d : Nat) (a b : Operand)
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer)
    (hd : d < 2 ^ 31)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi])
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
    (hd : d < 2 ^ 31)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi])
      (.block (callHead a b (Core.scalar d) qWorkspace)) hc).isSome = true) :
    RelCT isa (Two (ReadyAddPre d a b)) (Core.add a b (Core.scalar d)) (fun _ _ => True) :=
  two_map (fun p : ReadyProductPublic .q d => p.call a b)
    (fun _ _ h => ⟨readyCall_pre hpa hpb h.1, rfl, h.2⟩)
    (coreAdd_ct ha hb hd hT)

end VG.Proof.Dsa.X86_64
