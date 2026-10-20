module

public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack

/-! Saved input addresses and lengths determine the operand-import trace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

structure ImportAtInput (p : Inputs) (slots : List Nat) (s : State) : Prop where
  context : Context p slots s
  ready : ArithmeticReady p.base p.len p.w s

structure ImportArgsReady (p : Inputs) (slot : Nat) (k : Nat) (s : State) : Prop where
  ready : ArithmeticReady p.base p.len p.w s
  source : s.gpr .r4 = p.slotValue slot
  count : s.gpr .r6 = BitVec.ofNat 32 k

theorem importArgs_ready (s : State) {p : Inputs} {slots : List Nat} {slot countSlot k : Nat}
    (stable : stableSlots slots = true) (hs : slot ∈ slots) (hc : countSlot ∈ slots)
    (count : p.slotValue countSlot = BitVec.ofNat 32 k) (h : ImportAtInput p slots s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.Domain.importArgs slot countSlot)) s (ImportArgsReady p slot k) := by
  refine WP.mono (importArgs_ok s slot countSlot h.context stable hs hc) ?_
  rintro u ⟨⟨source, length, mem⟩, rest⟩
  exact ⟨h.ready.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr), source, length.trans count⟩

theorem importAt_ct {p : Inputs} {slots : List Nat} {a slot countSlot k : Nat}
    (stable : stableSlots slots = true) (hs : slot ∈ slots) (hc : countSlot ∈ slots)
    (count : p.slotValue countSlot = BitVec.ofNat 32 k) (ha : a < 8) :
    RelCT isa (fun s t => ImportAtInput p slots s ∧ ImportAtInput p slots t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.importAt a slot countSlot) (fun _ _ => True) := by
  have args := (importArgs_ct slot countSlot).mono
    (P' := fun (s t : State) => ImportAtInput p slots s ∧ ImportAtInput p slots t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have operand := (importOperand_ct (base := p.base) (src := p.slotValue slot) (len := p.len)
    (w := p.w) (k := k) ha).mono
    (P' := fun (s t : State) => ImportArgsReady p slot k s ∧ ImportArgsReady p slot k t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.1.source, h.2.1.source, h.1.count, h.2.1.count, h.2.2⟩)
    (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.importAt
  exact relCT_chain args (fun s h => importArgs_ready s stable hs hc count h)
    (fun s h => importArgs_ready s stable hs hc count h) operand

end VG.Proof.Ffdh.Arm
