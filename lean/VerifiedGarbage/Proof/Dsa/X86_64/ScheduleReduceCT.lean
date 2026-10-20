module
public import VerifiedGarbage.Proof.Dsa.X86_64.ReadyReduceCT
public import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCTState

import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.X86_64.CallOperands

/-! # Composable streaming-reduction timing steps -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def ScheduleUnaryPre (inputs : SchedulePublic → List (Operand × Nat))
    (a : Operand) (an : SchedulePublic → Nat) (p : SchedulePublic) (s : State) : Prop :=
  ScheduleState inputs p s ∧ Available p.layout a (an p) s

def scheduleReducePublic (d : Nat) (an : SchedulePublic → Nat)
    (hal : ∀ p, an p < 2 ^ 64) (hd : activeBytes ≤ d)
    (hend : ∀ p : SchedulePublic, d + p.layout.qLen ≤ usedBytes)
    (p : SchedulePublic) : ReadyReducePublic d :=
  ⟨p.layout, an p, p.qGreater, p.qOdd, hal p, hd, hend p⟩

theorem scheduleReduce_ct (M : Mont) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (d : Nat) (a : Operand) (an : SchedulePublic → Nat)
    (ha : pointerFits a.pointer) (hpa : stablePointer a.pointer) (hal : ∀ p, an p < 2 ^ 64)
    (hd : activeBytes ≤ d) (hd31 : d < 2 ^ 31)
    (hend : ∀ p : SchedulePublic, d + p.layout.qLen ≤ usedBytes)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (reduceHead a (Core.scalar d))) hc).isSome = true) :
    RelCT isa (Two (ScheduleUnaryPre inputs a an)) (Core.reduce M.mm a (Core.scalar d))
      (Two fun p s => ScheduleState inputs p s ∧ LocalReduced p.layout .q d s) := by
  refine two_post (two_map (scheduleReducePublic d an hal hd hend) ?_
    (readyReduce_ct M d a ha hpa hd31 hT)) ?_
  · intro p s ⟨hs, ba, has, hbl⟩
    exact ⟨hs.1, ba, has, hbl⟩
  · intro p s ⟨hs, ba, has, hbl⟩
    refine WP.mono (readyReduce_ok M hs.1 p.qGreater p.qOdd a ha has (hbl ▸ hal p) d hd (hend p))
      fun t h => ⟨h.schedule hs hd (hend p) (stable p), ?_⟩
    exact h.reduced (Nat.mod_lt _ (by have := p.qGreater; omega)) p.qFits

theorem CallResult.keepReduced {L : ExecutionLayout} {side other : ModulusSide}
    {d value e : Nat} {s t : State} (h : CallResult L side d value s t) (hs : Ready L s)
    (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes)
    (he : activeBytes ≤ e) (hee : e + other.length L ≤ usedBytes)
    (hsep : e + other.length L ≤ d ∨ d + side.length L ≤ e)
    (hr : LocalReduced L other e s) : LocalReduced L other e t := by
  have hbs := hs.readLocal other e he hee
  have hlen : (Spec.Rsa.bytesAt s.mem (off L.base e) (other.length L)).length = other.length L := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  have ht := h.local hd hend hbs (by rw [hlen]; exact hee) (by rw [hlen]; exact hsep)
  have htbytes := operand_bytesAt ht
  simp only [hlen] at htbytes
  change Spec.Rsa.bytesAt t.mem (off L.base e) (other.length L) = _ at htbytes
  unfold LocalReduced
  rw [htbytes]
  exact hr

theorem scheduleReduceKeep_ct (M : Mont) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (d e : Nat) (a : Operand) (an : SchedulePublic → Nat)
    (ha : pointerFits a.pointer) (hpa : stablePointer a.pointer) (hal : ∀ p, an p < 2 ^ 64)
    (hd : activeBytes ≤ d) (hd31 : d < 2 ^ 31)
    (hend : ∀ p : SchedulePublic, d + p.layout.qLen ≤ usedBytes)
    (he : activeBytes ≤ e) (hee : ∀ p : SchedulePublic, e + p.layout.qLen ≤ usedBytes)
    (hsep : ∀ p : SchedulePublic, e + p.layout.qLen ≤ d ∨ d + p.layout.qLen ≤ e)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (reduceHead a (Core.scalar d))) hc).isSome = true) :
    RelCT isa (Two fun p s => ScheduleUnaryPre inputs a an p s ∧ LocalReduced p.layout .q e s)
      (Core.reduce M.mm a (Core.scalar d))
      (Two fun p s => ScheduleState inputs p s ∧ LocalReduced p.layout .q d s ∧ LocalReduced p.layout .q e s) := by
  refine two_post (two_map (scheduleReducePublic d an hal hd hend) ?_
    (readyReduce_ct M d a ha hpa hd31 hT)) ?_
  · intro p s ⟨⟨hs, ba, has, hbl⟩, hr⟩
    exact ⟨hs.1, ba, has, hbl⟩
  · intro p s ⟨⟨hs, ba, has, hbl⟩, hr⟩
    refine WP.mono (readyReduce_ok M hs.1 p.qGreater p.qOdd a ha has (hbl ▸ hal p) d hd (hend p))
      fun t h => ⟨h.schedule hs hd (hend p) (stable p), ?_, ?_⟩
    · exact h.reduced (Nat.mod_lt _ (by have := p.qGreater; omega)) p.qFits
    · exact h.keepReduced hs.1 hd (hend p) he (hee p) (hsep p) hr

end VG.Proof.Dsa.X86_64
