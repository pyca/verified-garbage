module

public import VerifiedGarbage.Impl.Dsa.X86.Entry
import VerifiedGarbage.Proof.Dsa.X86.Layout
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Dsa.X86.ShapeSavedFrame
import VerifiedGarbage.Proof.Dsa.X86.SavedFrame
import VerifiedGarbage.Proof.Dsa.X86.RunBytes
import VerifiedGarbage.Proof.Framework.Offset

/-! Frames for schedules with retained tables beyond the ordinary arithmetic workspace. -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

/-- A schedule preserves input pointers and saved registers, and writes only its
workspace or helper-call stack. The workspace extent is explicit. -/
structure ScheduleFrame (base : Addr) (size : Nat) (s t : State) : Prop where
  keeps : Keeps powerClob s t
  outside : StackOutside (s.gpr .esp) base size s.mem t.mem
  fields : ∀ f : Field, f ≠ .mask →
    t.mem.readW (off base (Layout.field f)) 32 = s.mem.readW (off base (Layout.field f)) 32
  saved : ∀ regs, VG.X86.Spill.Saved s.mem (off base) regs Entry.savedRegisters →
    VG.X86.Spill.Saved t.mem (off base) regs Entry.savedRegisters

theorem Execution.schedule {base : Addr} {size : Nat} {s t : State}
    (E : Execution base s t) (extent : usedBytes ≤ size) : ScheduleFrame base size s t :=
  ⟨E.keeps, fun a ha hs => execution_outside E a (by omega) hs,
    fun _ h => runFrame_field E.mem h, fun _ h => E.saved h⟩

theorem ScheduleFrame.trans {base : Addr} {size : Nat} {s t u : State}
    (F : ScheduleFrame base size s t) (G : ScheduleFrame base size t u) :
    ScheduleFrame base size s u := by
  refine ⟨F.keeps.trans G.keeps, ?_, fun f h => (G.fields f h).trans (F.fields f h),
    fun regs h => G.saved regs (F.saved regs h)⟩
  intro a ha hs
  exact (G.outside a ha (by rw [F.keeps.1 .esp (by decide)]; exact hs)).trans (F.outside a ha hs)

theorem ScheduleFrame.pointer {base : Addr} {size : Nat} {s t : State}
    (F : ScheduleFrame base size s t) {p : Pointer} (hp : StablePointer p) :
    pointerValue base t p = pointerValue base s p := by
  cases p with
  | input f => exact F.fields f hp
  | «local» d => simp only [pointerValue, F.keeps.1 .edi (by decide)]
  | signatureS => simp only [pointerValue, F.fields .signature (by decide), F.fields .qLen (by decide)]

theorem ScheduleFrame.buffer {base : Addr} {size len : Nat} {s t : State} {p : Pointer}
    (F : ScheduleFrame base size s t) (B : CallerBuffer s base size p len) (hp : StablePointer p) :
    CallerBuffer t base size p len := by
  have P := F.pointer hp
  exact ⟨by rw [F.keeps.1 .esp (by decide)]; exact B.room,
    by rw [P]; exact B.fits, by rw [P,F.keeps.2.1,F.keeps.2.2]; exact B.read,
    by rw [P]; exact B.apart, by rw [P,F.keeps.1 .esp (by decide)]; exact B.stack⟩

theorem ScheduleFrame.bytes {base p : Addr} {size len : Nat} {s t : State}
    (F : ScheduleFrame base size s t) (hl : len ≤ 2^64)
    (apart : Region.Disjoint ⟨p,len⟩ ⟨base,size⟩)
    (stack : Region.Disjoint ⟨p,len⟩ (callStack (s.gpr .esp))) :
    Spec.Rsa.bytesAt t.mem p len = Spec.Rsa.bytesAt s.mem p len := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  have ilt := List.mem_range.mp hi
  have inside := Offset.contains_base p (show i+1≤len by omega) (show i<2^64 by omega)
  apply F.outside _ ?_ (stack _ inside)
  have H := apart _ inside
  change ¬ (ofs base (p+BitVec.ofNat 64 i)+1≤size) at H
  omega

theorem ScheduleFrame.value {base : Addr} {size len : Nat} {s t : State} {p : Pointer}
    (F : ScheduleFrame base size s t) (B : CallerBuffer s base size p len) (hp : StablePointer p) :
    operandValue t base p len = operandValue s base p len := by
  unfold operandValue
  rw [F.pointer hp, F.bytes (by have := B.fits; omega) B.apart B.stack]

theorem ScheduleFrame.moduli {base : Addr} {size pLen qLen p q : Nat} {s t : State}
    (F : ScheduleFrame base size s t) (M : Moduli base size pLen qLen p q s) :
    Moduli base size pLen qLen p q t :=
  ⟨M.scr.of_keeps F.keeps (by decide),M.extent,M.widths,
    F.buffer M.pBuffer (by decide),F.buffer M.qBuffer (by decide),
    (F.value M.pBuffer (by decide)).trans M.pValue,
    (F.value M.qBuffer (by decide)).trans M.qValue,
    M.pLarge,M.qLarge,M.pOdd,M.qOdd⟩

/-- Convert a precise footprint once; composition then does not depend on its layout. -/
theorem ScheduleFrame.of_ranges {base : Addr} {size : Nat} {s t : State} {rs : List (Nat × Nat)}
    (K : Keeps powerClob s t) (O : StackOuts base (s.gpr .esp) rs s.mem t.mem)
    (bounds : ∀ r∈rs, r.1+r.2≤size)
    (fields : ∀ f : Field, f ≠ .mask → ∀ r∈rs,
      Layout.field f+4≤r.1 ∨ r.1+r.2≤Layout.field f)
    (saved : ∀ p∈Entry.savedRegisters, ∀ r∈rs, p.2+4≤r.1 ∨ r.1+r.2≤p.2) :
    ScheduleFrame base size s t := by
  refine ⟨K,?_,?_,?_⟩
  · intro a ha hs
    exact O a (fun r hr => .inr (Nat.le_trans (bounds r hr) ha)) (.inr hs)
  · intro f hf
    apply BitVec.eq_of_toNat_eq
    have H := O.val32 (k := 1) (fields f hf) (by
      have H := (VG.Proof.Dsa.X86.Layout.field_bounds f).2
      change Layout.field f+4≤8256 at H
      change _≤15712; omega)
    simpa only [val32,Nat.mul_zero,Nat.add_zero] using H
  · intro regs S p hp
    have B := saved_bounds hp
    have H := O.val32 (k := 1) (saved p hp) (by change _≤15712; omega)
    have W : t.mem.readW (off base p.2) 32 = s.mem.readW (off base p.2) 32 := by
      apply BitVec.eq_of_toNat_eq
      simpa only [val32,Nat.mul_zero,Nat.add_zero] using H
    exact W.trans (S p hp)

end VG.Proof.Dsa.X86
