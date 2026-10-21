module

public import VerifiedGarbage.TCB.X86.State
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset

/-! # Read-only inputs and public frame slots for a complete exponent reduction -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

structure ArrayGeometry where
  sp : BitVec 32
  workspace : BitVec 32
  size : Nat
  n : Nat
  src : Nat
  exponent : Nat

def ArrayGeometry.base (g : ArrayGeometry) : Addr := g.workspace.setWidth 64
def ArrayGeometry.workspaceRegion (g : ArrayGeometry) : Region := ⟨g.base, g.size⟩
def ArrayGeometry.stackRegion (g : ArrayGeometry) : Region := ⟨g.sp.setWidth 64, 20⟩
def ArrayGeometry.pointer (g : ArrayGeometry) (i : Nat) : BitVec 32 :=
  g.workspace + BitVec.ofNat 32 (g.src + 4 * (g.n - 1)) - BitVec.ofNat 32 (4 * i)

structure ArrayGeometry.Valid (g : ArrayGeometry) : Prop where
  positive : 0 < g.n
  sourceFit : g.src + 4 * g.n ≤ g.size
  exponentFit : g.exponent + 8 ≤ g.size
  separate : g.workspaceRegion.Disjoint g.stackRegion

structure ArrayContext (g : ArrayGeometry) (candidate exponent : Nat) (s : State) : Prop where
  scratch : Scr s g.base g.size
  stack : Sieve.StackContext g.sp s
  candidateValue : val32 s.mem g.base g.src g.n = candidate
  exponentEq : exponentValue s.mem g.base g.exponent = exponent

structure ArrayState (g : ArrayGeometry) (candidate exponent i : Nat) (s : State) : Prop where
  context : ArrayContext g candidate exponent s
  pointer : s.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.pointer i
  count : s.mem.readW (off (g.sp.setWidth 64) 4) 32 = BitVec.ofNat 32 (g.n - i)
  value : pair (s.gpr .ecx) (s.gpr .ebx) = (candidate / 2 ^ (32 * (g.n - i))) % exponent
  bound : pair (s.gpr .ecx) (s.gpr .ebx) < exponent

theorem ArrayContext.workspace {g : ArrayGeometry} {candidate exponent : Nat} {s : State}
    (C : ArrayContext g candidate exponent s) : s.gpr .edi = g.workspace := by
  apply BitVec.eq_of_toNat_eq
  have H := C.scratch.edi_toNat
  change (s.gpr .edi).toNat = (g.workspace.setWidth 64).toNat at H
  rw [BitVec.toNat_setWidth] at H
  have := g.workspace.isLt
  omega

theorem ArrayContext.keepReadonly {g : ArrayGeometry} {candidate exponent : Nat} {s t : State}
    (C : ArrayContext g candidate exponent s) {rs : List Reg} (K : Keeps rs s t)
    (sp : .esp ∉ rs) (edi : .edi ∉ rs) (M : t.mem = s.mem) : ArrayContext g candidate exponent t :=
  ⟨C.scratch.of_keeps K edi sp, C.stack.keep K sp, by rw [M]; exact C.candidateValue,
    by rw [M]; exact C.exponentEq⟩

theorem ArrayContext.keepFrame {g : ArrayGeometry} (v : g.Valid) {candidate exponent : Nat} {s t : State}
    (C : ArrayContext g candidate exponent s) {rs : List Reg} (K : Keeps rs s t)
    (sp : .esp ∉ rs) (edi : .edi ∉ rs) (F : Frame [g.stackRegion] s.mem t.mem) : ArrayContext g candidate exponent t := by
  have read (d : Nat) (fit : d + 4 ≤ g.size) : t.mem.readW (off g.base d) 32 = s.mem.readW (off g.base d) 32 :=
    F.readW (r := g.workspaceRegion) (w := 32)
      (Offset.contains_base _ fit (by have := C.scratch.nowrap; omega))
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact v.separate) (by decide)
  refine ⟨C.scratch.of_keeps K edi sp, C.stack.keep K sp, ?_, ?_⟩
  · rw [← C.candidateValue]
    apply val32_congr
    intro i index
    exact congrArg BitVec.toNat (read _ (by have := v.sourceFit; omega))
  · rw [← C.exponentEq]
    unfold exponentValue
    rw [read _ (by have := v.exponentFit; omega), read _ (by have := v.exponentFit; omega)]

theorem arrayStackFrame {g : ArrayGeometry} {m m' : Mem}
    (O : Outside (g.sp.setWidth 64) 0 20 m m') : Frame [g.stackRegion] m m' := by
  simpa only [ArrayGeometry.stackRegion, off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
    using VG.Proof.Bignum.outside_frame O (by decide)

theorem ArrayGeometry.pointer_eq {g : ArrayGeometry} {i : Nat} (index : i < g.n) :
    g.pointer i = g.workspace + BitVec.ofNat 32 (g.src + 4 * (g.n - 1 - i)) := by
  unfold ArrayGeometry.pointer
  apply BitVec.sub_eq_iff_eq_add.mpr
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2
  omega

end VG.Proof.RsaKeyGen.X86.Mod64
