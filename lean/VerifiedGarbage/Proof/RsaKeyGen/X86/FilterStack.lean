module

public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
public import VerifiedGarbage.TCB.X86.State
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.MemoryFrame

/-! ### `RsaKeyGen.X86.Mod64ArrayContext`, which this module and modules that import it used -/

section

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
  omega_using [H]

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
      (Offset.contains_base _ fit (by have := C.scratch.nowrap; omega_using [fit, this]))
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact v.separate) (by decide)
  refine ⟨C.scratch.of_keeps K edi sp, C.stack.keep K sp, ?_, ?_⟩
  · rw [← C.candidateValue]
    apply val32_congr
    intro i index
    exact congrArg BitVec.toNat (read _ (by have := v.sourceFit; omega_using [index, this]))
  · rw [← C.exponentEq]
    unfold exponentValue
    rw [read _ (by have := v.exponentFit; omega_using [this]), read _ (by have := v.exponentFit; omega_using [this])]

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
  omega_using [index]

end VG.Proof.RsaKeyGen.X86.Mod64

end

end

/-! # Private native frames for candidate filters -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FilterStack
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem allocated_scratch {base : Addr} {size bytes : Nat} {s : State} (S : Scr s base size)
    (fit : bytes + 20 ≤ (s.gpr .esp).toNat)
    (separate : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + size + bytes + 20 ≤ (s.gpr .esp).toNat) :
    Scr (allocFrame bytes s) base size := by
  refine ⟨?_, List.mem_cons_of_mem _ S.wr, S.nowrap, ?_⟩
  · rw [allocFrame_gpr _ _ (by decide)]; exact S.edi
  · change 20 ≤ (s.gpr .esp - BitVec.ofNat 32 bytes).toNat ∧
      ((s.gpr .esp - BitVec.ofNat 32 bytes).toNat ≤ base.toNat ∨
        base.toNat + size + 20 ≤ (s.gpr .esp - BitVec.ofNat 32 bytes).toNat)
    rw [sub_toNat (by omega_using [fit])]
    rcases separate with h | h <;> constructor <;> omega_arith

theorem allocated_workspace {s : State} {bytes : Nat} (fit : bytes ≤ (s.gpr .esp).toNat) :
    Ws (allocFrame bytes s) ((s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64) bytes := by
  refine ⟨List.mem_cons_self, ?_⟩
  rw [BitVec.toNat_setWidth, sub_toNat fit, Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega_using [])]
  have := (s.gpr .esp).isLt
  omega_using [fit]

theorem allocated_context {s : State} (fit : 20 ≤ (s.gpr .esp).toNat) :
    Sieve.StackContext (s.gpr .esp - 20#32) (allocFrame 20 s) :=
  ⟨allocated_workspace fit, allocFrame_esp _ _⟩

theorem allocated_apart {base : Addr} {size bytes : Nat} {s : State}
    (fit : bytes ≤ (s.gpr .esp).toNat) (nowrap : base.toNat + size ≤ 2 ^ 32)
    (separate : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + size + bytes ≤ (s.gpr .esp).toNat) :
    (⟨base, size⟩ : Region).Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ := by
  have natEq : ((s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64).toNat = (s.gpr .esp).toNat - bytes := by
    rw [BitVec.toNat_setWidth, sub_toNat fit, Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega_using [])]
  rcases separate with h | h
  · apply Region.Disjoint.symm
    apply Offset.disjoint_of_le
    · change ((s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64).toNat + bytes ≤ base.toNat
      rw [natEq]; omega_using [fit, h]
    · exact Nat.le_trans nowrap (by decide)
  · apply Offset.disjoint_of_le
    · change base.toNat + size ≤ ((s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64).toNat
      rw [natEq]; omega_using [h]
    · change ((s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64).toNat + bytes ≤ 2 ^ 64
      rw [natEq]; have := (s.gpr .esp).isLt; omega_using [fit]

theorem freed_keeps {s t : State} {bytes : Nat} {rs : List Reg}
    (K : Keeps rs (allocFrame bytes s) t) (sp : .esp ∉ rs) : Keeps rs s (freed bytes t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r mem
    by_cases h : r = .esp
    · subst r
      rw [freed_esp, K.1 .esp sp, allocFrame_esp, BitVec.sub_add_cancel]
    · rw [freed_gpr _ _ h, K.1 r mem, allocFrame_gpr _ _ h]
  · rw [freed_rd, K.2.1, allocFrame_rd]
  · rw [freed_wr, K.2.2, allocFrame_wr]; rfl

end VG.Proof.RsaKeyGen.X86.FilterStack
