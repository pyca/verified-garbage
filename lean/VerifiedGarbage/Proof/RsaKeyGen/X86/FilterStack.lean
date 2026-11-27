module

public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
public import VerifiedGarbage.TCB.X86.State
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.MemoryFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Shift
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Subtract
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Bignum.Math

/-! ### `RsaKeyGen.X86.Mod64`, which this module and modules that import it used -/

section

/-! # A native paired-word bit reduction computes exactly the modular recurrence -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Mod64Select.lean`, which only this module imported.
section

/-! # One mask selects both native words of the reduced remainder -/

section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem select_ok (s : State) (choose : Bool)
    (mask : s.gpr .ebp = if choose then BitVec.allOnes 32 else 0) :
    WP isa (.block select) s fun t =>
      t.gpr .ecx = (if choose then s.gpr .eax else s.gpr .ecx) ∧
      t.gpr .ebx = (if choose then s.gpr .edx else s.gpr .ebx) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebx] s t := by
  unfold select
  refine wp_xor fun a A => wp_and fun b B => wp_xor fun c C =>
    wp_xor fun d D => wp_and fun e E => wp_xor fun t T => WP.block_nil ?_
  have Kc : Keeps [.eax, .ecx] s c := ((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps
  refine ⟨?_, ?_, ?_, (((Kc.mono (by decide)).widen D.keeps).widen E.keeps).widen T.keeps⟩
  · rw [T.other .ecx (by decide), E.other .ecx (by decide), D.other .ecx (by decide), C.gpr,
      B.other .ecx (by decide), A.other .ecx (by decide), B.gpr, A.gpr,
      A.other .ebp (by decide), mask, select_val]
  · rw [T.gpr, E.other .ebx (by decide), D.other .ebx (by decide), Kc.1 .ebx (by decide),
      E.gpr, D.gpr, Kc.1 .edx (by decide), Kc.1 .ebx (by decide),
      D.other .ebp (by decide), Kc.1 .ebp (by decide), mask, select_val]
  · rw [T.mem, E.mem, D.mem, C.mem, B.mem, A.mem]

end VG.Proof.RsaKeyGen.X86.Mod64
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Mod64Math.lean`, which only this module imported.
section

/-! # Carry, borrow and masked selection reduce the doubled remainder exactly once -/

section
namespace VG.Proof.RsaKeyGen.X86.Mod64

def choose (carry borrow : Bool) : Bool := decide (borrow.toNat ≤ carry.toNat)

theorem pair_lt (low high : BitVec 32) : pair low high < 2 ^ 64 := by
  unfold pair
  have := low.isLt
  have := high.isLt
  omega

theorem carry_le_borrow {low difference exponent : Nat} {carry borrow : Bool}
    (exponentBound : exponent < 2 ^ 64)
    (sumBound : low + 2 ^ 64 * carry.toNat < 2 * exponent)
    (sub : difference + exponent = low + 2 ^ 64 * borrow.toNat) : carry.toNat ≤ borrow.toNat := by
  cases carry <;> cases borrow <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at * <;> omega

theorem mask_value (carry borrow : Bool) (bound : carry.toNat ≤ borrow.toNat) :
    ((if carry then BitVec.allOnes 32 else 0) + 0#32 + (BitVec.ofBool borrow).setWidth 32) - 1 =
      if choose carry borrow then BitVec.allOnes 32 else 0 := by
  cases carry <;> cases borrow <;> first | rfl | (simp only [Bool.toNat_false, Bool.toNat_true] at bound; omega)

theorem selected_value {low difference exponent : Nat} {carry borrow : Bool}
    (exponentBound : exponent < 2 ^ 64) (differenceBound : difference < 2 ^ 64)
    (lowBound : low < 2 ^ 64) (sumBound : low + 2 ^ 64 * carry.toNat < 2 * exponent)
    (sub : difference + exponent = low + 2 ^ 64 * borrow.toNat) :
    (if choose carry borrow then difference else low) = (low + 2 ^ 64 * carry.toNat) % exponent := by
  have H := VG.Proof.Bignum.csub_result (Tw1 := 0) exponentBound differenceBound (Bool.toNat_le borrow)
    lowBound (by simpa only [Nat.mul_zero, Nat.add_zero] using sumBound) sub
  simp only [Nat.mul_zero, Nat.add_zero] at H
  by_cases accept : borrow.toNat ≤ carry.toNat
  · rw [choose, decide_eq_true accept]
    rw [ite_eq_right (by omega : ¬ carry.toNat < borrow.toNat)] at H
    exact H
  · rw [choose, decide_eq_false accept]
    rw [ite_eq_left (by omega : carry.toNat < borrow.toNat)] at H
    exact H

end VG.Proof.RsaKeyGen.X86.Mod64
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

def exponentValue (m : Mem) (base : Addr) (offset : Nat) : Nat :=
  pair (m.readW (off base offset) 32) (m.readW (off base (offset + 4)) 32)

theorem bit_ok {s : State} {base : Addr} {size exponent : Nat}
    (scratch : Scr s base size) (fit : exponent + 8 ≤ size)
    (remainder : pair (s.gpr .ecx) (s.gpr .ebx) < exponentValue s.mem base exponent) :
    WP isa (.block (bit exponent)) s fun t =>
      pair (t.gpr .ecx) (t.gpr .ebx) =
        (2 * pair (s.gpr .ecx) (s.gpr .ebx) + (incoming (s.gpr .esi)).toNat) % exponentValue s.mem base exponent ∧
      pair (t.gpr .ecx) (t.gpr .ebx) < exponentValue s.mem base exponent ∧
      t.gpr .esi = s.gpr .esi + s.gpr .esi ∧ t.mem = s.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold bit
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (shift_ok s) fun u ⟨shiftedWord, ⟨carry, mask, sum⟩, Mu, Ku⟩ => ?_)
  refine WP.block_append (WP.mono (subtract_ok (scratch.of_keeps Ku (by decide)) fit)
    fun v ⟨⟨borrow, choiceMask, sub⟩, Mv, Kv⟩ => ?_)
  rw [Mu] at sub
  have exponentBound : exponentValue s.mem base exponent < 2 ^ 64 := pair_lt ..
  have sumBound : pair (u.gpr .ecx) (u.gpr .ebx) + 2 ^ 64 * carry.toNat < 2 * exponentValue s.mem base exponent := by
    have := Bool.toNat_le (incoming (s.gpr .esi))
    omega_using [remainder, sum, this]
  have cb : carry.toNat ≤ borrow.toNat := carry_le_borrow exponentBound sumBound sub
  have chosen : v.gpr .ebp = if choose carry borrow then BitVec.allOnes 32 else 0 := by
    rw [choiceMask, mask]
    exact mask_value carry borrow cb
  refine WP.mono (select_ok v (choose carry borrow) chosen) fun t ⟨low, high, Mt, Kt⟩ => ?_
  have original : pair (v.gpr .ecx) (v.gpr .ebx) = pair (u.gpr .ecx) (u.gpr .ebx) := by
    rw [Kv.1 .ecx (by decide), Kv.1 .ebx (by decide)]
  have selected : pair (t.gpr .ecx) (t.gpr .ebx) =
      if choose carry borrow then pair (v.gpr .eax) (v.gpr .edx) else pair (u.gpr .ecx) (u.gpr .ebx) := by
    cases C : choose carry borrow <;> rw [C] at low high <;>
      simp only [Bool.false_eq_true, ↓reduceIte] at low high ⊢
    · rw [low, high, original]
    · rw [low, high]
  have value := selected.trans (selected_value exponentBound (pair_lt ..) (pair_lt ..) sumBound sub)
  rw [sum] at value
  have positive : 0 < exponentValue s.mem base exponent := by omega_using [remainder]
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t :=
    ((Ku.mono (by decide)).widen Kv).widen Kt
  refine ⟨value, ?_, ?_, Mt.trans (Mv.trans Mu), K⟩
  · rw [value]
    exact Nat.mod_lt _ positive
  · rw [Kt.1 .esi (by decide), Kv.1 .esi (by decide), shiftedWord]

end VG.Proof.RsaKeyGen.X86.Mod64

end

end

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
