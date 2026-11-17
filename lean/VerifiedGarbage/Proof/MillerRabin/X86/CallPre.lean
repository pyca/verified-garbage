module

public import VerifiedGarbage.Proof.MillerRabin.X86.Modulus
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.Compact.Arithmetic
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame

/-! ### `MillerRabin.X86.CallEntry`, which this module and modules that import it used -/

section

/-! # Montgomery's arguments and the disjoint stack of an i686 round -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def mulArgs : List Reg := [.eax, .ecx, .ecx, .edx, .edi]

def mulEntry (g : Geometry) (s : State) : State :=
  (pushed mulArgs s).callEntry.withRegions
    [⟨argAddr (pushed mulArgs s).callEntry 0, 20⟩] [⟨g.W, g.L⟩]

structure MulArguments (g : Geometry) (capacity b : Nat) (s : State) : Prop where
  base : s.gpr .edi = BitVec.ofNat 32 g.W.toNat
  length : s.gpr .edx = BitVec.ofNat 32 capacity
  index : s.gpr .ecx = 6#32
  right : s.gpr .eax = BitVec.ofNat 32 b

theorem mulEntry_arg {g : Geometry} {s : State} {capacity b : Nat}
    (A : MulArguments g capacity b s) (fit : 24 ≤ (s.gpr .esp).toNat) {i : Nat} (index : i < 5) :
    arg (mulEntry g s) i = BitVec.ofNat 32
      (if i = 0 then g.W.toNat else if i = 1 then capacity else if i = 4 then b else 6) := by
  rw [mulEntry, arg_withRegions, callEntry_arg (rs := mulArgs) (s := s) fit (by decide : Reg.esp ∉ mulArgs) index]
  have casesI : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega_using [index]
  rcases casesI with rfl | rfl | rfl | rfl | rfl <;>
    simp only [mulArgs, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
      List.getElem_cons_zero, List.getElem_cons_succ, ↓reduceIte, A.base, A.length, A.index, A.right] <;> rfl

theorem mulEntry_frame {g : Geometry} {s : State}
    (fit : 24 ≤ (s.gpr .esp).toNat) (nowrap : g.W.toNat + g.L ≤ 2 ^ 32)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below (s.gpr .esp) 24)) :
    WorkspaceFrame g [] s.mem (mulEntry g s).mem := by
  have F := callEntry_frame (rs := mulArgs) fit (by decide : Reg.esp ∉ mulArgs)
  intro i index _
  apply F.bytes (R := ⟨g.W, g.L⟩)
  · intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact far
  · have := nowrap
    change g.L ≤ 2 ^ 64
    omega_using [nowrap]
  · exact index

end VG.Proof.MillerRabin.X86

end

end

/-! # The prepared round meets Montgomery's reviewed cdecl contract -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem mulEntry_pre {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    {capacity b c : Nat} (length : g.L = 8 * capacity) (M : Modulus g c s.mem)
    (A : MulArguments g capacity b s) (right : Proof.Rsa.Mont.Operand b)
    (rightLt : val32 s.mem g.W (g.array b) g.words < c)
    (fit : 80 ≤ (s.gpr .esp).toNat)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below (s.gpr .esp) 80)) :
    (Proof.Rsa.Mont.mulContract abi 56).pre (mulEntry g s) := by
  have sa := fun {i} (hi : i < 5) => mulEntry_arg A (by omega_using [fit]) hi
  have capBound : capacity < 2 ^ 32 := by have := C.ws.nowrap; omega
  have ptrBound : g.W.toNat < 2 ^ 32 := by have := C.ws.nowrap; have := v.headerFit; omega_arith
  have bBound : b < 2 ^ 32 := by have := right.1; omega_using [this]
  have far24 := far.sub_right (below_sub (by decide : 24 ≤ 80) fit)
  have F := mulEntry_frame (by omega_using [fit] : 24 ≤ (s.gpr .esp).toNat) C.ws.nowrap far24
  have Mu := M.keep v F (by simp) (by simp)
  have lu := Mu.layout v (by omega_using [length])
  have sp : (mulEntry g s).gpr .esp = s.gpr .esp - 24#32 := by
    change (pushed mulArgs s).callEntry.gpr .esp = _
    exact callEntry_esp' mulArgs s
  have ar : argAddr (mulEntry g s) 0 = (s.gpr .esp - 20#32).setWidth 64 := by
    rw [mulEntry, argAddr_withRegions]
    exact callEntry_argAddr0 mulArgs s
  have rd : (mulEntry g s).rd = [⟨argAddr (mulEntry g s) 0, 20⟩] := by
    rw [mulEntry, State.withRegions_rd, argAddr_withRegions]
  have wr : (mulEntry g s).wr = [⟨g.W, g.L⟩] := rfl
  have sa0 : arg (mulEntry g s) 0 = BitVec.ofNat 32 g.W.toNat := sa (by decide)
  have sa1 : arg (mulEntry g s) 1 = BitVec.ofNat 32 capacity := sa (by decide)
  have sa2 : arg (mulEntry g s) 2 = 6#32 := sa (by decide)
  have sa3 : arg (mulEntry g s) 3 = 6#32 := sa (by decide)
  have sa4 : arg (mulEntry g s) 4 = BitVec.ofNat 32 b := sa (by decide)
  have ptr : (BitVec.ofNat 32 g.W.toNat).setWidth 64 = g.W := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ptrBound]
    exact Nat.mod_eq_of_lt g.W.isLt
  generalize eu : mulEntry g s = u at *
  sig_pre [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sa0, sa1, sa2, sa3, sa4, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt capBound, Nat.mod_eq_of_lt ptrBound, Nat.mod_eq_of_lt bBound,
    ptr, rd, wr, sp, ar, ← length, Nat.mul_comm capacity 8]
  have sp24 : (s.gpr .esp - 24#32).toNat = (s.gpr .esp).toNat - 24 := sub_toNat (by omega_using [fit])
  have nat20 : ((s.gpr .esp - 20#32).setWidth 64).toNat = (s.gpr .esp).toNat - 20 := by
    rw [BitVec.toNat_setWidth, sub_toNat (by omega_using [fit])]
    exact Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega_using [])
  have nat24 : ((s.gpr .esp - 24#32).setWidth 64).toNat = (s.gpr .esp).toNat - 24 := by
    rw [BitVec.toNat_setWidth, sp24]
    exact Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega_using [])
  have saved : (s.gpr .esp - 24#32).setWidth 64 - 56#64 =
      (s.gpr .esp - 80#32).setWidth 64 := by
    rw [← Taint.sub_setWidth (by rw [sp24]; omega_using [fit] : 56 ≤ (s.gpr .esp - 24#32).toNat)]
    congr 1
    rw [BitVec.sub_sub]
    rfl
  have nat40 : ((s.gpr .esp - 80#32).setWidth 64).toNat = (s.gpr .esp).toNat - 80 := by
    rw [BitVec.toNat_setWidth, sub_toNat fit]
    exact Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega_using [])
  have argSub : (⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩ : Region).Sub (below (s.gpr .esp) 80) :=
    below_sub (by decide) fit
  have retSub : (⟨(s.gpr .esp - 24#32).setWidth 64, 4⟩ : Region).Sub (below (s.gpr .esp) 80) :=
    fun x hx => below_sub (by decide : 24 ≤ 80) fit x ((Region.sub_prefix (by decide : 4 ≤ 24)) x hx)
  have saveSub : (⟨(s.gpr .esp - 24#32).setWidth 64 - 56#64, 56⟩ : Region).Sub (below (s.gpr .esp) 80) := by
    rw [saved]
    exact Region.sub_prefix (by decide : 56 ≤ 80)
  have retArgs : (⟨(s.gpr .esp - 24#32).setWidth 64, 4⟩ : Region).Disjoint
      ⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩ :=
    Offset.disjoint_of_le (by simp only [nat24, nat20]; omega_using [fit]) (by simp only [nat20]; have := (s.gpr .esp).isLt; omega_using [])
  have saveArgs : (⟨(s.gpr .esp - 24#32).setWidth 64 - 56#64, 56⟩ : Region).Disjoint
      ⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩ := by
    rw [saved]
    exact Offset.disjoint_of_le (by simp only [nat40, nat20]; omega_using [fit]) (by simp only [nat20]; have := (s.gpr .esp).isLt; omega_using [])
  refine ⟨by rw [sp24]; omega_using [fit], by rw [sp24]; have := (s.gpr .esp).isLt; omega_using [],
    trivial, trivial, far.sub_right argSub, (far.sub_right retSub).symm, retArgs,
    (far.sub_right saveSub).symm, saveArgs, C.ws.nowrap, ?_, by change 6 < 8 ∧ 6 ≠ 2 ∧ 6 ≠ 3; decide,
    by change 6 < 8 ∧ 6 ≠ 2 ∧ 6 ≠ 3; decide, right, ?_, ?_⟩
  · simpa only [length, Nat.mul_div_cancel_left capacity (by decide : 0 < 8)] using lu
  · rw [Mu.width]
    exact Mu.inverse
  · rw [Mu.width, VG.Proof.Mont.X86.Compact.numAt_val32, VG.Proof.Mont.X86.Compact.numAt_val32]
    change val32 u.mem g.W (g.array b) g.words < val32 u.mem g.W (g.array 0) g.words
    rw [Mu.candidate, F.val32 (v.arrayFit (by have := right.1; omega_using [this])) (by simp)]
    exact rightLt

end VG.Proof.MillerRabin.X86
