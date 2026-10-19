module

public import VerifiedGarbage.Proof.Mont.X86.MulAt
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
import VerifiedGarbage.Proof.Framework.Omega

/-! # What the callable multiplication's contract gives on entry

`MulABI n s`: the facts of `mulContract (ctxLayout n)`'s precondition, as
`sig_pre` states them; the arguments read from the stack; the working space
as `Scr` needs it once `edi` holds its base (`MulABI.scr`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Dynamic

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Mont VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Spec.Rsa.MontMulAt

/-- The working space, from the first argument. -/
abbrev wsOf (s : State) : Addr := (arg s 0).setWidth 64

theorem contextBytes_div (n : Nat) : contextBytes n / 8 * 8 = contextBytes n := by
  simp only [contextBytes, slot, stride]; omega

structure MulABI (n : Nat) (s : State) : Prop where
  stackLow : 20 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 16 ≤ 2 ^ 32
  rd : s.rd = [⟨argAddr s 0, 16⟩]
  wr : s.wr = [⟨wsOf s, contextBytes n / 8 * 8⟩]
  argScratch : (⟨wsOf s, contextBytes n / 8 * 8⟩ : Region).Disjoint ⟨argAddr s 0, 16⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨wsOf s, contextBytes n / 8 * 8⟩
  retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 16⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 20#64, 20⟩ : Region).Disjoint ⟨wsOf s, contextBytes n / 8 * 8⟩
  belowArgs : (⟨(s.gpr .esp).setWidth 64 - 20#64, 20⟩ : Region).Disjoint ⟨argAddr s 0, 16⟩
  bound : (arg s 0).toNat + contextBytes n / 8 * 8 ≤ 2 ^ 32
  o_le : (arg s 1).toNat + 8 * n ≤ 8 * (contextBytes n / 8)
  a_le : (arg s 2).toNat + 8 * n ≤ 8 * (contextBytes n / 8)
  b_le : (arg s 3).toNat + 8 * n ≤ 8 * (contextBytes n / 8)
  o_scr : Apart (arg s 1).toNat (8 * n) (slot n 1, 2 * stride n)
  a_scr : Apart (arg s 2).toNat (8 * n) (slot n 1, 2 * stride n)
  b_scr : Apart (arg s 3).toNat (8 * n) (slot n 1, 2 * stride n)
  o_mod : Apart (arg s 1).toNat (8 * n) (slot n 0, 8 * n)
  o_inv : Apart (arg s 1).toNat (8 * n) (0, 4)
  inv : (numAt s.mem (wsOf s) (slot n 0) (8 * n) * numAt s.mem (wsOf s) 0 4 + 1) % 2 ^ 32 = 0
  bLt : numAt s.mem (wsOf s) (arg s 3).toNat (8 * n) < numAt s.mem (wsOf s) (slot n 0) (8 * n)

theorem mulAbi_of {n : Nat} {s : State} (h : (mulContract (ctxLayout n) abi 20).pre s) : MulABI n s := by
  sig_pre [mulContract, sig, ctxLayout, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

theorem numAt_eq8 (m : Mem) (base : Addr) (d n : Nat) :
    numAt m base d (8 * n) = wordsVal m base d n := read_eq_wordsVal m base n d

theorem numAt_eq4 (m : Mem) (base : Addr) (d : Nat) : numAt m base d 4 = w32 m base d := by
  simp only [numAt, w32, off]; rfl

/-- The `i`-th argument, read from the stack. -/
theorem MulABI.readArg {n : Nat} {s : State} (A : MulABI n s) {i : Nat} (hi : i < 4) :
    readSrc s (.mem (at_ .esp (4 + 4 * i))) = some (arg s i) := by
  have hb := A.stackBound
  show s.load32 (argAddr s i) = some (arg s i)
  rw [State.load32, ite_eq_left_iff.mpr fun h => absurd ?_ h]
  · rfl
  rw [A.rd]
  refine ⟨_, List.mem_append_left _ (List.mem_singleton_self _), ?_⟩
  simp only [argAddr]
  rw [show (4 : Nat) + 4 * i = 4 + 4 * i from rfl]
  have e : (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 =
      (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 + BitVec.ofNat 64 (4 * i) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e]
  exact Offset.contains_base _ (by omega) (by omega)

theorem MulABI.size {n : Nat} {s : State} (_ : MulABI n s) : contextBytes n / 8 * 8 = contextBytes n :=
  contextBytes_div n

/-- The working space lies below `2³²`. -/
theorem MulABI.nowrap {n : Nat} {s : State} (A : MulABI n s) : (wsOf s).toNat + contextBytes n ≤ 2 ^ 32 := by
  have := A.bound
  rw [contextBytes_div] at this
  simpa only [wsOf, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans (arg s 0).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using this

theorem MulABI.stk {n : Nat} {s : State} (A : MulABI n s) : StkOk (s.gpr .esp) (wsOf s) (contextBytes n) := by
  have B := A.belowScratch
  rw [contextBytes_div] at B
  exact VG.Proof.Weierstrass.X86.stkOk_of (Nat.le_refl 20) A.stackLow A.nowrap
    (by simp only [contextBytes, slot, stride]; omega) B

/-- A byte apart from the working space lies past it, in offsets from its base. -/
theorem ofs_far {base : Addr} {size : Nat} {x : Addr}
    (h : ¬ (⟨base, size⟩ : Region).Contains x 1) : size ≤ ofs base x := by
  simp only [Region.Contains, ofs] at h ⊢
  omega

/-- The arguments lie past the working space, in offsets from its base. -/
theorem MulABI.argFar {n : Nat} {s : State} (A : MulABI n s) {i : Nat} (hi : i < 4) :
    ArgFar s (wsOf s) (contextBytes n) (at_ .esp (4 + 4 * i)) := by
  intro j hj
  have hb := A.stackBound
  refine ofs_far fun hc => A.argScratch _ (by rw [contextBytes_div]; exact hc) ?_
  simp only [Region.Contains, argAddr, State.ea, at_]
  have e : (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 + BitVec.ofNat 64 j -
      (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = BitVec.ofNat 64 (4 * i + j) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  rw [e, BitVec.toNat_ofNat]
  omega

end VG.Proof.Mont.X86.Dynamic
