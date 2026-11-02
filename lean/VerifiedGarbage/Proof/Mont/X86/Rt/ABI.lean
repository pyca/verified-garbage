module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Zero
public import VerifiedGarbage.Proof.Mont.X86.ArgWs
public import VerifiedGarbage.Proof.Mont.X86.ArgFar
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # What `vg_rsa_mont_mul_at`'s contract gives on entry

`RtABI s`: the facts of `mulContract abi 0`'s precondition, as `sig_pre`
states them; from them, the working space (`Ws`), the arguments on the stack
(`Args`, `ArgVals`) and the layout (`Lay`) of the proofs.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Rt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.MontMul (Apart numAt scratchBytes)
open VG.Proof.Mont.X86.Dynamic (ArgFar ofs_far)

/-- The working space, from the first argument, and its bytes. -/
abbrev wsOf (s : State) : Addr := (arg s 0).setWidth 64
abbrev lenOf (s : State) : Nat := (arg s 1).toNat * 8

structure RtABI (s : State) : Prop where
  stackBound : (s.gpr .esp).toNat + 4 + 36 ≤ 2 ^ 32
  rd : s.rd = [⟨argAddr s 0, 36⟩]
  wr : s.wr = [⟨wsOf s, lenOf s⟩]
  argScratch : (⟨wsOf s, lenOf s⟩ : Region).Disjoint ⟨argAddr s 0, 36⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨wsOf s, lenOf s⟩
  retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 36⟩
  bound : (arg s 0).toNat + lenOf s ≤ 2 ^ 32
  pos : 0 < (arg s 2).toNat
  mo_le : (arg s 3).toNat + 8 * (arg s 2).toNat ≤ 8 * (arg s 1).toNat
  inv_le : (arg s 4).toNat + 4 ≤ 8 * (arg s 1).toNat
  s_le : (arg s 5).toNat + scratchBytes (arg s 2).toNat ≤ 8 * (arg s 1).toNat
  o_le : (arg s 6).toNat + 8 * (arg s 2).toNat ≤ 8 * (arg s 1).toNat
  a_le : (arg s 7).toNat + 8 * (arg s 2).toNat ≤ 8 * (arg s 1).toNat
  b_le : (arg s 8).toNat + 8 * (arg s 2).toNat ≤ 8 * (arg s 1).toNat
  smo : Apart (arg s 3).toNat (8 * (arg s 2).toNat) ((arg s 5).toNat, scratchBytes (arg s 2).toNat)
  sinv : Apart (arg s 4).toNat 4 ((arg s 5).toNat, scratchBytes (arg s 2).toNat)
  so : Apart (arg s 6).toNat (8 * (arg s 2).toNat) ((arg s 5).toNat, scratchBytes (arg s 2).toNat)
  sa : Apart (arg s 7).toNat (8 * (arg s 2).toNat) ((arg s 5).toNat, scratchBytes (arg s 2).toNat)
  sb : Apart (arg s 8).toNat (8 * (arg s 2).toNat) ((arg s 5).toNat, scratchBytes (arg s 2).toNat)
  omo : Apart (arg s 6).toNat (8 * (arg s 2).toNat) ((arg s 3).toNat, 8 * (arg s 2).toNat)
  oinv : Apart (arg s 6).toNat (8 * (arg s 2).toNat) ((arg s 4).toNat, 4)
  inv : (numAt s.mem (wsOf s) (arg s 3).toNat (8 * (arg s 2).toNat) *
    numAt s.mem (wsOf s) (arg s 4).toNat 4 + 1) % 2 ^ 32 = 0
  bLt : numAt s.mem (wsOf s) (arg s 8).toNat (8 * (arg s 2).toNat) <
    numAt s.mem (wsOf s) (arg s 3).toNat (8 * (arg s 2).toNat)

theorem rtAbi_of {s : State} (h : (Proof.Rsa.MontMul.mulContract abi 0).pre s) : RtABI s := by
  sig_pre [Proof.Rsa.MontMul.mulContract, Proof.Rsa.MontMul.sig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

theorem RtABI.ws_toNat {s : State} (_ : RtABI s) : (wsOf s).toNat = (arg s 0).toNat := by
  simp only [wsOf, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans (arg s 0).isLt (by decide : 2 ^ 32 < 2 ^ 64))]

theorem RtABI.ws {s : State} (A : RtABI s) : Ws s (wsOf s) (lenOf s) :=
  ⟨by rw [A.wr]; exact List.mem_singleton_self _, by rw [A.ws_toNat]; exact A.bound⟩

/-- The `i`-th argument, read from the stack. -/
theorem RtABI.readArg {s : State} (A : RtABI s) {i : Nat} (hi : i < 9) :
    readSrc s (.mem (Rt.arg i)) = some (arg s i) := by
  have hb := A.stackBound
  show s.load32 (argAddr s i) = some (arg s i)
  rw [State.load32, ite_eq_left_iff.mpr fun h => absurd ?_ h]
  · rfl
  rw [A.rd]
  refine ⟨_, List.mem_append_left _ (List.mem_singleton_self _), ?_⟩
  simp only [argAddr]
  have e : (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 =
      (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 + BitVec.ofNat 64 (4 * i) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e]
  exact Offset.contains_base _ (by omega) (by omega)

/-- The arguments lie past the working space, in offsets from its base. -/
theorem RtABI.argFar {s : State} (A : RtABI s) {i : Nat} (hi : i < 9) :
    ArgFar s (wsOf s) (lenOf s) (Rt.arg i) := by
  intro j hj
  have hb := A.stackBound
  refine ofs_far fun hc => A.argScratch _ hc ?_
  simp only [Region.Contains, argAddr, State.ea, Rt.arg, at_]
  have e : (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 + BitVec.ofNat 64 j -
      (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = BitVec.ofNat 64 (4 * i + j) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  rw [e, BitVec.toNat_ofNat]
  omega

theorem RtABI.args {s : State} (A : RtABI s) : Args s (wsOf s) (lenOf s) (arg s) :=
  ⟨fun _ hi => A.readArg hi, fun _ hi => A.argFar hi⟩

/-- The widths and offsets, `N = 2 n` 32-bit words a number. -/
abbrev nOf (s : State) : Nat := 2 * (arg s 2).toNat

theorem RtABI.vals {s : State} (A : RtABI s) :
    ArgVals (arg s) (wsOf s) (nOf s) (arg s 5).toNat (arg s 3).toNat (arg s 4).toNat (arg s 6).toNat
      (arg s 7).toNat (arg s 8).toNat :=
  ⟨A.ws_toNat.symm, by simp only [nOf]; omega, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem RtABI.lay {s : State} (A : RtABI s) :
    Lay (lenOf s) (nOf s) (arg s 5).toNat (arg s 3).toNat (arg s 4).toNat (arg s 7).toNat (arg s 8).toNat := by
  have := A.s_le; have := A.mo_le; have := A.inv_le; have := A.a_le; have := A.b_le
  have := A.smo; have := A.sinv; have := A.sa; have := A.sb
  simp only [scratchBytes, Apart] at *
  constructor <;> simp only [nOf, lenOf] <;> omega

theorem RtABI.n32 {s : State} (A : RtABI s) : 4 * nOf s < 2 ^ 32 := by
  have := A.s_le; have := A.bound
  simp only [scratchBytes, nOf, lenOf] at *
  omega

end VG.Proof.Mont.X86.Rt
