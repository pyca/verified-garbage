module

import VerifiedGarbage.Proof.Dsa.X86.PowCorrect
import VerifiedGarbage.Proof.Dsa.X86.PowMul
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.X86.Pow
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86.PowBody
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.TCB.X86.Isa

/-! # Calling shared DSA exponentiation with an explicit stack frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Pow
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow

theorem nosp_seq {a b : Prog isa} (A : NoSp a) (B : NoSp b) : NoSp (.seq a b) := fun i hi =>
  (List.mem_append.mp hi).elim (A i) (B i)

theorem squarings_noSp (n : Nat) : ∀ k, NoSp (squarings n k)
  | 0 => NoSp.of_all rfl
  | k + 1 => nosp_seq (squarings_noSp n k) (mul_noSp n 4 4 4)

theorem body_noSp (n e : Nat) : NoSp (body n e) :=
  nosp_seq (NoSp.of_all rfl) <|
  nosp_seq (nosp_seq (nosp_seq (NoSp.of_all rfl) (squarings_noSp n 6)) <|
    nosp_seq (nosp_seq (NoSp.of_all rfl) (nosp_seq (mul_noSp n 6 4 7) (mul_noSp n 5 5 4))) <|
    nosp_seq (NoSp.of_all rfl) <|
    nosp_seq (nosp_seq (NoSp.of_all rfl) <| nosp_seq (mul_noSp n 7 6 5) <| nosp_seq (NoSp.of_all rfl) <|
      nosp_seq (mul_noSp n 5 5 5) <| nosp_seq (NoSp.of_all rfl) (NoSp.of_all rfl)) <|
    nosp_seq (NoSp.of_all rfl) (mul_noSp n 6 6 7)) <|
  NoSp.of_all rfl

theorem body_allNoSp (n e : Nat) : (body n e).allInstrs (fun i => !VG.X86.Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  rw [body_noSp n e i hi]
  rfl

theorem body_spSafe (n e : Nat) : (body n e).allInstrs (fun i => !isa.writesSp i) = true := by
  have e' : (fun i : Instr => !isa.writesSp i) = fun i => !VG.X86.Taint.clobbers i .esp := by
    funext i; cases i <;> rfl
  rw [e']
  exact body_allNoSp n e

theorem squarings_stackUse (n : Nat) : ∀ k, stackUse (squarings n k) ≤ 96
  | 0 => by simp [squarings, stackUse]
  | k + 1 => by
    rw [show squarings n (k + 1) = .seq (squarings n k) (mul n 4 4 4) from rfl]
    simp only [stackUse, mul_stackUse]
    have := squarings_stackUse n k
    omega

theorem body_stackUse (n e : Nat) : stackUse (body n e) ≤ 96 := by
  have := squarings_stackUse n 6
  have h₁ : stackUse (contextSeed n (65 * n)) = 0 := rfl
  have h₂ : stackUse (one n (slot n 7)) = 0 := rfl
  have h₃ : stackUse (selectProduct (contextMod n) (slot n 6) (slot n 7) 4) = 0 := rfl
  have h₄ : stackUse (shiftDown e (slot n 8)) = 0 := rfl
  simp only [body, core, setup, encode, step, finish, stackUse, mul_stackUse, h₁, h₂, h₃, h₄]
  omega

theorem zone_ofs {sp : BitVec 32} {base : Addr} {size : Nat}
    (H : Room sp base size) (hn : base.toNat + size ≤ 2 ^ 32)
    {x : Addr} (hx : (below sp 12).Contains x 1) : size ≤ ofs base x := by
  obtain ⟨h32, hz⟩ := H
  have hsp := sp.isLt
  simp only [Region.Contains] at hx
  simp only [ofs]
  have e : ((sp - BitVec.ofNat 32 12).setWidth 64).toNat = sp.toNat - 12 := by
    rw [BitVec.toNat_setWidth, VG.X86.sub_toNat (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  generalize ((sp - BitVec.ofNat 32 12).setWidth 64) = z at hx e
  bv_omega

theorem zone_ofs' {sp : BitVec 32} {base : Addr} {size k : Nat}
    (H : Room sp base size) (hn : base.toNat + size ≤ 2 ^ 32) (hk : k ≤ 108)
    {x : Addr} (hx : (below sp k).Contains x 1) : size ≤ ofs base x := by
  obtain ⟨h32, hz⟩ := H
  have hsp := sp.isLt
  simp only [Region.Contains] at hx
  simp only [ofs]
  have e : ((sp - BitVec.ofNat 32 k).setWidth 64).toNat = sp.toNat - k := by
    rw [BitVec.toNat_setWidth, VG.X86.sub_toNat (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  generalize ((sp - BitVec.ofNat 32 k).setWidth 64) = z at hx e
  bv_omega

theorem frame_val32 {sp : BitVec 32} {base : Addr} {size : Nat}
    (H : Room sp base size) (hn : base.toNat + size ≤ 2 ^ 32)
    {m m' : Mem} (F : Frame [below sp 12] m m') {d k : Nat} (hd : d + 4 * k ≤ size) :
    val32 m' base d k = val32 m base d k := by
  refine val32_congr fun j hj => congrArg BitVec.toNat (Mem.readW_congr fun i hi => F _ fun r hr hc => ?_)
  rw [List.mem_singleton.mp hr] at hc
  have := zone_ofs H hn hc
  rw [ofs_off base (by omega)] at this
  omega


end VG.Proof.Dsa.X86.Pow
