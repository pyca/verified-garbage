module

import VerifiedGarbage.Proof.Dsa.X86.PowCorrect
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

theorem body_noSp (n e : Nat) : NoSp (body n e) := NoSp.of_all (by
  rw [Code.allInstrs_eq]
  simp only [body, core, contextSetup, exponentiate, exponentStep, exponentBody,
    exponentProduct, instrs, List.all_append]
  rfl)

theorem body_spSafe (n e : Nat) : (body n e).allInstrs (fun i => !isa.writesSp i) = true := by
  rw [Code.allInstrs_eq]
  simp only [body, core, contextSetup, exponentiate, exponentStep, exponentBody,
    exponentProduct, instrs, List.all_append]
  rfl

theorem body_stackUse (n e : Nat) : stackUse (body n e) = 0 := by rfl

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
