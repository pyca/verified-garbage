module

public import VerifiedGarbage.Proof.Rsa.X86.KcABI
public import VerifiedGarbage.Impl.Rsa.X86.KeyCheckRt

import VerifiedGarbage.Proof.Rsa.X86.KcOperationTiming
import VerifiedGarbage.Proof.Rsa.X86.KcLoads
import VerifiedGarbage.Proof.Rsa.X86.KcResult
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Rsa.X86.KcBounds
import VerifiedGarbage.Proof.Bignum.X86.PublicReturn
import VerifiedGarbage.Proof.Rsa.X86.KcInstalled
import VerifiedGarbage.Proof.Rsa.X86.KcResources
import VerifiedGarbage.Proof.Rsa.X86.KcBodyPublic
import VerifiedGarbage.Proof.Bignum.X86.PublicSave
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Proof.Bignum.Octets
/-! # Complete i686 certificates for RSA key validation -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/KcReturn.lean`, which only this module imported.
section

/-! # Key validation preserves saved registers and the return address -/

section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum hiding off Outside
open VG.Proof.Bignum.X86 VG.Impl.Bignum.X86
open VG.Impl.Rsa.X86.KeyCheck

theorem body_saved {g : CallGeometry} {s : State} {m m' : Mem} {regs : Reg → BitVec 32}
    (h : Inputs g s) (f : Outside g.base 16 (g.size - 16) m m')
    (saved : Saved m (off g.base) regs PublicFn.savedRegisters) :
    Saved m' (off g.base) regs PublicFn.savedRegisters := by
  have low : 16 ≤ g.size := by have := h.ws.hdr_le; unfold VG.Impl.Rsa.X86.Keys.hdr at this; omega
  have high : g.size ≤ 2 ^ 64 := by have := h.ws.workspace.nowrap; omega
  have frame := outside_frame f (by omega)
  intro p hp
  have bound : p.2 + 4 ≤ 16 := by
    simp only [PublicFn.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  refine (frame.readW (r := ⟨g.base, 16⟩) (Offset.contains_base _ bound (by omega)) ?_ (by decide)).trans (saved p hp)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact Offset.base_disjoint g.base (Nat.le_refl 16) (by omega)

theorem operation_ok {full : Bool} {s : State} (a : ABI full s) :
    WP isa (VG.Impl.Rsa.X86.KeyCheckRt.code full) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (validity full (arg s 1).toNat (numbers (caller full s) s.mem)).toNat ∧
      abiPreserved s t := by
  have low : 16 ≤ (caller full s).size := by have := a.used; omega
  have high : (caller full s).size ≤ 2 ^ 64 := by have := a.scratchBound; omega
  unfold VG.Impl.Rsa.X86.KeyCheckRt.code
  refine WP.seq (WP.mono (installed_ok a) fun u ⟨inputs, saved, ku, ou⟩ => ?_)
  refine WP.seq (WP.mono (body_ok inputs a.lengths_ok (a.numberBounds u.mem))
    fun v ⟨⟨iv, value, frame⟩, kv⟩ => ?_)
  have saveV := body_saved inputs frame saved
  have whole : Frame [⟨(caller full s).base, (caller full s).size⟩] s.mem v.mem := by
    have f := outside_frame (ou.trans (frame.mono (by omega) (by omega))) (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using f
  have ret : v.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 :=
    whole.readW (Region.contains_self _ 4) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact a.retApart) (by decide)
  refine WP.mono (entryRestore_ok iv.ws.workspace low saveV) fun t restored => ?_
  refine ⟨?_, publicRestored_abi restored ((kv.1 _ (by decide)).trans (ku.1 _ (by decide))) ret⟩
  rw [numbers_entry a ou] at value
  rw [restored.other .eax (by decide)]
  exact value
end VG.Proof.Rsa.X86.KeyCheck
end

end

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/KcCorrect.lean`, which only this module imported.
section

/-! # Both i686 key-check operations satisfy their existing shared contracts -/

section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Dsa.X86

private theorem bool_result (b : Bool) : BitVec.ofNat 32 b.toNat = (if b then 1 else 0) := by
  cases b <;> rfl

theorem correct (full : Bool) (s : State) (h : (contract full).pre s) :
    ∃ trace t, Exec isa (VG.Impl.Rsa.X86.KeyCheckRt.code full) s trace t ∧ abiPreserved s t ∧
      (contract full).post s t := by
  have a := abi_of h
  obtain ⟨trace, t, run, value, preserved⟩ := operation_ok a
  refine ⟨trace, t, run, preserved, ?_⟩
  cases full
  · change (Spec.Rsa.checkCrtKeyContract abi 20).post s t
    sig_post [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argSlots, argVal, argBytes]
    rw [BitVec.setWidth_append_eq_right]
    simp only [validity, numbers, caller, inputBytes, CallGeometry.buffer, Bool.false_eq_true, ite_false] at value
    have dp : (arg s 9).toNat = (arg s 5).toNat := a.dpLen
    have dq : (arg s 11).toNat = (arg s 7).toNat := a.dqLen
    have qi : (arg s 13).toNat = (arg s 5).toNat := a.qiLen
    simp only [Nat.reduceAdd, Nat.reduceMul] at value
    rw [dp, dq, qi] at value
    unfold Spec.Rsa.checkCrtKey
    rw [value]
    rw [VG.Proof.Bignum.bytesAt_length]
    exact bool_result _
  · change (Spec.Rsa.checkKeyContract abi 20).post s t
    sig_post [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argSlots, argVal, argBytes]
    rw [BitVec.setWidth_append_eq_right]
    simp only [validity, numbers, caller, inputBytes, CallGeometry.buffer, ite_true] at value
    have dp : (arg s 11).toNat = (arg s 7).toNat := a.dpLen
    have dq : (arg s 13).toNat = (arg s 9).toNat := a.dqLen
    have qi : (arg s 15).toNat = (arg s 7).toNat := a.qiLen
    simp only [Nat.reduceAdd, Nat.reduceMul] at value
    rw [dp, dq, qi] at value
    unfold Spec.Rsa.checkKey
    rw [value]
    rw [VG.Proof.Bignum.bytesAt_length]
    exact bool_result _
end VG.Proof.Rsa.X86.KeyCheck
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86
open VG.Impl.Rsa.X86.KeyCheck
open VG.Impl.Rsa.X86.KeyCheckRt (code)

def crtState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16
    else if a = 0x20008 then 64
    else if a = 0x2000d then 32
    else if a = 0x20010 then 3
    else if a = 0x20015 then 48
    else if a = 0x20018 then 32
    else if a = 0x2001d then 64
    else if a = 0x20020 then 32
    else if a = 0x20025 then 80
    else if a = 0x20028 then 32
    else if a = 0x2002d then 96
    else if a = 0x20030 then 32
    else if a = 0x20035 then 112
    else if a = 0x20038 then 32
    else if a = 0x2003e then 1
    else if a = 0x20040 then 32
    else if a = 0x20041 then 4 else 0
  rd := [⟨4096, 64⟩, ⟨8192, 3⟩, ⟨12288, 32⟩, ⟨16384, 32⟩, ⟨20480, 32⟩, ⟨24576, 32⟩, ⟨28672, 32⟩]
  wr := [⟨0x10000, 8448⟩, ⟨0x20004, 64⟩]

theorem crt_satisfiable : ∃ s, (Spec.Rsa.checkCrtKeyContract abi 20).pre s := by
  have a0 : arg crtState 0 = 4096 := by decide
  have a1 : arg crtState 1 = 64 := by decide
  have a2 : arg crtState 2 = 8192 := by decide
  have a3 : arg crtState 3 = 3 := by decide
  have a4 : arg crtState 4 = 12288 := by decide
  have a5 : arg crtState 5 = 32 := by decide
  have a6 : arg crtState 6 = 16384 := by decide
  have a7 : arg crtState 7 = 32 := by decide
  have a8 : arg crtState 8 = 20480 := by decide
  have a9 : arg crtState 9 = 32 := by decide
  have a10 : arg crtState 10 = 24576 := by decide
  have a11 : arg crtState 11 = 32 := by decide
  have a12 : arg crtState 12 = 28672 := by decide
  have a13 : arg crtState 13 = 32 := by decide
  have a14 : arg crtState 14 = 65536 := by decide
  have a15 : arg crtState 15 = 1056 := by decide
  have e : argAddr crtState 0 = 0x20004 := by decide
  have esp : crtState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, e, esp, crtState, Spec.Rsa.lenValid, Spec.Rsa.scratchWords] using crtState

def keyState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16
    else if a = 0x20008 then 64
    else if a = 0x2000d then 32
    else if a = 0x20010 then 3
    else if a = 0x20015 then 48
    else if a = 0x20018 then 64
    else if a = 0x2001d then 64
    else if a = 0x20020 then 32
    else if a = 0x20025 then 80
    else if a = 0x20028 then 32
    else if a = 0x2002d then 96
    else if a = 0x20030 then 32
    else if a = 0x20035 then 112
    else if a = 0x20038 then 32
    else if a = 0x2003d then 128
    else if a = 0x20040 then 32
    else if a = 0x20046 then 1
    else if a = 0x20048 then 32
    else if a = 0x20049 then 4 else 0
  rd := [⟨4096, 64⟩, ⟨8192, 3⟩, ⟨12288, 64⟩, ⟨16384, 32⟩, ⟨20480, 32⟩, ⟨24576, 32⟩, ⟨28672, 32⟩, ⟨32768, 32⟩]
  wr := [⟨0x10000, 8448⟩, ⟨0x20004, 72⟩]

theorem key_satisfiable : ∃ s, (Spec.Rsa.checkKeyContract abi 20).pre s := by
  have a0 : arg keyState 0 = 4096 := by decide
  have a1 : arg keyState 1 = 64 := by decide
  have a2 : arg keyState 2 = 8192 := by decide
  have a3 : arg keyState 3 = 3 := by decide
  have a4 : arg keyState 4 = 12288 := by decide
  have a5 : arg keyState 5 = 64 := by decide
  have a6 : arg keyState 6 = 16384 := by decide
  have a7 : arg keyState 7 = 32 := by decide
  have a8 : arg keyState 8 = 20480 := by decide
  have a9 : arg keyState 9 = 32 := by decide
  have a10 : arg keyState 10 = 24576 := by decide
  have a11 : arg keyState 11 = 32 := by decide
  have a12 : arg keyState 12 = 28672 := by decide
  have a13 : arg keyState 13 = 32 := by decide
  have a14 : arg keyState 14 = 32768 := by decide
  have a15 : arg keyState 15 = 32 := by decide
  have a16 : arg keyState 16 = 65536 := by decide
  have a17 : arg keyState 17 = 1056 := by decide
  have e : argAddr keyState 0 = 0x20004 := by decide
  have esp : keyState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, e, esp, keyState, Spec.Rsa.lenValid, Spec.Rsa.scratchWords] using keyState

theorem satisfiable (full : Bool) : ∃ s, (contract full).pre s := by
  cases full
  · exact crt_satisfiable
  · exact key_satisfiable

theorem verified (full : Bool) : Verified target (code full) (contract full) :=
  ⟨correct full, constantTime full, satisfiable full⟩

end VG.Proof.Rsa.X86.KeyCheck
