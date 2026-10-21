module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Constant
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ScalarKey
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

/-! # The public-exponent inverse also needs an LCM of at least two -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aL kOk kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem lAtLeastTwo_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (bit : slot s.mem B kFlag ≤ 1) :
    WP isa lAtLeastTwo s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2] [kOk] s.mem t.mem ∧
      slot t.mem B kOk = (if 2 ≤ num s.mem B n aL ∧ slot s.mem B kFlag = 1 then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have hf : kFlag + 4 ≤ hdr := by decide
  unfold lAtLeastTwo seqs
  refine WP.seq (WP.mono (constant_ok h (by decide) (2 : BitVec 32)) fun u ⟨hu, Ou, constant, Ku⟩ => ?_)
  change num u.mem B n aT1 = 2 at constant
  have L : num u.mem B n aL = num s.mem B n aL := Ou.num (by decide) (by simp) (h.fit64 (by decide))
  refine WP.seq (WP.mono (sub_ok hu (by decide) (by decide) (by decide))
    fun v ⟨hv, Ov, subtract, borrow, Kv⟩ => ?_)
  rw [L, constant] at subtract
  have iffBorrow := VG.Proof.Rsa.borrow_iff subtract (val32_lt _ _ _ _) borrow
  have flag : slot v.mem B kFlag = slot s.mem B kFlag := by
    rw [Ov.slot hf (by simp), Ou.slot hf (by simp)]
  refine WP.mono (borrowMask_ok hv borrow (by rw [flag]; exact bit)) fun t ⟨ht, Ot, value, Kt⟩ => ?_
  have validMask : slot t.mem B kOk = (if 2 ≤ num s.mem B n aL ∧ slot s.mem B kFlag = 1 then 1 else 0) := by
    simpa only [iffBorrow, flag] using value
  exact ⟨ht, (Ou.join Ov (js := [aT1, aT2]) (ds := [])).join Ot
    (js := [aT1, aT2]) (ds := [kOk]), validMask,
    (Ku.mono (by decide)).trans (Kv.trans (Kt.mono (by decide)))⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
