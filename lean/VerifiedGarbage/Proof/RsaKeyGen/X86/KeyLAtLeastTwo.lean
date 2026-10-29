module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyBorrowMask
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyConstant
import VerifiedGarbage.Proof.Rsa.X86.KeySub
import VerifiedGarbage.Proof.Rsa.InverseArithmetic

/-! # The public-exponent inverse also needs an LCM of at least two -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem lAtLeastTwo_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (bit : slot s.mem B kFlag ≤ 1) :
    WP isa (lAtLeastTwo n) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2] [kOk] s.mem t.mem ∧
      slot t.mem B kOk = (if 2 ≤ num s.mem B n aL ∧ slot s.mem B kFlag = 1 then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have bound : 2 < 2 ^ (32 * n) := by
    have P : 2 ^ 2 ≤ 2 ^ (32 * n) := Nat.pow_le_pow_right (by decide) (by have := h.wpos; omega)
    omega
  have hf : kFlag + 4 ≤ hdr := by decide
  unfold lAtLeastTwo seqs
  refine WP.seq (WP.mono (constArray_ok h (by decide) bound) fun u ⟨hu, Ou, constant, Ku⟩ => ?_)
  have L : num u.mem B n aL = num s.mem B n aL := Ou.num (by decide) (by simp) (h.fit64 (by decide))
  refine WP.seq (WP.mono (sub3_ok hu (by decide) (by decide) (by decide) (by decide) (by decide))
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

end VG.Proof.RsaKeyGen.X86.Key
