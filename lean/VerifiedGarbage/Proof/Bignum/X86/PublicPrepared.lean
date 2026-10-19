module
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.X86.PublicInputs
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Bignum.X86.PublicApply
import VerifiedGarbage.Proof.Bignum.X86.PublicImport
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Resources and acceptance mask ready for checked RSA export -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicContext
open VG.Proof.Mont VG.Proof.Mont.X86

theorem publicPrepared_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PublicInputs base bytes len args s)
    (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true) :
    WP isa (.seq (PublicFn.importNumbers (Spec.Rsa.modulusWords len))
      (PublicFn.acceptAndPower (Spec.Rsa.modulusWords len))) s fun t =>
      PublicInputs base bytes len args t ∧ t.gpr .esp = s.gpr .esp ∧
      ∃ accept : Bool, t.mem.readW (off base 144) 32 = if accept then BitVec.allOnes 32 else 0 := by
  have dims := h.dimensions
  have facts := valid_facts valid h.lower
  have sz := size_eq (Spec.Rsa.modulusWords len)
  have space := h.space
  refine WP.seq (WP.mono (importNumbers_ok h.scratch dims.1 h.space (by have := h.lower; omega) dims.2.2
    (h.stack 2 (by decide)) (by rw [← h.nLen]; exact h.stack 3 (by decide))
    (h.stack 6 (by decide)) (by rw [← h.inLen]; exact h.stack 7 (by decide))
    h.nFit h.inFit h.nRead h.inRead h.nApart h.inApart)
    fun u ⟨N, X, O, K⟩ => ?_)
  have hu := h.keep K (by decide) (by decide) (O.mono (by omega) (by omega))
  refine WP.mono (acceptAndPower_ok hu.scratch dims.1 dims.2.1 h.space N X rfl facts.2.1 facts.1)
    fun t ⟨_, _, Mask, Ot, Kt⟩ => ?_
  have Kst : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := K.trans (Kt.mono (by decide))
  have Ost : Outside base 0 bytes s.mem t.mem :=
    (O.mono (by omega) (by omega)).trans (Ot.mono (by omega) (by omega))
  refine ⟨h.keep Kst (by decide) (by decide) Ost, Kst.1 _ (by decide),
    decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 6)) len) <
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)), ?_⟩
  simpa only [decide_eq_true_eq] using Mask

end VG.Proof.Bignum.X86.PublicContext
