module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Spec.Rsa

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.TopBit
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ScalarKey
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Scalar
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyMaskFlag
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyFinalMask
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Constant
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
public import VerifiedGarbage.Spec.Rsa.Contract
/-! # The final native mask is exactly the RSA key shape check -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/MaskFlag.lean`, which only this module imported.
section

/-! # Combine a checked bit with the persistent RSA validity mask -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (kOk kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem withFlag_ok {s : State} {B : Addr} {Z n value : Nat} {c : Prog isa} {rs : List Reg}
    (bit : slot s.mem B kOk ≤ 1) (valueBit : value ≤ 1)
    (correct : WP isa c s fun u => Ws u B Z n 32 ∧ Keep B n [] [kFlag] s.mem u.mem ∧
      slot u.mem B kFlag = value ∧ Keeps rs s u) (eax : .eax ∈ rs := by decide) :
    WP isa (withFlag c) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [] [kFlag, kOk] s.mem t.mem ∧
      slot t.mem B kOk = (if slot s.mem B kOk = 1 ∧ value = 1 then 1 else 0) ∧ Keeps rs s t := by
  unfold withFlag
  refine WP.seq (WP.mono correct fun u ⟨hu, Ou, flag, Ku⟩ => ?_)
  have maskU : slot u.mem B kOk = slot s.mem B kOk := Ou.slot (by decide) (by decide)
  refine WP.mono (andS_ok hu (by decide) (by decide) (by decide)
    (by rw [maskU]; exact bit) (by rw [flag]; exact valueBit)) fun t ⟨ht, Ot, mask, Kt⟩ => ?_
  exact ⟨ht, Ou.join Ot (js := []) (ds := [kFlag, kOk]), by rw [mask, maskU, flag], Ku.trans (Kt.mono (by simpa using eax))⟩


end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/FinalExponent.lean`, which only this module imported.
section

/-! # The lower bound on the runtime public exponent -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aE kOk kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem exponentAtLeastThree_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (bit : slot s.mem B kOk ≤ 1) :
    WP isa exponentAtLeastThree s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2] [kFlag, kOk] s.mem t.mem ∧
      slot t.mem B kOk = (if 3 ≤ num s.mem B n aE ∧ slot s.mem B kOk = 1 then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  unfold exponentAtLeastThree seqs
  refine WP.seq (WP.mono (constant_ok h (by decide) (3 : BitVec 32)) fun u ⟨hu, Ou, constant, Ku⟩ => ?_)
  change num u.mem B n aT1 = 3 at constant
  have E : num u.mem B n aE = num s.mem B n aE := Ou.num (by decide) (by simp) (h.fit64 (by decide))
  refine WP.seq (WP.mono (sub_ok hu (by decide) (by decide) (by decide))
    fun v ⟨hv, Ov, subtract, borrow, Kv⟩ => ?_)
  rw [E, constant] at subtract
  have iffBorrow := VG.Proof.Rsa.borrow_iff subtract (val32_lt _ _ _ _) borrow
  have maskV : slot v.mem B kOk = slot s.mem B kOk :=
    (Ov.slot (by decide) (by simp)).trans (Ou.slot (by decide) (by simp))
  refine WP.seq (WP.mono (saveSlot_ok hv (by decide) (by decide)) fun w ⟨hw, Ow, flag, Kw⟩ => ?_)
  rw [maskV] at flag
  have borrowW : (w.gpr .ebx).toNat = (v.gpr .ebx).toNat := congrArg BitVec.toNat (Kw.1 .ebx (by decide))
  refine WP.mono (borrowMask_ok hw (by rw [borrowW]; exact borrow)
    (by rw [flag]; exact bit)) fun t ⟨ht, Ot, value, Kt⟩ => ?_
  refine ⟨ht, ((Ou.join Ov (js := [aT1, aT2]) (ds := [])).join Ow
    (js := [aT1, aT2]) (ds := [kFlag])).join Ot (js := [aT1, aT2]) (ds := [kFlag, kOk]), ?_,
    (Ku.mono (by decide)).trans (Kv.trans ((Kw.mono (by decide)).trans (Kt.mono (by decide))))⟩
  simpa only [borrowW, iffBorrow, flag] using value

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aN aE kOk kFlag kEv)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (mask_bit mask_ite_one maskFlag_preserves_e)

theorem finalMask_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (bit : slot s.mem B kOk ≤ 1) (loaded : num s.mem B n aE = val32 s.mem B kEv 2) :
    WP isa finalMask s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2] [kFlag, kOk] s.mem t.mem ∧
      slot t.mem B kOk = (if slot s.mem B kOk = 1 ∧
        2 ^ (32 * n - 1) ≤ num s.mem B n aN ∧
        num s.mem B n aPa % 2 = 1 ∧ num s.mem B n aQa % 2 = 1 ∧
        Spec.Rsa.exponentValid (val32 s.mem B kEv 2) = true then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  unfold finalMask seqs
  refine WP.seq (WP.mono (withFlag_ok bit (by split <;> omega_arith) (topBit_ok h))
    fun u ⟨hu, Ou, Mu, Ku⟩ => ?_)
  have Pu : num u.mem B n aPa = num s.mem B n aPa := Ou.num (by simp) (by decide) (h.fit64 (by decide))
  refine WP.seq (WP.mono (withFlag_ok (by rw [Mu]; exact mask_bit _)
    (show num u.mem B n aPa % 2 ≤ 1 by omega_arith) (bitOf_ok hu (by decide) (by decide)))
    fun v ⟨hv, Ov, Mv, Kv⟩ => ?_)
  rw [Pu, Mu] at Mv
  have Fv := Ou.trans Ov
  have Qv : num v.mem B n aQa = num s.mem B n aQa := Fv.num (by simp) (by decide) (h.fit64 (by decide))
  refine WP.seq (WP.mono (withFlag_ok (by rw [Mv]; exact mask_bit _)
    (show num v.mem B n aQa % 2 ≤ 1 by omega_arith) (bitOf_ok hv (by decide) (by decide)))
    fun w ⟨hw, Ow, Mw, Kw⟩ => ?_)
  rw [Qv, Mv] at Mw
  have Fw := Fv.trans Ow
  have Ew : num w.mem B n aE = val32 s.mem B kEv 2 :=
    (Fw.num (by simp) (by decide) (h.fit64 (by decide))).trans loaded
  refine WP.seq (WP.mono (withFlag_ok (by rw [Mw]; exact mask_bit _)
    (show num w.mem B n aE % 2 ≤ 1 by omega_arith) (bitOf_ok hw (by decide) (by decide)))
    fun a ⟨ha, Oa, Ma, Ka⟩ => ?_)
  rw [Ew, Mw] at Ma
  have Fa := Fw.trans Oa
  have Ea : val32 a.mem B kEv 2 = val32 s.mem B kEv 2 := maskFlag_preserves_e Fa
  refine WP.seq (WP.mono (withFlag_ok (by rw [Ma]; exact mask_bit _)
    (by split <;> omega_arith) (exponentUpper_ok ha)) fun b ⟨hb, Ob, Mb, Kb⟩ => ?_)
  rw [Ea, Ma] at Mb
  have Fb := Fa.trans Ob
  have Eb : num b.mem B n aE = val32 s.mem B kEv 2 :=
    (Fb.num (by simp) (by decide) (h.fit64 (by decide))).trans loaded
  refine WP.mono (exponentAtLeastThree_ok hb (by rw [Mb]; exact mask_bit _))
    fun t ⟨ht, Ot, Mt, Kt⟩ => ?_
  rw [Eb, Mb] at Mt
  refine ⟨ht, Fb.join Ot (js := [aT1, aT2]) (ds := [kFlag, kOk]), ?_,
    (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans ((Kw.mono (by decide)).trans
      ((Ka.mono (by decide)).trans ((Kb.mono (by decide)).trans Kt))))⟩
  exact Mt.trans (Key.finalMask_cond _ _ _ _ _ _)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
