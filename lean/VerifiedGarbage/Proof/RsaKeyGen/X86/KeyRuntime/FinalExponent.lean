module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Constant
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ScalarKey
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

/-! # The lower bound on the runtime public exponent -/

@[expose] public section
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
