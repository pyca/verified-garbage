module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.SmallConstant
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Rsa.KeyBits32
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

/-! # Detect the specified private-exponent retry bound -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aD kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem smallMask_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (bit : slot s.mem B kOk ≤ 1) :
    WP isa smallMask s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2] [] s.mem t.mem ∧
      isa.eval .e t = some (decide (¬(slot s.mem B kOk = 1 ∧ num s.mem B n aD ≤ 2 ^ (16 * n)))) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have head := h.hdr_le
  unfold smallMask seqs
  refine WP.seq (WP.mono (smallConstant_ok h)
    fun u ⟨hu, Ou, constant, Ku⟩ => ?_)
  have Du : num u.mem B n aD = num s.mem B n aD :=
    Ou.num (by decide) (by simp) (h.fit64 (by decide))
  refine WP.seq (WP.mono (sub_ok hu (by decide) (by decide) (by decide))
    fun v ⟨hv, Ov, subtract, borrowBit, Kv⟩ => ?_)
  rw [Du, constant] at subtract
  have borrow := VG.Proof.Rsa.borrow_iff subtract (val32_lt _ _ _ _) borrowBit
  have borrowOne : (v.gpr .ebx).toNat = 1 ↔ num s.mem B n aD ≤ 2 ^ (16 * n) := by omega
  have maskV : slot v.mem B kOk = slot s.mem B kOk :=
    (Ov.slot (by decide) (by simp)).trans (Ou.slot (by decide) (by simp))
  refine wp_movS (readSrc_sc hv.old.workspace (by unfold kOk hdr at *; omega)) fun w W _ => ?_
  refine wp_logicS (.inl rfl) rfl fun a A => ?_
  refine wp_cmpS rfl fun t T flag => WP.block_nil ?_
  have Ktail : Keeps [.eax] v t := (W.keeps.trans A.keeps).trans (T.keeps _)
  have memory : t.mem = v.mem := T.mem.trans (A.mem.trans W.mem)
  refine ⟨hv.keep Ktail (by rw [memory]; exact Outside.refl _ _ _ _), ?_, ?_, (Ku.mono (by decide)).trans (Kv.trans (Ktail.mono (by decide)))⟩
  · rw [memory]
    exact Ou.join Ov (js := [aT1, aT2]) (ds := [])
  · change t.zf = _
    rw [flag]
    change some (a.gpr .eax - 0#32 == 0#32) = _
    rw [BitVec.sub_zero, A.gpr, W.gpr, W.other _ (by decide)]
    change some ((v.mem.readW (off B kOk) 32 &&& v.gpr .ebx) == 0#32) = _
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_zero]
    rw [VG.Proof.Rsa.KeyBits32.bv_and_bits (by change slot v.mem B kOk ≤ 1; rw [maskV]; exact bit) borrowBit]
    change (if slot v.mem B kOk = 1 ∧ (v.gpr .ebx).toNat = 1 then 1 else 0) = 0 ↔ _
    simpa only [maskV, borrowOne] using
      (show (if slot s.mem B kOk = 1 ∧ num s.mem B n aD ≤ 2 ^ (16 * n) then 1 else 0) = 0 ↔
        ¬(slot s.mem B kOk = 1 ∧ num s.mem B n aD ≤ 2 ^ (16 * n)) from by split <;> simp_all)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
