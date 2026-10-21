module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNotSlot
import VerifiedGarbage.Proof.Rsa.X86.KeyCopy
import VerifiedGarbage.Proof.Rsa.X86.KeyEq
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Handle public exponents zero and one, including degenerate LCMs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem dZero_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa dZero s fun t => Ws t B Z n 32 ∧ Keep B n [] [kOk] s.mem t.mem ∧
      slot t.mem B kOk = 0 ∧ Keeps [.eax] s t := by
  have head := h.hdr_le
  unfold dZero
  refine wp_movS rfl fun u U _ => ?_
  have hu := h.rest U.keeps
  refine wp_storeS (hu.workspace.ea (by unfold kOk hdr at *; omega))
    (hu.workspace.write (by unfold kOk hdr at *; omega)) fun t T => WP.block_nil ?_
  refine ⟨hu.rest (T.keeps []), ?_, ?_, U.keeps.trans (T.keeps _)⟩
  · rw [T.mem, U.mem]
    exact Keep.of_slot (writeW32_outside _ _ _ (by decide)) (by simp)
  · unfold slot
    rw [T.mem, U.mem, w32_write_self, U.gpr]
    rfl

theorem dOne_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (one : num s.mem B n aOne = 1) :
    WP isa (dOne n) s fun t => Ws t B Z n 32 ∧
      Keep B n [aD, aT1] [sT, kFlag, kOk] s.mem t.mem ∧ num t.mem B n aD = 1 ∧
      slot t.mem B kOk = (if num s.mem B n aL = 1 then 0 else 1) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have hf : kFlag + 4 ≤ hdr := by decide
  unfold dOne seqs
  refine WP.seq (WP.mono (copy_ok h (by decide) (by decide)) fun u ⟨hu, Ou, D, Ku, _⟩ => ?_)
  rw [one] at D
  have L : num u.mem B n aL = num s.mem B n aL := Ou.num (by decide) (by simp) (h.fit64 (by decide))
  have O : num u.mem B n aOne = 1 := by rw [Ou.num (by decide) (by simp) (h.fit64 (by decide)), one]
  refine WP.seq (WP.mono (eqS_ok hu (by decide) (by decide) (by decide) (by decide) (by decide) hf)
    fun v ⟨hv, Ov, flag, Kv⟩ => ?_)
  rw [L, O] at flag
  have bit : slot v.mem B kFlag ≤ 1 := by rw [flag]; split <;> omega
  refine WP.mono (notSlot_ok hv (by decide) hf bit) fun t ⟨ht, Ot, mask, Kt⟩ => ?_
  refine ⟨ht, (Ou.join Ov (js := [aD, aT1]) (ds := [sT, kFlag, kOk])).join Ot
    (js := [aD, aT1]) (ds := [sT, kFlag, kOk]), ?_, ?_,
    (Ku.mono (by decide)).trans (Kv.trans (Kt.mono (by decide)))⟩
  · rw [Ot.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; decide)
      (h.fit64 (by decide)), Ov.num (by decide) (by decide) (h.fit64 (by decide)), D]
  · rw [mask, flag]
    by_cases p : num s.mem B n aL = 1 <;> simp [p]

end VG.Proof.RsaKeyGen.X86.Key
