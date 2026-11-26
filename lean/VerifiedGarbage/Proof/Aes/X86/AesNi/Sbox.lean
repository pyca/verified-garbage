module

public import VerifiedGarbage.TCB.X86.Sse
meta import VerifiedGarbage.TCB.X86.Sse
public import VerifiedGarbage.Proof.Aes.SboxTable
meta import VerifiedGarbage.Proof.Aes.SboxTable

/-!
# The AES S-box of the x86 model

The S-box of the ISA model, computed by repeated squaring, is the one of
`Spec/Aes.lean` (`sbox_eq`), and so its table (`aesSbox_eq_sboxN`).
-/

@[expose] public section

namespace VG.Proof.Aes.X86.AesNi

open VG.X86
open VG.Spec.Aes (sbox)

theorem mul_eq : aesMul = Spec.Aes.mul := rfl

/-- Both square and multiply `b²`, `b⁴`, …, `b¹²⁸` in the same order: unfolded
to the same term (no evaluation left for the kernel). -/
theorem inv_eq (b : BitVec 8) : aesInv b = Spec.Aes.inv b := by
  simp (config := {decide := true}) only [aesInv, Spec.Aes.inv_eq_pow, Spec.Aes.pow, List.range_succ,
    List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil, mul_eq,
    ite_true, ite_false]

theorem sbox_eq : aesSbox = sbox := by
  funext b
  simp only [aesSbox, sbox, inv_eq, ofBits8]

/-- The S-box, from its table (`Proof/Aes/SboxTable.lean`). -/
theorem aesSbox_eq_sboxN (b : BitVec 8) : aesSbox b = BitVec.ofNat 8 (sboxN b.toNat) := by
  rw [sbox_eq, sbox_eq_sboxN]

end VG.Proof.Aes.X86.AesNi
