module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyFinal
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.TopWord32
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Check the high modulus bit with a single native-word load -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem topBit_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (.block (topBit n)) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag = (if 2 ^ (32 * n - 1) ≤ num s.mem B n aN then 1 else 0) ∧
      Keeps [.eax] s t := by
  have head := h.hdr_le
  have fits := h.arr_fit (j := aN) (by decide)
  have positive := h.wpos
  unfold topBit
  refine wp_movS (readSrc_sc h.workspace (by change arr n aN + 4 * (n - 1) + 4 ≤ Z; unfold S at fits; omega))
    fun u U _ => ?_
  refine wp_shr (by decide) fun v V _ => ?_
  have K := U.keeps.trans V.keeps
  have hv := h.rest K
  refine wp_storeS (hv.workspace.ea (by unfold kFlag hdr at *; omega))
    (hv.workspace.write (by unfold kFlag hdr at *; omega)) fun t T => WP.block_nil ?_
  have memory : v.mem = s.mem := V.mem.trans U.mem
  refine ⟨hv.rest (T.keeps []), ?_, ?_, K.trans (T.keeps _)⟩
  · rw [T.mem, memory]
    exact Keep.of_slot (writeW32_outside _ _ _ (by decide)) (by simp)
  · unfold slot
    rw [T.mem, memory, w32_write_self, V.gpr, U.gpr, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    change w32 s.mem B (arr n aN + 4 * (n - 1)) / 2 ^ 31 = _
    rw [← VG.Proof.RsaKeyGen.WordBounds32.top_div positive]
    change num s.mem B n aN / 2 ^ (32 * n - 1) = _
    have bound := val32_lt s.mem B (arr n aN) n
    change num s.mem B n aN < 2 ^ (32 * n) at bound
    have p := Nat.two_pow_pos (32 * n - 1)
    have factor : 2 ^ (32 * n) = 2 ^ (32 * n - 1) * 2 := by
      calc
        2 ^ (32 * n) = 2 ^ ((32 * n - 1) + 1) := congrArg (2 ^ ·) (by omega)
        _ = _ := Nat.pow_succ ..
    rw [factor] at bound
    split
    · next H => exact Nat.div_eq_of_lt_le (by simpa only [Nat.one_mul] using H) (by omega)
    · next H => exact Nat.div_eq_of_lt (by omega)

end VG.Proof.RsaKeyGen.X86.Key
