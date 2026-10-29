module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyConstant
import VerifiedGarbage.Proof.Rsa.X86.KeyEq

/-! # Recognize a unit GCD at either prime or public-exponent width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem gcdIsOne_ok {s : State} {B : Addr} {Z k N : Nat} (h : Ws s B Z k N) (space : 15 ≤ N) :
    WP isa (gcdIsOne k) s fun t =>
      Ws t B Z k N ∧ Keep B k [aT2, aT1] [sT, kFlag] s.mem t.mem ∧
      slot t.mem B kFlag = (if num s.mem B k 1 = 1 then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have bound : 1 < 2 ^ (32 * k) := by
    have P : 2 ^ 1 ≤ 2 ^ (32 * k) := Nat.pow_le_pow_right (by decide) (by have := h.wpos; omega)
    omega
  unfold gcdIsOne seqs
  refine WP.seq (WP.mono (constArray_ok h (by unfold aT2; omega) bound)
    fun u ⟨hu, Ou, constant, Ku⟩ => ?_)
  refine WP.mono (eqS_ok hu (by unfold aT1; omega) (by omega) (by unfold aT2; omega)
    (by decide) (by decide) (by decide)) fun t ⟨ht, Ot, result, Kt⟩ => ?_
  have original : num u.mem B k 1 = num s.mem B k 1 :=
    Ou.num (by decide) (by simp) (h.fit64 (by omega))
  rw [original, constant] at result
  exact ⟨ht, Ou.join Ot (js := [aT2, aT1]) (ds := [sT, kFlag]), result,
    (Ku.mono (by decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Key
