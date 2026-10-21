module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseLoad
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseFrame
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBank

/-! # Complete native RSA inverse at prime or public-exponent width

The same code proves both a gcd result and the coefficient's congruence.
It therefore supports LCM computation as well as modular inversion.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem inverseFrom_ok {s : State} {B : Addr} {Z n src mo : Nat}
    (h : Ws s B Z n 15) (L : InverseLayout Z n src mo)
    (odd : val32 s.mem B mo n % 2 = 1) (large : 1 < val32 s.mem B mo n) :
    WP isa (inverseFrom n src mo) s fun t =>
      Ws t B Z n 15 ∧ Outs B (inverseRanges n invSlots) s.mem t.mem ∧
      num t.mem B n 1 = Nat.gcd (val32 s.mem B src n) (val32 s.mem B mo n) ∧
      (val32 s.mem B mo n : Int) ∣ (num t.mem B n 3 : Int) * val32 s.mem B src n - num t.mem B n 1 ∧
      num t.mem B n 3 < val32 s.mem B mo n ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  unfold inverseFrom inverseSetup
  refine WP.seq (WP.seq (WP.mono (inverseLoad_ok h L) fun u ⟨hu, Ou, input, modulus, zero, Ku⟩ => ?_))
  refine WP.mono (inverseBank_ok hu input modulus (by omega)
    (zero aZero (by decide) (by decide) (by decide))
    (zero 2 (by decide) (by decide) (by decide))
    (zero 3 (by decide) (by decide) (by decide))) fun v ⟨hv, Ov, ready, Kv⟩ => ?_
  have inputV : num v.mem B n 0 = val32 s.mem B src n := congrArg Prod.fst ready.initial
  refine WP.mono (inverse_ok hv (by decide)) fun t ⟨ht, Ot, Kt, computed⟩ => ?_
  have negative : num v.mem B n aNM + num v.mem B n aM = 2 ^ (32 * n) := by
    rw [ready.modulus]
    exact ready.negated
  have bankV : bank v.mem B n 0 = (num v.mem B n 0, num v.mem B n aM, 1, 0) := by
    rw [inputV, ready.modulus]
    exact ready.initial
  have result := computed negative ready.zero (by rw [ready.modulus]; exact odd)
    (by rw [ready.modulus]; exact large) bankV
  rw [inputV, ready.modulus] at result
  refine ⟨ht, ?_, result.1, result.2.1, result.2.2,
    (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans Kt)⟩
  exact ((inverse_frame_clear invSlots Ou).trans
    (inverse_frame_slots (by decide) Ov)).trans (inverse_frame (by decide) Ot)

end VG.Proof.RsaKeyGen.X86.Key
