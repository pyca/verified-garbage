module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseBank
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseFrame
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.InvLoop
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseLoad
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

/-! # All key-generation inversions reuse the shared runtime inverse proof -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num bank invSlots invArrs)
open VG.Impl.Rsa.X86.Keys (aM aNM aZero)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (InverseLayout inverseRanges inverse_frame_clear
  inverse_frame_slots inverse_frame)

theorem inverseFrom_ok {s : State} {B : Addr} {Z n N : Nat} {w : Width} {src mo : Loc}
    (h : Ws s B Z n N) (bound : 15 ≤ N) (hw : w ≠ .correction)
    (L : InverseLayout Z (w.words n) (src.offset n) (mo.offset n))
    (odd : val32 s.mem B (mo.offset n) (w.words n) % 2 = 1)
    (large : 1 < val32 s.mem B (mo.offset n) (w.words n)) :
    WP isa (inverseFrom w src mo) s fun t =>
      Ws t B Z n N ∧ Outs B (inverseRanges (w.words n) invSlots) s.mem t.mem ∧
      num t.mem B (w.words n) 1 = Nat.gcd (val32 s.mem B (src.offset n) (w.words n))
        (val32 s.mem B (mo.offset n) (w.words n)) ∧
      (val32 s.mem B (mo.offset n) (w.words n) : Int) ∣
        (num t.mem B (w.words n) 3 : Int) * val32 s.mem B (src.offset n) (w.words n) -
          num t.mem B (w.words n) 1 ∧
      num t.mem B (w.words n) 3 < val32 s.mem B (mo.offset n) (w.words n) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  unfold inverseFrom inverseSetup
  refine WP.seq (WP.seq (WP.mono (inverseLoad_ok h bound hw L)
    fun u ⟨hu, Ou, input, modulus, zero, Ku⟩ => ?_))
  have Hu := shrinkRt (hu.runtime hw) bound
  have bankProof := inverseBank_ok Hu
    (by simpa only [kw_words h.width] using input)
    (by simpa only [kw_words h.width] using modulus) (by omega)
    (by simpa only [kw_words h.width] using zero aZero (by decide) (by decide) (by decide))
    (by simpa only [kw_words h.width] using zero 2 (by decide) (by decide) (by decide))
    (by simpa only [kw_words h.width] using zero 3 (by decide) (by decide) (by decide))
  rw [kw_words h.width] at bankProof
  refine WP.mono bankProof fun v ⟨Hv, Ov, ready, Kv⟩ => ?_
  have hv : Ws v B Z n N := hu.afterBank hw Kv Ov
    (by
      intro j hj
      have small := (by decide : ∀ j ∈ ([1, 2, aNM] : List Nat), j < 15) j hj
      omega)
    (by simp)
  have inputV : num v.mem B (w.words n) 0 = val32 s.mem B (src.offset n) (w.words n) :=
    congrArg Prod.fst ready.initial
  have inverseProof := VG.Proof.Rsa.X86.KeyRt.inverse_ok Hv (by decide)
  rw [kw_words h.width] at inverseProof
  refine WP.mono inverseProof fun t ⟨_, Ot, Kt, computed⟩ => ?_
  have negative : num v.mem B (w.words n) aNM + num v.mem B (w.words n) aM =
      2 ^ (32 * w.words n) := by
    rw [ready.modulus]; exact ready.negated
  have bankV : bank v.mem B (w.words n) 0 =
      (num v.mem B (w.words n) 0, num v.mem B (w.words n) aM, 1, 0) := by
    rw [inputV, ready.modulus]; exact ready.initial
  have result := computed negative ready.zero (by rw [ready.modulus]; exact odd)
    (by rw [ready.modulus]; exact large) bankV
  rw [inputV, ready.modulus] at result
  have ht : Ws t B Z n N := hv.afterBank hw Kt Ot (by
    intro j hj
    have small := (by decide : ∀ j ∈ invArrs, j < 15) j hj
    omega) (by decide)
  refine ⟨ht, ?_, result.1, result.2.1, result.2.2,
    (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans Kt)⟩
  exact ((inverse_frame_clear invSlots Ou).trans
    (inverse_frame_slots (by decide) Ov)).trans (inverse_frame (by decide) Ot)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
