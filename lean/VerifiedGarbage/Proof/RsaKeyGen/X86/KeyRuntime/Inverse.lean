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
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StackRange
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseCall
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToAdditive

/-! # All key-generation inversions reuse the shared runtime inverse proof -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num bank invSlots invArrs)
open VG.Impl.Rsa.X86.Keys (aM aNM aZero)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (InverseLayout inverseRanges inverse_frame_clear
  inverse_frame_slots inverse_frame)

/-- The setup leaves the inverse's input, modulus and accumulators in place. -/
theorem inverseSetup_ok {s : State} {B : Addr} {Z n N : Nat} {w : Width} {src mo : Loc}
    (h : Ws s B Z n N) (bound : 15 ≤ N) (hw : w ≠ .correction)
    (L : InverseLayout Z (w.words n) (src.offset n) (mo.offset n))
    (odd : val32 s.mem B (mo.offset n) (w.words n) % 2 = 1)
    (large : 1 < val32 s.mem B (mo.offset n) (w.words n)) :
    WP isa (inverseSetup w src mo) s fun v =>
      InvReady B Z n N w v ∧ Outs B (inverseRanges (w.words n) invSlots) s.mem v.mem ∧
      num v.mem B (w.words n) 0 = val32 s.mem B (src.offset n) (w.words n) ∧
      num v.mem B (w.words n) aM = val32 s.mem B (mo.offset n) (w.words n) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s v := by
  unfold inverseSetup
  refine WP.seq (WP.mono (inverseLoad_ok h bound hw L)
    fun u ⟨hu, Ou, input, modulus, zero, Ku⟩ => ?_)
  have Hu := shrinkRt (hu.runtime hw) bound
  have bankProof := inverseBank_ok Hu
    (by simpa only [kw_words h.width] using input)
    (by simpa only [kw_words h.width] using modulus) (by omega)
    (by simpa only [kw_words h.width] using zero aZero (by decide) (by decide) (by decide))
    (by simpa only [kw_words h.width] using zero 2 (by decide) (by decide) (by decide))
    (by simpa only [kw_words h.width] using zero 3 (by decide) (by decide) (by decide))
  rw [kw_words h.width] at bankProof
  refine WP.mono bankProof fun v ⟨_, Ov, ready, Kv⟩ => ?_
  have hv : Ws v B Z n N := hu.afterBank hw Kv Ov
    (by
      intro j hj
      have small := (by decide : ∀ j ∈ ([1, 2, aNM] : List Nat), j < 15) j hj
      omega)
    (by simp)
  have bankV := ready.initial
  simp only [bank, Prod.mk.injEq] at bankV
  refine ⟨⟨hv, bound, hw, by rw [ready.modulus]; exact odd, by rw [ready.modulus]; exact large,
      bankV.2.1.trans ready.modulus.symm, bankV.2.2.1, bankV.2.2.2,
      by rw [ready.modulus]; exact ready.negated, ready.zero⟩,
    (inverse_frame_clear invSlots Ou).trans (inverse_frame_slots (by decide) Ov), bankV.1, ready.modulus,
    (Ku.mono (by decide)).trans (Kv.mono (by decide))⟩

theorem inverseFrom_ok {s : State} {B : Addr} {Z n N : Nat} {w : Width} {src mo : Loc}
    (h : Ws s B Z n N) (bound : 15 ≤ N) (hw : w ≠ .correction)
    (L : InverseLayout Z (w.words n) (src.offset n) (mo.offset n))
    (odd : val32 s.mem B (mo.offset n) (w.words n) % 2 = 1)
    (large : 1 < val32 s.mem B (mo.offset n) (w.words n)) :
    WP isa (inverseFrom w src mo) s fun t =>
      Ws t B Z n N ∧ OutsS B (s.gpr .esp) (inverseRanges (w.words n) invSlots) s.mem t.mem ∧
      num t.mem B (w.words n) 1 = Nat.gcd (val32 s.mem B (src.offset n) (w.words n))
        (val32 s.mem B (mo.offset n) (w.words n)) ∧
      (val32 s.mem B (mo.offset n) (w.words n) : Int) ∣
        (num t.mem B (w.words n) 3 : Int) * val32 s.mem B (src.offset n) (w.words n) -
          num t.mem B (w.words n) 1 ∧
      num t.mem B (w.words n) 3 < val32 s.mem B (mo.offset n) (w.words n) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  unfold inverseFrom
  refine WP.seq (WP.mono (inverseSetup_ok h bound hw L odd large) fun v ⟨R, Ov, input, modulus, Kv⟩ => ?_)
  refine WP.mono (callInverse_ok R) fun t ⟨ht, Ot, gcd, bezout, lt, Kt, _⟩ => ?_
  rw [input, modulus] at gcd bezout
  rw [modulus] at lt
  have spV : v.gpr .esp = s.gpr .esp := Kv.1 .esp (by decide)
  rw [spV] at Ot
  exact ⟨ht, (OutsS.of_outs Ov).trans Ot, gcd, bezout, lt, Kv.trans (Kt.mono (by decide))⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
