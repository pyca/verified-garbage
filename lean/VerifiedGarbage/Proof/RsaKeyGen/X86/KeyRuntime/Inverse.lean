module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseFrame
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseLoad
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StackRange
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseCall

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseLoad
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.InvLoop
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBank
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word
/-! # All key-generation inversions reuse the shared runtime inverse proof -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/InverseBank.lean`, which only this module imported.
section

/-! # Inverse-bank setup uses the shared runtime-width RSA operations -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.Rsa.X86.KeyRt (RtWs kw)
open VG.Proof.RsaKeyGen.X86.Key (InverseReady)

theorem inverseBank_ok {s : State} {B : Addr} {Z len a m : Nat} {w : Width}
    (h : RtWs w.lay s B Z len 15) (input : num s.mem B (kw len) 0 = a)
    (modulus : num s.mem B (kw len) aM = m) (positive : 0 < m)
    (zero : num s.mem B (kw len) aZero = 0)
    (x₁ : num s.mem B (kw len) 2 = 0) (x₂ : num s.mem B (kw len) 3 = 0) :
    WP isa (VG.Impl.RsaKeyGen.X86.KeyRuntime.inverseBank w) s fun t =>
      RtWs w.lay t B Z len 15 ∧ Keep B (kw len) [1, 2, aNM] [] s.mem t.mem ∧
      InverseReady B (kw len) a m t ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have f0 := h.ws.fit64 (j := 0) (by decide)
  have f1 := h.ws.fit64 (j := 1) (by decide)
  have f2 := h.ws.fit64 (j := 2) (by decide)
  have f3 := h.ws.fit64 (j := 3) (by decide)
  have fm := h.ws.fit64 (j := aM) (by decide)
  have fz := h.ws.fit64 (j := aZero) (by decide)
  unfold VG.Impl.RsaKeyGen.X86.KeyRuntime.inverseBank seqs
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.KeyRt.copy_ok h (by decide) (by decide) (by decide)) fun u ⟨hu, Ou, v1, Ku, _⟩ => ?_)
  have two : num u.mem B (kw len) 2 = 0 := by rw [Ou.num (by decide) (by simp) f2, x₁]
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.KeyRt.setOne_ok hu (by decide)) fun v ⟨hv, Ov, v2, Kv⟩ => ?_)
  rw [two, Nat.zero_div, Nat.mul_zero, Nat.add_zero] at v2
  have z : num v.mem B (kw len) aZero = 0 := by
    rw [Ov.num (by decide) (by simp) fz, Ou.num (by decide) (by simp) fz, zero]
  have mV : num v.mem B (kw len) aM = m := by
    rw [Ov.num (by decide) (by simp) fm, Ou.num (by decide) (by simp) fm, modulus]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.sub3_ok hv (by decide) (by decide) (by decide))
    fun t ⟨ht, Ot, subtract, bit, Kt⟩ => ?_
  rw [z, mV, Nat.zero_add] at subtract
  have borrow : (t.gpr .ebx).toNat = 1 := by
    by_cases p : (t.gpr .ebx).toNat = 0
    · rw [p, Nat.mul_zero] at subtract
      omega
    · omega
  rw [borrow, Nat.mul_one] at subtract
  have one : num t.mem B (kw len) 1 = m := by
    rw [Ot.num (by decide) (by simp) f1, Ov.num (by decide) (by simp) f1, v1, modulus]
  have twoT : num t.mem B (kw len) 2 = 1 := by rw [Ot.num (by decide) (by simp) f2, v2]
  have value0 : num t.mem B (kw len) 0 = a := by
    rw [Ot.num (by decide) (by simp) f0, Ov.num (by decide) (by simp) f0,
      Ou.num (by decide) (by simp) f0, input]
  have value3 : num t.mem B (kw len) 3 = 0 := by
    rw [Ot.num (by decide) (by simp) f3, Ov.num (by decide) (by simp) f3,
      Ou.num (by decide) (by simp) f3, x₂]
  refine ⟨ht, (Ou.join Ov (js := [1, 2, aNM]) (ds := [])).join Ot
    (js := [1, 2, aNM]) (ds := []), ⟨?_, subtract, ?_, ?_⟩,
    (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans (Kt.mono (by decide)))⟩
  · rw [Ot.num (by decide) (by simp) fm, mV]
  · rw [Ot.num (by decide) (by simp) fz, z]
  · simp only [bank, Nat.zero_add, value0, one, twoT, value3]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

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
