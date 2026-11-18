module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseFrame
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseLoad
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseCall
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Copy
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Framed
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Rsa.X86.KeySub
public import VerifiedGarbage.Impl.Rsa.X86.Inverse
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero

/-! ### `RsaKeyGen.X86.KeyRuntime.Clear`, which this module and modules that import it used -/

section

/-! # The inverse and persistent banks reuse the runtime RSA clear proof -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Impl.Rsa.X86.Keys (hdr)

theorem clear_ok {s : State} {B : Addr} {Z n N k : Nat} (h : Ws s B Z n N)
    (w : Width) (hw : w ≠ .correction) (positive : 0 < k) (bound : k ≤ N) :
    WP isa (clear w k) s fun t => Ws t B Z n N ∧
      Outside B hdr (4 * (k * (w.words n + 2))) s.mem t.mem ∧
      (∀ j < k, val32 t.mem B (Loc.offset n (.array w j)) (w.words n + 2) = 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have H := h.runtime hw
  have code : clear w k = VG.Impl.Rsa.X86.KeyRt.zeroArrays w.lay k := by
    cases w <;> simp_all [clear]
  rw [code]
  have core := VG.Proof.Rsa.X86.KeyRt.zeroArrays_ok H positive bound
  rw [kw_words h.width] at core
  refine WP.mono core fun t ⟨_, O, V, K⟩ => ?_
  have fit := H.ws.fits
  rw [kw_words h.width] at fit
  have bound' : hdr + 4 * (k * (w.words n + 2)) ≤ Z := by
    have le := Nat.mul_le_mul_right (w.words n + 2) bound
    simp only [VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S] at fit
    rw [Nat.mul_left_comm] at fit
    omega_using [fit, le]
  simp only [VG.Proof.Rsa.X86.Keys.arr, Nat.zero_mul, Nat.add_zero] at O
  refine ⟨h.keep K (O.mono (Nat.zero_le _) (by omega_using [bound'])), O, ?_, K⟩
  simpa only [Loc.offset, VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S,
    VG.Impl.Rsa.X86.Keys.slot, VG.Impl.Rsa.X86.Keys.stride] using V

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.InverseLoad`, which only this module used -/

section

/-! # Load a prime, exponent or full-width inverse bank without specializing code -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep arr S)
open VG.Impl.Rsa.X86.Keys (hdr aM)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (InverseLayout)

theorem inverseLoad_ok {s : State} {B : Addr} {Z n N : Nat} {w : Width} {src mo : Loc}
    (h : Ws s B Z n N) (bound : 15 ≤ N) (hw : w ≠ .correction)
    (L : InverseLayout Z (w.words n) (src.offset n) (mo.offset n)) :
    WP isa (inverseLoad w src mo) s fun t =>
      Ws t B Z n N ∧ Outside B hdr (4 * (15 * (w.words n + 2))) s.mem t.mem ∧
      num t.mem B (w.words n) 0 = val32 s.mem B (src.offset n) (w.words n) ∧
      num t.mem B (w.words n) aM = val32 s.mem B (mo.offset n) (w.words n) ∧
      (∀ j, j < 15 → j ≠ 0 → j ≠ aM → num t.mem B (w.words n) j = 0) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  obtain H := shrinkRt (h.runtime hw) bound
  have hn := h.old.workspace.nowrap
  obtain f0 := H.ws.arr_fit (j := 0) (by decide)
  obtain fm := H.ws.arr_fit (j := aM) (by decide)
  rw [kw_words h.width] at f0 fm
  have srcBound := L.source_bound
  have moBound := L.modulus_bound
  have srcSep := L.source_outside
  have moSep := L.modulus_outside
  obtain sepSource : (Loc.array w 0).offset n + 4 * w.words n ≤ src.offset n ∨
      src.offset n + 4 * w.words n ≤ (Loc.array w 0).offset n := by
    simp only [offset_array, arr, S] at *
    omega_arith
  obtain sepModulus : (Loc.array w aM).offset n + 4 * w.words n ≤ mo.offset n ∨
      mo.offset n + 4 * w.words n ≤ (Loc.array w aM).offset n := by
    simp only [offset_array, arr, S, aM] at *
    omega_arith
  unfold inverseLoad VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (WP.mono (clear_ok h w hw (by decide) bound) fun u ⟨hu, Ou, zero, Ku⟩ => ?_)
  have zeros (j : Nat) (hj : j < 15) : num u.mem B (w.words n) j = 0 := by
    obtain V := zero j hj
    rw [offset_array, val32_append] at V
    change val32 u.mem B (arr (w.words n) j) (w.words n) = 0
    omega_arith
  obtain source : val32 u.mem B (src.offset n) (w.words n) = val32 s.mem B (src.offset n) (w.words n) :=
    Ou.val32 (by simp only [arr, S] at srcSep; omega_arith) (by omega_arith)
  refine WP.seq (WP.mono (copy_loc_ok hu w (.array w 0) src
    (by simp only [offset_array]; unfold S at f0; omega_arith) srcBound sepSource)
    fun v ⟨hv, Ov, input, Kv⟩ => ?_)
  rw [offset_array] at Ov input
  change num v.mem B (w.words n) 0 = val32 u.mem B (src.offset n) (w.words n) at input
  obtain vKeep : Keep B (w.words n) [0] [] u.mem v.mem :=
    Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using Ov) (by unfold S; omega_arith) (by simp)
  obtain vFrame : Outside B hdr (4 * (15 * (w.words n + 2))) s.mem v.mem :=
    Ou.trans (Ov.mono (by unfold arr; omega_arith)
      (by unfold arr S; omega_arith))
  obtain modulus : val32 v.mem B (mo.offset n) (w.words n) = val32 s.mem B (mo.offset n) (w.words n) :=
    vFrame.val32 (by simp only [arr, S] at moSep; omega_arith) (by omega_arith)
  refine WP.mono (copy_loc_ok hv w (.array w aM) mo
    (by simp only [offset_array]; unfold S at fm; omega_arith) moBound sepModulus)
    fun t ⟨ht, Ot, valueM, Kt⟩ => ?_
  rw [offset_array] at Ot valueM
  change num t.mem B (w.words n) aM = val32 v.mem B (mo.offset n) (w.words n) at valueM
  obtain tKeep : Keep B (w.words n) [aM] [] v.mem t.mem :=
    Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using Ot) (by unfold S; omega_arith) (by simp)
  have bankfit (j : Nat) (hj : j < 15) : arr (w.words n) j + S (w.words n) ≤ 2 ^ 64 := by
    obtain fit := H.ws.fit64 hj
    rwa [kw_words h.width] at fit
  refine ⟨ht, vFrame.trans (Ot.mono (by unfold arr; omega_arith)
    (by unfold arr S aM; omega_arith)), ?_, valueM.trans modulus, ?_,
    (Ku.mono (by decide)).trans (Kv.trans Kt)⟩
  · rw [tKeep.num (by decide) (by simp) (bankfit _ (by decide)), input, source]
  · intro j hj j0 jm
    rw [tKeep.num (by simp only [List.mem_singleton]; intro k e; subst k; exact Ne.symm jm)
      (by simp) (bankfit j hj),
      vKeep.num (by simp only [List.mem_singleton]; intro k e; subst k; exact Ne.symm j0)
      (by simp) (bankfit j hj), zeros j hj]

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyInverseBank`, which only this module used -/

section

/-! # Initialize the native inverse's Euclidean bank and negated modulus -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot

structure InverseReady (B : Addr) (n a m : Nat) (s : State) : Prop where
  modulus : num s.mem B n aM = m
  negated : num s.mem B n aNM + m = 2 ^ (32 * n)
  zero : num s.mem B n aZero = 0
  initial : bank s.mem B n 0 = (a, m, 1, 0)

end VG.Proof.RsaKeyGen.X86.Key

end

end

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
  obtain f0 := h.ws.fit64 (j := 0) (by decide)
  obtain f1 := h.ws.fit64 (j := 1) (by decide)
  obtain f2 := h.ws.fit64 (j := 2) (by decide)
  obtain f3 := h.ws.fit64 (j := 3) (by decide)
  obtain fm := h.ws.fit64 (j := aM) (by decide)
  obtain fz := h.ws.fit64 (j := aZero) (by decide)
  unfold VG.Impl.RsaKeyGen.X86.KeyRuntime.inverseBank seqs
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.KeyRt.copy_ok h (by decide) (by decide) (by decide)) fun u ⟨hu, Ou, v1, Ku, _⟩ => ?_)
  obtain two : num u.mem B (kw len) 2 = 0 := by rw [Ou.num (by decide) (by simp) f2, x₁]
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.KeyRt.setOne_ok hu (by decide)) fun v ⟨hv, Ov, v2, Kv⟩ => ?_)
  rw [two, Nat.zero_div, Nat.mul_zero, Nat.add_zero] at v2
  obtain z : num v.mem B (kw len) aZero = 0 := by
    rw [Ov.num (by decide) (by simp) fz, Ou.num (by decide) (by simp) fz, zero]
  obtain mV : num v.mem B (kw len) aM = m := by
    rw [Ov.num (by decide) (by simp) fm, Ou.num (by decide) (by simp) fm, modulus]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.sub3_ok hv (by decide) (by decide) (by decide))
    fun t ⟨ht, Ot, subtract, bit, Kt⟩ => ?_
  rw [z, mV, Nat.zero_add] at subtract
  obtain borrow : (t.gpr .ebx).toNat = 1 := by
    by_cases p : (t.gpr .ebx).toNat = 0
    · rw [p, Nat.mul_zero] at subtract
      omega
    · omega
  rw [borrow, Nat.mul_one] at subtract
  obtain one : num t.mem B (kw len) 1 = m := by
    rw [Ot.num (by decide) (by simp) f1, Ov.num (by decide) (by simp) f1, v1, modulus]
  obtain twoT : num t.mem B (kw len) 2 = 1 := by rw [Ot.num (by decide) (by simp) f2, v2]
  obtain value0 : num t.mem B (kw len) 0 = a := by
    rw [Ot.num (by decide) (by simp) f0, Ov.num (by decide) (by simp) f0,
      Ou.num (by decide) (by simp) f0, input]
  obtain value3 : num t.mem B (kw len) 3 = 0 := by
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
  obtain Hu := shrinkRt (hu.runtime hw) bound
  obtain bankProof := inverseBank_ok Hu
    (by simpa only [kw_words h.width] using input)
    (by simpa only [kw_words h.width] using modulus) (by omega_using [odd])
    (by simpa only [kw_words h.width] using zero aZero (by decide) (by decide) (by decide))
    (by simpa only [kw_words h.width] using zero 2 (by decide) (by decide) (by decide))
    (by simpa only [kw_words h.width] using zero 3 (by decide) (by decide) (by decide))
  rw [kw_words h.width] at bankProof
  refine WP.mono bankProof fun v ⟨_, Ov, ready, Kv⟩ => ?_
  obtain hv : Ws v B Z n N := hu.afterBank hw Kv Ov
    (by
      intro j hj
      obtain small := (by decide : ∀ j ∈ ([1, 2, aNM] : List Nat), j < 15) j hj
      omega_using [bound, small])
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
  obtain spV : v.gpr .esp = s.gpr .esp := Kv.1 .esp (by decide)
  rw [spV] at Ot
  exact ⟨ht, (OutsS.of_outs Ov).trans Ot, gcd, bezout, lt, Kv.trans (Kt.mono (by decide))⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
