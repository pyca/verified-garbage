module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Wordwise zero checks for DSA validation masks -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- OR the high limbs `1, …, w - 1` (from `x16`, counting `x14` down) into
an accumulator `x9` that already describes the low limb. -/
theorem orWords_ok {s : State} {B : Addr} {Z w e : Nat} {A : Prop}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B (e + 8))
    (h14 : s.gpr .x14 = BitVec.ofNat 64 (w - 1)) (h9 : s.gpr .x9 = 0 ↔ A)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (he : e + 8 * w ≤ Z) :
    WP isa (countLoop .x14 [ld .x3 .x16, .logic .orr .x .x9 .x9 .x3, next .x16]) s fun t =>
      (t.gpr .x9 = 0 ↔ A ∧ ∀ i, 1 ≤ i → i < w → word s.mem B (e + 8 * i) = 0) ∧
      t.mem = s.mem ∧ Keep [.x3, .x4, .x9, .x14, .x16, .x17] s t := by
  refine WP.mono (wp_countdown (N := w - 1) (by omega) (by omega)
    (fun j t => OrInv s B Z (fun j => A ∧ ∀ i < j, word s.mem B (e + 8 + 8 * i) = 0) j t ∧
      t.gpr .x16 = off B (e + 8 + 8 * j))
    (fun j hj t hI _ => orStep_ok (by omega) hj hI.1 hI.2)
    ⟨⟨hs, Keep.refl _ _, rfl, h9.trans ⟨fun h => ⟨h, fun i hi => absurd hi (Nat.not_lt_zero _)⟩, fun h => h.1⟩⟩,
      by rw [h16, Nat.mul_zero, Nat.add_zero]⟩ h14) fun t ⟨hI, _⟩ => ⟨hI.val.trans (and_congr Iff.rfl ⟨fun h i hi1 hi => ?_, fun h i hi => ?_⟩),
      hI.mem, hI.keep⟩
  · have := h (i - 1) (by omega)
    rwa [show e + 8 + 8 * (i - 1) = e + 8 * i by omega] at this
  · have := h (i + 1) (by omega) (by omega)
    rwa [show e + 8 * (i + 1) = e + 8 + 8 * i by omega] at this

end VG.Proof.Dsa.AArch64
