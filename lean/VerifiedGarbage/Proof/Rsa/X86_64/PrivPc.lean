module
public import VerifiedGarbage.Proof.Bignum.X86_64.PcCode
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame

import VerifiedGarbage.Proof.Rsa.X86_64.PrivCrt
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Rsa.Scratch
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-!
# `vg_rsa_private_checked` on x86-64: the call of `vg_rsa_public_precompute`

`r₁` kept in its slot, and `n`'s values written to the frame at `oPre`
(`pc_stage`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

variable {X : List Region}

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- A stack argument past a store to the frame. -/
theorem arg_wo {s : State} (m : Mem) {d : Nat} (v : BitVec 64) (hd : d + 8 ≤ frameBytes) {j : Nat} (hj : j < 14) :
    (m.writeW (off (fb s) d) v).readW (stackArgAddr s j) 64 = m.readW (stackArgAddr s j) 64 := by
  rw [stackArgAddr_fb]
  exact word_wo m (fb s) v (by unfold frameBytes at *; omega_using [hd]) (by unfold frameBytes at *; omega_using [hd])
    (by unfold frameBytes; omega_using [hj])

/-- `2 ⌈k / 8⌉` from `k`. -/
theorem preWords_val {x : BitVec 64} (hx : x.toNat ≤ 1024) :
    (x + BitVec.signExtend 64 (7 : BitVec 32)) >>> 3 + (x + BitVec.signExtend 64 (7 : BitVec 32)) >>> 3 =
      BitVec.ofNat 64 (Spec.Rsa.precomputedWords x.toNat) := by
  rw [sx7]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords, show (7 : BitVec 64).toNat = 7 from rfl]
  omega_using [hx]

/-! ## The call -/

theorem preWords_le {s : State} (hp : PreF X s) : Spec.Rsa.precomputedWords (s.gpr .rcx).toNat ≤ 256 := by
  have := hp.k2; unfold Spec.Rsa.precomputedWords Spec.Rsa.modulusWords; omega_using [this]

/-- A region of the frame at `d`, apart from the return address of a call. -/
theorem ret_disjoint (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    (below (fb s) 8).Disjoint ⟨off (fb s) d, n⟩ := by
  rw [show below (fb s) 8 = ⟨kb s, 8⟩ by simp only [below]; rw [← fb_sub8]; rfl, fb_off]
  exact Offset.base_disjoint _ (by omega_using []) (by unfold frameBytes at h; omega_using [h])

end VG.Proof.Rsa.X86_64
