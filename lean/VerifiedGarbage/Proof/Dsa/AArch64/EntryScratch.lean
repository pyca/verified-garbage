module
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp

import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Contract

/-! # Loading caller scratch from the AAPCS64 stack argument area -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem entryScratch_ok {s : State} {sp B : Addr} (j : Nat) (hj : j < 4096) (hsp : s.sp = sp)
    (hr : InRegions (s.rd ++ s.wr) (off sp (8 * j)) 8) (hb : word s.mem sp (8 * j) = B) :
    WP isa (.block [.ldrSp .x11 (8 * j)]) s fun t =>
      t.gpr .x11 = B ∧ t.mem = s.mem ∧ Keep [.x11] s t := by
  refine WP.mono (WP.keep [.x11] (Q := fun t => t.gpr .x11 = B ∧ t.mem = s.mem)
    ?_ rfl rfl rfl) fun t ⟨⟨hp, hm⟩, hk⟩ => ⟨hp, hm, hk⟩
  have he : 8 * j % 8 = 0 ∧ 8 * j < 32768 := ⟨by omega, by omega⟩
  brun [exec_ldrSp_x', hsp, he, hr, hb]

end VG.Proof.Dsa.AArch64
