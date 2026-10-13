module

public import VerifiedGarbage.Proof.Dsa.AArch64.EntryFieldsFrame
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Loading the caller's scratch pointer from the stack -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem entryScratch_ok {s : State} {sp B : Addr} {o : Nat} (ho : o % 8 = 0 ∧ o < 32768) (hsp : s.sp = sp)
    (hr : InRegions (s.rd ++ s.wr) (off sp o) 8) (hb : word s.mem sp o = B) :
    WP isa (.block [.ldrSp .x8 o]) s fun t =>
      t.gpr .x8 = B ∧ t.mem = s.mem ∧ Keep [.x8] s t := by
  refine WP.mono (WP.keep [.x8] (Q := fun t => t.gpr .x8 = B ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨hp, hm⟩, hk⟩ => ⟨hp, hm, hk⟩
  rw [← hsp] at hr hb
  brun [exec_ldrSp_arg ho hr]
  exact hb

theorem entry_stack_frame {mem mem' : Mem} {B sp : Addr} {Z o n d : Nat}
    (hf : Outside B o n mem mem') (hhi : o + n ≤ Z)
    (hsep : ∀ i < 8, Z ≤ ofs B (off sp d + BitVec.ofNat 64 i)) : word mem' sp d = word mem sp d := by
  apply Mem.readW_congr
  intro i hi
  exact hf _ (Or.inr (Nat.le_trans hhi (hsep i hi)))

end VG.Proof.Dsa.AArch64
