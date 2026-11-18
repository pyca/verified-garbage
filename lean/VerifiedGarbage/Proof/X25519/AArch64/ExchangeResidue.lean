module

public import VerifiedGarbage.Impl.Residue.AArch64
public meta import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.Proof.Ed25519.AArch64.DivstepSound
public meta import VerifiedGarbage.Proof.Ed25519.AArch64.DivstepSound
public import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Verified
public meta import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Verified
public import VerifiedGarbage.Proof.X25519.AArch64.Base.Verified
public meta import VerifiedGarbage.Proof.X25519.AArch64.Base.Verified
public import VerifiedGarbage.Proof.X25519.AArch64.Exchange
public meta import VerifiedGarbage.Proof.X25519.AArch64.Exchange
public import VerifiedGarbage.TCB.AArch64.Residue
public meta import VerifiedGarbage.TCB.AArch64.Residue
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# X25519 on AArch64 returns without secret residue

`vg_x25519_exchange` runs the ladder in a 16-byte frame, which the analysis of
the window's bytes (`rtaintG`) finds may differ between the two runs on
return. It clears the registers the ladder leaves secret, the upper half of
`x0` (`withRet 32`) and the flags, then zeroes that granule
(`withScrubG 16 [0]`). Its postcondition reads the memory on return only
within `out` (`exchangePost_local`).
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.ExchangeResidue

open VG VG.AArch64 VG.Impl.Residue.AArch64 VG.AArch64.RTaintG

/-! ## The postcondition reads only `out` -/

theorem bytesAt_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} (hn : 32 ≤ n)
    (h : ∀ a, Region.Contains ⟨o, n⟩ a 1 → m₁ a = m₂ a) :
    Spec.X25519.bytesAt m₂ o 32 = Spec.X25519.bytesAt m₁ o 32 := by
  simp only [Spec.X25519.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact (h _ (Offset.contains_base _ (by omega_using [hn, this]) (by omega_using [this]))).symm

theorem exchangeOk : RTaintF.ScrubOk (Spec.X25519.exchangeContract AArch64.abi 16) 16 :=
  RTaintF.scrubOk_regs (sig := Spec.X25519.exchangeSig) (by decide) (by decide) (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨o, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨u, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.X25519.exchangeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    show Spec.X25519.bytesAt m₂ o 32 = _ ∧ _
    rw [bytesAt_of (by simp only [Elem.size]; omega_using []) hb.1]; exact h

/-- `vg_x25519_exchange`, before its granules [0] are zeroed. -/
abbrev exchangeBase : Prog isa :=
  withRet 32 (withClears [.x3, .x4, .x5, .x6, .x7, .x8, .x10, .x12, .x13, .x14, .x15, .x16, .x17]
    [] (some .x3)
    (Impl.Xdh.AArch64.exchange "vg_x25519" Impl.X25519.AArch64.AltLadder.x25519 32))

theorem exchangeBase_verified : Verified AArch64.target exchangeBase (Spec.X25519.exchangeContract AArch64.abi 16) :=
  RTaintF.Verified.withRet (Clears.Verified.withClears (Proof.X25519.AArch64.Exchange.exchange_verified) (by decide))

theorem exchangeScrubOk : RTaintF.ScrubOk (Spec.X25519.exchangeContract AArch64.abi 16) 16 :=
  exchangeOk

/-- `vg_x25519_exchange`. -/
abbrev exchangeCode : Prog isa := withScrubG 16 [0] exchangeBase

theorem exchangeCode_verified : Verified AArch64.target exchangeCode (Spec.X25519.exchangeContract AArch64.abi 16) :=
  RTaintG.Verified.withScrubG exchangeBase_verified ⟨by decide, by decide, by decide⟩ (by decide) exchangeScrubOk

theorem exchangeCode_noResidue : NoResidue exchangeCode (Spec.X25519.exchangeContract AArch64.abi 16) 32 :=
  noResidue_withScrubG (P₀ := 0) exchangeBase_verified ⟨by decide, by decide, by decide⟩ exchangeScrubOk.sp
    (fun _ _ _ _ _ hb => by simp at hb) ⟨_, by taint_decide_ct⟩

end VG.Proof.X25519.AArch64.ExchangeResidue
