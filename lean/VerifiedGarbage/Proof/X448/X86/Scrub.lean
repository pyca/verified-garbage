module

public import VerifiedGarbage.Spec.X448.Contract
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.X448.X86.Base
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.X448.X86.Exchange
public import VerifiedGarbage.Proof.X448.X86.Base
public import VerifiedGarbage.Proof.Ed448.CombFacts
import VerifiedGarbage.Proof.X448.X86.Lit
import VerifiedGarbage.Proof.X448.X86.BaseLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Spec.X448.Contract
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Impl.X448.X86.Base
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.X448.X86.Exchange
meta import VerifiedGarbage.Proof.X448.X86.Base
meta import VerifiedGarbage.Proof.Ed448.CombFacts
meta import VerifiedGarbage.Proof.X448.X86.Lit
meta import VerifiedGarbage.Proof.X448.X86.BaseLit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# X448 on x86, without secret residue

`vg_x448_exchange` and `vg_x448_base` have frames and call other
functions. Each as emitted (`Impl.X448.X86.Fn`) is followed by the zeroing of
the stack its contract reserves below `esp`, which its frames and calls use,
then by `Impl.Scrub.X86.tail`, which clears the registers a callee may change
but the result's bits, the flags and `xmm0`–`xmm7`, and returns without
secret residue (`X86.Scrub.verifiedScrubbedF`).
Their postconditions read the memory on return only within `out`
(`X86.Scrub.PostOut`, by `postOut_of_local`). What the scrub needs of the
code (its stack use within those bytes, no indirect call, no MMX
instruction) is one Boolean, `X86.Scrub.scrubFSide`, proved by evaluating
the code once (`lit_decide`) when this module is built.
-/

@[expose] public section

namespace VG.Proof.X448.X86.Scrub

open VG.X86 VG.X86.Scrub

/-! ## Postconditions -/

/-- The 56 bytes at `o` read the memory only within `⟨o, n⟩`, for `56 ≤ n`. -/
theorem bytesAt_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} (hn : 56 ≤ n)
    (h : ∀ a, Region.Contains ⟨o, n⟩ a 1 → m₁ a = m₂ a) :
    Spec.X448.bytesAt m₂ o 56 = Spec.X448.bytesAt m₁ o 56 := by
  simp only [Spec.X448.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact (h _ (Offset.contains_base _ (by omega_using [hn, this]) (by omega_using [this]))).symm

theorem baseOut (cs : List (String × List (BitVec 64))) (stack : Nat) :
    PostOut (Spec.X448.x448BaseContract (X86.abi.withConsts cs) stack)
      (Spec.X448.x448BaseSig.retBits 32) :=
  postOut_of_local (leak := none) (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨o, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.X448.x448BaseSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    show Spec.X448.bytesAt m₂ o 56 = _
    rw [bytesAt_of (by simp only [Elem.size]; omega_using []) hb.1]; exact h

theorem exchangeOut (stack : Nat) :
    PostOut (Spec.X448.exchangeContract X86.abi stack) (Spec.X448.exchangeSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨o, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨u, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.X448.exchangeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    show Spec.X448.bytesAt m₂ o 56 = _ ∧ _
    rw [bytesAt_of (by simp only [Elem.size]; omega_using []) hb.1]; exact h

/-! ## The functions as emitted -/

/-- `vg_x448_exchange`. -/
theorem exchange_scrubbed :
    VerifiedScrubbed target Impl.X448.X86.Fn.exchange (Spec.X448.exchangeContract X86.abi 40) 32 :=
  verifiedScrubbedF (api := Spec.X448.exchangeApi)
    { code := Impl.Xdh.X86.exchange "vg_x448" Impl.X448.X86.x448 56
      verified := Proof.X448.X86.Exchange.exchange_verified }
    (exchangeOut _)

/-- `vg_x448_base`. -/
theorem base_scrubbed :
    VerifiedScrubbed target Impl.X448.X86.Fn.base (Spec.X448.x448BaseContract X86.abi 20) 0 :=
  verifiedScrubbedF (api := Spec.X448.x448BaseApi)
    { code := Impl.X448.X86.x448Base
      verified := Proof.X448.X86.x448Base_verified Proof.Ed448.baseCombU_ok }
    (baseOut [] _)

end VG.Proof.X448.X86.Scrub
