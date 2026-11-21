module

public import VerifiedGarbage.Spec.X25519.Contract
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Impl.X25519.X86.Base
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.X25519.X86.Exchange
public import VerifiedGarbage.Proof.X25519.X86.Base.Verified
import VerifiedGarbage.Proof.X25519.X86.Lit
import VerifiedGarbage.Proof.X25519.X86.Base.Lit
import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
import VerifiedGarbage.Proof.Ed25519.X86.CombLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Spec.X25519.Contract
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Impl.X25519.X86.Base
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.X25519.X86.Exchange
meta import VerifiedGarbage.Proof.X25519.X86.Base.Verified
meta import VerifiedGarbage.Proof.X25519.X86.Lit
meta import VerifiedGarbage.Proof.X25519.X86.Base.Lit
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86.CombLit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# X25519 on x86, without secret residue

`vg_x25519_exchange` and `vg_x25519_base` have frames and call other
functions. Each as emitted (`Impl.X25519.X86.Fn`) is followed by the zeroing of
the stack its contract reserves below `esp`, which its frames and calls use,
then by `Impl.Scrub.X86.tail`, which clears the registers a callee may change
but the result's bits, the flags and `xmm0`–`xmm7`, and returns without
secret residue (`X86.Scrub.verifiedScrubbedAll`).
Their postconditions read the memory on return only within `out`
(`X86.Scrub.PostOut`, by `postOut_of_local`). What the scrub needs of the
code (its stack use within those bytes, no indirect call, no MMX
instruction) is one Boolean, `X86.Scrub.scrubFSide`, proved by evaluating
the code once (`lit_decide`) when this module is built.
-/

@[expose] public section

namespace VG.Proof.X25519.X86.Scrub

open VG.X86 VG.X86.Scrub

/-! ## Postconditions -/

/-- The 32 bytes at `o` read the memory only within `⟨o, n⟩`, for `32 ≤ n`. -/
theorem bytesAt_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} (hn : 32 ≤ n)
    (h : ∀ a, Region.Contains ⟨o, n⟩ a 1 → m₁ a = m₂ a) :
    Spec.X25519.bytesAt m₂ o 32 = Spec.X25519.bytesAt m₁ o 32 := by
  simp only [Spec.X25519.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact (h _ (Offset.contains_base _ (by omega_using [hn, this]) (by omega_using [this]))).symm

theorem baseOut (cs : List (String × List (BitVec 64))) (stack : Nat) :
    PostOut (Spec.X25519.x25519BaseContract (X86.abi.withConsts cs) stack)
      (Spec.X25519.x25519BaseSig.retBits 32) :=
  postOut_of_local (leak := none) (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨o, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.X25519.x25519BaseSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    show Spec.X25519.bytesAt m₂ o 32 = _
    rw [bytesAt_of (by simp only [Elem.size]; omega_using []) hb.1]; exact h

theorem exchangeOut (stack : Nat) :
    PostOut (Spec.X25519.exchangeContract X86.abi stack) (Spec.X25519.exchangeSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
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

/-! ## The functions as emitted -/

/-- `vg_x25519_exchange`. -/
theorem exchange_scrubbed :
    VerifiedScrubbed target Impl.X25519.X86.Fn.exchange (Spec.X25519.exchangeContract X86.abi 28) 32 :=
  verifiedScrubbedAll (api := Spec.X25519.exchangeApi)
    { code := Impl.Xdh.X86.exchange "vg_x25519" Impl.X25519.X86.x25519 32
      verified := Proof.X25519.X86.Exchange.exchange_verified }
    (exchangeOut _)

/-- `vg_x25519_base`. -/
theorem base_scrubbed :
    VerifiedScrubbed target Impl.X25519.X86.Fn.base
      (Spec.X25519.x25519BaseContract (X86.abi.withConsts Impl.Ed25519.X86.combConsts) 8) 0 :=
  verifiedScrubbedAll (api := Spec.X25519.x25519BaseApi)
    { code := Impl.X25519.X86.Base.x25519Base
      verified := Proof.X25519.X86.Base.x25519Base_verified }
    (baseOut Impl.Ed25519.X86.combConsts _)

end VG.Proof.X25519.X86.Scrub
