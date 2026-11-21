module

import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Impl.Dsa.X86_64.Fn
public import VerifiedGarbage.Proof.Dsa.X86_64.ParameterSearchInit
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem

/-!
# DSA's parameter search's `init` on x86-64, without secret residue

`vg_dsa_parameter_search_init`, followed by its cleanup, which clears every
register it may write (`X86_64.Scrub.verifiedScrubbedAll`; it uses no stack). Its postcondition reads the memory on return
only within the state (`wordsAt_congr`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86_64.ParameterSearchInit

open VG.X86_64 VG.X86_64.Scrub

/-- `n` words at `q` are the same in two memories that agree on the `N`
bytes at `q`, `8 * n ≤ N`. -/
theorem wordsAt_congr {m₁ m₂ : Mem} {q : Addr} {k N : Nat} (hk : 8 * k ≤ N) (hN : N < 2 ^ 64)
    (h : ∀ a, Region.Contains ⟨q, N⟩ a 1 → m₁ a = m₂ a) :
    Spec.Rsa.wordsAt m₂ q k = Spec.Rsa.wordsAt m₁ q k :=
  List.map_congr_left fun i hi => Mem.readW_congr fun t ht => by
    have := List.mem_range.mp hi
    rw [Offset.add_add]
    exact (h _ (Offset.contains_base _ (by omega_using [hk, ht, this]) (by omega_using [hk, hN, ht, this]))).symm

theorem initOut : PostOut (Spec.Dsa.parameterInitContract abi) (Spec.Dsa.parameterInitSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨a0, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨a1, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Dsa.parameterInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, Elem.size] at hb
    have hw := wordsAt_congr (k := 4) (by decide) (by decide) hb
    change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _] _ _ _ m₁ r at h
    change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _] _ _ _ m₂ r
    dsimp only [Curry.apply] at h ⊢
    rw [show ArgWord.addr.ofRaw a0 = a0 from rfl, hw]; exact h

theorem init_codeSp : Impl.Dsa.X86_64.ParameterSearch.init.all (fun i => !isa.writesSp i) = true := by sp_safe

/-- `Spec.Dsa.parameterInitApi`'s function as emitted (`Impl.Dsa.X86_64.Fn.parameterInit`) meets its
contract in constant time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed target Impl.Dsa.X86_64.Fn.parameterInit (Spec.Dsa.parameterInitApi.contract X86_64.abi 0) 32 :=
  verifiedScrubbedAll (api := Spec.Dsa.parameterInitApi)
    { code := Impl.Dsa.X86_64.ParameterSearch.init, verified := init_verified, spSafe := init_codeSp } .sse initOut

theorem init_spSafe : Impl.Dsa.X86_64.Fn.parameterInit.all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe init_codeSp

end VG.Proof.Dsa.X86_64.ParameterSearchInit
