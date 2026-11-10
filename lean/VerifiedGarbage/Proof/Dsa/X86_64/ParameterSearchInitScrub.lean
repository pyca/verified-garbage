module

public import VerifiedGarbage.Proof.Dsa.X86_64.ParameterSearchInit
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Dsa.X86_64.ParameterSearchInit
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Mem

/-!
# DSA's parameter search's `init` on x86-64, without secret residue

`vg_dsa_parameter_search_init`, followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.Scrub.withScrub`). Its postcondition reads the memory on return
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
    exact (h _ (Offset.contains_base _ (by omega) (by omega))).symm

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

def initKs : List Nat := keep_for% Spec.Dsa.parameterInitApi.sig 0 Impl.Dsa.X86_64.ParameterSearch.init []

theorem initOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Dsa.parameterInitApi.sig 0 []) Impl.Dsa.X86_64.ParameterSearch.init
      h).any (RScrub.resOkB · 0 initKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of initKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `Spec.Dsa.parameterInitApi` without secret residue. -/
def initReg : Registration Spec.Dsa.parameterInitApi X86_64.target :=
  withScrub { code := Impl.Dsa.X86_64.ParameterSearch.init, verified := init_verified } initOut [] (pubOk_nil _)
    (some ⟨initKs, initOk⟩)

end VG.Proof.Dsa.X86_64.ParameterSearchInit
