module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitVerified
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Init
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitVerified
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Init
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Mem

/-!
# FFDH's `init` functions on x86-64, without secret residue

`vg_ffdh_parameter_generation_init` and `vg_ffdh_key_generation_init`, each
followed by `Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`). Their
postconditions read the memory on return only within the state
(`wordsAt_congr`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Scrub

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

theorem parameterInitOut : PostOut (Spec.Ffdh.parameterInitContract abi) (Spec.Ffdh.parameterInitSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨a0, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨a1, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨a2, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Ffdh.parameterInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, Elem.size] at hb
    have hw := wordsAt_congr (k := 4) (by decide) (by decide) hb
    change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _] _ _ _ m₁ r at h
    change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _] _ _ _ m₂ r
    dsimp only [Curry.apply] at h ⊢
    rw [show ArgWord.addr.ofRaw a0 = a0 from rfl, hw]; exact h

def parameterInitKs : List Nat := keep_for% Spec.Ffdh.parameterInitApi.sig 0 Impl.Ffdh.X86_64.Generation.init []

theorem parameterInitOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Ffdh.parameterInitApi.sig 0 []) Impl.Ffdh.X86_64.Generation.init
      h).any (RScrub.resOkB · 0 parameterInitKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of parameterInitKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `Spec.Ffdh.parameterInitApi` without secret residue. -/
def parameterInitReg : Registration Spec.Ffdh.parameterInitApi X86_64.target :=
  withScrub { code := Impl.Ffdh.X86_64.Generation.init, verified := Generation.init_verified } parameterInitOut [] (pubOk_nil _)
    (some ⟨parameterInitKs, parameterInitOk⟩)

theorem keyInitOut : PostOut (Spec.Ffdh.keyInitContract abi) (Spec.Ffdh.keyInitSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨a0, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨a1, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Ffdh.keyInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, Elem.size] at hb
    have hw := wordsAt_congr (k := 4) (by decide) (by decide) hb
    change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _] _ _ _ m₁ r at h
    change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _] _ _ _ m₂ r
    dsimp only [Curry.apply] at h ⊢
    rw [show ArgWord.addr.ofRaw a0 = a0 from rfl, hw]; exact h

def keyInitKs : List Nat := keep_for% Spec.Ffdh.keyInitApi.sig 0 Impl.Ffdh.X86_64.KeyGeneration.init []

theorem keyInitOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Ffdh.keyInitApi.sig 0 []) Impl.Ffdh.X86_64.KeyGeneration.init
      h).any (RScrub.resOkB · 0 keyInitKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of keyInitKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `Spec.Ffdh.keyInitApi` without secret residue. -/
def keyInitReg : Registration Spec.Ffdh.keyInitApi X86_64.target :=
  withScrub { code := Impl.Ffdh.X86_64.KeyGeneration.init, verified := KeyGeneration.init_verified } keyInitOut [] (pubOk_nil _)
    (some ⟨keyInitKs, keyInitOk⟩)

end VG.Proof.Ffdh.X86_64.Scrub
