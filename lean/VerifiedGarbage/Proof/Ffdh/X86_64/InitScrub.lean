module

import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFn
public import VerifiedGarbage.Impl.Ffdh.X86_64.Fn
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitVerified
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Init
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem

/-!
# FFDH's `init` functions on x86-64, without secret residue

`vg_ffdh_parameter_generation_init` and `vg_ffdh_key_generation_init`, each
followed by its cleanup, which clears every register it may write
(`X86_64.Scrub.verifiedScrubbedAll`; they use no stack). Their
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

theorem parameterInit_codeSp : Impl.Ffdh.X86_64.Generation.init.all (fun i => !isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Ffdh.parameterInitApi`'s function as emitted (`Impl.Ffdh.X86_64.Fn.parameterInit`) meets its
contract in constant time and returns without secret residue. -/
theorem parameterInit_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.X86_64.Fn.parameterInit (Spec.Ffdh.parameterInitApi.contract X86_64.abi 0) 32 :=
  verifiedScrubbedAll (api := Spec.Ffdh.parameterInitApi)
    { code := Impl.Ffdh.X86_64.Generation.init, verified := Generation.init_verified, spSafe := parameterInit_codeSp }
    .sse parameterInitOut

theorem parameterInit_spSafe : Impl.Ffdh.X86_64.Fn.parameterInit.all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe parameterInit_codeSp

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

theorem keyInit_codeSp : Impl.Ffdh.X86_64.KeyGeneration.init.all (fun i => !isa.writesSp i) = true := by sp_safe

/-- `Spec.Ffdh.keyInitApi`'s function as emitted (`Impl.Ffdh.X86_64.Fn.keyInit`) meets its contract in
constant time and returns without secret residue. -/
theorem keyInit_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.X86_64.Fn.keyInit (Spec.Ffdh.keyInitApi.contract X86_64.abi 0) 32 :=
  verifiedScrubbedAll (api := Spec.Ffdh.keyInitApi)
    { code := Impl.Ffdh.X86_64.KeyGeneration.init, verified := KeyGeneration.init_verified, spSafe := keyInit_codeSp }
    .sse keyInitOut

theorem keyInit_spSafe : Impl.Ffdh.X86_64.Fn.keyInit.all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe keyInit_codeSp

end VG.Proof.Ffdh.X86_64.Scrub
