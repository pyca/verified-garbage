module

import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Fn
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KeyInit
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem

/-!
# RSA key generation's `init` on x86-64, without secret residue

`vg_rsa_generate_init`, followed by its cleanup, which clears every
register it may write (`X86_64.Scrub.verifiedScrubbedAll`; it uses no stack). Its postcondition reads the memory on return
only within the state (`wordsAt_congr`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.KeyInit

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

theorem initOut : PostOut (Spec.RsaKeyGen.keyInitContract abi) (Spec.RsaKeyGen.keyInitSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨a0, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨a1, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨a2, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨a3, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.RsaKeyGen.keyInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size] at hb
    have h7 := wordsAt_congr (k := 7) (by decide) (by decide) hb.1
    have h6 := wordsAt_congr (k := 6) (by decide) (by decide) hb.1
    have hB : Spec.Rsa.bytesAt m₂ (a0 + 48) 8 = Spec.Rsa.bytesAt m₁ (a0 + 48) 8 := by
      simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      have := List.mem_range.mp hi
      rw [show (a0 + 48 : Addr) = a0 + BitVec.ofNat 64 48 from rfl, Offset.add_add]
      exact (hb.1 _ (Offset.contains_base _ (by omega_using [this]) (by omega_using [this]))).symm
    change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _] _ _ _ m₁ r at h
    change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _] _ _ _ m₂ r
    dsimp only [Curry.apply] at h ⊢
    rw [show ArgWord.addr.ofRaw a0 = a0 from rfl, h7, h6, hB]; exact h

theorem init_codeSp : Impl.RsaKeyGen.X86_64.KeyInit.init.all (fun i => !isa.writesSp i) = true := by sp_safe

/-- `Spec.RsaKeyGen.keyInitApi`'s function as emitted (`Impl.RsaKeyGen.X86_64.Fn.keyInit`) meets its
contract in constant time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed target Impl.RsaKeyGen.X86_64.Fn.keyInit (Spec.RsaKeyGen.keyInitApi.contract X86_64.abi 0) 32 :=
  verifiedScrubbedAll (api := Spec.RsaKeyGen.keyInitApi)
    { code := Impl.RsaKeyGen.X86_64.KeyInit.init, verified := init_verified, spSafe := init_codeSp } .sse initOut

theorem init_spSafe : Impl.RsaKeyGen.X86_64.Fn.keyInit.all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe init_codeSp

end VG.Proof.RsaKeyGen.X86_64.KeyInit
