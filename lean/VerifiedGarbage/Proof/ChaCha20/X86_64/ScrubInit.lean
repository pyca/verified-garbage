module

import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Scrub
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.Init
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.ChaCha20.ScrubLocal

/-!
# ChaCha20's `init` and `set_nonce` without secret residue (x86-64)

`vg_chacha20_init` and `vg_chacha20_set_nonce`, each followed by the
clearing of every SSE and caller-saved register
(`Impl.ChaCha20.X86_64.Fn.init`, `setNonce`). Their postconditions read the memory on return only within the
streaming state (`Scrub.stream_congr`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Spec.ChaCha20 VG.Proof.ChaCha20.ScrubLocal

theorem initOut : PostOut (initContract X86_64.abi) (initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 136, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [hi]) (by omega_using [hi]))).symm
    obtain ⟨hk, hr, -⟩ := stream_congr hs
    show keyAt m₂ st = _ ∧ restAt m₂ st = _
    rw [hk, hr]; exact h

theorem setNonceOut : PostOut (setNonceContract X86_64.abi) (setNonceSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [setNonceSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 136, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [hi]) (by omega_using [hi]))).symm
    obtain ⟨hk, hr, -⟩ := stream_congr hs
    show keyAt m₂ st = _ ∧ restAt m₂ st = _
    rw [hk, hr]; exact h

/-- `Spec.ChaCha20.initApi`'s function as emitted (`Impl.ChaCha20.X86_64.Fn.init`)
meets its contract in constant time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed target Impl.ChaCha20.X86_64.Fn.init (initApi.contract X86_64.abi 0) 0 :=
  verifiedScrubbedAll (api := initApi) { code := Impl.ChaCha20.X86_64.Stream.init, verified := Stream.init_verified } .sse initOut

theorem init_spSafeFn : Impl.ChaCha20.X86_64.Fn.init.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (by decide)

/-- `Spec.ChaCha20.setNonceApi`'s function as emitted
(`Impl.ChaCha20.X86_64.Fn.setNonce`) meets its contract in constant time and
returns without secret residue. -/
theorem setNonce_scrubbed :
    VerifiedScrubbed target Impl.ChaCha20.X86_64.Fn.setNonce (setNonceApi.contract X86_64.abi 0) 0 :=
  verifiedScrubbedAll (api := setNonceApi) { code := Impl.ChaCha20.X86_64.Stream.setNonce, verified := Stream.setNonce_verified } .sse
    setNonceOut

theorem setNonce_spSafeFn : Impl.ChaCha20.X86_64.Fn.setNonce.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (by decide)

end VG.Proof.ChaCha20.X86_64.Scrub
