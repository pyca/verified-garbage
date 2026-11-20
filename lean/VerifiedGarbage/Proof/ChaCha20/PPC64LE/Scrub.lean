module

public import VerifiedGarbage.Impl.ChaCha20.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Stream.ApplyCT
public import VerifiedGarbage.Spec.ChaCha20.Contract
import VerifiedGarbage.Proof.ChaCha20.ScrubLocal
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ChaCha20 on PPC64LE, without secret residue

`vg_chacha20_init`, `vg_chacha20_set_nonce` and `vg_chacha20_apply`, each
followed by `Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.verifiedScrubbed`), which
clears the volatile registers they write. None of them has a frame, so no
stack is wiped. Their postconditions read the memory on return only within
the streaming state and the data, by RISC-V's proofs
(`Proof/ChaCha20/RISCV64/Scrub.lean`, `Proof/ChaCha20/ScrubLocal.lean`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub VG.Spec.ChaCha20 VG.Proof.ChaCha20.ScrubLocal

/-! ## Postconditions -/

theorem initOut : PostOut (initContract PPC64LE.abi) (initSig.retBits 64) :=
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

theorem setNonceOut : PostOut (setNonceContract PPC64LE.abi) (setNonceSig.retBits 64) :=
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

theorem applyOut (stack : Nat) : PostOut (applyContract PPC64LE.abi stack) (applySig.retBits 64) :=
  postOut_of_local (post := applyPost 64) ScrubAbi.plain (applyPost_out 64 rfl)

/-! ## The functions as emitted -/

/-- `vg_chacha20_init` as emitted (`Impl.ChaCha20.PPC64LE.Fn.init`) meets its
contract in constant time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.ChaCha20.PPC64LE.Fn.init
      (Spec.ChaCha20.initContract PPC64LE.abi) 0 :=
  verifiedScrubbed (api := Spec.ChaCha20.initApi) {
      code := Impl.ChaCha20.PPC64LE.Stream.init
      verified := Proof.ChaCha20.PPC64LE.Stream.init_verified }
    0 ⟨false, false, [.r4, .r9, .r10, .r11, .r12], false, []⟩
    initOut
    (by dsimp only; lit_decide)

/-- `vg_chacha20_set_nonce` as emitted (`Impl.ChaCha20.PPC64LE.Fn.setNonce`) meets
its contract in constant time and returns without secret residue. -/
theorem setNonce_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.ChaCha20.PPC64LE.Fn.setNonce
      (Spec.ChaCha20.setNonceContract PPC64LE.abi) 0 :=
  verifiedScrubbed (api := Spec.ChaCha20.setNonceApi) {
      code := Impl.ChaCha20.PPC64LE.Stream.setNonce
      verified := Proof.ChaCha20.PPC64LE.Stream.setNonce_verified }
    0 ⟨false, false, [.r9, .r10, .r11, .r12], false, []⟩
    setNonceOut
    (by dsimp only; lit_decide)

/-- `vg_chacha20_apply` as emitted (`Impl.ChaCha20.PPC64LE.Fn.apply`) meets its
contract in constant time and returns without secret residue.
`Spec.ChaCha20.applyApi`: it calls the block function and
`vg_chacha20_xor`, which write every volatile register. -/
theorem apply_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.ChaCha20.PPC64LE.Fn.apply
      (Spec.ChaCha20.applyContract PPC64LE.abi) 32 :=
  verifiedScrubbed (api := Spec.ChaCha20.applyApi) {
      code := Impl.ChaCha20.PPC64LE.Stream.apply
      verified := Proof.ChaCha20.PPC64LE.Stream.apply_verified }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9,
       .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (applyOut _)
    (by dsimp only; lit_decide)

end VG.Proof.ChaCha20.PPC64LE.Scrub
