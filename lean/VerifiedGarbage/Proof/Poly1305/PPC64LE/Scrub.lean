module

public import VerifiedGarbage.Impl.Poly1305.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Shared
public import VerifiedGarbage.Spec.Poly1305.Contract
public import VerifiedGarbage.Proof.Poly1305.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Poly1305.Scratch
import VerifiedGarbage.Proof.Poly1305.BlocksScratch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Poly1305 on PPC64LE, without secret residue

`vg_poly1305_init`, `vg_poly1305_update` and `vg_poly1305_finalize`, each
followed by `Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.verifiedScrubbedAll`), which
clears the volatile registers and the stack its frames used: `update` and
`finalize` keep their working space in a 160-byte frame they do not wipe
themselves (`withStackScratch`). Their postconditions read the memory on
return only within the state and the tag, by RISC-V's proofs
(`Proof/Poly1305/RISCV64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.PPC64LE.Scrub

open VG.Spec.Poly1305 VG.PPC64LE VG.PPC64LE.Scrub VG.Proof.Poly1305

/-! ## Postconditions -/

theorem agreeBuf {m₁ m₂ : Mem} {p : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := fun i hi =>
  (h _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hn, hi]))).symm

theorem initOut (stack : Nat) : PostOut (initContract PPC64LE.abi stack) (initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (Nat.succ.inj hlen)
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj (Nat.succ.inj hlen))
    simp only [initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    exact repr_congr (fun i hi => agreeBuf (n := 16 * Elem.size .u64) (by decide) hb.1 i
      (by simp only [Elem.size]; omega_using [hi])) h

theorem updateOut (stack : Nat) : PostOut (updateContract PPC64LE.abi stack) (updateSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ct, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [updateSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    intro key msg hbf hc
    exact buffered_congr (fun i hi => agreeBuf (n := 16 * Elem.size .u64) (by decide) hb.1 i
      (by simp only [Elem.size]; omega_using [hi])) (h key msg hbf hc)

theorem finalizeOut (stack : Nat) : PostOut (finalizeContract PPC64LE.abi stack) (finalizeSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ct, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ot, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [finalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    intro key msg hbf hc
    show bytesAt m₂ ot 16 = _
    rw [bytesAt_congr' fun i hi => agreeBuf (n := 16 * Elem.size .u8) (by decide) hb.2 i
      (by simp only [Elem.size]; omega_using [hi])]
    exact h key msg hbf hc

/-! ## The functions as emitted -/

/-- `vg_poly1305_init` as emitted (`Impl.Poly1305.PPC64LE.Fn.init`) meets its
contract in constant time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Poly1305.PPC64LE.Fn.init
      (Spec.Poly1305.initContract PPC64LE.abi) 0 :=
  verifiedScrubbedAll (api := Spec.Poly1305.initApi) {
      code := Impl.Poly1305.PPC64LE.init
      verified := Proof.Poly1305.PPC64LE.Shared.init }
    0 ⟨false, false, [.r5, .r6, .r7, .r8], false, []⟩
    (initOut _)
    (by dsimp only; lit_decide)

/-- `vg_poly1305_update` as emitted (`Impl.Poly1305.PPC64LE.Fn.update`) meets its
contract in constant time and returns without secret residue. -/
theorem update_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Poly1305.PPC64LE.Fn.update
      (Spec.Poly1305.updateContract PPC64LE.abi 160) 0 :=
  verifiedScrubbedAll (api := Spec.Poly1305.updateApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 160 .r7 Impl.Poly1305.PPC64LE.update
      verified := Proof.Poly1305.PPC64LE.Shared.update }
    160 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (updateOut _)
    (by dsimp only; lit_decide)

/-- `vg_poly1305_finalize` as emitted (`Impl.Poly1305.PPC64LE.Fn.finalize`) meets
its contract in constant time and returns without secret residue. -/
theorem finalize_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Poly1305.PPC64LE.Fn.finalize
      (Spec.Poly1305.finalizeContract PPC64LE.abi 160) 0 :=
  verifiedScrubbedAll (api := Spec.Poly1305.finalizeApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 160 .r6 Impl.Poly1305.PPC64LE.finalize
      verified := Proof.Poly1305.PPC64LE.Shared.finalize }
    160 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (finalizeOut _)
    (by dsimp only; lit_decide)

end VG.Proof.Poly1305.PPC64LE.Scrub
