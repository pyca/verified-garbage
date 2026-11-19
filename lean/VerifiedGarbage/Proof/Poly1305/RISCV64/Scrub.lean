module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Poly1305.Scratch
import VerifiedGarbage.Proof.Poly1305.BlocksScratch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Poly1305.RISCV64.Init
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Poly1305.Contract
public import VerifiedGarbage.Proof.Poly1305.Contract
public import VerifiedGarbage.Impl.Poly1305.RISCV64
public import VerifiedGarbage.TCB.RISCV64.Target

/-! ### `Poly1305.RISCV64.Shared`, which only this module used -/

section

/-!
# Poly1305 on RISC-V: the shared contracts

The proofs are written against per-target contracts
(`Proof/Poly1305/RISCV64/Init.lean`); these theorems move them to the
shared contracts, which the artifacts are emitted with. No function uses
the stack.
-/

@[expose] public section

namespace VG.Proof.Poly1305.RISCV64.Shared

theorem init :
    Verified RISCV64.target Impl.Poly1305.RISCV64.init (Spec.Poly1305.initContract RISCV64.abi) :=
  init_verified.of_implies (by
    contract_implies [Spec.Poly1305.initContract, Spec.Poly1305.initSig, Proof.Poly1305.initRISCV64,
      RISCV64.abi, RISCV64.argRegs] [initSat] using initSat)

theorem update :
    Verified RISCV64.target Impl.Poly1305.RISCV64.update (Spec.Poly1305.updateContract RISCV64.abi) :=
  update_verified.of_implies
    { pre := by
        sig_implies_pre [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig,
          Spec.Poly1305.updatePost, Proof.Poly1305.updateRISCV64, RISCV64.abi, RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig,
          Spec.Poly1305.updatePost, RISCV64.abi, RISCV64.argRegs]
        intro key msg hb hc
        exact h key msg hb (count_mod hc)
      pub := by
        sig_implies_pub [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig,
          Spec.Poly1305.updatePost, Proof.Poly1305.updateRISCV64, RISCV64.abi, RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig,
          Spec.Poly1305.updatePost, RISCV64.abi, RISCV64.argRegs, updateSat] [updateSat]
          using updateSat }

theorem finalize :
    Verified RISCV64.target Impl.Poly1305.RISCV64.finalize (Spec.Poly1305.finalizeContract RISCV64.abi) :=
  finalize_verified.of_implies
    { pre := by
        sig_implies_pre [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
          Spec.Poly1305.finalizePost, Proof.Poly1305.finalizeRISCV64, RISCV64.abi, RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
          Spec.Poly1305.finalizePost, RISCV64.abi, RISCV64.argRegs]
        intro key msg hb hc
        exact h key msg hb (count_mod hc)
      pub := by
        sig_implies_pub [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
          Spec.Poly1305.finalizePost, Proof.Poly1305.finalizeRISCV64, RISCV64.abi, RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
          Spec.Poly1305.finalizePost, RISCV64.abi, RISCV64.argRegs, finalizeSat] [finalizeSat]
          using finalizeSat }

end VG.Proof.Poly1305.RISCV64.Shared

end

end

/-!
# Poly1305 on RISC-V, without secret residue

`vg_poly1305_init`, `vg_poly1305_update` and `vg_poly1305_finalize`, each followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.scrubOf`), which clears the caller-saved registers and the
stack its frames used. Their postconditions read the memory on return only
within the state and the tag (`RISCV64.Scrub.PostOut`), as on x86-64 (`Proof/Poly1305/X86_64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.RISCV64.Scrub

open VG.Spec.Poly1305 VG.RISCV64 VG.RISCV64.Scrub VG.Proof.Poly1305

/-! ## Postconditions -/

theorem agreeBuf {m₁ m₂ : Mem} {p : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := fun i hi =>
  (h _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hn, hi]))).symm

theorem initOut (stack : Nat) : PostOut (initContract RISCV64.abi stack) (initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (Nat.succ.inj hlen)
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj (Nat.succ.inj hlen))
    simp only [initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    exact repr_congr (fun i hi => agreeBuf (n := 16 * Elem.size .u64) (by decide) hb.1 i
      (by simp only [Elem.size]; omega_using [hi])) h

theorem updateOut (stack : Nat) : PostOut (updateContract RISCV64.abi stack) (updateSig.retBits 64) :=
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

theorem finalizeOut (stack : Nat) : PostOut (finalizeContract RISCV64.abi stack) (finalizeSig.retBits 64) :=
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

/-! ## The registrations -/

/-- `Spec.Poly1305.initApi`. -/
def initReg : Registration Spec.Poly1305.initApi RISCV64.target :=
  scrubOf {
      code := Impl.Poly1305.RISCV64.init
      verified := Proof.Poly1305.RISCV64.Shared.init }
    (initOut _)

/-- `Spec.Poly1305.updateApi`. -/
def updateReg : Registration Spec.Poly1305.updateApi RISCV64.target :=
  scrubOf {
      code := Impl.Poly1305.RISCV64.update
      verified := Proof.Poly1305.RISCV64.Shared.update }
    (updateOut _)

/-- `Spec.Poly1305.finalizeApi`. -/
def finalizeReg : Registration Spec.Poly1305.finalizeApi RISCV64.target :=
  scrubOf {
      code := Impl.Poly1305.RISCV64.finalize
      verified := Proof.Poly1305.RISCV64.Shared.finalize }
    (finalizeOut _)

end VG.Proof.Poly1305.RISCV64.Scrub
