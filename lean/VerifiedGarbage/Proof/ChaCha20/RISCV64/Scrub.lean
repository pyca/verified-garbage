module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Xor
public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Stream.Init
public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Stream.ApplyCT
import VerifiedGarbage.Proof.ChaCha20.ScrubLocal
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ChaCha20 on RISC-V, without secret residue

`vg_chacha20_init`, `vg_chacha20_set_nonce` and `vg_chacha20_apply`, each followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.withScrub`), which clears the caller-saved registers and the
stack its frames used. Their postconditions read the memory on return only
within the streaming state and the data (`RISCV64.Scrub.PostOut`), as on x86-64 (`Proof/ChaCha20/X86_64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub VG.Spec.ChaCha20 VG.Proof.ChaCha20.ScrubLocal

/-! ## Postconditions -/

theorem initOut : PostOut (initContract RISCV64.abi) (initSig.retBits 64) :=
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

theorem setNonceOut : PostOut (setNonceContract RISCV64.abi) (setNonceSig.retBits 64) :=
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

theorem applyOut (stack : Nat) : PostOut (applyContract RISCV64.abi stack) (applySig.retBits 64) := by
  unfold applyContract
  refine postOut_of_local ScrubAbi.plain ?_
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
  simp only [applySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  have hs : ∀ i < 136, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
    (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [hi]) (by omega_using [hi]))).symm
  have hd : Spec.ChaCha20.bytesAt m₂ dt ln.toNat = Spec.ChaCha20.bytesAt m₁ dt ln.toNat := by
    simp only [Spec.ChaCha20.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    exact (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [this]) (by omega_using [this]))).symm
  obtain ⟨k, rs, -⟩ := stream_congr hs
  show keyAt m₂ st = _ ∧ _
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [k]; exact h1, ?_⟩
  have e64 : (ArgWord.int RISCV64.abi.ptrBits).ofRaw ln = ln := BitVec.setWidth_eq ln
  rw [e64] at h2 ⊢
  split at h2 <;> split <;> rename_i h₁ h₂
  · obtain ⟨a, b, c⟩ := h2; exact ⟨a, hd.trans b, rs.trans c⟩
  · exact absurd h₁ h₂
  · exact absurd h₂ h₁
  · obtain ⟨a, b, c⟩ := h2; exact ⟨a, hd.trans b, rs.trans c⟩

/-! ## The registrations -/

/-- `Spec.ChaCha20.initApi`. -/
def initReg : Registration Spec.ChaCha20.initApi RISCV64.target :=
  withScrub {
      code := Impl.ChaCha20.RISCV64.Stream.init
      verified := Proof.ChaCha20.RISCV64.Stream.init_verified }
    (initOut)

/-- `Spec.ChaCha20.setNonceApi`. -/
def setNonceReg : Registration Spec.ChaCha20.setNonceApi RISCV64.target :=
  withScrub {
      code := Impl.ChaCha20.RISCV64.Stream.setNonce
      verified := Proof.ChaCha20.RISCV64.Stream.setNonce_verified }
    (setNonceOut)

/-- `Spec.ChaCha20.applyApi`. -/
def applyReg : Registration Spec.ChaCha20.applyApi RISCV64.target :=
  withScrub {
      code := Impl.ChaCha20.RISCV64.Stream.apply
      verified := Proof.ChaCha20.RISCV64.Stream.apply_verified }
    (applyOut _)

end VG.Proof.ChaCha20.RISCV64.Scrub
