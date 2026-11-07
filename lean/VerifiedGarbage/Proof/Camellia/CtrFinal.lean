module

public import VerifiedGarbage.Spec.Camellia.CtrFinal
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Camellia.Scratch
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: shared by the final function's proofs of every target.

/-!
# Camellia-CTR of a message's last piece: the contract on the subkeys it is given

Not trusted, and the same on every target. `ctrFinalContractSk`:
`Spec.Camellia.ctrFinalContract` on the subkeys at `schedule`, for `rounds` of
18 or 24, from which the shared contract follows (`ctrFinal_of_sk`), as
`ctrContractSk` is for `vg_camellia_ctr` (`CtrScratch.lean`); its
precondition and postcondition read the memory on entry, and its
postcondition the memory on return, only within the function's buffers
(`ctrFinalPre_local`, `ctrFinalPost_local`, `ctrFinalPostOut_local`), as a
frame that keeps working space on the stack needs. What a final function leaves gives `Spec.Ctr.CryptFinal` by
`Proof.Modes.CtrFinal.cryptFinal_of`, for any cipher.
-/

@[expose] public section

namespace VG.Proof.Camellia

open VG.Spec.Camellia

/-- `Spec.Camellia.ctrFinalContract`'s postcondition on the subkeys at
`schedule`, for `rounds` of 18 or 24. -/
def ctrFinalPostSk (pb : Nat) : ctrFinalSig.Post pb := fun schedule rounds ctr data len m m' _ =>
  (rounds.toNat = 18 ∨ rounds.toNat = 24) →
    Spec.Ctr.CryptFinal (cipher (subkeysAt m schedule rounds.toNat)) m m' ctr data len.toNat

/-- `Spec.Camellia.ctrFinalContract` with `ctrFinalPostSk`. -/
def ctrFinalContractSk {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ctrFinalSig.contract A (pre := ctrFinalPre A.ptrBits) (post := ctrFinalPostSk A.ptrBits) (writeArgs := true)
    (stack := stack)

theorem ctrFinalPost_of_sk (pb : Nat) : Curry.Imp _ (ctrFinalPostSk pb) (fun schedule rounds ctr data len m m' _ =>
    ∀ key, KeySchedule m schedule rounds.toNat key →
      Spec.Ctr.CryptFinal (cipher (expandKey key)) m m' ctr data len.toNat) := by
  intro _ _ _ _ _ _ _ _ h key hk
  rw [← subkeysAt_of_keySchedule hk]
  exact h (rounds_of_keySchedule hk)

theorem ctrFinal_of_sk {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (ctrFinalContractSk A stack)) : Verified T c (Spec.Camellia.ctrFinalContract A stack) :=
  verified_of_post h (ctrFinalPost_of_sk A.ptrBits)

private theorem bytesAt_congr' {m₁ m₂ : Mem} {p : Addr} {k : Nat}
    (h : ∀ i < k, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m₂ p k = Spec.Aes.bytesAt m₁ p k := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- `ctrFinalPostSk` reads the memory on return only within the buffers. -/
theorem ctrFinalPostOut_local (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (ctrFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs ctrFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ctrFinalSig.words pb) (ctrFinalPostSk pb) vs m m₁ r →
      Curry.apply (ctrFinalSig.words pb) (ctrFinalPostSk pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [k, rounds, ctr, data, len], _ =>
    simp only [ctrFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of hb.2.1
    have hd := agree_of hb.2.2
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (ctrFinalPostSk pb) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (ctrFinalPostSk pb) _ m m₂ r
    dsimp only [Curry.apply, ctrFinalPostSk, ArgWord.ofRaw, Spec.Ctr.CryptFinal] at h ⊢
    have := Nat.mod_le len.toNat (2 ^ pb)
    intro hR
    rw [bytesAt_congr' fun i hi => hd i (by rw [BitVec.toNat_setWidth] at hi; omega), bytesAt_congr' hc]
    exact h hR

/-- `Spec.Camellia.ctrFinalPre` reads no memory. -/
theorem ctrFinalPre_local (pb : Nat) : ∀ vs m₁ m₂, vs.length = (ctrFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs ctrFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ctrFinalSig.words pb) (ctrFinalPre pb) vs m₁ →
      Curry.apply (ctrFinalSig.words pb) (ctrFinalPre pb) vs m₂ := by
  intro vs m₁ m₂ hlen _ h
  match vs, hlen with
  | [_, _, _, _, _], _ => exact h

/-- `ctrFinalPostSk` reads the memory on entry only within the buffers. -/
theorem ctrFinalPost_local (pb : Nat) : ∀ vs m₁ m₂ m' r, vs.length = (ctrFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs ctrFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ctrFinalSig.words pb) (ctrFinalPostSk pb) vs m₁ m' r →
      Curry.apply (ctrFinalSig.words pb) (ctrFinalPostSk pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  match vs, hlen with
  | [k, rounds, ctr, data, len], _ =>
    simp only [ctrFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hk := agree_of hb.1
    have hc := agree_of hb.2.1
    have hd := agree_of hb.2.2
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (ctrFinalPostSk pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (ctrFinalPostSk pb) _ m₂ m' r
    dsimp only [Curry.apply, ctrFinalPostSk, ArgWord.ofRaw, Spec.Ctr.CryptFinal] at h ⊢
    have := Nat.mod_le len.toNat (2 ^ pb)
    intro hR
    rw [subkeysAt_congr (by rcases hR with h' | h' <;> rw [h'] <;> decide) hk,
      bytesAt_congr' fun i hi => hd i (by rw [BitVec.toNat_setWidth] at hi; omega), bytesAt_congr' hc]
    exact h hR

end VG.Proof.Camellia
