module

public import VerifiedGarbage.Spec.Cast5.CfbFinal
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.PostMono
import VerifiedGarbage.Proof.Framework.Offset

/-!
# CAST5-CFB64 of a message's last piece on the subkeys at `schedule`

`cfbEncFinalPost`, `cfbDecFinalPost`: the final functions' postconditions on
the subkeys at `schedule` and `rounds` rounds, which read the memory on
return only within the functions' buffers (`cfbEncFinalPostOut_local`, …),
as the frame that keeps a scratch buffer on the stack needs
(`Verified.stackScratchWiped`); `cfbEncryptFinal_keyed`, … give the
specification's contracts, on every key whose subkeys those are.
-/

@[expose] public section

namespace VG.Proof.Cast5

open VG.Spec.Cast5

private theorem agree_of {m₁ m₂ : Mem} {p : Addr} {n : Nat} (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

private theorem bytesAt_congr' {m₁ m₂ : Mem} {p : Addr} {k : Nat}
    (h : ∀ i < k, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m₂ p k = Spec.Aes.bytesAt m₁ p k := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- `cfbEncryptFinalContract`'s postcondition on the subkeys at `schedule`, with
`rounds` rounds. -/
def cfbEncFinalPost (pb : Nat) : cfbFinalSig.Post pb := fun schedule rounds iv data len m m' _ =>
  Spec.Cfb.EncryptFinal (cipher (scheduleAt m schedule) rounds.toNat) 8 m m' iv data len.toNat

/-- For `rounds` of 12 or 16, with the subkeys at `schedule`: the final
encryption (`cfbEncFinalPost`). -/
def cfbEncryptFinalRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbFinalSig.contract A (pre := cfbFinalPre A.ptrBits) (post := cfbEncFinalPost A.ptrBits) (writeArgs := true)
    (stack := stack)

/-- `Spec.Cast5.cfbEncryptFinalContract` from `cfbEncryptFinalRoundsContract`. -/
theorem cfbEncryptFinal_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (cfbEncryptFinalRoundsContract A stack)) : Verified T c (Spec.Cast5.cfbEncryptFinalContract A stack) :=
  h.post_mono fun _ _ _ _ _ _ _ _ hp key ⟨_, hr, hw⟩ => by
    unfold cfbEncFinalPost at hp
    rw [hw, hr] at hp
    exact hp

theorem cfbEncFinalPostOut_local (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (cfbFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs cfbFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfbFinalSig.words pb) (cfbEncFinalPost pb) vs m m₁ r →
      Curry.apply (cfbFinalSig.words pb) (cfbEncFinalPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 2
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbEncFinalPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbEncFinalPost pb) _ m m₂ r
  dsimp only [Curry.apply, cfbEncFinalPost, ArgWord.ofRaw, Spec.Cfb.EncryptFinal] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [bytesAt_congr' (k := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega), bytesAt_congr' hv]
  exact h

/-- `cfbDecryptFinalContract`'s postcondition on the subkeys at `schedule`, with
`rounds` rounds. -/
def cfbDecFinalPost (pb : Nat) : cfbFinalSig.Post pb := fun schedule rounds iv data len m m' _ =>
  Spec.Cfb.DecryptFinal (cipher (scheduleAt m schedule) rounds.toNat) 8 m m' iv data len.toNat

/-- For `rounds` of 12 or 16, with the subkeys at `schedule`: the final
decryption (`cfbDecFinalPost`). -/
def cfbDecryptFinalRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbFinalSig.contract A (pre := cfbFinalPre A.ptrBits) (post := cfbDecFinalPost A.ptrBits) (writeArgs := true)
    (stack := stack)

/-- `Spec.Cast5.cfbDecryptFinalContract` from `cfbDecryptFinalRoundsContract`. -/
theorem cfbDecryptFinal_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (cfbDecryptFinalRoundsContract A stack)) : Verified T c (Spec.Cast5.cfbDecryptFinalContract A stack) :=
  h.post_mono fun _ _ _ _ _ _ _ _ hp key ⟨_, hr, hw⟩ => by
    unfold cfbDecFinalPost at hp
    rw [hw, hr] at hp
    exact hp

theorem cfbDecFinalPostOut_local (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (cfbFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs cfbFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfbFinalSig.words pb) (cfbDecFinalPost pb) vs m m₁ r →
      Curry.apply (cfbFinalSig.words pb) (cfbDecFinalPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 2
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbDecFinalPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbDecFinalPost pb) _ m m₂ r
  dsimp only [Curry.apply, cfbDecFinalPost, ArgWord.ofRaw, Spec.Cfb.DecryptFinal] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [bytesAt_congr' (k := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega), bytesAt_congr' hv]
  exact h

end VG.Proof.Cast5
