module

public import VerifiedGarbage.Spec.Camellia.CfbFinal
public import VerifiedGarbage.Spec.Camellia.OfbFinal
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Camellia.Scratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Camellia-CFB128 and Camellia-OFB of a message's last piece with its working space as an argument

`cfbEncFinalScratchContract n` and `cfbDecFinalScratchContract n` are the final
functions' contracts on the subkeys at `schedule` (`cfbEncryptFinalPostSk`,
…) with a `scratch` buffer of `n` words appended, for the frame that keeps it
on the stack (`Verified.stackScratchWiped`), which needs each postcondition to
read the memory on return only within the function's buffers
(`cfbEncryptFinalPostOut_local`, …), and, for 32-bit x86's frame, the memory
on entry likewise (`cfbEncryptFinalPost_local`, …, and `cfbFinalPre_local`); `cfbEncryptFinal_of_sk`, … give the
specification's contracts, on every key whose subkeys those are.
`ofbFinalScratchContract n`, `ofbFinalPostOut_local`, …, `ofbFinal_of_sk` are
the same for the final OFB function.
-/

@[expose] public section

namespace VG.Proof.Camellia

open VG.Spec.Camellia

/-- `cfbEncryptFinalContract`'s postcondition on the subkeys at `schedule`, for
`rounds` of 18 or 24. -/
def cfbEncryptFinalPostSk (pb : Nat) : cfbFinalSig.Post pb := fun schedule rounds iv data len m m' _ =>
  (rounds.toNat = 18 ∨ rounds.toNat = 24) →
    Spec.Cfb.EncryptFinal (cipher (subkeysAt m schedule rounds.toNat)) 16 m m' iv data len.toNat

/-- `cfbEncryptFinalContract` with `cfbEncryptFinalPostSk`. -/
def cfbEncryptFinalContractSk {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbFinalSig.contract A (pre := cfbFinalPre A.ptrBits) (post := cfbEncryptFinalPostSk A.ptrBits) (writeArgs := true)
    (stack := stack)

/-- `cfbEncryptFinalContractSk`, whatever the appended `scratch` is. -/
abbrev cfbEncFinalScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  Sig.scratchContract A cfbFinalSig "scratch" .u64 n (cfbFinalPre A.ptrBits) (cfbEncryptFinalPostSk A.ptrBits) true stack

/-- `cfbDecryptFinalContract`'s postcondition on the subkeys at `schedule`, for
`rounds` of 18 or 24. -/
def cfbDecryptFinalPostSk (pb : Nat) : cfbFinalSig.Post pb := fun schedule rounds iv data len m m' _ =>
  (rounds.toNat = 18 ∨ rounds.toNat = 24) →
    Spec.Cfb.DecryptFinal (cipher (subkeysAt m schedule rounds.toNat)) 16 m m' iv data len.toNat

/-- `cfbDecryptFinalContract` with `cfbDecryptFinalPostSk`. -/
def cfbDecryptFinalContractSk {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbFinalSig.contract A (pre := cfbFinalPre A.ptrBits) (post := cfbDecryptFinalPostSk A.ptrBits) (writeArgs := true)
    (stack := stack)

/-- `cfbDecryptFinalContractSk`, whatever the appended `scratch` is. -/
abbrev cfbDecFinalScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  Sig.scratchContract A cfbFinalSig "scratch" .u64 n (cfbFinalPre A.ptrBits) (cfbDecryptFinalPostSk A.ptrBits) true stack

private theorem bytesAt_congr' {m₁ m₂ : Mem} {p : Addr} {k : Nat}
    (h : ∀ i < k, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m₂ p k = Spec.Aes.bytesAt m₁ p k := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

variable (pb : Nat)

/-- `cfbFinalPre` reads no memory. -/
theorem cfbFinalPre_local : ∀ vs m₁ m₂, vs.length = (cfbFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs cfbFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfbFinalSig.words pb) (cfbFinalPre pb) vs m₁ → Curry.apply (cfbFinalSig.words pb) (cfbFinalPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 4
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

/-- `cfbEncryptFinalPostSk` reads the memory on entry only within the function's
buffers. -/
theorem cfbEncryptFinalPost_local : ∀ vs m₁ m₂ m' r, vs.length = (cfbFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs cfbFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfbFinalSig.words pb) (cfbEncryptFinalPostSk pb) vs m₁ m' r →
      Curry.apply (cfbFinalSig.words pb) (cfbEncryptFinalPostSk pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
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
  have hs := agree_of hb.1
  have hd := agree_of hb.2.2
  have hv := agree_of hb.2.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbEncryptFinalPostSk pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbEncryptFinalPostSk pb) _ m₂ m' r
  dsimp only [Curry.apply, cfbEncryptFinalPostSk, ArgWord.ofRaw, Spec.Cfb.EncryptFinal] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [subkeysAt_congr (by simp only [scheduleLength]; omega) fun i hi => hs i (by omega),
    bytesAt_congr' (k := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega), bytesAt_congr' hv]
  exact h hR

theorem cfbEncryptFinalPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (cfbFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs cfbFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfbFinalSig.words pb) (cfbEncryptFinalPostSk pb) vs m m₁ r →
      Curry.apply (cfbFinalSig.words pb) (cfbEncryptFinalPostSk pb) vs m m₂ r := by
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
  have hd := agree_of hb.2.2
  have hv := agree_of hb.2.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbEncryptFinalPostSk pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbEncryptFinalPostSk pb) _ m m₂ r
  dsimp only [Curry.apply, cfbEncryptFinalPostSk, ArgWord.ofRaw, Spec.Cfb.EncryptFinal] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [bytesAt_congr' (k := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega), bytesAt_congr' hv]
  exact h hR

theorem cfbEncryptFinalPost_of_sk : Curry.Imp _ (cfbEncryptFinalPostSk pb) (fun schedule rounds iv data len m m' _ =>
    ∀ key, KeySchedule m schedule rounds.toNat key →
      Spec.Cfb.EncryptFinal (cipher (expandKey key)) 16 m m' iv data len.toNat : cfbFinalSig.Post pb) := by
  intro _ _ _ _ _ _ _ _ h key hk
  rw [← subkeysAt_of_keySchedule hk]
  exact h (rounds_of_keySchedule hk)

theorem cfbEncryptFinal_of_sk {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (cfbEncryptFinalContractSk A stack)) : Verified T c (cfbEncryptFinalContract A stack) :=
  verified_of_post h (cfbEncryptFinalPost_of_sk A.ptrBits)

/-- `cfbDecryptFinalPostSk` reads the memory on entry only within the function's
buffers. -/
theorem cfbDecryptFinalPost_local : ∀ vs m₁ m₂ m' r, vs.length = (cfbFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs cfbFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfbFinalSig.words pb) (cfbDecryptFinalPostSk pb) vs m₁ m' r →
      Curry.apply (cfbFinalSig.words pb) (cfbDecryptFinalPostSk pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
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
  have hs := agree_of hb.1
  have hd := agree_of hb.2.2
  have hv := agree_of hb.2.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbDecryptFinalPostSk pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbDecryptFinalPostSk pb) _ m₂ m' r
  dsimp only [Curry.apply, cfbDecryptFinalPostSk, ArgWord.ofRaw, Spec.Cfb.DecryptFinal] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [subkeysAt_congr (by simp only [scheduleLength]; omega) fun i hi => hs i (by omega),
    bytesAt_congr' (k := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega), bytesAt_congr' hv]
  exact h hR

theorem cfbDecryptFinalPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (cfbFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs cfbFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfbFinalSig.words pb) (cfbDecryptFinalPostSk pb) vs m m₁ r →
      Curry.apply (cfbFinalSig.words pb) (cfbDecryptFinalPostSk pb) vs m m₂ r := by
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
  have hd := agree_of hb.2.2
  have hv := agree_of hb.2.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbDecryptFinalPostSk pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbDecryptFinalPostSk pb) _ m m₂ r
  dsimp only [Curry.apply, cfbDecryptFinalPostSk, ArgWord.ofRaw, Spec.Cfb.DecryptFinal] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [bytesAt_congr' (k := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega), bytesAt_congr' hv]
  exact h hR

theorem cfbDecryptFinalPost_of_sk : Curry.Imp _ (cfbDecryptFinalPostSk pb) (fun schedule rounds iv data len m m' _ =>
    ∀ key, KeySchedule m schedule rounds.toNat key →
      Spec.Cfb.DecryptFinal (cipher (expandKey key)) 16 m m' iv data len.toNat : cfbFinalSig.Post pb) := by
  intro _ _ _ _ _ _ _ _ h key hk
  rw [← subkeysAt_of_keySchedule hk]
  exact h (rounds_of_keySchedule hk)

theorem cfbDecryptFinal_of_sk {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (cfbDecryptFinalContractSk A stack)) : Verified T c (cfbDecryptFinalContract A stack) :=
  verified_of_post h (cfbDecryptFinalPost_of_sk A.ptrBits)

/-! ## OFB of a message's last piece -/

/-- `ofbFinalContract`'s postcondition on the subkeys at `schedule`, for
`rounds` of 18 or 24. -/
def ofbFinalPostSk (pb : Nat) : ofbFinalSig.Post pb := fun schedule rounds iv data len m m' _ =>
  (rounds.toNat = 18 ∨ rounds.toNat = 24) →
    Spec.Ofb.CryptFinal (cipher (subkeysAt m schedule rounds.toNat)) 16 m m' iv data len.toNat

/-- `ofbFinalContract` with `ofbFinalPostSk`. -/
def ofbFinalContractSk {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ofbFinalSig.contract A (pre := ofbFinalPre A.ptrBits) (post := ofbFinalPostSk A.ptrBits) (writeArgs := true)
    (stack := stack)

/-- `ofbFinalContractSk`, whatever the appended `scratch` is. -/
abbrev ofbFinalScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  Sig.scratchContract A ofbFinalSig "scratch" .u64 n (ofbFinalPre A.ptrBits) (ofbFinalPostSk A.ptrBits) true stack

/-- `ofbFinalPre` reads no memory. -/
theorem ofbFinalPre_local : ∀ vs m₁ m₂, vs.length = (ofbFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs ofbFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ofbFinalSig.words pb) (ofbFinalPre pb) vs m₁ → Curry.apply (ofbFinalSig.words pb) (ofbFinalPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 4
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

/-- `ofbFinalPostSk` reads the memory on entry only within the function's
buffers. -/
theorem ofbFinalPost_local : ∀ vs m₁ m₂ m' r, vs.length = (ofbFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs ofbFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ofbFinalSig.words pb) (ofbFinalPostSk pb) vs m₁ m' r →
      Curry.apply (ofbFinalSig.words pb) (ofbFinalPostSk pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
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
  simp only [ofbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hd := agree_of hb.2.2
  have hv := agree_of hb.2.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (ofbFinalPostSk pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (ofbFinalPostSk pb) _ m₂ m' r
  dsimp only [Curry.apply, ofbFinalPostSk, ArgWord.ofRaw, Spec.Ofb.CryptFinal] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [subkeysAt_congr (by simp only [scheduleLength]; omega) fun i hi => hs i (by omega),
    bytesAt_congr' (k := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega), bytesAt_congr' hv]
  exact h hR

theorem ofbFinalPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (ofbFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs ofbFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ofbFinalSig.words pb) (ofbFinalPostSk pb) vs m m₁ r →
      Curry.apply (ofbFinalSig.words pb) (ofbFinalPostSk pb) vs m m₂ r := by
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
  simp only [ofbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hd := agree_of hb.2.2
  have hv := agree_of hb.2.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (ofbFinalPostSk pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (ofbFinalPostSk pb) _ m m₂ r
  dsimp only [Curry.apply, ofbFinalPostSk, ArgWord.ofRaw, Spec.Ofb.CryptFinal] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [bytesAt_congr' (k := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega), bytesAt_congr' hv]
  exact h hR

theorem ofbFinalPost_of_sk : Curry.Imp _ (ofbFinalPostSk pb) (fun schedule rounds iv data len m m' _ =>
    ∀ key, KeySchedule m schedule rounds.toNat key →
      Spec.Ofb.CryptFinal (cipher (expandKey key)) 16 m m' iv data len.toNat : ofbFinalSig.Post pb) := by
  intro _ _ _ _ _ _ _ _ h key hk
  rw [← subkeysAt_of_keySchedule hk]
  exact h (rounds_of_keySchedule hk)

theorem ofbFinal_of_sk {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (ofbFinalContractSk A stack)) : Verified T c (ofbFinalContract A stack) :=
  verified_of_post h (ofbFinalPost_of_sk A.ptrBits)

end VG.Proof.Camellia
