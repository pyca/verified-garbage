module

public import VerifiedGarbage.Spec.Camellia.Ofb
public import VerifiedGarbage.Spec.Camellia.Cfb
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Camellia.Scratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Camellia-OFB and Camellia-CFB128 with their working space as an argument

`ofbScratchContract n`, `cfbEncScratchContract n` and `cfbDecScratchContract
n` are `ofbContract`, `cfbEncryptContract` and `cfbDecryptContract` with a
`scratch` buffer of `n` words appended, whatever it holds (each target lays
out its own), for the frame that keeps it on the stack
(`Verified.stackScratchWiped`), which needs each postcondition to read the
memory on return only within the function's buffers (`ofbPostOut_local`,
…), and, where the frame copies stack arguments (ARMv7), the precondition
and postconditions to read the memory on entry only within them too
(`ofbPre_local`, `ofbPost_local`, …).
-/

@[expose] public section

namespace VG.Proof.Camellia

open VG.Spec.Camellia

/-- `ofbPost` on the subkeys at `schedule`, for `rounds` of 18 or 24. -/
def ofbPostSk (pb : Nat) : ofbSig.Post pb := fun schedule rounds iv data n m m' _ =>
  (rounds.toNat = 18 ∨ rounds.toNat = 24) →
    let ciph := cipher (subkeysAt m schedule rounds.toNat)
    Spec.Cbc.blocksAt m' data n.toNat = Spec.Ofb.crypt ciph (Spec.Aes.bytesAt m iv 16) (Spec.Cbc.blocksAt m data n.toNat) ∧
      Spec.Aes.bytesAt m' iv 16 = Spec.Ofb.next ciph (Spec.Aes.bytesAt m iv 16) n.toNat

/-- `ofbContract` with `ofbPostSk`. -/
def ofbContractSk {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ofbSig.contract A (pre := ofbPre A.ptrBits) (post := ofbPostSk A.ptrBits) (writeArgs := true)
    (stack := stack)

/-- `cfbEncryptPost` on the subkeys at `schedule`, for `rounds` of 18 or 24. -/
def cfbEncryptPostSk (pb : Nat) : cfbSig.Post pb := fun schedule rounds iv data n m m' _ =>
  (rounds.toNat = 18 ∨ rounds.toNat = 24) →
    let cs := Spec.Cfb.encrypt (cipher (subkeysAt m schedule rounds.toNat)) (Spec.Aes.bytesAt m iv 16)
      (Spec.Cbc.blocksAt m data n.toNat)
    Spec.Cbc.blocksAt m' data n.toNat = cs ∧ Spec.Aes.bytesAt m' iv 16 = Spec.Cbc.next (Spec.Aes.bytesAt m iv 16) cs

/-- `cfbEncryptContract` with `cfbEncryptPostSk`. -/
def cfbEncryptContractSk {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbSig.contract A (pre := cfbPre A.ptrBits) (post := cfbEncryptPostSk A.ptrBits) (writeArgs := true)
    (stack := stack)

/-- `cfbDecryptPost` on the subkeys at `schedule`, for `rounds` of 18 or 24. -/
def cfbDecryptPostSk (pb : Nat) : cfbSig.Post pb := fun schedule rounds iv data n m m' _ =>
  (rounds.toNat = 18 ∨ rounds.toNat = 24) →
    let cs := Spec.Cbc.blocksAt m data n.toNat
    Spec.Cbc.blocksAt m' data n.toNat =
        Spec.Cfb.decrypt (cipher (subkeysAt m schedule rounds.toNat)) (Spec.Aes.bytesAt m iv 16) cs ∧
      Spec.Aes.bytesAt m' iv 16 = Spec.Cbc.next (Spec.Aes.bytesAt m iv 16) cs

/-- `cfbDecryptContract` with `cfbDecryptPostSk`. -/
def cfbDecryptContractSk {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbSig.contract A (pre := cfbPre A.ptrBits) (post := cfbDecryptPostSk A.ptrBits) (writeArgs := true)
    (stack := stack)

/-- `vg_camellia_ofb` with `scratch: *mut [u64; n]`. -/
def ofbScratchSig (n : Nat) : Sig where
  params := ofbSig.params ++ [("scratch", .array true .u64 n)]

/-- CFB128's functions with `scratch: *mut [u64; n]`. -/
def cfbScratchSig (n : Nat) : Sig where
  params := cfbSig.params ++ [("scratch", .array true .u64 n)]

/-- `ofbContractSk`, whatever `scratch` is. -/
def ofbScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (ofbScratchSig n).contract A
    (pre := fun schedule rounds iv data n _scratch => ofbPre A.ptrBits schedule rounds iv data n)
    (post := fun schedule rounds iv data n _scratch => ofbPostSk A.ptrBits schedule rounds iv data n)
    (writeArgs := true) (stack := stack)

theorem ofbScratchContract_eq {M : ISA} (A : Abi M) (n stack : Nat) :
    ofbScratchContract A n stack = Sig.scratchContract A ofbSig "scratch" .u64 n
      (ofbPre A.ptrBits) (ofbPostSk A.ptrBits) true stack := rfl

/-- `cfbEncryptContractSk`, whatever `scratch` is. -/
def cfbEncScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (cfbScratchSig n).contract A
    (pre := fun schedule rounds iv data n _scratch => cfbPre A.ptrBits schedule rounds iv data n)
    (post := fun schedule rounds iv data n _scratch => cfbEncryptPostSk A.ptrBits schedule rounds iv data n)
    (writeArgs := true) (stack := stack)

theorem cfbEncScratchContract_eq {M : ISA} (A : Abi M) (n stack : Nat) :
    cfbEncScratchContract A n stack = Sig.scratchContract A cfbSig "scratch" .u64 n
      (cfbPre A.ptrBits) (cfbEncryptPostSk A.ptrBits) true stack := rfl

/-- `cfbDecryptContractSk`, whatever `scratch` is. -/
def cfbDecScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (cfbScratchSig n).contract A
    (pre := fun schedule rounds iv data n _scratch => cfbPre A.ptrBits schedule rounds iv data n)
    (post := fun schedule rounds iv data n _scratch => cfbDecryptPostSk A.ptrBits schedule rounds iv data n)
    (writeArgs := true) (stack := stack)

theorem cfbDecScratchContract_eq {M : ISA} (A : Abi M) (n stack : Nat) :
    cfbDecScratchContract A n stack = Sig.scratchContract A cfbSig "scratch" .u64 n
      (cfbPre A.ptrBits) (cfbDecryptPostSk A.ptrBits) true stack := rfl

section

variable {m₁ m₂ : Mem} {p : Addr}

private theorem bytesAt_congr' {k : Nat}
    (h : ∀ i < k, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m₂ p k = Spec.Aes.bytesAt m₁ p k := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

private theorem cbcBlocksAt_congr {n : Nat}
    (h : ∀ i < 16 * n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Cbc.blocksAt m₂ p n = Spec.Cbc.blocksAt m₁ p n := by
  simp only [Spec.Cbc.blocksAt]
  refine List.map_congr_left fun i hi => bytesAt_congr' fun j hj => ?_
  have := List.mem_range.mp hi
  rw [Offset.add_add]
  exact h _ (by omega_arith)

end

variable (pb : Nat)

theorem ofbPre_local : ∀ vs m₁ m₂, vs.length = (ofbSig.words pb).length →
    (∀ b ∈ Sig.bufs ofbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ofbSig.words pb) (ofbPre pb) vs m₁ → Curry.apply (ofbSig.words pb) (ofbPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 4
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

theorem cfbPre_local : ∀ vs m₁ m₂, vs.length = (cfbSig.words pb).length →
    (∀ b ∈ Sig.bufs cfbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfbSig.words pb) (cfbPre pb) vs m₁ → Curry.apply (cfbSig.words pb) (cfbPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 4
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

theorem ofbPost_local : ∀ vs m₁ m₂ m' r, vs.length = (ofbSig.words pb).length →
    (∀ b ∈ Sig.bufs ofbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ofbSig.words pb) (ofbPostSk pb) vs m₁ m' r → Curry.apply (ofbSig.words pb) (ofbPostSk pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (ofbPostSk pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (ofbPostSk pb) _ m₂ m' r
  dsimp only [Curry.apply, ofbPostSk, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [subkeysAt_congr (by simp only [scheduleLength]; omega_arith) fun i hi => hs i (by omega_arith), bytesAt_congr' hv,
    cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by rw [BitVec.toNat_setWidth] at hi; omega_arith)]
  exact h hR

theorem cfbEncryptPost_local : ∀ vs m₁ m₂ m' r, vs.length = (cfbSig.words pb).length →
    (∀ b ∈ Sig.bufs cfbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfbSig.words pb) (cfbEncryptPostSk pb) vs m₁ m' r → Curry.apply (cfbSig.words pb) (cfbEncryptPostSk pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbEncryptPostSk pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbEncryptPostSk pb) _ m₂ m' r
  dsimp only [Curry.apply, cfbEncryptPostSk, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [subkeysAt_congr (by simp only [scheduleLength]; omega_arith) fun i hi => hs i (by omega_arith), bytesAt_congr' hv,
    cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by rw [BitVec.toNat_setWidth] at hi; omega_arith)]
  exact h hR

theorem cfbDecryptPost_local : ∀ vs m₁ m₂ m' r, vs.length = (cfbSig.words pb).length →
    (∀ b ∈ Sig.bufs cfbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfbSig.words pb) (cfbDecryptPostSk pb) vs m₁ m' r → Curry.apply (cfbSig.words pb) (cfbDecryptPostSk pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbDecryptPostSk pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbDecryptPostSk pb) _ m₂ m' r
  dsimp only [Curry.apply, cfbDecryptPostSk, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [subkeysAt_congr (by simp only [scheduleLength]; omega_arith) fun i hi => hs i (by omega_arith), bytesAt_congr' hv,
    cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by rw [BitVec.toNat_setWidth] at hi; omega_arith)]
  exact h hR

theorem ofbPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (ofbSig.words pb).length →
    (∀ b ∈ Sig.bufs ofbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ofbSig.words pb) (ofbPostSk pb) vs m m₁ r → Curry.apply (ofbSig.words pb) (ofbPostSk pb) vs m m₂ r := by
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
  simp only [ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hd := agree_of hb.2.2
  have hv := agree_of hb.2.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (ofbPostSk pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (ofbPostSk pb) _ m m₂ r
  dsimp only [Curry.apply, ofbPostSk, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega_arith), bytesAt_congr' hv]
  exact h hR

theorem cfbEncryptPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (cfbSig.words pb).length →
    (∀ b ∈ Sig.bufs cfbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfbSig.words pb) (cfbEncryptPostSk pb) vs m m₁ r → Curry.apply (cfbSig.words pb) (cfbEncryptPostSk pb) vs m m₂ r := by
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
  simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hd := agree_of hb.2.2
  have hv := agree_of hb.2.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbEncryptPostSk pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbEncryptPostSk pb) _ m m₂ r
  dsimp only [Curry.apply, cfbEncryptPostSk, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega_arith), bytesAt_congr' hv]
  exact h hR

theorem cfbDecryptPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (cfbSig.words pb).length →
    (∀ b ∈ Sig.bufs cfbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfbSig.words pb) (cfbDecryptPostSk pb) vs m m₁ r → Curry.apply (cfbSig.words pb) (cfbDecryptPostSk pb) vs m m₂ r := by
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
  simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hd := agree_of hb.2.2
  have hv := agree_of hb.2.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbDecryptPostSk pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbDecryptPostSk pb) _ m m₂ r
  dsimp only [Curry.apply, cfbDecryptPostSk, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega_arith), bytesAt_congr' hv]
  exact h hR

theorem ofbPost_of_sk (pb : Nat) : Curry.Imp _ (ofbPostSk pb) (ofbPost pb) := by
  intro _ _ _ _ _ _ _ _ h key hk
  rw [← subkeysAt_of_keySchedule hk]
  exact h (rounds_of_keySchedule hk)

theorem ofb_of_sk {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (ofbContractSk A stack)) : Verified T c (ofbContract A stack) :=
  verified_of_post h (ofbPost_of_sk A.ptrBits)

theorem cfbEncryptPost_of_sk (pb : Nat) : Curry.Imp _ (cfbEncryptPostSk pb) (cfbEncryptPost pb) := by
  intro _ _ _ _ _ _ _ _ h key hk
  rw [← subkeysAt_of_keySchedule hk]
  exact h (rounds_of_keySchedule hk)

theorem cfbEncrypt_of_sk {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (cfbEncryptContractSk A stack)) : Verified T c (cfbEncryptContract A stack) :=
  verified_of_post h (cfbEncryptPost_of_sk A.ptrBits)

theorem cfbDecryptPost_of_sk (pb : Nat) : Curry.Imp _ (cfbDecryptPostSk pb) (cfbDecryptPost pb) := by
  intro _ _ _ _ _ _ _ _ h key hk
  rw [← subkeysAt_of_keySchedule hk]
  exact h (rounds_of_keySchedule hk)

theorem cfbDecrypt_of_sk {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (cfbDecryptContractSk A stack)) : Verified T c (cfbDecryptContract A stack) :=
  verified_of_post h (cfbDecryptPost_of_sk A.ptrBits)

end VG.Proof.Camellia
