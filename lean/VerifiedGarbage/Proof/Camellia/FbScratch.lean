module

public import VerifiedGarbage.Spec.Camellia.Ofb
public import VerifiedGarbage.Spec.Camellia.Cfb
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Camellia.Scratch
import VerifiedGarbage.Proof.Framework.AddrArith

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

/-- `vg_camellia_ofb` with `scratch: *mut [u64; n]`. -/
def ofbScratchSig (n : Nat) : Sig where
  params := ofbSig.params ++ [("scratch", .array true .u64 n)]

/-- CFB128's functions with `scratch: *mut [u64; n]`. -/
def cfbScratchSig (n : Nat) : Sig where
  params := cfbSig.params ++ [("scratch", .array true .u64 n)]

/-- `ofbContract`, whatever `scratch` is. -/
def ofbScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (ofbScratchSig n).contract A
    (pre := fun schedule rounds iv data n _scratch => ofbPre A.ptrBits schedule rounds iv data n)
    (post := fun schedule rounds iv data n _scratch => ofbPost A.ptrBits schedule rounds iv data n)
    (writeArgs := true) (stack := stack)

theorem ofbScratchContract_eq {M : ISA} (A : Abi M) (n stack : Nat) :
    ofbScratchContract A n stack = Sig.scratchContract A ofbSig "scratch" .u64 n
      (ofbPre A.ptrBits) (ofbPost A.ptrBits) true stack := rfl

/-- `cfbEncryptContract`, whatever `scratch` is. -/
def cfbEncScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (cfbScratchSig n).contract A
    (pre := fun schedule rounds iv data n _scratch => cfbPre A.ptrBits schedule rounds iv data n)
    (post := fun schedule rounds iv data n _scratch => cfbEncryptPost A.ptrBits schedule rounds iv data n)
    (writeArgs := true) (stack := stack)

theorem cfbEncScratchContract_eq {M : ISA} (A : Abi M) (n stack : Nat) :
    cfbEncScratchContract A n stack = Sig.scratchContract A cfbSig "scratch" .u64 n
      (cfbPre A.ptrBits) (cfbEncryptPost A.ptrBits) true stack := rfl

/-- `cfbDecryptContract`, whatever `scratch` is. -/
def cfbDecScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (cfbScratchSig n).contract A
    (pre := fun schedule rounds iv data n _scratch => cfbPre A.ptrBits schedule rounds iv data n)
    (post := fun schedule rounds iv data n _scratch => cfbDecryptPost A.ptrBits schedule rounds iv data n)
    (writeArgs := true) (stack := stack)

theorem cfbDecScratchContract_eq {M : ISA} (A : Abi M) (n stack : Nat) :
    cfbDecScratchContract A n stack = Sig.scratchContract A cfbSig "scratch" .u64 n
      (cfbPre A.ptrBits) (cfbDecryptPost A.ptrBits) true stack := rfl

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
  exact h _ (by omega)

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
    Curry.apply (ofbSig.words pb) (ofbPost pb) vs m₁ m' r → Curry.apply (ofbSig.words pb) (ofbPost pb) vs m₂ m' r := by
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
    (ofbPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (ofbPost pb) _ m₂ m' r
  dsimp only [Curry.apply, ofbPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [subkeysAt_congr (by simp only [scheduleLength]; omega) fun i hi => hs i (by omega), bytesAt_congr' hv,
    cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by rw [BitVec.toNat_setWidth] at hi; omega)]
  exact h hR

theorem cfbEncryptPost_local : ∀ vs m₁ m₂ m' r, vs.length = (cfbSig.words pb).length →
    (∀ b ∈ Sig.bufs cfbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfbSig.words pb) (cfbEncryptPost pb) vs m₁ m' r → Curry.apply (cfbSig.words pb) (cfbEncryptPost pb) vs m₂ m' r := by
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
    (cfbEncryptPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbEncryptPost pb) _ m₂ m' r
  dsimp only [Curry.apply, cfbEncryptPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [subkeysAt_congr (by simp only [scheduleLength]; omega) fun i hi => hs i (by omega), bytesAt_congr' hv,
    cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by rw [BitVec.toNat_setWidth] at hi; omega)]
  exact h hR

theorem cfbDecryptPost_local : ∀ vs m₁ m₂ m' r, vs.length = (cfbSig.words pb).length →
    (∀ b ∈ Sig.bufs cfbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfbSig.words pb) (cfbDecryptPost pb) vs m₁ m' r → Curry.apply (cfbSig.words pb) (cfbDecryptPost pb) vs m₂ m' r := by
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
    (cfbDecryptPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbDecryptPost pb) _ m₂ m' r
  dsimp only [Curry.apply, cfbDecryptPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [subkeysAt_congr (by simp only [scheduleLength]; omega) fun i hi => hs i (by omega), bytesAt_congr' hv,
    cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by rw [BitVec.toNat_setWidth] at hi; omega)]
  exact h hR

theorem ofbPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (ofbSig.words pb).length →
    (∀ b ∈ Sig.bufs ofbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ofbSig.words pb) (ofbPost pb) vs m m₁ r → Curry.apply (ofbSig.words pb) (ofbPost pb) vs m m₂ r := by
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
    (ofbPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (ofbPost pb) _ m m₂ r
  dsimp only [Curry.apply, ofbPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega), bytesAt_congr' hv]
  exact h hR

theorem cfbEncryptPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (cfbSig.words pb).length →
    (∀ b ∈ Sig.bufs cfbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfbSig.words pb) (cfbEncryptPost pb) vs m m₁ r → Curry.apply (cfbSig.words pb) (cfbEncryptPost pb) vs m m₂ r := by
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
    (cfbEncryptPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbEncryptPost pb) _ m m₂ r
  dsimp only [Curry.apply, cfbEncryptPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega), bytesAt_congr' hv]
  exact h hR

theorem cfbDecryptPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (cfbSig.words pb).length →
    (∀ b ∈ Sig.bufs cfbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfbSig.words pb) (cfbDecryptPost pb) vs m m₁ r → Curry.apply (cfbSig.words pb) (cfbDecryptPost pb) vs m m₂ r := by
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
    (cfbDecryptPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (cfbDecryptPost pb) _ m m₂ r
  dsimp only [Curry.apply, cfbDecryptPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega), bytesAt_congr' hv]
  exact h hR

end VG.Proof.Camellia
