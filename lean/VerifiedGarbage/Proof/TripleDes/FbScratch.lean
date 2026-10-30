module

public import VerifiedGarbage.Spec.TripleDes.Ofb
public import VerifiedGarbage.Spec.TripleDes.Cfb8
public import VerifiedGarbage.Spec.Cfb
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.TripleDes.CbcBlocks
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Sig

/-!
# Triple DES-OFB, -CFB64 and -CFB8 with their working space as an argument

`fbScratchContract n post` and `cfb8ScratchContract n post` are the OFB and
CFB64 contracts (one signature, `ofbSig = cfbSig`) and the CFB8 contracts
with a `scratch` buffer of `n` words appended, whatever it holds (each
target lays out its own), for the frame that keeps it on the stack
(`Verified.stackScratchWiped`), which needs each postcondition to read the
memory on return only within the function's buffers (`ofbPostOut_local`,
…), and, where the frame copies stack arguments (ARMv7), on entry too
(`ofbPost_local`, …).
-/

@[expose] public section

namespace VG.Proof.TripleDes

open VG.Spec.TripleDes

/-- `vg_triple_des_ofb` (and CFB64's functions) with `scratch: *mut [u64; n]`. -/
def fbScratchSig (n : Nat) : Sig where
  params := ofbSig.params ++ [("scratch", .array true .u64 n)]

/-- CFB8's functions with `scratch: *mut [u64; n]`. -/
def cfb8ScratchSig (n : Nat) : Sig where
  params := cfb8Sig.params ++ [("scratch", .array true .u64 n)]

/-- `ofbContract`'s postcondition. -/
def ofbPost (pb : Nat) : ofbSig.Post pb := fun schedule iv data n m m' _ =>
  let ciph := cipher (scheduleAt m schedule)
  cbcBlocksAt m' data n.toNat = Spec.Ofb.crypt ciph (bytesAt m iv 8) (cbcBlocksAt m data n.toNat) ∧
    bytesAt m' iv 8 = Spec.Ofb.next ciph (bytesAt m iv 8) n.toNat

/-- `cfbEncryptContract`'s postcondition. -/
def cfbEncPost (pb : Nat) : ofbSig.Post pb := fun schedule iv data n m m' _ =>
  let cs := Spec.Cfb.encrypt (cipher (scheduleAt m schedule)) (bytesAt m iv 8) (cbcBlocksAt m data n.toNat)
  cbcBlocksAt m' data n.toNat = cs ∧ bytesAt m' iv 8 = Spec.Cbc.next (bytesAt m iv 8) cs

/-- `cfbDecryptContract`'s postcondition. -/
def cfbDecPost (pb : Nat) : ofbSig.Post pb := fun schedule iv data n m m' _ =>
  let cs := cbcBlocksAt m data n.toNat
  cbcBlocksAt m' data n.toNat = Spec.Cfb.decrypt (cipher (scheduleAt m schedule)) (bytesAt m iv 8) cs ∧
    bytesAt m' iv 8 = Spec.Cbc.next (bytesAt m iv 8) cs

/-- `cfb8EncryptContract`'s postcondition. -/
def cfb8EncPost (pb : Nat) : cfb8Sig.Post pb := fun schedule iv data len m m' _ =>
  let cs := Spec.Cfb8.encrypt (cipher (scheduleAt m schedule)) (bytesAt m iv 8) (bytesAt m data len.toNat)
  bytesAt m' data len.toNat = cs ∧ bytesAt m' iv 8 = Spec.Cfb8.next (bytesAt m iv 8) cs

/-- `cfb8DecryptContract`'s postcondition. -/
def cfb8DecPost (pb : Nat) : cfb8Sig.Post pb := fun schedule iv data len m m' _ =>
  let cs := bytesAt m data len.toNat
  bytesAt m' data len.toNat = Spec.Cfb8.decrypt (cipher (scheduleAt m schedule)) (bytesAt m iv 8) cs ∧
    bytesAt m' iv 8 = Spec.Cfb8.next (bytesAt m iv 8) cs

/-- An OFB or CFB64 contract with the postcondition `post`, whatever
`scratch` is. -/
def fbScratchContract {M : ISA} (A : Abi M) (n : Nat) (post : (pb : Nat) → ofbSig.Post pb) (stack : Nat := 0) :
    Contract M :=
  (fbScratchSig n).contract A
    (post := fun schedule iv data len _scratch => post A.ptrBits schedule iv data len)
    (writeArgs := true) (stack := stack)

/-- A CFB8 contract with the postcondition `post`, whatever `scratch` is. -/
def cfb8ScratchContract {M : ISA} (A : Abi M) (n : Nat) (post : (pb : Nat) → cfb8Sig.Post pb) (stack : Nat := 0) :
    Contract M :=
  (cfb8ScratchSig n).contract A
    (post := fun schedule iv data len _scratch => post A.ptrBits schedule iv data len)
    (writeArgs := true) (stack := stack)

section

variable {m₁ m₂ : Mem} {p : Addr}

private theorem cbcBlocksAt_congr {n : Nat}
    (h : ∀ i < 8 * n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    cbcBlocksAt m₂ p n = cbcBlocksAt m₁ p n := by
  simp only [cbcBlocksAt, blocksAt]
  refine congrArg _ (List.map_congr_left fun i hi => Vector.ext fun j hj => ?_)
  have := List.mem_range.mp hi
  simp only [blockAt, Vector.getElem_ofFn]
  rw [Offset.add_add]
  exact h _ (by omega_arith)

private theorem bytesAt_congr {n : Nat} (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    bytesAt m₂ p n = bytesAt m₁ p n :=
  List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

private theorem agree_of {n : Nat} (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega_arith) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega_arith

end

variable (pb : Nat)

theorem ofbPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (ofbSig.words pb).length →
    (∀ b ∈ Sig.bufs ofbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ofbSig.words pb) (ofbPost pb) vs m m₁ r → Curry.apply (ofbSig.words pb) (ofbPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [ofbSig, Sig.bufs_nil, Sig.bufs_array, Sig.bufs_slice, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hd := agree_of hb.2.2
  have hv := agree_of hb.2.1
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ofbPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ofbPost pb) _ m m₂ r
  dsimp only [Curry.apply, ofbPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega_arith), bytesAt_congr hv]
  exact h

theorem cfbEncPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (ofbSig.words pb).length →
    (∀ b ∈ Sig.bufs ofbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ofbSig.words pb) (cfbEncPost pb) vs m m₁ r → Curry.apply (ofbSig.words pb) (cfbEncPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [ofbSig, Sig.bufs_nil, Sig.bufs_array, Sig.bufs_slice, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hd := agree_of hb.2.2
  have hv := agree_of hb.2.1
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbEncPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbEncPost pb) _ m m₂ r
  dsimp only [Curry.apply, cfbEncPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega_arith), bytesAt_congr hv]
  exact h

theorem cfbDecPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (ofbSig.words pb).length →
    (∀ b ∈ Sig.bufs ofbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ofbSig.words pb) (cfbDecPost pb) vs m m₁ r → Curry.apply (ofbSig.words pb) (cfbDecPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [ofbSig, Sig.bufs_nil, Sig.bufs_array, Sig.bufs_slice, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hd := agree_of hb.2.2
  have hv := agree_of hb.2.1
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbDecPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbDecPost pb) _ m m₂ r
  dsimp only [Curry.apply, cfbDecPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega_arith), bytesAt_congr hv]
  exact h

theorem cfb8EncPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (cfb8Sig.words pb).length →
    (∀ b ∈ Sig.bufs cfb8Sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfb8Sig.words pb) (cfb8EncPost pb) vs m m₁ r → Curry.apply (cfb8Sig.words pb) (cfb8EncPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [cfb8Sig, Sig.bufs_nil, Sig.bufs_array, Sig.bufs_slice, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hd := agree_of hb.2.2
  have hv := agree_of hb.2.1
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfb8EncPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfb8EncPost pb) _ m m₂ r
  dsimp only [Curry.apply, cfb8EncPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [bytesAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega_arith), bytesAt_congr hv]
  exact h

theorem cfb8DecPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (cfb8Sig.words pb).length →
    (∀ b ∈ Sig.bufs cfb8Sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfb8Sig.words pb) (cfb8DecPost pb) vs m m₁ r → Curry.apply (cfb8Sig.words pb) (cfb8DecPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [cfb8Sig, Sig.bufs_nil, Sig.bufs_array, Sig.bufs_slice, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hd := agree_of hb.2.2
  have hv := agree_of hb.2.1
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfb8DecPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfb8DecPost pb) _ m m₂ r
  dsimp only [Curry.apply, cfb8DecPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [bytesAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega_arith), bytesAt_congr hv]
  exact h

theorem ofbPost_local : ∀ vs m₁ m₂ m' r, vs.length = (ofbSig.words pb).length →
    (∀ b ∈ Sig.bufs ofbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ofbSig.words pb) (ofbPost pb) vs m₁ m' r → Curry.apply (ofbSig.words pb) (ofbPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [ofbSig, Sig.bufs_nil, Sig.bufs_array, Sig.bufs_slice, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ofbPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ofbPost pb) _ m₂ m' r
  dsimp only [Curry.apply, ofbPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [scheduleAt_copy hs, bytesAt_congr hv, cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega_arith)]
  exact h

theorem cfbEncPost_local : ∀ vs m₁ m₂ m' r, vs.length = (ofbSig.words pb).length →
    (∀ b ∈ Sig.bufs ofbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ofbSig.words pb) (cfbEncPost pb) vs m₁ m' r → Curry.apply (ofbSig.words pb) (cfbEncPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [ofbSig, Sig.bufs_nil, Sig.bufs_array, Sig.bufs_slice, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbEncPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbEncPost pb) _ m₂ m' r
  dsimp only [Curry.apply, cfbEncPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [scheduleAt_copy hs, bytesAt_congr hv, cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega_arith)]
  exact h

theorem cfbDecPost_local : ∀ vs m₁ m₂ m' r, vs.length = (ofbSig.words pb).length →
    (∀ b ∈ Sig.bufs ofbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ofbSig.words pb) (cfbDecPost pb) vs m₁ m' r → Curry.apply (ofbSig.words pb) (cfbDecPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [ofbSig, Sig.bufs_nil, Sig.bufs_array, Sig.bufs_slice, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbDecPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbDecPost pb) _ m₂ m' r
  dsimp only [Curry.apply, cfbDecPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [scheduleAt_copy hs, bytesAt_congr hv, cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega_arith)]
  exact h

theorem cfb8EncPost_local : ∀ vs m₁ m₂ m' r, vs.length = (cfb8Sig.words pb).length →
    (∀ b ∈ Sig.bufs cfb8Sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfb8Sig.words pb) (cfb8EncPost pb) vs m₁ m' r → Curry.apply (cfb8Sig.words pb) (cfb8EncPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [cfb8Sig, Sig.bufs_nil, Sig.bufs_array, Sig.bufs_slice, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfb8EncPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfb8EncPost pb) _ m₂ m' r
  dsimp only [Curry.apply, cfb8EncPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [scheduleAt_copy hs, bytesAt_congr hv, bytesAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega_arith)]
  exact h

theorem cfb8DecPost_local : ∀ vs m₁ m₂ m' r, vs.length = (cfb8Sig.words pb).length →
    (∀ b ∈ Sig.bufs cfb8Sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfb8Sig.words pb) (cfb8DecPost pb) vs m₁ m' r → Curry.apply (cfb8Sig.words pb) (cfb8DecPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [cfb8Sig, Sig.bufs_nil, Sig.bufs_array, Sig.bufs_slice, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfb8DecPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfb8DecPost pb) _ m₂ m' r
  dsimp only [Curry.apply, cfb8DecPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [scheduleAt_copy hs, bytesAt_congr hv, bytesAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega_arith)]
  exact h

end VG.Proof.TripleDes
