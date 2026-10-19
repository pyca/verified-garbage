module

public import VerifiedGarbage.Spec.Seed.Cbc
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Seed.Scratch
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Seed-CBC with its working space as an argument

`cbcEncChainedScratchContract n` and `cbcDecChainedScratchContract n` are
`cbcEncryptChainedContract` and `cbcDecryptChainedContract` with a
`scratch` buffer of `n` words appended, whatever it holds (each target lays
out its own), for the frame that keeps it on the stack
(`Verified.stackScratchWiped`), which needs each postcondition to read the
memory on return only within the function's buffers
(`cbcEncChainedPostOut_local`, …), and the memory on entry only within them
too (`cbcEncChainedPost_local`, …). As CFB's (`FbScratch.lean`), whose
signature has the same shape.
-/

@[expose] public section

namespace VG.Proof.Seed

open VG.Spec.Seed
open VG.Spec.Aes (bytesAt)

/-- `vg_seed_cbc_encrypt_chained` and `_decrypt_chained` with `scratch: *mut [u64; n]`. -/
def cbcChainedScratchSig (n : Nat) : Sig where
  params := cbcChainedSig.params ++ [("scratch", .array true .u64 n)]

/-- `cbcEncryptChainedContract`'s postcondition. -/
def cbcEncChainedPost (pb : Nat) : cbcChainedSig.Post pb := fun schedule iv data n m m' _ =>
      let cs := Spec.Cbc.encrypt (cipher (scheduleAt m schedule)) (Spec.Aes.bytesAt m iv 16)
        (Spec.Cbc.blocksAt m data n.toNat)
      Spec.Cbc.blocksAt m' data n.toNat = cs ∧
        Spec.Aes.bytesAt m' iv 16 = Spec.Cbc.next (Spec.Aes.bytesAt m iv 16) cs

/-- `cbcDecryptChainedContract`'s postcondition. -/
def cbcDecChainedPost (pb : Nat) : cbcChainedSig.Post pb := fun schedule iv data n m m' _ =>
      let cs := Spec.Cbc.blocksAt m data n.toNat
      Spec.Cbc.blocksAt m' data n.toNat =
          Spec.Cbc.decrypt (invCipher (scheduleAt m schedule)) (Spec.Aes.bytesAt m iv 16) cs ∧
        Spec.Aes.bytesAt m' iv 16 = Spec.Cbc.next (Spec.Aes.bytesAt m iv 16) cs

/-- `cbcEncryptChainedContract`, whatever `scratch` is. -/
def cbcEncChainedScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (cbcChainedScratchSig n).contract A
    (post := fun schedule iv data len _scratch => cbcEncChainedPost A.ptrBits schedule iv data len)
    (writeArgs := true) (stack := stack)

/-- `cbcDecryptChainedContract`, whatever `scratch` is. -/
def cbcDecChainedScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (cbcChainedScratchSig n).contract A
    (post := fun schedule iv data len _scratch => cbcDecChainedPost A.ptrBits schedule iv data len)
    (writeArgs := true) (stack := stack)

section

variable {m₁ m₂ : Mem} {p : Addr}

private theorem cbcBlocksAt_congr {n : Nat}
    (h : ∀ i < 16 * n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Cbc.blocksAt m₂ p n = Spec.Cbc.blocksAt m₁ p n := by
  simp only [Spec.Cbc.blocksAt]
  refine List.map_congr_left fun i hi => List.map_congr_left fun j hj => ?_
  have := List.mem_range.mp hi
  have := List.mem_range.mp hj
  rw [Offset.add_add]
  exact h _ (by omega)

private theorem bytesAt_congr {n : Nat} (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    bytesAt m₂ p n = bytesAt m₁ p n :=
  List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

private theorem agree_of {n : Nat} (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

end

variable (pb : Nat)

theorem cbcEncChainedPost_local : ∀ vs m₁ m₂ m' r, vs.length = (cbcChainedSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcChainedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcChainedSig.words pb) (cbcEncChainedPost pb) vs m₁ m' r → Curry.apply (cbcChainedSig.words pb) (cbcEncChainedPost pb) vs m₂ m' r := by
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
  simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cbcEncChainedPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cbcEncChainedPost pb) _ m₂ m' r
  dsimp only [Curry.apply, cbcEncChainedPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [scheduleAt_congr hs, bytesAt_congr hv, cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi =>
    hd i (by rw [BitVec.toNat_setWidth] at hi; omega)]
  exact h

theorem cbcDecChainedPost_local : ∀ vs m₁ m₂ m' r, vs.length = (cbcChainedSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcChainedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcChainedSig.words pb) (cbcDecChainedPost pb) vs m₁ m' r → Curry.apply (cbcChainedSig.words pb) (cbcDecChainedPost pb) vs m₂ m' r := by
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
  simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cbcDecChainedPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cbcDecChainedPost pb) _ m₂ m' r
  dsimp only [Curry.apply, cbcDecChainedPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [scheduleAt_congr hs, bytesAt_congr hv, cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi =>
    hd i (by rw [BitVec.toNat_setWidth] at hi; omega)]
  exact h

theorem cbcEncChainedPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (cbcChainedSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcChainedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcChainedSig.words pb) (cbcEncChainedPost pb) vs m m₁ r → Curry.apply (cbcChainedSig.words pb) (cbcEncChainedPost pb) vs m m₂ r := by
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
  simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hd := agree_of hb.2.2
  have hv := agree_of hb.2.1
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cbcEncChainedPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cbcEncChainedPost pb) _ m m₂ r
  dsimp only [Curry.apply, cbcEncChainedPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega), bytesAt_congr hv]
  exact h

theorem cbcDecChainedPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (cbcChainedSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcChainedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcChainedSig.words pb) (cbcDecChainedPost pb) vs m m₁ r → Curry.apply (cbcChainedSig.words pb) (cbcDecChainedPost pb) vs m m₂ r := by
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
  simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hd := agree_of hb.2.2
  have hv := agree_of hb.2.1
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cbcDecChainedPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cbcDecChainedPost pb) _ m m₂ r
  dsimp only [Curry.apply, cbcDecChainedPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega), bytesAt_congr hv]
  exact h

end VG.Proof.Seed
