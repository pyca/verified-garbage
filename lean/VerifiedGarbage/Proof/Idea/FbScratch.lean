module

public import VerifiedGarbage.Spec.Idea.Ofb
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Spec.Cfb
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Idea.Arith
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Spec.Idea.Cfb

/-!
# IDEA-OFB and -CFB64 with their working space as an argument

`fbScratchContract n post` is the OFB or a CFB64 contract (one signature,
`ofbSig = cfbSig`) with a `scratch` buffer of `n` words appended, whatever it holds (each
target lays out its own), for the frame that keeps it on the stack
(`Verified.stackScratchWiped`), which needs each postcondition to read the
memory on return only within the function's buffers (`ofbPostOut_local`,
…).
-/

@[expose] public section

namespace VG.Proof.Idea

open VG.Spec.Idea
open VG.Spec.Aes (bytesAt)

/-- `vg_idea_ofb` (and CFB64's functions) with `scratch: *mut [u64; n]`. -/
def fbScratchSig (n : Nat) : Sig where
  params := ofbSig.params ++ [("scratch", .array true .u64 n)]

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

/-- An OFB or CFB64 contract with the postcondition `post`, whatever
`scratch` is. -/
def fbScratchContract {M : ISA} (A : Abi M) (n : Nat) (post : (pb : Nat) → ofbSig.Post pb) (stack : Nat := 0) :
    Contract M :=
  (fbScratchSig n).contract A
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
  simp only [ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ofbPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ofbPost pb) _ m₂ m' r
  dsimp only [Curry.apply, ofbPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [scheduleAt_congr hs, bytesAt_congr hv, cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi =>
    hd i (by rw [BitVec.toNat_setWidth] at hi; omega)]
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
  simp only [ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbEncPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbEncPost pb) _ m₂ m' r
  dsimp only [Curry.apply, cfbEncPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [scheduleAt_congr hs, bytesAt_congr hv, cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi =>
    hd i (by rw [BitVec.toNat_setWidth] at hi; omega)]
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
  simp only [ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbDecPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbDecPost pb) _ m₂ m' r
  dsimp only [Curry.apply, cfbDecPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [scheduleAt_congr hs, bytesAt_congr hv, cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi =>
    hd i (by rw [BitVec.toNat_setWidth] at hi; omega)]
  exact h

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
  simp only [ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hd := agree_of hb.2.2
  have hv := agree_of hb.2.1
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ofbPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ofbPost pb) _ m m₂ r
  dsimp only [Curry.apply, ofbPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega), bytesAt_congr hv]
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
  simp only [ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hd := agree_of hb.2.2
  have hv := agree_of hb.2.1
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbEncPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbEncPost pb) _ m m₂ r
  dsimp only [Curry.apply, cfbEncPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega), bytesAt_congr hv]
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
  simp only [ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hd := agree_of hb.2.2
  have hv := agree_of hb.2.1
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbDecPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbDecPost pb) _ m m₂ r
  dsimp only [Curry.apply, cfbDecPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega), bytesAt_congr hv]
  exact h

end VG.Proof.Idea
