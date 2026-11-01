module

public import VerifiedGarbage.Spec.Cast5.Ofb
public import VerifiedGarbage.Spec.Cast5.Cfb
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# CAST5-CBC, CAST5-OFB and CAST5-CFB64 with their working space as an argument

`modeScratchContract sig n pre post` is a mode's contract (`cbcChainedSig`,
`ofbSig` or `cfbSig`, whose words are the same) with a `scratch` buffer of
`n` words appended, whatever it holds (each target lays out its own), for
the frame that keeps it on the stack (`Verified.stackScratchWipedC`), which
needs the precondition to read no memory (`modePre_local`) and each
postcondition to read the memory on entry and on return only within the
function's buffers (`cbcEncChainedPost_local`, `cbcEncChainedPostOut_local`, …).
-/

@[expose] public section

namespace VG.Proof.Cast5

open VG.Spec.Cast5

/-- `cbcEncryptChainedContract`'s and `cbcDecryptChainedContract`'s precondition: `rounds` is 12 or 16. -/
def cbcChainedPre (pb : Nat) : Curry (cbcChainedSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _iv _data _n _ => rounds.toNat = 12 ∨ rounds.toNat = 16

/-- `cbcEncryptChainedContract`'s postcondition. -/
def cbcEncChainedPost (pb : Nat) : cbcChainedSig.Post pb := fun schedule rounds iv data n m m' _ =>
  let cs := Spec.Cbc.encrypt (cipher (scheduleAt m schedule) rounds.toNat) (Spec.Aes.bytesAt m iv 8)
    (cbcBlocksAt m data n.toNat)
  cbcBlocksAt m' data n.toNat = cs ∧ Spec.Aes.bytesAt m' iv 8 = Spec.Cbc.next (Spec.Aes.bytesAt m iv 8) cs

/-- `cbcDecryptChainedContract`'s postcondition. -/
def cbcDecChainedPost (pb : Nat) : cbcChainedSig.Post pb := fun schedule rounds iv data n m m' _ =>
  let cs := cbcBlocksAt m data n.toNat
  cbcBlocksAt m' data n.toNat =
      Spec.Cbc.decrypt (invCipher (scheduleAt m schedule) rounds.toNat) (Spec.Aes.bytesAt m iv 8) cs ∧
    Spec.Aes.bytesAt m' iv 8 = Spec.Cbc.next (Spec.Aes.bytesAt m iv 8) cs

/-- `ofbContract`'s postcondition. -/
def ofbPost (pb : Nat) : ofbSig.Post pb := fun schedule rounds iv data n m m' _ =>
  let ciph := cipher (scheduleAt m schedule) rounds.toNat
  cbcBlocksAt m' data n.toNat = Spec.Ofb.crypt ciph (Spec.Aes.bytesAt m iv 8) (cbcBlocksAt m data n.toNat) ∧
    Spec.Aes.bytesAt m' iv 8 = Spec.Ofb.next ciph (Spec.Aes.bytesAt m iv 8) n.toNat

/-- `cfbEncryptContract`'s postcondition. -/
def cfbEncPost (pb : Nat) : cfbSig.Post pb := fun schedule rounds iv data n m m' _ =>
  let cs := Spec.Cfb.encrypt (cipher (scheduleAt m schedule) rounds.toNat) (Spec.Aes.bytesAt m iv 8)
    (cbcBlocksAt m data n.toNat)
  cbcBlocksAt m' data n.toNat = cs ∧ Spec.Aes.bytesAt m' iv 8 = Spec.Cbc.next (Spec.Aes.bytesAt m iv 8) cs

/-- `cfbDecryptContract`'s postcondition. -/
def cfbDecPost (pb : Nat) : cfbSig.Post pb := fun schedule rounds iv data n m m' _ =>
  let cs := cbcBlocksAt m data n.toNat
  cbcBlocksAt m' data n.toNat = Spec.Cfb.decrypt (cipher (scheduleAt m schedule) rounds.toNat)
    (Spec.Aes.bytesAt m iv 8) cs ∧ Spec.Aes.bytesAt m' iv 8 = Spec.Cbc.next (Spec.Aes.bytesAt m iv 8) cs

/-- A mode's contract (signature `sig`) with the precondition `pre` and the
postcondition `post`, whatever `scratch: *mut [u64; n]` is. -/
def modeScratchContract {M : ISA} (A : Abi M) (sig : Sig) (n : Nat)
    (pre : Curry (sig.words A.ptrBits) (Mem → Prop)) (post : sig.Post A.ptrBits) (stack : Nat := 0) :
    Contract M :=
  Sig.scratchContract A sig "scratch" .u64 n pre post true stack

section

variable {m₁ m₂ : Mem} {p : Addr}

private theorem bytesAt_congr {k : Nat}
    (h : ∀ i < k, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m₂ p k = Spec.Aes.bytesAt m₁ p k := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

private theorem blockAt_congr
    (h : ∀ i < 8, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    blockAt m₂ p = blockAt m₁ p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  exact h i hi

private theorem cbcBlocksAt_congr {n : Nat}
    (h : ∀ i < 8 * n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    cbcBlocksAt m₂ p n = cbcBlocksAt m₁ p n := by
  simp only [cbcBlocksAt, blocksAt, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact congrArg Vector.toList (blockAt_congr fun j hj => by rw [Offset.add_add]; exact h _ (by omega_arith))

theorem scheduleAt_congr
    (h : ∀ i < 128, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    scheduleAt m₂ p = scheduleAt m₁ p := by
  apply Vector.ext
  intro i hi
  simp only [scheduleAt, Vector.getElem_ofFn]
  rw [h _ (by omega_arith), h _ (by omega_arith), h _ (by omega_arith), h _ (by omega_arith)]

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

/-- The modes' precondition reads no memory. -/
theorem modePre_local : ∀ vs m₁ m₂, vs.length = (cbcChainedSig.words pb).length →
    Curry.apply (cbcChainedSig.words pb) (cbcChainedPre pb) vs m₁ →
      Curry.apply (cbcChainedSig.words pb) (cbcChainedPre pb) vs m₂ := by
  intro vs _ _ hlen h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 4
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h





theorem ofbPost_local : ∀ vs m₁ m₂ m' r, vs.length = (ofbSig.words pb).length →
    (∀ b ∈ Sig.bufs ofbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ofbSig.words pb) (ofbPost pb) vs m₁ m' r →
      Curry.apply (ofbSig.words pb) (ofbPost pb) vs m₂ m' r := by
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
  simp only [ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ofbPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ofbPost pb) _ m₂ m' r
  dsimp only [Curry.apply, ofbPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [scheduleAt_congr hs, bytesAt_congr hv, cbcBlocksAt_congr (n := (n.setWidth pb).toNat)
    fun i hi => hd i (by rw [BitVec.toNat_setWidth] at hi; omega_arith)]
  exact h

theorem ofbPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (ofbSig.words pb).length →
    (∀ b ∈ Sig.bufs ofbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ofbSig.words pb) (ofbPost pb) vs m m₁ r →
      Curry.apply (ofbSig.words pb) (ofbPost pb) vs m m₂ r := by
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
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ofbPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ofbPost pb) _ m m₂ r
  dsimp only [Curry.apply, ofbPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega_arith), bytesAt_congr hv]
  exact h

theorem cfbEncPost_local : ∀ vs m₁ m₂ m' r, vs.length = (cfbSig.words pb).length →
    (∀ b ∈ Sig.bufs cfbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfbSig.words pb) (cfbEncPost pb) vs m₁ m' r →
      Curry.apply (cfbSig.words pb) (cfbEncPost pb) vs m₂ m' r := by
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
  simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbEncPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbEncPost pb) _ m₂ m' r
  dsimp only [Curry.apply, cfbEncPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [scheduleAt_congr hs, bytesAt_congr hv, cbcBlocksAt_congr (n := (n.setWidth pb).toNat)
    fun i hi => hd i (by rw [BitVec.toNat_setWidth] at hi; omega_arith)]
  exact h

theorem cfbEncPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (cfbSig.words pb).length →
    (∀ b ∈ Sig.bufs cfbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfbSig.words pb) (cfbEncPost pb) vs m m₁ r →
      Curry.apply (cfbSig.words pb) (cfbEncPost pb) vs m m₂ r := by
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
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbEncPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbEncPost pb) _ m m₂ r
  dsimp only [Curry.apply, cfbEncPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega_arith), bytesAt_congr hv]
  exact h

theorem cfbDecPost_local : ∀ vs m₁ m₂ m' r, vs.length = (cfbSig.words pb).length →
    (∀ b ∈ Sig.bufs cfbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfbSig.words pb) (cfbDecPost pb) vs m₁ m' r →
      Curry.apply (cfbSig.words pb) (cfbDecPost pb) vs m₂ m' r := by
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
  simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbDecPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbDecPost pb) _ m₂ m' r
  dsimp only [Curry.apply, cfbDecPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [scheduleAt_congr hs, bytesAt_congr hv, cbcBlocksAt_congr (n := (n.setWidth pb).toNat)
    fun i hi => hd i (by rw [BitVec.toNat_setWidth] at hi; omega_arith)]
  exact h

theorem cfbDecPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (cfbSig.words pb).length →
    (∀ b ∈ Sig.bufs cfbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cfbSig.words pb) (cfbDecPost pb) vs m m₁ r →
      Curry.apply (cfbSig.words pb) (cfbDecPost pb) vs m m₂ r := by
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
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbDecPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cfbDecPost pb) _ m m₂ r
  dsimp only [Curry.apply, cfbDecPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega_arith), bytesAt_congr hv]
  exact h

theorem cbcEncChainedPost_local : ∀ vs m₁ m₂ m' r, vs.length = (cbcChainedSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcChainedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcChainedSig.words pb) (cbcEncChainedPost pb) vs m₁ m' r →
      Curry.apply (cbcChainedSig.words pb) (cbcEncChainedPost pb) vs m₂ m' r := by
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
  simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cbcEncChainedPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cbcEncChainedPost pb) _ m₂ m' r
  dsimp only [Curry.apply, cbcEncChainedPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [scheduleAt_congr hs, bytesAt_congr hv, cbcBlocksAt_congr (n := (n.setWidth pb).toNat)
    fun i hi => hd i (by rw [BitVec.toNat_setWidth] at hi; omega_arith)]
  exact h

theorem cbcEncChainedPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (cbcChainedSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcChainedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcChainedSig.words pb) (cbcEncChainedPost pb) vs m m₁ r →
      Curry.apply (cbcChainedSig.words pb) (cbcEncChainedPost pb) vs m m₂ r := by
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
  simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cbcEncChainedPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cbcEncChainedPost pb) _ m m₂ r
  dsimp only [Curry.apply, cbcEncChainedPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega_arith), bytesAt_congr hv]
  exact h

theorem cbcDecChainedPost_local : ∀ vs m₁ m₂ m' r, vs.length = (cbcChainedSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcChainedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcChainedSig.words pb) (cbcDecChainedPost pb) vs m₁ m' r →
      Curry.apply (cbcChainedSig.words pb) (cbcDecChainedPost pb) vs m₂ m' r := by
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
  simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cbcDecChainedPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cbcDecChainedPost pb) _ m₂ m' r
  dsimp only [Curry.apply, cbcDecChainedPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [scheduleAt_congr hs, bytesAt_congr hv, cbcBlocksAt_congr (n := (n.setWidth pb).toNat)
    fun i hi => hd i (by rw [BitVec.toNat_setWidth] at hi; omega_arith)]
  exact h

theorem cbcDecChainedPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (cbcChainedSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcChainedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcChainedSig.words pb) (cbcDecChainedPost pb) vs m m₁ r →
      Curry.apply (cbcChainedSig.words pb) (cbcDecChainedPost pb) vs m m₂ r := by
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
  simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cbcDecChainedPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cbcDecChainedPost pb) _ m m₂ r
  dsimp only [Curry.apply, cbcDecChainedPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega_arith), bytesAt_congr hv]
  exact h

end VG.Proof.Cast5
