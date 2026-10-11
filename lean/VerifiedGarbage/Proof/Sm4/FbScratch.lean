import VerifiedGarbage.Spec.Sm4.Ofb
import VerifiedGarbage.Spec.Sm4.Cfb
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SM4-OFB and SM4-CFB128 with their working space as an argument

`fbScratchContract n post` is an OFB or CFB128 contract (one signature,
`ofbSig = cfbSig`) with a `scratch` buffer of `n` words appended, whatever it holds (each
target lays out its own), for the frame that keeps it on the stack
(`Verified.stackScratchWiped`), which needs each postcondition to read the
memory on return only within the function's buffers (`ofbPostOut_local`,
…).
-/

namespace VG.Proof.Sm4

open VG.Spec.Sm4

/-- `vg_sm4_ofb` (and CFB128's functions) with `scratch: *mut [u64; n]`. -/
def fbScratchSig (n : Nat) : Sig where
  params := ofbSig.params ++ [("scratch", .array true .u64 n)]

/-- `ofbContract`'s postcondition. -/
def ofbPost (pb : Nat) : ofbSig.Post pb := fun schedule iv data n m m' _ =>
  let ciph := cipher (scheduleAt m schedule)
  Spec.Cbc.blocksAt m' data n.toNat = Spec.Ofb.crypt ciph (Spec.Aes.bytesAt m iv 16) (Spec.Cbc.blocksAt m data n.toNat) ∧
    Spec.Aes.bytesAt m' iv 16 = Spec.Ofb.next ciph (Spec.Aes.bytesAt m iv 16) n.toNat

/-- `cfbEncryptContract`'s postcondition. -/
def cfbEncPost (pb : Nat) : ofbSig.Post pb := fun schedule iv data n m m' _ =>
  let cs := Spec.Cfb.encrypt (cipher (scheduleAt m schedule)) (Spec.Aes.bytesAt m iv 16) (Spec.Cbc.blocksAt m data n.toNat)
  Spec.Cbc.blocksAt m' data n.toNat = cs ∧ Spec.Aes.bytesAt m' iv 16 = Spec.Cbc.next (Spec.Aes.bytesAt m iv 16) cs

/-- `cfbDecryptContract`'s postcondition. -/
def cfbDecPost (pb : Nat) : ofbSig.Post pb := fun schedule iv data n m m' _ =>
  let cs := Spec.Cbc.blocksAt m data n.toNat
  Spec.Cbc.blocksAt m' data n.toNat = Spec.Cfb.decrypt (cipher (scheduleAt m schedule)) (Spec.Aes.bytesAt m iv 16) cs ∧
    Spec.Aes.bytesAt m' iv 16 = Spec.Cbc.next (Spec.Aes.bytesAt m iv 16) cs

/-- An OFB or CFB128 contract with the postcondition `post`, whatever
`scratch` is. -/
def fbScratchContract {M : ISA} (A : Abi M) (n : Nat) (post : (pb : Nat) → ofbSig.Post pb) (stack : Nat := 0) :
    Contract M :=
  (fbScratchSig n).contract A
    (post := fun schedule iv data len _scratch => post A.ptrBits schedule iv data len)
    (writeArgs := true) (stack := stack)

section

variable {m₁ m₂ : Mem} {p : Addr}

private theorem bytesAt_congr {k : Nat}
    (h : ∀ i < k, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m₂ p k = Spec.Aes.bytesAt m₁ p k := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

private theorem cbcBlocksAt_congr {n : Nat}
    (h : ∀ i < 16 * n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Cbc.blocksAt m₂ p n = Spec.Cbc.blocksAt m₁ p n := by
  simp only [Spec.Cbc.blocksAt]
  refine List.map_congr_left fun i hi => bytesAt_congr fun j hj => ?_
  have := List.mem_range.mp hi
  rw [Offset.add_add]
  exact h _ (by omega)

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

theorem ofbPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (ofbSig.words pb).length →
    (∀ b ∈ Sig.bufs ofbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ofbSig.words pb) (ofbPost pb) vs m m₁ r → Curry.apply (ofbSig.words pb) (ofbPost pb) vs m m₂ r
  | [_, iv, data, n], m, m₁, m₂, r, _, hb, h => by
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
    Curry.apply (ofbSig.words pb) (cfbEncPost pb) vs m m₁ r → Curry.apply (ofbSig.words pb) (cfbEncPost pb) vs m m₂ r
  | [_, iv, data, n], m, m₁, m₂, r, _, hb, h => by
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
    Curry.apply (ofbSig.words pb) (cfbDecPost pb) vs m m₁ r → Curry.apply (ofbSig.words pb) (cfbDecPost pb) vs m m₂ r
  | [_, iv, data, n], m, m₁, m₂, r, _, hb, h => by
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

end VG.Proof.Sm4
