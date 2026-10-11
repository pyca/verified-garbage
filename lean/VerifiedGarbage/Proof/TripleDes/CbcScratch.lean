import VerifiedGarbage.Spec.TripleDes.Cbc
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Triple DES-CBC with its working space as an argument

`cbcEncScratchContract n` and `cbcDecScratchContract n` are
`cbcEncryptContract` and `cbcDecryptContract` with a `scratch` buffer of
`n` words appended, whatever it holds (each target lays out its own), for
the frame that keeps it on the stack (`Verified.stackScratchWiped`), which
needs `cbcEncPost` and `cbcDecPost` to read the memory on return only
within the function's buffers (`cbcEncPostOut_local`, `cbcDecPostOut_local`).
-/

namespace VG.Proof.TripleDes

open VG.Spec.TripleDes

/-- `vg_triple_des_cbc_decrypt` with `scratch: *mut [u64; n]`. -/
def cbcScratchSig (n : Nat) : Sig where
  params := cbcSig.params ++ [("scratch", .array true .u64 n)]

/-- `cbcDecryptContract`'s postcondition. -/
def cbcDecPost (pb : Nat) : cbcSig.Post pb := fun schedule iv data n m m' _ =>
  cbcBlocksAt m' data n.toNat =
    Spec.Cbc.decrypt (invCipher (scheduleAt m schedule)) (bytesAt m iv 8) (cbcBlocksAt m data n.toNat)

/-- `cbcEncryptContract`'s postcondition. -/
def cbcEncPost (pb : Nat) : cbcSig.Post pb := fun schedule iv data n m m' _ =>
  cbcBlocksAt m' data n.toNat =
    Spec.Cbc.encrypt (cipher (scheduleAt m schedule)) (bytesAt m iv 8) (cbcBlocksAt m data n.toNat)

/-- `cbcEncryptContract`, whatever `scratch` is. -/
def cbcEncScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (cbcScratchSig n).contract A
    (post := fun schedule iv data len _scratch => cbcEncPost A.ptrBits schedule iv data len)
    (writeArgs := true) (stack := stack)

/-- `cbcDecryptContract`, whatever `scratch` is. -/
def cbcDecScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (cbcScratchSig n).contract A
    (post := fun schedule iv data len _scratch => cbcDecPost A.ptrBits schedule iv data len)
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

theorem cbcEncPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (cbcSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcSig.words pb) (cbcEncPost pb) vs m m₁ r →
      Curry.apply (cbcSig.words pb) (cbcEncPost pb) vs m m₂ r
  | [_, _, data, n], m, m₁, m₂, r, _, hb, h => by
    simp only [cbcSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hd := agree_of hb.2.2
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cbcEncPost pb) _
      m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cbcEncPost pb) _
      m m₂ r
    dsimp only [Curry.apply, cbcEncPost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le n.toNat (2 ^ pb)
    rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h

theorem cbcDecPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (cbcSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcSig.words pb) (cbcDecPost pb) vs m m₁ r →
      Curry.apply (cbcSig.words pb) (cbcDecPost pb) vs m m₂ r
  | [_, _, data, n], m, m₁, m₂, r, _, hb, h => by
    simp only [cbcSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hd := agree_of hb.2.2
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cbcDecPost pb) _
      m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (cbcDecPost pb) _
      m m₂ r
    dsimp only [Curry.apply, cbcDecPost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le n.toNat (2 ^ pb)
    rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h

end VG.Proof.TripleDes
