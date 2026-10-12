module

public import VerifiedGarbage.Spec.Camellia.Cbc
public import VerifiedGarbage.Proof.Camellia.Scratch
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Camellia-CBC with its working space as an argument

`cbcEncScratchContract n` and `cbcDecScratchContract n` are
`cbcEncryptContract` and `cbcDecryptContract` with a `scratch` buffer of
`n` words appended, whatever it holds (each target lays out its own), for
the frame that keeps it on the stack (`Verified.stackScratchWiped`), which
needs `cbcEncryptPost` and `cbcDecryptPost` to read the memory on return
only within the function's buffers (`cbcEncPostOut_local`,
`cbcDecPostOut_local`), and the precondition and postconditions to read the
memory on entry only within them too (`cbcPre_local`, `cbcEncryptPost_local`, …).
-/

@[expose] public section

namespace VG.Proof.Camellia

open VG.Spec.Camellia

/-- `vg_camellia_cbc_decrypt` with `scratch: *mut [u64; n]`. -/
def cbcScratchSig (n : Nat) : Sig where
  params := cbcSig.params ++ [("scratch", .array true .u64 n)]

/-- `cbcEncryptContract`, whatever `scratch` is. -/
def cbcEncScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (cbcScratchSig n).contract A
    (pre := fun schedule rounds iv data n _scratch => cbcPre A.ptrBits schedule rounds iv data n)
    (post := fun schedule rounds iv data n _scratch => cbcEncryptPost A.ptrBits schedule rounds iv data n)
    (writeArgs := true) (stack := stack)

theorem cbcEncScratchContract_eq {M : ISA} (A : Abi M) (n stack : Nat) :
    cbcEncScratchContract A n stack = Sig.scratchContract A cbcSig "scratch" .u64 n
      (cbcPre A.ptrBits) (cbcEncryptPost A.ptrBits) true stack := rfl

/-- `cbcDecryptContract`, whatever `scratch` is. -/
def cbcDecScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (cbcScratchSig n).contract A
    (pre := fun schedule rounds iv data n _scratch => cbcPre A.ptrBits schedule rounds iv data n)
    (post := fun schedule rounds iv data n _scratch => cbcDecryptPost A.ptrBits schedule rounds iv data n)
    (writeArgs := true) (stack := stack)

theorem cbcDecScratchContract_eq {M : ISA} (A : Abi M) (n stack : Nat) :
    cbcDecScratchContract A n stack = Sig.scratchContract A cbcSig "scratch" .u64 n
      (cbcPre A.ptrBits) (cbcDecryptPost A.ptrBits) true stack := rfl

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

theorem cbcPre_local : ∀ vs m₁ m₂, vs.length = (cbcSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcSig.words pb) (cbcPre pb) vs m₁ → Curry.apply (cbcSig.words pb) (cbcPre pb) vs m₂
  | [_, _, _, _, _], _, _, _, _, h => h

theorem cbcEncryptPost_local : ∀ vs m₁ m₂ m' r, vs.length = (cbcSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcSig.words pb) (cbcEncryptPost pb) vs m₁ m' r →
      Curry.apply (cbcSig.words pb) (cbcEncryptPost pb) vs m₂ m' r
  | [_, _, iv, data, n], m₁, m₂, m', r, _, hb, h => by
    simp only [cbcSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hs := agree_of hb.1
    have hv := agree_of hb.2.1
    have hd := agree_of hb.2.2
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (cbcEncryptPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (cbcEncryptPost pb) _ m₂ m' r
    dsimp only [Curry.apply, cbcEncryptPost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le n.toNat (2 ^ pb)
    intro hR
    rw [subkeysAt_congr (by simp only [scheduleLength]; omega) fun i hi => hs i (by omega), bytesAt_congr' hv,
      cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h hR

theorem cbcDecryptPost_local : ∀ vs m₁ m₂ m' r, vs.length = (cbcSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcSig.words pb) (cbcDecryptPost pb) vs m₁ m' r →
      Curry.apply (cbcSig.words pb) (cbcDecryptPost pb) vs m₂ m' r
  | [_, _, iv, data, n], m₁, m₂, m', r, _, hb, h => by
    simp only [cbcSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hs := agree_of hb.1
    have hv := agree_of hb.2.1
    have hd := agree_of hb.2.2
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (cbcDecryptPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (cbcDecryptPost pb) _ m₂ m' r
    dsimp only [Curry.apply, cbcDecryptPost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le n.toNat (2 ^ pb)
    intro hR
    rw [subkeysAt_congr (by simp only [scheduleLength]; omega) fun i hi => hs i (by omega), bytesAt_congr' hv,
      cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h hR

theorem cbcEncPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (cbcSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcSig.words pb) (cbcEncryptPost pb) vs m m₁ r →
      Curry.apply (cbcSig.words pb) (cbcEncryptPost pb) vs m m₂ r
  | [_, _, _, data, n], m, m₁, m₂, r, _, hb, h => by
    simp only [cbcSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hd := agree_of hb.2.2
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (cbcEncryptPost pb) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (cbcEncryptPost pb) _ m m₂ r
    dsimp only [Curry.apply, cbcEncryptPost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le n.toNat (2 ^ pb)
    intro hR
    rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h hR


theorem cbcDecPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (cbcSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcSig.words pb) (cbcDecryptPost pb) vs m m₁ r →
      Curry.apply (cbcSig.words pb) (cbcDecryptPost pb) vs m m₂ r
  | [_, _, _, data, n], m, m₁, m₂, r, _, hb, h => by
    simp only [cbcSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hd := agree_of hb.2.2
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (cbcDecryptPost pb) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (cbcDecryptPost pb) _ m m₂ r
    dsimp only [Curry.apply, cbcDecryptPost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le n.toNat (2 ^ pb)
    intro hR
    rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h hR

end VG.Proof.Camellia
