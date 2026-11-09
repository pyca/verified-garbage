module

public import VerifiedGarbage.Spec.Camellia.Ctr
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Camellia.Scratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Camellia-CTR with its working space as an argument

`ctrScratchContract n` is `ctrContract` with a `scratch` buffer of `n`
words appended, whatever it holds (each target lays out its own), for the
frame that keeps it on the stack (`Verified.stackScratchWiped`), which
needs `ctrPost` to read the memory on return only within the function's
buffers (`ctrPostOut_local`).
-/

@[expose] public section

namespace VG.Proof.Camellia

open VG.Spec.Camellia

/-- `ctrPost` on the subkeys at `schedule`, for `rounds` of 18 or 24. -/
def ctrPostSk (pb : Nat) : ctrSig.Post pb := fun schedule rounds ctr data n m m' _ =>
  (rounds.toNat = 18 ∨ rounds.toNat = 24) →
    Spec.Cbc.blocksAt m' data n.toNat =
        Spec.Ctr.crypt (cipher (subkeysAt m schedule rounds.toNat)) (Spec.Aes.bytesAt m ctr 16)
          (Spec.Cbc.blocksAt m data n.toNat) ∧
      Spec.Aes.bytesAt m' ctr 16 = Spec.Ctr.next (Spec.Aes.bytesAt m ctr 16) n.toNat

/-- `ctrContract` with `ctrPostSk`. -/
def ctrContractSk {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ctrSig.contract A (pre := ctrPre A.ptrBits) (post := ctrPostSk A.ptrBits) (writeArgs := true)
    (stack := stack)

/-- `vg_camellia_ctr` with `scratch: *mut [u64; n]`. -/
def ctrScratchSig (n : Nat) : Sig where
  params := ctrSig.params ++ [("scratch", .array true .u64 n)]

/-- `ctrContractSk`, whatever `scratch` is. -/
def ctrScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (ctrScratchSig n).contract A
    (pre := fun schedule rounds ctr data n _scratch => ctrPre A.ptrBits schedule rounds ctr data n)
    (post := fun schedule rounds ctr data n _scratch => ctrPostSk A.ptrBits schedule rounds ctr data n)
    (writeArgs := true) (stack := stack)

theorem ctrScratchContract_eq {M : ISA} (A : Abi M) (n stack : Nat) :
    ctrScratchContract A n stack = Sig.scratchContract A ctrSig "scratch" .u64 n
      (ctrPre A.ptrBits) (ctrPostSk A.ptrBits) true stack := rfl

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

theorem ctrPre_local : ∀ vs m₁ m₂, vs.length = (ctrSig.words pb).length →
    (∀ b ∈ Sig.bufs ctrSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ctrSig.words pb) (ctrPre pb) vs m₁ → Curry.apply (ctrSig.words pb) (ctrPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 4
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

theorem ctrPost_local : ∀ vs m₁ m₂ m' r, vs.length = (ctrSig.words pb).length →
    (∀ b ∈ Sig.bufs ctrSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ctrSig.words pb) (ctrPostSk pb) vs m₁ m' r → Curry.apply (ctrSig.words pb) (ctrPostSk pb) vs m₂ m' r := by
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
  simp only [ctrSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (ctrPostSk pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (ctrPostSk pb) _ m₂ m' r
  dsimp only [Curry.apply, ctrPostSk, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [subkeysAt_congr (by simp only [scheduleLength]; omega) fun i hi => hs i (by omega), bytesAt_congr' hv,
    cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by rw [BitVec.toNat_setWidth] at hi; omega)]
  exact h hR

theorem ctrPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (ctrSig.words pb).length →
    (∀ b ∈ Sig.bufs ctrSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ctrSig.words pb) (ctrPostSk pb) vs m m₁ r →
      Curry.apply (ctrSig.words pb) (ctrPostSk pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ctr, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [ctrSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (ctrPostSk pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
    (ctrPostSk pb) _ m m₂ r
  dsimp only [Curry.apply, ctrPostSk, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega), bytesAt_congr' hc]
  exact h hR

theorem ctrPost_of_sk (pb : Nat) : Curry.Imp _ (ctrPostSk pb) (ctrPost pb) := by
  intro _ _ _ _ _ _ _ _ h key hk
  rw [← subkeysAt_of_keySchedule hk]
  exact h (rounds_of_keySchedule hk)

theorem ctr_of_sk {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (ctrContractSk A stack)) : Verified T c (ctrContract A stack) :=
  verified_of_post h (ctrPost_of_sk A.ptrBits)

end VG.Proof.Camellia
