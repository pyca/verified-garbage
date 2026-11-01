module

public import VerifiedGarbage.Proof.Sm4.Contract
public import VerifiedGarbage.Spec.Sm4.Gcm
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# SM4's counter mode with `inc₃₂` with its working space as an argument

As `ctrScratchContract` (`Scratch.lean`) for `vg_sm4_ctr`:
`ctr32ScratchContract n` is `vg_sm4_ctr32`'s contract with a `scratch`
buffer of `n` words appended, whatever it holds, for the frames that keep
the working space on the stack (`Verified.stackScratchWiped`), which need
the postcondition to read the memory on return only within the function's
buffers (`ctr32PostOut_local`) and on entry only within them
(`ctr32Post_local`).
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG.Spec.Sm4

/-- `vg_sm4_ctr32` with `scratch: *mut [u64; n]`. -/
def ctr32ScratchSig (n : Nat) : Sig where
  params := [("schedule", .array false .u8 128), ("counter", .array true .u8 16),
    ("data", .slice true (.array .u8 16) "n"), ("scratch", .array true .u64 n)]

/-- `ctr32Contract`'s postcondition. -/
def ctr32Post (pb : Nat) : ctr32Sig.Post pb := fun schedule counter data n m m' _ =>
  Spec.Gcm.blocksAt m' data n.toNat =
      Spec.Gcm.ctr32 (gcmCipher (scheduleAt m schedule)) (Spec.Gcm.blockAt m counter)
        (Spec.Gcm.blocksAt m data n.toNat) ∧
    Spec.Gcm.blockAt m' counter = Nat.repeat Spec.Gcm.inc32 n.toNat (Spec.Gcm.blockAt m counter)

/-- `ctr32Contract`, whatever `scratch` is. -/
def ctr32ScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (ctr32ScratchSig n).contract A
    (post := fun schedule counter data len _scratch => ctr32Post A.ptrBits schedule counter data len)
    (writeArgs := true) (stack := stack)

theorem ctr32Contract_eq {M : ISA} (A : Abi M) (stack : Nat) :
    ctr32Contract A stack = ctr32Sig.contract A (post := ctr32Post A.ptrBits) (writeArgs := true)
      (stack := stack) := rfl

/-! ## Locality -/

section

variable {m₁ m₂ : Mem} {p : Addr}

private theorem foldl_congr {α β : Type} {f g : β → α → β} :
    ∀ (l : List α) (b : β), (∀ x ∈ l, ∀ b, f b x = g b x) → l.foldl f b = l.foldl g b
  | [], _, _ => rfl
  | x :: l, b, h => by
    simp only [List.foldl_cons]
    rw [h x List.mem_cons_self]
    exact foldl_congr l _ fun y hy => h y (List.mem_cons_of_mem _ hy)

private theorem scheduleAt_congr
    (h : ∀ i < 128, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    scheduleAt m₂ p = scheduleAt m₁ p := by
  simp only [scheduleAt]
  congr 1
  funext i
  refine foldl_congr _ _ fun j hj out => ?_
  rw [h _ (by have := i.isLt; have := List.mem_range.mp hj; omega)]

private theorem bytesAt_congr {k : Nat}
    (h : ∀ i < k, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m₂ p k = Spec.Aes.bytesAt m₁ p k := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

private theorem gcmBlockAt_congr (h : ∀ i < 16, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Gcm.blockAt m₂ p = Spec.Gcm.blockAt m₁ p := by
  simp only [Spec.Gcm.blockAt]
  rw [bytesAt_congr h]

private theorem gcmBlocksAt_congr {n : Nat}
    (h : ∀ i < n * 16, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Gcm.blocksAt m₂ p n = Spec.Gcm.blocksAt m₁ p n := by
  simp only [Spec.Gcm.blocksAt]
  refine List.map_congr_left fun i hi => gcmBlockAt_congr fun j hj => ?_
  have := List.mem_range.mp hi
  rw [Offset.add_add]
  exact h _ (by omega)

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on the
region. -/
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

theorem ctr32PostOut_local : ∀ vs m m₁ m₂ r, vs.length = (ctr32Sig.words pb).length →
    (∀ b ∈ Sig.bufs ctr32Sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ctr32Sig.words pb) (ctr32Post pb) vs m m₁ r →
      Curry.apply (ctr32Sig.words pb) (ctr32Post pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ctr, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [ctr32Sig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ctr32Post pb) _
    m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ctr32Post pb) _
    m m₂ r
  dsimp only [Curry.apply, ctr32Post, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [gcmBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; have := Nat.mul_le_mul_right 16 this; omega), gcmBlockAt_congr hc]
  exact h

theorem ctr32Post_local : ∀ vs m₁ m₂ m' r, vs.length = (ctr32Sig.words pb).length →
    (∀ b ∈ Sig.bufs ctr32Sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ctr32Sig.words pb) (ctr32Post pb) vs m₁ m' r →
      Curry.apply (ctr32Sig.words pb) (ctr32Post pb) vs m₂ m' r := by
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
  simp only [ctr32Sig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ctr32Post pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ctr32Post pb) _ m₂ m' r
  dsimp only [Curry.apply, ctr32Post, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [scheduleAt_congr hs, gcmBlockAt_congr hv, gcmBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; have := Nat.mul_le_mul_right 16 this; omega)]
  exact h

end VG.Proof.Sm4
