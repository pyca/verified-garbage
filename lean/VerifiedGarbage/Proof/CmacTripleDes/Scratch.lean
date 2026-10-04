import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# TDEA-CMAC with its working space as an argument

`vg_cmac_triple_des_init`, `update` and `finalize` keep their working space
in a frame of their own (`Verified.stackScratch`), around code proved with
the working space as an argument: `initScratchContract`,
`updateScratchContract` and `finalizeScratchContract` are the shared
contracts with a 640-byte `scratch` buffer appended, whatever it holds.

On x86 and ARMv7 the frame also holds a copy of the arguments passed on the
stack, which needs the pre- and postconditions to read the memory on entry
only within the function's buffers (`initPost_local`, `updatePost_local`,
`finalizePost_local`).
-/

namespace VG.Proof.CmacTripleDes

open VG.Spec.Cmac

/-- `vg_cmac_triple_des_init` with `scratch: *mut [u64; 80]`. -/
def initScratchSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("out", .array true .u8 400),
    ("scratch", .array true .u64 80)]

/-- `tdesInitContract`, whatever `scratch` is. -/
def initScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initScratchSig.contract A
    (pre := fun key keyLen out _scratch => tdesInitPre A.ptrBits key keyLen out)
    (post := fun key keyLen out _scratch => tdesInitPost A.ptrBits key keyLen out)
    (stack := stack)

/-- `vg_cmac_triple_des_update` with `scratch: *mut [u64; 80]`. -/
def updateScratchSig : Sig where
  params := [("schedule", .array false .u8 384), ("state", .array true .u8 8),
    ("data", .slice false (.array .u8 8) "n"), ("scratch", .array true .u64 80)]

/-- `tdesUpdateContract`, whatever `scratch` is. -/
def updateScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  updateScratchSig.contract A
    (post := fun schedule state data n _scratch => tdesUpdatePost A.ptrBits schedule state data n)
    (stack := stack)

/-- `vg_cmac_triple_des_finalize` with `scratch: *mut [u64; 80]`. -/
def finalizeScratchSig : Sig where
  params := [("key", .array false .u8 400), ("state", .array true .u8 8),
    ("last", .slice false .u8 "last_len"), ("scratch", .array true .u64 80)]

/-- `tdesFinalizeContract`, whatever `scratch` is. -/
def finalizeScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeScratchSig.contract A
    (pre := fun key state last lastLen _scratch => tdesFinalizePre A.ptrBits key state last lastLen)
    (post := fun key state last lastLen _scratch =>
      tdesFinalizePost A.ptrBits key state last lastLen)
    (stack := stack)

/-! ## Locality -/

theorem foldl_congr {α β : Type} {f g : β → α → β} :
    ∀ (l : List α) (b : β), (∀ x ∈ l, ∀ b, f b x = g b x) → l.foldl f b = l.foldl g b
  | [], _, _ => rfl
  | x :: l, b, h => by
    simp only [List.foldl_cons]
    rw [h x List.mem_cons_self]
    exact foldl_congr l _ fun y hy => h y (List.mem_cons_of_mem _ hy)

section

variable {m₁ m₂ : Mem} {p : Addr}

theorem bytesAt_congr {n : Nat} (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem tdesBytesAt_congr {n : Nat}
    (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.TripleDes.bytesAt m₂ p n = Spec.TripleDes.bytesAt m₁ p n := by
  simp only [Spec.TripleDes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem scheduleAt_congr
    (h : ∀ i < 384, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.TripleDes.scheduleAt m₂ p = Spec.TripleDes.scheduleAt m₁ p := by
  simp only [Spec.TripleDes.scheduleAt]
  congr 1
  funext i
  refine foldl_congr _ _ fun j hj out => ?_
  rw [h _ (by have := i.isLt; have := List.mem_range.mp hj; omega)]

theorem blocksAt_congr {b n : Nat}
    (h : ∀ i < b * n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    blocksAt m₂ p b n = blocksAt m₁ p b n := by
  simp only [blocksAt]
  refine List.map_congr_left fun i hi => bytesAt_congr fun k hk => ?_
  have := List.mem_range.mp hi
  have : b * i + k < b * n := by
    have := Nat.mul_le_mul_left b (Nat.succ_le_of_lt this)
    rw [Nat.mul_succ] at this; omega
  rw [Offset.add_add]
  exact h _ this

end

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on the
region. -/
theorem agree_of {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

variable (pb : Nat)

theorem initPre_local : ∀ vs m₁ m₂, vs.length = (tdesInitSig.words pb).length →
    (∀ b ∈ Sig.bufs tdesInitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (tdesInitSig.words pb) (tdesInitPre pb) vs m₁ →
      Curry.apply (tdesInitSig.words pb) (tdesInitPre pb) vs m₂
  | [_, _, _], _, _, _, _, h => h

theorem initPost_local : ∀ vs m₁ m₂ m' r, vs.length = (tdesInitSig.words pb).length →
    (∀ b ∈ Sig.bufs tdesInitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (tdesInitSig.words pb) (tdesInitPost pb) vs m₁ m' r →
      Curry.apply (tdesInitSig.words pb) (tdesInitPost pb) vs m₂ m' r
  | [key, kl, _], m₁, m₂, m', r, _, hb, h => by
    simp only [tdesInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hk := agree_of hb.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (tdesInitPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (tdesInitPost pb) _ m₂ m' r
    dsimp only [Curry.apply, tdesInitPost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le kl.toNat (2 ^ pb)
    rw [tdesBytesAt_congr (n := (kl.setWidth pb).toNat) fun i hi => hk i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h

theorem updatePost_local : ∀ vs m₁ m₂ m' r, vs.length = (tdesUpdateSig.words pb).length →
    (∀ b ∈ Sig.bufs tdesUpdateSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (tdesUpdateSig.words pb) (tdesUpdatePost pb) vs m₁ m' r →
      Curry.apply (tdesUpdateSig.words pb) (tdesUpdatePost pb) vs m₂ m' r
  | [sch, st, data, n], m₁, m₂, m', r, _, hb, h => by
    simp only [tdesUpdateSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hs := agree_of hb.1
    have ht := agree_of hb.2.1
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (tdesUpdatePost pb) _
      m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (tdesUpdatePost pb) _
      m₂ m' r
    dsimp only [Curry.apply, tdesUpdatePost, ArgWord.ofRaw] at h ⊢
    have hd := agree_of hb.2.2
    have := Nat.mod_le n.toNat (2 ^ pb)
    rw [scheduleAt_congr hs, bytesAt_congr ht, blocksAt_congr (b := 8) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h

theorem finalizePre_local : ∀ vs m₁ m₂, vs.length = (tdesFinalizeSig.words pb).length →
    (∀ b ∈ Sig.bufs tdesFinalizeSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (tdesFinalizeSig.words pb) (tdesFinalizePre pb) vs m₁ →
      Curry.apply (tdesFinalizeSig.words pb) (tdesFinalizePre pb) vs m₂
  | [_, _, _, _], _, _, _, _, h => h

theorem finalizePost_local : ∀ vs m₁ m₂ m' r, vs.length = (tdesFinalizeSig.words pb).length →
    (∀ b ∈ Sig.bufs tdesFinalizeSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (tdesFinalizeSig.words pb) (tdesFinalizePost pb) vs m₁ m' r →
      Curry.apply (tdesFinalizeSig.words pb) (tdesFinalizePost pb) vs m₂ m' r
  | [key, st, last, ll], m₁, m₂, m', r, _, hb, h => by
    simp only [tdesFinalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hk := agree_of hb.1
    have ht := agree_of hb.2.1
    have hl := agree_of hb.2.2
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (tdesFinalizePost pb) _
      m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (tdesFinalizePost pb) _
      m₂ m' r
    dsimp only [Curry.apply, tdesFinalizePost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le ll.toNat (2 ^ pb)
    rw [scheduleAt_congr fun i hi => hk i (by omega), bytesAt_congr ht,
      bytesAt_congr (n := (ll.setWidth pb).toNat) fun i hi => hl i (by
        rw [BitVec.toNat_setWidth] at hi; omega),
      show key + 384 = key + BitVec.ofNat 64 384 from rfl,
      bytesAt_congr (m₁ := m₁) (n := 16) fun i hi => by
        rw [Offset.add_add]; exact hk _ (by omega)]
    exact h

end VG.Proof.CmacTripleDes
