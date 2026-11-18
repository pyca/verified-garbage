module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.RandomSignRemaining
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomState
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Impl.Dsa.AArch64.Random
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp

/-! ### `Dsa.AArch64.RandomSignSaved`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.RandomSignEntry`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.RandomSlots`, which this module and modules that import it used -/

section

/-! Exact memory effects of copying stack argument slots. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def randomSlotsMem (B : Addr) (m : Mem) : List (Nat × Nat) → Mem
  | [] => m
  | (src, dst) :: rest => randomSlotsMem B (m.writeW (off B dst) (word m B src)) rest

theorem random_copySlot_ok {s : State} {B : Addr} (src dst : Nat)
    (hsp : s.sp = B)
    (hsrc : src % 8 = 0 ∧ src < 32768) (hdst : dst < 4096)
    (hr : InRegions (s.rd ++ s.wr) (off B src) 8) (hw : InRegions s.wr (off B dst) 8) :
    WP isa (.block (Random.copySlot src dst)) s fun t =>
      t.mem = s.mem.writeW (off B dst) (word s.mem B src) ∧ Keep [.x0, .x15] s t := by
  refine WP.keep [.x0, .x15] (Q := fun t => t.mem = s.mem.writeW (off B dst) (word s.mem B src)) ?_ rfl rfl rfl
  unfold Random.copySlot Random.store
  brun [exec_ldrSp hsrc, exec_addSp hdst, hsp, hr, hw]

theorem random_copySlots_ok {s : State} {B : Addr} (slots : List (Nat × Nat))
    (hsp : s.sp = B)
    (hslots : ∀ p ∈ slots, (p.1 % 8 = 0 ∧ p.1 < 32768) ∧ p.2 < 4096)
    (hr : ∀ p ∈ slots, InRegions (s.rd ++ s.wr) (off B p.1) 8)
    (hw : ∀ p ∈ slots, InRegions s.wr (off B p.2) 8) :
    WP isa (.block (slots.flatMap (fun p => Random.copySlot p.1 p.2))) s fun t =>
      t.mem = randomSlotsMem B s.mem slots ∧ Keep [.x0, .x15] s t := by
  induction slots generalizing s with
  | nil => exact WP.block_nil ⟨rfl, Keep.refl _ _⟩
  | cons p rest ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (random_copySlot_ok p.1 p.2 hsp (hslots p (by simp)).1 (hslots p (by simp)).2 (hr p (by simp)) (hw p (by simp)))
      fun u ⟨hum, hku⟩ => ?_
    refine WP.mono (ih (hku.sp.trans hsp)
      (fun q hq => hslots q (List.mem_cons_of_mem _ hq))
      (fun q hq => by rw [hku.rd, hku.wr]; exact hr q (List.mem_cons_of_mem _ hq))
      (fun q hq => by rw [hku.wr]; exact hw q (List.mem_cons_of_mem _ hq)))
      fun t ⟨htm, hkt⟩ => ⟨by rw [htm, hum]; rfl, (hku.trans hkt).mono (by decide)⟩

theorem random_slots_outside (B : Addr) (m : Mem) (slots : List (Nat × Nat)) (o n : Nat)
    (hslots : ∀ p ∈ slots, o ≤ p.2 ∧ p.2 + 8 ≤ o + n ∧ p.2 + 8 ≤ 2 ^ 64) :
    Outside B o n m (randomSlotsMem B m slots) := by
  induction slots generalizing m with
  | nil => exact Outside.refl _ _ _ _
  | cons p rest ih =>
    have hp := hslots p (by simp)
    exact ((writeW_outside _ B _ hp.2.2).mono hp.1 hp.2.1).trans
      (ih _ (fun q hq => hslots q (List.mem_cons_of_mem _ hq)))

theorem random_word_write_other (m : Mem) (B : Addr) (src dst : Nat) (v : BitVec 64)
    (hs : src + 8 ≤ 2 ^ 64) (hd : dst + 8 ≤ 2 ^ 64)
    (h : src + 8 ≤ dst ∨ dst + 8 ≤ src) :
    word (m.writeW (off B dst) v) B src = word m B src :=
  (writeW_outside m B v hd).word h hs


end VG.Proof.Dsa.AArch64

end

end

/-! Save the randomized signer's ABI arguments in its private stack frame. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def randomEntryHeaderMem (s : State) (B : Addr) : Mem :=
  ((((((((((((s.mem.writeW (off B Random.oOut) (s.gpr .x0)).writeW (off B Random.oOutLen) (s.gpr .x1)).writeW (off B Random.oUsedPtr) (s.gpr .x2)).writeW (off B Random.oKey) (s.gpr .x3)).writeW (off B Random.oKeyLen) (s.gpr .x4)).writeW (off B Random.oPLen) (s.gpr .x5)).writeW (off B Random.oQLen) (s.gpr .x6)).writeW (off B Random.oDigest) (s.gpr .x7)).writeW (off B RandomSign.oLink) (s.gpr .x30)).writeW (off B Random.oQ) (s.gpr .x3 + s.gpr .x5)).writeW (off B Random.oUsed) (0 : BitVec 64)).writeW (off B Random.oAttempts) (8 : BitVec 64))

theorem random_entryHeader_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B) :
    WP isa (.block RandomSign.entryHeader) s fun t =>
      t.mem = randomEntryHeaderMem s B ∧ Keep [.x0, .x4, .x15] s t := by
  refine WP.keep [.x0, .x4, .x15] (Q := fun t => t.mem = randomEntryHeaderMem s B) ?_ rfl rfl rfl
  unfold RandomSign.entryHeader Random.store randomEntryHeaderMem
  brun [hsp,
    exec_addSp (show Random.oOut < 4096 by decide), hs.st (d := Random.oOut) (by decide),
    exec_addSp (show Random.oOutLen < 4096 by decide), hs.st (d := Random.oOutLen) (by decide),
    exec_addSp (show Random.oUsedPtr < 4096 by decide), hs.st (d := Random.oUsedPtr) (by decide),
    exec_addSp (show Random.oKey < 4096 by decide), hs.st (d := Random.oKey) (by decide),
    exec_addSp (show Random.oKeyLen < 4096 by decide), hs.st (d := Random.oKeyLen) (by decide),
    exec_addSp (show Random.oPLen < 4096 by decide), hs.st (d := Random.oPLen) (by decide),
    exec_addSp (show Random.oQLen < 4096 by decide), hs.st (d := Random.oQLen) (by decide),
    exec_addSp (show Random.oDigest < 4096 by decide), hs.st (d := Random.oDigest) (by decide),
    exec_addSp (show RandomSign.oLink < 4096 by decide), hs.st (d := RandomSign.oLink) (by decide),
    exec_addSp (show Random.oQ < 4096 by decide), hs.st (d := Random.oQ) (by decide),
    exec_addSp (show Random.oUsed < 4096 by decide), hs.st (d := Random.oUsed) (by decide),
    exec_addSp (show Random.oAttempts < 4096 by decide), hs.st (d := Random.oAttempts) (by decide)]
  rfl

theorem random_entry_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hr : ∀ p ∈ RandomSign.incomingSlots, InRegions (s.rd ++ s.wr) (off B p.1) 8) :
    WP isa (.block RandomSign.entry) s fun t =>
      t.mem = randomSlotsMem B (randomEntryHeaderMem s B) RandomSign.incomingSlots ∧
      Keep [.x0, .x4, .x15] s t := by
  unfold RandomSign.entry
  rw [WP.block_append_iff]
  refine WP.mono (random_entryHeader_ok hs hsp) fun u ⟨hum, hku⟩ => ?_
  have hus := hs.congr hku.wr
  refine WP.mono (random_copySlots_ok RandomSign.incomingSlots
    (hku.sp.trans hsp)
    (by intro p hp; simp only [RandomSign.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp;
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun p hp => by rw [hku.rd, hku.wr]; exact hr p hp)
    (fun p hp => hus.st (by
      simp only [RandomSign.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide)))
    fun t ⟨htm, hkt⟩ => ⟨by rw [htm, hum], (hku.trans hkt).mono (by decide)⟩

private theorem extend_entry_frame {B : Addr} {m m' : Mem} {d : Nat} (v : BitVec 64)
    (h : Outside B 0 Random.frameBytes m m') (hd : d + 8 ≤ Random.frameBytes) :
    Outside B 0 Random.frameBytes m (m'.writeW (off B d) v) :=
  h.trans ((writeW_outside _ B _ (by unfold Random.frameBytes at hd; omega_using [hd])).mono (Nat.zero_le _) hd)

theorem random_entryHeader_outside (s : State) (B : Addr) :
    Outside B 0 Random.frameBytes s.mem (randomEntryHeaderMem s B) := by
  unfold randomEntryHeaderMem
  repeat' apply extend_entry_frame _ _ (by decide)
  exact Outside.refl _ _ _ _

theorem random_entry_outside (s : State) (B : Addr) :
    Outside B 0 Random.frameBytes s.mem
      (randomSlotsMem B (randomEntryHeaderMem s B) RandomSign.incomingSlots) :=
  (random_entryHeader_outside s B).trans (random_slots_outside _ _ _ _ _ (by
    intro p hp
    simp only [RandomSign.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide))

end VG.Proof.Dsa.AArch64

end

end

/-! Values of the saved arguments and retry state after wrapper entry. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

def randomEntryValues (s : State) (B : Addr) : List (Nat × BitVec 64) :=
  [(40, s.gpr .x0), (48, s.gpr .x1), (56, s.gpr .x2), (64, s.gpr .x3),
    (72, s.gpr .x4), (80, s.gpr .x5), (88, s.gpr .x6), (96, s.gpr .x7), (232, s.gpr .x30),
    (168, s.gpr .x3 + s.gpr .x5), (144, 0), (152, 8),
    (104, word s.mem B 256), (112, word s.mem B 264), (120, word s.mem B 272),
    (128, word s.mem B 280), (136, word s.mem B 288)]

theorem random_entry_values (s : State) (B : Addr) :
    ∀ p ∈ randomEntryValues s B,
      word (randomSlotsMem B (randomEntryHeaderMem s B) RandomSign.incomingSlots) B p.1 = p.2 := by
  simp only [RandomSign.incomingSlots, randomSlotsMem, randomEntryHeaderMem,
      RandomSign.oLink, Random.oOut, Random.oOutLen, Random.oUsedPtr, Random.oKey, Random.oKeyLen, Random.oPLen,
      Random.oQ, Random.oUsed, Random.oAttempts, Random.oQLen, Random.oDigest, Random.oDigestLen,
      Random.oRand, Random.oRandLen, Random.oScratch, Random.oScratchLen]
  simp (disch := decide) only [random_word_write_other]
  intro p hp
  simp only [randomEntryValues, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [word_writeW_self, random_word_write_other]

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.RandomSignInputs`, which the modules that import this one used -/

section

/-! Read-only inputs and the sampler context derived from the public ABI. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

def randomInput (s : State) : VG.Proof.Dsa.RandomSignInput where
  pLen := (s.gpr .x5).toNat
  qLen := (s.gpr .x6).toNat
  key := Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat
  digest := Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat
  rand := Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat

def randomQBytes (s : State) : List Byte :=
  ((randomInput s).key.drop (randomInput s).pLen).take (randomInput s).qLen

theorem random_q_length {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    (randomQBytes s).length = (s.gpr .x6).toNat := by
  simp only [randomQBytes, randomInput, List.length_take, List.length_drop, bytesAt_length, h.keyLength]
  omega_using []

theorem random_q_decode (s : State) :
    Spec.Dsa.decodeBE (randomQBytes s) =
      (Spec.Dsa.privateKeyBytes (randomInput s).pLen (randomInput s).qLen (randomInput s).key).params.q := rfl

theorem random_initial_source {extra : Nat} {s : State} (h : RandomSignABI extra s)
    {p : Addr} {n : Nat} (hr : (⟨p, n⟩ : Region) ∈ s.rd)
    (hn : n ≤ 2 ^ 64) (hd : (below (s.sp) (extra + 256)).Disjoint ⟨p, n⟩) :
    Src (allocated Random.frameBytes s) (randomBase s) Random.frameBytes p (Spec.Rsa.bytesAt s.mem p n) :=
  src_of_region (List.mem_append_left _ hr) hn ((hd.sub_left (random_frame_sub h)).symm)

theorem random_initial_key {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    Src (allocated Random.frameBytes s) (randomBase s) Random.frameBytes (s.gpr .x3) (randomInput s).key :=
  random_initial_source h (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x4).isLt) h.stackKey

theorem random_initial_rand {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    Src (allocated Random.frameBytes s) (randomBase s) Random.frameBytes (stackArg s 1) (randomInput s).rand :=
  random_initial_source h (by rw [h.rd]; simp) (Nat.le_of_lt (stackArg s 2).isLt) h.stackRand

theorem random_initial_digest {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    Src (allocated Random.frameBytes s) (randomBase s) Random.frameBytes (s.gpr .x7) (randomInput s).digest :=
  random_initial_source h (by rw [h.rd]; simp) (Nat.le_of_lt (stackArg s 0).isLt) h.stackDigest

theorem random_initial_q {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    Src (allocated Random.frameBytes s) (randomBase s) Random.frameBytes
      (s.gpr .x3 + s.gpr .x5) (randomQBytes s) := by
  have hh := random_src_take (random_src_drop (random_initial_key h) (randomInput s).pLen) (randomInput s).qLen
  simpa only [randomQBytes, randomInput, ofNat_toNat64] using hh

def randomContextOf {extra : Nat} {s : State} (h : RandomSignABI extra s) (m : Mem)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) : RandomContext where
  B := randomBase s
  initialMem := m
  R := stackArg s 1
  Q := s.gpr .x3 + s.gpr .x5
  qBytes := randomQBytes s
  rand := (randomInput s).rand
  qlen := by
    rw [random_q_length h]
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega_using [hl]
  randBound := by rw [randomInput, bytesAt_length]; exact (stackArg s 2).isLt
  positive := by
    have hh := (VG.Proof.Dsa.random_valid_scan (randomQBytes s)).mp hq
    omega_using [hh]

end VG.Proof.Dsa.AArch64

end

end

/-! Saved public arguments retained throughout randomized signing. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

def randomSavedValues (s : State) : List (Nat × BitVec 64) :=
  [(40, s.gpr .x0), (48, s.gpr .x1), (56, s.gpr .x2), (64, s.gpr .x3),
    (72, s.gpr .x4), (80, s.gpr .x5), (88, s.gpr .x6), (96, s.gpr .x7),
    (104, stackArg s 0), (112, stackArg s 1), (120, stackArg s 2),
    (128, stackArg s 3), (136, stackArg s 4)]

def RandomSaved (s : State) (m : Mem) : Prop :=
  ∀ p ∈ randomSavedValues s, word m (randomBase s) p.1 = p.2

theorem random_saved_bound {s : State} {p : Nat × BitVec 64} (hp : p ∈ randomSavedValues s) :
    40 ≤ p.1 ∧ p.1 + 8 ≤ 144 := by
  simp only [randomSavedValues, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)

theorem RandomSaved.congr {s : State} {m m' : Mem} (h : RandomSaved s m)
    (hw : ∀ d, 40 ≤ d → d + 8 ≤ 144 → word m' (randomBase s) d = word m (randomBase s) d) : RandomSaved s m' :=
  fun p hp => (hw _ (random_saved_bound hp).1 (random_saved_bound hp).2).trans (h p hp)

theorem random_entry_stackWord (s : State) (j : Nat) :
    word s.mem (randomBase s) (256 + 8 * j) = stackArg s j := by
  unfold VG.Proof.Bignum.word
  rw [random_incoming_address]
  rfl

theorem random_saved_entry (s : State) :
    RandomSaved s (randomSlotsMem (randomBase s)
      (randomEntryHeaderMem (allocated Random.frameBytes s) (randomBase s)) RandomSign.incomingSlots) := by
  have hv := random_entry_values (allocated Random.frameBytes s) (randomBase s)
  have hs : ∀ p ∈ randomSavedValues s, p ∈ randomEntryValues (allocated Random.frameBytes s) (randomBase s) := by
    intro p hp
    simp only [randomSavedValues, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [randomEntryValues, allocated, random_entry_stackWord s 0,
        random_entry_stackWord s 1, random_entry_stackWord s 2, random_entry_stackWord s 3,
        random_entry_stackWord s 4]
  exact fun p hp => hv p (hs p hp)

end VG.Proof.Dsa.AArch64
