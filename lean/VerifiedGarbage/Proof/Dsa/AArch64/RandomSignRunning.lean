module

import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomState
import VerifiedGarbage.Proof.Dsa.RandomEncoding
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomClear
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomMask
public import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Spec.Dsa.Random
import VerifiedGarbage.Proof.Dsa.AArch64.RandomScan
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFrame
public import VerifiedGarbage.Proof.Dsa.RandomSignRemaining
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
public import VerifiedGarbage.Impl.Dsa.AArch64.Random
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp

/-! ### `Dsa.AArch64.RandomSignEnv`, which this module and modules that import it used -/

section

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

end

end

/-! ### `Dsa.AArch64.RandomPrepareState`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.RandomPrepare`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.RandomPrepareFinish`, which only this module used -/

section

/-! The public q>1 decision and mask store at the end of initialization. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64 VG.Impl.Bignum.AArch64

private theorem compare_ok (s : State) :
    WP isa (.block [movi .x0 0, movi .x4 1, movi .x3 2, .subs .x .x3 .x9 .x3,
      .csel .x .x0 .x4 .x0, movi .x3 2, .subs .x .x3 .x10 .x3,
      .csel .x .x0 .x4 .x0]) s fun t =>
      t.gpr .x0 = (if 2 ≤ (s.gpr .x10).toNat then 1#64
        else if 2 ≤ (s.gpr .x9).toNat then 1#64 else 0#64) ∧ t.mem = s.mem := by
  brun [random_sub_carry, Bool.toNat_true, decide_eq_true_eq]
  rfl

private theorem finishTail_ok {s : State} {B : Addr} {w : Nat} {b : Byte} {m : BitVec 64}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (h8 : s.gpr .x8 = m) (h9 : s.gpr .x10 = b.setWidth 64)
    (h11 : s.gpr .x9 = BitVec.ofNat 64 w) (hw : w < 2 ^ 64) :
    WP isa (.block (Random.store Random.oMask .x8 ++
      [movi .x0 0, movi .x4 1, movi .x3 2, .subs .x .x3 .x9 .x3,
       .csel .x .x0 .x4 .x0, movi .x3 2, .subs .x .x3 .x10 .x3,
       .csel .x .x0 .x4 .x0])) s fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (if w < 2 ∧ b.toNat < 2 then 0 else 1) ∧
      t.mem = s.mem.writeW (off B Random.oMask) m ∧ Keep [.x0, .x3, .x4, .x15] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x15] (Q := fun u =>
    u.mem = s.mem.writeW (off B Random.oMask) m)
    (by unfold Random.store; brun [exec_addSp (show Random.oMask < 4096 by decide),
      hsp, hs.st (d := Random.oMask) (by decide), h8]) rfl rfl rfl)
    fun u ⟨hum, hku⟩ => ?_
  have hu9 := (hku.gpr .x9 (by decide)).trans h11
  have hu10 := (hku.gpr .x10 (by decide)).trans h9
  have hb : (b.setWidth 64).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega_using [])]
  refine WP.mono (WP.keep [.x0, .x3, .x4] (Q := fun t =>
    t.gpr .x0 = BitVec.ofNat 64 (if w < 2 ∧ b.toNat < 2 then 0 else 1) ∧ t.mem = u.mem)
    ?_ rfl rfl rfl) fun t ⟨⟨hta, htm⟩, hkt⟩ =>
      ⟨hta, htm.trans hum, (hku.trans hkt).mono (by decide)⟩
  refine WP.mono (compare_ok u) fun t ⟨ht, hm⟩ => ⟨?_, hm⟩
  rw [ht, hu9, hu10, hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
  by_cases hw2 : w < 2 <;> by_cases hb2 : b.toNat < 2 <;>
    simp (disch := omega) only [ite_eq_left, ite_eq_right] <;> rfl


theorem random_prepareFinish_ok {s : State} {B : Addr} {w : Nat} {b : Byte}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (ha : s.gpr .x0 = b.setWidth 64) (h11 : s.gpr .x9 = BitVec.ofNat 64 w) (hw : w < 2 ^ 64) :
    WP isa Random.prepareFinish s fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (if w < 2 ∧ b.toNat < 2 then 0 else 1) ∧
      t.mem = s.mem.writeW (off B Random.oMask) (randomMaskValue b.toNat) ∧
      Keep [.x0, .x3, .x4, .x8, .x10, .x15] s t := by
  unfold Random.prepareFinish
  refine WP.seq (WP.mono (WP.keep [.x10] (Q := fun u => u.gpr .x10 = b.setWidth 64 ∧ u.mem = s.mem)
      (by brun [ha]) rfl rfl rfl) fun u ⟨⟨hu9, hum⟩, hku⟩ => ?_)
  refine WP.seq (WP.mono (random_mask_ok u) fun v ⟨hv8, hvm, hkv⟩ => ?_)
  have hua := (hku.gpr .x0 (by decide)).trans ha
  have hb : (b.setWidth 64).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega_using [])]
  rw [hua, hb] at hv8
  have hk := hku.trans hkv
  refine WP.mono (finishTail_ok (hs.congr hk.wr) (hk.sp.trans hsp)
      hv8 ((hkv.gpr .x10 (by decide)).trans hu9) ((hk.gpr .x9 (by decide)).trans h11) hw)
    fun t ⟨hta, htm, hkt⟩ => ?_
  exact ⟨hta, by rw [htm, hvm, hum], (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64

end

end


/-! Initialization of the sampler, including its exact memory effects. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def randomPrepareMem (m : Mem) (B p : Addr) (bs : List Byte) : Mem :=
  (((randomClearMem m B).writeW (off B Random.oQ)
    (p + BitVec.ofNat 64 (bs.length - (VG.Proof.Dsa.significant bs).1))).writeW
    (off B Random.oWidth) (BitVec.ofNat 64 (VG.Proof.Dsa.significant bs).1)).writeW
    (off B Random.oMask) (randomMaskValue (VG.Proof.Dsa.significant bs).2.toNat)

theorem random_prepare_ok {s : State} {B p : Addr} {bs : List Byte}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hq : word s.mem B Random.oQ = p)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 bs.length)
    (hsrc : Src s B Random.frameBytes p bs)
    (hpos : 0 < bs.length) (hbound : bs.length < 2 ^ 64) :
    WP isa Random.prepare s fun t =>
      t.gpr .x0 = BitVec.ofNat 64
        (if (VG.Proof.Dsa.significant bs).1 < 2 ∧
          (VG.Proof.Dsa.significant bs).2.toNat < 2 then 0 else 1) ∧
      t.mem = randomPrepareMem s.mem B p bs ∧
      Keep [.x0, .x1, .x3, .x4, .x8, .x9, .x10, .x12, .x13, .x15] s t := by
  unfold Random.prepare
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (random_clear_ok hs hsp) fun u ⟨hum, hku⟩ => ?_
  have hus := hs.congr hku.wr
  have husp := hku.sp.trans hsp
  have huq : word u.mem B Random.oQ = p := by
    rw [hum, (random_clear_outside s.mem B).word (by decide) (by decide)]; exact hq
  have hul : word u.mem B Random.oQLen = BitVec.ofNat 64 bs.length := by
    rw [hum, (random_clear_outside s.mem B).word (by decide) (by decide)]; exact hl
  refine WP.mono (WP.keep [.x12, .x9] (Q := fun v =>
      v.gpr .x12 = p ∧ v.gpr .x9 = BitVec.ofNat 64 bs.length ∧ v.mem = u.mem)
      (by brun [exec_ldrSp (show Random.oQ % 8 = 0 ∧ Random.oQ < 32768 by decide),
        exec_ldrSp (show Random.oQLen % 8 = 0 ∧ Random.oQLen < 32768 by decide), husp, hus.ld (d := Random.oQ) (by decide),
        hus.ld (d := Random.oQLen) (by decide), huq, hul]) rfl rfl rfl)
    fun v ⟨⟨hv10, hv11, hvm⟩, hkv⟩ => ?_
  have hk := hku.trans hkv
  have hvsrc := hsrc.congrK (show InScr B Random.frameBytes s.mem v.mem from by
    rw [hvm, hum]; exact InScr.of_outside (random_clear_outside s.mem B) (by decide)) hk
  refine WP.seq (WP.mono (random_significant_ok hv10 hv11 hvsrc hpos hbound)
    fun w ⟨hw10, hw11, hwa, hwm, hkw⟩ => ?_)
  have hkw' := hk.trans hkw
  have hws := hs.congr hkw'.wr
  have hwsp := hkw'.sp.trans hsp
  refine WP.seq (WP.mono (WP.keep [.x15] (Q := fun x => x.mem =
      (w.mem.writeW (off B Random.oQ) (p + BitVec.ofNat 64
        (bs.length - (VG.Proof.Dsa.significant bs).1))).writeW
      (off B Random.oWidth) (BitVec.ofNat 64 (VG.Proof.Dsa.significant bs).1))
      (by unfold Random.store; brun [exec_addSp (show Random.oQ < 4096 by decide),
        exec_addSp (show Random.oWidth < 4096 by decide), hwsp, hws.st (d := Random.oQ) (by decide),
        hws.st (d := Random.oWidth) (by decide), hw10, hw11]) rfl rfl rfl)
    fun x ⟨hxm, hkx⟩ => ?_)
  have hkx' := hkw'.trans hkx
  refine WP.mono (random_prepareFinish_ok (hs.congr hkx'.wr)
    (hkx'.sp.trans hsp) ((hkx.gpr .x0 (by decide)).trans hwa)
    ((hkx.gpr .x9 (by decide)).trans hw11)
    (by have := VG.Proof.Dsa.significant_fits bs; omega_using [hbound, this]))
    fun t ⟨hta, htm, hkt⟩ => ?_
  exact ⟨hta, by rw [htm, hxm, hwm, hvm, hum]; rfl,
    (hkx'.trans hkt).mono (by decide)⟩

/-- Initialization returns success exactly for the spec's admissible modulus. -/
theorem random_prepare_valid {s : State} {B p : Addr} {bs : List Byte}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hq : word s.mem B Random.oQ = p)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 bs.length)
    (hsrc : Src s B Random.frameBytes p bs)
    (hpos : 0 < bs.length) (hbound : bs.length < 2 ^ 64) :
    WP isa Random.prepare s fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (if 1 < Spec.Dsa.decodeBE bs then 1 else 0) ∧
      t.mem = randomPrepareMem s.mem B p bs ∧
      Keep [.x0, .x1, .x3, .x4, .x8, .x9, .x10, .x12, .x13, .x15] s t := by
  refine WP.mono (random_prepare_ok hs hsp hq hl hsrc hpos hbound)
    fun t ⟨hta, htm, hkt⟩ => ⟨?_, htm, hkt⟩
  rw [hta]
  have hv := VG.Proof.Dsa.random_valid_scan_ge bs
  by_cases h : 1 < Spec.Dsa.decodeBE bs
  · have hn : ¬ ((VG.Proof.Dsa.significant bs).1 < 2 ∧
        (VG.Proof.Dsa.significant bs).2.toNat < 2) := by omega_using [hv, h]
    rw [ite_eq_right hn, ite_eq_left h]
  · have hn : (VG.Proof.Dsa.significant bs).1 < 2 ∧
        (VG.Proof.Dsa.significant bs).2.toNat < 2 := by omega_using [hv, h]
    rw [ite_eq_left hn, ite_eq_right h]

theorem random_prepare_width (m : Mem) (B p : Addr) (bs : List Byte) :
    word (randomPrepareMem m B p bs) B Random.oWidth =
      BitVec.ofNat 64 (Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE bs)) := by
  unfold randomPrepareMem
  rw [(writeW_outside _ B _ (by decide)).word (by decide) (by decide), word_writeW_self,
    VG.Proof.Dsa.random_drawBytes_scan]

theorem random_prepare_pointer (m : Mem) (B p : Addr) (bs : List Byte) :
    word (randomPrepareMem m B p bs) B Random.oQ =
      p + BitVec.ofNat 64 (bs.length - (VG.Proof.Dsa.significant bs).1) := by
  unfold randomPrepareMem
  rw [(writeW_outside _ B _ (by decide)).word (by decide) (by decide),
    (writeW_outside _ B _ (by decide)).word (by decide) (by decide), word_writeW_self]

theorem random_prepare_mask (m : Mem) (B p : Addr) (bs : List Byte) :
    word (randomPrepareMem m B p bs) B Random.oMask =
      randomMaskValue (VG.Proof.Dsa.significant bs).2.toNat := by
  unfold randomPrepareMem
  rw [word_writeW_self]

/-- All caller fields before q, and all memory after the nonce, are unchanged. -/
theorem random_prepare_outside (m : Mem) (B p : Addr) (bs : List Byte) :
    Outside B 168 64 m (randomPrepareMem m B p bs) := by
  unfold randomPrepareMem
  exact ((((random_clear_outside m B).mono (by decide) (by decide)).trans
    ((writeW_outside _ B _ (by decide)).mono (by decide) (by decide))).trans
    ((writeW_outside _ B _ (by decide)).mono (by decide) (by decide))).trans
    ((writeW_outside _ B _ (by decide)).mono (by decide) (by decide))

theorem random_prepare_zero (m : Mem) (B p : Addr) (bs : List Byte)
    (i : Nat) (hi : i < 32) :
    randomPrepareMem m B p bs (off B (200 + i)) = 0 := by
  have ho : ofs B (off B (200 + i)) = 200 + i := by
    have he : off B (200 + i) + BitVec.ofNat 64 0 = off B (200 + i) := BitVec.add_zero _
    simpa only [he, Nat.add_zero] using ofs_off B (d := 200 + i) (i := 0) (by omega_using [hi])
  unfold randomPrepareMem
  rw [(writeW_outside _ B _ (by decide)) _ (by rw [ho]; right; simp only [Random.oMask]; omega_using []),
    (writeW_outside _ B _ (by decide)) _ (by rw [ho]; right; simp only [Random.oWidth]; omega_using []),
    (writeW_outside _ B _ (by decide)) _ (by rw [ho]; right; simp only [Random.oQ]; omega_using [])]
  exact random_clear_byte m B i hi

end VG.Proof.Dsa.AArch64

end

end

/-! Initialize the persistent sampler state from the public q buffer. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_prepare_ready {C : RandomContext} {used draws : Nat} {s : State}
    (hs : Scr s C.B Random.frameBytes) (hsp : s.sp = C.B)
    (hR : word s.mem C.B Random.oRand = C.R)
    (hRL : word s.mem C.B Random.oRandLen = BitVec.ofNat 64 C.rand.length)
    (hU : word s.mem C.B Random.oUsed = BitVec.ofNat 64 used)
    (hD : word s.mem C.B Random.oDraws = BitVec.ofNat 64 draws)
    (hQ : word s.mem C.B Random.oQ = C.Q)
    (hQL : word s.mem C.B Random.oQLen = BitVec.ofNat 64 C.qBytes.length)
    (hRand : Src s C.B Random.frameBytes C.R C.rand)
    (hQS : Src s C.B Random.frameBytes C.Q C.qBytes)
    (hFrame : Frm C.B randomWriteRanges C.initialMem s.mem)
    (hUsed : used ≤ C.rand.length) (hq : 1 < Spec.Dsa.decodeBE C.qBytes) :
    WP isa Random.prepare s fun t => t.gpr .x0 = 1 ∧ RandomReady C used draws t := by
  have hfit := VG.Proof.Dsa.significant_fits C.qBytes
  refine WP.mono (random_prepare_valid hs hsp hQ hQL hQS
    (by have := C.positive; omega_using [hfit, this]) (by have := C.qlen; omega_using [this]))
    fun t ⟨hta, htm, hkt⟩ => ?_
  have hf : Outside C.B 168 64 s.mem t.mem := by
    rw [htm]; exact random_prepare_outside _ _ _ _
  have hfs := InScr.of_outside hf (show 168 + 64 ≤ Random.frameBytes by decide)
  have hw (d : Nat) (hd : d + 8 ≤ 168) : word t.mem C.B d = word s.mem C.B d :=
    hf.word (Or.inl hd) (by omega_using [hd])
  refine ⟨?_, hs.congr hkt.wr, hkt.sp.trans hsp,
    (hw _ (by decide)).trans hR, (hw _ (by decide)).trans hRL,
    (hw _ (by decide)).trans hU, ?_, (hw _ (by decide)).trans hQL, ?_, ?_,
    (hw _ (by decide)).trans hD, hRand.congrK hfs hkt, hQS.congrK hfs hkt, hUsed,
    hFrame.trans (Frm.of_outside (hf.mono (by decide) (by decide))
      (show (160, 72) ∈ randomWriteRanges by decide)), ?_⟩
  · rw [hta, ite_eq_left hq]; rfl
  · rw [htm, random_prepare_width, VG.Proof.Dsa.random_drawBytes_scan]
  · rw [htm, random_prepare_mask]
  · rw [htm, random_prepare_pointer]
  · intro i hi
    rw [htm]
    exact random_prepare_zero _ _ _ _ i (by have := C.qlen; omega_using [hi, this])

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.RandomSignInit`, which only this module used -/

section

/-! Initialize randomized signing from the shared ABI's arguments. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_sign_init {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) :
    WP isa (.seq (.block RandomSign.entry) Random.prepare) (allocated Random.frameBytes s) fun t =>
      ((∃ m draws, t.gpr .x0 = 1 ∧ RandomReady (randomContextOf h m hq) 0 draws t) ∧
      RandomSaved s t.mem ∧ word t.mem (randomBase s) Random.oAttempts = 8 ∧
      Src t (randomBase s) Random.frameBytes (s.gpr .x3) (randomInput s).key ∧
      Src t (randomBase s) Random.frameBytes (s.gpr .x7) (randomInput s).digest ∧
      word t.mem (randomBase s) RandomSign.oLink = s.gpr .x30) ∧
      Keep [.x0, .x1, .x3, .x4, .x8, .x9, .x10, .x12, .x13, .x15] (allocated Random.frameBytes s) t := by
  refine WP.keep [.x0, .x1, .x3, .x4, .x8, .x9, .x10, .x12, .x13, .x15] ?_ rfl rfl rfl
  have hsp : (allocated Random.frameBytes s).sp = randomBase s := by
    rfl
  refine WP.seq (WP.mono (random_entry_ok (random_alloc_scr h) hsp (random_incoming_read h))
    fun u ⟨hum, hku⟩ => ?_)
  have hus := (random_alloc_scr h).congr hku.wr
  have husp := hku.sp.trans hsp
  have hsaved : RandomSaved s u.mem := by rw [hum]; exact random_saved_entry s
  have hframe : InScr (randomBase s) Random.frameBytes (allocated Random.frameBytes s).mem u.mem := by
    rw [hum]
    exact InScr.of_outside (random_entry_outside _ _) (by decide)
  have hqs := (random_initial_q h).congrK hframe hku
  have hrs := (random_initial_rand h).congrK hframe hku
  have hv (p : Nat × BitVec 64) (hp : p ∈ randomEntryValues (allocated Random.frameBytes s) (randomBase s)) :
      word u.mem (randomBase s) p.1 = p.2 := by
    rw [hum]; exact random_entry_values _ _ p hp
  have hqu : word u.mem (randomBase s) Random.oQ = s.gpr .x3 + s.gpr .x5 :=
    hv (168, s.gpr .x3 + s.gpr .x5) (by simp [randomEntryValues, allocated])
  have huu : word u.mem (randomBase s) Random.oUsed = 0 :=
    hv (144, 0) (by simp [randomEntryValues])
  have hau : word u.mem (randomBase s) Random.oAttempts = 8 :=
    hv (152, 8) (by simp [randomEntryValues])
  have hlu : word u.mem (randomBase s) RandomSign.oLink = s.gpr .x30 :=
    hv (232, s.gpr .x30) (by simp [randomEntryValues, allocated])
  let C := randomContextOf h u.mem hq
  have hr : word u.mem C.B Random.oRand = C.R :=
    hsaved (112, stackArg s 1) (by simp [randomSavedValues])
  have hrl : word u.mem C.B Random.oRandLen = BitVec.ofNat 64 C.rand.length := by
    simpa only [Random.oRandLen, C, randomContextOf, randomInput, bytesAt_length, ofNat_toNat64] using
      hsaved (120, stackArg s 2) (by simp [randomSavedValues])
  have hql : word u.mem C.B Random.oQLen = BitVec.ofNat 64 C.qBytes.length := by
    simpa only [Random.oQLen, C, randomContextOf, random_q_length h, ofNat_toNat64] using
      hsaved (88, s.gpr .x6) (by simp [randomSavedValues])
  refine WP.mono (WP.keep [.x0, .x1, .x3, .x4, .x8, .x9, .x10, .x12, .x13, .x15] (random_prepare_ready (C := C) (draws := (word u.mem C.B Random.oDraws).toNat)
    hus husp hr hrl huu (ofNat_toNat64 _).symm hqu hql hrs hqs (Frm.refl _ _ _) (Nat.zero_le _) hq) rfl rfl rfl)
    fun t ⟨⟨hta, htr⟩, hkp⟩ => ?_
  have hw (d : Nat) (hd : d + 8 ≤ 144 ∨ d = 152 ∨ d = 232) : word t.mem (randomBase s) d = word u.mem (randomBase s) d := by
    apply htr.frame.word_eq
    · intro r hr
      simp only [randomWriteRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega_using [hd]
    · omega_using [hd]
  have hpf : InScr (randomBase s) Random.frameBytes u.mem t.mem := InScr.of_frm htr.frame (by
    intro r hr
    simp only [randomWriteRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide)
  exact ⟨⟨u.mem, _, hta, htr⟩, hsaved.congr (fun d _ hd => hw d (Or.inl hd)),
    (hw _ (Or.inr (Or.inl rfl))).trans hau,
    ((random_initial_key h).congrK hframe hku).congrK hpf hkp,
    ((random_initial_digest h).congrK hframe hku).congrK hpf hkp,
    (hw _ (Or.inr (Or.inr rfl))).trans hlu⟩

end VG.Proof.Dsa.AArch64

end

end


/-! The persistent state of the bounded randomized-signing loop. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def randomVolatile : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7,
  .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

theorem random_saved_not_volatile {r : Reg} (h : r ∈ preserved) : r ∉ randomVolatile := by
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

structure RandomSignRunning {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) (used fuel : Nat) (t : State) : Prop where
  ready : ∃ m draws, RandomReady (randomContextOf h m hq) used draws t
  saved : RandomSaved s t.mem
  attempts : word t.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 fuel
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  key : Src t (randomBase s) Random.frameBytes (s.gpr .x3) (randomInput s).key
  digest : Src t (randomBase s) Random.frameBytes (s.gpr .x7) (randomInput s).digest
  callee : ∀ r ∈ preserved, t.gpr r = s.gpr r
  vectors : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  link : word t.mem (randomBase s) RandomSign.oLink = s.gpr .x30

theorem random_sign_init_running {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) :
    WP isa (.seq (.block RandomSign.entry) Random.prepare) (allocated Random.frameBytes s) fun t =>
      t.gpr .x0 = 1 ∧ RandomSignRunning h hq 0 8 t := by
  refine WP.mono (random_sign_init h hq)
    fun t ⟨⟨⟨m, draws, hresult, hr⟩, hs, ha, hkey, hdigest, hlink⟩, hk⟩ => ?_
  have hkv : Keep randomVolatile (allocated Random.frameBytes s) t := hk.mono (by decide)
  refine ⟨hresult, ⟨m, draws, hr⟩, hs, ha, hk.rd, hk.wr, hkey, hdigest, ?_, hk.vcs, hlink⟩
  intro r hr
  exact hkv.gpr r (random_saved_not_volatile hr)

theorem RandomSignRunning.congr {extra : Nat} {s t u : State} {h : RandomSignABI extra s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hr : RandomSignRunning h hq used fuel t) (hm : u.mem = t.mem) (hk : Keep [.x0, .x4] t u) : RandomSignRunning h hq used fuel u := by
  obtain ⟨m, draws, hready⟩ := hr.ready
  have hf : InScr (randomBase s) Random.frameBytes t.mem u.mem := by rw [hm]; exact InScr.refl _ _ _
  refine ⟨⟨m, draws, hready.congr hm hk⟩, by rw [hm]; exact hr.saved,
    by rw [hm]; exact hr.attempts, hk.rd.trans hr.rd, hk.wr.trans hr.wr,
    hr.key.congrK hf hk, hr.digest.congrK hf hk, ?_,
    fun r hc => (hk.vcs r hc).trans (hr.vectors r hc), by rw [hm]; exact hr.link⟩
  intro r hc
  exact ((hk.mono (show ∀ r ∈ [Reg.x0, Reg.x4], r ∈ randomVolatile by decide)).gpr r
    (random_saved_not_volatile hc)).trans (hr.callee r hc)

end VG.Proof.Dsa.AArch64
