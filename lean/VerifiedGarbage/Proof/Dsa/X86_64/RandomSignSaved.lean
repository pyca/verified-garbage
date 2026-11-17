module

public import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
public import VerifiedGarbage.Impl.Dsa.X86_64.Random
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-! ### `Dsa.X86_64.RandomSignEntry`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.RandomSlots`, which this module and modules that import it used -/

section

/-! Exact memory effects of copying stack argument slots. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def randomSlotsMem (B : Addr) (m : Mem) : List (Nat × Nat) → Mem
  | [] => m
  | (src, dst) :: rest => randomSlotsMem B (m.writeW (off B dst) (word m B src)) rest

theorem random_copySlot_ok {s : State} {B : Addr} (src dst : Nat)
    (hsp : s.gpr .rsp = B)
    (hr : InRegions (s.rd ++ s.wr) (off B src) 8) (hw : InRegions s.wr (off B dst) 8) :
    WP isa (.block (Random.copySlot src dst)) s fun t =>
      t.mem = s.mem.writeW (off B dst) (word s.mem B src) ∧ Keep [.rax] s t := by
  refine WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off B dst) (word s.mem B src)) ?_ rfl
  unfold Random.copySlot
  xrun [random_ea_sp, hsp, hr, hw]

theorem random_copySlots_ok {s : State} {B : Addr} (slots : List (Nat × Nat))
    (hsp : s.gpr .rsp = B)
    (hr : ∀ p ∈ slots, InRegions (s.rd ++ s.wr) (off B p.1) 8)
    (hw : ∀ p ∈ slots, InRegions s.wr (off B p.2) 8) :
    WP isa (.block (slots.flatMap (fun p => Random.copySlot p.1 p.2))) s fun t =>
      t.mem = randomSlotsMem B s.mem slots ∧ Keep [.rax] s t := by
  induction slots generalizing s with
  | nil => exact WP.block_nil ⟨rfl, Keep.refl _ _⟩
  | cons p rest ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (random_copySlot_ok p.1 p.2 hsp (hr p (by simp)) (hw p (by simp)))
      fun u ⟨hum, hku⟩ => ?_
    refine WP.mono (ih ((hku.gpr (by decide)).trans hsp)
      (fun q hq => by rw [hku.2.1, hku.2.2]; exact hr q (List.mem_cons_of_mem _ hq))
      (fun q hq => by rw [hku.2.2]; exact hw q (List.mem_cons_of_mem _ hq)))
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


end VG.Proof.Dsa.X86_64

end

end

/-! Save the randomized signer's ABI arguments in its private stack frame. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def randomEntryHeaderMem (s : State) (B : Addr) : Mem :=
  ((((((((s.mem.writeW (off B Random.oOut) (s.gpr .rdi)).writeW
    (off B Random.oOutLen) (s.gpr .rsi)).writeW (off B Random.oUsedPtr) (s.gpr .rdx)).writeW
    (off B Random.oKey) (s.gpr .rcx)).writeW (off B Random.oKeyLen) (s.gpr .r8)).writeW
    (off B Random.oPLen) (s.gpr .r9)).writeW (off B Random.oQ) (s.gpr .rcx + s.gpr .r9)).writeW
    (off B Random.oUsed) (0 : BitVec 64)).writeW (off B Random.oAttempts) (8 : BitVec 64)

theorem random_entryHeader_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B) :
    WP isa (.block RandomSign.entryHeader) s fun t =>
      t.mem = randomEntryHeaderMem s B ∧ Keep [.rax, .rcx] s t := by
  refine WP.keep [.rax, .rcx] (Q := fun t => t.mem = randomEntryHeaderMem s B) ?_ rfl
  unfold RandomSign.entryHeader randomEntryHeaderMem
  xrun [random_ea_sp, hsp, hs.st (d := Random.oOut) (by decide),
    hs.st (d := Random.oOutLen) (by decide), hs.st (d := Random.oUsedPtr) (by decide),
    hs.st (d := Random.oKey) (by decide), hs.st (d := Random.oKeyLen) (by decide),
    hs.st (d := Random.oPLen) (by decide), hs.st (d := Random.oQ) (by decide),
    hs.st (d := Random.oUsed) (by decide), hs.st (d := Random.oAttempts) (by decide)]
  rfl

theorem random_entry_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hr : ∀ p ∈ RandomSign.incomingSlots, InRegions (s.rd ++ s.wr) (off B p.1) 8) :
    WP isa (.block RandomSign.entry) s fun t =>
      t.mem = randomSlotsMem B (randomEntryHeaderMem s B) RandomSign.incomingSlots ∧
      Keep [.rax, .rcx] s t := by
  unfold RandomSign.entry
  rw [WP.block_append_iff]
  refine WP.mono (random_entryHeader_ok hs hsp) fun u ⟨hum, hku⟩ => ?_
  have hus := hs.congr hku.2.2
  refine WP.mono (random_copySlots_ok RandomSign.incomingSlots
    ((hku.gpr (by decide)).trans hsp)
    (fun p hp => by rw [hku.2.1, hku.2.2]; exact hr p hp)
    (fun p hp => hus.st (by
      simp only [RandomSign.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)))
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
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))

end VG.Proof.Dsa.X86_64

end

end

/-! Values of the saved arguments and retry state after wrapper entry. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

def randomEntryValues (s : State) (B : Addr) : List (Nat × BitVec 64) :=
  [(40, s.gpr .rdi), (48, s.gpr .rsi), (56, s.gpr .rdx), (64, s.gpr .rcx),
    (72, s.gpr .r8), (80, s.gpr .r9), (168, s.gpr .rcx + s.gpr .r9), (144, 0), (152, 8),
    (88, word s.mem B 256), (96, word s.mem B 264), (104, word s.mem B 272),
    (112, word s.mem B 280), (120, word s.mem B 288), (128, word s.mem B 296), (136, word s.mem B 304)]

theorem random_entry_values (s : State) (B : Addr) :
    ∀ p ∈ randomEntryValues s B,
      word (randomSlotsMem B (randomEntryHeaderMem s B) RandomSign.incomingSlots) B p.1 = p.2 := by
  simp only [RandomSign.incomingSlots, randomSlotsMem, randomEntryHeaderMem,
      Random.oOut, Random.oOutLen, Random.oUsedPtr, Random.oKey, Random.oKeyLen, Random.oPLen,
      Random.oQ, Random.oUsed, Random.oAttempts, Random.oQLen, Random.oDigest, Random.oDigestLen,
      Random.oRand, Random.oRandLen, Random.oScratch, Random.oScratchLen]
  simp (disch := decide) only [random_word_write_other]
  intro p hp
  simp only [randomEntryValues, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [word_writeW_self, random_word_write_other]

end VG.Proof.Dsa.X86_64
