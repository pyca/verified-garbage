module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSlots
public import VerifiedGarbage.Impl.Dsa.AArch64.GenerateKey
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFrame
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignEnv
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Save the key-generation ABI arguments in the private stack frame. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def keygenEntryHeaderMem (s : State) (B : Addr) : Mem :=
  ((((((((((((s.mem.writeW (off B Random.oOut) (s.gpr .x0)).writeW (off B Random.oOutLen) (s.gpr .x1)).writeW (off B Random.oUsedPtr) (s.gpr .x2)).writeW (off B Random.oKey) (s.gpr .x3)).writeW (off B Random.oKeyLen) (s.gpr .x4)).writeW (off B Random.oPLen) (s.gpr .x5)).writeW (off B Random.oQLen) (s.gpr .x6)).writeW (off B Random.oRand) (s.gpr .x7)).writeW (off B RandomSign.oLink) (s.gpr .x30)).writeW (off B Random.oQ) (s.gpr .x3 + s.gpr .x5)).writeW (off B Random.oUsed) (0 : BitVec 64)).writeW (off B Random.oStatus) (0 : BitVec 64))

theorem keygen_entryHeader_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B) :
    WP isa (.block GenerateKey.entryHeader) s fun t =>
      t.mem = keygenEntryHeaderMem s B ∧ Keep [.x0, .x4, .x15] s t := by
  refine WP.keep [.x0, .x4, .x15] (Q := fun t => t.mem = keygenEntryHeaderMem s B) ?_ rfl rfl rfl
  unfold GenerateKey.entryHeader Random.store keygenEntryHeaderMem
  brun [hsp,
    exec_addSp (show Random.oOut < 4096 by decide), hs.st (d := Random.oOut) (by decide),
    exec_addSp (show Random.oOutLen < 4096 by decide), hs.st (d := Random.oOutLen) (by decide),
    exec_addSp (show Random.oUsedPtr < 4096 by decide), hs.st (d := Random.oUsedPtr) (by decide),
    exec_addSp (show Random.oKey < 4096 by decide), hs.st (d := Random.oKey) (by decide),
    exec_addSp (show Random.oKeyLen < 4096 by decide), hs.st (d := Random.oKeyLen) (by decide),
    exec_addSp (show Random.oPLen < 4096 by decide), hs.st (d := Random.oPLen) (by decide),
    exec_addSp (show Random.oQLen < 4096 by decide), hs.st (d := Random.oQLen) (by decide),
    exec_addSp (show Random.oRand < 4096 by decide), hs.st (d := Random.oRand) (by decide),
    exec_addSp (show RandomSign.oLink < 4096 by decide), hs.st (d := RandomSign.oLink) (by decide),
    exec_addSp (show Random.oQ < 4096 by decide), hs.st (d := Random.oQ) (by decide),
    exec_addSp (show Random.oUsed < 4096 by decide), hs.st (d := Random.oUsed) (by decide),
    exec_addSp (show Random.oStatus < 4096 by decide), hs.st (d := Random.oStatus) (by decide)]
  rfl

theorem keygen_entry_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hr : ∀ p ∈ GenerateKey.incomingSlots, InRegions (s.rd ++ s.wr) (off B p.1) 8) :
    WP isa (.block GenerateKey.entry) s fun t =>
      t.mem = randomSlotsMem B (keygenEntryHeaderMem s B) GenerateKey.incomingSlots ∧
      Keep [.x0, .x4, .x15] s t := by
  unfold GenerateKey.entry
  rw [WP.block_append_iff]
  refine WP.mono (keygen_entryHeader_ok hs hsp) fun u ⟨hum, hku⟩ => ?_
  have hus := hs.congr hku.wr
  refine WP.mono (random_copySlots_ok GenerateKey.incomingSlots
    (hku.sp.trans hsp)
    (by intro p hp; simp only [GenerateKey.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp;
        rcases hp with rfl | rfl | rfl <;> decide)
    (fun p hp => by rw [hku.rd, hku.wr]; exact hr p hp)
    (fun p hp => hus.st (by
      simp only [GenerateKey.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> decide)))
    fun t ⟨htm, hkt⟩ => ⟨by rw [htm, hum], (hku.trans hkt).mono (by decide)⟩

private theorem extend_entry_frame {B : Addr} {m m' : Mem} {d : Nat} (v : BitVec 64)
    (h : Outside B 0 Random.frameBytes m m') (hd : d + 8 ≤ Random.frameBytes) :
    Outside B 0 Random.frameBytes m (m'.writeW (off B d) v) :=
  h.trans ((writeW_outside _ B _ (by unfold Random.frameBytes at hd; omega)).mono (Nat.zero_le _) hd)

theorem keygen_entryHeader_outside (s : State) (B : Addr) :
    Outside B 0 Random.frameBytes s.mem (keygenEntryHeaderMem s B) := by
  unfold keygenEntryHeaderMem
  repeat' apply extend_entry_frame _ _ (by decide)
  exact Outside.refl _ _ _ _

theorem keygen_entry_outside (s : State) (B : Addr) :
    Outside B 0 Random.frameBytes s.mem
      (randomSlotsMem B (keygenEntryHeaderMem s B) GenerateKey.incomingSlots) :=
  (keygen_entryHeader_outside s B).trans (random_slots_outside _ _ _ _ _ (by
    intro p hp
    simp only [GenerateKey.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> decide))

def keygenEntryMem (s : State) (B : Addr) : Mem :=
  randomSlotsMem B (keygenEntryHeaderMem s B) GenerateKey.incomingSlots

/-- The saved arguments: the frame's words the calls and the finish read. -/
def keygenSavedValues (s : State) : List (Nat × BitVec 64) :=
  [(40, s.gpr .x0), (48, s.gpr .x1), (56, s.gpr .x2), (64, s.gpr .x3),
    (72, s.gpr .x4), (80, s.gpr .x5), (88, s.gpr .x6), (112, s.gpr .x7),
    (120, stackArg s 0), (128, stackArg s 1), (136, stackArg s 2)]

def KeygenSaved (s : State) (m : Mem) : Prop :=
  ∀ p ∈ keygenSavedValues s, word m (randomBase s) p.1 = p.2

theorem keygen_saved_bound {s : State} {p : Nat × BitVec 64} (hp : p ∈ keygenSavedValues s) :
    40 ≤ p.1 ∧ p.1 + 8 ≤ 144 := by
  simp only [keygenSavedValues, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)

theorem KeygenSaved.congr {s : State} {m m' : Mem} (h : KeygenSaved s m)
    (hw : ∀ d, 40 ≤ d → d + 8 ≤ 144 → word m' (randomBase s) d = word m (randomBase s) d) : KeygenSaved s m' :=
  fun p hp => (hw _ (keygen_saved_bound hp).1 (keygen_saved_bound hp).2).trans (h p hp)

def keygenEntryValues (s : State) (B : Addr) : List (Nat × BitVec 64) :=
  [(40, s.gpr .x0), (48, s.gpr .x1), (56, s.gpr .x2), (64, s.gpr .x3),
    (72, s.gpr .x4), (80, s.gpr .x5), (88, s.gpr .x6), (112, s.gpr .x7),
    (232, s.gpr .x30), (168, s.gpr .x3 + s.gpr .x5), (144, 0), (192, 0),
    (120, word s.mem B 256), (128, word s.mem B 264), (136, word s.mem B 272)]

theorem keygen_entry_values (s : State) (B : Addr) :
    ∀ p ∈ keygenEntryValues s B, word (keygenEntryMem s B) B p.1 = p.2 := by
  simp only [keygenEntryMem, GenerateKey.incomingSlots, randomSlotsMem, keygenEntryHeaderMem,
      RandomSign.oLink, Random.oOut, Random.oOutLen, Random.oUsedPtr, Random.oKey, Random.oKeyLen, Random.oPLen,
      Random.oQ, Random.oUsed, Random.oStatus, Random.oQLen,
      Random.oRand, Random.oRandLen, Random.oScratch, Random.oScratchLen]
  simp (disch := decide) only [random_word_write_other]
  intro p hp
  simp only [keygenEntryValues, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [word_writeW_self, random_word_write_other]

theorem keygen_saved_entry (s : State) :
    KeygenSaved s (keygenEntryMem (allocated Random.frameBytes s) (randomBase s)) := by
  have hv := keygen_entry_values (allocated Random.frameBytes s) (randomBase s)
  have hs : ∀ p ∈ keygenSavedValues s, p ∈ keygenEntryValues (allocated Random.frameBytes s) (randomBase s) := by
    intro p hp
    simp only [keygenSavedValues, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [keygenEntryValues, allocated, random_entry_stackWord s 0,
        random_entry_stackWord s 1, random_entry_stackWord s 2]
  exact fun p hp => hv p (hs p hp)

end VG.Proof.Dsa.AArch64
