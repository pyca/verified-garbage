module
public import VerifiedGarbage.Impl.Dsa.X86_64.GenerateKey
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSlots

import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignEnv
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel

/-! # Key generation's entry: the arguments saved in its frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def keygenEntryHeaderMem (s : State) (B : Addr) : Mem :=
  (((((((((s.mem.writeW (off B Random.oOut) (s.gpr .rdi)).writeW
    (off B Random.oOutLen) (s.gpr .rsi)).writeW (off B Random.oUsedPtr) (s.gpr .rdx)).writeW
    (off B Random.oKey) (s.gpr .rcx)).writeW (off B Random.oKeyLen) (s.gpr .r8)).writeW
    (off B Random.oPLen) (s.gpr .r9)).writeW (off B Random.oQ) (s.gpr .rcx + s.gpr .r9)).writeW
    (off B Random.oUsed) (0 : BitVec 64)).writeW (off B Random.oStatus) (0 : BitVec 64))

theorem keygen_entryHeader_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B) :
    WP isa (.block GenerateKey.entryHeader) s fun t =>
      t.mem = keygenEntryHeaderMem s B ∧ Keep [.rax, .rcx] s t := by
  refine WP.keep [.rax, .rcx] (Q := fun t => t.mem = keygenEntryHeaderMem s B) ?_ rfl
  unfold GenerateKey.entryHeader keygenEntryHeaderMem
  xrun [random_ea_sp, hsp, hs.st (d := Random.oOut) (by decide),
    hs.st (d := Random.oOutLen) (by decide), hs.st (d := Random.oUsedPtr) (by decide),
    hs.st (d := Random.oKey) (by decide), hs.st (d := Random.oKeyLen) (by decide),
    hs.st (d := Random.oPLen) (by decide), hs.st (d := Random.oQ) (by decide),
    hs.st (d := Random.oUsed) (by decide), hs.st (d := Random.oStatus) (by decide)]
  rfl

def keygenEntryMem (s : State) (B : Addr) : Mem :=
  randomSlotsMem B (keygenEntryHeaderMem s B) GenerateKey.incomingSlots

theorem keygen_entry_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hr : ∀ p ∈ GenerateKey.incomingSlots, InRegions (s.rd ++ s.wr) (off B p.1) 8) :
    WP isa (.block GenerateKey.entry) s fun t =>
      t.mem = keygenEntryMem s B ∧ Keep [.rax, .rcx] s t := by
  unfold GenerateKey.entry
  rw [WP.block_append_iff]
  refine WP.mono (keygen_entryHeader_ok hs hsp) fun u ⟨hum, hku⟩ => ?_
  have hus := hs.congr hku.2.2
  refine WP.mono (random_copySlots_ok GenerateKey.incomingSlots
    ((hku.gpr (by decide)).trans hsp)
    (fun p hp => by rw [hku.2.1, hku.2.2]; exact hr p hp)
    (fun p hp => hus.st (by
      simp only [GenerateKey.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide)))
    fun t ⟨htm, hkt⟩ => ⟨by rw [htm, hum]; rfl, (hku.trans hkt).mono (by decide)⟩

private theorem extend_entry_frame {B : Addr} {m m' : Mem} {d : Nat} (v : BitVec 64)
    (h : Outside B 0 Random.frameBytes m m') (hd : d + 8 ≤ Random.frameBytes) :
    Outside B 0 Random.frameBytes m (m'.writeW (off B d) v) :=
  h.trans ((writeW_outside _ B _ (by unfold Random.frameBytes at hd; omega)).mono (Nat.zero_le _) hd)

theorem keygen_entry_outside (s : State) (B : Addr) :
    Outside B 0 Random.frameBytes s.mem (keygenEntryMem s B) := by
  have hh : Outside B 0 Random.frameBytes s.mem (keygenEntryHeaderMem s B) := by
    unfold keygenEntryHeaderMem
    repeat' apply extend_entry_frame _ _ (by decide)
    exact Outside.refl _ _ _ _
  exact hh.trans (random_slots_outside _ _ _ _ _ (by
    intro p hp
    simp only [GenerateKey.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide))

/-- The saved arguments: the frame's words the calls and the finish read. -/
def keygenSavedValues (s : State) : List (Nat × BitVec 64) :=
  [(40, s.gpr .rdi), (48, s.gpr .rsi), (56, s.gpr .rdx), (64, s.gpr .rcx),
    (72, s.gpr .r8), (80, s.gpr .r9), (88, stackArg s 0), (112, stackArg s 1),
    (120, stackArg s 2), (128, stackArg s 3), (136, stackArg s 4)]

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
  [(40, s.gpr .rdi), (48, s.gpr .rsi), (56, s.gpr .rdx), (64, s.gpr .rcx),
    (72, s.gpr .r8), (80, s.gpr .r9), (168, s.gpr .rcx + s.gpr .r9), (144, 0), (192, 0),
    (88, word s.mem B 256), (112, word s.mem B 264), (120, word s.mem B 272),
    (128, word s.mem B 280), (136, word s.mem B 288)]

theorem keygen_entry_values (s : State) (B : Addr) :
    ∀ p ∈ keygenEntryValues s B, word (keygenEntryMem s B) B p.1 = p.2 := by
  simp only [keygenEntryMem, GenerateKey.incomingSlots, randomSlotsMem, keygenEntryHeaderMem,
      Random.oOut, Random.oOutLen, Random.oUsedPtr, Random.oKey, Random.oKeyLen, Random.oPLen,
      Random.oQ, Random.oUsed, Random.oStatus, Random.oQLen,
      Random.oRand, Random.oRandLen, Random.oScratch, Random.oScratchLen]
  simp (disch := decide) only [random_word_write_other]
  intro p hp
  simp only [keygenEntryValues, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [word_writeW_self, random_word_write_other]

theorem keygen_saved_entry (s : State) :
    KeygenSaved s (keygenEntryMem (allocState Random.frameBytes s) (randomBase s)) := by
  have hv := keygen_entry_values (allocState Random.frameBytes s) (randomBase s)
  have hs : ∀ p ∈ keygenSavedValues s, p ∈ keygenEntryValues (allocState Random.frameBytes s) (randomBase s) := by
    intro p hp
    simp only [keygenSavedValues, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [keygenEntryValues, allocState, State.setReg, random_entry_stackWord s 0,
        random_entry_stackWord s 1, random_entry_stackWord s 2, random_entry_stackWord s 3,
        random_entry_stackWord s 4]
  exact fun p hp => hv p (hs p hp)

end VG.Proof.Dsa.X86_64
