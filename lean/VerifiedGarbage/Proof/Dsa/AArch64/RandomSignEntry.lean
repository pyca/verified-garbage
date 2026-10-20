module

public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSlots
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

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
  h.trans ((writeW_outside _ B _ (by unfold Random.frameBytes at hd; omega)).mono (Nat.zero_le _) hd)

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
