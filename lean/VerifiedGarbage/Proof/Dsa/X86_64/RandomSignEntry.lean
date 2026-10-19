module

public import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSlots
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame

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
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))

end VG.Proof.Dsa.X86_64
