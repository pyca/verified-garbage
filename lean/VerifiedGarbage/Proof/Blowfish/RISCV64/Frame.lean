module

public import VerifiedGarbage.Impl.Blowfish.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Blowfish on RISC-V: the frame holding the schedule

`inFrame` allocates 4176 bytes below the stack pointer in three frames
(2032, 2032 and 112 bytes); its body runs from `inner s`, with the stack
pointer at their base, `frameBase s` (`inFrame_wp`), and an access of `n`
bytes at an offset `o` of the base that does not cross a 16-byte boundary
lies in one of them (`frame_in`). `Zeroed`: the frame zeroed, as the code
leaves it before freeing it.
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64

open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64

/-- The state `inFrame`'s body starts in. -/
def inner (s : State) : State := allocd 112 (allocd 2032 (allocd 2032 s))

/-- The base of the frame. -/
def frameBase (s : State) : Addr := s.sp - BitVec.ofNat 64 2032 - BitVec.ofNat 64 2032 - BitVec.ofNat 64 112

theorem inner_sp (s : State) : (inner s).sp = frameBase s := rfl
theorem inner_gpr (s : State) : (inner s).gpr = s.gpr := rfl
theorem inner_mem (s : State) : (inner s).mem = s.mem := rfl
theorem inner_rd (s : State) : (inner s).rd = s.rd := rfl

theorem inner_wr (s : State) : (inner s).wr =
    ⟨frameBase s, 112⟩ :: ⟨s.sp - BitVec.ofNat 64 2032 - BitVec.ofNat 64 2032, 2032⟩ ::
      ⟨s.sp - BitVec.ofNat 64 2032, 2032⟩ :: s.wr := rfl

theorem frameBase_eq (s : State) : frameBase s = s.sp - BitVec.ofNat 64 4176 := by
  apply BitVec.eq_of_toNat_eq
  simp only [frameBase, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem frameBase_al (s : State) (hal : s.sp.toNat % 16 = 0) (h : 4176 ≤ s.sp.toNat) :
    (frameBase s).toNat % 16 = 0 := by
  rw [frameBase_eq s, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega),
    BitVec.toNat_ofNat]
  omega

/-- The body of `inFrame` runs from `inner s`; if it keeps the permissions
and the stack pointer, the frame ends with those of `s`. -/
theorem inFrame_wp {body : Prog isa} {s : State} {Q : State → Prop} (hsp : 4176 ≤ s.sp.toNat)
    (hb : WP isa body (inner s) fun s₂ => Q { s₂ with sp := s.sp, wr := s.wr }) :
    WP isa (inFrame body) s Q := by
  unfold inFrame
  refine WP.alloc (by decide) (by omega) ?_
  refine WP.alloc (by decide) (by
    show 2032 ≤ (s.sp - BitVec.ofNat 64 2032).toNat
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
    omega) ?_
  refine WP.alloc (by decide) (by
    show 112 ≤ (s.sp - BitVec.ofNat 64 2032 - BitVec.ofNat 64 2032).toNat
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega) ?_
  refine WP.mono (WP.rdwr hb) fun s₂ ⟨h, _, hwr, hsp₂⟩ => ?_
  have e : freed 2032 (freed 2032 (freed 112 s₂)) = { s₂ with sp := s.sp, wr := s.wr } := by
    simp only [freed, hwr, hsp₂, allocd, List.tail_cons, BitVec.sub_add_cancel]
  rw [e]
  exact h

/-- The accesses that the frame at `S` allows: `n` bytes at offset `o`,
within the schedule and a 16-byte aligned chunk. -/
def Writable (wr : List Region) (S : Addr) : Prop :=
  ∀ o n, o + n ≤ 4168 → o % 16 + n ≤ 16 → InRegions wr (S + BitVec.ofNat 64 o) n

/-- The frame at `F` zeroed: its 522 doublewords. -/
def Zeroed (F : Addr) (m : Mem) : Prop :=
  ∀ j < 522, m.readW (F + BitVec.ofNat 64 (8 * j)) 64 = 0#64

/-- An access of `n` bytes at offset `o` of the frame, within a 16-byte
aligned chunk of it. -/
theorem frame_in (s : State) {o n : Nat} (ho : o + n ≤ 4176)
    (hc : o % 16 + n ≤ 16) :
    InRegions (inner s).wr (frameBase s + BitVec.ofNat 64 o) n := by
  have e2 : s.sp - BitVec.ofNat 64 2032 - BitVec.ofNat 64 2032 = frameBase s + BitVec.ofNat 64 112 := by
    simp only [frameBase, BitVec.sub_add_cancel]
  have e3 : s.sp - BitVec.ofNat 64 2032 = frameBase s + BitVec.ofNat 64 2144 := by
    apply BitVec.eq_of_toNat_eq
    simp only [frameBase, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [inner_wr]
  by_cases h1 : o + n ≤ 112
  · exact ⟨_, List.mem_cons_self, Offset.contains_base _ h1 (by omega)⟩
  · by_cases h2 : o + n ≤ 2144
    · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      rw [e2]
      exact Offset.contains _ (by omega) (by omega) (by omega)
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩
      rw [e3]
      exact Offset.contains _ (by omega) (by omega) (by omega)

theorem frame_writable (s : State) : Writable (inner s).wr (frameBase s) :=
  fun _ _ ho hc => frame_in s (by omega) hc

end VG.Proof.Blowfish.RISCV64
