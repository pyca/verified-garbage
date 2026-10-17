module

public import VerifiedGarbage.Impl.Bignum.Arm.PdFn
public import VerifiedGarbage.Proof.Bignum.Arm.PcEntryMemory
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Save the checked public operation's output and workspace arguments -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_str)

theorem pdEntry_ok (s : State) {base : BitVec 32}
    (fit : s.sp.toNat + 76 ≤ 2 ^ 32)
    (stack : (⟨State.addr s.sp, 56⟩ : Region) ∈ s.wr)
    (argRead : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 72) 4)
    (arg : s.mem.readW (off (State.addr s.sp) 72) 32 = base) :
    WP isa (.block PdFn.entry) s fun t => t.gpr .r0 = base ∧
      t.mem = ((s.mem.writeW (off (State.addr s.sp) 4) (s.gpr .r0)).writeW (State.addr s.sp) base).writeW (off (State.addr s.sp) 12) (s.gpr .r1) ∧
      Rest [.r0, .r12] s t := by
  unfold PdFn.entry PublicFn.entry
  simp only [List.cons_append, List.nil_append]
  refine wp_stackAddr (by decide) fun u h => ?_
  have ptr : u.gpr .r12 = s.sp := by simpa only [BitVec.add_zero] using h.gpr
  refine wp_str (a := off (State.addr s.sp) 4) (by decide)
    (by rw [ptr]; exact addr_add (by omega))
    (by rw [h.wr]; exact ⟨_, stack, Offset.contains_base _ (by decide) (by decide)⟩) fun v j => ?_
  have outside := writeW32_outside s.mem (State.addr s.sp) (d := 4) (s.gpr .r0) (by decide)
  have memV : v.mem = s.mem.writeW (off (State.addr s.sp) 4) (s.gpr .r0) := by
    rw [j.mem, h.mem, h.other .r0 (by decide)]
  have argV : v.mem.readW (off (State.addr s.sp) 72) 32 = base := by
    rw [memV, outside_read32 outside (by decide) (by decide)]; exact arg
  refine wp_loadStack (a := off (State.addr s.sp) 72) (by decide)
    (by rw [j.sp, h.sp]; exact addr_add (by omega))
    (by rw [j.rd, j.wr, h.rd, h.wr]; exact argRead) fun z l => ?_
  have baseZ : z.gpr .r0 = base := l.gpr.trans argV
  refine wp_str (a := State.addr s.sp) (by decide)
    (by rw [l.other .r12 (by decide), j.gpr, ptr]; simp)
    (by rw [l.wr, j.wr, h.wr]; exact ⟨_, stack, by simp [Region.Contains]⟩) fun t q => ?_
  have ptrT : t.gpr .r12 = s.sp := by rw [q.gpr, l.other .r12 (by decide), j.gpr, ptr]
  refine wp_str (a := off (State.addr s.sp) 12) (by decide)
    (by rw [ptrT]; exact addr_add (by omega))
    (by rw [q.wr, l.wr, j.wr, h.wr]; exact ⟨_, stack, Offset.contains_base _ (by decide) (by decide)⟩)
    fun z last => WP.block_nil ?_
  exact ⟨by rw [last.gpr, q.gpr]; exact baseZ,
    by rw [last.mem, q.mem, baseZ, l.mem, memV, q.gpr, l.other .r1 (by decide), j.gpr, h.other .r1 (by decide)],
    (h.rest (by simp)).trans ((j.rest _).trans ((l.rest (by simp)).trans ((q.rest _).trans (last.rest _))))⟩

end VG.Proof.Bignum.Arm
