module
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.X25519.Arm.Instr

import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Restore any list of distinct registers from readable stack slots -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem restoreSlots_ok (slots : List (Reg × Nat)) (s : State) (g : Reg → BitVec 32) {size : Nat}
    (distinct : (slots.map Prod.fst).Nodup)
    (nowrap : s.sp.toNat + size ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr s.sp) size)
    (fits : ∀ p ∈ slots, p.2 + 4 ≤ size ∧ p.2 < 4096)
    (saved : ∀ p ∈ slots, s.mem.readW (off (State.addr s.sp) p.2) 32 = g p.1) :
    WP isa (.block (slots.map fun p => Instr.ldrSp p.1 p.2)) s fun t =>
      (∀ p ∈ slots, t.gpr p.1 = g p.1) ∧ t.mem = s.mem ∧ Rest (slots.map Prod.fst) s t := by
  induction slots generalizing s with
  | nil => exact WP.block_nil ⟨by simp, rfl, Rest.refl _ _⟩
  | cons p slots ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp distinct
    have bound := fits p (by simp)
    simp only [List.map_cons]
    refine wp_loadStack (a := off (State.addr s.sp) p.2) bound.2 (addr_add (by omega))
      (CallLay.inRegions_sub read bound.1 (by omega)) fun u loaded => ?_
    refine WP.mono (ih u tail (by rw [loaded.sp]; exact nowrap)
      (by rw [loaded.rd, loaded.wr, loaded.sp]; exact read)
      (fun q hq => fits q (by simp [hq]))
      (fun q hq => by rw [loaded.mem, loaded.sp]; exact saved q (by simp [hq]))) ?_
    rintro t ⟨values, mem, rest⟩
    refine ⟨?_, mem.trans loaded.mem, ?_⟩
    · intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact (rest.gpr q.1 fresh).trans (loaded.gpr.trans (saved q (by simp)))
      · exact values q hq
    · exact (loaded.rest (by simp)).trans (rest.mono (fun r hr => List.mem_cons_of_mem _ hr))

end VG.Proof.Bignum.Arm
