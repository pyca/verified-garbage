module

public import VerifiedGarbage.Proof.Framework.AArch64.InterleaveFootprints
public import VerifiedGarbage.Impl.Gcm.AArch64.Stitch
import all Init.Data.Nat.Bitwise.Basic

/-!
# Interleaved counter mode and GHASH on AArch64: the two parts are independent

`aesPart` writes `v0`–`v7`, `v30`, `v31`, `x10` and `x12`, which `ghPart`
neither reads nor writes, and reads `x9`, `x20`, `x21` and memory, which it
does not write; `ghPart` writes `v16` and `v18`–`v29`, which `aesPart`
neither reads nor writes. Neither stores. So woven they run as `aesPart` and
then `ghPart` (`Interleave.WP.weaveG`, `parts_ok`; the weave keeps each `aese`
next to its `aesmc`, `fuse`), checked once on the parts' footprints
(memory read at any base: `Proof/Framework/AArch64/Interleave.lean`).
-/

@[expose] public section

namespace VG.Proof.Gcm.AArch64.Stitch

open VG VG.AArch64 VG.Impl.Gcm.AArch64.Stitch

/-- The footprints of the parts' code; neither stores, so the base register
does not matter. -/
abbrev fps : VG.Interleave.Footprints isa := VG.AArch64.Interleave.footprints .x0

theorem parts_check : ∀ nr ∈ [10, 12, 14], ∀ o ∈ [0, 128],
    ((fps.blockFp (aesPart nr o)).bind fun A => (fps.blockFp ghPart).map fun B => fps.indep A B) = some true := by
  decide +kernel

theorem parts_indeps {nr o : Nat} (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) (ho : o = 0 ∨ o = 128) :
    VG.Interleave.Indeps isa fps.Inv (aesPart nr o) ghPart :=
  fps.indeps_of_check (parts_check nr (by rcases hnr with rfl | rfl | rfl <;> decide) o
    (by rcases ho with rfl | rfl <;> decide))

theorem fuse_flatten (l : List Instr) : (fuse l).flatten = l := by
  induction l using fuse.induct <;> simp_all [fuse]

theorem flatten_singles {α : Type} : ∀ l : List α, (l.map fun x => [x]).flatten = l
  | [] => rfl
  | x :: l => by rw [List.map_cons, List.flatten_cons, flatten_singles l]; rfl

/-- The parts, woven, run as `aesPart` and then `ghPart`. -/
theorem parts_ok {nr o : Nat} (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) (ho : o = 0 ∨ o = 128) {s : State}
    {Q : State → Prop} (h : WP isa (.block (aesPart nr o)) s fun t => WP isa (.block ghPart) t Q) :
    WP isa (.block (parts nr o)) s Q := by
  unfold parts
  refine VG.Interleave.WP.weaveG (P := fps.Inv) ?_ trivial ?_
  · rw [fuse_flatten, flatten_singles]; exact parts_indeps hnr ho
  · rw [fuse_flatten, flatten_singles]; exact h

end VG.Proof.Gcm.AArch64.Stitch
