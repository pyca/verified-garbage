module

public import VerifiedGarbage.Proof.Framework.X86_64.Interleave
public import VerifiedGarbage.Impl.Sha512.X86_64.Avx2Rolled
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# SHA-512 with AVX2 on x86-64, rolled: the schedule woven into the rounds

Each schedule step writes only vector registers and its own slot of the
scratch space, which the two rounds it is woven into (`groupR`) neither read
nor write; the rounds write only general-purpose registers and the flags,
which the schedule step does not read. So the woven group runs as the
schedule step and then the rounds (`Interleave.WP.weave`), checked once on
the steps' footprints, memory at `[rcx + rdx * 2 + disp]`.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Avx2.Rolled

open VG VG.X86_64 VG.Impl.Sha512.X86_64.Avx2Rolled

/-- The footprints of the iterations' code, memory at `[rcx + rdx * 2 + disp]`. -/
abbrev fps : VG.Interleave.Footprints isa := VG.X86_64.Interleave.footprints .rcx (some .rdx) 2

theorem group_check : ∀ n < 8,
    ((fps.blockFp (scheduleR (n + 8))).bind fun A =>
      (fps.blockFp (roundR 0 (2 * n) ++ roundR 0 (2 * n + 1))).map fun B => fps.indep A B) = some true := by
  decide +kernel

theorem group_indeps {n : Nat} (hn : n < 8) :
    VG.Interleave.Indeps isa fps.Inv (scheduleR (n + 8)) (roundR 0 (2 * n) ++ roundR 0 (2 * n + 1)) :=
  fps.indeps_of_check (group_check n hn)

end VG.Proof.Sha512.X86_64.Avx2.Rolled
