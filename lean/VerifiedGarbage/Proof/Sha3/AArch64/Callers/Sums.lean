import VerifiedGarbage.Proof.Sha3.AArch64.Sums
import VerifiedGarbage.Proof.Framework.TaintSumGeneric
import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint

/-!
# The summaries of the sponge's callers, for any Keccak backend

The constant-time checks of the sponge's callers (ML-KEM, ML-DSA) use the
summaries of the sponge's functions over a backend's permutation
(`sponge_taint_summaries`) and of ML-KEM's functions. `checkSum` looks
neither at the code of a summarized call nor at the names of calls, so each
caller is checked once for any backend `c` (`taint_decide_generic`,
`Callers/MlKem.lean`, `Callers/MlDsa.lean`) from the summaries `sums c`, whose
`pre`, `post` and frame are the same for every backend: each function of the
sponge from each set of callee-saved registers public at some call, as
`sponge_taint_summaries ns c saving` states them, ending with the registers
the callers need public. Each backend gives them from its own summaries: those
of a permutation that saves and restores the callee-saved registers with less
public at the end (`Taint.SumOk.weaken`), those of one that keeps them from
their frames (`Taint.SumOk.restrict`).
-/

namespace VG.Proof.Sha3.AArch64.Callers

open VG VG.AArch64

/-- The calls of the sponge's functions of the backend `c`, as its summaries
state them (`sponge_taint_summaries`). -/
abbrev absorbCall (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .call ("vg_keccak_absorb_scratch" ++ c.suffix) (Impl.Sha3.AArch64.Stream.absorbWith c)
abbrev padCall (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .call ("vg_keccak_pad_scratch" ++ c.suffix) (Impl.Sha3.AArch64.Stream.padWith c)
abbrev squeezeCall (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .call ("vg_keccak_squeeze_scratch" ++ c.suffix) (Impl.Sha3.AArch64.Stream.squeezeWith c)

/-- ML-KEM's functions' summaries (`MlKemSums`), the same for every backend. -/
abbrev mlkem : List (Taint.Summary isa VectorTaint.taint.T) :=
  [Taint.sumOf MlKemSums.ntt, Taint.sumOf MlKemSums.nttInv, Taint.sumOf MlKemSums.mul,
    Taint.sumOf MlKemSums.add, Taint.sumOf MlKemSums.sub, Taint.sumOf MlKemSums.cbd2,
    Taint.sumOf MlKemSums.encode12, Taint.sumOf MlKemSums.decode12, Taint.sumOf MlKemSums.ce,
    Taint.sumOf MlKemSums.dd, Taint.sumOf MlKemSums.ce1024, Taint.sumOf MlKemSums.dd1024]

theorem mlkem_ok : Taint.AllOk VectorTaint.taint mlkem :=
  ⟨MlKemSums.ntt, MlKemSums.nttInv, MlKemSums.mul, MlKemSums.add, MlKemSums.sub, MlKemSums.cbd2,
    MlKemSums.encode12, MlKemSums.decode12, MlKemSums.ce, MlKemSums.dd, MlKemSums.ce1024,
    MlKemSums.dd1024, trivial⟩

/-- The summaries of the sponge's callers' checks, for the backend `c`, in
`sponge_taint_decide`'s order: each function of the sponge from each set of
callee-saved registers public at some call, with the registers public at its
end, then ML-KEM's functions'. -/
def sums (c : Impl.Sha3.AArch64.Callee) : List (Taint.Summary isa VectorTaint.taint.T) :=
  let sum (f : Prog isa) (pre post : List Reg) : Taint.Summary isa VectorTaint.taint.T :=
    (f, VectorTaint.ofRegs pre, VectorTaint.ofRegs post, Taint.Frame.bot (A := VectorTaint.taint))
  let perm : Prog isa := .call c.name c.code
  [sum (absorbCall c) [.x0, .x1, .x2, .x3, .x4, .x5, .x23, .x25, .x26, .x27, .x28]
      [.x0, .x25, .x26, .x27, .x28],
    sum (absorbCall c) [.x0, .x1, .x2, .x3, .x4, .x5, .x24, .x25, .x26, .x27, .x28]
      [.x0, .x25, .x26, .x27, .x28],
    sum (absorbCall c) [.x0, .x1, .x2, .x3, .x4, .x5, .x25, .x26, .x27, .x28]
      [.x0, .x25, .x26, .x27, .x28],
    sum (absorbCall c) [.x0, .x1, .x2, .x3, .x4, .x5, .x25, .x26, .x27]
      [.x0, .x25, .x26, .x27],
    sum (absorbCall c) [.x0, .x1, .x2, .x3, .x4, .x5, .x24, .x25, .x26]
      [.x0, .x25, .x26],
    sum (padCall c) [.x0, .x1, .x2, .x4, .x25, .x26, .x27, .x28]
      [.x25, .x26, .x27, .x28],
    sum (padCall c) [.x0, .x1, .x2, .x4, .x25, .x26, .x27]
      [.x25, .x26, .x27],
    sum (padCall c) [.x0, .x1, .x2, .x4, .x25, .x26]
      [.x25, .x26],
    sum (squeezeCall c) [.x0, .x1, .x2, .x3, .x4, .x5, .x25, .x26, .x27, .x28]
      [.x0, .x25, .x26, .x27, .x28],
    sum (squeezeCall c) [.x0, .x1, .x2, .x3, .x4, .x5, .x25, .x26, .x27]
      [.x0, .x25, .x26, .x27],
    sum (squeezeCall c) [.x0, .x1, .x2, .x3, .x4, .x5, .x25, .x26]
      [.x0, .x25, .x26],
    sum perm [.x0, .x1, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]
      [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28],
    sum perm [.x0, .x1, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]
      [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27],
    sum perm [.x0, .x1, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26]
      [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26],
    sum perm [.x0, .x1, .x19, .x20, .x21, .x22, .x23, .x24]
      [.x19, .x20, .x21, .x22, .x23, .x24],
    sum perm [.x0, .x1, .x25, .x26, .x27, .x28]
      [.x25, .x26, .x27, .x28],
    sum perm [.x0, .x1, .x25, .x26, .x27]
      [.x25, .x26, .x27],
    sum perm [.x0, .x1, .x25, .x26]
      [.x25, .x26],
    sum perm [.x0, .x1]
      []] ++ mlkem

/-- `sums c` holds, from the backend's summaries, in `sums`'s order. -/
theorem sums_ok {c : Impl.Sha3.AArch64.Callee}
    (h : Taint.AllOk VectorTaint.taint (sums c |>.take 19)) : Taint.AllOk VectorTaint.taint (sums c) := by
  have e : sums c = (sums c).take 19 ++ mlkem := rfl
  rw [e]
  exact .append h mlkem_ok

end VG.Proof.Sha3.AArch64.Callers
