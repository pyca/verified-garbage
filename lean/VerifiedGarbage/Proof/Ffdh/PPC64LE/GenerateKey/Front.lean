module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicCT
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainFn
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_generate_key` on PPC64LE: the front

The front stores x, `x_len`, `y` and `rand` in the working space's header
words 8–11 (`gkHdr_ok`); the domain's data `gcOf` has g as the `Y` of
`Base`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.GenerateKey

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Proof.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot)

/-- The public data of a run, as `Base`'s: the domain, g and the working space. -/
def gcOf (s : State) : CD :=
  ⟨s.gpr .r7, off (s.gpr .r7) (s.gpr .r9).toNat, stackArg s 1, (s.gpr .r9).toNat, (s.gpr .r8).toNat,
    (stackArg s 2).toNat * 8, Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat,
    Spec.Rsa.bytesAt s.mem (off (s.gpr .r7) (s.gpr .r9).toNat) (s.gpr .r9).toNat⟩

/-- x, `x_len`, `y` and `rand` into the header's words 8–11 at `S`, and the
domain's arguments into `r3`–`r5`. -/
theorem gkHdr_ok {s : State} {S : Addr} (h23 : s.gpr .r23 = S)
    (hin : ∀ i < 4, InRegions s.wr (off S (64 + 8 * i)) 8) :
    WP isa (.block ([.store .d .r3 .r23 64, .store .d .r4 .r23 72, .store .d .r5 .r23 80, .store .d .r10 .r23 88,
      .addi .r3 .r7 0, .addi .r4 .r8 0, .addi .r5 .r9 0] : List Instr)) s fun t =>
      (word t.mem S 64 = s.gpr .r3 ∧ word t.mem S 72 = s.gpr .r4 ∧ word t.mem S 80 = s.gpr .r5 ∧
        word t.mem S 88 = s.gpr .r10 ∧ t.gpr .r3 = s.gpr .r7 ∧ t.gpr .r4 = s.gpr .r8 ∧ t.gpr .r5 = s.gpr .r9 ∧
        Outside S 64 32 s.mem t.mem) ∧ Keep [.r3, .r4, .r5] s t := by
  refine WP.keep _ ?_ (by decide)
  have i0 : InRegions s.wr (S + BitVec.ofNat 64 64) 8 := hin 0 (by decide)
  have i1 : InRegions s.wr (S + BitVec.ofNat 64 72) 8 := hin 1 (by decide)
  have i2 : InRegions s.wr (S + BitVec.ofNat 64 80) 8 := hin 2 (by decide)
  have i3 : InRegions s.wr (S + BitVec.ofNat 64 88) 8 := hin 3 (by decide)
  prun [h23, i0, i1, i2, i3, BitVec.add_zero]
  have o0 := writeW_outside s.mem S (d := 64) (s.gpr .r3) (by omega)
  have o1 := writeW_outside (s.mem.writeW (off S 64) (s.gpr .r3)) S (d := 72) (s.gpr .r4) (by omega)
  have o2 := writeW_outside ((s.mem.writeW (off S 64) (s.gpr .r3)).writeW (off S 72) (s.gpr .r4)) S (d := 80)
    (s.gpr .r5) (by omega)
  have o3 := writeW_outside (((s.mem.writeW (off S 64) (s.gpr .r3)).writeW (off S 72) (s.gpr .r4)).writeW
    (off S 80) (s.gpr .r5)) S (d := 88) (s.gpr .r10) (by omega)
  refine ⟨?_, ?_, ?_, word_writeW_self _ _ _ _, ?_⟩
  · show word _ S 64 = _
    rw [o3.word (by omega) (by omega), o2.word (by omega) (by omega), o1.word (by omega) (by omega)]
    exact word_writeW_self _ _ _ _
  · show word _ S 72 = _
    rw [o3.word (by omega) (by omega), o2.word (by omega) (by omega)]
    exact word_writeW_self _ _ _ _
  · show word _ S 80 = _
    rw [o3.word (by omega) (by omega)]
    exact word_writeW_self _ _ _ _
  · exact (((o0.mono (by omega) (by omega)).trans (o1.mono (by omega) (by omega))).trans
      (o2.mono (by omega) (by omega))).trans (o3.mono (by omega) (by omega))

end VG.Proof.Ffdh.PPC64LE.GenerateKey
