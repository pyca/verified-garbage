module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.AttemptFn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Front
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.Attempt
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.ScalarEq
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Status
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.DomainBody
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_generate_key_cached` on PPC64LE: correctness

`front` saves the registers, puts the context's pointer and its three
metadata words in the header (`ctxHdr_ok`), x's, `y`'s and `rand`'s addresses
and `x_len` in its words 8–11, and sets up (`cg_front`); then p is loaded and
checked, the body cuts x to the context's width and computes `g^x mod p` by
the context's comb (`bodyC_ok`), and the registers are restored
(`cg_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Impl.Ffdh.PPC64LE.Cached VG.Impl.Ffdh.PPC64LE.Cached.Generate
open VG.Proof.Ffdh.PPC64LE.Domain
open VG.Proof.Ffdh.PPC64LE.GenerateKey (gcOf gkHdr_ok)
open VG.Proof.Bignum (slot)

/-- `r12 :=` the stack's `ctx` argument. -/
theorem loadC_ok (s : State) (h : InRegions (s.rd ++ s.wr) (stackArgAddr s 3) 8) :
    WP isa (.block ([.addSp .r12 120, .load .d .r12 .r12 0] : List Instr)) s fun t =>
      (t.gpr .r12 = stackArg s 3 ∧ t.mem = s.mem) ∧ Keep [.r12] s t := by
  refine WP.keep _ ?_ (by decide)
  simp only [stackArgAddr, Nat.reduceMul, Nat.reduceAdd] at h
  have ea : exec (.addSp .r12 120) s = some (s.write .r12 (s.sp + BitVec.ofNat 64 120)) := by
    simp [exec]
  prun [ea, h, BitVec.add_zero]
  rfl

/-- `ctxHdr`: the context's pointer (`r12`) and its words 0–2 into the
header's words 0–3 at `S`. -/
theorem ctxHdr_ok {s : State} {S C : Addr} (h23 : s.gpr .r23 = S) (h12 : s.gpr .r12 = C)
    (hin : ∀ i < 4, InRegions s.wr (off S (8 * i)) 8) (hrd : ∀ i < 3, InRegions (s.rd ++ s.wr) (off C (8 * i)) 8) :
    WP isa (.block ctxHdr) s fun t =>
      (word t.mem S 0 = C ∧ word t.mem S 8 = word s.mem C 0 ∧ word t.mem S 16 = word s.mem C 8 ∧
        word t.mem S 24 = word s.mem C 16 ∧ Outside S 0 32 s.mem t.mem) ∧ Keep [.r0, .r6, .r11] s t := by
  refine WP.keep _ ?_ (by decide)
  have i0 : InRegions s.wr (S + BitVec.ofNat 64 0) 8 := hin 0 (by decide)
  have i1 : InRegions s.wr (S + BitVec.ofNat 64 8) 8 := hin 1 (by decide)
  have i2 : InRegions s.wr (S + BitVec.ofNat 64 16) 8 := hin 2 (by decide)
  have i3 : InRegions s.wr (S + BitVec.ofNat 64 24) 8 := hin 3 (by decide)
  have r0 : InRegions (s.rd ++ s.wr) (C + BitVec.ofNat 64 0) 8 := hrd 0 (by decide)
  have r1 : InRegions (s.rd ++ s.wr) (C + BitVec.ofNat 64 8) 8 := hrd 1 (by decide)
  have r2 : InRegions (s.rd ++ s.wr) (C + BitVec.ofNat 64 16) 8 := hrd 2 (by decide)
  unfold ctxHdr sth
  prun [hCtx, hBits, hBytes, hRows, h23, h12, i0, i1, i2, i3, r0, r1, r2]
  have o0 := writeW_outside s.mem S (d := 0) C (by omega)
  have o1 := writeW_outside (s.mem.writeW (off S 0) C) S (d := 8) (word s.mem C 0) (by omega)
  have o2 := writeW_outside ((s.mem.writeW (off S 0) C).writeW (off S 8) (word s.mem C 0)) S (d := 16)
    (word s.mem C 8) (by omega)
  have o3 := writeW_outside (((s.mem.writeW (off S 0) C).writeW (off S 8) (word s.mem C 0)).writeW
    (off S 16) (word s.mem C 8)) S (d := 24) (word s.mem C 16) (by omega)
  refine ⟨?_, ?_, ?_, word_writeW_self _ _ _ _, ?_⟩
  · show word _ S 0 = _
    rw [o3.word (by omega) (by omega), o2.word (by omega) (by omega), o1.word (by omega) (by omega)]
    exact word_writeW_self _ _ _ _
  · show word _ S 8 = _
    rw [o3.word (by omega) (by omega), o2.word (by omega) (by omega)]
    exact word_writeW_self _ _ _ _
  · show word _ S 16 = _
    rw [o3.word (by omega) (by omega)]
    exact word_writeW_self _ _ _ _
  · exact (((o0.mono (by omega) (by omega)).trans (o1.mono (by omega) (by omega))).trans
      (o2.mono (by omega) (by omega))).trans (o3.mono (by omega) (by omega))

end VG.Proof.Ffdh.PPC64LE.Cached
