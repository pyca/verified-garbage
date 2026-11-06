module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrRound
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTBase
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrMain
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrRound
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTBase
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrMain
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# A candidate on AArch64: constant time of Miller–Rabin's loop

For the loop over the witnesses, for runs that agree on the public data
`q : FPub` and so on the shape of the test's result `q.sch.mr`, which fixes
how many iterations remain from each offset (`itersOf`): what Miller–Rabin
needs (`MrPre`) and what the end needs (`EndW`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY)
open VG.Proof.RsaKeyGen (shapeOf itersOf passS checksW)

/-- The working space of the public data. -/
abbrev FPub.L (q : FPub) : WsP := ⟨q.B, q.Z, q.w⟩

/-- The offset of iteration `j`'s witness. -/
abbrev uOf (q : FPub) (j : Nat) : Nat := 8 * q.w + 8 * q.w * j

/-- The iterations of the loop. -/
abbrev Nq (q : FPub) : Nat := itersOf (8 * q.w) q.rl q.sch.mr (8 * q.w)

/-- What the end needs of the state before Miller–Rabin. -/
def EndW (q : FPub) (s : State) : Prop :=
  word s.mem q.B (8 * kOut) = q.op ∧ word s.mem q.B (8 * kUsedP) = q.up ∧
    word s.mem q.B (8 * kLen) = BitVec.ofNat 64 (8 * q.w) ∧ OutUp s q.B q.Z q.op q.up (8 * q.w)

theorem checksW_lt (w : Nat) : checksW w < 2 ^ 62 := Nat.lt_of_le_of_lt (checksW_le w) (by decide)

/-- The registers of the round's branch and of `kStat`'s test. -/
theorem kStat0_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block [movi .x3 0, sth .x3 kStat]) s fun t => Ws t B Z w := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s.mem.writeW (off B (8 * kStat)) (BitVec.ofNat 64 0)) (by
    brun [h.x0, hdr_enc (show kStat < 32 by decide), h.scr.st (d := 8 * kStat) (by simp only [kStat, sFn]; omega)]
    rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
  exact h.congr' (Frm.of_outside (by rw [hm]; exact writeW_outside _ _ _ (by simp only [kStat, sFn]; omega))
    (List.mem_singleton_self (8 * kStat, 8))) (by msb_mut) k (by decide)

/-- What Miller–Rabin needs, for the public data. -/
def MrPre (q : FPub) (s : State) : Prop :=
  4 ≤ q.w ∧ q.w ≤ 128 ∧ slot q.w aE + 8 * (q.w + 2) ≤ q.Z ∧ q.rl < 2 ^ 64 ∧ ∃ (c bm : Nat) (r : List Byte),
    MrCtx s q.B q.Z q.w c bm ∧ ECtx s.mem q.B q.w c ∧
    wv s.mem q.B (slot q.w aR2) q.w = 2 ^ (64 * q.w) * 2 ^ (64 * q.w) % c ∧ 1 < c ∧
    VG.Proof.RsaKeyGen.PrimeShape (64 * q.w) c ∧ word s.mem q.B (8 * kRand) = q.rP ∧
    word s.mem q.B (8 * kRandLen) = BitVec.ofNat 64 r.length ∧ r.length = q.rl ∧
    word s.mem q.B (8 * kChecks) = BitVec.ofNat 64 (checksW q.w) ∧ Src s q.B q.Z q.rP r ∧
    word s.mem q.B (8 * kUsed) = BitVec.ofNat 64 (8 * q.w) ∧ 8 * q.w ≤ r.length ∧
    shapeOf (mrRest c (checksW q.w) r 1 0 (8 * q.w)) = q.sch.mr ∧ EndW q s

end VG.Proof.RsaKeyGen.AArch64
