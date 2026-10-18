module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashArgs
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Omega

/-! Select the wrapped-seed buffer while preserving all other frame words. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG.Proof.Bignum (Outside writeW_outside)
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64

theorem useWrappedSeed_ok {s : State} {F S op : Addr}
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (hop : W 3 = op) :
    WP isa (.block Impl.Dsa.AArch64.Generation.useWrappedSeed) s fun t =>
      Rep t.mem F S V (upd W 25 op) ∧
      Outside F sLab 8 s.mem t.mem ∧ Keep [.x0] s t := by
  have h3 : s.mem.readW (F + BitVec.ofNat 64 24) 64 = op := (R.fr 3 (by decide)).trans hop
  refine WP.mono (WP.keep [.x0] (Q := fun t =>
    t.mem = s.mem.writeW (off F sLab) op) ?_ rfl rfl rfl) fun t ⟨hm, hk⟩ => ?_
  · unfold Impl.Dsa.AArch64.Generation.useWrappedSeed
    brun [exec_ldrSp (off := 24) (by decide), exec_storeSp (off := sLab) (by decide),
      L.sp, L.ld (d := 24) (n := 8) (by decide), L.st (d := sLab) (n := 8) (by decide), h3, off]
  · refine ⟨?_, ?_, hk⟩
    · rw [hm]
      exact R.wf L.geo (by decide : 25 < nW) op
    · rw [hm]
      exact writeW_outside _ _ _ (by decide)

end VG.Proof.Dsa.AArch64.Generation
