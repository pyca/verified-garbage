module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.QCandidate
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hash
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Omega

/-! Transfer the persistent subgroup destination and digest pointer to byte shaping. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64

theorem qArgs_ok {s : State} {F S qp : Addr} {len : Nat}
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep s.mem F S V W)
    (hp : W 0 = qp) (hl : W 26 = BitVec.ofNat 64 len) :
    WP isa (.block Impl.Dsa.AArch64.Generation.qArgs) s fun t =>
      t.gpr .x2 = qp ∧ t.gpr .x12 = VG.Proof.Bignum.off S oDig ∧ t.gpr .x9 = BitVec.ofNat 64 len ∧
      t.mem = s.mem ∧ Keep [.x2, .x12, .x9] s t := by
  refine WP.mono (WP.keep [.x2, .x12, .x9] (Q := fun t =>
    t.gpr .x2 = qp ∧ t.gpr .x12 = VG.Proof.Bignum.off S oDig ∧ t.gpr .x9 = BitVec.ofNat 64 len ∧ t.mem = s.mem)
    ?_ rfl rfl rfl) fun t ⟨ht, hk⟩ => ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2, hk⟩
  have hpw : s.mem.readW (F + BitVec.ofNat 64 0) 64 = qp := (R.fr 0 (by decide)).trans hp
  have hlw : s.mem.readW (F + BitVec.ofNat 64 sLabLen) 64 = BitVec.ofNat 64 len := (R.fr 26 (by decide)).trans hl
  have hsw : s.mem.readW (F + BitVec.ofNat 64 sScr) 64 = S := L.slot
  have hperm : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 0) 8 := by
    rw [L.sp]
    exact L.ld (d := 0) (n := 8) (by decide)
  have hload := exec_ldrSp (t := .x2) (off := 0) (by decide) hperm
  unfold Impl.Dsa.AArch64.Generation.qArgs
  brun [hload, exec_ldrSp (off := sScr) (by decide),
    exec_ldrSp (off := sLabLen) (by decide), L.sp,
    L.ld (d := sScr) (n := 8) (by decide),
    L.ld (d := sLabLen) (n := 8) (by decide), hpw, hlw, hsw]
  simpa only [BitVec.add_zero] using hpw

end VG.Proof.Dsa.AArch64.Generation
