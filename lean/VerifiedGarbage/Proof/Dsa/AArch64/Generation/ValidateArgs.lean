module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Validate
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hash
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Omega

/-! # Set the packed-domain checker's arguments from the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem validateArgs_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {pLen qLen : Nat}
    (hp : pLen < 2 ^ 16) (hq : qLen < 2 ^ 16) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.validateArgs pLen qLen)) s fun t =>
      t.gpr .x0 = VG.Proof.Bignum.off (W 5) packed ∧ t.gpr .x4 = VG.Proof.Bignum.off (W 5) domainCheck ∧
      t.gpr .x2 = BitVec.ofNat 64 pLen ∧ t.gpr .x3 = BitVec.ofNat 64 qLen ∧
      t.mem = s.mem ∧ Keep [.x0, .x4, .x2, .x3] s t := by
  have cast (n : Nat) (hn : n < 2 ^ 16) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  refine WP.mono (WP.keep [.x0, .x4, .x2, .x3] (Q := fun t =>
      t.gpr .x0 = VG.Proof.Bignum.off (W 5) packed ∧ t.gpr .x4 = VG.Proof.Bignum.off (W 5) domainCheck ∧
      t.gpr .x2 = BitVec.ofNat 64 pLen ∧ t.gpr .x3 = BitVec.ofNat 64 qLen ∧ t.mem = s.mem) (by
    have hw : s.mem.readW (F + BitVec.ofNat 64 40) 64 = W 5 := R.fr 5 (by decide)
    brun [Impl.Dsa.AArch64.Generation.validateArgs, exec_ldrSp (off := 40) (by decide), L.sp,
      L.ld (d := 40) (n := 8) (by decide), hw,
      cast packed (by decide), cast domainCheck (by decide), cast pLen hp, cast qLen hq]) rfl rfl rfl)
    fun t ⟨⟨hdi, h8, hdx, hcx, hm⟩, hk⟩ => ⟨hdi, h8, hdx, hcx, hm, hk⟩

end VG.Proof.Dsa.AArch64.Generation
