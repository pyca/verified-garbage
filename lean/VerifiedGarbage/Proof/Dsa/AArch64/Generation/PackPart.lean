module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Pack
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CopyBytes
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! # Copy one generated domain component while retaining the search frame -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

theorem packArgs_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {src dst len : Nat}
    (hs : src < 2 ^ 16) (hd : dst < 2 ^ 16) (hl : len ≤ 1024) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.packArgs src dst len)) s fun t =>
      t.gpr .x12 = VG.Proof.Bignum.off (W 5) src ∧ t.gpr .x2 = VG.Proof.Bignum.off (W 5) dst ∧
      t.gpr .x9 = BitVec.ofNat 64 len ∧
      t.mem = s.mem ∧ Keep [.x12, .x2, .x9, .x3] s t := by
  have cast (n : Nat) (hn : n < 2 ^ 16) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  refine WP.mono (WP.keep [.x12, .x2, .x9, .x3] (Q := fun t =>
      t.gpr .x12 = VG.Proof.Bignum.off (W 5) src ∧ t.gpr .x2 = VG.Proof.Bignum.off (W 5) dst ∧
      t.gpr .x9 = BitVec.ofNat 64 len ∧ t.mem = s.mem) (by
    have hw : s.mem.readW (F + BitVec.ofNat 64 40) 64 = W 5 := R.fr 5 (by decide)
    brun [Impl.Dsa.AArch64.Generation.packArgs, exec_ldrSp (off := 40) (by decide), L.sp,
      L.ld (d := 40) (n := 8) (by decide), hw,
      cast src hs, cast dst hd, cast len (by omega)]) rfl rfl rfl)
    fun t ⟨⟨hsi, hdi, hcx, hm⟩, hk⟩ => ⟨hsi, hdi, hcx, hm, hk⟩

theorem packPart_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {src dst : Nat} {bs : List Byte}
    (hs : src < 2 ^ 16) (hd : dst < 2 ^ 16) (hl : 2 ≤ bs.length ∧ bs.length ≤ 1024)
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) src) i) 1)
    (hwr : ∀ i < bs.length, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) dst) i) 1)
    (hb : ∀ i < bs.length, s.mem (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) src) i) = bs.getD i 0)
    (hsep : ∀ i < bs.length, ∀ j < bs.length,
      VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) src) i ≠ VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) dst) j)
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨VG.Proof.Bignum.off (W 5) dst, bs.length⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨VG.Proof.Bignum.off (W 5) dst, bs.length⟩) :
    WP isa (Impl.Dsa.AArch64.Generation.packPart src dst bs.length) s fun t =>
      Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (W 5) dst) bs.length = bs ∧
      Lay t F S ∧ Rep t.mem F S V W ∧
      Frame [⟨VG.Proof.Bignum.off (W 5) dst, bs.length⟩] s.mem t.mem ∧ Keep (.x0 :: mmRegs) s t := by
  unfold Impl.Dsa.AArch64.Generation.packPart
  refine WP.seq (WP.mono (packArgs_ok L R hs hd hl.2) fun u ⟨hsi, hdi, hcx, hm, ku⟩ => ?_)
  refine WP.mono (copyBytes_ok (by omega) hsi hdi hcx
    (fun i hi => by rw [ku.rd, ku.wr]; exact hrd i hi)
    (fun i hi => by rw [ku.wr]; exact hwr i hi)
    (fun i hi => by rw [hm]; exact hb i hi) hsep) fun t ⟨result, ft, kt⟩ => ?_
  have ff : Frame [⟨VG.Proof.Bignum.off (W 5) dst, bs.length⟩] s.mem t.mem := by
    intro a ha
    rw [ft a (by
      intro i hi he
      apply ha ⟨VG.Proof.Bignum.off (W 5) dst, bs.length⟩ (by simp)
      rw [he]
      exact Offset.contains_base _ (by omega) (by omega)), hm]
  have Rt := rep_of_disjoint_frame R ff
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hF)
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hS)
  have keep := ku.trans kt
  exact ⟨result, lay_of_rep L R Rt rfl keep.sp keep.wr, Rt, ff, keep.mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation
