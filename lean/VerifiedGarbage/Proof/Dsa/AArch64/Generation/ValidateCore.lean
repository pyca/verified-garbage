module

public import VerifiedGarbage.Proof.Dsa.AArch64.Parameters
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Validate
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! ### `Dsa.AArch64.Generation.ValidateArgs`, which this module and modules that import it used -/

section

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
    omega_using [hn]
  refine WP.mono (WP.keep [.x0, .x4, .x2, .x3] (Q := fun t =>
      t.gpr .x0 = VG.Proof.Bignum.off (W 5) packed ∧ t.gpr .x4 = VG.Proof.Bignum.off (W 5) domainCheck ∧
      t.gpr .x2 = BitVec.ofNat 64 pLen ∧ t.gpr .x3 = BitVec.ofNat 64 qLen ∧ t.mem = s.mem) (by
    have hw : s.mem.readW (F + BitVec.ofNat 64 40) 64 = W 5 := R.fr 5 (by decide)
    brun [Impl.Dsa.AArch64.Generation.validateArgs, exec_ldrSp (off := 40) (by decide), L.sp,
      L.ld (d := 40) (n := 8) (by decide), hw,
      cast packed (by decide), cast domainCheck (by decide), cast pLen hp, cast qLen hq]) rfl rfl rfl)
    fun t ⟨⟨hdi, h8, hdx, hcx, hm⟩, hk⟩ => ⟨hdi, h8, hdx, hcx, hm, hk⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Reuse the complete verified domain checker inside parameter generation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem validateCore_ok (M : Mont) {s : State} {F S : Addr}
    {V : Nat → Byte} {W : Nat → BitVec 64} (p : ParametersInput)
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (hbase : p.base = VG.Proof.Bignum.off (W 5) domainCheck)
    (hp : p.pLen < 2 ^ 16) (hq : p.qLen < 2 ^ 16)
    (hs : Scr s p.base Impl.Dsa.Layout.usedBytes)
    (src : Src s p.base Impl.Dsa.Layout.usedBytes (VG.Proof.Bignum.off (W 5) packed) p.params)
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩) :
    WP isa (.seq (.block (Impl.Dsa.AArch64.Generation.validateArgs p.pLen p.qLen))
      (Impl.Dsa.AArch64.Generate.checkParameters M.mm)) s fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (if Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params then 1 else 0) ∧
      Lay t F S ∧ Rep t.mem F S V W ∧
      Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩] s.mem t.mem ∧ Keep coreRegs s t := by
  refine WP.seq (WP.mono (validateArgs_ok L R hp hq) fun u ⟨hdi, h8, hdx, hcx, hm, ku⟩ => ?_)
  have pre : ParametersPre p u := ⟨hs.congr ku.wr, h8.trans hbase.symm, hdx, hcx,
    hdi ▸ src.congrK (fun a _ => by rw [hm]) ku⟩
  refine WP.mono (parametersMain_ok M pre) fun t ⟨result, ft, kt⟩ => ?_
  have frame : Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩] s.mem t.mem := by
    intro a ha
    have hn := ha ⟨p.base, Impl.Dsa.Layout.usedBytes⟩ (by simp)
    change ¬ ofs p.base a < Impl.Dsa.Layout.usedBytes at hn
    rw [ft a (by omega_using [hn]), hm]
  have Rt := rep_of_disjoint_frame R frame
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hF)
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hS)
  have keep := ku.trans kt
  exact ⟨result, lay_of_rep L R Rt rfl keep.sp keep.wr, Rt, frame, keep.mono (by decide)⟩

theorem validateTest_ok {s : State} {valid : Bool}
    (hr : s.gpr .x0 = BitVec.ofNat 64 (if valid then 1 else 0)) :
    eval (.zero .x .x0) s = some (!valid) := by
  cases valid <;> simp only [eval, State.read, hr, Size.bits, BitVec.setWidth_eq] <;> rfl

end VG.Proof.Dsa.AArch64.Generation
