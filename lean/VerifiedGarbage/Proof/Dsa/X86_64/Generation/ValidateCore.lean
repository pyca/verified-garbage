module

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DomainCall
public import VerifiedGarbage.Proof.Dsa.X86_64.Parameters
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Validate
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf

/-! ### `Dsa.X86_64.Generation.ValidateArgs`, which this module and modules that import it used -/

section

/-! # Set the packed-domain checker's arguments from the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem validateArgs_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {pLen qLen : Nat}
    (hp : pLen < 2 ^ 32) (hq : qLen < 2 ^ 32) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.validateArgs pLen qLen)) s fun t =>
      t.gpr .rdi = off (W 5) packed ∧ t.gpr .r8 = off (W 5) domainCheck ∧
      t.gpr .rdx = BitVec.ofNat 64 pLen ∧ t.gpr .rcx = BitVec.ofNat 64 qLen ∧
      t.mem = s.mem ∧ Keep [.rdi, .r8, .rdx, .rcx, .rsi, .r9] s t := by
  have cast (n : Nat) (hn : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  refine WP.mono (WP.keep [.rdi, .r8, .rdx, .rcx, .rsi, .r9] (Q := fun t =>
      t.gpr .rdi = off (W 5) packed ∧ t.gpr .r8 = off (W 5) domainCheck ∧
      t.gpr .rdx = BitVec.ofNat 64 pLen ∧ t.gpr .rcx = BitVec.ofNat 64 qLen ∧ t.mem = s.mem) (by
    xrun [Impl.Dsa.X86_64.Generation.validateArgs, ea_sp, L.rsp,
      L.ld (d := 40) (by decide), R.slot (d := 40) (k := 5) rfl (by decide) rfl,
      sx_ofNat (by decide : packed < 2 ^ 31), sx_ofNat (by decide : domainCheck < 2 ^ 31),
      cast pLen hp, cast qLen hq]) rfl)
    fun t ⟨⟨hdi, h8, hdx, hcx, hm⟩, hk⟩ => ⟨hdi, h8, hdx, hcx, hm, hk⟩

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Reuse the complete verified domain checker inside parameter generation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
variable {checkName : String}
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem validateCore_ok (M : Mont) (Sq : MontS) {s : State} {F S : Addr}
    {V : Nat → Byte} {W : Nat → BitVec 64} (p : ParametersInput)
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (hbase : p.base = off (W 5) domainCheck)
    (hp : p.pLen < 2 ^ 32) (hq : p.qLen < 2 ^ 32)
    (hs : Scr s p.base Impl.Dsa.Layout.usedBytes)
    (src : Src s p.base Impl.Dsa.Layout.usedBytes (off (W 5) packed) p.params)
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩)
    (hstack : (below F 8).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩)
    (hparams : (below F 8).Disjoint ⟨off (W 5) packed, p.params.length⟩) :
    WP isa (.seq (.block (Impl.Dsa.X86_64.Generation.validateArgs p.pLen p.qLen))
      (.call checkName (Impl.Dsa.X86_64.Generate.checkParameters Sq.mm M.mm))) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (if Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params then 1 else 0) ∧
      Lay t F S ∧ Rep t.mem F S V W ∧
      Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩, below F 8] s.mem t.mem ∧ Keep coreRegs s t := by
  refine WP.seq (WP.mono (validateArgs_ok L R hp hq) fun u ⟨hdi, h8, hdx, hcx, hm, ku⟩ => ?_)
  have pre : ParametersPre p u := ⟨hs.congr ku.2.2, h8.trans hbase.symm, hdx, hcx,
    hdi ▸ src.congrK (fun a _ => by rw [hm]) ku⟩
  have usp : u.gpr .rsp = F := (ku.gpr (by decide)).trans L.rsp
  have call := domainCall_ok (name := checkName) M Sq pre
    (by simpa only [domainReturn, usp] using hstack)
    (by simpa only [domainReturn, usp, hdi] using hparams)
  refine WP.mono call fun t ⟨result, ft, kt⟩ => ?_
  have frame : Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩, below F 8] s.mem t.mem := by
    intro a ha
    rw [ft a (by simpa only [domainReturn, usp] using ha), hm]
  have Rt := rep_of_disjoint_frame R frame
    (by intro r hr; rcases List.mem_cons.mp hr with rfl | hr
        · exact hF
        · obtain rfl := List.mem_singleton.mp hr
          exact Offset.base_disjoint_below F (by decide))
    (by intro r hr; rcases List.mem_cons.mp hr with rfl | hr
        · exact hS
        · obtain rfl := List.mem_singleton.mp hr
          exact (L.dRS.sub_left (below_sub (by decide) (by decide))).symm)
  have keep := ku.trans kt
  exact ⟨result, lay_of_rep L R Rt rfl (keep.gpr (by decide)) keep.2.2, Rt, frame, keep.mono (by decide)⟩

theorem validateTest_ok {s : State} {valid : Bool}
    (hr : s.gpr .rax = BitVec.ofNat 64 (if valid then 1 else 0)) :
    WP isa (.block [.alu .test .rax (.reg .rax)]) s fun t =>
      t.zf = some (!valid) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (!valid) ∧ t.mem = s.mem) (by
    xrun [hr]
    cases valid <;> decide) rfl) fun t ⟨⟨hz, hm⟩, hk⟩ => ⟨hz, hm, hk⟩

end VG.Proof.Dsa.X86_64.Generation
