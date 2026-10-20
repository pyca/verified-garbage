module
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.FrameStore
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Initialize workspace pointers and cursors in the native generation frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

theorem frameDerived_ok {s : State} {F S B : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) (hbase : W 5 = B)
    {k offset : Nat} (hk : k < nW) (hd : offset < 2 ^ 31) :
    WP isa (.block [.mov .rax (.mem (sp 40)), .alu .add .rax (.imm (BitVec.ofNat 32 offset)),
      .store (sp (8 * k)) .rax]) s fun t =>
      Rep t.mem F S V (upd W k (off B offset)) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax] s t := by
  have hw : InRegions s.wr (off F (8 * k)) 8 :=
    ⟨_, hfr, Offset.contains_base _ (by unfold nW frameBytes at *; omega) (by unfold nW frameBytes at *; omega)⟩
  have hr : InRegions (s.rd ++ s.wr) (off F 40) 8 :=
    ⟨⟨F, frameBytes⟩, List.mem_append_right _ hfr, Offset.contains_base _ (by decide) (by decide)⟩
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off F (8 * k)) (off B offset))
    (by xrun [ea_sp, hsp, hr, hw, R.slot (d := 40) (k := 5) rfl (by decide) hbase, sx_ofNat hd]) rfl)
    fun t ⟨hm, kt⟩ => ?_
  exact ⟨hm ▸ R.wf G hk _, hm ▸ frameWord_write hk s.mem _, kt⟩

theorem frameZero_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) {k : Nat} (hk : k < nW) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (sp (8 * k)) .rax]) s fun t =>
      Rep t.mem F S V (upd W k 0) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax] s t := by
  have hw : InRegions s.wr (off F (8 * k)) 8 :=
    ⟨_, hfr, Offset.contains_base _ (by unfold nW frameBytes at *; omega) (by unfold nW frameBytes at *; omega)⟩
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off F (8 * k)) (0 : BitVec 64))
    (by xrun [ea_sp, hsp, hw]; rfl) rfl) fun t ⟨hm, kt⟩ => ?_
  exact ⟨hm ▸ R.wf G hk _, hm ▸ frameWord_write hk s.mem _, kt⟩

end VG.Proof.Dsa.X86_64.Generation
