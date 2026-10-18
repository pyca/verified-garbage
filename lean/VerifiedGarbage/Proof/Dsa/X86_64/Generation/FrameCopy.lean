module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.FrameStore

/-! # Copy incoming stack arguments into the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

theorem frameCopy_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) {k src : Nat} (hk : k < nW)
    (hr : InRegions (s.rd ++ s.wr) (off F src) 8) :
    WP isa (.block [.mov .rax (.mem (sp src)), .store (sp (8 * k)) .rax]) s fun t =>
      Rep t.mem F S V (upd W k (word s.mem F src)) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax] s t := by
  have hw : InRegions s.wr (off F (8 * k)) 8 :=
    ⟨_, hfr, Offset.contains_base _ (by unfold nW frameBytes at *; omega) (by unfold nW frameBytes at *; omega)⟩
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off F (8 * k)) (word s.mem F src))
    (by xrun [ea_sp, hsp, hr, hw, VG.Proof.Bignum.word]) rfl) fun t ⟨hm, kt⟩ => ?_
  exact ⟨hm ▸ R.wf G hk _, hm ▸ frameWord_write hk s.mem _, kt⟩

end VG.Proof.Dsa.X86_64.Generation
