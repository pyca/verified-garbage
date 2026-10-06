import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8RowsCT

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

def BlockState (a : Nat) (L : CtLayout) (s : State) : Prop :=
  HeadState L s ∧ L.e=slot L.w a+8*L.I

def CoreReady (L : CtLayout) (s : State) : Prop := HeadState L s ∧ s.gpr .rbp=off L.B L.e

theorem setup_ct_fw {a : Nat} (ha : a<8) (L : CtLayout) (s : State) (h : BlockState a L s) :
    WP isa (.block (AdxTri8.setup a)) s (CoreReady L) := by
  obtain ⟨⟨mi,hg,hI⟩,he⟩ := h
  refine WP.mono (setup_ok hg.scr hg.rdi hg.hdr L.hZ ha hI) fun t ⟨pt,mt,kt⟩ => ?_
  exact ⟨⟨mi,⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,mt ▸ hg.hdr⟩,mt ▸ hI⟩,he ▸ pt⟩

theorem clear_ct_fw (L : CtLayout) (s : State) (h : CoreReady L s) :
    WP isa (.block AdxTri8.clearColumns) s (Stage 7 AdxTri8.columns L) := by
  obtain ⟨⟨mi,hg,hI⟩,hp⟩ := h
  refine WP.mono (clear_ok AdxTri8.columns s) fun t ⟨zt,mt,kt⟩ => ?_
  exact ⟨⟨mi,⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,mt ▸ hg.hdr⟩,mt ▸ hI⟩,
    (kt.gpr (by decide)).trans hp,value_zero_lt zt 7⟩

theorem block_ct {a : Nat} (ha : a<8)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup a)) hint).isSome=true) :
    RelCT isa (Two (BlockState a)) (AdxTri8.block a) (fun _ _ => True) := by
  unfold AdxTri8.block
  refine RelCT.seq (two_piece [.rdi] ?_ hS (setup_ct_fw ha)) ?_
  · intro L s t hs ht
    exact head_pins L s t hs.1 ht.1
  exact RelCT.seq (two_piece [] (by simp [Pins]) (by taint_decide) clear_ct_fw)
    (rows_ct 7 0 AdxTri8.columns columns_regs (by decide) (by decide) checks_seven)

end VG.Proof.Bignum.X86_64.AdxTri8
