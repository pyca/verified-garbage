import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8RowsCT

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

def BlockState (ps : List (Nat × Nat)) (a : Nat) (L : CtLayout) (s : State) : Prop :=
  HeadState L s ∧ Ops s.mem L.B L.w ps ∧ L.e=slot L.w a+8*L.I

def CoreReady (L : CtLayout) (s : State) : Prop := HeadState L s ∧ s.gpr .rbp=off L.B L.e

theorem setup_ct_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (L : CtLayout) (s : State)
    (h : BlockState ps a L s) : WP isa (.block (AdxTri8.setup ca)) s (CoreReady L) := by
  obtain ⟨⟨mi,hg,hI⟩,hv,he⟩ := h
  refine WP.mono (setup_ok hg.scr hg.rdi L.hZ hv pa hI) fun t ⟨pt,mt,kt⟩ => ?_
  exact ⟨⟨mi,⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,mt ▸ hg.hdr⟩,mt ▸ hI⟩,he ▸ pt⟩

theorem clear_ct_fw (L : CtLayout) (s : State) (h : CoreReady L s) :
    WP isa (.block AdxTri8.clearColumns) s (Stage 7 AdxTri8.columns L) := by
  obtain ⟨⟨mi,hg,hI⟩,hp⟩ := h
  refine WP.mono (clear_ok AdxTri8.columns s) fun t ⟨zt,mt,kt⟩ => ?_
  exact ⟨⟨mi,⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,mt ▸ hg.hdr⟩,mt ▸ hI⟩,
    (kt.gpr (by decide)).trans hp,value_zero_lt zt 7⟩

theorem block_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) hint).isSome=true) :
    RelCT isa (Two (BlockState ps a)) (AdxTri8.block ca) (fun _ _ => True) := by
  unfold AdxTri8.block
  refine RelCT.seq (two_piece [.rdi] ?_ hS (setup_ct_fw pa)) ?_
  · intro L s t hs ht
    exact head_pins L s t hs.1 ht.1
  exact RelCT.seq (two_piece [] (by simp [Pins]) (by taint_decide) clear_ct_fw)
    (rows_ct 7 0 AdxTri8.columns columns_regs (by decide) (by decide) checks_seven)

end VG.Proof.Bignum.X86_64.AdxTri8
