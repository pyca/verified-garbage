module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCTData
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchTerminate
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRestore
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCTData
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchTerminate
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRestore
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # Native failure clearing leaks only the public output pointer and width -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def SearchZeroCT (p : SearchPoint) (s : State) : Prop := SearchCTL p s ∧ s.gpr .rdi = p.inputs.control

private theorem zero_header (p : SearchPoint) (s : State) (h : SearchZeroCT p s) :
    WP isa (.block [.mov .rsi (.mem (hdr 5)), .mov .rcx (.mem (hdr 6)), .mov32 .rax (.imm 0)]) s
      fun t => t.gpr .rsi = p.inputs.c.op ∧ t.gpr .rcx = BitVec.ofNat 64 p.inputs.c.k := by
  obtain ⟨⟨original, h⟩, hd⟩ := h
  have scr := h.input.control_scr h.wr
  have hp : word s.mem p.inputs.control 40 = p.inputs.c.op :=
    h.headers (5, p.inputs.c.op) (by simp [SearchPublic.headers])
  have hk : word s.mem p.inputs.control 48 = BitVec.ofNat 64 p.inputs.c.k :=
    h.headers (6, BitVec.ofNat 64 p.inputs.c.k) (by simp [SearchPublic.headers])
  have hl5 : InRegions (s.rd ++ s.wr) (p.inputs.control + BitVec.ofNat 64 40) 8 := scr.ld (by decide)
  have hl6 : InRegions (s.rd ++ s.wr) (p.inputs.control + BitVec.ofNat 64 48) 8 := scr.ld (by decide)
  xrun [State.ea, hdr, hdrOff, hd, hp, hk, hl5, hl6]

theorem search_zero_ct : RelCT isa (Two SearchZeroCT) (VG.Impl.Rsa.X86_64.Keys.zeroOut 5 6)
    (fun _ _ => True) := by
  unfold VG.Impl.Rsa.X86_64.Keys.zeroOut
  refine RelCT.seq (two_piece [.rdi] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.2.trans h₂.2.symm) (by taint_decide) zero_header) ?_
  exact two_taint [.rsi, .rcx] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

private theorem exhausted_prefix (p : SearchPoint) (s : State) (h : SearchCTL p s) :
    WP isa (.block (terminal 3 ++ ([.mov .rdi (.reg .r12)] : List Instr))) s
      (SearchZeroCT { p with remaining := 0 }) := by
  obtain ⟨original, h⟩ := h
  rw [WP.block_append_iff]
  refine WP.mono (search_terminal h 3) fun t ⟨ht, _, _⟩ => ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun u =>
    u.gpr .rdi = p.inputs.control ∧ u.mem = t.mem) (by xrun [ht.r12]) rfl)
    fun u ⟨⟨hd, hm⟩, k⟩ => ⟨⟨original, ht.keep k hm (by decide)⟩, hd⟩

theorem search_exhausted_ct : RelCT isa (Two SearchCTL) exhausted (fun _ _ => True) := by
  unfold exhausted
  exact RelCT.seq (two_piece [.r12, .rsp] search_ctl_pins (by taint_decide) exhausted_prefix)
    (two_map (fun p => { p with remaining := 0 }) (fun _ _ h => h) search_zero_ct)

end VG.Proof.Ffdh.X86_64.Generation
