module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeR2CT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeR2CT
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega

/-! # Public addresses for copying the Montgomery encoding of one -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64

def PrimeGood (p : PrimeParams) (s : State) : Prop := ∃ mi, Good s p.B p.Z p.w mi

def CopyR1Regs (p : PrimeParams) (s : State) : Prop :=
  s.gpr .r12 = BitVec.ofNat 64 p.w ∧ s.gpr .rsi = off p.B (slot p.w aY) ∧
    s.gpr .rbx = off p.B (slot p.w aR1)

theorem copyR1Args_state {p : PrimeParams} {s : State} (h : PrimeGood p s) :
    WP isa (.block (([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY)))] : List Instr) ++
      extBase aR1 .rbx)) s (CopyR1Regs p) := by
  obtain ⟨mi, hg⟩ := h
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot p.w 8 hi; have := p.dims.z; omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12, .rsi] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.w ∧
    t.gpr .rsi = off p.B (slot p.w aY) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hdrOff, hg.rdi, hl sW (by decide), hl (sArr aY) (by decide),
        hg.hdr.hw, hg.hdr.harr aY (by decide)]) rfl) fun u ⟨⟨h12, hsi, hm⟩, hk⟩ => ?_
  have hu : Good u p.B p.Z p.w mi :=
    ⟨hg.scr.congr hk.2.2, (hk.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr⟩
  exact WP.mono (extBase_ok hu p.dims.z (by have := p.dims.w128; omega)
    (j := aR1) (by decide) (r := .rbx) (by decide) rfl rfl) fun t ⟨hbx, _, kt⟩ =>
      ⟨(kt.gpr (by decide)).trans h12, (kt.gpr (by decide)).trans hsi, hbx⟩

theorem copyR1_ct : RelCT isa (Two PrimeGood)
    Impl.Ffdh.X86_64.ParameterCandidate.copyR1 (fun _ _ => True) := by
  unfold Impl.Ffdh.X86_64.ParameterCandidate.copyR1
  refine RelCT.seq (two_post (two_taint [.rdi] ?_ (by taint_decide))
    (fun _ _ h => copyR1Args_state h)) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨mi, hs⟩ := hs
    obtain ⟨mi', ht⟩ := ht
    exact hs.rdi.trans ht.rdi.symm
  · exact two_taint [.r12, .rsi, .rbx] (by
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.trans ht.2.2.symm) (by taint_decide)

theorem copyR1_good {p : PrimeParams} {s : State} (h : PrimeGood p s) :
    WP isa Impl.Ffdh.X86_64.ParameterCandidate.copyR1 s (PrimeGood p) := by
  obtain ⟨mi, hg⟩ := h
  have hfit : slot p.w aR1 + 8 * (p.w + 2) ≤ p.Z := by
    exact Nat.le_trans (Nat.add_le_add_right
      (slot_mono p.w (show aR1 ≤ aRm1 by decide)) _) p.dims.x
  refine WP.mono (copyToExt_ok hg p.dims.z (by have := p.dims.w4; omega)
    (by have := p.dims.w128; omega) (a := aY) (d := aR1) (by decide) (by decide)
    hfit)
    fun t ⟨_, hf, hk⟩ => ?_
  exact ⟨mi, hg.scr.congr hk.2.2, (hk.gpr (by decide)).trans hg.rdi,
    hg.hdr.outside hf (by unfold slot; omega)⟩

end VG.Proof.Dsa.X86_64.Generation
