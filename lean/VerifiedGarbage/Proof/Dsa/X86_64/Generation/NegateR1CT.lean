module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyR1CT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyR1CT
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega

/-! # Public-width subtraction for the Montgomery encoding of minus one -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64

def NegateR1Regs (p : PrimeParams) (s : State) : Prop :=
  s.gpr .r12 = BitVec.ofNat 64 p.w ∧ s.gpr .r8 = off p.B (slot p.w aN) ∧
    s.gpr .r10 = off p.B (slot p.w aR1) ∧ s.gpr .rsi = off p.B (slot p.w aRm1)

theorem negateR1Args_state {p : PrimeParams} {s : State} (h : PrimeGood p s) :
    WP isa (.block (([.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aN)))] : List Instr) ++
      extBase aR1 .r10 ++ extBase aRm1 .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr))) s (NegateR1Regs p) := by
  obtain ⟨mi, hg⟩ := h
  have hw : p.w < 2 ^ 31 := by have := p.dims.w128; omega
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot p.w 8 hi; have := p.dims.z; omega)
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r12, .r8] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.w ∧
    t.gpr .r8 = off p.B (slot p.w aN) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hdrOff, hg.rdi, hl sW (by decide), hl (sArr aN) (by decide),
        hg.hdr.hw, hg.hdr.harr aN (by decide)]) rfl) fun u ⟨⟨h12, h8, hm⟩, ku⟩ => ?_
  have hu : Good u p.B p.Z p.w mi :=
    ⟨hg.scr.congr ku.2.2, (ku.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr⟩
  refine WP.mono (extBase_ok hu p.dims.z hw (j := aR1) (by decide)
    (r := .r10) (by decide) rfl rfl) fun v ⟨h10, hmv, kv⟩ => ?_
  have hv : Good v p.B p.Z p.w mi :=
    ⟨hu.scr.congr kv.2.2, (kv.gpr (by decide)).trans hu.rdi, by rw [hmv]; exact hu.hdr⟩
  refine WP.mono (extBase_ok hv p.dims.z hw (j := aRm1) (by decide)
    (r := .rsi) (by decide) rfl rfl) fun z ⟨hsi, _, kz⟩ => ?_
  refine WP.mono (WP.keep [.rbp] (Q := fun _ => True) (by xrun; exact ⟨_, rfl⟩) rfl) fun t ⟨_, kt⟩ => ?_
  exact ⟨(((kv.trans kz).trans kt).gpr (by decide)).trans h12,
    (((kv.trans kz).trans kt).gpr (by decide)).trans h8,
    ((kz.trans kt).gpr (by decide)).trans h10, (kt.gpr (by decide)).trans hsi⟩

theorem negateR1_ct : RelCT isa (Two PrimeGood)
    Impl.Ffdh.X86_64.ParameterCandidate.negateR1 (fun _ _ => True) := by
  unfold Impl.Ffdh.X86_64.ParameterCandidate.negateR1
  refine RelCT.seq (two_post (two_taint [.rdi] ?_ (by taint_decide))
    (fun _ _ h => negateR1Args_state h)) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨mi, hs⟩ := hs
    obtain ⟨mi', ht⟩ := ht
    exact hs.rdi.trans ht.rdi.symm
  · exact two_taint [.r12, .r8, .r10, .rsi] (by
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.1.trans ht.2.2.1.symm
      · exact hs.2.2.2.trans ht.2.2.2.symm) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation
