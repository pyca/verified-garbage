module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundState
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundStatus
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages
import Mathlib.Basic.IsEmpty.Defs

/-! # FFDH parameter generation on x86-64: composite or next accepted round -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate (kFlag)

theorem roundResult_ok {p : WitnessParams} {rp : Addr} {used i checks : Nat} {pass : Bool}
    {bs : List Byte} {s : State} (h : DrawState p rp used bs s)
    (hflag : word s.mem p.I (8 * kFlag) = mask pass)
    (hi : word s.mem p.O (8 * oIndex) = BitVec.ofNat 64 i)
    (hc : word s.mem p.O (8 * oChecks) = BitVec.ofNat 64 checks)
    (hi32 : i < 2 ^ 31) (hc32 : checks < 2 ^ 31) :
    WP isa roundResult s fun t => DrawState p rp used bs t ∧
      word t.mem p.O (8 * oStatus) = BitVec.ofNat 64 (if pass then passStatus i checks else 2) ∧
      word t.mem p.O (8 * oIndex) = BitVec.ofNat 64 (if pass then i + 1 else i) ∧
      RoundSaved p s.mem t.mem ∧ DrawFrame p s.mem t.mem ∧ Keep mmRegs s t := by
  have h184 : 184 ≤ p.IZ := by
    have hz := p.dims.z
    unfold slot VG.Impl.Bignum.hdrBytes at hz
    omega_using [hz]
  have houter : Scr s p.O 256 := by
    simpa [off] using h.scr.sub (o := 0) (n := 256) p.space_bounds.1 (by decide)
  unfold roundResult
  refine WP.seq (WP.mono (roundFlag_ok h.ready.good.scr h184 h.ready.good.rdi hflag)
    fun u ⟨hz, hm, k⟩ => ?_)
  have hu := h.same_mem hm k ((k.gpr (by decide)).trans h.ready.good.rdi)
  have hiu : word u.mem p.O (8 * oIndex) = BitVec.ofNat 64 i := by rw [hm]; exact hi
  have hcu : word u.mem p.O (8 * oChecks) = BitVec.ofNat 64 checks := by rw [hm]; exact hc
  cases pass
  · refine WP.ite true (by simp only [eval, hz, Bool.not_false]) (fun _ => ?_) (by simp)
    refine WP.mono (roundFail_ok hu.ready.good.scr p.space_bounds.2.1 (houter.congr k.2.2)
      hu.ready.good.rdi hu.link) fun t ⟨hmt, kt⟩ => ?_
    obtain ⟨ht, _, hh, hf⟩ := hu.status_write (2#64) hmt kt ((kt.gpr (by decide)).trans hu.ready.good.rdi)
    refine ⟨ht, ?_, ?_, ?_, ?_, (k.trans kt).mono (by decide)⟩
    · rw [hmt]; exact word_writeW_self _ _ _ _
    · simpa only [Bool.false_eq_true, ↓reduceIte] using (hh _ (by decide) (by decide)).trans hiu
    · intro j hj _ _ _ _ h19
      rw [hh j hj h19, hm]
    · rw [← hm]; exact hf
  · refine WP.ite false (by simp only [eval, hz, Bool.not_true]) (by simp) (fun _ => ?_)
    refine WP.mono (roundPass_ok hu.ready.good.scr p.space_bounds.2.1 (houter.congr k.2.2)
      hu.ready.good.rdi hu.link hiu hcu hi32 hc32) fun t ⟨hmt, kt⟩ => ?_
    have hf : Frm p.O [(8 * oIndex, 16)] u.mem t.mem := by rw [hmt]; exact passMem_frame _ _ _ _
    have hlo : ∀ r ∈ [(8 * oIndex, 16)], 136 ≤ r.1 := by simp [oIndex]
    have hhi : ∀ r ∈ [(8 * oIndex, 16)], r.1 + r.2 ≤ 256 := by simp [oIndex]
    have ht := hu.outer_frame hf hlo hhi kt ((kt.gpr (by decide)).trans hu.ready.good.rdi)
    refine ⟨ht, ?_, ?_, ?_, ?_, (k.trans kt).mono (by decide)⟩
    · rw [hmt]; exact passMem_status _ _ _ _
    · rw [hmt]; exact passMem_index _ _ _ _
    · intro j hj _ _ _ h18 h19
      rw [hf.word_eq (fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        change 8 * j + 8 ≤ 144 ∨ 160 ≤ 8 * j
        omega_using [h18, h19]) (by omega), hm]
    · rw [← hm]
      exact DrawFrame.of_scr (InScr.of_frm hf (fun r hr => Nat.le_trans (hhi r hr) p.space_bounds.1))

end VG.Proof.Ffdh.X86_64.ParameterCandidate
