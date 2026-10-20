module

import VerifiedGarbage.Proof.AesGcm.X86_64.Split.ShortRun
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.ShortRun
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# AES-GCM `seal_split` on x86-64 with AVX-512: the short path, in two runs

Untrusted: everything here is checked by Lean. Two runs test the same
public lengths (`Short.cond_rel`), so take the same path: `run` (`splitRun_rel`),
or `src` copied to `dst` from the same public pointers and length
(`copySrc`, checked by the taint analysis once they are loaded) and the text
sealed there (`Short.sealShort_rel`, from the states `withSrc` describes):
`runShort_rel`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts IsShort condE_ok condS_of cond_rel rel_next rel_piece keepsEnv
  sealShort_rel powers_ct powFrom_powers)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)

theorem copySrcArgs_check : ∃ hc, (taint.check (Taint.ofRegs [.r13, .r14, .r15, .rsp])
    (.block [.mov .rsi (.mem (at_ .r15 tlO)), .mov .rdi (.mem (at_ .r15 dataO)), .mov .rcx (.mem (at_ .r15 tlenO))])
    hc).isSome = true := ⟨_, by simp only [tlO, dataO, tlenO]; taint_decide⟩

theorem gatherCopy_check : ∃ hc, (taint.check (Taint.ofRegs (([.rsi, .rdi, .rcx] : List Reg) ++
    ([.r13, .r14, .r15, .rsp] : List Reg))) SealGather.copy hc).isSome = true := ⟨_, by taint_decide⟩

/-- After the entry, `seal_split` with the short path, in two runs. -/
theorem runShort_rel (hF : ShortFacts) (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToFn M) {fin : Prog isa}
    (hfr : FinRel M fin) : MidRel M (SealSplit.runShort (v.withBlk B) T.fn fin) := by
  intro s₀ s₀' Ctx W SP Np A D S T' nl al n sl R C C' X X' kM hNp hnl hal hR hNp' hnl' hal' hR'
  have hlt := C.data.ok.lt
  unfold SealSplit.runShort
  have hw : ∀ {s₀ : State} (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl), (s₀.gpr .rcx).toNat = nl →
      (s₀.gpr .r9).toNat = al → ∀ s, SEntry s₀ Ctx W SP A D S n sl s →
      WP isa Short.cond s fun u => u.zf = some (decide ¬IsShort nl al n) ∧ SEntry s₀ Ctx W SP A D S n sl u :=
    fun C hnl hal s h => WP.mono (condE_ok C.toOneCtx h.toOneEntry hnl hal) fun _ ⟨z, E, K⟩ =>
      ⟨z, E, by rw [K.mem]; exact h.src, by rw [K.mem]; exact h.slen⟩
  have c := rel_next (cond_rel (F₁ := SEntry s₀ Ctx W SP A D S n sl) (F₂ := SEntry s₀' Ctx W SP A D S n sl)
      (fun _ h => condS_of h.toOneEntry hnl hal) (fun _ h => condS_of h.toOneEntry hnl' hal')
      (by rw [← hnl]; exact BitVec.isLt _) (by rw [← hal]; exact BitVec.isLt _) (by omega))
    (hw C hnl hal) (hw C' hnl' hal')
  refine RelCT.seq c (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1])
    ((splitRun_rel v B T hfr C C' X X' kM hNp hnl hal hR hNp' hnl' hal' hR').mono
      (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h) ?_)
  by_cases hs : IsShort nl al n
  · have hn5 : n < 512 := hs.2.2.1
    have cp := rel_piece (F₁ := SEntry s₀ Ctx W SP A D S n sl) (F₂ := SEntry s₀' Ctx W SP A D S n sl)
      (b := [.mov .rsi (.mem (at_ .r15 tlO)), .mov .rdi (.mem (at_ .r15 dataO)), .mov .rcx (.mem (at_ .r15 tlenO))])
      (c := SealGather.copy)
      (G₁ := fun t => t.gpr .rsi = S ∧ t.gpr .rdi = D ∧ t.gpr .rcx = BitVec.ofNat 64 sl)
      (G₂ := fun t => t.gpr .rsi = S ∧ t.gpr .rdi = D ∧ t.gpr .rcx = BitVec.ofNat 64 sl)
      [.rsi, .rdi, .rcx] (fun _ h => h.env) (fun _ h => h.env) (keepsEnv (by decide +kernel))
      copySrcArgs_check (fun _ h => WP.mono (copySrcArgs_ok h) fun _ g => ⟨g.1, g.2.1, g.2.2.1⟩)
      (fun _ h => WP.mono (copySrcArgs_ok h) fun _ g => ⟨g.1, g.2.1, g.2.2.1⟩) (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) gatherCopy_check
    have cp' := rel_next cp (fun _ h => copySrc_ok C h hn5) (fun _ h => copySrc_ok C' h hn5)
    exact (RelCT.seq cp' ((sealShort_rel (powers_ct hF) C.oneCtx4 C'.oneCtx4 (powFrom_powers hF) (powFrom_powers hF) hNp hnl hal hR hNp' hnl' hal' hR' hs).mono
      (fun _ _ h => h) fun _ _ h => h)).mono (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h
  · exact RelCT.of_false fun _ _ h => by have := h.1.1.1.symm.trans h.2; simp [hs] at this

end VG.Proof.AesGcm.X86_64.Split
