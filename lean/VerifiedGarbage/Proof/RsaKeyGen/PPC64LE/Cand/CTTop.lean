module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.CTMain
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Body
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.CTMain
meta import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Body
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# A candidate on PPC64LE: the whole function in constant time

`code_ct`: two runs from calls with the same public data (`KRel`) leak the
same trace. The frames leak the stack pointer; the entry, `out`'s zeroing
and the test of `rand`'s length are checked by the taint analysis from the
arguments, whose test is then the same in both runs; then `main_ct`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (code body entry zeroOut finNone main restore frameBytes)
open VG.Impl.MillerRabin.PPC64LE.Search (geFlag)
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)

/-- The body's start. -/
def PS (a : CD) (u : State) : Prop := ∃ s0, KRel a s0 ∧ u = started s0

/-- After the entry. -/
def PE (a : CD) (t : State) : Prop := ∃ s0, KRel a s0 ∧ Bx s0 t ∧ Regs s0 t ∧ t.syms = s0.syms

/-- After `out`'s zeroing. -/
def PB (a : CD) (t : State) : Prop := ∃ s0, KRel a s0 ∧ BR s0 t

/-- After the test of `rand`'s length. -/
def PF (a : CD) (t : State) : Prop := ∃ s0, KRel a s0 ∧ BF s0 t

/-- Before the restore. -/
def PX (a : CD) (t : State) : Prop := ∃ s0, KRel a s0 ∧ Bx s0 t

theorem pins_PS : Pins PS [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] := by
  rintro a s₁ s₂ ⟨s0, k, rfl⟩ ⟨s0', k', rfl⟩ r hr
  rw [(started_ok k.1).gpr r (by revert hr; revert r; decide),
    (started_ok k'.1).gpr r (by revert hr; revert r; decide)]
  exact k.reg k' (by simp only [argRegs]; exact hr)

theorem pins_PE : Pins PE [.r23, .r24] := by
  rintro a s₁ s₂ ⟨s0, k, -, hr, -⟩ ⟨s0', k', -, hr', -⟩ r h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · rw [hr.r23, hr'.r23]; exact k.reg k' (by decide)
  · rw [hr.r24, hr'.r24]; exact k.reg k' (by decide)

theorem pins_PB : Pins PB [.r27, .r24] := by
  rintro a s₁ s₂ ⟨s0, k, h⟩ ⟨s0', k', h'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h.regs.r27, h'.regs.r27]; exact k.arg k' (by decide)
  · rw [h.regs.r24, h'.regs.r24]; exact k.reg k' (by decide)

theorem pins_PF : Pins PF [.r25] := by
  rintro a s₁ s₂ ⟨s0, k, h⟩ ⟨s0', k', h'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [h.1.regs.r25, h'.1.regs.r25]; exact k.reg k' (by decide)

theorem len_eval : ∀ (a : CD) (s₁ s₂ : State), PF a s₁ → PF a s₂ →
    isa.eval (.zero .d .r5) s₁ = isa.eval (.zero .d .r5) s₂ := by
  rintro a s₁ s₂ ⟨s0, k, -, h5⟩ ⟨s0', k', -, h5'⟩
  rw [eval_zero_ofNat _ _ (by split <;> decide) h5, eval_zero_ofNat _ _ (by split <;> decide) h5',
    k.oL_eq k', k.rL_eq k']

theorem body_ct {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) :
    RelCT isa (Two PS) (body trial R.name R.code) fun _ _ => True := by
  unfold body
  simp only [VG.Impl.RsaKeyGen.PPC64LE.Candidate.seqs]
  refine RelCT.seq (two_post (Ψ := PE) (two_taint _ pins_PS (by taint_decide)) fun a s ⟨s0, k, hs⟩ => ?_)
    (RelCT.seq (two_post (Ψ := PB) (two_taint _ pins_PE (by taint_decide))
      fun a s ⟨s0, k, hb, hr, sy⟩ => WP.mono (zeroS hb hr sy) fun t ht => ⟨s0, k, ht⟩)
    (RelCT.seq (two_post (Ψ := PF) (two_taint _ pins_PB (by taint_decide))
      fun a s ⟨s0, k, h⟩ => WP.mono (flagS h) fun t ht => ⟨s0, k, ht⟩)
    (RelCT.seq (two_post (Ψ := PX) (two_ite len_eval (two_taint _ (pins_and pins_PF) (by taint_decide))
      (two_mono (Ψ := SG MIn) (fun a s ⟨⟨s0, k, ⟨c, hr, sy⟩, h5⟩, ev⟩ => ⟨s0, k, ?_⟩) (main_ct D R)))
      fun a s ⟨s0, k, h⟩ => WP.mono (iteS D R k.2.1 h) fun t ht => ⟨s0, k, ht.1⟩)
      (two_taint [] (fun _ _ _ _ _ _ hr => by simp at hr) (by taint_decide)))))
  · subst hs
    exact WP.mono_syms (entry_ok (started_ok k.1)) fun t ⟨hb, hr⟩ sy => ⟨s0, k, hb, hr, sy⟩
  · have hav : oL s0 ≤ rL s0 := by
      rw [eval_zero_ofNat _ _ (by split <;> decide) h5] at ev
      by_contra hc; simp only [hc, ↓reduceIte] at ev; exact absurd ev (by decide)
    exact ⟨c, hr.r21, hr.r30, hr.r18, hr.r19, hr.r26, hr.r27, hr.r31, hr.r11, hav, sy, k.2.1⟩

/-- After `mflr`. -/
def P1 (a : CD) (s : State) : Prop := ∃ s0, KRel a s0 ∧ s = s0.write .r0 s0.lr

theorem code_ct {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) :
    RelCT isa (Two KRel) (code trial R.name R.code) fun _ _ => True := by
  unfold code
  refine RelCT.seq (two_post (Ψ := P1) (two_taint [] (fun _ _ _ _ _ _ hr => by simp at hr) (by taint_decide))
    fun a s k => WP.of_runBlock ⟨s.write .r0 s.lr,
      (by simp only [runBlock_cons, runStep_some, runBlock_nil, exec_mflr]), ⟨s, k, rfl⟩⟩)
    (RelCT.seq (RelCT.frame (fun _ _ ⟨a, h₁, h₂, hsp⟩ => hsp)
      (RelCT.alloc (fun s t ⟨s₁, s₂, ⟨a, h₁, h₂, hsp⟩, e₁, e₂⟩ => by subst e₁ e₂; simp only [pushed, hsp])
        ((body_ct D R).mono (fun x y ⟨s, t, ⟨s₁, s₂, ⟨a, ⟨s0, k, e₀⟩, ⟨s0', k', e₀'⟩, hsp⟩, e₁, e₂⟩, e₃, e₄⟩ =>
          ⟨a, ⟨s0, k, by rw [e₃, e₁, e₀]; rfl⟩, ⟨s0', k', by rw [e₄, e₂, e₀']; rfl⟩, by
            subst e₃ e₄ e₁ e₂ e₀ e₀'
            simp only [allocated, pushed, State.write] at hsp ⊢
            rw [hsp]⟩) fun _ _ h => h)))
      (RelCT.taint (A := taint) (ofRegs []) (fun _ _ hsp => ⟨hsp, fun r hr => by simp at hr⟩)
        (by taint_decide)))

end VG.Proof.RsaKeyGen.PPC64LE.Cand
