module

public import VerifiedGarbage.Proof.MlKem.X86_64.SHTop
meta import VerifiedGarbage.Proof.MlKem.X86_64.SHTop
public import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
import all Init.Data.Nat.Bitwise.Basic
import Mathlib.Tactic.Conv
meta import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Loop
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Loop

/-!
# ML-KEM on x86-64: `Sample4.sampleH`, constant time but for the seeds

As `vg_mlkem_sample_ntt4_avx2` (`S4CT.lean`): two runs whose seeds and
pointers agree leak the same. The code but for the loops and the checks of
the counts is proven by the taint analysis from the pointers, with every
byte of the states secret: the sponge's state and blocks, which the fourth
state absorbs, flow only into the states, the fourth buffer and the
sponge's state, at fixed addresses. The loops of both runs read the same
output of the first three seeds (`S4.run_ct`), and the checks give both the
same flags (`branch3_ct`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.SH

variable {w16 : Bool}

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Proof.MlKem.X86_64.S4
open VG.Spec.MlKem

theorem startH_ct : RelCT isa (S4.R4W w16 fun σ s => s = σ)
    (.block (pro ++ Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) ++ absorb4))
    (S4.R4W w16 fun σ s => SqInvW w16 σ 0 s ∧ HR σ s.mem) :=
  relInv (fun σ s hp h => by subst h; exact startF_ok (preW_of hp))
    (taintRel [.rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.1]) (by taint_decide))

theorem hload_ct : RelCT isa (S4.R4W w16 fun σ s => SqInvW w16 σ 0 s ∧ HR σ s.mem) (.block hload)
    (S4.R4W w16 fun σ s => SqY w16 σ (hst σ 0) 0 0 s ∧ HR σ s.mem) :=
  relInv (fun σ s hp h => hload_ok (preW_of hp) h.1 h.2)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.1.env h₂.1.env) (by taint_decide))

theorem squeezesH_ct {fast : Bool} : RelCT isa (S4.R4W w16 fun σ s => SqY w16 σ (hst σ 0) 0 0 s ∧ HR σ s.mem)
    (squeezesH fast) (S4.R4W w16 fun σ s => SqY w16 σ (hst σ 3) 0 3 s ∧ HR σ s.mem) := by
  have hsq : ∃ hc : VG.Taint.Hint X86_64.Taint.T,
      (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeezesH fast) hc).isSome = true := by
    cases fast
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, c⟩ := hsq
  exact relInv (fun σ s hp h => squeezesH_ok (fast := fast) (preW_of hp) h.1 h.2)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.1.env h₂.1.env) c)

theorem hsave_ct : RelCT isa (S4.R4W w16 fun σ s => SqY w16 σ (hst σ 3) 0 3 s ∧ HR σ s.mem) (.block hsave)
    (S4.R4W w16 fun σ s => SqY w16 σ (hst σ 3) 0 3 s ∧ HS σ (hst σ 3) s.mem) :=
  relInv (fun σ s hp h => hsave_ok (preW_of hp) h.1)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.1.env h₂.1.env) (by taint_decide))

section
variable {Y Hf : State → Spec.Sha3.State}

theorem tabY_ct : RelCT isa (S4.R4W w16 fun σ s => SqY w16 σ (Y σ) 0 3 s ∧ HS σ (Hf σ) s.mem) (.block tabAddr)
    (S4.R4W w16 fun σ s => Q1 w16 σ (Y σ) (Hf σ) 0 s) :=
  relInv (fun σ s _ h => tabY_ok h.1 h.2)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.1.env h₂.1.env) (by taint_decide))

theorem run1Y_ct {K : Nat} (hK : K < 3) {h₂ : VG.Taint.Hint X86_64.Taint.T}
    (c₂ : (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block [.store (at_ .rbx (oCnt + 8 * K)) .rdi]) h₂).isSome = true) :
    RelCT isa (S4.R4W w16 fun σ s => Q1 w16 σ (Y σ) (Hf σ) K s) (run1 K w16)
      (S4.R4W w16 fun σ s => Q1 w16 σ (Y σ) (Hf σ) (K + 1) s) := by
  obtain ⟨⟨_, c₁⟩, _⟩ := setup_taint (by omega : K < 4) w16
  exact run_ct (N := 21) (by omega) (by decide) (by decide) (by decide)
    (fun σ s hp h => ⟨h.sq.env, setup_ok (preW_of hp) (by omega) (lbY1 hK h)⟩)
    (fun σ s₀ s hp h₀ hA => run1EndY_ok (preW_of hp) hK h₀ hA) c₁ c₂

theorem run2Y_ct {K : Nat} (hK : K < 3) {h₂ : VG.Taint.Hint X86_64.Taint.T}
    (c₂ : (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block [.store (at_ .rbx (oCnt + 8 * K)) .rdi]) h₂).isSome = true) :
    RelCT isa (S4.R4W w16 fun σ s => Q2 w16 σ (Y σ) (Hf σ) K s) (run2 K w16)
      (S4.R4W w16 fun σ s => Q2 w16 σ (Y σ) (Hf σ) (K + 1) s) := by
  obtain ⟨_, ⟨_, c₁⟩⟩ := setup_taint (by omega : K < 4) w16
  exact run_ct (N := 14) (by omega) (by decide) (by decide) (by decide)
    (fun σ s hp h => ⟨h.sq.env, contSetup_ok (preW_of hp) (by omega) (lbY2 hK h)
      (by rw [h.j K hK, ite_eq_right (by omega)]) (by have := h.st K hK; rwa [ite_eq_right (by omega)] at this)⟩)
    (fun σ s₀ s hp h₀ hA => run2EndY_ok (preW_of hp) hK h₀ hA) c₁ c₂

theorem pub_allFull3 {σ₁ σ₂ : State} (hq : sample4K.pub σ₁ σ₂) (t : Nat) : allFull3 σ₁ t = allFull3 σ₂ t := by
  simp only [allFull3, List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, Bool.true_and]
  rw [pub_Lt hq (K := 0) (by decide), pub_Lt hq (K := 1) (by decide), pub_Lt hq (K := 2) (by decide)]

theorem check3_ct : RelCT isa (S4.R4W w16 fun σ s => Q1 w16 σ (Y σ) (Hf σ) 3 s)
    (.block (cntFlags3 ++ ([.alu32 .cmp .r14 (.imm 0)] : List Instr))) (S4.R4W w16 fun σ s => Checked3 w16 σ (Y σ) (Hf σ) s) :=
  relInv (fun σ s hp h => check3_ok (preW_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) (by taint_decide))

theorem more3_ct {fast : Bool} : RelCT isa (S4.R4W w16 fun σ s => Checked3 w16 σ (Y σ) (Hf σ) s) (more3 fast w16)
    (S4.R4W w16 fun σ s => Done3 w16 σ (Hf σ) s) := by
  unfold more3
  refine RelCT.seq (relInv (fun σ s _ h => reset3_ok h) (taintRel [] SampleNtt.nil_regs (by taint_decide))) ?_
  have hsq : ∃ hc : VG.Taint.Hint X86_64.Taint.T,
      (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeezes 0 2 fast) hc).isSome = true := by
    cases fast
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, csq⟩ := hsq
  refine RelCT.seq (relInv (fun σ s hp h => sqM3_ok (fast := fast) (preW_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) csq)) ?_
  refine RelCT.seq (relInv (fun σ s _ h => tabY2_ok h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) (by taint_decide))) ?_
  refine RelCT.seq (run2Y_ct (K := 0) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run2Y_ct (K := 1) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run2Y_ct (K := 2) (by decide) (by taint_decide)) ?_
  exact relInv (fun σ s hp h => last3_ok (preW_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) (by taint_decide))

theorem branch3_ct {fast : Bool} : RelCT isa (S4.R4W w16 fun σ s => Checked3 w16 σ (Y σ) (Hf σ) s)
    (.ite .e (more3 fast w16) (.block [])) (S4.R4W w16 fun σ s => Done3 w16 σ (Hf σ) s) := by
  refine RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ => by
    show x.zf = y.zf; rw [h₁.zf, h₂.zf, pub_allFull3 hq])
    (RelCT.mono more3_ct (fun _ _ h => h.1) (fun _ _ h => h)) ?_
  have empty : RelCT isa (S4.R4W w16 fun σ s => Checked3 w16 σ (Y σ) (Hf σ) s ∧ allFull3 σ 168 = true) (.block [])
      (S4.R4W w16 fun σ s => Done3 w16 σ (Hf σ) s) :=
    relInv (fun σ s _ ⟨h, hf⟩ => WP.block_nil (Done3.of_full h hf)) (taintRel [] SampleNtt.nil_regs (by taint_decide))
  refine RelCT.mono empty (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩, hb⟩ => ?_) (fun _ _ h => h)
  have hz : x.zf = some false := hb
  have hf : allFull3 σ₁ 168 = true := by rw [h₁.zf] at hz; simpa using hz
  exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁, hf⟩, ⟨h₂, by rw [← pub_allFull3 hq]; exact hf⟩⟩

theorem tail3_ct {fast : Bool} : RelCT isa (S4.R4W w16 fun σ s => Q1 w16 σ (Y σ) (Hf σ) 3 s) (tail3 fast w16)
    (fun _ _ => True) := by
  unfold tail3
  exact RelCT.seq check3_ct (RelCT.seq branch3_ct
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide)))

end

theorem ctW {fast : Bool} : ConstantTime isa (sampleHKW w16).pre (sampleHKW w16).pub (sampleH fast w16) := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq startH_ct (RelCT.seq hload_ct
    (RelCT.seq (squeezesH_ct (fast := fast)) (RelCT.seq hsave_ct
      (RelCT.seq (tabY_ct (Y := fun σ => hst σ 3) (Hf := fun σ => hst σ 3)) ?_)))))
  refine RelCT.seq (run1Y_ct (K := 0) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run1Y_ct (K := 1) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run1Y_ct (K := 2) (by decide) (by taint_decide)) ?_
  exact tail3_ct

theorem ct {fast : Bool} : ConstantTime isa sampleHK.pre sampleHK.pub (sampleH fast) := by
  rw [sampleHK_eq]; exact ctW (w16 := false)

end VG.Proof.MlKem.X86_64.SH
