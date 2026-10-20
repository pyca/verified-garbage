module

public import VerifiedGarbage.Proof.Rsa.X86.CvDivD
public import VerifiedGarbage.Proof.Rsa.X86.CvDivN
import VerifiedGarbage.Proof.Rsa.X86.InvParts

/-! # Complete CRT parameter arithmetic and its workspace frame -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.CrtValues
open VG.Proof.Rsa.X86.Keys

def coreArrays : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 18, 19, 20, 21, 22, 23]
def coreSlots : List Nat := [sOdd, sB, sC, sT, sPodd, sE1, sE2, sE3, sMask]

theorem core_ok {g : Geometry} {s : State} (h : Start g s) :
    WP isa (core g.w) s fun t =>
      Keep g.base g.w coreArrays coreSlots s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t ∧
      num t.mem g.base g.w aZero = 0 ∧
      ∃ X₁ X₂, (0 < g.P → X₁ = g.N / g.P ∧ X₂ = g.N % g.P) ∧ Computed g X₁ X₂ t := by
  unfold core
  refine WP.seq (WP.mono (firstDiv_ok h) fun a ⟨ha, ka, ra⟩ => ?_)
  refine WP.seq ?_
  change WP isa (seqs (checksA g.w ++ checksB g.w)) a _
  rw [wp_seqs_append (by unfold checksA; exact List.cons_ne_nil _ _) (by unfold checksB; exact List.cons_ne_nil _ _)]
  refine WP.mono (checksA_ok ha) fun b ⟨hb, kb, rb⟩ => ?_
  refine WP.mono (checksB_ok hb) fun c ⟨hc, kc, rc⟩ => ?_
  refine WP.seq (WP.mono (divP_ok hc) fun d ⟨hd, kd, rd⟩ => ?_)
  refine WP.mono (divQ_ok hd) fun t ⟨ht, kt, rt⟩ => ?_
  have K : Keep g.base g.w coreArrays coreSlots s.mem t.mem :=
    (ka.mono (by decide) (by decide)).trans ((kb.mono (by decide) (by decide)).trans
      ((kc.mono (by decide) (by decide)).trans ((kd.mono (by decide) (by simp)).trans
        (kt.mono (by decide) (by simp)))))
  refine ⟨K, ra.trans ((rb.mono (by decide)).trans (rc.trans (rd.trans rt))), ?_, _, _, ha.division, ht⟩
  rw [K.num (by decide) (by decide) (h.ws.fit64 (by decide))]
  exact h.zeros aZero (by decide)
end VG.Proof.Rsa.X86.CrtValues
