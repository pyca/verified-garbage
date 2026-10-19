module

public import VerifiedGarbage.Proof.Rsa.X86.RvHelperTiming
public import VerifiedGarbage.Proof.Rsa.X86.RvBase
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # Relate fixed-count recovery loops while their secret arithmetic differs -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

/-- Functional invariants recover the public termination flag after each round. -/
theorem fixedLoop_relCT {body : Prog isa} {c : Nat}
    (I J : Nat → State → Prop) (positive : 0 < c)
    (schedule : WorkspacePublic body)
    (agree : ∀ k s t, I k s → J k t → VG.X86.Taint.Agree (workspaceTaint false) s t)
    (left : ∀ k s, k < c → I k s → WP isa body s fun t =>
      I (k + 1) t ∧ t.zf = some (decide (c - (k + 1) = 0)))
    (right : ∀ k s, k < c → J k s → WP isa body s fun t =>
      J (k + 1) t ∧ t.zf = some (decide (c - (k + 1) = 0))) :
    RelCT isa (fun s t => I 0 s ∧ J 0 t) (.loop body .ne)
      (fun s t => I c s ∧ J c t) := by
  have loop := VG.RelCT.loop (M := isa) (body := body) (c := .ne)
    (Q := fun s t => I c s ∧ J c t)
    (fun remaining s t => ∃ k, k + remaining = c ∧ 0 < remaining ∧ I k s ∧ J k t)
    (fun remaining s t tr ur sf tf ⟨k, sum, pos, hs, ht⟩ es et => by
      have trace := (schedule.trace _ _ _ _ _ _ (agree k s t hs ht) es et).1
      obtain ⟨is, zs⟩ := wp_result (left k s (by omega) hs) es
      obtain ⟨it, zt⟩ := wp_result (right k t (by omega) ht) et
      refine ⟨trace, ?_, ?_, ?_⟩
      · change sf.zf.map (!·) = tf.zf.map (!·)
        rw [zs, zt]
      · intro done
        have last : k + 1 = c := by
          change sf.zf.map (!·) = some false at done
          rw [zs] at done
          simp only [Option.map_some, Option.some.injEq, Bool.not_eq_false', decide_eq_true_eq] at done
          omega
        exact ⟨last ▸ is, last ▸ it⟩
      · intro more
        have next : k + 1 < c := by
          change sf.zf.map (!·) = some true at more
          rw [zs] at more
          simp only [Option.map_some, Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at more
          omega
        exact ⟨remaining - 1, by omega, k + 1, by omega, by omega, is, it⟩) c
  apply loop.mono
  · intro s t ⟨hs, ht⟩
    exact ⟨0, by omega, positive, hs, ht⟩
  · intro s t h; exact h

theorem ks_agree {g : Geo} {s0 t0 s t : State} {A B AW BW V W : Nat → Nat}
    {al bl aw bw sl tl : List Nat}
    (h : KS g s0 A al AW aw V sl s) (j : KS g t0 B bl BW bw W tl t) :
    VG.X86.Taint.Agree (workspaceTaint false) s t := by
  apply agree_regs
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact BitVec.eq_of_toNat_eq (h.ws.workspace.edi_toNat.trans j.ws.workspace.edi_toNat.symm)

end VG.Proof.Rsa.X86.Recover
