module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingPublic
public import VerifiedGarbage.Proof.MillerRabin.X86.FinishTiming

/-! # Compose the complete callable body without sharing secret memory -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt wOf)

theorem after_snapshot_ct {s t : State} (A : RoundABI s) (B : RoundABI t) (P : RoundPublic s t) :
    RelCT isa (fun a b => SnapshotReady s a ∧ SnapshotReady t b)
      (.seq arithmetic (.seq restoreProtected (.seq (.block finish) (.block [])))) (fun _ _ => True) := by
  intro a b tr₁ tr₂ a' b' ⟨ready₁, ready₂⟩ e₁ e₂
  have C := P.snapshot_context A B ready₁ ready₂
  have initial₁ := Stage.initial ready₁.context ready₁.room (w := wOf s.mem (wsOf s))
  have initial₂ := Stage.initial C.initial₂.context C.initial₂.room (w := wOf s.mem (wsOf s))
  have arith := arithmetic_ct C initial₁ initial₂ (prepared_tail ready₁.width ready₁.prepared)
    (P.tail_second ready₂)
  exact (arith.seq (restore_finish_ct C)) a b tr₁ tr₂ a' b' ⟨rfl, rfl⟩ e₁ e₂

theorem RoundABI.workspace_fit {s : State} (A : RoundABI s) : arrAt (wOf s.mem (wsOf s)) 28 ≤ bytesOf s := by
  obtain ⟨_, _, _, _, fit, _⟩ := A.layout
  change arrAt (wOf s.mem (wsOf s)) 28 ≤ 8 * (arg s 1).toNat at fit
  simpa only [bytesOf, Nat.mul_comm] using fit

theorem body_ct {s t : State} (A : RoundABI s) (B : RoundABI t) (P : RoundPublic s t) :
    RelCT isa (fun a b => a = allocFrame 1132 s ∧ b = allocFrame 1132 t) body (fun _ _ => True) := by
  obtain ⟨hc, checked⟩ := entry_cert
  have entryCT : RelCT isa (fun a b => a = allocFrame 1132 s ∧ b = allocFrame 1132 t)
      (.block entry) (fun _ _ => True) :=
    RelCT.taint (A := taint) entryTaint (fun a b ⟨ha, hb⟩ => by
      subst a; subst b
      exact A.entry_agree B P.stack P.args) checked
  have entryPost := entryCT.wp (F₁ := EntryReady s) (F₂ := EntryReady t)
    (fun a b ⟨ha, hb⟩ => by subst a; subst b; exact ⟨entry_ok A, entry_ok B⟩)
  have backupCT := ((PieceInput.save_protected_ct (sp := (allocFrame 1132 s).gpr .esp)
    (len := arg s 1) A.workspace_fit).mono
    (P' := fun a b => True ∧ EntryReady s a ∧ EntryReady t b)
    (fun _ _ ⟨_, a, b⟩ => ⟨PieceInput.of_entry A a, P.entry_input B b⟩) (fun _ _ _ => trivial)).wp
    (F₁ := SnapshotReady s) (F₂ := SnapshotReady t)
    (fun _ _ ⟨_, a, b⟩ => ⟨snapshot_ok A a, snapshot_ok B b⟩)
  unfold body seqs
  simp only [List.foldr_cons, List.foldr_nil]
  exact entryPost.seq (backupCT.seq ((after_snapshot_ct A B P).mono
    (fun _ _ ⟨_, a, b⟩ => ⟨a, b⟩) (fun _ _ _ => trivial)))

end VG.Proof.MillerRabin.X86
