module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Transfer
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Compose existing word copies while retaining all source snapshots. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86

def transferRanges (ts : List WordTransfer) : List (Nat × Nat) :=
  ts.map fun t => (t.destination, 4 * t.words)

def TransferApart (a b : WordTransfer) : Prop :=
  a.destination + 4 * a.words ≤ b.destination ∨ b.destination + 4 * b.words ≤ a.destination

def TransferSourceApart (a b : WordTransfer) : Prop :=
  a.source + 4 * a.words ≤ b.destination ∨ b.destination + 4 * b.words ≤ a.source

structure TransferPlanFits (bytes : Nat) (ts : List WordTransfer) : Prop where
  fits : ∀ t ∈ ts, TransferFits bytes t
  targets : ts.Pairwise TransferApart
  sources : ∀ t ∈ ts, ∀ u ∈ ts, TransferSourceApart t u

theorem TransferPlanFits.mono {bytes bytes' : Nat} {ts : List WordTransfer}
    (P : TransferPlanFits bytes ts) (bound : bytes ≤ bytes') : TransferPlanFits bytes' ts :=
  ⟨fun t ht => ⟨Nat.le_trans (P.fits t ht).1 bound,
    Nat.le_trans (P.fits t ht).2.1 bound, (P.fits t ht).2.2⟩, P.targets, P.sources⟩

theorem transfer_words {s : State} {base : Addr} {bytes : Nat} {ts : List WordTransfer}
    (scr : Scr s base bytes) (plan : TransferPlanFits bytes ts) :
    WP isa (transferWords ts) s fun u =>
      (∀ t ∈ ts, val32 u.mem base t.destination t.words = val32 s.mem base t.source t.words) ∧
      Outs base (transferRanges ts) s.mem u.mem ∧ Keeps [.eax] s u := by
  induction ts generalizing s with
  | nil => exact WP.block_nil ⟨by simp, Outs.refl _ _ _, Keeps.refl _ _⟩
  | cons t ts ih =>
    have fit := plan.fits t (List.mem_cons_self ..)
    have targetPairs := List.pairwise_cons.mp plan.targets
    have rest : TransferPlanFits bytes ts := ⟨fun v hv => plan.fits v (List.mem_cons_of_mem _ hv),
      targetPairs.2, fun v hv w hw => plan.sources v (List.mem_cons_of_mem _ hv) w
        (List.mem_cons_of_mem _ hw)⟩
    refine WP.seq (WP.mono (word_transfer scr fit) fun u ⟨value, K, F⟩ => ?_)
    refine WP.mono (ih (scr.of_keeps K (by decide)) rest) fun v ⟨values, O, K'⟩ => ?_
    refine ⟨?_, ?_, K.trans K'⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · rw [O.val32 ?_ (by have := scr.nowrap; have := fit.1; omega), value]
        intro r hr
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
        exact targetPairs.1 w hw
      · rw [values w hw, F.val32 (plan.sources w (List.mem_cons_of_mem _ hw) t
          (List.mem_cons_self ..)) (by have := scr.nowrap; have := (rest.fits w hw).2.1; omega)]
    · have first : Outs base (transferRanges (t :: ts)) s.mem u.mem :=
        Outs.of_outside F (by simp [transferRanges])
      exact first.trans (O.mono (by intro r hr; exact List.mem_cons_of_mem _ hr))

end VG.Proof.Dsa.X86.Generation
