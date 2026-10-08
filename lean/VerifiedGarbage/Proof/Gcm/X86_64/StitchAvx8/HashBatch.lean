import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Core

/-! # A batch hashes ciphertext before it can be overwritten -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block blockAt)

def lead (dec : Bool) : Nat := if dec then 0 else 16

def window (s₀ : State) (dec : Bool) (g : Nat) : Nat → Block := fun i => hashBlock s₀ dec (g + i)

def Buffered (s₀ : State) (dec : Bool) (g : Nat) (m : Mem) : Prop :=
  ∀ i < 8, m.readW (hashAddr s₀ i) 128 = window s₀ dec g i

theorem CoreInv.hashBatch {s₀ s : State} {P : Nat → Block} {dec : Bool} {c g : Nat}
    (hp : SPre s₀) (h : CoreInv s₀ P dec c g s) (hcg : c = g + lead dec)
    (hB : Buffered s₀ dec g s.mem) (more : Bool) (hc : c + 8 ≤ nb s₀)
    (hn : more = true → g + 16 ≤ nb s₀) :
    WP isa (Impl.Gcm.X86_64.StitchAvx8.batch (nr s₀) 8 (lead dec)
      (Impl.Gcm.X86_64.StitchAvx8.q8 (nr s₀) more)) s
      (BatchPost s₀ s P (window s₀ dec g)
        (fun i => if more then window s₀ dec g (8 + i) else window s₀ dec g i)
        (hashPrefix s₀ dec g) c (lead dec) true) := by
  obtain ⟨hw, hwrap, hsub⟩ := h.batchBounds hp (lead dec) hcg.symm hc
  refine batch_ok hp true more (lead dec) h.env h.templates (by
    intro i hi; exact hB i hi) h.hash h.counter hw hwrap hsub
    (fun _ hm k hk => ?_) (fun _ hm k hk => ?_) (fun _ hm k hk => ?_) (fun _ _ _ => rfl)
  · rw [h.addr]
    exact in_rdwr (in_sub hp.d_in (by have := hn hm; omega))
  · rw [h.addr]
    exact hp.d_p.sub_left (Offset.sub_base (dp s₀) (d := 16 * (g + k)) (n := 16) (k := 16 * nb s₀)
      (by have := hn hm; omega))
  · rw [h.addr, h.data (g + k) (by have := hn hm; omega)]
    cases dec with
    | false =>
      have he : g + k < c := by change c = g + 16 at hcg; omega
      exact ite_eq_left he
    | true =>
      have he : ¬g + k < c := by change c = g + 0 at hcg; omega
      exact ite_eq_right he

end VG.Proof.Gcm.X86_64.StitchAvx8
