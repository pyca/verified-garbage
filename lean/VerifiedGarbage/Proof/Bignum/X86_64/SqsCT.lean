import VerifiedGarbage.Proof.Bignum.X86_64.PubR2

/-!
# Multiword arithmetic on x86-64: the squarings of `R² mod m` are constant time

`sqs` counts its six squarings in a header slot; it leaks the same in runs
whose public data fix the working space, if a squaring and the count keep
what the runs know (`sqs_ctG`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

/-- The `ne` condition after a count that sets ZF when `j + 1 = n`. -/
theorem eval_ne_count {s : State} {j n : Nat} (hj : j < n) (hz : s.zf = some (decide (j + 1 = n))) :
    isa.eval .ne s = some (decide (j + 1 < n)) := by
  simp only [eval, hz, Option.map_some, Option.some.injEq]
  by_cases h : j + 1 = n
  · simp [h]
  · simp only [h, decide_false, Bool.not_false]; exact (decide_eq_true (by omega)).symm

/-- `sqs`' count after `j` squarings, in slot `sl` of the header at `rdi`. -/
def SqCnt (sl j : Nat) (s : State) : Prop := word s.mem (s.gpr .rdi) (8 * sl) = BitVec.ofNat 64 (6 - j)

/-- `sqs` leaks the same in runs whose public data `Φ` fixes, if each squaring
keeps `Φ` and the count does too. -/
theorem sqs_ctG (M : Mont) {α : Type} {Φ : α → State → Prop} {sl : Nat} (hpin : Pins Φ [.rdi])
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov32 .rcx (.imm 6), .store (hdr sl) .rcx]) hc).isSome = true)
    {hc' : VG.Taint.Hint VG.X86_64.Taint.T}
    (h' : (taint.check (Taint.ofRegs [.rdi]) (.block (dblCount sl)) hc').isSome = true)
    (one : RelCT isa (Two Φ) (M.mm aR2 aR2 aR2) fun _ _ => True)
    (hmm : ∀ a s, Φ a s → WP isa (M.mm aR2 aR2 aR2) s (Φ a))
    (hstart : ∀ a s, Φ a s → WP isa (.block [.mov32 .rcx (.imm 6), .store (hdr sl) .rcx]) s fun t =>
      Φ a t ∧ SqCnt sl 0 t)
    (hstep : ∀ a j s, j < 6 → Φ a s → SqCnt sl j s → WP isa (.seq (M.mm aR2 aR2 aR2) (.block (dblCount sl))) s
      fun t => t.zf = some (decide (j + 1 = 6)) ∧ Φ a t ∧ SqCnt sl (j + 1) t) :
    RelCT isa (Two Φ) (sqs M.mm sl) (Two Φ) := by
  unfold sqs
  refine RelCT.seq (two_piece (Ψ := fun a s => 0 < 6 ∧ Φ a s ∧ SqCnt sl 0 s) _ hpin h
    fun a s hs => WP.mono (hstart a s hs) fun t ht => ⟨by decide, ht⟩) ?_
  refine two_loop (Φ := fun a j s => Φ a s ∧ SqCnt sl j s) (fun _ => 6) ?_ ?_
  · exact RelCT.seq (two_post (Ψ := fun (q : α × Nat) s => Φ q.1 s)
      (two_map (·.1) (fun _ _ h => h.2.1) one) fun q s h => hmm q.1 s h.2.1)
      (two_taint _ (fun q s₁ s₂ h₁ h₂ => hpin q.1 s₁ s₂ h₁ h₂) h')
  · rintro a j s hj ⟨hs, hc⟩
    exact WP.mono (hstep a j s hj hs hc) fun t ⟨hz, ht, hc'⟩ =>
      ⟨eval_ne_count hj hz, fun _ => ⟨ht, hc'⟩, fun _ => ht⟩

end VG.Proof.Bignum.X86_64
