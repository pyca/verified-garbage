import VerifiedGarbage.Proof.Bignum.X86_64.G.Block
import VerifiedGarbage.Proof.Bignum.X86_64.AmmCore

/-!
# RSA with AVX512_IFMA on x86-64, any size: the multiplication's loop

`AmmCore` for `CrtIfmaG`: the zeroing of the accumulators and the zero
register (`zeros_ok`), and the loop of four blocks from `InBlk` for block
`4 - n` to `InBlk` for block 4: the lanes after `4 R` steps (`loop_ok`).
-/

namespace VG.Proof.Bignum.X86_64.G

open VG VG.X86_64
open VG.Impl.Rsa.X86_64.CrtIfmaG
open VG.Proof.Bignum.X86_64.AmmSym (Keeps)

variable {l : Lay}

/-- The zeroing of the accumulators and the zero register. -/
def zeros (l : Lay) : List Instr :=
  (List.range (2 * l.R + 5)).map fun r => .eop (.bin .vpxorq (vreg r) (vreg r) (vreg r))

def checkZeros (l : Lay) : Bool :=
  match ESym.init.run (fun _ => 0) (zeros l) with
  | some σ => (List.range (2 * l.R + 5)).all fun r => decide (σ.reg r = .zero)
  | none => false

theorem checkZeros_ok (hl : LayOk l) : checkZeros l = true := by
  rcases hl with rfl | rfl | rfl <;> decide +kernel

theorem zeros_ok (hl : LayOk l) {s : State} :
    WP isa (.block (zeros l)) s fun s' => (∀ r < 2 * l.R + 5, ∀ t < 4, qv s' (vreg r) t = 0) ∧ Keeps s s' := by
  obtain ⟨_, hR10⟩ := hl.bounds
  have h := checkZeros_ok hl
  unfold checkZeros at h
  split at h
  · rename_i σ hσ
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    refine WP.mono (run_ok (fun b d n hn hd => absurd hd (by omega)) (SRel.init s) hσ) fun s' hs =>
      ⟨fun r hr t ht => ?_, ⟨fun r hr => hs.gpr hr, hs.mem, hs.rd, hs.wr, hs.mxcsr, hs.flags⟩⟩
    rw [hs.reg _ t ht, vi_vreg r (by omega), h r hr]; rfl
  · cases h

/-- The loop of four blocks, from block `4 - n`. -/
theorem loop_ok (hl : LayOk l) {s₀ : State} {a m : Nat → Nat → Nat} {k : Nat → Nat} {bl : Nat → Nat → Nat}
    (e : Env l s₀ a m k bl) :
    ∀ n s, 1 ≤ n → n ≤ 4 → InBlk l s₀ s a m k bl (4 - n) 0 → s.gpr .rcx = BitVec.ofNat 64 n →
      WP isa (.loop (.block (ammBlock l)) .ne) s fun s' =>
        InBlk l s₀ s' a m k bl 4 0 ∧ (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧
        s'.mxcsr = s.mxcsr := by
  intro n s h1 h4 hi hc
  refine WP.loop (M := isa) (body := .block (ammBlock l)) (c := .ne)
    (Q := fun s' => InBlk l s₀ s' a m k bl 4 0 ∧ (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.mxcsr = s.mxcsr)
    (fun n (t : State) => 1 ≤ n ∧ n ≤ 4 ∧ InBlk l s₀ t a m k bl (4 - n) 0 ∧ t.gpr .rcx = BitVec.ofNat 64 n ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → t.gpr r = s.gpr r) ∧ t.mxcsr = s.mxcsr) ?_ n s
    ⟨h1, h4, hi, hc, fun _ _ _ _ => rfl, rfl⟩
  intro n t ⟨h1, h4, hi, hc, hg, hx⟩
  refine WP.mono (ammBlock_ok hl (blk := 4 - n) (by omega) e hi (by rw [hc]; congr 1; omega))
    fun t' ⟨hi', hc', hz, hg', hx'⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_or_lt_of_le h1 with rfl | hn
  · refine .inl ⟨by simp, ?_, fun r r1 r2 r3 => (hg' r r1 r2 r3).trans (hg r r1 r2 r3), hx'.trans hx⟩
    exact hi'
  · refine .inr ⟨by simp only [decide_eq_false (show ¬ (4 - n + 1 = 4) by omega), Bool.not_false], n - 1,
      by omega, by omega, by omega, by rw [show 4 - (n - 1) = 4 - n + 1 by omega]; exact hi',
      by rw [hc']; congr 1; omega, fun r r1 r2 r3 => (hg' r r1 r2 r3).trans (hg r r1 r2 r3), hx'.trans hx⟩

end VG.Proof.Bignum.X86_64.G
