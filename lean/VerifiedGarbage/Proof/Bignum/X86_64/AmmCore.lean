import VerifiedGarbage.Proof.Bignum.X86_64.AmmBlock

/-!
# RSA with AVX512_IFMA on x86-64: the multiplication's loop

The start of `ammCore` (`r10 := rbx`, the count of blocks, the accumulators
and register 14 zeroed) gives `InBlk` for block 0 (`init_ok`), and the loop
of four blocks `InBlk` for block 4: the lanes after twenty steps
(`loop_ok`).
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 ammStep ammBlock)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw)

theorem xr_eq : ∀ r < 16, VG.Impl.Rsa.X86_64.CrtIfma.xr r = xr r := by decide

/-- The zeroing of the accumulators and register 14. -/
def zeros : List Instr :=
  (List.range 15).map fun r => .vop (.vbin .vpxor .l256 (VG.Impl.Rsa.X86_64.CrtIfma.xr r)
    (VG.Impl.Rsa.X86_64.CrtIfma.xr r) (VG.Impl.Rsa.X86_64.CrtIfma.xr r))

def checkZeros : Bool :=
  match Sym.init.run (fun _ => 0) zeros with
  | some σ => (List.range 15).all fun r => decide (σ.reg r = .zero)
  | none => false

theorem checkZeros_ok : checkZeros = true := by decide +kernel

theorem zeros_ok {s : State} :
    WP isa (.block zeros) s fun s' => (∀ r < 15, ∀ t < 4, qw s' (xr r) t = 0) ∧ Keeps s s' := by
  have h := checkZeros_ok
  unfold checkZeros at h
  split at h
  · rename_i σ hσ
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    refine WP.mono (run_ok (fun b d n hn hd => absurd hd (by omega)) hσ) fun s' hs => ⟨fun r hr t ht => ?_,
      ⟨fun r hr => hs.gpr hr, hs.mem, hs.rd, hs.wr, hs.mxcsr, hs.flags⟩⟩
    · rw [hs.reg _ t ht, xi_xr r (by omega), h r hr]; rfl
  · cases h

/-- The loop of four blocks, from block `4 - n`. -/
theorem loop_ok {s₀ : State} {a m : Nat → Nat → Nat} {k : Nat → Nat} {bl : Nat → Nat → Nat}
    (e : Env s₀ a m k bl) :
    ∀ n s, 1 ≤ n → n ≤ 4 → InBlk s₀ s a m k bl (4 - n) 0 → s.gpr .rcx = BitVec.ofNat 64 n →
      WP isa (.loop (.block ammBlock) .ne) s fun s' =>
        InBlk s₀ s' a m k bl 4 0 ∧ (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧
        s'.mxcsr = s.mxcsr := by
  intro n s h1 h4 hi hc
  refine WP.loop (M := isa) (body := .block ammBlock) (c := .ne)
    (Q := fun s' => InBlk s₀ s' a m k bl 4 0 ∧ (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.mxcsr = s.mxcsr)
    (fun n (t : State) => 1 ≤ n ∧ n ≤ 4 ∧ InBlk s₀ t a m k bl (4 - n) 0 ∧ t.gpr .rcx = BitVec.ofNat 64 n ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → t.gpr r = s.gpr r) ∧ t.mxcsr = s.mxcsr) ?_ n s
    ⟨h1, h4, hi, hc, fun _ _ _ _ => rfl, rfl⟩
  intro n t ⟨h1, h4, hi, hc, hg, hx⟩
  refine WP.mono (ammBlock_ok (blk := 4 - n) (by omega) e hi (by rw [hc]; congr 1; omega))
    fun t' ⟨hi', hc', hz, hg', hx'⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_or_lt_of_le h1 with rfl | hn
  · refine .inl ⟨by simp, ?_, fun r r1 r2 r3 => (hg' r r1 r2 r3).trans (hg r r1 r2 r3), hx'.trans hx⟩
    exact hi'
  · refine .inr ⟨by simp only [decide_eq_false (show ¬ (4 - n + 1 = 4) by omega), Bool.not_false], n - 1,
      by omega, by omega, by omega, by rw [show 4 - (n - 1) = 4 - n + 1 by omega]; exact hi',
      by rw [hc']; congr 1; omega, fun r r1 r2 r3 => (hg' r r1 r2 r3).trans (hg r r1 r2 r3), hx'.trans hx⟩

end VG.Proof.Bignum.X86_64.AmmSym
