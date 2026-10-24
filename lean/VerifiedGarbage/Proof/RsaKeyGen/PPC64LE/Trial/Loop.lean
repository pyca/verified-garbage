module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Trial.Entry
public import VerifiedGarbage.Proof.RsaKeyGen.TrialFilter

/-!
# Trial division on PPC64LE: the table's first `n` entries

`loop_ok`: from the table at `T` (`r23`, its entries `TrialTable32.entry i`)
and `r24 = n`, the entries in turn until one divides the candidate `c`:
`r22 :=` 1 if one of the first `n` does (`trialPrefix c n`), else 0. The
loop stops at the first divisor, when `entry_ok` clears `r24`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Trial

open VG VG.PPC64LE VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.PPC64LE.Trial VG.Proof.Bignum.PPC64LE VG.Proof.Mont
open VG.Proof.RsaKeyGen (trialPrefix trialPrefix_succ trialPrefix_hit entryDivides)

/-- The loop's state with `m` entries left of the first `n`, from its entry `u`:
`k = n − m` entries tested, none dividing `c`, the next at `r23` and the
count in `r24`. -/
def TInv (u : State) (T : Addr) (c n m : Nat) (v : State) : Prop :=
  ∃ k, m = n - k ∧ k < n ∧ (v.gpr .r23 = T + BitVec.ofNat 64 (8 * k) ∧ v.gpr .r24 = BitVec.ofNat 64 (n - k) ∧
    trialPrefix c k = false ∧ v.mem = u.mem) ∧ Keep entryRegs u v

/-- One entry: the loop goes on exactly when it does not divide and is not
the last; then with one entry fewer left, else with the result. -/
theorem step_ok {u : State} {B T : Addr} {Z o w c n m : Nat} (hs : Scr u B Z)
    (h10 : u.gpr .r10 = off B o) (h11 : u.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hc : val32 u.mem B o (2 * w) = c) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : o + 8 * w ≤ Z)
    (hn' : n ≤ 1024)
    (htab : ∀ i < n, u.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 = BitVec.ofNat 64 (TrialTable32.entry i) ∧
      InRegions (u.rd ++ u.wr) (T + BitVec.ofNat 64 (8 * i)) 8)
    {v : State} (hI : TInv u T c n m v) :
    WP isa entry v fun t =>
      isa.eval (.nonzero .d .r24) t = some (decide (c % tabEntry (n - m) ≠ 0 ∧ n - m + 1 ≠ n)) ∧
      (isa.eval (.nonzero .d .r24) t = some false →
        (t.gpr .r22 = BitVec.ofNat 64 (if trialPrefix c n then 1 else 0) ∧ t.mem = u.mem) ∧ Keep entryRegs u t) ∧
      (isa.eval (.nonzero .d .r24) t = some true → 0 < m ∧ TInv u T c n (m - 1) t) := by
  obtain ⟨k, hm, hk, ⟨v23, v24, hpre, vm⟩, kv⟩ := hI
  subst hm
  have hv : Scr v B Z := hs.congr kv.wr
  obtain ⟨tk, tr⟩ := htab k hk
  have hnk : n - (n - k) = k := by omega
  rw [hnk]
  refine WP.mono (entry_ok (c := c) (i := k) (n := n - k) hv ((kv.gpr .r10 (by decide)).trans h10) ((kv.gpr .r11 (by decide)).trans h11)
    (by rw [vm]; exact hc) hw hw' hZ (by omega) v23 (by rw [vm]; exact tk) (by rw [kv.rd, kv.wr]; exact tr) v24
    (by omega) (by omega)) fun t ⟨⟨t22, t23, t24, tm⟩, kt⟩ => ?_
  have kut := (kv.trans kt).mono (by intro r hr; simp only [List.mem_append] at hr; rcases hr with hr | hr <;> exact hr)
  by_cases hit : c % tabEntry k = 0
  · simp only [hit, ↓reduceIte] at t22 t24
    have ev : isa.eval (.nonzero .d .r24) t = some false := by rw [eval_nonzero, t24]; rfl
    refine ⟨by rw [ev]; simp [hit], fun _ => ⟨⟨by rw [t22, trialPrefix_hit hk (by
      simp only [entryDivides, decide_eq_true_eq]; exact hit)]; rfl, by rw [tm, vm]⟩, kut⟩,
      fun h => by rw [ev] at h; cases h⟩
  · simp only [hit, ↓reduceIte] at t22 t24
    have hpre' : trialPrefix c (k + 1) = false := by
      rw [trialPrefix_succ, hpre, Bool.false_or]
      simp only [entryDivides, decide_eq_false_iff_not]; exact hit
    by_cases hl : k + 1 = n
    · subst hl
      have ev : isa.eval (.nonzero .d .r24) t = some false := by
        rw [eval_nonzero, t24, Nat.add_sub_cancel_left, Nat.sub_self]; rfl
      refine ⟨by rw [ev]; simp, fun _ => ⟨⟨by rw [t22, hpre']; rfl, by rw [tm, vm]⟩, kut⟩,
        fun h => by rw [ev] at h; cases h⟩
    · have ev : isa.eval (.nonzero .d .r24) t = some true := by
        rw [eval_nonzero, t24, ne_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        simp only [Option.some.injEq, decide_eq_true_eq]
        omega
      refine ⟨by rw [ev]; simp only [Option.some.injEq]; exact (decide_eq_true ⟨hit, hl⟩).symm,
        fun h => (by rw [ev] at h; cases h), fun _ => ⟨by omega, k + 1, by omega, by omega,
          ⟨by rw [t23, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2,
            by rw [t24]; congr 1, hpre', by rw [tm, vm]⟩, kut⟩⟩

/-- The first `n` entries of the table at `T`. -/
theorem loop_ok {u : State} {B T : Addr} {Z o w c n : Nat} (hs : Scr u B Z)
    (h10 : u.gpr .r10 = off B o) (h11 : u.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hc : val32 u.mem B o (2 * w) = c) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : o + 8 * w ≤ Z)
    (hn : 1 ≤ n) (hn' : n ≤ 1024) (h23 : u.gpr .r23 = T)
    (htab : ∀ i < n, u.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 = BitVec.ofNat 64 (TrialTable32.entry i) ∧
      InRegions (u.rd ++ u.wr) (T + BitVec.ofNat 64 (8 * i)) 8)
    (h24 : u.gpr .r24 = BitVec.ofNat 64 n) :
    WP isa loop u fun t =>
      (t.gpr .r22 = BitVec.ofNat 64 (if trialPrefix c n then 1 else 0) ∧ t.mem = u.mem) ∧ Keep entryRegs u t := by
  refine WP.loop (M := isa) (Q := fun t => (t.gpr .r22 = BitVec.ofNat 64 (if trialPrefix c n then 1 else 0) ∧
      t.mem = u.mem) ∧ Keep entryRegs u t) (TInv u T c n) (fun m v hI => ?_) n u
    ⟨0, by omega, by omega, ⟨by rw [h23, Nat.mul_zero, BitVec.add_zero], by rw [h24, Nat.sub_zero], rfl, rfl⟩,
      Keep.refl _ _⟩
  refine WP.mono (step_ok hs h10 h11 hc hw hw' hZ hn' htab hI) fun t ⟨he, hf, ht⟩ => ?_
  cases e : isa.eval (.nonzero .d .r24) t with
  | none => rw [e] at he; cases he
  | some b =>
    cases b
    · exact .inl ⟨rfl, hf e⟩
    · obtain ⟨hm, hI'⟩ := ht e
      exact .inr ⟨rfl, m - 1, by omega, hI'⟩

end VG.Proof.RsaKeyGen.PPC64LE.Trial
