module

public import VerifiedGarbage.Proof.Rsa.X86.RvWindowOps
public import VerifiedGarbage.Proof.Rsa.X86.RvMont
public import VerifiedGarbage.Proof.Rsa.X86.RvMontTracked
public import VerifiedGarbage.Proof.Rsa.X86.RvMontStage
public import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Rsa.X86.RvWrite
import VerifiedGarbage.Proof.Rsa.X86.InvParts

/-! # The candidate's window table, and the scan that reads its entries

The table holds the candidate's powers `0` to `15` in Montgomery form, in
arrays `0` to `15`, below the Montgomery accumulator.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Impl.Rsa.X86.RecoverRt (nar)
open VG.Impl.Rsa.X86.KeyRt (copy)
open VG.Proof.Rsa.X86.Keys

/-- The arrays with the table's first `k` entries. -/
def tableA (A : Nat → Nat) (n m b k : Nat) : Nat → Nat :=
  fun j => if j < k then b ^ j * 2 ^ (64 * n) % m else A j

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live liveW : List Nat}
  {AW : Nat → Nat} {V : Nat → Nat} {ls : List Nat}

/-- What the table's construction leaves of the stage: arrays above the
accumulator, other than the Montgomery temporaries. -/
structure TableLive (live : List Nat) : Prop where
  above : ∀ j ∈ live, 20 ≤ j
  tmp : mTmp ∉ live
  xm : mXm ∉ live

/-- The table's first `i + 2` entries, the last in `mXm` too. -/
def TI (g : Geo) (s0 : State) (A AW V : Nat → Nat) (live ls : List Nat) (m b i : Nat) (s : State) : Prop :=
  KS g s0 (upd (tableA A g.n m b (i + 2)) mXm (b ^ (i + 1) * 2 ^ (64 * g.n) % m))
    (mXm :: (List.range (i + 2) ++ live)) AW [wRc, wR] V ls s

/-- One of the table's unrolled steps: the next power into `mXm`, and into entry `i + 2`. -/
abbrev tableStep (i : Nat) : Prog isa :=
  .seq (VG.Impl.Rsa.X86.RecoverRt.mmul mXm mXm mG) (copy nar (i + 2) mXm)

theorem tableStep_ok {m b i : Nat} (h : TI g s0 A AW V live ls m b i s) (L : TableLive live)
    (hG : mG ∈ live) (hB : mBase ∈ live)
    (hI : sInv ∈ ls) (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (odd : m % 2 = 1) (positive : 0 < m)
    (base : A mG = b * 2 ^ (64 * g.n) % m) (hi : i < 14) :
    WP isa (tableStep i) s (TI g s0 A AW V live ls m b (i + 1)) := by
  have aboveA (j : Nat) (hj : j ∈ live) (k : Nat) (hk : k ≤ 16) : tableA A g.n m b k j = A j := by
    have := L.above j hj
    simp only [tableA, show ¬ j < k by omega, ↓reduceIte]
  have notX (j : Nat) (hj : j ∈ live) : j ≠ mXm := fun e => L.xm (e ▸ hj)
  unfold TI at h
  -- The next power, in `mXm`.
  have mr := h.montReady (m := m) (by simp [hB]) hI
    (by rw [upd_ne _ _ (by decide), aboveA _ hB _ (by omega)]; exact value) bound inverse
  refine WP.seq (WP.mono (h.mmul mr (o := mXm) (a := mXm) (b := mG) (by decide) (by decide)
    (by decide) (by decide) (by simp) (by simp [hG])
    (by rw [upd_self]; exact Nat.mod_lt _ positive)
    (by rw [upd_ne _ _ (by decide), aboveA _ hG _ (by omega), base]; exact Nat.mod_lt _ positive)
    ?_ (by decide)) fun s₁ ⟨X, h₁, _, _, lt, v⟩ => ?_)
  · intro j hj
    simp only [List.mem_cons, List.mem_append, List.mem_range] at hj
    rcases hj with e | lo | hi
    · exact .inl e
    · right; simp only [montWrites, List.mem_cons, List.not_mem_nil, or_false]; unfold mXm mAcc; omega
    · have := L.above j hi
      have := notX j hi
      right; simp only [montWrites, List.mem_cons, List.not_mem_nil, or_false]; unfold mAcc; omega
  have power : X = b ^ (i + 2) * 2 ^ (64 * g.n) % m := by
    have p := VG.Proof.Dsa.mont_product (VG.Proof.Bignum.coprime_pow2 odd _)
      (a := b ^ (i + 1)) (b := b) (by rw [upd_self, Nat.mod_mod])
      (by rw [upd_ne _ _ (by decide), aboveA _ hG _ (by omega), base, Nat.mod_mod]) v
    rwa [Nat.mod_eq_of_lt lt, ← Nat.pow_succ] at p
  rw [upd_twice, power] at h₁
  -- Into entry `i + 2`.
  refine WP.mono (h₁.copy_w (o := i + 2) (a := mXm) (by unfold nArr; omega) (by simp)
    (by unfold mXm; omega) (by intro j hj; simp [wRc, wR] at hj; omega)) fun t ⟨ht, _, _⟩ => ?_
  rw [upd_self] at ht
  refine ht.mono (fun j hj => ⟨?_, ?_⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  · simp only [List.mem_cons, List.mem_append, List.mem_range] at hj ⊢
    rcases hj with e | lo | hi
    · exact .inr (.inl e)
    · by_cases e2 : j = i + 2
      · exact .inl e2
      · exact .inr (.inr (.inr (.inl (by omega))))
    · exact .inr (.inr (.inr (.inr hi)))
  · by_cases ex : j = mXm
    · subst ex
      rw [upd_ne _ _ (by unfold mXm; omega), upd_self, upd_self]
    · by_cases e2 : j = i + 2
      · subst e2
        rw [upd_self, upd_ne _ _ ex]
        simp only [tableA, show i + 2 < i + 1 + 2 by omega, ↓reduceIte]
      · rw [upd_ne _ _ e2, upd_ne _ _ ex, upd_ne _ _ ex]
        simp only [tableA]
        by_cases lt2 : j < i + 2
        · simp only [lt2, show j < i + 1 + 2 by omega, ↓reduceIte]
        · simp only [lt2, show ¬ j < i + 1 + 2 by omega, ↓reduceIte]

theorem table_ok {m b : Nat} (h : KS g s0 A live AW [wRc, wR] V ls s) (L : TableLive live)
    (hO : aO ∈ live) (hG : mG ∈ live) (hB : mBase ∈ live)
    (hI : sInv ∈ ls) (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (odd : m % 2 = 1) (positive : 0 < m)
    (one : A aO = 2 ^ (64 * g.n) % m) (base : A mG = b * 2 ^ (64 * g.n) % m) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.table s fun t =>
      KS g s0 (tableA A g.n m b 16) (List.range 16 ++ live) AW [wRc, wR] V ls t := by
  let pre : List (Prog isa) := [copy nar 0 aO, copy nar 1 mG, copy nar mXm mG]
  have init : WP isa (seqs pre) s (TI g s0 A AW V live ls m b 0) := by
    simp only [pre, seqs]
    refine WP.seq (WP.mono (h.copy_w (o := 0) (a := aO) (by decide) hO (by decide) (by decide))
      fun s1 ⟨h1, _, _⟩ => ?_)
    refine WP.seq (WP.mono (h1.copy_w (o := 1) (a := mG) (by decide) (by simp [hG]) (by decide) (by decide))
      fun s2 ⟨h2, _, _⟩ => ?_)
    refine WP.mono (h2.copy_w (o := mXm) (a := mG) (by decide) (by simp [hG]) (by decide) (by decide))
      fun s3 ⟨h3, _, _⟩ => ?_
    refine h3.mono (fun j hj => ⟨?_, ?_⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
    · simp only [List.mem_cons, List.mem_append, List.mem_range] at hj ⊢
      rcases hj with e | lo | hi
      · exact .inl e
      · rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
        · exact .inr (.inr (.inl rfl))
        · exact .inr (.inl rfl)
      · exact .inr (.inr (.inr hi))
    · have mG1 : (upd (upd A 0 (A aO)) 1 (upd A 0 (A aO) mG)) mG = A mG := by
        rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]
      by_cases ex : j = mXm
      · subst ex
        rw [upd_self, upd_self, mG1, base, Nat.pow_one]
      · rw [upd_ne _ _ ex, upd_ne _ _ ex]
        simp only [List.mem_cons, List.mem_append, List.mem_range] at hj
        rcases hj with e | lo | hi
        · exact absurd e ex
        · rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
          · rw [upd_ne _ _ (show (0 : Nat) ≠ 1 by decide), upd_self, one]
            simp only [tableA, show 0 < 0 + 2 by decide, ↓reduceIte, Nat.pow_zero, Nat.one_mul]
          · rw [upd_self, upd_ne _ _ (show mG ≠ 0 by decide), base]
            simp only [tableA, show 1 < 0 + 2 by decide, ↓reduceIte, Nat.pow_one]
        · have := L.above j hi
          rw [upd_ne _ _ (show j ≠ 1 by omega), upd_ne _ _ (show j ≠ 0 by omega)]
          simp only [tableA, show ¬ j < 0 + 2 by omega, ↓reduceIte]
  have steps : ∀ k ≤ 14, WP isa (seqs (pre ++ (List.range k).map tableStep)) s
      (TI g s0 A AW V live ls m b k) := by
    intro k hk
    induction k with
    | zero => simpa using init
    | succ k ih =>
      rw [List.range_succ, List.map_append, ← List.append_assoc,
        wp_seqs_append (by simp [pre]) (by simp)]
      exact WP.mono (ih (by omega)) fun t ht =>
        tableStep_ok ht L hG hB hI value bound inverse odd positive base (by omega)
  unfold VG.Impl.Rsa.X86.RecoverRt.table
  refine WP.mono (steps 14 (by decide)) fun t hu => ?_
  exact hu.mono (fun j hj => ⟨List.mem_cons_of_mem _ hj, by
    have : j ≠ mXm := by
      simp only [List.mem_append, List.mem_range] at hj
      rcases hj with lo | hi'
      · unfold mXm; omega
      · exact fun e => L.xm (e ▸ hi')
    rw [upd_ne _ _ this]⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)

/-- The window's table entry into `mXm`, by a scan of entries `0` to `k`. -/
theorem scan_ok (h : KS g s0 A live AW [wRc, wR] V ls s)
    (ht : ∀ j < 16, j ∈ live) (hw : sWin ∈ ls) (small : V sWin < 16)
    (hEq : sEq ∉ ls) :
    ∀ k, k < 16 → WP isa (VG.Impl.Rsa.X86.RecoverRt.scan k) s fun t =>
      KS g s0 (upd A mXm (if V sWin ≤ k then A (V sWin) else A 0)) (mXm :: live) AW [wRc, wR] V ls t
  | 0, _ => by
    refine WP.mono (h.copy_w (o := mXm) (a := 0) (by decide) (ht 0 (by decide)) (by decide) (by decide))
      fun t ⟨ht', _, _⟩ => ?_
    refine ht'.mono (fun j hj => ⟨hj, ?_⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
    simp only [upd]
    split
    · split
      · rename_i z; rw [show V sWin = 0 by omega]
      · rfl
    · rfl
  | k + 1, hk => by
    rw [VG.Impl.Rsa.X86.RecoverRt.scan]
    simp only [seqs]
    refine WP.seq (WP.mono (scan_ok h ht hw small hEq k (by omega)) fun u hu => ?_)
    refine WP.seq (WP.mono (hu.windowIs_ok (j := k + 1) hw small hk) fun v ⟨hv, _⟩ => ?_)
    refine WP.mono (hv.sel_w (o := mXm) (a := mXm) (b := k + 1) (sl := sEq) (by decide)
      (by simp) (by simp [ht (k + 1) hk]) (by simp)
      (by rw [upd_self]; split <;> omega) (.inr (by unfold mXm; omega)) (by decide)) fun t ⟨ht', _⟩ => ?_
    refine ht'.mono (fun j hj => ⟨by simp [hj], ?_⟩) (fun j hj => ⟨hj, rfl⟩)
      (fun d hd => ⟨by simp [hd], ?_⟩)
    · simp only [upd_self]
      by_cases e : j = mXm
      · subst e
        simp only [upd_self]
        by_cases w : V sWin = k + 1
        · simp only [w, ↓reduceIte, Nat.le_refl, show (1 : Nat) ≠ 0 by decide]
          rw [upd_ne _ _ (show k + 1 ≠ mXm by unfold mXm; omega)]
        · simp only [w, ↓reduceIte]
          by_cases le : V sWin ≤ k
          · simp only [le, show V sWin ≤ k + 1 by omega, ↓reduceIte]
          · simp only [le, show ¬ V sWin ≤ k + 1 by omega, ↓reduceIte]
      · simp only [upd_ne _ _ e]
    · have ne : d ≠ sEq := fun e => hEq (e ▸ hd)
      exact upd_ne _ _ ne

end
end VG.Proof.Rsa.X86.Recover
