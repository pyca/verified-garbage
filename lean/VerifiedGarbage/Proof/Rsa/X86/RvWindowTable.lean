module

public import VerifiedGarbage.Proof.Rsa.X86.RvWindowOps
public import VerifiedGarbage.Proof.Rsa.X86.RvMontTracked
public import VerifiedGarbage.Proof.Rsa.X86.RvMontStage
public import VerifiedGarbage.Proof.Dsa.Arithmetic

/-! # The candidate's window table, and the scan that reads its entries

The table holds the candidate's powers `0` to `15` in Montgomery form, in
arrays `0` to `15`, below the Montgomery accumulator.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

/-- The arrays with the table's first `k` entries. -/
def tableA (A : Nat → Nat) (n m b k : Nat) : Nat → Nat :=
  fun j => if j < k then b ^ j * 2 ^ (64 * n) % m else A j

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {V : Nat → Nat} {ls : List Nat}

/-- What the table's construction leaves of the stage: arrays above the
accumulator, other than the Montgomery temporaries. -/
structure TableLive (live : List Nat) : Prop where
  above : ∀ j ∈ live, 20 ≤ j
  tmp : mTmp ∉ live

theorem powers_ok {m b : Nat} (L : TableLive live) (hG : mG ∈ live) (hB : mBase ∈ live)
    (hI : sInv ∈ ls) (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (odd : m % 2 = 1) (positive : 0 < m)
    (base : A mG = b * 2 ^ (64 * g.n) % m) :
    ∀ k, k ≤ 14 →
    KS g s0 (tableA A g.n m b 2) (List.range 2 ++ live) AW [wRc, wR] V ls s →
    WP isa (powers g.n k) s fun t =>
      KS g s0 (tableA A g.n m b (k + 2)) (List.range (k + 2) ++ live) AW [wRc, wR] V ls t
  | 0, _, h => WP.block_nil h
  | k + 1, hk, h => by
    rw [powers]
    refine WP.seq (WP.mono (powers_ok L hG hB hI value bound inverse odd positive base k (by omega) h)
      fun u hu => ?_)
    have aboveA (j : Nat) (hj : j ∈ live) : tableA A g.n m b (k + 2) j = A j := by
      have := L.above j hj
      simp only [tableA, show ¬ j < k + 2 by omega, ↓reduceIte]
    have mr := hu.montReady (m := m) (by simp [hB]) hI
      (by rw [aboveA _ hB]; exact value) bound inverse
    refine WP.mono (hu.mmul mr (o := k + 2) (a := k + 1) (b := mG)
      ⟨.inr (by omega), by unfold nArr; omega, by unfold mTmp; omega⟩
      ⟨.inr (by omega), by unfold nArr; omega, by unfold mTmp; omega⟩
      (by decide) (by unfold mBase; omega)
      (by simp [List.mem_range]) (by simp [hG])
      (by simp only [tableA, show k + 1 < k + 2 by omega, ↓reduceIte]; exact Nat.mod_lt _ positive)
      (by rw [aboveA _ hG, base]; exact Nat.mod_lt _ positive)
      ?_ (by intro j hj i hi; simp [montWrites, mTmp, mAcc, wRc, wR] at hj hi ⊢; omega))
      fun t ⟨X, ht, _, _, lt, v⟩ => ?_
    · intro j hj
      simp only [List.mem_append, List.mem_range] at hj
      rcases hj with lo | hi
      · right; unfold mTmp mAcc; omega
      · have := L.above j hi
        by_cases e : j = mTmp
        · exact absurd (e ▸ hi) L.tmp
        · right; unfold mAcc; refine ⟨e, ?_, ?_⟩ <;> omega
    have power : X = b ^ (k + 2) * 2 ^ (64 * g.n) % m := by
      have p := VG.Proof.Dsa.mont_product (VG.Proof.Bignum.coprime_pow2 odd _)
        (a := b ^ (k + 1)) (b := b)
        (by simp only [tableA, show k + 1 < k + 2 by omega, ↓reduceIte, Nat.mod_mod])
        (by rw [aboveA _ hG, base, Nat.mod_mod]) v
      rwa [Nat.mod_eq_of_lt lt, ← Nat.pow_succ] at p
    refine ht.mono (fun j hj => ⟨?_, ?_⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
    · rcases List.mem_append.mp hj with lo | hi
      · rw [List.mem_range] at lo
        by_cases e : j = k + 2
        · exact e ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_range.mpr (by omega)))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ hi)
    · by_cases e : j = k + 2
      · subst e
        rw [upd_self, power]
        simp only [tableA, show k + 2 < k + 1 + 2 by omega, ↓reduceIte]
      · rw [upd_ne _ _ e]
        simp only [tableA]
        by_cases lt : j < k + 2
        · simp only [lt, show j < k + 1 + 2 by omega, ↓reduceIte]
        · simp only [lt, show ¬ j < k + 1 + 2 by omega, ↓reduceIte]

theorem table_ok {m b : Nat} (h : KS g s0 A live AW [wRc, wR] V ls s) (L : TableLive live)
    (hO : aO ∈ live) (hG : mG ∈ live) (hB : mBase ∈ live)
    (hI : sInv ∈ ls) (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (odd : m % 2 = 1) (positive : 0 < m)
    (one : A aO = 2 ^ (64 * g.n) % m) (base : A mG = b * 2 ^ (64 * g.n) % m) :
    WP isa (table g.n) s fun t =>
      KS g s0 (tableA A g.n m b 16) (List.range 16 ++ live) AW [wRc, wR] V ls t := by
  unfold table
  simp only [seqs]
  refine WP.seq (WP.mono (h.copy_w (o := 0) (a := aO) (by decide) hO (by decide))
    fun s1 ⟨h1, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h1.copy_w (o := 1) (a := mG) (by decide) (by simp [hG]) (by decide))
    fun s2 ⟨h2, _, _⟩ => ?_)
  refine powers_ok L hG hB hI value bound inverse odd positive base 14 (by decide) ?_
  refine h2.mono (fun j hj => ⟨?_, ?_⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  · rcases List.mem_append.mp hj with lo | hi
    · rw [List.mem_range] at lo
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi)
  · rcases List.mem_append.mp hj with lo | hi
    · rw [List.mem_range] at lo
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · rw [upd_ne _ _ (show (0 : Nat) ≠ 1 by decide), upd_self, one]
        simp only [tableA, show 0 < 2 by decide, ↓reduceIte, Nat.pow_zero, Nat.one_mul]
      · rw [upd_self, upd_ne _ _ (show mG ≠ 0 by decide), base]
        simp only [tableA, show 1 < 2 by decide, ↓reduceIte, Nat.pow_one]
    · have := L.above j hi
      rw [upd_ne _ _ (show j ≠ 1 by omega), upd_ne _ _ (show j ≠ 0 by omega)]
      simp only [tableA, show ¬ j < 2 by omega, ↓reduceIte]

/-- The window's table entry into `mXm`, by a scan of entries `0` to `k`. -/
theorem scan_ok (h : KS g s0 A live AW [wRc, wR] V ls s)
    (ht : ∀ j < 16, j ∈ live) (hw : sWin ∈ ls) (small : V sWin < 16)
    (hEq : sEq ∉ ls) :
    ∀ k, k < 16 → WP isa (scan g.n k) s fun t =>
      KS g s0 (upd A mXm (if V sWin ≤ k then A (V sWin) else A 0)) (mXm :: live) AW [wRc, wR] V ls t
  | 0, _ => by
    refine WP.mono (h.copy_w (o := mXm) (a := 0) (by decide) (ht 0 (by decide)) (by decide))
      fun t ⟨ht', _, _⟩ => ?_
    refine ht'.mono (fun j hj => ⟨hj, ?_⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
    simp only [upd]
    split
    · split
      · rename_i z; rw [show V sWin = 0 by omega]
      · rfl
    · rfl
  | k + 1, hk => by
    rw [scan]
    simp only [seqs]
    refine WP.seq (WP.mono (scan_ok h ht hw small hEq k (by omega)) fun u hu => ?_)
    refine WP.seq (WP.mono (hu.windowIs_ok (j := k + 1) hw small hk) fun v ⟨hv, _⟩ => ?_)
    refine WP.mono (hv.sel_w (o := mXm) (a := mXm) (b := k + 1) (sl := sEq) (by decide)
      (by simp) (by simp [ht (k + 1) hk]) (by simp)
      (by rw [upd_self]; split <;> omega) (by decide)) fun t ⟨ht', _⟩ => ?_
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
