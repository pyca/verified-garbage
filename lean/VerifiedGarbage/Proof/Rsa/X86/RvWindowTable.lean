module

public import VerifiedGarbage.Proof.Rsa.X86.RvWindowOps
public import VerifiedGarbage.Proof.Rsa.X86.RvMont
public import VerifiedGarbage.Proof.Mont.X86.WindowCopy
public import VerifiedGarbage.Proof.Rsa.X86.RvMontTracked
public import VerifiedGarbage.Proof.Rsa.X86.RvMontStage
public import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Rsa.X86.RvWrite

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
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live liveW : List Nat}
  {AW : Nat → Nat} {V : Nat → Nat} {ls : List Nat}

/-- What the table's construction leaves of the stage: arrays above the
accumulator, other than the Montgomery temporaries. -/
structure TableLive (live : List Nat) : Prop where
  above : ∀ j ∈ live, 20 ≤ j
  tmp : mTmp ∉ live
  xm : mXm ∉ live

theorem KS.copyOut_w {o a : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ho : o < nArr) (ha : a ∈ live) (hoa : o ≠ a) (hlW : ∀ j ∈ liveW, o / 2 ≠ j)
    (hesi : s.gpr .esi = s.gpr .edi + BitVec.ofNat 32 (arr g.w o)) :
    WP isa (VG.Impl.Mont.X86.Dynamic.copyOut g.w (arr g.w a)) s fun t =>
      KS g s0 (upd A o (A a)) (o :: live) AW liveW V ls t ∧
      t.gpr .esi = t.gpr .edi + BitVec.ofNat 32 (arr g.w o + 4 * g.w) ∧ Keeps opRegs s t := by
  have fa := h.ws.arr_fit (h.live_lt a ha)
  have fo := h.ws.arr_fit ho
  have wp := h.ws.wpos
  have sep := arr_disj (w := g.w) hoa
  simp only [S] at fa fo sep
  refine WP.mono (VG.Proof.Mont.X86.Dynamic.copyOut_ok h.ws.workspace (k := g.w) (src := arr g.w a)
    (dst := arr g.w o) wp (by omega) (by omega) (by omega) hesi) fun t ⟨Vt, O, E, K⟩ => ?_
  have k : Keep g.B g.w [o] [] s.mem t.mem :=
    Keep.of_arr (d := 0) (by simpa using O) (by unfold S; omega) (by simp)
  refine ⟨h.write_w k ho (by simp) (K.mono (by decide)) ?_ hlW (by simp), E, K.mono (by decide)⟩
  change val32 t.mem g.B (arr g.w o) g.w = _
  rw [Vt]
  exact h.arrs a ha

/-- The table's first `i + 2` entries, the last in `mXm` too. -/
def TI (g : Geo) (s0 : State) (A AW V : Nat → Nat) (live ls : List Nat) (m b i : Nat) (s : State) : Prop :=
  KS g s0 (upd (tableA A g.n m b (i + 2)) mXm (b ^ (i + 1) * 2 ^ (64 * g.n) % m))
    (mXm :: (List.range (i + 2) ++ live)) AW [wRc, wR] V ls s ∧
  s.gpr .esi = s.gpr .edi + BitVec.ofNat 32 (arr g.w (i + 2))

theorem tableStep_ok {m b i : Nat} (h : TI g s0 A AW V live ls m b i s) (L : TableLive live)
    (hG : mG ∈ live) (hB : mBase ∈ live)
    (hI : sInv ∈ ls) (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (odd : m % 2 = 1) (positive : 0 < m)
    (base : A mG = b * 2 ^ (64 * g.n) % m) (hi : i < 14) :
    WP isa (tableStep g.n) s fun t => TI g s0 A AW V live ls m b (i + 1) t ∧
      t.zf = some (decide (i + 3 = 16)) := by
  obtain ⟨h, hesi⟩ := h
  have aboveA (j : Nat) (hj : j ∈ live) (k : Nat) (hk : k ≤ 16) : tableA A g.n m b k j = A j := by
    have := L.above j hj
    simp only [tableA, show ¬ j < k by omega, ↓reduceIte]
  have notX (j : Nat) (hj : j ∈ live) : j ≠ mXm := fun e => L.xm (e ▸ hj)
  have notT (j : Nat) (hj : j ∈ live) : j ≠ mTmp := fun e => L.tmp (e ▸ hj)
  have wf := h.ws.arr_fit (show 16 < nArr by decide)
  have nw := h.ws.workspace.nowrap
  have sz := h.ws.workspace.size_lt
  simp only [S] at wf
  unfold tableStep
  simp only [seqs]
  -- The next power, in `mXm`.
  have mr := h.montReady (m := m) (by simp [hB]) hI
    (by rw [upd_ne _ _ (by decide), aboveA _ hB _ (by omega)]; exact value) bound inverse
  refine WP.seq (WP.mono (h.mmul mr (o := mXm) (a := mXm) (b := mG) (by decide) (by decide)
    (by decide) (by decide) (by simp) (by simp [hG])
    (by rw [upd_self]; exact Nat.mod_lt _ positive)
    (by rw [upd_ne _ _ (by decide), aboveA _ hG _ (by omega), base]; exact Nat.mod_lt _ positive)
    ?_ (by decide)) fun s₁ ⟨X, h₁, _, ⟨r₁, esi₁⟩, lt, v⟩ => ?_)
  · intro j hj
    simp only [List.mem_cons, List.mem_append, List.mem_range] at hj
    rcases hj with e | lo | hi
    · exact .inl e
    · right; unfold mTmp mAcc; omega
    · have := L.above j hi
      right; refine ⟨notT j hi, ?_, ?_⟩ <;> unfold mAcc <;> omega
  have power : X = b ^ (i + 2) * 2 ^ (64 * g.n) % m := by
    have p := VG.Proof.Dsa.mont_product (VG.Proof.Bignum.coprime_pow2 odd _)
      (a := b ^ (i + 1)) (b := b) (by rw [upd_self, Nat.mod_mod])
      (by rw [upd_ne _ _ (by decide), aboveA _ hG _ (by omega), base, Nat.mod_mod]) v
    rwa [Nat.mod_eq_of_lt lt, ← Nat.pow_succ] at p
  rw [upd_twice, power] at h₁
  -- Into the entry at `esi`.
  refine WP.seq (WP.mono (h₁.copyOut_w (o := i + 2) (a := mXm) (by unfold nArr; omega) (by simp)
    (by unfold mXm; omega) (by intro j hj; simp [wRc, wR] at hj; omega)
    (by rw [esi₁, r₁.1 _ (by decide)]; exact hesi)) fun s₂ ⟨h₂, esi₂, _⟩ => ?_)
  rw [upd_self] at h₂
  refine wp_addS rfl fun s₃ u₃ _ => ?_
  refine wp_movS rfl fun s₄ u₄ _ => ?_
  refine wp_addS rfl fun s₅ u₅ _ => ?_
  refine wp_cmpS rfl fun t ft zt => WP.block_nil ?_
  have ht := (((h₂.of_rest u₃.keeps (by decide) u₃.mem).of_rest u₄.keeps (by decide) u₄.mem).of_rest
    u₅.keeps (by decide) u₅.mem).of_rest (ft.keeps []) (by decide) ft.mem
  have next : arr g.w (i + 2) + 4 * g.w + 8 = arr g.w (i + 3) := by
    have := arr_succ g.w (i + 2); simp only [S] at this
    rw [show i + 2 + 1 = i + 3 from rfl] at this; omega
  have esi₅ : s₅.gpr .esi = s₂.gpr .edi + BitVec.ofNat 32 (arr g.w (i + 3)) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, esi₂, BitVec.add_assoc, ← next]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : BitVec 32).toNat = 8 from rfl]
    omega
  have edx₅ : s₅.gpr .edx = s₂.gpr .edi + BitVec.ofNat 32 (arr g.w 16) := by
    rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide)]
    rfl
  have edi₅ : s₅.gpr .edi = s₂.gpr .edi := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]
  have le3 : arr g.w (i + 3) ≤ arr g.w 16 := arr_mono (by omega)
  refine ⟨⟨ht.mono (fun j hj => ⟨?_, ?_⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩), ?_⟩, ?_⟩
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
  · rw [ft.gpr, esi₅, edi₅]
  · rw [zt, esi₅, edx₅, VG.Proof.Mont.X86.Dynamic.ptr_cmp _ (by omega) (by omega)]
    congr 2
    apply propext
    constructor
    · intro e
      by_contra ne
      rcases Nat.lt_or_gt_of_ne ne with lt' | gt'
      · have := arr_end (w := g.w) lt'; simp only [S] at this; omega
      · have := arr_end (w := g.w) gt'; simp only [S] at this; omega
    · intro e; rw [e]

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
  refine WP.seq (WP.mono (h2.copy_w (o := mXm) (a := mG) (by decide) (by simp [hG]) (by decide))
    fun s3 ⟨h3, _, _⟩ => ?_)
  refine WP.seq (wp_movS rfl fun s4 u4 _ => wp_addS rfl fun s5 u5 _ => WP.block_nil ?_)
  have h5 := (h3.of_rest u4.keeps (by decide) u4.mem).of_rest u5.keeps (by decide) u5.mem
  have init : TI g s0 A AW V live ls m b 0 s5 := by
    refine ⟨h5.mono (fun j hj => ⟨?_, ?_⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩), ?_⟩
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
    · rw [u5.gpr, u5.other _ (by decide), u4.gpr, u4.other _ (by decide)]
      rfl
  refine WP.mono (WP.loop (M := isa) (fun c t => ∃ i, c = 14 - i ∧ i < 14 ∧ TI g s0 A AW V live ls m b i t)
    ?_ 14 s5 ⟨0, rfl, by decide, init⟩) fun t ht => ht
  rintro c t ⟨i, rfl, hi, I⟩
  refine WP.mono (tableStep_ok I L hG hB hI value bound inverse odd positive base hi)
    fun u ⟨Iu, zu⟩ => ?_
  by_cases last : i + 1 = 14
  · refine .inl ⟨?_, ?_⟩
    · simp only [eval, zu, show i + 3 = 16 by omega, decide_true, Option.map_some, Bool.not_true]
    · obtain ⟨hu, _⟩ := Iu
      rw [show i + 1 + 2 = 16 by omega] at hu
      exact hu.mono (fun j hj => ⟨List.mem_cons_of_mem _ hj, by
        have : j ≠ mXm := by
          simp only [List.mem_append, List.mem_range] at hj
          rcases hj with lo | hi'
          · unfold mXm; omega
          · exact fun e => L.xm (e ▸ hi')
        rw [upd_ne _ _ this]⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  · refine .inr ⟨?_, 14 - (i + 1), by omega, i + 1, rfl, by omega, Iu⟩
    simp only [eval, zu, show i + 3 ≠ 16 by omega, decide_false, Option.map_some, Bool.not_false]

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
