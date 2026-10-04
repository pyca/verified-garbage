import VerifiedGarbage.Proof.Mont.AArch64.Blocks

/-!
# Montgomery arithmetic on AArch64: a round of the multiplication

The accumulator's window of registers (`wins n i`), how it rotates from one
round to the next, the multiplicands' values (`rwVal_bWords`, `rwVal_mWords`,
`rwVal_fWords`), and a round (`round_ok`): the accumulator `T < 2m` becomes
`(T + a_i B + u m) / 2⁶⁴ < 2m` for some `u`: for a general modulus, the low
word of `T + a_i B + u m` is zero; for a friendly one, `u = t₀` and the
words above `t₀` become `⌊(T + a_i B) / 2⁶⁴⌋ + t₀ m'`.
-/

namespace VG.Proof.Mont.AArch64

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-! ## The window -/

theorem win_succ (n i j : Nat) : win n (i + 1) j = win n i (j + 1) := by
  simp only [win, Nat.add_assoc, Nat.add_comm 1 j]

theorem win_wrap (n i : Nat) : win n i (n + 2) = win n i 0 := by
  simp only [win, Nat.add_zero, Nat.add_mod_right]

theorem win_mod (n i j : Nat) : win n i j = win n (i % (n + 2)) j := by
  simp only [win, Nat.add_mod i j, Nat.mod_mod, Nat.add_mod (i % (n + 2)) j]

theorem wins_mod (n i : Nat) : wins n i = wins n (i % (n + 2)) := by
  simp only [wins]; exact List.map_congr_left fun j _ => win_mod n i j

theorem wins_length (n i : Nat) : (wins n i).length = n + 2 := by simp [wins]

theorem wins_cons (n i : Nat) :
    wins n i = win n i 0 :: (List.range (n + 1)).map (fun j => win n i (j + 1)) := by
  simp only [wins, List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

theorem wins_succ (n i : Nat) :
    wins n (i + 1) = (List.range (n + 1)).map (fun j => win n i (j + 1)) ++ [win n i 0] := by
  rw [wins, show win n (i + 1) = fun j => win n i (j + 1) from funext (win_succ n i)]
  simp only [List.range_succ (n := n + 1), List.map_append, List.map_cons, List.map_nil, win_wrap]

theorem wins_split (n i : Nat) :
    wins n i = (List.range n).map (win n i) ++ [win n i n, win n i (n + 1)] := by
  simp only [wins, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    List.append_assoc, List.singleton_append]

theorem fresh_wins_lt : ∀ n < 7, ∀ i < n + 2, Fresh (wins n i) := by
  unfold Fresh; decide

theorem fresh_wins {n : Nat} (hn : n < 7) (i : Nat) : Fresh (wins n i) := by
  rw [wins_mod]; exact fresh_wins_lt n hn _ (Nat.mod_lt _ (by omega))

/-! ## The multiplicands -/

/-- The registers `bRegs` hold their words of `[b]` (`n` words). -/
def BRegs (s : State) (base : Addr) (b n : Nat) : Prop :=
  ∀ j < n, ∀ r, bRegs[j]? = some r → s.gpr r = word s.mem base (b + 8 * j)

theorem BRegs.keep {s s' : State} {base : Addr} {b n : Nat} (h : BRegs s base b n)
    (hm : s'.mem = s.mem) (hr : ∀ r ∈ bRegs, s'.gpr r = s.gpr r) : BRegs s' base b n :=
  fun j hj r hjr => by rw [hr r (List.mem_of_getElem? hjr), hm]; exact h j hj r hjr

/-- `x6` holds the constant the reduction uses: `minv`, or the first general
word of `m'`. -/
def ConstOk (M : Mod) (s : State) : Prop :=
  match M.red with
  | .general => s.gpr .x6 = M.minv
  | .friendly ws => ∀ v, firstGen ws = some v → s.gpr .x6 = BitVec.ofNat 64 v

theorem ConstOk.keep {M : Mod} {s s' : State} (h : ConstOk M s) (h6 : s'.gpr .x6 = s.gpr .x6) :
    ConstOk M s' := by
  unfold ConstOk at h ⊢
  cases hr : M.red with
  | general => rw [hr] at h; exact h6.trans h
  | friendly ws => rw [hr] at h; exact fun v hv => h6.trans (h v hv)

theorem bWords_length (b : Nat) : ∀ j k, (bWords b j k).length = k
  | _, 0 => rfl
  | j, k + 1 => by simp only [bWords, List.length_cons, bWords_length b (j + 1) k]

theorem mWords_length (mo : Nat) : ∀ j k, (mWords mo j k).length = k
  | _, 0 => rfl
  | j, k + 1 => by simp only [mWords, List.length_cons, mWords_length mo (j + 1) k]

theorem mem_bWords {b : Nat} : ∀ {j k : Nat} {w : RWord}, w ∈ bWords b j k →
    ∃ j', j ≤ j' ∧ j' < j + k ∧ w = .gen (bSrc b j')
  | _, 0, _, h => absurd h List.not_mem_nil
  | j, k + 1, w, h => by
    simp only [bWords, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨j, Nat.le_refl _, by omega, rfl⟩
    · obtain ⟨j', h1, h2, h3⟩ := mem_bWords h
      exact ⟨j', by omega, by omega, h3⟩

theorem mem_mWords {mo : Nat} : ∀ {j k : Nat} {w : RWord}, w ∈ mWords mo j k →
    ∃ j', j ≤ j' ∧ j' < j + k ∧ w = .gen (.mem (mo + 8 * j'))
  | _, 0, _, h => absurd h List.not_mem_nil
  | j, k + 1, w, h => by
    simp only [mWords, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨j, Nat.le_refl _, by omega, rfl⟩
    · obtain ⟨j', h1, h2, h3⟩ := mem_mWords h
      exact ⟨j', by omega, by omega, h3⟩

theorem bSrc_val {s : State} {base : Addr} {b n : Nat} (hB : BRegs s base b n) {j : Nat}
    (hj : j < n) : (bSrc b j).val s base = (word s.mem base (b + 8 * j)).toNat := by
  unfold bSrc
  cases h : bRegs[j]? with
  | none => rfl
  | some r => simp only [Src.val, hB j hj r h]

theorem rwVal_bWords {s : State} {base : Addr} {b n : Nat} (hB : BRegs s base b n) :
    ∀ j k, j + k ≤ n → rwVal s base (bWords b j k) = wordsVal s.mem base (b + 8 * j) k
  | _, 0, _ => rfl
  | j, k + 1, h => by
    simp only [bWords, rwVal, wordsVal, RWord.val, bSrc_val hB (show j < n by omega),
      rwVal_bWords hB (j + 1) k (by omega), show b + 8 * (j + 1) = b + 8 * j + 8 by omega]

theorem rwVal_mWords (s : State) (base : Addr) (mo : Nat) :
    ∀ j k, rwVal s base (mWords mo j k) = wordsVal s.mem base (mo + 8 * j) k
  | _, 0 => rfl
  | j, k + 1 => by
    simp only [mWords, rwVal, wordsVal, RWord.val, Src.val, rwVal_mWords s base mo (j + 1) k,
      show mo + 8 * (j + 1) = mo + 8 * j + 8 by omega]

theorem fWord_val {s : State} {base : Addr} {g : Option Nat}
    (h6 : ∀ v, g = some v → s.gpr .x6 = BitVec.ofNat 64 v) {w : MWord} (hw : w.ok = true) :
    (fWord g w).val s base = w.val := by
  cases w with
  | zero => rfl
  | one => rfl
  | pow2 k => rfl
  | gen v =>
    have hv : v < 2 ^ 64 := by simpa [MWord.ok] using hw
    show RWord.val s base (if g = some v then .gen (.reg .x6) else .gen (.imm (BitVec.ofNat 64 v))) = v
    split
    · rename_i hg
      simp only [RWord.val, Src.val, h6 v hg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
    · simp only [RWord.val, Src.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

theorem rwVal_fWords {s : State} {base : Addr} {g : Option Nat}
    (h6 : ∀ v, g = some v → s.gpr .x6 = BitVec.ofNat 64 v) :
    ∀ ws : List MWord, ws.all MWord.ok = true → rwVal s base (ws.map (fWord g)) = mwVal ws
  | [], _ => rfl
  | w :: ws, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, rwVal, mwVal, rwVal_fWords h6 ws h.2, fWord_val h6 h.1]

theorem fWord_ok {size : Nat} {g : Option Nat} {w : MWord} (hw : w.ok = true) :
    (fWord g w).Ok size ∧ ∀ r ∈ (fWord g w).reads, r = .x6 := by
  cases w with
  | zero => exact ⟨trivial, fun _ h => by simp [fWord, RWord.reads] at h⟩
  | one => exact ⟨trivial, fun _ h => by simp [fWord, RWord.reads] at h⟩
  | pow2 k =>
    simp only [MWord.ok, Bool.and_eq_true, decide_eq_true_eq] at hw
    exact ⟨hw, fun _ h => by simp [fWord, RWord.reads] at h⟩
  | gen v =>
    show RWord.Ok size (if g = some v then .gen (.reg .x6) else .gen (.imm (BitVec.ofNat 64 v))) ∧
      ∀ r ∈ (if g = some v then RWord.gen (.reg .x6) else .gen (.imm (BitVec.ofNat 64 v))).reads,
        r = .x6
    split
    · exact ⟨⟨by decide, by decide⟩, fun r h => by simpa [RWord.reads, Src.reads] using h.symm⟩
    · exact ⟨trivial, fun _ h => by simp [RWord.reads, Src.reads] at h⟩

/-! ## A round -/

theorem wins_tail (n i : Nat) :
    (wins n i).tail = (List.range (n + 1)).map (fun j => win n i (j + 1)) := by
  rw [wins_cons]; rfl

/-- The window's registers: distinct, and none of `x0`–`x7`, `x16`, `x17`. -/
theorem wins_regs {n : Nat} (hn : n < 7) (i : Nat) :
    ∀ r ∈ wins n i, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x5 ∧ r ≠ .x6 ∧
      r ≠ .x7 ∧ r ≠ .x16 ∧ r ≠ .x17 := by
  intro r hr
  have := (fresh_wins hn i).2 r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
  exact this

theorem bRegs_regs : ∀ r ∈ bRegs, r = .x4 ∨ r = .x5 ∨ r = .x16 ∨ r = .x17 := by decide

theorem rowOkA {size : Nat} {n b : Nat} (hn : n < 7) (hb : b + 8 * n ≤ size) (hb8 : b % 8 = 0)
    (i : Nat) : RowOk size .x1 (wins n i) (bWords b 0 n) where
  nodup := (fresh_wins hn i).1
  regs t ht := by have := wins_regs hn i t ht; exact ⟨this.1, this.2.2.1, this.2.2.2.1,
    this.2.2.2.2.2.2.2.1, this.2.1⟩
  ok w hw := by
    obtain ⟨j, -, hj, rfl⟩ := mem_bWords hw
    unfold bSrc
    cases h : bRegs[j]? with
    | none => exact ⟨by omega, by omega⟩
    | some r =>
      rcases bRegs_regs r (List.mem_of_getElem? h) with rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, by decide⟩
  reads w hw r hr := by
    obtain ⟨j, -, hj, rfl⟩ := mem_bWords hw
    unfold bSrc at hr
    cases h : bRegs[j]? with
    | none => rw [h] at hr; simp [RWord.reads, Src.reads] at hr
    | some q =>
      rw [h] at hr
      simp only [RWord.reads, Src.reads, Option.mem_def, Option.some.injEq] at hr
      subst hr
      refine ⟨fun hm => ?_, ?_⟩
      · have := wins_regs hn i q hm
        rcases bRegs_regs q (List.mem_of_getElem? h) with rfl | rfl | rfl | rfl <;> simp at this
      · rcases bRegs_regs q (List.mem_of_getElem? h) with rfl | rfl | rfl | rfl <;> decide
  x2 := by decide
  x3 := by decide

theorem rowOkM {size : Nat} {n mo : Nat} (hn : n < 7) (hmo : mo + 8 * n ≤ size) (hmo8 : mo % 8 = 0)
    (i : Nat) : RowOk size .x1 (wins n i) (mWords mo 0 n) where
  nodup := (fresh_wins hn i).1
  regs t ht := by have := wins_regs hn i t ht; exact ⟨this.1, this.2.2.1, this.2.2.2.1,
    this.2.2.2.2.2.2.2.1, this.2.1⟩
  ok w hw := by
    obtain ⟨j, -, hj, rfl⟩ := mem_mWords hw
    exact ⟨by omega, by omega⟩
  reads w hw r hr := by
    obtain ⟨j, -, hj, rfl⟩ := mem_mWords hw
    simp [RWord.reads, Src.reads] at hr
  x2 := by decide
  x3 := by decide

theorem rowOkF {size : Nat} {n : Nat} (hn : n < 7) (i : Nat) {ws : List MWord}
    (hws : ws.all MWord.ok = true) (g : Option Nat) :
    RowOk size (win n i 0) (wins n i).tail (ws.map (fWord g)) where
  nodup := (fresh_wins hn i).1.tail
  regs t ht := by
    have hm : t ∈ wins n i := List.mem_of_mem_tail ht
    have := wins_regs hn i t hm
    refine ⟨this.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.2.2.2.1, fun h => ?_⟩
    have hnd := (fresh_wins hn i).1
    rw [wins_cons] at hnd ht
    exact (List.nodup_cons.mp hnd).1 (h ▸ ht)
  ok w hw := by
    obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
    exact (fWord_ok (List.all_eq_true.mp hws w' hw')).1
  reads w hw r hr := by
    obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
    have := (fWord_ok (size := size) (g := g) (List.all_eq_true.mp hws w' hw')).2 r hr
    subst this
    exact ⟨fun hm => (wins_regs hn i _ (List.mem_of_mem_tail hm)).2.2.2.2.2.2.1 rfl, by decide,
      by decide⟩
  x2 := (wins_regs hn i _ (by rw [wins_cons]; exact List.mem_cons_self ..)).2.2.1
  x3 := (wins_regs hn i _ (by rw [wins_cons]; exact List.mem_cons_self ..)).2.2.2.1

/-- `x1 = t₀ x6 mod 2⁶⁴`. -/
theorem mulU_ok (s : State) (t0 : Reg) :
    WP isa (.block [.mul .x .x1 t0 .x6]) s fun s' =>
      (s'.gpr .x1).toNat = (s.gpr t0).toNat * (s.gpr .x6).toNat % 2 ^ 64 ∧ Keeps [.x1] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [BitVec.toNat_mul], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  exact RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr)

/-- `x1 = a_i` and `T += a_i B`. -/
theorem rowA_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n : Nat}
    (hn : n < 7) {a b i m : Nat} (ha : a + 8 * i + 8 ≤ size) (hb : b + 8 * n ≤ size)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hz : s.gpr .x7 = 0) (hBR : BRegs s base b n)
    (hm : m < 2 ^ (64 * n)) (hB : wordsVal s.mem base b n < m) (hT : regsVal s (wins n i) < 2 * m) :
    WP isa (.block (([ld .x1 (a + 8 * i)] : List Instr) ++ row .x1 (wins n i) (bWords b 0 n))) s
      fun s' => regsVal s' (wins n i) = regsVal s (wins n i) +
          (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b n ∧
        Keeps (.x1 :: .x2 :: .x3 :: wins n i) s s' := by
  have hw := wins_regs hn i
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs ha (by omega) .x1) fun s₁ ⟨c₁, k₁, _⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr .x7 (by decide), hz]
  have hT₁ : regsVal s₁ (wins n i) = regsVal s (wins n i) := regsVal_congr fun q hq =>
    k₁.gpr q (by simp [(hw q hq).2.1])
  have hBR₁ : BRegs s₁ base b n := hBR.keep k₁.mem fun r hr => k₁.gpr r (by
    rcases bRegs_regs r hr with rfl | rfl | rfl | rfl <;> decide)
  have hRB : rwVal s₁ base (bWords b 0 n) = wordsVal s.mem base b n := by
    rw [rwVal_bWords hBR₁ 0 n (by omega), k₁.mem]; rfl
  have hA := (word s.mem base (a + 8 * i)).isLt
  have hAB : (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b n ≤ (2 ^ 64 - 1) * m :=
    Nat.mul_le_mul (by omega) (by omega)
  have hlen : (wins n i).length = n + 2 := wins_length n i
  have hP : 2 ^ (64 * (n + 2)) = 2 ^ (64 * n) * 2 ^ 64 * 2 ^ 64 := by
    rw [show 64 * (n + 2) = 64 * n + 64 + 64 by omega, Nat.pow_add, Nat.pow_add]
  have hmP : (2 ^ 64 - 1) * m ≤ 2 ^ (64 * n) * 2 ^ 64 := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) (by omega)
  refine WP.mono (row_ok hs₁ hz₁ (rowOkA hn hb hb8 i) (by rw [bWords_length, hlen]; omega) (by
      rw [hT₁, c₁, hRB, hlen, hP]; omega)) fun s₂ ⟨e₂, k₂⟩ => ?_
  refine ⟨by rw [e₂, hT₁, c₁, hRB], (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩

/-- Round `i` of the multiplication, with `x7 = 0`, `[b]`'s words in
`bRegs` and the reduction's constant in `x6`: `2⁶⁴ T' = T + a_i B + u m`,
and `T' < 2m` if `T < 2m`. -/
theorem round_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    (hn : M.n < 7) {a b i m : Nat} (ha : a + 8 * i + 8 ≤ size) (hb : b + 8 * M.n ≤ size)
    (hmo : M.mo + 8 * M.n ≤ size) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hmo8 : M.mo % 8 = 0)
    (hz : s.gpr .x7 = 0) (hm : wordsVal s.mem base M.mo M.n = m)
    (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) (hred : M.red.ok M.n m = true)
    (hBR : BRegs s base b M.n) (h6 : ConstOk M s) (hB : wordsVal s.mem base b M.n < m)
    (hT : regsVal s (wins M.n i) < 2 * m) :
    WP isa (.block (round M a b i)) s fun s' =>
      (∃ u, 2 ^ 64 * regsVal s' (wins M.n (i + 1)) = regsVal s (wins M.n i) +
        (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n + u * m) ∧
      regsVal s' (wins M.n (i + 1)) < 2 * m ∧
      Keeps (.x1 :: .x2 :: .x3 :: wins M.n i) s s' := by
  have hw := wins_regs hn i
  have n0 : Reg.x0 ∉ wins M.n i := fun h => (hw _ h).1 rfl
  have n6 : Reg.x6 ∉ wins M.n i := fun h => (hw _ h).2.2.2.2.2.2.1 rfl
  have n7 : Reg.x7 ∉ wins M.n i := fun h => (hw _ h).2.2.2.2.2.2.2.1 rfl
  have hm' : m < 2 ^ (64 * M.n) := hm ▸ wordsVal_lt _ _ _ _
  have hcons := wins_cons M.n i
  have ht0 : win M.n i 0 ∈ wins M.n i := by rw [hcons]; exact List.mem_cons_self ..
  have hlen : (wins M.n i).length = M.n + 2 := wins_length M.n i
  have hP : 2 ^ (64 * (M.n + 2)) = 2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64 := by
    rw [show 64 * (M.n + 2) = 64 * M.n + 64 + 64 by omega, Nat.pow_add, Nat.pow_add]
  have hmP : (2 ^ 64 - 1) * m ≤ 2 ^ (64 * M.n) * 2 ^ 64 := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) (by omega)
  have hAB : (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n ≤ (2 ^ 64 - 1) * m :=
    Nat.mul_le_mul (by have := (word s.mem base (a + 8 * i)).isLt; omega) (by omega)
  -- The window after the round, from its value `V` with a zero low word.
  have hrot : ∀ t : State, (t.gpr (win M.n i 0)).toNat = 0 →
      2 ^ 64 * regsVal t (wins M.n (i + 1)) = regsVal t (wins M.n i) := by
    intro t h0
    rw [wins_succ, regsVal_append, hcons, regsVal]
    simp only [regsVal, h0, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  cases hr : M.red with
  | general =>
    have hcode : round M a b i = (([ld .x1 (a + 8 * i)] : List Instr) ++
        row .x1 (wins M.n i) (bWords b 0 M.n)) ++
        (([.mul .x .x1 (win M.n i 0) .x6] : List Instr) ++ row .x1 (wins M.n i) (mWords M.mo 0 M.n)) := by
      simp only [round, hr, List.cons_append, List.nil_append]
    have h6' : s.gpr .x6 = M.minv := by unfold ConstOk at h6; rw [hr] at h6; exact h6
    rw [hcode, WP.block_append_iff]
    refine WP.mono (rowA_ok hs hn ha hb ha8 hb8 hz hBR hm' hB hT) fun s₂ ⟨e₂, k₂⟩ => ?_
    have hs₂ := hs.of_keeps k₂ (by simp [n0])
    have hz₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (by simp [n7]), hz]
    have h6₂ : s₂.gpr .x6 = M.minv := by
      rw [k₂.gpr _ (by simp [n6]), h6']
    rw [WP.block_append_iff]
    refine WP.mono (mulU_ok s₂ (win M.n i 0)) fun s₃ ⟨u₃, k₃⟩ => ?_
    have hs₃ := hs₂.of_keeps k₃ (by decide)
    have hz₃ : s₃.gpr .x7 = 0 := by rw [k₃.gpr .x7 (by decide), hz₂]
    have hT₃ : regsVal s₃ (wins M.n i) = regsVal s₂ (wins M.n i) := regsVal_congr fun q hq =>
      k₃.gpr q (by simp [(hw q hq).2.1])
    have hmem₃ : s₃.mem = s.mem := by rw [k₃.mem, k₂.mem]
    have hu := (s₃.gpr .x1).isLt
    have hum : (s₃.gpr .x1).toNat * m ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul (by omega) (Nat.le_refl _)
    have hRM : rwVal s₃ base (mWords M.mo 0 M.n) = m := by
      rw [rwVal_mWords, hmem₃, Nat.mul_zero, Nat.add_zero, hm]
    refine WP.mono (row_ok hs₃ hz₃ (rowOkM hn hmo hmo8 i) (by rw [mWords_length, hlen]; omega) (by
        rw [hT₃, e₂, hRM, hlen, hP]; omega)) fun s₄ ⟨e₄, k₄⟩ => ?_
    rw [hT₃, e₂, hRM] at e₄
    -- The low word is zero.
    have ht0₂ : (regsVal s₂ (wins M.n i)) % 2 ^ 64 = (s₂.gpr (win M.n i 0)).toNat := by
      rw [hcons, regsVal]; omega
    have h₄ : (regsVal s₄ (wins M.n i)) % 2 ^ 64 = (s₄.gpr (win M.n i 0)).toNat := by
      rw [hcons, regsVal]; omega
    have hlow : (s₄.gpr (win M.n i 0)).toNat = 0 := by
      have h := mont_low (s₂.gpr (win M.n i 0)).toNat M.minv.toNat m hinv
      rw [h6₂] at u₃
      rw [← u₃] at h
      rw [← h₄, e₄]
      omega
    refine ⟨⟨(s₃.gpr .x1).toNat, by rw [hrot s₄ hlow, e₄]⟩, ?_, ?_⟩
    · have : 2 ^ 64 * regsVal s₄ (wins M.n (i + 1)) < 2 ^ 64 * (2 * m) := by
        rw [hrot s₄ hlow, e₄]; omega
      exact Nat.lt_of_mul_lt_mul_left this
    · exact (k₂.trans (k₃.mono (by sub_regs))).trans (k₄.mono (by sub_regs))
  | friendly ws =>
    have hcode : round M a b i = (([ld .x1 (a + 8 * i)] : List Instr) ++
        row .x1 (wins M.n i) (bWords b 0 M.n)) ++
        (row (win M.n i 0) (wins M.n i).tail (ws.map (fWord (firstGen ws))) ++
          ([.movz .x (win M.n i 0) 0 0] : List Instr)) := by
      simp only [round, hr, List.append_assoc]
    have hok := hred
    rw [hr] at hok
    simp only [Red.ok, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨hwl, hm1⟩, hmv⟩, hwok⟩ := hok
    have h6' : ∀ v, firstGen ws = some v → s.gpr .x6 = BitVec.ofNat 64 v := by
      unfold ConstOk at h6; rw [hr] at h6; exact h6
    -- `2⁶⁴ m' = m + 1`.
    have hm2 : 2 ^ 64 * mwVal ws = m + 1 := by
      rw [hmv]
      have := Nat.div_add_mod (m + 1) (2 ^ 64)
      have : (m + 1) % 2 ^ 64 = 0 := by omega
      omega
    rw [hcode, WP.block_append_iff]
    refine WP.mono (rowA_ok hs hn ha hb ha8 hb8 hz hBR hm' hB hT) fun s₂ ⟨e₂, k₂⟩ => ?_
    have hs₂ := hs.of_keeps k₂ (by simp [n0])
    have hz₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (by simp [n7]), hz]
    have h6₂ : ∀ v, firstGen ws = some v → s₂.gpr .x6 = BitVec.ofNat 64 v := fun v hv => by
      rw [k₂.gpr _ (by simp [n6]), h6' v hv]
    have hRF : rwVal s₂ base (ws.map (fWord (firstGen ws))) = mwVal ws := rwVal_fWords h6₂ ws hwok
    -- The window as its low word and the rest.
    have hsplit : ∀ t : State, regsVal t (wins M.n i) =
        (t.gpr (win M.n i 0)).toNat + 2 ^ 64 * regsVal t (wins M.n i).tail := by
      intro t; rw [hcons]; rfl
    have htl : (wins M.n i).tail.length = M.n + 1 := by rw [wins_tail]; simp
    have hPt : 2 ^ (64 * (M.n + 1)) = 2 ^ (64 * M.n) * 2 ^ 64 := by
      rw [show 64 * (M.n + 1) = 64 * M.n + 64 by omega, Nat.pow_add]
    have hS := hsplit s₂
    have ht0v := (s₂.gpr (win M.n i 0)).isLt
    have htm : (s₂.gpr (win M.n i 0)).toNat * m ≤ (2 ^ 64 - 1) * m :=
      Nat.mul_le_mul (by omega) (Nat.le_refl _)
    -- `2⁶⁴ (R + t₀ m') = S + t₀ m`, for the window's value `S = t₀ + 2⁶⁴ R`.
    have hkey : 2 ^ 64 * (regsVal s₂ (wins M.n i).tail + (s₂.gpr (win M.n i 0)).toNat * mwVal ws) =
        regsVal s₂ (wins M.n i) + (s₂.gpr (win M.n i 0)).toNat * m := by
      rw [Nat.mul_add, Nat.mul_left_comm, hm2, Nat.mul_add, Nat.mul_one, hS]; omega
    rw [WP.block_append_iff]
    refine WP.mono (row_ok hs₂ hz₂ (rowOkF hn i hwok (firstGen ws)) (by
        rw [List.length_map, hwl, htl]; omega) (by
        rw [hRF, htl, hPt]
        have : 2 ^ 64 * (regsVal s₂ (wins M.n i).tail + (s₂.gpr (win M.n i 0)).toNat * mwVal ws) <
            2 ^ 64 * (2 ^ (64 * M.n) * 2 ^ 64) := by
          rw [hkey, e₂]; omega
        exact Nat.lt_of_mul_lt_mul_left this)) fun s₃ ⟨e₃, k₃⟩ => ?_
    rw [hRF] at e₃
    refine WP.mono (movz0_ok s₃ (win M.n i 0)) fun s₄ ⟨z₄, k₄⟩ => ?_
    have htl₄ : regsVal s₄ (wins M.n i).tail = regsVal s₃ (wins M.n i).tail := regsVal_congr
      fun q hq => k₄.gpr q (by
        have hnd := (fresh_wins hn i).1
        rw [hcons] at hnd
        simp only [List.mem_singleton]
        intro h; subst h
        exact (List.nodup_cons.mp hnd).1 (by rw [← wins_tail]; exact hq))
    have hval : 2 ^ 64 * regsVal s₄ (wins M.n (i + 1)) = regsVal s₂ (wins M.n i) +
        (s₂.gpr (win M.n i 0)).toNat * m := by
      rw [wins_succ, regsVal_append, ← wins_tail, htl, htl₄, e₃]
      simp only [regsVal, z₄, Nat.mul_zero, Nat.add_zero]
      exact hkey
    refine ⟨⟨(s₂.gpr (win M.n i 0)).toNat, by rw [hval, e₂]⟩, ?_, ?_⟩
    · have : 2 ^ 64 * regsVal s₄ (wins M.n (i + 1)) < 2 ^ 64 * (2 * m) := by
        rw [hval, e₂]; omega
      exact Nat.lt_of_mul_lt_mul_left this
    · refine (k₂.trans (k₃.mono ?_)).trans (k₄.mono ?_)
      · intro q hq
        simp only [List.mem_cons] at hq ⊢
        rcases hq with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (List.mem_of_mem_tail h)))
      · intro q hq
        simp only [List.mem_singleton] at hq
        subst hq
        simp only [List.mem_cons]
        exact Or.inr (Or.inr (Or.inr ht0))

end VG.Proof.Mont.AArch64
