import VerifiedGarbage.Proof.Mont.AArch64.Blocks

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.AArch64.RowInit`. -/
section

/-!
# Montgomery arithmetic on AArch64: the first row

Into a cleared accumulator, the first row of products needs no chain for its
low words: `rowInit x ts bs` multiplies straight into `ts` (`mulsLo_ok`), and
then adds the high words one word up in a chain (`chainSkip_ok`). The low and
high words add up to `x B` (`lo_hi_sum`), which fits in `ts` (`rowInit_ok`).
-/

namespace VG.Proof.Mont.AArch64

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- `Σ_j v_j 2^(64 j)`. -/
def numVal : List Nat → Nat
  | [] => 0
  | v :: vs => v + 2 ^ 64 * VG.Proof.Mont.AArch64.numVal vs

/-- `Σ_j (x v_j mod 2⁶⁴) 2^(64 j)`. -/
def loSum (x : Nat) : List Nat → Nat
  | [] => 0
  | v :: vs => x * v % 2 ^ 64 + 2 ^ 64 * VG.Proof.Mont.AArch64.loSum x vs

/-- `Σ_j ⌊x v_j / 2⁶⁴⌋ 2^(64 j)`. -/
def hiSum (x : Nat) : List Nat → Nat
  | [] => 0
  | v :: vs => x * v / 2 ^ 64 + 2 ^ 64 * VG.Proof.Mont.AArch64.hiSum x vs

theorem lo_hi_sum (x : Nat) : ∀ vs : List Nat, VG.Proof.Mont.AArch64.loSum x vs + 2 ^ 64 * VG.Proof.Mont.AArch64.hiSum x vs = x * VG.Proof.Mont.AArch64.numVal vs
  | [] => rfl
  | v :: vs => by
    have ih := VG.Proof.Mont.AArch64.lo_hi_sum x vs
    have hd := Nat.mod_add_div (x * v) (2 ^ 64)
    simp only [VG.Proof.Mont.AArch64.loSum, VG.Proof.Mont.AArch64.hiSum, VG.Proof.Mont.AArch64.numVal, Nat.mul_add]
    rw [Nat.mul_left_comm x (2 ^ 64), ← ih, Nat.mul_add]
    omega

theorem regsVal_eq_zero {s : State} : ∀ {rs : List Reg}, (∀ r ∈ rs, s.gpr r = 0) → regsVal s rs = 0
  | [], _ => rfl
  | r :: rs, h => by
    simp only [regsVal, h r (List.mem_cons_self ..),
      VG.Proof.Mont.AArch64.regsVal_eq_zero fun q hq => h q (List.mem_cons_of_mem _ hq), Nat.mul_zero, Nat.add_zero]
    rfl

/-- `t_j = x b_j mod 2⁶⁴`, into the cleared `ts`. -/
theorem mulsLo_ok {x : Reg} : ∀ (ts bs : List Reg) {s : State}, bs.length ≤ ts.length → ts.Nodup →
    (∀ t ∈ ts, t ≠ x ∧ t ∉ bs) → (∀ t ∈ ts, s.gpr t = 0) →
    WP isa (.block ((ts.zip bs).map fun (t, r) => .mul .x t x r)) s fun s' =>
      regsVal s' ts = VG.Proof.Mont.AArch64.loSum (s.gpr x).toNat (bs.map fun r => (s.gpr r).toNat) ∧ Keeps ts s s'
  | ts, [], s, _, _, _, h0 => by
    rw [List.zip_nil_right]
    exact WP.block_nil ⟨VG.Proof.Mont.AArch64.regsVal_eq_zero h0, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | [], _ :: _, _, hl, _, _, _ => absurd hl (by simp)
  | t :: ts, r :: bs, s, hl, hnd, hx, h0 => by
    simp only [List.length_cons, Nat.add_le_add_iff_right] at hl
    have htx := hx t (List.mem_cons_self ..)
    have htn := (List.nodup_cons.mp hnd).1
    rw [List.zip_cons_cons, List.map_cons, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.mul .x t x r]) s (fun s₁ =>
        (s₁.gpr t).toNat = (s.gpr x).toNat * (s.gpr r).toNat % 2 ^ 64 ∧ Keeps [t] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
        BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
      refine ⟨by rw [BitVec.toNat_mul], fun q hq => ?_, rfl, rfl, rfl, rfl⟩
      exact RegUpd.gpr_write_of_ne _ _ _ (by simpa using hq)) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hts : ∀ q ∈ ts, s₁.gpr q = s.gpr q := fun q hq => k₁.gpr q (by
      simp only [List.mem_singleton]; exact fun h => htn (h ▸ hq))
    refine WP.mono (VG.Proof.Mont.AArch64.mulsLo_ok ts bs (s := s₁) hl (List.nodup_cons.mp hnd).2
      (fun q hq => by
        have := hx q (List.mem_cons_of_mem _ hq)
        exact ⟨this.1, fun h => this.2 (List.mem_cons_of_mem _ h)⟩)
      (fun q hq => by rw [hts q hq]; exact h0 q (List.mem_cons_of_mem _ hq)))
      fun s₂ ⟨e₂, k₂⟩ => ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    have hx₁ : s₁.gpr x = s.gpr x := k₁.gpr x (by simpa using Ne.symm htx.1)
    have hbs : bs.map (fun q => (s₁.gpr q).toNat) = bs.map (fun q => (s.gpr q).toNat) :=
      List.map_congr_left fun q hq => by
        rw [k₁.gpr q (by
          simp only [List.mem_singleton]; exact fun h => htx.2 (h ▸ List.mem_cons_of_mem _ hq))]
    have ht₂ : s₂.gpr t = s₁.gpr t := k₂.gpr t htn
    simp only [regsVal, List.map_cons, VG.Proof.Mont.AArch64.loSum, ht₂, e₂, e₁, hx₁, hbs]

/-- The chain of the high words adds `⌊x b_j / 2⁶⁴⌋` at word `j`. -/
theorem chainVal_hi (x : Nat) (s : State) (base : Addr) : ∀ (ts bs : List Reg),
    bs.length ≤ ts.length →
    chainVal x s base ((ts.zip bs).map fun (t, r) => (t, some (Piece.hi (.reg r)))) =
      VG.Proof.Mont.AArch64.hiSum x (bs.map fun r => (s.gpr r).toNat)
  | _, [], _ => by simp [chainVal, VG.Proof.Mont.AArch64.hiSum]
  | [], _ :: _, h => absurd h (by simp)
  | t :: ts, r :: bs, h => by
    simp only [List.length_cons, Nat.add_le_add_iff_right] at h
    simp only [List.zip_cons_cons, List.map_cons, chainVal, optVal, Piece.val, Src.val, VG.Proof.Mont.AArch64.hiSum,
      VG.Proof.Mont.AArch64.chainVal_hi x s base ts bs h]

theorem numVal_map (s : State) : ∀ bs : List Reg, VG.Proof.Mont.AArch64.numVal (bs.map fun r => (s.gpr r).toNat) = regsVal s bs
  | [] => rfl
  | r :: bs => by simp only [List.map_cons, VG.Proof.Mont.AArch64.numVal, regsVal, VG.Proof.Mont.AArch64.numVal_map s bs]

theorem map_fst_zip_map {tl bs : List Reg} (h : tl.length = bs.length) :
    ((tl.zip bs).map fun (t, r) => (t, some (Piece.hi (.reg r)))).map Prod.fst = tl := by
  rw [List.map_map]
  exact (List.map_congr_left fun _ _ => rfl).trans (List.map_fst_zip (by omega))

theorem mem_zip_map {tl bs : List Reg} {e : Reg × Option Piece}
    (h : e ∈ (tl.zip bs).map fun (t, r) => (t, some (Piece.hi (.reg r)))) :
    ∃ t r, t ∈ tl ∧ r ∈ bs ∧ e = (t, some (Piece.hi (.reg r))) := by
  obtain ⟨⟨t, r⟩, hm, rfl⟩ := List.mem_map.mp h
  exact ⟨t, r, List.of_mem_zip hm |>.1, List.of_mem_zip hm |>.2, rfl⟩

/-- The first row into the cleared `ts` (`n + 1` words), for the
multiplicand's `n` words in the registers `bs`: `ts = x B`. -/
theorem rowInit_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.AArch64.Scr s base size) (hz : s.gpr .x7 = 0)
    {x : Reg} {ts bs : List Reg} (hlen : ts.length = bs.length + 1) (hnd : ts.Nodup)
    (hts : ∀ t ∈ ts, t ≠ .x0 ∧ t ≠ .x2 ∧ t ≠ .x3 ∧ t ≠ .x7 ∧ t ≠ x ∧ t ∉ bs)
    (hbs : ∀ r ∈ bs, r ≠ .x2 ∧ r ≠ .x3) (hx2 : x ≠ .x2) (hx3 : x ≠ .x3)
    (h0 : ∀ t ∈ ts, s.gpr t = 0) :
    WP isa (.block (rowInit x ts bs)) s fun s' =>
      regsVal s' ts = (s.gpr x).toNat * regsVal s bs ∧ Keeps (.x2 :: .x3 :: ts) s s' := by
  obtain ⟨t0, tl, rfl⟩ : ∃ t0 tl, ts = t0 :: tl := by
    cases ts with
    | nil => simp at hlen
    | cons t0 tl => exact ⟨t0, tl, rfl⟩
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
  have ht0 := hts t0 (List.mem_cons_self ..)
  have ht0l : t0 ∉ tl := (List.nodup_cons.mp hnd).1
  rw [rowInit, List.tail_cons, WP.block_append_iff]
  refine WP.mono (VG.Proof.Mont.AArch64.mulsLo_ok (x := x) (t0 :: tl) bs (by simp only [List.length_cons]; omega) hnd
    (fun t ht => ⟨(hts t ht).2.2.2.2.1, (hts t ht).2.2.2.2.2⟩) h0) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (fun h => (hts _ h).1 rfl)
  have hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr _ (fun h => (hts _ h).2.2.2.1 rfl), hz]
  have hx₁ : s₁.gpr x = s.gpr x := k₁.gpr x (fun h => (hts _ h).2.2.2.2.1 rfl)
  have hb₁ : bs.map (fun r => (s₁.gpr r).toNat) = bs.map (fun r => (s.gpr r).toNat) :=
    List.map_congr_left fun r hr => by rw [k₁.gpr r (fun h => (hts _ h).2.2.2.2.2 hr)]
  have hLf := VG.Proof.Mont.AArch64.map_fst_zip_map (bs := bs) hlen
  have hc : ChainOk size x ((tl.zip bs).map fun (t, r) => (t, some (Piece.hi (.reg r)))) := {
    nodup := by rw [hLf]; exact (List.nodup_cons.mp hnd).2
    regs := fun t ht => by
      rw [hLf] at ht
      have := hts t (List.mem_cons_of_mem _ ht)
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1⟩
    ok := fun e he p hp => by
      obtain ⟨t, r, -, hr, rfl⟩ := VG.Proof.Mont.AArch64.mem_zip_map he
      simp only [Option.mem_def, Option.some.injEq] at hp
      subst hp
      exact hbs r hr
    reads := fun e he p hp q hq => by
      obtain ⟨t, r, -, hr, rfl⟩ := VG.Proof.Mont.AArch64.mem_zip_map he
      simp only [Option.mem_def, Option.some.injEq] at hp
      subst hp
      simp only [Piece.reads, Src.reads, Option.mem_def, Option.some.injEq] at hq
      subst hq
      rw [hLf]
      exact ⟨fun h => (hts _ (List.mem_cons_of_mem _ h)).2.2.2.2.2 hr, hbs _ hr⟩ }
  refine WP.mono (chainSkip_ok hx2 hx3 _ hs₁ hz₁ hc) fun s₂ ⟨⟨c, hc1, e₂⟩, k₂⟩ => ?_
  rw [hLf] at e₂ k₂
  rw [List.length_map, List.length_zip, hlen, Nat.min_self] at e₂
  rw [VG.Proof.Mont.AArch64.chainVal_hi _ s₁ base tl bs (by omega), hb₁, hx₁] at e₂
  refine ⟨?_, k₁.mono (by sub_regs) |>.trans (k₂.mono fun q hq => by
    simp only [List.mem_cons] at hq ⊢
    rcases hq with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h)))⟩
  have ht₂ : s₂.gpr t0 = s₁.gpr t0 := k₂.gpr t0 (by
    simp only [List.mem_cons, not_or]; exact ⟨ht0.2.1, ht0.2.2.1, ht0l⟩)
  have hsum := VG.Proof.Mont.AArch64.lo_hi_sum (s.gpr x).toNat (bs.map fun r => (s.gpr r).toNat)
  rw [VG.Proof.Mont.AArch64.numVal_map] at hsum

  have hlt : (s.gpr x).toNat * regsVal s bs < 2 ^ (64 * (bs.length + 1)) := by
    have h1 := (s.gpr x).isLt
    have h2 := regsVal_lt s bs
    rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm (2 ^ (64 * bs.length))]
    exact Nat.mul_lt_mul_of_lt_of_lt h1 h2
  simp only [regsVal] at e₁ ⊢
  rw [ht₂]
  have hP : 2 ^ (64 * (bs.length + 1)) = 2 ^ 64 * 2 ^ (64 * bs.length) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
  rw [hP] at hlt
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
  · simp only [Nat.mul_zero, Nat.add_zero] at e₂
    rw [← hsum, e₂, Nat.mul_add]; omega
  · exfalso
    simp only [Nat.mul_one] at e₂
    have h3 : 2 ^ 64 * (regsVal s₂ tl + 2 ^ (64 * bs.length)) =
        2 ^ 64 * (regsVal s₁ tl + VG.Proof.Mont.AArch64.hiSum (s.gpr x).toNat (bs.map fun r => (s.gpr r).toNat)) := by
      rw [e₂]
    rw [Nat.mul_add, Nat.mul_add] at h3
    omega

end VG.Proof.Mont.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.AArch64.Round`. -/
section

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
  simp only [wins]; exact List.map_congr_left fun j _ => VG.Proof.Mont.AArch64.win_mod n i j

theorem wins_length (n i : Nat) : (wins n i).length = n + 2 := by simp [wins]

theorem wins_cons (n i : Nat) :
    wins n i = win n i 0 :: (List.range (n + 1)).map (fun j => win n i (j + 1)) := by
  simp only [wins, List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

theorem wins_succ (n i : Nat) :
    wins n (i + 1) = (List.range (n + 1)).map (fun j => win n i (j + 1)) ++ [win n i 0] := by
  rw [wins, show win n (i + 1) = fun j => win n i (j + 1) from funext (VG.Proof.Mont.AArch64.win_succ n i)]
  simp only [List.range_succ (n := n + 1), List.map_append, List.map_cons, List.map_nil, VG.Proof.Mont.AArch64.win_wrap]

theorem wins_split (n i : Nat) :
    wins n i = (List.range n).map (win n i) ++ [win n i n, win n i (n + 1)] := by
  simp only [wins, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    List.append_assoc, List.singleton_append]

theorem fresh_wins_lt : ∀ n < 7, ∀ i < n + 2, Fresh (wins n i) := by
  unfold Fresh; decide

theorem fresh_wins {n : Nat} (hn : n < 7) (i : Nat) : Fresh (wins n i) := by
  rw [VG.Proof.Mont.AArch64.wins_mod]; exact VG.Proof.Mont.AArch64.fresh_wins_lt n hn _ (Nat.mod_lt _ (by omega))

/-! ## The multiplicands -/

/-- The registers `bRegs` hold their words of `[b]` (`n` words). -/
def BRegs (s : State) (base : Addr) (b n : Nat) : Prop :=
  ∀ j < n, ∀ r, bRegs[j]? = some r → s.gpr r = VG.Proof.Mont.word s.mem base (b + 8 * j)

theorem BRegs.keep {s s' : State} {base : Addr} {b n : Nat} (h : VG.Proof.Mont.AArch64.BRegs s base b n)
    (hm : s'.mem = s.mem) (hr : ∀ r ∈ bRegs, s'.gpr r = s.gpr r) : VG.Proof.Mont.AArch64.BRegs s' base b n :=
  fun j hj r hjr => by rw [hr r (List.mem_of_getElem? hjr), hm]; exact h j hj r hjr

/-- `x6` holds the constant the reduction uses: `minv`, or the first general
word of `m'`. -/
def ConstOk (M : Mod) (s : State) : Prop :=
  match M.red with
  | .general => s.gpr .x6 = M.minv
  | .friendly ws => ∀ v, firstGen ws = some v → s.gpr .x6 = BitVec.ofNat 64 v

theorem ConstOk.keep {M : Mod} {s s' : State} (h : VG.Proof.Mont.AArch64.ConstOk M s) (h6 : s'.gpr .x6 = s.gpr .x6) :
    VG.Proof.Mont.AArch64.ConstOk M s' := by
  unfold VG.Proof.Mont.AArch64.ConstOk at h ⊢
  cases hr : M.red with
  | general => rw [hr] at h; exact h6.trans h
  | friendly ws => rw [hr] at h; exact fun v hv => h6.trans (h v hv)

theorem bWords_length (b : Nat) : ∀ j k, (bWords b j k).length = k
  | _, 0 => rfl
  | j, k + 1 => by simp only [bWords, List.length_cons, VG.Proof.Mont.AArch64.bWords_length b (j + 1) k]

theorem mWords_length (mo : Nat) : ∀ j k, (mWords mo j k).length = k
  | _, 0 => rfl
  | j, k + 1 => by simp only [mWords, List.length_cons, VG.Proof.Mont.AArch64.mWords_length mo (j + 1) k]

theorem mem_bWords {b : Nat} : ∀ {j k : Nat} {w : RWord}, w ∈ bWords b j k →
    ∃ j', j ≤ j' ∧ j' < j + k ∧ w = .gen (bSrc b j')
  | _, 0, _, h => absurd h List.not_mem_nil
  | j, k + 1, w, h => by
    simp only [bWords, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨j, Nat.le_refl _, by omega, rfl⟩
    · obtain ⟨j', h1, h2, h3⟩ := VG.Proof.Mont.AArch64.mem_bWords h
      exact ⟨j', by omega, by omega, h3⟩

theorem mem_mWords {mo : Nat} : ∀ {j k : Nat} {w : RWord}, w ∈ mWords mo j k →
    ∃ j', j ≤ j' ∧ j' < j + k ∧ w = .gen (.mem (mo + 8 * j'))
  | _, 0, _, h => absurd h List.not_mem_nil
  | j, k + 1, w, h => by
    simp only [mWords, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨j, Nat.le_refl _, by omega, rfl⟩
    · obtain ⟨j', h1, h2, h3⟩ := VG.Proof.Mont.AArch64.mem_mWords h
      exact ⟨j', by omega, by omega, h3⟩

theorem bSrc_val {s : State} {base : Addr} {b n : Nat} (hB : VG.Proof.Mont.AArch64.BRegs s base b n) {j : Nat}
    (hj : j < n) : (bSrc b j).val s base = (VG.Proof.Mont.word s.mem base (b + 8 * j)).toNat := by
  unfold bSrc
  cases h : bRegs[j]? with
  | none => rfl
  | some r => simp only [Src.val, hB j hj r h]

theorem rwVal_bWords {s : State} {base : Addr} {b n : Nat} (hB : VG.Proof.Mont.AArch64.BRegs s base b n) :
    ∀ j k, j + k ≤ n → rwVal s base (bWords b j k) = wordsVal s.mem base (b + 8 * j) k
  | _, 0, _ => rfl
  | j, k + 1, h => by
    simp only [bWords, rwVal, wordsVal, RWord.val, VG.Proof.Mont.AArch64.bSrc_val hB (show j < n by omega),
      VG.Proof.Mont.AArch64.rwVal_bWords hB (j + 1) k (by omega), show b + 8 * (j + 1) = b + 8 * j + 8 by omega]

theorem rwVal_mWords (s : State) (base : Addr) (mo : Nat) :
    ∀ j k, rwVal s base (mWords mo j k) = wordsVal s.mem base (mo + 8 * j) k
  | _, 0 => rfl
  | j, k + 1 => by
    simp only [mWords, rwVal, wordsVal, RWord.val, Src.val, VG.Proof.Mont.AArch64.rwVal_mWords s base mo (j + 1) k,
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
    simp only [List.map_cons, rwVal, mwVal, VG.Proof.Mont.AArch64.rwVal_fWords h6 ws h.2, VG.Proof.Mont.AArch64.fWord_val h6 h.1]

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
  rw [VG.Proof.Mont.AArch64.wins_cons]; rfl

/-- The window's registers: distinct, and none of `x0`–`x7`, `x16`, `x17`. -/
theorem wins_regs {n : Nat} (hn : n < 7) (i : Nat) :
    ∀ r ∈ wins n i, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x5 ∧ r ≠ .x6 ∧
      r ≠ .x7 ∧ r ≠ .x16 ∧ r ≠ .x17 := by
  intro r hr
  have := (VG.Proof.Mont.AArch64.fresh_wins hn i).2 r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
  exact this

theorem bRegs_regs : ∀ r ∈ bRegs, r = .x4 ∨ r = .x5 ∨ r = .x16 ∨ r = .x17 := by decide

theorem rowOkA {size : Nat} {n b : Nat} (hn : n < 7) (hb : b + 8 * n ≤ size) (hb8 : b % 8 = 0)
    (i : Nat) : RowOk size .x1 (wins n i) (bWords b 0 n) where
  nodup := (VG.Proof.Mont.AArch64.fresh_wins hn i).1
  regs t ht := by have := VG.Proof.Mont.AArch64.wins_regs hn i t ht; exact ⟨this.1, this.2.2.1, this.2.2.2.1,
    this.2.2.2.2.2.2.2.1, this.2.1⟩
  ok w hw := by
    obtain ⟨j, -, hj, rfl⟩ := VG.Proof.Mont.AArch64.mem_bWords hw
    unfold bSrc
    cases h : bRegs[j]? with
    | none => exact ⟨by omega, by omega⟩
    | some r =>
      rcases VG.Proof.Mont.AArch64.bRegs_regs r (List.mem_of_getElem? h) with rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, by decide⟩
  reads w hw r hr := by
    obtain ⟨j, -, hj, rfl⟩ := VG.Proof.Mont.AArch64.mem_bWords hw
    unfold bSrc at hr
    cases h : bRegs[j]? with
    | none => rw [h] at hr; simp [RWord.reads, Src.reads] at hr
    | some q =>
      rw [h] at hr
      simp only [RWord.reads, Src.reads, Option.mem_def, Option.some.injEq] at hr
      subst hr
      refine ⟨fun hm => ?_, ?_⟩
      · have := VG.Proof.Mont.AArch64.wins_regs hn i q hm
        rcases VG.Proof.Mont.AArch64.bRegs_regs q (List.mem_of_getElem? h) with rfl | rfl | rfl | rfl <;> simp at this
      · rcases VG.Proof.Mont.AArch64.bRegs_regs q (List.mem_of_getElem? h) with rfl | rfl | rfl | rfl <;> decide
  x2 := by decide
  x3 := by decide

theorem rowOkM {size : Nat} {n mo : Nat} (hn : n < 7) (hmo : mo + 8 * n ≤ size) (hmo8 : mo % 8 = 0)
    (i : Nat) : RowOk size .x1 (wins n i) (mWords mo 0 n) where
  nodup := (VG.Proof.Mont.AArch64.fresh_wins hn i).1
  regs t ht := by have := VG.Proof.Mont.AArch64.wins_regs hn i t ht; exact ⟨this.1, this.2.2.1, this.2.2.2.1,
    this.2.2.2.2.2.2.2.1, this.2.1⟩
  ok w hw := by
    obtain ⟨j, -, hj, rfl⟩ := VG.Proof.Mont.AArch64.mem_mWords hw
    exact ⟨by omega, by omega⟩
  reads w hw r hr := by
    obtain ⟨j, -, hj, rfl⟩ := VG.Proof.Mont.AArch64.mem_mWords hw
    simp [RWord.reads, Src.reads] at hr
  x2 := by decide
  x3 := by decide

theorem rowOkF {size : Nat} {n : Nat} (hn : n < 7) (i : Nat) {ws : List MWord}
    (hws : ws.all MWord.ok = true) (g : Option Nat) :
    RowOk size (win n i 0) (wins n i).tail (ws.map (fWord g)) where
  nodup := (VG.Proof.Mont.AArch64.fresh_wins hn i).1.tail
  regs t ht := by
    have hm : t ∈ wins n i := List.mem_of_mem_tail ht
    have := VG.Proof.Mont.AArch64.wins_regs hn i t hm
    refine ⟨this.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.2.2.2.1, fun h => ?_⟩
    have hnd := (VG.Proof.Mont.AArch64.fresh_wins hn i).1
    rw [VG.Proof.Mont.AArch64.wins_cons] at hnd ht
    exact (List.nodup_cons.mp hnd).1 (h ▸ ht)
  ok w hw := by
    obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
    exact (VG.Proof.Mont.AArch64.fWord_ok (List.all_eq_true.mp hws w' hw')).1
  reads w hw r hr := by
    obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
    have := (VG.Proof.Mont.AArch64.fWord_ok (size := size) (g := g) (List.all_eq_true.mp hws w' hw')).2 r hr
    subst this
    exact ⟨fun hm => (VG.Proof.Mont.AArch64.wins_regs hn i _ (List.mem_of_mem_tail hm)).2.2.2.2.2.2.1 rfl, by decide,
      by decide⟩
  x2 := (VG.Proof.Mont.AArch64.wins_regs hn i _ (by rw [VG.Proof.Mont.AArch64.wins_cons]; exact List.mem_cons_self ..)).2.2.1
  x3 := (VG.Proof.Mont.AArch64.wins_regs hn i _ (by rw [VG.Proof.Mont.AArch64.wins_cons]; exact List.mem_cons_self ..)).2.2.2.1

/-- `x1 = t₀ x6 mod 2⁶⁴`. -/
theorem mulU_ok (s : State) (t0 : Reg) :
    WP isa (.block [.mul .x .x1 t0 .x6]) s fun s' =>
      (s'.gpr .x1).toNat = (s.gpr t0).toNat * (s.gpr .x6).toNat % 2 ^ 64 ∧ Keeps [.x1] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [BitVec.toNat_mul], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  exact RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr)

theorem RowOk.sub {size : Nat} {x : Reg} {ts ts' : List Reg} {ws : List RWord} (h : RowOk size x ts ws)
    (hs : ts'.Sublist ts) : RowOk size x ts' ws where
  nodup := hs.nodup h.nodup
  regs t ht := h.regs t (hs.subset ht)
  ok := h.ok
  reads w hw r hr := have := h.reads w hw r hr; ⟨fun h' => this.1 (hs.subset h'), this.2⟩
  x2 := h.x2
  x3 := h.x3

theorem regsVal_zero_of {s : State} {rs : List Reg} (h : regsVal s rs = 0) : ∀ r ∈ rs, s.gpr r = 0 := by
  induction rs with
  | nil => intro r hr; exact absurd hr List.not_mem_nil
  | cons q rs ih =>
    intro r hr
    simp only [regsVal] at h
    rcases List.mem_cons.mp hr with rfl | hr
    · exact BitVec.eq_of_toNat_eq (show _ = 0 by omega)
    · exact ih (by omega) r hr

/-- The window as its low `n + 1` words and the rest. -/
theorem regsVal_wins_split (s : State) (n i : Nat) :
    regsVal s (wins n i) = regsVal s ((wins n i).take (n + 1)) +
      2 ^ (64 * (n + 1)) * regsVal s ((wins n i).drop (n + 1)) := by
  conv => lhs; rw [← List.take_append_drop (n + 1) (wins n i)]
  rw [regsVal_append, List.length_take, VG.Proof.Mont.AArch64.wins_length, Nat.min_eq_left (by omega)]

theorem bWords_regs (b : Nat) : ∀ n ≤ 4, bWords b 0 n = (bRegs.take n).map fun r => .gen (.reg r) := by
  intro n hn
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem rwVal_regs (s : State) (base : Addr) : ∀ rs : List Reg,
    rwVal s base (rs.map fun r => .gen (.reg r)) = regsVal s rs
  | [] => rfl
  | r :: rs => by simp only [List.map_cons, rwVal, RWord.val, Src.val, regsVal, VG.Proof.Mont.AArch64.rwVal_regs s base rs]

/-- `x1 = a_i` and `T += a_i B`: the first row straight into the cleared
accumulator, or a row into the window (its low `n + 1` words for a tight
modulus). -/
theorem prodRow_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.AArch64.Scr s base size) {M : Mod}
    (hn : M.n < 7) {a b i m : Nat} (ha : a + 8 * i + 8 ≤ size) (hb : b + 8 * M.n ≤ size)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hz : s.gpr .x7 = 0) (hBR : VG.Proof.Mont.AArch64.BRegs s base b M.n)
    (hm : m < 2 ^ (64 * M.n)) (hok : M.ok m = true) (hB : wordsVal s.mem base b M.n < m)
    (hT : regsVal s (wins M.n i) < 2 * m) (h0 : i = 0 → regsVal s (wins M.n 0) = 0) :
    WP isa (.block (prodRow M a b i)) s
      fun s' => regsVal s' (wins M.n i) = regsVal s (wins M.n i) +
          (VG.Proof.Mont.word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n ∧
        Keeps (.x1 :: .x2 :: .x3 :: wins M.n i) s s' := by
  have hw := VG.Proof.Mont.AArch64.wins_regs hn i
  rw [prodRow, WP.block_append_iff]
  refine WP.mono (VG.Proof.Mont.AArch64.ld_ok hs ha (by omega) .x1) fun s₁ ⟨c₁, k₁, _⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr .x7 (by decide), hz]
  have hT₁ : ∀ ts : List Reg, (∀ q ∈ ts, q ∈ wins M.n i) → regsVal s₁ ts = regsVal s ts :=
    fun ts hts => regsVal_congr fun q hq => k₁.gpr q (by simp [(hw q (hts q hq)).2.1])
  have hBR₁ : VG.Proof.Mont.AArch64.BRegs s₁ base b M.n := hBR.keep k₁.mem fun r hr => k₁.gpr r (by
    rcases VG.Proof.Mont.AArch64.bRegs_regs r hr with rfl | rfl | rfl | rfl <;> decide)
  have hRB : rwVal s₁ base (bWords b 0 M.n) = wordsVal s.mem base b M.n := by
    rw [VG.Proof.Mont.AArch64.rwVal_bWords hBR₁ 0 M.n (by omega), k₁.mem]; rfl
  have hA := (VG.Proof.Mont.word s.mem base (a + 8 * i)).isLt
  have hAB : (VG.Proof.Mont.word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n ≤ (2 ^ 64 - 1) * m :=
    Nat.mul_le_mul (by omega) (by omega)
  have hlen : (wins M.n i).length = M.n + 2 := VG.Proof.Mont.AArch64.wins_length M.n i
  have htake : ∀ q ∈ (wins M.n i).take (M.n + 1), q ∈ wins M.n i := fun q hq => List.mem_of_mem_take hq
  have hdrop : ∀ q ∈ (wins M.n i).drop (M.n + 1), q ∈ wins M.n i := fun q hq => List.mem_of_mem_drop hq
  have hnd := (VG.Proof.Mont.AArch64.fresh_wins hn i).1
  have hdisj : ∀ q ∈ (wins M.n i).drop (M.n + 1), q ∉ (wins M.n i).take (M.n + 1) := fun q hq ht => by
    have hnd' : ((wins M.n i).take (M.n + 1) ++ (wins M.n i).drop (M.n + 1)).Nodup := by
      rw [List.take_append_drop]; exact hnd
    exact (List.nodup_append.mp hnd').2.2 q ht q hq rfl
  have hP1 : 2 ^ (64 * (M.n + 1)) = 2 ^ (64 * M.n) * 2 ^ 64 := by
    rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
  have hmP : (2 ^ 64 - 1) * m ≤ 2 ^ (64 * M.n) * 2 ^ 64 := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) (by omega)
  -- A row into the low `n + 1` words leaves the rest.
  have rest : ∀ t : State, (∀ q ∈ (wins M.n i).drop (M.n + 1), t.gpr q = s₁.gpr q) →
      regsVal t ((wins M.n i).take (M.n + 1)) = regsVal s ((wins M.n i).take (M.n + 1)) +
        (VG.Proof.Mont.word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n →
      regsVal t (wins M.n i) = regsVal s (wins M.n i) +
        (VG.Proof.Mont.word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n := by
    intro t hd ht
    rw [VG.Proof.Mont.AArch64.regsVal_wins_split t, VG.Proof.Mont.AArch64.regsVal_wins_split s, ht, regsVal_congr hd, hT₁ _ hdrop]
    omega
  by_cases hi : i = 0 ∧ M.n ≤ 4
  · rw [ite_eq_left_iff.mpr (fun h => absurd hi h)]
    obtain ⟨rfl, hn4⟩ := hi
    have hz0 := VG.Proof.Mont.AArch64.regsVal_zero_of (h0 rfl)
    have hbl : (bRegs.take M.n).length = M.n := by
      rw [List.length_take]; exact Nat.min_eq_left (by simp [bRegs]; omega)
    have hbs : ∀ r ∈ bRegs.take M.n, r ∈ bRegs := fun r hr => List.mem_of_mem_take hr
    refine WP.mono (VG.Proof.Mont.AArch64.rowInit_ok hs₁ hz₁ (x := .x1) (ts := (wins M.n 0).take (M.n + 1))
      (bs := bRegs.take M.n) (by rw [List.length_take, VG.Proof.Mont.AArch64.wins_length, hbl]; omega)
      ((List.take_sublist _ _).nodup hnd)
      (fun t ht => by
        have := hw t (htake t ht)
        refine ⟨this.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.2.2.2.1, this.2.1, fun hb' => ?_⟩
        rcases VG.Proof.Mont.AArch64.bRegs_regs t (hbs t hb') with rfl | rfl | rfl | rfl <;> simp at this)
      (fun r hr => by rcases VG.Proof.Mont.AArch64.bRegs_regs r (hbs r hr) with rfl | rfl | rfl | rfl <;> decide)
      (by decide) (by decide)
      (fun t ht => by rw [k₁.gpr t (by simp [(hw t (htake t ht)).2.1])]; exact hz0 t (htake t ht)))
      fun s₂ ⟨e₂, k₂⟩ => ⟨rest s₂ (fun q hq => k₂.gpr q (by
          have := hw q (hdrop q hq)
          simp only [List.mem_cons, not_or]
          exact ⟨this.2.2.1, this.2.2.2.1, hdisj q hq⟩)) (by
        have hz : regsVal s ((wins M.n 0).take (M.n + 1)) = 0 := by
          have h := h0 rfl; rw [VG.Proof.Mont.AArch64.regsVal_wins_split] at h; omega
        rw [e₂, hz, c₁, ← VG.Proof.Mont.AArch64.rwVal_regs s₁ base, ← VG.Proof.Mont.AArch64.bWords_regs b M.n hn4, hRB, Nat.zero_add]), (k₁.mono (by sub_regs)).trans (k₂.mono fun q hq => by
          simp only [List.mem_cons] at hq ⊢
          rcases hq with h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (htake q h))))⟩
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hi), prodWins]
    by_cases ht : M.tight = true
    · rw [ite_eq_left_iff.mpr (fun h => absurd ht h)]
      have hti := Mod.ok_tight hok ht
      have hRT : regsVal s ((wins M.n i).take (M.n + 1)) < 2 * m := by
        have := VG.Proof.Mont.AArch64.regsVal_wins_split s M.n i; omega
      refine WP.mono (row_ok hs₁ hz₁ ((VG.Proof.Mont.AArch64.rowOkA hn hb hb8 i).sub (List.take_sublist _ _))
          (by rw [VG.Proof.Mont.AArch64.bWords_length, List.length_take, hlen]; omega) (by
            rw [hT₁ _ htake, c₁, hRB, List.length_take, hlen, Nat.min_eq_left (by omega)]
            omega)) fun s₂ ⟨e₂, k₂⟩ =>
        ⟨rest s₂ (fun q hq => k₂.gpr q (by
            have := hw q (hdrop q hq)
            simp only [List.mem_cons, not_or]
            exact ⟨this.2.2.1, this.2.2.2.1, hdisj q hq⟩))
          (by rw [e₂, hT₁ _ htake, c₁, hRB]),
          (k₁.mono (by sub_regs)).trans (k₂.mono fun q hq => by
            simp only [List.mem_cons] at hq ⊢
            rcases hq with h | h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr (htake q h))))⟩
    · rw [ite_eq_right_iff.mpr (fun h => absurd h ht)]
      have hP : 2 ^ (64 * (M.n + 2)) = 2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64 := by
        rw [show 64 * (M.n + 2) = 64 * M.n + 64 + 64 by omega, Nat.pow_add, Nat.pow_add]
      refine WP.mono (row_ok hs₁ hz₁ (VG.Proof.Mont.AArch64.rowOkA hn hb hb8 i) (by rw [VG.Proof.Mont.AArch64.bWords_length, hlen]; omega) (by
          rw [hT₁ _ (fun _ h => h), c₁, hRB, hlen, hP]; omega)) fun s₂ ⟨e₂, k₂⟩ => ?_
      refine ⟨by rw [e₂, hT₁ _ (fun _ h => h), c₁, hRB],
        (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩

/-- Round `i` of the multiplication, with `x7 = 0`, `[b]`'s words in
`bRegs` and the reduction's constant in `x6`: `2⁶⁴ T' = T + a_i B + u m`,
and `T' < 2m` if `T < 2m`. -/
theorem round_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.AArch64.Scr s base size) {M : Mod}
    (hn : M.n < 7) {a b i m : Nat} (ha : a + 8 * i + 8 ≤ size) (hb : b + 8 * M.n ≤ size)
    (hmo : M.mo + 8 * M.n ≤ size) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hmo8 : M.mo % 8 = 0)
    (hz : s.gpr .x7 = 0) (hm : wordsVal s.mem base M.mo M.n = m)
    (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) (hok : M.ok m = true)
    (hBR : VG.Proof.Mont.AArch64.BRegs s base b M.n) (h6 : VG.Proof.Mont.AArch64.ConstOk M s) (hB : wordsVal s.mem base b M.n < m)
    (hT : regsVal s (wins M.n i) < 2 * m) (h0 : i = 0 → regsVal s (wins M.n 0) = 0) :
    WP isa (.block (VG.Impl.Mont.AArch64.round M a b i)) s fun s' =>
      (∃ u, 2 ^ 64 * regsVal s' (wins M.n (i + 1)) = regsVal s (wins M.n i) +
        (VG.Proof.Mont.word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n + u * m) ∧
      regsVal s' (wins M.n (i + 1)) < 2 * m ∧
      Keeps (.x1 :: .x2 :: .x3 :: wins M.n i) s s' := by
  have hred := Mod.ok_red hok
  have hw := VG.Proof.Mont.AArch64.wins_regs hn i
  have n0 : Reg.x0 ∉ wins M.n i := fun h => (hw _ h).1 rfl
  have n6 : Reg.x6 ∉ wins M.n i := fun h => (hw _ h).2.2.2.2.2.2.1 rfl
  have n7 : Reg.x7 ∉ wins M.n i := fun h => (hw _ h).2.2.2.2.2.2.2.1 rfl
  have hm' : m < 2 ^ (64 * M.n) := hm ▸ wordsVal_lt _ _ _ _
  have hcons := VG.Proof.Mont.AArch64.wins_cons M.n i
  have ht0 : win M.n i 0 ∈ wins M.n i := by rw [hcons]; exact List.mem_cons_self ..
  have hlen : (wins M.n i).length = M.n + 2 := VG.Proof.Mont.AArch64.wins_length M.n i
  have hP : 2 ^ (64 * (M.n + 2)) = 2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64 := by
    rw [show 64 * (M.n + 2) = 64 * M.n + 64 + 64 by omega, Nat.pow_add, Nat.pow_add]
  have hmP : (2 ^ 64 - 1) * m ≤ 2 ^ (64 * M.n) * 2 ^ 64 := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) (by omega)
  have hAB : (VG.Proof.Mont.word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n ≤ (2 ^ 64 - 1) * m :=
    Nat.mul_le_mul (by have := (VG.Proof.Mont.word s.mem base (a + 8 * i)).isLt; omega) (by omega)
  -- The window after the round, from its value `V` with a zero low word.
  have hrot : ∀ t : State, (t.gpr (win M.n i 0)).toNat = 0 →
      2 ^ 64 * regsVal t (wins M.n (i + 1)) = regsVal t (wins M.n i) := by
    intro t h0
    rw [VG.Proof.Mont.AArch64.wins_succ, regsVal_append, hcons, regsVal]
    simp only [regsVal, h0, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  cases hr : M.red with
  | general =>
    have hcode : VG.Impl.Mont.AArch64.round M a b i = prodRow M a b i ++
        (([.mul .x .x1 (win M.n i 0) .x6] : List Instr) ++ row .x1 (wins M.n i) (mWords M.mo 0 M.n)) := by
      simp only [VG.Impl.Mont.AArch64.round, hr, List.cons_append, List.nil_append]
    have h6' : s.gpr .x6 = M.minv := by unfold VG.Proof.Mont.AArch64.ConstOk at h6; rw [hr] at h6; exact h6
    rw [hcode, WP.block_append_iff]
    refine WP.mono (VG.Proof.Mont.AArch64.prodRow_ok hs hn ha hb ha8 hb8 hz hBR hm' hok hB hT h0) fun s₂ ⟨e₂, k₂⟩ => ?_
    have hs₂ := hs.of_keeps k₂ (by simp [n0])
    have hz₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (by simp [n7]), hz]
    have h6₂ : s₂.gpr .x6 = M.minv := by
      rw [k₂.gpr _ (by simp [n6]), h6']
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Mont.AArch64.mulU_ok s₂ (win M.n i 0)) fun s₃ ⟨u₃, k₃⟩ => ?_
    have hs₃ := hs₂.of_keeps k₃ (by decide)
    have hz₃ : s₃.gpr .x7 = 0 := by rw [k₃.gpr .x7 (by decide), hz₂]
    have hT₃ : regsVal s₃ (wins M.n i) = regsVal s₂ (wins M.n i) := regsVal_congr fun q hq =>
      k₃.gpr q (by simp [(hw q hq).2.1])
    have hmem₃ : s₃.mem = s.mem := by rw [k₃.mem, k₂.mem]
    have hu := (s₃.gpr .x1).isLt
    have hum : (s₃.gpr .x1).toNat * m ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul (by omega) (Nat.le_refl _)
    have hRM : rwVal s₃ base (mWords M.mo 0 M.n) = m := by
      rw [VG.Proof.Mont.AArch64.rwVal_mWords, hmem₃, Nat.mul_zero, Nat.add_zero, hm]
    refine WP.mono (row_ok hs₃ hz₃ (VG.Proof.Mont.AArch64.rowOkM hn hmo hmo8 i) (by rw [VG.Proof.Mont.AArch64.mWords_length, hlen]; omega) (by
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
    have hcode : VG.Impl.Mont.AArch64.round M a b i = prodRow M a b i ++
        (row (win M.n i 0) (wins M.n i).tail (ws.map (fWord (firstGen ws))) ++
          ([.movz .x (win M.n i 0) 0 0] : List Instr)) := by
      simp only [VG.Impl.Mont.AArch64.round, hr]
    have hok := hred
    rw [hr] at hok
    simp only [Red.ok, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨hwl, hm1⟩, hmv⟩, hwok⟩ := hok
    have h6' : ∀ v, firstGen ws = some v → s.gpr .x6 = BitVec.ofNat 64 v := by
      unfold VG.Proof.Mont.AArch64.ConstOk at h6; rw [hr] at h6; exact h6
    -- `2⁶⁴ m' = m + 1`.
    have hm2 : 2 ^ 64 * mwVal ws = m + 1 := by
      rw [hmv]
      have := Nat.div_add_mod (m + 1) (2 ^ 64)
      have : (m + 1) % 2 ^ 64 = 0 := by omega
      omega
    rw [hcode, WP.block_append_iff]
    refine WP.mono (VG.Proof.Mont.AArch64.prodRow_ok hs hn ha hb ha8 hb8 hz hBR hm' hok hB hT h0) fun s₂ ⟨e₂, k₂⟩ => ?_
    have hs₂ := hs.of_keeps k₂ (by simp [n0])
    have hz₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (by simp [n7]), hz]
    have h6₂ : ∀ v, firstGen ws = some v → s₂.gpr .x6 = BitVec.ofNat 64 v := fun v hv => by
      rw [k₂.gpr _ (by simp [n6]), h6' v hv]
    have hRF : rwVal s₂ base (ws.map (fWord (firstGen ws))) = mwVal ws := VG.Proof.Mont.AArch64.rwVal_fWords h6₂ ws hwok
    -- The window as its low word and the rest.
    have hsplit : ∀ t : State, regsVal t (wins M.n i) =
        (t.gpr (win M.n i 0)).toNat + 2 ^ 64 * regsVal t (wins M.n i).tail := by
      intro t; rw [hcons]; rfl
    have htl : (wins M.n i).tail.length = M.n + 1 := by rw [VG.Proof.Mont.AArch64.wins_tail]; simp
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
    refine WP.mono (row_ok hs₂ hz₂ (VG.Proof.Mont.AArch64.rowOkF hn i hwok (firstGen ws)) (by
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
        have hnd := (VG.Proof.Mont.AArch64.fresh_wins hn i).1
        rw [hcons] at hnd
        simp only [List.mem_singleton]
        intro h; subst h
        exact (List.nodup_cons.mp hnd).1 (by rw [← VG.Proof.Mont.AArch64.wins_tail]; exact hq))
    have hval : 2 ^ 64 * regsVal s₄ (wins M.n (i + 1)) = regsVal s₂ (wins M.n i) +
        (s₂.gpr (win M.n i 0)).toNat * m := by
      rw [VG.Proof.Mont.AArch64.wins_succ, regsVal_append, ← VG.Proof.Mont.AArch64.wins_tail, htl, htl₄, e₃]
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

end

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.AArch64.Rounds`. -/
section

/-!
# Montgomery arithmetic on AArch64: the rounds of the multiplication

The accumulator cleared (`zeros_ok`), then `k` rounds (`rounds_ok`):
`2^(64 k) T = [a]_k B + U m` for some `U`, with `T < 2m`.
-/

namespace VG.Proof.Mont.AArch64

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

theorem regsVal_zero {s : State} {rs : List Reg} (h : ∀ r ∈ rs, s.gpr r = 0) : regsVal s rs = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [regsVal, h r (List.mem_cons_self ..), ih fun q hq => h q (List.mem_cons_of_mem _ hq)]
    rfl

theorem zeros_ok (s : State) : ∀ ts : List Reg,
    WP isa (.block (zeros ts)) s fun s' => (∀ t ∈ ts, s'.gpr t = 0) ∧ Keeps ts s s'
  | [] => WP.block_nil ⟨fun _ h => absurd h (List.not_mem_nil), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | t :: ts => by
    rw [zeros, List.map_cons, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (movz0_ok s t) fun s₁ ⟨z₁, k₁⟩ => ?_
    refine WP.mono (VG.Proof.Mont.AArch64.zeros_ok s₁ ts) fun s₂ ⟨z₂, k₂⟩ => ⟨fun q hq => ?_, (k₁.mono (by sub_regs)).trans
      (k₂.mono (by sub_regs))⟩
    by_cases hqt : q ∈ ts
    · exact z₂ q hqt
    · have : q = t := by simpa [hqt] using hq
      subst this; rw [k₂.gpr _ hqt, z₁]

theorem wins_sub_acc_lt : ∀ n < 7, ∀ i < n + 2, ∀ r ∈ wins n i, r ∈ acc n := by decide

theorem wins_sub_acc {n : Nat} (hn : n < 7) (i : Nat) : ∀ r ∈ wins n i, r ∈ acc n := by
  rw [VG.Proof.Mont.AArch64.wins_mod]; exact VG.Proof.Mont.AArch64.wins_sub_acc_lt n hn _ (Nat.mod_lt _ (by omega))

theorem acc_regs_lt : ∀ n < 7, ∀ r ∈ acc n,
    r ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17] := by
  decide

/-- `k` rounds, from a cleared accumulator, with `x7 = 0`, `[b]`'s words in
`bRegs` and the reduction's constant in `x6`. -/
theorem rounds_ok {M : Mod} (hn : M.n < 7) {a b m size : Nat}
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size) (hmo : M.mo + 8 * M.n ≤ size)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hmo8 : M.mo % 8 = 0)
    (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) (hok : M.ok m = true) :
    ∀ k ≤ M.n, ∀ {s : State} {base : Addr}, VG.Proof.Mont.AArch64.Scr s base size → s.gpr .x7 = 0 →
      wordsVal s.mem base M.mo M.n = m → VG.Proof.Mont.AArch64.BRegs s base b M.n → VG.Proof.Mont.AArch64.ConstOk M s →
      wordsVal s.mem base b M.n < m → regsVal s (wins M.n 0) = 0 →
      WP isa (.block ((List.range k).flatMap (VG.Impl.Mont.AArch64.round M a b))) s fun s' =>
        (∃ U, 2 ^ (64 * k) * regsVal s' (wins M.n k) =
          wordsVal s.mem base a k * wordsVal s.mem base b M.n + U * m) ∧
        regsVal s' (wins M.n k) < 2 * m ∧
        Keeps (.x1 :: .x2 :: .x3 :: acc M.n) s s' ∧ (k = 0 → regsVal s' (wins M.n 0) = 0)
  | 0, _, s, _, _, _, _, _, _, hB, h0 => WP.block_nil ⟨⟨0, by simp [h0, wordsVal]⟩, by rw [h0]; omega,
      ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩, fun _ => h0⟩
  | k + 1, hk, s, base, hs, hz, hm, hBR, h6, hB, h0 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (VG.Proof.Mont.AArch64.rounds_ok hn ha hb hmo ha8 hb8 hmo8 hinv hok k (by omega) hs hz hm hBR h6 hB h0)
      fun s₁ ⟨⟨U, eU⟩, hT, k₁, hz0⟩ => ?_
    have hmem : s₁.mem = s.mem := k₁.mem
    have hacc := VG.Proof.Mont.AArch64.acc_regs_lt _ hn
    have nk : ∀ r ∈ [Reg.x0, .x4, .x5, .x6, .x7, .x16, .x17],
        r ∉ Reg.x1 :: Reg.x2 :: Reg.x3 :: acc M.n := by
      intro r hr h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr h
      rcases h with h | h | h | h
      · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact absurd h (by decide)
      · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact absurd h (by decide)
      · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact absurd h (by decide)
      · have := hacc r h
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at this
    have hs₁ := hs.of_keeps k₁ (nk .x0 (by simp))
    have hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr .x7 (nk .x7 (by simp)), hz]
    have hBR₁ : VG.Proof.Mont.AArch64.BRegs s₁ base b M.n := hBR.keep hmem fun r hr => k₁.gpr r (nk r (by
      rcases VG.Proof.Mont.AArch64.bRegs_regs r hr with rfl | rfl | rfl | rfl <;> simp))
    have h6₁ : VG.Proof.Mont.AArch64.ConstOk M s₁ := h6.keep (k₁.gpr .x6 (nk .x6 (by simp)))
    refine WP.mono (VG.Proof.Mont.AArch64.round_ok hs₁ hn (i := k) (by omega) hb hmo ha8 hb8 hmo8 hz₁ (by rw [hmem, hm])
      hinv hok hBR₁ h6₁ (by rw [hmem]; exact hB) hT (fun hk0 => hz0 hk0)) fun s₂ ⟨⟨u, eu⟩, hT₂, k₂⟩ => ?_
    rw [hmem] at eu
    refine ⟨⟨U + 2 ^ (64 * k) * u, ?_⟩, hT₂, k₁.trans (k₂.mono fun q hq => ?_), fun h => absurd h (by omega)⟩
    · calc 2 ^ (64 * (k + 1)) * regsVal s₂ (wins M.n (k + 1))
          = 2 ^ (64 * k) * (2 ^ 64 * regsVal s₂ (wins M.n (k + 1))) := by
            rw [Nat.mul_succ, Nat.pow_add, Nat.mul_assoc]
        _ = 2 ^ (64 * k) * regsVal s₁ (wins M.n k) +
            2 ^ (64 * k) * (VG.Proof.Mont.word s.mem base (a + 8 * k)).toNat * wordsVal s.mem base b M.n +
            2 ^ (64 * k) * u * m := by rw [eu]; simp only [Nat.mul_add, Nat.mul_assoc]
        _ = (wordsVal s.mem base a k + 2 ^ (64 * k) * (VG.Proof.Mont.word s.mem base (a + 8 * k)).toNat) *
            wordsVal s.mem base b M.n + (U + 2 ^ (64 * k) * u) * m := by
            rw [eU, Nat.add_mul, Nat.add_mul]; omega
        _ = _ := by rw [wordsVal_succ_top]
    · simp only [List.mem_cons] at hq ⊢
      rcases hq with h | h | h | h
      any_goals simp only [h, true_or, or_true]
      exact Or.inr (Or.inr (Or.inr (VG.Proof.Mont.AArch64.wins_sub_acc hn k q h)))

end VG.Proof.Mont.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.AArch64.Csub`. -/
section

/-!
# Montgomery arithmetic on AArch64: the conditional subtraction

`csubR M ts top` reduces `ts + 2^(64 n) top < 2m` modulo `m` (`csubR_ok`):
the difference with `m` goes to the registers `dRegs n` (`diffsR_ok`, a chain
of `subs` and `sbcs`, in which the carry flag is the complement of the
borrow), the top word's subtraction leaves the carry set exactly if it does not
borrow (`flagR_ok`), and a `csel` on it selects each word (`selectsR_ok`).
-/

namespace VG.Proof.Mont.AArch64

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut Word64.subCarry_value Word64.borrow_mask)

/-! ## The differences -/

/-- `d = n + ~m + c` (`subs` with `c` true, or `sbcs` with the carry flag),
and its carry out, the complement of the borrow. -/
theorem subc_ok (s : State) (d n m : Reg) (first : Bool) {c : Bool}
    (hc : (if first then true else s.c) = c) :
    WP isa (.block [if first then .subs .x d n m else .sbcs .x d n m]) s fun s' =>
      s'.gpr d = Word64.addCarry (s.gpr n) (~~~(s.gpr m)) c ∧
      s'.c = Word64.carryOut (s.gpr n) (~~~(s.gpr m)) c ∧ Keeps [d] s s' := by
  subst hc
  apply WP.of_runBlock
  cases first <;>
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Bool.false_eq_true,
      ite_true, ite_false, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, BitVec.setWidth_eq,
      Option.some.injEq, exists_eq_left']
    refine ⟨rfl, rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_addWithCarry, hr, ite_false]

/-- `t - b` as `n + ~m + c`, with the borrow `b = !c` in and out. -/
theorem sub_borrow (a b : BitVec 64) (c : Bool) :
    (Word64.addCarry a (~~~b) c).toNat + b.toNat + (!c).toNat =
      a.toNat + 2 ^ 64 * (!Word64.carryOut a (~~~b) c).toNat := by
  have := Word64.subCarry_value a b c
  generalize Word64.carryOut a (~~~b) c = co at this ⊢
  cases c <;> cases co <;> simp only [Bool.not_true, Bool.not_false, Bool.toNat_true,
    Bool.toNat_false] at this ⊢ <;> omega

/-- The registers for the difference. -/
abbrev dPool : List Reg := [.x1, .x3, .x4, .x5, .x6, .x16]

/-- Registers for the difference: distinct, from `dPool`. -/
def DRegs (ds : List Reg) : Prop := ds.Nodup ∧ ∀ d ∈ ds, d ∈ VG.Proof.Mont.AArch64.dPool

theorem dPool_ne : ∀ d ∈ VG.Proof.Mont.AArch64.dPool, d ≠ .x2 ∧ d ≠ .x17 ∧ d ≠ .x7 ∧ d ≠ .x0 := by decide

theorem dPool_sub : ∀ d ∈ VG.Proof.Mont.AArch64.dPool, d ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17] := by
  decide

/-- A register of the pool is not a fresh one. -/
theorem dPool_fresh {d t : Reg} (hd : d ∈ VG.Proof.Mont.AArch64.dPool)
    (ht : t ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17]) : d ≠ t := fun h =>
  ht (h ▸ VG.Proof.Mont.AArch64.dPool_sub d hd)

theorem dRegs_ok : ∀ n < 7, VG.Proof.Mont.AArch64.DRegs (dRegs n) ∧ (n ≤ 6 → (dRegs n).length = n) := by
  unfold VG.Proof.Mont.AArch64.DRegs dRegs; decide

theorem DRegs.tail {d : Reg} {ds : List Reg} (h : VG.Proof.Mont.AArch64.DRegs (d :: ds)) : VG.Proof.Mont.AArch64.DRegs ds :=
  ⟨(List.nodup_cons.mp h.1).2, fun q hq => h.2 q (List.mem_cons_of_mem _ hq)⟩

/-- One word of the difference: `d = t - [mo] - b` with the borrow `b = !c` in
(`c` the carry flag, true for `subs`), and its borrow out. -/
theorem diffR1_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.AArch64.Scr s base size) (t d : Reg)
    (ht2 : t ≠ .x2) (first : Bool) {c : Bool} (hc : (if first then true else s.c) = c)
    {mo : Nat} (hmo : mo + 8 ≤ size) (hmo8 : mo % 8 = 0) :
    WP isa (.block [ld .x2 mo, if first then .subs .x d t .x2 else .sbcs .x d t .x2]) s
      fun s' => (s'.gpr d).toNat + (VG.Proof.Mont.word s.mem base mo).toNat + (!c).toNat =
          (s.gpr t).toNat + 2 ^ 64 * (!s'.c).toNat ∧ Keeps [.x2, d] s s' := by
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (VG.Proof.Mont.AArch64.ld_ok hs hmo hmo8 .x2) fun s₁ ⟨l₁, k₁, c₁⟩ => ?_
  refine WP.mono (VG.Proof.Mont.AArch64.subc_ok s₁ d t .x2 first (c := c) (by rw [c₁, hc])) fun s₂ ⟨d₂, c₂, k₂⟩ => ?_
  rw [l₁, k₁.gpr t (by simpa using ht2)] at d₂ c₂
  refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  rw [d₂, c₂]
  exact VG.Proof.Mont.AArch64.sub_borrow _ _ c

/-- The difference of the words `ts` and the words at `mo`, with the borrow
`!c` in (`c` the carry flag), into `ds`, and its borrow out. -/
theorem diffsRSbc_ok {size : Nat} : ∀ (ts ds : List Reg) {s : State} {base : Addr} {mo : Nat},
    VG.Proof.Mont.AArch64.Scr s base size → ts.length = ds.length → mo + 8 * ts.length ≤ size → mo % 8 = 0 → Fresh ts →
    VG.Proof.Mont.AArch64.DRegs ds →
    WP isa (.block (diffsR false ts ds mo)) s fun s' =>
      regsVal s' ds + wordsVal s.mem base mo ts.length + (!s.c).toNat =
        regsVal s ts + 2 ^ (64 * ts.length) * (!s'.c).toNat ∧ Keeps (.x2 :: ds) s s'
  | [], [], s, _, _, _, _, _, _, _, _ => WP.block_nil ⟨by simp [wordsVal, regsVal],
      fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | [], _ :: _, _, _, _, _, hl, _, _, _, _ => absurd hl (by simp)
  | _ :: _, [], _, _, _, _, hl, _, _, _, _ => absurd hl (by simp)
  | t :: ts, d :: ds, s, base, mo, hs, hl, hmo, hmo8, hf, hd => by
    simp only [List.length_cons] at hmo hl
    have ht2 : t ≠ .x2 := fun h => hf.head.2 (by simp [h])
    have hdP := hd.2 d (List.mem_cons_self ..)
    rw [diffsR, WP.block_append_iff]
    refine WP.mono (VG.Proof.Mont.AArch64.diffR1_ok hs t d ht2 false (c := s.c) rfl (mo := mo)
      (by omega) hmo8) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by decide, Ne.symm (VG.Proof.Mont.AArch64.dPool_ne d hdP).2.2.2⟩)
    refine WP.mono (VG.Proof.Mont.AArch64.diffsRSbc_ok ts ds hs₁ (mo := mo + 8) (by omega) (by omega) (by omega) hf.tail
      hd.tail) fun s₂ ⟨e₂, k₂⟩ => ?_
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
      have hq' := hf.tail.2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hq' (by simp [h]), fun h => VG.Proof.Mont.AArch64.dPool_fresh hdP hq' h.symm⟩)
    have hd₂ : s₂.gpr d = s₁.gpr d := k₂.gpr d (by
      simp only [List.mem_cons, not_or]
      exact ⟨(VG.Proof.Mont.AArch64.dPool_ne d hdP).1, (List.nodup_cons.mp hd.1).1⟩)
    rw [hR, k₁.mem] at e₂
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    simp only [wordsVal, regsVal, List.length_cons, pow64_succ, hd₂]
    rw [Nat.mul_assoc]
    omega

/-- The difference of the words `t :: ts` and the words at `mo` into `ds`, and
its borrow `!c` (`c` the carry flag after it). -/
theorem diffsR_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.AArch64.Scr s base size) {t : Reg}
    {ts ds : List Reg} {mo : Nat} (hl : (t :: ts).length = ds.length)
    (hmo : mo + 8 * (t :: ts).length ≤ size) (hmo8 : mo % 8 = 0) (hf : Fresh (t :: ts))
    (hd : VG.Proof.Mont.AArch64.DRegs ds) :
    WP isa (.block (diffsR true (t :: ts) ds mo)) s fun s' =>
      regsVal s' ds + wordsVal s.mem base mo (t :: ts).length =
        regsVal s (t :: ts) + 2 ^ (64 * (t :: ts).length) * (!s'.c).toNat ∧ Keeps (.x2 :: ds) s s' := by
  obtain ⟨d, ds', rfl⟩ : ∃ d ds', ds = d :: ds' := by
    cases ds with
    | nil => simp at hl
    | cons d ds' => exact ⟨d, ds', rfl⟩
  simp only [List.length_cons] at hmo hl ⊢
  have ht2 : t ≠ .x2 := fun h => hf.head.2 (by simp [h])
  have hdP := hd.2 d (List.mem_cons_self ..)
  rw [diffsR, WP.block_append_iff]
  refine WP.mono (VG.Proof.Mont.AArch64.diffR1_ok hs t d ht2 true (c := true) rfl (mo := mo)
    (by omega) hmo8) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨by decide, Ne.symm (VG.Proof.Mont.AArch64.dPool_ne d hdP).2.2.2⟩)
  refine WP.mono (VG.Proof.Mont.AArch64.diffsRSbc_ok ts ds' hs₁ (mo := mo + 8) (by omega) (by omega) (by omega) hf.tail
    hd.tail) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
    have hq' := hf.tail.2 q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun h => hq' (by simp [h]), fun h => VG.Proof.Mont.AArch64.dPool_fresh hdP hq' h.symm⟩)
  have hd₂ : s₂.gpr d = s₁.gpr d := k₂.gpr d (by
    simp only [List.mem_cons, not_or]
    exact ⟨(VG.Proof.Mont.AArch64.dPool_ne d hdP).1, (List.nodup_cons.mp hd.1).1⟩)
  rw [hR, k₁.mem] at e₂
  refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  simp only [wordsVal, regsVal, pow64_succ, hd₂]
  simp only [Bool.not_true, Bool.toNat_false, Nat.add_zero] at e₁
  rw [Nat.mul_assoc]
  omega

/-! ## The borrow and the selection -/

theorem borrow_flag (x : Nat) (c : Bool) (hx : x < 2 ^ 64) :
    decide (2 ^ 64 ≤ x + (2 ^ 64 - 1) + c.toNat) = !decide (x < (!c).toNat) := by
  cases c
  · by_cases h : x < 1
    · rw [decide_eq_false (by simp only [Bool.toNat_false]; omega), decide_eq_true (by simpa using h)]; rfl
    · rw [decide_eq_true (by simp only [Bool.toNat_false]; omega), decide_eq_false (by simpa using h)]; rfl
  · rw [decide_eq_true (by simp only [Bool.toNat_true]; omega), decide_eq_false (by simp)]; rfl

/-- The top word less the borrow `!c`: the carry is then set exactly if it
does not borrow. -/
theorem flagR_ok (s : State) (top : Reg) (hz : s.gpr .x7 = 0) :
    WP isa (.block [.sbcs .x .x2 top .x7]) s fun s' =>
      s'.c = !decide ((s.gpr top).toNat < (!s.c).toNat) ∧ Keeps [.x2] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.c_addWithCarry, hz, Option.some.injEq, exists_eq_left']
  refine ⟨VG.Proof.Mont.AArch64.borrow_flag _ _ (s.gpr top).isLt, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_addWithCarry, hr, ite_false]

/-- Each word of `ts` kept if the carry is clear (`k`), and replaced by the
word of `ds` if it is set. -/
theorem selectsR_ok : ∀ (ts ds : List Reg) {s : State} (k : Bool), ts.length = ds.length → Fresh ts →
    VG.Proof.Mont.AArch64.DRegs ds → s.c = !k →
    WP isa (.block (selectsR ts ds)) s fun s' =>
      regsVal s' ts = (if k then regsVal s ts else regsVal s ds) ∧ Keeps ts s s' ∧ s'.c = s.c
  | [], [], s, k, _, _, _, _ => WP.block_nil ⟨by cases k <;> rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  | [], _ :: _, _, _, hl, _, _, _ => absurd hl (by simp)
  | _ :: _, [], _, _, hl, _, _, _ => absurd hl (by simp)
  | t :: ts, d :: ds, s, k, hl, hf, hd, hk => by
    obtain ⟨htn, hto⟩ := hf.head
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hto
    have hdP := hd.2 d (List.mem_cons_self ..)
    have hdt : d ≠ t := VG.Proof.Mont.AArch64.dPool_fresh hdP (by simp [hto.1, hto.2.1, hto.2.2.1, hto.2.2.2.1,
                            hto.2.2.2.2.1, hto.2.2.2.2.2.1, hto.2.2.2.2.2.2.1, hto.2.2.2.2.2.2.2.1,
                            hto.2.2.2.2.2.2.2.2.1, hto.2.2.2.2.2.2.2.2.2])
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [selectsR, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.csel .x t d t]) s (fun s₁ =>
        s₁.gpr t = (if k then s.gpr t else s.gpr d) ∧ Keeps [t] s s₁ ∧ s₁.c = s.c) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
        BitVec.setWidth_eq, ite_true, Option.some.injEq, exists_eq_left', hk]
      refine ⟨by cases k <;> rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, by rw [RegUpd.c_write, hk]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_write, hr, ite_false]) fun s₁ ⟨e₁, k₁, c₁⟩ => ?_
    refine WP.mono (VG.Proof.Mont.AArch64.selectsR_ok ts ds k hl hf.tail hd.tail (c₁.trans hk)) fun s₂ ⟨e₂, k₂, c₂⟩ => ?_
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => htn (h ▸ hq))
    have hD : regsVal s₁ ds = regsVal s ds := regsVal_congr fun q hq => k₁.gpr q (by
      have hqP := hd.2 q (List.mem_cons_of_mem _ hq)
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact VG.Proof.Mont.AArch64.dPool_fresh hqP (by simp [hto.1, hto.2.1, hto.2.2.1, hto.2.2.2.1,
                              hto.2.2.2.2.1, hto.2.2.2.2.2.1, hto.2.2.2.2.2.2.1, hto.2.2.2.2.2.2.2.1,
                              hto.2.2.2.2.2.2.2.2.1, hto.2.2.2.2.2.2.2.2.2]))
    have ht₂ : s₂.gpr t = s₁.gpr t := k₂.gpr t htn
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs)), c₂.trans c₁⟩
    rw [regsVal, regsVal, regsVal, ht₂, e₁, e₂, hR, hD]
    cases k <;> rfl

/-! ## The conditional subtraction -/

/-- `csubR`: `ts + 2^(64 n) top < 2m` reduced modulo `m`, with `x7 = 0`. -/
theorem csubR_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.AArch64.Scr s base size) {M : Mod}
    {ts : List Reg} {top : Reg} (hlen : ts.length = M.n) (hn : 0 < M.n) (h7 : M.n < 7)
    (hf : Fresh (top :: ts)) (hmo : M.mo + 8 * M.n ≤ size) (hmo8 : M.mo % 8 = 0)
    (hz : s.gpr .x7 = 0) {m : Nat} (hm : wordsVal s.mem base M.mo M.n = m)
    (hV : regsVal s ts + 2 ^ (64 * M.n) * (s.gpr top).toNat < 2 * m) :
    WP isa (.block (csubR M ts top)) s fun s' =>
      regsVal s' ts = (regsVal s ts + 2 ^ (64 * M.n) * (s.gpr top).toNat) % m ∧
      Keeps (.x2 :: .x17 :: ts ++ dRegs M.n) s s' := by
  obtain ⟨t, ts', rfl⟩ : ∃ t ts', ts = t :: ts' := by
    cases ts with
    | nil => simp at hlen; omega
    | cons t ts' => exact ⟨t, ts', rfl⟩
  have hft := hf.tail
  have htop := hf.head
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at htop
  obtain ⟨hD, hDl⟩ := VG.Proof.Mont.AArch64.dRegs_ok M.n h7
  have hDl' := hDl (by omega)
  have hmX : m < 2 ^ (64 * M.n) := hm ▸ wordsVal_lt _ _ _ _
  rw [csubR, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Mont.AArch64.diffsR_ok hs (mo := M.mo) (ds := dRegs M.n) (by rw [hlen, hDl']) (by rw [hlen]; omega)
    hmo8 hft hD) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by
    intro h
    rcases List.mem_cons.mp h with h | h
    · exact absurd h (by decide)
    · exact (VG.Proof.Mont.AArch64.dPool_ne _ (hD.2 _ h)).2.2.2 rfl)
  have hz₁ : s₁.gpr .x7 = 0 := by
    rw [k₁.gpr _ (by
      intro h
      rcases List.mem_cons.mp h with h | h
      · exact absurd h (by decide)
      · exact (VG.Proof.Mont.AArch64.dPool_ne _ (hD.2 _ h)).2.2.1 rfl), hz]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Mont.AArch64.flagR_ok s₁ top hz₁) fun s₂ ⟨x₂, k₂⟩ => ?_
  have htopP : ∀ d ∈ dRegs M.n, d ≠ top := fun d hd => VG.Proof.Mont.AArch64.dPool_fresh (hD.2 d hd) (by
    simp [htop.2.1, htop.2.2.1, htop.2.2.2.1, htop.2.2.2.2.1, htop.2.2.2.2.2.1, htop.2.2.2.2.2.2.1,
      htop.2.2.2.2.2.2.2.1, htop.2.2.2.2.2.2.2.2.1, htop.2.2.2.2.2.2.2.2.2.1, htop.2.2.2.2.2.2.2.2.2.2])
  have htop₁ : s₁.gpr top = s.gpr top := k₁.gpr top (by
    intro h
    rcases List.mem_cons.mp h with h | h
    · exact htop.2.2.2.1 h
    · exact htopP _ h rfl)
  rw [htop₁] at x₂
  have hDs : ∀ q ∈ dRegs M.n, q ∉ [Reg.x2] := fun q hq hq' =>
    (VG.Proof.Mont.AArch64.dPool_ne q (hD.2 q hq)).1 (List.mem_singleton.mp hq')
  refine WP.mono (VG.Proof.Mont.AArch64.selectsR_ok _ (dRegs M.n) (decide ((s.gpr top).toNat < (!s₁.c).toNat))
    (s := s₂) (by rw [hlen, hDl']) hft hD x₂)
    fun s₃ ⟨e₃, k₃, _⟩ => ?_
  have hR₂ : regsVal s₂ (t :: ts') = regsVal s (t :: ts') := by
    rw [regsVal_congr fun q hq => k₂.gpr q (by
      have := hft.2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
      exact this.2.2.1)]
    exact regsVal_congr fun q hq => k₁.gpr q (by
      have hq' := hft.2 q hq
      intro h
      rcases List.mem_cons.mp h with h | h
      · exact hq' (by simp [h])
      · exact VG.Proof.Mont.AArch64.dPool_fresh (hD.2 _ h) hq' rfl)
  have hD₂ : regsVal s₂ (dRegs M.n) = regsVal s₁ (dRegs M.n) :=
    regsVal_congr fun q hq => k₂.gpr q (hDs q hq)
  rw [hlen] at e₁
  rw [hm] at e₁
  refine ⟨?_, ((k₁.mono (by
      intro r hr; rcases List.mem_cons.mp hr with h | h
      · subst h; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ h)))).trans
      ((k₂.mono (by sub_regs)).trans (k₃.mono fun r hr =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hr)))))⟩
  rw [e₃, hR₂, hD₂]
  simp only [decide_eq_true_eq]
  have hDlt := regsVal_lt s₁ (dRegs M.n)
  rw [hDl'] at hDlt
  exact csub_arith (b := !s₁.c) hmX hDlt hV e₁

end VG.Proof.Mont.AArch64

end
