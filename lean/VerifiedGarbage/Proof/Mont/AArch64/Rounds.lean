module

import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Mont.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Mont.AArch64.RowInit`, which this module and modules that import it used -/

section

/-!
# Montgomery arithmetic on AArch64: the first row

Into a cleared accumulator, the first row of products needs no chain for its
low words: `rowInit x ts bs` multiplies straight into `ts` (`mulsLo_ok`), and
then adds the high words one word up in a chain (`chainSkip_ok`). The low and
high words add up to `x B` (`lo_hi_sum`), which fits in `ts` (`rowInit_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.AArch64

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- `Σ_j v_j 2^(64 j)`. -/
def numVal : List Nat → Nat
  | [] => 0
  | v :: vs => v + 2 ^ 64 * numVal vs

/-- `Σ_j (x v_j mod 2⁶⁴) 2^(64 j)`. -/
def loSum (x : Nat) : List Nat → Nat
  | [] => 0
  | v :: vs => x * v % 2 ^ 64 + 2 ^ 64 * loSum x vs

/-- `Σ_j ⌊x v_j / 2⁶⁴⌋ 2^(64 j)`. -/
def hiSum (x : Nat) : List Nat → Nat
  | [] => 0
  | v :: vs => x * v / 2 ^ 64 + 2 ^ 64 * hiSum x vs

theorem lo_hi_sum (x : Nat) : ∀ vs : List Nat, loSum x vs + 2 ^ 64 * hiSum x vs = x * numVal vs
  | [] => rfl
  | v :: vs => by
    have ih := lo_hi_sum x vs
    have hd := Nat.mod_add_div (x * v) (2 ^ 64)
    simp only [loSum, hiSum, numVal, Nat.mul_add]
    rw [Nat.mul_left_comm x (2 ^ 64), ← ih, Nat.mul_add]
    omega_using []

theorem regsVal_eq_zero {s : State} : ∀ {rs : List Reg}, (∀ r ∈ rs, s.gpr r = 0) → regsVal s rs = 0
  | [], _ => rfl
  | r :: rs, h => by
    simp only [regsVal, h r (List.mem_cons_self ..),
      regsVal_eq_zero fun q hq => h q (List.mem_cons_of_mem _ hq), Nat.mul_zero, Nat.add_zero]
    rfl

/-- `t_j = x b_j mod 2⁶⁴`, into `ts`, whose words past `bs` are cleared. -/
theorem mulsLo_ok {x : Reg} : ∀ (ts bs : List Reg) {s : State}, bs.length ≤ ts.length → ts.Nodup →
    (∀ t ∈ ts, t ≠ x ∧ t ∉ bs) → (∀ t ∈ ts.drop bs.length, s.gpr t = 0) →
    WP isa (.block ((ts.zip bs).map fun (t, r) => .mul .x t x r)) s fun s' =>
      regsVal s' ts = loSum (s.gpr x).toNat (bs.map fun r => (s.gpr r).toNat) ∧ Keeps ts s s'
  | ts, [], s, _, _, _, h0 => by
    rw [List.zip_nil_right]
    exact WP.block_nil ⟨regsVal_eq_zero h0, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
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
    refine WP.mono (mulsLo_ok ts bs (s := s₁) hl (List.nodup_cons.mp hnd).2
      (fun q hq => by
        have := hx q (List.mem_cons_of_mem _ hq)
        exact ⟨this.1, fun h => this.2 (List.mem_cons_of_mem _ h)⟩)
      (fun q hq => by
        rw [hts q (List.mem_of_mem_drop hq)]; exact h0 q (by simpa only [List.length_cons, List.drop_succ_cons] using hq)))
      fun s₂ ⟨e₂, k₂⟩ => ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    have hx₁ : s₁.gpr x = s.gpr x := k₁.gpr x (by simpa using Ne.symm htx.1)
    have hbs : bs.map (fun q => (s₁.gpr q).toNat) = bs.map (fun q => (s.gpr q).toNat) :=
      List.map_congr_left fun q hq => by
        rw [k₁.gpr q (by
          simp only [List.mem_singleton]; exact fun h => htx.2 (h ▸ List.mem_cons_of_mem _ hq))]
    have ht₂ : s₂.gpr t = s₁.gpr t := k₂.gpr t htn
    simp only [regsVal, List.map_cons, loSum, ht₂, e₂, e₁, hx₁, hbs]

/-- The chain of the high words adds `⌊x b_j / 2⁶⁴⌋` at word `j`. -/
theorem chainVal_hi (x : Nat) (s : State) (base : Addr) : ∀ (ts bs : List Reg),
    bs.length ≤ ts.length →
    chainVal x s base ((ts.zip bs).map fun (t, r) => (t, some (Piece.hi (.reg r)))) =
      hiSum x (bs.map fun r => (s.gpr r).toNat)
  | _, [], _ => by simp [chainVal, hiSum]
  | [], _ :: _, h => absurd h (by simp)
  | t :: ts, r :: bs, h => by
    simp only [List.length_cons, Nat.add_le_add_iff_right] at h
    simp only [List.zip_cons_cons, List.map_cons, chainVal, optVal, Piece.val, Src.val, hiSum,
      chainVal_hi x s base ts bs h]

theorem numVal_map (s : State) : ∀ bs : List Reg, numVal (bs.map fun r => (s.gpr r).toNat) = regsVal s bs
  | [] => rfl
  | r :: bs => by simp only [List.map_cons, numVal, regsVal, numVal_map s bs]

theorem map_fst_zip_map {tl bs : List Reg} (h : tl.length = bs.length) :
    ((tl.zip bs).map fun (t, r) => (t, some (Piece.hi (.reg r)))).map Prod.fst = tl := by
  rw [List.map_map]
  exact (List.map_congr_left fun _ _ => rfl).trans (List.map_fst_zip (by omega_using [h]))

theorem mem_zip_map {tl bs : List Reg} {e : Reg × Option Piece}
    (h : e ∈ (tl.zip bs).map fun (t, r) => (t, some (Piece.hi (.reg r)))) :
    ∃ t r, t ∈ tl ∧ r ∈ bs ∧ e = (t, some (Piece.hi (.reg r))) := by
  obtain ⟨⟨t, r⟩, hm, rfl⟩ := List.mem_map.mp h
  exact ⟨t, r, List.of_mem_zip hm |>.1, List.of_mem_zip hm |>.2, rfl⟩

/-- The first row into `ts` (`n + 1` words), whose top word is cleared, for
the multiplicand's `n` words in the registers `bs`: `ts = x B`. -/
theorem rowInit_ok {s : State} {rm : Reg} {base : Addr} {size : Nat} (hs : Ptr s rm base size)
    (hz : s.gpr .x7 = 0) (hr2 : rm ≠ .x2) (hr3 : rm ≠ .x3)
    {x : Reg} {ts bs : List Reg} (hlen : ts.length = bs.length + 1) (hnd : ts.Nodup)
    (hts : ∀ t ∈ ts, t ≠ rm ∧ t ≠ .x2 ∧ t ≠ .x3 ∧ t ≠ .x7 ∧ t ≠ x ∧ t ∉ bs)
    (hbs : ∀ r ∈ bs, r ≠ .x2 ∧ r ≠ .x3) (hx2 : x ≠ .x2) (hx3 : x ≠ .x3) (htx0 : ∀ t ∈ ts, t ≠ .x0)
    (h0 : ∀ t ∈ ts.drop bs.length, s.gpr t = 0) :
    WP isa (.block (rowInit rm x ts bs)) s fun s' =>
      regsVal s' ts = (s.gpr x).toNat * regsVal s bs ∧ Keeps (.x2 :: .x3 :: ts) s s' := by
  obtain ⟨t0, tl, rfl⟩ : ∃ t0 tl, ts = t0 :: tl := by
    cases ts with
    | nil => simp at hlen
    | cons t0 tl => exact ⟨t0, tl, rfl⟩
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
  have ht0 := hts t0 (List.mem_cons_self ..)
  have ht0l : t0 ∉ tl := (List.nodup_cons.mp hnd).1
  rw [rowInit, List.tail_cons, WP.block_append_iff]
  refine WP.mono (mulsLo_ok (x := x) (t0 :: tl) bs (by simp only [List.length_cons]; omega_using [hlen]) hnd
    (fun t ht => ⟨(hts t ht).2.2.2.2.1, (hts t ht).2.2.2.2.2⟩) h0) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (fun h => (hts _ h).1 rfl)
  have hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr _ (fun h => (hts _ h).2.2.2.1 rfl), hz]
  have hx₁ : s₁.gpr x = s.gpr x := k₁.gpr x (fun h => (hts _ h).2.2.2.2.1 rfl)
  have hb₁ : bs.map (fun r => (s₁.gpr r).toNat) = bs.map (fun r => (s.gpr r).toNat) :=
    List.map_congr_left fun r hr => by rw [k₁.gpr r (fun h => (hts _ h).2.2.2.2.2 hr)]
  have hLf := map_fst_zip_map (bs := bs) hlen
  have hc : ChainOk size x ((tl.zip bs).map fun (t, r) => (t, some (Piece.hi (.reg r)))) := {
    nodup := by rw [hLf]; exact (List.nodup_cons.mp hnd).2
    regs := fun t ht => by
      rw [hLf] at ht
      have := hts t (List.mem_cons_of_mem _ ht)
      exact ⟨htx0 t (List.mem_cons_of_mem _ ht), this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1⟩
    ok := fun e he p hp => by
      obtain ⟨t, r, -, hr, rfl⟩ := mem_zip_map he
      simp only [Option.mem_def, Option.some.injEq] at hp
      subst hp
      exact hbs r hr
    reads := fun e he p hp q hq => by
      obtain ⟨t, r, -, hr, rfl⟩ := mem_zip_map he
      simp only [Option.mem_def, Option.some.injEq] at hp
      subst hp
      simp only [Piece.reads, Src.reads, Option.mem_def, Option.some.injEq] at hq
      subst hq
      rw [hLf]
      exact ⟨fun h => (hts _ (List.mem_cons_of_mem _ h)).2.2.2.2.2 hr, hbs _ hr⟩ }
  refine WP.mono (chainSkip_ok hx2 hx3 hr2 hr3 _ hs₁ hz₁ hc
    (by rw [hLf]; exact fun h => (hts _ (List.mem_cons_of_mem _ h)).1 rfl)) fun s₂ ⟨⟨c, hc1, e₂⟩, k₂⟩ => ?_
  rw [hLf] at e₂ k₂
  rw [List.length_map, List.length_zip, hlen, Nat.min_self] at e₂
  rw [chainVal_hi _ s₁ base tl bs (by omega_using [hlen]), hb₁, hx₁] at e₂
  refine ⟨?_, k₁.mono (by sub_regs) |>.trans (k₂.mono fun q hq => by
    simp only [List.mem_cons] at hq ⊢
    rcases hq with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h)))⟩
  have ht₂ : s₂.gpr t0 = s₁.gpr t0 := k₂.gpr t0 (by
    simp only [List.mem_cons, not_or]; exact ⟨ht0.2.1, ht0.2.2.1, ht0l⟩)
  have hsum := lo_hi_sum (s.gpr x).toNat (bs.map fun r => (s.gpr r).toNat)
  rw [numVal_map] at hsum

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
  rcases (by omega_using [hc1] : c = 0 ∨ c = 1) with rfl | rfl
  · simp only [Nat.mul_zero, Nat.add_zero] at e₂
    rw [← hsum, e₂, Nat.mul_add]; omega_using [e₁]
  · exfalso
    simp only [Nat.mul_one] at e₂
    have h3 : 2 ^ 64 * (regsVal s₂ tl + 2 ^ (64 * bs.length)) =
        2 ^ 64 * (regsVal s₁ tl + hiSum (s.gpr x).toNat (bs.map fun r => (s.gpr r).toNat)) := by
      rw [e₂]
    rw [Nat.mul_add, Nat.mul_add] at h3
    omega_using [e₁, hsum, hlt, e₂]

end VG.Proof.Mont.AArch64

end

end

/-! ### `Mont.AArch64.Round`, which this module and modules that import it used -/

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

@[expose] public section

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

theorem fresh_wins_lt : ∀ n < 10, ∀ i < n + 2, Fresh (wins n i) := by
  unfold Fresh; decide +kernel

theorem fresh_wins {n : Nat} (hn : n < 10) (i : Nat) : Fresh (wins n i) := by
  rw [wins_mod]; exact fresh_wins_lt n hn _ (Nat.mod_lt _ (by omega_using []))

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
    · exact ⟨j, Nat.le_refl _, by omega_using [], rfl⟩
    · obtain ⟨j', h1, h2, h3⟩ := mem_bWords h
      exact ⟨j', by omega_using [h1], by omega_using [h2], h3⟩

theorem mem_mWords {mo : Nat} : ∀ {j k : Nat} {w : RWord}, w ∈ mWords mo j k →
    ∃ j', j ≤ j' ∧ j' < j + k ∧ w = .gen (.mem (mo + 8 * j'))
  | _, 0, _, h => absurd h List.not_mem_nil
  | j, k + 1, w, h => by
    simp only [mWords, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨j, Nat.le_refl _, by omega_using [], rfl⟩
    · obtain ⟨j', h1, h2, h3⟩ := mem_mWords h
      exact ⟨j', by omega_using [h1], by omega_using [h2], h3⟩

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
    simp only [bWords, rwVal, wordsVal, RWord.val, bSrc_val hB (show j < n by omega_using [h]),
      rwVal_bWords hB (j + 1) k (by omega_using [h]), show b + 8 * (j + 1) = b + 8 * j + 8 by omega_using []]

theorem rwVal_mWords (s : State) (base : Addr) (mo : Nat) :
    ∀ j k, rwVal s base (mWords mo j k) = wordsVal s.mem base (mo + 8 * j) k
  | _, 0 => rfl
  | j, k + 1 => by
    simp only [mWords, rwVal, wordsVal, RWord.val, Src.val, rwVal_mWords s base mo (j + 1) k,
      show mo + 8 * (j + 1) = mo + 8 * j + 8 by omega_using []]

theorem fWord_val {s : State} {base : Addr} {g : Option Nat}
    (h6 : ∀ v, g = some v → s.gpr .x6 = BitVec.ofNat 64 v) {w : MWord} (hw : w.ok = true) :
    (fWord g w).val s base = w.val := by
  cases w with
  | zero => rfl
  | one => rfl
  | pow2 k => rfl
  | gen v =>
    obtain hv : v < 2 ^ 64 := by simpa [MWord.ok] using hw
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
theorem wins_regs {n : Nat} (hn : n < 10) (i : Nat) :
    ∀ r ∈ wins n i, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x5 ∧ r ≠ .x6 ∧
      r ≠ .x7 ∧ r ≠ .x16 ∧ r ≠ .x17 := by
  intro r hr
  have := (fresh_wins hn i).2 r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h16, h17, -, -⟩ := this
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h16, h17⟩

theorem bRegs_regs : ∀ r ∈ bRegs, r = .x4 ∨ r = .x5 ∨ r = .x16 ∨ r = .x17 := by decide

theorem rowOkA {size : Nat} {n b : Nat} (hn : n < 10) (hb : b + 8 * n ≤ size) (hb8 : b % 8 = 0)
    (i : Nat) : RowOk size .x1 (wins n i) (bWords b 0 n) where
  nodup := (fresh_wins hn i).1
  regs t ht := by have := wins_regs hn i t ht; exact ⟨this.1, this.2.2.1, this.2.2.2.1,
    this.2.2.2.2.2.2.2.1, this.2.1⟩
  ok w hw := by
    obtain ⟨j, -, hj, rfl⟩ := mem_bWords hw
    unfold bSrc
    cases h : bRegs[j]? with
    | none => exact ⟨by omega_using [hb, hj], by omega_using [hb8]⟩
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

theorem rowOkM {size : Nat} {n mo : Nat} (hn : n < 10) (hmo : mo + 8 * n ≤ size) (hmo8 : mo % 8 = 0)
    (i : Nat) : RowOk size .x1 (wins n i) (mWords mo 0 n) where
  nodup := (fresh_wins hn i).1
  regs t ht := by have := wins_regs hn i t ht; exact ⟨this.1, this.2.2.1, this.2.2.2.1,
    this.2.2.2.2.2.2.2.1, this.2.1⟩
  ok w hw := by
    obtain ⟨j, -, hj, rfl⟩ := mem_mWords hw
    exact ⟨by omega_using [hmo, hj], by omega_using [hmo8]⟩
  reads w hw r hr := by
    obtain ⟨j, -, hj, rfl⟩ := mem_mWords hw
    simp [RWord.reads, Src.reads] at hr
  x2 := by decide
  x3 := by decide

theorem rowOkF {size : Nat} {n : Nat} (hn : n < 10) (i : Nat) {ws : List MWord}
    (hws : ws.all MWord.ok = true) (g : Option Nat) :
    RowOk size (win n i 0) (wins n i).tail (ws.map (fWord g)) where
  nodup := (fresh_wins hn i).1.tail
  regs t ht := by
    obtain hm : t ∈ wins n i := List.mem_of_mem_tail ht
    have := wins_regs hn i t hm
    refine ⟨this.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.2.2.2.1, fun h => ?_⟩
    obtain hnd := (fresh_wins hn i).1
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

theorem RowOk.sub {size : Nat} {x : Reg} {ts ts' : List Reg} {ws : List RWord} (h : RowOk size x ts ws)
    (hs : ts'.Sublist ts) : RowOk size x ts' ws where
  nodup := hs.nodup h.nodup
  regs t ht := h.regs t (hs.subset ht)
  ok := h.ok
  reads w hw r hr := have := h.reads w hw r hr; ⟨fun h' => this.1 (hs.subset h'), this.2⟩
  x2 := h.x2
  x3 := h.x3

/-- The window as its low `n + 1` words and the rest. -/
theorem regsVal_wins_split (s : State) (n i : Nat) :
    regsVal s (wins n i) = regsVal s ((wins n i).take (n + 1)) +
      2 ^ (64 * (n + 1)) * regsVal s ((wins n i).drop (n + 1)) := by
  conv => lhs; rw [← List.take_append_drop (n + 1) (wins n i)]
  rw [regsVal_append, List.length_take, wins_length, Nat.min_eq_left (by omega_using [])]

theorem bWords_regs (b : Nat) : ∀ n ≤ 4, bWords b 0 n = (bRegs.take n).map fun r => .gen (.reg r) := by
  intro n hn
  rcases (by omega_using [hn] : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem rwVal_regs (s : State) (base : Addr) : ∀ rs : List Reg,
    rwVal s base (rs.map fun r => .gen (.reg r)) = regsVal s rs
  | [] => rfl
  | r :: rs => by simp only [List.map_cons, rwVal, RWord.val, Src.val, regsVal, rwVal_regs s base rs]

theorem wins_sub_acc_lt : ∀ n < 10, ∀ i < n + 2, ∀ r ∈ wins n i, r ∈ acc n := by decide +kernel

theorem wins_sub_acc {n : Nat} (hn : n < 10) (i : Nat) : ∀ r ∈ wins n i, r ∈ acc n := by
  rw [wins_mod]; exact wins_sub_acc_lt n hn _ (Nat.mod_lt _ (by omega_using []))

/-- A register the multiplication may load or store through: none it
writes (`x1`–`x7`, `x16`, `x17` and the accumulator). -/
structure PtrOk (n : Nat) (r : Reg) : Prop where
  regs : r ∉ [Reg.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17]
  acc : r ∉ acc n

theorem PtrOk.x1 {n : Nat} {r : Reg} (h : PtrOk n r) : r ≠ .x1 := fun e => h.regs (by simp [e])
theorem PtrOk.x2 {n : Nat} {r : Reg} (h : PtrOk n r) : r ≠ .x2 := fun e => h.regs (by simp [e])
theorem PtrOk.x3 {n : Nat} {r : Reg} (h : PtrOk n r) : r ≠ .x3 := fun e => h.regs (by simp [e])

theorem ptrOk_x0_lt : ∀ n < 10, Reg.x0 ∉ acc n := by decide

theorem ptrOk_x0 {n : Nat} (hn : n < 10) : PtrOk n .x0 := ⟨by decide, ptrOk_x0_lt n hn⟩

/-- The accumulator's value entering round `i`: zero entering the first,
which sets the words it needs (`AccInit`). -/
def accV (M : Mod) (s : State) (i : Nat) : Nat := if i = 0 then 0 else regsVal s (wins M.n i)

theorem accV_succ (M : Mod) (s : State) (i : Nat) : accV M s (i + 1) = regsVal s (wins M.n (i + 1)) :=
  ite_eq_right (Nat.succ_ne_zero i)

theorem accV_of_pos (M : Mod) (s : State) {i : Nat} (h : 0 < i) : accV M s i = regsVal s (wins M.n i) :=
  ite_eq_right (Nat.pos_iff_ne_zero.mp h)

/-- The accumulator entering the first round: its top two words cleared, and
all of it unless the first row writes the others (`rowInit`, for `n ≤ 4`). -/
structure AccInit (M : Mod) (s : State) : Prop where
  top : ∀ r ∈ (wins M.n 0).drop M.n, s.gpr r = 0
  all : ¬ M.n ≤ 4 → regsVal s (wins M.n 0) = 0

/-- `x1 = a_i` and `T += a_i B`: the first row straight into the
accumulator, or a row into the window (its low `n + 1` words for a tight
modulus). -/
theorem prodRow_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    (hn : M.n < 10) {ra rb : Reg} {pa pb : Addr} {sa sb : Nat} (hpa : Ptr s ra pa sa)
    (hpb : Ptr s rb pb sb) (hrb : PtrOk M.n rb)
    {a b i m : Nat} (ha : a + 8 * i + 8 ≤ sa) (hb : b + 8 * M.n ≤ sb)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hz : s.gpr .x7 = 0) (hBR : BRegs s pb b M.n)
    (hm : m < 2 ^ (64 * M.n)) (hok : M.ok m = true) (hB : wordsVal s.mem pb b M.n < m)
    (hT : accV M s i < 2 * m) (h0 : i = 0 → AccInit M s) :
    WP isa (.block (prodRow M ra rb a b i)) s
      fun s' => regsVal s' (wins M.n i) = accV M s i +
          (word s.mem pa (a + 8 * i)).toNat * wordsVal s.mem pb b M.n ∧
        Keeps (.x1 :: .x2 :: .x3 :: wins M.n i) s s' := by
  obtain hw := wins_regs hn i
  rw [prodRow, WP.block_append_iff]
  refine WP.mono (ldR_ok hpa ha (by omega_using [ha8]) .x1) fun s₁ ⟨c₁, k₁, _⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  obtain hpb₁ := hpb.of_keeps k₁ (by simpa using hrb.x1)
  obtain hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr .x7 (by decide), hz]
  obtain hT₁ : ∀ ts : List Reg, (∀ q ∈ ts, q ∈ wins M.n i) → regsVal s₁ ts = regsVal s ts :=
    fun ts hts => regsVal_congr fun q hq => k₁.gpr q (by simp [(hw q (hts q hq)).2.1])
  obtain hBR₁ : BRegs s₁ pb b M.n := hBR.keep k₁.mem fun r hr => k₁.gpr r (by
    rcases bRegs_regs r hr with rfl | rfl | rfl | rfl <;> decide)
  obtain hRB : rwVal s₁ pb (bWords b 0 M.n) = wordsVal s.mem pb b M.n := by
    rw [rwVal_bWords hBR₁ 0 M.n (by omega_using []), k₁.mem]; rfl
  obtain hA := (word s.mem pa (a + 8 * i)).isLt
  obtain hAB : (word s.mem pa (a + 8 * i)).toNat * wordsVal s.mem pb b M.n ≤ (2 ^ 64 - 1) * m :=
    Nat.mul_le_mul (by omega_using []) (by omega_using [hB])
  obtain hlen : (wins M.n i).length = M.n + 2 := wins_length M.n i
  obtain htake : ∀ q ∈ (wins M.n i).take (M.n + 1), q ∈ wins M.n i := fun q hq => List.mem_of_mem_take hq
  obtain hdrop : ∀ q ∈ (wins M.n i).drop (M.n + 1), q ∈ wins M.n i := fun q hq => List.mem_of_mem_drop hq
  obtain hnd := (fresh_wins hn i).1
  obtain hdisj : ∀ q ∈ (wins M.n i).drop (M.n + 1), q ∉ (wins M.n i).take (M.n + 1) := fun q hq ht => by
    obtain hnd' : ((wins M.n i).take (M.n + 1) ++ (wins M.n i).drop (M.n + 1)).Nodup := by
      rw [List.take_append_drop]; exact hnd
    exact (List.nodup_append.mp hnd').2.2 q ht q hq rfl
  obtain hP1 : 2 ^ (64 * (M.n + 1)) = 2 ^ (64 * M.n) * 2 ^ 64 := by
    rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
  obtain hmP : (2 ^ 64 - 1) * m ≤ 2 ^ (64 * M.n) * 2 ^ 64 := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega_using [hm]) (by omega_using [])
  -- A row into the low `n + 1` words leaves the rest.
  obtain rest : ∀ t : State, (∀ q ∈ (wins M.n i).drop (M.n + 1), t.gpr q = s₁.gpr q) →
      regsVal t ((wins M.n i).take (M.n + 1)) = regsVal s ((wins M.n i).take (M.n + 1)) +
        (word s.mem pa (a + 8 * i)).toNat * wordsVal s.mem pb b M.n →
      regsVal t (wins M.n i) = regsVal s (wins M.n i) +
        (word s.mem pa (a + 8 * i)).toNat * wordsVal s.mem pb b M.n := by
    intro t hd ht
    rw [regsVal_wins_split t, regsVal_wins_split s, ht, regsVal_congr hd, hT₁ _ hdrop]
    omega_using []
  by_cases hi : i = 0 ∧ M.n ≤ 4
  · rw [ite_eq_left_iff.mpr (fun h => absurd hi h)]
    obtain ⟨rfl, hn4⟩ := hi
    obtain hz0 := (h0 rfl).top
    obtain hbl : (bRegs.take M.n).length = M.n := by
      rw [List.length_take]; exact Nat.min_eq_left (by simp [bRegs]; omega_using [hn4])
    obtain hbs : ∀ r ∈ bRegs.take M.n, r ∈ bRegs := fun r hr => List.mem_of_mem_take hr
    refine WP.mono (rowInit_ok hs₁.ptr hz₁ (by decide) (by decide) (x := .x1) (ts := (wins M.n 0).take (M.n + 1))
      (bs := bRegs.take M.n) (by rw [List.length_take, wins_length, hbl]; omega_using [])
      ((List.take_sublist _ _).nodup hnd)
      (fun t ht => by
        have := hw t (htake t ht)
        refine ⟨this.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.2.2.2.1, this.2.1, fun hb' => ?_⟩
        rcases bRegs_regs t (hbs t hb') with rfl | rfl | rfl | rfl <;> simp at this)
      (fun r hr => by rcases bRegs_regs r (hbs r hr) with rfl | rfl | rfl | rfl <;> decide)
      (by decide) (by decide) (fun t ht => (hw t (htake t ht)).1)
      (fun t ht => by
        rw [hbl, List.drop_take] at ht
        obtain ht' := List.mem_of_mem_take ht
        rw [k₁.gpr t (by simp [(hw t (List.mem_of_mem_drop ht')).2.1])]; exact hz0 t ht'))
      fun s₂ ⟨e₂, k₂⟩ => ⟨by
        obtain hd : regsVal s₂ ((wins M.n 0).drop (M.n + 1)) = 0 := regsVal_eq_zero fun q hq => by
          have := hw q (hdrop q hq)
          rw [k₂.gpr q (by simp only [List.mem_cons, not_or]; exact ⟨this.2.2.1, this.2.2.2.1, hdisj q hq⟩),
            k₁.gpr q (by simp [this.2.1])]
          exact hz0 q ((List.drop_sublist_drop_left _ (Nat.le_succ _)).subset hq)
        rw [regsVal_wins_split s₂, hd, e₂, c₁, ← rwVal_regs s₁ pb, ← bWords_regs b M.n hn4, hRB]
        simp only [accV, ↓reduceIte, Nat.mul_zero, Nat.add_zero, Nat.zero_add], (k₁.mono (by sub_regs)).trans (k₂.mono fun q hq => by
          simp only [List.mem_cons] at hq ⊢
          rcases hq with h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (htake q h))))⟩
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hi), prodWins]
    obtain hV : accV M s i = regsVal s (wins M.n i) := by
      unfold accV
      split
      · next h => subst h; exact ((h0 rfl).all fun h4 => hi ⟨rfl, h4⟩).symm
      · rfl
    rw [hV] at hT ⊢
    by_cases ht : M.tight = true
    · rw [ite_eq_left_iff.mpr (fun h => absurd ht h)]
      obtain hti := Mod.ok_tight hok ht
      obtain hRT : regsVal s ((wins M.n i).take (M.n + 1)) < 2 * m := by
        have := regsVal_wins_split s M.n i; omega_using [hT, this]
      refine WP.mono (row_ok hpb₁ hz₁ ((rowOkA hn hb hb8 i).sub (List.take_sublist _ _))
          hrb.x2 hrb.x3 (fun h => hrb.acc (wins_sub_acc hn i _ (List.mem_of_mem_take h)))
          (by rw [bWords_length, List.length_take, hlen]; omega_using []) (by
            rw [hT₁ _ htake, c₁, hRB, List.length_take, hlen, Nat.min_eq_left (by omega_using [])]
            omega_using [hAB, hti, hRT])) fun s₂ ⟨e₂, k₂⟩ =>
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
      obtain hP : 2 ^ (64 * (M.n + 2)) = 2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64 := by
        rw [show 64 * (M.n + 2) = 64 * M.n + 64 + 64 by omega_using [], Nat.pow_add, Nat.pow_add]
      refine WP.mono (row_ok hpb₁ hz₁ (rowOkA hn hb hb8 i) hrb.x2 hrb.x3
          (fun h => hrb.acc (wins_sub_acc hn i _ h)) (by rw [bWords_length, hlen]; omega_using []) (by
          rw [hT₁ _ (fun _ h => h), c₁, hRB, hlen, hP]; omega_using [hT, hAB, hmP])) fun s₂ ⟨e₂, k₂⟩ => ?_
      refine ⟨by rw [e₂, hT₁ _ (fun _ h => h), c₁, hRB],
        (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩

/-- Round `i` of the multiplication, with `x7 = 0`, `[b]`'s words in
`bRegs` and the reduction's constant in `x6`: `2⁶⁴ T' = T + a_i B + u m`,
and `T' < 2m` if `T < 2m`. -/
theorem round_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    (hn : M.n < 10) {ra rb : Reg} {pa pb : Addr} {sa sb : Nat} (hpa : Ptr s ra pa sa)
    (hpb : Ptr s rb pb sb) (hrb : PtrOk M.n rb)
    {a b i m : Nat} (ha : a + 8 * i + 8 ≤ sa) (hb : b + 8 * M.n ≤ sb)
    (hmo : M.mo + 8 * M.n ≤ size) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hmo8 : M.mo % 8 = 0)
    (hz : s.gpr .x7 = 0) (hm : wordsVal s.mem base M.mo M.n = m)
    (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) (hok : M.ok m = true)
    (hBR : BRegs s pb b M.n) (h6 : ConstOk M s) (hB : wordsVal s.mem pb b M.n < m)
    (hT : accV M s i < 2 * m) (h0 : i = 0 → AccInit M s) :
    WP isa (.block (round M ra rb a b i)) s fun s' =>
      (∃ u, 2 ^ 64 * regsVal s' (wins M.n (i + 1)) = accV M s i +
        (word s.mem pa (a + 8 * i)).toNat * wordsVal s.mem pb b M.n + u * m) ∧
      regsVal s' (wins M.n (i + 1)) < 2 * m ∧
      Keeps (.x1 :: .x2 :: .x3 :: wins M.n i) s s' := by
  obtain hred := Mod.ok_red hok
  obtain hw := wins_regs hn i
  obtain n0 : Reg.x0 ∉ wins M.n i := fun h => (hw _ h).1 rfl
  obtain n6 : Reg.x6 ∉ wins M.n i := fun h => (hw _ h).2.2.2.2.2.2.1 rfl
  obtain n7 : Reg.x7 ∉ wins M.n i := fun h => (hw _ h).2.2.2.2.2.2.2.1 rfl
  obtain hm' : m < 2 ^ (64 * M.n) := hm ▸ wordsVal_lt _ _ _ _
  obtain hcons := wins_cons M.n i
  obtain ht0 : win M.n i 0 ∈ wins M.n i := by rw [hcons]; exact List.mem_cons_self ..
  obtain hlen : (wins M.n i).length = M.n + 2 := wins_length M.n i
  obtain hP : 2 ^ (64 * (M.n + 2)) = 2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64 := by
    rw [show 64 * (M.n + 2) = 64 * M.n + 64 + 64 by omega_using [], Nat.pow_add, Nat.pow_add]
  obtain hmP : (2 ^ 64 - 1) * m ≤ 2 ^ (64 * M.n) * 2 ^ 64 := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega_using [hm']) (by omega_using [])
  obtain hAB : (word s.mem pa (a + 8 * i)).toNat * wordsVal s.mem pb b M.n ≤ (2 ^ 64 - 1) * m :=
    Nat.mul_le_mul (by have := (word s.mem pa (a + 8 * i)).isLt; omega_using []) (by omega_using [hB])
  -- The window after the round, from its value `V` with a zero low word.
  obtain hrot : ∀ t : State, (t.gpr (win M.n i 0)).toNat = 0 →
      2 ^ 64 * regsVal t (wins M.n (i + 1)) = regsVal t (wins M.n i) := by
    intro t h0
    rw [wins_succ, regsVal_append, hcons, regsVal]
    simp only [regsVal, h0, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  cases hr : M.red with
  | general =>
    obtain hcode : round M ra rb a b i = prodRow M ra rb a b i ++
        (([.mul .x .x1 (win M.n i 0) .x6] : List Instr) ++ row .x0 .x1 (wins M.n i) (mWords M.mo 0 M.n)) := by
      simp only [round, hr, List.cons_append, List.nil_append]
    obtain h6' : s.gpr .x6 = M.minv := by unfold ConstOk at h6; rw [hr] at h6; exact h6
    rw [hcode, WP.block_append_iff]
    refine WP.mono (prodRow_ok hs hn hpa hpb hrb ha hb ha8 hb8 hz hBR hm' hok hB hT h0) fun s₂ ⟨e₂, k₂⟩ => ?_
    obtain hs₂ := hs.of_keeps k₂ (by simp [n0])
    obtain hz₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (by simp [n7]), hz]
    obtain h6₂ : s₂.gpr .x6 = M.minv := by
      rw [k₂.gpr _ (by simp [n6]), h6']
    rw [WP.block_append_iff]
    refine WP.mono (mulU_ok s₂ (win M.n i 0)) fun s₃ ⟨u₃, k₃⟩ => ?_
    obtain hs₃ := hs₂.of_keeps k₃ (by decide)
    obtain hz₃ : s₃.gpr .x7 = 0 := by rw [k₃.gpr .x7 (by decide), hz₂]
    obtain hT₃ : regsVal s₃ (wins M.n i) = regsVal s₂ (wins M.n i) := regsVal_congr fun q hq =>
      k₃.gpr q (by simp [(hw q hq).2.1])
    obtain hmem₃ : s₃.mem = s.mem := by rw [k₃.mem, k₂.mem]
    obtain hu := (s₃.gpr .x1).isLt
    obtain hum : (s₃.gpr .x1).toNat * m ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul (by omega_using []) (Nat.le_refl _)
    obtain hRM : rwVal s₃ base (mWords M.mo 0 M.n) = m := by
      rw [rwVal_mWords, hmem₃, Nat.mul_zero, Nat.add_zero, hm]
    refine WP.mono (row_ok hs₃.ptr hz₃ (rowOkM hn hmo hmo8 i) (by decide) (by decide) n0 (by rw [mWords_length, hlen]; omega_using []) (by
        rw [hT₃, e₂, hRM, hlen, hP]; omega_using [hT, hmP, hAB, hum])) fun s₄ ⟨e₄, k₄⟩ => ?_
    rw [hT₃, e₂, hRM] at e₄
    -- The low word is zero.
    obtain ht0₂ : (regsVal s₂ (wins M.n i)) % 2 ^ 64 = (s₂.gpr (win M.n i 0)).toNat := by
      rw [hcons, regsVal]; omega_using []
    obtain h₄ : (regsVal s₄ (wins M.n i)) % 2 ^ 64 = (s₄.gpr (win M.n i 0)).toNat := by
      rw [hcons, regsVal]; omega_using []
    obtain hlow : (s₄.gpr (win M.n i 0)).toNat = 0 := by
      obtain h := mont_low (s₂.gpr (win M.n i 0)).toNat M.minv.toNat m hinv
      rw [h6₂] at u₃
      rw [← u₃] at h
      rw [← h₄, e₄]
      omega_using [e₂, ht0₂, h]
    refine ⟨⟨(s₃.gpr .x1).toNat, by rw [hrot s₄ hlow, e₄]⟩, ?_, ?_⟩
    · have : 2 ^ 64 * regsVal s₄ (wins M.n (i + 1)) < 2 ^ 64 * (2 * m) := by
        rw [hrot s₄ hlow, e₄]; omega_using [hT, hAB, hum]
      exact Nat.lt_of_mul_lt_mul_left this
    · exact (k₂.trans (k₃.mono (by sub_regs))).trans (k₄.mono (by sub_regs))
  | friendly ws =>
    obtain hcode : round M ra rb a b i = prodRow M ra rb a b i ++
        (row .x0 (win M.n i 0) (wins M.n i).tail (ws.map (fWord (firstGen ws))) ++
          ([.movz .x (win M.n i 0) 0 0] : List Instr)) := by
      simp only [round, hr]
    have hok := hred
    rw [hr] at hok
    simp only [Red.ok, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨hwl, hm1⟩, hmv⟩, hwok⟩ := hok
    obtain h6' : ∀ v, firstGen ws = some v → s.gpr .x6 = BitVec.ofNat 64 v := by
      unfold ConstOk at h6; rw [hr] at h6; exact h6
    -- `2⁶⁴ m' = m + 1`.
    obtain hm2 : 2 ^ 64 * mwVal ws = m + 1 := by
      rw [hmv]
      have := Nat.div_add_mod (m + 1) (2 ^ 64)
      have : (m + 1) % 2 ^ 64 = 0 := by omega_using [hm1]
      omega_using [this]
    rw [hcode, WP.block_append_iff]
    refine WP.mono (prodRow_ok hs hn hpa hpb hrb ha hb ha8 hb8 hz hBR hm' hok hB hT h0) fun s₂ ⟨e₂, k₂⟩ => ?_
    obtain hs₂ := hs.of_keeps k₂ (by simp [n0])
    obtain hz₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (by simp [n7]), hz]
    obtain h6₂ : ∀ v, firstGen ws = some v → s₂.gpr .x6 = BitVec.ofNat 64 v := fun v hv => by
      rw [k₂.gpr _ (by simp [n6]), h6' v hv]
    obtain hRF : rwVal s₂ base (ws.map (fWord (firstGen ws))) = mwVal ws := rwVal_fWords h6₂ ws hwok
    -- The window as its low word and the rest.
    obtain hsplit : ∀ t : State, regsVal t (wins M.n i) =
        (t.gpr (win M.n i 0)).toNat + 2 ^ 64 * regsVal t (wins M.n i).tail := by
      intro t; rw [hcons]; rfl
    obtain htl : (wins M.n i).tail.length = M.n + 1 := by rw [wins_tail]; simp
    obtain hPt : 2 ^ (64 * (M.n + 1)) = 2 ^ (64 * M.n) * 2 ^ 64 := by
      rw [show 64 * (M.n + 1) = 64 * M.n + 64 by omega_using [], Nat.pow_add]
    obtain hS := hsplit s₂
    obtain ht0v := (s₂.gpr (win M.n i 0)).isLt
    obtain htm : (s₂.gpr (win M.n i 0)).toNat * m ≤ (2 ^ 64 - 1) * m :=
      Nat.mul_le_mul (by omega_using []) (Nat.le_refl _)
    -- `2⁶⁴ (R + t₀ m') = S + t₀ m`, for the window's value `S = t₀ + 2⁶⁴ R`.
    obtain hkey : 2 ^ 64 * (regsVal s₂ (wins M.n i).tail + (s₂.gpr (win M.n i 0)).toNat * mwVal ws) =
        regsVal s₂ (wins M.n i) + (s₂.gpr (win M.n i 0)).toNat * m := by
      rw [Nat.mul_add, Nat.mul_left_comm, hm2, Nat.mul_add, Nat.mul_one, hS]; omega_using []
    rw [WP.block_append_iff]
    refine WP.mono (row_ok hs₂.ptr hz₂ (rowOkF hn i hwok (firstGen ws)) (by decide) (by decide)
        (fun h => n0 (List.mem_of_mem_tail h)) (by
        rw [List.length_map, hwl, htl]; omega_using []) (by
        rw [hRF, htl, hPt]
        have : 2 ^ 64 * (regsVal s₂ (wins M.n i).tail + (s₂.gpr (win M.n i 0)).toNat * mwVal ws) <
            2 ^ 64 * (2 ^ (64 * M.n) * 2 ^ 64) := by
          rw [hkey, e₂]; omega_using [hT, hmP, hAB, htm]
        exact Nat.lt_of_mul_lt_mul_left this)) fun s₃ ⟨e₃, k₃⟩ => ?_
    rw [hRF] at e₃
    refine WP.mono (movz0_ok s₃ (win M.n i 0)) fun s₄ ⟨z₄, k₄⟩ => ?_
    have htl₄ : regsVal s₄ (wins M.n i).tail = regsVal s₃ (wins M.n i).tail := regsVal_congr
      fun q hq => k₄.gpr q (by
        obtain hnd := (fresh_wins hn i).1
        rw [hcons] at hnd
        simp only [List.mem_singleton]
        intro h; subst h
        exact (List.nodup_cons.mp hnd).1 (by rw [← wins_tail]; exact hq))
    obtain hval : 2 ^ 64 * regsVal s₄ (wins M.n (i + 1)) = regsVal s₂ (wins M.n i) +
        (s₂.gpr (win M.n i 0)).toNat * m := by
      rw [wins_succ, regsVal_append, ← wins_tail, htl, htl₄, e₃]
      simp only [regsVal, z₄, Nat.mul_zero, Nat.add_zero]
      exact hkey
    refine ⟨⟨(s₂.gpr (win M.n i 0)).toNat, by rw [hval, e₂]⟩, ?_, ?_⟩
    · have : 2 ^ 64 * regsVal s₄ (wins M.n (i + 1)) < 2 ^ 64 * (2 * m) := by
        rw [hval, e₂]; omega_using [hT, hAB, htm]
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

end

/-!
# Montgomery arithmetic on AArch64: the rounds of the multiplication

The accumulator cleared (`zeros_ok`), then `k` rounds (`rounds_ok`):
`2^(64 k) T = [a]_k B + U m` for some `U`, with `T < 2m`.
-/

@[expose] public section

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
    refine WP.mono (zeros_ok s₁ ts) fun s₂ ⟨z₂, k₂⟩ => ⟨fun q hq => ?_, (k₁.mono (by sub_regs)).trans
      (k₂.mono (by sub_regs))⟩
    by_cases hqt : q ∈ ts
    · exact z₂ q hqt
    · have : q = t := by simpa [hqt] using hq
      subst this; rw [k₂.gpr _ hqt, z₁]

theorem acc_regs_lt : ∀ n < 10, ∀ r ∈ acc n,
    r ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17, .x24, .x25] := by
  decide

/-- `k` rounds, from an accumulator ready for the first (`AccInit`), with `x7 = 0`, `[b]`'s words in
`bRegs` and the reduction's constant in `x6`. -/
theorem rounds_ok {M : Mod} (hn : M.n < 10) {ra rb : Reg} {pa pb : Addr} {sa sb : Nat}
    (hra : PtrOk M.n ra) (hrb : PtrOk M.n rb) {a b m size : Nat}
    (ha : a + 8 * M.n ≤ sa) (hb : b + 8 * M.n ≤ sb) (hmo : M.mo + 8 * M.n ≤ size)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hmo8 : M.mo % 8 = 0)
    (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) (hok : M.ok m = true) :
    ∀ k ≤ M.n, ∀ {s : State} {base : Addr}, Scr s base size → Ptr s ra pa sa → Ptr s rb pb sb →
      s.gpr .x7 = 0 →
      wordsVal s.mem base M.mo M.n = m → BRegs s pb b M.n → ConstOk M s →
      wordsVal s.mem pb b M.n < m → AccInit M s →
      WP isa (.block ((List.range k).flatMap (round M ra rb a b))) s fun s' =>
        (∃ U, 2 ^ (64 * k) * accV M s' k =
          wordsVal s.mem pa a k * wordsVal s.mem pb b M.n + U * m) ∧
        accV M s' k < 2 * m ∧
        Keeps (.x1 :: .x2 :: .x3 :: acc M.n) s s' ∧ (k = 0 → AccInit M s')
  | 0, _, s, _, _, _, _, _, _, _, _, hB, h0 => WP.block_nil ⟨⟨0, by simp [accV, wordsVal]⟩, by
      simp only [accV, ↓reduceIte]; omega_arith, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩, fun _ => h0⟩
  | k + 1, hk, s, base, hs, hpa, hpb, hz, hm, hBR, h6, hB, h0 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (rounds_ok hn hra hrb ha hb hmo ha8 hb8 hmo8 hinv hok k (by omega_arith) hs hpa hpb hz hm hBR h6 hB h0)
      fun s₁ ⟨⟨U, eU⟩, hT, k₁, hz0⟩ => ?_
    have hmem : s₁.mem = s.mem := k₁.mem
    have hacc := acc_regs_lt _ hn
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
    have pk : ∀ r, PtrOk M.n r → r ∉ Reg.x1 :: Reg.x2 :: Reg.x3 :: acc M.n := fun r hr h => by
      simp only [List.mem_cons] at h
      rcases h with h | h | h | h
      · exact hr.x1 h
      · exact hr.x2 h
      · exact hr.x3 h
      · exact hr.acc h
    have hpa₁ := hpa.of_keeps k₁ (pk ra hra)
    have hpb₁ := hpb.of_keeps k₁ (pk rb hrb)
    have hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr .x7 (nk .x7 (by simp)), hz]
    have hBR₁ : BRegs s₁ pb b M.n := hBR.keep hmem fun r hr => k₁.gpr r (nk r (by
      rcases bRegs_regs r hr with rfl | rfl | rfl | rfl <;> simp))
    have h6₁ : ConstOk M s₁ := h6.keep (k₁.gpr .x6 (nk .x6 (by simp)))
    refine WP.mono (round_ok hs₁ hn hpa₁ hpb₁ hrb (i := k) (by omega_arith) hb hmo ha8 hb8 hmo8 hz₁ (by rw [hmem, hm])
      hinv hok hBR₁ h6₁ (by rw [hmem]; exact hB) hT (fun hk0 => hz0 hk0)) fun s₂ ⟨⟨u, eu⟩, hT₂, k₂⟩ => ?_
    rw [hmem] at eu
    rw [accV_succ]
    refine ⟨⟨U + 2 ^ (64 * k) * u, ?_⟩, hT₂, k₁.trans (k₂.mono fun q hq => ?_), fun h => absurd h (by omega_arith)⟩
    · calc 2 ^ (64 * (k + 1)) * regsVal s₂ (wins M.n (k + 1))
          = 2 ^ (64 * k) * (2 ^ 64 * regsVal s₂ (wins M.n (k + 1))) := by
            rw [Nat.mul_succ, Nat.pow_add, Nat.mul_assoc]
        _ = 2 ^ (64 * k) * accV M s₁ k +
            2 ^ (64 * k) * (word s.mem pa (a + 8 * k)).toNat * wordsVal s.mem pb b M.n +
            2 ^ (64 * k) * u * m := by rw [eu]; simp only [Nat.mul_add, Nat.mul_assoc]
        _ = (wordsVal s.mem pa a k + 2 ^ (64 * k) * (word s.mem pa (a + 8 * k)).toNat) *
            wordsVal s.mem pb b M.n + (U + 2 ^ (64 * k) * u) * m := by
            rw [eU, Nat.add_mul, Nat.add_mul]; omega_arith
        _ = _ := by rw [wordsVal_succ_top]
    · simp only [List.mem_cons] at hq ⊢
      rcases hq with h | h | h | h
      any_goals simp only [h, true_or, or_true]
      exact Or.inr (Or.inr (Or.inr (wins_sub_acc hn k q h)))

end VG.Proof.Mont.AArch64
