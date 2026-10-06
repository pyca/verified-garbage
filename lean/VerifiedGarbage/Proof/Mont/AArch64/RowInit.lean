import VerifiedGarbage.Proof.Mont.AArch64.Row

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
    omega

theorem regsVal_eq_zero {s : State} : ∀ {rs : List Reg}, (∀ r ∈ rs, s.gpr r = 0) → regsVal s rs = 0
  | [], _ => rfl
  | r :: rs, h => by
    simp only [regsVal, h r (List.mem_cons_self ..),
      regsVal_eq_zero fun q hq => h q (List.mem_cons_of_mem _ hq), Nat.mul_zero, Nat.add_zero]
    rfl

/-- `t_j = x b_j mod 2⁶⁴`, into the cleared `ts`. -/
theorem mulsLo_ok {x : Reg} : ∀ (ts bs : List Reg) {s : State}, bs.length ≤ ts.length → ts.Nodup →
    (∀ t ∈ ts, t ≠ x ∧ t ∉ bs) → (∀ t ∈ ts, s.gpr t = 0) →
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
      (fun q hq => by rw [hts q hq]; exact h0 q (List.mem_cons_of_mem _ hq)))
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
  exact (List.map_congr_left fun _ _ => rfl).trans (List.map_fst_zip (by omega))

theorem mem_zip_map {tl bs : List Reg} {e : Reg × Option Piece}
    (h : e ∈ (tl.zip bs).map fun (t, r) => (t, some (Piece.hi (.reg r)))) :
    ∃ t r, t ∈ tl ∧ r ∈ bs ∧ e = (t, some (Piece.hi (.reg r))) := by
  obtain ⟨⟨t, r⟩, hm, rfl⟩ := List.mem_map.mp h
  exact ⟨t, r, List.of_mem_zip hm |>.1, List.of_mem_zip hm |>.2, rfl⟩

/-- The first row into the cleared `ts` (`n + 1` words), for the
multiplicand's `n` words in the registers `bs`: `ts = x B`. -/
theorem rowInit_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hz : s.gpr .x7 = 0)
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
  refine WP.mono (mulsLo_ok (x := x) (t0 :: tl) bs (by simp only [List.length_cons]; omega) hnd
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
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1⟩
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
  refine WP.mono (chainSkip_ok hx2 hx3 _ hs₁ hz₁ hc) fun s₂ ⟨⟨c, hc1, e₂⟩, k₂⟩ => ?_
  rw [hLf] at e₂ k₂
  rw [List.length_map, List.length_zip, hlen, Nat.min_self] at e₂
  rw [chainVal_hi _ s₁ base tl bs (by omega), hb₁, hx₁] at e₂
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
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
  · simp only [Nat.mul_zero, Nat.add_zero] at e₂
    rw [← hsum, e₂, Nat.mul_add]; omega
  · exfalso
    simp only [Nat.mul_one] at e₂
    have h3 : 2 ^ 64 * (regsVal s₂ tl + 2 ^ (64 * bs.length)) =
        2 ^ 64 * (regsVal s₁ tl + hiSum (s.gpr x).toNat (bs.map fun r => (s.gpr r).toNat)) := by
      rw [e₂]
    rw [Nat.mul_add, Nat.mul_add] at h3
    omega

end VG.Proof.Mont.AArch64
