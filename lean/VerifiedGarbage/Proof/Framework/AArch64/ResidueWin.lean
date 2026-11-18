module

public import VerifiedGarbage.Proof.Framework.AArch64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.AArch64.MemEffect
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# Which bytes of the window the two runs agree on (AArch64)

`rtaintG W` is `rtaintF W` (`ResidueFrame.lean`) that also keeps, as a bit
mask over the window (`P`), which of its bytes hold the same in both runs,
and which registers hold the address of a byte of it (`ptrs`), from the
stack pointer (`add xd, sp, #imm`) and offsets of them. A store through the
stack pointer or one of them, of a register public in the analysis, makes
the bytes it writes agree; of a secret one, not. A store elsewhere of a
public register writes the same bytes at the same address in both runs,
and keeps every byte that agreed; of a secret one, the analysis forgets the
whole mask. A frame's release keeps them: the unknowns replace a byte in
both runs alike. So at the end, the bytes of the window that may differ
are those whose bit is clear, and only their 16-byte granules need zeroing
(`withScrubG`).
-/

@[expose] public section

namespace VG.AArch64.RTaintG

open VG.AArch64 VG.AArch64.Residue VG.AArch64.MemEffect VG.AArch64.RTaintF

/-! ## Bit masks -/

/-- The `w` low bits. -/
def ones (w : Nat) : Nat := 2 ^ w - 1

/-- `b` with its `w` bits from bit `d` set. -/
def bset (b d w : Nat) : Nat := b ||| (ones w <<< d)

/-- `b` with its `w` bits from bit `d` cleared. -/
def bclr (b d w : Nat) : Nat := b ^^^ (b &&& (ones w <<< d))

theorem testBit_ones (w k : Nat) : (ones w).testBit k = decide (k < w) := Nat.testBit_two_pow_sub_one w k

theorem testBit_bset (b d w k : Nat) :
    (bset b d w).testBit k = (b.testBit k || (decide (d ≤ k) && decide (k < d + w))) := by
  simp only [bset, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_ones]
  congr 1
  by_cases h : d ≤ k
  · simp only [ge_iff_le, h, decide_true, Bool.true_and, decide_eq_decide]; omega
  · simp only [ge_iff_le, h, decide_false, Bool.false_and]

theorem testBit_bclr (b d w k : Nat) :
    (bclr b d w).testBit k = (b.testBit k && !(decide (d ≤ k) && decide (k < d + w))) := by
  simp only [bclr, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft, testBit_ones]
  have : (decide (k ≥ d) && decide (k - d < w)) = (decide (d ≤ k) && decide (k < d + w)) := by
    by_cases h : d ≤ k
    · simp only [ge_iff_le, h, decide_true, Bool.true_and, decide_eq_decide]; omega
    · simp only [ge_iff_le, h, decide_false, Bool.false_and]
  rw [this]
  cases b.testBit k <;> cases (decide (d ≤ k) && decide (k < d + w)) <;> rfl

/-! ## Stores into the window -/

theorem off_sub {w : Addr} {o o' : Nat} (h₁ : o ≤ o') (h₂ : o' < 2 ^ 64) :
    (w + BitVec.ofNat 64 o' - (w + BitVec.ofNat 64 o)).toNat = o' - o := by
  rw [show w + BitVec.ofNat 64 o' - (w + BitVec.ofNat 64 o) = BitVec.ofNat 64 o' - BitVec.ofNat 64 o by
    rw [← BitVec.sub_sub, BitVec.add_sub_comm, BitVec.sub_self, BitVec.zero_add]]
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt h₂, Nat.mod_eq_of_lt (show o < 2 ^ 64 by omega)]
  omega

theorem off_sub_lt {w : Addr} {o o' : Nat} (h₁ : o' < o) (h₂ : o < 2 ^ 64) :
    2 ^ 64 - o ≤ (w + BitVec.ofNat 64 o' - (w + BitVec.ofNat 64 o)).toNat := by
  rw [show w + BitVec.ofNat 64 o' - (w + BitVec.ofNat 64 o) = BitVec.ofNat 64 o' - BitVec.ofNat 64 o by
    rw [← BitVec.sub_sub, BitVec.add_sub_comm, BitVec.sub_self, BitVec.zero_add]]
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt h₂, Nat.mod_eq_of_lt (show o' < 2 ^ 64 by omega)]
  omega

/-- A write of `n` bytes at `w + o`, within the window's `W` bytes, read at `w + o'`. -/
theorem write_at {w : Addr} {o o' n W : Nat} (hW : W < 2 ^ 64) (ho : o + n ≤ W) (ho' : o' < W)
    (m : Mem) (v : BitVec (8 * n)) :
    (m.write (w + BitVec.ofNat 64 o) n v) (w + BitVec.ofNat 64 o') =
      if o ≤ o' ∧ o' < o + n then v.extractLsb' (8 * (o' - o)) 8 else m (w + BitVec.ofNat 64 o') := by
  simp only [Mem.write]
  by_cases h₁ : o ≤ o'
  · rw [off_sub h₁ (by omega)]
    by_cases h₂ : o' < o + n
    · simp only [show o' - o < n by omega, ↓reduceIte, h₁, h₂, and_self]
    · simp only [show ¬ o' - o < n by omega, ↓reduceIte, h₂, and_false]
  · have := off_sub_lt (w := w) (show o' < o by omega) (show o < 2 ^ 64 by omega)
    simp only [show ¬ (w + BitVec.ofNat 64 o' - (w + BitVec.ofNat 64 o)).toNat < n by omega,
      ↓reduceIte, h₁, false_and]

/-! ## What the analysis keeps of the window -/

/-- The offset in the window of a store's base. -/
def offOf (W d : Nat) (ptrs : List (Reg × Nat)) : Base → Option Nat
  | .sp => some (W - d)
  | .reg r => (ptrs.find? (·.1 == r)).map (·.2)

/-- A store's source is public. -/
def srcPub (τ : RTaintB.T) : Src → Bool
  | .gpr r => τ.1.1.1.1.mem r
  | .vec v => τ.1.1.1.2.mem v

/-- The mask after a store. -/
def storeP (W d : Nat) (ptrs : List (Reg × Nat)) (τ : RTaintB.T) (P : Nat)
    (st : Base × Nat × Nat × Src) : Nat :=
  match offOf W d ptrs st.1 with
  | some o =>
    if o + st.2.1 + st.2.2.1 ≤ W then
      (if srcPub τ st.2.2.2 then bset P (o + st.2.1) st.2.2.1 else bclr P (o + st.2.1) st.2.2.1)
    else (if srcPub τ st.2.2.2 then P else 0)
  | none => if srcPub τ st.2.2.2 then P else 0

/-- The mask after stores. -/
def storesP (W d : Nat) (ptrs : List (Reg × Nat)) (τ : RTaintB.T) : Nat → List (Base × Nat × Nat × Src) → Nat
  | P, [] => P
  | P, st :: l => storesP W d ptrs τ (storeP W d ptrs τ P st) l

/-- The window's base, `W` bytes below the stack pointer on entry, `d` bytes above `sp`. -/
def wbase (sp : Addr) (d W : Nat) : Addr := sp + BitVec.ofNat 64 d - BitVec.ofNat 64 W

/-- The bytes `P` says agree, agree. -/
def PAgree (W : Nat) (w : Addr) (P : Nat) (m₁ m₂ : Mem) : Prop :=
  ∀ o < W, P.testBit o = true → m₁ (w + BitVec.ofNat 64 o) = m₂ (w + BitVec.ofNat 64 o)

/-- The registers `ptrs` lists hold the addresses it says, in both runs. -/
def PtrsOk (w : Addr) (ptrs : List (Reg × Nat)) (s₁ s₂ : State) : Prop :=
  ∀ e ∈ ptrs, s₁.gpr e.1 = w + BitVec.ofNat 64 e.2 ∧ s₂.gpr e.1 = w + BitVec.ofNat 64 e.2

theorem offOf_val {W d : Nat} {ptrs : List (Reg × Nat)} {w : Addr} {s₁ s₂ : State}
    (hp : PtrsOk w ptrs s₁ s₂) (hsp : s₁.sp = s₂.sp) (hw : w = wbase s₂.sp d W) (hd : d ≤ W)
    (hW : W < 2 ^ 64) {b : Base} {o : Nat} (h : offOf W d ptrs b = some o) :
    b.val s₁ = w + BitVec.ofNat 64 o ∧ b.val s₂ = w + BitVec.ofNat 64 o := by
  cases b with
  | sp =>
    simp only [offOf, Option.some.injEq] at h
    subst h
    have e : s₂.sp = w + BitVec.ofNat 64 (W - d) := by
      rw [hw, wbase]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
      have := s₂.sp.isLt
      rw [Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show W < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show W - d < 2 ^ 64 by omega)]
      omega
    exact ⟨by simp only [Base.val, hsp, e], by simp only [Base.val, e]⟩
  | reg r =>
    simp only [offOf, Option.map_eq_some_iff] at h
    obtain ⟨e, he, rfl⟩ := h
    have hr : e.1 = r := by simpa using List.find?_some he
    have := hp e (List.mem_of_find?_eq_some he)
    rw [hr] at this
    exact this

theorem srcPub_val {τ : RTaintB.T} {s₁ s₂ : State} (ha : RTaintB.Agree τ s₁ s₂) {src : Src}
    (h : srcPub τ src = true) (n : Nat) : src.val n s₁ = src.val n s₂ := by
  obtain ⟨⟨⟨⟨⟨-, hgr⟩, hvr⟩, -⟩, -⟩, -⟩ := ha
  cases src with
  | gpr r => simp only [Src.val]; rw [hgr r (Taint.pub_iff.mp h)]
  | vec v => simp only [Src.val]; rw [hvr v h]

/-- A store keeps what the mask after it says. -/
theorem storeP_sound {W d : Nat} {ptrs : List (Reg × Nat)} {τ : RTaintB.T} {P : Nat} {w : Addr}
    {s₁ s₂ : State} {m₁ m₂ : Mem} (hW : W < 2 ^ 64) (hd : d ≤ W) (hsp : s₁.sp = s₂.sp)
    (hw : w = wbase s₂.sp d W)
    (ha : RTaintB.Agree τ s₁ s₂) (hp : PtrsOk w ptrs s₁ s₂) (hP : PAgree W w P m₁ m₂)
    {st : Base × Nat × Nat × Src}
    (hadr : st.1.val s₁ + BitVec.ofNat 64 st.2.1 = st.1.val s₂ + BitVec.ofNat 64 st.2.1) :
    PAgree W w (storeP W d ptrs τ P st)
      (m₁.write (st.1.val s₁ + BitVec.ofNat 64 st.2.1) st.2.2.1 (st.2.2.2.val st.2.2.1 s₁))
      (m₂.write (st.1.val s₂ + BitVec.ofNat 64 st.2.1) st.2.2.1 (st.2.2.2.val st.2.2.1 s₂)) := by
  obtain ⟨b, off, n, src⟩ := st
  simp only at hadr ⊢
  -- A public store at the same address in both runs keeps every byte that agreed.
  have hsame : srcPub τ src = true → PAgree W w P
      (m₁.write (b.val s₁ + BitVec.ofNat 64 off) n (src.val n s₁))
      (m₂.write (b.val s₂ + BitVec.ofNat 64 off) n (src.val n s₂)) := by
    intro hpub o ho hb
    rw [hadr, srcPub_val ha hpub n]
    simp only [Mem.write]
    split
    · rfl
    · exact hP o ho hb
  unfold storeP
  split
  · rename_i o ho
    obtain ⟨hv₁, hv₂⟩ := offOf_val hp hsp hw hd hW ho
    simp only
    split
    · rename_i hfit
      have ha₁ : b.val s₁ + BitVec.ofNat 64 off = w + BitVec.ofNat 64 (o + off) := by
        rw [hv₁, BitVec.ofNat_add, BitVec.add_assoc]
      have ha₂ : b.val s₂ + BitVec.ofNat 64 off = w + BitVec.ofNat 64 (o + off) := by
        rw [hv₂, BitVec.ofNat_add, BitVec.add_assoc]
      split
      · rename_i hpub
        intro o' ho' hb
        rw [testBit_bset] at hb
        rw [ha₁, ha₂, write_at hW (by omega) ho', write_at hW (by omega) ho', srcPub_val ha hpub n]
        split
        · rfl
        · rename_i hn
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
          rcases hb with hb | hb
          · exact hP o' ho' hb
          · exact absurd hb hn
      · intro o' ho' hb
        rw [testBit_bclr] at hb
        simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hb
        rw [ha₁, ha₂, write_at hW (by omega) ho', write_at hW (by omega) ho']
        have hn : ¬ (o + off ≤ o' ∧ o' < o + off + n) := by
          rintro ⟨h₁, h₂⟩; rcases hb.2 with h | h <;> omega
        simp only [hn, ↓reduceIte]
        exact hP o' ho' hb.1
    · split
      · rename_i hpub; exact hsame hpub
      · intro o' _ hb; simp at hb
  · split
    · rename_i hpub; exact hsame hpub
    · intro o' _ hb; simp at hb

theorem storesP_sound {W d : Nat} {ptrs : List (Reg × Nat)} {τ : RTaintB.T} {w : Addr}
    {s₁ s₂ : State} (hW : W < 2 ^ 64) (hd : d ≤ W) (hsp : s₁.sp = s₂.sp) (hw : w = wbase s₂.sp d W)
    (ha : RTaintB.Agree τ s₁ s₂) (hp : PtrsOk w ptrs s₁ s₂) :
    ∀ (l : List (Base × Nat × Nat × Src)) {P : Nat} {m₁ m₂ : Mem},
      (∀ st ∈ l, st.1.val s₁ + BitVec.ofNat 64 st.2.1 = st.1.val s₂ + BitVec.ofNat 64 st.2.1) →
      PAgree W w P m₁ m₂ → PAgree W w (storesP W d ptrs τ P l) (writeAll s₁ l m₁) (writeAll s₂ l m₂)
  | [], _, _, _, _, hP => hP
  | st :: l, _, _, _, hadr, hP =>
    storesP_sound hW hd hsp hw ha hp l (fun st' h => hadr st' (List.mem_cons_of_mem _ h))
      (storeP_sound hW hd hsp hw ha hp hP (hadr st (List.mem_cons_self ..)))

/-- The stores' addresses are the instruction's. -/
theorem stores_addrs {i : Instr} {s₁ s₂ : State} (h : addrs i s₁ = addrs i s₂) :
    ∀ st ∈ stores i, st.1.val s₁ + BitVec.ofNat 64 st.2.1 = st.1.val s₂ + BitVec.ofNat 64 st.2.1 := by
  intro st hst
  cases i <;> simp only [stores, List.mem_cons, List.not_mem_nil, or_false] at hst
  all_goals first
    | (subst hst; simpa [addrs, Base.val] using h)
    | (rcases hst with rfl | rfl
       · simpa [addrs, Base.val] using (List.cons.inj h).1
       · have := (List.cons.inj (List.cons.inj h).2).1
         simp only [Base.val]
         rw [BitVec.ofNat_add, ← BitVec.add_assoc, ← BitVec.add_assoc]
         exact this)

end VG.AArch64.RTaintG
