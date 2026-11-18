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

/-! ## The registers that point into the window -/

/-- The pointers into the window after `i`. -/
def ptrStep (W d : Nat) (ptrs : List (Reg × Nat)) (i : Instr) : List (Reg × Nat) :=
  let kept := ptrs.filter (fun e => !clobbers i e.1)
  match i with
  | .addSp dd imm => (dd, W - d + imm) :: kept
  | .addImm .x dd n k =>
    match offOf W d ptrs (.reg n) with
    | some o => (dd, o + k) :: kept
    | none => kept
  | .subImm .x dd n k =>
    match offOf W d ptrs (.reg n) with
    | some o => if k ≤ o then (dd, o - k) :: kept else kept
    | none => kept
  | _ => kept

theorem wbase_add {sp : Addr} {d W imm : Nat} (hd : d ≤ W) (hW : W < 2 ^ 64) :
    wbase sp d W + BitVec.ofNat 64 (W - d + imm) = sp + BitVec.ofNat 64 imm := by
  unfold wbase
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := sp.isLt
  rw [Nat.mod_eq_of_lt (show W < 2 ^ 64 by omega)]
  omega

theorem kept_ok {i : Instr} {w : Addr} {ptrs : List (Reg × Nat)} {s₁ s₂ s₁' s₂' : State}
    (hp : PtrsOk w ptrs s₁ s₂) (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    PtrsOk w (ptrs.filter (fun e => !clobbers i e.1)) s₁' s₂' := by
  intro e he
  obtain ⟨he, hc⟩ := List.mem_filter.mp he
  have hc' : clobbers i e.1 = false := by simpa using hc
  rw [exec_gpr hc' e₁, exec_gpr hc' e₂]
  exact hp e he

theorem exec_addSp_eq {d : Reg} {imm : Nat} {s s' : State} (h : exec (.addSp d imm) s = some s') :
    s' = s.write .x d (s.sp + BitVec.ofNat 64 imm) := by
  simp only [exec] at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

theorem exec_addImm_eq {d n : Reg} {k : Nat} {s s' : State} (h : exec (.addImm .x d n k) s = some s') :
    s' = s.write .x d (s.read .x n + BitVec.ofNat _ k) := by
  simp only [exec] at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

theorem exec_subImm_eq {d n : Reg} {k : Nat} {s s' : State} (h : exec (.subImm .x d n k) s = some s') :
    s' = s.write .x d (s.read .x n - BitVec.ofNat _ k) := by
  simp only [exec] at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

theorem ptrStep_sound {W d : Nat} {i : Instr} {w : Addr} {ptrs : List (Reg × Nat)}
    {s₁ s₂ s₁' s₂' : State} (hp : PtrsOk w ptrs s₁ s₂) (hsp : s₁.sp = s₂.sp)
    (hw : w = wbase s₂.sp d W) (hd : d ≤ W) (hW : W < 2 ^ 64)
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    PtrsOk w (ptrStep W d ptrs i) s₁' s₂' := by
  have hk := kept_ok hp e₁ e₂
  unfold ptrStep
  split
  · rename_i dd imm
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · rw [exec_addSp_eq e₁, exec_addSp_eq e₂]
      simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq, hw, wbase_add hd hW, hsp]
      constructor <;> first | trivial | rfl
    · exact hk e he
  · rename_i dd n k
    split
    · rename_i o ho
      obtain ⟨hv₁, hv₂⟩ := offOf_val hp hsp hw hd hW ho
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · rw [exec_addImm_eq e₁, exec_addImm_eq e₂]
        simp only [Base.val] at hv₁ hv₂
        simp only [RegUpd.gpr_write_self, State.read, Size.bits, BitVec.setWidth_eq, hv₁, hv₂,
          BitVec.ofNat_add, BitVec.add_assoc]
        constructor <;> first | trivial | rfl
      · exact hk e he
    · exact hk
  · rename_i dd n k
    split
    · rename_i o ho
      obtain ⟨hv₁, hv₂⟩ := offOf_val hp hsp hw hd hW ho
      split
      · rename_i hko
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · rw [exec_subImm_eq e₁, exec_subImm_eq e₂]
          simp only [Base.val] at hv₁ hv₂
          have e : ∀ x : Addr, x + BitVec.ofNat 64 o - BitVec.ofNat 64 k = x + BitVec.ofNat 64 (o - k) := by
            intro x
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
            omega
          simp only [RegUpd.gpr_write_self, State.read, Size.bits, BitVec.setWidth_eq, hv₁, hv₂, e]
          constructor <;> first | trivial | rfl
        · exact hk e he
      · exact hk
    · exact hk
  · exact hk

/-! ## The analysis -/

/-- `rtaintB`'s taint, and, unless forgotten, the depth in the window, the
mask of its bytes the runs agree on, and the pointers into it. -/
abbrev T := RTaintB.T × Option (Nat × Nat × List (Reg × Nat))

def AgreeG (W : Nat) (τ : T) (s₁ s₂ : State) : Prop :=
  match τ.2 with
  | some (d, P, ptrs) => AgreeD W τ.1 d s₁ s₂ ∧ PAgree W (wbase s₂.sp d W) P s₁.mem s₂.mem ∧
      PtrsOk (wbase s₂.sp d W) ptrs s₁ s₂
  | none => ∃ d, AgreeD W τ.1 d s₁ s₂

theorem writeAll_congr {s t : State} (hg : s.gpr = t.gpr) (hsp : s.sp = t.sp) (hv : s.v = t.v) :
    ∀ (l : List (Base × Nat × Nat × Src)) (m : Mem), writeAll s l m = writeAll t l m
  | [], _ => rfl
  | (b, off, n, src) :: l, m => by
    have hb : b.val s = b.val t := by cases b <;> simp [Base.val, hg, hsp]
    have hs : src.val n s = src.val n t := by cases src <;> simp [Src.val, hg, hv]
    simp only [writeAll, hb, hs]
    exact writeAll_congr hg hsp hv l _

def stepG (W : Nat) (τ : T) (i : Instr) : Option T :=
  (RTaintB.step τ.1 i).map fun τb => (τb, τ.2.map fun (d, P, ptrs) =>
    (d, storesP W d ptrs τ.1 P (stores i), ptrStep W d ptrs i))

theorem stepG_sound {W : Nat} {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : AgreeG W τ s₁ s₂)
    (hs : stepG W τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂')
    (hadr : addrs i s₁ = addrs i s₂) : AgreeG W τ' s₁' s₂' := by
  obtain ⟨τb, fi⟩ := τ
  obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.mp hs
  cases fi with
  | none =>
    obtain ⟨d, hD⟩ := ha
    exact ⟨d, step_sound hD hσ e₁ e₂ hadr⟩
  | some f =>
    obtain ⟨d, P, ptrs⟩ := f
    obtain ⟨hD, hP, hp⟩ := ha
    obtain ⟨hsp, -, -, -, -⟩ := AgreeD.rest hD
    have sp₂ := exec_sp e₂
    refine ⟨step_sound hD hσ e₁ e₂ hadr, ?_, ?_⟩
    · show PAgree W (wbase s₂'.sp d W) (storesP W d ptrs τb P (stores i)) s₁'.mem s₂'.mem
      rw [sp₂, exec_mem e₁, exec_mem e₂]
      have hg := storesP_sound (s₂ := ghost s₁ s₂) hD.2.2.1 hD.2.1 hsp rfl hD.1 hp (stores i)
        (stores_addrs (by rw [hadr]; exact (addrs_withMS i s₂ _ _).symm)) hP
      rw [writeAll_congr (s := ghost s₁ s₂) (t := s₂) rfl rfl rfl] at hg
      exact hg
    · show PtrsOk (wbase s₂'.sp d W) (ptrStep W d ptrs i) s₁' s₂'
      rw [sp₂]
      exact ptrStep_sound hp hsp rfl hD.2.1 hD.2.2.1 e₁ e₂

/-! ## Calls, returns and frames -/

def pushG (W : Nat) (τ : T) (i : Instr) : Option T :=
  match τ.2, i with
  | some (d, P, ptrs), .alloc b => if d + b ≤ W then some (τ.1, some (d + b, P, ptrs)) else none
  | some (d, P, ptrs), .push r =>
    if d + 16 ≤ W then
      some (τ.1, some (d + 16, (if τ.1.1.1.1.1.mem r then bset P (W - d - 16) 8 else bclr P (W - d - 16) 8),
        ptrs))
    else none
  | _, _ => none

def popG (τ : T) (j : Instr) : Option T :=
  match τ.2, j with
  | some (d, P, ptrs), .free b => if b ≤ d then some (τ.1, some (d - b, P, ptrs)) else none
  | some (d, P, ptrs), .pop r =>
    if 16 ≤ d then some (eraseT τ.1 r, some (d - 16, P, ptrs.filter (·.1 != r))) else none
  | _, _ => none

def callG (τ : T) : T :=
  (callT τ.1, τ.2.map fun (d, P, ptrs) =>
    (d, P, ptrs.filter (fun e => e.1 != .x30 && e.1 != .x16 && e.1 != .x17)))

theorem wbase_sub {sp : Addr} {b d W : Nat} :
    wbase (sp - BitVec.ofNat 64 b) (d + b) W = wbase sp d W := by
  unfold wbase; rw [sp_sub_add]

theorem wbase_sub16 {sp : Addr} {d W : Nat} : wbase (sp - 16) (d + 16) W = wbase sp d W := by
  unfold wbase; rw [sp_sub16_add]

theorem wbase_add' {sp : Addr} {b d W : Nat} (h : b ≤ d) :
    wbase (sp + BitVec.ofNat 64 b) (d - b) W = wbase sp d W := by
  unfold wbase; rw [sp_add_sub h]

theorem lose_agree {m₁ m₂ : Mem} {a x : Addr} {n : Nat} {u : Nat → BitVec 64} (h : m₁ x = m₂ x) :
    lose m₁ a n u x = lose m₂ a n u x := by
  simp only [lose]; split <;> [split <;> [exact h; rfl]; exact h]

end RTaintG
end VG.AArch64

namespace VG.AArch64.RTaintG
open VG.AArch64 VG.AArch64.Residue VG.AArch64.MemEffect VG.AArch64.RTaintF

theorem wbase_push {sp : Addr} {d W : Nat} (hd : d + 16 ≤ W) (hW : W < 2 ^ 64) :
    sp - 16 = wbase sp d W + BitVec.ofNat 64 (W - d - 16) := by
  unfold wbase
  rw [show (16 : Addr) = BitVec.ofNat 64 16 from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := sp.isLt
  rw [Nat.mod_eq_of_lt (show W < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show W - d - 16 < 2 ^ 64 by omega)]
  omega

theorem pushG_sound {W : Nat} {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : AgreeG W τ s₁ s₂)
    (hs : pushG W τ i = some τ') (e₁ : push i s₁ = some s₁') (e₂ : push i s₂ = some s₂') :
    AgreeG W τ' s₁' s₂' := by
  obtain ⟨τb, fi⟩ := τ
  cases fi with
  | none => simp only [pushG] at hs; cases hs
  | some f =>
  obtain ⟨d, P, ptrs⟩ := f
  obtain ⟨hD, hP, hp⟩ := ha
  obtain ⟨hsp, -, -, -, -⟩ := AgreeD.rest hD
  cases i <;> simp only [pushG, reduceCtorEq] at hs
  case alloc b =>
    split at hs <;> [rename_i hle; cases hs]
    obtain rfl := Option.some.inj hs
    obtain ⟨d', hd', hD'⟩ := pushF_sound (τ := (τb, some d)) (τ' := (τb, some (d + b)))
      ⟨d, Or.inl rfl, hD⟩ (by simp only [pushF, hle, ↓reduceIte]) e₁ e₂
    have : d' = d + b := by
      rcases hd' with h | h
      · exact (Option.some.inj h).symm
      · cases h
    subst this
    simp only [push] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    obtain rfl := Option.some.inj e₁
    obtain rfl := Option.some.inj e₂
    refine ⟨hD', ?_, ?_⟩
    · show PAgree W (wbase (s₂.sp - BitVec.ofNat 64 b) (d + b) W) P s₁.mem s₂.mem
      rw [wbase_sub]; exact hP
    · show PtrsOk (wbase (s₂.sp - BitVec.ofNat 64 b) (d + b) W) ptrs s₁ s₂
      rw [wbase_sub]; exact hp
  case push r =>
    split at hs <;> [rename_i hle; cases hs]
    obtain rfl := Option.some.inj hs
    obtain ⟨d', hd', hD'⟩ := pushF_sound (τ := (τb, some d)) (τ' := (τb, some (d + 16)))
      ⟨d, Or.inl rfl, hD⟩ (by simp only [pushF, hle, ↓reduceIte]) e₁ e₂
    have : d' = d + 16 := by
      rcases hd' with h | h
      · exact (Option.some.inj h).symm
      · cases h
    subst this
    have hW := hD.2.2.1
    simp only [push] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    obtain rfl := Option.some.inj e₁
    obtain rfl := Option.some.inj e₂
    refine ⟨hD', ?_, ?_⟩
    · show PAgree W (wbase (s₂.sp - 16) (d + 16) W) _ (s₁.mem.write (s₁.sp - 16) 8 (s₁.gpr r))
        (s₂.mem.write (s₂.sp - 16) 8 (s₂.gpr r))
      rw [wbase_sub16, hsp, wbase_push hle hW]
      intro o' ho' hb
      rw [write_at hW (by omega) ho', write_at hW (by omega) ho']
      split at hb
      · rename_i hpub
        rw [testBit_bset] at hb
        have hr : s₁.gpr r = s₂.gpr r := hD.1.1.1.1.1.2 r (Taint.pub_iff.mp hpub)
        split
        · rw [hr]
        · rename_i hn
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
          rcases hb with hb | hb
          · exact hP o' ho' hb
          · exact absurd hb hn
      · rw [testBit_bclr] at hb
        simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hb
        have hn : ¬ (W - d - 16 ≤ o' ∧ o' < W - d - 16 + 8) := by
          rintro ⟨h₁, h₂⟩; rcases hb.2 with h | h <;> omega
        simp only [hn, ↓reduceIte]
        exact hP o' ho' hb.1
    · show PtrsOk (wbase (s₂.sp - 16) (d + 16) W) ptrs _ _
      rw [wbase_sub16]; exact hp

theorem popG_sound {W : Nat} {τ τ' : T} {j : Instr} {a₁ a₂ b₁ b₂ c₁ c₂ : State}
    (ha : AgreeG W τ b₁ b₂) (hs : popG τ j = some τ') (e₁ : pop j a₁ b₁ = some c₁)
    (e₂ : pop j a₂ b₂ = some c₂) : AgreeG W τ' c₁ c₂ := by
  obtain ⟨τb, fi⟩ := τ
  cases fi with
  | none => simp only [popG] at hs; cases hs
  | some f =>
  obtain ⟨d, P, ptrs⟩ := f
  obtain ⟨hD, hP, hp⟩ := ha
  obtain ⟨hsp, -, -, -, hu⟩ := AgreeD.rest hD
  cases j <;> simp only [popG, reduceCtorEq] at hs
  case free n =>
    split at hs <;> [rename_i hle; cases hs]
    obtain rfl := Option.some.inj hs
    obtain ⟨d', hd', hD'⟩ := popF_sound (τ := (τb, some d)) (τ' := (τb, some (d - n)))
      ⟨d, Or.inl rfl, hD⟩ (by simp only [popF, hle, ↓reduceIte]) e₁ e₂
    have : d' = d - n := by
      rcases hd' with h | h
      · exact (Option.some.inj h).symm
      · cases h
    subst this
    simp only [pop] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    obtain rfl := Option.some.inj e₁
    obtain rfl := Option.some.inj e₂
    refine ⟨hD', ?_, ?_⟩
    · show PAgree W (wbase (b₂.sp + BitVec.ofNat 64 n) (d - n) W) P
        (lose b₁.mem b₁.sp n b₁.unknowns) (lose b₂.mem b₂.sp n b₂.unknowns)
      rw [wbase_add' hle, hsp, hu]
      intro o' ho' hb
      exact lose_agree (hP o' ho' hb)
    · show PtrsOk (wbase (b₂.sp + BitVec.ofNat 64 n) (d - n) W) ptrs _ _
      rw [wbase_add' hle]; exact hp
  case pop r =>
    split at hs <;> [rename_i hle; cases hs]
    obtain rfl := Option.some.inj hs
    obtain ⟨d', hd', hD'⟩ := popF_sound (τ := (τb, some d)) (τ' := (eraseT τb r, some (d - 16)))
      ⟨d, Or.inl rfl, hD⟩ (by simp only [popF, hle, ↓reduceIte]) e₁ e₂
    have : d' = d - 16 := by
      rcases hd' with h | h
      · exact (Option.some.inj h).symm
      · cases h
    subst this
    simp only [pop] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    obtain rfl := Option.some.inj e₁
    obtain rfl := Option.some.inj e₂
    refine ⟨hD', ?_, ?_⟩
    · show PAgree W (wbase (b₂.sp + 16) (d - 16) W) P
        (lose b₁.mem b₁.sp 16 b₁.unknowns) (lose b₂.mem b₂.sp 16 b₂.unknowns)
      rw [show (16 : Addr) = BitVec.ofNat 64 16 from rfl, wbase_add' hle, hsp, hu]
      intro o' ho' hb
      exact lose_agree (hP o' ho' hb)
    · show PtrsOk (wbase (b₂.sp + 16) (d - 16) W) _ _ _
      rw [show (16 : Addr) = BitVec.ofNat 64 16 from rfl, wbase_add' hle]
      intro e he
      obtain ⟨he, hne⟩ := List.mem_filter.mp he
      have hne' : ¬ e.1 = r := by simpa using hne
      show (b₁.write .x r _).gpr e.1 = _ ∧ (b₂.write .x r _).gpr e.1 = _
      rw [RegUpd.gpr_write_of_ne b₁ .x _ hne', RegUpd.gpr_write_of_ne b₂ .x _ hne']
      exact hp e he

theorem callG_sound {W : Nat} {τ : T} {s₁ s₂ s₁' s₂' : State} (ha : AgreeG W τ s₁ s₂)
    (e₁ : call s₁ = some s₁') (e₂ : call s₂ = some s₂') : AgreeG W (callG τ) s₁' s₂' := by
  obtain ⟨τb, fi⟩ := τ
  cases fi with
  | none =>
    obtain ⟨d, hD⟩ := ha
    obtain ⟨d', hd', hD'⟩ := callF_sound (τ := (τb, some d)) ⟨d, Or.inl rfl, hD⟩ e₁ e₂
    exact ⟨d', hD'⟩
  | some f =>
  obtain ⟨d, P, ptrs⟩ := f
  obtain ⟨hD, hP, hp⟩ := ha
  obtain ⟨d', hd', hD'⟩ := callF_sound (τ := (τb, some d)) ⟨d, Or.inl rfl, hD⟩ e₁ e₂
  have : d' = d := by
    rcases hd' with h | h
    · exact (Option.some.inj h).symm
    · cases h
  subst this
  simp only [call, Option.some.injEq] at e₁ e₂
  subst e₁ e₂
  refine ⟨hD', hP, fun e he => ?_⟩
  obtain ⟨he, hne⟩ := List.mem_filter.mp he
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hne
  simp only [hne.1.1, hne.1.2, hne.2, ↓reduceIte]
  exact hp e he

/-! ## Meet and order -/

/-- Every bit of `a` is set in `b`. -/
def bsub (a b : Nat) : Bool := a &&& b == a

theorem bsub_bit {a b k : Nat} (h : bsub a b = true) (hk : a.testBit k = true) : b.testBit k = true := by
  have e : (a &&& b) = a := by simpa [bsub] using h
  rw [← e, Nat.testBit_and, Bool.and_eq_true] at hk
  exact hk.2

def meetG (τ σ : T) : T :=
  (rtaintB.meet τ.1 σ.1, match τ.2, σ.2 with
    | some (d, P, p), some (d', P', p') =>
      if d = d' then some (d, P &&& P', p.filter (fun e => p'.contains e)) else none
    | _, _ => none)

def leG (τ σ : T) : Bool :=
  rtaintB.le τ.1 σ.1 && match τ.2, σ.2 with
    | none, _ => true
    | some (d, P, p), some (d', P', p') => d == d' && bsub P P' && p.all (fun e => p'.contains e)
    | some _, none => false

theorem agreeD_meet_left {W : Nat} {τ σ : RTaintB.T} {d : Nat} {s₁ s₂ : State} (h : AgreeD W τ d s₁ s₂) :
    AgreeD W (rtaintB.meet τ σ) d s₁ s₂ := ⟨rtaintB.meet_left h.1, h.2⟩

theorem agreeD_meet_right {W : Nat} {τ σ : RTaintB.T} {d : Nat} {s₁ s₂ : State} (h : AgreeD W σ d s₁ s₂) :
    AgreeD W (rtaintB.meet τ σ) d s₁ s₂ := ⟨rtaintB.meet_right h.1, h.2⟩

theorem AgreeG.forget {W : Nat} {τ : T} {s₁ s₂ : State} (h : AgreeG W τ s₁ s₂) :
    ∃ d, AgreeD W τ.1 d s₁ s₂ := by
  obtain ⟨τb, fi⟩ := τ
  cases fi with
  | none => exact h
  | some f => exact ⟨f.1, h.1⟩

theorem meetG_left {W : Nat} {τ σ : T} {s₁ s₂ : State} (h : AgreeG W τ s₁ s₂) :
    AgreeG W (meetG τ σ) s₁ s₂ := by
  obtain ⟨τb, fi⟩ := τ
  obtain ⟨σb, gi⟩ := σ
  cases fi with
  | none => obtain ⟨d, hD⟩ := h; exact ⟨d, agreeD_meet_left hD⟩
  | some f =>
  obtain ⟨d, P, p⟩ := f
  obtain ⟨hD, hP, hp⟩ := h
  cases gi with
  | none => exact ⟨d, agreeD_meet_left hD⟩
  | some g =>
  obtain ⟨d', P', p'⟩ := g
  show AgreeG W (_, if d = d' then _ else none) s₁ s₂
  split
  · refine ⟨agreeD_meet_left hD, fun o ho hb => hP o ho ?_, fun e he => hp e (List.mem_filter.mp he).1⟩
    rw [Nat.testBit_and, Bool.and_eq_true] at hb; exact hb.1
  · exact ⟨d, agreeD_meet_left hD⟩

theorem meetG_right {W : Nat} {τ σ : T} {s₁ s₂ : State} (h : AgreeG W σ s₁ s₂) :
    AgreeG W (meetG τ σ) s₁ s₂ := by
  obtain ⟨τb, fi⟩ := τ
  obtain ⟨σb, gi⟩ := σ
  cases gi with
  | none =>
    obtain ⟨d, hD⟩ := h
    cases fi with
    | none => exact ⟨d, agreeD_meet_right hD⟩
    | some f => exact ⟨d, agreeD_meet_right hD⟩
  | some g =>
  obtain ⟨d', P', p'⟩ := g
  obtain ⟨hD, hP, hp⟩ := h
  cases fi with
  | none => exact ⟨d', agreeD_meet_right hD⟩
  | some f =>
  obtain ⟨d, P, p⟩ := f
  show AgreeG W (_, if d = d' then _ else none) s₁ s₂
  split
  · rename_i hdd
    subst hdd
    refine ⟨agreeD_meet_right hD, fun o ho hb => hP o ho ?_, fun e he => ?_⟩
    · rw [Nat.testBit_and, Bool.and_eq_true] at hb; exact hb.2
    · have := (List.mem_filter.mp he).2
      exact hp e (List.contains_iff_mem.mp this)
  · exact ⟨d', agreeD_meet_right hD⟩

theorem leG_sound {W : Nat} {τ σ : T} {s₁ s₂ : State} (hl : leG τ σ = true) (h : AgreeG W σ s₁ s₂) :
    AgreeG W τ s₁ s₂ := by
  obtain ⟨τb, fi⟩ := τ
  obtain ⟨σb, gi⟩ := σ
  simp only [leG, Bool.and_eq_true] at hl
  obtain ⟨hle, hr⟩ := hl
  have hle' : ∀ {d}, AgreeD W σb d s₁ s₂ → AgreeD W τb d s₁ s₂ := fun hD => ⟨rtaintB.le_sound hle hD.1, hD.2⟩
  cases fi with
  | none =>
    obtain ⟨d, hD⟩ := AgreeG.forget h
    exact ⟨d, hle' hD⟩
  | some f =>
  obtain ⟨d, P, p⟩ := f
  cases gi with
  | none => simp at hr
  | some g =>
  obtain ⟨d', P', p'⟩ := g
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hr
  obtain ⟨⟨rfl, hPP⟩, hpp⟩ := hr
  obtain ⟨hD, hP, hp⟩ := h
  exact ⟨hle' hD, fun o ho hb => hP o ho (bsub_bit hPP hb),
    fun e he => hp e (List.contains_iff_mem.mp (hpp e he))⟩

end RTaintG

open RTaintG in
/-- `rtaintF W` with the mask of the window's bytes the runs agree on (see `RTaintG`). -/
def rtaintG (W : Nat) : VG.TaintCT isa where
  T := RTaintG.T
  Agree := AgreeG W
  step := stepG W
  step_sound ha hs e₁ e₂ hadr := stepG_sound ha hs e₁ e₂ hadr
  addrs_length := RTaintCT.addrs_length
  meet := meetG
  meet_left := meetG_left
  meet_right := meetG_right
  le := leG
  le_sound := leG_sound
  call τ := some (callG τ)
  call_sound ha hs e₁ e₂ _ := by
    obtain rfl := Option.some.inj hs
    exact callG_sound ha e₁ e₂
  callAddrs_length _ _ := rfl
  ret τ := some τ
  ret_sound ha hs e₁ e₂ _ := by
    obtain rfl := Option.some.inj hs
    simp only [isa, ret] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    obtain rfl := Option.some.inj e₁
    obtain rfl := Option.some.inj e₂
    exact ha
  retAddrs_length _ _ := rfl
  push := pushG W
  push_sound ha hs e₁ e₂ _ := pushG_sound ha hs e₁ e₂
  pop := popG
  pop_sound ha hs e₁ e₂ _ := popG_sound ha hs e₁ e₂

namespace RTaintG

end VG.AArch64.RTaintG
