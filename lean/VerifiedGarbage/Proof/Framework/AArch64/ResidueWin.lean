module

public import VerifiedGarbage.Proof.Framework.AArch64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.AArch64.MemEffect
public import VerifiedGarbage.Proof.Framework.KernelList
public import VerifiedGarbage.TCB.Registration
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
(`scrubSel`).
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

/-! ## The step the kernel evaluates

`stepGK` is `stepG` (`stepGK_eq`) written for the kernel (see "An analysis the
kernel finds again" in the `proof-performance` skill):

* it takes the taint apart once (`stepGK`'s match), and matches on the
  instruction once, with the cases of the match closed (`stepGFnK`,
  `inline_match%`);
* the taint it gives is evaluated: what an instruction changes is forced
  before the taint is built of it (`RegSet.force`, `forceN`, `forceB`,
  `forceL`), and what it does not change is handed on as it was: the widths
  and the pointers, if none is of the register it writes (`keepL`, `keepO`),
  and the mask, if the bytes a store writes are in it, or are not, already
  (`maskK`). So the kernel finds again a step it has made of the same
  instruction from the same taint. -/

section
open VG.KList (all filter find?)

/-- `k n`, with `n` evaluated: what `k` is given is a numeral (see `RegSet.force`). -/
def forceN {α : Type} (n : Nat) (k : Nat → α) : α :=
  Nat.casesOn (motive := fun _ => α) (Nat.succ n) (k n) (fun m => k m)

theorem forceN_eq {α : Type} (n : Nat) (k : Nat → α) : forceN n k = k n := rfl

/-- `k b`, with `b` evaluated. -/
def forceB {α : Type} (b : Bool) (k : Bool → α) : α :=
  Bool.casesOn (motive := fun _ => α) b (k false) (k true)

theorem forceB_eq {α : Type} (b : Bool) (k : Bool → α) : forceB b k = k b := by cases b <;> rfl

def forceLC {α : Type} (l : List (Reg × Nat)) (k : List (Reg × Nat) → α) : α := k l

/-- `k l`, with the list `l` evaluated to its cells and numerals. -/
@[implemented_by forceLC] def forceL {α : Type} (l : List (Reg × Nat)) (k : List (Reg × Nat) → α) : α :=
  List.rec (motive := fun _ => (List (Reg × Nat) → α) → α) (fun k => k [])
    (fun e _ ih k => Prod.casesOn (motive := fun _ => α) e fun r n => forceN n fun n => ih fun l => k ((r, n) :: l)) l k

theorem forceL_eq {α : Type} : ∀ (l : List (Reg × Nat)) (k : List (Reg × Nat) → α), forceL l k = k l
  | [], _ => rfl
  | (_, _) :: l, _ => forceL_eq l _

/-- `a == b`, by the registers' indices. -/
def regEq (a b : Reg) : Bool := Nat.beq a.ctorIdx b.ctorIdx

theorem regEq_eq (a b : Reg) : regEq a b = (a == b) := by
  rw [regEq, KList.beq_eq, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨fun h => RegIdx.idx_inj h, fun h => h ▸ rfl⟩

/-- The registers of a list's entries. The kernel computes it once for a list,
and for a list with one more entry from that of the list without it. -/
def regsC (l : List (Reg × Nat)) : RegSet Reg := l.foldr (fun e s => s.insert e.1) .empty

@[implemented_by regsC] def regsOf (l : List (Reg × Nat)) : RegSet Reg :=
  List.rec (motive := fun _ => RegSet Reg) .empty (fun e _ ih => ih.insert e.1) l

theorem mem_regsOf {l : List (Reg × Nat)} {r : Reg} : (regsOf l).mem r = l.any fun e => r == e.1 := by
  induction l with
  | nil => exact Bool.eq_false_iff.mpr (RegSet.not_mem_empty r)
  | cons e l ih =>
    rw [List.any_cons, ← ih, Bool.eq_iff_iff, Bool.or_eq_true, beq_iff_eq]
    exact RegSet.mem_insert

theorem filter_of_regsOf {l : List (Reg × Nat)} {d : Reg} (h : (regsOf l).mem d = false) :
    (l.filter fun e => !(d == e.1)) = l := by
  rw [mem_regsOf, List.any_eq_false] at h
  exact List.filter_eq_self.mpr fun e he => by rw [Bool.not_eq_true', Bool.eq_false_iff]; exact h e he

/-- The entry of `r`. -/
def getK (l : List (Reg × Nat)) (r : Reg) : Option Nat :=
  bif (regsOf l).mem r then (find? (fun e => regEq e.1 r) l).map (·.2) else none

theorem getK_eq (l : List (Reg × Nat)) (r : Reg) : getK l r = (l.find? (·.1 == r)).map (·.2) := by
  simp only [getK, KList.find?_eq, regEq_eq]
  cases h : (regsOf l).mem r
  · rw [mem_regsOf, List.any_eq_false] at h
    rw [Bool.cond_false, List.find?_eq_none.mpr fun e he => by
      have := h e he; rw [Bool.beq_comm]; exact this]
    rfl
  · rfl

/-- `k` of the entries of `l` but those of `d`, evaluated: `l` as it is, if it has none. -/
def keepL {α : Type} (l : List (Reg × Nat)) (d : Reg) (k : List (Reg × Nat) → α) : α :=
  bif (regsOf l).mem d then forceL (filter (fun e => !regEq d e.1) l) k else k l

theorem keepL_eq {α : Type} (l : List (Reg × Nat)) (d : Reg) (k : List (Reg × Nat) → α) :
    keepL l d k = k (l.filter fun e => !(d == e.1)) := by
  simp only [keepL, KList.filter_eq, forceL_eq, regEq_eq]
  cases h : (regsOf l).mem d
  · rw [Bool.cond_false, filter_of_regsOf h]
  · rfl

/-- The depth in the window, the mask and the pointers, unless forgotten. -/
abbrev Win := Option (Nat × Nat × List (Reg × Nat))

/-- `k` of `o` without the pointers of `d`. -/
def keepO {α : Type} (o : Win) (d : Reg) (k : Win → α) : α :=
  match o with
  | none => k none
  | some (d₀, P, p) =>
    bif (regsOf p).mem d then forceL (filter (fun e => !regEq d e.1) p) fun p => k (some (d₀, P, p)) else k o

/-- `o` with the pointers of `d` dropped. -/
def dropO (o : Win) (d : Reg) : Win :=
  o.map fun (d₀, P, p) => (d₀, P, p.filter fun e => !(d == e.1))

theorem keepO_eq {α : Type} (o : Win) (d : Reg) (k : Win → α) : keepO o d k = k (dropO o d) := by
  obtain _ | ⟨d₀, P, p⟩ := o
  · rfl
  simp only [keepO, KList.filter_eq, forceL_eq, regEq_eq, dropO, Option.map_some]
  cases h : (regsOf p).mem d
  · rw [Bool.cond_false, filter_of_regsOf h]
  · rfl

/-- `k` of `o` with the pointer `(dd, off)` in place of those of `dd`: `off`
is given the window's depth and pointers. -/
def ptrO {α : Type} (o : Win) (dd : Reg) (off : Nat → List (Reg × Nat) → Option Nat) (k : Win → α) : α :=
  match o with
  | none => k none
  | some (d₀, P, p) =>
    match off d₀ p with
    | none => keepO o dd k
    | some a => forceN a fun a => keepL p dd fun p => k (some (d₀, P, (dd, a) :: p))

/-- `k` of the mask after a store of `n` bytes at offset `a`: `P` as it is if
the store does not change it. -/
def maskK {α : Type} (W a n P : Nat) (pub : Bool) (k : Nat → α) : α :=
  bif Nat.ble (Nat.add a n) W then
    bif pub then
      bif Nat.beq (Nat.land (Nat.shiftRight P a) (ones n)) (ones n) then k P else k (bset P a n)
    else
      bif Nat.beq (Nat.land (Nat.shiftRight P a) (ones n)) 0 then k P else k (bclr P a n)
  else bif pub then k P else k 0

/-- `k` of `o` after a store through `b`. -/
def stK {α : Type} (W : Nat) (o : Win) (b : Reg) (off n : Nat) (pub : Bool) (k : Win → α) : α :=
  match o with
  | none => k none
  | some (d₀, P, p) =>
    match getK p b with
    | some a => forceN (Nat.add a off) fun a => maskK W a n P pub fun P => k (some (d₀, P, p))
    | none => bif pub then k o else k (some (d₀, 0, p))

/-- `k` of `o` after a store through the stack pointer. -/
def stSpK {α : Type} (W : Nat) (o : Win) (off n : Nat) (pub : Bool) (k : Win → α) : α :=
  match o with
  | none => k none
  | some (d₀, P, p) =>
    forceN (Nat.add (Nat.sub W d₀) off) fun a => maskK W a n P pub fun P => k (some (d₀, P, p))

/-- What an instruction does to a taint, given the window's bytes and the taint's parts. -/
abbrev Fn := Nat → RegSet Reg → RegSet VReg → Bool → Nat → RegSet VReg → RegSet VReg → List (Reg × Nat) → Win → Option T

/-- Whether what an instruction writes is public. -/
abbrev PubF := RegSet Reg → RegSet VReg → Bool

def p0 (b : Bool) : PubF := fun _ _ => b
def p1 (n : Reg) : PubF := fun g _ => g.mem n
def p2 (n m : Reg) : PubF := fun g _ => g.mem n && g.mem m
def p3 (n m a : Reg) : PubF := fun g _ => g.mem n && g.mem m && g.mem a
def pv (n : VReg) : PubF := fun _ v => v.mem n
def pv2 (n m : VReg) : PubF := fun _ v => v.mem n && v.mem m

/-- The taint after a write of `d`, public if `p`, with `hk` the bits of the
result that may be secret if `d` is `x0`. -/
def setR (d : Reg) (p : Bool) (hk : Nat) (g : RegSet Reg) (v : RegSet VReg) (f : Bool) (h : Nat)
    (lo hi : RegSet VReg) (w : List (Reg × Nat)) (o : Win) : Option T :=
  (bif p then g.insert d else g.erase d).force fun g =>
    forceN (bif g.mem .x0 then 0 else bif regEq d .x0 then hk else h) fun h =>
      some ((((((g, v), f, h), lo, hi)), w), o)

/-- A write of `d` and nothing else. -/
def wr (d : Reg) (p : PubF) (hk : Nat) : Fn := fun _ g v f h lo hi w o =>
  keepL w d fun w => keepO o d fun o => setR d (p g v) hk g v f h lo hi w o

/-- A write of `d` and of the flags, both public if `p`. -/
def wrF (d : Reg) (p : PubF) : Fn := fun _ g v _ h lo hi w o =>
  forceB (p g v) fun f => keepL w d fun w => keepO o d fun o => setR d f 64 g v f h lo hi w o

/-- A write of `d` and of the flags, both secret. -/
def wrS (d : Reg) : Fn := fun W g v _ h lo hi w o => wr d (p0 false) 64 W g v false h lo hi w o

/-- A write of `d` of a value less than `2 ^ n`. -/
def wrW (d : Reg) (p : PubF) (n : List (Reg × Nat) → Nat) : Fn := fun _ g v f h lo hi w o =>
  forceN (n w) fun n => keepL w d fun w => keepO o d fun o => setR d (p g v) 64 g v f h lo hi ((d, n) :: w) o

/-- A write of `d` of a pointer into the window. -/
def wrP (d : Reg) (p : PubF) (off : Nat → Nat → List (Reg × Nat) → Option Nat) : Fn := fun W g v f h lo hi w o =>
  keepL w d fun w => ptrO o d (off W) fun o => setR d (p g v) 64 g v f h lo hi w o

/-- A load into `d`, through the base `n`. -/
def ld (n d : Reg) : Fn := fun W g v f h lo hi w o =>
  wr d (p0 false) 64 W (g.insert n) v f h lo hi w o

/-- A load into `d` and `e`, through the base `n`. -/
def ld2 (n d e : Reg) : Fn := fun _ g v f h lo hi w o =>
  keepL w d fun w => keepL w e fun w => keepO o d fun o => keepO o e fun o =>
    (((g.insert n).erase d).erase e).force fun g =>
      forceN (bif g.mem .x0 then 0 else bif regEq d .x0 || regEq e .x0 then 64 else h) fun h =>
        some ((((((g, v), f, h), lo, hi)), w), o)

/-- The taint after an instruction that writes no general-purpose register. -/
def same : Fn := fun _ g v f h lo hi w o =>
  forceN (bif g.mem .x0 then 0 else h) fun h => some ((((((g, v), f, h), lo, hi)), w), o)

/-- `same`, with the flags public if `p`. -/
def sameF (p : PubF) : Fn := fun W g v _ h lo hi w o => forceB (p g v) fun f => same W g v f h lo hi w o

/-- A store of `k` bytes, public if `p`, through the base `n`. -/
def st (n : Reg) (off k : Nat) (p : PubF) : Fn := fun W g v f h lo hi w o =>
  stK W o n off k (p g v) fun o => (g.insert n).force fun g => same W g v f h lo hi w o

/-- A store of 16 bytes, the first 8 public if `p` and the others if `q`, through the base `n`. -/
def st2 (n : Reg) (off : Nat) (p q : PubF) : Fn := fun W g v f h lo hi w o =>
  stK W o n off 8 (p g v) fun o => stK W o n (Nat.add off 8) 8 (q g v) fun o =>
    (g.insert n).force fun g => same W g v f h lo hi w o

/-- A store of 8 bytes, public if `p`, through the stack pointer. -/
def stSp (off : Nat) (p : PubF) : Fn := fun W g v f h lo hi w o =>
  stSpK W o off 8 (p g v) fun o => same W g v f h lo hi w o

/-- The taint after a write of the vector register `d`, public if `p`. -/
def wv (d : VReg) (p : PubF) : Fn := fun W g v f h lo hi w o =>
  (bif p g v then v.insert d else v.erase d).force fun v => (lo.erase d).force fun lo => (hi.erase d).force fun hi =>
    same W g v f h lo hi w o

/-- A load into the vector register `d`, through the base `n`. -/
def ldv (n : Reg) (d : VReg) : Fn := fun W g v f h lo hi w o =>
  (g.insert n).force fun g => wv d (p0 false) W g v f h lo hi w o

/-- The taint after a write of half `k` of the vector register `d`, public if `n` is. -/
def wl (d : VReg) (k : Bool) (n : Reg) : Fn := fun W g v f h lo hi w o =>
  (bif v.mem d then lo.insert d else lo).force fun lo => (bif v.mem d then hi.insert d else hi).force fun hi =>
    (v.erase d).force fun v =>
      bif k then (bif g.mem n then hi.insert d else hi.erase d).force fun hi => same W g v f h lo hi w o
      else (bif g.mem n then lo.insert d else lo.erase d).force fun lo => same W g v f h lo hi w o

/-- `bitsOf`. -/
def bitsK (n : Nat) : Nat := bif Nat.ble 2 n then bif Nat.ble 256 n then 16 else 8 else 1

/-- `wget`. -/
def wgetK (w : List (Reg × Nat)) (r : Reg) : Nat := (getK w r).getD 64

/-- The smaller. -/
def minK (a b : Nat) : Nat := bif Nat.ble a b then a else b

/-- The bits of the result that may be secret after a write of size `sz`. -/
def hkS : Size → Nat
  | .w => 32
  | .x => 64

/-- `lsr`, by its size. -/
def lsrK (d n : Reg) (sh : Nat) : Size → Fn
  | .w => wr d (p1 n) 32
  | .x => wr d (p1 n) (Nat.sub 64 sh)

/-- `add` of an immediate, by its size. -/
def addK (d n : Reg) (k : Nat) : Size → Fn
  | .w => wr d (p1 n) 32
  | .x => wrP d (p1 n) fun _ _ p => (getK p n).map fun a => Nat.add a k

/-- `sub` of an immediate, by its size. -/
def subK (d n : Reg) (k : Nat) : Size → Fn
  | .w => wr d (p1 n) 32
  | .x => wrP d (p1 n) fun _ _ p => (getK p n).bind fun a => bif Nat.ble k a then some (Nat.sub a k) else none

/-- `movz`, by its size. -/
def movzK (d : Reg) (imm : BitVec 16) (hw : Nat) : Size → Fn
  | .w => wr d (p0 true) 32
  | .x => bif Nat.beq hw 0 then wrW d (p0 true) fun _ => bitsK imm.toNat else wr d (p0 true) 64

/-- The logical operations, by their size. -/
def logicK (op : LogicOp) (d n m : Reg) : Size → Fn
  | .w => wr d (p2 n m) 32
  | .x => match op with
    | .and => wrW d (p2 n m) fun w => minK (wgetK w n) (wgetK w m)
    | _ => wr d (p2 n m) 64

/-- `ins`, by its arrangement. -/
def insK (d : VReg) (k : Nat) (n : Reg) : VArr → Fn
  | .d2 => wl d (Nat.beq k 1) n
  | _ => wv d (p0 false)

/-- The vector operations. -/
def vopFn : VOp → Fn
  | .movi0 d => wv d (p0 true)
  | .mov d n => wv d (pv n)
  | .dup _ d n => wv d (p1 n)
  | .add _ d n m | .sub _ d n m => wv d (pv2 n m)
  | .ins a d k n => insK d k n a
  | op => wv op.dst (p0 false)

/-- `vopFn`, with its cases closed (`inline_match%`). -/
def vopFnK : VOp → Fn := inline_match% vopFn VOp.dst

theorem vopFnK_eq (op : VOp) : vopFnK op = vopFn op := by cases op <;> rfl

/-- `stepG`, as a function of the instruction first, of the parts of the taint. -/
def stepGFn : Instr → Fn
  | .add sz d n m | .sub sz d n m => wr d (p2 n m) (hkS sz)
  | .adds _ d n m | .subs _ d n m => wrF d (p2 n m)
  | .logic op sz d n m => logicK op d n m sz
  | .logicRor _ _ d n m _ | .bicRor _ d n m _ | .extr _ d n m _ | .mul _ d n m | .umulh d n m | .umull d n m =>
    wr d (p2 n m) 64
  | .adcs _ d _ _ | .sbcs _ d _ _ => wrS d
  | .adc _ d _ _ | .sbc _ d _ _ | .csel _ d _ _ | .cselc _ d _ _ _ | .csneg _ d _ _ _ | .adrSym d _ | .mrsDit d
  | .ldrSp d _ => wr d (p0 false) 64
  | .tst _ n m => sameF (p2 n m)
  | .ccmp .. => sameF (p0 false)
  | .madd _ d n m a | .umaddl d n m a => wr d (p3 n m a) 64
  | .addImm sz d n k => addK d n k sz
  | .subImm sz d n k => subK d n k sz
  | .lsr sz d n sh => lsrK d n sh sz
  | .ror _ d n _ | .lsl _ d n _ | .rev32 d n | .rev d n | .clz _ d n | .rbit _ d n => wr d (p1 n) 64
  | .addSp d imm => wrP d (p0 true) fun W d₀ _ => some (Nat.add (Nat.sub W d₀) imm)
  | .movz sz d imm hw => movzK d imm hw sz
  | .ldrTbl _ d .. => wr d (p0 true) 64
  | .movk _ d _ _ => wr d (p1 d) 64
  | .ldr _ t n _ | .ldrb t n _ => ld n t
  | .ldp t1 t2 n _ => ld2 n t1 t2
  | .str sz t n off => st n off sz.bytes (p1 t)
  | .strb t n off => st n off 1 (p1 t)
  | .stp t1 t2 n off => st2 n off (p1 t1) (p1 t2)
  | .strq t n off => st n off 16 (pv t)
  | .strSp t off => stSp off (p1 t)
  | .ldrq t n _ => ldv n t
  | .ldrqTbl t .. => wv t (p0 true)
  | .umov _ d n _ => wr d (pv n) 64
  | .vop op => vopFnK op
  | .align _ | .msrDitImm _ | .barrier _ => same
  | .blr _ | .push .. | .pop .. | .alloc _ | .free _ => fun _ _ _ _ _ _ _ _ _ => none

/-- `stepGFn`, with its cases closed (`inline_match%`). -/
def stepGFnK : Instr → Fn := inline_match% stepGFn

theorem stepGFnK_eq (i : Instr) : stepGFnK i = stepGFn i := by cases i <;> rfl

/-! ### The step is `stepG` -/

theorem ones_pos_land {P a n : Nat} (h : Nat.land (Nat.shiftRight P a) (ones n) = ones n) : bset P a n = P := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_bset]
  cases hk : decide (a ≤ k) && decide (k < a + n)
  · rw [Bool.or_false]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
    have hb := congrArg (fun x => x.testBit (k - a)) h
    simp only [show Nat.land (Nat.shiftRight P a) (ones n) = (P >>> a) &&& ones n from rfl, Nat.testBit_and,
      Nat.testBit_shiftRight, testBit_ones, show k - a < n by omega, decide_true, Bool.and_true,
      show a + (k - a) = k by omega] at hb
    rw [hb, Bool.or_true]

theorem zero_land {P a n : Nat} (h : Nat.land (Nat.shiftRight P a) (ones n) = 0) : bclr P a n = P := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_bclr]
  cases hk : decide (a ≤ k) && decide (k < a + n)
  · rw [Bool.not_false, Bool.and_true]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
    have hb := congrArg (fun x => x.testBit (k - a)) h
    simp only [show Nat.land (Nat.shiftRight P a) (ones n) = (P >>> a) &&& ones n from rfl, Nat.testBit_and,
      Nat.testBit_shiftRight, testBit_ones, show k - a < n by omega, decide_true, Bool.and_true,
      show a + (k - a) = k by omega, Nat.zero_testBit] at hb
    rw [hb, Bool.false_and]

theorem maskK_eq {α : Type} (W a n P : Nat) (pub : Bool) (k : Nat → α) :
    maskK W a n P pub k = k (if a + n ≤ W then (if pub then bset P a n else bclr P a n) else (if pub then P else 0)) := by
  simp only [maskK, KList.ble_eq, show Nat.add a n = a + n from rfl]
  by_cases hW : a + n ≤ W <;> cases pub <;>
    simp only [hW, decide_true, decide_false, Bool.cond_true, Bool.cond_false, ↓reduceIte, Bool.false_eq_true]
  · cases hb : Nat.beq (Nat.land (Nat.shiftRight P a) (ones n)) 0
    · rfl
    · rw [zero_land (Nat.eq_of_beq_eq_true hb)]; rfl
  · cases hb : Nat.beq (Nat.land (Nat.shiftRight P a) (ones n)) (ones n)
    · rfl
    · rw [ones_pos_land (Nat.eq_of_beq_eq_true hb)]; rfl

/-- The window after a store. -/
def stO (W : Nat) (o : Win) (τ : RTaintB.T) (st : Base × Nat × Nat × Src) : Win :=
  o.map fun (d₀, P, p) => (d₀, storeP W d₀ p τ P st, p)

theorem stK_eq {α : Type} (W : Nat) (o : Win) (b : Reg) (off n : Nat) (τ : RTaintB.T) (src : Src) (k : Win → α) :
    stK W o b off n (srcPub τ src) k = k (stO W o τ (.reg b, off, n, src)) := by
  obtain _ | ⟨d₀, P, p⟩ := o
  · rfl
  simp only [stK, getK_eq, maskK_eq, forceN_eq, stO, Option.map_some, storeP, offOf,
    show ∀ a b : Nat, Nat.add a b = a + b from fun _ _ => rfl]
  cases hf : (p.find? (·.1 == b)).map (·.2)
  · simp only
    cases srcPub τ src <;> rfl
  · rfl

theorem stSpK_eq {α : Type} (W : Nat) (o : Win) (off n : Nat) (τ : RTaintB.T) (src : Src) (k : Win → α) :
    stSpK W o off n (srcPub τ src) k = k (stO W o τ (.sp, off, n, src)) := by
  obtain _ | ⟨d₀, P, p⟩ := o
  · rfl
  simp only [stSpK, maskK_eq, forceN_eq, stO, Option.map_some, storeP, offOf,
    show ∀ a b : Nat, Nat.add a b = a + b from fun _ _ => rfl, show ∀ a b : Nat, Nat.sub a b = a - b from fun _ _ => rfl]

theorem ptrO_eq {α : Type} (o : Win) (dd : Reg) (off : Nat → List (Reg × Nat) → Option Nat) (k : Win → α) :
    ptrO o dd off k = k (o.map fun (d₀, P, p) => (d₀, P, match off d₀ p with
      | none => p.filter fun e => !(dd == e.1)
      | some a => (dd, a) :: p.filter fun e => !(dd == e.1))) := by
  obtain _ | ⟨d₀, P, p⟩ := o
  · rfl
  simp only [ptrO, Option.map_some, forceN_eq, keepL_eq, keepO_eq, dropO]
  cases off d₀ p <;> rfl


theorem bif_set (g : RegSet Reg) (d : Reg) (p : Bool) : (bif p then g.insert d else g.erase d) = Taint.set g d p := by
  cases p <;> rfl

theorem bif_setV (v : RegSet VReg) (d : VReg) (p : Bool) :
    (bif p then v.insert d else v.erase d) = VectorTaint.setV v d p := by cases p <;> rfl

/-- The result's bits after a write of `d`. -/
def hAfter (g : RegSet Reg) (c : Bool) (hk h : Nat) : Nat :=
  if Taint.pub g .x0 then 0 else if c then hk else h

theorem forceN_h {α : Type} (g : RegSet Reg) (c : Bool) (hk h : Nat) (k : Nat → α) :
    forceN (bif g.mem .x0 then 0 else bif c then hk else h) k = k (hAfter g c hk h) := by
  rw [forceN_eq, hAfter, Taint.pub]
  cases g.mem .x0 <;> cases c <;> rfl

theorem forceN_h' {α : Type} (g : RegSet Reg) (h : Nat) (k : Nat → α) :
    forceN (bif g.mem .x0 then 0 else h) k = k (hAfter g false 0 h) := forceN_h g false 0 h k

theorem bitsK_eq (n : Nat) : bitsK n = RTaintB.bitsOf n := by
  simp only [bitsK, RTaintB.bitsOf, KList.ble_eq]
  by_cases h₂ : n < 2
  · simp only [h₂, ↓reduceIte, show ¬ 2 ≤ n by omega, decide_false, Bool.cond_false]
  · by_cases h₃ : n < 256
    · simp only [h₂, h₃, ↓reduceIte, show 2 ≤ n by omega, show ¬ 256 ≤ n by omega, decide_true, decide_false,
        Bool.cond_true, Bool.cond_false]
    · simp only [h₂, h₃, ↓reduceIte, show 2 ≤ n by omega, show 256 ≤ n by omega, decide_true, Bool.cond_true]

theorem minK_eq (a b : Nat) : minK a b = min a b := by
  simp only [minK, KList.ble_eq, Nat.min_def]
  cases h : decide (a ≤ b)
  · rw [ite_eq_right (of_decide_eq_false h)]; rfl
  · rw [ite_eq_left (of_decide_eq_true h)]; rfl

theorem wgetK_eq (w : List (Reg × Nat)) (r : Reg) : wgetK w r = RTaintB.wget w r := by
  rw [wgetK, getK_eq]; rfl

theorem setR_eq (d : Reg) (p : Bool) (hk : Nat) (g : RegSet Reg) (v : RegSet VReg) (f : Bool) (h : Nat)
    (lo hi : RegSet VReg) (w : List (Reg × Nat)) (o : Win) :
    setR d p hk g v f h lo hi w o =
      some ((((((Taint.set g d p, v), f, hAfter (Taint.set g d p) (d == .x0) hk h), lo, hi)), w), o) := by
  simp only [setR, bif_set, RegSet.force_eq, regEq_eq, forceN_h]

section
variable {W : Nat} {g g₁ g' : RegSet Reg} {v v' : RegSet VReg} {f f' : Bool} {h h' : Nat} {lo hi lo' hi' : RegSet VReg}
  {w w' : List (Reg × Nat)} {o : Win} {i : Instr}

/-- `stepG`, from what its parts give. -/
theorem stepG_parts (hb : RTaintCT.pubBase (((g, v), f, h), lo, hi) i = (((g₁, v), f, h), lo, hi))
    (hv : RTaint.vstep (g₁, v) i = some (g', v')) (hf : RTaint.fstep g₁ f i = f') (hh : RTaint.hstep g' h i = h')
    (hl : RTaintL.lstep ((g₁, v), f, h) (lo, hi) i = (lo', hi')) (hw : RTaintB.wstep w i = w') :
    stepG W ((((((g, v), f, h), lo, hi)), w), o) i =
      some ((((((g', v'), f', h'), lo', hi')), w'), o.map fun (d, P, p) =>
        (d, storesP W d p ((((g, v), f, h), lo, hi), w) P (stores i), ptrStep W d p i)) := by
  simp only [stepG, RTaintB.step, RTaintCT.step, hb, RTaintL.step, RTaint.step, hv, hf, hh, hl, hw, Option.map_some]

theorem hh_of {d : Reg} {hk : Nat} (hc : clobbers i .x0 = (d == .x0))
    (hx : d = .x0 → ∀ g' h, RTaint.hstep g' h i = hAfter g' true hk h) (g' : RegSet Reg) (h : Nat) :
    RTaint.hstep g' h i = hAfter g' (d == .x0) hk h := by
  cases hd : d == .x0
  · simp only [RTaint.hstep, hAfter, hc, hd, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  · exact hx (beq_iff_eq.mp hd) g' h

theorem wr_eq {d : Reg} {p : PubF} {hk : Nat}
    (hb : RTaintCT.pubBase (((g, v), f, h), lo, hi) i = (((g₁, v), f, h), lo, hi))
    (hv : RTaint.vstep (g₁, v) i = some (Taint.set g₁ d (p g₁ v), v)) (hf : RTaint.fstep g₁ f i = f')
    (hh : ∀ g' h, RTaint.hstep g' h i = hAfter g' (d == .x0) hk h)
    (hl : RTaintL.lstep ((g₁, v), f, h) (lo, hi) i = (lo, hi))
    (hw : RTaintB.wstep w i = w.filter fun e => !clobbers i e.1)
    (hs : stores i = []) (hp : ∀ W d₀ p, ptrStep W d₀ p i = p.filter fun e => !clobbers i e.1)
    (hc : ∀ r, clobbers i r = (d == r)) :
    wr d p hk W g₁ v f' h lo hi w o = stepG W ((((((g, v), f, h), lo, hi)), w), o) i := by
  rw [stepG_parts hb hv hf (hh _ _) hl hw]
  simp only [wr, keepL_eq, keepO_eq, setR_eq, hc, hs, hp, storesP]
  rfl

/-- A load or a store through `n` is of a public base, once `n` is public. -/
theorem vstep_ins {n : Reg} {x : RegSet Reg}
    (h : RTaint.vstep (g.insert n, v) i =
      (if Taint.pub (g.insert n) n = true then some x else none).map fun g => (g, v')) :
    RTaint.vstep (g.insert n, v) i = some (x, v') := by
  rw [h, show Taint.pub (g.insert n) n = true from RegSet.mem_insert.mpr (.inl rfl)]; rfl

theorem wrF_eq (d : Reg) (p : PubF) (W : Nat) (g : RegSet Reg) (v : RegSet VReg) (f : Bool) (h : Nat) (lo hi : RegSet VReg)
    (w : List (Reg × Nat)) (o : Win) :
    wrF d p W g v f h lo hi w o = wr d p 64 W g v (p g v) h lo hi w o := by
  rw [wrF, forceB_eq]; rfl

theorem sameF_eq (p : PubF) (W : Nat) (g : RegSet Reg) (v : RegSet VReg) (f : Bool) (h : Nat) (lo hi : RegSet VReg)
    (w : List (Reg × Nat)) (o : Win) :
    sameF p W g v f h lo hi w o = same W g v (p g v) h lo hi w o := by
  rw [sameF, forceB_eq]

theorem wrP_eq {d : Reg} {p : PubF} {off : Nat → Nat → List (Reg × Nat) → Option Nat}
    (hb : RTaintCT.pubBase (((g, v), f, h), lo, hi) i = (((g, v), f, h), lo, hi))
    (hv : RTaint.vstep (g, v) i = some (Taint.set g d (p g v), v)) (hf : RTaint.fstep g f i = f)
    (hh : ∀ g' h, RTaint.hstep g' h i = hAfter g' (d == .x0) 64 h)
    (hl : RTaintL.lstep ((g, v), f, h) (lo, hi) i = (lo, hi))
    (hw : RTaintB.wstep w i = w.filter fun e => !clobbers i e.1)
    (hs : stores i = [])
    (hp : ∀ W d₀ p, ptrStep W d₀ p i = match off W d₀ p with
      | none => p.filter fun e => !clobbers i e.1
      | some a => (d, a) :: p.filter fun e => !clobbers i e.1)
    (hc : ∀ r, clobbers i r = (d == r)) :
    wrP d p off W g v f h lo hi w o = stepG W ((((((g, v), f, h), lo, hi)), w), o) i := by
  rw [stepG_parts hb hv hf (hh _ _) hl hw]
  simp only [wrP, keepL_eq, ptrO_eq, setR_eq, hc, hs, hp, storesP]

theorem wrW_eq {d : Reg} {p : PubF} {n : List (Reg × Nat) → Nat}
    (hb : RTaintCT.pubBase (((g, v), f, h), lo, hi) i = (((g, v), f, h), lo, hi))
    (hv : RTaint.vstep (g, v) i = some (Taint.set g d (p g v), v)) (hf : RTaint.fstep g f i = f)
    (hh : ∀ g' h, RTaint.hstep g' h i = hAfter g' (d == .x0) 64 h)
    (hl : RTaintL.lstep ((g, v), f, h) (lo, hi) i = (lo, hi))
    (hw : RTaintB.wstep w i = (d, n w) :: w.filter fun e => !clobbers i e.1)
    (hs : stores i = []) (hp : ∀ W d₀ p, ptrStep W d₀ p i = p.filter fun e => !clobbers i e.1)
    (hc : ∀ r, clobbers i r = (d == r)) :
    wrW d p n W g v f h lo hi w o = stepG W ((((((g, v), f, h), lo, hi)), w), o) i := by
  rw [stepG_parts hb hv hf (hh _ _) hl hw]
  simp only [wrW, forceN_eq, keepL_eq, keepO_eq, setR_eq, hc, hs, hp, storesP]
  rfl

theorem filter_none {l : List (Reg × Nat)} (hc : ∀ r, clobbers i r = false) :
    (l.filter fun e => !clobbers i e.1) = l := by
  exact List.filter_eq_self.mpr fun e _ => by rw [hc, Bool.not_false]

/-- `same`, after the stores of an instruction that writes no general-purpose register. -/
theorem same_eq (hb : RTaintCT.pubBase (((g, v), f, h), lo, hi) i = (((g₁, v), f, h), lo, hi))
    (hv : RTaint.vstep (g₁, v) i = some (g₁, v')) (hf : RTaint.fstep g₁ f i = f')
    (hh : ∀ g' h, RTaint.hstep g' h i = hAfter g' false 0 h)
    (hl : RTaintL.lstep ((g₁, v), f, h) (lo, hi) i = (lo', hi'))
    (hw : RTaintB.wstep w i = w.filter fun e => !clobbers i e.1)
    (hp : ∀ W d₀ p, ptrStep W d₀ p i = p.filter fun e => !clobbers i e.1)
    (hc : ∀ r, clobbers i r = false) {o' : Win}
    (ho : o' = o.map fun (d, P, p) => (d, storesP W d p ((((g, v), f, h), lo, hi), w) P (stores i), p)) :
    same W g₁ v' f' h lo' hi' w o' = stepG W ((((((g, v), f, h), lo, hi)), w), o) i := by
  rw [stepG_parts hb hv hf (hh _ _) hl (hw.trans (filter_none hc)), ho]
  simp only [same, forceN_h', hp, filter_none hc]

/-- `same`, of an instruction that stores nothing. -/
theorem same_eq₀ (hb : RTaintCT.pubBase (((g, v), f, h), lo, hi) i = (((g₁, v), f, h), lo, hi))
    (hv : RTaint.vstep (g₁, v) i = some (g₁, v')) (hf : RTaint.fstep g₁ f i = f')
    (hh : ∀ g' h, RTaint.hstep g' h i = hAfter g' false 0 h)
    (hl : RTaintL.lstep ((g₁, v), f, h) (lo, hi) i = (lo', hi'))
    (hw : RTaintB.wstep w i = w.filter fun e => !clobbers i e.1) (hs : stores i = [])
    (hp : ∀ W d₀ p, ptrStep W d₀ p i = p.filter fun e => !clobbers i e.1) (hc : ∀ r, clobbers i r = false) :
    same W g₁ v' f' h lo' hi' w o = stepG W ((((((g, v), f, h), lo, hi)), w), o) i :=
  same_eq hb hv hf hh hl hw hp hc (by rw [hs]; cases o <;> rfl)

/-- `wv`, of an instruction that writes the vector register `d` alone. -/
theorem wv_eq {d : VReg} {p : PubF} (hb : RTaintCT.pubBase (((g, v), f, h), lo, hi) i = (((g₁, v), f, h), lo, hi))
    (hv : RTaint.vstep (g₁, v) i = some (g₁, VectorTaint.setV v d (p g₁ v))) (hf : RTaint.fstep g₁ f i = f)
    (hh : ∀ g' h, RTaint.hstep g' h i = hAfter g' false 0 h)
    (hl : RTaintL.lstep ((g₁, v), f, h) (lo, hi) i = (lo.erase d, hi.erase d))
    (hw : RTaintB.wstep w i = w.filter fun e => !clobbers i e.1) (hs : stores i = [])
    (hp : ∀ W d₀ p, ptrStep W d₀ p i = p.filter fun e => !clobbers i e.1) (hc : ∀ r, clobbers i r = false) :
    wv d p W g₁ v f h lo hi w o = stepG W ((((((g, v), f, h), lo, hi)), w), o) i := by
  rw [← same_eq₀ hb hv hf hh hl hw hs hp hc]
  simp only [wv, bif_setV, RegSet.force_eq]

theorem st_eq (n : Reg) (off k : Nat) (p : PubF) (src : Src) (hp : p g v = srcPub ((((g, v), f, h), lo, hi), w) src) :
    st n off k p W g v f h lo hi w o = same W (g.insert n) v f h lo hi w
      (o.map fun (d, P, p) => (d, storesP W d p ((((g, v), f, h), lo, hi), w) P [(.reg n, off, k, src)], p)) := by
  rw [st, hp, stK_eq]; rfl

theorem st2_eq (n : Reg) (off : Nat) (p q : PubF) (src src' : Src) (hp : p g v = srcPub ((((g, v), f, h), lo, hi), w) src)
    (hq : q g v = srcPub ((((g, v), f, h), lo, hi), w) src') :
    st2 n off p q W g v f h lo hi w o = same W (g.insert n) v f h lo hi w
      (o.map fun (d, P, p) => (d, storesP W d p ((((g, v), f, h), lo, hi), w) P
        [(.reg n, off, 8, src), (.reg n, off + 8, 8, src')], p)) := by
  rw [st2, hp, hq, stK_eq, stK_eq]
  cases o <;> rfl

theorem stSp_eq (off : Nat) (p : PubF) (src : Src) (hp : p g v = srcPub ((((g, v), f, h), lo, hi), w) src) :
    stSp off p W g v f h lo hi w o = same W g v f h lo hi w
      (o.map fun (d, P, p) => (d, storesP W d p ((((g, v), f, h), lo, hi), w) P [(.sp, off, 8, src)], p)) := by
  rw [stSp, hp, stSpK_eq]; rfl

theorem stepGFn_eq (W : Nat) (g : RegSet Reg) (v : RegSet VReg) (f : Bool) (h : Nat) (lo hi : RegSet VReg)
    (w : List (Reg × Nat)) (o : Win) (i : Instr) :
    stepGFn i W g v f h lo hi w o = stepG W ((((((g, v), f, h), lo, hi)), w), o) i := by
  cases i
  case add sz d n m | sub sz d n m =>
    exact wr_eq rfl rfl rfl (hh_of rfl fun e _ _ => by subst e; cases sz <;> rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
  case adc d _ _ | sbc d _ _ | csel d _ _ | cselc d _ _ _ | csneg d _ _ _ | adrSym d _ | mrsDit d | ldrSp d _
    | bicRor _ d _ _ _ | extr _ d _ _ _ | mul _ d _ _ | umulh d _ _ | umull d _ _ | madd _ d _ _ _ | umaddl d _ _ _ | ror _ d _ _
    | lsl _ d _ _ | rev32 d _ | rev d _ | clz _ d _ | rbit _ d _ | movk _ d _ _ | umov _ d _ _ =>
    exact wr_eq rfl rfl rfl (hh_of rfl fun e _ _ => by subst e; rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
  case logicRor _ _ d _ _ _ | ldrTbl _ d _ _ _ _ =>
    exact wr_eq rfl rfl rfl (hh_of rfl fun e _ _ => by subst e; rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
  case adcs sz d n m | sbcs sz d n m =>
    exact wr_eq rfl rfl rfl (hh_of rfl fun e _ _ => by subst e; rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
  case adds sz d n m | subs sz d n m =>
    refine (wrF_eq d (p2 n m) W g v f h lo hi w o).trans ?_
    exact wr_eq (p := p2 n m) rfl rfl rfl (hh_of rfl fun e _ _ => by subst e; rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
  case lsr sz d n sh =>
    cases sz <;>
      exact wr_eq rfl rfl rfl (hh_of rfl fun e _ _ => by subst e; rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
  case addImm sz d n k =>
    cases sz
    · exact wr_eq rfl rfl rfl (hh_of rfl fun e _ _ => by subst e; rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
    · refine wrP_eq (i := .addImm .x d n k) (p := p1 n) (off := fun _ _ p => (getK p n).map fun a => Nat.add a k)
        rfl rfl rfl (hh_of rfl fun e _ _ => by subst e; rfl) rfl rfl rfl (fun W d₀ p => ?_) (fun _ => rfl)
      simp only [ptrStep, offOf, getK_eq]
      cases (p.find? (·.1 == n)).map (·.2) <;> rfl
  case subImm sz d n k =>
    cases sz
    · exact wr_eq rfl rfl rfl (hh_of rfl fun e _ _ => by subst e; rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
    · refine wrP_eq (i := .subImm .x d n k) (p := p1 n)
        (off := fun _ _ p => (getK p n).bind fun a => bif Nat.ble k a then some (Nat.sub a k) else none)
        rfl rfl rfl (hh_of rfl fun e _ _ => by subst e; rfl) rfl rfl rfl (fun W d₀ p => ?_) (fun _ => rfl)
      simp only [ptrStep, offOf, getK_eq]
      cases (p.find? (·.1 == n)).map (·.2) with
      | none => rfl
      | some a =>
        simp only [Option.bind_some, KList.ble_eq]
        by_cases hk : k ≤ a <;> simp only [hk, decide_true, decide_false, Bool.cond_true, Bool.cond_false, ↓reduceIte] <;> rfl
  case addSp d imm =>
    exact wrP_eq (i := .addSp d imm) (p := p0 true) (off := fun W d₀ _ => some (Nat.add (Nat.sub W d₀) imm))
      rfl rfl rfl (hh_of rfl fun e _ _ => by subst e; rfl) rfl rfl rfl (fun W d₀ p => rfl) (fun _ => rfl)
  case movz sz d imm hw =>
    cases sz
    · exact wr_eq rfl rfl rfl (hh_of rfl fun e _ _ => by subst e; rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
    · cases hw
      · refine wrW_eq (i := .movz .x d imm 0) (d := d) (p := p0 true) (n := fun _ => bitsK imm.toNat) rfl rfl rfl (hh_of rfl fun e _ _ => by subst e; rfl) rfl ?_ rfl (fun _ _ _ => rfl) (fun _ => rfl)
        simp only [RTaintB.wstep, bitsK_eq]
      · exact wr_eq rfl rfl rfl (hh_of rfl fun e _ _ => by subst e; rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
  case logic op sz d n m =>
    cases sz
    · cases op <;>
        exact wr_eq rfl rfl rfl (hh_of rfl fun e _ _ => by subst e; rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
    · cases op
      case and =>
        refine wrW_eq (i := .logic .and .x d n m) (d := d) (p := p2 n m) (n := fun w => minK (wgetK w n) (wgetK w m)) rfl rfl rfl (hh_of rfl fun e _ _ => by subst e; rfl) rfl ?_ rfl (fun _ _ _ => rfl) (fun _ => rfl)
        simp only [RTaintB.wstep, minK_eq, wgetK_eq]
      all_goals exact wr_eq rfl rfl rfl (hh_of rfl fun e _ _ => by subst e; rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
  case ldr sz t n off | ldrb t n off =>
    exact wr_eq rfl (vstep_ins rfl) rfl (hh_of rfl fun e _ _ => by subst e; rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
  case tst sz n m =>
    refine (sameF_eq (p2 n m) W g v f h lo hi w o).trans ?_
    exact same_eq₀ rfl rfl rfl (fun _ _ => rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
  case ccmp =>
    refine (sameF_eq (p0 false) W g v f h lo hi w o).trans ?_
    exact same_eq₀ rfl rfl rfl (fun _ _ => rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
  case align | msrDitImm | barrier =>
    exact same_eq₀ rfl rfl rfl (fun _ _ => rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
  case blr | push | pop | alloc | free => rfl
  case str sz t n off =>
    refine (st_eq n off sz.bytes (p1 t) (.gpr t) rfl).trans ?_
    exact same_eq (i := .str sz t n off) rfl (vstep_ins rfl) rfl (fun _ _ => rfl) rfl rfl (fun _ _ _ => rfl) (fun _ => rfl) rfl
  case strb t n off =>
    refine (st_eq n off 1 (p1 t) (.gpr t) rfl).trans ?_
    exact same_eq (i := .strb t n off) rfl (vstep_ins rfl) rfl (fun _ _ => rfl) rfl rfl (fun _ _ _ => rfl) (fun _ => rfl) rfl
  case strq t n off =>
    refine (st_eq n off 16 (pv t) (.vec t) rfl).trans ?_
    exact same_eq (i := .strq t n off) rfl (vstep_ins rfl) rfl (fun _ _ => rfl) rfl rfl (fun _ _ _ => rfl) (fun _ => rfl) rfl
  case stp t1 t2 n off =>
    refine (st2_eq n off (p1 t1) (p1 t2) (.gpr t1) (.gpr t2) rfl rfl).trans ?_
    exact same_eq (i := .stp t1 t2 n off) rfl (vstep_ins rfl) rfl (fun _ _ => rfl) rfl rfl (fun _ _ _ => rfl) (fun _ => rfl) rfl
  case strSp t off =>
    refine (stSp_eq off (p1 t) (.gpr t) rfl).trans ?_
    exact same_eq (i := .strSp t off) rfl rfl rfl (fun _ _ => rfl) rfl rfl (fun _ _ _ => rfl) (fun _ => rfl) rfl
  case ldp t1 t2 n off =>
    rw [stepG_parts (g' := Taint.set (Taint.set (g.insert n) t1 false) t2 false) (v' := v) (f' := f)
      (h' := hAfter (Taint.set (Taint.set (g.insert n) t1 false) t2 false) (Reg.x0 == t1 || Reg.x0 == t2) 64 h) (lo' := lo)
      (hi' := hi) (w' := w.filter fun e => !(e.1 == t1 || e.1 == t2)) rfl (vstep_ins rfl) rfl (by
        unfold hAfter RTaint.hstep
        simp only [clobbers, Bool.not_eq_eq_eq_not, Bool.not_true]
        cases Taint.pub (Taint.set (Taint.set (g.insert n) t1 false) t2 false) .x0 <;>
          cases (Reg.x0 == t1 || Reg.x0 == t2) <;> rfl) rfl rfl]
    show ld2 n t1 t2 W g v f h lo hi w o = _
    simp only [ld2, keepL_eq, keepO_eq, RegSet.force_eq, regEq_eq, forceN_h, stores, storesP, ptrStep, clobbers, dropO,
      List.filter_filter, Option.map_map]
    have e : (fun e : Reg × Nat => !(t2 == e.1) && !(t1 == e.1)) = fun e => !(e.1 == t1 || e.1 == t2) := by
      funext e
      rw [Bool.not_or, Bool.and_comm, Bool.beq_comm (a := t1), Bool.beq_comm (a := t2)]
    rw [e, Bool.beq_comm (a := t1), Bool.beq_comm (a := t2)]
    obtain _ | ⟨d₀, P, p⟩ := o
    · rfl
    · simp only [Option.map_some, Function.comp_apply, List.filter_filter, e]; rfl
  case ldrq t n off =>
    exact wv_eq (p := p0 false) rfl (vstep_ins rfl) rfl (fun _ _ => rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
  case ldrqTbl t n off name words =>
    exact wv_eq (p := p0 true) rfl rfl rfl (fun _ _ => rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
  case vop op =>
    refine (congrFun (congrFun (congrFun (congrFun (congrFun (congrFun (congrFun (congrFun (congrFun (vopFnK_eq op) W) g) v) f) h) lo) hi) w) o).trans ?_
    cases op
    case mov d n =>
      exact wv_eq (p := pv n) rfl rfl rfl (fun _ _ => rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
    case movi0 d =>
      exact wv_eq (p := p0 true) rfl rfl rfl (fun _ _ => rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
    case dup _ d n =>
      exact wv_eq (p := p1 n) rfl rfl rfl (fun _ _ => rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
    case add _ d n m | sub _ d n m =>
      exact wv_eq (p := pv2 n m) rfl rfl rfl (fun _ _ => rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
    case ins a d k n =>
      cases a
      case d2 =>
        show wl d (Nat.beq k 1) n W g v f h lo hi w o = _
        have hl : RTaintL.lstep ((g, v), f, h) (lo, hi) (.vop (.ins .d2 d k n)) =
            LaneTaint.put (if v.mem d then LaneTaint.both (lo, hi) d true else (lo, hi)) (k == 1) d (Taint.pub g n) := rfl
        rw [← same_eq₀ (v' := v.erase d) rfl rfl rfl (fun _ _ => rfl) hl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)]
        simp only [wl, RegSet.force_eq, bif_setV, KList.beq_eq]
        rw [show g.mem n = Taint.pub g n from rfl]
        generalize Taint.pub g n = c
        cases v.mem d <;> cases k == 1 <;> cases c <;> rfl
      all_goals exact wv_eq (p := p0 false) rfl rfl rfl (fun _ _ => rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
    all_goals
      exact wv_eq (p := p0 false) rfl rfl rfl (fun _ _ => rfl) rfl rfl rfl (fun _ _ _ => rfl) (fun _ => rfl)
end

/-- `stepG`, for the kernel. -/
def stepGK (W : Nat) (τ : T) (i : Instr) : Option T :=
  match τ with
  | ((((((g, v), f, h), lo, hi)), w), o) => stepGFnK i W g v f h lo hi w o

theorem stepGK_eq (W : Nat) (τ : T) (i : Instr) : stepGK W τ i = stepG W τ i := by
  obtain ⟨⟨⟨⟨⟨g, v⟩, f, h⟩, lo, hi⟩, w⟩, o⟩ := τ
  rw [stepGK, stepGFnK_eq]
  exact stepGFn_eq W g v f h lo hi w o i

/-- `k τ`, with the taint `τ` evaluated, but the mask. -/
def forceG {α : Type} (τ : T) (k : T → α) : α :=
  match τ with
  | ((((((g, v), f, h), lo, hi)), w), o) =>
    g.force fun g => v.force fun v => forceB f fun f => forceN h fun h => lo.force fun lo => hi.force fun hi =>
      forceL w fun w =>
        match o with
        | none => k ((((((g, v), f, h), lo, hi)), w), none)
        | some (d, P, p) => forceN d fun d => forceL p fun p => k ((((((g, v), f, h), lo, hi)), w), some (d, P, p))

theorem forceG_eq {α : Type} (τ : T) (k : T → α) : forceG τ k = k τ := by
  obtain ⟨⟨⟨⟨⟨g, v⟩, f, h⟩, lo, hi⟩, w⟩, o⟩ := τ
  simp only [forceG, RegSet.force_eq, forceB_eq, forceN_eq, forceL_eq]
  cases o <;> rfl

/-- `o`, with the taint evaluated. -/
def forceO (o : Option T) : Option T :=
  match o with
  | none => none
  | some τ => forceG τ some

theorem forceO_eq (o : Option T) : forceO o = o := by
  cases o
  · rfl
  · exact forceG_eq _ _

end

/-- A taint as a literal whose numbers are numerals (`Lean.mkRawNatLit`), as
the steps leave them, so that the kernel finds again after a hint what it
evaluated before it. -/
instance (priority := high) : Lean.ToExpr T where
  toTypeExpr := .const ``T []
  toExpr τ :=
    let (((((g, v), f, h), lo, hi), w), o) := τ
    let nat : Lean.Expr := .const ``Nat []
    let reg : Lean.Expr := .const ``Reg []
    let pair (a b : Lean.Expr × Lean.Expr) : Lean.Expr × Lean.Expr :=
      (Lean.mkApp4 (.const ``Prod.mk [0, 0]) a.2 b.2 a.1 b.1, Lean.mkApp2 (.const ``Prod [0, 0]) a.2 b.2)
    let num (n : Nat) : Lean.Expr × Lean.Expr := (Lean.mkRawNatLit n, nat)
    let set (R : Lean.Name) (n : Nat) : Lean.Expr × Lean.Expr :=
      (Lean.mkApp2 (.const ``RegSet.mk []) (.const R []) (Lean.mkRawNatLit n), .app (.const ``RegSet []) (.const R []))
    let list (l : List (Reg × Nat)) : Lean.Expr × Lean.Expr :=
      let ty := Lean.mkApp2 (.const ``Prod [0, 0]) reg nat
      (l.foldr (fun e l => Lean.mkApp3 (.const ``List.cons [0]) ty (pair (Lean.toExpr e.1, reg) (num e.2)).1 l)
        (.app (.const ``List.nil [0]) ty), .app (.const ``List [0]) ty)
    let win (d P : Nat) (p : List (Reg × Nat)) := pair (num d) (pair (num P) (list p))
    let opt := match o with
      | none => Lean.Expr.app (.const ``Option.none [0]) (win 0 0 []).2
      | some (d, P, p) => Lean.mkApp2 (.const ``Option.some [0]) (win d P p).2 (win d P p).1
    (pair (pair (pair (pair (pair (set ``Reg g.bits) (set ``VReg v.bits)) (pair (Lean.toExpr f, .const ``Bool []) (num h)))
      (pair (set ``VReg lo.bits) (set ``VReg hi.bits))) (list w)) (opt, .app (.const ``Option [0]) (win 0 0 []).2)).1

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
  step := stepGK W
  step_sound ha hs e₁ e₂ hadr := stepG_sound ha ((stepGK_eq W _ _).symm.trans hs) e₁ e₂ hadr
  addrs_length := RTaintCT.addrs_length
  meet := meetG
  meet_left := meetG_left
  meet_right := meetG_right
  le := leG
  le_sound := leG_sound
  call τ := forceG (callG τ) some
  call_sound ha hs e₁ e₂ _ := by
    rw [forceG_eq] at hs
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
  push τ i := forceO (pushG W τ i)
  push_sound ha hs e₁ e₂ _ := pushG_sound ha ((forceO_eq _).symm.trans hs) e₁ e₂
  pop τ i := forceO (popG τ i)
  pop_sound ha hs e₁ e₂ _ := popG_sound ha ((forceO_eq _).symm.trans hs) e₁ e₂

namespace RTaintG

open VG.AArch64 VG.AArch64.Residue VG.AArch64.MemEffect VG.AArch64.RTaintF VG.AArch64.Scrub
  VG.Impl.Scrub.AArch64

/-! ## Clearing only the granules that may differ -/

/-- Every 16-byte granule of the `W` bytes but those of `ks` is in `P`. -/
def granOk (W P : Nat) (ks : List Nat) : Bool :=
  (List.range (W / 16)).all fun k => ks.contains k || Nat.beq (Nat.land (Nat.shiftRight P (16 * k)) 65535) 65535

/-- `doneF r` at depth 0, with the granules of the window not in `ks` agreeing,
each of `ks` in the window, and, if `ks` is empty (no clearing), `x9` and
`v31` public. -/
def doneG (W r : Nat) (ks : List Nat) (τ : T) : Bool :=
  match τ.2 with
  | some (d, P, _) =>
    d == 0 && doneF r (τ.1, some 0) && granOk W P ks && ks.all (fun k => decide (16 * k + 16 ≤ W)) &&
      (!ks.isEmpty || (τ.1.1.1.1.1.mem .x9 && RTaintL.vpub τ.1.1 .v31))
  | none => false

theorem wbase0 (sp : Addr) (W : Nat) : wbase sp 0 W = sp - BitVec.ofNat 64 W := by
  simp [wbase]

theorem off_self (b : Addr) {o : Nat} (ho : o < 2 ^ 64) : (b + BitVec.ofNat 64 o - b).toNat = o := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]

theorem gran_bit {W P : Nat} {ks : List Nat} {b : Addr} (hW : W < 2 ^ 64) (hW16 : W % 16 = 0)
    (h : granOk W P ks = true) {o : Nat} (ho : o < W) (hn : inG b ks (b + BitVec.ofNat 64 o) = false) :
    P.testBit o = true := by
  simp only [inG, off_self b (show o < 2 ^ 64 by omega), List.any_eq_false, decide_eq_true_eq] at hn
  simp only [granOk, List.all_eq_true, List.mem_range, Bool.or_eq_true, List.contains_iff_mem] at h
  rcases h (o / 16) (by omega) with hk | hk
  · exact absurd ⟨by omega, by omega⟩ (hn _ hk)
  · have hk : (P >>> (16 * (o / 16))) &&& ones 16 = ones 16 := Nat.eq_of_beq_eq_true hk
    have := congrArg (fun x => x.testBit (o % 16)) hk
    simp only [Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones,
      show o % 16 < 16 by omega, decide_true, Bool.and_true, show 16 * (o / 16) + o % 16 = o by omega] at this
    exact this

theorem zeroG_out {W : Nat} {ks : List Nat} (hks : ∀ k ∈ ks, 16 * k + 16 ≤ W) {b x : Addr} (m : Mem)
    (h : ¬ (x - b).toNat < W) : zeroG b ks m x = m x := by
  simp only [zeroG]
  split
  · next hin =>
    simp only [inG, List.any_eq_true, decide_eq_true_eq] at hin
    obtain ⟨k, hk, -, h₂⟩ := hin
    have := hks k hk
    omega
  · rfl

/-- What `doneF` gives of the registers and flags after the code. -/
theorem done_regs {τF : RTaintF.T} {r : Nat} {s₁ s₂ s₁' s₂' : State}
    (hd : doneF r τF = true) (hb : RTaintB.Agree τF.1 s₁' (ghost s₁' s₂'))
    (hp₁ : abiPreserved s₁ s₁') (hp₂ : abiPreserved s₂ s₂') (ho : Outside 0 s₁ s₂) :
    (∀ q, q ≠ .x0 → q ≠ .x9 → s₁'.gpr q = s₂'.gpr q) ∧
    s₁'.gpr .x0 >>> r = s₂'.gpr .x0 >>> r ∧
    s₁'.c = s₂'.c ∧ s₁'.nf = s₂'.nf ∧ s₁'.zf = s₂'.zf ∧ s₁'.vf = s₂'.vf ∧
    ∀ w, w ≠ .v31 → s₁'.v w = s₂'.v w := by
  simp only [doneF, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at hd
  obtain ⟨⟨⟨⟨-, hg⟩, hvv⟩, hfl⟩, hx⟩ := hd
  obtain ⟨⟨⟨⟨⟨-, hgr⟩, hvr⟩, hflags, hx0, -⟩, hq⟩, hb₁, hb₂⟩ := hb
  refine ⟨fun q hq0 h9 => ?_, ?_, (hflags hfl).1, (hflags hfl).2.1, (hflags hfl).2.2.1,
    (hflags hfl).2.2.2, fun w h31 => ?_⟩
  · by_cases hpq : q ∈ preserved
    · rw [hp₁.1 q hpq, hp₂.1 q hpq]; exact ho.2.2.1 q hq0
    · exact hgr q (Taint.pub_iff.mp (hg q (mem_scratchNo9 hq0 h9 hpq)))
  · rcases hx with hx | hx
    · exact RTaint.shr_mono hx0 (Nat.le_of_ble_eq_true hx)
    · rw [RTaintB.shr_eq_zero (RTaintB.wget_bound hb₁ .x0) (Nat.le_of_ble_eq_true hx),
        RTaintB.shr_eq_zero (x := s₂'.gpr .x0) (RTaintB.wget_bound hb₂ .x0)
          (Nat.le_of_ble_eq_true hx)]
  · have hw := (hvv w (RTaintL.mem_vregs w)).resolve_left (by simpa using h31)
    by_cases hpv : w ∈ preservedV
    · simp only [List.contains_iff_mem.mpr hpv, ↓reduceIte, Bool.or_eq_true] at hw
      rcases hw with hw | hw
      · exact hvr w hw
      · refine RTaintL.eq_of_halves ?_ (hq true w hw)
        rw [hp₁.2.2 w hpv, hp₂.2.2 w hpv, ho.2.2.2.2.2.2.2.2.2.2.1]
    · have : preservedV.contains w = false := by simpa using hpv
      simp only [this, Bool.false_eq_true, ↓reduceIte, RTaintL.vpub, Bool.or_eq_true,
        Bool.and_eq_true] at hw
      rcases hw with hw | ⟨h₀, h₁'⟩
      · exact hvr w hw
      · exact RTaintL.eq_of_halves (hq false w h₀) (hq true w h₁')

/-- Code verified against its contract, whose analysis (`rtaintG W`, from the
mask `P₀` of the window's bytes the two runs agree on at entry) ends in
`doneG W r ks`, followed by the zeroing of the granules `ks` of the `W` bytes
below the stack pointer, returns without secret residue, with an `r`-bit
result. -/
theorem noResidue_scrubSel {c : Prog isa} {k : Contract isa} {r W : Nat} {ks : List Nat} {P₀ : Nat}
    (hv : Verified target c k) (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0)
    (hsp : ∀ s, k.pre s → W ≤ s.sp.toNat)
    (hP₀ : ∀ s₁ s₂, Outside 0 s₁ s₂ → PAgree W (wbase s₂.sp 0 W) P₀ s₁.mem s₂.mem)
    (h : ∃ hc, ((rtaintG W).check (RTaintB.init, some (0, P₀, [])) c hc).any (doneG W r ks) = true) :
    NoResidue (scrubSel W ks c) k r := by
  intro s₁ s₂ t₁ t₂ s₁'' s₂'' h₁ h₂ hp ho hu e₁ e₂
  obtain ⟨hc, h⟩ := h
  cases hτ : (rtaintG W).check (RTaintB.init, some (0, P₀, [])) c hc with
  | none => rw [hτ] at h; cases h
  | some τ' =>
  rw [hτ] at h
  have hd : doneG W r ks τ' = true := h
  obtain ⟨τ, o⟩ := τ'
  cases o with
  | none => simp [doneG] at hd
  | some o =>
  obtain ⟨d, P, ptrs⟩ := o
  simp only [doneG, Bool.and_eq_true, beq_iff_eq] at hd
  obtain ⟨⟨⟨⟨rfl, hdF⟩, hgran⟩, hks⟩, hnil⟩ := hd
  have hks' : ∀ k ∈ ks, 16 * k + 16 ≤ W := by simpa using hks
  have hinit : AgreeG W (RTaintB.init, some (0, P₀, [])) s₁ s₂ := by
    obtain ⟨d, hdd, hA⟩ := agree_init (W := W) (by omega) ho hu
    obtain rfl : d = 0 := by
      rcases hdd with h | h
      · exact (Option.some.inj h).symm
      · cases h
    exact ⟨hA, hP₀ s₁ s₂ ho, fun _ h => nomatch h⟩
  have run : ∀ {t₁ t₂ s₁' s₂'}, Exec isa c s₁ t₁ s₁' → Exec isa c s₂ t₂ s₂' →
      AgreeG W (τ, some (0, P, ptrs)) s₁' s₂' ∧ abiPreserved s₁ s₁' ∧ abiPreserved s₂ s₂' := by
    intro _ _ _ _ ea₁ ea₂
    obtain ⟨_, u₁, f₁, hp₁, -⟩ := hv.1 s₁ h₁
    obtain ⟨_, u₂, f₂, hp₂, -⟩ := hv.1 s₂ h₂
    obtain ⟨-, rfl⟩ := Exec.det ea₁ f₁
    obtain ⟨-, rfl⟩ := Exec.det ea₂ f₂
    exact ⟨TaintCT.agree_of_check hv.2.1 hτ h₁ h₂ hp hinit ea₁ ea₂, hp₁, hp₂⟩
  cases ks with
  | nil =>
    change Exec isa c _ _ _ at e₁ e₂
    obtain ⟨⟨hA, hPA, -⟩, hp₁, hp₂⟩ := run e₁ e₂
    obtain ⟨hsp', hrd', hwr', hdi', -⟩ := AgreeD.rest hA
    obtain ⟨hgr, hx0, hc', hn', hz', hv', hvr⟩ := done_regs hdF hA.1 hp₁ hp₂ ho
    simp only [List.isEmpty_nil, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hnil
    obtain ⟨⟨⟨⟨⟨-, hg⟩, hvp⟩, -⟩, hq⟩, -, -⟩ := hA.1
    refine ⟨hrd', hwr', fun q hq0 => ?_, hx0, hsp', hc', hn', hz', hv', hdi', ?_, ?_⟩
    · by_cases h9 : q = .x9
      · subst h9; exact hg .x9 (Taint.pub_iff.mp hnil.1)
      · exact hgr q hq0 h9
    · funext w
      by_cases h31 : w = .v31
      · subst h31
        simp only [RTaintL.vpub, Bool.or_eq_true, Bool.and_eq_true] at hnil
        rcases hnil.2 with hw | ⟨h₀, h₁'⟩
        · exact hvp _ hw
        · exact RTaintL.eq_of_halves (hq false _ h₀) (hq true _ h₁')
      · exact hvr w h31
    · intro x hx
      by_cases hin : (x - wbase s₂''.sp 0 W).toNat < W
      · have hxo : x = wbase s₂''.sp 0 W + BitVec.ofNat 64 (x - wbase s₂''.sp 0 W).toNat := by
          rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
        rw [hxo]
        exact hPA _ hin (gran_bit (b := wbase s₂''.sp 0 W) (by omega) hW.2.2 hgran hin (by simp [inG]))
      · refine hA.2.2.2 x (by rw [← hrd', ← hwr']; exact hx) fun hc => hin ?_
        unfold window Region.Contains at hc
        simp only [BitVec.add_zero] at hc
        rw [wbase0]
        omega
  | cons k ks =>
    change Exec isa (.seq c (scrubTailG W (k :: ks))) _ _ _ at e₁ e₂
    cases e₁ with
    | seq ea₁ eb₁ =>
    cases e₂ with
    | seq ea₂ eb₂ =>
    rename_i s₁' _ _ s₂' _ _
    obtain ⟨⟨hA, hPA, -⟩, hp₁, hp₂⟩ := run ea₁ ea₂
    obtain ⟨hsp', hrd', hwr', hdi', hu'⟩ := AgreeD.rest hA
    obtain ⟨hgr, hx0, hc', hn', hz', hv', hvr⟩ := done_regs hdF hA.1 hp₁ hp₂ ho
    obtain ⟨v₁, x₁, tr₁⟩ := tailG_run hW hks' s₁' (by rw [hp₁.2.1]; exact hsp s₁ h₁)
    obtain ⟨v₂, x₂, tr₂⟩ := tailG_run hW hks' s₂' (by rw [hp₂.2.1]; exact hsp s₂ h₂)
    obtain ⟨-, rfl⟩ := Exec.det eb₁ x₁
    obtain ⟨-, rfl⟩ := Exec.det eb₂ x₂
    refine ⟨by rw [tr₁.rd, tr₂.rd, hrd'], by rw [tr₁.wr, tr₂.wr, hwr'], fun q hq0 => ?_, ?_,
      by rw [tr₁.sp, tr₂.sp, hsp'], by rw [tr₁.c, tr₂.c, hc'], by rw [tr₁.nf, tr₂.nf, hn'],
      by rw [tr₁.zf, tr₂.zf, hz'], by rw [tr₁.vf, tr₂.vf, hv'], by rw [tr₁.dit, tr₂.dit, hdi'], ?_, ?_⟩
    · rw [tr₁.gpr, tr₂.gpr]
      by_cases h9 : q = .x9
      · simp only [h9, ↓reduceIte, hsp']
      · simp only [h9, ↓reduceIte]; exact hgr q hq0 h9
    · rw [tr₁.gpr, tr₂.gpr]
      simp only [reduceCtorEq, ↓reduceIte]
      exact hx0
    · rw [tr₁.v, tr₂.v]
      funext w
      by_cases h31 : w = .v31
      · simp only [h31, ↓reduceIte]
      · simp only [h31, ↓reduceIte]; exact hvr w h31
    · intro x hx
      rw [tr₁.rd, tr₁.wr] at hx
      rw [tr₁.mem, tr₂.mem, hsp']
      have hb : s₂'.sp - BitVec.ofNat 64 W = wbase s₂'.sp 0 W := (wbase0 _ _).symm
      by_cases hin : (x - (s₂'.sp - BitVec.ofNat 64 W)).toNat < W
      · rw [hu']
        refine lose_agree ?_
        simp only [zeroG]
        split
        · rfl
        · next hn =>
          have hxo : x = (s₂'.sp - BitVec.ofNat 64 W) +
              BitVec.ofNat 64 (x - (s₂'.sp - BitVec.ofNat 64 W)).toNat := by
            rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
          rw [← hb] at hPA
          rw [hxo] at hn ⊢
          exact hPA _ hin (gran_bit (by omega) hW.2.2 hgran hin (by simpa using hn))
      · rw [lose_out hin, lose_out hin, zeroG_out hks' _ hin, zeroG_out hks' _ hin]
        refine hA.2.2.2 x (by rw [← hrd', ← hwr']; exact hx) fun hc => hin ?_
        unfold window Region.Contains at hc
        simp only [BitVec.add_zero] at hc
        omega

/-- The zeroing of the granules `ks` keeps code verified (`RTaintF.ScrubOk`). -/
theorem Verified.scrubSel {c : Prog isa} {k : Contract isa} {W : Nat} {ks : List Nat}
    (h : Verified target c k) (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0)
    (hks : ks.all (fun k => decide (16 * k + 16 ≤ W)) = true) (hk : ScrubOk k W) :
    Verified target (scrubSel W ks c) k := by
  have hks' : ∀ k ∈ ks, 16 * k + 16 ≤ W := by simpa using hks
  cases ks with
  | nil => exact h
  | cons k₀ ks =>
  obtain ⟨hcor, hct, hsat⟩ := h
  have hrun : ∀ s, k.pre s → ∃ t s₃ u,
      Exec isa c s t s₃ ∧ abiPreserved s s₃ ∧ k.post s s₃ ∧
      Exec isa (scrubTailG W (k₀ :: ks)) s₃ (tailTraceG s₃.sp W (k₀ :: ks)) u ∧
        TailRunG W (k₀ :: ks) s₃ u := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor s hs
    obtain ⟨u, ex, tr⟩ := tailG_run hW hks' s₃ (by rw [ha.2.1]; exact hk.sp s hs)
    exact ⟨t, s₃, u, he, ha, hq, ex, tr⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, u, he, ha, hq, ex, tr⟩ := hrun s hs
    refine ⟨_, u, Exec.seq he ex, ⟨fun q hq' => ?_, by rw [tr.sp]; exact ha.2.1, fun w hw => ?_⟩, ?_⟩
    · have h9 : q ≠ .x9 := by rintro rfl; simp [preserved] at hq'
      rw [tr.gpr]; simp only [h9, ↓reduceIte]; exact ha.1 q hq'
    · have h31 : w ≠ .v31 := by rintro rfl; simp [preservedV] at hw
      rw [tr.v]; simp only [h31, ↓reduceIte]; exact ha.2.2 w hw
    · refine hk.post s s₃ u hs hq (fun a ha' => ?_) (by rw [tr.gpr]; simp)
      rw [tr.mem, ha.2.1, lose_out ha', zeroG_out hks' _ ha']
  · change Exec isa (.seq c (scrubTailG W (k₀ :: ks))) _ _ _ at e₁ e₂
    cases e₁ with
    | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
    obtain ⟨_, _, _, f₁, p₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨_, _, _, f₂, p₂, -, x₂, -⟩ := hrun s₂ h₂
    obtain ⟨rfl, rfl⟩ := Exec.det a₁ f₁
    obtain ⟨rfl, rfl⟩ := Exec.det a₂ f₂
    rw [(Exec.det b₁ x₁).1, (Exec.det b₂ x₂).1, p₁.2.1, p₂.2.1,
      hct _ _ _ _ _ _ h₁ h₂ hp a₁ a₂, hk.pub s₁ s₂ hp]

/-- `noResidue_scrubSel` with no granule left to zero: the code alone,
from no byte of the window known to agree. -/
theorem noResidue_of_doneG {c : Prog isa} {k : Contract isa} {r W : Nat}
    (hv : Verified target c k) (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0)
    (hsp : ∀ s, k.pre s → W ≤ s.sp.toNat)
    (h : ∃ hc, ((rtaintG W).check (RTaintB.init, some (0, 0, [])) c hc).any (doneG W r []) = true) :
    NoResidue c k r :=
  noResidue_scrubSel (ks := []) (P₀ := 0) hv hW hsp (fun _ _ _ _ _ hb => by simp at hb) h

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- A contract whose arguments are all in registers has room for `W ≤ stack` bytes. -/
theorem sp_of_pre (hk : (sig.words abi.ptrBits).length ≤ 8) {W : Nat} (hW : 0 < W) (hWs : W ≤ stack) :
    ∀ s, (sig.contract abi pre post wa stack leak).pre s → W ≤ s.sp.toNat := fun s hs => by
  rw [pre_regs hk] at hs
  have := hW
  rcases hs.1 with h0 | h0 <;> omega

end

end VG.AArch64.RTaintG
