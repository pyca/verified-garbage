module

-- separate module: changes to the carry arithmetic do not recheck the store and memory footprint proofs.

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CarryMask
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.MaskSteps
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CarryRegs
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Rsa.X86_64.CrtIfma

/-- A one-bit shift aligns the carry mask with the next stride row. -/
theorem alignCarryMask_run (s : State) (j : Nat) :
    ∃ t, runBlock isa (if j = 0 then [] else [.shift .shr .rax 1]) s = some t ∧
      t.gpr .rax = (if j = 0 then s.gpr .rax else s.gpr .rax >>> 1) ∧
      (∀ q, q ≠ .rax → t.gpr q = s.gpr q) ∧ (∀ v, t.vy v = s.vy v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  by_cases h : j = 0
  · simpa only [h, ite_true, runBlock_nil] using
      (show ∃ t : State, (some s : Option State) = some t ∧ t.gpr .rax = s.gpr .rax ∧
        (∀ q, q ≠ .rax → t.gpr q = s.gpr q) ∧ (∀ v, t.vy v = s.vy v) ∧
        t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr from
        ⟨s, rfl, rfl, fun _ _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl⟩)
  · simp [h, runBlock_cons, runStep_some, runBlock_nil, exec, execShift,
      State.setFlags, State.setReg]
    refine ⟨?_, ?_⟩
    · intro q hq
      simp [hq]
    · intro v
      cases v <;> rfl

/-- The value used at the start of lane normalization keeps all accumulators
and saves the preceding high words for row zero. -/
def begin3072Collect (s : State) : State :=
  let t := (EOp.valignq (vreg 27) (carryHigh3072 7) (vreg 26) 3).exec s
  let a := (arithFlags t (0#32) false false).setReg32 .rax 0
  (arithFlags a (0#32) false false).setReg32 .rcx 0

theorem begin3072Collect_run (s : State) :
    runBlock isa [.eop (.valignq (vreg 27) (carryHigh3072 7) (vreg 26) 3),
      .alu32 .xor .rax (.reg .rax), .alu32 .xor .rcx (.reg .rcx)] s = some (begin3072Collect s) := by
  simp [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, begin3072Collect]

theorem begin3072Collect_qv (s : State) (r : VReg) (k : Nat) (hr : r ≠ vreg 27) :
    qv (begin3072Collect s) r k = qv s r k := by
  change qv (s.setVy (vreg 27) _) r k = _
  rw [qv_setVy, ite_eq_right hr]

theorem begin3072Collect_align (s : State) {k : Nat} (hk : k < 4) :
    qv (begin3072Collect s) (vreg 27) k =
      if k = 0 then qv s (vreg 26) 3 else qv s (carryHigh3072 7) (k - 1) :=
  qv_align_row s hk

theorem carry_word_hi (x : Nat) (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x >>> 52 = BitVec.ofNat 64 (x / 2 ^ 52) := by
  apply BitVec.eq_of_toNat_eq
  have hy : x / 2 ^ 52 < 2 ^ 64 := by omega
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.shiftRight_eq_div_pow]

private theorem acc_ne_carry_align (p : Fin 2) (j : Fin 8) :
    carryAcc3072 p.val j.val ≠ vreg 27 :=
  (show ∀ (p : Fin 2) (j : Fin 8), carryAcc3072 p.val j.val ≠ vreg 27 from by decide) p j

private theorem carry_high_ne_align (j : Fin 8) : carryHigh3072 j.val ≠ vreg 27 :=
  (show ∀ j : Fin 8, carryHigh3072 j.val ≠ vreg 27 from by decide) j

/-- After splitting, the shift-by-one alignment makes each row sum equal
to the arithmetic proof's provisional limb at the corresponding index. -/
theorem provisional3072_qword (s : State) (p : Nat) (hp : p < 2) (L : Nat → Nat)
    (hlo : ∀ j < 8, ∀ k < 4, qv s (carryAcc3072 p j) k = BitVec.ofNat 64 (L (j + 8 * k) % 2 ^ 52))
    (hhi : ∀ j < 8, ∀ k < 4, qv s (carryHigh3072 j) k = BitVec.ofNat 64 (L (j + 8 * k) / 2 ^ 52))
    (hz : qv s (vreg 26) 3 = 0) {j k : Nat} (hj : j < 8) (hk : k < 4) :
    qv (begin3072Collect s) (carryAcc3072 p j) k +
      qv (begin3072Collect s) (if j = 0 then vreg 27 else carryHigh3072 (j - 1)) k =
      BitVec.ofNat 64 (provisional L (j + 8 * k)) := by
  rw [begin3072Collect_qv _ _ _ (acc_ne_carry_align ⟨p, hp⟩ ⟨j, hj⟩), hlo j hj k hk]
  have hh : qv (begin3072Collect s) (if j = 0 then vreg 27 else carryHigh3072 (j - 1)) k =
      BitVec.ofNat 64 (priorHigh L (j + 8 * k)) := by
    by_cases he : j = 0
    · subst j
      rw [ite_eq_left rfl, begin3072Collect_align _ hk]
      by_cases hk0 : k = 0
      · subst k; simp [hz, priorHigh]
      · rw [ite_eq_right hk0, hhi 7 (by decide) (k - 1) (by omega)]
        have e : 0 + 8 * k = (7 + 8 * (k - 1)) + 1 := by omega
        rw [e, priorHigh]
    · rw [ite_eq_right he, begin3072Collect_qv _ _ _ (carry_high_ne_align ⟨j - 1, by omega⟩),
        hhi (j - 1) (by omega) k hk]
      have e : j + 8 * k = (j - 1 + 8 * k) + 1 := by omega
      rw [e, priorHigh]
  rw [hh, ← BitVec.ofNat_add]
  rfl

private theorem write_run_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some t => exact ih t

/-- A row is stored after shifting the carry mask, except for row zero. -/
def write3072Row (p j : Nat) : List Instr :=
  (if j = 0 then [] else [.shift .shr .rax 1]) ++
    store3072Row (carryAcc3072 p j) (lay3072.D * p + 32 * j)

def aligned3072Row (s : State) (p j : Nat) (carry : BitVec 64) : BitVec 256 :=
  normalizedCarryRow (s.setReg .rax carry) (carryAcc3072 p j)

private theorem aligned3072Row_congr (s t : State) (p j : Nat) (carry : BitVec 64)
    (hr : t.vy (carryAcc3072 p j) = s.vy (carryAcc3072 p j))
    (hm : t.vy (vreg 24) = s.vy (vreg 24)) (ho : t.vy (vreg 25) = s.vy (vreg 25))
    (hc : t.gpr .rsi = s.gpr .rsi) :
    aligned3072Row s p j carry = aligned3072Row t p j carry := by
  have h (u : State) (r : VReg) : (u.setReg .rax carry).vy r = u.vy r := by cases r <;> rfl
  unfold aligned3072Row normalizedCarryRow compactCarryBits
  simp only [h, hr, hm, ho, hc, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne _ _ (show Reg.rsi ≠ .rax by decide)]

theorem write3072Row_run (s : State) (p j : Nat) (hm : vreg 24 ≠ carryAcc3072 p j)
    (hw : InRegions s.wr (s.ea (at_ .r11 (lay3072.D * p + 32 * j))) 32) :
    let carry := if j = 0 then s.gpr .rax else s.gpr .rax >>> 1
    ∃ t : State, runBlock isa (write3072Row p j) s = some t ∧
      t.gpr .rax = carry ∧
      t.mem = s.mem.writeW (s.ea (at_ .r11 (lay3072.D * p + 32 * j))) (aligned3072Row s p j carry) ∧
      (∀ v, v ≠ carryAcc3072 p j → t.vy v = s.vy v) ∧
      (∀ q, q ≠ .rax → q ≠ .rdx → t.gpr q = s.gpr q) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  let carry := if j = 0 then s.gpr .rax else s.gpr .rax >>> 1
  obtain ⟨u, hu, hc, hr, hv, hmem, hrd, hwr, hmx⟩ := alignCarryMask_run s j
  have he : u.ea (at_ .r11 (lay3072.D * p + 32 * j)) = s.ea (at_ .r11 (lay3072.D * p + 32 * j)) := by
    change u.gpr .r11 + _ = s.gpr .r11 + _
    rw [hr .r11 (by decide)]
  obtain ⟨t, ht, tm, tv, tr, trd, twr, tx⟩ := store3072Row_run u _ _ hm (by rw [hwr, he]; exact hw)
  have hval : normalizedCarryRow u (carryAcc3072 p j) = aligned3072Row s p j carry := by
    have v (r : VReg) : (s.setReg .rax carry).vy r = s.vy r := by cases r <;> rfl
    unfold aligned3072Row
    simp only [normalizedCarryRow, compactCarryBits, v, hv, hc, hr .rsi (by decide), RegUpd.gpr_setReg_self,
      RegUpd.gpr_setReg_of_ne _ _ (show Reg.rsi ≠ .rax by decide)]
    rfl
  have hrun : runBlock isa (write3072Row p j) s = some t := by
    rw [write3072Row, write_run_append, hu, Option.bind_some, ht]
  exact ⟨t, hrun, (tr .rax (by decide)).trans hc, by rw [tm, hmem, he, hval],
    fun v h => (tv v h).trans (hv v), fun q ha hd => (tr q hd).trans (hr q ha),
    trd.trans hrd, twr.trans hwr, tx.trans hmx⟩

def write3072Rows (p n : Nat) : List Instr :=
  (List.range n).flatMap (write3072Row p)

def carryWrites (s : State) (p n : Nat) : List (Nat × BitVec 256) :=
  (List.range n).map fun j => (lay3072.D * p + 32 * j, aligned3072Row s p j (s.gpr .rax >>> j))

def CarryWritten (s t : State) (p n : Nat) : Prop :=
  t.gpr .rax = s.gpr .rax >>> (n - 1) ∧
  t.mem = AmmSym.wrList s.mem (s.gpr .r11) (carryWrites s p n) ∧
  (∀ v, (∀ j < n, v ≠ carryAcc3072 p j) → t.vy v = s.vy v) ∧
  (∀ q, q ≠ .rax → q ≠ .rdx → t.gpr q = s.gpr q) ∧
  t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr

private theorem carry_write_append (m : Mem) (b : Addr) (a c : List (Nat × BitVec 256)) :
    AmmSym.wrList m b (a ++ c) = AmmSym.wrList (AmmSym.wrList m b a) b c := by
  induction a generalizing m with
  | nil => rfl
  | cons w a ih => cases w; exact ih _

private theorem carry_write_succ (s : State) (p n : Nat) :
    carryWrites s p (n + 1) = carryWrites s p n ++
      [(lay3072.D * p + 32 * n, aligned3072Row s p n (s.gpr .rax >>> n))] := by
  simp only [carryWrites, List.range_succ, List.map_append, List.map_cons, List.map_nil]

private theorem carryAcc_constants_ne (p : Fin 2) (j : Fin 8) :
    vreg 24 ≠ carryAcc3072 p.val j.val ∧ vreg 25 ≠ carryAcc3072 p.val j.val :=
  (show ∀ (p : Fin 2) (j : Fin 8), vreg 24 ≠ carryAcc3072 p.val j.val ∧
    vreg 25 ≠ carryAcc3072 p.val j.val from by decide) p j

private theorem carryAcc_row_ne (p : Fin 2) (i j : Fin 8) (h : i ≠ j) :
    carryAcc3072 p.val i.val ≠ carryAcc3072 p.val j.val :=
  (show ∀ (p : Fin 2) (i j : Fin 8), i ≠ j → carryAcc3072 p.val i.val ≠
    carryAcc3072 p.val j.val from by decide) p i j h

private theorem carry_mask_next (x : BitVec 64) (n : Nat) :
    (if n = 0 then x >>> (n - 1) else (x >>> (n - 1)) >>> 1) = x >>> n := by
  by_cases h : n = 0
  · subst n; rfl
  · rw [ite_eq_right h]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_ushiftRight]
    rw [show n - 1 + (1 + i) = n + i by omega]

private theorem write3072Rows_step (s u : State) (p n : Nat) (hp : p < 2) (hn : n < 8)
    (hw : InRegions s.wr (s.ea (at_ .r11 (lay3072.D * p + 32 * n))) 32)
    (h : CarryWritten s u p n) :
    ∃ t, runBlock isa (write3072Row p n) u = some t ∧ CarryWritten s t p (n + 1) := by
  rcases h with ⟨hcarry, hmem, hvec, hreg, hrd, hwr, hx⟩
  let r := carryAcc3072 p n
  have he : u.ea (at_ .r11 (lay3072.D * p + 32 * n)) = s.ea (at_ .r11 (lay3072.D * p + 32 * n)) := by
    change u.gpr .r11 + _ = s.gpr .r11 + _
    rw [hreg .r11 (by decide) (by decide)]
  obtain ⟨t, ht, hd, hm, hv, hg, hrd', hwr', hx'⟩ := write3072Row_run u p n
    (carryAcc_constants_ne ⟨p, hp⟩ ⟨n, hn⟩).1 (by rw [hwr, he]; exact hw)
  have hc : (if n = 0 then u.gpr .rax else u.gpr .rax >>> 1) = s.gpr .rax >>> n := by
    rw [hcarry, carry_mask_next]
  have hkeep : ∀ j < n, r ≠ carryAcc3072 p j := by
    intro j hj
    exact carryAcc_row_ne ⟨p, hp⟩ ⟨n, hn⟩ ⟨j, by omega⟩
      (fun e => (by omega : n ≠ j) (congrArg Fin.val e))
  have hval : aligned3072Row u p n (s.gpr .rax >>> n) = aligned3072Row s p n (s.gpr .rax >>> n) := by
    symm
    apply aligned3072Row_congr
    · exact hvec r hkeep
    · exact hvec _ (fun j hj => (carryAcc_constants_ne ⟨p, hp⟩ ⟨j, by omega⟩).1)
    · exact hvec _ (fun j hj => (carryAcc_constants_ne ⟨p, hp⟩ ⟨j, by omega⟩).2)
    · exact hreg .rsi (by decide) (by decide)
  refine ⟨t, ht, ?_, ?_, ?_, ?_, hrd'.trans hrd, hwr'.trans hwr, hx'.trans hx⟩
  · rw [hd, hc, Nat.add_sub_cancel]
  · rw [hm, hc, hval, he, hmem, carry_write_succ, carry_write_append]
    rfl
  · intro v hv'
    exact (hv v (hv' n (by omega))).trans (hvec v (fun j hj => hv' j (by omega)))
  · intro q ha hd
    exact (hg q ha hd).trans (hreg q ha hd)

private theorem write3072Rows_join (s u t : State) (p n : Nat)
    (h₁ : runBlock isa (write3072Rows p n) s = some u) (h₂ : runBlock isa (write3072Row p n) u = some t) :
    runBlock isa (write3072Rows p (n + 1)) s = some t := by
  have h : write3072Rows p (n + 1) = write3072Rows p n ++ write3072Row p n := by
    simp only [write3072Rows, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
  rw [h, write_run_append, h₁, Option.bind_some, h₂]

/-- Execute and account for the single complete write of every row. -/
theorem write3072Rows_run (s : State) (p n : Nat) (hp : p < 2) (hn : n ≤ 8)
    (hw : ∀ j < n, InRegions s.wr (s.ea (at_ .r11 (lay3072.D * p + 32 * j))) 32) :
    ∃ t, runBlock isa (write3072Rows p n) s = some t ∧ CarryWritten s t p n := by
  induction n with
  | zero =>
    exact ⟨s, runBlock_nil, rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨u, hu, hu'⟩ := ih (by omega) (fun j hj => hw j (by omega))
    obtain ⟨t, ht, ht'⟩ := write3072Rows_step s u p n hp (by omega) (hw n (by omega)) hu'
    exact ⟨t, write3072Rows_join s u t p n hu ht, ht'⟩

/-- Extract the final high word and add the carry bit beyond the last row. -/
def finish3072Code (p : Nat) : List Instr :=
  [.shift .shr .rax 25, .eop (.vpermq (carryAcc3072 p 0) (carryHigh3072 7) 0xff),
    .movqR (cReg p) (if p = 0 then .xmm6 else .xmm14),
    .alu .add (cReg p) (.reg .rax)] ++
  (if p = 0 then [.mov .r10 (.reg .rdx)] else [.mov .rdx (.reg .r10)])

def finish3072Value (s : State) : BitVec 64 := qv s (carryHigh3072 7) 3 + (s.gpr .rax >>> 25)

private theorem carry_low_broadcast (x : BitVec 64) :
    (x ++ x ++ x ++ x).extractLsb' 0 64 = x :=
  qword256_bcast x (k := 0) (by decide)

theorem finish3072Code_run (s : State) (p : Nat) (hp : p < 2) :
    ∃ t, runBlock isa (finish3072Code p) s = some t ∧
      (if p = 0 then t.gpr .r10 else t.gpr .rsi) = finish3072Value s ∧
      (p = 1 → t.gpr .rdx = s.gpr .r10) ∧ (p = 0 → t.gpr .rsi = s.gpr .rsi) ∧
      (∀ q, q ≠ .rax → q ≠ .rdx → q ≠ .rsi → q ≠ .r10 → t.gpr q = s.gpr q) ∧
      (∀ v, v ≠ carryAcc3072 p 0 → t.vy v = s.vy v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl
  all_goals
    simp [finish3072Code, runBlock_cons, runStep_some, runBlock_nil, exec, execShift, execAlu,
      readSrc, finish3072Value, cReg, carryAcc3072, acc, lay3072, vreg, EOp.exec, State.setVy,
      State.setV, State.setReg, State.setFlags, arithFlags, permQwords, qv, State.vy, qword256,
      carryHigh3072, carry_low_broadcast]
    repeat' apply And.intro
    all_goals first | rfl | (intro q a b c d; simp [a,b,c,d]) | (intro v h; cases v <;> simp_all [State.ymm])
/-- The vector-only split preserves every scalar register and memory. -/
theorem split3072Rows_frame (s t : State) (p n : Nat)
    (h : runBlock isa (split3072Rows p n) s = some t) :
    t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  induction n generalizing t with
  | zero =>
    change some s = some t at h
    cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    have he : split3072Rows p (n + 1) = split3072Rows p n ++
        split3072Row (carryAcc3072 p n) (carryHigh3072 n) := by
      simp only [split3072Rows, List.range_succ, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
    rw [he, write_run_append, Option.bind_eq_some_iff] at h
    obtain ⟨u, hu, ht⟩ := h
    have hf := ih u hu
    have hs : t.gpr = u.gpr ∧ t.mem = u.mem ∧ t.rd = u.rd ∧ t.wr = u.wr ∧ t.mxcsr = u.mxcsr := by
      let r := carryAcc3072 p n
      let hi := carryHigh3072 n
      let mid := (EOp.shift .vpsrlq hi r 52).exec u
      let last := (EOp.bin .vpandq r r (vreg 24)).exec mid
      change some last = some t at ht
      have heq := Option.some.inj ht
      subst t
      cases hr : r <;> cases hh : hi <;> simp [last, mid, EOp.exec, hr, hh, State.setVy, State.setV]
    exact ⟨hs.1.trans hf.1, hs.2.1.trans hf.2.1, hs.2.2.1.trans hf.2.2.1,
      hs.2.2.2.1.trans hf.2.2.2.1, hs.2.2.2.2.trans hf.2.2.2.2⟩

theorem begin3072Collect_frame (s : State) :
    (begin3072Collect s).gpr .rax = 0 ∧ (begin3072Collect s).gpr .rcx = 0 ∧
      (∀ q, q ≠ .rax → q ≠ .rcx → (begin3072Collect s).gpr q = s.gpr q) ∧
      (begin3072Collect s).mem = s.mem ∧ (begin3072Collect s).rd = s.rd ∧
      (begin3072Collect s).wr = s.wr ∧ (begin3072Collect s).mxcsr = s.mxcsr := by
  simp [begin3072Collect, EOp.exec, vreg, State.setVy, State.setReg32, State.setReg,
    arithFlags, State.setFlags]
  intro q ha hc
  simp [ha, hc]

/-- Four corresponding quadwords determine the row. -/
theorem carry_row_ext {a b : BitVec 256} (h : ∀ k < 4, qword256 a k = qword256 b k) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have he := congrArg (fun (x : BitVec 64) => x.getLsbD (i % 64)) (h (i / 64) (by omega))
  simp only [qword256, BitVec.getLsbD_extractLsb', show i % 64 < 64 by omega,
    decide_true, Bool.true_and] at he
  rw [show 64 * (i / 64) + i % 64 = i by omega] at he
  exact he

end VG.Proof.Bignum.X86_64.Ifma
