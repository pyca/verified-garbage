module

-- separate module: changes to the final stores do not recheck the stride-row accumulation invariants.

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CarryMask
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CarryRegs
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.MaskSteps

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Poly1305.X86_64.Avx2 (qword_and)

/-- The final vector add applies the relevant bit of the aligned carry mask
to each provisional limb and returns that limb's low 52 bits. -/
theorem normalizedCarryRow_qword (s : State) (r : VReg) {k : Nat} (hk : k < 4)
    (hm : qv s (vreg 24) k = mask52) (ho : qv s (vreg 25) k = 1)
    (hs : s.gpr .rsi = 0x01010101) :
    qword256 (normalizedCarryRow s r) k =
      (qv s r k + (BitVec.ofBool ((s.gpr .rax).getLsbD (8 * k))).setWidth 64) &&& mask52 := by
  rw [normalizedCarryRow, qword256_lanes _ _ _ hk]
  simp only [XBinOp.eval]
  rw [qword_and, qword_lane256, qword_lane256, qword256_maskAddQ _ _ _ _ hk]
  change (if (compactCarryBits s).getLsbD k then qv s r k + qv s (vreg 25) k
    else qv s r k) &&& qv s (vreg 24) k = _
  rw [compactCarryBits, hs, compactCarryBits_bit _ hk, hm, ho]
  cases (s.gpr .rax).getLsbD (8 * k) <;> simp

/-- The register compare sets only the low nibble. -/
theorem cmpUqMask_small (gt : Bool) (a b : BitVec 256) : (cmpUqMask gt a b).toNat < 16 := by
  cases gt <;> simp only [cmpUqMask, BitVec.toNat_ofNat, List.range_succ, List.range_zero, List.nil_append,
    List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.reducePow, Nat.zero_add,
    Bool.false_eq_true, ite_false, ite_true] <;>
    split <;> split <;> split <;> split <;> decide

/-- Row `j` updates only the packed mask bits for that stride row. -/
theorem addCarryRowBits_bit (gt : Bool) (s : State) (r : VReg) {j i : Nat} (hj : j < 8) (hi : i < 32)
    (hmask : s.gpr .rsi = 0x01010101) :
    (addCarryRowBits gt r j s).getLsbD i =
      ((s.gpr (if gt then .rax else .rcx)).getLsbD i ||
        (decide (i % 8 = j) && (cmpUqMask gt (s.vy r) (s.vy (vreg 24))).getLsbD (i / 8))) := by
  let c := cmpUqMask gt (s.vy r) (s.vy (vreg 24))
  have hset : ((((c.setWidth 64) * 0x00204081) &&& 0x01010101).setWidth 32) =
      (c * 0x00204081) &&& 0x01010101 := by
    rw [BitVec.setWidth_and, BitVec.setWidth_mul _ _ (by decide),
      BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
    rfl
  unfold addCarryRowBits
  rw [hmask]
  change ((_ ||| (((c.setWidth 64 * 0x00204081) &&& 0x01010101).setWidth 32 <<< j)) : BitVec 32).getLsbD i = _
  rw [hset, BitVec.getLsbD_or, BitVec.getLsbD_setWidth, spreadCarryMask_shifted c
    (cmpUqMask_small gt (s.vy r) (s.vy (vreg 24))) hj hi]
  simp [hi] <;> rfl

private theorem normalize_run_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some t => exact ih t

/-- The three consecutive blocks for one stride row. -/
def collect3072Row (p j : Nat) : List Instr :=
  let r := carryAcc3072 p j
  let prev := if j = 0 then vreg 27 else carryHigh3072 (j - 1)
  [.eop (.bin .vpaddq r r prev)] ++ spreadCarryMask true r j ++ spreadCarryMask false r j

private theorem addCarryRowBits_congr (gt : Bool) (r : VReg) (j : Nat) (s t : State)
    (hr : t.vy r = s.vy r) (hm : t.vy (vreg 24) = s.vy (vreg 24))
    (hs : t.gpr .rsi = s.gpr .rsi)
    (h : t.gpr (if gt then .rax else .rcx) = s.gpr (if gt then .rax else .rcx)) :
    addCarryRowBits gt r j t = addCarryRowBits gt r j s := by
  simp only [addCarryRowBits, hr, hm, hs, h]

/-- Each compare observes the provisional vector. The second mask update
does not change the first mask or any accumulator rows. -/
theorem collect3072Row_run (s : State) (p j : Nat) (hj : j < 8) :
    let r := carryAcc3072 p j
    let prev := if j = 0 then vreg 27 else carryHigh3072 (j - 1)
    let mid := (EOp.bin .vpaddq r r prev).exec s
    ∃ t, runBlock isa (collect3072Row p j) s = some t ∧
      t.gpr .rax = (addCarryRowBits true r j mid).setWidth 64 ∧
      t.gpr .rcx = (addCarryRowBits false r j mid).setWidth 64 ∧
      (∀ v, t.vy v = mid.vy v) ∧
      (∀ q, q ≠ .rax → q ≠ .rcx → q ≠ .rdx → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  let r := carryAcc3072 p j
  let prev := if j = 0 then vreg 27 else carryHigh3072 (j - 1)
  let mid := (EOp.bin .vpaddq r r prev).exec s
  have midG (q : Reg) : mid.gpr q = s.gpr q := by
    change (s.setVy r _).gpr q = _
    exact gpr_setVy _ _ _ _
  have midF : mid.mem = s.mem ∧ mid.rd = s.rd ∧ mid.wr = s.wr ∧ mid.mxcsr = s.mxcsr := by
    change (s.setVy r _).mem = s.mem ∧ (s.setVy r _).rd = s.rd ∧
      (s.setVy r _).wr = s.wr ∧ (s.setVy r _).mxcsr = s.mxcsr
    cases r <;> exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨a, ha, hg, av, ag, am, ard, awr, ax⟩ := spreadCarryMask_run true r j hj mid
  obtain ⟨t, ht, hp, tv, tg, tm, trd, twr, tx⟩ := spreadCarryMask_run false r j hj a
  have hcmp : addCarryRowBits false r j a = addCarryRowBits false r j mid :=
    addCarryRowBits_congr _ _ _ _ _ (av _) (av _) (ag .rsi (by decide) (by decide)) (ag .rcx (by decide) (by decide))
  have hcode : collect3072Row p j =
      [.eop (.bin .vpaddq r r prev)] ++ spreadCarryMask true r j ++ spreadCarryMask false r j := rfl
  have hstep : runBlock isa ([.eop (.bin .vpaddq r r prev)] : List Instr) s = some mid := rfl
  have hrun : runBlock isa (collect3072Row p j) s = some t := by
    rw [hcode, normalize_run_append, normalize_run_append, hstep, Option.bind_some, ha, Option.bind_some, ht]
  have hG : t.gpr .rax = (addCarryRowBits true r j mid).setWidth 64 :=
    (tg .rax (by decide) (by decide)).trans hg
  have hP : t.gpr .rcx = (addCarryRowBits false r j mid).setWidth 64 :=
    hp.trans (congrArg (BitVec.setWidth 64) hcmp)
  exact ⟨t, hrun, hG, hP, fun v => (tv v).trans (av v),
    fun q hq hc hd => (tg q hd hc).trans ((ag q hd hq).trans (midG q)),
    tm.trans (am.trans midF.1), trd.trans (ard.trans midF.2.1), twr.trans (awr.trans midF.2.2.1),
    tx.trans (ax.trans midF.2.2.2)⟩

/-- The row sum before applying single-bit carries. -/
def collect3072Value (s : State) (p j k : Nat) : BitVec 64 :=
  qv s (carryAcc3072 p j) k +
    qv s (if j = 0 then vreg 27 else carryHigh3072 (j - 1)) k

/-- The predicate corresponding to bit `i` in a partially collected mask.
The first `n` rows have been processed, in either the generate mask or the
propagate mask. -/
def collectedBit (s : State) (p n : Nat) (gt : Bool) (i : Nat) : Bool :=
  if i < 32 ∧ i % 8 < n then
    let v := collect3072Value s p (i % 8) (i / 8)
    if gt then decide (mask52.toNat < v.toNat) else decide (v = mask52)
  else false

/-- View a vector write as replacing exactly one register in the row map. -/
theorem collect3072Row_vy (s : State) (p j : Nat) (v : VReg) (h : v ≠ carryAcc3072 p j) :
    ((EOp.bin .vpaddq (carryAcc3072 p j) (carryAcc3072 p j)
       (if j = 0 then vreg 27 else carryHigh3072 (j - 1))).exec s).vy v = s.vy v := by
  cases hv : v <;> cases hr : carryAcc3072 p j <;>
    simp_all [EOp.exec, State.setVy, State.vy, State.ymm, State.setV]

/-- Each compare adds one of the four provisional quadword predicates at
the corresponding bit position. -/
theorem collect3072Row_bit (s t : State) (p : Nat) {j i : Nat} (hj : j < 8) (hi : i < 32)
    (gt : Bool) (hm : ∀ k < 4, qv s (vreg 24) k = mask52)
    (hr : vreg 24 ≠ carryAcc3072 p j) (hs : s.gpr .rsi = 0x01010101)
    (ht : t.gpr (if gt then .rax else .rcx) =
      (addCarryRowBits gt (carryAcc3072 p j) j
        ((EOp.bin .vpaddq (carryAcc3072 p j) (carryAcc3072 p j)
          (if j = 0 then vreg 27 else carryHigh3072 (j - 1))).exec s)).setWidth 64) :
    (t.gpr (if gt then .rax else .rcx)).getLsbD i =
      ((s.gpr (if gt then .rax else .rcx)).getLsbD i ||
        (decide (i % 8 = j) &&
          if gt then decide (mask52.toNat < (collect3072Value s p j (i / 8)).toNat)
          else decide (collect3072Value s p j (i / 8) = mask52))) := by
  let r := carryAcc3072 p j
  let prev := if j = 0 then vreg 27 else carryHigh3072 (j - 1)
  let u := (EOp.bin .vpaddq r r prev).exec s
  have hg (reg : Reg) : u.gpr reg = s.gpr reg := by
    change (s.setVy r _).gpr reg = _
    exact gpr_setVy s r _ reg
  have hmask : qv u (vreg 24) (i / 8) = mask52 := by
    change qv (s.setVy r _) (vreg 24) (i / 8) = _
    rw [qv_setVy, ite_eq_right hr, hm _ (by omega)]
  have hk : i / 8 < 4 := by omega
  change (t.gpr _).getLsbD i = _
  rw [ht, BitVec.getLsbD_setWidth]
  have ei : i < 64 := by omega
  simp only [ei, decide_true, Bool.true_and]
  change (addCarryRowBits gt r j u).getLsbD i = _
  rw [addCarryRowBits_bit gt u r hj hi (hg .rsi ▸ hs), hg]
  rw [cmpUqMask_bit _ _ _ hk]
  change (_ || (_ && if gt then decide ((qv u (vreg 24) _).toNat < (qv u r _).toNat)
    else decide (qv u r _ = qv u (vreg 24) _))) = _
  rw [hmask, qv_add_row _ _ _ _ hk]
  rfl

/-- All mask updates for the first `n` rows of one prime. -/
def collect3072Rows (p n : Nat) : List Instr :=
  (List.range n).flatMap (collect3072Row p)

def CarryCollected (s t : State) (p n : Nat) : Prop :=
  (∀ j < n, ∀ k < 4, qv t (carryAcc3072 p j) k = collect3072Value s p j k) ∧
  (∀ v, (∀ j < n, v ≠ carryAcc3072 p j) → t.vy v = s.vy v) ∧
  (∀ q, q ≠ .rax → q ≠ .rcx → q ≠ .rdx → t.gpr q = s.gpr q) ∧
  (∀ gt i, (t.gpr (if gt then .rax else .rcx)).getLsbD i = collectedBit s p n gt i) ∧
  t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr

private theorem collect_acc_ne (p : Fin 2) (i j : Fin 8) (h : i ≠ j) :
    carryAcc3072 p.val i.val ≠ carryAcc3072 p.val j.val := by
  exact (show ∀ (p : Fin 2) (i j : Fin 8), i ≠ j → carryAcc3072 p.val i.val ≠
    carryAcc3072 p.val j.val from by decide) p i j h

private theorem collect_prev_ne (p : Fin 2) (i j : Fin 8) :
    (if i.val = 0 then vreg 27 else carryHigh3072 (i.val - 1)) ≠ carryAcc3072 p.val j.val :=
  (show ∀ (p : Fin 2) (i j : Fin 8), (if i.val = 0 then vreg 27 else carryHigh3072 (i.val - 1)) ≠
    carryAcc3072 p.val j.val from by decide) p i j

private theorem collect_mask_ne (p : Fin 2) (i : Fin 8) : vreg 24 ≠ carryAcc3072 p.val i.val :=
  (show ∀ (p : Fin 2) (i : Fin 8), vreg 24 ≠ carryAcc3072 p.val i.val from by decide) p i

private theorem collect3072Rows_step (s u : State) (p n : Nat) (hp : p < 2) (hn8 : n < 8)
    (hm : ∀ k < 4, qv s (vreg 24) k = mask52) (hs : s.gpr .rsi = 0x01010101)
    (hcol : CarryCollected s u p n) :
    ∃ t, runBlock isa (collect3072Row p n) u = some t ∧ CarryCollected s t p (n + 1) := by
  obtain ⟨hrow, hvec, hgr, hbits, hmem, hrd, hwr, hmx⟩ := hcol
  obtain ⟨t, ht, htG, htP, htV, htR, htM, htRD, htWR, htMX⟩ := collect3072Row_run u p n hn8
  let r := carryAcc3072 p n
  let prev := if n = 0 then vreg 27 else carryHigh3072 (n - 1)
  let mid := (EOp.bin .vpaddq r r prev).exec u
  have hf (j : Nat) (hj : j < n) : r ≠ carryAcc3072 p j := by
    exact collect_acc_ne ⟨p, hp⟩ ⟨n, hn8⟩ ⟨j, by omega⟩
      (fun e => (by omega : n ≠ j) (congrArg Fin.val e))
  have hprev : u.vy prev = s.vy prev :=
    hvec _ (fun j hj => collect_prev_ne ⟨p, hp⟩ ⟨n, hn8⟩ ⟨j, by omega⟩)
  have hr : u.vy r = s.vy r := hvec _ hf
  have hv (k : Nat) : collect3072Value u p n k = collect3072Value s p n k := by
    change qword256 (u.vy r) k + qword256 (u.vy prev) k = _
    rw [hr, hprev]
    rfl
  have hv' (v : VReg) (h : v ≠ r) : t.vy v = u.vy v :=
    (htV v).trans (collect3072Row_vy u p n v h)
  refine ⟨t, ht, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, htM.trans hmem, htRD.trans hrd, htWR.trans hwr, htMX.trans hmx⟩
  · intro j hj k hk
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
    · have e : qv t (carryAcc3072 p j) k = qv u (carryAcc3072 p j) k := by
        unfold qv
        rw [hv' _ (Ne.symm (hf j hj))]
      rw [e, hrow j hj k hk]
    · unfold qv
      rw [htV]
      change qv mid r k = _
      rw [qv_add_row _ _ _ _ hk]
      exact hv k
  · intro v h
    exact (hv' v (h n (by omega))).trans (hvec v fun j hj => h j (by omega))
  · intro q ha hc hd
    exact (htR q ha hc hd).trans (hgr q ha hc hd)
  · intro gt i
    have hm' : ∀ k < 4, qv u (vreg 24) k = mask52 := by
      intro k hk
      unfold qv
      rw [hvec _ (fun j hj => collect_mask_ne ⟨p, hp⟩ ⟨j, by omega⟩)]
      exact hm k hk
    have hs' : u.gpr .rsi = 0x01010101 := (hgr .rsi (by decide) (by decide) (by decide)).trans hs
    have hgt : t.gpr (if gt then .rax else .rcx) =
        (addCarryRowBits gt r n mid).setWidth 64 := by
      cases gt
      · exact htP
      · exact htG
    by_cases hi : i < 32
    · rw [collect3072Row_bit u t p hn8 hi gt hm' (collect_mask_ne ⟨p, hp⟩ ⟨n, hn8⟩) hs' hgt,
        hbits, hv]
      unfold collectedBit
      by_cases h : i % 8 = n
      · simp [hi, h, show ¬ n < n from Nat.lt_irrefl n]
      · by_cases h' : i % 8 < n
        · simp [hi, h, h', show i % 8 < n + 1 by omega]
        · simp [hi, h, h', show ¬ i % 8 < n + 1 by omega]
    · rw [hgt, BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge _ _ (by omega : 32 ≤ i)]
      simp [collectedBit, hi]

private theorem collect3072Rows_succ (p n : Nat) :
    collect3072Rows p (n + 1) = collect3072Rows p n ++ collect3072Row p n := by
  simp only [collect3072Rows, List.range_succ, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

private theorem collect3072Rows_join (s u t : State) (p n : Nat)
    (h₁ : runBlock isa (collect3072Rows p n) s = some u)
    (h₂ : runBlock isa (collect3072Row p n) u = some t) :
    runBlock isa (collect3072Rows p (n + 1)) s = some t := by
  rw [collect3072Rows_succ, normalize_run_append, h₁, Option.bind_some, h₂]

/-- The provisional row values and packed masks after the row loop. -/
theorem collect3072Rows_run (s : State) (p n : Nat) (hp : p < 2) (hn : n ≤ 8)
    (hm : ∀ k < 4, qv s (vreg 24) k = mask52) (hs : s.gpr .rsi = 0x01010101)
    (hz : s.gpr .rax = 0 ∧ s.gpr .rcx = 0) :
    ∃ t, runBlock isa (collect3072Rows p n) s = some t ∧ CarryCollected s t p n := by
  induction n with
  | zero =>
    refine ⟨s, runBlock_nil, ?_⟩
    refine ⟨by simp, fun _ _ => rfl, fun _ _ _ _ => rfl, ?_, rfl, rfl, rfl, rfl⟩
    intro gt i
    cases gt <;> simp [collectedBit, hz.1, hz.2]
  | succ n ih =>
    obtain ⟨u, hu, hc⟩ := ih (by omega)
    obtain ⟨t, ht, hs'⟩ := collect3072Rows_step s u p n hp (by omega) hm hs hc
    exact ⟨t, collect3072Rows_join s u t p n hu ht, hs'⟩

end VG.Proof.Bignum.X86_64.Ifma
