module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.Run
public import VerifiedGarbage.Proof.Cast5.Table
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# CAST5 on PPC64LE: the scan of a table

`scan` visits the 256 entries of the table at `tbl`, in order, and leaves in
`r18 + k` word `k` of the entry whose number is in `r14 + k` (`scan_ok`),
zero-extended.
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE

open VG VG.PPC64LE VG.Impl.Cast5.PPC64LE

theorem idxReg_ne {k : Nat} : ∀ r ∈ [Reg.r0, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r27], idxReg k ≠ r := by
  unfold idxReg; split <;> decide
theorem accReg_ne {k : Nat} : ∀ r ∈ [Reg.r0, .r14, .r15, .r16, .r17, .r22, .r23, .r24, .r25, .r27], accReg k ≠ r := by
  unfold accReg; split <;> decide

theorem accReg_inj {k e : Nat} (hk : k < 4) (he : e < 4) (h : accReg k = accReg e) : k = e := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;>
  first | rfl | exact absurd h (by decide)

/-- One lookup at entry `j` (in `num`), the entry's words at `ep`. -/
theorem look_ok (s : State) (k : Nat) (hk : k < 4) {j : Nat} (hj : j < 256)
    (h0 : s.gpr .r0 = 0) (hj' : s.gpr num = BitVec.ofNat 64 j) (hx : (s.gpr (idxReg k)).toNat < 256)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr ep + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (look k)) s fun t =>
      t.gpr (accReg k) = (s.gpr (accReg k) ||| (if s.gpr (idxReg k) = BitVec.ofNat 64 j then
        (s.mem.readW (s.gpr ep + BitVec.ofNat 64 (4 * k)) 32).setWidth 64 else 0)) ∧
      Keep [tmp, wd, accReg k] s t ∧ t.mem = s.mem := by
  have ho : 4 * k < 2 ^ 15 := by omega
  unfold look
  have i24 : idxReg k ≠ .r24 := idxReg_ne _ (by decide)
  have i25 : idxReg k ≠ .r25 := idxReg_ne _ (by decide)
  have a24 : accReg k ≠ .r24 := accReg_ne _ (by decide)
  have a25 : accReg k ≠ .r25 := accReg_ne _ (by decide)
  c5run [ho, hin, h0, hj', i24, i25, a24, a25]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · rw [mask_eq hx hj]
    split
    · rw [BitVec.and_allOnes]
    · exact congrArg _ (BitVec.eq_of_getLsbD_eq (by simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2, ite_false]

/-- Word `k` of entry `e` of the table at `T`, zero-extended. -/
abbrev tw (m : Mem) (T : Addr) (e k : Nat) : BitVec 64 := (ent m T e k).setWidth 64

/-- The value of lookup `k` once entries `0 … j - 1` are visited. -/
def acc (tab : Nat → Nat → BitVec 64) (idx : Nat → BitVec 64) (j k : Nat) : BitVec 64 :=
  if (idx k).toNat < j then tab (idx k).toNat k else 0

theorem acc_succ (tab : Nat → Nat → BitVec 64) (idx : Nat → BitVec 64) {j : Nat} (hj : j < 256) (k : Nat) :
    (acc tab idx j k ||| if idx k = BitVec.ofNat 64 j then tab j k else 0) = acc tab idx (j + 1) k := by
  unfold acc
  by_cases h : idx k = BitVec.ofNat 64 j
  · have hn : (idx k).toNat = j := by rw [h, BitVec.toNat_ofNat]; omega
    rw [ite_eq_left h, ite_eq_right (by omega), ite_eq_left (by omega), hn]
    exact BitVec.eq_of_getLsbD_eq (by simp)
  · have hn : (idx k).toNat ≠ j := fun h' => h (BitVec.eq_of_toNat_eq (by
      rw [h', BitVec.toNat_ofNat]; omega))
    rw [ite_eq_right h, show ∀ y : BitVec 64, y ||| 0 = y from fun y => BitVec.eq_of_getLsbD_eq (by simp)]
    by_cases h2 : (idx k).toNat < j
    · rw [ite_eq_left h2, ite_eq_left (by omega)]
    · rw [ite_eq_right h2, ite_eq_right (by omega)]

/-- The registers the loop of a scan writes. -/
def loopRegs : List Reg := [tmp, wd, num, ep, .r18, .r19, .r20, .r21]

/-- The state of the scan of the table at `T` in the memory `m` with entries
`0 … j - 1` visited, from `s₀`. -/
structure ScanAt (s₀ : State) (m : Mem) (T : Addr) (idx : Nat → BitVec 64) (j : Nat) (s : State) : Prop where
  hidx : ∀ k < 4, s.gpr (idxReg k) = idx k
  hacc : ∀ k < 4, s.gpr (accReg k) = acc (tw m T) idx j k
  num : s.gpr num = BitVec.ofNat 64 j
  ep : s.gpr ep = T + BitVec.ofNat 64 (16 * j)
  zero : s.gpr .r0 = 0
  keep : Keep loopRegs s₀ s
  mem : s.mem = m

theorem accReg_mem (k : Nat) : accReg k ∈ loopRegs := by
  unfold accReg; split <;> decide

theorem entry_ok {s₀ s : State} {m : Mem} {T : Addr} {idx : Nat → BitVec 64} {j : Nat}
    (hj : j < 256) (hidx : ∀ k < 4, (idx k).toNat < 256)
    (hrT : (⟨T, 4096⟩ : Region) ∈ s₀.rd ++ s₀.wr) (h : ScanAt s₀ m T idx j s) :
    WP isa (.block scanEntry) s fun t =>
      (∀ k < 4, t.gpr (idxReg k) = idx k) ∧ (∀ k < 4, t.gpr (accReg k) = acc (tw m T) idx (j + 1) k) ∧
      t.gpr num = BitVec.ofNat 64 j ∧ t.gpr ep = T + BitVec.ofNat 64 (16 * j) ∧ t.gpr .r0 = 0 ∧
      Keep loopRegs s₀ t ∧ t.mem = m := by
  -- Lookups `0 … e - 1` done.
  have step : ∀ e ≤ 4, WP isa (.block ((List.range e).flatMap look)) s
      fun t => (∀ k < 4, t.gpr (idxReg k) = idx k) ∧
        (∀ k < 4, t.gpr (accReg k) = if k < e then acc (tw m T) idx (j + 1) k else acc (tw m T) idx j k) ∧
        t.gpr num = BitVec.ofNat 64 j ∧ t.gpr ep = T + BitVec.ofNat 64 (16 * j) ∧ t.gpr .r0 = 0 ∧
        Keep loopRegs s₀ t ∧ t.mem = m := by
    intro e he
    induction e with
    | zero => exact wp_nil ⟨h.hidx, fun k hk => by rw [ite_eq_right (by omega)]; exact h.hacc k hk,
        h.num, h.ep, h.zero, h.keep, h.mem⟩
    | succ e ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        WP.block_append_iff]
      refine WP.mono (ih (by omega)) fun t ⟨ti, ta, t2, t3, t0, tk, tm⟩ => ?_
      have ea : t.gpr ep + BitVec.ofNat 64 (4 * e) = T + BitVec.ofNat 64 (16 * j + 4 * e) := by
        rw [t3, Offset.add_add]
      have hin : InRegions (t.rd ++ t.wr) (t.gpr ep + BitVec.ofNat 64 (4 * e)) 4 := by
        rw [tk.2.1, tk.2.2, ea]; exact ⟨_, hrT, Offset.contains_base _ (by omega) (by omega)⟩
      refine WP.mono (look_ok t e (by omega) hj t0 t2 (by rw [ti e (by omega)]; exact hidx e (by omega)) hin)
        fun u ⟨ua, uk, um⟩ => ?_
      have ug (r : Reg) (hr : r ∉ [tmp, wd, accReg e]) : u.gpr r = t.gpr r := uk.gpr hr
      refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_, ?_,
        (tk.trans uk).mono fun r hr => ?_, um.trans tm⟩
      · rw [ug _ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨idxReg_ne _ (by decide), idxReg_ne _ (by decide), (accReg_ne _ (by
            unfold idxReg; split <;> decide)).symm⟩), ti k hk]
      · by_cases hke : k = e
        · subst hke
          have ev : (t.mem.readW (t.gpr ep + BitVec.ofNat 64 (4 * k)) 32).setWidth 64 = tw m T j k := by
            rw [tm, t3, Offset.add_add]; rfl
          rw [ite_eq_left (by omega), ua, ta k hk, ite_eq_right (by omega), ti k hk, ev, acc_succ _ idx hj]
        · have hne : accReg k ≠ accReg e := fun h' => hke (accReg_inj hk (by omega) h')
          rw [ug _ (by
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
            exact ⟨accReg_ne _ (by decide), accReg_ne _ (by decide), hne⟩), ta k hk]
          by_cases hk' : k < e
          · rw [ite_eq_left hk', ite_eq_left (by omega)]
          · rw [ite_eq_right hk', ite_eq_right (by omega)]
      · rw [ug _ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨by decide, by decide, (accReg_ne _ (by decide)).symm⟩), t2]
      · rw [ug _ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨by decide, by decide, (accReg_ne _ (by decide)).symm⟩), t3]
      · rw [ug _ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨by decide, by decide, (accReg_ne _ (by decide)).symm⟩), t0]
      · rcases List.mem_append.mp hr with hr | hr
        · exact hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · decide
        · decide
        · exact accReg_mem e
  refine WP.mono (step 4 (Nat.le_refl _)) fun t ⟨ti, ta, t2, t3, t0, tk, tm⟩ =>
    ⟨ti, fun k hk => ?_, t2, t3, t0, tk, tm⟩
  rw [ta k hk, ite_eq_left hk]

/-- An iteration of the loop: an entry, then on to the next. -/
theorem body_ok {s₀ s : State} {m : Mem} {T : Addr} {idx : Nat → BitVec 64} {j : Nat}
    (hj : j < 256) (hidx : ∀ k < 4, (idx k).toNat < 256)
    (hrT : (⟨T, 4096⟩ : Region) ∈ s₀.rd ++ s₀.wr) (h : ScanAt s₀ m T idx j s) :
    WP isa (.block scanBody) s fun t => ScanAt s₀ m T idx (j + 1) t ∧
      t.gpr tmp = BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 256 := by
  unfold scanBody
  rw [WP.block_append_iff]
  refine WP.mono (entry_ok hj hidx hrT h) fun t ⟨ti, ta, t2, t3, t0, tk, tm⟩ => ?_
  c5run [t2, t3]
  refine ⟨⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, tk.2.1, tk.2.2⟩, tm⟩, ?_⟩
  · rw [← ti k hk]
    simp only [idxReg_ne _ (show Reg.r24 ∈ _ by decide), idxReg_ne _ (show Reg.r22 ∈ _ by decide),
      idxReg_ne _ (show Reg.r23 ∈ _ by decide), ite_false]
  · rw [← ta k hk]
    simp only [accReg_ne _ (show Reg.r24 ∈ _ by decide), accReg_ne _ (show Reg.r22 ∈ _ by decide),
      accReg_ne _ (show Reg.r23 ∈ _ by decide), ite_false]
  · simp only [reduceCtorEq, ↓reduceIte]; rw [BitVec.ofNat_add]
  · simp only [reduceCtorEq, ↓reduceIte]
    rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add_eq _ (show 16 * j + 16 = 16 * (j + 1) by omega)]
  · simp only [reduceCtorEq, ↓reduceIte]; exact t0
  · simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h4, h2, h3, h5⟩ := hr
    simp only [h1, h2, h3, ite_false]
    exact tk.gpr (by simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h4, h2, h3, h5⟩)
  · rw [BitVec.ofNat_add]

/-- What a scan needs: the indices below 256, zero in `r0`, and the table,
4096 bytes at `tbl`, readable. -/
structure ScanPre (s : State) : Prop where
  idx : ∀ k < 4, (s.gpr (idxReg k)).toNat < 256
  zero : s.gpr .r0 = 0
  trd : (⟨s.gpr tbl, 4096⟩ : Region) ∈ s.rd ++ s.wr

/-- The tested count after entry `j`, nonzero until the last. -/
theorem tmp_ne {j : Nat} (hj : j < 256) :
    (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 256 != 0) = !decide (j = 255) := by
  by_cases he : j = 255
  · subst he; rfl
  · rw [decide_eq_false he]
    have : BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 256 ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
      simp at this; omega
    simpa using this

/-- The scan: `r18 + k` is word `k` of the entry of the table whose number
is in `r14 + k`, zero-extended; only the scan's registers are written. -/
theorem scan_ok (s : State) (h : ScanPre s) :
    WP isa scan s fun t =>
      (∀ k < 4, t.gpr (accReg k) = tw s.mem (s.gpr tbl) (s.gpr (idxReg k)).toNat k) ∧
      Keep loopRegs s t ∧ t.mem = s.mem := by
  obtain ⟨T, hT⟩ : ∃ T, s.gpr tbl = T := ⟨_, rfl⟩
  have hrT : (⟨T, 4096⟩ : Region) ∈ s.rd ++ s.wr := hT ▸ h.trd
  unfold scan
  refine WP.seq (WP.mono (Q := fun s₁ => ScanAt s s.mem T (fun k => s.gpr (idxReg k)) 0 s₁) ?_ fun s₁ h₁ => ?_)
  · c5run [hT]
    refine ⟨fun k hk => ?_, fun k hk => ?_, rfl, ?_, ?_, ⟨?_, rfl, rfl⟩, rfl⟩
    · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
    · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
        simp only [acc, Nat.not_lt_zero, ite_false] <;> rfl
    · simp only [reduceCtorEq, ↓reduceIte]; rw [Nat.mul_zero, BitVec.add_zero]
    · simp only [reduceCtorEq, ↓reduceIte]; exact h.zero
    · intro r hr
      simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨_, _, h2, h3, h8, h9, h10, h11⟩ := hr
      simp only [h2, h3, h8, h9, h10, h11, ite_false]
  -- The loop.
  refine WP.loop (M := isa) (fun n (v : State) => ∃ j, n = 256 - j ∧ j < 256 ∧
      ScanAt s s.mem T (fun k => s.gpr (idxReg k)) j v) ?_ 256 s₁ ⟨0, rfl, by decide, h₁⟩
  rintro n v ⟨j, rfl, hj, hv⟩
  refine WP.mono (body_ok hj (fun k hk => h.idx k hk) hrT hv) fun w ⟨hw, wt⟩ => ?_
  have ev : isa.eval (.nonzero .d tmp) w = some (!decide (j = 255)) := by
    rw [eval_nonzero, wt, tmp_ne hj]
  by_cases he : j = 255
  · subst he
    refine .inl ⟨by rw [ev]; rfl, fun k hk => ?_, hw.keep, hw.mem⟩
    rw [hw.hacc k hk, acc, ite_eq_left (h.idx k hk), hT]
  · exact .inr ⟨by rw [ev, decide_eq_false he]; rfl, 256 - (j + 1), by omega, j + 1, rfl, by omega, hw⟩

end VG.Proof.Cast5.PPC64LE
