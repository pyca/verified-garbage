import VerifiedGarbage.Proof.Cast5.Arm.Run

/-!
# CAST5 on ARMv7: the scan of a table

`scan tab` visits the 256 entries of `tab`, in order, and leaves in
`r8 + k` word `k` of the entry whose number is in `r4 + k` (`scan_ok`).
-/

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Cast5.Arm

theorem vec_getD (v : Vector Spec.Cast5.Word 256) {j : Nat} (hj : j < 256) :
    v.toList.getD j 0 = v[(BitVec.ofNat 8 j).toFin] := by
  simp only [List.getD_eq_getElem?_getD, Vector.getElem?_toList, BitVec.toFin_ofNat, Fin.getElem_fin,
    Fin.val_ofNat, Nat.mod_eq_of_lt hj, Vector.getElem?_eq_getElem hj, Option.getD_some]

theorem tab1234_eq {j k : Nat} (hj : j < 256) (hk : k < 4) :
    tab1234 j k = tabOf Spec.Cast5.S4 Spec.Cast5.S3 Spec.Cast5.S2 Spec.Cast5.S1 j k := by
  unfold tab1234 tab1234Nat
  rw [show (4 * j + k) / 4 = j by omega, show (4 * j + k) % 4 = k by omega, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
    exact vec_getD _ hj

theorem tab5678_eq {j k : Nat} (hj : j < 256) (hk : k < 4) :
    tab5678 j k = tabOf Spec.Cast5.S8 Spec.Cast5.S7 Spec.Cast5.S6 Spec.Cast5.S5 j k := by
  unfold tab5678 tab5678Nat
  rw [show (4 * j + k) / 4 = j by omega, show (4 * j + k) % 4 = k by omega, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
    exact vec_getD _ hj

theorem idxReg_ne_r0 (k : Nat) : idxReg k ≠ .r0 := by
  unfold idxReg; split <;> decide
theorem idxReg_ne_r1 (k : Nat) : idxReg k ≠ .r1 := by
  unfold idxReg; split <;> decide
theorem accReg_ne_r0 (k : Nat) : accReg k ≠ .r0 := by
  unfold accReg; split <;> decide
theorem accReg_ne_r1 (k : Nat) : accReg k ≠ .r1 := by
  unfold accReg; split <;> decide
theorem accReg_ne_idxReg (k k' : Nat) : accReg k ≠ idxReg k' := by
  unfold accReg idxReg; split <;> split <;> decide

theorem accReg_inj {k e : Nat} (hk : k < 4) (he : e < 4) (h : accReg k = accReg e) : k = e := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;>
  first | rfl | exact absurd h (by decide)

/-- The mask of a lookup: all ones iff the index `x` is `j`. -/
theorem mask_eq {x : BitVec 32} (hx : x.toNat < 256) {j : Nat} (hj : j < 256) :
    (((x ^^^ BitVec.ofNat 32 j) - 1) >>> 8 ||| ((x ^^^ BitVec.ofNat 32 j) - 1) >>> 8 <<< 8) =
      if x = BitVec.ofNat 32 j then BitVec.allOnes 32 else 0 := by
  by_cases h : x = BitVec.ofNat 32 j
  · rw [ite_eq_left h, h, BitVec.xor_self]
    decide
  · rw [ite_eq_right h]
    obtain ⟨z, hz⟩ : ∃ z, x ^^^ BitVec.ofNat 32 j = z := ⟨_, rfl⟩
    have hzl : z.toNat < 256 := by
      rw [← hz, BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact Nat.xor_lt_two_pow (n := 8) hx hj
    have hz0 : z ≠ 0 := fun e => h (by
      rw [e] at hz
      have := congrArg (· ^^^ BitVec.ofNat 32 j) hz
      simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at this
      rw [this]; exact BitVec.eq_of_getLsbD_eq (by simp))
    have hz1 : z.toNat ≠ 0 := fun e => hz0 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    rw [hz]
    have hs : (z - 1) >>> 8 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow,
        show (1 : BitVec 32).toNat = 1 from rfl, show (0 : BitVec 32).toNat = 0 from rfl]
      omega
    rw [hs]
    rfl

theorem movImm_val (v : BitVec 32) :
    ((v.extractLsb' 16 16 ++ ((v.extractLsb' 0 16).setWidth 32).extractLsb' 0 16 : BitVec 32)) = v :=
  movw_movt v

/-- One lookup at entry `j`. -/
theorem box_ok (s : State) {j : Nat} (hj : j < 256) (k : Nat) (v : BitVec 32)
    (hx : (s.gpr (idxReg k)).toNat < 256) :
    WP isa (.block (scanBox j k v)) s fun t =>
      t.gpr (accReg k) = (s.gpr (accReg k) ||| (if s.gpr (idxReg k) = BitVec.ofNat 32 j then v else 0)) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ accReg k → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hjv := toNat_ofNat_lt hj
  unfold scanBox movImm
  crun [hjv, idxReg_ne_r0, idxReg_ne_r1, accReg_ne_r0, accReg_ne_r1]
  refine ⟨?_, fun r h0 h1 hk => by simp only [h0, h1, hk, ite_false]⟩
  rw [movImm_val, mask_eq hx hj]
  split
  · rw [BitVec.and_allOnes]
  · rw [show v &&& 0 = 0 from BitVec.eq_of_getLsbD_eq (by simp)]

/-- The value of lookup `k` once entries `0 … j - 1` are visited. -/
def acc (tab : Nat → Nat → BitVec 32) (idx : Nat → BitVec 32) (j k : Nat) : BitVec 32 :=
  if (idx k).toNat < j then tab (idx k).toNat k else 0

theorem acc_succ (tab : Nat → Nat → BitVec 32) (idx : Nat → BitVec 32) {j : Nat} (hj : j < 256) (k : Nat) :
    (acc tab idx j k ||| if idx k = BitVec.ofNat 32 j then tab j k else 0) = acc tab idx (j + 1) k := by
  unfold acc
  by_cases h : idx k = BitVec.ofNat 32 j
  · have hn : (idx k).toNat = j := by rw [h, BitVec.toNat_ofNat]; omega
    rw [ite_eq_left h, ite_eq_right (by omega), ite_eq_left (by omega), hn]
    exact BitVec.eq_of_getLsbD_eq (by simp)
  · have hn : (idx k).toNat ≠ j := fun h' => h (BitVec.eq_of_toNat_eq (by
      rw [h', BitVec.toNat_ofNat]; omega))
    rw [ite_eq_right h, show ∀ y : BitVec 32, y ||| 0 = y from fun y => BitVec.eq_of_getLsbD_eq (by simp)]
    by_cases h2 : (idx k).toNat < j
    · rw [ite_eq_left h2, ite_eq_left (by omega)]
    · rw [ite_eq_right h2, ite_eq_right (by omega)]

/-- The state of the scan with entries `0 … j - 1` visited, from `s₀`. -/
structure ScanAt (s₀ : State) (tab : Nat → Nat → BitVec 32) (idx : Nat → BitVec 32) (j : Nat)
    (s : State) : Prop where
  hidx : ∀ k < 4, s.gpr (idxReg k) = idx k
  hacc : ∀ k < 4, s.gpr (accReg k) = acc tab idx j k
  keep : Keep [.r0, .r1, .r8, .r9, .r10, .r11] s₀ s
  mem : s.mem = s₀.mem

theorem accReg_mem (k : Nat) : accReg k ∈ [Reg.r0, .r1, .r8, .r9, .r10, .r11] := by
  unfold accReg; split <;> decide

theorem entry_ok {s₀ s : State} {tab : Nat → Nat → BitVec 32} {idx : Nat → BitVec 32} {j : Nat}
    (hj : j < 256) (hidx : ∀ k < 4, (idx k).toNat < 256) (h : ScanAt s₀ tab idx j s) :
    WP isa (.block (scanEntry tab j)) s (ScanAt s₀ tab idx (j + 1)) := by
  -- Boxes `0 … e - 1` done.
  have step : ∀ e ≤ 4, WP isa (.block ((List.range e).flatMap fun k => scanBox j k (tab j k))) s
      fun t => (∀ k < 4, t.gpr (idxReg k) = idx k) ∧
        (∀ k < 4, t.gpr (accReg k) = if k < e then acc tab idx (j + 1) k else acc tab idx j k) ∧
        Keep [.r0, .r1, .r8, .r9, .r10, .r11] s₀ t ∧ t.mem = s₀.mem := by
    intro e he
    induction e with
    | zero => exact WP.block_nil ⟨h.hidx, fun k hk => by rw [ite_eq_right (by omega)]; exact h.hacc k hk,
        h.keep, h.mem⟩
    | succ e ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        WP.block_append_iff]
      refine WP.mono (ih (by omega)) fun t ⟨ti, ta, tk, tm⟩ => ?_
      refine WP.mono (box_ok t hj e (tab j e) (by rw [ti e (by omega)]; exact hidx e (by omega)))
        fun u ⟨ua, uo, um, urd, uwr, usp⟩ => ?_
      refine ⟨fun k hk => by rw [uo _ (idxReg_ne_r0 k) (idxReg_ne_r1 k) (accReg_ne_idxReg e k).symm,
          ti k hk], fun k hk => ?_, tk.trans ⟨fun r hr => ?_, urd, uwr, usp⟩, um.trans tm⟩
      · by_cases hke : k = e
        · subst hke
          rw [ite_eq_left (by omega), ua, ta k hk, ite_eq_right (by omega), ti k hk, acc_succ tab idx hj]
        · have hne : accReg k ≠ accReg e := fun h' => hke (accReg_inj hk (by omega) h')
          rw [uo _ (accReg_ne_r0 k) (accReg_ne_r1 k) hne, ta k hk]
          by_cases hk' : k < e
          · rw [ite_eq_left hk', ite_eq_left (by omega)]
          · rw [ite_eq_right hk', ite_eq_right (by omega)]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        exact uo r hr.1 hr.2.1 fun e' => by
          rw [e'] at hr; unfold accReg at hr; split at hr <;> simp_all
  refine WP.mono (step 4 (Nat.le_refl _)) fun t ⟨ti, ta, tk, tm⟩ => ⟨ti, fun k hk => ?_, tk, tm⟩
  rw [ta k hk, ite_eq_left hk]

theorem entries_ok {s₀ : State} {tab : Nat → Nat → BitVec 32} {idx : Nat → BitVec 32}
    (hidx : ∀ k < 4, (idx k).toNat < 256) :
    ∀ cnt j s, j + cnt ≤ 256 → ScanAt s₀ tab idx j s → WP isa (scanFrom tab j cnt) s (ScanAt s₀ tab idx (j + cnt))
  | 0, j, s, _, h => WP.block_nil h
  | cnt + 1, j, s, hj, h => by
    unfold scanFrom
    refine WP.seq (WP.mono (entry_ok (by omega) hidx h) fun t ht => ?_)
    rw [show j + (cnt + 1) = j + 1 + cnt by omega]
    exact entries_ok hidx cnt (j + 1) t (by omega) ht

/-- The scan: `r8 + k` is word `k` of the entry of `tab` whose number is in
`r4 + k`; only `r0`, `r1` and `r8`–`r11` are written. -/
theorem scan_ok (s : State) (tab : Nat → Nat → BitVec 32) (hidx : ∀ k < 4, (s.gpr (idxReg k)).toNat < 256) :
    WP isa (scan tab) s fun t =>
      (∀ k < 4, t.gpr (accReg k) = tab (s.gpr (idxReg k)).toNat k) ∧
      Keep [.r0, .r1, .r8, .r9, .r10, .r11] s t ∧ t.mem = s.mem := by
  unfold scan
  refine WP.seq ?_
  crun
  refine WP.mono (entries_ok (s₀ := s) (tab := tab) (idx := fun k => s.gpr (idxReg k)) hidx 256 0
    ((((s.setReg .r8 0).setReg .r9 0).setReg .r10 0).setReg .r11 0) (by decide) ⟨fun k hk => ?_, fun k hk => ?_,
    ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl⟩) fun t ht => ⟨fun k hk => ?_, ht.keep, ht.mem⟩
  · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
  · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨_, _, h8, h9, h10, h11⟩ := hr
    simp only [RegUpd.gpr_setReg, h8, h9, h10, h11, ite_false]
  · rw [ht.hacc k hk, acc, ite_eq_left (hidx k hk)]

end VG.Proof.Cast5.Arm
