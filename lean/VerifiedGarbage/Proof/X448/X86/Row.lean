import VerifiedGarbage.Proof.X448.X86.RowTail

/-!
# X448 on x86 (32-bit): one multiplication row

Bounded input limbs and previous product digits keep every multiply-add within
a 32-bit word. The row reads `a_i` with code `ldA` and `b_j` at `mb j`
(`rowWith_ok`): X448's own rows read both at constant offsets of `edi`
(`row_ok`), the field function's through its operand pointers.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem acc_shift (m : Mem) (base : Addr) (i j : Nat) :
    limbs m base (ACC + 4 * i) j = accw m base (i + j) := by
  change (word m base (ACC + 4 * i + 4 * j)).toNat = _
  rw [show ACC + 4 * i + 4 * j = ACC + 4 * (i + j) by omega]

/-- What a row needs of the code `ldA` loading `a_i` (from any state of the
row's invariant) and of the addresses `mb j` of `b_j` (from any state whose
registers but `clob` are those of `s0`). -/
structure RowCode (base : Addr) (a b : Nat) (s0 : State) (i : Nat) (ldA : List Instr)
    (mb : Nat → MemOp) : Prop where
  ldA : ∀ s, RowInv base a b s0 i s → WP isa (.block ldA) s fun t =>
    t.gpr .ecx = word s.mem base (a + 4 * i) ∧ Keeps [.ecx] s t ∧ t.mem = s.mem
  mb : ∀ j < 28, ∀ s, Scr s base → Keeps clob s0 s → s.ea (mb j) = off base (b + 4 * j)

theorem rowWith_ok {base : Addr} {a b : Nat} (ha : Slot a) (hb : Slot b) {s0 s : State}
    {ldA : List Instr} {mb : Nat → MemOp}
    (ab : Bounded s0.mem base a) (bb : Bounded s0.mem base b) {i : Nat} (hi : i < 28)
    (hc : RowCode base a b s0 i ldA mb) (h : RowInv base a b s0 i s) :
    WP isa (.block (rowWith ldA mb)) s fun t =>
      RowInv base a b s0 (i + 1) t ∧ t.zf = some (decide (i + 1 = 28)) := by
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  have input : ∀ o, Slot o → ∀ j < 28, limbs s.mem base o j = limbs s0.mem base o j := by
    intro o ho j hj
    exact h.mem.limbs (Or.inl ho) (Nat.le_trans ho (by decide)) hj
  unfold rowWith
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (hc.ldA s h) fun t ⟨tc, tk, tm⟩ => ?_
  refine wp_mov rfl fun u hu => ?_
  have ku : Keeps [.ecx, .ebx] s u := (tk.mono (by decide)).trans (hu.rest (by decide))
  have us := h.scr.of_keeps ku (by decide)
  have um : u.mem = s.mem := hu.mem.trans tm
  have uc : (u.gpr .ecx).toNat = limbs s0.mem base a i := by
    rw [hu.other .ecx (by decide), tc]; exact input a ha i hi
  have up : u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [ku.1 _ (by decide), ku.1 _ (by decide)]; exact h.ptr
  have k0u : Keeps clob s0 u := h.regs.trans (ku.mono (by decide))
  let c := rowC (accw s.mem base) (limbs s0.mem base a) (limbs s0.mem base b) i
  have cb : ∀ j < 28, c j ≤ 2 ^ 32 - radix := by
    intro j hj
    exact rowC_bound (ab i hi) (bb j hj) (h.lt (i + j) (by omega))
  change WP isa (.block (carryPass .ebp ACC (rowSrcWith mb) ++ rowEnd)) u _
  rw [WP.block_append_iff]
  refine WP.mono (carryPass_ok (s0 := u) (base := base) (o := ACC + 4 * i) (c := c)
    (by decide) (by simp only [ACC]; omega)
    (fun j hj => by
      rw [rowEa us up (by simp only [ACC]; omega),
        show 4 * i + (ACC + 4 * j) = ACC + 4 * i + 4 * j by omega])
    (fun j hj => us.write (by simp only [ACC]; omega)) (by rw [hu.gpr]; rfl) cb ?_) fun v hv => ?_
  · intro j hj v hv
    have vs := us.of_keeps hv.regs (by decide)
    have vp : v.gpr .ebp = v.gpr .edi + BitVec.ofNat 32 (4 * i) := by
      rw [hv.regs.1 _ (by decide), hv.regs.1 _ (by decide)]; exact up
    have va : (v.gpr .ecx).toNat = limbs s0.mem base a i := by rw [hv.regs.1 _ (by decide), uc]
    have vb : limbs v.mem base b j = limbs s0.mem base b j := by
      rw [hv.mem.limbs (Or.inl (by simp only [ACC]; omega)) (by omega) hj, um, input b hb j hj]
    have vacc : accw v.mem base (i + j) = accw s.mem base (i + j) := by
      change (word v.mem base (ACC + 4 * (i + j))).toNat = _
      rw [hv.mem.word (Or.inr (by omega)) (by simp only [ACC]; omega), um]
    refine WP.mono (rowSrcWith_ok vs hb hi hj vp (hc.mb j hj v vs (k0u.trans (hv.regs.mono (by decide))))
      (by rw [va]; exact ab i hi) (by rw [vb]; exact bb j hj)
      (by rw [vacc]; exact h.lt (i + j) (by omega))) fun w ⟨wv, wk, wm⟩ => ⟨?_, wk, wm⟩
    rw [va, vb, vacc] at wv
    exact wv
  · have vs := us.of_keeps hv.regs (by decide)
    have vp : v.gpr .ebp = v.gpr .edi + BitVec.ofNat 32 (4 * i) := by
      rw [hv.regs.1 _ (by decide), hv.regs.1 _ (by decide)]; exact up
    refine WP.mono (rowTail_ok vs hi vp) fun w ⟨wp, wz, wm, wk⟩ => ?_
    have passMem : Outside base (ACC + 4 * i) 112 s.mem v.mem := by rw [← um]; exact hv.mem
    have kv : Keeps clob s v := (ku.mono (by decide)).trans (hv.regs.mono (by decide))
    have limbsOut : ∀ k < i + 29, accw w.mem base k =
        rowAcc (accw s.mem base) (limbs s0.mem base a) (limbs s0.mem base b) i k := by
      intro k hk
      change (word w.mem base (ACC + 4 * k)).toNat = _
      rw [wm, word_write v.mem base (by simp only [ACC]; omega) (by simp only [ACC]; omega)]
      by_cases he : k = i + 28
      · rw [ite_eq_left he, hv.carry]
        simp only [c, rowAcc, he, show ¬i + 28 < i by omega, Nat.lt_irrefl, ite_false]
      · rw [ite_eq_right he]
        by_cases hk' : k < i
        · rw [passMem.word (Or.inl (by omega)) (by simp only [ACC]; omega)]
          simp only [rowAcc, hk', ite_true]
        · have out := hv.outs (k - i) (by omega)
          rw [acc_shift, show i + (k - i) = k by omega] at out
          change accw v.mem base k = _
          rw [out]
          simp only [c, rowAcc, hk', show k < i + 28 by omega, ite_false, ite_true]
    refine ⟨⟨vs.of_keeps wk (by decide), h.regs.trans (kv.trans wk), wp, ?_, ?_, ?_⟩, wz⟩
    · rw [wm]
      exact (h.mem.trans (passMem.mono (by omega) (by omega))).trans
        ((writeW_outside _ _ _ (by simp only [ACC]; omega)).mono (by omega) (by omega))
    · intro k hk
      rw [limbsOut k hk]
      exact rowAcc_lt (fun k hk => h.lt k (by omega)) cb k hk
    · rw [valN_congr limbsOut]
      exact row_val h.val

/-- X448's rows: `a_i` and `b_j` at constant offsets of `edi`. -/
theorem rowCode_sc (base : Addr) {a b : Nat} (ha : Slot a) (hb : Slot b) (s0 : State) {i : Nat}
    (hi : i < 28) :
    RowCode base a b s0 i [.mov .ecx (.mem (at_ .ebp a))] (fun j => sc (b + 4 * j)) := by
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  refine ⟨fun s h => ?_, fun j hj s hs _ => hs.ea (by omega)⟩
  · refine wp_load (by rw [rowEa h.scr h.ptr (by omega), Nat.add_comm]) (h.scr.read (by omega))
      fun t ht => WP.block_nil ⟨ht.gpr, ht.rest (by decide), ht.mem⟩

theorem row_ok {base : Addr} {a b : Nat} (ha : Slot a) (hb : Slot b) {s0 s : State}
    (ab : Bounded s0.mem base a) (bb : Bounded s0.mem base b) {i : Nat} (hi : i < 28)
    (h : RowInv base a b s0 i s) :
    WP isa (.block (row a b)) s fun t => RowInv base a b s0 (i + 1) t ∧ t.zf = some (decide (i + 1 = 28)) :=
  rowWith_ok ha hb ab bb hi (rowCode_sc base ha hb s0 hi) h

end VG.Proof.X448.X86
