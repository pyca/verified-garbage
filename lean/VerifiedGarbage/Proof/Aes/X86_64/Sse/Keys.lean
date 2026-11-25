module

public import VerifiedGarbage.Proof.Aes.X86_64.Sse.Batch
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Interleave

/-! # The round keys in slices -/

@[expose] public section

namespace VG.Proof.Aes.X86_64.Sse

open VG VG.X86_64 VG.X86_64.RegUpd VG.X86_64.StraightX VG.Bitslice VG.Impl.Aes.X86_64.Sse VG.Proof.Aes

/-! ## The masks -/

theorem setMask_ok (k : Nat) (v : BitVec 64) (hk : k < 18) (s : State)
    (hin : InRegions s.wr (xAddr (s.gpr .r9) k) 16) :
    ∃ s', runBlock isa (setMask k v) s = some s' ∧
      (∀ l < 2, qword (s'.mem.readW (xAddr (s.gpr .r9) k) 128) l = v) ∧
      (∀ j < 18, j ≠ k → s'.mem.readW (xAddr (s.gpr .r9) j) 128 = s.mem.readW (xAddr (s.gpr .r9) j) 128) ∧
      Frame [⟨s.gpr .r9, 288⟩] s.mem s'.mem ∧
      (∀ x, x ≠ .rax → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [setMask, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec,
    XOp.exec, State.store128, ea_slot, stx, gpr_setXmm, gpr_setReg, reduceCtorEq, ite_false, ite_true, wr_setXmm,
    wr_setReg, hin, mem_setXmm, mem_setReg, xmm_setXmm, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, fun j hj hne => ?_, ?_, fun x a => ?_, by first | rfl | trivial, by first | rfl | trivial⟩
  · rw [readW_writeW_self128, qword_unpckl _ _ hl]
    have : ∀ x y : BitVec 64, qword (x ++ y) 0 = y := fun x y => by
      rw [StraightY.qword_app _ _ (by decide)]; simp
    split <;> exact this _ _
  · exact Mem.readW_writeW_sep (slot_sep _ (by omega) (by omega) hne) (by decide)
  · exact (Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))
  · simp only [a, ite_false]

theorem setMasks_eq : setMasks = maskVals.flatMap fun m => setMask m.1 m.2 := by decide

theorem masks_list (l : List (Nat × BitVec 64)) (hn : (l.map (·.1)).Nodup) (hl : ∀ m ∈ l, m.1 < 18) (s : State)
    (hin : ∀ k < 18, InRegions s.wr (xAddr (s.gpr .r9) k) 16) :
    ∃ s', runBlock isa (l.flatMap fun m => setMask m.1 m.2) s = some s' ∧
      (∀ m ∈ l, ∀ i < 2, qword (s'.mem.readW (xAddr (s.gpr .r9) m.1) 128) i = m.2) ∧
      (∀ j < 18, j ∉ l.map (·.1) → s'.mem.readW (xAddr (s.gpr .r9) j) 128 = s.mem.readW (xAddr (s.gpr .r9) j) 128) ∧
      Frame [⟨s.gpr .r9, 288⟩] s.mem s'.mem ∧
      (∀ x, x ≠ .rax → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  induction l generalizing s with
  | nil => exact ⟨s, rfl, fun _ h => absurd h List.not_mem_nil, fun _ _ _ => rfl, Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩
  | cons m l ih =>
    obtain ⟨s1, e1, a1, o1, f1, g1, r1, w1⟩ := setMask_ok m.1 m.2 (hl m List.mem_cons_self) s
      (hin _ (hl m List.mem_cons_self))
    have h9 : s1.gpr .r9 = s.gpr .r9 := g1 _ (by decide)
    obtain ⟨s2, e2, a2, o2, f2, g2, r2, w2⟩ := ih (List.nodup_cons.mp hn).2 (fun x hx => hl x (List.mem_cons_of_mem _ hx)) s1
      (by rw [w1, h9]; exact hin)
    rw [h9] at a2 o2 f2
    refine ⟨s2, ?_, fun x hx i hi => ?_, fun j hj hne => ?_, f1.trans f2, fun x a => (g2 x a).trans (g1 x a),
      r2.trans r1, w2.trans w1⟩
    · rw [List.flatMap_cons, Interleave.runBlock_append, e1, Option.bind_some, e2]
    · rcases List.mem_cons.mp hx with rfl | hx
      · rw [o2 _ (hl x List.mem_cons_self) (List.nodup_cons.mp hn).1]; exact a1 i hi
      · exact a2 x hx i hi
    · simp only [List.map_cons, List.mem_cons, not_or] at hne
      rw [o2 j hj hne.2, o1 j hj hne.1]

/-! ## The schedule's bytes -/

theorem rk_byte (m : Mem) (p : Addr) {nr i n : Nat} (hi : i ≤ nr) (hn : n < 16) :
    (Spec.Aes.roundKey (Spec.Aes.bytesAt m p (16 * (nr + 1))) i).getD n 0 = m (p + BitVec.ofNat 64 (16 * i + n)) := by
  simp only [Spec.Aes.roundKey, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD]
  rw [List.getElem?_take_of_lt hn, List.getElem?_drop, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

theorem rk_length (m : Mem) (p : Addr) {nr i : Nat} (hi : i ≤ nr) :
    (Spec.Aes.roundKey (Spec.Aes.bytesAt m p (16 * (nr + 1))) i).length = 16 := by
  simp only [Spec.Aes.roundKey, Spec.Aes.bytesAt, List.length_take, List.length_drop, List.length_map, List.length_range]
  omega

/-- The bits of a half of a round key. -/
theorem key_bit (m : Mem) (p : Addr) {nr i n j : Nat} (hi : i ≤ nr) (hn : n < 16) (hj : j < 8) :
    (m.readW (p + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (8 * (n / 8))) 64).getLsbD (8 * (n % 8) + j) =
      ((rkState (Spec.Aes.roundKey (Spec.Aes.bytesAt m p (16 * (nr + 1))) i)).getD n 0).getLsbD j := by
  rw [getD_rkState _ hn, rk_byte m p hi hn, Mem.readW, BitVec.getLsbD_setWidth, decide_eq_true (by omega), Bool.true_and,
    getLsbD_read _ _ (by omega), BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
    show 16 * i + (8 * (n / 8) + (8 * (n % 8) + j) / 8) = 16 * i + n by omega, show (8 * (n % 8) + j) % 8 = j by omega]

/-! ## Loading keys -/

theorem ea_at (s : State) (r : Reg) (d : Nat) : s.ea (Impl.Aes.X86_64.at_ r d) = s.gpr r + BitVec.ofNat 64 d := by
  simp only [State.ea, Impl.Aes.X86_64.at_, BitVec.ofInt_natCast]

theorem q_eqs : q 0 = .xmm0 ∧ q 1 = .xmm1 ∧ q 2 = .xmm2 ∧ q 3 = .xmm3 ∧ q 4 = .xmm4 ∧ q 5 = .xmm5 ∧ q 6 = .xmm6 ∧
    q 7 = .xmm7 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem spread_ok (s : State) :
    ∃ s', runBlock isa keySpread s = some s' ∧
      (∀ k < 4, ∀ h < 2, s'.xmm (q (k + 4 * h)) = s.xmm (q (4 * h))) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [keySpread, mv, q, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, XOp.exec, XBinOp.eval,
    xmm_setXmm, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, reduceCtorEq, ite_false, Option.some.injEq,
    exists_eq_left', and_self, and_true]
  intro k hk h hh
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    simp only [reduceCtorEq, ite_false, ite_true]

/-- Where a pair's or the last key's halves come from: key `l` is at `r10 + 16 (d l)`. -/
theorem load2_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .r10) 16)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .r10 + BitVec.ofNat 64 16) 16) :
    ∃ s', runBlock isa keyLoad2 s = some s' ∧
      (∀ l < 2, ∀ h < 2, qword (s'.xmm (q (4 * h))) l =
        s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (16 * l) + BitVec.ofNat 64 (8 * h)) 64) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h0' : InRegions (s.rd ++ s.wr) (s.gpr .r10 + BitVec.ofNat 64 0) 16 := by simpa using h0
  simp only [keyLoad2, mv, unpckl, unpckh, q, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, State.load128,
    ea_at, gpr_setXmm, rd_setXmm, wr_setXmm, mem_setXmm, h0', h1, ite_true, Option.map_some, XOp.exec, xmm_setXmm,
    reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl h hh => ?_, trivial, trivial, trivial, trivial⟩
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
  · simp only [Nat.mul_zero, reduceCtorEq, ite_false, ite_true]
    rw [qword_unpckl _ _ hl]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp only [ite_true]; rw [qword_readW _ _ (by decide)]
    · simp only [Nat.one_ne_zero, ite_false]; rw [qword_readW _ _ (by decide)]
  · simp only [Nat.mul_one, reduceCtorEq, ite_false, ite_true]
    rw [qword_unpckh _ _ hl]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp only [ite_true, XBinOp.eval]; rw [qword_readW _ _ (by decide)]
    · simp only [Nat.one_ne_zero, ite_false]; rw [qword_readW _ _ (by decide)]

theorem load1_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .r10) 16) :
    ∃ s', runBlock isa keyLoad1 s = some s' ∧
      (∀ l < 2, ∀ h < 2, qword (s'.xmm (q (4 * h))) l = s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (8 * h)) 64) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h0' : InRegions (s.rd ++ s.wr) (s.gpr .r10 + BitVec.ofNat 64 0) 16 := by simpa using h0
  simp only [keyLoad1, mv, unpckl, unpckh, q, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, State.load128,
    ea_at, gpr_setXmm, rd_setXmm, wr_setXmm, mem_setXmm, h0', ite_true, Option.map_some, XOp.exec, xmm_setXmm,
    reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl h hh => ?_, trivial, trivial, trivial, trivial⟩
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
  · simp only [Nat.mul_zero, reduceCtorEq, ite_false, ite_true]
    rw [qword_unpckl _ _ hl]
    simp only [ite_self]; rw [qword_readW _ _ (by decide)]; simp
  · simp only [Nat.mul_one, reduceCtorEq, ite_false, ite_true]
    rw [qword_unpckh _ _ hl]
    simp only [ite_self, XBinOp.eval]; rw [qword_readW _ _ (by decide)]; simp

/-! ## Storing keys -/

theorem lowStep (q0 q1 : XReg) (i : Nat) (s : State) (h : q0 ≠ .xmm8 ∧ q1 ≠ .xmm8)
    (hin : InRegions s.wr (s.gpr kp + BitVec.ofNat 64 (16 * i)) 16) :
    ∃ s', runBlock isa [mv .xmm8 q0, unpckl .xmm8 q1, .movdquStore (Impl.Aes.X86_64.at_ kp (16 * i)) .xmm8] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr kp + BitVec.ofNat 64 (16 * i)) (XBinOp.eval .punpcklqdq (s.xmm q0) (s.xmm q1)) ∧
      (∀ x, x ≠ .xmm8 → s'.xmm x = s.xmm x) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨a1, a2⟩ := h
  simp only [mv, unpckl, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, State.store128, XOp.exec, ea_at,
    gpr_setXmm, rd_setXmm, wr_setXmm, mem_setXmm, hin, ite_true, xmm_setXmm, a2, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, fun x c => ?_, trivial, trivial, trivial⟩
  simp only [c, ite_false]

theorem highStep (q0 q1 : XReg) (i : Nat) (s : State)
    (hin : InRegions s.wr (s.gpr kp + BitVec.ofNat 64 (64 + 16 * i)) 16) :
    ∃ s', runBlock isa [unpckh q0 q1, .movdquStore (Impl.Aes.X86_64.at_ kp (64 + 16 * i)) q0] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr kp + BitVec.ofNat 64 (64 + 16 * i)) (XBinOp.eval .punpckhqdq (s.xmm q0) (s.xmm q1)) ∧
      (∀ x, x ≠ q0 → s'.xmm x = s.xmm x) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [unpckh, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, State.store128, XOp.exec, ea_at,
    gpr_setXmm, wr_setXmm, mem_setXmm, hin, ite_true, xmm_setXmm, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun x c => ?_, by first | rfl | trivial, by first | rfl | trivial, by first | rfl | trivial⟩
  simp only [c, ite_false]

/-- The quadwords of a 16-byte store of two registers' quadwords `l`. -/
theorem store_pair {m : Mem} {a : Addr} {v : BitVec 128} {x y : BitVec 64}
    (hv : ∀ i < 2, qword v i = if i = 0 then x else y) (j : Nat) (hj : j < 2) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 (8 * j)) 64 = if j = 0 then x else y := by
  rw [← qword_readW _ _ hj, readW_writeW_self128, hv j hj]

/-- `n` steps of either store, of quadword `l` at `a`. -/
theorem stores_ok (c : Nat → List Instr) (a : State → Addr) (l : Nat)
    (hstep : ∀ i < 4, ∀ s : State, InRegions s.wr (a s + BitVec.ofNat 64 (16 * i)) 16 → ∃ s', ∃ v : BitVec 128,
      runBlock isa (c i) s = some s' ∧ s'.mem = s.mem.writeW (a s + BitVec.ofNat 64 (16 * i)) v ∧
      (∀ j < 2, qword v j = if j = 0 then lane q s l (2 * i) else lane q s l (2 * i + 1)) ∧
      (∀ j < 8, 2 * i + 2 ≤ j → s'.xmm (q j) = s.xmm (q j)) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    (ha : ∀ s s' : State, s'.gpr = s.gpr → a s' = a s)
    (s : State) (hin : ∀ i < 4, InRegions s.wr (a s + BitVec.ofNat 64 (16 * i)) 16) :
    ∀ n ≤ 4, ∃ s', runBlock isa ((List.range n).flatMap c) s = some s' ∧
      (∀ j < 2 * n, s'.mem.readW (a s + BitVec.ofNat 64 (8 * j)) 64 = lane q s l j) ∧
      (∀ j < 8, 2 * n ≤ j → s'.xmm (q j) = s.xmm (q j)) ∧
      s'.gpr = s.gpr ∧ Frame [⟨a s, 64⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  intro n hn
  induction n with
  | zero => exact ⟨s, rfl, fun j hj => absurd hj (Nat.not_lt_zero _), fun _ _ _ => rfl, rfl, Frame.refl _ _, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨s1, e1, h1, x1, g1, f1, r1, w1⟩ := ih (by omega)
    have ha1 := ha s s1 g1
    obtain ⟨s2, v, e2, hm, hv, hx, g2, r2, w2⟩ := hstep n (by omega) s1 (by rw [w1, ha1]; exact hin n (by omega))
    rw [ha1] at hm
    refine ⟨s2, ?_, fun j hj => ?_, fun j hj hnj => ?_, g2.trans g1, ?_, r2.trans r1, w2.trans w1⟩
    · rw [List.range_succ, List.flatMap_append, Interleave.runBlock_append, e1, Option.bind_some, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, e2]
    · by_cases hj' : j < 2 * n
      · rw [hm, Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide), h1 j hj']
      · have := store_pair (m := s1.mem) (a := a s + BitVec.ofNat 64 (16 * n)) hv (j - 2 * n) (by omega)
        rw [← hm, BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * n + 8 * (j - 2 * n) = 8 * j by omega] at this
        rw [this]
        rcases (by omega : j = 2 * n ∨ j = 2 * n + 1) with rfl | rfl
        · simp only [Nat.sub_self, ite_true, lane, x1 (2 * n) (by omega) (by omega)]
        · simp only [show 2 * n + 1 - 2 * n = 1 by omega, Nat.one_ne_zero, ite_false, lane, x1 (2 * n + 1) (by omega) (by omega)]
    · rw [hx j hj (by omega), x1 j hj (by omega)]
    · rw [hm]
      exact f1.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))

theorem q_inj {i j : Nat} (hi : i < 8) (hj : j < 8) (h : q i = q j) : i = j := (q_ne i hi).2.2 j hj h

theorem storeLow_ok (s : State) (hin : ∀ i < 4, InRegions s.wr (s.gpr .rax + BitVec.ofNat 64 (16 * i)) 16) :
    ∃ s', runBlock isa storeLow s = some s' ∧
      (∀ j < 8, s'.mem.readW (s.gpr .rax + BitVec.ofNat 64 (8 * j)) 64 = lane q s 0 j) ∧
      (∀ j < 8, s'.xmm (q j) = s.xmm (q j)) ∧ s'.gpr = s.gpr ∧ Frame [⟨s.gpr .rax, 64⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have key := stores_ok (fun i => [mv .xmm8 (q (2 * i)), unpckl .xmm8 (q (2 * i + 1)),
      .movdquStore (Impl.Aes.X86_64.at_ kp (16 * i)) .xmm8]) (fun s => s.gpr .rax) 0
    (fun i hi s h => by
      obtain ⟨s', e, hm, hx, hg, hr, hw⟩ := lowStep (q (2 * i)) (q (2 * i + 1)) i s
        ⟨(q_ne _ (by omega)).1, (q_ne _ (by omega)).1⟩ h
      exact ⟨s', _, e, hm, fun j hj => by rw [qword_unpckl _ _ hj]; rfl, fun j hj _ => hx _ (q_ne j hj).1, hg, hr, hw⟩)
    (fun s s' h => by simp only [h]) s hin
  -- the low store keeps every slice
  have all : ∀ n ≤ 4, ∀ s : State, (∀ i < 4, InRegions s.wr (s.gpr .rax + BitVec.ofNat 64 (16 * i)) 16) →
      ∀ s', runBlock isa ((List.range n).flatMap fun i => [mv .xmm8 (q (2 * i)), unpckl .xmm8 (q (2 * i + 1)),
        .movdquStore (Impl.Aes.X86_64.at_ kp (16 * i)) .xmm8]) s = some s' →
        (∀ j < 8, s'.xmm (q j) = s.xmm (q j)) ∧ s'.gpr = s.gpr ∧ s'.wr = s.wr := by
    intro n
    induction n with
    | zero => intro _ s _ s' e; obtain rfl := Option.some.inj (e : some s = some s'); exact ⟨fun _ _ => rfl, rfl, rfl⟩
    | succ n ih =>
      intro hn s hin s' e
      rw [List.range_succ, List.flatMap_append, Interleave.runBlock_append] at e
      obtain ⟨s1, e1, e2⟩ := Option.bind_eq_some_iff.mp e
      obtain ⟨x1, g1, w1⟩ := ih (by omega) s hin s1 e1
      obtain ⟨s2, e3, -, hx, hg, -, hw⟩ := lowStep (q (2 * n)) (q (2 * n + 1)) n s1
        ⟨(q_ne _ (by omega)).1, (q_ne _ (by omega)).1⟩ (by rw [w1, g1]; exact hin n (by omega))
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, e3] at e2
      obtain rfl := Option.some.inj e2
      exact ⟨fun j hj => (hx _ (q_ne j hj).1).trans (x1 j hj), hg.trans g1, hw.trans w1⟩
  obtain ⟨s', e, h1, -, hg, hf, hr, hw⟩ := key 4 (Nat.le_refl _)
  exact ⟨s', e, h1, (all 4 (Nat.le_refl _) s hin s' e).1, hg, hf, hr, hw⟩

theorem storeHigh_ok (s : State) (hin : ∀ i < 4, InRegions s.wr (s.gpr .rax + BitVec.ofNat 64 (64 + 16 * i)) 16) :
    ∃ s', runBlock isa storeHigh s = some s' ∧
      (∀ j < 8, s'.mem.readW (s.gpr .rax + BitVec.ofNat 64 64 + BitVec.ofNat 64 (8 * j)) 64 = lane q s 1 j) ∧
      s'.gpr = s.gpr ∧ Frame [⟨s.gpr .rax + BitVec.ofNat 64 64, 64⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', e, h1, -, hg, hf, hr, hw⟩ := stores_ok (fun i => [unpckh (q (2 * i)) (q (2 * i + 1)),
      .movdquStore (Impl.Aes.X86_64.at_ kp (64 + 16 * i)) (q (2 * i))]) (fun s => s.gpr .rax + BitVec.ofNat 64 64) 1
    (fun i hi s h => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add] at h
      obtain ⟨s', e, hm, hx, hg, hr, hw⟩ := highStep (q (2 * i)) (q (2 * i + 1)) i s h
      refine ⟨s', _, e, by rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact hm, fun j hj => by
        rw [qword_unpckh _ _ hj]; rfl, fun j hj hne => hx _ fun h => ?_, hg, hr, hw⟩
      have := q_inj hj (by omega) h
      omega)
    (fun s s' h => by simp only [h]) s (fun i hi => by rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact hin i hi) 4
    (Nat.le_refl _)
  exact ⟨s', e, h1, hg, hf, hr, hw⟩

/-! ## A pair of keys -/

/-- Slices of a key in form 0 become slices in form 1. -/
theorem form1_holds {s : State} (he : Env0 s) {S : Nat → Spec.Aes.State} (hS : Holds false q s S) :
    ∃ s', runBlock isa form1 s = some s' ∧ Keep s s' ∧ Holds true q s' S := by
  obtain ⟨s', e, k, h⟩ := layer_ok form1_check (by decide +kernel) (by decide) he
  refine ⟨s', e, k, fun l hl j hj n hn k hk => ?_⟩
  rw [h l hl j hj _ (Nat.lt_of_lt_of_le (posAt_lt true hn hk) (by decide))]
  simp only [form1T, termsXor, List.foldr_cons, List.foldr_nil, Bool.xor_false, byteAt_posAt true hn hk,
    posAt_mod true n hk]
  exact hS l hl j hj n hn k hk

/-- The invariant of the key loop: `n` keys stored, the source at `r10`. -/
structure KS (s₀ : State) (b sch : Addr) (nr : Nat) (n : Nat) (cnt : BitVec 64) (s : State) : Prop where
  env : Env0 s
  r9 : s.gpr .r9 = b
  rax : s.gpr .rax = keyAddr b n
  r10 : s.gpr .r10 = sch + BitVec.ofNat 64 (16 * n)
  rdi : s.gpr .rdi = cnt
  gpr : ∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .rdi → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨b, 1480⟩] s₀.mem s.mem
  keys : ∀ i < n, KeyAt s.mem (keyAddr b i) (i % 2 == 1)
    (Spec.Aes.roundKey (Spec.Aes.bytesAt s₀.mem sch (16 * (nr + 1))) i)

/-- What the key setup needs. -/
structure KPre (b sch : Addr) (nr : Nat) (s : State) : Prop where
  r9 : s.gpr .r9 = b
  rdi : s.gpr .rdi = sch
  rsi : s.gpr .rsi = BitVec.ofNat 64 nr
  nrs : nr = 10 ∨ nr = 12 ∨ nr = 14
  sc : ⟨b, 2048⟩ ∈ s.wr ∨ ⟨b, 1480⟩ ∈ s.wr
  schIn : ⟨sch, 240⟩ ∈ s.rd
  disj : Region.Disjoint ⟨sch, 240⟩ ⟨b, 1480⟩

theorem KeyAt.frame {m m' : Mem} {a : Addr} {f : Bool} {rk : List Byte} (h : KeyAt m a f rk) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, 64⟩ r) : KeyAt m' a f rk :=
  h.congrW fun j hj => (hf.readW (r := ⟨a, 64⟩) (Offset.contains_base _ (by omega) (by omega)) hd (by decide)).symm

/-- The machine after a store of keys. -/
theorem Env0.store {s s' : State} (he : Env0 s) (hg : s'.gpr = s.gpr) (hw : s'.wr = s.wr) {R : Region}
    (hf : Frame [R] s.mem s'.mem) (hd : Region.Disjoint ⟨s.gpr .r9 + BitVec.ofNat 64 144, 144⟩ R) : Env0 s' where
  ok := he.ok.congr (by rw [hg]) hw
  masks m hm l hl := by
    have h1 := mask_ge m hm
    have h2 := mask_slots m hm
    rw [hg, hf.readW (r := ⟨s.gpr .r9 + BitVec.ofNat 64 144, 144⟩) (Offset.contains _ (by omega) (by omega) (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)]
    exact he.masks m hm l hl

theorem keyAddr_disj (b : Addr) {i n len : Nat} (h : i < n) (hn : 64 * n + len ≤ 1064) :
    Region.Disjoint ⟨keyAddr b i, 64⟩ ⟨keyAddr b n, len⟩ :=
  Offset.disjoint _ (.inl (by omega)) (by simp only [keysOff]; omega) (by simp only [keysOff]; omega)

theorem mask_disj (b : Addr) {n len : Nat} (hn : 64 * n + len ≤ 1064) :
    Region.Disjoint ⟨b + BitVec.ofNat 64 144, 144⟩ ⟨keyAddr b n, len⟩ :=
  Offset.disjoint _ (.inl (by simp only [keysOff]; omega)) (by decide) (by simp only [keysOff]; omega)

theorem sub_scratch (b : Addr) {d len : Nat} (h : d + len ≤ 1480) :
    Region.Sub ⟨b + BitVec.ofNat 64 d, len⟩ ⟨b, 1480⟩ := fun x hx => by
  simp only [Region.Contains] at hx ⊢
  rw [Offset.sub_add_eq, Offset.toNat_sub_ofNat] at hx
  have := (x - b).isLt
  omega

variable {s₀ : State} {b sch : Addr} {nr : Nat}

theorem KS.src {n : Nat} {cnt : BitVec 64} {s : State} (hp : KPre b sch nr s₀) (h : KS s₀ b sch nr n cnt s) {i : Nat}
    (hi : i ≤ nr) {d : Nat} (hd : d + 8 ≤ 16) :
    s.mem.readW (sch + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 d) 64 =
      s₀.mem.readW (sch + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 d) 64 := by
  have := hp.nrs
  refine h.frame.readW (r := ⟨sch, 240⟩) ?_ (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.disj) (by decide)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact Offset.contains_base _ (by omega) (by omega)

theorem KPre.inSch (hp : KPre b sch nr s₀) {s : State} (hr : s.rd = s₀.rd) {i : Nat} (hi : i ≤ nr) :
    InRegions (s.rd ++ s.wr) (sch + BitVec.ofNat 64 (16 * i)) 16 := by
  have := hp.nrs
  exact ⟨_, List.mem_append_left _ (by rw [hr]; exact hp.schIn), Offset.contains_base _ (by omega) (by omega)⟩

theorem KPre.inScr (hp : KPre b sch nr s₀) {s : State} (hw : s.wr = s₀.wr) {d n : Nat} (hd : d + n ≤ 1480) :
    InRegions s.wr (b + BitVec.ofNat 64 d) n := by
  rw [hw]
  rcases hp.sc with h | h
  · exact ⟨_, h, Offset.contains_base _ (by omega) (by omega)⟩
  · exact ⟨_, h, Offset.contains_base _ hd (by omega)⟩

/-- From the halves in the registers, the slices. -/
theorem spreadBs_ok (w : List Byte) (i : Nat → Nat) {s : State} (he : Env0 s)
    (hq : ∀ l < 2, ∀ n < 16, ∀ j < 8,
      (qword (s.xmm (q (4 * (n / 8)))) l).getLsbD (8 * (n % 8) + j) = ((rkState (Spec.Aes.roundKey w (i l))).getD n 0).getLsbD j) :
    ∃ s', runBlock isa (keySpread ++ toBs) s = some s' ∧ Keep s s' ∧
      Holds false q s' fun x => rkState (Spec.Aes.roundKey w (i (x / 4))) := by
  obtain ⟨s1, e1, h1, g1, m1, r1, w1⟩ := spread_ok s
  have k1 := keep_of he g1 m1 r1 w1
  obtain ⟨s2, e2, k2, h2⟩ := toBs_bits (S := fun x => rkState (Spec.Aes.roundKey w (i (x / 4)))) k1.env
    fun l hl k hk n hn j hj => by
      rw [lane, h1 k hk _ (by omega), hq l hl n hn j hj, show (4 * l + k) / 4 = l by omega]
  exact ⟨s2, by rw [Interleave.runBlock_append, e1, Option.bind_some, e2], k1.trans k2, h2⟩

/-- The slices of a lane, stored. -/
theorem keyAt_of {s : State} {f : Bool} {w : List Byte} {i : Nat → Nat} {l : Nat} (hl : l < 2)
    (h : Holds f q s fun x => rkState (Spec.Aes.roundKey w (i (x / 4)))) {m : Mem} {a : Addr}
    (hm : ∀ j < 8, m.readW (a + BitVec.ofNat 64 (8 * j)) 64 = lane q s l j) : KeyAt m a f (Spec.Aes.roundKey w (i l)) :=
  ((h l hl).congr fun k hk => by dsimp only; rw [show (4 * l + k) / 4 = l by omega]).congrW fun j hj => (hm j hj).symm

theorem low_sub (b : Addr) : ∀ r ∈ [(⟨b, 288⟩ : Region)], ∃ r' ∈ [(⟨b, 1480⟩ : Region)], Region.Sub r r' := fun r hr => by
  rw [List.mem_singleton.mp hr]
  exact ⟨_, List.mem_singleton.mpr rfl, fun x hx => by simp only [Region.Contains] at hx ⊢; omega⟩

theorem key_low_disj (b : Addr) {i : Nat} (hi : i ≤ 14) : ∀ r ∈ [(⟨b, 288⟩ : Region)], Region.Disjoint ⟨keyAddr b i, 64⟩ r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint_base _ (by simp only [keysOff]; omega) (by simp only [keysOff]; omega)

theorem keyBody_ok (hp : KPre b sch nr s₀) {n c : Nat} (hn : n + 2 ≤ nr) (h2 : n % 2 = 0) (hc : c < 2 ^ 32) {s : State}
    (h : KS s₀ b sch nr n (BitVec.ofNat 64 (c + 1)) s) :
    WP isa (.block keyBody) s fun s' => KS s₀ b sch nr (n + 2) (BitVec.ofNat 64 c) s' ∧
      X86_64.eval .ne s' = some (decide (c ≠ 0)) := by
  have hnr := hp.nrs
  obtain ⟨w, hw⟩ : ∃ w, w = Spec.Aes.bytesAt s₀.mem sch (16 * (nr + 1)) := ⟨_, rfl⟩
  refine WP.block_append (WP.block_append (WP.block_append (WP.block_append (WP.block_append ?_))))
  obtain ⟨s1, e1, q1, g1, m1, r1, w1⟩ := load2_ok s (by rw [h.r10]; exact hp.inSch h.rd (by omega))
    (by rw [h.r10, BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * n + 16 = 16 * (n + 1) by omega]
        exact hp.inSch h.rd (by omega))
  have k1 := keep_of h.env g1 m1 r1 w1
  obtain ⟨s2, e2, k2, h2s⟩ := spreadBs_ok w (fun l => n + l) k1.env fun l hl x hx j hj => by
    rw [q1 l hl _ (by omega), h.r10, BitVec.add_assoc sch, ← BitVec.ofNat_add, show 16 * n + 16 * l = 16 * (n + l) by omega,
      h.src hp (by omega) (by omega), hw]
    exact key_bit _ _ (by omega) hx hj
  have k2' := k1.trans k2
  have rax2 : s2.gpr .rax = keyAddr b n := by rw [k2'.gpr, h.rax]
  have r92 : s2.gpr .r9 = b := by rw [k2'.gpr, h.r9]
  have wr2 : s2.wr = s₀.wr := k2'.wr.trans h.wr
  obtain ⟨s3, e3, q3, x3, g3, f3, r3, w3⟩ := storeLow_ok s2 (fun i hi => by
    rw [rax2, keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hp.inScr wr2 (by simp only [keysOff]; omega))
  rw [rax2] at q3 f3
  have he3 := k2.env.store g3 w3 f3 (by rw [r92]; exact mask_disj b (by omega))
  have h3s : Holds false q s3 fun x => rkState (Spec.Aes.roundKey w (n + x / 4)) := fun l hl =>
    (h2s l hl).congrW fun j hj => by rw [lane, lane, x3 j hj]
  obtain ⟨s4, e4, k4, h4s⟩ := form1_holds he3 h3s
  have g4 : s4.gpr = s.gpr := k4.gpr.trans (g3.trans k2'.gpr)
  have f4 : Frame [⟨b, 288⟩] s3.mem s4.mem := by
    have := k4.frame
    rwa [slotRegion, show s3.gpr cfg.base = b from by rw [show cfg.base = Reg.r9 from rfl, g3, r92]] at this
  have wr4 : s4.wr = s₀.wr := k4.wr.trans (w3.trans wr2)
  obtain ⟨s5, e5, q5, g5, f5, r5, w5⟩ := storeHigh_ok s4 (fun i hi => by
    rw [g4, h.rax, keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hp.inScr wr4 (by simp only [keysOff]; omega))
  have e64 : keyAddr b n + BitVec.ofNat 64 64 = keyAddr b (n + 1) := by
    rw [keyAddr, keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add, show keysOff + 64 * (n + 1) = keysOff + 64 * n + 64 by omega]
  rw [g4, h.rax, e64] at q5 f5
  have he5 := k4.env.store g5 w5 f5 (by rw [g4, h.r9]; exact mask_disj b (by omega))
  have f2 : Frame [⟨b, 288⟩] s.mem s2.mem := by
    have := k2'.frame
    rwa [slotRegion, show s.gpr cfg.base = b from h.r9] at this
  have hfr : Frame [⟨b, 1480⟩] s.mem s5.mem := by
    refine ((f2.sub (low_sub b)).trans (f3.sub fun r hr => ?_)).trans ((f4.sub (low_sub b)).trans (f5.sub fun r hr => ?_))
    · rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_singleton.mpr rfl, sub_scratch b (by simp only [keysOff]; omega)⟩
    · rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_singleton.mpr rfl, sub_scratch b (by simp only [keysOff]; omega)⟩
  have keys : ∀ i < n + 2, KeyAt s5.mem (keyAddr b i) (i % 2 == 1) (Spec.Aes.roundKey w i) := by
    intro i hi
    by_cases hi1 : i = n + 1
    · subst hi1
      rw [show ((n + 1) % 2 == 1) = true by simp; omega]
      exact keyAt_of (i := fun l => n + l) (l := 1) (by decide) h4s q5
    have hd : KeyAt s4.mem (keyAddr b i) (i % 2 == 1) (Spec.Aes.roundKey w i) := by
      refine KeyAt.frame ?_ f4 (key_low_disj b (by omega))
      by_cases hi0 : i = n
      · subst hi0
        rw [show (i % 2 == 1) = false by simp; omega]
        exact keyAt_of (i := fun l => i + l) (l := 0) (by decide) h2s q3
      · refine KeyAt.frame (KeyAt.frame ?_ f2 (key_low_disj b (by omega))) f3 fun r hr => ?_
        · rw [hw]; exact h.keys i (by omega)
        · rw [List.mem_singleton.mp hr]; exact keyAddr_disj b (by omega) (by omega)
    exact hd.frame f5 fun r hr => by rw [List.mem_singleton.mp hr]; exact keyAddr_disj b (by omega) (by omega)
  refine WP.of_runBlock ⟨s1, e1, WP.of_runBlock ⟨s2, e2, WP.of_runBlock ⟨s3, e3, WP.of_runBlock ⟨s4, e4,
    WP.of_runBlock ⟨s5, e5, ?_⟩⟩⟩⟩⟩
  have g5' : s5.gpr = s.gpr := g5.trans g4
  have rd5 : s5.rd = s₀.rd := r5.trans (k4.rd.trans (r3.trans (k2'.rd.trans h.rd)))
  have wr5 : s5.wr = s₀.wr := w5.trans wr4
  have ecnt : s5.gpr .rdi - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 c := by
    rw [g5', h.rdi, show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 by decide, BitVec.ofNat_add,
      BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, Option.bind_some,
    show kp = Reg.rax from rfl, gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ecnt, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨he5.ok.congr (by simp [gpr_setReg, gpr_arithFlags, cfg]) rfl, ?_⟩, ?_, ?_, ?_, ?_, fun x a c d => ?_, rd5, wr5,
    h.frame.trans hfr, fun i hi => ?_⟩, ?_⟩
  · intro m hm l hl
    simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, mem_setReg, mem_arithFlags]
    exact he5.masks m hm l hl
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, g5', h.r9]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, g5', h.rax]
    rw [keyAddr, keyAddr, BitVec.add_assoc, show BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 128 by decide,
      ← BitVec.ofNat_add, show keysOff + 64 * (n + 2) = keysOff + 64 * n + 128 by omega]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, g5', h.r10]
    rw [BitVec.add_assoc, show BitVec.signExtend 64 (32 : BitVec 32) = BitVec.ofNat 64 32 by decide, ← BitVec.ofNat_add]
    rfl
  · simp only [gpr_setReg, gpr_arithFlags, ite_true]
  · simp only [gpr_setReg, gpr_arithFlags, a, c, d, ite_false, g5']; exact h.gpr x a c d
  · rw [← hw]; exact keys i hi
  · simp only [X86_64.eval, zf_setReg, zf_arithFlags, Option.map_some, Option.some.injEq]
    rw [beq_zero (by omega)]
    simp

/-- The last key. -/
theorem lastKey_ok (hp : KPre b sch nr s₀) {s : State} (h : KS s₀ b sch nr nr 0 s) :
    WP isa (.block (keyLoad1 ++ (keySpread ++ toBs) ++ storeLow)) s fun s' => Env0 s' ∧
      (∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .rdi → s'.gpr x = s₀.gpr x) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      Frame [⟨b, 1480⟩] s₀.mem s'.mem ∧
      ∀ i ≤ nr, KeyAt s'.mem (keyAddr b i) (i % 2 == 1)
        (Spec.Aes.roundKey (Spec.Aes.bytesAt s₀.mem sch (16 * (nr + 1))) i) := by
  have hnr := hp.nrs
  obtain ⟨w, hw⟩ : ∃ w, w = Spec.Aes.bytesAt s₀.mem sch (16 * (nr + 1)) := ⟨_, rfl⟩
  obtain ⟨s1, e1, q1, g1, m1, r1, w1⟩ := load1_ok s (by rw [h.r10]; exact hp.inSch h.rd (Nat.le_refl _))
  have k1 := keep_of h.env g1 m1 r1 w1
  obtain ⟨s2, e2, k2, h2s⟩ := spreadBs_ok w (fun _ => nr) k1.env fun l hl x hx j hj => by
    rw [q1 l hl _ (by omega), h.r10, h.src hp (Nat.le_refl _) (by omega), hw]
    exact key_bit _ _ (Nat.le_refl _) hx hj
  have k2' := k1.trans k2
  have rax2 : s2.gpr .rax = keyAddr b nr := by rw [k2'.gpr, h.rax]
  have r92 : s2.gpr .r9 = b := by rw [k2'.gpr, h.r9]
  have wr2 : s2.wr = s₀.wr := k2'.wr.trans h.wr
  obtain ⟨s3, e3, q3, x3, g3, f3, r3, w3⟩ := storeLow_ok s2 (fun i hi => by
    rw [rax2, keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hp.inScr wr2 (by simp only [keysOff]; omega))
  rw [rax2] at q3 f3
  have he3 := k2.env.store g3 w3 f3 (by rw [r92]; exact mask_disj b (by omega))
  have f2 : Frame [⟨b, 288⟩] s.mem s2.mem := by
    have := k2'.frame
    rwa [slotRegion, show s.gpr cfg.base = b from h.r9] at this
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s1, e1, WP.of_runBlock ⟨s2, e2, WP.of_runBlock ⟨s3, e3, he3,
    fun x a c d => by rw [g3, k2'.gpr, h.gpr x a c d], r3.trans (k2'.rd.trans h.rd), w3.trans wr2,
    h.frame.trans ((f2.sub (low_sub b)).trans (f3.sub fun r hr => ?_)), fun i hi => ?_⟩⟩⟩))
  · rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton.mpr rfl, sub_scratch b (by simp only [keysOff]; omega)⟩
  · rw [← hw]
    by_cases hi0 : i = nr
    · subst hi0
      rw [show (i % 2 == 1) = false by simp; omega]
      exact keyAt_of (i := fun _ => i) (l := 0) (by decide) h2s q3
    · refine KeyAt.frame (KeyAt.frame ?_ f2 (key_low_disj b (by omega))) f3 fun r hr => ?_
      · rw [hw]; exact h.keys i (by omega)
      · rw [List.mem_singleton.mp hr]; exact keyAddr_disj b (by omega) (by omega)

/-! ## The constant -/

theorem flip_ok (j : Nat) (s : State)
    (hin : InRegions s.wr (s.gpr .rax + BitVec.ofNat 64 (8 * j)) 8) :
    ∃ s', runBlock isa (flip j) s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .rax + BitVec.ofNat 64 (8 * j))
        (~~~ s.mem.readW (s.gpr .rax + BitVec.ofNat 64 (8 * j)) 64) ∧
      (∀ x, x ≠ .r10 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin' : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofNat 64 (8 * j)) 8 := by
    obtain ⟨R, hR, hc⟩ := hin
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  have e : BitVec.signExtend 64 (0xFFFFFFFF : BitVec 32) = BitVec.allOnes 64 := by decide
  simp only [Impl.Aes.X86_64.Sse.flip, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, State.load64,
    State.store64, ea_at, show kp = Reg.rax from rfl, hin', ite_true, Option.map_some, Option.bind_some, e, gpr_setReg,
    gpr_arithFlags, reduceCtorEq, ite_false, hin, wr_setReg, wr_arithFlags, mem_setReg, mem_arithFlags, Option.some.injEq,
    exists_eq_left', BitVec.xor_allOnes]
  refine ⟨trivial, fun x c => ?_, by first | rfl | trivial, by first | rfl | trivial⟩
  simp only [c, ite_false]

theorem flips_ok (l : List Nat) (hn : l.Nodup) (hl : ∀ j ∈ l, j < 8) (s : State) (a : Addr) (ha : s.gpr .rax = a)
    (hin : ∀ j < 8, InRegions s.wr (a + BitVec.ofNat 64 (8 * j)) 8) :
    ∃ s', runBlock isa (l.flatMap Impl.Aes.X86_64.Sse.flip) s = some s' ∧
      (∀ j < 8, s'.mem.readW (a + BitVec.ofNat 64 (8 * j)) 64 =
        if j ∈ l then ~~~ s.mem.readW (a + BitVec.ofNat 64 (8 * j)) 64 else s.mem.readW (a + BitVec.ofNat 64 (8 * j)) 64) ∧
      (∀ x, x ≠ .r10 → s'.gpr x = s.gpr x) ∧ Frame [⟨a, 64⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  induction l generalizing s with
  | nil => exact ⟨s, rfl, fun _ _ => by simp, fun _ _ => rfl, Frame.refl _ _, rfl, rfl⟩
  | cons m l ih =>
    obtain ⟨hm, hn'⟩ := List.nodup_cons.mp hn
    have hm8 := hl m List.mem_cons_self
    obtain ⟨s1, e1, m1, g1, r1, w1⟩ := flip_ok m s (by rw [ha]; exact hin m hm8)
    obtain ⟨s2, e2, q2, g2, f2, r2, w2⟩ := ih hn' (fun j hj => hl j (List.mem_cons_of_mem _ hj)) s1
      ((g1 _ (by decide)).trans ha) (by rw [w1]; exact hin)
    rw [ha] at m1
    refine ⟨s2, by rw [List.flatMap_cons, Interleave.runBlock_append, e1, Option.bind_some, e2], fun j hj => ?_,
      fun x c => (g2 x c).trans (g1 x c), ?_, r2.trans r1, w2.trans w1⟩
    · rw [q2 j hj, m1]
      by_cases hjm : j = m
      · subst hjm
        simp only [hm, ite_false, List.mem_cons_self, ite_true]
        exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        simp only [List.mem_cons, hjm, false_or]
    · rw [m1] at f2
      exact ((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))).trans f2

theorem complement_eq : complement = [0, 1, 5, 6].flatMap Impl.Aes.X86_64.Sse.flip ++
    [.alu .add kp (.imm 64), .alu .sub .rdi (.imm 1)] := by decide

/-- A key with the slices flipped is the key with `{63}` added. -/
theorem keyAt_flip {m m' : Mem} {a : Addr} {f : Bool} {rk : List Byte} (hr : rk.length = 16) (h : KeyAt m a f rk)
    (hm : ∀ j < 8, m'.readW (a + BitVec.ofNat 64 (8 * j)) 64 =
      if j ∈ [0, 1, 5, 6] then ~~~ m.readW (a + BitVec.ofNat 64 (8 * j)) 64 else m.readW (a + BitVec.ofNat 64 (8 * j)) 64) :
    KeyAt m' a f (rk63 rk) := fun j hj n hn k hk => by
  have hb := h j hj n hn k hk
  have hp : posAt 4 f n k < 64 := Nat.lt_of_lt_of_le (posAt_lt f hn hk) (by decide)
  dsimp only at hb ⊢
  rw [getD_rkState _ hn] at hb ⊢
  rw [hm j hj, getD_rk63 _ (by omega), BitVec.getLsbD_xor, ← hb]
  have : ∀ j < 8, (j ∈ [0, 1, 5, 6]) = ((0x63 : Byte).getLsbD j = true) := by decide
  simp only [this j hj]
  split
  · rename_i h1; rw [h1]; simp [hp]
  · rename_i h1; simp only [Bool.not_eq_true] at h1; rw [h1]; simp

/-- The invariant of the complementing loop: keys `1 … m` done. -/
structure CS (s₀ : State) (b sch : Addr) (nr : Nat) (m : Nat) (s : State) : Prop where
  env : Env0 s
  rax : s.gpr .rax = keyAddr b (m + 1)
  rdi : s.gpr .rdi = BitVec.ofNat 64 (nr - m)
  gpr : ∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .rdi → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨b, 1480⟩] s₀.mem s.mem
  keys : ∀ i ≤ nr, KeyAt s.mem (keyAddr b i) (i % 2 == 1)
    (if i ≤ m then kr (Spec.Aes.bytesAt s₀.mem sch (16 * (nr + 1))) i
      else Spec.Aes.roundKey (Spec.Aes.bytesAt s₀.mem sch (16 * (nr + 1))) i)

theorem complement_ok (hp : KPre b sch nr s₀) {m : Nat} (hm : m < nr) {s : State} (h : CS s₀ b sch nr m s) :
    WP isa (.block complement) s fun s' => CS s₀ b sch nr (m + 1) s' ∧
      X86_64.eval .ne s' = some (decide (nr - (m + 1) ≠ 0)) := by
  have hnr := hp.nrs
  have h9 : s.gpr .r9 = b := by rw [h.gpr _ (by decide) (by decide) (by decide), hp.r9]
  rw [complement_eq]
  obtain ⟨s1, e1, q1, g1, f1, r1, w1⟩ := flips_ok [0, 1, 5, 6] (by decide) (by decide) s _ h.rax fun j hj => by
    rw [keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hp.inScr h.wr (by simp only [keysOff]; omega)
  refine WP.block_append (WP.of_runBlock ⟨s1, e1, ?_⟩)
  have h91 : s1.gpr .r9 = b := (g1 _ (by decide)).trans h9
  have hmask : ∀ k ∈ maskVals, ∀ l < 2, qword (s1.mem.readW (xAddr b k.1) 128) l = k.2 := fun k hk l hl => by
    have a1 := mask_ge k hk
    have a2 := mask_slots k hk
    rw [f1.readW (r := ⟨b + BitVec.ofNat 64 144, 144⟩) (Offset.contains _ (by omega) (by omega) (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact mask_disj b (by omega)) (by decide)]
    have := h.env.masks k hk l hl
    rwa [h9] at this
  have ecnt : s1.gpr .rdi - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (nr - (m + 1)) := by
    rw [g1 _ (by decide), h.rdi, show nr - m = nr - (m + 1) + 1 by omega,
      show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 by decide, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, Option.bind_some,
    show kp = Reg.rax from rfl, gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ecnt, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨⟨fun k hk => ?_, by decide⟩, fun k hk l hl => ?_⟩, ?_, ?_, fun x a c d => ?_, r1.trans h.rd, w1.trans h.wr,
    h.frame.trans (f1.sub fun r hr => ?_), fun i hi => ?_⟩, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, cfg, h91, wr_setReg, wr_arithFlags]
    exact hp.inScr (w1.trans h.wr) (by simp only [cfg] at hk; omega)
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, mem_setReg, mem_arithFlags, h91]
    exact hmask k hk l hl
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, g1 _ (show Reg.rax ≠ .r10 by decide), h.rax]
    rw [keyAddr, keyAddr, BitVec.add_assoc, show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 64 by decide,
      ← BitVec.ofNat_add, show keysOff + 64 * (m + 1 + 1) = keysOff + 64 * (m + 1) + 64 by omega]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true]
  · simp only [gpr_setReg, gpr_arithFlags, a, d, ite_false, g1 x c]; exact h.gpr x a c d
  · rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton.mpr rfl, sub_scratch b (by simp only [keysOff]; omega)⟩
  · simp only [mem_setReg, mem_arithFlags]
    by_cases hi1 : i = m + 1
    · subst hi1
      simp only [Nat.le_refl, ite_true, kr, Nat.succ_ne_zero, ite_false]
      have := h.keys (m + 1) hi
      rw [ite_eq_right (by omega)] at this
      exact keyAt_flip (rk_length _ _ hi) this q1
    · have := h.keys i hi
      simp only [show (i ≤ m + 1) = (i ≤ m) by apply propext; omega]
      exact this.frame f1 fun r hr => by
        rw [List.mem_singleton.mp hr]
        rcases Nat.lt_or_gt_of_ne hi1 with hlt | hgt
        · exact keyAddr_disj b hlt (by omega)
        · exact (keyAddr_disj b hgt (by omega)).symm
  · simp only [X86_64.eval, zf_setReg, zf_arithFlags, Option.map_some, Option.some.injEq]
    rw [beq_zero (by omega)]
    simp

theorem shr1 : ∀ n, n = 10 ∨ n = 12 ∨ n = 14 → (BitVec.ofNat 64 n >>> (1 : Nat) : BitVec 64) = BitVec.ofNat 64 (n / 2) := by
  rintro n (rfl | rfl | rfl) <;> decide

/-- What the key setup leaves. -/
structure KPost (b sch : Addr) (nr : Nat) (s s' : State) : Prop where
  ready : Ready b nr (Spec.Aes.bytesAt s.mem sch (16 * (nr + 1))) s'.mem s'.rd s'.wr
  gpr : ∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .rdi → s'.gpr x = s.gpr x
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨b, 1480⟩] s.mem s'.mem

theorem keys_ok (hp : KPre b sch nr s₀) : WP isa keys s₀ (KPost b sch nr s₀) := by
  have hnr := hp.nrs
  -- the masks and the pointers
  obtain ⟨s1, e1, a1, -, f1, g1, r1, w1⟩ := masks_list maskVals (by decide) mask_slots s₀ fun k hk => by
    rw [hp.r9, xAddr]; exact hp.inScr rfl (by omega)
  rw [hp.r9] at a1 f1
  have g9 : s1.gpr .r9 = b := (g1 _ (by decide)).trans hp.r9
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s1, by rw [setMasks_eq]; exact e1, ?_⟩))
  refine WP.mono (Q := KS s₀ b sch nr 0 (BitVec.ofNat 64 (nr / 2))) ?_ fun s2 h2 => ?_
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, execShift, readSrc, Option.bind_some,
      Option.map_some, show kp = Reg.rax from rfl, gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false,
      Nat.le_refl, Nat.reduceLeDiff, and_self, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨fun k hk => ?_, by decide⟩, ?_⟩, ?_, ?_, ?_, ?_, fun x a c d => ?_, r1, w1, f1.sub (low_sub b), fun i hi =>
      absurd hi (Nat.not_lt_zero _)⟩
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false, cfg, g9]
      exact hp.inScr w1 (by simp only [cfg] at hk; omega)
    · intro k hk l hl
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false, g9]
      exact a1 k hk l hl
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false, g9]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false, ite_true, g9]
      exact (keyAddr_zero b).symm
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false, ite_true, g1 _ (show Reg.rdi ≠ .rax by decide),
        hp.rdi]
      simp
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, g1 _ (show Reg.rsi ≠ .rax by decide), hp.rsi]
      exact shr1 nr hnr
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, a, c, d, ite_false, g1 x a]
  -- the pairs
  refine WP.seq (WP.mono (Q := KS s₀ b sch nr nr 0) ?_ fun s3 h3 => ?_)
  · let I : Nat → State → Prop := fun c s => ∃ m, c = nr / 2 - m ∧ m < nr / 2 ∧
      KS s₀ b sch nr (2 * m) (BitVec.ofNat 64 (nr / 2 - m)) s
    refine WP.loop (M := isa) I ?_ (nr / 2) s2 ⟨0, rfl, by omega, h2⟩
    rintro c s' ⟨m, rfl, hm, hs'⟩
    rw [show nr / 2 - m = nr / 2 - (m + 1) + 1 by omega] at hs'
    refine WP.mono (keyBody_ok hp (by omega) (by omega) (by omega) hs') fun s4 ⟨h4, hz⟩ => ?_
    by_cases hl : nr / 2 - (m + 1) = 0
    · refine .inl ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], ?_⟩
      rw [hl, show 2 * m + 2 = nr by omega] at h4
      exact h4
    · exact .inr ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], _, by omega, m + 1, rfl, by omega, h4⟩
  -- the last key
  refine WP.seq (WP.block_append (WP.mono (lastKey_ok hp h3) fun s4 ⟨he4, g4, rd4, wr4, fr4, k4⟩ => ?_))
  have g49 : s4.gpr .r9 = b := (g4 _ (by decide) (by decide) (by decide)).trans hp.r9
  have e64 : BitVec.signExtend 64 (BitVec.ofNat 32 (keysOff + 64)) = BitVec.ofNat 64 (keysOff + 64 * (0 + 1)) := by decide
  refine WP.mono (Q := CS s₀ b sch nr 0) ?_ fun s5 h5 => ?_
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, Option.bind_some,
      Option.map_some, show kp = Reg.rax from rfl, gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false,
      ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨fun k hk => ?_, by decide⟩, ?_⟩, ?_, ?_, fun x a c d => ?_, rd4, wr4, fr4, fun i hi => ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, cfg, g49]
      exact hp.inScr wr4 (by simp only [cfg] at hk; omega)
    · intro k hk l hl
      simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, g49]
      have := he4.masks k hk l hl
      rwa [g49] at this
    · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, g49]
      rw [e64]; rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, g4 _ (show Reg.rsi ≠ .rax by decide) (by decide) (by decide), hp.rsi]
      rfl
    · simp only [gpr_setReg, gpr_arithFlags, a, d, ite_false, g4 x a c d]
    · have := k4 i hi
      by_cases h0 : i = 0
      · subst h0; simpa [kr, mem_setReg, mem_arithFlags] using this
      · simpa [h0, mem_setReg, mem_arithFlags] using this
  -- the constant
  let I : Nat → State → Prop := fun c s => ∃ m, c = nr - m ∧ m < nr ∧ CS s₀ b sch nr m s
  refine WP.loop (M := isa) I ?_ nr s5 ⟨0, rfl, by omega, h5⟩
  rintro c s' ⟨m, rfl, hm, hs'⟩
  refine WP.mono (complement_ok hp hm hs') fun s6 ⟨h6, hz⟩ => ?_
  by_cases hl : nr - (m + 1) = 0
  · refine .inl ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], ?_⟩
    have g9' : s6.gpr .r9 = b := (h6.gpr _ (by decide) (by decide) (by decide)).trans hp.r9
    refine ⟨⟨by rw [h6.wr]; exact hp.sc, fun i hi => ?_, ?_, hnr, fun i hi => rk_length _ _ hi⟩, h6.gpr, h6.rd, h6.wr, h6.frame⟩
    · have := h6.keys i hi
      rwa [ite_eq_left (by omega)] at this
    · have := h6.env.masks
      rwa [g9'] at this
  · exact .inr ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], _, by omega, m + 1, rfl, by omega, h6⟩

end VG.Proof.Aes.X86_64.Sse
