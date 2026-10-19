module

public import VerifiedGarbage.Proof.Cast5.Arm.Run
public import VerifiedGarbage.Proof.Cast5.Table
public import VerifiedGarbage.Impl.Cast5.Arm
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# CAST5 on ARMv7: the scan of a table

`scan sym o` visits the 256 entries of the static `sym`, in order, and leaves
in `r8 + k` word `k` of the entry whose number is in `r4 + k` (`scan_ok`);
`r2` and `r3`, which hold the entry's number and address meanwhile, are
saved at `o` and `o + 4` in the working space at `r12` and restored.
-/

@[expose] public section

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Cast5.Arm

/-- Word `k` of entry `e` of the table at the 32-bit address `T`. -/
def tw (m : Mem) (T : BitVec 32) (e k : Nat) : BitVec 32 :=
  m.readW (State.addr (T + BitVec.ofNat 32 (16 * e + 4 * k))) 32

/-- Word `k` of entry `e` of a table held at `T`, which does not wrap. -/
theorem tw_table {m : Mem} {T : BitVec 32} {a b c d : Byte → Spec.Cast5.Word} (hT : T.toNat + 4096 ≤ 2 ^ 32)
    (h : Held m (State.addr T) (Impl.Cast5.table a b c d)) {e k : Nat} (he : e < 256) (hk : k < 4) :
    tw m T e k = tableEnt a b c d e k := by
  rw [← ent_table h he hk, tw, ent, addr_add (by omega)]

/-- Memory holding a table, later: its words are kept by writes apart from it. -/
theorem held_frame {rs : List Region} {m m' : Mem} {T : Addr} {W : List (BitVec 64)} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨T, 8 * W.length⟩ r) (hl : 8 * W.length < 2 ^ 64) (h : Held m T W) :
    Held m' T W := fun i hi => by
  rw [hf.readW (Offset.contains_base _ (by omega) (by omega)) hd (by decide)]
  exact h i hi

theorem idxReg_ne_r0 (k : Nat) : idxReg k ≠ .r0 := by
  unfold idxReg; split <;> decide
theorem idxReg_ne_r1 (k : Nat) : idxReg k ≠ .r1 := by
  unfold idxReg; split <;> decide
theorem idxReg_ne_r2 (k : Nat) : idxReg k ≠ .r2 := by
  unfold idxReg; split <;> decide
theorem idxReg_ne_r3 (k : Nat) : idxReg k ≠ .r3 := by
  unfold idxReg; split <;> decide
theorem accReg_ne_r0 (k : Nat) : accReg k ≠ .r0 := by
  unfold accReg; split <;> decide
theorem accReg_ne_r1 (k : Nat) : accReg k ≠ .r1 := by
  unfold accReg; split <;> decide
theorem accReg_ne_r2 (k : Nat) : accReg k ≠ .r2 := by
  unfold accReg; split <;> decide
theorem accReg_ne_r3 (k : Nat) : accReg k ≠ .r3 := by
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

/-- One lookup at entry `j` (in `r2`), the entry's words at `r3`. -/
theorem look_ok (s : State) (k : Nat) (hk : k < 4) {j : Nat} (hj : j < 256) (h2 : s.gpr .r2 = BitVec.ofNat 32 j)
    (hx : (s.gpr (idxReg k)).toNat < 256)
    (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r3 + BitVec.ofNat 32 (4 * k))) 4) :
    WP isa (.block (look k)) s fun t =>
      t.gpr (accReg k) = (s.gpr (accReg k) ||| (if s.gpr (idxReg k) = BitVec.ofNat 32 j then
        s.mem.readW (State.addr (s.gpr .r3 + BitVec.ofNat 32 (4 * k))) 32 else 0)) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ accReg k → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have ho : 4 * k < 4096 := by omega
  unfold look
  crun [ho, hin, h2, idxReg_ne_r0, idxReg_ne_r1, accReg_ne_r0, accReg_ne_r1]
  refine ⟨?_, fun r h0 h1 hk => by simp only [h0, h1, hk, ite_false]⟩
  rw [mask_eq hx hj]
  split
  · rw [BitVec.and_allOnes]
  · rw [show ∀ v : BitVec 32, v &&& 0 = 0 from fun v => BitVec.eq_of_getLsbD_eq (by simp)]

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

/-- The registers the loop of a scan writes. -/
def loopRegs : List Reg := [.r0, .r1, .r2, .r3, .r8, .r9, .r10, .r11]

/-- The state of the scan of the table at `T` in the memory `m` with entries
`0 … j - 1` visited, from `s₀`. -/
structure ScanAt (s₀ : State) (m : Mem) (T : BitVec 32) (idx : Nat → BitVec 32) (j : Nat) (s : State) : Prop where
  hidx : ∀ k < 4, s.gpr (idxReg k) = idx k
  hacc : ∀ k < 4, s.gpr (accReg k) = acc (tw m T) idx j k
  r2 : s.gpr .r2 = BitVec.ofNat 32 j
  r3 : s.gpr .r3 = T + BitVec.ofNat 32 (16 * j)
  keep : Keep loopRegs s₀ s
  mem : s.mem = m

theorem accReg_mem (k : Nat) : accReg k ∈ loopRegs := by
  unfold accReg; split <;> decide

theorem entry_ok {s₀ s : State} {m : Mem} {T : BitVec 32} {idx : Nat → BitVec 32} {j : Nat}
    (hj : j < 256) (hidx : ∀ k < 4, (idx k).toNat < 256) (hT : T.toNat + 4096 ≤ 2 ^ 32)
    (hrT : (⟨State.addr T, 4096⟩ : Region) ∈ s₀.rd ++ s₀.wr) (h : ScanAt s₀ m T idx j s) :
    WP isa (.block scanEntry) s fun t =>
      (∀ k < 4, t.gpr (idxReg k) = idx k) ∧ (∀ k < 4, t.gpr (accReg k) = acc (tw m T) idx (j + 1) k) ∧
      t.gpr .r2 = BitVec.ofNat 32 j ∧ t.gpr .r3 = T + BitVec.ofNat 32 (16 * j) ∧ Keep loopRegs s₀ t ∧
      t.mem = m := by
  -- Lookups `0 … e - 1` done.
  have step : ∀ e ≤ 4, WP isa (.block ((List.range e).flatMap look)) s
      fun t => (∀ k < 4, t.gpr (idxReg k) = idx k) ∧
        (∀ k < 4, t.gpr (accReg k) = if k < e then acc (tw m T) idx (j + 1) k else acc (tw m T) idx j k) ∧
        t.gpr .r2 = BitVec.ofNat 32 j ∧ t.gpr .r3 = T + BitVec.ofNat 32 (16 * j) ∧ Keep loopRegs s₀ t ∧
        t.mem = m := by
    intro e he
    induction e with
    | zero => exact WP.block_nil ⟨h.hidx, fun k hk => by rw [ite_eq_right (by omega)]; exact h.hacc k hk,
        h.r2, h.r3, h.keep, h.mem⟩
    | succ e ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        WP.block_append_iff]
      refine WP.mono (ih (by omega)) fun t ⟨ti, ta, t2, t3, tk, tm⟩ => ?_
      have ea : State.addr (t.gpr .r3 + BitVec.ofNat 32 (4 * e)) = State.addr T + BitVec.ofNat 64 (16 * j + 4 * e) := by
        rw [t3, BitVec.add_assoc, ← BitVec.ofNat_add, addr_add (by omega)]
      have hin : InRegions (t.rd ++ t.wr) (State.addr (t.gpr .r3 + BitVec.ofNat 32 (4 * e))) 4 := by
        rw [tk.rd, tk.wr, ea]; exact ⟨_, hrT, Offset.contains_base _ (by omega) (by omega)⟩
      refine WP.mono (look_ok t e (by omega) hj t2 (by rw [ti e (by omega)]; exact hidx e (by omega)) hin)
        fun u ⟨ua, uo, um, urd, uwr, usp⟩ => ?_
      refine ⟨fun k hk => by rw [uo _ (idxReg_ne_r0 k) (idxReg_ne_r1 k) (accReg_ne_idxReg e k).symm,
          ti k hk], fun k hk => ?_, by rw [uo _ (by decide) (by decide) (accReg_ne_r2 e).symm, t2],
        by rw [uo _ (by decide) (by decide) (accReg_ne_r3 e).symm, t3],
        tk.trans ⟨fun r hr => ?_, urd, uwr, usp⟩, um.trans tm⟩
      · by_cases hke : k = e
        · subst hke
          have ev : t.mem.readW (State.addr (t.gpr .r3 + BitVec.ofNat 32 (4 * k))) 32 = tw m T j k := by
            rw [tm, t3, BitVec.add_assoc, ← BitVec.ofNat_add]; rfl
          rw [ite_eq_left (by omega), ua, ta k hk, ite_eq_right (by omega), ti k hk, ev, acc_succ _ idx hj]
        · have hne : accReg k ≠ accReg e := fun h' => hke (accReg_inj hk (by omega) h')
          rw [uo _ (accReg_ne_r0 k) (accReg_ne_r1 k) hne, ta k hk]
          by_cases hk' : k < e
          · rw [ite_eq_left hk', ite_eq_left (by omega)]
          · rw [ite_eq_right hk', ite_eq_right (by omega)]
      · exact uo r (fun e' => hr (by rw [e']; decide)) (fun e' => hr (by rw [e']; decide))
          fun e' => hr (by rw [e']; exact accReg_mem e)
  refine WP.mono (step 4 (Nat.le_refl _)) fun t ⟨ti, ta, t2, t3, tk, tm⟩ => ⟨ti, fun k hk => ?_, t2, t3, tk, tm⟩
  rw [ta k hk, ite_eq_left hk]

/-- An iteration of the loop: an entry, then on to the next. -/
theorem body_ok {s₀ s : State} {m : Mem} {T : BitVec 32} {idx : Nat → BitVec 32} {j : Nat}
    (hj : j < 256) (hidx : ∀ k < 4, (idx k).toNat < 256) (hT : T.toNat + 4096 ≤ 2 ^ 32)
    (hrT : (⟨State.addr T, 4096⟩ : Region) ∈ s₀.rd ++ s₀.wr) (h : ScanAt s₀ m T idx j s) :
    WP isa (.block scanBody) s fun t => ScanAt s₀ m T idx (j + 1) t ∧ t.z = decide (j = 255) := by
  unfold scanBody
  rw [WP.block_append_iff]
  refine WP.mono (entry_ok hj hidx hT hrT h) fun t ⟨ti, ta, t2, t3, tk, tm⟩ => ?_
  crun [t2, t3]
  refine ⟨⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_, tk.trans ⟨fun r hr => ?_, rfl, rfl, rfl⟩, tm⟩, ?_⟩
  · rw [← ti k hk]
    simp only [gpr_setReg, idxReg_ne_r2, idxReg_ne_r3, gpr_sub, ite_false]
  · rw [← ta k hk]
    simp only [gpr_setReg, accReg_ne_r2, accReg_ne_r3, gpr_sub, ite_false]
  · simp only [gpr_setReg, ite_true]; rw [BitVec.ofNat_add]; rfl
  · simp only [gpr_setReg, gpr_sub, reduceCtorEq, ite_true, ite_false]
    rw [BitVec.add_assoc, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, ← BitVec.ofNat_add,
      show 16 * j + 16 = 16 * (j + 1) by omega]
  · simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨_, _, h2, h3, _⟩ := hr
    simp only [gpr_setReg, h2, h3, gpr_sub, ite_false]
  · by_cases he : j = 255
    · subst he; rfl
    · rw [decide_eq_false he]
      have : BitVec.ofNat 32 j - 255 ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
        simp at this; omega
      simpa using this

/-- What a scan needs: the indices below 256; its two slots at `o` in the
working space at `r12`, writable and within the address space; and the
table, 4096 bytes at the static's address, readable, within the address
space and apart from the slots. -/
structure ScanPre (sym : String) (o : Nat) (s : State) : Prop where
  idx : ∀ k < 4, (s.gpr (idxReg k)).toNat < 256
  cfit : (s.gpr .r12).toNat + o + 8 ≤ 2 ^ 32
  ofit : o + 8 ≤ 4096
  s0 : InRegions s.wr (State.addr (s.gpr .r12) + BitVec.ofNat 64 o) 4
  s4 : InRegions s.wr (State.addr (s.gpr .r12) + BitVec.ofNat 64 (o + 4)) 4
  tfit : (s.syms sym).toNat + 4096 ≤ 2 ^ 32
  trd : (⟨State.addr (s.syms sym), 4096⟩ : Region) ∈ s.rd ++ s.wr
  dTS : Region.Disjoint ⟨State.addr (s.syms sym), 4096⟩ ⟨State.addr (s.gpr .r12) + BitVec.ofNat 64 o, 8⟩

/-- The memory after a scan: `r2` and `r3` in its slots. -/
def scanMem (s : State) (o : Nat) : Mem :=
  (s.mem.writeW (State.addr (s.gpr .r12) + BitVec.ofNat 64 o) (s.gpr .r2)).writeW
    (State.addr (s.gpr .r12) + BitVec.ofNat 64 (o + 4)) (s.gpr .r3)

theorem syms_mem (s : State) (m : Mem) : (putMem s m).syms = s.syms := rfl

/-- The table's words, read past the slots. -/
theorem tw_scanMem {s : State} {sym : String} {o : Nat} (h : ScanPre sym o s) {e k : Nat} (he : e < 256)
    (hk : k < 4) : tw (scanMem s o) (s.syms sym) e k = tw s.mem (s.syms sym) e k := by
  have hT := h.tfit
  have hof := h.ofit
  have ea : State.addr (s.syms sym + BitVec.ofNat 32 (16 * e + 4 * k)) =
      State.addr (s.syms sym) + BitVec.ofNat 64 (16 * e + 4 * k) := addr_add (by omega)
  have cT : (⟨State.addr (s.syms sym), 4096⟩ : Region).Contains (State.addr (s.syms sym + BitVec.ofNat 32
      (16 * e + 4 * k))) (32 / 8) := by
    rw [ea]; exact Offset.contains_base _ (by omega) (by omega)
  unfold tw scanMem
  rw [Mem.readW_writeW_sep (h.dTS.sep cT (Offset.contains (State.addr (s.gpr .r12)) (d := o + 4) (n := 32 / 8)
      (e := o) (k := 8) (by omega) (by omega) (by omega))) (by decide),
    Mem.readW_writeW_sep (h.dTS.sep cT (Offset.contains (State.addr (s.gpr .r12)) (d := o) (n := 32 / 8)
      (e := o) (k := 8) (by omega) (by omega) (by omega))) (by decide)]

/-- The scan: `r8 + k` is word `k` of the entry of the table whose number
is in `r4 + k`; only `r0`, `r1`, `r8`–`r11` and the two slots are written. -/
theorem scan_ok (s : State) (sym : String) (o : Nat) (h : ScanPre sym o s) :
    WP isa (scan sym o) s fun t =>
      (∀ k < 4, t.gpr (accReg k) = tw s.mem (s.syms sym) (s.gpr (idxReg k)).toNat k) ∧
      Keep [.r0, .r1, .r8, .r9, .r10, .r11] s t ∧ t.mem = scanMem s o := by
  have hcf := h.cfit
  have hof := h.ofit
  have e0 : State.addr (s.gpr .r12 + BitVec.ofNat 32 o) = State.addr (s.gpr .r12) + BitVec.ofNat 64 o :=
    addr_add (by omega)
  have e4 : State.addr (s.gpr .r12 + BitVec.ofNat 32 (o + 4)) =
      State.addr (s.gpr .r12) + BitVec.ofNat 64 (o + 4) := addr_add (by omega)
  have w0 : InRegions s.wr (State.addr (s.gpr .r12 + BitVec.ofNat 32 o)) 4 := by rw [e0]; exact h.s0
  have w4 : InRegions s.wr (State.addr (s.gpr .r12 + BitVec.ofNat 32 (o + 4))) 4 := by rw [e4]; exact h.s4
  have ho : o < 4096 := by omega
  have ho4 : o + 4 < 4096 := by omega
  obtain ⟨T, hT⟩ : ∃ T, s.syms sym = T := ⟨_, rfl⟩
  have hTf : T.toNat + 4096 ≤ 2 ^ 32 := hT ▸ h.tfit
  have hrT : (⟨State.addr T, 4096⟩ : Region) ∈ s.rd ++ s.wr := hT ▸ h.trd
  unfold scan
  -- The slots, the table's address and the values so far.
  refine WP.seq (WP.mono (Q := fun s₁ => ScanAt s (scanMem s o) T (fun k => s.gpr (idxReg k)) 0 s₁) ?_ fun s₁ h₁ => ?_)
  · crun [w0, w4, ho, ho4, exec_adrSym, syms_mem, hT]
    refine ⟨fun k hk => ?_, fun k hk => ?_, rfl, ?_, ⟨?_, rfl, rfl, rfl⟩, ?_⟩
    · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
    · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
        simp only [acc, Nat.not_lt_zero, ite_false] <;> rfl
    · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
      rw [Nat.mul_zero, BitVec.add_zero]
    · intro r hr
      simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨_, _, h2, h3, h8, h9, h10, h11⟩ := hr
      simp only [gpr_setReg, h2, h3, h8, h9, h10, h11, ite_false]
    · simp only [mem_setReg]
      rw [scanMem, ← e0, ← e4]
  -- The loop.
  have loop : WP isa (.loop (.block scanBody) .ne) s₁ (ScanAt s (scanMem s o) T (fun k => s.gpr (idxReg k)) 256) := by
    refine WP.loop (M := isa) (fun n (v : State) => ∃ j, n = 256 - j ∧ j < 256 ∧ ScanAt s (scanMem s o) T (fun k => s.gpr (idxReg k)) j v)
      ?_ 256 s₁ ⟨0, rfl, by decide, h₁⟩
    rintro n v ⟨j, rfl, hj, hv⟩
    refine WP.mono (body_ok hj (fun k hk => h.idx k hk) hTf hrT hv) fun w ⟨hw, wz⟩ => ?_
    by_cases he : j = 255
    · subst he
      exact .inl ⟨by show some (!w.z) = _; rw [wz]; rfl, hw⟩
    · exact .inr ⟨by show some (!w.z) = _; rw [wz, decide_eq_false he]; rfl, 256 - (j + 1), by omega, j + 1, rfl,
        by omega, hw⟩
  refine WP.seq (WP.mono loop fun v hv => ?_)
  -- `r2` and `r3` back.
  have v12 : v.gpr .r12 = s.gpr .r12 := hv.keep.gpr _ (by decide)
  have sep : Mem.Sep (State.addr (s.gpr .r12) + BitVec.ofNat 64 o) (32 / 8)
      (State.addr (s.gpr .r12) + BitVec.ofNat 64 (o + 4)) (32 / 8) := Offset.sep _ (by omega) (by omega) (by omega)
  have r0 : (scanMem s o).readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 o)) 32 = s.gpr .r2 := by
    rw [e0, scanMem, Mem.readW_writeW_sep sep (by decide), Mem.readW_writeW_self32]
  have r4 : (scanMem s o).readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 (o + 4))) 32 = s.gpr .r3 := by
    rw [e4, scanMem, Mem.readW_writeW_self32]
  have w0' : InRegions (v.rd ++ v.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 o)) 4 := by
    rw [hv.keep.rd, hv.keep.wr]; obtain ⟨g, hg, hc⟩ := w0; exact ⟨g, List.mem_append_right _ hg, hc⟩
  have w4' : InRegions (v.rd ++ v.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 (o + 4))) 4 := by
    rw [hv.keep.rd, hv.keep.wr]; obtain ⟨g, hg, hc⟩ := w4; exact ⟨g, List.mem_append_right _ hg, hc⟩
  crun [v12, w0', w4', ho, ho4, hv.mem, r0, r4]
  refine ⟨fun k hk => ?_, ⟨fun r hr => ?_, hv.keep.rd, hv.keep.wr, hv.keep.sp⟩⟩
  · have hk8 := hv.hacc k hk
    simp only [accReg_ne_r2, accReg_ne_r3, ite_false, hk8, acc]
    rw [ite_eq_left (h.idx k hk), ← hT]
    exact tw_scanMem h (h.idx k hk) hk
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h1, h8, h9, h10, h11⟩ := hr
    simp only [gpr_setReg]
    split
    · subst_vars; rfl
    split
    · subst_vars; rfl
    rename_i n3 n2
    exact hv.keep.gpr r (by
      simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨h0, h1, n2, n3, h8, h9, h10, h11⟩)

end VG.Proof.Cast5.Arm
