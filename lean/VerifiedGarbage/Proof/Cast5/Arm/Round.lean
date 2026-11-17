module

public import VerifiedGarbage.Proof.Cast5.Rotate
public import VerifiedGarbage.Proof.Cast5.Round
public import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Cast5.Arm.Run
public import VerifiedGarbage.Proof.Cast5.Table
public import VerifiedGarbage.Impl.Cast5.Arm
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

/-! ### `Cast5.Arm.Scan`, which this module and modules that import it used -/

section

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
  rw [← ent_table h he hk, tw, ent, addr_add (by omega_arith)]

/-- Memory holding a table, later: its words are kept by writes apart from it. -/
theorem held_frame {rs : List Region} {m m' : Mem} {T : Addr} {W : List (BitVec 64)} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨T, 8 * W.length⟩ r) (hl : 8 * W.length < 2 ^ 64) (h : Held m T W) :
    Held m' T W := fun i hi => by
  rw [hf.readW (Offset.contains_base _ (by omega_arith) (by omega_arith)) hd (by decide)]
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
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_arith) with rfl | rfl | rfl | rfl <;>
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega_arith) with rfl | rfl | rfl | rfl <;>
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
      rw [← hz, BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
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
      omega_arith
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
  have ho : 4 * k < 4096 := by omega_arith
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
  · have hn : (idx k).toNat = j := by rw [h, BitVec.toNat_ofNat]; omega_arith
    rw [ite_eq_left h, ite_eq_right (by omega_arith), ite_eq_left (by omega_arith), hn]
    exact BitVec.eq_of_getLsbD_eq (by simp)
  · have hn : (idx k).toNat ≠ j := fun h' => h (BitVec.eq_of_toNat_eq (by
      rw [h', BitVec.toNat_ofNat]; omega_arith))
    rw [ite_eq_right h, show ∀ y : BitVec 32, y ||| 0 = y from fun y => BitVec.eq_of_getLsbD_eq (by simp)]
    by_cases h2 : (idx k).toNat < j
    · rw [ite_eq_left h2, ite_eq_left (by omega_arith)]
    · rw [ite_eq_right h2, ite_eq_right (by omega_arith)]

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
    | zero => exact WP.block_nil ⟨h.hidx, fun k hk => by rw [ite_eq_right (by omega_arith)]; exact h.hacc k hk,
        h.r2, h.r3, h.keep, h.mem⟩
    | succ e ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        WP.block_append_iff]
      refine WP.mono (ih (by omega_arith)) fun t ⟨ti, ta, t2, t3, tk, tm⟩ => ?_
      have ea : State.addr (t.gpr .r3 + BitVec.ofNat 32 (4 * e)) = State.addr T + BitVec.ofNat 64 (16 * j + 4 * e) := by
        rw [t3, BitVec.add_assoc, ← BitVec.ofNat_add, addr_add (by omega_arith)]
      have hin : InRegions (t.rd ++ t.wr) (State.addr (t.gpr .r3 + BitVec.ofNat 32 (4 * e))) 4 := by
        rw [tk.rd, tk.wr, ea]; exact ⟨_, hrT, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
      refine WP.mono (look_ok t e (by omega_arith) hj t2 (by rw [ti e (by omega_arith)]; exact hidx e (by omega_arith)) hin)
        fun u ⟨ua, uo, um, urd, uwr, usp⟩ => ?_
      refine ⟨fun k hk => by rw [uo _ (idxReg_ne_r0 k) (idxReg_ne_r1 k) (accReg_ne_idxReg e k).symm,
          ti k hk], fun k hk => ?_, by rw [uo _ (by decide) (by decide) (accReg_ne_r2 e).symm, t2],
        by rw [uo _ (by decide) (by decide) (accReg_ne_r3 e).symm, t3],
        tk.trans ⟨fun r hr => ?_, urd, uwr, usp⟩, um.trans tm⟩
      · by_cases hke : k = e
        · subst hke
          have ev : t.mem.readW (State.addr (t.gpr .r3 + BitVec.ofNat 32 (4 * k))) 32 = tw m T j k := by
            rw [tm, t3, BitVec.add_assoc, ← BitVec.ofNat_add]; rfl
          rw [ite_eq_left (by omega_arith), ua, ta k hk, ite_eq_right (by omega_arith), ti k hk, ev, acc_succ _ idx hj]
        · have hne : accReg k ≠ accReg e := fun h' => hke (accReg_inj hk (by omega_arith) h')
          rw [uo _ (accReg_ne_r0 k) (accReg_ne_r1 k) hne, ta k hk]
          by_cases hk' : k < e
          · rw [ite_eq_left hk', ite_eq_left (by omega_arith)]
          · rw [ite_eq_right hk', ite_eq_right (by omega_arith)]
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
      show 16 * j + 16 = 16 * (j + 1) by omega_arith]
  · simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨_, _, h2, h3, _⟩ := hr
    simp only [gpr_setReg, h2, h3, gpr_sub, ite_false]
  · by_cases he : j = 255
    · subst he; rfl
    · rw [decide_eq_false he]
      have : BitVec.ofNat 32 j - 255 ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
        simp at this; omega_arith
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
      State.addr (s.syms sym) + BitVec.ofNat 64 (16 * e + 4 * k) := addr_add (by omega_arith)
  have cT : (⟨State.addr (s.syms sym), 4096⟩ : Region).Contains (State.addr (s.syms sym + BitVec.ofNat 32
      (16 * e + 4 * k))) (32 / 8) := by
    rw [ea]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  unfold tw scanMem
  rw [Mem.readW_writeW_sep (h.dTS.sep cT (Offset.contains (State.addr (s.gpr .r12)) (d := o + 4) (n := 32 / 8)
      (e := o) (k := 8) (by omega_arith) (by omega_arith) (by omega_arith))) (by decide),
    Mem.readW_writeW_sep (h.dTS.sep cT (Offset.contains (State.addr (s.gpr .r12)) (d := o) (n := 32 / 8)
      (e := o) (k := 8) (by omega_arith) (by omega_arith) (by omega_arith))) (by decide)]

/-- The scan: `r8 + k` is word `k` of the entry of the table whose number
is in `r4 + k`; only `r0`, `r1`, `r8`–`r11` and the two slots are written. -/
theorem scan_ok (s : State) (sym : String) (o : Nat) (h : ScanPre sym o s) :
    WP isa (scan sym o) s fun t =>
      (∀ k < 4, t.gpr (accReg k) = tw s.mem (s.syms sym) (s.gpr (idxReg k)).toNat k) ∧
      Keep [.r0, .r1, .r8, .r9, .r10, .r11] s t ∧ t.mem = scanMem s o := by
  have hcf := h.cfit
  have hof := h.ofit
  have e0 : State.addr (s.gpr .r12 + BitVec.ofNat 32 o) = State.addr (s.gpr .r12) + BitVec.ofNat 64 o :=
    addr_add (by omega_arith)
  have e4 : State.addr (s.gpr .r12 + BitVec.ofNat 32 (o + 4)) =
      State.addr (s.gpr .r12) + BitVec.ofNat 64 (o + 4) := addr_add (by omega_arith)
  have w0 : InRegions s.wr (State.addr (s.gpr .r12 + BitVec.ofNat 32 o)) 4 := by rw [e0]; exact h.s0
  have w4 : InRegions s.wr (State.addr (s.gpr .r12 + BitVec.ofNat 32 (o + 4))) 4 := by rw [e4]; exact h.s4
  have ho : o < 4096 := by omega_arith
  have ho4 : o + 4 < 4096 := by omega_arith
  obtain ⟨T, hT⟩ : ∃ T, s.syms sym = T := ⟨_, rfl⟩
  have hTf : T.toNat + 4096 ≤ 2 ^ 32 := hT ▸ h.tfit
  have hrT : (⟨State.addr T, 4096⟩ : Region) ∈ s.rd ++ s.wr := hT ▸ h.trd
  unfold scan
  -- The slots, the table's address and the values so far.
  refine WP.seq (WP.mono (Q := fun s₁ => ScanAt s (scanMem s o) T (fun k => s.gpr (idxReg k)) 0 s₁) ?_ fun s₁ h₁ => ?_)
  · crun [w0, w4, ho, ho4, exec_adrSym, syms_mem, hT]
    refine ⟨fun k hk => ?_, fun k hk => ?_, rfl, ?_, ⟨?_, rfl, rfl, rfl⟩, ?_⟩
    · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> rfl
    · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_arith) with rfl | rfl | rfl | rfl <;>
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
    · exact .inr ⟨by show some (!w.z) = _; rw [wz, decide_eq_false he]; rfl, 256 - (j + 1), by omega_arith, j + 1, rfl,
        by omega_arith, hw⟩
  refine WP.seq (WP.mono loop fun v hv => ?_)
  -- `r2` and `r3` back.
  have v12 : v.gpr .r12 = s.gpr .r12 := hv.keep.gpr _ (by decide)
  have sep : Mem.Sep (State.addr (s.gpr .r12) + BitVec.ofNat 64 o) (32 / 8)
      (State.addr (s.gpr .r12) + BitVec.ofNat 64 (o + 4)) (32 / 8) := Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)
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

end

end

/-!
# CAST5 on ARMv7: a round

`round up` computes `I` (`byType mix`, `rotate`), spreads its bytes over
`r4`–`r7` (`spread`), scans `VG_CAST5_S1234` and combines the four values into `f`
(`byType comb`), makes the Feistel step (`feistel`), and moves the type and
the count of rounds left on (`next`).
-/

@[expose] public section

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Cast5.Arm
open VG.Impl.Cast5 (s1234Sym)

/-! ## Choosing by the type -/

/-- The address of the slot at `off` of the working space at `r12`. -/
scoped notation:max "slot " s:max off:max => State.addr (State.gpr s Reg.r12 + BitVec.ofNat 32 off)

theorem byType_ok (s : State) (f : Nat → List Instr) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3)
    (hin : InRegions (s.rd ++ s.wr) (slot s 20) 4) (hv : s.mem.readW (slot s 20) 32 = BitVec.ofNat 32 t)
    {Q : State → Prop} (hQ : ∀ u, Keep [.r0] s u → u.mem = s.mem → WP isa (.block (f t)) u Q) :
    WP isa (byType f) s Q := by
  unfold byType
  refine WP.seq ?_
  crun [typeOff, hin, hv]
  rcases ht with rfl | rfl | rfl
  · refine WP.ite true rfl (fun _ => hQ _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ rfl)
      (fun h => absurd h (by decide))
    simp only [List.mem_singleton] at hr
    simp only [gpr_sub]; exact gpr_setReg_of_ne _ _ hr
  · refine WP.ite false rfl (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq ?_
    crun
    refine WP.ite true rfl (fun _ => hQ _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ rfl)
      (fun h => absurd h (by decide))
    simp only [List.mem_singleton] at hr
    simp only [gpr_sub]; exact gpr_setReg_of_ne _ _ hr
  · refine WP.ite false rfl (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq ?_
    crun
    refine WP.ite false rfl (fun h => absurd h (by decide)) (fun _ =>
      hQ _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ rfl)
    simp only [List.mem_singleton] at hr
    simp only [gpr_sub]; exact gpr_setReg_of_ne _ _ hr

/-! ## The pieces of a round -/

theorem mix_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) {km d : Spec.Cast5.Word}
    (h3 : s.gpr .r3 = d) (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 4)
    (hv : s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 32 = km) :
    WP isa (.block (Impl.Cast5.Arm.mix t)) s fun u => u.gpr .r1 = Proof.Cast5.mix t km d ∧ Keep [.r1] s u ∧ u.mem = s.mem := by
  rcases ht with rfl | rfl | rfl <;>
  · unfold Impl.Cast5.Arm.mix
    crun [hin, hv, h3]
    exact ⟨rfl, ⟨fun r hr => by simp only [List.mem_singleton] at hr; simp only [gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩⟩

theorem rotateStep_ok (s : State) {b : Nat} (hb : b < 5) {a kb : BitVec 32}
    (h1 : s.gpr .r1 = a) (h0 : s.gpr .r0 = kb) :
    WP isa (.block (rotateStep b)) s fun u =>
      u.gpr .r1 = Proof.Cast5.step a kb b ∧ u.gpr .r0 = (if b < 4 then kb >>> 1 else kb) ∧
      Keep [.r0, .r1, .r4, .r5] s u ∧ u.mem = s.mem := by
  have hn : 1 ≤ 32 - 2 ^ b ∧ 32 - 2 ^ b ≤ 31 := by
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 by omega_using [hb]) with h | h | h | h | h <;>
      subst h <;> decide
  unfold rotateStep
  by_cases h4 : b < 4
  · rw [ite_eq_left h4]
    crun [h1, h0, hn]
    exact ⟨rfl, by rw [ite_eq_left h4], ⟨by keep_regs, rfl, rfl, rfl⟩⟩
  · rw [ite_eq_right h4]
    crun [h1, h0, hn]
    exact ⟨rfl, by rw [ite_eq_right h4], ⟨by keep_regs, rfl, rfl, rfl⟩⟩

theorem rotate_ok (s : State) {a kr : BitVec 32} (h1 : s.gpr .r1 = a)
    (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 64)) 4)
    (hv : s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 64)) 32 = kr) :
    WP isa (.block rotate) s fun u =>
      u.gpr .r1 = a.rotateLeft (kr.toNat % 32) ∧ Keep [.r0, .r1, .r4, .r5] s u ∧ u.mem = s.mem := by
  have e : rotate = [.ldr .r0 .lr 64] ++ rotateStep 0 ++ rotateStep 1 ++ rotateStep 2 ++ rotateStep 3 ++
      rotateStep 4 := rfl
  rw [e, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  have k0 : WP isa (.block [.ldr .r0 .lr 64]) s fun u =>
      u.gpr .r0 = kr ∧ u.gpr .r1 = a ∧ Keep [.r0, .r1, .r4, .r5] s u ∧ u.mem = s.mem := by
    crun [hin, hv, h1]
    exact ⟨fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp only [gpr_setReg, hr.1, ite_false],
      rfl, rfl, rfl⟩
  refine WP.mono k0 fun t₀ ⟨k₀, a₀, p₀, m₀⟩ => ?_
  refine WP.mono (rotateStep_ok t₀ (by decide) a₀ k₀) fun t₁ ⟨a₁, k₁, p₁, m₁⟩ => ?_
  rw [ite_eq_left (by decide)] at k₁
  refine WP.mono (rotateStep_ok t₁ (by decide) a₁ k₁) fun t₂ ⟨a₂, k₂, p₂, m₂⟩ => ?_
  rw [ite_eq_left (by decide)] at k₂
  refine WP.mono (rotateStep_ok t₂ (by decide) a₂ k₂) fun t₃ ⟨a₃, k₃, p₃, m₃⟩ => ?_
  rw [ite_eq_left (by decide)] at k₃
  refine WP.mono (rotateStep_ok t₃ (by decide) a₃ k₃) fun t₄ ⟨a₄, k₄, p₄, m₄⟩ => ?_
  rw [ite_eq_left (by decide)] at k₄
  refine WP.mono (rotateStep_ok t₄ (by decide) a₄ k₄) fun t₅ ⟨a₅, _, p₅, m₅⟩ => ?_
  refine ⟨?_, p₀.trans (p₁.trans (p₂.trans (p₃.trans (p₄.trans p₅)))), by rw [m₅, m₄, m₃, m₂, m₁, m₀]⟩
  rw [a₅, Proof.Cast5.steps_eq]

/-- Index `k` of a scan of `I`: byte `k` of `I` (from the least significant). -/
def idx (i : BitVec 32) : Nat → BitVec 32
  | 0 => i &&& 255
  | 1 => i >>> 8 &&& 255
  | 2 => i >>> 16 &&& 255
  | _ => i >>> 24

theorem idx_toNat (i : BitVec 32) {k : Nat} (hk : k < 4) :
    (idx i k).toNat = i.toNat / 2 ^ (8 * k) % 256 := by
  have := i.isLt
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;>
    simp only [idx, BitVec.toNat_ushiftRight, BitVec.toNat_and, Nat.shiftRight_eq_div_pow,
      show (255 : BitVec 32).toNat = 255 from rfl, show (255 : Nat) = 2 ^ 8 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod] <;> omega_using []

theorem idx_lt (i : BitVec 32) {k : Nat} (hk : k < 4) : (idx i k).toNat < 256 := by
  rw [idx_toNat i hk]; omega_using []

theorem idx_byte (i : BitVec 32) {k : Nat} (hk : k < 4) :
    BitVec.ofNat 8 (idx i k).toNat = Spec.Cast5.byte i (3 - k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, idx_toNat i hk]
  simp only [Spec.Cast5.byte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;> omega_using []

theorem spread_ok (s : State) {i : BitVec 32} (h1 : s.gpr .r1 = i) :
    WP isa (.block spread) s fun u =>
      (∀ k < 4, u.gpr (idxReg k) = idx i k) ∧ Keep [.r4, .r5, .r6, .r7] s u ∧ u.mem = s.mem := by
  unfold spread
  crun [h1]
  refine ⟨fun k hk => ?_, ⟨fun r hr => ?_, rfl, rfl, rfl⟩⟩
  · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem comb_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) :
    WP isa (.block (Impl.Cast5.Arm.comb t)) s fun u =>
      u.gpr .r1 = Proof.Cast5.comb t (s.gpr .r11) (s.gpr .r10) (s.gpr .r9) (s.gpr .r8) ∧ Keep [.r1] s u ∧
        u.mem = s.mem := by
  rcases ht with rfl | rfl | rfl <;>
  · unfold Impl.Cast5.Arm.comb
    crun
    exact ⟨rfl, ⟨fun r hr => by simp only [List.mem_singleton] at hr; simp only [gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩⟩

theorem feistel_ok (s : State) (up : Bool) :
    WP isa (.block (feistel up)) s fun u =>
      u.gpr .r2 = s.gpr .r3 ∧ u.gpr .r3 = s.gpr .r1 ^^^ s.gpr .r2 ∧
      u.gpr .lr = (if up then s.gpr .lr + 4 else s.gpr .lr - 4) ∧ Keep [.r1, .r2, .r3, .lr] s u ∧
      u.mem = s.mem := by
  cases up <;>
  · unfold feistel
    crun
    exact ⟨by keep_regs, rfl, rfl, rfl⟩

/-- The type after `t`. -/
def nextT (up : Bool) (t : Nat) : Nat :=
  if up then (if t = 3 then 1 else t + 1) else (if t = 1 then 3 else t - 1)

/-- The type `v` (in `r0`) to its slot, then the count of rounds left down. -/
theorem nextTail_ok (s : State) {v cnt : BitVec 32} (h0 : s.gpr .r0 = v)
    (hinT : InRegions s.wr (slot s 20) 4)
    (hinC : InRegions s.wr (slot s 16) 4) (hvC : (s.mem.writeW (slot s 20) v).readW (slot s 16) 32 = cnt) :
    WP isa (.block [.str .r0 .r12 typeOff, .ldr .r0 .r12 cntOff, .subs .r0 .r0 (.imm 1), .str .r0 .r12 cntOff]) s
      fun u => u.mem = (s.mem.writeW (slot s 20) v).writeW (slot s 16) (cnt - 1) ∧ u.z = (cnt - 1 == 0) ∧
        Keep [.r0] s u := by
  have hinC' : InRegions (s.rd ++ s.wr) (slot s 16) 4 := by
    obtain ⟨g, hg, hc⟩ := hinC; exact ⟨g, List.mem_append_right _ hg, hc⟩
  crun [typeOff, cntOff, h0, hinT, hinC, hinC', hvC]
  exact ⟨by keep_regs, rfl, rfl, rfl⟩

theorem next_ok (s : State) (up : Bool) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) {cnt : BitVec 32}
    (hinT : InRegions s.wr (slot s 20) 4) (hvT : s.mem.readW (slot s 20) 32 = BitVec.ofNat 32 t)
    (hinC : InRegions s.wr (slot s 16) 4) (hvC : s.mem.readW (slot s 16) 32 = cnt)
    (hsep : Mem.Sep (slot s 16) 4 (slot s 20) 4) :
    WP isa (next up) s fun u =>
      u.mem = (s.mem.writeW (slot s 20) (BitVec.ofNat 32 (nextT up t))).writeW (slot s 16) (cnt - 1) ∧
      u.z = (cnt - 1 == 0) ∧ Keep [.r0] s u := by
  have hinT' : InRegions (s.rd ++ s.wr) (slot s 20) 4 := by
    obtain ⟨g, hg, hc⟩ := hinT; exact ⟨g, List.mem_append_right _ hg, hc⟩
  have hvC' (v : BitVec 32) : (s.mem.writeW (slot s 20) v).readW (slot s 16) 32 = cnt := by
    rw [Mem.readW_writeW_sep hsep (by decide), hvC]
  -- The rest, from the state after the branch, which wrote only `r0` and the flags.
  have tail : ∀ u : State, Keep [.r0] s u → u.mem = s.mem → u.gpr .r0 = BitVec.ofNat 32 (nextT up t) →
      WP isa (.block [.str .r0 .r12 typeOff, .ldr .r0 .r12 cntOff, .subs .r0 .r0 (.imm 1),
        .str .r0 .r12 cntOff]) u fun w =>
      w.mem = (s.mem.writeW (slot s 20) (BitVec.ofNat 32 (nextT up t))).writeW (slot s 16) (cnt - 1) ∧
      w.z = (cnt - 1 == 0) ∧ Keep [.r0] s w := by
    intro u uk um u0
    have e12 : u.gpr .r12 = s.gpr .r12 := uk.gpr _ (by decide)
    have es (off : Nat) : slot u off = slot s off := by rw [e12]
    refine WP.mono (nextTail_ok u u0 (by rw [es, uk.wr]; exact hinT) (by rw [es, uk.wr]; exact hinC)
      (by rw [es, es, um]; exact hvC' _)) fun w ⟨wm, wz, wk⟩ => ⟨by rw [wm, es, es, um], wz, uk.trans wk⟩
  unfold next
  cases up <;> rcases ht with rfl | rfl | rfl
  all_goals
    refine WP.seq ?_
    crun [typeOff, hinT', hvT]
  all_goals
    refine WP.seq (wp_ite_eq (fun h => ?_) (fun h => ?_))
  all_goals first
    | exact absurd (h.symm.trans (z_sub _ _ _)) (by decide)
    | refine WP.mono (Q := fun u : State => Keep [.r0] s u ∧ u.mem = s.mem ∧
          u.gpr .r0 = BitVec.ofNat 32 (nextT _ _)) ?_ fun u ⟨a, b, c⟩ => tail u a b c
      crun
      exact ⟨⟨by keep_regs, rfl, rfl, rfl⟩, by decide⟩

/-! ## The round -/

/-- `f` of a round of type `t` with the subkeys `km`, `kr`, on `D = d`. -/
def fT (t : Nat) (km kr d : Spec.Cast5.Word) : Spec.Cast5.Word :=
  let i := (Proof.Cast5.mix t km d).rotateLeft (kr.toNat % 32)
  Proof.Cast5.comb t (Spec.Cast5.S1 (Spec.Cast5.byte i 0)) (Spec.Cast5.S2 (Spec.Cast5.byte i 1))
    (Spec.Cast5.S3 (Spec.Cast5.byte i 2)) (Spec.Cast5.S4 (Spec.Cast5.byte i 3))

/-- What a round needs: `(L, R)` in `(r2, r3)`; `Kmᵢ` at `lr` and `Krᵢ` at
`lr + 64`; the type `t` and the count `cnt` of rounds left in their slots;
the scan's slots writable; and the table `VG_CAST5_S1234`, readable and
apart from them. -/
structure RoundPre (s : State) (km kr l r : Spec.Cast5.Word) (t : Nat) (cnt : BitVec 32) : Prop where
  r2 : s.gpr .r2 = l
  r3 : s.gpr .r3 = r
  inM : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 4
  valM : s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 32 = km
  inR : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 64)) 4
  valR : s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 64)) 32 = kr
  ht : t = 1 ∨ t = 2 ∨ t = 3
  inT : InRegions s.wr (slot s 20) 4
  valT : s.mem.readW (slot s 20) 32 = BitVec.ofNat 32 t
  inC : InRegions s.wr (slot s 16) 4
  valC : s.mem.readW (slot s 16) 32 = cnt
  sep : Mem.Sep (slot s 16) 4 (slot s 20) 4
  cfit : (s.gpr .r12).toNat + 32 ≤ 2 ^ 32
  inS24 : InRegions s.wr (State.addr (s.gpr .r12) + BitVec.ofNat 64 24) 4
  inS28 : InRegions s.wr (State.addr (s.gpr .r12) + BitVec.ofNat 64 28) 4
  tfit : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 32
  trd : (⟨State.addr (s.syms s1234Sym), 4096⟩ : Region) ∈ s.rd ++ s.wr
  held : Held s.mem (State.addr (s.syms s1234Sym)) Impl.Cast5.s1234
  dTS : Region.Disjoint ⟨State.addr (s.syms s1234Sym), 4096⟩ ⟨State.addr (s.gpr .r12) + BitVec.ofNat 64 24, 8⟩

theorem RoundPre.inT' {s : State} {km kr l r : Spec.Cast5.Word} {t : Nat} {cnt : BitVec 32}
    (h : RoundPre s km kr l r t cnt) : InRegions (s.rd ++ s.wr) (slot s 20) 4 := by
  obtain ⟨g, hg, hc⟩ := h.inT; exact ⟨g, List.mem_append_right _ hg, hc⟩

/-- The registers a round writes before its Feistel step. -/
def preRegs : List Reg := [.r0, .r1, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

/-- The registers a round writes. -/
def roundRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

/-- The slots of the working space, as the scan addresses them. -/
theorem slot_addr {s : State} (hc : (s.gpr .r12).toNat + 32 ≤ 2 ^ 32) {off : Nat} (ho : off < 32) :
    slot s off = State.addr (s.gpr .r12) + BitVec.ofNat 64 off := addr_add (by omega_using [hc, ho])

/-- A slot below the scan's, past its stores. -/
theorem scanMem_slot (s : State) (hc : (s.gpr .r12).toNat + 32 ≤ 2 ^ 32) {off : Nat} (ho : off + 4 ≤ 24) :
    (scanMem s spillEcb).readW (slot s off) 32 = s.mem.readW (slot s off) 32 := by
  rw [slot_addr hc (by omega_using [ho]), scanMem, spillEcb,
    Mem.readW_writeW_sep (Offset.sep _ (by omega_using [ho]) (by omega_using [ho]) (by omega_using [])) (by decide),
    Mem.readW_writeW_sep (Offset.sep _ (by omega_using [ho]) (by omega_using [ho]) (by omega_using [])) (by decide)]

theorem round_ok (s : State) (up : Bool) {km kr l r : Spec.Cast5.Word} {t : Nat} {cnt : BitVec 32}
    (h : RoundPre s km kr l r t cnt) :
    WP isa (round up) s fun u =>
      u.gpr .r2 = r ∧ u.gpr .r3 = l ^^^ fT t km kr r ∧
      u.gpr .lr = (if up then s.gpr .lr + 4 else s.gpr .lr - 4) ∧
      u.mem = ((scanMem s spillEcb).writeW (slot s 20) (BitVec.ofNat 32 (nextT up t))).writeW (slot s 16)
        (cnt - 1) ∧
      u.z = (cnt - 1 == 0) ∧ Keep roundRegs s u := by
  have ht := h.ht
  unfold round
  -- `I` before the rotation.
  refine WP.seq (VG.Arm.WP.mono_syms (byType_ok s Impl.Cast5.Arm.mix (Q := fun v => v.gpr .r1 = Proof.Cast5.mix t km r ∧
      Keep [.r0, .r1] s v ∧ v.mem = s.mem) ht h.inT' h.valT fun u uk um => ?_) fun v hv vsy => ?_)
  · have g (q : Reg) (hq : q ≠ .r0) : u.gpr q = s.gpr q := uk.gpr q (by simpa using hq)
    exact WP.mono (mix_ok u ht (by rw [g _ (by decide)]; exact h.r3)
      (by rw [uk.rd, uk.wr, g _ (by decide)]; exact h.inM) (by rw [um, g _ (by decide)]; exact h.valM))
      fun v ⟨v1, vk, vm⟩ => ⟨v1, (uk.mono (by decide)).trans (vk.mono (by decide)), vm.trans um⟩
  obtain ⟨v1, vk, vm⟩ := hv
  have gv (q : Reg) (hq : q ∉ [Reg.r0, .r1]) : v.gpr q = s.gpr q := vk.gpr q hq
  -- The rotation, the indices and the scan.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine (VG.Arm.WP.mono_syms (rotate_ok v v1 (kr := kr) (by rw [vk.rd, vk.wr, gv _ (by decide)]; exact h.inR)
    (by rw [vm, gv _ (by decide)]; exact h.valR)) fun w ⟨w1, wk, wm⟩ wsy => ?_)
  obtain ⟨i, hi⟩ : ∃ i, (Proof.Cast5.mix t km r).rotateLeft (kr.toNat % 32) = i := ⟨_, rfl⟩
  rw [hi] at w1
  refine VG.Arm.WP.mono_syms (spread_ok w w1) fun x ⟨xi, xk, xm⟩ xsy => ?_
  have kx := (vk.mono (by decide)).trans ((wk.mono (by decide)).trans
    (xk.mono (show ∀ q ∈ [Reg.r4, .r5, .r6, .r7], q ∈ preRegs by decide)))
  have mx : x.mem = s.mem := xm.trans (wm.trans vm)
  have sx : x.syms = s.syms := xsy.trans (wsy.trans vsy)
  have r12x : x.gpr .r12 = s.gpr .r12 := kx.gpr _ (by decide)
  have sp : ScanPre s1234Sym spillEcb x :=
    { idx := fun k hk => by rw [xi k hk]; exact idx_lt i hk
      cfit := by rw [r12x]; have := h.cfit; unfold spillEcb; omega_using [this]
      ofit := by decide
      s0 := by rw [r12x, kx.wr]; exact h.inS24
      s4 := by rw [r12x, kx.wr]; exact h.inS28
      tfit := by rw [sx]; exact h.tfit
      trd := by rw [sx, kx.rd, kx.wr]; exact h.trd
      dTS := by rw [sx, r12x]; exact h.dTS }
  have ex : scanMem x spillEcb = scanMem s spillEcb := by
    rw [scanMem, scanMem, mx, r12x, kx.gpr _ (by decide), kx.gpr _ (by decide)]
  refine WP.seq (WP.mono (scan_ok x s1234Sym spillEcb sp) fun y ⟨ya, yk, ym⟩ => ?_)
  have kxy := kx.trans (yk.mono (show ∀ r ∈ [Reg.r0, .r1, .r8, .r9, .r10, .r11], r ∈ preRegs by decide))
  rw [ex] at ym
  have r12y : y.gpr .r12 = s.gpr .r12 := kxy.gpr _ (by decide)
  have esl (off : Nat) : slot y off = slot s off := by rw [r12y]
  have valT : y.mem.readW (slot y 20) 32 = BitVec.ofNat 32 t := by
    rw [ym, esl, scanMem_slot s h.cfit (by decide)]; exact h.valT
  -- `f`.
  refine WP.seq (WP.mono (byType_ok y Impl.Cast5.Arm.comb (Q := fun z => z.gpr .r1 = fT t km kr r ∧
      Keep preRegs s z ∧ z.mem = scanMem s spillEcb) ht (by rw [kxy.rd, kxy.wr, r12y]; exact h.inT')
      valT fun u uk um => ?_) fun z hz => ?_)
  · have g (q : Reg) (hq : q ≠ .r0) : u.gpr q = y.gpr q := uk.gpr q (by simpa using hq)
    refine WP.mono (comb_ok u ht) fun z ⟨z1, zk, zm⟩ => ⟨?_, kxy.trans ((uk.mono (by decide)).trans
      (zk.mono (by decide))), zm.trans (um.trans ym)⟩
    have hT := h.tfit
    have ent (k : Nat) (hk : k < 4) : y.gpr (accReg k) = tableEnt Spec.Cast5.S4 Spec.Cast5.S3 Spec.Cast5.S2
        Spec.Cast5.S1 (idx i k).toNat k := by
      rw [ya k hk, mx, xi k hk, sx]; exact tw_table hT h.held (idx_lt i hk) hk
    have a0 : y.gpr .r8 = _ := ent 0 (by decide)
    have a1 : y.gpr .r9 = _ := ent 1 (by decide)
    have a2 : y.gpr .r10 = _ := ent 2 (by decide)
    have a3 : y.gpr .r11 = _ := ent 3 (by decide)
    rw [z1, g _ (by decide), g _ (by decide), g _ (by decide), g _ (by decide), a0, a1, a2, a3]
    unfold fT
    rw [hi]
    simp only [tableEnt, idx_byte i (show 0 < 4 by decide), idx_byte i (show 1 < 4 by decide),
      idx_byte i (show 2 < 4 by decide), idx_byte i (show 3 < 4 by decide)]
  obtain ⟨z1, zk, zm⟩ := hz
  have gz (q : Reg) (hq : q ∉ preRegs) : z.gpr q = s.gpr q := zk.gpr q hq
  -- The Feistel step, then the type and the count.
  refine WP.seq (WP.mono (feistel_ok z up) fun a ⟨a2, a3, alr, ak, am⟩ => ?_)
  have ka := (zk.mono (show ∀ q ∈ preRegs, q ∈ roundRegs by decide)).trans
    (ak.mono (show ∀ q ∈ [Reg.r1, .r2, .r3, .lr], q ∈ roundRegs by decide))
  have r12a : a.gpr .r12 = s.gpr .r12 := ka.gpr _ (by decide)
  have es (off : Nat) : slot a off = slot s off := by rw [r12a]
  have ma : a.mem = scanMem s spillEcb := am.trans zm
  have hinT := h.inT
  have hinC := h.inC
  refine WP.mono (next_ok a up ht (cnt := cnt) (by rw [es, ka.wr]; exact h.inT)
    (by rw [es, ma, scanMem_slot s h.cfit (by decide)]; exact h.valT)
    (by rw [es, ka.wr]; exact h.inC) (by rw [es, ma, scanMem_slot s h.cfit (by decide)]; exact h.valC)
    (by rw [es, es]; exact h.sep))
    fun b ⟨bm, bz, bk⟩ => ?_
  have gb (q : Reg) (hq : q ≠ .r0) : b.gpr q = a.gpr q := bk.gpr q (by simpa using hq)
  refine ⟨by rw [gb _ (by decide), a2, gz _ (by decide), h.r3], ?_, ?_, by rw [bm, es, es, ma], bz,
    ka.trans (bk.mono (by decide))⟩
  · rw [gb _ (by decide), a3, z1, gz _ (by decide), h.r2, BitVec.xor_comm]
  · rw [gb _ (by decide), alr, gz _ (by decide)]

end VG.Proof.Cast5.Arm
