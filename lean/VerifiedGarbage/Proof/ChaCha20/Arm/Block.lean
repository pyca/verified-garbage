module

import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.ChaCha20.Spec
public import VerifiedGarbage.Impl.ChaCha20.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Spec.ChaCha20.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Reduce
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Spill
meta import VerifiedGarbage.Proof.ChaCha20.Spec
meta import VerifiedGarbage.Impl.ChaCha20.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Spec.ChaCha20.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Reduce
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Spec.ChaCha20
meta import VerifiedGarbage.TCB.Artifact

@[expose] public section

section

/-!
# ChaCha20 block function on 32-bit ARM: the rounds

A quarter round, executed once for any registers and any rotations of its
second and fourth words (`qr_ok`), and the rounds on the state: words 0–7 and
12–15 in their registers, those of the second and fourth rows rotated
(`pendAt`), and words 8–11 in `lr` or their slots (`Holds`, `RI`).
-/

namespace VG.Proof.ChaCha20.Arm

open VG VG.Arm VG.Impl.ChaCha20.Arm VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)

/-! ## Rotated operands -/

theorem rotr_zero (x : Word) : x.rotateRight 0 = x := by
  ext i hi
  simp [BitVec.getElem_rotateRight, hi]

theorem ror_eval {k : Nat} (hk : 1 ≤ k ∧ k ≤ 31) (r : Reg) (s : State) :
    (Op2.shifted r .ror k).eval s = some ((s.gpr r).rotateRight k) := by
  simp only [Op2.eval, hk, and_self, ↓reduceIte]

theorem rop_eval {k : Nat} (hk : k < 32) (r : Reg) (s : State) :
    (rop r k).eval s = some ((s.gpr r).rotateRight k) := by
  unfold rop
  split
  · rename_i h; rw [h, rotr_zero]; rfl
  · exact ror_eval (by omega_arith) r s

/-- `quarterRound` as the code computes it: the exclusive-ors before their
rotations, which the next additions and the last results apply. -/
theorem quarterRound_code (a b c d : Word) : quarterRound a b c d =
    let a1 := a + b; let e1 := a1 ^^^ d
    let c1 := c + e1.rotateRight 16; let f1 := c1 ^^^ b
    let a2 := a1 + f1.rotateRight 20; let e2 := a2 ^^^ e1.rotateRight 16
    let c2 := c1 + e2.rotateRight 24; let f2 := c2 ^^^ f1.rotateRight 20
    (a2, f2.rotateRight 25, c2, e2.rotateRight 24) := by
  simp only [quarterRound_eq, BitVec.xor_comm d, BitVec.xor_comm b,
    BitVec.xor_comm ((a + b ^^^ d).rotateRight 16),
    BitVec.xor_comm ((c + (a + b ^^^ d).rotateRight 16 ^^^ b).rotateRight 20)]

theorem qr_ok {a b c d : Reg} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) {br dr : Nat} (hbr : br < 32) (hdr : dr < 32) (s : State) :
    WP isa (.block (qr a b c d br dr)) s fun s' =>
      s'.gpr a = (quarterRound (s.gpr a) ((s.gpr b).rotateRight br) (s.gpr c)
        ((s.gpr d).rotateRight dr)).1 ∧
      (s'.gpr b).rotateRight 25 = (quarterRound (s.gpr a) ((s.gpr b).rotateRight br) (s.gpr c)
        ((s.gpr d).rotateRight dr)).2.1 ∧
      s'.gpr c = (quarterRound (s.gpr a) ((s.gpr b).rotateRight br) (s.gpr c)
        ((s.gpr d).rotateRight dr)).2.2.1 ∧
      (s'.gpr d).rotateRight 24 = (quarterRound (s.gpr a) ((s.gpr b).rotateRight br) (s.gpr c)
        ((s.gpr d).rotateRight dr)).2.2.2 ∧
      (∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [qr, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, rop_eval hbr, rop_eval hdr,
    ror_eval (k := 16) (by decide), ror_eval (k := 20) (by decide), ror_eval (k := 24) (by decide),
    Option.map_some, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ hab,
    RegUpd.gpr_setReg_of_ne _ _ hac, RegUpd.gpr_setReg_of_ne _ _ had, RegUpd.gpr_setReg_of_ne _ _ hbc,
    RegUpd.gpr_setReg_of_ne _ _ hbd, RegUpd.gpr_setReg_of_ne _ _ hcd,
    RegUpd.gpr_setReg_of_ne _ _ hab.symm, RegUpd.gpr_setReg_of_ne _ _ hac.symm,
    RegUpd.gpr_setReg_of_ne _ _ had.symm, RegUpd.gpr_setReg_of_ne _ _ hbc.symm,
    RegUpd.gpr_setReg_of_ne _ _ hbd.symm, RegUpd.gpr_setReg_of_ne _ _ hcd.symm,
    Option.some.injEq, exists_eq_left', quarterRound_code, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, true_and, and_true]
  intro r h1 h2 h3 h4
  simp only [RegUpd.gpr_setReg_of_ne _ _ h1, RegUpd.gpr_setReg_of_ne _ _ h2,
    RegUpd.gpr_setReg_of_ne _ _ h3, RegUpd.gpr_setReg_of_ne _ _ h4]

/-! ## The order of the diagonal round -/

/-- Quarter rounds on different words commute. -/
theorem qround_comm (v : CState) {x y z w x' y' z' w' : Fin 16}
    (h : ([x.1, y.1, z.1, w.1].all fun i => [x'.1, y'.1, z'.1, w'.1].all fun j => i != j) = true) :
    qround (qround v x y z w) x' y' z' w' = qround (qround v x' y' z' w') x y z w := by
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3, c4⟩, d1, d2, d3, d4⟩ := h
  apply Vector.ext
  intro k hk
  simp only [qround_get, Fin.getElem_fin, a1, a2, a3, a4, b1, b2, b3, b4, c1, c2, c3, c4, d1, d2, d3, d4,
    Ne.symm a1, Ne.symm a2, Ne.symm a3, Ne.symm a4, Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm b4,
    Ne.symm c1, Ne.symm c2, Ne.symm c3, Ne.symm c4, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
    ↓reduceIte]
  by_cases e1 : w'.1 = k
  · subst e1; simp only [↓reduceIte, a4, b4, c4, d4]
  by_cases e2 : z'.1 = k
  · subst e2; simp only [↓reduceIte, e1, a3, b3, c3, d3]
  by_cases e3 : y'.1 = k
  · subst e3; simp only [↓reduceIte, e1, e2, a2, b2, c2, d2]
  by_cases e4 : x'.1 = k
  · subst e4; simp only [↓reduceIte, e1, e2, e3, a1, b1, c1, d1]
  simp only [↓reduceIte, e1, e2, e3, e4]

/-- `inner_block` with the diagonal round's quarter rounds in the code's order. -/
theorem innerBlock_eq (v : CState) : innerBlock v =
    qround (qround (qround (qround (qround (qround (qround (qround v 0 4 8 12) 1 5 9 13) 2 6 10 14)
      3 7 11 15) 1 6 11 12) 0 5 10 15) 3 4 9 14) 2 7 8 13 := by
  simp only [innerBlock]
  rw [qround_comm (x := 2) (x' := 3) _ (by decide), qround_comm (x := 0) (x' := 1) _ (by decide)]

theorem repeat_succ' {α : Type} (f : α → α) (n : Nat) (a : α) :
    Nat.repeat f (n + 1) a = Nat.repeat f n (f a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.repeat, ih]; rfl

/-! ## Where the words are -/

/-- Word `k` is in its register `wreg k` (rather than its slot) when the
third-row word in `lr` is `c`: always, except for the third-row words other
than `c`. -/
def inReg (c k : Nat) : Bool := !(8 ≤ k && k ≤ 11) || k == c

/-- The home slot of word `k` (8–11), relative to the 64-bit address `B` of `buf`. -/
abbrev slotAddr (B : Addr) (k : Nat) : Addr := B + BitVec.ofNat 64 (slotOff k)

/-- The rotation right that gives word `k` from its register once the
quarter rounds of the first `n` columns have run: `pend`'s for those
columns' words, none for the others. -/
def pendAt (n k : Nat) : Nat := if k % 4 < n then pend k else 0

theorem pendAt_c (n : Nat) {k : Nat} (h8 : 8 ≤ k) (h11 : k ≤ 11) : pendAt n k = 0 := by
  have h1 : ¬(4 ≤ k ∧ k < 8) := by omega_arith
  have h2 : ¬12 ≤ k := by omega_arith
  simp only [pendAt, pend, h1, h2, ite_false, ite_self]

/-- The state `v` is in the registers and slots, with word `c` in `lr`, and
word `k` its register rotated right by `p k`. -/
def Holds (B : Addr) (c : Nat) (p : Nat → Nat) (v : CState) (s : State) : Prop :=
  ∀ k (hk : k < 16), if inReg c k then (s.gpr (wreg k)).rotateRight (p k) = v[k]
    else s.mem.readW (slotAddr B k) 32 = v[k]

theorem wreg_ne_r1 (k : Nat) : wreg k ≠ .r1 := by
  unfold wreg; split <;> decide

/-! ## One quarter round -/

/-- The side conditions of `quarter_ok`, decidable for concrete arguments:
the four words are in different registers, which hold no other word, the
first and third are not rotated and the second and fourth are by `br` and
`dr`, and the quarter round takes the rotations of the columns below `n` to
those of the columns below `n'`. -/
def QSide (c n n' br dr x y z w : Nat) : Bool :=
  inReg c x && inReg c y && inReg c z && inReg c w && [x, y, z, w].Nodup &&
  [wreg x, wreg y, wreg z, wreg w].Nodup &&
  ((List.range 16).all fun k => [x, y, z, w].contains k || !inReg c k ||
    !([wreg x, wreg y, wreg z, wreg w].contains (wreg k))) &&
  pendAt n x == 0 && pendAt n y == br && pendAt n z == 0 && pendAt n w == dr && decide (br < 32) &&
  decide (dr < 32) &&
  (List.range 16).all fun k => pendAt n' k == if w = k then 24 else if y = k then 25 else pendAt n k

theorem quarter_ok {c n n' br dr x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16) (hw : w < 16)
    (hq : QSide c n n' br dr x y z w = true) {B : Addr} {v : CState} {s : State}
    (h : Holds B c (pendAt n) v s) :
    WP isa (quarter x y z w br dr) s fun s' =>
      Holds B c (pendAt n') (qround v ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s' ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .r1 = s.gpr .r1 := by
  simp only [QSide, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq] at hq
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ix, iy⟩, iz⟩, iw⟩, nd⟩, nr⟩, others⟩, px⟩, py⟩, pz⟩, pw⟩, hbr⟩, hdr⟩, pn⟩ := hq
  have nd' : (x ≠ y ∧ x ≠ z ∧ x ≠ w) ∧ (y ≠ z ∧ y ≠ w) ∧ z ≠ w := by simpa using nd
  have nr' : (wreg x ≠ wreg y ∧ wreg x ≠ wreg z ∧ wreg x ≠ wreg w) ∧
      (wreg y ≠ wreg z ∧ wreg y ≠ wreg w) ∧ wreg z ≠ wreg w := by simpa using nr
  obtain ⟨⟨nxy, nxz, nxw⟩, ⟨nyz, nyw⟩, nzw⟩ := nd'
  obtain ⟨⟨rxy, rxz, rxw⟩, ⟨ryz, ryw⟩, rzw⟩ := nr'
  have gx := h x hx; have gy := h y hy; have gz := h z hz; have gw := h w hw
  simp only [ix, iy, iz, iw, ite_true, px, py, pz, pw, rotr_zero] at gx gy gz gw
  refine WP.mono (qr_ok rxy rxz rxw ryz ryw rzw hbr hdr s)
    fun s' ⟨ha, hb, hc, hd, hr, hm, hrd, hwr⟩ => ⟨fun k hk => ?_, hm, hrd, hwr,
      hr _ (wreg_ne_r1 x).symm (wreg_ne_r1 y).symm (wreg_ne_r1 z).symm (wreg_ne_r1 w).symm⟩
  rw [gx, gy, gz, gw] at ha hb hc hd
  rw [qround_get _ _ _ _ _ k hk, pn k hk]
  simp only
  by_cases ew : w = k
  · subst ew; simp only [iw, ite_true]; exact hd
  by_cases ez : z = k
  · subst ez; simp only [iz, ite_true, ew, ite_false, nyz, pz, rotr_zero]; exact hc
  by_cases ey : y = k
  · subst ey; simp only [iy, ite_true, ew, ez, ite_false]; exact hb
  by_cases ex : x = k
  · subst ex; simp only [ix, ite_true, ew, ez, ey, ite_false, px, rotr_zero]; exact ha
  simp only [ew, ez, ey, ex, ite_false]
  have hk' := h k hk
  have ho := others k hk
  split
  · rename_i hin
    simp only [hin, ite_true] at hk'
    have ho' : wreg k ≠ wreg x ∧ wreg k ≠ wreg y ∧ wreg k ≠ wreg z ∧ wreg k ≠ wreg w := by
      simpa [Ne.symm ex, Ne.symm ey, Ne.symm ez, Ne.symm ew, hin] using ho
    rw [hr _ ho'.1 ho'.2.1 ho'.2.2.1 ho'.2.2.2]; exact hk'
  · rename_i hin
    simp only [hin] at hk'
    rw [hm]; exact hk'

/-! ## Swapping the third-row word in `lr` -/

/-- The four home slots. -/
abbrev slotR (B : Addr) : Region := ⟨B + BitVec.ofNat 64 64, 16⟩

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem slot_in_slotR (B : Addr) {k : Nat} (h8 : 8 ≤ k) (h11 : k ≤ 11) :
    (slotR B).Contains (slotAddr B k) 4 := Offset.contains B (by unfold slotOff; omega_arith) (by unfold slotOff; omega_arith) (by lit_omega)

theorem slot_sep (B : Addr) {j k : Nat} (hj8 : 8 ≤ j) (hj : j ≤ 11) (hk8 : 8 ≤ k) (hk : k ≤ 11)
    (h : j ≠ k) : Mem.Sep (slotAddr B j) 4 (slotAddr B k) 4 := Offset.sep B (by unfold slotOff; omega_arith) (by unfold slotOff; omega_arith) (by unfold slotOff; omega_arith)

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (B : Addr) (c n : Nat) (v : CState) (s₀ s : State) : Prop where
  holds : Holds B c (pendAt n) v s
  frame : Frame [slotR B] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r1 : s.gpr .r1 = s₀.gpr .r1

theorem quarter_step {c n n' br dr x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16)
    (hw : w < 16) (hq : QSide c n n' br dr x y z w = true) {B : Addr} {v : CState} {s₀ s : State}
    (h : RI B c n v s₀ s) :
    WP isa (quarter x y z w br dr) s (RI B c n' (qround v ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s₀) :=
  WP.mono (quarter_ok hx hy hz hw hq h.holds) fun _ ⟨hh, hm, hrd, hwr, hr1⟩ =>
    ⟨hh, hm ▸ h.frame, hrd.trans h.rd, hwr.trans h.wr, hr1.trans h.r1⟩

theorem swap_step {i j n : Nat} (hi8 : 8 ≤ i) (hi : i ≤ 11) (hj8 : 8 ≤ j) (hj : j ≤ 11) (hij : i ≠ j)
    {B : Addr} {v : CState} {s₀ s : State} (h : RI B i n v s₀ s)
    (haddr : ∀ off, off < 256 → State.addr (s₀.gpr .r1 + BitVec.ofNat 32 off) = B + BitVec.ofNat 64 off)
    (hw : (⟨B, 256⟩ : Region) ∈ s₀.wr) :
    WP isa (swap i j) s (RI B j n v s₀) := by
  have ea : ∀ off, off < 256 → State.addr (s.gpr .r1 + BitVec.ofNat 32 off) = B + BitVec.ofNat 64 off :=
    fun off ho => by rw [h.r1]; exact haddr off ho
  have cb : ∀ k, 8 ≤ k → k ≤ 11 → (⟨B, 256⟩ : Region).Contains (slotAddr B k) 4 := fun k h1 h2 => by
    simp only [slotAddr, slotOff]
    exact Offset.contains_base B (by lit_omega) (by lit_omega)
  have hout : InRegions s.wr (slotAddr B i) 4 := ⟨_, h.wr ▸ hw, cb i hi8 hi⟩
  have hin : InRegions (s.rd ++ s.wr) (slotAddr B j) 4 :=
    ⟨_, List.mem_append_right _ (h.wr ▸ hw), cb j hj8 hj⟩
  have hi' : inReg i i = true := by simp [inReg]
  have hl := h.holds i (by lit_omega)
  simp only [hi', ite_true, pendAt_c n hi8 hi, rotr_zero] at hl
  have hj' : inReg i j = false := by simp [inReg, hij.symm]; omega_arith
  have hv := h.holds j (by lit_omega)
  simp only [hj'] at hv
  have wlr : ∀ i < 12, 8 ≤ i → wreg i = .lr := by decide
  have wi : wreg i = .lr := wlr i (by lit_omega) hi8
  have wj : wreg j = .lr := wlr j (by lit_omega) hj8
  rw [wi] at hl
  apply WP.of_runBlock
  simp only [runBlock_cons, isa]
  rw [exec_str (by simp only [slotOff]; omega_arith) (by rw [ea _ (by simp only [slotOff]; omega_arith)]; exact hout)]
  simp only [runStep_some, runBlock_cons]
  rw [exec_ldr (by simp only [slotOff]; omega_arith)
    (by show InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 (slotOff j))) 4
        rw [ea _ (by simp only [slotOff]; omega_arith)]; exact hin)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', ea _ (show slotOff i < 256 by
    simp only [slotOff]; omega_arith), ea _ (show slotOff j < 256 by simp only [slotOff]; omega_arith)]
  rw [Mem.readW_writeW_sep (slot_sep B hj8 hj hi8 hi (Ne.symm hij)) (by decide)]
  refine ⟨fun k hk => ?_, ?_, h.rd, h.wr, ?_⟩
  · have hk' := h.holds k hk
    by_cases hkj : k = j
    · subst hkj
      simp only [inReg, beq_self_eq_true, Bool.or_true, ite_true, State.setReg, wj, pendAt_c n hj8 hj,
        rotr_zero]
      simpa [slotAddr] using hv
    by_cases hki : k = i
    · subst hki
      have : inReg j k = false := by simp [inReg, hij]; omega_arith
      simp only [this, Bool.false_eq_true, ite_false, State.setReg, slotAddr,
        Mem.readW_writeW_self32]
      exact hl
    · by_cases h811 : 8 ≤ k ∧ k ≤ 11
      · have e1 : inReg j k = false := by simp [inReg, hkj]; omega_arith
        have e2 : inReg i k = false := by simp [inReg, hki]; omega_arith
        simp only [e1, e2, Bool.false_eq_true, ite_false, State.setReg] at hk' ⊢
        rw [Mem.readW_writeW_sep (slot_sep B h811.1 h811.2 hi8 hi hki) (by decide)]; exact hk'
      · have e1 : inReg j k = true := by simp [inReg]; omega_arith
        have e2 : inReg i k = true := by simp [inReg]; omega_arith
        have ne : wreg k ≠ .lr :=
          (show ∀ k < 16, ¬(8 ≤ k ∧ k ≤ 11) → wreg k ≠ .lr by decide) k hk h811
        simp only [e1, e2, ite_true, State.setReg, ne, ite_false] at hk' ⊢; exact hk'
  · exact h.frame.writeW (List.mem_singleton_self _) _ (slot_in_slotR B hi8 hi)
  · simp only [State.setReg, show Reg.r1 ≠ Reg.lr by decide, ite_false]; exact h.r1

/-! ## Double rounds -/

section
variable {B : Addr} {s₀ : State}
  (haddr : ∀ off, off < 256 → State.addr (s₀.gpr .r1 + BitVec.ofNat 32 off) = B + BitVec.ofNat 64 off)
  (hw : (⟨B, 256⟩ : Region) ∈ s₀.wr)
include haddr hw

/-- A column round, from the rotations of the columns below `n₀`; each
quarter round takes them to those of the columns below the next `n`. -/
theorem columns_ok {n₀ n₁ n₂ n₃ n₄ br dr : Nat} (q₀ : QSide 8 n₀ n₁ br dr 0 4 8 12 = true)
    (q₁ : QSide 9 n₁ n₂ br dr 1 5 9 13 = true) (q₂ : QSide 10 n₂ n₃ br dr 2 6 10 14 = true)
    (q₃ : QSide 11 n₃ n₄ br dr 3 7 11 15 = true) {v : CState} {s : State} (h : RI B 8 n₀ v s₀ s) :
    WP isa (columns br dr) s
      (RI B 11 n₄ (qround (qround (qround (qround v 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15) s₀) := by
  unfold columns
  refine WP.seq (WP.mono (quarter_step (by decide) (by decide) (by decide) (by decide) q₀ h)
    fun _ h1 => ?_)
  refine WP.seq (WP.mono (swap_step (i := 8) (j := 9) (by lit_omega) (by lit_omega) (by lit_omega)
    (by lit_omega) (by lit_omega) h1 haddr hw) fun _ h2 => ?_)
  refine WP.seq (WP.mono (quarter_step (by decide) (by decide) (by decide) (by decide) q₁ h2)
    fun _ h3 => ?_)
  refine WP.seq (WP.mono (swap_step (i := 9) (j := 10) (by lit_omega) (by lit_omega) (by lit_omega)
    (by lit_omega) (by lit_omega) h3 haddr hw) fun _ h4 => ?_)
  refine WP.seq (WP.mono (quarter_step (by decide) (by decide) (by decide) (by decide) q₂ h4)
    fun _ h5 => ?_)
  refine WP.seq (WP.mono (swap_step (i := 10) (j := 11) (by lit_omega) (by lit_omega) (by lit_omega)
    (by lit_omega) (by lit_omega) h5 haddr hw) fun _ h6 => ?_)
  exact quarter_step (by decide) (by decide) (by decide) (by decide) q₃ h6

theorem diagonals_ok {v : CState} {s : State} (h : RI B 11 4 v s₀ s) :
    WP isa diagonals s
      (RI B 8 4 (qround (qround (qround (qround v 1 6 11 12) 0 5 10 15) 3 4 9 14) 2 7 8 13) s₀) := by
  unfold diagonals
  refine WP.seq (WP.mono (quarter_step (n' := 4) (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h) fun _ h1 => ?_)
  refine WP.seq (WP.mono (swap_step (i := 11) (j := 10) (by lit_omega) (by lit_omega) (by lit_omega)
    (by lit_omega) (by lit_omega) h1 haddr hw) fun _ h2 => ?_)
  refine WP.seq (WP.mono (quarter_step (n' := 4) (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h2) fun _ h3 => ?_)
  refine WP.seq (WP.mono (swap_step (i := 10) (j := 9) (by lit_omega) (by lit_omega) (by lit_omega)
    (by lit_omega) (by lit_omega) h3 haddr hw) fun _ h4 => ?_)
  refine WP.seq (WP.mono (quarter_step (n' := 4) (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h4) fun _ h5 => ?_)
  refine WP.seq (WP.mono (swap_step (i := 9) (j := 8) (by lit_omega) (by lit_omega) (by lit_omega)
    (by lit_omega) (by lit_omega) h5 haddr hw) fun _ h6 => ?_)
  exact quarter_step (n' := 4) (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide) (by decide)
    (by decide) (by decide) h6

theorem doubleRound_ok {n₀ n₁ n₂ n₃ br dr : Nat} (q₀ : QSide 8 n₀ n₁ br dr 0 4 8 12 = true)
    (q₁ : QSide 9 n₁ n₂ br dr 1 5 9 13 = true) (q₂ : QSide 10 n₂ n₃ br dr 2 6 10 14 = true)
    (q₃ : QSide 11 n₃ 4 br dr 3 7 11 15 = true) {v : CState} {s : State} (h : RI B 8 n₀ v s₀ s) :
    WP isa (doubleRound br dr) s (RI B 8 4 (innerBlock v) s₀) := by
  rw [innerBlock_eq]
  exact WP.seq (WP.mono (columns_ok haddr hw q₀ q₁ q₂ q₃ h) fun _ h' => diagonals_ok haddr hw h')

theorem rounds_ok {v : CState} {s : State} (h : RI B 8 4 v s₀ s) :
    ∀ n, WP isa (rounds n) s (RI B 8 4 (Nat.repeat innerBlock n v) s₀)
  | 0 => WP.block_nil h
  | n + 1 => WP.seq (WP.mono (rounds_ok h n) fun _ h' =>
      doubleRound_ok haddr hw (n₁ := 4) (n₂ := 4) (n₃ := 4) (by decide) (by decide) (by decide)
        (by decide) h')

end

end VG.Proof.ChaCha20.Arm

end

/-!
# ChaCha20 block function on 32-bit ARM: the whole function
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20 VG.Arm

/-- 32-bit ARM contract for `vg_chacha20_block(state: *const [u32; 16], buf:
*mut [u32; 64])`: writes `block` of the state at `state` to the first 16 words
of `buf`.

The same function and Rust signature on every target: the code may
read `state` (64 bytes) and read and write `buf` (256 bytes; its first 64
bytes hold the result on exit, and the rest is scratch space whose contents
on exit are unspecified). `buf` may not overlap `state`, and neither may wrap
around the end of the (32-bit) address space. The pointers are public; the
state (key, counter and nonce) is secret. -/
def blockArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 64⟩
    let buf : Region := ⟨State.addr (s.gpr .r1), 256⟩
    s.rd = [state] ∧ s.wr = [buf] ∧ buf.Disjoint state ∧
    (s.gpr .r0).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 256 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem (State.addr (s.gpr .r1)) = block (stateAt s.mem (State.addr (s.gpr .r0)))
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.Arm

open VG VG.Arm VG.Impl.ChaCha20.Arm VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word stateAt innerBlock)

/-! ## Offsets -/

theorem contains_off {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem off_sep (p : Addr) {d e n k : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (hn : n ≤ 8)
    (hk : k ≤ 8) (h : d + n ≤ e ∨ e + k ≤ d) :
    Mem.Sep (p + BitVec.ofNat 64 d) n (p + BitVec.ofNat 64 e) k :=
  Offset.sep p h (by lit_omega) (by lit_omega)

/-- Reading a 32-bit word after writing one elsewhere in `buf`. -/
theorem readW_writeW_off (m : Mem) (p : Addr) (v : Word) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 32 =
      m.readW (p + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (off_sep p hd he (by lit_omega) (by lit_omega) h) (by decide)

/-- A sub-range `[a, a + len)` of `buf` contains `[d, d + n)`. -/
theorem contains_sub (p : Addr) {a len d n : Nat} (h1 : a ≤ d) (h2 : d + n ≤ a + len)
    (h3 : a + len < 2 ^ 32) :
    (⟨p + BitVec.ofNat 64 a, len⟩ : Region).Contains (p + BitVec.ofNat 64 d) n :=
  Offset.contains p h1 h2 (by lit_omega)

theorem sub_buf (p : Addr) {a len : Nat} (h : a + len ≤ 256) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, len⟩ ⟨p, 256⟩ :=
  Offset.sub_base p h

/-- Everything in `buf` but what the prologue stores: the output and the slots. -/
abbrev workR (p : Addr) : Region := ⟨p + BitVec.ofNat 64 0, 80⟩

theorem sub_work (p : Addr) {a len : Nat} (h : a + len ≤ 80) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, len⟩ (workR p) := Offset.sub p (by lit_omega) (by lit_omega)

theorem frame_work {p : Addr} {a len : Nat} (h : a + len ≤ 80) {m m' : Mem}
    (hf : Frame [⟨p + BitVec.ofNat 64 a, len⟩] m m') : Frame [workR p] m m' :=
  hf.sub fun r hr => ⟨workR p, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact sub_work p h⟩

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev st : BitVec 32 := s₀.gpr .r0
abbrev buf : BitVec 32 := s₀.gpr .r1
/-- The 64-bit addresses of `state` and `buf`. -/
abbrev SA : Addr := State.addr (st s₀)
abbrev BA : Addr := State.addr (buf s₀)
abbrev stR : Region := ⟨SA s₀, 64⟩
abbrev bufR : Region := ⟨BA s₀, 256⟩
/-- The input state. -/
abbrev V : CState := stateAt s₀.mem (SA s₀)
/-- The result of the rounds. -/
abbrev Rs : CState := Nat.repeat innerBlock 10 (V s₀)
end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [stR s₀]
  wr : s₀.wr = [bufR s₀]
  buf_st : (bufR s₀).Disjoint (stR s₀)
  st_fits : (st s₀).toNat + 64 ≤ 2 ^ 32
  buf_fits : (buf s₀).toNat + 256 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.ChaCha20.blockArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem eaB {off : Nat} (h : off < 256) :
    State.addr (buf s₀ + BitVec.ofNat 32 off) = BA s₀ + BitVec.ofNat 64 off :=
  addr_add (by have := hp.buf_fits; omega_arith)

theorem eaS {off : Nat} (h : off < 64) :
    State.addr (st s₀ + BitVec.ofNat 32 off) = SA s₀ + BitVec.ofNat 64 off :=
  addr_add (by have := hp.st_fits; omega_arith)

theorem hw : bufR s₀ ∈ s₀.wr := by simp [hp.wr]

theorem in_buf {d n : Nat} (h : d + n ≤ 256) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (BA s₀ + BitVec.ofNat 64 d) n :=
  ⟨bufR s₀, by simp [hp.wr], contains_off (by lit_omega) (by lit_omega)⟩

theorem out_buf {d n : Nat} (h : d + n ≤ 256) : InRegions s₀.wr (BA s₀ + BitVec.ofNat 64 d) n :=
  ⟨bufR s₀, by simp [hp.wr], contains_off (by lit_omega) (by lit_omega)⟩

theorem in_st {k : Nat} (hk : k < 16) (ws : List Region) :
    InRegions (s₀.rd ++ ws) (SA s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [hp.rd], contains_off (by lit_omega) (by lit_omega)⟩

/-- Reading the input state after writes to `buf` only. -/
theorem read_st {m : Mem} (hf : Frame [bufR s₀] s₀.mem m) {k : Nat} (hk : k < 16) :
    m.readW (SA s₀ + BitVec.ofNat 64 (4 * k)) 32 = (V s₀)[k] := by
  rw [hf.readW (r := stR s₀) (contains_off (by lit_omega) (by lit_omega)) (by simpa using hp.buf_st.symm)
    (by decide)]
  simp only [V, stateAt, Vector.getElem_ofFn]

end Pre

theorem out_lt {k : Nat} (hk : k < 16) : outOff k + 4 ≤ 256 := by simp only [outOff]; omega_arith

/-! ## Saving and restoring the callee-saved registers, and `state` -/

/-- The memory after the prologue's stores. -/
def saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (BA s₀) s₀.gpr kept

/-- The callee-saved registers and `state` are saved in `buf`. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (BA s₀) s₀.gpr kept

theorem kept_slots : Spill.Slots 80 120 kept := by decide

theorem saved_slots : Spill.Slots 80 116 saved := by decide

theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block save) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ := by
  rw [save, ← List.append_nil (kept.map _)]
  exact Spill.save_slots_ok kept_slots (Nat.le_trans (Nat.add_le_add_left (by decide : 120 ≤ 256) _) hp.buf_fits)
    (fun _ _ hd => hp.out_buf (by omega_arith)) (WP.block_nil ⟨rfl, rfl, rfl, rfl⟩)

theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := Spill.saveMem_saved _ _ _ _ kept_slots

theorem saveMem_frame (s₀ : State) : Frame [bufR s₀] s₀.mem (saveMem s₀) :=
  Spill.saveMem_frame _ _ _ (by decide) kept (by decide)

theorem saved_frame {s₀ : State} {m m' : Mem} (h : Saved s₀ m) (hf : Frame [workR (BA s₀)] m m') :
    Saved s₀ m' :=
  h.frame kept_slots hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)

/-- `state`, from where the prologue stored it. -/
theorem Saved.ptr {s₀ : State} {m : Mem} (h : Saved s₀ m) :
    m.readW (BA s₀ + BitVec.ofNat 64 ptrOff) 32 = st s₀ :=
  h (.r0, ptrOff) (by decide)

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hs : Saved s₀ s.mem)
    (hr1 : s.gpr .r1 = buf s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block restore) s fun s' =>
      s'.mem = s.mem ∧ ∀ r ∈ preserved, s'.gpr r = s₀.gpr r := by
  rw [restore, ← List.append_nil (saved.map _)]
  refine Spill.restore_slots_ok saved_slots (by decide) (g := s₀.gpr)
    (by rw [hr1]; exact Nat.le_trans (Nat.add_le_add_left (by decide : 116 ≤ 256) _) hp.buf_fits)
    (fun _ _ hd => by rw [hwr, hr1]; exact hp.in_buf (by omega_arith) _)
    (by rw [hr1]; exact fun p hp' => hs p (List.mem_append_left _ hp'))
    fun s' ho _ hm _ _ _ => WP.block_nil ⟨hm, Spill.restored_of ho (by decide)⟩

/-! ## Loading the registers -/

theorem lo_lt {i : Nat} (hi : i < 16) : loadOrder i < 16 :=
  (by decide : ∀ i < 16, loadOrder i < 16) i hi

/-- After loading the first `n` words of `loadOrder`, relative to the state
`s₁` after the prologue's stores. -/
structure LI (s₀ s₁ : State) (n : Nat) (s : State) : Prop where
  loaded : ∀ i (hi : i < 16), i < n →
    if inReg 8 (loadOrder i) then s.gpr (wreg (loadOrder i)) = (V s₀)[loadOrder i]'(lo_lt hi)
    else s.mem.readW (slotAddr (BA s₀) (loadOrder i)) 32 = (V s₀)[loadOrder i]'(lo_lt hi)
  r0 : n < 16 → s.gpr .r0 = st s₀
  r1 : s.gpr .r1 = buf s₀
  frame : Frame [slotR (BA s₀)] s₁.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem slotR_sub (s₀ : State) : Region.Sub (slotR (BA s₀)) (bufR s₀) := sub_buf _ (by decide)

theorem load_step {s₀ s₁ : State} (hp : Pre s₀) (hf₁ : Frame [bufR s₀] s₀.mem s₁.mem) {n : Nat}
    (hn : n < 16) {s : State} (h : LI s₀ s₁ n s) :
    WP isa (.block (loadWord (loadOrder n))) s (LI s₀ s₁ (n + 1)) := by
  have hk := lo_lt hn
  have hfs : Frame [bufR s₀] s₀.mem s.mem :=
    hf₁.trans (h.frame.sub fun r hr => ⟨bufR s₀, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact slotR_sub s₀⟩)
  have hx : s.mem.readW (SA s₀ + BitVec.ofNat 64 (4 * loadOrder n)) 32 = (V s₀)[loadOrder n] :=
    hp.read_st hfs hk
  have e0 := hp.eaS (show 4 * loadOrder n < 64 by omega_arith)
  have h4 : 4 * loadOrder n < 4096 := by omega_arith
  have hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * loadOrder n))) 4 := by
    rw [h.r0 hn, e0, h.rd]; exact hp.in_st hk _
  have hw : bufR s₀ ∈ s.wr := h.wr ▸ hp.hw
  suffices key : ∀ s' : State, (∀ r, r ≠ wreg (loadOrder n) → s'.gpr r = s.gpr r) →
      s'.gpr (wreg (loadOrder n)) = (V s₀)[loadOrder n] →
      (s'.mem = if 9 ≤ loadOrder n ∧ loadOrder n ≤ 11 then
        s.mem.writeW (slotAddr (BA s₀) (loadOrder n)) (V s₀)[loadOrder n] else s.mem) →
      s'.rd = s.rd → s'.wr = s.wr → LI s₀ s₁ (n + 1) s' by
    apply WP.of_runBlock
    by_cases h911 : 9 ≤ loadOrder n ∧ loadOrder n ≤ 11
    · have wk : wreg (loadOrder n) = .lr :=
        (by decide : ∀ k < 16, 9 ≤ k ∧ k ≤ 11 → wreg k = .lr) _ hk h911
      have es := hp.eaB (show slotOff (loadOrder n) < 256 by simp only [slotOff]; omega_arith)
      have o : InRegions s.wr (BA s₀ + BitVec.ofNat 64 (slotOff (loadOrder n))) 4 :=
        ⟨bufR s₀, hw, contains_off (by simp only [slotOff]; omega_arith) (by simp only [slotOff]; omega_arith)⟩
      have h5 : slotOff (loadOrder n) < 4096 := by simp only [slotOff]; omega_arith
      simp only [loadWord, h911, and_self, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, isa,
        exec_ldr h4 hin, reduceExec, h5, State.store32, RegUpd.gpr_setReg_self, RegUpd.wr_setReg,
        RegUpd.gpr_setReg_of_ne _ _ (wreg_ne_r1 (loadOrder n)).symm,
        h.r1, es, o, Option.some.injEq, exists_eq_left', h.r0 hn, e0, hx]
      exact key _ (fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr) (RegUpd.gpr_setReg_self _ _ _)
        (by simp only [h911, and_self, ↓reduceIte, RegUpd.mem_setReg]) rfl rfl
    · simp only [loadWord, h911, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, isa,
        exec_ldr h4 hin, Option.some.injEq, exists_eq_left', h.r0 hn, e0, hx]
      exact key _ (fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr) (RegUpd.gpr_setReg_self _ _ _)
        (by simp only [h911, ↓reduceIte, RegUpd.mem_setReg]) rfl rfl
  intro s' hg hgk hm hrd hwr
  have inj : ∀ i, i < n → loadOrder i ≠ loadOrder n := fun i hi =>
    (by decide : ∀ n < 16, ∀ i < n, loadOrder i ≠ loadOrder n) n hn i hi
  have slot_of : ∀ k, k < 16 → inReg 8 k = false → 9 ≤ k ∧ k ≤ 11 := by decide
  refine ⟨fun i hi hin' => ?_, fun hn' => ?_, ?_, ?_, hrd.trans h.rd, hwr.trans h.wr⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hin' with hlt | rfl
    · have old := h.loaded i hi hlt
      split
      · rename_i hr
        simp only [hr, ↓reduceIte] at old
        rw [hg _ ((by decide : ∀ n < 16, ∀ i < n, inReg 8 (loadOrder i) = true →
          wreg (loadOrder i) ≠ wreg (loadOrder n)) n hn i hlt hr)]
        exact old
      · rename_i hr
        simp only [hr] at old
        have hi9 := slot_of _ (lo_lt hi) (by simpa using hr)
        rw [hm]
        split
        · rename_i h911
          rw [Mem.readW_writeW_sep (slot_sep _ (by omega_arith) hi9.2 (by omega_arith) h911.2 (inj i hlt))
            (by decide)]
          exact old
        · exact old
    · split
      · exact hgk
      · rename_i hr
        have h911 := slot_of _ hk (by simpa using hr)
        simp only [hm, h911, and_self, ↓reduceIte, Mem.readW_writeW_self32]
  · rw [hg _ ((by decide : ∀ n < 15, Reg.r0 ≠ wreg (loadOrder n)) n (by omega_arith))]
    exact h.r0 hn
  · rw [hg _ (wreg_ne_r1 _).symm]; exact h.r1
  · rw [hm]
    split
    · rename_i h911
      exact h.frame.writeW (List.mem_singleton_self _) _ (slot_in_slotR _ (by omega_arith) h911.2)
    · exact h.frame

theorem lo_surj {k : Nat} (hk : k < 16) : ∃ i, i < 16 ∧ loadOrder i = k :=
  (by decide : ∀ k < 16, ∃ i, i < 16 ∧ loadOrder i = k) k hk

theorem load_ok {s₀ s₁ : State} (hp : Pre s₀) (h₁ : s₁.gpr = s₀.gpr) (hrd₁ : s₁.rd = s₀.rd)
    (hwr₁ : s₁.wr = s₀.wr) (hf₁ : Frame [bufR s₀] s₀.mem s₁.mem) :
    WP isa (.block load) s₁ fun s' =>
      Holds (BA s₀) 8 (pendAt 0) (V s₀) s' ∧ Frame [slotR (BA s₀)] s₁.mem s'.mem ∧ s'.rd = s₀.rd ∧
      s'.wr = s₀.wr ∧ s'.gpr .r1 = buf s₀ := by
  have h0 : LI s₀ s₁ 0 s₁ :=
    ⟨fun _ _ h => absurd h (by lit_omega), fun _ => by rw [h₁], by rw [h₁], Frame.refl _ _, hrd₁, hwr₁⟩
  have hl : WP isa (.block load) s₁ (LI s₀ s₁ 16) := by
    unfold load
    exact wp_range_flatMap (M := isa) (LI s₀ s₁) (fun k s' hk h => load_step hp hf₁ hk h) 16
      (Nat.le_refl _) s₁ h0
  refine WP.mono hl fun s' h => ⟨fun k hk => ?_, h.frame, h.rd, h.wr, h.r1⟩
  obtain ⟨i, hi, rfl⟩ := lo_surj hk
  have := h.loaded i hi hi
  simp only [pendAt, Nat.not_lt_zero, ↓reduceIte, rotr_zero]
  exact this

/-! ## Adding the input state -/

theorem ao_lt {i : Nat} (hi : i < 16) : addOrder i < 16 :=
  (by decide : ∀ i < 16, addOrder i < 16) i hi

theorem ao_surj {k : Nat} (hk : k < 16) : ∃ i, i < 16 ∧ addOrder i = k :=
  (by decide : ∀ k < 16, ∃ i, i < 16 ∧ addOrder i = k) k hk

theorem reg_eval (r : Reg) (s : State) : (Op2.reg r).eval s = some (s.gpr r) := rfl

/-- After adding the first `n` words of `addOrder`, relative to the state
`sB` before them: those words of the output are the block's, and the others
of the rounds' result `R` are where they were, in memory (`inMem`) or in
their registers. -/
structure AI (s₀ : State) (R : CState) (sB : State) (n : Nat) (s : State) : Prop where
  out : ∀ i (hi : i < 16), i < n →
    s.mem.readW (BA s₀ + BitVec.ofNat 64 (outOff (addOrder i))) 32 =
      R[addOrder i]'(ao_lt hi) + (V s₀)[addOrder i]'(ao_lt hi)
  rest : ∀ i (hi : i < 16), n ≤ i →
    if inMem (addOrder i) then
      s.mem.readW (BA s₀ + BitVec.ofNat 64 (rawOff (addOrder i))) 32 = R[addOrder i]'(ao_lt hi)
    else (s.gpr (wreg (addOrder i))).rotateRight (pend (addOrder i)) = R[addOrder i]'(ao_lt hi)
  frame : Frame [workR (BA s₀)] sB.mem s.mem
  lr : s.gpr .lr = st s₀
  r1 : s.gpr .r1 = buf s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem workR_sub (s₀ : State) : Region.Sub (workR (BA s₀)) (bufR s₀) := sub_buf _ (by decide)

theorem add_step {s₀ : State} (hp : Pre s₀) {R : CState} {sB : State}
    (hfB : Frame [bufR s₀] s₀.mem sB.mem) {n : Nat} (hn : n < 16) {s : State} (hs : AI s₀ R sB n s) :
    WP isa (.block (addWord (addOrder n))) s (AI s₀ R sB (n + 1)) := by
  have hk := ao_lt hn
  have hfs : Frame [bufR s₀] s₀.mem s.mem :=
    hfB.trans (hs.frame.sub fun r hr => ⟨bufR s₀, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact workR_sub s₀⟩)
  have hx : s.mem.readW (SA s₀ + BitVec.ofNat 64 (4 * addOrder n)) 32 = (V s₀)[addOrder n] :=
    hp.read_st hfs hk
  have e0 := hp.eaS (show 4 * addOrder n < 64 by omega_arith)
  have eo := hp.eaB (show outOff (addOrder n) < 256 by simp only [outOff]; omega_arith)
  have h4 : 4 * addOrder n < 4096 := by omega_arith
  have h5 : outOff (addOrder n) < 4096 := by simp only [outOff]; omega_arith
  have hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 (4 * addOrder n))) 4 := by
    rw [hs.lr, e0, hs.rd]; exact hp.in_st hk _
  have hw : bufR s₀ ∈ s.wr := hs.wr ▸ hp.hw
  have o : InRegions s.wr (BA s₀ + BitVec.ofNat 64 (outOff (addOrder n))) 4 :=
    ⟨bufR s₀, hw, contains_off (out_lt hk) (by simp only [outOff]; omega_arith)⟩
  have old := hs.rest n hn (Nat.le_refl _)
  suffices key : ∀ s' : State,
      s'.mem = s.mem.writeW (BA s₀ + BitVec.ofNat 64 (outOff (addOrder n)))
        (R[addOrder n] + (V s₀)[addOrder n]) →
      (∀ i, n < i → i < 16 → inMem (addOrder i) = false →
        s'.gpr (wreg (addOrder i)) = s.gpr (wreg (addOrder i))) →
      s'.gpr .lr = s.gpr .lr → s'.gpr .r1 = s.gpr .r1 → s'.rd = s.rd → s'.wr = s.wr →
      AI s₀ R sB (n + 1) s' by
    apply WP.of_runBlock
    by_cases hm : inMem (addOrder n) = true
    · simp only [hm, ↓reduceIte] at old
      have h6 : rawOff (addOrder n) < 256 :=
        (by decide : ∀ k < 16, inMem k = true → rawOff k < 256) _ hk hm
      have er := hp.eaB h6
      have ir : InRegions (s.rd ++ s.wr) (BA s₀ + BitVec.ofNat 64 (rawOff (addOrder n))) 4 :=
        ⟨bufR s₀, List.mem_append_right _ hw, contains_off
          ((by decide : ∀ k < 16, inMem k = true → rawOff k + 4 ≤ 256) _ hk hm) (by omega_arith)⟩
      have h7 : rawOff (addOrder n) < 4096 := by omega_arith
      simp only [addWord, hm, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, isa,
        exec_ldr h4 hin, reduceExec, h5, h7, State.load32, State.store32, reg_eval, Option.map_some,
        RegUpd.gpr_setReg, reduceCtorEq, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
        hs.lr, hs.r1, e0, eo, er, ir, o, hx, old, Option.some.injEq, exists_eq_left']
      exact key _ rfl (fun i hni hi hmi => absurd hmi (by
          rw [(by decide : ∀ n < 16, ∀ i < 16, n < i → inMem (addOrder n) = true →
            inMem (addOrder i) = true) n hn i hi hni hm]; decide))
        (by simp only [RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte])
        (by simp only [RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]) rfl rfl
    · have hm' : inMem (addOrder n) = false := by simpa using hm
      simp only [hm', Bool.false_eq_true, ↓reduceIte] at old
      obtain ⟨w0, wl, wp⟩ := (by decide : ∀ k < 16, inMem k = false →
        wreg k ≠ .r0 ∧ wreg k ≠ .lr ∧ pend k < 32) _ hk hm'
      have w1 := wreg_ne_r1 (addOrder n)
      simp only [addWord, hm', Bool.false_eq_true, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil,
        isa, exec_ldr h4 hin, reduceExec, h5, State.store32, rop_eval wp, Option.map_some,
        RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ w0, RegUpd.gpr_setReg_of_ne _ _ w1.symm,
        RegUpd.gpr_setReg_of_ne _ _ (show Reg.r1 ≠ Reg.r0 by decide),
        RegUpd.wr_setReg, RegUpd.mem_setReg, hs.lr, hs.r1, e0, eo, o, hx, old, Option.some.injEq,
        exists_eq_left']
      exact key _ (congrArg (s.mem.writeW _) (BitVec.add_comm _ _)) (fun i hni hi hmi => by
          have a := (by decide : ∀ n < 16, ∀ i < 16, n < i ∧ inMem (addOrder n) = false ∧
            inMem (addOrder i) = false → wreg (addOrder i) ≠ wreg (addOrder n)) n hn i hi ⟨hni, hm', hmi⟩
          have b := ((by decide : ∀ k < 16, inMem k = false →
            wreg k ≠ .r0 ∧ wreg k ≠ .lr ∧ pend k < 32) _ (ao_lt hi) hmi).1
          simp only [RegUpd.gpr_setReg_of_ne _ _ a, RegUpd.gpr_setReg_of_ne _ _ b])
        (by simp only [RegUpd.gpr_setReg_of_ne _ _ wl.symm,
          RegUpd.gpr_setReg_of_ne _ _ (show Reg.lr ≠ Reg.r0 by decide)])
        (by simp only [RegUpd.gpr_setReg_of_ne _ _ w1.symm,
          RegUpd.gpr_setReg_of_ne _ _ (show Reg.r1 ≠ Reg.r0 by decide)]) rfl rfl
  intro s' hm hg hlr hr1 hrd hwr
  refine ⟨fun i hi hin' => ?_, fun i hi hni => ?_, ?_, hlr.trans hs.lr, hr1.trans hs.r1, hrd.trans hs.rd,
    hwr.trans hs.wr⟩
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hin' with hlt | rfl
    · have ne := (by decide : ∀ n < 16, ∀ i < n, addOrder i ≠ addOrder n) n hn i hlt
      have := ao_lt hi
      rw [readW_writeW_off _ _ _ (by simp only [outOff]; omega_arith) (by simp only [outOff]; omega_arith)
        (by simp only [outOff]; omega_arith)]
      exact hs.out i hi hlt
    · exact Mem.readW_writeW_self32 _ _ _
  · have old' := hs.rest i hi (by omega_arith)
    split
    · rename_i hmi
      simp only [hmi, ↓reduceIte] at old'
      have := ao_lt hi
      rw [hm, readW_writeW_off _ _ _
        (Nat.lt_of_lt_of_le ((by decide : ∀ k < 16, inMem k = true → rawOff k < 256) _ this hmi)
          (by decide)) (by simp only [outOff]; omega_arith)
        ((by decide : ∀ n < 16, ∀ i < 16, n < i → inMem (addOrder i) = true →
          rawOff (addOrder i) + 4 ≤ outOff (addOrder n) ∨
            outOff (addOrder n) + 4 ≤ rawOff (addOrder i)) n hn i hi hni hmi)]
      exact old'
    · rename_i hmi
      simp only [hmi] at old'
      rw [hg i hni hi (by simpa using hmi)]
      exact old'
  · rw [hm]
    exact hs.frame.writeW (List.mem_singleton_self _) _
      (contains_sub _ (by lit_omega) (by simp only [outOff]; omega_arith) (by lit_omega))

theorem pendAt_four (k : Nat) : pendAt 4 k = pend k := by
  simp only [pendAt, Nat.mod_lt k (show 0 < 4 by decide), ↓reduceIte]

/-- Before the additions: word 8 goes to its slot, `state` into `lr`, and
word 0 to its place in the output. -/
theorem stash_ok {s₀ : State} (hp : Pre s₀) {R : CState} {s : State}
    (hh : Holds (BA s₀) 8 (pendAt 4) R s) (hsv : Saved s₀ s.mem) (hr1 : s.gpr .r1 = buf s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block [.str .lr .r1 (slotOff 8), .ldr .lr .r1 ptrOff, .str .r0 .r1 (outOff 0)]) s
      (AI s₀ R s 0) := by
  have hw : bufR s₀ ∈ s.wr := hwr ▸ hp.hw
  have e8 := hp.eaB (show slotOff 8 < 256 by decide)
  have ep := hp.eaB (show ptrOff < 256 by decide)
  have eo := hp.eaB (show outOff 0 < 256 by decide)
  have o8 : InRegions s.wr (BA s₀ + BitVec.ofNat 64 (slotOff 8)) 4 :=
    ⟨bufR s₀, hw, contains_off (by decide) (by decide)⟩
  have ip : InRegions (s.rd ++ s.wr) (BA s₀ + BitVec.ofNat 64 ptrOff) 4 :=
    ⟨bufR s₀, List.mem_append_right _ hw, contains_off (by decide) (by decide)⟩
  have oo : InRegions s.wr (BA s₀ + BitVec.ofNat 64 (outOff 0)) 4 :=
    ⟨bufR s₀, hw, contains_off (by decide) (by decide)⟩
  have h8 := hh 8 (by decide)
  have h0 := hh 0 (by decide)
  simp only [show inReg 8 8 = true by decide, show inReg 8 0 = true by decide, ↓reduceIte,
    show pendAt 4 8 = 0 by decide, show pendAt 4 0 = 0 by decide, rotr_zero,
    show wreg 8 = .lr from rfl, show wreg 0 = .r0 from rfl] at h8 h0
  have hptr : (s.mem.writeW (BA s₀ + BitVec.ofNat 64 (slotOff 8)) R[8]).readW
      (BA s₀ + BitVec.ofNat 64 ptrOff) 32 = st s₀ :=
    (readW_writeW_off _ _ _ (by decide) (by decide) (by decide)).trans hsv.ptr
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, show slotOff 8 < 4096 by decide,
    show ptrOff < 4096 by decide, show outOff 0 < 4096 by decide, ↓reduceIte, State.store32,
    State.load32, Option.map_some, RegUpd.gpr_setReg, reduceCtorEq, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, hr1, e8, ep, eo, o8, ip, oo, h8, h0, hptr, Option.some.injEq, exists_eq_left']
  refine ⟨fun _ _ h => absurd h (by lit_omega), fun i hi _ => ?_, ?_, ?_, ?_, hrd, hwr⟩
  · have key : ∀ j (hj : j < 16), if inMem j then
          ((s.mem.writeW (BA s₀ + BitVec.ofNat 64 (slotOff 8)) R[8]).writeW
            (BA s₀ + BitVec.ofNat 64 (outOff 0)) R[0]).readW (BA s₀ + BitVec.ofNat 64 (rawOff j)) 32 = R[j]
        else (s.gpr (wreg j)).rotateRight (pend j) = R[j] := by
      intro j hj
      have hj' := hh j hj
      rw [pendAt_four] at hj'
      rcases (by decide : ∀ j < 16, j = 0 ∨ j = 8 ∨ (9 ≤ j ∧ j ≤ 11) ∨ inMem j = false) j hj with
        rfl | rfl | h911 | hm
      · exact Mem.readW_writeW_self32 _ _ _
      · exact (readW_writeW_off _ _ _ (by decide) (by decide) (by decide)).trans
          (Mem.readW_writeW_self32 _ _ _)
      · have hm : inMem j = true := (by decide : ∀ j < 16, 9 ≤ j ∧ j ≤ 11 → inMem j = true) j hj h911
        have hr : inReg 8 j = false := (by decide : ∀ j < 16, 9 ≤ j ∧ j ≤ 11 → inReg 8 j = false) j hj h911
        have e : rawOff j = slotOff j := by
          simp only [rawOff, show ¬j = 0 by omega_arith, ↓reduceIte]
        simp only [hr, Bool.false_eq_true, ↓reduceIte, slotAddr] at hj'
        simp only [hm, ↓reduceIte, e]
        rw [readW_writeW_off _ _ _ (by simp only [slotOff]; omega_arith) (by decide)
          (by simp only [slotOff, outOff]; omega_arith),
          readW_writeW_off _ _ _ (by simp only [slotOff]; omega_arith) (by decide)
          (by simp only [slotOff]; omega_arith)]
        exact hj'
      · have hr : inReg 8 j = true := (by decide : ∀ j < 16, inMem j = false → inReg 8 j = true) j hj hm
        simp only [hr, ↓reduceIte] at hj'
        simp only [hm, Bool.false_eq_true, ↓reduceIte]
        exact hj'
    have hk := key _ (ao_lt hi)
    split
    · rename_i hm; simp only [hm, ↓reduceIte] at hk; exact hk
    · rename_i hm
      simp only [hm] at hk
      have ne : wreg (addOrder i) ≠ .lr :=
        ((by decide : ∀ k < 16, inMem k = false → wreg k ≠ .r0 ∧ wreg k ≠ .lr ∧ pend k < 32) _
          (ao_lt hi) (by simpa using hm)).2.1
      simp only [RegUpd.gpr_setReg, ne, ↓reduceIte]
      exact hk
  · exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_sub _ (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (contains_sub _ (by decide) (by decide) (by decide))
  · simp only [RegUpd.gpr_setReg, ↓reduceIte]
  · simp only [RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte, hr1]

/-! ## The whole function -/

theorem block_post {p : Addr} {m : Mem} {R v : CState}
    (h : ∀ j (hj : j < 16), m.readW (p + BitVec.ofNat 64 (outOff j)) 32 = R[j] + v[j]) :
    stateAt m p = Vector.zipWith (· + ·) R v := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_zipWith]
  exact h j hj

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa block s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.ChaCha20.blockArm.post s₀ s' := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok hp) fun s₁ ⟨hg₁, hrd₁, hwr₁, hm₁⟩ => ?_
  have hf₁ : Frame [bufR s₀] s₀.mem s₁.mem := hm₁ ▸ saveMem_frame s₀
  refine WP.mono (load_ok hp hg₁ hrd₁ hwr₁ hf₁) fun s₂ ⟨hh₂, hfr₂, hrd₂, hwr₂, hr1₂⟩ => ?_
  have haddr : ∀ off, off < 256 →
      State.addr (s₂.gpr .r1 + BitVec.ofNat 32 off) = BA s₀ + BitVec.ofNat 64 off :=
    fun off ho => by rw [hr1₂]; exact hp.eaB ho
  have hw₂ : bufR s₀ ∈ s₂.wr := by rw [hwr₂]; exact hp.hw
  refine WP.seq (WP.mono (doubleRound_ok haddr hw₂ (n₁ := 1) (n₂ := 2) (n₃ := 3) (by decide)
    (by decide) (by decide) (by decide) ⟨hh₂, Frame.refl _ _, rfl, rfl, rfl⟩) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (rounds_ok haddr hw₂ h₃ 9) fun s₄ hR => ?_)
  rw [← repeat_succ'] at hR
  have hwork : Frame [workR (BA s₀)] s₁.mem s₄.mem :=
    (frame_work (a := 64) (len := 16) (by decide) hfr₂).trans
      (frame_work (a := 64) (len := 16) (by decide) hR.frame)
  have hsv₄ : Saved s₀ s₄.mem := saved_frame (hm₁ ▸ saveMem_saved s₀) hwork
  have hfB : Frame [bufR s₀] s₀.mem s₄.mem :=
    hf₁.trans (hwork.sub fun r hr => ⟨bufR s₀, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact workR_sub s₀⟩)
  unfold finish
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (stash_ok hp hR.holds hsv₄ (hR.r1.trans hr1₂) (hR.rd.trans hrd₂) (hR.wr.trans hwr₂))
    fun s₅ hA₀ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (AI s₀ (Rs s₀) s₄)
    (fun k s hk ha => add_step hp hfB hk ha) 16 (Nat.le_refl _) s₅ hA₀) fun s₆ hA => ?_
  refine WP.mono (restore_ok hp (saved_frame hsv₄ hA.frame) hA.r1 hA.wr) fun s' ⟨hm', hg'⟩ => ⟨hg', ?_⟩
  show stateAt s'.mem (BA s₀) = Spec.ChaCha20.block (V s₀)
  rw [hm']
  exact block_post fun j hj => by obtain ⟨i, hi, rfl⟩ := ao_surj hj; exact hA.out i hi hi

theorem block_correct (s : State) (hs : Proof.ChaCha20.blockArm.pre s) :
    ∃ t s', Exec isa block s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.blockArm.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩

/-! ## Constant time -/

/-- The initial taint: the pointers are public, and `r1` points at `buf`,
where the prologue's store of `state` is then a public slot, which the
additions of the input state reload as their address. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1], flags := false, lens := [256], bases := [(.r1, 0)] }

theorem toNat_addr (p : BitVec 32) : (State.addr p).toNat = p.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := p.isLt; omega_arith)

theorem wf₀ {s : State} (h : Proof.ChaCha20.blockArm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  obtain hp := pre_of s h
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simp [hp.wr], ?_⟩, ?_, fun h => absurd h (by decide),
    fun _ h => by simp [τ₀] at h⟩
  · simp only [hp.wr, List.mem_singleton]
    rintro r rfl
    simp only [toNat_addr]
    exact hp.buf_fits
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'
    subst hp'
    simp [VG.Arm.Taint.region, hp.wr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.ChaCha20.blockArm.pre s₁)
    (h₂ : Proof.ChaCha20.blockArm.pre s₂) (hpub : Proof.ChaCha20.blockArm.pub s₁ s₂) :
    VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p0, p1⟩ := hpub
  obtain hp₁ := pre_of s₁ h₁; have hp₂ := pre_of s₂ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (by decide), fun k hk => absurd hk (by simp [τ₀])⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [bufR, BA, buf, p1]

theorem block_ct :
    ConstantTime isa Proof.ChaCha20.blockArm.pre Proof.ChaCha20.blockArm.pub Impl.ChaCha20.Arm.block :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by native_taint_decide)

end VG.Proof.ChaCha20.Arm
