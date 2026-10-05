import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.ChaCha20.StreamBytes
import VerifiedGarbage.Impl.ChaCha20.Arm
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.ChaCha20.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Impl.ChaCha20.Arm.Xor
import VerifiedGarbage.Proof.ChaCha20.Arm.Lit

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.Arm.Block`. -/
section

section

/-!
# ChaCha20 block function on 32-bit ARM: the rounds
-/

namespace VG.Proof.ChaCha20.Arm

open VG VG.Arm VG.Impl.ChaCha20.Arm VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)

theorem qr_ok {a b c d : Reg} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (s : State) (va vb vc vd : VG.Spec.ChaCha20.Word)
    (ha : s.gpr a = va) (hb : s.gpr b = vb) (hc : s.gpr c = vc) (hd : s.gpr d = vd) :
    WP isa (.block (qr a b c d)) s fun s' =>
      s'.gpr a = (quarterRound va vb vc vd).1 ∧ s'.gpr b = (quarterRound va vb vc vd).2.1 ∧
      s'.gpr c = (quarterRound va vb vc vd).2.2.1 ∧ s'.gpr d = (quarterRound va vb vc vd).2.2.2 ∧
      (∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceLeDiff, and_self, qr, runBlock_cons, runStep_some,
    runBlock_nil, exec, Op2.eval, isa, State.setReg, ha, hb,
    hc, hd, hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm,
    hcd.symm, Option.map_some, Option.some.injEq,
    exists_eq_left']
  and_intros
  all_goals first
    | simp only [quarterRound_eq]
    | (intro r h1 h2 h3 h4; simp [h1, h2, h3, h4])

/-! ## Where the words are -/

/-- Word `k` is in its register `wreg k` (rather than its slot) when the
third-row word in `lr` is `c`: always, except for the third-row words other
than `c`. -/
def inReg (c k : Nat) : Bool := !(8 ≤ k && k ≤ 11) || k == c

/-- The home slot of word `k` (8–11), relative to the 64-bit address `B` of `buf`. -/
abbrev slotAddr (B : Addr) (k : Nat) : Addr := B + BitVec.ofNat 64 (slotOff k)

/-- The state `v` is in the registers and slots, with word `c` in `lr`. -/
def Holds (B : Addr) (c : Nat) (v : CState) (s : State) : Prop :=
  ∀ k (hk : k < 16), if VG.Proof.ChaCha20.Arm.inReg c k then s.gpr (wreg k) = v[k] else s.mem.readW (VG.Proof.ChaCha20.Arm.slotAddr B k) 32 = v[k]

theorem wreg_ne_r1 (k : Nat) : wreg k ≠ .r1 := by
  unfold wreg; split <;> decide

/-! ## One quarter round -/

/-- The side conditions of `quarter_ok`, decidable for concrete arguments. -/
def QSide (c x y z w : Nat) : Bool :=
  VG.Proof.ChaCha20.Arm.inReg c x && VG.Proof.ChaCha20.Arm.inReg c y && VG.Proof.ChaCha20.Arm.inReg c z && VG.Proof.ChaCha20.Arm.inReg c w && [x, y, z, w].Nodup &&
  [wreg x, wreg y, wreg z, wreg w].Nodup &&
  (List.range 16).all fun k => [x, y, z, w].contains k || !VG.Proof.ChaCha20.Arm.inReg c k ||
    !([wreg x, wreg y, wreg z, wreg w].contains (wreg k))

theorem quarter_ok {c x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16) (hw : w < 16)
    (hq : VG.Proof.ChaCha20.Arm.QSide c x y z w = true) {B : Addr} {v : CState} {s : State} (h : VG.Proof.ChaCha20.Arm.Holds B c v s) :
    WP isa (quarter x y z w) s fun s' =>
      VG.Proof.ChaCha20.Arm.Holds B c (qround v ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s' ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .r1 = s.gpr .r1 := by
  simp only [VG.Proof.ChaCha20.Arm.QSide, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hq
  obtain ⟨⟨⟨⟨⟨⟨ix, iy⟩, iz⟩, iw⟩, nd⟩, nr⟩, others⟩ := hq
  have nd' : (x ≠ y ∧ x ≠ z ∧ x ≠ w) ∧ (y ≠ z ∧ y ≠ w) ∧ z ≠ w := by simpa using nd
  have nr' : (wreg x ≠ wreg y ∧ wreg x ≠ wreg z ∧ wreg x ≠ wreg w) ∧
      (wreg y ≠ wreg z ∧ wreg y ≠ wreg w) ∧ wreg z ≠ wreg w := by simpa using nr
  obtain ⟨⟨nxy, nxz, nxw⟩, ⟨nyz, nyw⟩, nzw⟩ := nd'
  obtain ⟨⟨rxy, rxz, rxw⟩, ⟨ryz, ryw⟩, rzw⟩ := nr'
  have gx := h x hx; have gy := h y hy; have gz := h z hz; have gw := h w hw
  simp only [ix, iy, iz, iw, ite_true] at gx gy gz gw
  refine WP.mono (VG.Proof.ChaCha20.Arm.qr_ok rxy rxz rxw ryz ryw rzw s _ _ _ _ gx gy gz gw)
    fun _ ⟨ha, hb, hc, hd, hr, hm, hrd, hwr⟩ => ⟨fun k hk => ?_, hm, hrd, hwr,
      hr _ (VG.Proof.ChaCha20.Arm.wreg_ne_r1 x).symm (VG.Proof.ChaCha20.Arm.wreg_ne_r1 y).symm (VG.Proof.ChaCha20.Arm.wreg_ne_r1 z).symm (VG.Proof.ChaCha20.Arm.wreg_ne_r1 w).symm⟩
  rw [qround_get _ _ _ _ _ k hk]
  simp only
  by_cases ew : w = k
  · subst ew; simp only [iw, ite_true]; exact hd
  by_cases ez : z = k
  · subst ez; simp only [iz, ite_true, ew]; exact hc
  by_cases ey : y = k
  · subst ey; simp only [iy, ite_true, ew, ez]; exact hb
  by_cases ex : x = k
  · subst ex; simp only [ix, ite_true, ew, ez, ey]; exact ha
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
abbrev slotR (B : Addr) : Region := ⟨B + BitVec.ofNat 64 128, 16⟩

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem slot_in_slotR (B : Addr) {k : Nat} (h8 : 8 ≤ k) (h11 : k ≤ 11) :
    (VG.Proof.ChaCha20.Arm.slotR B).Contains (VG.Proof.ChaCha20.Arm.slotAddr B k) 4 := Offset.contains B (by unfold slotOff; omega) (by unfold slotOff; omega) (by lit_omega)

theorem slot_sep (B : Addr) {j k : Nat} (hj8 : 8 ≤ j) (hj : j ≤ 11) (hk8 : 8 ≤ k) (hk : k ≤ 11)
    (h : j ≠ k) : Mem.Sep (VG.Proof.ChaCha20.Arm.slotAddr B j) 4 (VG.Proof.ChaCha20.Arm.slotAddr B k) 4 := Offset.sep B (by unfold slotOff; omega) (by unfold slotOff; omega) (by unfold slotOff; omega)

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (B : Addr) (c : Nat) (v : CState) (s₀ s : State) : Prop where
  holds : VG.Proof.ChaCha20.Arm.Holds B c v s
  frame : Frame [VG.Proof.ChaCha20.Arm.slotR B] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r1 : s.gpr .r1 = s₀.gpr .r1

theorem quarter_step {c x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16) (hw : w < 16)
    (hq : VG.Proof.ChaCha20.Arm.QSide c x y z w = true) {B : Addr} {v : CState} {s₀ s : State} (h : VG.Proof.ChaCha20.Arm.RI B c v s₀ s) :
    WP isa (quarter x y z w) s (VG.Proof.ChaCha20.Arm.RI B c (qround v ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s₀) :=
  WP.mono (VG.Proof.ChaCha20.Arm.quarter_ok hx hy hz hw hq h.holds) fun _ ⟨hh, hm, hrd, hwr, hr1⟩ =>
    ⟨hh, hm ▸ h.frame, hrd.trans h.rd, hwr.trans h.wr, hr1.trans h.r1⟩

theorem swap_step {i j : Nat} (hi8 : 8 ≤ i) (hi : i ≤ 11) (hj8 : 8 ≤ j) (hj : j ≤ 11) (hij : i ≠ j)
    {B : Addr} {v : CState} {s₀ s : State} (h : VG.Proof.ChaCha20.Arm.RI B i v s₀ s)
    (haddr : ∀ off, off < 256 → State.addr (s₀.gpr .r1 + BitVec.ofNat 32 off) = B + BitVec.ofNat 64 off)
    (hw : (⟨B, 256⟩ : Region) ∈ s₀.wr) :
    WP isa (swap i j) s (VG.Proof.ChaCha20.Arm.RI B j v s₀) := by
  have ea : ∀ off, off < 256 → State.addr (s.gpr .r1 + BitVec.ofNat 32 off) = B + BitVec.ofNat 64 off :=
    fun off ho => by rw [h.r1]; exact haddr off ho
  have cb : ∀ k, 8 ≤ k → k ≤ 11 → (⟨B, 256⟩ : Region).Contains (VG.Proof.ChaCha20.Arm.slotAddr B k) 4 := fun k h1 h2 => by
    simp only [VG.Proof.ChaCha20.Arm.slotAddr, slotOff]
    exact Offset.contains_base B (by lit_omega) (by lit_omega)
  have hout : InRegions s.wr (VG.Proof.ChaCha20.Arm.slotAddr B i) 4 := ⟨_, h.wr ▸ hw, cb i hi8 hi⟩
  have hin : InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.Arm.slotAddr B j) 4 :=
    ⟨_, List.mem_append_right _ (h.wr ▸ hw), cb j hj8 hj⟩
  have hi' : VG.Proof.ChaCha20.Arm.inReg i i = true := by simp [VG.Proof.ChaCha20.Arm.inReg]
  have hl := h.holds i (by lit_omega)
  simp only [hi', ite_true] at hl
  have hj' : VG.Proof.ChaCha20.Arm.inReg i j = false := by simp [VG.Proof.ChaCha20.Arm.inReg, hij.symm]; omega
  have hv := h.holds j (by lit_omega)
  simp only [hj'] at hv
  have wlr : ∀ i < 12, 8 ≤ i → wreg i = .lr := by decide
  have wi : wreg i = .lr := wlr i (by lit_omega) hi8
  have wj : wreg j = .lr := wlr j (by lit_omega) hj8
  rw [wi] at hl
  apply WP.of_runBlock
  simp only [runBlock_cons, isa]
  rw [exec_str (by simp only [slotOff]; omega) (by rw [ea _ (by simp only [slotOff]; omega)]; exact hout)]
  simp only [runStep_some, runBlock_cons]
  rw [exec_ldr (by simp only [slotOff]; omega)
    (by show InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 (slotOff j))) 4
        rw [ea _ (by simp only [slotOff]; omega)]; exact hin)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', ea _ (show slotOff i < 256 by
    simp only [slotOff]; omega), ea _ (show slotOff j < 256 by simp only [slotOff]; omega)]
  rw [Mem.readW_writeW_sep (VG.Proof.ChaCha20.Arm.slot_sep B hj8 hj hi8 hi (Ne.symm hij)) (by decide)]
  refine ⟨fun k hk => ?_, ?_, h.rd, h.wr, ?_⟩
  · have hk' := h.holds k hk
    by_cases hkj : k = j
    · subst hkj
      simp only [VG.Proof.ChaCha20.Arm.inReg, beq_self_eq_true, Bool.or_true, ite_true, State.setReg, wj]
      simpa [VG.Proof.ChaCha20.Arm.slotAddr] using hv
    by_cases hki : k = i
    · subst hki
      have : VG.Proof.ChaCha20.Arm.inReg j k = false := by simp [VG.Proof.ChaCha20.Arm.inReg, hij]; omega
      simp only [this, Bool.false_eq_true, ite_false, State.setReg, VG.Proof.ChaCha20.Arm.slotAddr,
        Mem.readW_writeW_self32]
      exact hl
    · by_cases h811 : 8 ≤ k ∧ k ≤ 11
      · have e1 : VG.Proof.ChaCha20.Arm.inReg j k = false := by simp [VG.Proof.ChaCha20.Arm.inReg, hkj]; omega
        have e2 : VG.Proof.ChaCha20.Arm.inReg i k = false := by simp [VG.Proof.ChaCha20.Arm.inReg, hki]; omega
        simp only [e1, e2, Bool.false_eq_true, ite_false, State.setReg] at hk' ⊢
        rw [Mem.readW_writeW_sep (VG.Proof.ChaCha20.Arm.slot_sep B h811.1 h811.2 hi8 hi hki) (by decide)]; exact hk'
      · have e1 : VG.Proof.ChaCha20.Arm.inReg j k = true := by simp [VG.Proof.ChaCha20.Arm.inReg]; omega
        have e2 : VG.Proof.ChaCha20.Arm.inReg i k = true := by simp [VG.Proof.ChaCha20.Arm.inReg]; omega
        have ne : wreg k ≠ .lr :=
          (show ∀ k < 16, ¬(8 ≤ k ∧ k ≤ 11) → wreg k ≠ .lr by decide) k hk h811
        simp only [e1, e2, ite_true, State.setReg, ne, ite_false] at hk' ⊢; exact hk'
  · exact h.frame.writeW (List.mem_singleton_self _) _ (VG.Proof.ChaCha20.Arm.slot_in_slotR B hi8 hi)
  · simp only [State.setReg, show Reg.r1 ≠ Reg.lr by decide, ite_false]; exact h.r1

/-! ## Double rounds -/

theorem doubleRound_ok {B : Addr} {v : CState} {s₀ s : State} (h : VG.Proof.ChaCha20.Arm.RI B 8 v s₀ s)
    (haddr : ∀ off, off < 256 → State.addr (s₀.gpr .r1 + BitVec.ofNat 32 off) = B + BitVec.ofNat 64 off)
    (hw : (⟨B, 256⟩ : Region) ∈ s₀.wr) :
    WP isa doubleRound s (VG.Proof.ChaCha20.Arm.RI B 8 (innerBlock v) s₀) := by
  unfold doubleRound
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.quarter_step (x := 0) (y := 4) (z := 8) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h) fun _ h1 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.swap_step (i := 8) (j := 9) (by lit_omega) (by lit_omega) (by lit_omega) (by lit_omega)
    (by lit_omega) h1 haddr hw) fun _ h2 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.quarter_step (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) h2) fun _ h3 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.swap_step (i := 9) (j := 10) (by lit_omega) (by lit_omega) (by lit_omega) (by lit_omega)
    (by lit_omega) h3 haddr hw) fun _ h4 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.quarter_step (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h4) fun _ h5 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.swap_step (i := 10) (j := 11) (by lit_omega) (by lit_omega) (by lit_omega) (by lit_omega)
    (by lit_omega) h5 haddr hw) fun _ h6 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.quarter_step (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h6) fun _ h7 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.swap_step (i := 11) (j := 10) (by lit_omega) (by lit_omega) (by lit_omega) (by lit_omega)
    (by lit_omega) h7 haddr hw) fun _ h8 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.quarter_step (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h8) fun _ h9 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.swap_step (i := 10) (j := 11) (by lit_omega) (by lit_omega) (by lit_omega) (by lit_omega)
    (by lit_omega) h9 haddr hw) fun _ h10 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.quarter_step (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h10) fun _ h11 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.swap_step (i := 11) (j := 8) (by lit_omega) (by lit_omega) (by lit_omega) (by lit_omega)
    (by lit_omega) h11 haddr hw) fun _ h12 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.quarter_step (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) h12) fun _ h13 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.swap_step (i := 8) (j := 9) (by lit_omega) (by lit_omega) (by lit_omega) (by lit_omega)
    (by lit_omega) h13 haddr hw) fun _ h14 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.quarter_step (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h14) fun _ h15 => ?_)
  exact VG.Proof.ChaCha20.Arm.swap_step (i := 9) (j := 8) (by lit_omega) (by lit_omega) (by lit_omega) (by lit_omega) (by lit_omega) h15 haddr hw

theorem rounds_ok {B : Addr} {v : CState} {s₀ : State} (h : VG.Proof.ChaCha20.Arm.Holds B 8 v s₀)
    (haddr : ∀ off, off < 256 → State.addr (s₀.gpr .r1 + BitVec.ofNat 32 off) = B + BitVec.ofNat 64 off)
    (hw : (⟨B, 256⟩ : Region) ∈ s₀.wr) :
    ∀ n, WP isa (VG.Impl.ChaCha20.Arm.rounds n) s₀ (VG.Proof.ChaCha20.Arm.RI B 8 (Nat.repeat innerBlock n v) s₀)
  | 0 => WP.block_nil ⟨h, Frame.refl _ _, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.rounds_ok h haddr hw n) fun _ h' => VG.Proof.ChaCha20.Arm.doubleRound_ok h' haddr hw)

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
    VG.Spec.ChaCha20.stateAt s'.mem (State.addr (s.gpr .r1)) = block (VG.Spec.ChaCha20.stateAt s.mem (State.addr (s.gpr .r0)))
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
theorem readW_writeW_off (m : Mem) (p : Addr) (v : VG.Spec.ChaCha20.Word) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 32 =
      m.readW (p + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (VG.Proof.ChaCha20.Arm.off_sep p hd he (by lit_omega) (by lit_omega) h) (by decide)

/-- A sub-range `[a, a + len)` of `buf` contains `[d, d + n)`. -/
theorem contains_sub (p : Addr) {a len d n : Nat} (h1 : a ≤ d) (h2 : d + n ≤ a + len)
    (h3 : a + len < 2 ^ 32) :
    (⟨p + BitVec.ofNat 64 a, len⟩ : Region).Contains (p + BitVec.ofNat 64 d) n :=
  Offset.contains p h1 h2 (by lit_omega)

/-- Two sub-ranges of `buf` that do not overlap. -/
theorem disjoint_sub (p : Addr) {a la b lb : Nat} (h : a + la ≤ b ∨ b + lb ≤ a)
    (ha : a + la < 2 ^ 32) (hb : b + lb < 2 ^ 32) :
    (⟨p + BitVec.ofNat 64 a, la⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 b, lb⟩ :=
  Offset.disjoint p h (by lit_omega) (by lit_omega)

theorem sub_buf (p : Addr) {a len : Nat} (h : a + len ≤ 256) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, len⟩ ⟨p, 256⟩ :=
  Offset.sub_base p h

/-- The output area of `buf`. -/
abbrev outR (p : Addr) : Region := ⟨p + BitVec.ofNat 64 0, 64⟩
/-- Everything in `buf` but the saved registers: output, input copy and slots. -/
abbrev workR (p : Addr) : Region := ⟨p + BitVec.ofNat 64 0, 144⟩

theorem sub_work (p : Addr) {a len : Nat} (h : a + len ≤ 144) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, len⟩ (VG.Proof.ChaCha20.Arm.workR p) := Offset.sub p (by lit_omega) (by lit_omega)

theorem frame_work {p : Addr} {a len : Nat} (h : a + len ≤ 144) {m m' : Mem}
    (hf : Frame [⟨p + BitVec.ofNat 64 a, len⟩] m m') : Frame [VG.Proof.ChaCha20.Arm.workR p] m m' :=
  hf.sub fun r hr => ⟨VG.Proof.ChaCha20.Arm.workR p, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.ChaCha20.Arm.sub_work p h⟩

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev st : BitVec 32 := s₀.gpr .r0
abbrev buf : BitVec 32 := s₀.gpr .r1
/-- The 64-bit addresses of `state` and `buf`. -/
abbrev SA : Addr := State.addr (VG.Proof.ChaCha20.Arm.st s₀)
abbrev BA : Addr := State.addr (VG.Proof.ChaCha20.Arm.buf s₀)
abbrev stR : Region := ⟨VG.Proof.ChaCha20.Arm.SA s₀, 64⟩
abbrev bufR : Region := ⟨VG.Proof.ChaCha20.Arm.BA s₀, 256⟩
/-- The input state. -/
abbrev V : CState := VG.Spec.ChaCha20.stateAt s₀.mem (VG.Proof.ChaCha20.Arm.SA s₀)
/-- The result of the rounds. -/
abbrev Rs : CState := Nat.repeat innerBlock 10 (VG.Proof.ChaCha20.Arm.V s₀)
end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.ChaCha20.Arm.stR s₀]
  wr : s₀.wr = [VG.Proof.ChaCha20.Arm.bufR s₀]
  buf_st : (VG.Proof.ChaCha20.Arm.bufR s₀).Disjoint (VG.Proof.ChaCha20.Arm.stR s₀)
  st_fits : (VG.Proof.ChaCha20.Arm.st s₀).toNat + 64 ≤ 2 ^ 32
  buf_fits : (VG.Proof.ChaCha20.Arm.buf s₀).toNat + 256 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.ChaCha20.blockArm.pre s₀) : VG.Proof.ChaCha20.Arm.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Pre
variable {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Pre s₀)
include hp

theorem eaB {off : Nat} (h : off < 256) :
    State.addr (VG.Proof.ChaCha20.Arm.buf s₀ + BitVec.ofNat 32 off) = VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 off :=
  addr_add (by have := hp.buf_fits; omega)

theorem eaS {off : Nat} (h : off < 64) :
    State.addr (VG.Proof.ChaCha20.Arm.st s₀ + BitVec.ofNat 32 off) = VG.Proof.ChaCha20.Arm.SA s₀ + BitVec.ofNat 64 off :=
  addr_add (by have := hp.st_fits; omega)

theorem hw : VG.Proof.ChaCha20.Arm.bufR s₀ ∈ s₀.wr := by simp [hp.wr]

theorem in_buf {d n : Nat} (h : d + n ≤ 256) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 d) n :=
  ⟨VG.Proof.ChaCha20.Arm.bufR s₀, by simp [hp.wr], VG.Proof.ChaCha20.Arm.contains_off (by lit_omega) (by lit_omega)⟩

theorem out_buf {d n : Nat} (h : d + n ≤ 256) : InRegions s₀.wr (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 d) n :=
  ⟨VG.Proof.ChaCha20.Arm.bufR s₀, by simp [hp.wr], VG.Proof.ChaCha20.Arm.contains_off (by lit_omega) (by lit_omega)⟩

theorem in_st {k : Nat} (hk : k < 16) (ws : List Region) :
    InRegions (s₀.rd ++ ws) (VG.Proof.ChaCha20.Arm.SA s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨VG.Proof.ChaCha20.Arm.stR s₀, by simp [hp.rd], VG.Proof.ChaCha20.Arm.contains_off (by lit_omega) (by lit_omega)⟩

/-- Reading the input state after writes to `buf` only. -/
theorem read_st {m : Mem} (hf : Frame [VG.Proof.ChaCha20.Arm.bufR s₀] s₀.mem m) {k : Nat} (hk : k < 16) :
    m.readW (VG.Proof.ChaCha20.Arm.SA s₀ + BitVec.ofNat 64 (4 * k)) 32 = (VG.Proof.ChaCha20.Arm.V s₀)[k] := by
  rw [hf.readW (r := VG.Proof.ChaCha20.Arm.stR s₀) (VG.Proof.ChaCha20.Arm.contains_off (by lit_omega) (by lit_omega)) (by simpa using hp.buf_st.symm)
    (by decide)]
  simp only [VG.Proof.ChaCha20.Arm.V, VG.Spec.ChaCha20.stateAt, Vector.getElem_ofFn]

end Pre

theorem in_lt {k : Nat} (hk : k < 16) : inOff k + 4 ≤ 256 := by simp only [inOff]; omega
theorem out_lt {k : Nat} (hk : k < 16) : outOff k + 4 ≤ 256 := by simp only [outOff]; omega

/-! ## Copying the state -/

theorem copyWord_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Pre s₀) {k : Nat} (hk : k < 16) {s : State}
    (hr0 : s.gpr .r0 = VG.Proof.ChaCha20.Arm.st s₀) (hr1 : s.gpr .r1 = VG.Proof.ChaCha20.Arm.buf s₀)
    (hin : InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.Arm.SA s₀ + BitVec.ofNat 64 (4 * k)) 4)
    (hw : VG.Proof.ChaCha20.Arm.bufR s₀ ∈ s.wr) :
    WP isa (.block (copyWord k)) s fun s' =>
      s'.mem = (if 9 ≤ k ∧ k ≤ 11 then
          (s.mem.writeW (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (inOff k))
            (s.mem.readW (VG.Proof.ChaCha20.Arm.SA s₀ + BitVec.ofNat 64 (4 * k)) 32)).writeW
            (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (slotOff k)) (s.mem.readW (VG.Proof.ChaCha20.Arm.SA s₀ + BitVec.ofNat 64 (4 * k)) 32)
        else s.mem.writeW (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (inOff k))
          (s.mem.readW (VG.Proof.ChaCha20.Arm.SA s₀ + BitVec.ofNat 64 (4 * k)) 32)) ∧
      (∀ r, r ≠ .r2 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o₁ : InRegions s.wr (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (inOff k)) 4 :=
    ⟨VG.Proof.ChaCha20.Arm.bufR s₀, hw, VG.Proof.ChaCha20.Arm.contains_off (VG.Proof.ChaCha20.Arm.in_lt hk) (by simp only [inOff]; omega)⟩
  have e0 := hp.eaS (show 4 * k < 64 by omega)
  have e1 := hp.eaB (show inOff k < 256 by simp only [inOff]; omega)
  have h4 : 4 * k < 4096 := by omega
  have h5 : inOff k < 4096 := by simp only [inOff]; omega
  apply WP.of_runBlock
  by_cases h : 9 ≤ k ∧ k ≤ 11
  · have o₂ : InRegions s.wr (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (slotOff k)) 4 :=
      ⟨VG.Proof.ChaCha20.Arm.bufR s₀, hw, VG.Proof.ChaCha20.Arm.contains_off (by simp only [slotOff]; omega) (by simp only [slotOff]; omega)⟩
    have e2 := hp.eaB (show slotOff k < 256 by simp only [slotOff]; omega)
    have h6 : slotOff k < 4096 := by simp only [slotOff]; omega
    simp only [reduceCtorEq, ↓reduceIte, copyWord, h, and_self, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
          exec, isa, State.setReg, State.load32, State.store32, hr0, hr1,
      e0, e1, e2, h4, h5, h6, hin, o₁, o₂, Option.map_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  · simp only [reduceCtorEq, ↓reduceIte, and_self, copyWord, h, List.append_nil,
      runBlock_cons, runStep_some, runBlock_nil,
      exec, isa, State.setReg, State.load32, State.store32, hr0, hr1, e0, e1, h4, h5, hin, o₁,
      Option.map_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩

/-- The copy invariant after `n` words, relative to the state `s₁` after the prologue's stores. -/
structure CI (s₀ s₁ : State) (n : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .r2 → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 64, 80⟩] s₁.mem s.mem
  inw : ∀ j (hj : j < 16), j < n → s.mem.readW (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (inOff j)) 32 = (VG.Proof.ChaCha20.Arm.V s₀)[j]
  slot : ∀ j (hj : j < 16), j < n → (9 ≤ j ∧ j ≤ 11) →
    s.mem.readW (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (slotOff j)) 32 = (VG.Proof.ChaCha20.Arm.V s₀)[j]

theorem copy_step {s₀ s₁ : State} (hp : VG.Proof.ChaCha20.Arm.Pre s₀) (h₁ : s₁.gpr = s₀.gpr)
    (hf₁ : Frame [VG.Proof.ChaCha20.Arm.bufR s₀] s₀.mem s₁.mem) {n : Nat} (hn : n < 16)
    {s : State} (hc : VG.Proof.ChaCha20.Arm.CI s₀ s₁ n s) : WP isa (.block (copyWord n)) s (VG.Proof.ChaCha20.Arm.CI s₀ s₁ (n + 1)) := by
  have hr0 : s.gpr .r0 = VG.Proof.ChaCha20.Arm.st s₀ := by rw [hc.gpr _ (by decide), h₁]
  have hr1 : s.gpr .r1 = VG.Proof.ChaCha20.Arm.buf s₀ := by rw [hc.gpr _ (by decide), h₁]
  have hfs : Frame [VG.Proof.ChaCha20.Arm.bufR s₀] s₀.mem s.mem :=
    hf₁.trans (hc.frame.sub fun r hr => ⟨VG.Proof.ChaCha20.Arm.bufR s₀, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.ChaCha20.Arm.sub_buf _ (by lit_omega)⟩)
  refine WP.mono (VG.Proof.ChaCha20.Arm.copyWord_ok hp hn hr0 hr1 (by rw [hc.rd, hc.wr]; exact hp.in_st hn _)
    (by rw [hc.wr]; exact hp.hw)) fun s' ⟨hm, hg, hrd, hwr⟩ => ?_
  have hx : s.mem.readW (VG.Proof.ChaCha20.Arm.SA s₀ + BitVec.ofNat 64 (4 * n)) 32 = (VG.Proof.ChaCha20.Arm.V s₀)[n] := hp.read_st hfs hn
  have cin : (⟨VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 64, 80⟩ : Region).Contains
      (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (inOff n)) (32 / 8) :=
    VG.Proof.ChaCha20.Arm.contains_sub _ (by simp [inOff]) (by simp [inOff]; omega) (by lit_omega)
  refine ⟨fun r hr => (hg r hr).trans (hc.gpr r hr), hrd.trans hc.rd, hwr.trans hc.wr, ?_, ?_, ?_⟩
  · rw [hm]
    split
    · exact (hc.frame.writeW (List.mem_singleton_self _) _ cin).writeW (List.mem_singleton_self _) _
        (VG.Proof.ChaCha20.Arm.contains_sub _ (by simp [slotOff]; omega) (by simp [slotOff]; omega) (by lit_omega))
    · exact hc.frame.writeW (List.mem_singleton_self _) _ cin
  · intro j hj hjn
    rw [hm]
    have e1 : ∀ m : Mem, (m.writeW (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (slotOff n)) ((VG.Proof.ChaCha20.Arm.V s₀)[n])).readW
        (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (inOff j)) 32 = m.readW (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (inOff j)) 32 :=
      fun m => VG.Proof.ChaCha20.Arm.readW_writeW_off m _ _ (by simp [inOff]; omega) (by simp [slotOff]; omega)
        (by simp [inOff, slotOff]; omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · have e2 : (s.mem.writeW (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (inOff n)) ((VG.Proof.ChaCha20.Arm.V s₀)[n])).readW
          (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (inOff j)) 32 = s.mem.readW (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (inOff j)) 32 :=
        VG.Proof.ChaCha20.Arm.readW_writeW_off _ _ _ (by simp [inOff]; omega) (by simp [inOff]; omega)
          (by simp [inOff]; omega)
      rw [hx]; split <;> simp only [e1, e2, hc.inw j hj hjn]
    · rw [hx]; split <;> simp only [e1, Mem.readW_writeW_self32]
  · intro j hj hjn h911
    rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · have e2 : ∀ m : Mem, ∀ d, d = inOff n ∨ d = slotOff n → (m.writeW (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 d)
          ((VG.Proof.ChaCha20.Arm.V s₀)[n])).readW (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (slotOff j)) 32 =
          m.readW (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (slotOff j)) 32 := by
        rintro m d (rfl | rfl)
        · exact VG.Proof.ChaCha20.Arm.readW_writeW_off _ _ _ (by simp [slotOff]; omega) (by simp [inOff]; omega)
            (by simp [inOff, slotOff]; omega)
        · exact VG.Proof.ChaCha20.Arm.readW_writeW_off _ _ _ (by simp [slotOff]; omega) (by simp [slotOff]; omega)
            (by simp [slotOff]; omega)
      rw [hx]; split <;> simp only [e2 _ _ (.inl rfl), e2 _ _ (.inr rfl), hc.slot j hj hjn h911]
    · simp only [hx, h911, and_self, ite_true, Mem.readW_writeW_self32]

/-! ## Saving and restoring the callee-saved registers -/

/-- The memory after the prologue's stores. -/
def saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (VG.Proof.ChaCha20.Arm.BA s₀) s₀.gpr VG.Impl.ChaCha20.Arm.saved

/-- The callee-saved registers are saved in `buf`. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (VG.Proof.ChaCha20.Arm.BA s₀) s₀.gpr VG.Impl.ChaCha20.Arm.saved

theorem saved_slots : Spill.Slots 144 180 VG.Impl.ChaCha20.Arm.saved := by decide

theorem save_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Pre s₀) :
    WP isa (.block VG.Impl.ChaCha20.Arm.save) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = VG.Proof.ChaCha20.Arm.saveMem s₀ := by
  rw [VG.Impl.ChaCha20.Arm.save, ← List.append_nil (saved.map _)]
  exact Spill.save_slots_ok VG.Proof.ChaCha20.Arm.saved_slots (Nat.le_trans (Nat.add_le_add_left (by decide : 180 ≤ 256) _) hp.buf_fits)
    (fun _ _ hd => hp.out_buf (by omega)) (WP.block_nil ⟨rfl, rfl, rfl, rfl⟩)

theorem saveMem_saved (s₀ : State) : VG.Proof.ChaCha20.Arm.Saved s₀ (VG.Proof.ChaCha20.Arm.saveMem s₀) := Spill.saveMem_saved _ _ _ _ VG.Proof.ChaCha20.Arm.saved_slots

theorem saveMem_frame (s₀ : State) : Frame [VG.Proof.ChaCha20.Arm.bufR s₀] s₀.mem (VG.Proof.ChaCha20.Arm.saveMem s₀) :=
  Spill.saveMem_frame _ _ _ (by decide) VG.Impl.ChaCha20.Arm.saved (by decide)

theorem saved_frame {s₀ : State} {m m' : Mem} (h : VG.Proof.ChaCha20.Arm.Saved s₀ m) (hf : Frame [VG.Proof.ChaCha20.Arm.workR (VG.Proof.ChaCha20.Arm.BA s₀)] m m') :
    VG.Proof.ChaCha20.Arm.Saved s₀ m' :=
  h.frame VG.Proof.ChaCha20.Arm.saved_slots hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)

theorem restore_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Pre s₀) {s : State} (hs : VG.Proof.ChaCha20.Arm.Saved s₀ s.mem)
    (hr1 : s.gpr .r1 = VG.Proof.ChaCha20.Arm.buf s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block VG.Impl.ChaCha20.Arm.restore) s fun s' =>
      s'.mem = s.mem ∧ ∀ r ∈ preserved, s'.gpr r = s₀.gpr r := by
  rw [VG.Impl.ChaCha20.Arm.restore, ← List.append_nil (saved.map _)]
  refine Spill.restore_slots_ok VG.Proof.ChaCha20.Arm.saved_slots (by decide) (g := s₀.gpr)
    (by rw [hr1]; exact Nat.le_trans (Nat.add_le_add_left (by decide : 180 ≤ 256) _) hp.buf_fits)
    (fun _ _ hd => by rw [hwr, hr1]; exact hp.in_buf (by omega) _) (by rw [hr1]; exact hs)
    fun s' ho _ hm _ _ _ => WP.block_nil ⟨hm, Spill.restored_of ho (by decide)⟩

/-! ## Loading the registers -/

theorem wreg_inj {j k : Nat} (hj : j < 16) (hk : k < 16) (hj8 : VG.Proof.ChaCha20.Arm.inReg 8 j = true)
    (hk8 : VG.Proof.ChaCha20.Arm.inReg 8 k = true) (h : wreg j = wreg k) : j = k := by
  have key : ∀ j, j < 16 → ∀ k, k < 16 → VG.Proof.ChaCha20.Arm.inReg 8 j = true → VG.Proof.ChaCha20.Arm.inReg 8 k = true →
      wreg j = wreg k → j = k := by decide
  exact key j hj k hk hj8 hk8 h

/-- After loading words `< n`. -/
structure LI (s₀ : State) (sL : State) (n : Nat) (s : State) : Prop where
  loaded : ∀ j (hj : j < 16), j < n → VG.Proof.ChaCha20.Arm.inReg 8 j = true → s.gpr (wreg j) = (VG.Proof.ChaCha20.Arm.V s₀)[j]
  mem : s.mem = sL.mem
  rd : s.rd = sL.rd
  wr : s.wr = sL.wr
  r1 : s.gpr .r1 = VG.Proof.ChaCha20.Arm.buf s₀

theorem load_step {s₀ s₁ sL : State} (hp : VG.Proof.ChaCha20.Arm.Pre s₀) (hc : VG.Proof.ChaCha20.Arm.CI s₀ s₁ 16 sL) {n : Nat} (hn : n < 16)
    {s : State} (h : VG.Proof.ChaCha20.Arm.LI s₀ sL n s) : WP isa (.block (loadWord n)) s (VG.Proof.ChaCha20.Arm.LI s₀ sL (n + 1)) := by
  by_cases h911 : 9 ≤ n ∧ n ≤ 11
  · simp only [loadWord, h911, and_self, ite_true]
    refine WP.block_nil ⟨fun j hj hjn hin => ?_, h.mem, h.rd, h.wr, h.r1⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · exact h.loaded j hj hjn hin
    · simp [VG.Proof.ChaCha20.Arm.inReg] at hin; omega
  · have hin8 : VG.Proof.ChaCha20.Arm.inReg 8 n = true := by simp [VG.Proof.ChaCha20.Arm.inReg]; omega
    have hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 (inOff n))) 4 := by
      rw [h.r1, hp.eaB (by simp only [inOff]; omega), h.rd, h.wr, hc.wr]
      exact hp.in_buf (VG.Proof.ChaCha20.Arm.in_lt hn) _
    simp only [loadWord, h911, ite_false]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa,
      exec_ldr (show inOff n < 4096 by simp only [inOff]; omega) hin,
      Option.some.injEq, exists_eq_left']
    rw [h.r1, hp.eaB (by simp only [inOff]; omega), h.mem, hc.inw n hn hn]
    refine ⟨fun j hj hjn hj8 => ?_, h.mem, h.rd, h.wr, ?_⟩
    · simp only [State.setReg]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
      · have e : wreg j ≠ wreg n := fun e => absurd (VG.Proof.ChaCha20.Arm.wreg_inj hj hn hj8 hin8 e) (by lit_omega)
        simp only [e, ite_false]; exact h.loaded j hj hjn hj8
      · simp
    · simp only [State.setReg, show Reg.r1 ≠ wreg n from (VG.Proof.ChaCha20.Arm.wreg_ne_r1 n).symm, ite_false]
      exact h.r1

theorem load_ok {s₀ s₁ : State} (hp : VG.Proof.ChaCha20.Arm.Pre s₀) (h₁ : s₁.gpr = s₀.gpr) {s : State}
    (hc : VG.Proof.ChaCha20.Arm.CI s₀ s₁ 16 s) :
    WP isa (.block load) s fun s' =>
      VG.Proof.ChaCha20.Arm.Holds (VG.Proof.ChaCha20.Arm.BA s₀) 8 (VG.Proof.ChaCha20.Arm.V s₀) s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.gpr .r1 = VG.Proof.ChaCha20.Arm.buf s₀ := by
  have h0 : VG.Proof.ChaCha20.Arm.LI s₀ s 0 s :=
    ⟨fun _ _ h => absurd h (by lit_omega), rfl, rfl, rfl, by rw [hc.gpr _ (by decide), h₁]⟩
  have hl : WP isa (.block load) s (VG.Proof.ChaCha20.Arm.LI s₀ s 16) := by
    unfold load
    exact wp_range_flatMap (M := isa) (VG.Proof.ChaCha20.Arm.LI s₀ s) (fun k s' hk h => VG.Proof.ChaCha20.Arm.load_step hp hc hk h) 16 (Nat.le_refl _)
      s h0
  refine WP.mono hl fun s' h => ⟨fun k hk => ?_, h.mem, h.rd, h.wr, h.r1⟩
  split
  · rename_i hin; exact h.loaded k hk hk hin
  · rename_i hin
    have h911 : 9 ≤ k ∧ k ≤ 11 := by simp [VG.Proof.ChaCha20.Arm.inReg] at hin; omega
    rw [VG.Proof.ChaCha20.Arm.slotAddr, h.mem]; exact hc.slot k hk hk h911


/-! ## Storing the rounds' result -/

/-- The store invariant after `n` words. -/
structure SI (B : Addr) (R : CState) (sB : State) (n : Nat) (s : State) : Prop where
  out : ∀ j (hj : j < 16), j < n → s.mem.readW (B + BitVec.ofNat 64 (outOff j)) 32 = R[j]
  rest : ∀ j (hj : j < 16), n ≤ j → if VG.Proof.ChaCha20.Arm.inReg 8 j then s.gpr (wreg j) = R[j]
    else s.mem.readW (VG.Proof.ChaCha20.Arm.slotAddr B j) 32 = R[j]
  frame : Frame [VG.Proof.ChaCha20.Arm.outR B] sB.mem s.mem
  r1 : s.gpr .r1 = sB.gpr .r1
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem wreg_ne_r0 {j : Nat} (h : 10 ≤ j) (hj : j < 16) : wreg j ≠ .r0 :=
  (show ∀ j < 16, 10 ≤ j → wreg j ≠ .r0 by decide) j hj h

theorem store_step {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Pre s₀) {R : CState} {sB : State} (hwB : VG.Proof.ChaCha20.Arm.bufR s₀ ∈ sB.wr)
    (hr1B : sB.gpr .r1 = VG.Proof.ChaCha20.Arm.buf s₀) {n : Nat} (hn : n < 16) {s : State} (hs : VG.Proof.ChaCha20.Arm.SI (VG.Proof.ChaCha20.Arm.BA s₀) R sB n s) :
    WP isa (.block (storeWord n)) s (VG.Proof.ChaCha20.Arm.SI (VG.Proof.ChaCha20.Arm.BA s₀) R sB (n + 1)) := by
  have hw : VG.Proof.ChaCha20.Arm.bufR s₀ ∈ s.wr := hs.wr ▸ hwB
  have hr1 : s.gpr .r1 = VG.Proof.ChaCha20.Arm.buf s₀ := hs.r1.trans hr1B
  have eo := hp.eaB (show outOff n < 256 by simp only [outOff]; omega)
  have o : InRegions s.wr (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (outOff n)) 4 :=
    ⟨VG.Proof.ChaCha20.Arm.bufR s₀, hw, VG.Proof.ChaCha20.Arm.contains_off (VG.Proof.ChaCha20.Arm.out_lt hn) (by simp only [outOff]; omega)⟩
  have h4 : outOff n < 4096 := by simp only [outOff]; omega
  have cout : (VG.Proof.ChaCha20.Arm.outR (VG.Proof.ChaCha20.Arm.BA s₀)).Contains (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (outOff n)) (32 / 8) :=
    VG.Proof.ChaCha20.Arm.contains_sub _ (by lit_omega) (by simp [outOff]; omega) (by lit_omega)
  have hr := hs.rest n hn (Nat.le_refl _)
  suffices key : ∀ s', s'.mem = s.mem.writeW (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (outOff n)) R[n] →
      (∀ j (hj : j < 16), n < j → VG.Proof.ChaCha20.Arm.inReg 8 j = true → s'.gpr (wreg j) = s.gpr (wreg j)) →
      s'.gpr .r1 = s.gpr .r1 → s'.rd = s.rd → s'.wr = s.wr → VG.Proof.ChaCha20.Arm.SI (VG.Proof.ChaCha20.Arm.BA s₀) R sB (n + 1) s' by
    apply WP.of_runBlock
    by_cases h : 9 ≤ n ∧ n ≤ 11
    · have hin : VG.Proof.ChaCha20.Arm.inReg 8 n = false := by simp [VG.Proof.ChaCha20.Arm.inReg]; omega
      simp only [hin, Bool.false_eq_true, ite_false, VG.Proof.ChaCha20.Arm.slotAddr] at hr
      have es := hp.eaB (show slotOff n < 256 by simp only [slotOff]; omega)
      have i : InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (slotOff n)) 4 :=
        ⟨VG.Proof.ChaCha20.Arm.bufR s₀, List.mem_append_right _ hw, VG.Proof.ChaCha20.Arm.contains_off (by simp only [slotOff]; omega)
          (by simp only [slotOff]; omega)⟩
      have h5 : slotOff n < 4096 := by simp only [slotOff]; omega
      simp (config := {decide := true}) only [storeWord, h, and_self, ite_true,
        runBlock_cons, runStep_some, runBlock_nil, exec, isa,
        State.setReg, State.load32, State.store32, hr1, es, eo, i, o, h4, h5, ite_false,
        Option.map_some, Option.some.injEq, exists_eq_left']
      refine key _ (by simp only [hr]) (fun j hj hnj _ => ?_) (by simp) rfl rfl
      simp [VG.Proof.ChaCha20.Arm.wreg_ne_r0 (show 10 ≤ j by omega) hj]
    · have hin : VG.Proof.ChaCha20.Arm.inReg 8 n = true := by simp [VG.Proof.ChaCha20.Arm.inReg]; omega
      simp only [hin, ite_true] at hr
      simp (config := {decide := true}) only [storeWord, h, ite_false, runBlock_cons,
        runStep_some, runBlock_nil, exec, isa,
        State.store32, hr1, eo, o, h4, ite_true, hr, Option.some.injEq,
        exists_eq_left']
      exact key _ rfl (fun _ _ _ _ => rfl) rfl rfl rfl
  intro s' hm hg hr1' hrd hwr
  refine ⟨fun j hj hjn => ?_, fun j hj hjn => ?_, ?_, hr1'.trans hs.r1, hrd.trans hs.rd,
    hwr.trans hs.wr⟩
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · rw [VG.Proof.ChaCha20.Arm.readW_writeW_off _ _ _ (by simp [outOff]; omega) (by simp [outOff]; omega)
        (by simp [outOff]; omega)]
      exact hs.out j hj hjn
    · exact Mem.readW_writeW_self32 _ _ _
  · have hr' := hs.rest j hj (by lit_omega)
    split
    · rename_i hin; simp only [hin, ite_true] at hr'; rw [hg j hj (by lit_omega) hin]; exact hr'
    · rename_i hin; simp only [hin, Bool.false_eq_true, ite_false] at hr'
      rw [hm, VG.Proof.ChaCha20.Arm.slotAddr, VG.Proof.ChaCha20.Arm.readW_writeW_off _ _ _ (by simp [slotOff]; omega)
        (by simp [outOff]; omega) (by simp [outOff, slotOff]; omega)]
      exact hr'
  · rw [hm]; exact hs.frame.writeW (List.mem_singleton_self _) _ cout

/-! ## Adding the input state -/

/-- The add invariant after `n` words. -/
structure AI (B : Addr) (R v : CState) (sB : State) (n : Nat) (s : State) : Prop where
  out : ∀ j (hj : j < 16), s.mem.readW (B + BitVec.ofNat 64 (outOff j)) 32 =
    if j < n then R[j] + v[j] else R[j]
  inw : ∀ j (hj : j < 16), s.mem.readW (B + BitVec.ofNat 64 (inOff j)) 32 = v[j]
  frame : Frame [VG.Proof.ChaCha20.Arm.outR B] sB.mem s.mem
  r1 : s.gpr .r1 = sB.gpr .r1
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem add_step {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Pre s₀) {R v : CState} {sB : State} (hwB : VG.Proof.ChaCha20.Arm.bufR s₀ ∈ sB.wr)
    (hr1B : sB.gpr .r1 = VG.Proof.ChaCha20.Arm.buf s₀) {n : Nat} (hn : n < 16) {s : State}
    (hs : VG.Proof.ChaCha20.Arm.AI (VG.Proof.ChaCha20.Arm.BA s₀) R v sB n s) : WP isa (.block (addWord n)) s (VG.Proof.ChaCha20.Arm.AI (VG.Proof.ChaCha20.Arm.BA s₀) R v sB (n + 1)) := by
  have hw : VG.Proof.ChaCha20.Arm.bufR s₀ ∈ s.wr := hs.wr ▸ hwB
  have hr1 : s.gpr .r1 = VG.Proof.ChaCha20.Arm.buf s₀ := hs.r1.trans hr1B
  have eo := hp.eaB (show outOff n < 256 by simp only [outOff]; omega)
  have ei := hp.eaB (show inOff n < 256 by simp only [inOff]; omega)
  have o : InRegions s.wr (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (outOff n)) 4 :=
    ⟨VG.Proof.ChaCha20.Arm.bufR s₀, hw, VG.Proof.ChaCha20.Arm.contains_off (VG.Proof.ChaCha20.Arm.out_lt hn) (by simp only [outOff]; omega)⟩
  have io : InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (outOff n)) 4 :=
    ⟨VG.Proof.ChaCha20.Arm.bufR s₀, List.mem_append_right _ hw, VG.Proof.ChaCha20.Arm.contains_off (VG.Proof.ChaCha20.Arm.out_lt hn) (by simp only [outOff]; omega)⟩
  have ii : InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (inOff n)) 4 :=
    ⟨VG.Proof.ChaCha20.Arm.bufR s₀, List.mem_append_right _ hw, VG.Proof.ChaCha20.Arm.contains_off (VG.Proof.ChaCha20.Arm.in_lt hn) (by simp only [inOff]; omega)⟩
  have h4 : outOff n < 4096 := by simp only [outOff]; omega
  have h5 : inOff n < 4096 := by simp only [inOff]; omega
  have cout : (VG.Proof.ChaCha20.Arm.outR (VG.Proof.ChaCha20.Arm.BA s₀)).Contains (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (outOff n)) (32 / 8) :=
    VG.Proof.ChaCha20.Arm.contains_sub _ (by lit_omega) (by simp [outOff]; omega) (by lit_omega)
  have ho := hs.out n hn
  simp only [Nat.lt_irrefl, ite_false] at ho
  have hi := hs.inw n hn
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addWord, runBlock_cons,
    runStep_some, runBlock_nil, exec, Op2.eval, isa, State.setReg,
    State.load32, State.store32, hr1, eo, ei, o, io, ii, h4, h5, ho, hi, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun j hj => ?_, fun j hj => ?_, hs.frame.writeW (List.mem_singleton_self _) _ cout,
    by simpa using hs.r1, hs.rd, hs.wr⟩
  · by_cases hjn : j = n
    · subst hjn; simp [Mem.readW_writeW_self32]
    · rw [VG.Proof.ChaCha20.Arm.readW_writeW_off _ _ _ (by simp [outOff]; omega) (by simp [outOff]; omega)
        (by simp [outOff]; omega), hs.out j hj]
      split <;> split <;> first | rfl | omega
  · rw [VG.Proof.ChaCha20.Arm.readW_writeW_off _ _ _ (by simp [inOff]; omega) (by simp [outOff]; omega)
      (by simp [inOff, outOff]; omega)]
    exact hs.inw j hj

/-! ## The whole function -/

theorem finish_split : finish ++ VG.Impl.ChaCha20.Arm.restore =
    ((List.range 16).flatMap storeWord ++ (List.range 16).flatMap addWord) ++ VG.Impl.ChaCha20.Arm.restore := by
  unfold finish; rfl

theorem read_in {B : Addr} {m m' : Mem} {r : Region}
    (hf : Frame [r] m m') (hd : ∀ j < 16, (⟨B + BitVec.ofNat 64 (inOff j), 4⟩ : Region).Disjoint r)
    {j : Nat} (hj : j < 16) :
    m'.readW (B + BitVec.ofNat 64 (inOff j)) 32 = m.readW (B + BitVec.ofNat 64 (inOff j)) 32 :=
  hf.readW (Region.contains_self _ _) (by simpa using hd j hj) (by decide)

theorem block_post {p : Addr} {m : Mem} {R v : CState}
    (h : ∀ j (hj : j < 16), m.readW (p + BitVec.ofNat 64 (outOff j)) 32 = R[j] + v[j]) :
    VG.Spec.ChaCha20.stateAt m p = Vector.zipWith (· + ·) R v := by
  apply Vector.ext
  intro j hj
  simp only [VG.Spec.ChaCha20.stateAt, Vector.getElem_ofFn, Vector.getElem_zipWith]
  exact h j hj

theorem correct {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Pre s₀) :
    WP isa block s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.ChaCha20.blockArm.post s₀ s' := by
  have hw₀ := hp.hw
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.ChaCha20.Arm.save_ok hp) fun s₁ ⟨hg₁, hrd₁, hwr₁, hm₁⟩ => ?_
  have hf₁ : Frame [VG.Proof.ChaCha20.Arm.bufR s₀] s₀.mem s₁.mem := hm₁ ▸ VG.Proof.ChaCha20.Arm.saveMem_frame s₀
  have hc₀ : VG.Proof.ChaCha20.Arm.CI s₀ s₁ 0 s₁ :=
    ⟨fun _ _ => rfl, hrd₁, hwr₁, Frame.refl _ _, fun _ _ h => absurd h (by lit_omega),
      fun _ _ h => absurd h (by lit_omega)⟩
  refine WP.mono (wp_range_flatMap (M := isa) (VG.Proof.ChaCha20.Arm.CI s₀ s₁)
    (fun k s hk hc => VG.Proof.ChaCha20.Arm.copy_step hp hg₁ hf₁ hk hc) 16 (Nat.le_refl _) s₁ hc₀) fun s hc => ?_
  refine WP.mono (VG.Proof.ChaCha20.Arm.load_ok hp hg₁ hc) fun s₂ ⟨hh₂, hm₂, hrd₂, hwr₂, hr1₂⟩ => ?_
  have hw₂ : VG.Proof.ChaCha20.Arm.bufR s₀ ∈ s₂.wr := by rw [hwr₂, hc.wr]; exact hw₀
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.rounds_ok hh₂ (fun off ho => by rw [hr1₂]; exact hp.eaB ho) hw₂ 10)
    fun s₃ hR => ?_)
  have hw₃ : VG.Proof.ChaCha20.Arm.bufR s₀ ∈ s₃.wr := by rw [hR.wr]; exact hw₂
  have hr1₃ : s₃.gpr .r1 = VG.Proof.ChaCha20.Arm.buf s₀ := hR.r1.trans hr1₂
  rw [VG.Proof.ChaCha20.Arm.finish_split, WP.block_append_iff, WP.block_append_iff]
  have hs₀ : VG.Proof.ChaCha20.Arm.SI (VG.Proof.ChaCha20.Arm.BA s₀) (VG.Proof.ChaCha20.Arm.Rs s₀) s₃ 0 s₃ :=
    ⟨fun _ _ h => absurd h (by lit_omega), fun j hj _ => hR.holds j hj, Frame.refl _ _, rfl, rfl, rfl⟩
  refine WP.mono (wp_range_flatMap (M := isa) (VG.Proof.ChaCha20.Arm.SI (VG.Proof.ChaCha20.Arm.BA s₀) (VG.Proof.ChaCha20.Arm.Rs s₀) s₃)
    (fun k s hk hs => VG.Proof.ChaCha20.Arm.store_step hp hw₃ hr1₃ hk hs) 16 (Nat.le_refl _) s₃ hs₀) fun s₄ hS => ?_
  have hw₄ : VG.Proof.ChaCha20.Arm.bufR s₀ ∈ s₄.wr := by rw [hS.wr]; exact hw₃
  have hr1₄ : s₄.gpr .r1 = VG.Proof.ChaCha20.Arm.buf s₀ := hS.r1.trans hr1₃
  have hinw : ∀ j (hj : j < 16),
      s₄.mem.readW (VG.Proof.ChaCha20.Arm.BA s₀ + BitVec.ofNat 64 (inOff j)) 32 = (VG.Proof.ChaCha20.Arm.V s₀)[j] := by
    intro j hj
    rw [VG.Proof.ChaCha20.Arm.read_in hS.frame (fun j hj => VG.Proof.ChaCha20.Arm.disjoint_sub _ (by simp only [inOff]; omega)
        (by simp only [inOff]; omega) (by lit_omega)) hj,
      VG.Proof.ChaCha20.Arm.read_in hR.frame (fun j hj => VG.Proof.ChaCha20.Arm.disjoint_sub _ (by simp only [inOff]; omega)
        (by simp only [inOff]; omega) (by lit_omega)) hj, hm₂]
    exact hc.inw j hj hj
  have ha₀ : VG.Proof.ChaCha20.Arm.AI (VG.Proof.ChaCha20.Arm.BA s₀) (VG.Proof.ChaCha20.Arm.Rs s₀) (VG.Proof.ChaCha20.Arm.V s₀) s₄ 0 s₄ :=
    ⟨fun j hj => by simp only [Nat.not_lt_zero, ite_false]; exact hS.out j hj hj, hinw,
      Frame.refl _ _, rfl, rfl, rfl⟩
  refine WP.mono (wp_range_flatMap (M := isa) (VG.Proof.ChaCha20.Arm.AI (VG.Proof.ChaCha20.Arm.BA s₀) (VG.Proof.ChaCha20.Arm.Rs s₀) (VG.Proof.ChaCha20.Arm.V s₀) s₄)
    (fun k s hk ha => VG.Proof.ChaCha20.Arm.add_step hp hw₄ hr1₄ hk ha) 16 (Nat.le_refl _) s₄ ha₀) fun s₅ hA => ?_
  have hwork : Frame [VG.Proof.ChaCha20.Arm.workR (VG.Proof.ChaCha20.Arm.BA s₀)] s₁.mem s₅.mem := by
    refine (VG.Proof.ChaCha20.Arm.frame_work (a := 64) (len := 80) (by lit_omega) hc.frame).trans ?_
    rw [← hm₂]
    refine (VG.Proof.ChaCha20.Arm.frame_work (a := 128) (len := 16) (by lit_omega) hR.frame).trans ?_
    exact (VG.Proof.ChaCha20.Arm.frame_work (a := 0) (len := 64) (by lit_omega) hS.frame).trans
      (VG.Proof.ChaCha20.Arm.frame_work (a := 0) (len := 64) (by lit_omega) hA.frame)
  have hsaved : VG.Proof.ChaCha20.Arm.Saved s₀ s₅.mem := VG.Proof.ChaCha20.Arm.saved_frame (hm₁ ▸ VG.Proof.ChaCha20.Arm.saveMem_saved s₀) hwork
  refine WP.mono (VG.Proof.ChaCha20.Arm.restore_ok hp hsaved (hA.r1.trans hr1₄) (by rw [hA.wr, hS.wr, hR.wr, hwr₂, hc.wr]))
    fun s' ⟨hm', hg'⟩ => ⟨hg', ?_⟩
  show VG.Spec.ChaCha20.stateAt s'.mem (VG.Proof.ChaCha20.Arm.BA s₀) = Spec.ChaCha20.block (VG.Proof.ChaCha20.Arm.V s₀)
  rw [hm']
  exact VG.Proof.ChaCha20.Arm.block_post fun j hj => by simpa [hj] using hA.out j hj

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 256⟩]

theorem block_correct (s : State) (hs : Proof.ChaCha20.blockArm.pre s) :
    ∃ t s', Exec isa block s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.blockArm.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.ChaCha20.Arm.correct (VG.Proof.ChaCha20.Arm.pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩

theorem block_ct :
    ConstantTime isa Proof.ChaCha20.blockArm.pre Proof.ChaCha20.blockArm.pub Impl.ChaCha20.Arm.block := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> with_reducible assumption

theorem block_verified :
    Verified Arm.target Impl.ChaCha20.Arm.block (Spec.ChaCha20.blockContract Arm.abi) :=
  Verified.of_correct VG.Proof.ChaCha20.Arm.block_correct VG.Proof.ChaCha20.Arm.block_ct (by
    sig_implies [Spec.ChaCha20.blockContract, Spec.ChaCha20.blockSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Proof.ChaCha20.blockArm, State.addr]
      [satState] using VG.Proof.ChaCha20.Arm.satState)

end VG.Proof.ChaCha20.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.Arm.Xor`. -/
section

/-!
# ChaCha20 keystream XOR on ARMv7

The per-instruction WP rules are those of the streaming hash proofs
(`Proof/MdStream/Arm/Common.lean`).

The call of the block function goes through its `Verified` proof
(`WP.call`): it keeps `r1` (which its code never writes) and `r4`–`r11`,
so the loop's variables survive it, and changes memory only in the first
256 bytes of `buf`. The block function writes `r7`–`r11`, so that the code
keeps our caller's values of those is part of the invariants (`Keep`).

For constant time, the taint analysis runs through the block function's
code too: its saves and restores of `r4`–`r6` (our public pointers and
length) are public slots of `buf`, which needs lower bounds on the lengths
of all three writable regions, `0` for the data (`τ₀`).
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20 VG.Arm

/-- 32-bit ARM contract for `vg_chacha20_xor(state: *mut [u32; 16], data: *mut
u8, len: usize, buf: *mut [u32; 80])`: XORs the first `len` bytes of the
keystream of the state at `state` into the `len` bytes at `data`.

The code may read and write `state` (64 bytes; its contents on exit are
unspecified), `data` (`len` bytes) and `buf` (320 bytes of working space).
They may not overlap each other, and none may wrap around the end of the
(32-bit) address space. The return address is in `lr`, not on the stack, and
the code uses no stack. The pointers and the length are public; the state and
the data are secret. -/
def xorArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 64⟩
    let data : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
    let buf : Region := ⟨State.addr (s.gpr .r3), 320⟩
    s.rd = [] ∧ s.wr = [state, data, buf] ∧
    state.Disjoint data ∧ state.Disjoint buf ∧ data.Disjoint buf ∧
    (s.gpr .r0).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + 320 ≤ 2 ^ 32
  post s s' :=
    bytesAt s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
      List.zipWith (· ^^^ ·) (bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
        (keystream (stateAt s.mem (State.addr (s.gpr .r0))) (s.gpr .r2).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.Arm.Xor

open VG VG.Arm VG.Impl.ChaCha20.Arm.Xor
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_sub wp_subs
  wp_cmp wp_ldr wp_str wp_ldrb wp_strb eval_eq eval_ne ofNat_beq_zero sub_ofNat ofNat_shr)
open VG.Proof.ChaCha20 (ctr ctr_zero ctr_succ keystream_getD length_keystream bytesAt_xor
  serialize_stateAt)
open VG.Proof.ChaCha20.Arm (toNat_ofNat_lt contains_off readW_writeW_off block_correct)
open VG.Spec.ChaCha20 (stateAt keystream serialize bytesAt)

/-! ## One instruction at a time -/

theorem wp_eor {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {o : Op2}
    {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho])
    (k _ (Upd.setReg _ _ _))

theorem imm0 : encodable 0 = true := by decide
theorem imm1 : encodable 1 = true := by decide
theorem imm64 : encodable 64 = true := by decide

/-! ## Arithmetic -/

theorem add_zero' (x : BitVec 32) : x + 0 = x := by simp

theorem sub_zero' (x : BitVec 32) : x - 0 = x := by simp

theorem add_ofNat32 (p : BitVec 32) (a b : Nat) :
    p + BitVec.ofNat 32 a + BitVec.ofNat 32 b = p + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem add_one' (p : BitVec 32) (a : Nat) :
    p + BitVec.ofNat 32 a + 1 = p + BitVec.ofNat 32 (a + 1) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Proof.ChaCha20.Arm.Xor.add_ofNat32]

theorem sub_one' {a : Nat} (h : 1 ≤ a) : BitVec.ofNat 32 a - 1 = BitVec.ofNat 32 (a - 1) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat h]

/-- `[x, #0]` with `x = p + k`, as a 64-bit address. -/
theorem ea0 {p : BitVec 32} {k : Nat} (h : p.toNat + k < 2 ^ 32) :
    State.addr (p + BitVec.ofNat 32 k + BitVec.ofNat 32 0) = State.addr p + BitVec.ofNat 64 k := by
  rw [show BitVec.ofNat 32 0 = 0 from rfl, VG.Proof.ChaCha20.Arm.Xor.add_zero']
  exact addr_add h

theorem addr_toNat (p : BitVec 32) : (State.addr p).toNat = p.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := p.isLt; omega)

/-- The byte stored by `eor r0, r0, r12; strb r0, …` after two `ldrb`s. -/
theorem xor_setWidth (a b : Byte) : ((a.setWidth 32 ^^^ b.setWidth 32).setWidth 8) = a ^^^ b := by
  ext i hi; simp

theorem eval_ne_ofNat (s : State) {k : Nat} (hk : k < 2 ^ 32) {x : BitVec 32}
    (hz : s.z = (x - 0 == 0)) (hx : x = BitVec.ofNat 32 k) : isa.eval .ne s = some (decide (k ≠ 0)) := by
  have e : isa.eval .ne s = some !s.z := eval_ne s
  rw [e, hz, hx, VG.Proof.ChaCha20.Arm.Xor.sub_zero', ofNat_beq_zero hk]
  simp

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev stP : BitVec 32 := s₀.gpr .r0
abbrev dP : BitVec 32 := s₀.gpr .r1
abbrev L : Nat := (s₀.gpr .r2).toNat
abbrev bP : BitVec 32 := s₀.gpr .r3
abbrev stA : Addr := State.addr (VG.Proof.ChaCha20.Arm.Xor.stP s₀)
abbrev dA : Addr := State.addr (VG.Proof.ChaCha20.Arm.Xor.dP s₀)
abbrev bA : Addr := State.addr (VG.Proof.ChaCha20.Arm.Xor.bP s₀)
abbrev stRg : Region := ⟨VG.Proof.ChaCha20.Arm.Xor.stA s₀, 64⟩
abbrev dRg : Region := ⟨VG.Proof.ChaCha20.Arm.Xor.dA s₀, VG.Proof.ChaCha20.Arm.Xor.L s₀⟩
abbrev bRg : Region := ⟨VG.Proof.ChaCha20.Arm.Xor.bA s₀, 320⟩
/-- The state, the data and the keystream on entry. -/
abbrev S0 : CState := stateAt s₀.mem (VG.Proof.ChaCha20.Arm.Xor.stA s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (VG.Proof.ChaCha20.Arm.Xor.dA s₀ + BitVec.ofNat 64 k)
abbrev KS : List Byte := keystream (VG.Proof.ChaCha20.Arm.Xor.S0 s₀) (VG.Proof.ChaCha20.Arm.Xor.L s₀)
/-- The bytes of data done before block `j`. -/
abbrev P (j : Nat) : Nat := min (64 * j) (VG.Proof.ChaCha20.Arm.Xor.L s₀)
/-- How many bytes of block `j` are used. -/
abbrev C (j : Nat) : Nat := min 64 (VG.Proof.ChaCha20.Arm.Xor.L s₀ - VG.Proof.ChaCha20.Arm.Xor.P s₀ j)
end

theorem L_lt (s₀ : State) : VG.Proof.ChaCha20.Arm.Xor.L s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt

structure XPre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [VG.Proof.ChaCha20.Arm.Xor.stRg s₀, VG.Proof.ChaCha20.Arm.Xor.dRg s₀, VG.Proof.ChaCha20.Arm.Xor.bRg s₀]
  st_d : (VG.Proof.ChaCha20.Arm.Xor.stRg s₀).Disjoint (VG.Proof.ChaCha20.Arm.Xor.dRg s₀)
  st_b : (VG.Proof.ChaCha20.Arm.Xor.stRg s₀).Disjoint (VG.Proof.ChaCha20.Arm.Xor.bRg s₀)
  d_b : (VG.Proof.ChaCha20.Arm.Xor.dRg s₀).Disjoint (VG.Proof.ChaCha20.Arm.Xor.bRg s₀)
  st_fit : (VG.Proof.ChaCha20.Arm.Xor.stP s₀).toNat + 64 ≤ 2 ^ 32
  d_fit : (VG.Proof.ChaCha20.Arm.Xor.dP s₀).toNat + VG.Proof.ChaCha20.Arm.Xor.L s₀ ≤ 2 ^ 32
  b_fit : (VG.Proof.ChaCha20.Arm.Xor.bP s₀).toNat + 320 ≤ 2 ^ 32

theorem XPre.of (s₀ : State) (h : Proof.ChaCha20.xorArm.pre s₀) : VG.Proof.ChaCha20.Arm.Xor.XPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

namespace XPre
variable {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Xor.XPre s₀)
include hp

theorem eaB {d : Nat} (h : d < 320) : State.addr (VG.Proof.ChaCha20.Arm.Xor.bP s₀ + BitVec.ofNat 32 d) = VG.Proof.ChaCha20.Arm.Xor.bA s₀ + BitVec.ofNat 64 d :=
  addr_add (by have := hp.b_fit; omega)

theorem eaS {d : Nat} (h : d < 64) : State.addr (VG.Proof.ChaCha20.Arm.Xor.stP s₀ + BitVec.ofNat 32 d) = VG.Proof.ChaCha20.Arm.Xor.stA s₀ + BitVec.ofNat 64 d :=
  addr_add (by have := hp.st_fit; omega)

theorem inB {d n : Nat} (h : d + n ≤ 320) (rd : List Region) {wr : List Region}
    (hw : wr = s₀.wr) : InRegions (rd ++ wr) (VG.Proof.ChaCha20.Arm.Xor.bA s₀ + BitVec.ofNat 64 d) n :=
  ⟨VG.Proof.ChaCha20.Arm.Xor.bRg s₀, by simp [hw, hp.wr], VG.Proof.ChaCha20.Arm.contains_off h (by lit_omega)⟩

theorem outB {d n : Nat} (h : d + n ≤ 320) {wr : List Region} (hw : wr = s₀.wr) :
    InRegions wr (VG.Proof.ChaCha20.Arm.Xor.bA s₀ + BitVec.ofNat 64 d) n :=
  ⟨VG.Proof.ChaCha20.Arm.Xor.bRg s₀, by simp [hw, hp.wr], VG.Proof.ChaCha20.Arm.contains_off h (by lit_omega)⟩

end XPre

/-- Our caller's `r4`, `r5`, `r6` and `lr`, saved in `buf[256, 272)`. -/
abbrev XSaved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (VG.Proof.ChaCha20.Arm.Xor.bA s₀) s₀.gpr saved

theorem saved_slots : Spill.Slots 256 272 saved := by decide

/-- The callee-saved registers that the code keeps as they are (the block
function preserves them too). -/
def kept : List Reg := [.r7, .r8, .r9, .r10, .r11]

def Keep (s₀ s : State) : Prop := ∀ r ∈ VG.Proof.ChaCha20.Arm.Xor.kept, s.gpr r = s₀.gpr r

theorem Keep.upd {s₀ s s' : State} {d : Reg} {v : BitVec 32} (h : VG.Proof.ChaCha20.Arm.Xor.Keep s₀ s) (u : Upd s s' d v)
    (hd : d ∉ VG.Proof.ChaCha20.Arm.Xor.kept := by decide) : VG.Proof.ChaCha20.Arm.Xor.Keep s₀ s' :=
  fun r hr => by rw [u.other r (fun e => hd (e ▸ hr)), h r hr]

theorem Keep.mupd {s₀ s s' : State} {m : Mem} (h : VG.Proof.ChaCha20.Arm.Xor.Keep s₀ s) (u : Mupd s s' m) : VG.Proof.ChaCha20.Arm.Xor.Keep s₀ s' :=
  fun r hr => by rw [u.gpr, h r hr]

theorem Keep.fupd {s₀ s s' : State} (h : VG.Proof.ChaCha20.Arm.Xor.Keep s₀ s) (u : Fupd s s') : VG.Proof.ChaCha20.Arm.Xor.Keep s₀ s' :=
  fun r hr => by rw [u.gpr, h r hr]

/-- Before block `j`, but for the flags. -/
structure Inv (s₀ : State) (j : Nat) (s : State) : Prop where
  r1 : s.gpr .r1 = VG.Proof.ChaCha20.Arm.Xor.bP s₀
  r4 : s.gpr .r4 = VG.Proof.ChaCha20.Arm.Xor.stP s₀
  r5 : s.gpr .r5 = VG.Proof.ChaCha20.Arm.Xor.dP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Xor.P s₀ j)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Xor.L s₀ - VG.Proof.ChaCha20.Arm.Xor.P s₀ j)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : VG.Proof.ChaCha20.Arm.Xor.Keep s₀ s
  cnt : stateAt s.mem (VG.Proof.ChaCha20.Arm.Xor.stA s₀) = ctr (VG.Proof.ChaCha20.Arm.Xor.S0 s₀) j
  data : ∀ k < VG.Proof.ChaCha20.Arm.Xor.L s₀, s.mem (VG.Proof.ChaCha20.Arm.Xor.dA s₀ + BitVec.ofNat 64 k) =
    if k < VG.Proof.ChaCha20.Arm.Xor.P s₀ j then VG.Proof.ChaCha20.Arm.Xor.D0 s₀ k ^^^ (VG.Proof.ChaCha20.Arm.Xor.KS s₀).getD k 0 else VG.Proof.ChaCha20.Arm.Xor.D0 s₀ k
  saved : VG.Proof.ChaCha20.Arm.Xor.XSaved s₀ s.mem

/-- Before block `j` (the loop's invariant): `Z` says whether data remains. -/
structure OInv (s₀ : State) (j : Nat) (s : State) : Prop extends VG.Proof.ChaCha20.Arm.Xor.Inv s₀ j s where
  z : s.z = (s.gpr .r6 - 0 == 0)

/-! ## Memory -/

/-- The state after its counter (word 12) is stored. -/
theorem stateAt_writeW_counter (m : Mem) (p : Addr) (v : BitVec 32) :
    stateAt (m.writeW (p + BitVec.ofNat 64 48) v) p = (stateAt m p).set 12 v := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : 12 = i
  · subst h
    simp only [ite_true]
    exact Mem.readW_writeW_self32 _ _ _
  · simp only [h, ite_false]
    exact VG.Proof.ChaCha20.Arm.readW_writeW_off m p v (by lit_omega) (by lit_omega) (by lit_omega)

/-- A state in memory outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (VG.Proof.ChaCha20.Arm.contains_off (by lit_omega) (by lit_omega)) hd (by decide)

/-- The first 256 bytes of `buf`, which the block function may write. -/
abbrev b256 (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.Arm.Xor.bA s₀, 256⟩

/-- Where our caller's registers are saved. -/
abbrev savR (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.Arm.Xor.bA s₀ + BitVec.ofNat 64 256, 16⟩

theorem b256_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.Arm.Xor.b256 s₀) (VG.Proof.ChaCha20.Arm.Xor.bRg s₀) := Region.sub_prefix (by lit_omega)

theorem savR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.Arm.Xor.savR s₀) (VG.Proof.ChaCha20.Arm.Xor.bRg s₀) := Offset.sub_base _ (by lit_omega)

theorem savR_b256 (s₀ : State) : (VG.Proof.ChaCha20.Arm.Xor.savR s₀).Disjoint (VG.Proof.ChaCha20.Arm.Xor.b256 s₀) := Offset.disjoint_base _ (by lit_omega) (by lit_omega)

/-- The saved registers survive a frame that does not touch them. -/
theorem XSaved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : VG.Proof.ChaCha20.Arm.Xor.XSaved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (VG.Proof.ChaCha20.Arm.Xor.savR s₀).Disjoint r) : VG.Proof.ChaCha20.Arm.Xor.XSaved s₀ m' :=
  Spill.Saved.frame h VG.Proof.ChaCha20.Arm.Xor.saved_slots hf hd

/-- Distinct bytes of the data are at distinct addresses. -/
theorem data_ne {s₀ : State} {k k' : Nat} (hk : k < VG.Proof.ChaCha20.Arm.Xor.L s₀) (hk' : k' < VG.Proof.ChaCha20.Arm.Xor.L s₀) (h : k' ≠ k) :
    VG.Proof.ChaCha20.Arm.Xor.dA s₀ + BitVec.ofNat 64 k' ≠ VG.Proof.ChaCha20.Arm.Xor.dA s₀ + BitVec.ofNat 64 k := by
  have hL := VG.Proof.ChaCha20.Arm.Xor.L_lt s₀
  intro he
  have e : BitVec.ofNat 64 k' = BitVec.ofNat 64 k := by
    have e := congrArg (· - VG.Proof.ChaCha20.Arm.Xor.dA s₀) he; simpa using e
  have := congrArg BitVec.toNat e
  rw [VG.Proof.ChaCha20.Arm.toNat_ofNat_lt (by lit_omega), VG.Proof.ChaCha20.Arm.toNat_ofNat_lt (by lit_omega)] at this
  exact h this

theorem writeW8_apply (m : Mem) (a x : Addr) (v : Byte) :
    (m.writeW a v) x = if x = a then v else m x := by
  simp only [Mem.writeW, Mem.write]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 8 / 8 := by
      intro h'
      apply h
      have h0 : (x - a).toNat = 0 := by omega
      have := BitVec.eq_of_toNat_eq (x := x - a) (y := 0) (by rw [h0]; rfl)
      rw [← BitVec.sub_add_cancel x a, this]; exact BitVec.zero_add a
    simp only [this, h, ↓reduceIte]

/-! ## The prologue -/

theorem prologue_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Xor.XPre s₀) :
    WP isa (.block (save ++ ([.mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2),
      .mov .r1 (.reg .r3), .cmp .r6 (.imm 0)] : List Instr))) s₀ (VG.Proof.ChaCha20.Arm.Xor.OInv s₀ 0) := by
  refine Spill.save_slots_ok VG.Proof.ChaCha20.Arm.Xor.saved_slots (Nat.le_trans (Nat.add_le_add_left (by decide : 272 ≤ 320) _) hp.b_fit)
    (fun _ _ hd => hp.outB (by omega) rfl) ?_
  refine wp_mov (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ =>
    wp_mov (op2_reg _ _) fun s₇ u₇ => wp_mov (op2_reg _ _) fun s₈ u₈ =>
    wp_cmp (n := .r6) (op2_imm VG.Proof.ChaCha20.Arm.Xor.imm0) fun s₉ f₉ hz => WP.block_nil ?_
  have g : ∀ r, s₉.gpr r = s₈.gpr r := fun r => by rw [f₉.gpr]
  have hm : s₉.mem = Spill.saveMem s₀.mem (VG.Proof.ChaCha20.Arm.Xor.bA s₀) s₀.gpr saved := by
    rw [f₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]
  have hf : Frame [VG.Proof.ChaCha20.Arm.Xor.bRg s₀] s₀.mem s₉.mem := by
    rw [hm]; exact Spill.saveMem_frame _ _ _ (by decide) saved (by decide)
  have hr6 : s₉.gpr .r6 = s₀.gpr .r2 := by
    rw [g, u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_⟩, ?_⟩
  · rw [g, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide)]
  · rw [g, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  · rw [g, u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide)]
    simp [VG.Proof.ChaCha20.Arm.Xor.P]
  · rw [hr6]; simp [VG.Proof.ChaCha20.Arm.Xor.P]
  · rw [f₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd]
  · rw [f₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr]
  · intro r hr
    have hr' : r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r1 := by
      simp only [VG.Proof.ChaCha20.Arm.Xor.kept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g, u₈.other _ hr'.2.2.2, u₇.other _ hr'.2.2.1, u₆.other _ hr'.2.1, u₅.other _ hr'.1]
  · rw [VG.Proof.ChaCha20.Arm.Xor.stateAt_frame hf (by simpa using hp.st_b), ctr_zero]
  · simp only [VG.Proof.ChaCha20.Arm.Xor.P, Nat.mul_zero, Nat.zero_min, Nat.not_lt_zero, ite_false]
    exact hf.bytes (R := VG.Proof.ChaCha20.Arm.Xor.dRg s₀) (by simpa using hp.d_b) (show VG.Proof.ChaCha20.Arm.Xor.L s₀ ≤ 2 ^ 64 by have := VG.Proof.ChaCha20.Arm.Xor.L_lt s₀; omega) hk
  · rw [hm]; exact Spill.saveMem_saved _ _ _ _ VG.Proof.ChaCha20.Arm.Xor.saved_slots
  · rw [hz, g]

/-! ## Calling the block function -/

theorem block_keeps_r1 : ∀ i ∈ instrs Impl.ChaCha20.Arm.block, dstOf i ≠ some .r1 := by
  have : ((instrs Impl.ChaCha20.Arm.block).all fun i => dstOf i != some .r1) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp this i hi

/-- After the block function: `buf` holds block `j`'s keystream. -/
structure AInv (s₀ : State) (j : Nat) (s : State) : Prop extends VG.Proof.ChaCha20.Arm.Xor.Inv s₀ j s where
  ks : ∀ t < 64, s.mem (VG.Proof.ChaCha20.Arm.Xor.bA s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.Arm.Xor.S0 s₀) j))).getD t 0

theorem call_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Xor.XPre s₀) {j : Nat} {s : State} (h : VG.Proof.ChaCha20.Arm.Xor.Inv s₀ j s)
    (h0 : s.gpr .r0 = VG.Proof.ChaCha20.Arm.Xor.stP s₀) :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.Arm.block) s (VG.Proof.ChaCha20.Arm.Xor.AInv s₀ j) := by
  have c0 : s.callEntry.gpr .r0 = VG.Proof.ChaCha20.Arm.Xor.stP s₀ := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .r1 = VG.Proof.ChaCha20.Arm.Xor.bP s₀ := (State.callEntry_gpr _ (by decide)).trans h.r1
  have hwr : s.wr = [VG.Proof.ChaCha20.Arm.Xor.stRg s₀, VG.Proof.ChaCha20.Arm.Xor.dRg s₀, VG.Proof.ChaCha20.Arm.Xor.bRg s₀] := by rw [h.wr, hp.wr]
  have hrd : s.rd = [] := by rw [h.rd, hp.rd]
  refine WP.call (k := Proof.ChaCha20.blockArm) VG.Proof.ChaCha20.Arm.block_correct
    (rd := [VG.Proof.ChaCha20.Arm.Xor.stRg s₀]) (wr := [VG.Proof.ChaCha20.Arm.Xor.b256 s₀]) ?_ ?_ ?_ ?_
  · simp only [Proof.ChaCha20.blockArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, (hp.st_b.sub_right (VG.Proof.ChaCha20.Arm.Xor.b256_sub s₀)).symm, hp.st_fit,
      by have := hp.b_fit; omega⟩
  · rw [hrd, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.ChaCha20.Arm.Xor.stRg s₀, by simp, 0, by simp, show 0 + 64 ≤ 64 by omega⟩
    · exact ⟨VG.Proof.ChaCha20.Arm.Xor.bRg s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩
  · rw [hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.ChaCha20.Arm.Xor.bRg s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩
  · intro s₂ hrd₂ hwr₂ _ hf hcs hkeep hpost
    have hst : stateAt s₂.mem (VG.Proof.ChaCha20.Arm.Xor.stA s₀) = stateAt s.mem (VG.Proof.ChaCha20.Arm.Xor.stA s₀) :=
      VG.Proof.ChaCha20.Arm.Xor.stateAt_frame hf (by simpa using hp.st_b.sub_right (VG.Proof.ChaCha20.Arm.Xor.b256_sub s₀))
    simp only [Proof.ChaCha20.blockArm, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, h.cnt] at hpost
    have pr : ∀ r ∈ preserved, r ≠ .lr → s₂.gpr r = s.gpr r := hcs
    have hk₂ : VG.Proof.ChaCha20.Arm.Xor.Keep s₀ s₂ := by
      intro r hr
      simp only [VG.Proof.ChaCha20.Arm.Xor.kept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      · rw [pr _ (by decide) (by decide)]; exact h.keep _ (by decide)
    refine ⟨⟨by rw [hkeep .r1 VG.Proof.ChaCha20.Arm.Xor.block_keeps_r1 (by decide), h.r1],
      by rw [pr .r4 (by decide) (by decide), h.r4],
      by rw [pr .r5 (by decide) (by decide), h.r5],
      by rw [pr .r6 (by decide) (by decide), h.r6],
      by rw [hrd₂, h.rd], by rw [hwr₂, h.wr], hk₂, by rw [hst, h.cnt], fun k hk => ?_,
      h.saved.frame hf (by simpa using VG.Proof.ChaCha20.Arm.Xor.savR_b256 s₀)⟩, fun t ht => ?_⟩
    · rw [hf.bytes (R := VG.Proof.ChaCha20.Arm.Xor.dRg s₀) (by simpa using hp.d_b.sub_right (VG.Proof.ChaCha20.Arm.Xor.b256_sub s₀))
        (show VG.Proof.ChaCha20.Arm.Xor.L s₀ ≤ 2 ^ 64 by have := VG.Proof.ChaCha20.Arm.Xor.L_lt s₀; omega) hk]
      exact h.data k hk
    · rw [← serialize_stateAt s₂.mem (VG.Proof.ChaCha20.Arm.Xor.bA s₀) ht, hpost]

/-! ## The bytes of block `j` -/

/-- Before byte `i` of block `j`. -/
structure IInv (s₀ : State) (j i : Nat) (s : State) : Prop where
  r1 : s.gpr .r1 = VG.Proof.ChaCha20.Arm.Xor.bP s₀
  r4 : s.gpr .r4 = VG.Proof.ChaCha20.Arm.Xor.stP s₀
  r5 : s.gpr .r5 = VG.Proof.ChaCha20.Arm.Xor.dP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Xor.P s₀ j + i)
  r3 : s.gpr .r3 = VG.Proof.ChaCha20.Arm.Xor.bP s₀ + BitVec.ofNat 32 i
  r2 : s.gpr .r2 = BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Xor.C s₀ j - i)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Xor.L s₀ - VG.Proof.ChaCha20.Arm.Xor.P s₀ j - VG.Proof.ChaCha20.Arm.Xor.C s₀ j)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : VG.Proof.ChaCha20.Arm.Xor.Keep s₀ s
  cnt : stateAt s.mem (VG.Proof.ChaCha20.Arm.Xor.stA s₀) = ctr (VG.Proof.ChaCha20.Arm.Xor.S0 s₀) j
  data : ∀ k < VG.Proof.ChaCha20.Arm.Xor.L s₀, s.mem (VG.Proof.ChaCha20.Arm.Xor.dA s₀ + BitVec.ofNat 64 k) =
    if k < VG.Proof.ChaCha20.Arm.Xor.P s₀ j + i then VG.Proof.ChaCha20.Arm.Xor.D0 s₀ k ^^^ (VG.Proof.ChaCha20.Arm.Xor.KS s₀).getD k 0 else VG.Proof.ChaCha20.Arm.Xor.D0 s₀ k
  saved : VG.Proof.ChaCha20.Arm.Xor.XSaved s₀ s.mem
  ks : ∀ t < 64, s.mem (VG.Proof.ChaCha20.Arm.Xor.bA s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.Arm.Xor.S0 s₀) j))).getD t 0

/-- `n = min(64, r6)`, the rest of `r6`, and the keystream pointer. -/
def selA : List Instr := [.mov .r2 (.shifted .r6 .lsr 6), .cmp .r2 (.imm 0)]
def selB : List Instr := [.dp .sub .r6 .r6 (.reg .r2), .mov .r3 (.reg .r1)]

theorem sel_ok {s₀ : State} {j : Nat} (hj : VG.Proof.ChaCha20.Arm.Xor.P s₀ j < VG.Proof.ChaCha20.Arm.Xor.L s₀) {s : State} (h : VG.Proof.ChaCha20.Arm.Xor.AInv s₀ j s) :
    WP isa (.seq (.block VG.Proof.ChaCha20.Arm.Xor.selA)
      (.seq (.ite .eq (.block [.mov .r2 (.reg .r6)]) (.block [.mov .r2 (.imm 64)]))
        (.block VG.Proof.ChaCha20.Arm.Xor.selB))) s (VG.Proof.ChaCha20.Arm.Xor.IInv s₀ j 0) := by
  have hL := VG.Proof.ChaCha20.Arm.Xor.L_lt s₀
  have hC : VG.Proof.ChaCha20.Arm.Xor.C s₀ j = min 64 (VG.Proof.ChaCha20.Arm.Xor.L s₀ - VG.Proof.ChaCha20.Arm.Xor.P s₀ j) := rfl
  refine WP.seq (wp_mov (op2_lsr (by decide)) fun s₁ u₁ =>
    wp_cmp (n := .r2) (op2_imm VG.Proof.ChaCha20.Arm.Xor.imm0) fun s₂ f₂ hz => WP.block_nil ?_)
  have hx2 : s₁.gpr .r2 = BitVec.ofNat 32 ((VG.Proof.ChaCha20.Arm.Xor.L s₀ - VG.Proof.ChaCha20.Arm.Xor.P s₀ j) / 64) := by
    rw [u₁.gpr, h.r6, ofNat_shr (by lit_omega), show (2 : Nat) ^ 6 = 64 from rfl]
  have hx6 : s₂.gpr .r6 = BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Xor.L s₀ - VG.Proof.ChaCha20.Arm.Xor.P s₀ j) := by
    rw [f₂.gpr, u₁.other _ (by decide), h.r6]
  refine WP.seq (WP.mono (Q := fun s₃ : State => s₃.gpr .r2 = BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Xor.C s₀ j) ∧
      (∀ r, r ≠ .r2 → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr) ?_
    fun s₃ ⟨f₁, f₂', f₃, f₄, f₅⟩ => ?_)
  · refine WP.ite (decide ((VG.Proof.ChaCha20.Arm.Xor.L s₀ - VG.Proof.ChaCha20.Arm.Xor.P s₀ j) / 64 = 0))
      (by have e : isa.eval .eq s₂ = some s₂.z := eval_eq s₂
          rw [e, hz, hx2, VG.Proof.ChaCha20.Arm.Xor.sub_zero', ofNat_beq_zero (by lit_omega)])
      (fun ht => wp_mov (op2_reg _ _) fun s₃ u₃ => WP.block_nil ⟨?_, u₃.other, u₃.mem, u₃.rd, u₃.wr⟩)
      (fun hf => wp_mov (op2_imm VG.Proof.ChaCha20.Arm.Xor.imm64) fun s₃ u₃ => WP.block_nil ⟨?_, u₃.other, u₃.mem, u₃.rd, u₃.wr⟩)
    · simp only [decide_eq_true_eq] at ht
      rw [u₃.gpr, hx6, show VG.Proof.ChaCha20.Arm.Xor.C s₀ j = VG.Proof.ChaCha20.Arm.Xor.L s₀ - VG.Proof.ChaCha20.Arm.Xor.P s₀ j by omega]
    · simp only [decide_eq_false_iff_not] at hf
      rw [u₃.gpr, show VG.Proof.ChaCha20.Arm.Xor.C s₀ j = 64 by omega]; rfl
  · refine wp_sub (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
    have g : ∀ r, r ≠ .r2 → r ≠ .r6 → r ≠ .r3 → s₅.gpr r = s.gpr r :=
      fun r h₁ h₂ h₃ => by
        rw [u₅.other r h₃, u₄.other r h₂, f₂' r h₁, f₂.gpr, u₁.other r h₁]
    have gm : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, f₃, f₂.mem, u₁.mem]
    have gk : VG.Proof.ChaCha20.Arm.Xor.Keep s₀ s₅ := fun r hr => by
      rw [g r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)
        (by rintro rfl; revert hr; decide), h.keep r hr]
    refine ⟨by rw [g _ (by decide) (by decide) (by decide), h.r1],
      by rw [g _ (by decide) (by decide) (by decide), h.r4],
      by rw [g _ (by decide) (by decide) (by decide), h.r5, Nat.add_zero],
      by rw [u₅.gpr, u₄.other _ (by decide), f₂' _ (by decide), f₂.gpr, u₁.other _ (by decide),
        h.r1]; simp,
      by rw [u₅.other _ (by decide), u₄.other _ (by decide), f₁, Nat.sub_zero],
      by rw [u₅.other _ (by decide), u₄.gpr, f₂' _ (by decide), f₁, hx6, sub_ofNat (by lit_omega)],
      by rw [u₅.rd, u₄.rd, f₄, f₂.rd, u₁.rd, h.rd], by rw [u₅.wr, u₄.wr, f₅, f₂.wr, u₁.wr, h.wr],
      gk, by rw [gm, h.cnt], fun k hk => by rw [gm, h.data k hk, Nat.add_zero],
      by rw [gm]; exact h.saved, fun t ht => by rw [gm]; exact h.ks t ht⟩

/-! ## One byte -/

def xorBody : List Instr :=
  [.ldrb .r0 .r5 0, .ldrb .r12 .r3 0, .dp .eor .r0 .r0 (.reg .r12), .strb .r0 .r5 0,
    .dp .add .r5 .r5 (.imm 1), .dp .add .r3 .r3 (.imm 1), .subs .r2 .r2 (.imm 1)]

theorem xorLoop_eq : xorLoop = .loop (.block VG.Proof.ChaCha20.Arm.Xor.xorBody) .ne := rfl

/-- `P j = 64 j` while blocks remain. -/
theorem P_eq {s₀ : State} {j : Nat} (hj : VG.Proof.ChaCha20.Arm.Xor.P s₀ j < VG.Proof.ChaCha20.Arm.Xor.L s₀) : VG.Proof.ChaCha20.Arm.Xor.P s₀ j = 64 * j := by
  simp only [VG.Proof.ChaCha20.Arm.Xor.P] at *; omega

theorem ks_eq {s₀ : State} {j i : Nat} (hj : VG.Proof.ChaCha20.Arm.Xor.P s₀ j < VG.Proof.ChaCha20.Arm.Xor.L s₀) (hi : i < VG.Proof.ChaCha20.Arm.Xor.C s₀ j) :
    (VG.Proof.ChaCha20.Arm.Xor.KS s₀).getD (VG.Proof.ChaCha20.Arm.Xor.P s₀ j + i) 0 = (serialize (Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.Arm.Xor.S0 s₀) j))).getD i 0 := by
  have hP := VG.Proof.ChaCha20.Arm.Xor.P_eq hj
  have hC : VG.Proof.ChaCha20.Arm.Xor.C s₀ j = min 64 (VG.Proof.ChaCha20.Arm.Xor.L s₀ - VG.Proof.ChaCha20.Arm.Xor.P s₀ j) := rfl
  rw [VG.Proof.ChaCha20.Arm.Xor.KS, keystream_getD _ (by lit_omega), hP, show (64 * j + i) / 64 = j by omega,
    show (64 * j + i) % 64 = i by omega]

theorem xor_step {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Xor.XPre s₀) {j i : Nat} (hj : VG.Proof.ChaCha20.Arm.Xor.P s₀ j < VG.Proof.ChaCha20.Arm.Xor.L s₀) (hi : i < VG.Proof.ChaCha20.Arm.Xor.C s₀ j)
    {s : State} (h : VG.Proof.ChaCha20.Arm.Xor.IInv s₀ j i s) :
    WP isa (.block VG.Proof.ChaCha20.Arm.Xor.xorBody) s (fun s' => VG.Proof.ChaCha20.Arm.Xor.IInv s₀ j (i + 1) s' ∧ s'.z = (s'.gpr .r2 - 0 == 0)) := by
  have hL := VG.Proof.ChaCha20.Arm.Xor.L_lt s₀
  have hk : VG.Proof.ChaCha20.Arm.Xor.P s₀ j + i < VG.Proof.ChaCha20.Arm.Xor.L s₀ := by have hC : VG.Proof.ChaCha20.Arm.Xor.C s₀ j = min 64 (VG.Proof.ChaCha20.Arm.Xor.L s₀ - VG.Proof.ChaCha20.Arm.Xor.P s₀ j) := rfl; omega
  have hC64 : VG.Proof.ChaCha20.Arm.Xor.C s₀ j ≤ 64 := Nat.min_le_left _ _
  have hdf := hp.d_fit
  have hbf := hp.b_fit
  have cd : (VG.Proof.ChaCha20.Arm.Xor.dRg s₀).Contains (VG.Proof.ChaCha20.Arm.Xor.dA s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.Arm.Xor.P s₀ j + i)) 1 :=
    VG.Proof.ChaCha20.Arm.contains_off (by lit_omega) (by lit_omega)
  have cb : (VG.Proof.ChaCha20.Arm.Xor.bRg s₀).Contains (VG.Proof.ChaCha20.Arm.Xor.bA s₀ + BitVec.ofNat 64 i) 1 := VG.Proof.ChaCha20.Arm.contains_off (by lit_omega) (by lit_omega)
  have i₁ : InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.Arm.Xor.dA s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.Arm.Xor.P s₀ j + i)) 1 :=
    ⟨VG.Proof.ChaCha20.Arm.Xor.dRg s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cd⟩
  have i₂ : InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.Arm.Xor.bA s₀ + BitVec.ofNat 64 i) 1 :=
    ⟨VG.Proof.ChaCha20.Arm.Xor.bRg s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cb⟩
  have o₁ : InRegions s.wr (VG.Proof.ChaCha20.Arm.Xor.dA s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.Arm.Xor.P s₀ j + i)) 1 :=
    ⟨VG.Proof.ChaCha20.Arm.Xor.dRg s₀, by simp [h.wr, hp.wr], cd⟩
  have ed : ∀ x : State, x.gpr .r5 = s.gpr .r5 →
      State.addr (x.gpr .r5 + BitVec.ofNat 32 0) = VG.Proof.ChaCha20.Arm.Xor.dA s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.Arm.Xor.P s₀ j + i) :=
    fun x hx => by rw [hx, h.r5]; exact VG.Proof.ChaCha20.Arm.Xor.ea0 (by lit_omega)
  unfold VG.Proof.ChaCha20.Arm.Xor.xorBody
  refine wp_ldrb (by decide) (ed s rfl) i₁ fun s₁ u₁ => ?_
  refine wp_ldrb (a := VG.Proof.ChaCha20.Arm.Xor.bA s₀ + BitVec.ofNat 64 i) (by decide)
    (by rw [u₁.other _ (by decide), h.r3]; exact VG.Proof.ChaCha20.Arm.Xor.ea0 (by lit_omega))
    (by rw [u₁.rd, u₁.wr]; exact i₂) fun s₂ u₂ => ?_
  refine VG.Proof.ChaCha20.Arm.Xor.wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_strb (by decide) (ed s₃ (by rw [u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]))
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact o₁) fun s₄ g₄ => ?_
  refine wp_add (op2_imm VG.Proof.ChaCha20.Arm.Xor.imm1) fun s₅ u₅ => wp_add (op2_imm VG.Proof.ChaCha20.Arm.Xor.imm1) fun s₆ u₆ =>
    wp_subs (op2_imm VG.Proof.ChaCha20.Arm.Xor.imm1) fun s₇ u₇ hz => WP.block_nil ?_
  have hv : (s₃.gpr .r0).setWidth 8 =
      VG.Proof.ChaCha20.Arm.Xor.D0 s₀ (VG.Proof.ChaCha20.Arm.Xor.P s₀ j + i) ^^^ (VG.Proof.ChaCha20.Arm.Xor.KS s₀).getD (VG.Proof.ChaCha20.Arm.Xor.P s₀ j + i) 0 := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, VG.Proof.ChaCha20.Arm.Xor.xor_setWidth, h.data _ hk,
      h.ks i (by lit_omega), VG.Proof.ChaCha20.Arm.Xor.ks_eq hj hi]
    simp
  have hm : s₇.mem = s.mem.writeW (VG.Proof.ChaCha20.Arm.Xor.dA s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.Arm.Xor.P s₀ j + i))
      (VG.Proof.ChaCha20.Arm.Xor.D0 s₀ (VG.Proof.ChaCha20.Arm.Xor.P s₀ j + i) ^^^ (VG.Proof.ChaCha20.Arm.Xor.KS s₀).getD (VG.Proof.ChaCha20.Arm.Xor.P s₀ j + i) 0) := by
    rw [u₇.mem, u₆.mem, u₅.mem, g₄.mem, hv, u₃.mem, u₂.mem, u₁.mem]
  have hfd : Frame [VG.Proof.ChaCha20.Arm.Xor.dRg s₀] s.mem s₇.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cd
  have g : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r5 → r ≠ .r3 → r ≠ .r2 → s₇.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ => by
      rw [u₇.other r h₅, u₆.other r h₄, u₅.other r h₃, g₄.gpr, u₃.other r h₁, u₂.other r h₂,
        u₁.other r h₁]
  have h6 : s₆.gpr .r2 = BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Xor.C s₀ j - i) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), g₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.r2]
  have hr2 : s₇.gpr .r2 = BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Xor.C s₀ j - (i + 1)) := by
    rw [u₇.gpr, h6, VG.Proof.ChaCha20.Arm.Xor.sub_one' (by lit_omega), Nat.sub_sub]
  refine ⟨⟨by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r1],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r4], ?_, ?_, hr2,
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r6],
    by rw [u₇.rd, u₆.rd, u₅.rd, g₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    ((((((h.keep.upd u₁).upd u₂).upd u₃).mupd g₄).upd u₅).upd u₆).upd u₇,
    by rw [VG.Proof.ChaCha20.Arm.Xor.stateAt_frame hfd (by simpa using hp.st_d), h.cnt], fun k hk' => ?_,
    h.saved.frame hfd (by simpa using (hp.d_b.sub_right (VG.Proof.ChaCha20.Arm.Xor.savR_sub s₀)).symm), fun t ht => ?_⟩, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.r5, VG.Proof.ChaCha20.Arm.Xor.add_one', Nat.add_assoc]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.r3, VG.Proof.ChaCha20.Arm.Xor.add_one']
  · rw [hm, VG.Proof.ChaCha20.Arm.Xor.writeW8_apply]
    by_cases he : k = VG.Proof.ChaCha20.Arm.Xor.P s₀ j + i
    · subst he; simp
    · simp only [VG.Proof.ChaCha20.Arm.Xor.data_ne hk hk' he, ite_false]
      rw [h.data k hk']
      by_cases h₁ : k < VG.Proof.ChaCha20.Arm.Xor.P s₀ j + i
      · simp [h₁, show k < VG.Proof.ChaCha20.Arm.Xor.P s₀ j + (i + 1) by omega]
      · simp [h₁, show ¬ k < VG.Proof.ChaCha20.Arm.Xor.P s₀ j + (i + 1) by omega]
  · rw [hfd.bytes (R := VG.Proof.ChaCha20.Arm.Xor.bRg s₀) (by simpa using hp.d_b.symm) (show 320 ≤ 2 ^ 64 by omega)
      (show t < 320 by omega)]
    exact h.ks t ht
  · rw [hz, hr2, h6, VG.Proof.ChaCha20.Arm.Xor.sub_one' (by lit_omega), VG.Proof.ChaCha20.Arm.Xor.sub_zero', Nat.sub_sub]

/-! ## A whole block -/

theorem xorLoop_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Xor.XPre s₀) {j : Nat} (hj : VG.Proof.ChaCha20.Arm.Xor.P s₀ j < VG.Proof.ChaCha20.Arm.Xor.L s₀) {s : State}
    (h : VG.Proof.ChaCha20.Arm.Xor.IInv s₀ j 0 s) : WP isa xorLoop s (VG.Proof.ChaCha20.Arm.Xor.IInv s₀ j (VG.Proof.ChaCha20.Arm.Xor.C s₀ j)) := by
  have hL := VG.Proof.ChaCha20.Arm.Xor.L_lt s₀
  have hpos : 0 < VG.Proof.ChaCha20.Arm.Xor.C s₀ j := by simp only [VG.Proof.ChaCha20.Arm.Xor.C]; omega
  have hC : VG.Proof.ChaCha20.Arm.Xor.C s₀ j ≤ 64 := by simp only [VG.Proof.ChaCha20.Arm.Xor.C]; omega
  rw [VG.Proof.ChaCha20.Arm.Xor.xorLoop_eq]
  let Inv : Nat → State → Prop := fun n s => ∃ i, n = VG.Proof.ChaCha20.Arm.Xor.C s₀ j - i ∧ i < VG.Proof.ChaCha20.Arm.Xor.C s₀ j ∧ VG.Proof.ChaCha20.Arm.Xor.IInv s₀ j i s
  have hstep : ∀ n s, Inv n s → WP isa (.block VG.Proof.ChaCha20.Arm.Xor.xorBody) s (fun s' =>
      (isa.eval .ne s' = some false ∧ VG.Proof.ChaCha20.Arm.Xor.IInv s₀ j (VG.Proof.ChaCha20.Arm.Xor.C s₀ j) s') ∨
      (isa.eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨i, rfl, hi, hI⟩
    refine WP.mono (VG.Proof.ChaCha20.Arm.Xor.xor_step hp hj hi hI) fun s' ⟨h', hz'⟩ => ?_
    have hz := VG.Proof.ChaCha20.Arm.Xor.eval_ne_ofNat s' (by lit_omega) hz' h'.r2
    by_cases hl : i + 1 = VG.Proof.ChaCha20.Arm.Xor.C s₀ j
    · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ h'⟩
    · exact .inr ⟨by rw [hz]; simp; omega, VG.Proof.ChaCha20.Arm.Xor.C s₀ j - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep (VG.Proof.ChaCha20.Arm.Xor.C s₀ j) s ⟨0, by simp, hpos, h⟩

/-! ## The end of a block -/

def nextInstrs : List Instr :=
  [.ldr .r0 .r4 48, .dp .add .r0 .r0 (.imm 1), .str .r0 .r4 48, .cmp .r6 (.imm 0)]

theorem P_succ {s₀ : State} {j : Nat} (hj : VG.Proof.ChaCha20.Arm.Xor.P s₀ j < VG.Proof.ChaCha20.Arm.Xor.L s₀) : VG.Proof.ChaCha20.Arm.Xor.P s₀ (j + 1) = VG.Proof.ChaCha20.Arm.Xor.P s₀ j + VG.Proof.ChaCha20.Arm.Xor.C s₀ j := by
  simp only [VG.Proof.ChaCha20.Arm.Xor.P, VG.Proof.ChaCha20.Arm.Xor.C] at *; omega

theorem next_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Xor.XPre s₀) {j : Nat} (hj : VG.Proof.ChaCha20.Arm.Xor.P s₀ j < VG.Proof.ChaCha20.Arm.Xor.L s₀) {s : State}
    (h : VG.Proof.ChaCha20.Arm.Xor.IInv s₀ j (VG.Proof.ChaCha20.Arm.Xor.C s₀ j) s) : WP isa (.block VG.Proof.ChaCha20.Arm.Xor.nextInstrs) s (VG.Proof.ChaCha20.Arm.Xor.OInv s₀ (j + 1)) := by
  have hP := VG.Proof.ChaCha20.Arm.Xor.P_succ hj
  have c₁ : (VG.Proof.ChaCha20.Arm.Xor.stRg s₀).Contains (VG.Proof.ChaCha20.Arm.Xor.stA s₀ + BitVec.ofNat 64 48) 4 := VG.Proof.ChaCha20.Arm.contains_off (by lit_omega) (by lit_omega)
  unfold VG.Proof.ChaCha20.Arm.Xor.nextInstrs
  refine wp_ldr (by decide) (by rw [h.r4]; exact hp.eaS (by lit_omega))
    ⟨VG.Proof.ChaCha20.Arm.Xor.stRg s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], c₁⟩ fun s₁ u₁ => wp_add (op2_imm VG.Proof.ChaCha20.Arm.Xor.imm1) fun s₂ u₂ => ?_
  have e4 : s₂.gpr .r4 = VG.Proof.ChaCha20.Arm.Xor.stP s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r4]
  refine wp_str (by decide) (by rw [e4]; exact hp.eaS (by lit_omega))
    ⟨VG.Proof.ChaCha20.Arm.Xor.stRg s₀, by simp [u₂.wr, u₁.wr, h.wr, hp.wr], c₁⟩ fun s₃ g₃ =>
    wp_cmp (n := .r6) (op2_imm VG.Proof.ChaCha20.Arm.Xor.imm0) fun s₄ f₄ hz => WP.block_nil ?_
  have hv : s.mem.readW (VG.Proof.ChaCha20.Arm.Xor.stA s₀ + BitVec.ofNat 64 48) 32 = (ctr (VG.Proof.ChaCha20.Arm.Xor.S0 s₀) j)[12]'(by decide) := by
    rw [← h.cnt]; simp [stateAt]
  have hm : s₄.mem = s.mem.writeW (VG.Proof.ChaCha20.Arm.Xor.stA s₀ + BitVec.ofNat 64 48) ((ctr (VG.Proof.ChaCha20.Arm.Xor.S0 s₀) j)[12]'(by decide) + 1) := by
    rw [f₄.mem, g₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, hv]
  have hfs : Frame [VG.Proof.ChaCha20.Arm.Xor.stRg s₀] s.mem s₄.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁
  have g : ∀ r, r ≠ .r0 → s₄.gpr r = s.gpr r := fun r hr => by
    rw [f₄.gpr, g₃.gpr, u₂.other r hr, u₁.other r hr]
  refine ⟨⟨by rw [g _ (by decide), h.r1], by rw [g _ (by decide), h.r4],
    by rw [g _ (by decide), h.r5, hP], by rw [g _ (by decide), h.r6, hP, Nat.sub_sub],
    by rw [f₄.rd, g₃.rd, u₂.rd, u₁.rd, h.rd], by rw [f₄.wr, g₃.wr, u₂.wr, u₁.wr, h.wr],
    ((h.keep.upd u₁).upd u₂).mupd g₃ |>.fupd f₄,
    by rw [hm, VG.Proof.ChaCha20.Arm.Xor.stateAt_writeW_counter, h.cnt, ctr_succ], fun k hk => ?_,
    h.saved.frame hfs (by simpa using (hp.st_b.sub_right (VG.Proof.ChaCha20.Arm.Xor.savR_sub s₀)).symm)⟩, ?_⟩
  · rw [hfs.bytes (R := VG.Proof.ChaCha20.Arm.Xor.dRg s₀) (by simpa using hp.st_d.symm)
      (show VG.Proof.ChaCha20.Arm.Xor.L s₀ ≤ 2 ^ 64 by have := VG.Proof.ChaCha20.Arm.Xor.L_lt s₀; omega) hk,
      h.data k hk, hP]
  · rw [hz, g _ (by decide), g₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]

theorem body_eq : body =
    .seq (.block [.mov .r0 (.reg .r4)])
    (.seq (.call "vg_chacha20_block" Impl.ChaCha20.Arm.block)
    (.seq (.block VG.Proof.ChaCha20.Arm.Xor.selA)
    (.seq (.ite .eq (.block [.mov .r2 (.reg .r6)]) (.block [.mov .r2 (.imm 64)]))
    (.seq (.block VG.Proof.ChaCha20.Arm.Xor.selB)
    (.seq xorLoop (.block VG.Proof.ChaCha20.Arm.Xor.nextInstrs)))))) := rfl

theorem body_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Xor.XPre s₀) {j : Nat} (hj : VG.Proof.ChaCha20.Arm.Xor.P s₀ j < VG.Proof.ChaCha20.Arm.Xor.L s₀) {s : State}
    (h : VG.Proof.ChaCha20.Arm.Xor.OInv s₀ j s) : WP isa body s (VG.Proof.ChaCha20.Arm.Xor.OInv s₀ (j + 1)) := by
  rw [VG.Proof.ChaCha20.Arm.Xor.body_eq]
  refine WP.seq (wp_mov (op2_reg _ _) fun s₀' u => WP.block_nil ?_)
  have hI : VG.Proof.ChaCha20.Arm.Xor.Inv s₀ j s₀' :=
    ⟨by rw [u.other _ (by decide), h.r1], by rw [u.other _ (by decide), h.r4],
      by rw [u.other _ (by decide), h.r5], by rw [u.other _ (by decide), h.r6],
      by rw [u.rd, h.rd], by rw [u.wr, h.wr], h.keep.upd u, by rw [u.mem, h.cnt],
      by rw [u.mem]; exact h.data, by rw [u.mem]; exact h.saved⟩
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.Xor.call_ok hp hI (by rw [u.gpr, h.r4])) fun s₁ h₁ => ?_)
  have hs := VG.Proof.ChaCha20.Arm.Xor.sel_ok hj h₁
  rw [WP.seq_iff] at hs
  rw [WP.seq_iff]
  refine WP.mono hs fun s₂ h₂ => ?_
  rw [WP.seq_iff] at h₂
  rw [WP.seq_iff]
  refine WP.mono h₂ fun s₃ h₃ => ?_
  rw [WP.seq_iff]
  refine WP.mono h₃ fun s₄ h₄ => ?_
  exact WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.Xor.xorLoop_ok hp hj h₄) fun s₅ h₅ => VG.Proof.ChaCha20.Arm.Xor.next_ok hp hj h₅)

/-! ## The epilogue -/

/-- What the code guarantees on return. -/
def Post (s₀ s' : State) : Prop :=
  (∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) ∧ VG.Proof.ChaCha20.Arm.Xor.Keep s₀ s' ∧ s'.gpr .r0 = VG.Proof.ChaCha20.Arm.Xor.stP s₀ ∧
    s'.gpr .r1 = VG.Proof.ChaCha20.Arm.Xor.bP s₀ ∧ Proof.ChaCha20.xorArm.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Xor.XPre s₀) {j : Nat} (hj : VG.Proof.ChaCha20.Arm.Xor.P s₀ j = VG.Proof.ChaCha20.Arm.Xor.L s₀) {s : State}
    (h : VG.Proof.ChaCha20.Arm.Xor.Inv s₀ j s) : WP isa (.block (.mov .r0 (.reg .r4) :: restore)) s (VG.Proof.ChaCha20.Arm.Xor.Post s₀) := by
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  have b₁ : s₁.gpr .r1 = VG.Proof.ChaCha20.Arm.Xor.bP s₀ := by rw [u₁.other _ (by decide), h.r1]
  rw [restore, ← List.append_nil (saved.map _)]
  refine Spill.restore_slots_ok VG.Proof.ChaCha20.Arm.Xor.saved_slots (by decide) (g := s₀.gpr)
    (by rw [b₁]; exact Nat.le_trans (Nat.add_le_add_left (by decide : 272 ≤ 320) _) hp.b_fit)
    (fun _ _ hd => by rw [b₁, u₁.rd, u₁.wr, h.rd, h.wr]; exact hp.inB (by omega) _ rfl)
    (by rw [b₁, u₁.mem]; exact h.saved)
    fun s' hs ho hm _ _ _ => WP.block_nil ⟨hs, fun r hr => ?_, ?_, by rw [ho _ (by decide), b₁], ?_⟩
  · have hk : ∀ r ∈ VG.Proof.ChaCha20.Arm.Xor.kept, r ∉ saved.map Prod.fst ∧ r ≠ .r0 := by decide
    rw [ho r (hk r hr).1, u₁.other r (hk r hr).2, h.keep r hr]
  · rw [ho _ (by decide), u₁.gpr, h.r4]
  · refine bytesAt_xor (length_keystream _ _) fun k hk => ?_
    have hk' : k < VG.Proof.ChaCha20.Arm.Xor.L s₀ := hk
    rw [hm, u₁.mem, h.data k hk']
    simp only [show k < VG.Proof.ChaCha20.Arm.Xor.P s₀ j by omega, ite_true]

/-! ## The whole function -/

theorem xor_eq : Impl.ChaCha20.Arm.Xor.xor =
    .seq (.block (save ++ ([.mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2),
      .mov .r1 (.reg .r3), .cmp .r6 (.imm 0)] : List Instr)))
    (.seq (.ite .eq (.block []) (.loop body .ne)) (.block (.mov .r0 (.reg .r4) :: restore))) := rfl

theorem main_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Xor.XPre s₀) : WP isa Impl.ChaCha20.Arm.Xor.xor s₀ (VG.Proof.ChaCha20.Arm.Xor.Post s₀) := by
  have hL := VG.Proof.ChaCha20.Arm.Xor.L_lt s₀
  rw [VG.Proof.ChaCha20.Arm.Xor.xor_eq]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.Xor.prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ j, VG.Proof.ChaCha20.Arm.Xor.P s₀ j = VG.Proof.ChaCha20.Arm.Xor.L s₀ ∧ VG.Proof.ChaCha20.Arm.Xor.Inv s₀ j s) ?_
    fun s₂ ⟨j, hj, h₂⟩ => VG.Proof.ChaCha20.Arm.Xor.epilogue_ok hp hj h₂)
  have hz : isa.eval .eq s₁ = some (decide (VG.Proof.ChaCha20.Arm.Xor.L s₀ = 0)) := by
    have e : isa.eval .eq s₁ = some s₁.z := eval_eq s₁
    rw [e, h₁.z, h₁.r6, VG.Proof.ChaCha20.Arm.Xor.sub_zero', ofNat_beq_zero (by lit_omega)]
    simp [VG.Proof.ChaCha20.Arm.Xor.P]
  refine WP.ite (decide (VG.Proof.ChaCha20.Arm.Xor.L s₀ = 0)) hz (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    exact WP.block_nil ⟨0, by simp [VG.Proof.ChaCha20.Arm.Xor.P, h], h₁.toInv⟩
  · simp only [decide_eq_false_iff_not] at h
    let Inv' : Nat → State → Prop := fun n s => ∃ j, n = VG.Proof.ChaCha20.Arm.Xor.L s₀ - VG.Proof.ChaCha20.Arm.Xor.P s₀ j ∧ VG.Proof.ChaCha20.Arm.Xor.P s₀ j < VG.Proof.ChaCha20.Arm.Xor.L s₀ ∧ VG.Proof.ChaCha20.Arm.Xor.OInv s₀ j s
    have hstep : ∀ n s, Inv' n s → WP isa body s (fun s' =>
        (isa.eval .ne s' = some false ∧ ∃ j, VG.Proof.ChaCha20.Arm.Xor.P s₀ j = VG.Proof.ChaCha20.Arm.Xor.L s₀ ∧ VG.Proof.ChaCha20.Arm.Xor.Inv s₀ j s') ∨
        (isa.eval .ne s' = some true ∧ ∃ n' < n, Inv' n' s')) := by
      rintro n s ⟨j, rfl, hj, hI⟩
      refine WP.mono (VG.Proof.ChaCha20.Arm.Xor.body_ok hp hj hI) fun s' h' => ?_
      have hz' := VG.Proof.ChaCha20.Arm.Xor.eval_ne_ofNat s' (by lit_omega) h'.z h'.r6
      have hP := VG.Proof.ChaCha20.Arm.Xor.P_succ hj
      have hC : 0 < VG.Proof.ChaCha20.Arm.Xor.C s₀ j := by simp only [VG.Proof.ChaCha20.Arm.Xor.C]; omega
      have hle : VG.Proof.ChaCha20.Arm.Xor.P s₀ (j + 1) ≤ VG.Proof.ChaCha20.Arm.Xor.L s₀ := by simp only [VG.Proof.ChaCha20.Arm.Xor.P]; omega
      by_cases hl : VG.Proof.ChaCha20.Arm.Xor.L s₀ - VG.Proof.ChaCha20.Arm.Xor.P s₀ (j + 1) = 0
      · exact .inl ⟨by rw [hz']; simp [hl], j + 1, by omega, h'.toInv⟩
      · exact .inr ⟨by rw [hz']; simp [hl], VG.Proof.ChaCha20.Arm.Xor.L s₀ - VG.Proof.ChaCha20.Arm.Xor.P s₀ (j + 1), by omega, j + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv' hstep (VG.Proof.ChaCha20.Arm.Xor.L s₀ - VG.Proof.ChaCha20.Arm.Xor.P s₀ 0) s₁ ⟨0, rfl, by simp [VG.Proof.ChaCha20.Arm.Xor.P]; omega, h₁⟩

theorem correct {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Xor.XPre s₀) :
    ∃ t s', Exec isa Impl.ChaCha20.Arm.Xor.xor s₀ t s' ∧ abiPreserved s₀ s' ∧
      (Proof.ChaCha20.xorArm.post s₀ s' ∧ s'.gpr .r0 = s₀.gpr .r0 ∧ s'.gpr .r1 = s₀.gpr .r3) := by
  obtain ⟨t, s', he, ⟨hsv, hk, h0, h1, hpost⟩⟩ := VG.Proof.ChaCha20.Arm.Xor.main_ok hp
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he⟩, hpost, h0, h1⟩
  by_cases hs : r ∈ saved.map Prod.fst
  · exact Spill.restored_reg hsv hs
  · have hk' : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → r ∈ VG.Proof.ChaCha20.Arm.Xor.kept := by decide
    exact hk r (hk' r hr hs)

/-- `vg_chacha20_xor` returns with `r0` holding `state` and `r1` holding `buf`
(which was in `r3` on entry), for a caller that recomputes pointers from
them. -/
theorem xor_regs (s : State) (hs : Proof.ChaCha20.xorArm.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.Arm.Xor.xor s t s' ∧ abiPreserved s s' ∧
      (Proof.ChaCha20.xorArm.post s s' ∧ s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r3) :=
  VG.Proof.ChaCha20.Arm.Xor.correct (XPre.of s hs)

/-! ## Constant time -/

/-- The initial taint: the arguments are public, `r0` and `r3` point at the
state and `buf`, and `data`, of unknown length, lies between them. The
block function's saves and restores of `r4`–`r6` are then slots of `buf`. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [64, 0, 320],
    bases := [(.r0, 0), (.r3, 2)] }

theorem wf₀ {s : State} (h : Proof.ChaCha20.xorArm.pre s) : VG.Arm.Taint.Wf VG.Proof.ChaCha20.Arm.Xor.τ₀ s := by
  have hp := XPre.of s h
  refine ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.ChaCha20.Arm.Xor.τ₀], ?_, ?_⟩, ?_, fun h => absurd h (by decide),
    fun _ h => by simp [VG.Proof.ChaCha20.Arm.Xor.τ₀] at h⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_d, hp.st_b⟩, hp.d_b, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [VG.Proof.ChaCha20.Arm.Xor.addr_toNat]
    · exact hp.st_fit
    · exact hp.d_fit
    · exact hp.b_fit
  · intro p hp'
    simp only [VG.Proof.ChaCha20.Arm.Xor.τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> simp [VG.Arm.Taint.region, hp.wr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.ChaCha20.xorArm.pre s₁)
    (h₂ : Proof.ChaCha20.xorArm.pre s₂) (hpub : Proof.ChaCha20.xorArm.pub s₁ s₂) :
    VG.Arm.Taint.Agree VG.Proof.ChaCha20.Arm.Xor.τ₀ s₁ s₂ := by
  obtain ⟨p0, p1, p2, p3⟩ := hpub
  have hp₁ := XPre.of s₁ h₁; have hp₂ := XPre.of s₂ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.ChaCha20.Arm.Xor.wf₀ h₁, VG.Proof.ChaCha20.Arm.Xor.wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (by decide), fun k hk => absurd hk (by simp [VG.Proof.ChaCha20.Arm.Xor.τ₀])⟩
  · simp only [VG.Proof.ChaCha20.Arm.Xor.τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [VG.Proof.ChaCha20.Arm.Xor.stRg, VG.Proof.ChaCha20.Arm.Xor.dRg, VG.Proof.ChaCha20.Arm.Xor.bRg, VG.Proof.ChaCha20.Arm.Xor.stA, VG.Proof.ChaCha20.Arm.Xor.dA, VG.Proof.ChaCha20.Arm.Xor.bA, VG.Proof.ChaCha20.Arm.Xor.stP, VG.Proof.ChaCha20.Arm.Xor.dP, VG.Proof.ChaCha20.Arm.Xor.bP, VG.Proof.ChaCha20.Arm.Xor.L, p0, p1, p2, p3]

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 0⟩, ⟨0x3000, 320⟩]

theorem xor_correct (s : State) (hs : Proof.ChaCha20.xorArm.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.Arm.Xor.xor s t s' ∧ abiPreserved s s' ∧
      Proof.ChaCha20.xorArm.post s s' :=
  (VG.Proof.ChaCha20.Arm.Xor.correct (XPre.of s hs)).imp fun _ ⟨s', he, ha, hpost, _⟩ => ⟨s', he, ha, hpost⟩

theorem xor_ct : ConstantTime isa Proof.ChaCha20.xorArm.pre Proof.ChaCha20.xorArm.pub
    Impl.ChaCha20.Arm.Xor.xor :=
  VG.Taint.constantTime (A := taint) VG.Proof.ChaCha20.Arm.Xor.τ₀ (fun _ _ h₁ h₂ hp => VG.Proof.ChaCha20.Arm.Xor.agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem xor_verified :
    Verified Arm.target Impl.ChaCha20.Arm.Xor.xor (Spec.ChaCha20.xorContract Arm.abi) :=
  Verified.of_correct VG.Proof.ChaCha20.Arm.Xor.xor_correct VG.Proof.ChaCha20.Arm.Xor.xor_ct
    (by sig_implies [Spec.ChaCha20.xorContract, Spec.ChaCha20.xorSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Proof.ChaCha20.xorArm, State.addr]
      [sat] using VG.Proof.ChaCha20.Arm.Xor.sat)

end VG.Proof.ChaCha20.Arm.Xor

end
