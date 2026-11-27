module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrExp
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrExp
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
meta import VerifiedGarbage.Proof.RsaKeyGen.Slots
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Rsa.Ranges
meta import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrBit
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrBit
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrWin
import VerifiedGarbage.Proof.Bignum.CrtExp
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrWin
meta import VerifiedGarbage.Proof.Bignum.CrtExp

/-! ### `RsaKeyGen.AArch64.CTMrExp`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.AArch64.CTMrWin`, which this module and modules that import it used -/

section

/-!
# A candidate on AArch64: constant time of a window of Miller–Rabin

`mrWin`, for runs that agree on the working space (`mrWin_ct`): the
multiplications (`Mont.ct`), the comparisons (after `ws`), the selection of
the table's entry (its bases pinned after its first block, then one piece
whose loop counts the 16 entries and whose masks come from the digit), and
the blocks that only address the header. Between the pieces each run keeps
`WW`: `c`, `-c⁻¹`, the table and `y` below `c`, so that every
multiplication's operands are reduced; `mrLast_ct` is the same for a
squaring after the windows.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Rsa (slot_lt)
open VG.Impl.Bignum.Public (aN aAcc aTmp aXm aY sCnt)

/-- The working space. -/
def WsQ (L : WsP) (s : State) : Prop := Ws s L.B L.Z L.w

/-- `eqMask j` leaks the same in runs with the same working space. -/
theorem eqMask_ct {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block [movi .x9 0, mov .x14 .x12])
      (.seq (.block (base aY .x16 ++ base j .x17)) (.seq (countLoop .x14 xorBody)
        (.block ([movi .x7 0, movi .x4 1, .subs .x .x3 .x9 .x4] ++ borrowMask))))) hc).isSome = true) :
    RelCT isa (Two WsQ) (seqs (eqMask j)) (Two WsQ) :=
  ws_ct (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h) ht fun _ _ h =>
    WP.mono (eqMask_ok h hj) fun _ ⟨_, hm, k⟩ => h.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k
      (by decide)

/-! ## What the window code keeps -/

/-- The working space and its bounds, `c`, and the table and `y` below `c`. -/
def WW (L : WsP) (s : State) : Prop :=
  4 ≤ L.w ∧ L.w ≤ 128 ∧ slot L.w aE + 8 * (L.w + 2) ≤ L.Z ∧ ∃ c bm, MrCtx s L.B L.Z L.w c bm ∧ c % 2 = 1 ∧ 1 < c ∧
    (∀ j < 16, wv s.mem L.B (slot L.w (aT0 + j)) L.w < c) ∧ wv s.mem L.B (slot L.w aY) L.w < c

/-- `WW`, and `[aXm]` below `c`. -/
def WWX (L : WsP) (s : State) : Prop :=
  4 ≤ L.w ∧ L.w ≤ 128 ∧ slot L.w aE + 8 * (L.w + 2) ≤ L.Z ∧ ∃ c bm, MrCtx s L.B L.Z L.w c bm ∧ c % 2 = 1 ∧ 1 < c ∧
    (∀ j < 16, wv s.mem L.B (slot L.w (aT0 + j)) L.w < c) ∧ wv s.mem L.B (slot L.w aY) L.w < c ∧
    wv s.mem L.B (slot L.w aXm) L.w < c

/-- `WW`, and a digit in `kG`. -/
def WWD (L : WsP) (s : State) : Prop := WW L s ∧ ∃ d < 16, word s.mem L.B (8 * kG) = BitVec.ofNat 64 d

theorem WW.ws {L : WsP} {s : State} (h : WW L s) : Ws s L.B L.Z L.w := by
  obtain ⟨-, -, -, c, bm, hc, -⟩ := h; exact hc.ws

theorem WW.goodW {L : WsP} {s : State} (h : WW L s) : GoodW L s := by
  obtain ⟨-, -, -, c, bm, hc, -⟩ := h; exact ⟨_, hc.good⟩

theorem WWX.goodW {L : WsP} {s : State} (h : WWX L s) : GoodW L s := by
  obtain ⟨-, -, -, c, bm, hc, -⟩ := h; exact ⟨_, hc.good⟩

/-- What the window code changes but `y`. -/
def wkRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2)), (8 * kG, 8), (8 * kFlag, 8),
    (8 * kV, 8), (8 * kBits, 8), (8 * kWords, 8)]

/-- `wkRanges`'s ranges, in the header and in the arrays. -/
theorem wkRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(8, 8), (184, 8), (208, 8), (240, 8), (232, 8)]
    [(2, 1), (3, 1), (5, 1)] (wkRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false,
    wkRanges, Public.sCnt, Public.aAcc, Public.aTmp, Public.aXm, aAcc, aTmp, aXm, kT0, sFn, sCnt, kG, kV, kWords, kBits, kFlag, kPlen, kT1, kT2] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(5, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)

theorem wkRanges_mut (w : Nat) : ∀ r ∈ wkRanges w, KMut r := by unfold wkRanges; w_mut

theorem wkRanges_low (w : Nat) : ∀ r ∈ wkRanges w, r.1 + r.2 ≤ slot w aY ∨ slot w aY + 8 * (w + 2) ≤ r.1 := by
  unfold wkRanges; w_disj

theorem wkRanges_tab (w : Nat) : ∀ r ∈ wkRanges w, r.1 + r.2 ≤ slot w aT0 := by
  unfold wkRanges; w_disj

/-- `MrCtx` across changes within `wkRanges` and `aY`. -/
theorem MrCtx.of_wk {s t : State} {B : Addr} {Z w c bm : Nat} {rs : List (Nat × Nat)}
    (hc : MrCtx s B Z w c bm) (hf : Frm B rs s.mem t.mem) (hs : ∀ r ∈ rs, r ∈ wkRanges w ∨ r = (slot w aY, 8 * (w + 2)))
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : MrCtx t B Z w c bm := by
  have hm : ∀ r ∈ rs, KMut r := fun r hr => by
    rcases hs r hr with h | h
    · exact wkRanges_mut w r h
    · rw [h]; exact KMut.ofSlot _ _ _
  have dI : ∀ r ∈ wkRanges w, 8 * sMinv + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMinv := by unfold wkRanges; w_disj
  have dN : ∀ r ∈ wkRanges w, slot w aN + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN := by unfold wkRanges; w_disj
  have dB : ∀ r ∈ wkRanges w, slot w aB + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aB := by unfold wkRanges; w_disj
  have d1 : ∀ r ∈ wkRanges w, slot w aR1 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aR1 := by unfold wkRanges; w_disj
  have dm : ∀ r ∈ wkRanges w, slot w aRm1 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aRm1 := by unfold wkRanges; w_disj
  refine hc.of_frm hf hm k hr (fun r hr' => ?_) (fun r hr' => ?_) (fun r hr' => ?_) (fun r hr' => ?_)
    (fun r hr' => ?_)
  · rcases hs r hr' with h | h
    · exact dI r h
    · subst h; simp only [slot, hdrBytes, aY, sMinv]; omega_arith
  · rcases hs r hr' with h | h
    · exact dN r h
    · subst h; simp only [slot, hdrBytes, aY, aN]; omega_arith
  · rcases hs r hr' with h | h
    · exact dB r h
    · subst h; simp only [slot, hdrBytes, aY, aB]; omega_arith
  · rcases hs r hr' with h | h
    · exact d1 r h
    · subst h; simp only [slot, hdrBytes, aY, aR1]; omega_arith
  · rcases hs r hr' with h | h
    · exact dm r h
    · subst h; simp only [slot, hdrBytes, aY, aRm1]; omega_arith

/-- The table and `y` across changes within `wkRanges`. -/
theorem WW.of_frm {L : WsP} {s t : State} (h : WW L s) {rs : List (Nat × Nat)} (hf : Frm L.B rs s.mem t.mem)
    (hs : ∀ r ∈ rs, r ∈ wkRanges L.w) {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : WW L t := by
  obtain ⟨h4, h128, hEZ, c, bm, hc, hodd, hc1, hT, hY⟩ := h
  have hn := hc.ws.scr.nowrap
  refine ⟨h4, h128, hEZ, c, bm, hc.of_wk hf (fun r hr => Or.inl (hs r hr)) k hr, hodd, hc1, fun j hj => ?_, ?_⟩
  · have := tab_fits hEZ hj
    have := VG.Proof.Bignum.slot_mono L.w (show aT0 ≤ aT0 + j by omega_arith)
    rw [hf.wv_eq (fun r hr' => Or.inr (by have := wkRanges_tab L.w r (hs r hr'); omega_arith)) (by omega_arith)]
    exact hT j hj
  · have := slot_lt (w := L.w) (show aY < aE by decide)
    rw [hf.wv_eq (fun r hr' => by
      rcases wkRanges_low L.w r (hs r hr') with h | h
      · exact Or.inr h
      · exact Or.inl (by omega_arith)) (by omega_arith)]
    exact hY

/-! ## The pieces -/

theorem mul3_low (w : Nat) : ∀ r ∈ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)),
    (slot w aY, 8 * (w + 2))], r.1 + r.2 ≤ slot w aT0 := by w_disj

theorem mmY_ct (M : Mont) : RelCT isa (Two WW) (M.mm aY aY aY) (Two WW) :=
  two_post (two_map id (fun _ _ h => h.goodW) (M.ct (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))) fun L s h => by
    obtain ⟨h4, h128, hEZ, c, bm, hc, hodd, hc1, hT, hY⟩ := h
    have hn := hc.ws.scr.nowrap
    refine WP.mono (M.mm_ok hc.good.1 hc.good.2 (by omega_arith) (by omega_arith) (o := aY) (a := aY) (b := aY) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
      (by rw [hc.n]; exact hY)) fun t ⟨_, hlt, _, ha, k⟩ => ?_
    have hf : Frm L.B [(slot L.w aAcc, 8 * (L.w + 2)), (slot L.w aTmp, 8 * (L.w + 2)), (slot L.w aY, 8 * (L.w + 2))]
        s.mem t.mem := Frm.of_arrays ha (by simp)
    refine ⟨h4, h128, hEZ, c, bm, hc.of_wk hf (by simp [wkRanges]) k (by decide), hodd, hc1, fun j hj => ?_,
      by rw [← hc.n]; exact hlt⟩
    have := tab_fits hEZ hj
    have := VG.Proof.Bignum.slot_mono L.w (show aT0 ≤ aT0 + j by omega_arith)
    rw [hf.wv_eq (fun r hr => Or.inr (by have := mul3_low L.w r hr; omega_arith)) (by omega_arith)]
    exact hT j hj

theorem mmX_ct (M : Mont) : RelCT isa (Two WWX) (M.mm aY aY aXm) (Two WW) :=
  two_post (two_map id (fun _ _ h => h.goodW) (M.ct (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))) fun L s h => by
    obtain ⟨h4, h128, hEZ, c, bm, hc, hodd, hc1, hT, hY, hX⟩ := h
    have hn := hc.ws.scr.nowrap
    refine WP.mono (M.mm_ok hc.good.1 hc.good.2 (by omega_arith) (by omega_arith) (o := aY) (a := aY) (b := aXm) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
      (by rw [hc.n]; exact hX)) fun t ⟨_, hlt, _, ha, k⟩ => ?_
    have hf : Frm L.B [(slot L.w aAcc, 8 * (L.w + 2)), (slot L.w aTmp, 8 * (L.w + 2)), (slot L.w aY, 8 * (L.w + 2))]
        s.mem t.mem := Frm.of_arrays ha (by simp)
    refine ⟨h4, h128, hEZ, c, bm, hc.of_wk hf (by simp [wkRanges]) k (by decide), hodd, hc1, fun j hj => ?_,
      by rw [← hc.n]; exact hlt⟩
    have := tab_fits hEZ hj
    have := VG.Proof.Bignum.slot_mono L.w (show aT0 ≤ aT0 + j by omega_arith)
    rw [hf.wv_eq (fun r hr => Or.inr (by have := mul3_low L.w r hr; omega_arith)) (by omega_arith)]
    exact hT j hj

theorem eqW_ct {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block [movi .x9 0, mov .x14 .x12])
      (.seq (.block (base aY .x16 ++ base j .x17)) (.seq (countLoop .x14 xorBody)
        (.block ([movi .x7 0, movi .x4 1, .subs .x .x3 .x9 .x4] ++ borrowMask))))) hc).isSome = true) :
    RelCT isa (Two WW) (seqs (eqMask j)) (Two WW) :=
  two_post (two_map id (fun _ _ h => h.ws) ((eqMask_ct hj ht).mono (fun _ _ h => h) fun _ _ _ => trivial))
    fun L s h => WP.mono (eqMask_ok h.ws hj) fun t ⟨_, hm, k⟩ =>
      h.of_frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide)

/-- A block that stores into the header slots of `wkRanges` only keeps `WW`. -/
theorem hdr_ct {blk : List Instr} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block blk) hc).isSome = true)
    (hw : ∀ (L : WsP) s, WW L s → WP isa (.block blk) s fun t =>
      ∃ rs, Frm L.B rs s.mem t.mem ∧ (∀ r ∈ rs, r ∈ wkRanges L.w) ∧ ∃ regs, Keep regs s t ∧ .x0 ∉ regs) :
    RelCT isa (Two WW) (.block blk) (Two WW) :=
  two_piece [.x0] (pins_ws' (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) fun _ _ h => h.ws) ht
    fun L s h => WP.mono (hw L s h) fun _ ⟨_, hf, hs, _, k, hr⟩ => h.of_frm hf hs k hr

theorem frm_hdr {m : Mem} {B : Addr} {k : Nat} (hk : k < 32) (v : BitVec 64) {rs : List (Nat × Nat)}
    (hr : (8 * k, 8) ∈ rs) : Frm B rs m (m.writeW (off B (8 * k)) v) :=
  Frm.of_outside (writeW_outside _ B _ (d := 8 * k) (by omega_arith)) hr

/-- The flag or'ed with `x15`. -/
theorem flagOr_ct : RelCT isa (Two WW) (.block [ldh .x4 kFlag, .logic .orr .x .x4 .x4 .x15, sth .x4 kFlag]) (Two WW) :=
  hdr_ct (by taint_decide) fun L s h => by
    have hw := h.ws
    have hs := hw.scr
    have hn := hs.nowrap
    have h256 := hw.h256
    refine WP.mono (WP.keep [.x4] (Q := fun t => t.mem = s.mem.writeW (off L.B (8 * kFlag))
        (word s.mem L.B (8 * kFlag) ||| s.gpr .x15)) (by
      brun [hw.x0, hdr_enc (show kFlag < 32 by decide), hs.ld (d := 8 * kFlag) (by simp only [kFlag, kPlen, sFn]; omega_arith),
        hs.st (d := 8 * kFlag) (by simp only [kFlag, kPlen, sFn]; omega_arith)]) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ =>
      ⟨_, by rw [hm]; exact frm_hdr (show kFlag < 32 by decide) _ (List.mem_singleton_self _), by simp [wkRanges],
        _, k, by decide⟩

/-- `x15` into `kG`. -/
theorem kGst_ct : RelCT isa (Two WW) (.block [sth .x15 kG]) (Two WW) :=
  hdr_ct (by taint_decide) fun L s h => by
    have hw := h.ws
    have hs := hw.scr
    have hn := hs.nowrap
    have h256 := hw.h256
    refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off L.B (8 * kG)) (s.gpr .x15)) (by
      brun [hw.x0, hdr_enc (show kG < 32 by decide), hs.st (d := 8 * kG) (by simp only [kG]; omega_arith)]) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ =>
      ⟨_, by rw [hm]; exact frm_hdr (show kG < 32 by decide) _ (List.mem_singleton_self _), by simp [wkRanges],
        _, k, by decide⟩

/-- The window's last block. -/
theorem winTail_ct : RelCT isa (Two WW) (.block winTail) fun _ _ => True :=
  two_taint [.x0] (pins_ws' (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) fun _ _ h => h.ws)
    (by taint_decide)

/-- The digit into `kG`. -/
theorem digit_ct : RelCT isa (Two WW) (.block [ldh .x3 kV, .lsr .x .x3 .x3 60, sth .x3 kG]) (Two WWD) :=
  two_piece [.x0] (pins_ws' (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) fun _ _ h => h.ws)
    (by taint_decide) fun L s h =>
    WP.mono (winDigit_ok h.ws rfl) fun t ⟨hm, k⟩ =>
      ⟨h.of_frm (rs := [(8 * kG, 8)]) (by rw [hm]; exact frm_hdr (show kG < 32 by decide) _ (by simp))
        (by simp [wkRanges]) k (by decide), _, top_nibble _, by rw [hm, word_writeW_self]⟩

/-- The selection's registers, after its first block. -/
def selVal (L : WsP) : Reg → BitVec 64
  | .x0 => L.B
  | .x2 => off L.B (slot L.w (aT0 + 0))
  | .x10 => BitVec.ofNat 64 0
  | .x11 => BitVec.ofNat 64 (8 * (L.w + 2))
  | .x12 => BitVec.ofNat 64 L.w
  | _ => off L.B (slot L.w aXm)

theorem selInit_pin {L : WsP} {s : State} (h : WWD L s) :
    WP isa (.block (ws ++ base aT0 .x2 ++ base aXm .x13 ++ [ldh .x9 kG, movi .x10 0, movi .x7 0,
      .subImm .x .x8 .x7 1])) s fun t => ∀ r ∈ [Reg.x0, .x2, .x10, .x11, .x12, .x13], t.gpr r = selVal L r := by
  obtain ⟨hW, d, hd, hG⟩ := h
  have hw := hW.ws
  refine WP.mono (selInitW_ok hw hG) fun t hI r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hI.keep.gpr .x0 (by decide)).trans hw.x0
  · exact hI.x2
  · exact hI.x10
  · exact hI.x11
  · exact hI.x12
  · exact hI.x13

/-- The selection: its first block pins the bases, then one piece. -/
theorem mrSel_ct : RelCT isa (Two WWD) (seqs mrSel) (Two WWX) := by
  have e : seqs mrSel = Code.seq _ _ := rfl
  rw [e]
  refine pin_ct [.x0] [.x0, .x2, .x10, .x11, .x12, .x13] selVal
    (pins_ws' (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) fun _ _ h => h.1.ws)
    (by taint_decide) (fun L s h => selInit_pin h) (by taint_decide) fun L s h => ?_
  rw [← e]
  obtain ⟨⟨h4, h128, hEZ, c, bm, hc, hodd, hc1, hT, hY⟩, d, hd, hG⟩ := h
  have hn := hc.ws.scr.nowrap
  refine WP.mono (mrSel_ok hc.ws hEZ hd hG) fun t ⟨hv, ho, _, k⟩ => ?_
  have hf : Frm L.B [(slot L.w aXm, 8 * (L.w + 2))] s.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot L.w aXm) (n' := 8 * (L.w + 2)) (Nat.le_refl _) (by omega_arith)) (by simp)
  obtain ⟨-, -, -, c', bm', hc', hodd', hc1', hT', hY'⟩ :=
    WW.of_frm ⟨h4, h128, hEZ, c, bm, hc, hodd, hc1, hT, hY⟩ hf (by simp [wkRanges]) k (by decide)
  have hN := hc.ws.sl (show aN < 16 by decide)
  have hn' : c' = c := by rw [← hc'.n, ← hc.n, hf.wv_eq (by w_disj) (by omega_arith)]
  subst hn'
  exact ⟨h4, h128, hEZ, c', bm', hc', hodd', hc1', hT', hY', by rw [hv]; exact hT d hd⟩

/-! ## A window -/

theorem mrSq_ct (M : Mont) : RelCT isa (Two WW) (seqs (mrSq M.mm)) (Two WW) := by
  rw [mrSq_eq]
  exact ct_app' (by simp) (by simp [eqMask, eqA]) (mmY_ct M)
    (ct_app' (by simp [eqMask, eqA]) (by simp) (eqW_ct (by decide) (by taint_decide)) flagOr_ct)

/-- A window's four squarings. -/
theorem sq4_ct (M : Mont) :
    RelCT isa (Two WW) (seqs (mrSq M.mm ++ (mrSq M.mm ++ (mrSq M.mm ++ mrSq M.mm)))) (Two WW) :=
  ct_app' (by simp [mrSq]) (by simp [mrSq]) (mrSq_ct M)
    (ct_app' (by simp [mrSq]) (by simp [mrSq]) (mrSq_ct M) (ct_app' (by simp [mrSq]) (by simp [mrSq]) (mrSq_ct M)
      (mrSq_ct M)))

/-- A window after its selection: the multiplication by `[aXm]`, the
comparisons and the flag. -/
theorem winRest_ct (M : Mont) : RelCT isa (Two WWX)
    (seqs (([M.mm aY aY aXm] : List (Prog isa)) ++ (eqMask aRm1 ++
      (([.block [sth .x15 kG]] : List (Prog isa)) ++ (eqMask aR1 ++
        ([.block winTail] : List (Prog isa))))))) fun _ _ => True := by
  refine ct_app' (by simp) (by simp [eqMask, eqA]) (mmX_ct M) ?_
  refine ct_app' (by simp [eqMask, eqA]) (by simp) (eqW_ct (by decide) (by taint_decide)) ?_
  refine ct_app' (by simp) (by simp [eqMask, eqA]) kGst_ct ?_
  exact ct_app' (by simp [eqMask, eqA]) (by simp) (eqW_ct (by decide) (by taint_decide)) winTail_ct

/-- A window leaks the same in runs that agree on the working space. -/
theorem mrWin_ct (M : Mont) : RelCT isa (Two WW) (seqs (mrWin M.mm)) fun _ _ => True := by
  rw [mrWin_eq]
  refine ct_app' (by simp [mrSq]) (by simp) (ct_app' (by simp [mrSq]) (by simp [mrSq]) (mrSq_ct M)
    (ct_app' (by simp [mrSq]) (by simp [mrSq]) (mrSq_ct M) (ct_app' (by simp [mrSq]) (by simp [mrSq]) (mrSq_ct M)
      (mrSq_ct M)))) ?_
  refine ct_app' (by simp) (by simp [mrSel]) digit_ct ?_
  refine ct_app' (by simp [mrSel]) (by simp) mrSel_ct ?_
  refine ct_app' (by simp) (by simp [eqMask, eqA]) (mmX_ct M) ?_
  refine ct_app' (by simp [eqMask, eqA]) (by simp) (eqW_ct (by decide) (by taint_decide)) ?_
  refine ct_app' (by simp) (by simp [eqMask, eqA]) kGst_ct ?_
  exact ct_app' (by simp [eqMask, eqA]) (by simp) (eqW_ct (by decide) (by taint_decide)) winTail_ct

/-! ## The squarings after the windows -/

/-- `WW`, the exponent, and the flag a mask. -/
def WLast (L : WsP) (s : State) : Prop :=
  WW L s ∧ ECtx s.mem L.B L.w (wv s.mem L.B (slot L.w aN) L.w) ∧ ∃ P, word s.mem L.B (8 * kFlag) = mask P

/-- `WLast`, with a mask in `x15`. -/
def WLastM (L : WsP) (s : State) : Prop := WLast L s ∧ ∃ b, s.gpr .x15 = mask b

theorem WLast.of_frm {L : WsP} {s t : State} (h : WLast L s) {rs : List (Nat × Nat)} (hf : Frm L.B rs s.mem t.mem)
    (hs : ∀ r ∈ rs, r ∈ wkRanges L.w ∨ r = (slot L.w aY, 8 * (L.w + 2))) (hF : ∀ r ∈ rs, r ≠ (8 * kFlag, 8))
    (hW : WW L t) : WLast L t := by
  obtain ⟨⟨h4, h128, hEZ, c, bm, hc, -⟩, hE, P, hP⟩ := h
  have hn := hc.ws.scr.nowrap
  have hN := hc.ws.sl (show aN < 16 by decide)
  have hlo : ∀ r ∈ rs, r.1 + r.2 ≤ slot L.w aE := fun r hr => by
    rcases hs r hr with h | h
    · have := wkRanges_tab L.w r h; have := VG.Proof.Bignum.slot_mono L.w (show aT0 ≤ aE by decide); omega_arith
    · subst h; have := slot_lt (w := L.w) (show aY < aE by decide); simp only at this ⊢; omega_arith
  have hNe : wv t.mem L.B (slot L.w aN) L.w = wv s.mem L.B (slot L.w aN) L.w := by
    have dN : ∀ r ∈ wkRanges L.w, slot L.w aN + 8 * L.w ≤ r.1 ∨ r.1 + r.2 ≤ slot L.w aN := by
      unfold wkRanges; w_disj
    refine hf.wv_eq (fun r hr => ?_) (by omega_arith)
    rcases hs r hr with h | h
    · exact dN r h
    · subst h; simp only [slot, hdrBytes, aY, aN]; omega_arith
  refine ⟨hW, by rw [hNe]; exact hE.of_frm hf (fun r hr => Or.inr (hlo r hr)) (by omega_arith), P, ?_⟩
  rw [hf.word_eq (fun r hr => ?_) (by decide)]
  · exact hP
  · have dF : ∀ r ∈ wkRanges L.w, r ≠ (8 * kFlag, 8) → 8 * kFlag + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * kFlag := by
      unfold wkRanges
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, ne_eq, Prod.mk.injEq,
        slot, hdrBytes, aAcc, aTmp, aXm, kG, kFlag, kPlen, kV, kT0, sCnt, kBits, kT2, kWords, kT1, sFn]
      and_intros <;> first | omega_arith | simp
    rcases hs r hr with h | h
    · exact dF r h (hF r hr)
    · subst h; simp only [slot, hdrBytes, aY, kFlag, kPlen, sFn]; omega_arith

theorem mmL_ct (M : Mont) : RelCT isa (Two WLast) (M.mm aY aY aY) (Two WLast) :=
  two_post (two_map id (fun _ _ h => h.1.goodW) (M.ct (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))) fun L s h => by
    have hW := h.1
    obtain ⟨h4, h128, hEZ, c, bm, hc, hodd, hc1, hT, hY⟩ := hW
    have hn := hc.ws.scr.nowrap
    refine WP.mono (M.mm_ok hc.good.1 hc.good.2 (by omega_arith) (by omega_arith) (o := aY) (a := aY) (b := aY) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
      (by rw [hc.n]; exact hY)) fun t ⟨_, hlt, _, ha, k⟩ => ?_
    have hf : Frm L.B [(slot L.w aAcc, 8 * (L.w + 2)), (slot L.w aTmp, 8 * (L.w + 2)), (slot L.w aY, 8 * (L.w + 2))]
        s.mem t.mem := Frm.of_arrays ha (by simp)
    refine h.of_frm hf (by simp [wkRanges]) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, ne_eq, Prod.mk.injEq, slot,
        hdrBytes, aAcc, aTmp, aY, kFlag, kPlen, sFn]
      and_intros <;> omega_arith) ⟨h4, h128, hEZ, c, bm, hc.of_wk hf (by simp [wkRanges]) k (by decide), hodd, hc1,
        fun j hj => ?_, by rw [← hc.n]; exact hlt⟩
    have := tab_fits hEZ hj
    have := VG.Proof.Bignum.slot_mono L.w (show aT0 ≤ aT0 + j by omega_arith)
    rw [hf.wv_eq (fun r hr => Or.inr (by have := mul3_low L.w r hr; omega_arith)) (by omega_arith)]
    exact hT j hj

theorem eqL_ct : RelCT isa (Two WLast) (seqs (eqMask aRm1)) (Two WLastM) :=
  two_post (two_map id (fun _ _ h => h.1.ws) ((eqMask_ct (by decide) (by taint_decide)).mono (fun _ _ h => h)
    fun _ _ _ => trivial)) fun L s h => WP.mono (eqMask_ok h.1.ws (j := aRm1) (by decide)) fun t ⟨h15, hm, k⟩ =>
      ⟨h.of_frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (by simp)
        (h.1.of_frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide)), _, h15⟩

/-- The flag after a last squaring. -/
theorem lastTail_ct {j : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block (base aE .x16 ++
      (([.lsl .x .x5 .x12 3, .add .x .x16 .x16 .x5, ld .x3 .x16] : List Instr) ++ (ldK j ++
      ([.logic .and .x .x3 .x3 .x4, movi .x4 1, .subs .x .x3 .x3 .x4, movi .x7 0, .subImm .x .x8 .x7 1,
        .csel .x .x6 .x8 .x7, .logic .and .x .x15 .x15 .x6, ldh .x4 kFlag, .logic .orr .x .x4 .x4 .x15,
        sth .x4 kFlag] : List Instr))))) hc).isSome = true) (hj : 1 ≤ j ∧ j ≤ 3) :
    RelCT isa (Two WLastM) (.block (lastTail j)) (Two WLast) :=
  ws_block_ct (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h.1.1.ws) ht
    fun L s h => by
      obtain ⟨⟨hW, hE, P, hP⟩, b, h15⟩ := h
      have hEZ := hW.2.2.1
      refine WP.mono (lastTail_ok hW.ws hEZ hE hP h15 hj) fun t ⟨hm, k⟩ => ?_
      have hf : Frm L.B [(8 * kFlag, 8)] s.mem t.mem := by
        rw [hm]; exact frm_hdr (show kFlag < 32 by decide) _ (by simp)
      have hW' := hW.of_frm hf (by simp [wkRanges]) k (by decide)
      obtain ⟨-, -, -, c, bm, hc, -⟩ := hW
      have hn := hc.ws.scr.nowrap
      have hN := hc.ws.sl (show aN < 16 by decide)
      have hNe : wv t.mem L.B (slot L.w aN) L.w = wv s.mem L.B (slot L.w aN) L.w :=
        hf.wv_eq (by w_disj) (by omega_arith)
      have hEn : slot L.w aE + 8 * (L.w + 1) ≤ L.Z := by omega_arith
      refine ⟨hW', by rw [hNe]; exact hE.of_frm hf (by w_disj) (by omega_arith), _, by rw [hm, word_writeW_self]⟩

theorem mrLast_ct (M : Mont) {j : Nat} (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    RelCT isa (Two WLast) (seqs (mrLast M.mm j)) (Two WLast) := by
  rw [mrLast_eq]
  refine ct_app' (by simp) (by simp [eqMask, eqA]) (mmL_ct M) (ct_app' (by simp [eqMask, eqA]) (by simp) eqL_ct ?_)
  rcases hj with rfl | rfl | rfl
  · exact lastTail_ct (by taint_decide) (by decide)
  · exact lastTail_ct (by taint_decide) (by decide)
  · exact lastTail_ct (by taint_decide) (by decide)

end VG.Proof.RsaKeyGen.AArch64

end

end

/-!
# A candidate on AArch64: constant time of Miller–Rabin's exponentiation

`mrExpLoop`, for runs that agree on the working space (`mrExpLoop_ct`): its
loops run `w` words and 16 windows a word, counts that correctness pins
(`mrWord_ok`, `mrWinStep_ok`); the start of each word loads the word of `E`
at an address from `kWords` and `aE`'s base, which are pinned before the
load (`wordHead_ct`); then the three squarings (`mrLast_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero)
open VG.Impl.Bignum.Public (aN aAcc aTmp aXm aY sCnt)

theorem eval_cnt (r : Reg) {t : State} {j c : Nat} (hj : j < c) (h : (t.gpr r).toNat ≠ 0 ↔ j + 1 ≠ c) :
    isa.eval (.nonzero .x r) t = some (decide (j + 1 < c)) := by
  rw [eval_nonzero]
  congr 1
  by_cases hc : j + 1 < c
  · have hne : t.gpr r ≠ 0 := fun e => by
      rw [e] at h; exact absurd (h.mpr (by omega_using [hc])) (by simp)
    rw [bne_iff_ne.mpr hne, decide_eq_true hc]
  · have he : t.gpr r = 0 := BitVec.eq_of_toNat_eq (by
      by_contra hne; exact (h.mp (by simpa using hne)) (by omega_using [hj, hc]))
    rw [he, decide_eq_false hc]; rfl

/-- Before the exponentiation (`mrExpLoop_ok`'s hypotheses). -/
def E0 (L : WsP) (s : State) : Prop :=
  4 ≤ L.w ∧ L.w ≤ 128 ∧ slot L.w aE + 8 * (L.w + 2) ≤ L.Z ∧ ∃ c bm b, MrCtx s L.B L.Z L.w c bm ∧
    TabOK s.mem L.B L.w c b ∧ ECtx s.mem L.B L.w c ∧ c % 2 = 1 ∧ 1 < c ∧
    wv s.mem L.B (slot L.w aY) L.w = 2 ^ (64 * L.w) % c

/-- After `j` words. -/
def WI (L : WsP) (j : Nat) (s : State) : Prop :=
  4 ≤ L.w ∧ L.w ≤ 128 ∧ slot L.w aE + 8 * (L.w + 2) ≤ L.Z ∧ ∃ c bm b s₀, WordInv L.B L.Z L.w c bm b s₀ j s ∧
    ECtx s₀.mem L.B L.w c ∧ c % 2 = 1 ∧ 1 < c

/-- After `i` windows of word `w − 1 − j`. -/
def WinP (p : WsP × Nat) (i : Nat) (s : State) : Prop :=
  4 ≤ p.1.w ∧ p.1.w ≤ 128 ∧ slot p.1.w aE + 8 * (p.1.w + 2) ≤ p.1.Z ∧ p.2 < p.1.w ∧ ∃ c bm b s₀ W,
    WinInv p.1.B p.1.Z p.1.w c bm b (p.1.w - p.2) W s₀ i s ∧
    W.toNat = mrE c / 2 ^ (64 * (p.1.w - p.2 - 1)) % 2 ^ 64 ∧ ECtx s₀.mem p.1.B p.1.w c ∧ c % 2 = 1 ∧ 1 < c

theorem tab_lt {m : Mem} {B : Addr} {w c b : Nat} (h : TabOK m B w c b) (hc : 0 < c) :
    ∀ j < 16, wv m B (slot w (aT0 + j)) w < c := fun j hj => by rw [h j hj]; exact Nat.mod_lt _ hc

theorem winP_ww {p : WsP × Nat} {i : Nat} {s : State} (h : WinP p i s) : WW p.1 s := by
  obtain ⟨h4, h128, hEZ, -, c, bm, b, s₀, W, hI, -, -, hodd, hc1⟩ := h
  exact ⟨h4, h128, hEZ, c, bm, hI.ctx, hodd, hc1, tab_lt hI.tab (by omega_using [hodd]), by rw [hI.y]; exact Nat.mod_lt _ (by omega_using [hodd])⟩

/-- The registers pinned before a word's load. -/
def whVal (p : WsP × Nat) : Reg → BitVec 64
  | .x0 => p.1.B
  | .x3 => BitVec.ofNat 64 (p.1.w - p.2 - 1)
  | _ => off p.1.B (slot p.1.w aE)

/-- The start of a word, up to the index of its word. -/
theorem wordPre_ok {p : WsP × Nat} {s : State} (h : p.2 < p.1.w ∧ WI p.1 p.2 s) :
    WP isa (.block (ws ++ base aE .x16 ++ [ldh .x3 kWords, .subImm .x .x3 .x3 1, sth .x3 kWords])) s
      fun t => ∀ r ∈ [Reg.x0, .x3, .x16], t.gpr r = whVal p r := by
  obtain ⟨hj, h4, h128, hEZ, c, bm, b, s₀, hI, -⟩ := h
  have hw := hI.ctx.ws
  have hs := hw.scr
  have hn := hs.nowrap
  have h256 := hw.h256
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨⟨_, h11, m₁, _⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aE .x16 ((k₁.gpr .x0 (by decide)).trans hw.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.wr
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (p.1.w - p.2 - 1)) (by
    brun [(k12.gpr .x0 (by decide)).trans hw.x0, hdr_enc (show kWords < 32 by decide),
      hs₂.ld (d := 8 * kWords) (by simp only [kWords, kT1, sFn]; omega_using [h256]),
      hs₂.st (d := 8 * kWords) (by simp only [kWords, kT1, sFn]; omega_using [h256]),
      (by rw [m₂, m₁]; exact hI.words : word s₂.mem p.1.B (8 * kWords) = BitVec.ofNat 64 (p.1.w - p.2)),
      ofNat64_pred (show 1 ≤ p.1.w - p.2 by omega_using [hj]) (by omega_using [h128])])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨h3, k⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ((k12.trans k).gpr .x0 (by decide)).trans hw.x0
  · exact h3
  · exact (k.gpr .x16 (by decide)).trans h16

theorem wordStart_eq : ws ++ base aE .x16 ++ wordHead =
    (ws ++ base aE .x16 ++ ([ldh .x3 kWords, .subImm .x .x3 .x3 1, sth .x3 kWords] : List Instr)) ++
      ([.lsl .x .x5 .x3 3, .add .x .x4 .x16 .x5, ld .x5 .x4, sth .x5 kV, movi .x6 16, sth .x6 kBits] : List Instr) := by
  simp only [wordHead, List.append_assoc, List.cons_append, List.nil_append]

theorem wordHead_ct : RelCT isa (Two fun (p : WsP × Nat) s => p.2 < p.1.w ∧ WI p.1 p.2 s)
    (.block (ws ++ base aE .x16 ++ wordHead)) (Two fun p s => 0 < 16 ∧ WinP p 0 s) := by
  rw [wordStart_eq]
  exact blk_pin (ws ++ base aE .x16 ++ [ldh .x3 kWords, .subImm .x .x3 .x3 1, sth .x3 kWords])
    [.lsl .x .x5 .x3 3, .add .x .x4 .x16 .x5, ld .x5 .x4, sth .x5 kV, movi .x6 16, sth .x6 kBits] [.x0]
    [.x0, .x3, .x16] whVal
    (pins_ws' (fun p : WsP × Nat => p.1.B) (fun p => p.1.Z) (fun p => p.1.w)
      fun _ _ ⟨_, _, _, _, _, _, _, _, hI, _⟩ => hI.ctx.ws) (by taint_decide) (fun _ _ h => wordPre_ok h)
    (by taint_decide) fun p s ⟨hj, h4, h128, hEZ, c, bm, b, s₀, hI, hE, hodd, hc1⟩ => by
      rw [← wordStart_eq]
      have hW : (wordE s.mem p.1.B p.1.w p.2).toNat = mrE c / 2 ^ (64 * (p.1.w - p.2 - 1)) % 2 ^ 64 := by
        have hE' : ECtx s.mem p.1.B p.1.w c :=
          hE.of_low hI.frm (expRanges_low p.1.w) hEZ hI.ctx.ws.scr.nowrap
        rw [← hE'.e]; exact word_of_wv s.mem p.1.B (slot p.1.w aE) p.1.w (by omega_using [hj])
      exact WP.mono (wordStart_ok hEZ hj hI) fun t hB =>
        ⟨by decide, h4, h128, hEZ, hj, c, bm, b, s₀, _, hB, hW, hE, hodd, hc1⟩

/-- The windows of a word. -/
theorem wordWins_ct (M : Mont) : RelCT isa (Two fun (p : WsP × Nat) s => 0 < 16 ∧ WinP p 0 s)
    (.loop (seqs (mrWin M.mm)) (.nonzero .x .x3)) (Two fun p s => WinP p 16 s) := by
  refine two_loop (Φ := WinP) (fun _ => 16) (two_map (fun q : (WsP × Nat) × Nat => q.1.1)
    (fun _ _ h => winP_ww h.2) (mrWin_ct M)) ?_
  rintro p i s hi ⟨h4, h128, hEZ, hj, c, bm, b, s₀, W, hI, hW, hE, hodd, hc1⟩
  exact WP.mono (mrWinStep_ok M h128 hEZ hodd hc1 (by omega_using [hj]) (by omega_using []) hW hi hI) fun t ⟨hI', hz⟩ =>
    ⟨eval_cnt .x3 hi hz, fun _ => ⟨h4, h128, hEZ, hj, c, bm, b, s₀, W, hI', hW, hE, hodd, hc1⟩,
      fun e => e ▸ ⟨h4, h128, hEZ, hj, c, bm, b, s₀, W, hI', hW, hE, hodd, hc1⟩⟩

/-- One word. -/
theorem word_ct (M : Mont) : RelCT isa (Two fun (p : WsP × Nat) s => p.2 < p.1.w ∧ WI p.1 p.2 s)
    (seqs [.block (ws ++ base aE .x16 ++ wordHead), .loop (seqs (mrWin M.mm)) (.nonzero .x .x3),
      .block [ldh .x3 kWords]]) fun _ _ => True :=
  RelCT.seq wordHead_ct (RelCT.seq (wordWins_ct M) (two_taint [.x0]
    (pins_ws' (fun p : WsP × Nat => p.1.B) (fun p => p.1.Z) (fun p => p.1.w)
      fun _ _ h => (winP_ww h).ws) (by taint_decide)))

/-- The exponentiation leaks the same in runs that agree on the working space. -/
theorem mrExpLoop_ct (M : Mont) : RelCT isa (Two E0) (seqs (mrExpLoop M.mm)) fun _ _ => True := by
  rw [mrExpLoop_eq]
  refine ct_app' (by simp) (by simp [mrLast]) ?_ (ct_app' (by simp [mrLast]) (by simp [mrLast]) (mrLast_ct M (by decide))
    (ct_app' (by simp [mrLast]) (by simp [mrLast]) (mrLast_ct M (by decide))
      ((mrLast_ct M (by decide)).mono (fun _ _ h => h) fun _ _ _ => trivial)))
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun L s => 0 < L.w ∧ WI L 0 s) [.x0]
    (pins_ws' (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w)
      fun _ _ ⟨_, _, _, _, _, _, hc, _⟩ => hc.ws) (by taint_decide)
    fun L s ⟨h4, h128, hEZ, c, bm, b, hc, hT, hE, hodd, hc1, hY⟩ => WP.mono (expStart_ok hEZ hc hT hY) fun t hI =>
      ⟨by omega_using [h4], h4, h128, hEZ, c, bm, b, s, hI, hE, hodd, hc1⟩) ?_
  refine two_loop (Φ := WI) (Ψ := WLast) (fun L => L.w) (word_ct M) ?_
  rintro L j s hj ⟨h4, h128, hEZ, c, bm, b, s₀, hI, hE, hodd, hc1⟩
  refine WP.mono (mrWord_ok M h128 hEZ (hE.of_low hI.frm (expRanges_low L.w) hEZ hI.ctx.ws.scr.nowrap) hodd hc1 hj hI)
    fun t ⟨hI', hz⟩ => ⟨eval_cnt .x3 hj hz, fun _ => ⟨h4, h128, hEZ, c, bm, b, s₀, hI', hE, hodd, hc1⟩, fun _ => ?_⟩
  have hn := hI'.ctx.ws.scr.nowrap
  refine ⟨⟨h4, h128, hEZ, c, bm, hI'.ctx, hodd, hc1, tab_lt hI'.tab (by omega_using [hodd]),
    by rw [hI'.y]; exact Nat.mod_lt _ (by omega_using [hodd])⟩, by rw [hI'.ctx.n]; exact hE.of_low hI'.frm (expRanges_low L.w) hEZ hn,
    _, hI'.flag⟩

end VG.Proof.RsaKeyGen.AArch64

end

end

/-!
# A candidate on AArch64: constant time of Miller–Rabin's table

`tabBuild`, for runs that agree on the working space (`tabBuild_ct`): the
entry being written is a header word, pinned after the block that loads it
(`toEnt_ct`); its loop counts 14 entries, which correctness pins
(`tabStep_ok`); the multiplications are `Mont.ct`'s, with `[aXm]` below `c`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Rsa (slot_lt)
open VG.Impl.Bignum.Public (aN aAcc aTmp aXm aY sCnt)

/-- What the table's code keeps: the working space and its bounds, `c`, and
`[aXm]` below `c`. -/
def TB (L : WsP) (s : State) : Prop :=
  4 ≤ L.w ∧ L.w ≤ 128 ∧ slot L.w aE + 8 * (L.w + 2) ≤ L.Z ∧ ∃ c bm b, MrCtx s L.B L.Z L.w c bm ∧ c % 2 = 1 ∧
    1 < c ∧ wv s.mem L.B (slot L.w aXm) L.w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * L.w) % c

/-- `TB`, with entry `e` in `kV`. -/
def TBE (L : WsP) (e : Nat) (s : State) : Prop :=
  TB L s ∧ e < 16 ∧ word s.mem L.B (8 * kV) = off L.B (slot L.w (aT0 + e))

theorem TB.ws {L : WsP} {s : State} (h : TB L s) : Ws s L.B L.Z L.w := by
  obtain ⟨-, -, -, c, bm, b, hc, -⟩ := h; exact hc.ws

theorem TB.of_tab {L : WsP} {s t : State} (h : TB L s) {rs : List (Nat × Nat)} (hf : Frm L.B rs s.mem t.mem)
    (hs : ∀ r ∈ rs, r ∈ tabRanges L.w) {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : TB L t := by
  obtain ⟨h4, h128, hEZ, c, bm, b, hc, hodd, hc1, hX⟩ := h
  have hn := hc.ws.scr.nowrap
  have hXZ := hc.ws.sl (show aXm < 16 by decide)
  have dX : ∀ r ∈ tabRanges L.w, slot L.w aXm + 8 * L.w ≤ r.1 ∨ r.1 + r.2 ≤ slot L.w aXm := by
    unfold tabRanges; w_disj
  exact ⟨h4, h128, hEZ, c, bm, b, hc.of_tab hf hs k hr, hodd, hc1,
    by rw [hf.wv_eq (fun r hr' => dX r (hs r hr')) (by omega_using [hn, hXZ])]; exact hX⟩

/-- The registers pinned before an entry's copy. -/
def entVal (L : WsP) (a e : Nat) : Reg → BitVec 64
  | .x0 => L.B
  | .x12 => BitVec.ofNat 64 L.w
  | .x16 => off L.B (slot L.w a)
  | _ => off L.B (slot L.w (aT0 + e))

theorem toEntPre_ok {L : WsP} {e : Nat} {s : State} (h : TBE L e s) (a : Nat) :
    WP isa (.block (ws ++ base a .x16 ++ [ldh .x17 kV])) s fun t =>
      ∀ r ∈ [Reg.x0, .x12, .x16, .x17], t.gpr r = entVal L a e r := by
  obtain ⟨hT, he, hV⟩ := h
  have hw := hT.ws
  have hs := hw.scr
  have hn := hs.nowrap
  have h256 := hw.h256
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok a .x16 ((k₁.gpr .x0 (by decide)).trans hw.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  refine WP.mono (WP.keep [.x17] (Q := fun t => t.gpr .x17 = off L.B (slot L.w (aT0 + e))) (by
    brun [(k12.gpr .x0 (by decide)).trans hw.x0, hdr_enc (show kV < 32 by decide),
      (hs.congr k12.wr).ld (d := 8 * kV) (by simp only [kV, kT0, sCnt, sFn]; omega_using [h256]),
      (by rw [m₂, m₁]; exact hV : word s₂.mem L.B (8 * kV) = off L.B (slot L.w (aT0 + e)))])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨h17, k⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ((k12.trans k).gpr .x0 (by decide)).trans hw.x0
  · exact ((k₂.trans k).gpr .x12 (by decide)).trans h12
  · exact (k.gpr .x16 (by decide)).trans h16
  · exact h17

/-- `toEnt a`: the copy's addresses are pinned after its first block. -/
theorem toEnt_ct {α : Type} (L : α → WsP) (e : α → Nat) {a : Nat} (ha : a < aT0)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base a .x16 ++ [ldh .x17 kV])) hc).isSome = true) :
    RelCT isa (Two fun x s => TBE (L x) (e x) s) (seqs (toEnt a)) (Two fun x s => TBE (L x) (e x) s) := by
  have eq : seqs (toEnt a) = Code.seq (.block (ws ++ base a .x16 ++ [ldh .x17 kV])) copyWords := rfl
  rw [eq]
  refine pin_ct [.x0] [.x0, .x12, .x16, .x17] (fun x => entVal (L x) a (e x))
    (pins_ws' (fun x => (L x).B) (fun x => (L x).Z) (fun x => (L x).w) fun _ _ h => h.1.ws) ht
    (fun x s h => toEntPre_ok h a) (by taint_decide) fun x s h => ?_
  rw [← eq]
  obtain ⟨hT, he, hV⟩ := h
  have hw := hT.ws
  have hn := hw.scr.nowrap
  have hEZ := hT.2.2.1
  refine WP.mono (toEnt_ok hw hEZ ha he hV) fun t ⟨_, ho, k⟩ => ?_
  have hE := ent_in_tab (L x).w he
  have hf : Frm (L x).B [(slot (L x).w aT0, 128 * ((L x).w + 2))] s.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot (L x).w aT0) (n' := 128 * ((L x).w + 2)) hE.1 (by omega_using [hE])) (by simp)
  exact ⟨hT.of_tab hf (by simp [tabRanges]) k (by decide), he,
    by rw [hf.word_eq (VG.Proof.RsaKeyGen.past_hdrW rfl) (by decide)]; exact hV⟩

/-! ## The table's start -/

theorem tabStart_ct : RelCT isa (Two TB) (.block (ws ++ base aT0 .x3 ++ [sth .x3 kV, movi .x3 14, sth .x3 kBits]))
    (Two fun L s => TBE L 0 s) := by
  rw [List.append_assoc]
  exact ws_block_ct (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h.ws)
    (by taint_decide) fun L s h => by
      rw [← List.append_assoc]
      refine WP.mono (tabStart_ok h.ws) fun t ⟨hm, k⟩ => ?_
      have hf : Frm L.B [(8 * kV, 8), (8 * kBits, 8)] s.mem t.mem := by
        rw [hm]
        exact (frm_hdr (show kV < 32 by decide) _ (by simp)).trans (frm_hdr (show kBits < 32 by decide) _ (by simp))
      exact ⟨h.of_tab hf (by simp [tabRanges]) k (by decide), by decide, by
        rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]; rfl⟩

theorem nextEnt_ct {e : Nat} (he : e + 1 < 16) :
    RelCT isa (Two fun L s => TBE L e s) (.block nextEnt) (Two fun L s => TBE L (e + 1) s) :=
  two_piece [.x0] (pins_ws' (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) fun _ _ h => h.1.ws)
    (by taint_decide) fun L s h => by
      obtain ⟨hT, -, hV⟩ := h
      refine WP.mono (nextEnt_ok hT.ws hV) fun t ⟨hm, k⟩ => ?_
      have hf : Frm L.B [(8 * kV, 8)] s.mem t.mem := by
        rw [hm]; exact frm_hdr (show kV < 32 by decide) _ (by simp)
      exact ⟨hT.of_tab hf (by simp [tabRanges]) k (by decide), he, by rw [hm, word_writeW_self, slot_succ]; rfl⟩

/-- The table's loop: after `i` entries. -/
def TL (L : WsP) (i : Nat) (s : State) : Prop :=
  4 ≤ L.w ∧ L.w ≤ 128 ∧ slot L.w aE + 8 * (L.w + 2) ≤ L.Z ∧ ∃ c bm b s₀, TabI L.B L.Z L.w c bm b s₀ i s ∧
    c % 2 = 1 ∧ 1 < c

theorem copyA_tct {α : Type} {Φ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {o a : Nat} (ho : o < 16) (ha : a < 16) (hoa : o ≠ a)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base a .x16 ++ base o .x17)) copyWords)
      hc).isSome = true) :
    RelCT isa (Two Φ) (copyA o a) fun _ _ => True := by
  have e : copyA o a = .seq (.block (ws ++ (base a .x16 ++ base o .x17))) copyWords := by
    simp only [copyA, List.append_assoc]
  rw [e]
  refine (ws_ct (Ψ := fun _ _ => True) B Z w hws ht fun x s h => ?_).mono (fun _ _ h => h) fun _ _ _ => trivial
  rw [← e]
  exact WP.mono (copyA_ok (hws x s h) ho ha hoa) fun _ _ => trivial

/-! ## The table's loop -/

theorem tabMul_ok (M : Mont) {L : WsP} {i : Nat} {s : State} (hi : i < 14) (h : TL L i s) :
    WP isa (M.mm aY aY aXm) s fun t => TBE L (i + 2) t := by
  obtain ⟨h4, h128, hEZ, c, bm, b, s₀, hI, hodd, hc1⟩ := h
  have hc := hI.ctx
  have hn := hc.ws.scr.nowrap
  have hX : wv s.mem L.B (slot L.w aXm) L.w < c := by rw [hI.xm]; exact Nat.mod_lt _ (by omega_using [hodd])
  refine WP.mono (M.mm_ok hc.good.1 hc.good.2 (by omega_using [h4]) (by omega_using [h128]) (o := aY) (a := aY) (b := aXm) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hc.n]; exact hX)) fun t ⟨_, _, _, ha, k⟩ => ?_
  have hf : Frm L.B [(slot L.w aAcc, 8 * (L.w + 2)), (slot L.w aTmp, 8 * (L.w + 2)),
      (slot L.w aY, 8 * (L.w + 2))] s.mem t.mem := Frm.of_arrays ha (by simp)
  have hT : TB L s := ⟨h4, h128, hEZ, c, bm, b, hc, hodd, hc1, hI.xm⟩
  exact ⟨hT.of_tab hf (by simp [tabRanges]) k (by decide), by omega_using [hi],
    by rw [hf.word_eq ((VG.Proof.RsaKeyGen.mm_shape _ _).hdrW rfl rfl) (by decide)]; exact hI.v⟩

theorem tabMul_ct (M : Mont) : RelCT isa (Two fun (p : WsP × Nat) s => p.2 < 14 ∧ TL p.1 p.2 s) (M.mm aY aY aXm)
    (Two fun (p : WsP × Nat) s => TBE p.1 (p.2 + 2) s) :=
  two_post (two_map (fun p : WsP × Nat => p.1)
    (fun (p : WsP × Nat) (s : State) (h : p.2 < 14 ∧ TL p.1 p.2 s) => by
      obtain ⟨-, -, -, -, c, bm, b, s₀, hI, -⟩ := h; exact ⟨_, hI.ctx.good⟩)
    (M.ct (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))) fun p s h => tabMul_ok M h.1 h.2

/-- An entry of the table's loop. -/
theorem tabStep_ct (M : Mont) : RelCT isa (Two fun (p : WsP × Nat) s => p.2 < 14 ∧ TL p.1 p.2 s)
    (seqs (([M.mm aY aY aXm] : List (Prog isa)) ++ toEnt aY ++
      ([.block (nextEnt ++ ([ldh .x3 kBits, .subImm .x .x3 .x3 1, sth .x3 kBits] : List Instr))] : List (Prog isa))))
      fun _ _ => True := by
  rw [List.append_assoc]
  refine ct_app' (by simp) (by simp [toEnt]) (tabMul_ct M) (ct_app' (by simp [toEnt]) (by simp)
    (toEnt_ct (fun p : WsP × Nat => p.1) (fun p => p.2 + 2) (by decide) (by taint_decide)) (two_taint [.x0]
      (pins_ws' (Φ := fun (p : WsP × Nat) s => TBE p.1 (p.2 + 2) s) (fun p : WsP × Nat => p.1.B) (fun p => p.1.Z)
        (fun p => p.1.w) fun _ _ h => h.1.ws)
      (by taint_decide)))

/-- The table leaks the same in runs that agree on the working space. -/
theorem tabBuild_ct (M : Mont) : RelCT isa (Two TB) (seqs (tabBuild M.mm)) fun _ _ => True := by
  rw [tabBuild_eq]
  refine ct_app' (by simp [tabHead]) (by simp) (Ψ := fun L s => 0 < 14 ∧ TL L 0 s) ?_ ?_
  · refine two_post ?_ fun L s h => ?_
    · unfold tabHead
      refine ct_app' (by simp) (by simp [toEnt]) tabStart_ct ?_
      refine ct_app' (by simp [toEnt]) (by simp) (toEnt_ct id (fun _ => 0) (by decide) (by taint_decide)) ?_
      refine ct_app' (by simp) (by simp [toEnt]) (nextEnt_ct (by decide)) ?_
      refine ct_app' (by simp [toEnt]) (by simp) (toEnt_ct id (fun _ => 1) (by decide) (by taint_decide)) ?_
      refine RelCT.seq (nextEnt_ct (by decide)) ?_
      exact copyA_tct (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h.1.ws)
        (by decide) (by decide) (by decide) (by taint_decide)
    · obtain ⟨h4, h128, hEZ, c, bm, b, hc, hodd, hc1, hX⟩ := h
      exact WP.mono (tabHead_ok hEZ hc hc1 hX) fun t ⟨hI, _⟩ => ⟨by decide, h4, h128, hEZ, c, bm, b, t, hI, hodd, hc1⟩
  refine RelCT.seq (two_loop (Φ := TL) (Ψ := fun L s => Ws s L.B L.Z L.w) (fun _ => 14) (tabStep_ct M) ?_)
    (copyA_tct (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h)
      (by decide) (by decide) (by decide) (by taint_decide))
  rintro L i s hi ⟨h4, h128, hEZ, c, bm, b, s₀, hI, hodd, hc1⟩
  exact WP.mono (tabStep_ok M h128 hEZ hodd hc1 hi hI) fun t ⟨hI', hz⟩ =>
    ⟨eval_cnt .x3 hi hz, fun _ => ⟨h4, h128, hEZ, c, bm, b, s₀, hI', hodd, hc1⟩, fun _ => hI'.ctx.ws⟩


end VG.Proof.RsaKeyGen.AArch64
