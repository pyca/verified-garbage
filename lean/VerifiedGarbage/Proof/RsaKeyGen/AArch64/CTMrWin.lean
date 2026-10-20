module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrWin
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrBit
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrWin
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrBit
meta import VerifiedGarbage.Proof.Rsa.Ranges
meta import VerifiedGarbage.Proof.Bignum.CrtExp
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

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

theorem pins_wsq : Pins WsQ [.x0] := pins_ws' (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) fun _ _ h => h

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
    · subst h; simp only [slot, hdrBytes, aY, sMinv]; omega
  · rcases hs r hr' with h | h
    · exact dN r h
    · subst h; simp only [slot, hdrBytes, aY, aN]; omega
  · rcases hs r hr' with h | h
    · exact dB r h
    · subst h; simp only [slot, hdrBytes, aY, aB]; omega
  · rcases hs r hr' with h | h
    · exact d1 r h
    · subst h; simp only [slot, hdrBytes, aY, aR1]; omega
  · rcases hs r hr' with h | h
    · exact dm r h
    · subst h; simp only [slot, hdrBytes, aY, aRm1]; omega

/-- The table and `y` across changes within `wkRanges`. -/
theorem WW.of_frm {L : WsP} {s t : State} (h : WW L s) {rs : List (Nat × Nat)} (hf : Frm L.B rs s.mem t.mem)
    (hs : ∀ r ∈ rs, r ∈ wkRanges L.w) {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : WW L t := by
  obtain ⟨h4, h128, hEZ, c, bm, hc, hodd, hc1, hT, hY⟩ := h
  have hn := hc.ws.scr.nowrap
  refine ⟨h4, h128, hEZ, c, bm, hc.of_wk hf (fun r hr => Or.inl (hs r hr)) k hr, hodd, hc1, fun j hj => ?_, ?_⟩
  · have := tab_fits hEZ hj
    have := VG.Proof.Bignum.slot_mono L.w (show aT0 ≤ aT0 + j by omega)
    rw [hf.wv_eq (fun r hr' => Or.inr (by have := wkRanges_tab L.w r (hs r hr'); omega)) (by omega)]
    exact hT j hj
  · have := slot_lt (w := L.w) (show aY < aE by decide)
    rw [hf.wv_eq (fun r hr' => by
      rcases wkRanges_low L.w r (hs r hr') with h | h
      · exact Or.inr h
      · exact Or.inl (by omega)) (by omega)]
    exact hY

/-! ## The pieces -/

theorem mul3_low (w : Nat) : ∀ r ∈ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)),
    (slot w aY, 8 * (w + 2))], r.1 + r.2 ≤ slot w aT0 := by w_disj

theorem mmY_ct (M : Mont) : RelCT isa (Two WW) (M.mm aY aY aY) (Two WW) :=
  two_post (two_map id (fun _ _ h => h.goodW) (M.ct (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))) fun L s h => by
    obtain ⟨h4, h128, hEZ, c, bm, hc, hodd, hc1, hT, hY⟩ := h
    have hn := hc.ws.scr.nowrap
    refine WP.mono (M.mm_ok hc.good.1 hc.good.2 (by omega) (by omega) (o := aY) (a := aY) (b := aY) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
      (by rw [hc.n]; exact hY)) fun t ⟨_, hlt, _, ha, k⟩ => ?_
    have hf : Frm L.B [(slot L.w aAcc, 8 * (L.w + 2)), (slot L.w aTmp, 8 * (L.w + 2)), (slot L.w aY, 8 * (L.w + 2))]
        s.mem t.mem := Frm.of_arrays ha (by simp)
    refine ⟨h4, h128, hEZ, c, bm, hc.of_wk hf (by simp [wkRanges]) k (by decide), hodd, hc1, fun j hj => ?_,
      by rw [← hc.n]; exact hlt⟩
    have := tab_fits hEZ hj
    have := VG.Proof.Bignum.slot_mono L.w (show aT0 ≤ aT0 + j by omega)
    rw [hf.wv_eq (fun r hr => Or.inr (by have := mul3_low L.w r hr; omega)) (by omega)]
    exact hT j hj

theorem mmX_ct (M : Mont) : RelCT isa (Two WWX) (M.mm aY aY aXm) (Two WW) :=
  two_post (two_map id (fun _ _ h => h.goodW) (M.ct (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))) fun L s h => by
    obtain ⟨h4, h128, hEZ, c, bm, hc, hodd, hc1, hT, hY, hX⟩ := h
    have hn := hc.ws.scr.nowrap
    refine WP.mono (M.mm_ok hc.good.1 hc.good.2 (by omega) (by omega) (o := aY) (a := aY) (b := aXm) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
      (by rw [hc.n]; exact hX)) fun t ⟨_, hlt, _, ha, k⟩ => ?_
    have hf : Frm L.B [(slot L.w aAcc, 8 * (L.w + 2)), (slot L.w aTmp, 8 * (L.w + 2)), (slot L.w aY, 8 * (L.w + 2))]
        s.mem t.mem := Frm.of_arrays ha (by simp)
    refine ⟨h4, h128, hEZ, c, bm, hc.of_wk hf (by simp [wkRanges]) k (by decide), hodd, hc1, fun j hj => ?_,
      by rw [← hc.n]; exact hlt⟩
    have := tab_fits hEZ hj
    have := VG.Proof.Bignum.slot_mono L.w (show aT0 ≤ aT0 + j by omega)
    rw [hf.wv_eq (fun r hr => Or.inr (by have := mul3_low L.w r hr; omega)) (by omega)]
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
  Frm.of_outside (writeW_outside _ B _ (d := 8 * k) (by omega)) hr

/-- The flag or'ed with `x15`. -/
theorem flagOr_ct : RelCT isa (Two WW) (.block [ldh .x4 kFlag, .logic .orr .x .x4 .x4 .x15, sth .x4 kFlag]) (Two WW) :=
  hdr_ct (by taint_decide) fun L s h => by
    have hw := h.ws
    have hs := hw.scr
    have hn := hs.nowrap
    have h256 := hw.h256
    refine WP.mono (WP.keep [.x4] (Q := fun t => t.mem = s.mem.writeW (off L.B (8 * kFlag))
        (word s.mem L.B (8 * kFlag) ||| s.gpr .x15)) (by
      brun [hw.x0, hdr_enc (show kFlag < 32 by decide), hs.ld (d := 8 * kFlag) (by simp only [kFlag, kPlen, sFn]; omega),
        hs.st (d := 8 * kFlag) (by simp only [kFlag, kPlen, sFn]; omega)]) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ =>
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
      brun [hw.x0, hdr_enc (show kG < 32 by decide), hs.st (d := 8 * kG) (by simp only [kG]; omega)]) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ =>
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

theorem mrSel_eq : mrSel = [.block (ws ++ base aT0 .x2 ++ base aXm .x13 ++ [ldh .x9 kG, movi .x10 0, movi .x7 0,
    .subImm .x .x8 .x7 1]),
  .loop (seqs [
    .block [.logic .eor .x .x3 .x10 .x9, movi .x4 1, .subs .x .x3 .x3 .x4, .csel .x .x15 .x7 .x8, mov .x16 .x2,
      mov .x17 .x13, mov .x14 .x12],
    Crt.selLoop,
    .block [.add .x .x2 .x2 .x11, .addImm .x .x10 .x10 1, .subImm .x .x3 .x10 16]]) (.nonzero .x .x3)] := rfl

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
    Frm.of_outside (ho.mono (o' := slot L.w aXm) (n' := 8 * (L.w + 2)) (Nat.le_refl _) (by omega)) (by simp)
  obtain ⟨-, -, -, c', bm', hc', hodd', hc1', hT', hY'⟩ :=
    WW.of_frm ⟨h4, h128, hEZ, c, bm, hc, hodd, hc1, hT, hY⟩ hf (by simp [wkRanges]) k (by decide)
  have hN := hc.ws.sl (show aN < 16 by decide)
  have hn' : c' = c := by rw [← hc'.n, ← hc.n, hf.wv_eq (by w_disj) (by omega)]
  subst hn'
  exact ⟨h4, h128, hEZ, c', bm', hc', hodd', hc1', hT', hY', by rw [hv]; exact hT d hd⟩

/-! ## A window -/

theorem mrSq_ct (M : Mont) : RelCT isa (Two WW) (seqs (mrSq M.mm)) (Two WW) := by
  rw [mrSq_eq]
  exact ct_app' (by simp) (by simp [eqMask, eqA]) (mmY_ct M)
    (ct_app' (by simp [eqMask, eqA]) (by simp) (eqW_ct (by decide) (by taint_decide)) flagOr_ct)

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
    · have := wkRanges_tab L.w r h; have := VG.Proof.Bignum.slot_mono L.w (show aT0 ≤ aE by decide); omega
    · subst h; have := slot_lt (w := L.w) (show aY < aE by decide); simp only at this ⊢; omega
  have hNe : wv t.mem L.B (slot L.w aN) L.w = wv s.mem L.B (slot L.w aN) L.w := by
    have dN : ∀ r ∈ wkRanges L.w, slot L.w aN + 8 * L.w ≤ r.1 ∨ r.1 + r.2 ≤ slot L.w aN := by
      unfold wkRanges; w_disj
    refine hf.wv_eq (fun r hr => ?_) (by omega)
    rcases hs r hr with h | h
    · exact dN r h
    · subst h; simp only [slot, hdrBytes, aY, aN]; omega
  refine ⟨hW, by rw [hNe]; exact hE.of_frm hf (fun r hr => Or.inr (hlo r hr)) (by omega), P, ?_⟩
  rw [hf.word_eq (fun r hr => ?_) (by decide)]
  · exact hP
  · have dF : ∀ r ∈ wkRanges L.w, r ≠ (8 * kFlag, 8) → 8 * kFlag + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * kFlag := by
      unfold wkRanges
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, ne_eq, Prod.mk.injEq,
        slot, hdrBytes, aAcc, aTmp, aXm, kG, kFlag, kPlen, kV, kT0, sCnt, kBits, kT2, kWords, kT1, sFn]
      and_intros <;> first | omega | simp
    rcases hs r hr with h | h
    · exact dF r h (hF r hr)
    · subst h; simp only [slot, hdrBytes, aY, kFlag, kPlen, sFn]; omega

theorem mmL_ct (M : Mont) : RelCT isa (Two WLast) (M.mm aY aY aY) (Two WLast) :=
  two_post (two_map id (fun _ _ h => h.1.goodW) (M.ct (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))) fun L s h => by
    have hW := h.1
    obtain ⟨h4, h128, hEZ, c, bm, hc, hodd, hc1, hT, hY⟩ := hW
    have hn := hc.ws.scr.nowrap
    refine WP.mono (M.mm_ok hc.good.1 hc.good.2 (by omega) (by omega) (o := aY) (a := aY) (b := aY) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
      (by rw [hc.n]; exact hY)) fun t ⟨_, hlt, _, ha, k⟩ => ?_
    have hf : Frm L.B [(slot L.w aAcc, 8 * (L.w + 2)), (slot L.w aTmp, 8 * (L.w + 2)), (slot L.w aY, 8 * (L.w + 2))]
        s.mem t.mem := Frm.of_arrays ha (by simp)
    refine h.of_frm hf (by simp [wkRanges]) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, ne_eq, Prod.mk.injEq, slot,
        hdrBytes, aAcc, aTmp, aY, kFlag, kPlen, sFn]
      and_intros <;> omega) ⟨h4, h128, hEZ, c, bm, hc.of_wk hf (by simp [wkRanges]) k (by decide), hodd, hc1,
        fun j hj => ?_, by rw [← hc.n]; exact hlt⟩
    have := tab_fits hEZ hj
    have := VG.Proof.Bignum.slot_mono L.w (show aT0 ≤ aT0 + j by omega)
    rw [hf.wv_eq (fun r hr => Or.inr (by have := mul3_low L.w r hr; omega)) (by omega)]
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
        hf.wv_eq (by w_disj) (by omega)
      have hEn : slot L.w aE + 8 * (L.w + 1) ≤ L.Z := by omega
      refine ⟨hW', by rw [hNe]; exact hE.of_frm hf (by w_disj) (by omega), _, by rw [hm, word_writeW_self]⟩

theorem mrLast_ct (M : Mont) {j : Nat} (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    RelCT isa (Two WLast) (seqs (mrLast M.mm j)) (Two WLast) := by
  rw [mrLast_eq]
  refine ct_app' (by simp) (by simp [eqMask, eqA]) (mmL_ct M) (ct_app' (by simp [eqMask, eqA]) (by simp) eqL_ct ?_)
  rcases hj with rfl | rfl | rfl
  · exact lastTail_ct (by taint_decide) (by decide)
  · exact lastTail_ct (by taint_decide) (by decide)
  · exact lastTail_ct (by taint_decide) (by decide)

end VG.Proof.RsaKeyGen.AArch64
