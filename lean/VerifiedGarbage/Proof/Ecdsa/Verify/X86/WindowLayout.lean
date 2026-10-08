import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowPrep
import VerifiedGarbage.Proof.Weierstrass.X86.WinLoop

/-! # Scratch layout and preservation for the x86 P-256 window -/

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.X86
variable {c : Impl.Ecdsa.X86.Cfg}

private theorem listLay {M : Mod} {sz : Nat} {xs : List Nat}
    (hle : xs.all (fun x => decide (x + 8 * M.n ≤ sz)) = true)
    (hap : xs.all (fun x => xs.all (fun y => decide
      (x ≠ y → x + 8 * M.n ≤ y ∨ y + 8 * M.n ≤ x))) = true)
    (hmo : xs.all (fun x => decide (x + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ x)) = true)
    (htmp : xs.all (fun x => decide (x + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ x)) = true) :
    Lay M sz (· ∈ xs) := by
  refine ⟨fun x hx => ?_, fun x y hx hy => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · exact of_decide_eq_true (List.all_eq_true.mp hle x hx)
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hap x hx) y hy)
  · exact of_decide_eq_true (List.all_eq_true.mp hmo x hx)
  · exact of_decide_eq_true (List.all_eq_true.mp htmp x hx)

macro "window_layout" h:term : tactic => `(tactic|
  (simp only [Impl.Ecdsa.Verify.X86.Cfg.windowQ, Impl.Ecdh.X86.Cfg.windowCfg, Impl.Ecdsa.X86.Cfg.MP',
    Impl.Ecdsa.X86.Cfg.rcbSlots, Impl.Ecdsa.X86.Cfg.pt, Impl.Ecdsa.X86.Cfg.sl,
    slot, ($h), winSlots, winRo, winOther, winWs, winTblSlots, rcbW,
    List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    winW, Impl.Ecdh.X86.Cfg.windowBits, Mont.outW, Mont.own, Spec.Weierstrass.Mont.ownAt,
    Spec.Weierstrass.Mont.ownBytes, words, List.forall_mem_cons, List.forall_mem_nil, List.forall_mem_append,
    List.forall_mem_map]; decide))

/-- The variable-base table is disjoint from all original slots. -/
theorem windowLay (h4 : c.n = 4) : WinLay (Impl.Ecdsa.Verify.X86.Cfg.windowQ c) size := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply listLay
    all_goals window_layout h4
  all_goals window_layout h4

/-- The field arithmetic's own working space, `Mont.own 4`. -/
theorem windowWk (hc : CfgOk c) (h4 : c.n = 4) :
    WinWk (Impl.Ecdsa.Verify.X86.Cfg.windowQ c) c.SP c.C.p size (Mont.own c.n) := by
  refine ⟨⟨⟨hc.fp.2.2, hc.fp.1, hc.fp.2.1, rfl, rfl⟩, ?_, ?_, ?_⟩, ?_⟩
  all_goals window_layout h4

abbrev windowSlots : List Nat :=
  [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM]
/-- What the window writes: its slots, the table and the field arithmetic's
own working space (`[2640, 4096)`), the bits of the scalar, and memory past
the working space (the calls'). -/
abbrev windowW (c : Impl.Ecdsa.X86.Cfg) : List (Nat × Nat) :=
  slW c windowSlots ++ [(2640, 1456), (Impl.Ecdh.X86.Cfg.windowBits, 320), Mont.outW]

theorem windowW_fixed (h4 : c.n = 4) : FixedOk c (windowW c) := by
  refine (fixedOk_slW (by decide)).append ?_
  intro w hw
  right
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rw [sl_eq, h4]
  rcases hw with rfl | rfl | rfl <;> decide

theorem windowW_apart (h4 : c.n = 4) {i : Nat} (hi : i < 45) (hw : i ∉ windowSlots) :
    ∀ w ∈ windowW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  refine apart_append (apart_slW hw) ?_
  intro w hw
  left
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rw [sl_eq, h4]
  rcases hw with rfl | rfl | rfl <;> dsimp only [Impl.Ecdh.X86.Cfg.windowBits, Mont.outW] <;> omega

theorem windowW_cover (h4 : c.n = 4) :
    ∀ w ∈ winWX (Impl.Ecdsa.Verify.X86.Cfg.windowQ c) (Mont.own c.n),
      ∃ w' ∈ windowW c, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  simp only [winWX, windowW, slW]
  window_layout h4

theorem windowW_table (h4 : c.n = 4) {t : Nat} (ht : t < 64 * c.n) :
    ∀ w ∈ windowW c, bitsAt c.n 1 + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n 1 + t := by
  refine apart_append (tbl_apart_slW (by decide) 1 t (by rw [h4]; decide)) ?_
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rw [bitsAt_eq, h4]
  rw [h4] at ht
  rcases hw with rfl | rfl | rfl <;> dsimp only [Impl.Ecdh.X86.Cfg.windowBits, Mont.outW] <;> omega

end VG.Proof.Ecdsa.Verify.X86
