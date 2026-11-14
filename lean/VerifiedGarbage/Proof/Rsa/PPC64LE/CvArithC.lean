module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvArithA
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcMath
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyDiv
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.PPC64LE.MontKey
import VerifiedGarbage.Proof.Rsa.PPC64LE.IbOps
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.PPC64LE.DivN
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvTail

/-!
# `vg_rsa_crt_values` on PPC64LE: the arithmetic, `d` divided by `p - 1` and `q - 1`

`divD_ok`: `d` divided by a copy of `[a]` (`p` or `q`) with its low bit
cleared, the remainder in `[r]`. `partC_ok`: both.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs copy clrLow)
open VG.Impl.Rsa.PPC64LE.Div (div divP)
open VG.Impl.Rsa.PPC64LE.CrtValues (aQ aP aDQ aDD aDT aDR2 aDR3 aD aDR nArr divB divW shape tail)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- `divB len a r`: `d` divided by `[a]` with its low bit cleared, bit-serial, into `[r]`. -/
theorem divD_ok {s : State} {B : Addr} {Z w a r : Nat} (h : Ws s B Z w nArr)
    (ha : a = aP ∨ a = aQ) (hr : r = aDR2 ∨ r = aDR3)
    (top : w32 s.mem B (arr w aDD + 4 * w) = 0) {len : Reg} (hlen : len = .r20 ∨ len = .r22) {L : Nat}
    (hl : s.gpr len = BitVec.ofNat 64 L) (hL1 : 1 ≤ L) (hL : L < 2 ^ 32) (hlt : num s.mem B w a < 2 ^ (8 * L)) :
    WP isa (seqs (divB len a r)) s fun t => Ws t B Z w nArr ∧
      KeyWorkspace.Keep B w [aDQ, aDD, r, aDT] [] s.mem t.mem ∧
      (0 < 2 * (num s.mem B w a / 2) →
        num t.mem B w r = num s.mem B w aD % (2 * (num s.mem B w a / 2))) ∧
      w32 t.mem B (arr w aDD + 4 * w) = 0 ∧ Keep (.r12 :: stepRegs) s t := by
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  have fit : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have ha' : a < nArr ∧ a ≠ aDQ ∧ a ≠ aDD ∧ a ≠ aDT ∧ a ≠ aD := by
    rcases ha with rfl | rfl <;> decide
  have hr' : r < nArr ∧ r ≠ aDQ ∧ r ≠ aDD ∧ r ≠ aDT ∧ r ≠ aD ∧ r ≠ a := by
    rcases hr with rfl | rfl <;> rcases ha with rfl | rfl <;> decide
  obtain ⟨a1, a2, a3, a4, a5⟩ := ha'
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hr'
  unfold divB
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h (by decide) (by decide) (by decide) (by decide)) fun t1 ⟨h1, k1, v1, x1, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h1 (by decide) a1 (by decide) (Ne.symm a3)) fun t2 ⟨h2, k2, v2, x2, top2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine clrLow_ok h2 (by decide) (by decide) fun t30 h30 k30 v30 x30 top30 => ?_
  have hl0 : len ≠ .r0 := by rcases hlen with rfl | rfl <;> decide
  have l30 : t30.gpr len = BitVec.ofNat 64 L := by
    rcases hlen with rfl | rfl <;>
      rw [x30.gpr _ (by decide), x2.gpr _ (by decide), x1.gpr _ (by decide), hl]
  refine WP.mono (WP.keep [.r12] (Q := fun x => x.gpr .r12 = BitVec.ofNat 64 L ∧ x.mem = t30.mem)
    (by prun [l30, exec_addi hl0 (show 0 < 2 ^ 15 by decide), BitVec.add_zero]) (by cases len <;> decide))
    fun t3 ⟨⟨t12, tm⟩, k12⟩ => ?_
  have h3 : Ws t3 B Z w nArr := h30.of_keep k12
  have k3 := k30
  rw [← tm] at k3
  have v3 : num t3.mem B w aDD = 2 * (num t2.mem B w aDD / 2) := by rw [tm]; exact v30
  have x3 := x30.trans k12
  have topd : w32 t3.mem B (arr w aDD + 4 * w) = 0 := by
    rw [tm, top30, top2, KeyWorkspace.Keep.word k1 (i := w) (by omega_arith) (by decide) (by simp)
      (fit _ (by decide)), top]
  have a1'' : num t1.mem B w a = num s.mem B w a := k1.num (by simp; exact Ne.symm a2) (by simp) (fit _ a1)
  refine WP.mono (divP_ok h3 (by decide) r1 (by decide) (by decide) (by decide) (Ne.symm r2) (by decide)
    (by decide) r3 r4 (by decide) topd t12 hL1 hL (by rw [v3, v2, a1'']; omega_arith)) fun t ⟨h4, k4, x4, v4⟩ => ?_
  have a1' : num t1.mem B w a = num s.mem B w a := k1.num (by simp; exact Ne.symm a2) (by simp) (fit _ a1)
  have dd3 : num t3.mem B w aDD = 2 * (num s.mem B w a / 2) := by rw [v3, v2, a1']
  have dq3 : num t3.mem B w aDQ = num s.mem B w aD := by
    rw [k3.num (by decide) (by simp) (fit _ (by decide)), k2.num (by decide) (by simp) (fit _ (by decide)), v1]
  refine ⟨h4, ?_, fun hP => ?_, ?_, (((x1.trans x2).trans x3).trans x4).mono⟩
  · exact k1.mono.trans (k2.mono.trans (k3.mono.trans k4.mono))
  · obtain ⟨-, vr⟩ := v4 (by rw [dd3]; exact hP)
    rw [dd3, dq3] at vr
    have hlt : num1 t.mem B w r < 2 ^ (32 * w) := by
      rw [vr]
      have h1 : num s.mem B w a < 2 ^ (32 * w) := val32_lt _ _ _ _
      have h2 := Nat.mod_lt (num s.mem B w aD) hP
      omega_arith
    rw [num_of_num1 hlt, vr]
  · rw [KeyWorkspace.Keep.word k4 (i := w) (by omega_arith) (by simp; exact ⟨by decide, r3, by decide⟩) (by simp)
      (fit _ (by decide)), topd]

/-- `d` divided by `[a]` with its low bit cleared, by words, into `[r]`, for
`w = 4 wd`: exact when the divisor's top word (of `wd`) is not zero. -/
theorem divWD_ok {s : State} {B : Addr} {Z w a r : Nat} (h : Ws s B Z w nArr)
    (ha : a = aP ∨ a = aQ) (hr : r = aDR2 ∨ r = aDR3) (top : w32 s.mem B (arr w aDD + 4 * w) = 0)
    (hw : w = 4 * (w / 4)) (hw16 : 16 ≤ w) (hlt : num s.mem B w a < 2 ^ (64 * (w / 4))) :
    WP isa (seqs (VG.Impl.Rsa.PPC64LE.CrtValues.divW a r)) s fun t => Ws t B Z w nArr ∧
      KeyWorkspace.Keep B w [aDD, r, aDT, aDQ] [] s.mem t.mem ∧
      (0 < 2 * (num s.mem B w a / 2) → 2 ^ (64 * (w / 4 - 1)) ≤ 2 * (num s.mem B w a / 2) →
        num t.mem B w r = num s.mem B w aD % (2 * (num s.mem B w a / 2))) ∧
      w32 t.mem B (arr w aDD + 4 * w) = 0 ∧ Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] s t := by
  have := h.wle
  have nw := h.nowrap
  have fit : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have fD := fit aDD (by decide)
  simp only [S] at fD
  have ha' : a < nArr ∧ a ≠ aDD ∧ a ≠ aD := by rcases ha with rfl | rfl <;> decide
  have hr' : r < nArr ∧ r ≠ aDQ ∧ r ≠ aDD ∧ r ≠ aDT ∧ r ≠ aD := by rcases hr with rfl | rfl <;> decide
  obtain ⟨a1, a2, a3⟩ := ha'
  obtain ⟨r1, r2, r3, r4, r5⟩ := hr'
  unfold VG.Impl.Rsa.PPC64LE.CrtValues.divW
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h (by decide) a1 (by decide) (Ne.symm a2)) fun t1 ⟨h1, k1, v1, x1, top1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  rw [← List.append_nil (VG.Impl.Rsa.PPC64LE.Keys.clrLow aDD)]
  refine clrLow_ok h1 (by decide) (by decide) fun t2 h2 k2 v2 x2 top2 => WP.block_nil ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (VG.Proof.Rsa.PPC64LE.KeyDiv.fixTop_ok h2 (m := aDD) (by decide) (by decide) hw (by omega_using [hw16]))
    fun t3 ⟨m3, h3, k3⟩ => ?_
  have hd2 : num t2.mem B w aDD = 2 * (num s.mem B w a / 2) := by rw [v2, v1]
  have hdv : wordsVal t2.mem B (arr w aDD) (w / 4) = 2 * (num s.mem B w a / 2) := by
    rw [wordsVal_eq_val32]
    exact VG.Proof.Rsa.PPC64LE.MontKey.val32_low hd2 (by omega_using [])
      (by rw [show 32 * (2 * (w / 4)) = 64 * (w / 4) by omega_using []]; omega_using [hlt])
  have ft := VG.Proof.Rsa.PPC64LE.KeyDiv.fixTop_val (mem := t2.mem) (B := B) (d := arr w aDD) (wd := w / 4)
    (by omega_using [hw16]) (by omega_using [fD])
  rw [← m3] at ft
  obtain ⟨hT, hfix⟩ := ft
  have o3 : Outside B (arr w aDD + 8 * (w / 4 - 1)) 8 t2.mem t3.mem := by
    rw [m3]; exact writeW_outside _ B _ (by omega_using [fD])
  have kD : KeyWorkspace.Keep B w [aDD] [] t2.mem t3.mem :=
    KeyWorkspace.Keep.of_arr (o := aDD) o3 (by simp only [S]; omega_using []) (by simp)
  have dd3 : num t3.mem B w aD = num s.mem B w aD := by
    rw [kD.num (by decide) (by simp) (fit _ (by decide)), k2.num (by decide) (by simp) (fit _ (by decide)),
      k1.num (by decide) (by simp) (fit _ (by decide))]
  rw [show ∀ x : Prog isa, seqs [x] = x from fun _ => rfl]
  refine WP.mono (VG.Proof.Rsa.PPC64LE.KeyDiv.divW_ok h3 (by decide) r1 (by decide) (by decide) (by decide)
    (Ne.symm r5) (by decide) (by decide) r3 r4 r2 (by decide) (by decide) (by decide) (by decide) hw (by omega_using [hw16]) hT)
    fun t ⟨tr, ht, kt, mt⟩ => ⟨ht, ?_, fun _ hb => by rw [tr, dd3, hfix (by rw [hdv]; exact hb), hdv], ?_, ?_⟩
  · exact ((k1.mono (by simp) (by simp)).trans ((k2.mono (by simp) (by simp)).trans
      (kD.mono (by simp) (by simp)))).trans (mt.mono (by simp) (by simp))
  · have v3 : w32 t3.mem B (arr w aDD + 4 * w) = 0 := by
      rw [o3.w32 (by omega_using [hw16]) (by omega_using [fD]), top2, top1, top]
    rw [← v3]
    exact congrArg BitVec.toNat (VG.Proof.Rsa.PPC64LE.InvBatch.keep_word mt (b := 32) (o := 4 * w)
      (by simp only [S]; omega_using []) (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        exacts [r3, by decide, by decide]) (fun d hd => absurd hd (by simp)) (fit _ (by decide)))
  · exact (((x1.trans x2).trans k3).trans kt).mono (by decide)

/-- The divisions of `arith`: `shape`, then both by words or both bit-serial. -/
def partC : List (Prog isa) :=
  [.block shape, .ite (.zero .d .r0) (seqs (tail :: (divW aP aDR2 ++ divW aQ aDR3)))
    (seqs (divB .r20 aP aDR2 ++ divB .r22 aQ aDR3))]

/-- `partC`: `d mod (p - 1)` in `aDR2` and `d mod (q - 1)` in `aDR3`, exact but by
words for a balanced key, where the divisor's top word must not be zero. -/
theorem partC_ok {s : State} {B : Addr} {Z w pL qL : Nat} (h : Ws s B Z w nArr)
    (top : w32 s.mem B (arr w aDD + 4 * w) = 0) (h20 : s.gpr .r20 = BitVec.ofNat 64 pL)
    (h22 : s.gpr .r22 = BitVec.ofNat 64 qL) (hpL : 1 ≤ pL) (hqL : 1 ≤ qL) (hpw : pL < 2 ^ 32) (hqw : qL < 2 ^ 32)
    (hP : num s.mem B w aP < 2 ^ (8 * pL)) (hQ : num s.mem B w aQ < 2 ^ (8 * qL)) :
    WP isa (seqs partC) s fun t => Ws t B Z w nArr ∧
      KeyWorkspace.Keep B w [aDQ, aDD, aDR2, aDT, aDR3, aDR, 3, 4, 5] [] s.mem t.mem ∧
      (KeyCheck.Shape w pL qL → num s.mem B w 3 < num s.mem B w 8 → num s.mem B w 8 < 2 ^ (64 * (w / 4)) →
        2 ^ (64 * (w / 4 - 1)) ≤ num s.mem B w 8 →
        num t.mem B w 3 = num s.mem B w 3 * 2 ^ (5 * (3 * (w / 4) + 2)) % num s.mem B w 8) ∧
      (¬ KeyCheck.Shape w pL qL → num t.mem B w 3 = num s.mem B w 3) ∧
      (0 < 2 * (num s.mem B w aP / 2) → (KeyCheck.Shape w pL qL → 2 ^ (64 * (w / 4 - 1)) ≤ 2 * (num s.mem B w aP / 2)) →
        num t.mem B w aDR2 = num s.mem B w aD % (2 * (num s.mem B w aP / 2))) ∧
      (0 < 2 * (num s.mem B w aQ / 2) → (KeyCheck.Shape w pL qL → 2 ^ (64 * (w / 4 - 1)) ≤ 2 * (num s.mem B w aQ / 2)) →
        num t.mem B w aDR3 = num s.mem B w aD % (2 * (num s.mem B w aQ / 2))) ∧
      Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] s t := by
  have := h.wle
  have fit : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  unfold partC
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shape_ok h.r29 h20 h22 (by omega_using [this]) hpw hqw) fun s1 ⟨z1, m1, k1⟩ => ?_
  have h1 := h.of_keep k1
  have g1 : ∀ x ∈ [Reg.r20, .r22], s1.gpr x = s.gpr x := fun x hx => k1.gpr x (by revert x hx; decide)
  rw [show ∀ x : Prog isa, seqs [x] = x from fun _ => rfl]
  refine WP.ite (s1.gpr .r0 == 0) (eval_zero s1 .r0) (fun hz => ?_) (fun hz => ?_)
  · -- By words: the inverse's tail, then the divisions.
    obtain ⟨p8, hpw2, hpq, p32⟩ := z1.1 (by simpa using hz)
    have hw : w = 4 * (w / 4) := by omega_using [p8, hpw2]
    have hS : S w = 4 * (w + 2) := rfl
    rw [wp_seqs_cons (by simp [VG.Impl.Rsa.PPC64LE.CrtValues.divW])]
    refine WP.mono (tail_ok h1 hw (by omega_using [hpw2, p32])) fun t1 ⟨h1', K1, v1, x1⟩ => ?_
    rw [m1] at K1 v1
    have kp : ∀ j, j = aP ∨ j = aQ ∨ j = aD → num t1.mem B w j = num s.mem B w j := fun j hj => by
      rcases hj with rfl | rfl | rfl <;> exact K1.num (by decide) (by simp) (fit _ (by decide))
    have top1 : w32 t1.mem B (arr w aDD + 4 * w) = 0 := by
      rw [KeyWorkspace.Keep.word K1 (i := w) (by omega_arith) (by decide) (by simp) (fit _ (by decide)), top]
    rw [wp_seqs_append (by simp [VG.Impl.Rsa.PPC64LE.CrtValues.divW])
      (by simp [VG.Impl.Rsa.PPC64LE.CrtValues.divW])]
    refine WP.mono (divWD_ok h1' (.inl rfl) (.inl rfl) top1 hw (by omega_using [hpw2, p32])
      (by rw [kp aP (.inl rfl), show 64 * (w / 4) = 8 * pL by omega_using [p8, hpw2]]; exact hP)) fun t2 ⟨h2, k2, v2, top2, x2⟩ => ?_
    have q2 : num t2.mem B w aQ = num s.mem B w aQ := by
      rw [k2.num (by decide) (by simp) (fit _ (by decide)), kp aQ (.inr (.inl rfl))]
    refine WP.mono (divWD_ok h2 (.inr rfl) (.inr rfl) top2 hw (by omega_using [hpw2, p32])
      (by rw [q2, show 64 * (w / 4) = 8 * qL by omega_using [p8, hpw2, hpq]]; exact hQ)) fun t ⟨h3, k3, v3, _, x3⟩ => ?_
    have d2 : num t2.mem B w aD = num s.mem B w aD := by
      rw [k2.num (by decide) (by simp) (fit _ (by decide)), kp aD (.inr (.inr rfl))]
    have hs : KeyCheck.Shape w pL qL := ⟨p8, hpw2, hpq, p32⟩
    have y3 : num t.mem B w 3 = num t1.mem B w 3 := by
      rw [k3.num (by decide) (by simp) (fit _ (by decide)), k2.num (by decide) (by simp) (fit _ (by decide))]
    refine ⟨h3, ?_, fun _ a b c => by rw [y3]; exact v1 a b c, fun hn => absurd hs hn, fun h0 hb => ?_,
      fun h0 hb => ?_, (((k1.trans x1).trans x2).trans x3).mono (by decide)⟩
    · exact (K1.mono (by decide)).trans ((k2.mono (by decide) (by simp)).trans (k3.mono (by decide) (by simp)))
    · rw [k3.num (by decide) (by simp) (fit _ (by decide)), v2 (by rw [kp aP (.inl rfl)]; exact h0)
        (by rw [kp aP (.inl rfl)]; exact hb hs), kp aD (.inr (.inr rfl)), kp aP (.inl rfl)]
    · rw [v3 (by rw [q2]; exact h0) (by rw [q2]; exact hb hs), d2, q2]
  · -- Bit-serial.
    rw [wp_seqs_append (by simp [divB]) (by simp [divB])]
    refine WP.mono (divD_ok h1 (.inl rfl) (.inl rfl) (by rw [m1]; exact top) (len := .r20) (.inl rfl)
      ((g1 .r20 (by decide)).trans h20) hpL hpw (by rw [m1]; exact hP)) fun t2 ⟨h2, k2, v2, top2, x2⟩ => ?_
    have q2 : num t2.mem B w aQ = num s.mem B w aQ := by
      rw [k2.num (by decide) (by simp) (fit _ (by decide)), m1]
    refine WP.mono (divD_ok h2 (.inr rfl) (.inr rfl) top2 (len := .r22) (.inr rfl)
      (by rw [x2.gpr _ (by decide), g1 .r22 (by decide), h22]) hqL hqw (by rw [q2]; exact hQ))
      fun t ⟨h3, k3, v3, _, x3⟩ => ?_
    have d2 : num t2.mem B w aD = num s.mem B w aD := by
      rw [k2.num (by decide) (by simp) (fit _ (by decide)), m1]
    have hs : ¬ KeyCheck.Shape w pL qL := fun hs => by simp [z1.2 hs] at hz
    refine ⟨h3, ?_, fun h' => absurd h' hs, fun _ => ?_, fun h0 _ => ?_, fun h0 _ => ?_,
      ((k1.trans x2).trans x3).mono (by decide)⟩
    · rw [← m1]; exact (k2.mono (by decide) (by simp)).trans (k3.mono (by decide) (by simp))
    · rw [k3.num (by decide) (by simp) (fit _ (by decide)), k2.num (by decide) (by simp) (fit _ (by decide)), m1]
    · rw [k3.num (by decide) (by simp) (fit _ (by decide)), v2 (by rw [m1]; exact h0), m1]
    · rw [v3 (by rw [q2]; exact h0), d2, q2]

end VG.Proof.Rsa.PPC64LE.CrtValues
