module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintBase
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Pack.Hint
public import VerifiedGarbage.Proof.MlDsa.Pack.Hint2
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
import VerifiedGarbage.Proof.MlDsa.Pack.Mem
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlKem.RISCV64.Bytes
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep

/-!
# ML-DSA on RISC-V: `vg_mldsa_hint_bit_pack`, correct

As on AArch64 (`Proof/MlDsa/AArch64/Pack/HintPack.lean`), the code follows
the fold form of `HintBitPack` (`Proof/MlDsa/Pack/Hint.lean`) step by step:
the bytes of `y` are the array of the spec (`hpS`, `hpT`), and `t1` its
index, which stays below `ω` because it counts the 1s before the current
coefficient (`hpT_idx_lt`). Zeroing `y` (`zero_ok`) leaves the state the
loops start from (`ZPost`), from which constant time takes the runs
(`HintPackCT.lean`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Pack.Hint

open VG.RISCV64.Steps (Upd Mupd)
open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.RISCV64 (wp_loop_nz count_sub count_nz ptr_add byte_writeW8)
open VG.Proof.MlKem (bytesAt_writeW8 bytesAt_eq)
open VG.Proof.MlDsa.Pack

theorem _root_.VG.RISCV64.Steps.Upd.keepH {s s' : State} {d : Reg} {v : BitVec 64} (h : Upd s s' d v) : Keep [d] s s' :=
  ⟨fun r hr => h.other r fun e => hr (e ▸ List.mem_singleton_self _), h.rd, h.wr⟩

theorem _root_.VG.RISCV64.Steps.Mupd.keepH {s s' : State} {m : Mem} (h : Mupd s s' m) : Keep [] s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr⟩

theorem add0 (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## The arguments -/

section
variable (s₀ : State)

/-- `h`, `ω`, `y` and `len`. -/
abbrev pH : Addr := s₀.gpr .a0
abbrev pω : Nat := w32 s₀ .a2
abbrev pY : Addr := s₀.gpr .a3
abbrev pLen : Nat := (s₀.gpr .a4).toNat
abbrev pk : Nat := pLen s₀ - pω s₀
abbrev hR : Region := ⟨pH s₀, (s₀.gpr .a1).toNat * 4⟩
abbrev yR : Region := ⟨pY s₀, pLen s₀⟩
/-- The hint. -/
abbrev pHint : List (Vector Bool n) := hintAt s₀.mem (pH s₀) (pk s₀)
abbrev pS (i : Nat) : Array Byte × Nat := hpS (pω s₀) (pk s₀) (pHint s₀) i
abbrev pT (i j : Nat) : Array Byte × Nat := hpT (pω s₀) (pk s₀) (pHint s₀) i j

end

/-- The precondition, as `sig_pre` states it. -/
structure PPre (s : State) : Prop where
  rd : s.rd = [hR s]
  wr : s.wr = [yR s]
  d_hy : (hR s).Disjoint (yR s)
  fitH : (pH s).toNat + (s.gpr .a1).toNat * 4 ≤ 2 ^ 64
  fitY : (pY s).toNat + pLen s ≤ 2 ^ 64
  par : (pω s, pk s) ∈ hintParams
  ωle : pω s ≤ pLen s
  hlen : (s.gpr .a1).toNat = 256 * pk s
  ones : hintOnes (pHint s) ≤ pω s
  al : (pH s).toNat % 4 = 0

theorem pfacts {s₀ : State} (hp : PPre s₀) :
    4 ≤ pk s₀ ∧ pk s₀ ≤ 8 ∧ 55 ≤ pω s₀ ∧ pω s₀ ≤ 80 ∧ pω s₀ + pk s₀ = pLen s₀ ∧ pLen s₀ ≤ 88 := by
  have := mem_hintParams' hp.par
  have := hp.ωle
  have e : pk s₀ = pLen s₀ - pω s₀ := rfl
  omega_arith

/-! ## Zeroing `y` -/

/-- What zeroing `y` leaves. -/
structure ZPost (s₀ s : State) : Prop where
  a0 : s.gpr .a0 = pH s₀
  a1 : s.gpr .a1 = BitVec.ofNat 64 (pk s₀)
  a2 : s.gpr .a2 = BitVec.ofNat 64 (pω s₀)
  a3 : s.gpr .a3 = pY s₀
  zero : ∀ t < pLen s₀, s.mem (pY s₀ + BitVec.ofNat 64 t) = 0
  frame : Frame [yR s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The zeroing loop after `t` bytes, from `s₁`. -/
structure ZInv (s₀ s₁ : State) (t : Nat) (s : State) : Prop where
  a7 : s.gpr .a7 = pY s₀ + BitVec.ofNat 64 t
  a6 : s.gpr .a6 = BitVec.ofNat 64 (pLen s₀ - t)
  keep : Keep [.a6, .a7] s₁ s
  frame : Frame [yR s₀] s₀.mem s.mem
  zero : ∀ u < t, s.mem (pY s₀ + BitVec.ofNat 64 u) = 0

theorem zero_ok {s₀ : State} (hp : PPre s₀) : WP isa hbpZero s₀ (ZPost s₀) := by
  obtain ⟨hk4, -, -, -, hsum, hL88⟩ := pfacts hp
  have fY := hp.fitY
  unfold hbpZero zextOmega
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (Steps.wp_sll (by decide) fun s₁ o₁ => Steps.wp_srl (by decide) fun s₂ o₂ => Steps.wp_sub fun s₃ o₃ =>
    Steps.wp_addi (by decide) fun s₄ o₄ => Steps.wp_li (by decide) fun s₅ o₅ =>
    Steps.wp_addi (by decide) fun s₆ o₆ => WP.block_nil ?_)
  have k₅ := (((o₁.keepH.trans o₂.keepH).trans o₃.keepH).trans o₄.keepH).trans o₅.keepH
  have k₆ := k₅.trans o₆.keepH
  have m₆ : s₆.mem = s₀.mem := by rw [o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  have r5 : s₆.gpr .a2 = BitVec.ofNat 64 (pω s₀) := by
    rw [o₆.other _ (by decide), o₅.other _ (by decide), o₄.other _ (by decide), o₃.other _ (by decide), o₂.gpr,
      o₁.gpr, zext_eq]
  have r0 : s₆.gpr .t0 = 0 := by rw [o₆.other _ (by decide), o₅.gpr]; rfl
  have r4 : s₆.gpr .a1 = BitVec.ofNat 64 (pk s₀) := by
    rw [o₆.other _ (by decide), o₅.other _ (by decide), o₄.other _ (by decide), o₃.gpr,
      o₂.other _ (by decide), o₁.other _ (by decide), o₂.gpr, o₁.gpr, zext_eq]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, ofNat_lt (by omega_arith)]; exact hp.ωle), ofNat_lt (by omega_arith), ofNat_lt (by omega_arith)]
  have hwr : s₆.wr = [yR s₀] := by rw [k₆.2.2, hp.wr]
  refine WP.mono (wp_loop_nz (ZInv s₀ s₆) (N := pLen s₀) (by omega_arith) (fun t ht s h => ?_) (fun s h => h)
    ⟨by rw [o₆.gpr, k₅.gpr (r := .a3) (by decide), add0], ?_, Keep.refl _ _, by rw [m₆]; exact Frame.refl _ _,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s h => ?_
  · -- A byte.
    have hc : (yR s₀).Contains (pY s₀ + BitVec.ofNat 64 t) 1 := Offset.contains_base _ (by omega_arith) (by omega_arith)
    refine Steps.wp_sb (by decide) (by rw [h.a7, add0])
      (by rw [h.keep.2.2, hwr]; exact ⟨_, List.mem_singleton_self _, hc⟩) fun s₁ m₁ =>
      Steps.wp_addi (by decide) fun s₂ o₂ => Steps.wp_subi (by decide) fun s₃ o₃ => WP.block_nil ?_
    have c9 : s₃.gpr .a6 = BitVec.ofNat 64 (pLen s₀ - (t + 1)) := by
      rw [o₃.gpr, o₂.other _ (by decide), m₁.gpr, h.a6, count_sub ht]
    have m₃ : s₃.mem = s.mem.writeW (pY s₀ + BitVec.ofNat 64 t) ((s.gpr .t0).setWidth 8) := by
      rw [o₃.mem, o₂.mem, m₁.mem]
    refine ⟨⟨?_, c9, (h.keep.trans ((m₁.keepH.trans o₂.keepH).trans o₃.keepH)).mono (by decide), ?_, fun u hu => ?_⟩,
      by rw [c9]; exact count_nz ht (by omega_arith)⟩
    · rw [o₃.other _ (by decide), o₂.gpr, m₁.gpr, h.a7, ptr_add]
    · rw [m₃]; exact h.frame.writeW (List.mem_singleton_self _) _ hc
    · rw [m₃, byte_writeW8 _ _ (by omega_arith) (by omega_arith)]
      split
      · rw [h.keep.gpr (by decide), r0]; rfl
      · exact h.zero u (by omega_arith)
  · rw [o₆.other _ (by decide), o₅.other _ (by decide), o₄.gpr, add0, Nat.sub_zero, ofNat_toNat64,
      o₃.other _ (by decide), o₂.other _ (by decide), o₁.other _ (by decide)]
  · exact ⟨by rw [h.keep.gpr (by decide), k₆.gpr (by decide)], by rw [h.keep.gpr (by decide), r4],
      by rw [h.keep.gpr (by decide), r5], by rw [h.keep.gpr (by decide), k₆.gpr (by decide)], h.zero, h.frame,
      h.keep.2.1.trans k₆.2.1, h.keep.2.2.trans k₆.2.2⟩

/-! ## The polynomials -/

theorem pT_zero (s₀ : State) (i : Nat) : pT s₀ i 0 = pS s₀ i := hpT_zero _ _ _ i

theorem pS_succ (s₀ : State) (i : Nat) :
    pS s₀ (i + 1) = ((pT s₀ i 256).1.set! (pω s₀ + i) (BitVec.ofNat 8 (pT s₀ i 256).2), (pT s₀ i 256).2) :=
  hpS_succ _ _ _ i

/-- Before coefficient `j` of polynomial `i`. -/
structure CInv (s₀ : State) (i j : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = pH s₀ + BitVec.ofNat 64 (4 * (256 * i + j))
  a3 : s.gpr .a3 = pY s₀
  a6 : s.gpr .a6 = BitVec.ofNat 64 (pk s₀ - i)
  a7 : s.gpr .a7 = pY s₀ + BitVec.ofNat 64 (pω s₀ + i)
  t1 : s.gpr .t1 = BitVec.ofNat 64 (pT s₀ i j).2
  t2 : s.gpr .t2 = BitVec.ofNat 64 j
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [yR s₀] s₀.mem s.mem
  y : bytesAt s.mem (pY s₀) (pLen s₀) = (pT s₀ i j).1.toList

/-- The end of a coefficient: the pointer, `j` and the counter. -/
theorem coefTail_ok {s₀ : State} {i j : Nat} (hj : j < 256) {s : State}
    (r3 : s.gpr .a0 = pH s₀ + BitVec.ofNat 64 (4 * (256 * i + j))) (r6 : s.gpr .a3 = pY s₀)
    (r9 : s.gpr .a6 = BitVec.ofNat 64 (pk s₀ - i)) (r10 : s.gpr .a7 = pY s₀ + BitVec.ofNat 64 (pω s₀ + i))
    (r11 : s.gpr .t1 = BitVec.ofNat 64 (pT s₀ i (j + 1)).2) (r12 : s.gpr .t2 = BitVec.ofNat 64 j)
    (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) (frame : Frame [yR s₀] s₀.mem s.mem)
    (y : bytesAt s.mem (pY s₀) (pLen s₀) = (pT s₀ i (j + 1)).1.toList) :
    WP isa (.block [.addi .a0 .a0 4, .addi .t2 .t2 1, .addi .a5 .t2 (-256)]) s fun s' =>
      CInv s₀ i (j + 1) s' ∧ (s'.gpr .a5 != 0) = decide (j + 1 ≠ 256) :=
  Steps.wp_addi (by decide) fun s₁ o₁ => Steps.wp_addi (by decide) fun s₂ o₂ =>
    Steps.wp_subi (by decide) fun s₃ o₃ => WP.block_nil (by
      have k₃ := (o₁.keepH.trans o₂.keepH).trans o₃.keepH
      have c12' : s₂.gpr .t2 = BitVec.ofNat 64 (j + 1) := by
        rw [o₂.gpr, o₁.other _ (by decide), r12, ofNat_succ]
      have c12 : s₃.gpr .t2 = BitVec.ofNat 64 (j + 1) := by rw [o₃.other _ (by decide), c12']
      refine ⟨⟨?_, by rw [k₃.gpr (by decide), r6], by rw [k₃.gpr (by decide), r9], by rw [k₃.gpr (by decide), r10],
        by rw [k₃.gpr (by decide), r11], c12, by rw [k₃.2.1, rd], by rw [k₃.2.2, wr],
        by rw [o₃.mem, o₂.mem, o₁.mem]; exact frame, by rw [o₃.mem, o₂.mem, o₁.mem]; exact y⟩, ?_⟩
      · rw [o₃.other _ (by decide), o₂.other _ (by decide), o₁.gpr, r3, ptr_add,
          show 4 * (256 * i + j) + 4 = 4 * (256 * i + (j + 1)) by omega_arith]
      · rw [o₃.gpr, c12']; exact cnt256 hj)

/-- Coefficient `j` of polynomial `i`: if it is not 0, `y[index] ← j`. -/
theorem coef_ok {s₀ : State} (hp : PPre s₀) {i j : Nat} (hi : i < pk s₀) (hj : j < 256) {s : State}
    (hI : CInv s₀ i j s) :
    WP isa hbpCoef s fun s' => CInv s₀ i (j + 1) s' ∧ (s'.gpr .a5 != 0) = decide (j + 1 ≠ 256) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := pfacts hp
  have fH := hp.fitH
  have fY := hp.fitY
  have hl := hp.hlen
  have hpos : 256 * i + j < 256 * pk s₀ := by omega_arith
  have hR' : (hR s₀).Contains (coeffAddr (pH s₀) (256 * i + j)) 4 := Offset.contains_base _ (by omega_arith) (by omega_arith)
  have hw : s.mem.readW (coeffAddr (pH s₀) (256 * i + j)) 32 = coeffAt s₀.mem (pH s₀) (256 * i + j) :=
    hI.frame.readW hR' (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.d_hy) (by decide)
  have hbit := hintAt_get (m := s₀.mem) (p := pH s₀) hi (show j < n from hj)
  have hT : pT s₀ i (j + 1) = hpStep ((pHint s₀).getD i noHint) (pT s₀ i j) j := hpT_succ _ _ _ i j
  unfold hbpCoef
  refine WP.seq (Steps.wp_lwu (a := coeffAddr (pH s₀) (256 * i + j)) (by decide) (by rw [hI.a0, add0])
    (VG.Proof.MlKem.RISCV64.align4_add hp.al _)
    (by rw [hI.rd, hI.wr, hp.rd]; exact ⟨_, .head _, hR'⟩) fun s₁ o₁ => WP.block_nil ?_)
  have hb : (s₁.gpr .a5 == 0) = !((pHint s₀).getD i noHint)[j]! := by
    rw [hbit, o₁.gpr, word_w_zero, hw, Bool.beq_eq_decide_eq]
    by_cases e : coeffAt s₀.mem (pH s₀) (256 * i + j) = 0 <;> simp [e]
  refine WP.seq (WP.ite _ (eval_zero_w s₁ .a5) (fun h0 => ?_) (fun h1 => ?_))
  · -- A 0.
    rw [hb, Bool.not_eq_true'] at h0
    have hT0 : pT s₀ i (j + 1) = pT s₀ i j := by rw [hT, hpStep, h0]; rfl
    refine WP.block_nil (coefTail_ok hj (by rw [o₁.other _ (by decide), hI.a0]) (by rw [o₁.other _ (by decide), hI.a3])
      (by rw [o₁.other _ (by decide), hI.a6]) (by rw [o₁.other _ (by decide), hI.a7])
      (by rw [o₁.other _ (by decide), hI.t1, hT0]) (by rw [o₁.other _ (by decide), hI.t2])
      (by rw [o₁.rd, hI.rd]) (by rw [o₁.wr, hI.wr]) (by rw [o₁.mem]; exact hI.frame) (by rw [o₁.mem, hI.y, hT0]))
  · -- A 1: `y[index] ← j`.
    rw [hb, Bool.not_eq_false'] at h1
    have hlt : (pT s₀ i j).2 < pω s₀ := hpT_idx_lt (hintAt_length _ _ _) hp.ones hi (show j < n from hj) h1
    have hc : (yR s₀).Contains (pY s₀ + BitVec.ofNat 64 (pT s₀ i j).2) 1 := Offset.contains_base _ (by omega_arith) (by omega_arith)
    refine Steps.wp_add fun s₂ o₂ => wp_stb (a := pY s₀ + BitVec.ofNat 64 (pT s₀ i j).2) (by decide) (by decide)
      (by rw [o₂.gpr, o₁.other _ (by decide), o₁.other _ (by decide), hI.a3, hI.t1, add0])
      (by rw [o₂.wr, o₁.wr, hI.wr, hp.wr]; exact ⟨_, .head _, hc⟩) fun s₃ m₃ =>
      Steps.wp_addi (by decide) fun s₄ o₄ => WP.block_nil ?_
    have k₄ := ((o₁.keepH.trans o₂.keepH).trans m₃.keepH).trans o₄.keepH
    have mem₄ : s₄.mem = s.mem.writeW (pY s₀ + BitVec.ofNat 64 (pT s₀ i j).2) (BitVec.ofNat 8 j) := by
      rw [o₄.mem, m₃.mem, o₂.mem, o₁.mem, o₂.other _ (by decide), o₁.other _ (by decide), hI.t2, lowByte]
    have hT1 : pT s₀ i (j + 1) = ((pT s₀ i j).1.set! (pT s₀ i j).2 (BitVec.ofNat 8 j), (pT s₀ i j).2 + 1) := by
      rw [hT, hpStep, h1]; rfl
    refine coefTail_ok hj (by rw [k₄.gpr (by decide), hI.a0]) (by rw [k₄.gpr (by decide), hI.a3])
      (by rw [k₄.gpr (by decide), hI.a6]) (by rw [k₄.gpr (by decide), hI.a7])
      (by rw [o₄.gpr, m₃.gpr, o₂.other _ (by decide), o₁.other _ (by decide), hI.t1, hT1, ofNat_succ])
      (by rw [k₄.gpr (by decide), hI.t2]) (by rw [k₄.2.1, hI.rd]) (by rw [k₄.2.2, hI.wr]) ?_ ?_
    · rw [mem₄]; exact hI.frame.writeW (List.mem_singleton_self _) _ hc
    · rw [mem₄, bytesAt_writeW8 _ _ (by omega_arith) (by omega_arith), hI.y, hT1]
      simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]

/-- Before polynomial `i`. -/
structure HPInv (s₀ : State) (i : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = pH s₀ + BitVec.ofNat 64 (4 * (256 * i))
  a3 : s.gpr .a3 = pY s₀
  a6 : s.gpr .a6 = BitVec.ofNat 64 (pk s₀ - i)
  a7 : s.gpr .a7 = pY s₀ + BitVec.ofNat 64 (pω s₀ + i)
  t1 : s.gpr .t1 = BitVec.ofNat 64 (pS s₀ i).2
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [yR s₀] s₀.mem s.mem
  y : bytesAt s.mem (pY s₀) (pLen s₀) = (pS s₀ i).1.toList

theorem poly_ok {s₀ : State} (hp : PPre s₀) {i : Nat} (hi : i < pk s₀) {s : State} (hP : HPInv s₀ i s) :
    WP isa hbpPoly s fun s' => HPInv s₀ (i + 1) s' ∧ (s'.gpr .a6 != 0) = decide (i + 1 ≠ pk s₀) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := pfacts hp
  have fY := hp.fitY
  unfold hbpPoly
  refine WP.seq (Steps.wp_li (by decide) fun s₁ o₁ => WP.block_nil ?_)
  refine WP.seq (wp_loop_nz (CInv s₀ i) (N := 256) (by decide) (fun j hj s hI => coef_ok hp hi hj hI)
    (fun s h => ?_) ⟨by rw [o₁.other _ (by decide), hP.a0, Nat.add_zero], by rw [o₁.other _ (by decide), hP.a3],
      by rw [o₁.other _ (by decide), hP.a6], by rw [o₁.other _ (by decide), hP.a7],
      by rw [o₁.other _ (by decide), hP.t1, pT_zero], o₁.gpr, by rw [o₁.rd, hP.rd], by rw [o₁.wr, hP.wr],
      by rw [o₁.mem]; exact hP.frame, by rw [o₁.mem, hP.y, pT_zero]⟩)
  have hidx : (pT s₀ i 256).2 ≤ pω s₀ := hpT_idx_le (hintAt_length _ _ _) hp.ones hi
  have hc : (yR s₀).Contains (pY s₀ + BitVec.ofNat 64 (pω s₀ + i)) 1 := Offset.contains_base _ (by omega_arith) (by omega_arith)
  refine Steps.wp_sb (by decide) (by rw [h.a7, add0]) (by rw [h.wr, hp.wr]; exact ⟨_, .head _, hc⟩)
    fun s₂ m₂ => Steps.wp_addi (by decide) fun s₃ o₃ => Steps.wp_subi (by decide) fun s₄ o₄ => WP.block_nil ?_
  have k₄ := (m₂.keepH.trans o₃.keepH).trans o₄.keepH
  have c9 : s₄.gpr .a6 = BitVec.ofNat 64 (pk s₀ - (i + 1)) := by
    rw [o₄.gpr, o₃.other _ (by decide), m₂.gpr, h.a6, count_sub hi]
  have mem₄ : s₄.mem = s.mem.writeW (pY s₀ + BitVec.ofNat 64 (pω s₀ + i)) (BitVec.ofNat 8 (pT s₀ i 256).2) := by
    rw [o₄.mem, o₃.mem, m₂.mem, h.t1, lowByte]
  refine ⟨⟨?_, by rw [k₄.gpr (by decide), h.a3], c9, ?_, by rw [k₄.gpr (by decide), h.t1, pS_succ],
    by rw [k₄.2.1, h.rd], by rw [k₄.2.2, h.wr], ?_, ?_⟩, by rw [c9]; exact count_nz hi (by omega_arith)⟩
  · rw [k₄.gpr (by decide), h.a0, show 4 * (256 * i + 256) = 4 * (256 * (i + 1)) by omega_arith]
  · rw [o₄.other _ (by decide), o₃.gpr, m₂.gpr, h.a7, ptr_add, Nat.add_assoc]
  · rw [mem₄]; exact h.frame.writeW (List.mem_singleton_self _) _ hc
  · rw [mem₄, bytesAt_writeW8 _ _ (by omega_arith) (by omega_arith), h.y, pS_succ]
    simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]

theorem main_ok {s₀ : State} (hp : PPre s₀) {s : State} (hz : ZPost s₀ s) :
    WP isa hbpMain s fun s' =>
      bytesAt s'.mem (pY s₀) (pLen s₀) = hintBitPack (pω s₀) (pk s₀) (pHint s₀) ∧ Frame [yR s₀] s₀.mem s'.mem := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := pfacts hp
  unfold hbpMain
  refine WP.seq (Steps.wp_addi (by decide) fun s₁ o₁ => Steps.wp_add fun s₂ o₂ => Steps.wp_li (by decide) fun s₃ o₃ =>
    WP.block_nil ?_)
  have k₃ := (o₁.keepH.trans o₂.keepH).trans o₃.keepH
  refine wp_loop_nz (HPInv s₀) (N := pk s₀) (by omega_arith) (fun i hi s hP => poly_ok hp hi hP)
    (fun s hP => ⟨hP.y.trans (hintBitPack_hpS _ _ _).symm, hP.frame⟩)
    ⟨by rw [k₃.gpr (by decide), hz.a0]; exact (add0 _).symm, by rw [k₃.gpr (by decide), hz.a3],
      by rw [o₃.other _ (by decide), o₂.other _ (by decide), o₁.gpr, add0, hz.a1, Nat.sub_zero],
      by rw [o₃.other _ (by decide), o₂.gpr, o₁.other _ (by decide), o₁.other _ (by decide), hz.a3, hz.a2,
        Nat.add_zero],
      by rw [o₃.gpr]; rfl, by rw [k₃.2.1, hz.rd], by rw [k₃.2.2, hz.wr],
      by rw [o₃.mem, o₂.mem, o₁.mem]; exact hz.frame, ?_⟩
  rw [o₃.mem, o₂.mem, o₁.mem]
  show _ = (Array.replicate (pω s₀ + pk s₀) (0 : Byte)).toList
  rw [Array.toList_replicate, hsum]
  exact bytesAt_eq (by simp) fun t ht => by rw [hz.zero t ht]; simp

/-! ## The function -/

/-- The registers `hintBitPack` writes. -/
abbrev hbpRegs : List Reg := [.t0, .a0, .a1, .a2, .a5, .a6, .a7, .t1, .t2]

theorem correct {s₀ : State} (hp : PPre s₀) :
    WP isa Impl.MlDsa.RISCV64.Pack.hintBitPack s₀ fun s' =>
      bytesAt s'.mem (pY s₀) (pLen s₀) = hintBitPack (pω s₀) (pk s₀) (pHint s₀) ∧ Keep hbpRegs s₀ s' := by
  refine WP.keep hbpRegs (WP.seq (WP.mono (zero_ok hp) fun s hz => WP.mono (main_ok hp hz) fun _ h => h.1))
    (by decide +kernel)

end VG.Proof.MlDsa.RISCV64.Pack.Hint
