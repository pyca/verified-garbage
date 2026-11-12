module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Divs
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.WordLoops
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Twos
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtCorr
import VerifiedGarbage.Proof.Bignum.ShiftStages
import VerifiedGarbage.Proof.Bignum.LongDivision
import VerifiedGarbage.Proof.Rsa.X86_64.WordInit
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: the square root's normalization

`normX` (wide, `W = 2 h + 4`): `X` reduced to its low `2 h` words, `1` in
place of zero, then shifted left by whole words and by an even number of
bits until its top word is at least `2^62`; the shift `64 K + z` with `K`
in `sK2` and `z` in `sC`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-! ## A stage -/

/-- `testX`'s setup: the base of `X`'s top `c` of `2 h` words, `rbp := 0`, `r12 := c`. -/
theorem testXHd_ok {s : State} {B : Addr} {Z W h : Nat} (hw : Ws s B Z W) (hwh : W = 2 * h + 4) {c : Nat}
    (hc : c ≤ 2 * h) (hc128 : c ≤ 128) :
    WP isa (.block (ws ++ base sqZ .rbx ++ ([.mov .rax (.reg .r12), .alu .sub .rax (.imm (BitVec.ofNat 32 (c + 4))),
      .shift .shl .rax 3, .alu .add .rbx (.reg .rax), .mov32 .rbp (.imm 0),
      .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr))) s
      fun t => t.gpr .rbx = off B (slot W sqZ + 8 * (2 * h - c)) ∧ t.gpr .rbp = 0 ∧ t.gpr .r12 = BitVec.ofNat 64 c ∧
        t.mem = s.mem ∧ Keep [.r12, .r9, .rbx, .rbp, .rax] s t := by
  have hw2 := hw.w2
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok sqZ (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans hw.rdi) h9) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_
  refine WP.mono (WP.keep [.r12, .rbx, .rbp, .rax] (Q := fun t => t.gpr .rbx = off B (slot W sqZ + 8 * (2 * h - c)) ∧
      t.gpr .rbp = 0 ∧ t.gpr .r12 = BitVec.ofNat 64 c ∧ t.mem = s₂.mem) (by
    have shv : (1 ≤ 3 ∧ 3 ≤ 63) = True := eq_true ⟨by decide, by decide⟩
    xrun [(k₂.gpr (by decide) : s₂.gpr .r12 = _), h12, sx_ofNat (show c + 4 < 2 ^ 31 by omega_arith), hbx, shv,
      setW32 (show c < 2 ^ 32 by omega_arith), ofNat_sub64 (show c + 4 ≤ W by omega_arith) (by omega_arith),
      show W - (c + 4) = 2 * h - c by omega_arith, ofNat_shl3 (show 8 * (2 * h - c) < 2 ^ 64 by omega_arith), off_addN]
    done) rfl) fun t ⟨⟨a1, a2, a3, m₃⟩, k₃⟩ => ?_
  exact ⟨a1, a2, a3, by rw [m₃, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- `testX c`: `sB2 := ` the mask of `X`'s top `c` of `2 h` words not all zero. -/
theorem testX_ok {s : State} {B : Addr} {Z W h : Nat} (hw : Ws s B Z W) (hwh : W = 2 * h + 4) {c : Nat}
    (hc1 : 1 ≤ c) (hc : c ≤ 2 * h) (hc128 : c ≤ 128) :
    WP isa (seqs (testX c)) s fun t =>
      t.mem = s.mem.writeW (off B (8 * sB2)) (mask (!decide (wv s.mem B (slot W sqZ + 8 * (2 * h - c)) c = 0))) ∧
      Keep [.r12, .r9, .rbx, .rbp, .rax, .r14] s t := by
  have hn := hw.scr.nowrap
  have sj := hw.sl (j := sqZ) (by decide)
  have hw2 := hw.w2
  simp only [testX, seqs]
  refine WP.seq (WP.seq (WP.mono (testXHd_ok hw hwh hc hc128) fun s₁ ⟨hbx, hbp, h12, m₁, k₁⟩ => ?_))
  have hs := hw.scr.congr k₁.2.2
  have h₁ : Ws s₁ B Z W := hw.congrP (P := fun _ => False) (fun _ _ => by rw [m₁]) (fun _ f => f.elim) k₁ (by simp)
  refine WP.mono (or1_ok hs hbx h12 hc1 (by omega_arith) (by simp only [sqZ] at sj ⊢; omega_arith))
    fun s₂ ⟨hz, m₂, k₂⟩ => ?_
  refine WP.mono (keepOf_ok (h₁.congrP (P := fun _ => False) (fun _ _ => by rw [m₂]) (fun _ f => f.elim) k₂ (by simp))
    (z := wv s.mem B (slot W sqZ + 8 * (2 * h - c)) c = 0) (by rw [hz, hbp, m₁]; simp)) fun t ⟨m₃, k₃⟩ => ?_
  exact ⟨by rw [m₃, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- A stage's guard: `CF` of `2 h < c + 1`. -/
theorem stageXHd_ok {s : State} {B : Addr} {Z W h : Nat} (hw : Ws s B Z W) (hwh : W = 2 * h + 4) {c : Nat}
    (hc : c ≤ 128) :
    WP isa (.block (ws ++ ([.alu .cmp .r12 (.imm (BitVec.ofNat 32 (c + 5)))] : List Instr))) s fun t =>
      (t.cf = some (decide (2 * h < c + 1)) ∧ t.mem = s.mem) ∧ Keep [.r12, .r9] s t := by
  have hw2 := hw.w2
  rw [WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.cf = some (decide (2 * h < c + 1)) ∧ t.mem = s₁.mem) (by
    xrun [h12, sx_ofNat (show c + 5 < 2 ^ 31 by omega_arith)]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show W < 2 ^ 64 by omega_arith),
      Nat.mod_eq_of_lt (show c + 5 < 2 ^ 64 by omega_arith)]
    exact decide_eq_decide.mpr (by omega_arith)) rfl)
    fun t ⟨⟨hcf, m₂⟩, k₂⟩ => ⟨⟨hcf, by rw [m₂, m₁]⟩, (k₁.trans k₂).mono (by simp)⟩

/-- `addK c`: `K := K + c` unless `keep`. -/
theorem addK_ok {s : State} {B : Addr} {Z W : Nat} (hw : Ws s B Z W) {c K : Nat} (hc : c ≤ 128) {keep : Bool}
    (hk : word s.mem B (8 * sB2) = mask keep) (hK : word s.mem B (8 * sK2) = BitVec.ofNat 64 K) :
    WP isa (.block (addK c)) s fun t =>
      t.mem = s.mem.writeW (off B (8 * sK2)) (BitVec.ofNat 64 (if keep then K else K + c)) ∧ Keep [.rax] s t := by
  have h256 := hw.h256
  have hn := hw.scr.nowrap
  refine WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off B (8 * sK2))
    (BitVec.ofNat 64 (if keep then K else K + c))) ?_ rfl
  unfold addK
  xrun [State.ea, hdr, hw.rdi, hdrOff, hw.scr.ld (d := 8 * sB2) (by unfold sB2 sFn; omega_arith),
    hw.scr.ld (d := 8 * sK2) (by unfold sK2 sFn; omega_arith), hw.scr.st (d := 8 * sK2) (by unfold sK2 sFn; omega_arith),
    hk, hK, sx_ofNat (show c < 2 ^ 31 by omega_arith)]
  rw [sx_m1, mask_xor1]
  congr 1
  apply BitVec.eq_of_toNat_eq
  cases keep
  · rw [show mask (!false) = BitVec.allOnes 64 from rfl, BitVec.allOnes_and]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Bool.false_eq_true, ↓reduceIte]
    omega_arith
  · rw [show mask (!true) = 0#64 from rfl, BitVec.zero_and, BitVec.zero_add]
    simp

/-- What `normX`'s stages change: the arrays `sqT` and `sqZ`, `sB2` and `sK2`. -/
def nxRs (W : Nat) : List (Nat × Nat) := [(slot W sqT, 16 * (W + 2)), (8 * sB2, 8), (8 * sK2, 8)]

theorem nxR_trans {B : Addr} {W : Nat} {a b c : State} (h₁ : Frm B (nxRs W) a.mem b.mem ∧ Keep mmRegs a b)
    (h₂ : Frm B (nxRs W) b.mem c.mem ∧ Keep mmRegs b c) : Frm B (nxRs W) a.mem c.mem ∧ Keep mmRegs a c :=
  ⟨h₁.1.trans h₂.1, (h₁.2.trans h₂.2).mono (by simp [mmRegs])⟩

/-- A stage of `c` words of `X`'s leading zeros in its low `2 h` words: where
`c + 1 ≤ 2 h` and its top `c` words are zero, `X` shifts left by `64 c` bits
and `K` grows by `c`. -/
theorem stageX_ok {s : State} {B : Addr} {Z W h : Nat} (hw : Ws s B Z W) (hwh : W = 2 * h + 4) {X K : Nat}
    (hX : wv s.mem B (slot W sqZ) W = X) (hK : word s.mem B (8 * sK2) = BitVec.ofNat 64 K) {c : Nat} (hc : 1 ≤ c)
    (hc128 : c ≤ 128) :
    WP isa (stageX c) s fun t =>
      wv t.mem B (slot W sqZ) W =
        (if c + 1 ≤ 2 * h ∧ X / 2 ^ (64 * (2 * h - c)) % 2 ^ (64 * c) = 0 then X * 2 ^ (64 * c) % 2 ^ (64 * W) else X) ∧
      word t.mem B (8 * sK2) =
        BitVec.ofNat 64 (if c + 1 ≤ 2 * h ∧ X / 2 ^ (64 * (2 * h - c)) % 2 ^ (64 * c) = 0 then K + c else K) ∧
      Frm B (nxRs W) s.mem t.mem ∧ Keep mmRegs s t ∧ Ws t B Z W := by
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  rw [slotE] at hZ
  have hw2 := hw.w2
  have slZ : slot W sqZ = 256 + 7 * (8 * (W + 2)) := rfl
  have slT : slot W sqT = 256 + 6 * (8 * (W + 2)) := rfl
  have hsb : 8 * sB2 = 216 := rfl
  have hsk : 8 * sK2 = 248 := rfl
  unfold stageX
  refine WP.seq (WP.mono (stageXHd_ok hw hwh hc128) fun s₁ ⟨⟨hcf, m₁⟩, k₁⟩ => ?_)
  have h₁ : Ws s₁ B Z W := hw.congrP (P := fun _ => False) (fun _ _ => by rw [m₁]) (fun _ f => f.elim) k₁ (by simp)
  refine WP.ite (decide (2 * h < c + 1)) (by simp only [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · have hg : ¬ (c + 1 ≤ 2 * h) := by simp only [decide_eq_true_eq] at hb; omega_arith
    refine WP.block_nil_iff.mpr ⟨?_, ?_, ?_, k₁.mono (by simp [mmRegs]), h₁⟩
    · simp only [hg, false_and, ↓reduceIte]; rw [m₁, hX]
    · simp only [hg, false_and, ↓reduceIte]; rw [m₁, hK]
    · rw [m₁]; exact Frm.refl _ _ _
  · have hg : c + 1 ≤ 2 * h := by simp only [decide_eq_false_iff_not] at hb; omega_arith
    have hz : wv s₁.mem B (slot W sqZ + 8 * (2 * h - c)) c = X / 2 ^ (64 * (2 * h - c)) % 2 ^ (64 * c) := by
      rw [m₁, ← hX, wv_div_pow _ _ _ (show 2 * h - c ≤ W by omega_arith),
        wv_mod_low _ _ _ (show c ≤ W - (2 * h - c) by omega_arith)]
    show WP isa (seqs (testX c ++ ((shlWords false sqZ c sqT ++ [selK false sqZ sqT]) ++ [.block (addK c)]))) s₁ _
    refine wp_seqs_append (by simp [testX]) (by simp [shlWords]) (WP.mono (testX_ok h₁ hwh hc (by omega_arith)
      hc128) fun s₂ ⟨m₂, k₂⟩ => ?_)
    rw [hz] at m₂
    have h₂ := h₁.congrW m₂ (by unfold DOk; simp only [sB2, sFn]; omega_arith) (by decide) k₂ (by simp)
    have o₂ : Outside B (8 * sB2) 8 s₁.mem s₂.mem := by rw [m₂]; exact writeW_outside _ _ _ (by omega_arith)
    have hk₂ := (show word s₂.mem B (8 * sB2) = _ by rw [m₂, word_writeW_self])
    have X₂ : wv s₂.mem B (slot W sqZ) W = X := by rw [o₂.wv (by omega_arith) (by omega_arith), m₁, hX]
    refine wp_seqs_append (by simp [shlWords]) (by simp) (WP.mono (selShlD_ok h₂ (j := sqZ) (t := sqT) (by decide)
      (by decide) (by decide) hc (by omega_arith) hc128 hk₂) fun s₃ ⟨v3, f3, k3, h₃⟩ => ?_)
    rw [if_not_decide, X₂] at v3
    have hk₃ : word s₃.mem B (8 * sB2) = mask (!decide (X / 2 ^ (64 * (2 * h - c)) % 2 ^ (64 * c) = 0)) := by
      rw [f3.word_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith), hk₂]
    have K₃ : word s₃.mem B (8 * sK2) = BitVec.ofNat 64 K := by
      rw [f3.word_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith),
        o₂.word (by omega_arith) (by omega_arith), m₁, hK]
    simp only [seqs]
    refine WP.mono (addK_ok h₃ hc128 hk₃ K₃) fun t ⟨m₄, k₄⟩ => ?_
    have o₄ : Outside B (8 * sK2) 8 s₃.mem t.mem := by rw [m₄]; exact writeW_outside _ _ _ (by omega_arith)
    refine ⟨?_, ?_, ?_, (((k₁.trans k₂).trans k3).trans k₄).mono (by simp [mmRegs]),
      h₃.congrW m₄ (by unfold DOk; simp only [sK2, sFn]; omega_arith) (by decide) k₄ (by simp)⟩
    · rw [o₄.wv (by omega_arith) (by omega_arith), v3]
      by_cases hq : X / 2 ^ (64 * (2 * h - c)) % 2 ^ (64 * c) = 0 <;> simp [hq, hg]
    · rw [m₄, word_writeW_self]
      by_cases hq : X / 2 ^ (64 * (2 * h - c)) % 2 ^ (64 * c) = 0 <;> simp [hq, hg]
    · rw [← m₁]
      refine (((Frm.of_outside o₂ (by simp [nxRs])).trans (WordDivide.cover f3 ?_)).trans
        (Frm.of_outside o₄ (by simp [nxRs])))
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨⟨(slot W sqT, 16 * (W + 2)), by simp [nxRs], by omega_arith, by omega_arith⟩,
        ⟨(slot W sqT, 16 * (W + 2)), by simp [nxRs], by omega_arith, by omega_arith⟩⟩

/-- The word stages of `X`'s leading zeros in its low `H` words, in turn
(modulo `2^(64 W)`), with the count `K` of words shifted. -/
def xnF (H W X K : Nat) : List Nat → Nat × Nat
  | [] => (X, K)
  | c :: cs => if c + 1 ≤ H ∧ X / 2 ^ (64 * (H - c)) % 2 ^ (64 * c) = 0
      then xnF H W (X * 2 ^ (64 * c) % 2 ^ (64 * W)) (K + c) cs
      else xnF H W X K cs

theorem xnStages_ok {B : Addr} {Z W h : Nat} (hwh : W = 2 * h + 4) : ∀ (cs : List Nat), (∀ c ∈ cs, 1 ≤ c ∧ c ≤ 128) →
    cs ≠ [] → ∀ {s : State} {X K : Nat}, Ws s B Z W → wv s.mem B (slot W sqZ) W = X →
    word s.mem B (8 * sK2) = BitVec.ofNat 64 K →
    WP isa (seqs (cs.map stageX)) s fun t =>
      wv t.mem B (slot W sqZ) W = (xnF (2 * h) W X K cs).1 ∧
      word t.mem B (8 * sK2) = BitVec.ofNat 64 (xnF (2 * h) W X K cs).2 ∧
      Frm B (nxRs W) s.mem t.mem ∧ Keep mmRegs s t ∧ Ws t B Z W
  | [], _, h0, _, _, _, _, _, _ => absurd rfl h0
  | [c], hc, _, s, X, K, hw, hX, hK => by
    have hc' := hc c (by simp)
    simp only [List.map_cons, List.map_nil, seqs]
    refine WP.mono (stageX_ok hw hwh hX hK hc'.1 hc'.2) fun t ⟨v, k2, f, k, ht⟩ => ⟨?_, ?_, f, k, ht⟩ <;>
    · by_cases hg : c + 1 ≤ 2 * h ∧ X / 2 ^ (64 * (2 * h - c)) % 2 ^ (64 * c) = 0 <;>
        simp only [xnF, hg, ↓reduceIte] at v k2 ⊢ <;> first | exact v | exact k2
  | c :: c' :: cs, hc, _, s, X, K, hw, hX, hK => by
    have hc' := hc c (by simp)
    rw [List.map_cons, show seqs (stageX c :: (c' :: cs).map stageX) = .seq (stageX c) (seqs ((c' :: cs).map stageX))
      from rfl]
    refine WP.seq (WP.mono (stageX_ok hw hwh hX hK hc'.1 hc'.2) fun t ⟨v, k2, f, k, ht⟩ => ?_)
    refine WP.mono (xnStages_ok hwh (c' :: cs) (fun x hx => hc x (by simp [hx])) (by simp) ht v k2)
      fun u ⟨u1, u2, f', k', hu⟩ => ⟨?_, ?_, (nxR_trans ⟨f, k⟩ ⟨f', k'⟩).1, (nxR_trans ⟨f, k⟩ ⟨f', k'⟩).2, hu⟩ <;>
    · by_cases hg : c + 1 ≤ 2 * h ∧ X / 2 ^ (64 * (2 * h - c)) % 2 ^ (64 * c) = 0 <;>
        simp only [xnF, hg, ↓reduceIte] at v k2 u1 u2 ⊢ <;> first | exact u1 | exact u2

open VG.Proof.Bignum.ShiftStages in
/-- The word stages take `X`'s leading zero words `C = (64 H - 1 - log₂ X) / 64`
in its `H` words: `X 2^(64 C)` and `K = C`, exactly. -/
theorem xnF_greedy {H W X : Nat} (hHW : H + 4 ≤ W) (hX1 : 1 ≤ X) (hXh : X < 2 ^ (64 * H)) :
    ∀ (cs : List Nat), (∀ c ∈ cs, 1 ≤ c) → ∀ (a : Nat), a ≤ (64 * H - 1 - Nat.log2 X) / 64 →
    xnF H W (X * 2 ^ (64 * a)) a cs =
      (X * 2 ^ (64 * greedy ((64 * H - 1 - Nat.log2 X) / 64) cs a), greedy ((64 * H - 1 - Nat.log2 X) / 64) cs a)
  | [], _, a, _ => rfl
  | c :: cs, hc, a, ha => by
    have hX0 : X ≠ 0 := by omega_arith
    have hlog : Nat.log2 X < 64 * H := (lt_pow_iff hX0 0 (64 * H)).mp (by simpa using hXh)
    generalize hC : (64 * H - 1 - Nat.log2 X) / 64 = C at ha ⊢
    have fits : ∀ k, X * 2 ^ (64 * k) < 2 ^ (64 * H) ↔ k ≤ C := fun k => by
      rw [lt_pow_iff hX0]; omega_arith
    have hXa : X * 2 ^ (64 * a) < 2 ^ (64 * H) := (fits a).mpr ha
    have hP : 2 ^ (64 * H) ≤ 2 ^ (64 * W) := Nat.pow_le_pow_right (by decide) (by omega_arith)
    have key : (c + 1 ≤ H ∧ X * 2 ^ (64 * a) / 2 ^ (64 * (H - c)) % 2 ^ (64 * c) = 0) ↔ a + c ≤ C := by
      by_cases hch : c + 1 ≤ H
      · have hq : X * 2 ^ (64 * a) / 2 ^ (64 * (H - c)) < 2 ^ (64 * c) := by
          rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
            show 64 * c + 64 * (H - c) = 64 * H by omega_arith]; exact hXa
        rw [Nat.mod_eq_of_lt hq, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _), ← fits,
          show 64 * (a + c) = 64 * a + 64 * c by omega_arith, Nat.pow_add, ← Nat.mul_assoc]
        constructor
        · intro ⟨_, h2⟩
          calc X * 2 ^ (64 * a) * 2 ^ (64 * c) < 2 ^ (64 * (H - c)) * 2 ^ (64 * c) :=
                Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos _)
            _ = 2 ^ (64 * H) := by rw [← Nat.pow_add]; congr 1; omega_arith
        · intro h2
          refine ⟨hch, ?_⟩
          have : 2 ^ (64 * H) = 2 ^ (64 * (H - c)) * 2 ^ (64 * c) := by rw [← Nat.pow_add]; congr 1; omega_arith
          rw [this] at h2
          exact Nat.lt_of_mul_lt_mul_right h2
      · have : ¬ (a + c ≤ C) := by
          intro hl
          have := (fits (a + c)).mpr hl
          have hCh : C ≤ H - 1 := by rw [← hC]; omega_arith
          omega_arith
        simp only [hch, false_and, this]
    rw [xnF, greedy_cons]
    by_cases hl : a + c ≤ C
    · simp only [key.mpr hl, ↓reduceIte, hl]
      have hXc : X * 2 ^ (64 * a) * 2 ^ (64 * c) = X * 2 ^ (64 * (a + c)) := by
        rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega_arith
      rw [hXc, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ((fits _).mpr hl) hP)]
      rw [← hC]
      exact hC ▸ xnF_greedy hHW hX1 hXh cs (fun x hx => hc x (by simp [hx])) (a + c) (hC ▸ hl)
    · simp only [mt key.mp hl, ↓reduceIte, hl]
      rw [← hC]
      exact xnF_greedy hHW hX1 hXh cs (fun x hx => hc x (by simp [hx])) a (hC ▸ ha)

/-! ## The setup -/

/-- `topX`: `X`'s words `2 h` to `2 h + 3` cleared. -/
theorem topX_ok {s : State} {B : Addr} {Z W h : Nat} (hw : Ws s B Z W) (hwh : W = 2 * h + 4) :
    WP isa (.block topX) s fun t =>
      t.mem = ((((s.mem.writeW (off B (slot W sqZ + 8 * (2 * h))) (0 : BitVec 64)).writeW (off B (slot W sqZ + 8 * (2 * h + 1))) (0 : BitVec 64)).writeW
        (off B (slot W sqZ + 8 * (2 * h + 2))) (0 : BitVec 64)).writeW (off B (slot W sqZ + 8 * (2 * h + 3))) (0 : BitVec 64)) ∧
      Keep [.r12, .r9, .rbx, .rax] s t := by
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  rw [slotE] at hZ
  have hw2 := hw.w2
  have slZ : slot W sqZ = 256 + 7 * (8 * (W + 2)) := rfl
  unfold topX
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok sqZ (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans hw.rdi) h9) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_
  have hs₂ := hw.scr.congr (k₁.trans k₂).2.2
  have h12' : s₂.gpr .r12 = BitVec.ofNat 64 W := (k₂.gpr (by decide)).trans h12
  have a0 := addrI (d := -32) (k := 2 * h) hbx h12' (by omega)
  have a1 := addrI (d := -24) (k := 2 * h + 1) hbx h12' (by omega)
  have a2 := addrI (d := -16) (k := 2 * h + 2) hbx h12' (by omega)
  have a3 := addrI (d := -8) (k := 2 * h + 3) hbx h12' (by omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = ((((s₂.mem.writeW (off B (slot W sqZ + 8 * (2 * h))) (0 : BitVec 64)).writeW
      (off B (slot W sqZ + 8 * (2 * h + 1))) (0 : BitVec 64)).writeW (off B (slot W sqZ + 8 * (2 * h + 2))) (0 : BitVec 64)).writeW
        (off B (slot W sqZ + 8 * (2 * h + 3))) (0 : BitVec 64))) (by
    xrun [State.ea, ix, a0, a1, a2, a3, hs₂.st (d := slot W sqZ + 8 * (2 * h)) (by omega),
      hs₂.st (d := slot W sqZ + 8 * (2 * h + 1)) (by omega), hs₂.st (d := slot W sqZ + 8 * (2 * h + 2)) (by omega),
      hs₂.st (d := slot W sqZ + 8 * (2 * h + 3)) (by omega)]
    rfl) rfl) fun t ⟨m₃, k₃⟩ => ?_
  exact ⟨by rw [m₃, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- The zero test's setup: `rbx := [sqZ]`, `rbp := 0`, `r12 := W`. -/
theorem orXHd_ok {s : State} {B : Addr} {Z W : Nat} (hw : Ws s B Z W) :
    WP isa (.block (ws ++ base sqZ .rbx ++ ([.mov32 .rbp (.imm 0)] : List Instr))) s fun t =>
      t.gpr .rbx = off B (slot W sqZ) ∧ t.gpr .rbp = 0 ∧ t.gpr .r12 = BitVec.ofNat 64 W ∧ t.mem = s.mem ∧
        Keep [.r12, .r9, .rbx, .rbp] s t := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok sqZ (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans hw.rdi) h9) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = 0 ∧ t.mem = s₂.mem) (by xrun) rfl)
    fun t ⟨⟨a1, m₃⟩, k₃⟩ => ?_
  exact ⟨(k₃.gpr (by decide)).trans hbx, a1, (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12),
    by rw [m₃, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- `zeroX`: `sZ := [z]` (`z ↔ rbp = 0`), `X[0] := X[0] | z`, `K := 0`. -/
theorem zeroX_ok {s : State} {B : Addr} {Z W : Nat} (hw : Ws s B Z W) {z : Prop} [Decidable z]
    (hz : s.gpr .rbp = 0 ↔ z) :
    WP isa (.block zeroX) s fun t =>
      t.mem = ((s.mem.writeW (off B (8 * sZ)) (mask (decide z))).writeW (off B (slot W sqZ))
        (word s.mem B (slot W sqZ) ||| (mask (decide z) &&& 1))).writeW (off B (8 * sK2)) (0 : BitVec 64) ∧
      Keep [.r12, .r9, .rbx, .rbp, .rax] s t := by
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  have hZ := hw.hZ
  rw [slotE] at hZ
  have slZ : slot W sqZ = 256 + 7 * (8 * (W + 2)) := rfl
  have e : decide (s.gpr .rbp = 0) = decide z := by
    by_cases hz' : z
    · rw [decide_eq_true hz', decide_eq_true (hz.mpr hz')]
    · rw [decide_eq_false hz', decide_eq_false (fun h => hz' (hz.mp h))]
  unfold zeroX
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok sqZ (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans hw.rdi) h9) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := hw.scr.congr k12.2.2
  have hbp : s₂.gpr .rbp = s.gpr .rbp := k12.gpr (by decide)
  refine WP.mono (WP.keep [.rbp, .rax] (Q := fun t => t.mem = ((s.mem.writeW (off B (8 * sZ)) (mask (decide z))).writeW
      (off B (slot W sqZ)) (word s.mem B (slot W sqZ) ||| (mask (decide z) &&& 1))).writeW (off B (8 * sK2))
        (0 : BitVec 64)) (by
    have hdi : s₂.gpr .rdi = B := (k12.gpr (by decide)).trans hw.rdi
    have a0 : s₂.gpr .rbx + BitVec.ofInt 64 0 = off B (slot W sqZ) := by
      rw [hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
    xrun [State.ea, hdr, at0, hdi, hdrOff, hbp, a0,
      hs₂.st (d := 8 * sZ) (by unfold sZ sFn; omega_arith), hs₂.st (d := 8 * sK2) (by unfold sK2 sFn; omega_arith),
      hs₂.st (d := slot W sqZ) (by omega_arith), hs₂.ld (d := slot W sqZ) (by omega_arith), m₂, m₁]
    rw [show ∀ v, (s.mem.writeW (off B (8 * sZ)) v).readW (off B (slot W sqZ)) 64 = word s.mem B (slot W sqZ) from
      fun v => word_wW v (by unfold sZ sFn; omega_arith) (by unfold sZ sFn; omega_arith) (by omega_arith),
      show BitVec.setWidth 64 (0 : BitVec 32) = 0 from rfl, decide_lt_one', e,
      show (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide z))) = mask (decide z) from rfl, BitVec.or_comm]
    ) rfl) fun t ⟨m₃, k₃⟩ => ⟨m₃, (k12.trans k₃).mono (by simp)⟩

theorem and_m2 : ∀ n < 64, BitVec.ofNat 64 n &&& BitVec.signExtend 64 (BitVec.ofInt 32 (-2)) =
    BitVec.ofNat 64 (n / 2 * 2) := by decide

/-- `clzX`: `sC := ` the leading zeros of `X`'s word `2 h - 1` (`W - 5`), made even. -/
theorem clzX_ok {s : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W) (hW : 6 ≤ W) :
    WP isa (.block clzX) s fun t =>
      t.mem = s.mem.writeW (off B (8 * sC))
        (BitVec.ofNat 64 ((63 - Nat.log2 (word s.mem B (slot W sqZ + 8 * (W - 5))).toNat) / 2 * 2)) ∧
      Keep [.r12, .r9, .rbx, .rcx, .r8, .rdx, .r11] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl (j := sqZ) (by decide)
  have hw2 := h.w2
  unfold clzX
  rw [show ws ++ base sqZ .rbx ++ ([.mov .rdx (.mem (ix .rbx .r12 (-40))), .mov32 .r11 (.imm 0)] : List Instr) ++
      ([32, 16, 8, 4, 2, 1].map clzStage).flatten ++
      ([.alu .and .r11 (.imm (BitVec.ofInt 32 (-2))), .store (hdr sC) .r11] : List Instr) =
    ws ++ (base sqZ .rbx ++ (([.mov .rdx (.mem (ix .rbx .r12 (-40))), .mov32 .r11 (.imm 0)] : List Instr) ++
      (([32, 16, 8, 4, 2, 1].map clzStage).flatten ++
        ([.alu .and .r11 (.imm (BitVec.ofInt 32 (-2))), .store (hdr sC) .r11] : List Instr)))) by
    simp only [List.append_assoc], WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok sqZ (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).2.2
  have a5 := addrI (d := -40) (k := W - 5) hbx ((k₂.gpr (by decide)).trans h12) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx, .r11] (Q := fun t => t.gpr .rdx = word s.mem B (slot W sqZ + 8 * (W - 5)) ∧
      t.gpr .r11 = BitVec.ofNat 64 0 ∧ t.mem = s₂.mem) (by
    xrun [State.ea, ix, a5, hs₂.ld (d := slot W sqZ + 8 * (W - 5)) (by simp only [sqZ] at sj ⊢; omega_arith), m₂, m₁]
    done) rfl) fun s₃ ⟨⟨hdx, h11, m₃⟩, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (clzStages_ok _ (by decide) hdx h11) fun s₄ ⟨⟨_, h11', m₄⟩, k₄⟩ => ?_
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have hl : 63 - Nat.log2 (word s.mem B (slot W sqZ + 8 * (W - 5))).toNat < 64 := by omega
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.mem = s.mem.writeW (off B (8 * sC))
      (BitVec.ofNat 64 ((63 - Nat.log2 (word s.mem B (slot W sqZ + 8 * (W - 5))).toNat) / 2 * 2))) (by
    have hs₄ := h.scr.congr k14.2.2
    have ew : BitVec.ofNat 64 (word s.mem B (slot W sqZ + 8 * (W - 5))).toNat =
        word s.mem B (slot W sqZ + 8 * (W - 5)) := by simp
    rw [← ew, clzF_val (BitVec.isLt _)] at h11'
    xrun [State.ea, hdr, (k14.gpr (by decide) : s₄.gpr .rdi = _), h.rdi, hdrOff, h11', and_m2 _ hl,
      hs₄.st (d := 8 * sC) (by unfold sC sFn; have := h.h256; omega_arith), m₄, m₃, m₂, m₁]) rfl)
    fun t ⟨m₅, k₅⟩ => ⟨m₅, (k14.trans k₅).mono (by simp)⟩

/-! ## The normalization -/

open VG.Proof.Bignum.ShiftStages in
/-- The greedy word shift `C` of `0 < X < 2^(64 H)`: `X 2^(64 C)` has its top
word (of `H`) nonzero. -/
theorem fit_bounds {X H : Nat} (hX0 : X ≠ 0) (hX : X < 2 ^ (64 * H)) :
    2 ^ (64 * (H - 1)) ≤ X * 2 ^ (64 * ((64 * H - 1 - Nat.log2 X) / 64)) ∧
      X * 2 ^ (64 * ((64 * H - 1 - Nat.log2 X) / 64)) < 2 ^ (64 * H) ∧ (64 * H - 1 - Nat.log2 X) / 64 + 1 ≤ H := by
  have hlog : Nat.log2 X < 64 * H := (lt_pow_iff hX0 0 (64 * H)).mp (by simpa using hX)
  generalize hC : (64 * H - 1 - Nat.log2 X) / 64 = C
  have hCh : C + 1 ≤ H := by omega_arith
  have fits : ∀ k, X * 2 ^ (64 * k) < 2 ^ (64 * H) ↔ k ≤ C := fun k => by
    rw [lt_pow_iff hX0, ← hC]; omega_arith
  refine ⟨?_, (fits C).mpr (Nat.le_refl _), hCh⟩
  have := mt (fits (C + 1)).mp (by omega_arith)
  rw [Nat.not_lt, show 64 * (C + 1) = 64 * C + 64 by omega_arith, Nat.pow_add, ← Nat.mul_assoc,
    show 2 ^ (64 * H) = 2 ^ (64 * (H - 1)) * 2 ^ 64 by rw [← Nat.pow_add]; congr 1; omega_arith] at this
  exact Nat.le_of_mul_le_mul_right this (Nat.two_pow_pos _)

/-- The even bit shift of `Y` (top word of `H` nonzero): its top word at least `2^62`. -/
theorem norm_even {Y H : Nat} (hH : 1 ≤ H) (hlo : 2 ^ (64 * (H - 1)) ≤ Y) (hhi : Y < 2 ^ (64 * H)) :
    2 ^ 62 * 2 ^ (64 * (H - 1)) ≤ Y * 2 ^ ((63 - Nat.log2 (Y / 2 ^ (64 * (H - 1)))) / 2 * 2) ∧
      Y * 2 ^ ((63 - Nat.log2 (Y / 2 ^ (64 * (H - 1)))) / 2 * 2) < 2 ^ (64 * H) := by
  have hP : 2 ^ (64 * (H - 1)) * 2 ^ 64 = 2 ^ (64 * H) := by rw [← Nat.pow_add]; congr 1; omega_arith
  have nb := LongDivision.norm_bounds hlo (hP ▸ hhi)
  generalize 63 - Nat.log2 (Y / 2 ^ (64 * (H - 1))) = z at nb ⊢
  rcases Nat.mod_two_eq_zero_or_one z with hz | hz
  · rw [show z / 2 * 2 = z by omega_arith, ← hP]
    exact ⟨Nat.le_trans (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by decide)) nb.1, nb.2⟩
  · have e2 : Y * 2 ^ z = Y * 2 ^ (z / 2 * 2) * 2 := by
      rw [Nat.mul_assoc, ← Nat.pow_succ, show (z / 2 * 2).succ = z by omega_arith]
    rw [e2] at nb
    generalize Y * 2 ^ (z / 2 * 2) = V at nb ⊢
    rw [← hP]
    constructor
    · have : 2 ^ (64 * (H - 1)) * 2 ^ 63 = 2 ^ 62 * 2 ^ (64 * (H - 1)) * 2 := by
        rw [show (2 : Nat) ^ 63 = 2 ^ 62 * 2 from rfl]; grind
      omega_arith
    · omega_arith

/-- The normalized number: `X`'s low `2 h` words, or `1` if they are zero. -/
def Xn (X h : Nat) : Nat := if X % 2 ^ (64 * (2 * h)) = 0 then 1 else X % 2 ^ (64 * (2 * h))

theorem Xn_pos (X h : Nat) : 1 ≤ Xn X h := by
  unfold Xn; split <;> omega_arith

theorem Xn_lt {X h : Nat} (h1 : 1 ≤ h) : Xn X h < 2 ^ (64 * (2 * h)) := by
  unfold Xn
  have : 2 ≤ 2 ^ (64 * (2 * h)) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (64 * (2 * h)) := Nat.pow_le_pow_right (by decide) (by omega_arith)
  split
  · omega_arith
  · exact Nat.mod_lt _ (by omega_arith)

/-- What `normX` changes: the arrays `sqT` and `sqZ`, and the header's `sB2`,
`sZ`, `sC` and `sK2`. -/
def NxP (W y : Nat) : Prop :=
  (slot W sqT ≤ y ∧ y < slot W sqT + 16 * (W + 2)) ∨ (216 ≤ y ∧ y < 224) ∨ (232 ≤ y ∧ y < 256)

/-- `normX` (wide, `W = 2 h + 4`): `X`'s low `2 h` words (or `1` if zero) shifted
left by `64 C + z` bits (`z` even), with the top word at least `2^62`; `C` in
`sK2`, `z` in `sC`, and whether those words were zero in `sZ`. -/
theorem normX_ok {s : State} {B : Addr} {Z W h X : Nat} (hw : Ws s B Z W) (hwh : W = 2 * h + 4) (h1 : 1 ≤ h)
    (hh : h ≤ 128) (hX : wv s.mem B (slot W sqZ) W = X) :
    WP isa (seqs normX) s fun t => ∃ C z, z % 2 = 0 ∧ z < 64 ∧ C + 1 ≤ 2 * h ∧
      wv t.mem B (slot W sqZ) W = Xn X h * 2 ^ (64 * C) * 2 ^ z ∧
      2 ^ 62 * 2 ^ (64 * (2 * h - 1)) ≤ Xn X h * 2 ^ (64 * C) * 2 ^ z ∧
      Xn X h * 2 ^ (64 * C) * 2 ^ z < 2 ^ (64 * (2 * h)) ∧
      word t.mem B (8 * sK2) = BitVec.ofNat 64 C ∧ word t.mem B (8 * sC) = BitVec.ofNat 64 z ∧
      word t.mem B (8 * sZ) = mask (decide (X % 2 ^ (64 * (2 * h)) = 0)) ∧
      FrmP B (NxP W) s.mem t.mem ∧ Keep mmRegs s t ∧ Ws t B Z W := by
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  have hZ := hw.hZ
  rw [slotE] at hZ
  have hw2 := hw.w2
  have slZ : slot W sqZ = 256 + 7 * (8 * (W + 2)) := rfl
  have slT : slot W sqT = 256 + 6 * (8 * (W + 2)) := rfl
  have hsb : 8 * sB2 = 216 := rfl
  have hsk : 8 * sK2 = 248 := rfl
  have hsc : 8 * sC = 240 := rfl
  have hsz : 8 * sZ = 232 := rfl
  unfold normX
  refine wp_seqs_append (by simp) (by simp) ?_
  refine wp_seqs_append (by simp) (by simp [wordStages]) ?_
  -- `X mod 2^(64 · 2 h)`.
  refine WP.seq (WP.mono (topX_ok hw hwh) fun t₁ ⟨m₁, k₁⟩ => ?_)
  have FP₁ : FrmP B (fun y => slot W sqZ + 8 * (2 * h) ≤ y ∧ y < slot W sqZ + 8 * (2 * h + 4)) s.mem t₁.mem := by
    intro x hx
    rw [m₁, writeW_outside _ B _ (d := slot W sqZ + 8 * (2 * h + 3)) (by omega) x (by omega),
      writeW_outside _ B _ (d := slot W sqZ + 8 * (2 * h + 2)) (by omega) x (by omega),
      writeW_outside _ B _ (d := slot W sqZ + 8 * (2 * h + 1)) (by omega) x (by omega),
      writeW_outside _ B _ (d := slot W sqZ + 8 * (2 * h)) (by omega) x (by omega)]
  have h₁ := hw.congrP FP₁ (fun y hy => by unfold DOk; omega) k₁ (by decide)
  have top₁ : wv t₁.mem B (slot W sqZ + 8 * (2 * h)) 4 = 0 := by
    apply wv_zero
    intro k hk
    rw [m₁]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [show slot W sqZ + 8 * (2 * h) + 8 * 0 = slot W sqZ + 8 * (2 * h) by omega,
        word_wW (d := slot W sqZ + 8 * (2 * h + 3)) _ (by omega) (by omega) (by omega),
        word_wW (d := slot W sqZ + 8 * (2 * h + 2)) _ (by omega) (by omega) (by omega),
        word_wW (d := slot W sqZ + 8 * (2 * h + 1)) _ (by omega) (by omega) (by omega), word_writeW_self]
    · rw [show slot W sqZ + 8 * (2 * h) + 8 * 1 = slot W sqZ + 8 * (2 * h + 1) by omega,
        word_wW (d := slot W sqZ + 8 * (2 * h + 3)) _ (by omega) (by omega) (by omega),
        word_wW (d := slot W sqZ + 8 * (2 * h + 2)) _ (by omega) (by omega) (by omega), word_writeW_self]
    · rw [show slot W sqZ + 8 * (2 * h) + 8 * 2 = slot W sqZ + 8 * (2 * h + 2) by omega,
        word_wW (d := slot W sqZ + 8 * (2 * h + 3)) _ (by omega) (by omega) (by omega), word_writeW_self]
    · rw [show slot W sqZ + 8 * (2 * h) + 8 * 3 = slot W sqZ + 8 * (2 * h + 3) by omega, word_writeW_self]
  have X₁ : wv t₁.mem B (slot W sqZ) W = X % 2 ^ (64 * (2 * h)) := by
    have sp := wv_add t₁.mem B (slot W sqZ) (2 * h) 4
    rw [← hwh, top₁, Nat.mul_zero, Nat.add_zero,
      FP₁.wv_eq (d := slot W sqZ) (k := 2 * h) (fun y h1 h2 hy => by omega) (by omega)] at sp
    rw [sp, ← hX, wv_mod_low _ _ _ (show 2 * h ≤ W by omega)]
  -- The zero test.
  refine WP.seq (WP.seq (WP.mono (orXHd_ok h₁) fun s₂ ⟨hbx, hbp, h12, m₂, k₂⟩ => ?_))
  refine WP.mono (or1_ok (h₁.scr.congr k₂.2.2) hbx h12 (by omega) (by omega) (by omega))
    fun t₂ ⟨hz, m₂', k₂'⟩ => ?_
  have mm₂ : t₂.mem = t₁.mem := by rw [m₂', m₂]
  have hz' : t₂.gpr .rbp = 0 ↔ X % 2 ^ (64 * (2 * h)) = 0 := by rw [hz, hbp, m₂, X₁]; simp
  have h₂ : Ws t₂ B Z W :=
    h₁.congrP (P := fun _ => False) (fun _ _ => by rw [mm₂]) (fun _ f => f.elim) (k₂.trans k₂') (by simp)
  -- `sZ`, `X := X | z`, `K := 0`.
  refine WP.mono (zeroX_ok h₂ hz') fun t₃ ⟨m₃, k₃⟩ => ?_
  rw [mm₂] at m₃
  have hXn : Xn X h = if X % 2 ^ (64 * (2 * h)) = 0 then 1 else X % 2 ^ (64 * (2 * h)) := rfl
  have hXn1 := Xn_pos X h
  have hXnh := Xn_lt (X := X) h1
  generalize hX0 : X % 2 ^ (64 * (2 * h)) = X0 at X₁ m₃ hXn ⊢
  have FP₃ : FrmP B (fun y => (232 ≤ y ∧ y < 240) ∨ (slot W sqZ ≤ y ∧ y < slot W sqZ + 8) ∨ (248 ≤ y ∧ y < 256))
      t₁.mem t₃.mem := by
    intro x hx
    rw [m₃, writeW_outside _ B _ (d := 8 * sK2) (by omega) x (by omega),
      writeW_outside _ B _ (d := slot W sqZ) (by omega) x (by omega),
      writeW_outside _ B _ (d := 8 * sZ) (by omega) x (by omega)]
  have h₃ := h₂.congrP (by rw [mm₂]; exact FP₃) (fun y hy => by unfold DOk; omega) k₃ (by decide)
  have K₃ : word t₃.mem B (8 * sK2) = BitVec.ofNat 64 0 := by rw [m₃, word_writeW_self]; rfl
  have Z₃ : word t₃.mem B (8 * sZ) = mask (decide (X0 = 0)) := by
    rw [m₃, word_wW (d := 8 * sK2) _ (by omega) (by omega) (by omega),
      word_wW (d := slot W sqZ) _ (by omega) (by omega) (by omega), word_writeW_self]
  have X₃ : wv t₃.mem B (slot W sqZ) W = Xn X h := by
    have sp₁ := wv_add t₁.mem B (slot W sqZ) 1 (W - 1)
    have sp₃ := wv_add t₃.mem B (slot W sqZ) 1 (W - 1)
    rw [show 1 + (W - 1) = W by omega, wv_one', show 64 * 1 = 64 from rfl, show slot W sqZ + 8 * 1 = slot W sqZ + 8
      from rfl] at sp₁ sp₃
    have r₃ : wv t₃.mem B (slot W sqZ + 8) (W - 1) = wv t₁.mem B (slot W sqZ + 8) (W - 1) :=
      FP₃.wv_eq (fun y h1 h2 hy => by omega) (by omega)
    have w₃ : word t₃.mem B (slot W sqZ) = word t₁.mem B (slot W sqZ) ||| (mask (decide (X0 = 0)) &&& 1) := by
      rw [m₃, word_wW (d := 8 * sK2) _ (by omega) (by omega) (by omega), word_writeW_self]
    rw [sp₃, r₃, w₃, hXn]
    rw [X₁] at sp₁
    by_cases h0 : X0 = 0
    · have hw0 : word t₁.mem B (slot W sqZ) = 0 := by
        apply BitVec.eq_of_toNat_eq; rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega
      have hr0 : wv t₁.mem B (slot W sqZ + 8) (W - 1) = 0 := by
        have := Nat.two_pow_pos 64
        rcases Nat.eq_zero_or_pos (wv t₁.mem B (slot W sqZ + 8) (W - 1)) with e | e
        · exact e
        · have : 2 ^ 64 ≤ 2 ^ 64 * wv t₁.mem B (slot W sqZ + 8) (W - 1) := Nat.le_mul_of_pos_right _ e
          omega
      rw [hw0, hr0, decide_eq_true h0]; simp only [h0, ↓reduceIte]; rfl
    · rw [decide_eq_false h0, show mask false &&& 1 = 0#64 from rfl, BitVec.or_zero]; simp only [h0, ↓reduceIte]; exact sp₁.symm
  -- The word stages.
  refine WP.mono (xnStages_ok hwh (128 :: wordStages) (by decide) (by simp) h₃ X₃ K₃)
    fun t₄ ⟨x4, k4, f4, kk4, h₄⟩ => ?_
  obtain ⟨fl, fh, fC⟩ := fit_bounds (X := Xn X h) (H := 2 * h) (by omega) hXnh
  have g := xnF_greedy (H := 2 * h) (W := W) (by omega) hXn1 hXnh (128 :: wordStages) (by decide) 0 (Nat.zero_le _)
  generalize hC : (64 * (2 * h) - 1 - Nat.log2 (Xn X h)) / 64 = C at fl fh fC g
  rw [show 128 :: wordStages = VG.Proof.Bignum.ShiftStages.pows 7 by decide,
    VG.Proof.Bignum.ShiftStages.greedy_pows 7 C 0 (Nat.zero_le _) (by omega)] at g
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one] at g
  rw [show 128 :: wordStages = VG.Proof.Bignum.ShiftStages.pows 7 by decide, g] at x4 k4
  simp only at x4 k4
  -- The top word's leading zeros, even.
  refine WP.seq (WP.mono (clzX_ok h₄ (by omega_arith)) fun t₅ ⟨m5, k5⟩ => ?_)
  have top4 : (word t₄.mem B (slot W sqZ + 8 * (W - 5))).toNat = Xn X h * 2 ^ (64 * C) / 2 ^ (64 * (2 * h - 1)) := by
    rw [show W - 5 = 2 * h - 1 by omega, word_top (n := W) (by omega_arith)
      (by rw [x4, show 2 * h - 1 + 1 = 2 * h by omega]; exact fh), x4]
  rw [top4] at m5
  have ne := norm_even (Y := Xn X h * 2 ^ (64 * C)) (H := 2 * h) (by omega_arith) fl fh
  generalize hz : (63 - Nat.log2 (Xn X h * 2 ^ (64 * C) / 2 ^ (64 * (2 * h - 1)))) / 2 * 2 = z at m5 ne
  have hz64 : z < 64 := by omega
  have hz2 : z % 2 = 0 := by omega
  obtain ⟨nlo, nhi⟩ := ne
  have h₅ := h₄.congrW m5 (by unfold DOk; simp only [sC, sFn]; omega) (by decide) k5 (by simp)
  have o5 : Outside B (8 * sC) 8 t₄.mem t₅.mem := by rw [m5]; exact writeW_outside _ _ _ (by omega_arith)
  have c5 : word t₅.mem B (8 * sC) = BitVec.ofNat 64 z := by rw [m5, word_writeW_self]
  -- The shift by bits, and the copy back.
  refine WP.seq (WP.mono (shlClP_ok h₅ false (j := sqZ) (t := sqT) (by simp; decide) (by simp; decide)
    (by simp only [shlN, Bool.false_eq_true, ↓reduceIte]; omega) hz64 (sC_pre (by omega_arith) c5))
    fun t₆ ⟨v6, o6, k6⟩ => ?_)
  simp only [shlN, Bool.false_eq_true, ↓reduceIte] at v6 o6
  have h₆ := h₅.congrO o6 (by omega_arith) k6 (by simp)
  refine WP.mono (copyA_ok h₆ (o := sqZ) (a := sqT) (by decide) (by decide) (by decide)) fun t ⟨v7, o7, k7⟩ => ?_
  have hW' : 2 ^ (64 * (2 * h)) ≤ 2 ^ (64 * W) := Nat.pow_le_pow_right (by decide) (by omega_arith)
  refine ⟨C, z, hz2, hz64, fC, ?_, nlo, nhi, ?_, ?_, ?_, ?_,
    (((((((k₁.trans k₂).trans k₂').trans k₃).trans kk4).trans k5).trans k6).trans k7).mono (by simp [mmRegs]),
    h₆.congrO o7 (by omega_arith) k7 (by simp)⟩
  · rw [v7, v6, o5.wv (by omega_arith) (by omega_arith), x4, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le nhi hW')]
  · rw [o7.word (by omega_arith) (by omega_arith), o6.word (by omega_arith) (by omega_arith), o5.word (by omega_arith) (by omega_arith), k4]
  · rw [o7.word (by omega_arith) (by omega_arith), o6.word (by omega_arith) (by omega_arith), c5]
  · rw [o7.word (by omega_arith) (by omega_arith), o6.word (by omega_arith) (by omega_arith), o5.word (by omega_arith) (by omega_arith),
      f4.word_eq (fun r hr => by
        simp only [nxRs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp only <;> omega) (by omega_arith), Z₃]
  · have fr : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' → (∀ y, o ≤ y → y < o + n → NxP W y) →
        FrmP B (NxP W) m m' := fun ho hP => FrmP.of_out ho hP
    refine ((((((FP₁.mono fun y hy => by unfold NxP; omega).trans (FP₃.mono fun y hy => by unfold NxP; omega)).trans
      (FrmP.of_frm f4 fun r hr y h1 h2 => by
        simp only [nxRs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp only at h1 h2 <;> unfold NxP <;> omega)).trans
      (fr o5 fun y h1 h2 => by unfold NxP; omega)).trans (fr o6 fun y h1 h2 => by unfold NxP; omega)).trans
      (fr o7 fun y h1 h2 => by unfold NxP; omega))

end VG.Proof.Rsa.X86_64.Rd
