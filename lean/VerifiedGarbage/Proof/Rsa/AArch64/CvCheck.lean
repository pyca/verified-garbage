module

public import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
public import VerifiedGarbage.Proof.Rsa.AArch64.InvLaw
public import VerifiedGarbage.Proof.Rsa.AArch64.WDiv
import VerifiedGarbage.Proof.Rsa.AArch64.CvTail
import VerifiedGarbage.Proof.Rsa.AArch64.NCalc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.AArch64.CrtRows
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks

/-!
# `vg_rsa_crt_values` on AArch64: the loads and the check of `p q = n`

The loads of `n`, `p`, `q` and `d` (`cvLoads_ok`), and the mask of
`p q = n` (`cvCheck_ok`), as `n mod p = 0`, `n / p = q` and `p` odd
(`pq_iff`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.Keys.CrtValues
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN)

/-- `p q = n` for an odd `n`, as `pqCheck` checks it. -/
theorem pq_iff {N P Q : Nat} (hN : N % 2 = 1) :
    (P % 2 = 1 ∧ N / P = Q ∧ N % P = 0) ↔ P * Q = N := by
  constructor
  · rintro ⟨hp, hq, hr⟩
    have := Nat.div_add_mod N P
    rw [hq, hr, Nat.add_zero] at this
    exact this
  · intro h
    have hp : P % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one P with hP | hP
      · rw [← h, Nat.mul_mod, hP, Nat.zero_mul] at hN; exact absurd hN (by decide)
      · exact hP
    have hP0 : 0 < P := by omega_arith
    refine ⟨hp, ?_, ?_⟩
    · rw [← h, Nat.mul_div_cancel_left _ hP0]
    · rw [← h, Nat.mul_mod_right]

/-- The memory word of the mask. -/
abbrev mword (m : Mem) (B : Addr) : BitVec 64 := word m B (8 * Public.sMask)

/-- `CvS` and the mask, after a store to the mask's slot. -/
theorem CvS.mask {I : CvIn} {m₀ : Mem} {s t : State} (h : CvS I m₀ s) {v : BitVec 64}
    (hm : t.mem = s.mem.writeW (off I.B (8 * Public.sMask)) v) {regs : List Reg}
    (k : Keep regs s t) (hr : .x0 ∉ regs) : CvS I m₀ t ∧ mword t.mem I.B = v ∧
      ∀ j < 16, wv t.mem I.B (slot (wk I.k) j) (wk I.k + 2) = wv s.mem I.B (slot (wk I.k) j) (wk I.k + 2) := by
  have hn := h.ws.scr.nowrap
  have h256 := h.ws.h256
  have eM : Public.sMask = 22 := rfl
  have ho := writeW_outside s.mem I.B v (d := 8 * Public.sMask) (by omega_arith)
  rw [← hm] at ho
  refine ⟨h.step (Frm.of_outside ho (List.mem_singleton_self _)) (fun r hr => ?_) (fun r hr => ?_) k hr,
    by rw [hm]; exact word_writeW_self _ _ _ _, fun j hj => ho.wv (Or.inr ?_) (by have := h.ws.sl hj; omega_arith)⟩
  · rw [List.mem_singleton.mp hr]; exact Or.inr rfl
  · rw [List.mem_singleton.mp hr]; simp only [Public.sMask, sFn]; omega_arith
  · have := hdr_lt_slot (wk I.k) j (show Public.sMask < 32 by decide); omega_arith

/-- The bounds on the lengths. -/
structure CvLens (I : CvIn) : Prop where
  k1 : 64 ≤ I.k
  k2 : I.k ≤ 1024
  pl1 : 1 ≤ I.pl
  pl2 : I.pl < I.k
  ql1 : 1 ≤ I.ql
  ql2 : I.ql < I.k
  dl1 : 1 ≤ I.dl
  dl2 : I.dl ≤ I.k
  nl : I.nb.length = I.k
  pbl : I.pb.length = I.pl
  qbl : I.qb.length = I.ql
  dbl : I.db.length = I.dl
  z : 128 * I.k ≤ I.Z

/-- An array other than the one that changed. -/
theorem outside_arr {m m' : Mem} {B : Addr} {Z w j i n L : Nat} (ho : Outside B (slot w j) L m m')
    (hL : L ≤ 8 * (w + 2)) (hij : i ≠ j) (hn : n ≤ w + 2) (hi : i < 16) (hZ : slot w 16 ≤ Z)
    (hB : B.toNat + Z ≤ 2 ^ 64) : wv m' B (slot w i) n = wv m B (slot w i) n :=
  ho.wv (by have := slot_sep (w := w) hij; omega_arith) (by have := Nat.le_trans (slot_lt (w := w) hi) hZ; omega_arith)

/-- The loads of `n`, `p`, `q` and `d` into their arrays. -/
theorem cvLoads_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) :
    WP isa (seqs (loadA aN Public.sN Public.sK ++
      (loadA aP sP sPl ++ (loadA aQ sQ sQl ++ loadA aD sD sDl)))) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      wv t.mem I.B (slot (wk I.k) aN) (wk I.k) = Spec.Rsa.os2ip I.nb ∧
      wv t.mem I.B (slot (wk I.k) aP) (wk I.k) = Spec.Rsa.os2ip I.pb ∧
      wv t.mem I.B (slot (wk I.k) aQ) (wk I.k) = Spec.Rsa.os2ip I.qb ∧
      wv t.mem I.B (slot (wk I.k) aD) (wk I.k) = Spec.Rsa.os2ip I.db := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have k1 := L.k1
  have k2 := L.k2
  have eM : Public.sMask = 22 := rfl
  have hm : ∀ {m m' : Mem} {j : Nat}, Outside I.B (slot (wk I.k) j) (8 * (wk I.k + 2)) m m' →
      mword m' I.B = mword m I.B := fun {_ _ j} o =>
    o.word (Or.inl (by have := hdr_lt_slot (wk I.k) j (show Public.sMask < 32 by decide); omega_arith))
      (by have := hdr_lt_slot (wk I.k) j (show Public.sMask < 32 by decide); omega_arith)
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (loadA_ok h.ws (by decide) (by decide)
    (by decide) h.args.n h.args.k h.n L.nl (by omega_arith) (by unfold wk; omega_arith)) fun s₁ ⟨hv₁, o₁, _, _, k₁⟩ => ?_)
  have h₁ := h.arr (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (loadA_ok h₁.ws (by decide) (by decide)
    (by decide) h₁.args.p h₁.args.pl h₁.p L.pbl L.pl1 (by have := L.pl2; unfold wk; omega_arith)) fun s₂ ⟨hv₂, o₂, _, _, k₂⟩ => ?_)
  have h₂ := h₁.arr (by decide) (Nat.le_refl _) o₂ k₂ (by decide)
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (loadA_ok h₂.ws (by decide) (by decide)
    (by decide) h₂.args.q h₂.args.ql h₂.q L.qbl L.ql1 (by have := L.ql2; unfold wk; omega_arith)) fun s₃ ⟨hv₃, o₃, _, _, k₃⟩ => ?_)
  have h₃ := h₂.arr (by decide) (Nat.le_refl _) o₃ k₃ (by decide)
  refine WP.mono (loadA_ok h₃.ws (by decide) (by decide) (by decide) h₃.args.d h₃.args.dl h₃.d L.dbl L.dl1
    (by have := L.dl2; unfold wk; omega_arith)) fun t ⟨hv₄, o₄, _, _, k₄⟩ => ?_
  have h₄ := h₃.arr (by decide) (Nat.le_refl _) o₄ k₄ (by decide)
  refine ⟨h₄, ?_, ?_, ?_, ?_, hv₄⟩
  · rw [hm o₄, hm o₃, hm o₂, hm o₁]
  · rw [outside_arr o₄ (Nat.le_refl _) (by decide) (by omega_arith) (by decide) hZ hn,
      outside_arr o₃ (Nat.le_refl _) (by decide) (by omega_arith) (by decide) hZ hn,
      outside_arr o₂ (Nat.le_refl _) (by decide) (by omega_arith) (by decide) hZ hn]; exact hv₁
  · rw [outside_arr o₄ (Nat.le_refl _) (by decide) (by omega_arith) (by decide) hZ hn,
      outside_arr o₃ (Nat.le_refl _) (by decide) (by omega_arith) (by decide) hZ hn]; exact hv₂
  · rw [outside_arr o₄ (Nat.le_refl _) (by decide) (by omega_arith) (by decide) hZ hn]; exact hv₃

theorem mask_check {c : Bool} {A B1 B2 PQ : Prop} [Decidable A] [Decidable B1] [Decidable B2] [Decidable PQ]
    (h : A → ((A ∧ B1 ∧ B2) ↔ PQ)) (hA : ¬ A → ¬ PQ) :
    (decide A && (decide B2 && (decide B1 && c))) = (c && decide PQ) := by
  by_cases a : A
  · have := h a
    by_cases b1 : B1 <;> by_cases b2 : B2 <;> by_cases pq : PQ <;> simp_all
  · have := hA a
    simp_all

/-- `⌈a / 8⌉`, as `addImm 7; lsr 3` computes it. -/
theorem ceil8_bv {a : Nat} (ha : a < 2 ^ 60) :
    (BitVec.ofNat 64 a + 7#64) >>> 3 = BitVec.ofNat 64 ((a + 7) / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    show (7#64).toNat = 7 from rfl]
  rw [Nat.mod_eq_of_lt (by omega_arith : a < 2 ^ 64), Nat.mod_eq_of_lt (by omega_arith : a + 7 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega_arith : (a + 7) / 8 < 2 ^ 64)]

/-- `pqCheck`'s setup for `mulRows`: `p`'s base and words into `x11` and
`x13`, `q`'s into `x9` and `x12`, and the product's base `aU` into `x8`. -/
theorem pqSetup_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) :
    WP isa (.block (ws ++ base aP .x5 ++ base aQ .x9 ++ base aU .x8 ++ [mov .x11 .x5, ldh .x12 sQl,
      .addImm .x .x12 .x12 7, .lsr .x .x12 .x12 3, ldh .x13 sPl, .addImm .x .x13 .x13 7, .lsr .x .x13 .x13 3,
      movi .x7 0])) s fun t =>
      (t.gpr .x11 = off I.B (slot (wk I.k) aP) ∧ t.gpr .x9 = off I.B (slot (wk I.k) aQ) ∧
        t.gpr .x8 = off I.B (slot (wk I.k) aU) ∧ t.gpr .x12 = BitVec.ofNat 64 ((I.ql + 7) / 8) ∧
        t.gpr .x13 = BitVec.ofNat 64 ((I.pl + 7) / 8) ∧ t.gpr .x7 = 0 ∧ t.mem = s.mem) ∧
      Keep [.x5, .x7, .x8, .x9, .x11, .x12, .x13] s t := by
  have hn := h.ws.scr.nowrap
  have h256 := h.ws.h256
  have := L.pl2
  have := L.ql2
  have := L.k2
  simp only [List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun s₁ ⟨⟨_, h11, m₁, _⟩, k₁⟩ => ?_)
  rw [← List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono (base2_ok aP aQ .x5 .x9 ((k₁.gpr .x0 (by decide)).trans h.ws.x0) h11)
    fun s₂ ⟨⟨h5, h9, m₂, _⟩, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine WP.block_append_iff.mpr (WP.mono (base_ok aU .x8 ((k12.gpr .x0 (by decide)).trans h.ws.x0)
    ((k₂.gpr .x11 (by decide)).trans h11)) fun s₃ ⟨⟨h8, m₃, _⟩, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  have hs₃ := h.ws.scr.congr k13.wr
  have hl : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off I.B (8 * i)) 8 := fun i hi => hs₃.ld (by omega_arith)
  have mm : s₃.mem = s.mem := by rw [m₃, m₂, m₁]
  refine WP.mono (WP.keep [.x7, .x11, .x12, .x13] (Q := fun t => t.gpr .x11 = off I.B (slot (wk I.k) aP) ∧
      t.gpr .x12 = BitVec.ofNat 64 ((I.ql + 7) / 8) ∧ t.gpr .x13 = BitVec.ofNat 64 ((I.pl + 7) / 8) ∧
      t.gpr .x7 = 0 ∧ t.mem = s₃.mem) (by
    brun [(k13.gpr .x0 (by decide)).trans h.ws.x0, (k₃.gpr .x5 (by decide)).trans h5, hdr_enc (show sQl < 32 by decide),
      hdr_enc (show sPl < 32 by decide), hl sQl (by decide), hl sPl (by decide), mm, h.args.pl, h.args.ql,
      ceil8_bv (show I.pl < 2 ^ 60 by omega_arith), ceil8_bv (show I.ql < 2 ^ 60 by omega_arith)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h11', h12', h13', h7', mt⟩, k₄⟩ => ?_
  exact ⟨⟨h11', (k₄.gpr .x9 (by decide)).trans ((k₃.gpr .x9 (by decide)).trans h9), (k₄.gpr .x8 (by decide)).trans h8,
    h12', h13', h7', by rw [mt, mm]⟩, (k13.trans k₄).mono (by decide)⟩

/-- `pqCheck`'s parts. -/
theorem pqCheck_eq : pqCheck = ([zeroA aU, zeroA aV] : List (Prog isa)) ++
    (([.block (ws ++ base aP .x5 ++ base aQ .x9 ++ base aU .x8 ++
    ([mov .x11 .x5, ldh .x12 sQl, .addImm .x .x12 .x12 7, .lsr .x .x12 .x12 3, ldh .x13 sPl, .addImm .x .x13 .x13 7,
      .lsr .x .x13 .x13 3, movi .x7 0] : List Instr)), VG.Impl.Rsa.AArch64.Crt.mulRows] : List (Prog isa)) ++ (eqA aU aN ++
    ([.block [.addImm .x .x14 .x12 4], countLoop .x14 [ld .x3 .x16, .logic .orr .x .x9 .x9 .x3, next .x16],
      .block andZero] : List (Prog isa)))) := by
  simp only [pqCheck, List.cons_append, List.nil_append, List.append_assoc]

/-- `pqCheck`'s clearing: arrays `aU` and `aV`, `2 w + 4` words, all zero. -/
theorem pqZero_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) :
    WP isa (seqs [zeroA aU, zeroA aV]) s fun t =>
      CvS I m₀ t ∧ (∀ i < 2 * ((wk I.k) + 2), word t.mem I.B (slot (wk I.k) aU + 8 * i) = 0) ∧
      Outside I.B (slot (wk I.k) aU) (16 * ((wk I.k) + 2)) s.mem t.mem := by
  have hn := h.ws.scr.nowrap
  have eV : slot (wk I.k) aV = slot (wk I.k) aU + 8 * ((wk I.k) + 2) := by simp only [slot, aU, aV]; omega_arith
  have sU := h.ws.sl (j := aV) (by decide)
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_ok h.ws (j := aU) (by decide)) fun s₁ ⟨z₁, o₁, _, _, _, k₁⟩ => ?_)
  have h₁ := h.arr (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine WP.mono (zeroA_ok h₁.ws (j := aV) (by decide)) fun s₂ ⟨z₂, o₂, _, _, _, k₂⟩ => ?_
  refine ⟨h₁.arr (by decide) (Nat.le_refl _) o₂ k₂ (by decide), fun i hi => ?_,
    (o₁.mono (Nat.le_refl _) (by omega_arith)).trans (o₂.mono (by omega_arith) (by omega_arith))⟩
  have a₁ := (wv_eq_zero_iff _ _ _ _).mp z₁
  have a₂ := (wv_eq_zero_iff _ _ _ _).mp z₂
  by_cases hi' : i < (wk I.k) + 2
  · rw [o₂.word (by omega_arith) (by omega_arith)]; exact a₁ i hi'
  · have := a₂ (i - ((wk I.k) + 2)) (by omega_arith)
    rw [eV, show slot (wk I.k) aU + 8 * ((wk I.k) + 2) + 8 * (i - ((wk I.k) + 2)) = slot (wk I.k) aU + 8 * i by omega_arith] at this
    exact this

/-- `pqCheck`'s product: `p q` into the `2 w + 4` words of arrays `aU` and
`aV`, from zero. -/
theorem pqProd_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I)
    (hz : ∀ i < 2 * ((wk I.k) + 2), word s.mem I.B (slot (wk I.k) aU + 8 * i) = 0)
    (hPb : wv s.mem I.B (slot (wk I.k) aP) (wk I.k) < 256 ^ I.pl)
    (hQb : wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) < 256 ^ I.ql) :
    WP isa (seqs [.block (ws ++ base aP .x5 ++ base aQ .x9 ++ base aU .x8 ++
      [mov .x11 .x5, ldh .x12 sQl, .addImm .x .x12 .x12 7, .lsr .x .x12 .x12 3, ldh .x13 sPl, .addImm .x .x13 .x13 7,
        .lsr .x .x13 .x13 3, movi .x7 0]), VG.Impl.Rsa.AArch64.Crt.mulRows]) s fun t =>
      CvS I m₀ t ∧ wv t.mem I.B (slot (wk I.k) aU) ((wk I.k) + ((wk I.k) + 4)) =
        wv s.mem I.B (slot (wk I.k) aP) (wk I.k) * wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) ∧
      Outside I.B (slot (wk I.k) aU) (16 * ((wk I.k) + 2)) s.mem t.mem := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have k1 := L.k1
  have k2 := L.k2
  have pl1 := L.pl1
  have pl2 := L.pl2
  have ql1 := L.ql1
  have ql2 := L.ql2
  have hwp : (I.pl + 7) / 8 ≤ (wk I.k) := by unfold wk; omega_arith
  have hwq : (I.ql + 7) / 8 ≤ (wk I.k) := by unfold wk; omega_arith
  have sU := h.ws.sl (j := aV) (by decide)
  have sP := h.ws.sl (j := aP) (by decide)
  have sQ := h.ws.sl (j := aQ) (by decide)
  have pUP := slot_sep (w := wk I.k) (show aU ≠ aP by decide)
  have pUQ := slot_sep (w := wk I.k) (show aU ≠ aQ by decide)
  have pVP := slot_sep (w := wk I.k) (show aV ≠ aP by decide)
  have pVQ := slot_sep (w := wk I.k) (show aV ≠ aQ by decide)
  have eV : slot (wk I.k) aV = slot (wk I.k) aU + 8 * ((wk I.k) + 2) := by simp only [slot, aU, aV]; omega_arith
  have h8U : 8 * 32 ≤ slot (wk I.k) aU := by have := hdr_lt_slot (wk I.k) aU (show 31 < 32 by decide); omega_arith
  simp only [seqs]
  refine WP.seq (WP.mono (pqSetup_ok h L) fun s₃ ⟨⟨h11, h9, h8, h12, h13, h7, m₃⟩, k₃⟩ => ?_)
  have hs₃ := h.ws.scr.congr k₃.wr
  generalize hwp' : (I.pl + 7) / 8 = wp at *
  generalize hwq' : (I.ql + 7) / 8 = wq at *
  have hPw : wv s₃.mem I.B (slot (wk I.k) aP) wp = wv s.mem I.B (slot (wk I.k) aP) (wk I.k) := by
    have hb : wv s.mem I.B (slot (wk I.k) aP) (wk I.k) < 2 ^ (64 * wp) := Nat.lt_of_lt_of_le hPb (by
      rw [pow256_eq, ← hwp']; exact Nat.pow_le_pow_right (by decide) (by omega_arith))
    rw [m₃, wv_low_of_lt hwp hb]
  have hQw : wv s₃.mem I.B (slot (wk I.k) aQ) wq = wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) := by
    have hb : wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) < 2 ^ (64 * wq) := Nat.lt_of_lt_of_le hQb (by
      rw [pow256_eq, ← hwq']; exact Nat.pow_le_pow_right (by decide) (by omega_arith))
    rw [m₃, wv_low_of_lt hwq hb]
  have z₃ : wv s₃.mem I.B (slot (wk I.k) aU) (wp + wq + 2) = 0 := by
    rw [m₃]; exact wv_zero fun i hi => hz i (by omega_arith)
  refine WP.mono (mulRows_ok hs₃ h11 h9 h13 h12 h8 h7 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by rw [z₃]; exact Nat.two_pow_pos _))
    fun s₄ ⟨v₄, o₄, k₄⟩ => ?_
  rw [z₃, Nat.zero_add, hPw, hQw] at v₄
  have o₄' : Outside I.B (slot (wk I.k) aU) (16 * ((wk I.k) + 2)) s.mem s₄.mem := by
    rw [← m₃]; exact o₄.mono (Nat.le_refl _) (by omega_arith)
  refine ⟨h.step (Frm.of_outside o₄' (List.mem_singleton_self _)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Or.inl h8U) (fun r hr => by
    rw [List.mem_singleton.mp hr]; dsimp only; omega_arith) (k₃.trans k₄) (by decide), ?_, o₄'⟩
  have e := wv_add s₄.mem I.B (slot (wk I.k) aU) (wp + wq + 2) ((wk I.k) + ((wk I.k) + 4) - (wp + wq + 2))
  have z : wv s₄.mem I.B (slot (wk I.k) aU + 8 * (wp + wq + 2)) ((wk I.k) + ((wk I.k) + 4) - (wp + wq + 2)) = 0 :=
    wv_zero fun i hi => by
      rw [o₄.word (by omega_arith) (by omega_arith), m₃,
        show slot (wk I.k) aU + 8 * (wp + wq + 2) + 8 * i = slot (wk I.k) aU + 8 * (wp + wq + 2 + i) by omega_arith]
      exact hz _ (by omega_arith)
  rw [show wp + wq + 2 + ((wk I.k) + ((wk I.k) + 4) - (wp + wq + 2)) = (wk I.k) + ((wk I.k) + 4) by omega_arith, z,
    Nat.mul_zero, Nat.add_zero, v₄] at e
  exact e

/-- `pqCheck`'s comparison: the mask of `[aU] = n` over `2 w + 4` words and'ed
into `sMask`, the arrays unchanged. -/
theorem pqCmp_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) {c : Bool} (hc : mword s.mem I.B = mask c) :
    WP isa (seqs (eqA aU aN ++ ([.block [.addImm .x .x14 .x12 4],
      countLoop .x14 [ld .x3 .x16, .logic .orr .x .x9 .x9 .x3, next .x16], .block andZero] : List (Prog isa)))) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mask (decide (wv s.mem I.B (slot (wk I.k) aU) ((wk I.k) + ((wk I.k) + 4)) =
        wv s.mem I.B (slot (wk I.k) aN) (wk I.k)) && c) ∧
      ∀ j < 16, wv t.mem I.B (slot (wk I.k) j) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have sU := h.ws.sl (j := aV) (by decide)
  have sN := h.ws.sl (j := aN) (by decide)
  have pUN := slot_sep (w := wk I.k) (show aU ≠ aN by decide)
  have pVN := slot_sep (w := wk I.k) (show aV ≠ aN by decide)
  have eV : slot (wk I.k) aV = slot (wk I.k) aU + 8 * ((wk I.k) + 2) := by simp only [slot, aU, aV]; omega_arith
  have w1 := h.ws.w1
  have w2 := h.ws.w2
  simp only [eqA, List.cons_append, List.nil_append, seqs]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun s₅ ⟨⟨h12₅, h11₅, m₅, _⟩, k₅⟩ =>
    WP.mono (WP.keep [.x9, .x14] (Q := fun t => t.gpr .x9 = 0 ∧ t.gpr .x14 = BitVec.ofNat 64 (wk I.k) ∧
      t.mem = s₅.mem) (by brun [h12₅]) (by decide) (by decide) (by decide +kernel))
      fun s₆ ⟨⟨h9₆, h14₆, m₆⟩, k₆⟩ => ?_))
  have mm6 : s₆.mem = s.mem := by rw [m₆, m₅]
  have h₆ := h.step (rs := []) (by rw [mm6]; exact Frm.refl _ _ _) (by simp) (by simp) (k₅.trans k₆) (by decide)
  refine WP.seq (WP.mono (base2_ok aU aN .x16 .x17 h₆.ws.x0 ((k₆.gpr .x11 (by decide)).trans h11₅))
    fun s₇ ⟨⟨h16, h17, m₇, _⟩, k₇⟩ => ?_)
  have hs₇ := h₆.ws.scr.congr k₇.wr
  have mm7 : s₇.mem = s.mem := by rw [m₇, mm6]
  refine WP.seq (WP.mono (wp_countdown (N := wk I.k) (by omega_arith) (by omega_arith)
    (fun j t => OrInv s₇ I.B I.Z (fun j => ∀ i < j, word s₇.mem I.B (slot (wk I.k) aU + 8 * i) =
        word s₇.mem I.B (slot (wk I.k) aN + 8 * i)) j t ∧
      t.gpr .x16 = off I.B (slot (wk I.k) aU + 8 * j) ∧ t.gpr .x17 = off I.B (slot (wk I.k) aN + 8 * j))
    (fun j hj t hI _ => VG.Proof.Bignum.AArch64.xorStep_ok (by omega_arith) (by omega_arith) hj hI.1 hI.2.1 hI.2.2)
    ⟨⟨hs₇, Keep.refl _ _, rfl, by
      rw [(k₇.gpr .x9 (by decide)).trans h9₆]; exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩⟩,
      by rw [h16]; rfl, by rw [h17]; rfl⟩ ((k₇.gpr .x14 (by decide)).trans h14₆)) fun s₈ ⟨hI, h16₈, _⟩ => ?_)
  have mm8 : s₈.mem = s.mem := by rw [hI.mem, mm7]
  have h12₈ : s₈.gpr .x12 = BitVec.ofNat 64 (wk I.k) :=
    (((k₆.trans k₇).trans hI.keep).gpr .x12 (by decide)).trans h12₅
  refine WP.seq (WP.mono (WP.keep [.x14] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 (wk I.k + 4) ∧ t.mem = s₈.mem)
      (by brun [h12₈, ofNat_add_ofNat]) (by decide) (by decide) (by decide +kernel))
      fun s₁₀ ⟨⟨h14₁₀, m₁₀⟩, k₁₀⟩ => ?_)
  have mm10 : s₁₀.mem = s.mem := by rw [m₁₀, mm8]
  have hs₁₀ := hI.scr.congr k₁₀.wr
  have h16₁₀ : s₁₀.gpr .x16 = off I.B (slot (wk I.k) aU + 8 * wk I.k) := (k₁₀.gpr .x16 (by decide)).trans h16₈
  refine WP.seq (WP.mono (wp_countdown (N := wk I.k + 4) (by omega_arith) (by omega_arith)
    (fun j t => OrInv s₁₀ I.B I.Z (fun j => (∀ i < wk I.k, word s₇.mem I.B (slot (wk I.k) aU + 8 * i) =
        word s₇.mem I.B (slot (wk I.k) aN + 8 * i)) ∧
        ∀ i < j, word s₁₀.mem I.B (slot (wk I.k) aU + 8 * wk I.k + 8 * i) = 0) j t ∧
      t.gpr .x16 = off I.B (slot (wk I.k) aU + 8 * wk I.k + 8 * j))
    (fun j hj t hI _ => VG.Proof.Bignum.AArch64.orStep_ok (by omega_arith) hj hI.1 hI.2)
    ⟨⟨hs₁₀, Keep.refl _ _, rfl, by
      rw [k₁₀.gpr .x9 (by decide), hI.val]
      exact ⟨fun h => ⟨h, fun i hi => absurd hi (Nat.not_lt_zero _)⟩, fun h => h.1⟩⟩, by rw [h16₁₀]; rfl⟩ h14₁₀)
    fun s₁₁ ⟨hI₂, _⟩ => ?_)
  have mm11 : s₁₁.mem = s.mem := by rw [hI₂.mem, mm10]
  have h₁₁ := h.step (rs := []) (by rw [mm11]; exact Frm.refl _ _ _) (by simp) (by simp)
    (((((k₅.trans k₆).trans k₇).trans hI.keep).trans k₁₀).trans hI₂.keep) (by decide)
  have hz : s₁₁.gpr .x9 = 0 ↔ wv s.mem I.B (slot (wk I.k) aU) ((wk I.k) + ((wk I.k) + 4)) =
      wv s.mem I.B (slot (wk I.k) aN) (wk I.k) := by
    rw [hI₂.val, mm10, mm7, wv_add, split_eq_iff (wv_lt _ _ _ _), wv_eq_zero_iff]
    exact and_congr ⟨fun h => wv_congr2 h, fun h => wv_inj _ h⟩ Iff.rfl
  refine WP.mono (andZero_ok (c := c) h₁₁.ws (by rw [mm11]; exact hc) hz) fun t ⟨⟨mt, _⟩, kt⟩ => ?_
  obtain ⟨ht, hmt, -⟩ := h₁₁.mask mt kt (by decide)
  refine ⟨ht, hmt, fun j hj => ?_⟩
  have sj := h.ws.sl hj
  have hdj := hdr_lt_slot (wk I.k) j (show Public.sMask < 32 by decide)
  rw [mt, (writeW_outside _ _ _ (by omega_arith)).wv (Or.inr (by omega_arith)) (by omega_arith), mm11]

/-- `pqCheck`: the mask of `p q = n` and'ed into `sMask`: `p q` (`⌈p_len / 8⌉`
rows of `⌈q_len / 8⌉` words) into arrays `aU` and `aV`, its `2 w + 4` words
compared with `n`. -/
theorem cvCheck_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) {c : Bool}
    (hc : mword s.mem I.B = mask c) (hPb : wv s.mem I.B (slot (wk I.k) aP) (wk I.k) < 256 ^ I.pl)
    (hQb : wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) < 256 ^ I.ql) :
    WP isa (seqs pqCheck) s fun t =>
      CvS I m₀ t ∧ (∃ c', mword t.mem I.B = mask c' ∧
        c' = (c && decide (wv s.mem I.B (slot (wk I.k) aP) (wk I.k) *
        wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) = wv s.mem I.B (slot (wk I.k) aN) (wk I.k)))) ∧
      ∀ j, j = aP ∨ j = aQ ∨ j = aD → wv t.mem I.B (slot (wk I.k) j) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have eM : Public.sMask = 22 := rfl
  have h8U : 8 * 32 ≤ slot (wk I.k) aU := by have := hdr_lt_slot (wk I.k) aU (show 31 < 32 by decide); omega_arith
  have sV := h.ws.sl (j := aV) (by decide)
  have ar : ∀ {m m' : Mem} {j}, Outside I.B (slot (wk I.k) aU) (16 * ((wk I.k) + 2)) m m' → j ≠ aU → j ≠ aV → j < 16 →
      wv m' I.B (slot (wk I.k) j) (wk I.k) = wv m I.B (slot (wk I.k) j) (wk I.k) := fun o h1 h2 h3 => by
    have := h.ws.sl h3
    have e1 := slot_sep (w := wk I.k) h1
    have e2 := slot_sep (w := wk I.k) h2
    have eV : slot (wk I.k) aV = slot (wk I.k) aU + 8 * ((wk I.k) + 2) := by simp only [slot, aU, aV]; omega_arith
    exact o.wv (by omega_arith) (by omega_arith)
  rw [pqCheck_eq]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (pqZero_ok h) fun s₂ ⟨h₂, z₂, o₂⟩ => ?_)
  have eP₂ := ar o₂ (j := aP) (by decide) (by decide) (by decide)
  have eQ₂ := ar o₂ (j := aQ) (by decide) (by decide) (by decide)
  refine wp_seqs_append (by simp) (by simp [eqA]) (WP.mono (pqProd_ok h₂ L z₂ (by rw [eP₂]; exact hPb)
    (by rw [eQ₂]; exact hQb)) fun s₄ ⟨h₄, v₄, o₄⟩ => ?_)
  have hm₄ : mword s₄.mem I.B = mask c := by
    show word s₄.mem I.B (8 * Public.sMask) = _
    rw [o₄.word (Or.inl (by omega_arith)) (by omega_arith), o₂.word (Or.inl (by omega_arith)) (by omega_arith)]; exact hc
  refine WP.mono (pqCmp_ok h₄ hm₄) fun t ⟨ht, mt, at'⟩ => ⟨ht, ⟨_, mt, ?_⟩, fun j hj => ?_⟩
  · rw [v₄, eP₂, eQ₂, ar o₄ (j := aN) (by decide) (by decide) (by decide), ar o₂ (j := aN) (by decide) (by decide) (by decide),
      Bool.and_comm]
  · have hj' : j < 16 := by rcases hj with rfl | rfl | rfl <;> decide
    rw [at' j hj', ar o₄ (j := j) (by rcases hj with rfl | rfl | rfl <;> decide) (by rcases hj with rfl | rfl | rfl <;> decide) hj',
      ar o₂ (j := j) (by rcases hj with rfl | rfl | rfl <;> decide) (by rcases hj with rfl | rfl | rfl <;> decide) hj']

/-- `invSetup`: `inverse`'s start, `(u, v, x₁, x₂) := (q, p, 1, 0)`, with
the word of `u` above its `w` zero. -/
theorem invSetup_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) :
    WP isa (seqs invSetup) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      VG.Proof.Bignum.word t.mem I.B (slot (wk I.k) aU + 8 * wk I.k) = 0 ∧
      wv t.mem I.B (slot (wk I.k) aU) (wk I.k) = wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) ∧
      wv t.mem I.B (slot (wk I.k) aV) (wk I.k) = wv t.mem I.B (slot (wk I.k) aP) (wk I.k) ∧
      wv t.mem I.B (slot (wk I.k) aX₁) (wk I.k) = 1 ∧ wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) = 0 ∧
      ∀ j, j = aP ∨ j = aQ ∨ j = aD → wv t.mem I.B (slot (wk I.k) j) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have k1 := L.k1
  have eM : Public.sMask = 22 := rfl
  have hmw : ∀ {m m' : Mem} {j L' : Nat}, Outside I.B (slot (wk I.k) j) L' m m' → L' ≤ 8 * (wk I.k + 2) →
      mword m' I.B = mword m I.B := fun {_ _ j _} o _ =>
    o.word (Or.inl (by have := hdr_lt_slot (wk I.k) j (show Public.sMask < 32 by decide); omega_arith))
      (by omega_arith)
  have wvw : ∀ {m m' : Mem} {j : Nat}, j < 16 →
      wv m' I.B (slot (wk I.k) j) (wk I.k + 2) = wv m I.B (slot (wk I.k) j) (wk I.k + 2) →
      wv m' I.B (slot (wk I.k) j) (wk I.k) = wv m I.B (slot (wk I.k) j) (wk I.k) := fun {m m' j} _ e => by
    have e1 := wv_add m I.B (slot (wk I.k) j) (wk I.k) 2
    have e2 := wv_add m' I.B (slot (wk I.k) j) (wk I.k) 2
    have l1 := wv_lt m I.B (slot (wk I.k) j) (wk I.k)
    have l2 := wv_lt m' I.B (slot (wk I.k) j) (wk I.k)
    rw [e] at e2
    have := congrArg (· % 2 ^ (64 * wk I.k)) (e1.symm.trans e2)
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2] at this
    exact this.symm
  -- The arrays a piece leaves: `ot j` from an `Outside` of another.
  have ot : ∀ {m m' : Mem} {j i Ln : Nat}, Outside I.B (slot (wk I.k) j) Ln m m' → Ln ≤ 8 * (wk I.k + 2) → i ≠ j →
      i < 16 → wv m' I.B (slot (wk I.k) i) (wk I.k) = wv m I.B (slot (wk I.k) i) (wk I.k) :=
    fun o hL hij hi => outside_arr o hL hij (by omega_arith) hi hZ hn
  simp only [invSetup, seqs]
  -- `[u] := q`, `[v] := p`, `[x₁] := 1`, `[x₂] := 0`.
  refine WP.seq (WP.mono (zeroA_ok h.ws (j := aU) (by decide)) fun s₁ ⟨z₁, o₁, _, _, _, k₁⟩ => ?_)
  have h₁ := h.arr (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₁.ws (o := aU) (a := aQ) (by decide) (by decide) (by decide)) fun s₂ ⟨c₂, o₂, _, _, k₂⟩ => ?_)
  have h₂ := h₁.arr (by decide) (by omega_arith) o₂ k₂ (by decide)
  refine WP.seq (WP.mono (zeroA_ok h₂.ws (j := aV) (by decide)) fun s₃ ⟨z₃, o₃, _, _, _, k₃⟩ => ?_)
  have h₃ := h₂.arr (by decide) (Nat.le_refl _) o₃ k₃ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₃.ws (o := aV) (a := aP) (by decide) (by decide) (by decide)) fun s₄ ⟨c₄, o₄, _, _, k₄⟩ => ?_)
  have h₄ := h₃.arr (by decide) (by omega_arith) o₄ k₄ (by decide)
  refine WP.seq (WP.mono (zeroA_ok h₄.ws (j := aX₁) (by decide)) fun s₅ ⟨z₅, o₅, _, _, _, k₅⟩ => ?_)
  have h₅ := h₄.arr (by decide) (Nat.le_refl _) o₅ k₅ (by decide)
  refine WP.seq (WP.mono (setOneA_ok h₅.ws (j := aX₁) (by decide)) fun s₆ ⟨m₆, k₆⟩ => ?_)
  have o₆ := writeW_outside s₅.mem I.B (1 : BitVec 64) (d := slot (wk I.k) aX₁) (by have := h.ws.sl (j := aX₁) (by decide); omega_arith)
  rw [← m₆] at o₆
  have h₆ := h₅.arr (by decide) (by omega_arith) o₆ k₆ (by decide)
  refine WP.mono (zeroA_ok h₆.ws (j := aX₂) (by decide)) fun s₇ ⟨z₇, o₇, _, _, _, k₇⟩ => ?_
  have h₇ := h₆.arr (by decide) (Nat.le_refl _) o₇ k₇ (by decide)
  -- The values the inverse starts from.
  have eP : ∀ {m : Mem}, m = s.mem → wv m I.B (slot (wk I.k) aP) (wk I.k) = wv s.mem I.B (slot (wk I.k) aP) (wk I.k) :=
    fun e => by rw [e]
  have vP₇ : wv s₇.mem I.B (slot (wk I.k) aP) (wk I.k) = wv s.mem I.B (slot (wk I.k) aP) (wk I.k) := by
    rw [ot o₇ (Nat.le_refl _) (by decide) (by decide), ot o₆ (by omega_arith) (by decide) (by decide),
      ot o₅ (Nat.le_refl _) (by decide) (by decide), ot o₄ (by omega_arith) (by decide) (by decide),
      ot o₃ (Nat.le_refl _) (by decide) (by decide), ot o₂ (by omega_arith) (by decide) (by decide),
      ot o₁ (Nat.le_refl _) (by decide) (by decide)]
  have vQ₇ : wv s₇.mem I.B (slot (wk I.k) aQ) (wk I.k) = wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) := by
    rw [ot o₇ (Nat.le_refl _) (by decide) (by decide), ot o₆ (by omega_arith) (by decide) (by decide),
      ot o₅ (Nat.le_refl _) (by decide) (by decide), ot o₄ (by omega_arith) (by decide) (by decide),
      ot o₃ (Nat.le_refl _) (by decide) (by decide), ot o₂ (by omega_arith) (by decide) (by decide),
      ot o₁ (Nat.le_refl _) (by decide) (by decide)]
  have vU₇ : wv s₇.mem I.B (slot (wk I.k) aU) (wk I.k) = wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) := by
    rw [ot o₇ (Nat.le_refl _) (by decide) (by decide), ot o₆ (by omega_arith) (by decide) (by decide),
      ot o₅ (Nat.le_refl _) (by decide) (by decide), ot o₄ (by omega_arith) (by decide) (by decide),
      ot o₃ (Nat.le_refl _) (by decide) (by decide), c₂, ot o₁ (Nat.le_refl _) (by decide) (by decide)]
  have vV₇ : wv s₇.mem I.B (slot (wk I.k) aV) (wk I.k) = wv s₇.mem I.B (slot (wk I.k) aP) (wk I.k) := by
    rw [vP₇, ot o₇ (Nat.le_refl _) (by decide) (by decide), ot o₆ (by omega_arith) (by decide) (by decide),
      ot o₅ (Nat.le_refl _) (by decide) (by decide), c₄, ot o₃ (Nat.le_refl _) (by decide) (by decide),
      ot o₂ (by omega_arith) (by decide) (by decide), ot o₁ (Nat.le_refl _) (by decide) (by decide)]
  have vX₂ : wv s₇.mem I.B (slot (wk I.k) aX₂) (wk I.k) = 0 := by
    have := wv_add s₇.mem I.B (slot (wk I.k) aX₂) (wk I.k) 2; omega_arith
  have vX₁ : wv s₇.mem I.B (slot (wk I.k) aX₁) (wk I.k) = 1 := by
    rw [ot o₇ (Nat.le_refl _) (by decide) (by decide), m₆, wv_low (by have := h.ws.w1; omega_arith), word_writeW_self,
      (writeW_outside s₅.mem I.B (1 : BitVec 64) (d := slot (wk I.k) aX₁) (by
        have := h.ws.sl (j := aX₁) (by decide); omega_arith)).wv (Or.inr (by omega_arith)) (by have := h.ws.sl (j := aX₁) (by decide); omega_arith)]
    have hz : ∀ q < wk I.k + 2, VG.Proof.Bignum.word s₅.mem I.B (slot (wk I.k) aX₁ + 8 * q) = 0 :=
      (wv_eq_zero_iff _ _ _ _).mp z₅
    rw [wv_zero (n := wk I.k - 1) fun q hq => by
      have := hz (1 + q) (by omega_arith)
      rwa [show slot (wk I.k) aX₁ + 8 * (1 + q) = slot (wk I.k) aX₁ + 8 + 8 * q by omega_arith] at this]
    rfl
  have vU0 : VG.Proof.Bignum.word s₇.mem I.B (slot (wk I.k) aU + 8 * wk I.k) = 0 := by
    have e1 : VG.Proof.Bignum.word s₂.mem I.B (slot (wk I.k) aU + 8 * wk I.k) = 0 := by
      rw [o₂.word (Or.inr (by omega_arith)) (by have := h.ws.sl (j := aU) (by decide); omega_arith)]
      exact (wv_eq_zero_iff _ _ _ _).mp z₁ (wk I.k) (by omega_arith)
    have r := fun {j Ln : Nat} {m m' : Mem} (o : Outside I.B (slot (wk I.k) j) Ln m m') (hL : Ln ≤ 8 * (wk I.k + 2))
        (hj : j ≠ aU) (hj' : j < 16) =>
      o.word (d := slot (wk I.k) aU + 8 * wk I.k) (by have := slot_sep (w := wk I.k) hj; omega_arith)
        (by have := h.ws.sl (j := aU) (by decide); omega_arith)
    rw [r o₇ (Nat.le_refl _) (by decide) (by decide), r o₆ (by omega_arith) (by decide) (by decide),
      r o₅ (Nat.le_refl _) (by decide) (by decide), r o₄ (by omega_arith) (by decide) (by decide),
      r o₃ (Nat.le_refl _) (by decide) (by decide)]
    exact e1
  refine ⟨h₇, (hmw o₇ (Nat.le_refl _)).trans ((hmw o₆ (by omega_arith)).trans ((hmw o₅ (Nat.le_refl _)).trans
    ((hmw o₄ (by omega_arith)).trans ((hmw o₃ (Nat.le_refl _)).trans ((hmw o₂ (by omega_arith)).trans
      (hmw o₁ (Nat.le_refl _))))))), vU0, vU₇, vV₇, vX₁, vX₂, fun j hj => ?_⟩
  rcases hj with rfl | rfl | rfl
  · exact vP₇
  · exact vQ₇
  · rw [ot o₇ (Nat.le_refl _) (by decide) (by decide), ot o₆ (by omega_arith) (by decide) (by decide),
      ot o₅ (Nat.le_refl _) (by decide) (by decide), ot o₄ (by omega_arith) (by decide) (by decide),
      ot o₃ (Nat.le_refl _) (by decide) (by decide), ot o₂ (by omega_arith) (by decide) (by decide),
      ot o₁ (Nat.le_refl _) (by decide) (by decide)]

/-- `wordGuard` passes for `I`'s lengths and `n`'s first byte. -/
def CvIn.G (I : CvIn) : Prop := guardVal I.k I.pl I.ql (Mem.read (fun _ => I.nb[0]?.getD 0) 0 1) = 0

instance (I : CvIn) : Decidable I.G := inferInstanceAs (Decidable (_ = _))

/-- The doublings `inverseAtS` leaves to `qTail` when the guard passes. -/
def CvIn.E (I : CvIn) : Nat := if I.G then 15 * ((max I.pl I.ql + 7) / 8) + 10 else 0

/-- `n`'s first byte, as `wordGuard` reads it. -/
theorem cv_byte {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) :
    s.mem.read I.pN 1 = Mem.read (fun _ => I.nb[0]?.getD 0) 0 1 := by
  have hn0 : 0 < I.nb.length := by rw [L.nl]; have := L.k1; omega
  have := h.n.val 0 hn0
  rw [show I.pN + BitVec.ofNat 64 0 = I.pN by simp] at this
  simp only [Mem.read, this, List.getElem?_eq_getElem hn0, Option.getD_some]

/-- `guarded a b`: `a` if `I.G`, `b` otherwise, from the state after the
guard (the memory unchanged). -/
theorem cvGuarded_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) {a b : Prog isa}
    {Q : State → Prop}
    (ha : I.G → ∀ t, CvS I m₀ t → t.mem = s.mem → Keep [.x3, .x4, .x9, .x13, .x14, .x15, .x16] s t → WP isa a t Q)
    (hb : ¬ I.G → ∀ t, CvS I m₀ t → t.mem = s.mem → Keep [.x3, .x4, .x9, .x13, .x14, .x15, .x16] s t →
      WP isa b t Q) :
    WP isa (guarded a b) s Q := by
  have hn0 : 0 < I.nb.length := by rw [L.nl]; have := L.k1; omega
  unfold guarded
  refine WP.seq (WP.mono (wordGuard_ok (b := s.mem.read I.pN 1) h.ws.scr h.ws.x0 h.ws.h256 (by decide) (by decide)
    h.args.k h.args.pl h.args.ql h.args.n rfl (by simpa using h.n.rd 0 hn0)) fun s₁ ⟨⟨h9, m₁⟩, k₁⟩ => ?_)
  have h₁ := h.step (rs := []) (by rw [m₁]; exact Frm.refl _ _ _) (by simp) (by simp) k₁ (by decide)
  rw [cv_byte h L] at h9
  refine WP.ite (s₁.gpr .x9 == 0) (VG.Proof.MlKem.AArch64.eval_zero _ _) (fun hb' => ?_) (fun hb' => ?_)
  · exact ha (by unfold CvIn.G; rw [← h9]; simpa using hb') s₁ h₁ m₁ k₁
  · exact hb (fun hG => by unfold CvIn.G at hG; rw [← h9] at hG; simp [hG] at hb') s₁ h₁ m₁ k₁

/-- The inverse, without its doublings when the guard passes. -/
theorem cvInvG_ok [InvLaw] {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I)
    (hUn : wv s.mem I.B (slot (wk I.k) aU) (wk I.k) < 2 ^ (64 * ((max I.pl I.ql + 7) / 8)))
    (hMn : wv s.mem I.B (slot (wk I.k) aP) (wk I.k) < 2 ^ (64 * ((max I.pl I.ql + 7) / 8)))
    (hVM : wv s.mem I.B (slot (wk I.k) aV) (wk I.k) = wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) :
    WP isa (guarded (inverseAtS (nCalc sPl sQl) aU aV aX₁ aX₂ aP aT) (inverseAt (nCalc sPl sQl) aU aV aX₁ aX₂ aP aT))
      s fun t =>
      t.gpr .x0 = I.B ∧
      Frm I.B [ar (wk I.k) aU, ar (wk I.k) aV, ar (wk I.k) aX₁, ar (wk I.k) aX₂, ar (wk I.k) aT] s.mem t.mem ∧
      Keep (.x3 :: .x4 :: .x9 :: .x13 :: .x14 :: .x15 :: .x16 :: .x11 :: .x12 :: stepRegs) s t ∧
      (wv s.mem I.B (slot (wk I.k) aP) (wk I.k) % 2 = 1 → 1 < wv s.mem I.B (slot (wk I.k) aP) (wk I.k) →
        wv t.mem I.B (slot (wk I.k) aV) (wk I.k) =
          Nat.gcd (wv s.mem I.B (slot (wk I.k) aU) (wk I.k)) (wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) ∧
        ((wv s.mem I.B (slot (wk I.k) aP) (wk I.k) : Nat) : Int) ∣
          (wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) : Int) * 2 ^ I.E * wv s.mem I.B (slot (wk I.k) aU) (wk I.k) -
            wv t.mem I.B (slot (wk I.k) aV) (wk I.k) ∧
        wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) < wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) := by
  have hL1 := L.pl1; have hL2 := L.pl2; have hL3 := L.ql1; have hL4 := L.ql2; have hk2 := L.k2
  refine cvGuarded_ok h L (fun hG t ht hm k => ?_) (fun hG t ht hm k => ?_)
  · rw [← hm] at hUn hMn hVM
    refine WP.mono (InvLaw.inverseAtS_ok ht.ws (n := (max I.pl I.ql + 7) / 8)
      (iU := aU) (iV := aV) (iX₁ := aX₁) (iX₂ := aX₂) (iM := aP) (iT := aT) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by show _ ≤ (I.k + 7) / 8; omega) (by omega)
      (fun u hu h0 _ _ hm' => nCalc_ok hu h0 ht.ws.h256 (by omega) (by omega) (by rw [hm']; exact ht.args.pl)
        (by rw [hm']; exact ht.args.ql)) hUn hMn hVM) fun u ⟨u0, f, ku, v⟩ =>
      ⟨u0, by rw [← hm]; exact f, (k.trans ku).mono (by decide), fun hp hp1 => ?_⟩
    rw [hm] at v
    obtain ⟨v1, v2, v3⟩ := v hp hp1
    unfold CvIn.E
    rw [ite_eq_left hG, show 15 * ((max I.pl I.ql + 7) / 8) + 10 = 5 * (3 * ((max I.pl I.ql + 7) / 8) + 2) by omega]
    exact ⟨v1, v2, v3⟩
  · rw [← hm] at hUn hMn hVM
    refine WP.mono (InvLaw.inverseAt_ok ht.ws (n := (max I.pl I.ql + 7) / 8)
      (iU := aU) (iV := aV) (iX₁ := aX₁) (iX₂ := aX₂) (iM := aP) (iT := aT) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by show _ ≤ (I.k + 7) / 8; omega) (by omega)
      (fun u hu h0 _ _ hm' => nCalc_ok hu h0 ht.ws.h256 (by omega) (by omega) (by rw [hm']; exact ht.args.pl)
        (by rw [hm']; exact ht.args.ql)) hUn hMn hVM) fun u ⟨u0, f, ku, v⟩ =>
      ⟨u0, by rw [← hm]; exact f, (k.trans ku).mono (by decide), fun hp hp1 => ?_⟩
    rw [hm] at v
    obtain ⟨v1, v2, v3⟩ := v hp hp1
    unfold CvIn.E
    rw [ite_eq_right hG, Int.pow_zero, Int.mul_one]
    exact ⟨v1, v2, v3⟩

/-- `m ∣ y a - g` gives `m ∣ (y mod m) a - g`. -/
theorem dvd_mod_of_dvd {p y a g : Nat} (h : (p : Int) ∣ (y : Int) * a - g) :
    (p : Int) ∣ ((y % p : Nat) : Int) * a - g := by
  have e' : ((y % p : Nat) : Int) + p * ((y / p : Nat) : Int) = y := by exact_mod_cast Nat.mod_add_div y p
  have : ((y % p : Nat) : Int) * a - g = ((y : Int) * a - g) - p * (((y / p : Nat) : Int) * a) := by
    rw [← e', Int.add_mul, Int.mul_assoc]; omega
  rw [this]
  exact Int.dvd_sub h ⟨_, rfl⟩

/-- `invGcd`: `invPart` but `qTail`, `x₂ 2^E` the inverse. -/
theorem cvInvA_ok [InvLaw] {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) {c : Bool}
    (hc : mword s.mem I.B = mask c)
    (hcP : c = true → wv s.mem I.B (slot (wk I.k) aP) (wk I.k) % 2 = 1 ∧ 1 < wv s.mem I.B (slot (wk I.k) aP) (wk I.k))
    (hPl : wv s.mem I.B (slot (wk I.k) aP) (wk I.k) < 256 ^ I.pl)
    (hQl : wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) < 256 ^ I.ql) :
    WP isa (seqs invGcd) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mask (c && decide (Nat.gcd (wv s.mem I.B (slot (wk I.k) aQ) (wk I.k))
        (wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) = 1)) ∧
      (c = true → ((wv s.mem I.B (slot (wk I.k) aP) (wk I.k) : Nat) : Int) ∣
          (wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) : Int) * 2 ^ I.E * wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) -
            Nat.gcd (wv s.mem I.B (slot (wk I.k) aQ) (wk I.k)) (wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) ∧
        wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) < wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) ∧
      ∀ j, j = aP ∨ j = aQ ∨ j = aD → wv t.mem I.B (slot (wk I.k) j) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have k1 := L.k1
  have eM : Public.sMask = 22 := rfl
  have hmw : ∀ {m m' : Mem} {j L' : Nat}, Outside I.B (slot (wk I.k) j) L' m m' → L' ≤ 8 * (wk I.k + 2) →
      mword m' I.B = mword m I.B := fun {_ _ j _} o _ =>
    o.word (Or.inl (by have := hdr_lt_slot (wk I.k) j (show Public.sMask < 32 by decide); omega_arith))
      (by omega_arith)
  have wvw : ∀ {m m' : Mem} {j : Nat}, j < 16 →
      wv m' I.B (slot (wk I.k) j) (wk I.k + 2) = wv m I.B (slot (wk I.k) j) (wk I.k + 2) →
      wv m' I.B (slot (wk I.k) j) (wk I.k) = wv m I.B (slot (wk I.k) j) (wk I.k) := fun {m m' j} _ e => by
    have e1 := wv_add m I.B (slot (wk I.k) j) (wk I.k) 2
    have e2 := wv_add m' I.B (slot (wk I.k) j) (wk I.k) 2
    have l1 := wv_lt m I.B (slot (wk I.k) j) (wk I.k)
    have l2 := wv_lt m' I.B (slot (wk I.k) j) (wk I.k)
    rw [e] at e2
    have := congrArg (· % 2 ^ (64 * wk I.k)) (e1.symm.trans e2)
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2] at this
    exact this.symm
  -- The arrays a piece leaves: `ot j` from an `Outside` of another.
  have ot : ∀ {m m' : Mem} {j i Ln : Nat}, Outside I.B (slot (wk I.k) j) Ln m m' → Ln ≤ 8 * (wk I.k + 2) → i ≠ j →
      i < 16 → wv m' I.B (slot (wk I.k) i) (wk I.k) = wv m I.B (slot (wk I.k) i) (wk I.k) :=
    fun o hL hij hi => outside_arr o hL hij (by omega_arith) hi hZ hn
  simp only [invGcd]
  refine wp_seqs_append (by simp [invSetup]) (by simp) (WP.mono (invSetup_ok h L)
    fun s₇ ⟨h₇, m₇, vU0, vU₇, vV₇, vX₁, vX₂, p₇⟩ => ?_)
  have vP₇ := p₇ aP (.inl rfl)
  have vQ₇ := p₇ aQ (.inr (.inl rfl))
  have vD₇ := p₇ aD (.inr (.inr rfl))
  simp only [List.cons_append, List.nil_append]
  -- The inverse, at the primes' width.
  have hL1 := L.pl1; have hL2 := L.pl2; have hL3 := L.ql1; have hL4 := L.ql2; have hk2 := L.k2
  refine WP.seq (WP.mono (cvInvG_ok h₇ L (by rw [vU₇]; exact fits_nmax hQl (by omega))
    (by rw [vP₇]; exact fits_nmax hPl (by omega)) vV₇) fun s₈ ⟨_, f₈, k₈, hv₈⟩ => ?_)
  have h₈ := h₇.step f₈ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Mut.ofSlot _ _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have := h.ws.sl (j := aT) (by decide)
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> dsimp only
    · have := h.ws.sl (j := aU) (by decide); omega_arith
    · have := h.ws.sl (j := aV) (by decide); omega_arith
    · have := h.ws.sl (j := aX₁) (by decide); omega_arith
    · have := h.ws.sl (j := aX₂) (by decide); omega_arith
    · omega_arith) k₈ (by decide)
  rw [vU₇, vP₇] at hv₈
  have f8 : ∀ j, j < 16 → j ≠ aU → j ≠ aV → j ≠ aX₁ → j ≠ aX₂ → j ≠ aT →
      wv s₈.mem I.B (slot (wk I.k) j) (wk I.k) = wv s₇.mem I.B (slot (wk I.k) j) (wk I.k) := fun j hj h1 h2 h3 h4 h5 =>
    f₈.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> dsimp only
      · have := slot_sep (w := wk I.k) h1; omega_arith
      · have := slot_sep (w := wk I.k) h2; omega_arith
      · have := slot_sep (w := wk I.k) h3; omega_arith
      · have := slot_sep (w := wk I.k) h4; omega_arith
      · have := slot_sep (w := wk I.k) h5; omega_arith) (by have := h.ws.sl hj; omega_arith)
  have hm₈ : mword s₈.mem I.B = mask c := by
    have e8 : mword s₈.mem I.B = mword s₇.mem I.B := f₈.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> dsimp only
      · have := hdr_lt_slot (wk I.k) aU (show Public.sMask < 32 by decide); omega_arith
      · have := hdr_lt_slot (wk I.k) aV (show Public.sMask < 32 by decide); omega_arith
      · have := hdr_lt_slot (wk I.k) aX₁ (show Public.sMask < 32 by decide); omega_arith
      · have := hdr_lt_slot (wk I.k) aX₂ (show Public.sMask < 32 by decide); omega_arith
      · have := hdr_lt_slot (wk I.k) aT (show Public.sMask < 32 by decide); omega_arith) (by omega_arith)
    exact e8.trans (m₇.trans hc)
  -- `[c] := 1`, and the mask of `[v] = 1`.
  refine WP.seq (WP.mono (zeroA_ok h₈.ws (j := aC) (by decide)) fun s₉ ⟨z₉, o₉, _, _, _, k₉⟩ => ?_)
  have h₉ := h₈.arr (by decide) (Nat.le_refl _) o₉ k₉ (by decide)
  refine WP.seq (WP.mono (setOneA_ok h₉.ws (j := aC) (by decide)) fun s₁₀ ⟨m₁₀, k₁₀⟩ => ?_)
  have o₁₀ := writeW_outside s₉.mem I.B (1 : BitVec 64) (d := slot (wk I.k) aC) (by have := h.ws.sl (j := aC) (by decide); omega_arith)
  rw [← m₁₀] at o₁₀
  have h₁₀ := h₉.arr (by decide) (by omega_arith) o₁₀ k₁₀ (by decide)
  have vC : wv s₁₀.mem I.B (slot (wk I.k) aC) (wk I.k) = 1 := by
    rw [m₁₀, wv_low (by have := h.ws.w1; omega_arith), word_writeW_self,
      (writeW_outside s₉.mem I.B (1 : BitVec 64) (d := slot (wk I.k) aC) (by
        have := h.ws.sl (j := aC) (by decide); omega_arith)).wv (Or.inr (by omega_arith)) (by have := h.ws.sl (j := aC) (by decide); omega_arith)]
    have hz : ∀ q < wk I.k + 2, VG.Proof.Bignum.word s₉.mem I.B (slot (wk I.k) aC + 8 * q) = 0 :=
      (wv_eq_zero_iff _ _ _ _).mp z₉
    rw [wv_zero (n := wk I.k - 1) fun q hq => by
      have := hz (1 + q) (by omega_arith)
      rwa [show slot (wk I.k) aC + 8 * (1 + q) = slot (wk I.k) aC + 8 + 8 * q by omega_arith] at this]
    rfl
  have vV₁₀ : wv s₁₀.mem I.B (slot (wk I.k) aV) (wk I.k) = wv s₈.mem I.B (slot (wk I.k) aV) (wk I.k) := by
    rw [ot o₁₀ (by omega_arith) (by decide) (by decide), ot o₉ (Nat.le_refl _) (by decide) (by decide)]
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok h₁₀.ws (a := aV) (b := aC) (by decide) (by decide))
    fun s₁₁ ⟨hz₁₁, m₁₁, _, _, k₁₁⟩ => ?_)
  have h₁₁ := h₁₀.step (rs := []) (by rw [m₁₁]; exact Frm.refl _ _ _) (by simp) (by simp) k₁₁ (by decide)
  rw [vC, vV₁₀] at hz₁₁
  simp only [seqs]
  refine WP.mono (andZero_ok (c := c) h₁₁.ws (by rw [m₁₁]; exact (hmw o₁₀ (by omega_arith)).trans ((hmw o₉ (Nat.le_refl _)).trans hm₈)) hz₁₁)
    fun t ⟨⟨mt, _⟩, kt⟩ => ?_
  obtain ⟨ht, hmt, at'⟩ := h₁₁.mask mt kt (by decide)
  have tX : ∀ j, j < 16 → j ≠ aC → wv t.mem I.B (slot (wk I.k) j) (wk I.k) = wv s₈.mem I.B (slot (wk I.k) j) (wk I.k) :=
    fun j hj hne => by
      rw [wvw hj (at' j hj), m₁₁, ot o₁₀ (by omega_arith) hne hj, ot o₉ (Nat.le_refl _) hne hj]
  refine ⟨ht, ?_, fun hcT => ?_, fun j hj => ?_⟩
  · rw [hmt]
    congr 1
    cases c
    · simp
    · obtain ⟨hp, hp1⟩ := hcP rfl
      rw [(hv₈ hp hp1).1]
      simp
  · obtain ⟨hp, hp1⟩ := hcP hcT
    obtain ⟨e1, e2, e3⟩ := hv₈ hp hp1
    rw [tX aX₂ (by decide) (by decide)]
    exact ⟨e1 ▸ e2, e3⟩
  · have hj' : j < 16 := by rcases hj with rfl | rfl | rfl <;> decide
    rw [tX j hj' (by rcases hj with rfl | rfl | rfl <;> decide)]
    rcases hj with rfl | rfl | rfl
    · rw [f8 aP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), vP₇]
    · rw [f8 aQ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), vQ₇]
    · rw [f8 aD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), vD₇]

/-- `divisor j`: `[aC] := [j] - 1` for an odd `[j]`, and `[aU] := d`. -/
theorem cvDivisor_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) {j : Nat} (hj : j = aP ∨ j = aQ) :
    WP isa (seqs (divisor j)) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      (wv s.mem I.B (slot (wk I.k) j) (wk I.k) % 2 = 1 →
        wv t.mem I.B (slot (wk I.k) aC) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k) - 1) ∧
      wv t.mem I.B (slot (wk I.k) aU) (wk I.k) = wv s.mem I.B (slot (wk I.k) aD) (wk I.k) ∧
      Frm I.B [(slot (wk I.k) aC, 8 * (wk I.k + 2)), (slot (wk I.k) aU, 8 * (wk I.k + 2))] s.mem t.mem := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have k1 := L.k1
  have eM : Public.sMask = 22 := rfl
  have hj16 : j < 16 := by rcases hj with rfl | rfl <;> decide
  have hjC : j ≠ aC := by rcases hj with rfl | rfl <;> decide
  have hjU : j ≠ aU := by rcases hj with rfl | rfl <;> decide
  have hmw : ∀ {m m' : Mem} {i L' : Nat}, Outside I.B (slot (wk I.k) i) L' m m' → L' ≤ 8 * (wk I.k + 2) →
      mword m' I.B = mword m I.B := fun {_ _ i _} o _ =>
    o.word (Or.inl (by have := hdr_lt_slot (wk I.k) i (show Public.sMask < 32 by decide); omega_arith))
      (by omega_arith)
  have ot : ∀ {m m' : Mem} {j i Ln : Nat}, Outside I.B (slot (wk I.k) j) Ln m m' → Ln ≤ 8 * (wk I.k + 2) → i ≠ j →
      i < 16 → wv m' I.B (slot (wk I.k) i) (wk I.k) = wv m I.B (slot (wk I.k) i) (wk I.k) :=
    fun o hL hij hi => outside_arr o hL hij (by omega_arith) hi hZ hn
  have fr : ∀ {m m' : Mem} {i Ln : Nat}, i = aC ∨ i = aU → Outside I.B (slot (wk I.k) i) Ln m m' →
      Ln ≤ 8 * (wk I.k + 2) →
      Frm I.B [(slot (wk I.k) aC, 8 * (wk I.k + 2)), (slot (wk I.k) aU, 8 * (wk I.k + 2))] m m' :=
    fun {_ _ i _} hi o hL => Frm.of_outside (o.mono (o' := slot (wk I.k) i) (n' := 8 * (wk I.k + 2)) (Nat.le_refl _)
      (by omega_arith)) (by rcases hi with rfl | rfl <;> simp)
  simp only [divisor]
  -- `[c] := [j]`, minus one.
  refine WP.seq (WP.mono (zeroA_ok h.ws (j := aC) (by decide)) fun s₁ ⟨_, o₁, _, _, _, k₁⟩ => ?_)
  have h₁ := h.arr (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₁.ws (o := aC) (a := j) (by decide) hj16 (Ne.symm hjC)) fun s₂ ⟨c₂, o₂, _, _, k₂⟩ => ?_)
  have h₂ := h₁.arr (by decide) (by omega_arith) o₂ k₂ (by decide)
  rw [ot o₁ (Nat.le_refl _) hjC hj16] at c₂
  -- The low word.
  have sC := h.ws.sl (j := aC) (by decide)
  refine WP.seq (WP.mono (decA_ok h₂.ws (j := aC) (by decide)) fun s₃ ⟨m₃, k₃⟩ => ?_)
  have o₃ := writeW_outside s₂.mem I.B (VG.Proof.Bignum.word s₂.mem I.B (slot (wk I.k) aC) - 1)
    (d := slot (wk I.k) aC) (by omega_arith)
  rw [← m₃] at o₃
  have h₃ := h₂.arr (by decide) (by omega_arith) o₃ k₃ (by decide)
  -- `[c] = [j] - 1` for an odd `[j]`.
  have vC₃ : wv s₂.mem I.B (slot (wk I.k) aC) (wk I.k) % 2 = 1 →
      wv s₃.mem I.B (slot (wk I.k) aC) (wk I.k) = wv s₂.mem I.B (slot (wk I.k) aC) (wk I.k) - 1 := by
    have w1 := h.ws.w1
    have e3 := wv_low (m := s₃.mem) (B := I.B) (e := slot (wk I.k) aC) (w := wk I.k) (by omega_arith)
    have e2 := wv_low (m := s₂.mem) (B := I.B) (e := slot (wk I.k) aC) (w := wk I.k) (by omega_arith)
    have hw3 : VG.Proof.Bignum.word s₃.mem I.B (slot (wk I.k) aC) =
        VG.Proof.Bignum.word s₂.mem I.B (slot (wk I.k) aC) - 1 := by
      rw [m₃, word_writeW_self]
    have hup : wv s₃.mem I.B (slot (wk I.k) aC + 8) (wk I.k - 1) = wv s₂.mem I.B (slot (wk I.k) aC + 8) (wk I.k - 1) := by
      rw [m₃]; exact (writeW_outside s₂.mem I.B _ (by omega_arith)).wv (Or.inr (by omega_arith)) (by omega_arith)
    intro ho
    rw [e2] at ho ⊢
    have hodd : (VG.Proof.Bignum.word s₂.mem I.B (slot (wk I.k) aC)).toNat % 2 = 1 := by omega_arith
    have hsub : (VG.Proof.Bignum.word s₂.mem I.B (slot (wk I.k) aC) - 1).toNat =
        (VG.Proof.Bignum.word s₂.mem I.B (slot (wk I.k) aC)).toNat - 1 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega_arith)]; rfl
    rw [e3, hup, hw3, hsub]
    omega_arith
  rw [c₂] at vC₃
  -- `[u] := d`.
  refine WP.seq (WP.mono (zeroA_ok h₃.ws (j := aU) (by decide)) fun s₄ ⟨_, o₄, _, _, _, k₄⟩ => ?_)
  have h₄ := h₃.arr (by decide) (Nat.le_refl _) o₄ k₄ (by decide)
  refine WP.mono (copyA_ok h₄.ws (o := aU) (a := aD) (by decide) (by decide) (by decide)) fun s₅ ⟨c₅, o₅, _, _, k₅⟩ => ?_
  have h₅ := h₄.arr (by decide) (by omega_arith) o₅ k₅ (by decide)
  refine ⟨h₅, ?_, fun ho => ?_, ?_, ?_⟩
  · exact (hmw o₅ (by omega_arith)).trans ((hmw o₄ (Nat.le_refl _)).trans ((hmw o₃ (by omega_arith)).trans
      ((hmw o₂ (by omega_arith)).trans (hmw o₁ (Nat.le_refl _)))))
  · rw [ot o₅ (by omega_arith) (by decide) (by decide), ot o₄ (Nat.le_refl _) (by decide) (by decide)]
    exact vC₃ ho
  · rw [c₅, ot o₄ (Nat.le_refl _) (by decide) (by decide), ot o₃ (by omega_arith) (by decide) (by decide),
      ot o₂ (by omega_arith) (by decide) (by decide), ot o₁ (Nat.le_refl _) (by decide) (by decide)]
  · exact (((((fr (.inl rfl) o₁ (Nat.le_refl _)).trans (fr (.inl rfl) o₂ (by omega_arith))).trans
      (fr (.inl rfl) o₃ (by omega_arith))).trans (fr (.inr rfl) o₄ (Nat.le_refl _))).trans (fr (.inr rfl) o₅ (by omega_arith)))

/-- `divisor j ++ [divmod]`: `[aV] := d mod ([j] - 1)`, for an odd `[j]`. -/
theorem cvDivPart_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) {j : Nat} (hj : j = aP ∨ j = aQ) :
    WP isa (seqs (divisor j ++ [divmod aU aV aC aT])) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      (wv s.mem I.B (slot (wk I.k) j) (wk I.k) % 2 = 1 → 1 < wv s.mem I.B (slot (wk I.k) j) (wk I.k) →
        wv t.mem I.B (slot (wk I.k) aV) (wk I.k + 1) =
          wv s.mem I.B (slot (wk I.k) aD) (wk I.k) % (wv s.mem I.B (slot (wk I.k) j) (wk I.k) - 1)) ∧
      ∀ i, i = aP ∨ i = aQ ∨ i = aD ∨ i = aX₁ ∨ i = aX₂ →
        wv t.mem I.B (slot (wk I.k) i) (wk I.k) = wv s.mem I.B (slot (wk I.k) i) (wk I.k) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have eM : Public.sMask = 22 := rfl
  refine wp_seqs_append (by simp [divisor]) (by simp) (WP.mono (cvDivisor_ok h L hj) fun s₅ ⟨h₅, m₅, c₅, u₅, f₅⟩ => ?_)
  have back : ∀ i, i < 16 → i ≠ aC → i ≠ aU →
      wv s₅.mem I.B (slot (wk I.k) i) (wk I.k) = wv s.mem I.B (slot (wk I.k) i) (wk I.k) := fun i hi h1 h2 =>
    f₅.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only
      · have := slot_sep (w := wk I.k) h1; omega_arith
      · have := slot_sep (w := wk I.k) h2; omega_arith) (by have := h.ws.sl hi; omega_arith)
  -- `divmod`.
  simp only [seqs]
  refine WP.mono (divmod_ok h₅.ws
    (iQ := aU) (iR := aV) (iD := aC) (iT := aT) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun t ⟨_, f₆, k₆, hv₆⟩ => ?_
  have ht := h₅.step f₆ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Mut.ofSlot _ _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> exact h.ws.sl (by decide)) k₆ (by decide)
  have f6 : ∀ i, i < 16 → i ≠ aU → i ≠ aV → i ≠ aT →
      wv t.mem I.B (slot (wk I.k) i) (wk I.k) = wv s₅.mem I.B (slot (wk I.k) i) (wk I.k) := fun i hi h1 h2 h3 =>
    f₆.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only
      · have := slot_sep (w := wk I.k) h1; omega_arith
      · have := slot_sep (w := wk I.k) h2; omega_arith
      · have := slot_sep (w := wk I.k) h3; omega_arith) (by have := h.ws.sl hi; omega_arith)
  refine ⟨ht, ?_, fun ho h1 => ?_, fun i hi => ?_⟩
  · have e6 : mword t.mem I.B = mword s₅.mem I.B := f₆.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only
      · have := hdr_lt_slot (wk I.k) aU (show Public.sMask < 32 by decide); omega_arith
      · have := hdr_lt_slot (wk I.k) aV (show Public.sMask < 32 by decide); omega_arith
      · have := hdr_lt_slot (wk I.k) aT (show Public.sMask < 32 by decide); omega_arith) (by omega_arith)
    exact e6.trans m₅
  · have hC : wv s₅.mem I.B (slot (wk I.k) aC) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k) - 1 := c₅ ho
    have hU : wv s₅.mem I.B (slot (wk I.k) aU) (wk I.k) = wv s.mem I.B (slot (wk I.k) aD) (wk I.k) := u₅
    have hpos : 0 < wv s₅.mem I.B (slot (wk I.k) aC) (wk I.k) := by
      rw [hC]; omega_arith
    rw [(hv₆ hpos).1, hU, hC]
  · have hi16 : i < 16 := by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [f6 i hi16 (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide) (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide),
      back i hi16 (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide) (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)]

/-- `invPart`: `qInv` into `aX₂` and `gcd(q, p) = 1` and'ed into `sMask`,
for a mask that is set only if `p` is odd and above 1, and, when the guard
passes too, `p` of `n` words with its top bit set. -/
theorem cvInv_ok [InvLaw] {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) {c : Bool}
    (hc : mword s.mem I.B = mask c)
    (hcP : c = true → wv s.mem I.B (slot (wk I.k) aP) (wk I.k) % 2 = 1 ∧ 1 < wv s.mem I.B (slot (wk I.k) aP) (wk I.k))
    (hcG : c = true → I.G → 2 ^ (64 * (wk I.k / 2) - 1) ≤ wv s.mem I.B (slot (wk I.k) aP) (wk I.k) ∧
      wv s.mem I.B (slot (wk I.k) aP) (wk I.k) < 2 ^ (64 * (wk I.k / 2)))
    (hPl : wv s.mem I.B (slot (wk I.k) aP) (wk I.k) < 256 ^ I.pl)
    (hQl : wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) < 256 ^ I.ql) :
    WP isa (seqs invPart) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mask (c && decide (Nat.gcd (wv s.mem I.B (slot (wk I.k) aQ) (wk I.k))
        (wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) = 1)) ∧
      (c = true → ((wv s.mem I.B (slot (wk I.k) aP) (wk I.k) : Nat) : Int) ∣
          (wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) : Int) * wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) -
            Nat.gcd (wv s.mem I.B (slot (wk I.k) aQ) (wk I.k)) (wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) ∧
        wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) < wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) ∧
      ∀ j, j = aP ∨ j = aQ ∨ j = aD → wv t.mem I.B (slot (wk I.k) j) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have k1 := L.k1
  have k2 := L.k2
  unfold invPart
  refine wp_seqs_append (by simp [invGcd]) (by simp) (WP.mono (cvInvA_ok h L hc hcP hPl hQl)
    fun s₁ ⟨h₁, m₁, v₁, p₁⟩ => ?_)
  simp only [seqs]
  have P₁ := p₁ aP (.inl rfl)
  refine cvGuarded_ok h₁ L (fun hG t ht hm k => ?_) (fun hG t ht hm _ => WP.block_nil ?_)
  · -- The tail: `x₂ 2^K mod p`.
    obtain ⟨g16, g2, gpq, _⟩ := guard_zero (by omega) (by have := L.pl2; omega) (by have := L.ql2; omega) hG
    have hw2 : wk I.k % 2 = 0 := by unfold wk; omega
    have hw8 : 8 ≤ wk I.k := by unfold wk; omega
    have hnE : (max I.pl I.ql + 7) / 8 = wk I.k / 2 := by unfold wk; omega
    refine WP.mono (qTail_ok ht.ws hw2 hw8) fun u ⟨_, fu, ku, vu⟩ => ?_
    have mt : ∀ {m m' : Mem}, Frm I.B [ar (wk I.k) aX₂, ar (wk I.k) aC, ar (wk I.k) aT] m m' →
        mword m' I.B = mword m I.B := fun f => f.word_eq (fun r hr => by
      simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only <;>
        exact .inl (hdr_lt_slot _ _ (show Public.sMask < 32 by decide))) (by unfold Public.sMask sFn; omega_arith)
    have oj : ∀ {m m' : Mem} {j : Nat}, Frm I.B [ar (wk I.k) aX₂, ar (wk I.k) aC, ar (wk I.k) aT] m m' →
        j < 16 → j ≠ aX₂ → j ≠ aC → j ≠ aT → wv m' I.B (slot (wk I.k) j) (wk I.k) = wv m I.B (slot (wk I.k) j) (wk I.k) :=
      fun f hj h1 h2 h3 => f.wv_eq (fun r hr => by
        simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> dsimp only
        · have := slot_sep (w := wk I.k) h1; omega_arith
        · have := slot_sep (w := wk I.k) h2; omega_arith
        · have := slot_sep (w := wk I.k) h3; omega_arith) (by have := h.ws.sl hj; omega_arith)
    refine ⟨ht.step fu (fun r hr => by
        simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact Mut.ofSlot _ _ _) (fun r hr => by
        simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> dsimp only <;> exact h.ws.sl (by decide)) ku (by decide),
      by rw [mt fu, hm]; exact m₁, fun hcT => ?_, fun j hj => ?_⟩
    · obtain ⟨d1, d2⟩ := v₁ hcT
      obtain ⟨lo, hi⟩ := hcG hcT hG
      rw [← P₁] at lo hi d1 d2
      rw [← hm] at d1 d2 lo hi
      have hX := vu d2 lo hi
      rw [hX, hm]
      rw [hm, P₁] at d2
      unfold CvIn.E at d1
      rw [ite_eq_left hG, hnE] at d1
      rw [hm, P₁] at d1
      rw [P₁]
      exact ⟨dvd_mod_of_dvd (by push_cast; exact d1), Nat.mod_lt _ (by have := hcP hcT; omega)⟩
    · have hj16 : j < 16 := by rcases hj with rfl | rfl | rfl <;> decide
      rw [oj fu hj16 (by rcases hj with rfl | rfl | rfl <;> decide) (by rcases hj with rfl | rfl | rfl <;> decide)
        (by rcases hj with rfl | rfl | rfl <;> decide), hm, p₁ j hj]
  · -- No tail.
    refine ⟨ht, by rw [hm]; exact m₁, fun hcT => ?_, fun j hj => by rw [hm, p₁ j hj]⟩
    obtain ⟨d1, d2⟩ := v₁ hcT
    unfold CvIn.E at d1
    rw [ite_eq_right hG, Int.pow_zero, Int.mul_one] at d1
    rw [hm]; exact ⟨d1, d2⟩

end VG.Proof.Rsa.AArch64
