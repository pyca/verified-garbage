module

import VerifiedGarbage.Proof.Bignum.X86_64.PcMain
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Impl.Rsa.X86_64
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import Mathlib.Data.Int.GCD
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual

/-!
# `vg_rsa_public_precomputed` on x86-64: the computation

The load of `m` and `R² mod m` from `pre`, and the checks that refuse values
no modulus has (`pdLoadWith_ok`); then what the computation starts from for
values that pass them (`PdPre`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Precomputed
open VG.Proof.MlKem.X86_64

variable {M : Mont}

/-! ## The load and the checks -/

theorem check_eq (a top : BitVec 64) (c : Bool) :
    (a &&& 1 &&& mask c &&& 0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (top.toNat < BitVec.toNat (1 : BitVec 64)))) + 1 &&&
      (a &&& 1 &&& mask c &&& 0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (top.toNat < BitVec.toNat (1 : BitVec 64)))) + 1)
      == 0) = !(decide (a.toNat % 2 = 1) && c && decide (top ≠ 0)) := by
  have h1 : a &&& 1 = BitVec.ofNat 64 (a.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      BitVec.toNat_ofNat]
    omega_using []
  have h2 : decide (top.toNat < BitVec.toNat (1 : BitVec 64)) = decide (top = 0) :=
    decide_eq_decide.mpr ⟨fun h => BitVec.eq_of_toNat_eq (by
      rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl] at h; rw [show BitVec.toNat (0 : BitVec 64) = 0 from rfl]
      omega_using [h]),
      fun h => by subst h; decide⟩
  rw [h1, h2, decide_not]
  generalize decide (top = 0) = z
  rcases Nat.mod_two_eq_zero_or_one a.toNat with h | h <;> rw [h] <;> cases c <;> cases z <;> decide

/-- The checks' last block: ZF clear iff `m` (at `r10`, `w` words) is odd, its
top word is not zero, and `rbp` is the mask of a true `c`. -/
theorem checkBlk_ok {t : State} {B : Addr} {Z w : Nat} (hs : Scr t B Z) (h10 : t.gpr .r10 = off B (slot w aN))
    (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hZ : slot w 8 ≤ Z) {c : Bool}
    (hbp : t.gpr .rbp = mask c) :
    WP isa (.block [.mov .rax (.mem (at0 .r10)), .alu .and .rax (.imm 1), .alu .and .rax (.reg .rbp),
      .mov .rdx (.mem (ix .r10 .r12 (-8))), .alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx),
      .alu .add .rdx (.imm 1), .alu .and .rax (.reg .rdx), .alu .test .rax (.reg .rax)]) t fun t' =>
      t'.zf = some (!(decide ((word t.mem B (slot w aN)).toNat % 2 = 1) && c &&
        decide (word t.mem B (slot w aN + 8 * (w - 1)) ≠ 0))) ∧ t'.mem = t.mem ∧ Keep [.rax, .rdx] t t' := by
  have hn := hs.nowrap
  have := slot_le (w := w) (show aN < 8 by decide)
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t' => t'.zf = some (!(decide ((word t.mem B (slot w aN)).toNat % 2 = 1) && c &&
        decide (word t.mem B (slot w aN + 8 * (w - 1)) ≠ 0))) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨⟨hz, hm⟩, k⟩ => ⟨hz, hm, k⟩
  xrun [State.ea, ix, at0, addrm8 (b := off B (slot w aN)) rfl h12 (by omega_using [hw]), h10, hbp,
    show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
    hs.ld (show slot w aN + 8 * (w - 1) + 8 ≤ Z by omega_using [hZ, this]), hs.ld (show slot w aN + 8 ≤ Z by omega_using [hZ, this])]
  rw [check_eq]

/-- The load: `w`, the bases, `m` and `R² mod m` from `pre` (at `pp`, the
`2 w` words outside the working space), and ZF clear iff they pass the
checks. -/
theorem pdLoadWith_ok (cmp : Prog isa) (hc : CompareCorrect cmp) {s : State} {B : Addr} {Z k : Nat} {pp : Addr} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 9 ≤ k) (hk : k < 2 ^ 31)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hN : word s.mem B (8 * sN) = pp)
    (hpr : ∀ i < 2 * ((k + 7) / 8), InRegions (s.rd ++ s.wr) (off pp (8 * i)) 8)
    (hps : ∀ j < 16 * ((k + 7) / 8), Z ≤ ofs B (pp + BitVec.ofNat 64 j)) :
    WP isa (seqs (Precomputed.loadWith cmp)) s fun t =>
      wv t.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8) = wv s.mem pp 0 ((k + 7) / 8) ∧
      wv t.mem B (slot ((k + 7) / 8) aR2) ((k + 7) / 8) = wv s.mem pp (8 * ((k + 7) / 8)) ((k + 7) / 8) ∧
      word t.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) ∧
      (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j)) ∧
      t.zf = some (!(decide ((word t.mem B (slot ((k + 7) / 8) aN)).toNat % 2 = 1) &&
        decide (wv t.mem B (slot ((k + 7) / 8) aR2) ((k + 7) / 8) < wv t.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8)) &&
        decide (word t.mem B (slot ((k + 7) / 8) aN + 8 * ((k + 7) / 8 - 1)) ≠ 0))) ∧
      Frm B (pdLoadRanges ((k + 7) / 8)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  have h0 := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have hsN := slot_le (w := (k + 7) / 8) (show aN < 8 by decide)
  have hsR := slot_le (w := (k + 7) / 8) (show aR2 < 8 by decide)
  have hNR : slot ((k + 7) / 8) aN + 8 * ((k + 7) / 8 + 2) ≤ slot ((k + 7) / 8) aR2 := by
    unfold slot aN aR2; omega_using []
  have h0N : slot ((k + 7) / 8) 0 ≤ slot ((k + 7) / 8) aN := by unfold slot; omega_using []
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have hsl : ∀ r ∈ pdLoadRanges ((k + 7) / 8), r.1 + r.2 ≤ Z := fun r hr => (pdLoadRanges_le _ r hr).trans hZ
  -- A word of `pre` is outside the working space.
  have hpsep : ∀ e, e + 8 * ((k + 7) / 8) ≤ 16 * ((k + 7) / 8) → ∀ j < (k + 7) / 8, ∀ b < 8,
      Z ≤ ofs B (off pp (e + 8 * j) + BitVec.ofNat 64 b) := fun e he j hj b hb => by
    have := hps (e + 8 * j + b) (by omega_using [he, hj, hb])
    rwa [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  unfold Precomputed.loadWith
  refine WP.seq (WP.mono (setupHead_ok hs hdi hZ (by omega_using [hk]) hK hN)
    fun t₁ ⟨h12, _, hsi, hbx, hW₁, hb₁, hf₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hf₁' : Frm B (pdLoadRanges ((k + 7) / 8)) s.mem t₁.mem := hf₁.mono (by simp [pdLoadRanges])
  have hi₁ := InScr.of_frm hf₁' hsl
  -- `m`.
  refine WP.seq (WP.mono (copyWords_ok (S := pp) (eS := 0) (by rw [hsi]; simp [off]) hbx h12 (by omega_using [hk1]) (by omega_using [hk])
    (by omega_using [hZ, hn, hsR, hNR]) (fun j hj => by rw [k₁.2.1, k₁.2.2, Nat.zero_add]; exact hpr j (by omega_using [hj]))
    (fun j hj => by rw [k₁.2.2]; exact hs.st (by omega_using [hZ, hsR, hNR, hj]))
    (fun j hj b hb => Or.inr
        (by have := hpsep 0 (by omega_using []) j hj b hb; omega_using [hZ, hsR, hNR, this]))) fun t₂ ⟨hv₂, _, ho₂, k₂⟩ => ?_)
  have hm₂ : wv t₁.mem pp 0 ((k + 7) / 8) = wv s.mem pp 0 ((k + 7) / 8) :=
    wv_congr fun i hi => Mem.readW_congr fun b hb => hi₁ _ (hpsep 0 (by omega_using []) i hi b (by omega_using [hb]))
  rw [hm₂] at hv₂
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.2.2
  have hdi₂ : t₂.gpr .rdi = B := (k12.gpr (by decide)).trans hdi
  have hW₂ : word t₂.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) := by
    rw [ho₂.word (by omega_using [h8, h0N, eW]) (by omega_using [eW])]; exact hW₁
  have hb₂ : ∀ j < 8, word t₂.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j) := fun j hj => by
    rw [ho₂.word (d := 8 * sArr j) (by unfold sArr; omega_using [h8, h0N, hj]) (by unfold sArr; omega_using [hj])]; exact hb₁ j hj
  have hax8 : ∀ r : BitVec 64, r = BitVec.ofNat 64 ((k + 7) / 8) → r + r + (r + r) + (r + r + (r + r)) =
      BitVec.ofNat 64 (8 * ((k + 7) / 8)) := by
    rintro r rfl; simp only [BitVec.ofNat_add_ofNat]; congr 1; omega_using []
  -- `R² mod m`'s registers.
  refine WP.seq (WP.mono (WP.keep [.rax, .rsi, .rbx] (Q := fun t => t.gpr .rsi = off pp (8 * ((k + 7) / 8)) ∧
      t.gpr .rbx = off B (slot ((k + 7) / 8) aR2) ∧ t.mem = t₂.mem) (by
    unfold eightW
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.ld (d := 8 * sArr aR2)
        (by unfold sArr aR2; omega_using [hZ, h8, hsR, hNR, h0N]), hb₂ aR2 (by decide),
      (k₂.gpr (by decide)).trans h12, (k₂.gpr (by decide)).trans hsi, hax8 _ rfl]) rfl)
    fun t₃ ⟨⟨hsi₃, hbx₃, hm₃⟩, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  -- `R² mod m`.
  refine WP.seq (WP.mono (copyWords_ok hsi₃ hbx₃ ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12))
    (by omega_using [hk1]) (by omega_using [hk]) (by omega_using [hZ, hn, hsR])
    (fun j hj => by rw [k13.2.1, k13.2.2, show 8 * ((k + 7) / 8) + 8 * j = 8 * ((k + 7) / 8 + j) by omega_using []]
                    exact hpr _ (by omega_using [hj]))
    (fun j hj => by rw [k13.2.2]; exact hs.st (by omega_using [hZ, hsR, hj]))
    (fun j hj b hb => Or.inr (by have := hpsep (8 * ((k + 7) / 8)) (by omega_using []) j hj b hb; omega_using [hZ, hsR, this])))
    fun t₄ ⟨hv₄, _, ho₄, k₄⟩ => ?_)
  have hm₄ : wv t₃.mem pp (8 * ((k + 7) / 8)) ((k + 7) / 8) = wv s.mem pp (8 * ((k + 7) / 8)) ((k + 7) / 8) := by
    rw [hm₃]
    exact wv_congr fun i hi => Mem.readW_congr fun b hb => (ho₂ _ (Or.inr (by
      have := hpsep (8 * ((k + 7) / 8)) (by omega_using []) i hi b (by omega_using [hb]); omega_arith))).trans (hi₁ _ (by
      have := hpsep (8 * ((k + 7) / 8)) (by omega_using []) i hi b (by omega_using [hb]); omega_using [this]))
  rw [hm₄] at hv₄
  have k14 := k13.trans k₄
  have hs₄ := hs.congr k14.2.2
  have hdi₄ : t₄.gpr .rdi = B := (k14.gpr (by decide)).trans hdi
  have hN₄ : wv t₄.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8) = wv s.mem pp 0 ((k + 7) / 8) := by
    rw [ho₄.wv (by omega_using [hNR]) (by omega_using [hZ, hn, hsR, hNR]), hm₃]; exact hv₂
  have hb₄ : ∀ j < 8, word t₄.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j) := fun j hj => by
    rw [ho₄.word (d := 8 * sArr j) (by unfold sArr; omega_using [h8, hNR, h0N, hj]) (by unfold sArr; omega_using [hj]), hm₃]; exact hb₂ j hj
  have hW₄ : word t₄.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) := by
    rw [ho₄.word (by omega_using [h8, hNR, h0N, eW]) (by omega_using [eW]), hm₃]; exact hW₂
  have h12₄ : t₄.gpr .r12 = BitVec.ofNat 64 ((k + 7) / 8) :=
    (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12))
  have hbx₄ : t₄.gpr .rbx = off B (slot ((k + 7) / 8) aR2) := (k₄.gpr (by decide)).trans hbx₃
  -- The comparison's registers.
  refine WP.seq (WP.mono (WP.keep [.r10, .rbp] (Q := fun t => t.gpr .r10 = off B (slot ((k + 7) / 8) aN) ∧
      t.gpr .rbp = mask false ∧ t.mem = t₄.mem) (by
    xrun [State.ea, hdr, hdi₄, hdrOff, hs₄.ld (d := 8 * sArr aN)
        (by unfold sArr aN; omega_using [hZ, h8, hsR, hNR, h0N]), hb₄ aN (by decide)])
    rfl) fun t₅ ⟨⟨h10₅, hbp₅, hm₅⟩, k₅⟩ => ?_)
  have hs₅ := hs₄.congr k₅.2.2
  refine WP.seq (WP.mono (hc hs₅ ((k₅.gpr (by decide)).trans hbx₄) h10₅ ((k₅.gpr (by decide)).trans h12₄)
    hbp₅ (by omega_using [hk1]) (by omega_using [hk]) (by omega_using [hZ, hsR])
        (by omega_using [hZ, hsR, hNR])) fun t₆ ⟨hbp₆, hm₆, k₆⟩ => ?_)
  rw [hm₅] at hbp₆
  have hs₆ := hs₅.congr k₆.2.2
  rw [seqs_one]
  refine WP.mono (checkBlk_ok hs₆ ((k₆.gpr (by decide)).trans h10₅)
    ((k₆.gpr (by decide)).trans ((k₅.gpr (by decide)).trans h12₄)) (by omega_using [hk1]) hZ hbp₆) fun t ⟨hz, hm, k₇⟩ => ?_
  have hmm : t.mem = t₄.mem := by rw [hm, hm₆, hm₅]
  refine ⟨by rw [hmm]; exact hN₄, by rw [hmm]; exact hv₄, by rw [hmm]; exact hW₄,
    fun j hj => by rw [hmm]; exact hb₄ j hj, by rw [hz, hm₆, hm₅, hmm], ?_,
    ((((k14.trans k₅).trans k₆).trans k₇)).mono (by decide)⟩
  rw [hmm]
  have f₂ : Frm B (pdLoadRanges ((k + 7) / 8)) t₁.mem t₂.mem :=
    Frm.of_outside (ho₂.mono (o' := slot ((k + 7) / 8) aN) (n' := 8 * ((k + 7) / 8 + 2)) (Nat.le_refl _) (by omega_using []))
      (by simp [pdLoadRanges])
  have f₄ : Frm B (pdLoadRanges ((k + 7) / 8)) t₃.mem t₄.mem :=
    Frm.of_outside (ho₄.mono (o' := slot ((k + 7) / 8) aR2) (n' := 8 * ((k + 7) / 8 + 2)) (Nat.le_refl _) (by omega_using []))
      (by simp [pdLoadRanges])
  rw [hm₃] at f₄
  exact (hf₁'.trans f₂).trans f₄

/-! ## The computation -/


/-- What `rest` starts from: the header `entry` leaves, `m` and `R² mod m`
(here any `R < N`) in their arrays, as the checks accepted them. -/
structure PdPre (s : State) (B : Addr) (Z k : Nat) (op ep ip : Addr) (L : Nat) (eb xb : List Byte) (N R : Nat) :
    Prop where
  scr : Scr s B Z
  rdi : s.gpr .rdi = B
  z : slot ((k + 7) / 8) 8 ≤ Z
  k1 : 64 ≤ k
  k2 : k ≤ 1024
  hO : word s.mem B (8 * sOut) = op
  hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k
  hE : word s.mem B (8 * sE) = ep
  hL : word s.mem B (8 * sElen) = BitVec.ofNat 64 L
  hIn : word s.mem B (8 * sIn) = ip
  hW : word s.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8)
  hb : ∀ j < 8, word s.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j)
  n : wv s.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8) = N
  r : wv s.mem B (slot ((k + 7) / 8) aR2) ((k + 7) / 8) = R
  odd : N % 2 = 1
  n1 : 1 < N
  /-- The checks find the modulus' top word nonzero. -/
  big : 2 ^ (64 * ((k + 7) / 8 - 1)) ≤ N
  rlt : R < N
  x : Src s B Z ip xb
  e : Src s B Z ep eb
  xl : xb.length = k
  el : eb.length = L
  L1 : 1 ≤ L
  L2 : L ≤ k
  out : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1
  outSep : ∀ j < k, Z ≤ ofs B (op + BitVec.ofNat 64 j)
  /-- The public contract provides whole buffers, also permitting word loads. -/
  inSpan : InRegions (s.rd ++ s.wr) ip k
  outSpan : InRegions s.wr op k
  /-- `e` is odd and at least 3, as `vg_rsa_public_precomputed_checked` checks. -/
  eodd : Spec.Rsa.os2ip eb % 2 = 1
  e3 : 3 ≤ Spec.Rsa.os2ip eb

/-- What `Spec.Rsa.exponentValid` says of `e`. -/
theorem exponent_facts {e : Nat} (h : Spec.Rsa.exponentValid e = true) : e % 2 = 1 ∧ 3 ≤ e := by
  simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2⟩

/-- `x` with `x R ≡ X`, for `R` invertible modulo `N > 1`. -/
theorem exists_mont {R N : Nat} (hR : Nat.Coprime R N) (hN1 : 1 < N) (X : Nat) :
    ∃ x, X % N = x * R % N := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hR hN1
  refine ⟨X * m, ?_⟩
  rw [Nat.mul_assoc, Nat.mul_mod, Nat.mul_comm m R, hm, Nat.mul_one, Nat.mod_mod]

end VG.Proof.Bignum.X86_64
