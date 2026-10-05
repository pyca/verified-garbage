import VerifiedGarbage.Proof.MlDsa.Arm.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.Sample.Signs
import VerifiedGarbage.Impl.MlDsa.Arm.Sample.RejBounded
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejBoundedLoop`. -/
section

/-!
# ML-DSA on 32-bit ARM: the loop of `vg_mldsa_rej_bounded_poly`

The coefficient of an accepted half-byte, computed without a branch (`rbVal`),
is the one of `CoeffFromHalfByte`, modulo `q` (`rbF_eq`, by evaluation on the
accepted half-bytes); so a try does what `hbTry` does (`try_ok`, from its
pieces `tsgn_ok` and `acc_ok`, which the proof of constant time reuses), and
an iteration what `rbStep` does (`body_ok`). Between the pieces,
`Base` holds: the environment, the XOF output, the pointer `r0` to the byte of
iteration `t`, the count `r3` and the coefficients `L` stored, `j = |L|` in
`r2`.
-/

namespace VG.Proof.MlDsa.Arm.Sample.RejBounded

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Arm.RegUpd (gpr_setReg_self gpr_setReg_of_ne)
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample (hbTry rbStep rbFold coeffAddr Stored stored_nil zw ifT ifF hbTry_length
  halfByteOk_le rbFold_snoc rbFold_length_le)
open VG.Spec.MlDsa (Zq q ofInt coeffFromHalfByte halfByteOk)
open VG.Spec.Sha3 (bytesAt)

/-! ## The coefficient of a half-byte -/

/-- `x - 10` if `10 ≤ x`, as `csub 10` computes it. -/
def csubF10 (x : BitVec 32) : BitVec 32 := x - 10#32 + (x - 10#32) >>> 31 <<< 3 + (x - 10#32) >>> 31 <<< 1

/-- `x - 5` if `5 ≤ x`, as `csub 5` computes it. -/
def csubF5 (x : BitVec 32) : BitVec 32 := x - 5#32 + (x - 5#32) >>> 31 <<< 2 + (x - 5#32) >>> 31

/-- `x + q` if `x` is negative, as `addQNeg` computes it. -/
def aqF (x : BitVec 32) : BitVec 32 := x + x >>> 31 + x >>> 31 <<< 23 - x >>> 31 <<< 13

/-- What `rbVal η` computes of the half-byte `x`. -/
def rbF : Nat → BitVec 32 → BitVec 32
  | 2, x => VG.Proof.MlDsa.Arm.Sample.RejBounded.aqF (2 - VG.Proof.MlDsa.Arm.Sample.RejBounded.csubF5 (VG.Proof.MlDsa.Arm.Sample.RejBounded.csubF10 x))
  | _, x => VG.Proof.MlDsa.Arm.Sample.RejBounded.aqF (4 - x)

/-- The coefficient of an accepted half-byte. -/
def rbC (η b : Nat) : Int := if η = 2 then 2 - (b % 5 : Nat) else 4 - b

theorem coeffFromHalfByte_eq {η : Nat} (hη : η = 2 ∨ η = 4) (b : Nat) :
    coeffFromHalfByte η b = if b < rbBound η then some (VG.Proof.MlDsa.Arm.Sample.RejBounded.rbC η b) else none := by
  rcases hη with rfl | rfl <;> simp [coeffFromHalfByte, rbBound, VG.Proof.MlDsa.Arm.Sample.RejBounded.rbC]

theorem rbF_eq2 : ∀ b < 15, VG.Proof.MlDsa.Arm.Sample.RejBounded.rbF 2 (BitVec.ofNat 32 b) = zw (ofInt (VG.Proof.MlDsa.Arm.Sample.RejBounded.rbC 2 b)) := by decide

theorem rbF_eq4 : ∀ b < 9, VG.Proof.MlDsa.Arm.Sample.RejBounded.rbF 4 (BitVec.ofNat 32 b) = zw (ofInt (VG.Proof.MlDsa.Arm.Sample.RejBounded.rbC 4 b)) := by decide

theorem rbF_eq {η : Nat} (hη : η = 2 ∨ η = 4) {b : Nat} (hb : b < rbBound η) :
    VG.Proof.MlDsa.Arm.Sample.RejBounded.rbF η (BitVec.ofNat 32 b) = zw (ofInt (VG.Proof.MlDsa.Arm.Sample.RejBounded.rbC η b)) := by
  rcases hη with rfl | rfl
  · exact VG.Proof.MlDsa.Arm.Sample.RejBounded.rbF_eq2 b hb
  · exact VG.Proof.MlDsa.Arm.Sample.RejBounded.rbF_eq4 b hb

theorem hbTry_eq {η : Nat} (hη : η = 2 ∨ η = 4) (L : List Zq) (b : Nat) :
    hbTry η L b = if b < rbBound η then L ++ [ofInt (VG.Proof.MlDsa.Arm.Sample.RejBounded.rbC η b)] else L := by
  unfold hbTry
  rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.coeffFromHalfByte_eq hη]
  by_cases h : b < rbBound η <;> simp [h]

theorem halfByteOk_eq {η : Nat} (hη : η = 2 ∨ η = 4) (b : Nat) :
    halfByteOk η b = if b < rbBound η then 1 else 0 := by
  unfold halfByteOk
  rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.coeffFromHalfByte_eq hη]
  by_cases h : b < rbBound η <;> simp [h]

/-- Half-bytes accepted alike. -/
theorem bound_congr {η : Nat} (hη : η = 2 ∨ η = 4) {b₁ b₂ : Nat} (h : halfByteOk η b₁ = halfByteOk η b₂) :
    decide (rbBound η ≤ b₁) = decide (rbBound η ≤ b₂) := by
  rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.halfByteOk_eq hη, VG.Proof.MlDsa.Arm.Sample.RejBounded.halfByteOk_eq hη] at h
  by_cases h₁ : b₁ < rbBound η <;> by_cases h₂ : b₂ < rbBound η <;> simp [h₁, h₂] at h ⊢ <;> omega

theorem rbBound_le {η : Nat} (hη : η = 2 ∨ η = 4) : rbBound η ≤ 15 := by
  rcases hη with rfl | rfl <;> decide

theorem rbBound_enc {η : Nat} (hη : η = 2 ∨ η = 4) : encodable (BitVec.ofNat 32 (rbBound η)) = true := by
  rcases hη with rfl | rfl <;> decide

/-- `rbVal η`: the coefficient in `r10`, through `r9` and `r11`. -/
theorem rbVal_ok {η : Nat} (hη : η = 2 ∨ η = 4) (s : State) :
    WP isa (.block (rbVal η)) s fun s' => s'.gpr .r10 = VG.Proof.MlDsa.Arm.Sample.RejBounded.rbF η (s.gpr .r9) ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  rcases hη with rfl | rfl
  · simp only [rbVal, csub, Impl.MlDsa.Arm.Pack.addQNeg]
    run_block [and_true]
    exact ⟨rfl, fun r h9 h10 h11 => by simp [h9, h10, h11]⟩
  · simp only [rbVal, Impl.MlDsa.Arm.Pack.addQNeg]
    run_block [and_true]
    exact ⟨rfl, fun r _ h10 h11 => by simp [h10, h11]⟩

/-! ## The invariant between the pieces -/

/-- Iteration `t`, with the coefficients `L` stored, for the XOF output `X`. -/
structure Base (P : Sp) (σ : State) (X : List Byte) (t : Nat) (L : List Zq) (s : State) : Prop where
  env : Env P σ s
  out : bytesAt s.mem (P.at' 840) 544 = X
  r0 : s.gpr .r0 = P.scr + BitVec.ofNat 32 (840 + t)
  r3 : s.gpr .r3 = BitVec.ofNat 32 (544 - t)
  r2 : s.gpr .r2 = BitVec.ofNat 32 L.length
  len : L.length ≤ 256
  st : Stored s.mem P.A L

/-- `Base` after code that changes no memory and none of `r0`, `r2`, `r3`,
`r5` and `r6`. -/
theorem Base.regs {P : Sp} {σ : State} {X : List Byte} {t : Nat} {L : List Zq} {s s' : State}
    (h : VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ X t L s) (hg : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ X t L s' :=
  ⟨⟨hrd.trans h.env.rd, hwr.trans h.env.wr, hsp.trans h.env.sp,
      (hg .r5 (by decide) (by decide) (by decide) (by decide)).trans h.env.r5,
      (hg .r6 (by decide) (by decide) (by decide) (by decide)).trans h.env.r6,
      by rw [hm]; exact h.env.sav, by rw [hm]; exact h.env.savlr, by rw [hm]; exact h.env.frame⟩,
    by rw [hm]; exact h.out, (hg .r0 (by decide) (by decide) (by decide) (by decide)).trans h.r0,
    (hg .r3 (by decide) (by decide) (by decide) (by decide)).trans h.r3,
    (hg .r2 (by decide) (by decide) (by decide) (by decide)).trans h.r2, h.len, by rw [hm]; exact h.st⟩

/-! ## A try -/

/-- After the test of a try: `Z` is whether the half-byte `b` is rejected. -/
structure TS (η : Nat) (P : Sp) (σ : State) (X : List Byte) (t : Nat) (L : List Zq) (b : Nat) (v : BitVec 32)
    (s : State) : Prop where
  base : VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ X t L s
  r9 : s.gpr .r9 = BitVec.ofNat 32 b
  r8 : s.gpr .r8 = v
  z : s.z = decide (rbBound η ≤ b)

/-- The test of a try. -/
theorem tsgn_ok {η : Nat} (hη : η = 2 ∨ η = 4) {P : Sp} {σ : State} {X : List Byte} {t : Nat} {L : List Zq}
    {b : Nat} (hb : b < 16) {v : BitVec 32} {s : State} (h : VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ X t L s) (h9 : s.gpr .r9 = BitVec.ofNat 32 b)
    (h8 : s.gpr .r8 = v) :
    WP isa (.block [.dp .sub .r11 .r9 (.imm (BitVec.ofNat 32 (rbBound η))), .mov .r11 (.shifted .r11 .lsr 31),
      .cmp .r11 (.imm 0)]) s (VG.Proof.MlDsa.Arm.Sample.RejBounded.TS η P σ X t L b v) := by
  have e9 : (s.gpr .r9).toNat = b := by rw [h9, toNat_ofNat32 (by omega)]
  have hB := VG.Proof.MlDsa.Arm.Sample.RejBounded.rbBound_le hη
  refine WP.mono (sgn_ok s .r9 (.imm (BitVec.ofNat 32 (rbBound η))) (y := BitVec.ofNat 32 (rbBound η))
    (by simp only [Op2.eval, VG.Proof.MlDsa.Arm.Sample.RejBounded.rbBound_enc hη, ite_true]) (by omega) (by rw [toNat_ofNat32 (by omega)]; omega))
    fun s' ⟨hz, hg, hm, hrd, hwr, hsp⟩ => ⟨h.regs (fun r _ _ _ h11 => hg r h11) hm hrd hwr hsp,
      by rw [hg .r9 (by decide), h9], by rw [hg .r8 (by decide), h8], by rw [hz, e9, toNat_ofNat32 (by omega)]⟩

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

/-- The XOF output is apart from the output polynomial. -/
theorem out_disj : (⟨P.at' 840, 544⟩ : Region).Disjoint P.aR :=
  (hp.a_scr.sub_right (sub_scr (a := 840) (n := 544) (by omega))).symm

/-- An accepted half-byte: its coefficient stored. -/
theorem acc_ok {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat} {L : List Zq} {b : Nat} {v : BitVec 32}
    {s : State} (h : VG.Proof.MlDsa.Arm.Sample.RejBounded.TS η P σ X t L b v s) (hL : L.length < 256) (hb : b < rbBound η) :
    WP isa (.block (rbVal η ++ storeJ .r10)) s fun s' =>
      VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ X t (L ++ [ofInt (VG.Proof.MlDsa.Arm.Sample.RejBounded.rbC η b)]) s' ∧ s'.gpr .r8 = v := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.Arm.Sample.RejBounded.rbVal_ok hη s) fun s1 ⟨h10, hg, hm, hrd, hwr, hsp⟩ => ?_
  have b1 : VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ X t L s1 := h.base.regs (fun r _ h9 h10 h11 => hg r h9 h10 h11) hm hrd hwr hsp
  refine WP.mono (storeJ_stored hp b1.env (v := .r10) (by decide) b1.r2 hL b1.st (x := ofInt (VG.Proof.MlDsa.Arm.Sample.RejBounded.rbC η b))
    (by rw [h10, h.r9, VG.Proof.MlDsa.Arm.Sample.RejBounded.rbF_eq hη hb])) fun s2 ⟨hst, h2, hg2, _, he2, hf⟩ => ⟨⟨he2, ?_, ?_, ?_, h2, ?_, hst⟩, ?_⟩
  · rw [MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact VG.Proof.MlDsa.Arm.Sample.RejBounded.out_disj hp) (by omega)]
    exact b1.out
  · rw [hg2 .r0 (by decide) (by decide)]; exact b1.r0
  · rw [hg2 .r3 (by decide) (by decide)]; exact b1.r3
  · rw [List.length_append, List.length_singleton]; omega
  · rw [hg2 .r8 (by decide) (by decide), hg .r8 (by decide) (by decide) (by decide)]; exact h.r8

end

/-- A try: the half-byte `b` in `r9` tried, with `r8` kept. -/
theorem try_ok {P : Sp} {σ : State} (hp : SpOk P σ) {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat}
    {L : List Zq} {b : Nat} (hb : b < 16) {s : State} (h : VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ X t L s) (hL : L.length < 256)
    (h9 : s.gpr .r9 = BitVec.ofNat 32 b) :
    WP isa (rbTry η) s fun s' => VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ X t (hbTry η L b) s' ∧ s'.gpr .r8 = s.gpr .r8 := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.RejBounded.tsgn_ok hη hb h h9 rfl) fun s1 h1 => ?_)
  rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.hbTry_eq hη]
  refine WP.ite (decide (rbBound η ≤ b)) (by show some s1.z = _; rw [h1.z]) (fun hr => ?_) (fun hr => ?_)
  · simp only [decide_eq_true_eq] at hr
    rw [ifF (by omega)]
    exact WP.block_nil ⟨h1.base, h1.r8⟩
  · simp only [decide_eq_false_iff_not] at hr
    rw [ifT (by omega)]
    exact VG.Proof.MlDsa.Arm.Sample.RejBounded.acc_ok hp hη h1 hL (by omega)

end VG.Proof.MlDsa.Arm.Sample.RejBounded

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejBoundedBody`. -/
section

/-!
# ML-DSA on 32-bit ARM: an iteration of `vg_mldsa_rej_bounded_poly`

An iteration from `Base` with the coefficients `L`: the byte `z` of the XOF
output loaded, its low half-byte in `r9` and `Z` set iff `j ≥ 256` (`load_ok`,
leaving `LD`); if `j < 256`, the low half-byte tried (`try_ok`), the high
half-byte and the test of `j ≥ 256` again (`hi_ok`, leaving `HI`), and the
high half-byte tried if `j < 256` (`mid_ok`); then the step (`stepB_ok`): what
`rbStep` does (`body_ok`).
-/

namespace VG.Proof.MlDsa.Arm.Sample.RejBounded

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample (hbTry rbStep rbFold Stored ifT ifF hbTry_length halfByteOk_le rbFold_snoc
  rbFold_length_le)
open VG.Spec.MlDsa (Zq)
open VG.Spec.Sha3 (bytesAt)

/-- The low half-byte of a byte, as `rbLoad` computes it. -/
theorem lo_eq (z : Byte) : BitVec.setWidth 32 z <<< 28 >>> 28 = BitVec.ofNat 32 (z.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  have := z.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

/-- The high half-byte of a byte, as `rbHi` computes it. -/
theorem hi_eq (z : Byte) : BitVec.setWidth 32 z >>> 4 = BitVec.ofNat 32 (z.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  have := z.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-- The byte of iteration `t`. -/
abbrev zAt (X : List Byte) (t : Nat) : Byte := X.getD t 0

/-- After the loads: the byte `z` in `r8`, its low half-byte in `r9`, and `Z`
set iff `j ≥ 256`. -/
structure LD (P : Sp) (σ : State) (X : List Byte) (t : Nat) (L : List Zq) (s : State) : Prop where
  base : VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ X t L s
  r8 : s.gpr .r8 = BitVec.setWidth 32 (VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X t)
  r9 : s.gpr .r9 = BitVec.ofNat 32 ((VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X t).toNat % 16)
  z : s.z = decide (256 ≤ L.length)

/-- After the high half-byte: in `r9`, and `Z` set iff `j ≥ 256`. -/
structure HI (P : Sp) (σ : State) (X : List Byte) (t : Nat) (L : List Zq) (s : State) : Prop where
  base : VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ X t L s
  r8 : s.gpr .r8 = BitVec.setWidth 32 (VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X t)
  r9 : s.gpr .r9 = BitVec.ofNat 32 ((VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X t).toNat / 16)
  z : s.z = decide (256 ≤ L.length)

theorem lt31 {L : List Zq} (h : L.length ≤ 256) : L.length < 2 ^ 31 := by omega

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem ld3_ok {X : List Byte} {t : Nat} (ht : t < 544) {L : List Zq} {s : State} (h : VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ X t L s) :
    WP isa (.block [.ldrb .r8 .r0 0, .mov .r9 (.shifted .r8 .lsl 28), .mov .r9 (.shifted .r9 .lsr 28)]) s
      fun s' => s'.gpr .r8 = BitVec.setWidth 32 (VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X t) ∧ s'.gpr .r9 = BitVec.ofNat 32 ((VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X t).toNat % 16) ∧
        (∀ r, r ≠ .r8 → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp := by
  have ea : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = P.at' 840 + BitVec.ofNat 64 t := by
    rw [h.r0]
    show State.addr (P.scr + BitVec.ofNat 32 (840 + t) + 0#32) = _
    rw [BitVec.add_zero, at_eq hp (by omega), Offset.add_add]
  have hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 0)) 1 := by
    rw [ea, Offset.add_add]; exact inScrRd hp h.env (by omega)
  have hz : s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 0)) = VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X t := by
    have := MlKem.bytesAt_getD s.mem (P.at' 840) (len := 544) (i := t) (by omega)
    rw [h.out] at this
    rw [ea, ← this]
  have h0 : (0 : Nat) < 4096 := by decide
  run_block [hin, hz, h0, VG.Proof.MlDsa.Arm.Sample.RejBounded.lo_eq, and_true]
  refine ⟨trivial, trivial, fun r h8 h9 => ?_⟩
  simp [h8, h9]

/-- The loads. -/
theorem load_ok {X : List Byte} {t : Nat} (ht : t < 544) {L : List Zq} {s : State} (h : VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ X t L s) :
    WP isa (.block rbLoad) s (VG.Proof.MlDsa.Arm.Sample.RejBounded.LD P σ X t L) := by
  unfold rbLoad
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.Arm.Sample.RejBounded.ld3_ok hp ht h) fun s1 ⟨h8, h9, hg, hm, hrd, hwr, hsp⟩ => ?_
  have b1 : VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ X t L s1 := h.regs (fun r h8 h9 _ _ => hg r h8 h9) hm hrd hwr hsp
  refine WP.mono (jFull_ok s1 b1.r2 (VG.Proof.MlDsa.Arm.Sample.RejBounded.lt31 b1.len)) fun s2 ⟨hz, hg2, hm2, hrd2, hwr2, hsp2⟩ =>
    ⟨b1.regs (fun r _ _ _ h11 => hg2 r h11) hm2 hrd2 hwr2 hsp2, ?_, ?_, hz⟩
  · rw [hg2 .r8 (by decide), h8]
  · rw [hg2 .r9 (by decide), h9]

end

/-- The high half-byte, from the byte in `r8`. -/
theorem hi_ok {P : Sp} {σ : State} {X : List Byte} {t : Nat} {L : List Zq} {s : State} (h : VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ X t L s)
    (h8 : s.gpr .r8 = BitVec.setWidth 32 (VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X t)) : WP isa (.block rbHi) s (VG.Proof.MlDsa.Arm.Sample.RejBounded.HI P σ X t L) := by
  unfold rbHi
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (Q := fun s1 => s1 = s.setReg .r9 (BitVec.ofNat 32 ((VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X t).toNat / 16))) (by
    run_block [h8, VG.Proof.MlDsa.Arm.Sample.RejBounded.hi_eq]) fun s1 e1 => ?_
  subst e1
  have b1 : VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ X t L (s.setReg .r9 (BitVec.ofNat 32 ((VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X t).toNat / 16))) :=
    h.regs (fun r _ h9 _ _ => RegUpd.gpr_setReg_of_ne _ _ h9) rfl rfl rfl rfl
  refine WP.mono (jFull_ok _ b1.r2 (VG.Proof.MlDsa.Arm.Sample.RejBounded.lt31 b1.len)) fun s2 ⟨hz, hg2, hm2, hrd2, hwr2, hsp2⟩ =>
    ⟨b1.regs (fun r _ _ _ h11 => hg2 r h11) hm2 hrd2 hwr2 hsp2, ?_, ?_, hz⟩
  · rw [hg2 .r8 (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide), h8]
  · rw [hg2 .r9 (by decide), RegUpd.gpr_setReg_self]

/-- The coefficients after an iteration's tries, from the byte `z`. -/
theorem rbStep_eq (η : Nat) (L : List Zq) (z : Byte) :
    rbStep η L z = if L.length < 256 then
      (if (hbTry η L (z.toNat % 16)).length < 256 then hbTry η (hbTry η L (z.toNat % 16)) (z.toNat / 16)
        else hbTry η L (z.toNat % 16)) else L := rfl

theorem hbTry_length_le {η : Nat} {L : List Zq} (hL : L.length < 256) (b : Nat) : (hbTry η L b).length ≤ 256 := by
  rw [hbTry_length]; have := VG.Proof.MlDsa.Sample.halfByteOk_le η b; omega

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

/-- The tries of an iteration, from the loads. -/
theorem mid_ok {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat} {L : List Zq} {s : State}
    (h : VG.Proof.MlDsa.Arm.Sample.RejBounded.LD P σ X t L s) :
    WP isa (.ite .eq (.block []) (.seq (rbTry η) (.seq (.block rbHi) (.ite .eq (.block []) (rbTry η))))) s
      (VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ X t (rbStep η L (VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X t))) := by
  rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.rbStep_eq]
  refine WP.ite (decide (256 ≤ L.length)) (by show some s.z = _; rw [h.z]) (fun hr => ?_) (fun hr => ?_)
  · simp only [decide_eq_true_eq] at hr
    rw [ifF (by omega)]
    exact WP.block_nil h.base
  simp only [decide_eq_false_iff_not] at hr
  rw [ifT (by omega)]
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.RejBounded.try_ok hp hη (Nat.mod_lt _ (by decide)) h.base (by omega) h.r9) fun s1 ⟨b1, e8⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.RejBounded.hi_ok b1 (by rw [e8, h.r8])) fun s2 h2 => ?_)
  refine WP.ite (decide (256 ≤ (hbTry η L ((VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X t).toNat % 16)).length)) (by show some s2.z = _; rw [h2.z])
    (fun hr' => ?_) (fun hr' => ?_)
  · simp only [decide_eq_true_eq] at hr'
    rw [ifF (by omega)]
    exact WP.block_nil h2.base
  · simp only [decide_eq_false_iff_not] at hr'
    rw [ifT (by omega)]
    exact WP.mono (VG.Proof.MlDsa.Arm.Sample.RejBounded.try_ok hp hη (by have := (VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X t).isLt; omega) h2.base (by omega) h2.r9) fun _ h => h.1

end

theorem ofNat_pred {k : Nat} (hk : 0 < k) (hk' : k < 2 ^ 32) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, e1, Nat.mod_eq_of_lt hk']
  omega

/-- The step, to iteration `t + 1`: `Z` set iff it is the last. -/
theorem stepB_ok {P : Sp} {σ : State} {X : List Byte} {t : Nat} (ht : t < 544) {L : List Zq} {s : State}
    (h : VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ X t L s) :
    WP isa (.block (VG.Impl.MlDsa.Arm.Sample.step 1)) s fun s' => VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ X (t + 1) L s' ∧ s'.z = decide (t + 1 = 544) := by
  refine WP.mono (step_ok s (k := 1) (by decide)) fun s' ⟨h0, h3, hz, hg, hm, hrd, hwr, hsp⟩ => ?_
  have e3 : BitVec.ofNat 32 (544 - t) - 1 = BitVec.ofNat 32 (544 - (t + 1)) := by
    rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.ofNat_pred (by omega) (by omega)]; rfl
  refine ⟨⟨⟨hrd.trans h.env.rd, hwr.trans h.env.wr, hsp.trans h.env.sp,
      (hg .r5 (by decide) (by decide)).trans h.env.r5, (hg .r6 (by decide) (by decide)).trans h.env.r6,
      by rw [hm]; exact h.env.sav, by rw [hm]; exact h.env.savlr, by rw [hm]; exact h.env.frame⟩,
    by rw [hm]; exact h.out, by rw [h0, h.r0]; exact Offset.add_add_eq _ (by omega), by rw [h3, h.r3, e3],
    by rw [hg .r2 (by decide) (by decide)]; exact h.r2, h.len, by rw [hm]; exact h.st⟩, ?_⟩
  have ez := count_z (N := 544) (i := t) (k := 1) ht (by decide) (by decide)
  simp only [Nat.one_mul] at ez
  rw [hz, h.r3]; exact ez

/-- The coefficients after `t` iterations. -/
abbrev Lf (η : Nat) (X : List Byte) (t : Nat) : List Zq := rbFold η [] (X.take t)

theorem take_succ' (L : List Byte) {i : Nat} (h : i < L.length) : L.take (i + 1) = L.take i ++ [L.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem Lf_succ (η : Nat) {X : List Byte} (hX : X.length = 544) {t : Nat} (ht : t < 544) :
    VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X (t + 1) = rbStep η (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X t) (VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X t) := by
  simp only [VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf]
  rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.take_succ' _ (by omega), rbFold_snoc]

theorem Lf_length_le (η : Nat) (X : List Byte) (t : Nat) : (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X t).length ≤ 256 := rbFold_length_le (by simp) _

/-- An iteration: what `rbStep` does to the coefficients. -/
theorem body_ok {P : Sp} {σ : State} (hp : SpOk P σ) {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte}
    (hX : X.length = 544) {t : Nat} (ht : t < 544) {s : State} (h : VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ X t (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X t) s) :
    WP isa (rbBody η) s fun s' => VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ X (t + 1) (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X (t + 1)) s' ∧ s'.z = decide (t + 1 = 544) := by
  rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf_succ η hX ht]
  exact WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.RejBounded.load_ok hp ht h) fun _ h1 =>
    WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.RejBounded.mid_ok hp hη h1) fun _ h2 => VG.Proof.MlDsa.Arm.Sample.RejBounded.stepB_ok ht h2))

end VG.Proof.MlDsa.Arm.Sample.RejBounded

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejBoundedRun`. -/
section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_rej_bounded_poly`, correctness

The function runs in pieces: the prologue (`J0`), the sponge, whose output is
`H(ρ, 544)` (`J6`), the branch on `η`, and the loop for `η`, iteration `t` of
which starts from `Base` with the coefficients `rbFold` samples from the first
`t` bytes of output stored (`loop_ok`); then the end returns whether there are 256.
-/

namespace VG.Proof.MlDsa.Arm.Sample.RejBounded

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample (Stored stored_nil H_eq H_length)
open VG.Spec.MlDsa (Zq H)
open VG.Spec.Sha3 (bytesAt)

/-- `η`, the argument in `r1`. -/
abbrev etaOf (σ : State) : Nat := (σ.gpr .r1).toNat

/-- The call, from its entry state: `seed = r0`, `eta = r1`, `a = r2`,
`scratch = r3`. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .r0, 66, σ.gpr .r3, σ.gpr .r2, σ.gpr .r1⟩

/-- The XOF output the function uses: 544 bytes of `H(ρ)`. -/
abbrev X (σ : State) : List Byte := VG.Spec.MlDsa.H ((VG.Proof.MlDsa.Arm.Sample.RejBounded.spOf σ).msg σ) 544

theorem X_length (σ : State) : (VG.Proof.MlDsa.Arm.Sample.RejBounded.X σ).length = 544 := VG.Proof.MlDsa.Sample.H_length _ _

/-- The prologue. -/
theorem pro_ok {σ : State} (hp : SpOk (VG.Proof.MlDsa.Arm.Sample.RejBounded.spOf σ) σ) :
    WP isa (.block (pro .r3 .r2 (.reg .r1) (.imm 66) .r0)) σ (J0 (VG.Proof.MlDsa.Arm.Sample.RejBounded.spOf σ) σ) :=
  pro_rb hp rfl rfl rfl rfl rfl

section
variable {P : Sp} {σ : State}

/-- The loop's setup, from the sponge's output. -/
theorem init_ok {s : State} (h : J6 136 544 P σ s) :
    WP isa (.block [.dp .add .r0 .r6 (.imm 840), .mov .r2 (.imm 0), .mov .r3 (.imm 544)]) s
      (VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ (VG.Spec.MlDsa.H (P.msg σ) 544) 0 []) := by
  have e6 := h.env.r6
  refine WP.mono (Q := fun s' : State => s'.gpr .r0 = P.scr + BitVec.ofNat 32 840 ∧ s'.gpr .r2 = BitVec.ofNat 32 0 ∧
      s'.gpr .r3 = BitVec.ofNat 32 544 ∧ (∀ r, r ≠ .r0 → r ≠ .r2 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp) (by
    run_block [e6, and_true]
    exact ⟨rfl, trivial, trivial, fun r h0 h2 h3 => by simp [h0, h2, h3]⟩)
    fun s' ⟨h0, h2, h3, hg, hm, hrd, hwr, hsp⟩ => ⟨⟨hrd.trans h.env.rd, hwr.trans h.env.wr, hsp.trans h.env.sp,
      (hg .r5 (by decide) (by decide) (by decide)).trans h.env.r5,
      (hg .r6 (by decide) (by decide) (by decide)).trans h.env.r6,
      by rw [hm]; exact h.env.sav, by rw [hm]; exact h.env.savlr, by rw [hm]; exact h.env.frame⟩,
      by rw [hm, h.out, VG.Proof.MlDsa.Sample.H_eq], h0, h3, h2, by simp, stored_nil _ _⟩

/-- The loop for `η`. -/
theorem loop_ok (hp : SpOk P σ) {η : Nat} (hη : η = 2 ∨ η = 4) {s : State} (h : J6 136 544 P σ s) :
    WP isa (rbLoop η) s (VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ (VG.Spec.MlDsa.H (P.msg σ) 544) 544 (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η (VG.Spec.MlDsa.H (P.msg σ) 544) 544)) :=
  WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.RejBounded.init_ok h) fun _ h0 =>
    wp_loop_ne (fun t s => VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ (VG.Spec.MlDsa.H (P.msg σ) 544) t (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η (VG.Spec.MlDsa.H (P.msg σ) 544) t) s) (N := 544) (by decide)
      (fun _ ht _ hs => VG.Proof.MlDsa.Arm.Sample.RejBounded.body_ok hp hη (VG.Proof.MlDsa.Sample.H_length _ _) ht hs) (fun _ h => h) h0)

end

/-- The branch on `η`, and the loop for it. -/
theorem sel_ok {σ : State} (hp : SpOk (VG.Proof.MlDsa.Arm.Sample.RejBounded.spOf σ) σ) (hη : VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf σ = 2 ∨ VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf σ = 4) {s : State}
    (h : J6 136 544 (VG.Proof.MlDsa.Arm.Sample.RejBounded.spOf σ) σ s) :
    WP isa (.seq (.block [.cmp .r7 (.imm 2)]) (.ite .eq (rbLoop 2) (rbLoop 4))) s
      (VG.Proof.MlDsa.Arm.Sample.RejBounded.Base (VG.Proof.MlDsa.Arm.Sample.RejBounded.spOf σ) σ (VG.Proof.MlDsa.Arm.Sample.RejBounded.X σ) 544 (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf (VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf σ) (VG.Proof.MlDsa.Arm.Sample.RejBounded.X σ) 544)) := by
  have e7 := h.r7
  refine WP.seq (WP.mono (Q := fun s1 => s1 = subFlags s (σ.gpr .r1) 2) (by
    run_block [e7]) fun s1 e1 => ?_)
  subst e1
  have hj : J6 136 544 (VG.Proof.MlDsa.Arm.Sample.RejBounded.spOf σ) σ (subFlags s (σ.gpr .r1) 2) :=
    ⟨⟨h.env.rd, h.env.wr, h.env.sp, h.env.r5, h.env.r6, h.env.sav, h.env.savlr, h.env.frame⟩, h.r7, h.out⟩
  have hz : isa.eval .eq (subFlags s (σ.gpr .r1) 2) = some (decide (VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf σ = 2)) := by
    show some (σ.gpr .r1 - BitVec.ofNat 32 2 == 0) = _
    rw [cmp_z _ _ (by decide)]
  refine WP.ite _ hz (fun he => ?_) (fun he => ?_)
  · simp only [decide_eq_true_eq] at he
    rw [he]
    exact VG.Proof.MlDsa.Arm.Sample.RejBounded.loop_ok hp (η := 2) (.inl rfl) hj
  · simp only [decide_eq_false_iff_not] at he
    have e4 : VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf σ = 4 := hη.resolve_left he
    rw [e4]
    exact VG.Proof.MlDsa.Arm.Sample.RejBounded.loop_ok hp (η := 4) (.inr rfl) hj

/-- The whole function: the calling convention, `r0` whether the loop
sampled 256 coefficients, and those stored. -/
theorem correct {σ : State} (hp : SpOk (VG.Proof.MlDsa.Arm.Sample.RejBounded.spOf σ) σ) (hη : VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf σ = 2 ∨ VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf σ = 4) :
    WP isa rejBounded σ fun s' => abiPreserved σ s' ∧
      s'.gpr .r0 = (if (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf (VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf σ) (VG.Proof.MlDsa.Arm.Sample.RejBounded.X σ) 544).length = 256 then 1 else 0) ∧
      Stored s'.mem (VG.Proof.MlDsa.Arm.Sample.RejBounded.spOf σ).A (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf (VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf σ) (VG.Proof.MlDsa.Arm.Sample.RejBounded.X σ) 544) :=
  WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.RejBounded.pro_ok hp) fun _ h1 =>
    WP.seq (WP.mono (sponge_ok hp (rate := 136) (outlen := 544) (by decide) (by decide) (by decide) (by decide) h1)
      fun _ h2 => WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.RejBounded.sel_ok hp hη h2) fun _ h3 =>
        WP.mono (retEpi_ok hp h3.env h3.r2 h3.len) fun _ ⟨h0, hm, ha⟩ => ⟨ha, h0, by rw [hm]; exact h3.st⟩)))

end VG.Proof.MlDsa.Arm.Sample.RejBounded

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejBoundedCT`. -/
section

/-!
# ML-DSA on 32-bit ARM: the loop of `vg_mldsa_rej_bounded_poly`, constant time

Two runs of the loop for `η`, whose XOF outputs `X₁` and `X₂` have their
half-bytes accepted alike (`hbOks`, which the leak of the contract
determines), leak the same: at iteration `t`, both runs have sampled as many
coefficients (`rbFold_length_congr`), so the tests of `j ≥ 256` agree, and the
byte to read has its half-bytes accepted alike, so the tests of the tries
agree; the coefficients themselves are computed and stored by code that the
taint analysis proves leaks nothing of them but `j` and the output pointer
(`try_ct`). What each run is at each point comes from the correctness proof
(`relW`).
-/

namespace VG.Proof.MlDsa.Arm.Sample.RejBounded

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample (hbTry rbStep rbFold hbOks ifT ifF hbTry_length rbFold_length_congr)
open VG.Spec.MlDsa (Zq halfByteOk)

theorem nil_regs {R : State → State → Prop} : ∀ x y, R x y → ∀ r ∈ ([] : List Reg), x.gpr r = y.gpr r :=
  fun _ _ _ _ hr => absurd hr List.not_mem_nil

/-- The first block of a try, as the taint analysis sees it. -/
abbrev tsgn (η : Nat) : List Instr :=
  [.dp .sub .r11 .r9 (.imm (BitVec.ofNat 32 (rbBound η))), .mov .r11 (.shifted .r11 .lsr 31), .cmp .r11 (.imm 0)]

section
variable {P : Sp} {σ₁ σ₂ : State} (hp₁ : SpOk P σ₁) (hp₂ : SpOk P σ₂) {η : Nat} (hη : η = 2 ∨ η = 4)
  {h1 h2 h3 : VG.Taint.Hint VG.Arm.taint.T}
  (c1 : (VG.Arm.taint.check (Taint.ofRegs []) (.block (VG.Proof.MlDsa.Arm.Sample.RejBounded.tsgn η)) h1).isSome = true)
  (c2 : (VG.Arm.taint.check (Taint.ofRegs [.r2, .r5]) (.block (rbVal η ++ storeJ .r10)) h2).isSome = true)
  (c3 : (VG.Arm.taint.check (Taint.ofRegs []) (.block []) h3).isSome = true)
  {X₁ X₂ : List Byte}

/-- The eval of `.eq` is the flag `Z`. -/
theorem eval_eq (s : State) : isa.eval .eq s = some s.z := rfl

include hp₁ hp₂ hη c1 c2 c3 in
/-- A try, in two runs with as many coefficients and half-bytes accepted
alike. -/
theorem try_ct {t : Nat} {L₁ L₂ : List Zq} (hl : L₁.length = L₂.length) (hL : L₁.length < 256) {b₁ b₂ : Nat}
    (hb₁ : b₁ < 16) (hb₂ : b₂ < 16) (hok : halfByteOk η b₁ = halfByteOk η b₂) {v₁ v₂ : BitVec 32} :
    RelCT isa (fun a c => (VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₁ X₁ t L₁ a ∧ a.gpr .r9 = BitVec.ofNat 32 b₁ ∧ a.gpr .r8 = v₁) ∧
        (VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₂ X₂ t L₂ c ∧ c.gpr .r9 = BitVec.ofNat 32 b₂ ∧ c.gpr .r8 = v₂)) (rbTry η)
      fun a c => (VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₁ X₁ t (hbTry η L₁ b₁) a ∧ a.gpr .r8 = v₁) ∧
        (VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₂ X₂ t (hbTry η L₂ b₂) c ∧ c.gpr .r8 = v₂) := by
  have hbc := VG.Proof.MlDsa.Arm.Sample.RejBounded.bound_congr hη hok
  refine RelCT.seq (R := fun a c => VG.Proof.MlDsa.Arm.Sample.RejBounded.TS η P σ₁ X₁ t L₁ b₁ v₁ a ∧ VG.Proof.MlDsa.Arm.Sample.RejBounded.TS η P σ₂ X₂ t L₂ b₂ v₂ c)
    (relW (taintRel [] VG.Proof.MlDsa.Arm.Sample.RejBounded.nil_regs c1) fun a c h =>
      ⟨VG.Proof.MlDsa.Arm.Sample.RejBounded.tsgn_ok hη hb₁ h.1.1 h.1.2.1 h.1.2.2, VG.Proof.MlDsa.Arm.Sample.RejBounded.tsgn_ok hη hb₂ h.2.1 h.2.2.1 h.2.2.2⟩) ?_
  refine RelCT.ite (fun a c h => by rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.eval_eq, VG.Proof.MlDsa.Arm.Sample.RejBounded.eval_eq, h.1.z, h.2.z, hbc]) ?_ ?_
  · refine relW (taintRel [] VG.Proof.MlDsa.Arm.Sample.RejBounded.nil_regs c3) fun a c ⟨⟨t₁, t₂⟩, he⟩ => ?_
    have r₁ : rbBound η ≤ b₁ := by
      rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.eval_eq, t₁.z] at he; simpa using he
    have r₂ : rbBound η ≤ b₂ := by
      rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.eval_eq, t₁.z, hbc] at he; simpa using he
    rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.hbTry_eq hη, VG.Proof.MlDsa.Arm.Sample.RejBounded.hbTry_eq hη, ifF (by omega), ifF (by omega)]
    exact ⟨WP.block_nil ⟨t₁.base, t₁.r8⟩, WP.block_nil ⟨t₂.base, t₂.r8⟩⟩
  · refine relW (taintRel [.r2, .r5] (fun a c h r hr => ?_) c2) fun a c ⟨⟨t₁, t₂⟩, he⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1.base.r2, h.1.2.base.r2, hl]
      · rw [h.1.1.base.env.r5, h.1.2.base.env.r5]
    have r₁ : b₁ < rbBound η := by
      rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.eval_eq, t₁.z] at he; simpa using he
    have r₂ : b₂ < rbBound η := by
      rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.eval_eq, t₁.z, hbc] at he; simpa using he
    rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.hbTry_eq hη, VG.Proof.MlDsa.Arm.Sample.RejBounded.hbTry_eq hη, ifT r₁, ifT r₂]
    exact ⟨VG.Proof.MlDsa.Arm.Sample.RejBounded.acc_ok hp₁ hη t₁ hL r₁, VG.Proof.MlDsa.Arm.Sample.RejBounded.acc_ok hp₂ hη t₂ (by omega) r₂⟩

include hp₁ hp₂ hη c1 c2 c3 in
/-- The tries of an iteration, in two runs with as many coefficients and a
byte whose half-bytes are accepted alike. -/
theorem mid_ct {t : Nat} {L₁ L₂ : List Zq} (hl : L₁.length = L₂.length)
    (hok : hbOks η (VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₁ t) = hbOks η (VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₂ t)) :
    RelCT isa (fun a c => VG.Proof.MlDsa.Arm.Sample.RejBounded.LD P σ₁ X₁ t L₁ a ∧ VG.Proof.MlDsa.Arm.Sample.RejBounded.LD P σ₂ X₂ t L₂ c)
      (.ite .eq (.block []) (.seq (rbTry η) (.seq (.block rbHi) (.ite .eq (.block []) (rbTry η)))))
      fun a c => VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₁ X₁ t (rbStep η L₁ (VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₁ t)) a ∧ VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₂ X₂ t (rbStep η L₂ (VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₂ t)) c := by
  simp only [hbOks, Prod.mk.injEq] at hok
  rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.rbStep_eq, VG.Proof.MlDsa.Arm.Sample.RejBounded.rbStep_eq]
  have hz : ∀ a c, (VG.Proof.MlDsa.Arm.Sample.RejBounded.LD P σ₁ X₁ t L₁ a ∧ VG.Proof.MlDsa.Arm.Sample.RejBounded.LD P σ₂ X₂ t L₂ c) → isa.eval .eq a = isa.eval .eq c := fun a c h => by
    rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.eval_eq, VG.Proof.MlDsa.Arm.Sample.RejBounded.eval_eq, h.1.z, h.2.z, hl]
  by_cases hf : L₁.length < 256
  · rw [ifT hf, ifT (show L₂.length < 256 by omega)]
    refine RelCT.ite hz (RelCT.of_false fun a c ⟨h, he⟩ => by
      rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.eval_eq, h.1.z] at he; simp only [Option.some.injEq, decide_eq_true_eq] at he; omega) ?_
    have hm : (hbTry η L₁ ((VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₁ t).toNat % 16)).length = (hbTry η L₂ ((VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₂ t).toNat % 16)).length := by
      rw [hbTry_length, hbTry_length, hl, hok.1]
    refine RelCT.seq (R := fun (a c : State) =>
        (VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₁ X₁ t (hbTry η L₁ ((VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₁ t).toNat % 16)) a ∧ a.gpr .r8 = BitVec.setWidth 32 (VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₁ t)) ∧
        (VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₂ X₂ t (hbTry η L₂ ((VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₂ t).toNat % 16)) c ∧ c.gpr .r8 = BitVec.setWidth 32 (VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₂ t)))
      (RelCT.mono (VG.Proof.MlDsa.Arm.Sample.RejBounded.try_ct hp₁ hp₂ hη c1 c2 c3 hl hf (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) hok.1)
        (fun a c ⟨h, _⟩ => ⟨⟨h.1.base, h.1.r9, h.1.r8⟩, ⟨h.2.base, h.2.r9, h.2.r8⟩⟩) fun _ _ h => h) ?_
    refine RelCT.seq (R := fun (a c : State) => VG.Proof.MlDsa.Arm.Sample.RejBounded.HI P σ₁ X₁ t (hbTry η L₁ ((VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₁ t).toNat % 16)) a ∧
        VG.Proof.MlDsa.Arm.Sample.RejBounded.HI P σ₂ X₂ t (hbTry η L₂ ((VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₂ t).toNat % 16)) c)
      (relW (taintRel [] VG.Proof.MlDsa.Arm.Sample.RejBounded.nil_regs (by taint_decide)) fun a c h => ⟨VG.Proof.MlDsa.Arm.Sample.RejBounded.hi_ok h.1.1 h.1.2, VG.Proof.MlDsa.Arm.Sample.RejBounded.hi_ok h.2.1 h.2.2⟩) ?_
    have hz2 : ∀ a c, (VG.Proof.MlDsa.Arm.Sample.RejBounded.HI P σ₁ X₁ t (hbTry η L₁ ((VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₁ t).toNat % 16)) a ∧
        VG.Proof.MlDsa.Arm.Sample.RejBounded.HI P σ₂ X₂ t (hbTry η L₂ ((VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₂ t).toNat % 16)) c) → isa.eval .eq a = isa.eval .eq c := fun a c h => by
      rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.eval_eq, VG.Proof.MlDsa.Arm.Sample.RejBounded.eval_eq, h.1.z, h.2.z, hm]
    by_cases hm1 : (hbTry η L₁ ((VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₁ t).toNat % 16)).length < 256
    · rw [ifT hm1, ifT (show (hbTry η L₂ ((VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₂ t).toNat % 16)).length < 256 by omega)]
      refine RelCT.ite hz2 (RelCT.of_false fun a c ⟨h, he⟩ => by
        rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.eval_eq, h.1.z] at he; simp only [Option.some.injEq, decide_eq_true_eq] at he; omega) ?_
      refine RelCT.mono (VG.Proof.MlDsa.Arm.Sample.RejBounded.try_ct hp₁ hp₂ hη c1 c2 c3 hm hm1 (b₁ := (VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₁ t).toNat / 16)
        (b₂ := (VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₂ t).toNat / 16) (by have := (VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₁ t).isLt; omega) (by have := (VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₂ t).isLt; omega)
        hok.2) (fun a c ⟨h, _⟩ => ⟨⟨h.1.base, h.1.r9, h.1.r8⟩, ⟨h.2.base, h.2.r9, h.2.r8⟩⟩)
        fun _ _ h => ⟨h.1.1, h.2.1⟩
    · rw [ifF hm1, ifF (show ¬ (hbTry η L₂ ((VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₂ t).toNat % 16)).length < 256 by omega)]
      refine RelCT.ite hz2 ?_ (RelCT.of_false fun a c ⟨h, he⟩ => by
        rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.eval_eq, h.1.z] at he; simp only [Option.some.injEq, decide_eq_false_iff_not] at he; omega)
      exact relW (taintRel [] VG.Proof.MlDsa.Arm.Sample.RejBounded.nil_regs c3) fun a c h => ⟨WP.block_nil h.1.1.base, WP.block_nil h.1.2.base⟩
  · rw [ifF hf, ifF (show ¬ L₂.length < 256 by omega)]
    refine RelCT.ite hz ?_ (RelCT.of_false fun a c ⟨h, he⟩ => by
      rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.eval_eq, h.1.z] at he; simp only [Option.some.injEq, decide_eq_false_iff_not] at he; omega)
    exact relW (taintRel [] VG.Proof.MlDsa.Arm.Sample.RejBounded.nil_regs c3) fun a c h => ⟨WP.block_nil h.1.1.base, WP.block_nil h.1.2.base⟩

variable (hX₁ : X₁.length = 544) (hX₂ : X₂.length = 544)
  (oks : X₁.map (hbOks η) = X₂.map (hbOks η))

include oks in
theorem len_eq (t : Nat) : (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X₁ t).length = (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X₂ t).length :=
  rbFold_length_congr rfl (by rw [List.map_take, List.map_take, oks])

include hX₁ hX₂ oks in
theorem ok_eq {t : Nat} (ht : t < 544) : hbOks η (VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₁ t) = hbOks η (VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt X₂ t) := by
  have h := congrArg (fun L => L[t]?) oks
  simp only [List.getElem?_map, List.getElem?_eq_getElem (show t < X₁.length by omega),
    List.getElem?_eq_getElem (show t < X₂.length by omega), Option.map_some, Option.some.injEq] at h
  rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt, VG.Proof.MlDsa.Arm.Sample.RejBounded.zAt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show t < X₁.length by omega), List.getElem?_eq_getElem (show t < X₂.length by omega)]
  exact h

include hp₁ hp₂ hη c1 c2 c3 hX₁ hX₂ oks in
/-- An iteration. -/
theorem body_ct {t : Nat} (ht : t < 544) :
    RelCT isa (fun a c => VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₁ X₁ t (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X₁ t) a ∧ VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₂ X₂ t (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X₂ t) c) (rbBody η)
      fun a c => (VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₁ X₁ (t + 1) (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X₁ (t + 1)) a ∧ a.z = decide (t + 1 = 544)) ∧
        (VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₂ X₂ (t + 1) (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X₂ (t + 1)) c ∧ c.z = decide (t + 1 = 544)) := by
  rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf_succ η hX₁ ht, VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf_succ η hX₂ ht]
  refine RelCT.seq (R := fun a c => VG.Proof.MlDsa.Arm.Sample.RejBounded.LD P σ₁ X₁ t (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X₁ t) a ∧ VG.Proof.MlDsa.Arm.Sample.RejBounded.LD P σ₂ X₂ t (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X₂ t) c)
    (relW (taintRel [.r0] (fun a c h r hr => ?_) (by taint_decide)) fun a c h =>
      ⟨VG.Proof.MlDsa.Arm.Sample.RejBounded.load_ok hp₁ ht h.1, VG.Proof.MlDsa.Arm.Sample.RejBounded.load_ok hp₂ ht h.2⟩) ?_
  · rw [List.mem_singleton] at hr; subst hr; rw [h.1.r0, h.2.r0]
  refine RelCT.seq (VG.Proof.MlDsa.Arm.Sample.RejBounded.mid_ct hp₁ hp₂ hη c1 c2 c3 (VG.Proof.MlDsa.Arm.Sample.RejBounded.len_eq oks t) (VG.Proof.MlDsa.Arm.Sample.RejBounded.ok_eq hX₁ hX₂ oks ht)) ?_
  exact relW (taintRel [] VG.Proof.MlDsa.Arm.Sample.RejBounded.nil_regs (by taint_decide)) fun a c h => ⟨VG.Proof.MlDsa.Arm.Sample.RejBounded.stepB_ok ht h.1, VG.Proof.MlDsa.Arm.Sample.RejBounded.stepB_ok ht h.2⟩

include hp₁ hp₂ hη c1 c2 c3 hX₁ hX₂ oks in
/-- The loop. -/
theorem loop_ct :
    RelCT isa (fun a c => VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₁ X₁ 0 (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X₁ 0) a ∧ VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₂ X₂ 0 (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X₂ 0) c) (.loop (rbBody η) .ne)
      fun a c => VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₁ X₁ 544 (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X₁ 544) a ∧ VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₂ X₂ 544 (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X₂ 544) c := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := rbBody η) (c := .ne)
    (Q := fun a c => VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₁ X₁ 544 (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X₁ 544) a ∧ VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₂ X₂ 544 (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X₂ 544) c)
    (fun n a c => ∃ t, t < 544 ∧ n = 544 - t ∧ VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₁ X₁ t (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X₁ t) a ∧ VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₂ X₂ t (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X₂ t) c)
    (fun n => ?_) 544) (fun a c hab => ⟨0, by decide, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.exists_ fun t => ?_
  by_cases ht : t < 544
  · by_cases hn : n = 544 - t
    · refine RelCT.mono (P := fun a c => VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₁ X₁ t (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X₁ t) a ∧ VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₂ X₂ t (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η X₂ t) c)
        (VG.Proof.MlDsa.Arm.Sample.RejBounded.body_ct hp₁ hp₂ hη c1 c2 c3 hX₁ hX₂ oks ht) (fun _ _ hab => hab.2.2)
        fun a c ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · show some (!a.z) = some (!c.z); rw [z₁, z₂]
      · have : t + 1 = 544 := by
          have e' : (!a.z) = false := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ 544 := by
          have e' : (!a.z) = true := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨544 - (t + 1), by omega, t + 1, by omega, rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

end

end VG.Proof.MlDsa.Arm.Sample.RejBounded

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejBounded`. -/
section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_rej_bounded_poly`, constant time and `Verified`

Two runs from states that agree on the public data (the pointers, `η`, the
stack pointer, and which half-bytes of the XOF output are accepted,
`rejBoundedLeak`) leak the same trace: the prologue and the blocks around the
loop by the taint analysis, the sponge by `sponge_ct`, the branch on `η`
because `η` is public, and the loop iteration by iteration (`loop_ct`), since
the half-bytes of the first 544 bytes of output are accepted alike
(`leak_hbOks`).
-/

namespace VG.Proof.MlDsa.Arm.Sample

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample (hbOks leak_hbOks rejBounded_some rejBounded_none stored_polyIs H_length)
open VG.Spec.MlDsa (H rejBoundedContract rejBoundedSig rejBoundedLeak)
open VG.Spec.Sha3 (bytesAt)
open RejBounded

namespace RejBounded

/-- The test of `η = 2`. -/
theorem cmp_ok {P : Sp} {σ s : State} (h : J6 136 544 P σ s) :
    WP isa (.block [.cmp .r7 (.imm 2)]) s fun s' => J6 136 544 P σ s' ∧ s'.z = decide (P.prm.toNat = 2) := by
  have e7 := h.r7
  refine WP.mono (Q := fun s1 => s1 = subFlags s P.prm 2) (by run_block [e7]) fun s1 e1 => ?_
  subst e1
  refine ⟨⟨⟨h.env.rd, h.env.wr, h.env.sp, h.env.r5, h.env.r6, h.env.sav, h.env.savlr, h.env.frame⟩, h.r7, h.out⟩,
    ?_⟩
  show (P.prm - BitVec.ofNat 32 2 == 0) = _
  rw [cmp_z _ _ (by decide)]

section
variable {P : Sp} {σ₁ σ₂ : State} (hp₁ : SpOk P σ₁) (hp₂ : SpOk P σ₂)
include hp₁ hp₂

/-- The loop for `η`, from the sponge's output. -/
theorem rbLoop_ct {η : Nat} (hη : η = 2 ∨ η = 4)
    (oks : (VG.Spec.MlDsa.H (P.msg σ₁) 544).map (hbOks η) = (VG.Spec.MlDsa.H (P.msg σ₂) 544).map (hbOks η)) {h1 h2 h3 : VG.Taint.Hint VG.Arm.taint.T}
    (c1 : (VG.Arm.taint.check (Taint.ofRegs []) (.block (VG.Proof.MlDsa.Arm.Sample.RejBounded.tsgn η)) h1).isSome = true)
    (c2 : (VG.Arm.taint.check (Taint.ofRegs [.r2, .r5]) (.block (rbVal η ++ storeJ .r10)) h2).isSome = true)
    (c3 : (VG.Arm.taint.check (Taint.ofRegs []) (.block []) h3).isSome = true) :
    RelCT isa (fun a b => J6 136 544 P σ₁ a ∧ J6 136 544 P σ₂ b) (rbLoop η) fun a b =>
      VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₁ (VG.Spec.MlDsa.H (P.msg σ₁) 544) 544 (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η (VG.Spec.MlDsa.H (P.msg σ₁) 544) 544) a ∧
        VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₂ (VG.Spec.MlDsa.H (P.msg σ₂) 544) 544 (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf η (VG.Spec.MlDsa.H (P.msg σ₂) 544) 544) b :=
  RelCT.seq (relW (taintRel [.r6] (fun a b h r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [h.1.env.r6, h.2.env.r6]) (by taint_decide))
      fun a b h => ⟨VG.Proof.MlDsa.Arm.Sample.RejBounded.init_ok h.1, VG.Proof.MlDsa.Arm.Sample.RejBounded.init_ok h.2⟩)
    (VG.Proof.MlDsa.Arm.Sample.RejBounded.loop_ct hp₁ hp₂ hη c1 c2 c3 (VG.Proof.MlDsa.Sample.H_length _ _) (VG.Proof.MlDsa.Sample.H_length _ _) oks)

/-- The branch on `η`, and the loops. -/
theorem sel_ct (hη : P.prm.toNat = 2 ∨ P.prm.toNat = 4)
    (oks : (VG.Spec.MlDsa.H (P.msg σ₁) 544).map (hbOks P.prm.toNat) = (VG.Spec.MlDsa.H (P.msg σ₂) 544).map (hbOks P.prm.toNat)) :
    RelCT isa (fun a b => J6 136 544 P σ₁ a ∧ J6 136 544 P σ₂ b)
      (.seq (.block [.cmp .r7 (.imm 2)]) (.ite .eq (rbLoop 2) (rbLoop 4))) fun a b =>
      VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₁ (VG.Spec.MlDsa.H (P.msg σ₁) 544) 544 (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf P.prm.toNat (VG.Spec.MlDsa.H (P.msg σ₁) 544) 544) a ∧
        VG.Proof.MlDsa.Arm.Sample.RejBounded.Base P σ₂ (VG.Spec.MlDsa.H (P.msg σ₂) 544) 544 (VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf P.prm.toNat (VG.Spec.MlDsa.H (P.msg σ₂) 544) 544) b := by
  refine RelCT.seq (relW (taintRel [] VG.Proof.MlDsa.Arm.Sample.RejBounded.nil_regs (by taint_decide)) fun a b h => ⟨VG.Proof.MlDsa.Arm.Sample.RejBounded.cmp_ok h.1, VG.Proof.MlDsa.Arm.Sample.RejBounded.cmp_ok h.2⟩) ?_
  rcases hη with e | e
  · rw [e] at oks ⊢
    refine RelCT.ite (fun a b h => by rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.eval_eq, VG.Proof.MlDsa.Arm.Sample.RejBounded.eval_eq, h.1.2, h.2.2]) (RelCT.mono (VG.Proof.MlDsa.Arm.Sample.RejBounded.rbLoop_ct hp₁ hp₂ (η := 2) (.inl rfl) oks (by taint_decide) (by taint_decide)
      (by taint_decide)) (fun a b h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h) (RelCT.of_false fun a b ⟨h, he⟩ => by
        rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.eval_eq, h.1.2] at he; exact absurd he (by decide))
  · rw [e] at oks ⊢
    refine RelCT.ite (fun a b h => by rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.eval_eq, VG.Proof.MlDsa.Arm.Sample.RejBounded.eval_eq, h.1.2, h.2.2]) (RelCT.of_false fun a b ⟨h, he⟩ => by
        rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.eval_eq, h.1.2] at he; exact absurd he (by decide))
      (RelCT.mono (VG.Proof.MlDsa.Arm.Sample.RejBounded.rbLoop_ct hp₁ hp₂ (η := 4) (.inr rfl) oks (by taint_decide) (by taint_decide)
        (by taint_decide)) (fun a b h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h)

end

/-- The precondition, as `SpOk` and `η`. -/
theorem pre_of {s : State} (h : (rejBoundedContract Arm.abi 8).pre s) :
    SpOk (VG.Proof.MlDsa.Arm.Sample.RejBounded.spOf s) s ∧ (VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf s = 2 ∨ VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf s = 4) := by
  sig_pre [rejBoundedContract, rejBoundedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h8, -, hrd, hwr, d1, d2, d3, b1, b2, b3, f0, f2, f3, he⟩ := h
  exact ⟨⟨by rw [hrd]; exact List.mem_singleton_self _, hwr, d1, d2, d3, b1, b2, b3, f0, show (66 : Nat) < 2 ^ 32 by decide, f2, f3, h8⟩, he⟩

section
variable {σ₁ σ₂ : State} (hp₁ : SpOk (VG.Proof.MlDsa.Arm.Sample.RejBounded.spOf σ₁) σ₁) (hp₂ : SpOk (VG.Proof.MlDsa.Arm.Sample.RejBounded.spOf σ₂) σ₂) (hη : VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf σ₁ = 2 ∨ VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf σ₁ = 4)
  (hsp : σ₁.sp = σ₂.sp) (h0 : σ₁.gpr .r0 = σ₂.gpr .r0) (h1 : σ₁.gpr .r1 = σ₂.gpr .r1)
  (h2 : σ₁.gpr .r2 = σ₂.gpr .r2) (h3 : σ₁.gpr .r3 = σ₂.gpr .r3)
  (hl : rejBoundedLeak (VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf σ₁) ((VG.Proof.MlDsa.Arm.Sample.RejBounded.spOf σ₁).msg σ₁) = rejBoundedLeak (VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf σ₂) ((VG.Proof.MlDsa.Arm.Sample.RejBounded.spOf σ₂).msg σ₂))
include hp₁ hp₂ hη hsp h0 h1 h2 h3 hl

/-- The whole function, from two entry states that agree on the public data. -/
theorem all_ct : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) rejBounded fun _ _ => True := by
  have eP : VG.Proof.MlDsa.Arm.Sample.RejBounded.spOf σ₂ = VG.Proof.MlDsa.Arm.Sample.RejBounded.spOf σ₁ := by simp only [VG.Proof.MlDsa.Arm.Sample.RejBounded.spOf, h0, h1, h2, h3]
  rw [eP] at hp₂ hl
  have e1 : VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf σ₂ = VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf σ₁ := by rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf, VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf, h1]
  rw [e1] at hl
  have oks := leak_hbOks hl (B := 544) (by decide)
  refine RelCT.seq (relW (taintRel [.r0, .r1, .r2, .r3] (fun a b h r hr => ?_) (by taint_decide)) fun a b h =>
    ⟨by rw [h.1]; exact VG.Proof.MlDsa.Arm.Sample.RejBounded.pro_ok hp₁, by rw [h.2]; exact pro_rb hp₂ h0.symm h1.symm h2.symm h3.symm rfl⟩) ?_
  · rw [h.1, h.2]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  refine RelCT.seq (sponge_ct hp₁ hp₂ hsp (rate := 136) (outlen := 544) (by decide) (by decide) (by decide)
    (by decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (VG.Proof.MlDsa.Arm.Sample.RejBounded.sel_ct hp₁ hp₂ hη oks) ?_
  exact taintRel [.r6] (fun a b h r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [h.1.env.r6, h.2.env.r6]) (by taint_decide)

end

end RejBounded

end VG.Proof.MlDsa.Arm.Sample

namespace VG.Proof.MlDsa.Arm.Sample

open VG VG.Arm
open VG.Proof.MlKem.Arm (setWidth_append32)
open VG.Proof.MlDsa.Sample (rbFold rejBounded_some rejBounded_none stored_polyIs ifT ifF)
open VG.Spec.MlDsa (rejBoundedContract rejBoundedSig)
open RejBounded

/-- A state satisfying the precondition. -/
def rbSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 2 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 66⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem rejBounded_verified :
    Verified Arm.target Impl.MlDsa.Arm.Sample.rejBounded (rejBoundedContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ⟨VG.Proof.MlDsa.Arm.Sample.rbSat, ?_⟩⟩
  · obtain ⟨hp, hη⟩ := VG.Proof.MlDsa.Arm.Sample.RejBounded.pre_of hs
    obtain ⟨t, s', he, ha, h0, hst⟩ := VG.Proof.MlDsa.Arm.Sample.RejBounded.correct hp hη
    refine ⟨t, s', he, ha, ?_⟩
    have hL : VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf (VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf s) (VG.Proof.MlDsa.Arm.Sample.RejBounded.X s) 544 = rbFold (VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf s) [] (VG.Proof.MlDsa.Arm.Sample.RejBounded.X s) := by
      simp only [VG.Proof.MlDsa.Arm.Sample.RejBounded.Lf]; rw [List.take_of_length_le (by rw [VG.Proof.MlDsa.Arm.Sample.RejBounded.X_length])]
    rw [hL] at h0 hst
    sig_post [rejBoundedContract, rejBoundedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    rw [setWidth_append32, h0]
    by_cases hf : (rbFold (VG.Proof.MlDsa.Arm.Sample.RejBounded.etaOf s) [] (VG.Proof.MlDsa.Arm.Sample.RejBounded.X s)).length = 256
    · rw [ifT hf]
      obtain ⟨hred, hpoly⟩ := stored_polyIs hst hf
      exact ⟨fun _ => hred, .inl ⟨rfl, { Spec.MlDsa.minBounds with rejBounded := 544 }, by
        show Option.map _ (Spec.MlDsa.rejBoundedPoly _ 544 _) = _
        exact (rejBounded_some _ hf).trans (congrArg some hpoly.symm)⟩⟩
    · rw [ifF hf]
      exact ⟨fun h1 => absurd h1 (by decide), .inr ⟨rfl, by
        show Option.map _ (Spec.MlDsa.rejBoundedPoly _ 481 _) = none
        exact (congrArg (Option.map _) (rejBounded_none _ (B := 544) (by decide) hf)).trans rfl⟩⟩
  · obtain ⟨hp₁, hη⟩ := VG.Proof.MlDsa.Arm.Sample.RejBounded.pre_of h₁
    obtain ⟨hp₂, -⟩ := VG.Proof.MlDsa.Arm.Sample.RejBounded.pre_of h₂
    sig_pub [rejBoundedContract, rejBoundedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpub
    obtain ⟨hsp, hb, h0, h1, h2, h3⟩ := hpub
    exact (VG.Proof.MlDsa.Arm.Sample.RejBounded.all_ct hp₁ hp₂ hη hsp h0 h1 h2 h3 hb s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · sig_apply_check
    · decide +kernel
    · sig_reduce [rejBoundedContract, rejBoundedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlDsa.Arm.Sample

end
