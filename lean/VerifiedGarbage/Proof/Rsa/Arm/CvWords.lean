module

public import VerifiedGarbage.Proof.Rsa.Arm.CvFinish
public import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
public import VerifiedGarbage.Proof.Rsa.Arm.CvChecksB
public import VerifiedGarbage.Proof.Rsa.Arm.KcShape
public import VerifiedGarbage.Proof.Rsa.Arm.KcBodyW
public import VerifiedGarbage.Proof.Rsa.Arm.CvTaintW
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
import VerifiedGarbage.Proof.Bignum.Octets

/-! # `vg_rsa_crt_values` on ARMv7: a balanced key, by words

`shapeCv_ok`: Z exactly for a balanced key (`BalCv`); `midW_ok`: for one, the
checks and the values by words (`KeyDiv.mulLo`, `KeyDiv.divW`), which leave the
mask of `p` odd, `p q mod 2^(32 w) = n` and the inverse's gcd 1, and the
remainders of `d` modulo `p - 1` and `q - 1` with their top words made not zero
(`fixT`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

/-- A balanced key: `p` and `q` of `2 w` bytes, `w` even. -/
abbrev BalCv (s0 : State) : Prop := cvPl s0 = 2 * cvW s0 ∧ cvQl s0 = 2 * cvW s0 ∧ cvW s0 % 2 = 0

theorem StA.of_rest {s0 s t : State} (h : StA s0 s) {ws : List Reg} (r : Rest ws s t) (m : t.mem = s.mem)
    (h7 : .r7 ∉ ws := by decide) (h8 : .r8 ∉ ws := by decide) (h9 : .r9 ∉ ws := by decide) : StA s0 t :=
  ⟨h.base.of_rest r m, h.ws.rest r h7 h8 h9, m ▸ h.count, m ▸ h.n, m ▸ h.p, m ▸ h.q, m ▸ h.d,
    fun j hj => m ▸ h.zeros j hj⟩

/-- `shapeCv`: Z exactly for a balanced key; only `r0`–`r3`, `r11` and the flags change. -/
theorem shapeCv_ok {s0 s : State} (h : StA s0 s) :
    WP isa (.block shapeCv) s fun t => StA s0 t ∧ t.z = decide (BalCv s0) := by
  have pre := h.base.pre
  have kb := pre.kb
  have sp := pre.sp48
  rw [h.base.sp.symm] at sp
  unfold shapeCv VG.Impl.Rsa.Arm.KeyDiv.shape
  refine wp_ldrSp h.base.rA_mem sp (i := 3) (by decide) fun s1 u1 => ?_
  have b1 := h.base.of_rest (u1.rest (ws := [.r11]) (by simp)) u1.mem
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
  have b3 := b1.of_rest ((u2.rest (ws := [.r3]) (by simp)).trans (u3.rest (by simp))) (u3.mem.trans u2.mem)
  refine wp_ldrSp b3.rA_mem (by rw [u3.sp, u2.sp, u1.sp]; exact sp) (i := 5) (by decide) fun s4 u4 => ?_
  have b4 := b3.of_rest (u4.rest (ws := [.r0]) (by simp)) u4.mem
  refine wp_ldrSp b4.rA_mem (by rw [u4.sp, u3.sp, u2.sp, u1.sp]; exact sp) (i := 7) (by decide) fun s5 u5 => ?_
  refine wp_mov (op2_lsl (by decide)) fun s6 u6 => ?_
  refine wp_dp (op2_reg _ _) fun s7 u7 => ?_
  refine wp_dp (op2_reg _ _) fun s8 u8 => ?_
  refine wp_dp (op2_reg _ _) fun s9 u9 => ?_
  refine wp_dp (op2_imm (by decide)) fun s10 u10 => ?_
  refine wp_dp (op2_reg _ _) fun s11 u11 => ?_
  refine wp_cmp (op2_imm (by decide)) fun t ut zt => WP.block_nil ?_
  have R : Rest [.r0, .r1, .r2, .r3, .r11] s t :=
    (((((((((((u1.rest (by simp)).trans (u2.rest (by simp))).trans (u3.rest (by simp))).trans
      (u4.rest (by simp))).trans (u5.rest (by simp))).trans (u6.rest (by simp))).trans (u7.rest (by simp))).trans
      (u8.rest (by simp))).trans (u9.rest (by simp))).trans (u10.rest (by simp))).trans (u11.rest (by simp))).trans
      (ut.rest _)
  have m : t.mem = s.mem := by
    rw [ut.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨h.of_rest R m, ?_⟩
  have a3 : stackArg s 3 = stackArg s0 3 := h.base.arg (by decide)
  have a5 : stackArg s3 5 = stackArg s0 5 := b3.arg (by decide)
  have a7 : stackArg s4 7 = stackArg s0 7 := b4.arg (by decide)
  have e0 : s11.gpr .r0 = (((stackArg s0 5 ^^^ (((stackArg s0 3 + 3) >>> 2) <<< 1)) |||
      (stackArg s0 7 ^^^ (((stackArg s0 3 + 3) >>> 2) <<< 1))) ||| (((stackArg s0 3 + 3) >>> 2) &&& 1)) := by
    simp (disch := decide) only [u11.gpr, u10.gpr, u9.gpr, u8.gpr, u7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr,
      u1.gpr, u10.other, u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, dpVal, a3, a5, a7]
  rw [zt, e0]
  exact VG.Proof.Rsa.Arm.KeyCheck.shape_z kb.2

/-- The first comparison's quotient for a balanced key: `q` exactly when `p q mod 2^(32 w) = n`. -/
abbrev xW (s0 : State) : Nat :=
  if cvP s0 * cvQ s0 % 2 ^ (32 * cvW s0) = cvN s0 then cvQ s0 else cvQ s0 + 1

/-- `fixT` of `p - 1` and of `q - 1`, the divisors of the divisions by words. -/
abbrev fP (s0 : State) : Nat := VG.Proof.Rsa.fixT (cvW s0 / 2) (2 * (cvP s0 / 2))
abbrev fQ (s0 : State) : Nat := VG.Proof.Rsa.fixT (cvW s0 / 2) (2 * (cvQ s0 / 2))

theorem slot16 {s0 : State} {m : Mem} (pre : CvPre s0)
    (h : m.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0)) : slot m (cvB s0) 16 = cvW s0 := by
  have := pre.w16
  simp only [slot, w32]; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem bytes_lt_half {s0 : State} {b : List Byte} (hl : b.length = 2 * cvW s0) (hw : cvW s0 % 2 = 0) :
    Spec.Rsa.os2ip b < 2 ^ (32 * (cvW s0 / 2)) := by
  have := VG.Proof.Bignum.os2ip_lt b
  rw [hl, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  rw [show 32 * (cvW s0 / 2) = 8 * (2 * cvW s0) by omega]
  exact this

theorem BalCv.p_lt {s0 : State} (hB : BalCv s0) : cvP s0 < 2 ^ (32 * (cvW s0 / 2)) :=
  bytes_lt_half (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hB.1) hB.2.2

theorem BalCv.q_lt {s0 : State} (hB : BalCv s0) : cvQ s0 < 2 ^ (32 * (cvW s0 / 2)) :=
  bytes_lt_half (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hB.2.1) hB.2.2

/-- Before the product: the loads, and `p` odd. -/
structure SA (s0 s : State) : Prop where
  base : Base s0 s
  ws : Ws s (cvB s0) (cvZ s0) (cvW s0) nArr
  count : s.mem.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0)
  podd : slot s.mem (cvB s0) sPodd = cvP s0 % 2
  n : num s.mem (cvB s0) (cvW s0) aDQ = cvN s0
  p : num s.mem (cvB s0) (cvW s0) aP = cvP s0
  q : num s.mem (cvB s0) (cvW s0) aQ = cvQ s0
  d : num s.mem (cvB s0) (cvW s0) aD = cvD s0
  ddTop : w32 s.mem (State.addr (cvB s0)) (arr (cvW s0) aDD + 4 * cvW s0) = 0
  zeros : ∀ j ∈ [0, 2, 3, aZero, aOne], num s.mem (cvB s0) (cvW s0) j = 0

theorem SA.mulPre {s0 s : State} (h : SA s0 s) (hB : BalCv s0) :
    VG.Proof.Rsa.Arm.KeyDiv.MulPre (cvB s0) (cvZ s0) (cvW s0) nArr aP s :=
  ⟨h.ws, slot16 h.base.pre h.count, by rw [h.p]; exact hB.p_lt, h.zeros 0 (by decide)⟩

/-- `ctx`, and `p` odd. -/
theorem oddW_ok {s0 s : State} (h : StA s0 s) : WP isa (.block (ctx ++ bitOf sPodd aP)) s (SA s0) := by
  rw [← List.append_nil (bitOf sPodd aP), ← List.append_assoc]
  refine ctx_ok h.base fun t1 b1 h1 r1 m1 => ?_
  have fit := fun j (hj : j < nArr) => h1.fit64 (j := j) hj
  refine bitOf_ok h1 (j := aP) (sl := sPodd) (by decide) (by decide) (by decide) fun t2 h2 k2 e2 r2 =>
    WP.block_nil ?_
  have K1 : ∀ j, j < nArr → num t2.mem (cvB s0) (cvW s0) j = num s.mem (cvB s0) (cvW s0) j :=
    fun j hj => by rw [k2.num (by simp) (by decide) (fit j hj), m1]
  refine ⟨b1.keep k2 (by decide) (by decide) (by decide) r2.sp r2.rd r2.wr, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h.count, ← m1]
    exact BitVec.eq_of_toNat_eq (k2.slot (e := 16) (by decide) (by decide))
  · rw [e2, m1, h.p]
  · rw [K1 _ (by decide), h.n]
  · rw [K1 _ (by decide), h.p]
  · rw [K1 _ (by decide), h.q]
  · rw [K1 _ (by decide), h.d]
  · rw [k2.word (by simp only [S]; omega_arith) (by simp) (by decide) (fit _ (by decide)), m1]
    exact top_of_full (h.zeros aDD (by decide))
  · intro j hj
    have hj' : j < nArr := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [K1 _ hj']
    exact num_of_zero (h.zeros j (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide))

/-- The product `p q mod 2^(32 w)`. -/
theorem mulW_ok {s0 s : State} (h : SA s0 s) (hB : BalCv s0) :
    WP isa (VG.Impl.Rsa.Arm.KeyDiv.mulLo aDR aP aQ) s fun t => SA s0 t ∧
      num t.mem (cvB s0) (cvW s0) aDR = cvP s0 * cvQ s0 % 2 ^ (32 * cvW s0) := by
  have pre := h.base.pre
  have w16 := pre.w16
  have fit := fun j (hj : j < nArr) => h.ws.fit64 (j := j) hj
  refine WP.mono (VG.Proof.Rsa.Arm.KeyDiv.mulLo_ok h.ws (o := aDR) (x := aP) (y := aQ) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (slot16 pre h.count) hB.2.2 (by omega) h.p hB.p_lt
    h.q (h.zeros 0 (by decide))) fun t ⟨ht, e, k, r⟩ => ⟨?_, e⟩
  have K1 : ∀ j, j < nArr → j ≠ aDR → num t.mem (cvB s0) (cvW s0) j = num s.mem (cvB s0) (cvW s0) j :=
    fun j hj hn => k.num (by simpa using Ne.symm hn) (by decide) (fit j hj)
  refine ⟨h.base.keep k (by decide) (by decide) (by decide) r.sp r.rd r.wr, ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h.count]; exact BitVec.eq_of_toNat_eq (k.slot (e := 16) (by decide) (by decide))
  · rw [k.slot (by decide) (by decide), h.podd]
  · rw [K1 _ (by decide) (by decide), h.n]
  · rw [K1 _ (by decide) (by decide), h.p]
  · rw [K1 _ (by decide) (by decide), h.q]
  · rw [K1 _ (by decide) (by decide), h.d]
  · rw [k.word (by simp only [S]; omega_arith) (by decide) (by decide) (fit _ (by decide)), h.ddTop]
  · intro j hj
    have hj' : j < nArr ∧ j ≠ aDR := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [K1 _ hj'.1 hj'.2]; exact h.zeros j hj

/-- The two comparisons: `p q mod 2^(32 w) = n`, and the remainder 0. -/
theorem cmpW_ok {s0 s : State} (h : SA s0 s)
    (e : num s.mem (cvB s0) (cvW s0) aDR = cvP s0 * cvQ s0 % 2 ^ (32 * cvW s0)) :
    WP isa (seqs [eqS sE1 aDR aDQ aT1, eqS sE2 aZero aZero aT1]) s (StC1 s0 (xW s0) 0) := by
  have fit := fun j (hj : j < nArr) => h.ws.fit64 (j := j) hj
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h.ws (d := sE1) (a := aDR) (b := aDQ) (t := aT1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun t4 ⟨h4, k4, e4, r4⟩ => ?_
  refine WP.mono (eqS_ok h4 (d := sE2) (a := aZero) (b := aZero) (t := aT1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun t5 ⟨h5, k5, e5, r5⟩ => ?_
  have K : Keep (cvB s0) (cvW s0) [aT1] [sT, sE1, sE2] s.mem t5.mem := k4.mono.trans k5.mono
  have R : Rest opRegs s t5 := r4.trans r5
  have K1 : ∀ j, j < nArr → j ≠ aT1 → num t5.mem (cvB s0) (cvW s0) j = num s.mem (cvB s0) (cvW s0) j :=
    fun j hj hn => K.num (by simpa using Ne.symm hn) (by decide) (fit j hj)
  refine ⟨h.base.keep K (by decide) (by decide) (by decide) R.sp R.rd R.wr, h5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h.count]; exact BitVec.eq_of_toNat_eq (K.slot (e := 16) (by decide) (by decide))
  · rw [K.slot (by decide) (by decide), h.podd]
  · rw [k5.slot (by decide) (by decide), e4, e, h.n]
    by_cases c : cvP s0 * cvQ s0 % 2 ^ (32 * cvW s0) = cvN s0 <;> simp [xW, c]
  · rw [e5]; simp
  · rw [K1 _ (by decide) (by decide), h.p]
  · rw [K1 _ (by decide) (by decide), h.q]
  · rw [K1 _ (by decide) (by decide), h.d]
  · rw [K.word (by simp only [S]; omega_arith) (by decide) (by decide) (fit _ (by decide)), h.ddTop]
  · intro j hj
    have hj' : j < nArr ∧ j ≠ aT1 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl | rfl | rfl <;> decide
    rw [K1 _ hj'.1 hj'.2]
    exact h.zeros j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)

/-- Between the divisions by words: the mask, `q`, `d` and the zero array. -/
structure SW (s0 : State) (X₁ : Nat) (s : State) : Prop where
  base : Base s0 s
  ws : Ws s (cvB s0) (cvZ s0) (cvW s0) nArr
  count : s.mem.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0)
  q : num s.mem (cvB s0) (cvW s0) aQ = cvQ s0
  d : num s.mem (cvB s0) (cvW s0) aD = cvD s0
  zero : num s.mem (cvB s0) (cvW s0) 0 = 0
  mask : ∃ V, slot s.mem (cvB s0) sMask = (if maskOf (cvP s0) (cvQ s0) X₁ 0 V then 1 else 0) ∧
    (1 < cvM s0 → V = Nat.gcd (cvQ s0) (cvM s0) ∧
      (cvM s0 : Int) ∣ (num s.mem (cvB s0) (cvW s0) 3 : Int) * cvQ s0 - V ∧
      num s.mem (cvB s0) (cvW s0) 3 < cvM s0)

/-- `SW` after code that keeps every array but `js` (none of `aQ`, `aD`, 0, 3) and the header but
`ds`. -/
theorem SW.keep {s0 s t : State} {X₁ : Nat} (h : SW s0 X₁ s) {js ds : List Nat}
    (k : Keep (cvB s0) (cvW s0) js ds s.mem t.mem) (hjs : ∀ j ∈ js, j < nArr)
    (hj : ∀ j ∈ js, j ≠ aQ ∧ j ≠ aD ∧ j ≠ 0 ∧ j ≠ 3) (hds : ∀ d ∈ ds, 64 ≤ d ∧ d + 4 ≤ hdr ∧ (sMask + 4 ≤ d ∨ d + 4 ≤ sMask))
    (W : Ws t (cvB s0) (cvZ s0) (cvW s0) nArr) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
    SW s0 X₁ t := by
  have fit := fun j (hj : j < nArr) => h.ws.fit64 (j := j) hj
  have hd1 : ∀ d ∈ ds, d + 4 ≤ hdr := fun d hd => (hds d hd).2.1
  have K1 : ∀ i, i < nArr → (∀ j ∈ js, j ≠ i) → num t.mem (cvB s0) (cvW s0) i = num s.mem (cvB s0) (cvW s0) i :=
    fun i hi hn => k.num hn hd1 (fit i hi)
  obtain ⟨V, mV, iV⟩ := h.mask
  refine ⟨h.base.keep k hjs (fun d hd => Or.inr (hds d hd).1) hd1 sp rd wr, W, ?_,
    by rw [K1 _ (by decide) fun j hj' => (hj j hj').1, h.q], by rw [K1 _ (by decide) fun j hj' => (hj j hj').2.1, h.d],
    by rw [K1 _ (by decide) fun j hj' => (hj j hj').2.2.1, h.zero], V, ?_, ?_⟩
  · rw [← h.count]
    exact BitVec.eq_of_toNat_eq (k.slot (e := 16) (by decide) fun d hd => Or.inl (by have := (hds d hd).1; omega))
  · rw [k.slot (by decide) fun d hd => (hds d hd).2.2, mV]
  · rw [K1 _ (by decide) fun j hj' => (hj j hj').2.2.2]; exact iV

theorem SW.divPre {s0 s : State} {X₁ : Nat} (h : SW s0 X₁ s) {M : Nat}
    (hM : num s.mem (cvB s0) (cvW s0) aDD = VG.Proof.Rsa.fixT (cvW s0 / 2) M) (hMl : M < 2 ^ (32 * (cvW s0 / 2))) :
    VG.Proof.Rsa.Arm.KeyDiv.DivPre (cvB s0) (cvZ s0) (cvW s0) nArr aDD s := by
  have w16 := h.base.pre.w16
  have l := VG.Proof.Rsa.fixT_lt (k := cvW s0 / 2) (by omega) hMl
  refine ⟨h.ws, slot16 h.base.pre h.count, by rw [hM]; exact l,
    VG.Proof.Rsa.Arm.KeyCheck.top_word_pos (k := cvW s0 / 2 - 1) (n := cvW s0) (by omega) hM
      (by rw [show cvW s0 / 2 - 1 + 1 = cvW s0 / 2 by omega]; exact l) VG.Proof.Rsa.fixT_ge, h.zero⟩

/-- `[aDD] := fixT [d']` cleared of its low bit. -/
theorem setW_ok {s0 s : State} {X₁ : Nat} (h : SW s0 X₁ s) {d' : Nat} (hd : d' ∈ [aP, aQ])
    {Dv : Nat} (hD : num s.mem (cvB s0) (cvW s0) d' = Dv) (hDl : Dv < 2 ^ (32 * (cvW s0 / 2))) :
    WP isa (seqs [copy aDD d', .block (clrLow aDD ++ VG.Impl.Rsa.Arm.KeyDiv.fixTop aDD)]) s fun t =>
      SW s0 X₁ t ∧ num t.mem (cvB s0) (cvW s0) aDD = VG.Proof.Rsa.fixT (cvW s0 / 2) (2 * (Dv / 2)) ∧
      ∀ j, j < nArr → j ≠ aDD → num t.mem (cvB s0) (cvW s0) j = num s.mem (cvB s0) (cvW s0) j := by
  have w16 := h.base.pre.w16
  have fit := fun j (hj : j < nArr) => h.ws.fit64 (j := j) hj
  have hd' : d' < nArr ∧ d' ≠ aDD := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl <;> decide
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h.ws (o := aDD) (a := d') (by decide) hd'.1 (by decide) (Ne.symm hd'.2))
    fun t1 ⟨h1, k1, e1, r1, _⟩ => ?_
  refine clrLow_ok h1 (j := aDD) (by decide) (by decide) fun t2 h2 k2 e2 r2 _ => ?_
  have D2 : num t2.mem (cvB s0) (cvW s0) aDD = 2 * (Dv / 2) := by rw [e2, e1, hD]
  refine WP.mono (VG.Proof.Rsa.Arm.KeyDiv.fixTopW_ok h2 (m := aDD) (by decide) (by decide) D2
    (Nat.lt_of_le_of_lt (by omega) hDl) (by omega)) fun t ⟨ht, k3, e3, r3, _⟩ => ?_
  have K : Keep (cvB s0) (cvW s0) [aDD] [] s.mem t.mem := k1.trans (k2.trans k3)
  have R : Rest opRegs s t := r1.trans (r2.trans (r3.mono (by decide)))
  refine ⟨h.keep K (by decide) (by decide) (by decide) ht R.sp R.rd R.wr, e3, fun j hj hn =>
    K.num (by simpa using Ne.symm hn) (by decide) (fit j hj)⟩

/-- `[r] := [aD] mod [aDD]` by words. -/
theorem remW_ok {s0 s : State} {X₁ : Nat} (h : SW s0 X₁ s) {r : Nat} (hr : r ∈ [aDR2, aDR3]) {M : Nat}
    (hM : num s.mem (cvB s0) (cvW s0) aDD = VG.Proof.Rsa.fixT (cvW s0 / 2) M) (hMl : M < 2 ^ (32 * (cvW s0 / 2))) :
    WP isa (VG.Impl.Rsa.Arm.KeyDiv.divW aD r aDD aDQ aDT aT1) s fun t =>
      SW s0 X₁ t ∧ num t.mem (cvB s0) (cvW s0) r = cvD s0 % VG.Proof.Rsa.fixT (cvW s0 / 2) M ∧
      ∀ j, j < nArr → j ∉ [r, aDQ, aT1, aDT] → num t.mem (cvB s0) (cvW s0) j = num s.mem (cvB s0) (cvW s0) j := by
  have w16 := h.base.pre.w16
  have fit := fun j (hj : j < nArr) => h.ws.fit64 (j := j) hj
  have hr' : r < nArr ∧ r ≠ aD ∧ r ≠ aDD ∧ r ≠ aDQ ∧ r ≠ aT1 ∧ r ≠ aDT ∧ r ≠ 0 ∧ r ≠ aQ ∧ r ≠ 3 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> decide
  obtain ⟨W, c, ML, T0, z⟩ := h.divPre hM hMl
  refine WP.mono (VG.Proof.Rsa.Arm.KeyDiv.divW_ok W (a := aD) (r := r) (m := aDD) (t := aDQ) (nm := aDT)
    (u := aT1) (by decide) hr'.1 (by decide) (by decide) (by decide) (by decide) (by decide) hr'.2.1
    hr'.2.2.2.1 hr'.2.2.2.2.1 (by decide) (Ne.symm hr'.2.2.1) (by decide) (by decide)
    (Ne.symm hr'.2.2.2.2.2.1) (by decide) (by decide) (by decide) hr'.2.2.2.2.2.2.1 (by decide) (by decide)
    (by decide) (by omega) c hM (by rw [← hM]; exact ML) T0 z) fun t ⟨ht, et, _, kt, rt⟩ => ?_
  refine ⟨h.keep kt (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl <;> first | decide | exact hr'.1)
    (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl <;> first | decide | exact ⟨hr'.2.2.2.2.2.2.2.1, hr'.2.1, hr'.2.2.2.2.2.2.1,
        hr'.2.2.2.2.2.2.2.2⟩) (by decide) ht rt.sp rt.rd rt.wr, by rw [et, h.d], fun j hj hn =>
    kt.num (fun k hk e => hn (by subst e; exact hk)) (by decide) (fit j hj)⟩

/-- What a balanced key's checks leave: the mask of `p` odd, `p q mod 2^(32 w) = n` (for the
quotient `xW`, and the remainder 0) and the inverse, and the remainders by words. -/
def MidW (s0 t : State) : Prop :=
  StM s0 (xW s0) 0 t ∧
  num t.mem (cvB s0) (cvW s0) aDR2 = cvD s0 % fP s0 ∧ num t.mem (cvB s0) (cvW s0) aDR3 = cvD s0 % fQ s0

/-- The comparisons, the inverse and `checks`' set-up, the zero array again, and `fixT (p - 1)`. -/
theorem chunkW_ok [VG.Proof.Rsa.Arm.Keys.InvLaw] {s0 s : State} (h : SA s0 s) (hB : BalCv s0)
    (e : num s.mem (cvB s0) (cvW s0) aDR = cvP s0 * cvQ s0 % 2 ^ (32 * cvW s0)) :
    WP isa (seqs chunkW) s fun t => SW s0 (xW s0) t ∧ num t.mem (cvB s0) (cvW s0) aDD = fP s0 := by
  rw [show chunkW = [eqS sE1 aDR aDQ aT1, eqS sE2 aZero aZero aT1] ++ (invSetup ++ (checksB ++
    [copy 0 aZero, copy aDD aP, .block (clrLow aDD ++ VG.Impl.Rsa.Arm.KeyDiv.fixTop aDD)])) from rfl,
    wp_seqs_append (List.cons_ne_nil _ _) (by unfold invSetup; simp)]
  refine WP.mono (cmpW_ok h e) fun t1 h1 => ?_
  rw [wp_seqs_append (by unfold invSetup; simp) (by unfold checksB; simp)]
  refine WP.mono (invSetup_ok h1) fun t2 h2 => ?_
  rw [wp_seqs_append (by unfold checksB; simp) (List.cons_ne_nil _ _)]
  refine WP.mono (checksB_ok h2) fun t3 h3 => ?_
  have fit := fun j (hj : j < nArr) => h3.ws.fit64 (j := j) hj
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h3.ws (o := 0) (a := aZero) (by decide) (by decide) (by decide) (by decide))
    fun t4 ⟨h4, k4, e4, r4, _⟩ => ?_
  obtain ⟨V, mV, iV⟩ := h3.mask
  have s4 : SW s0 (xW s0) t4 := by
    refine ⟨h3.base.keep k4 (by decide) (by decide) (by decide) r4.sp r4.rd r4.wr, h4, ?_,
      by rw [k4.num (by decide) (by decide) (fit _ (by decide)), h3.q],
      by rw [k4.num (by decide) (by decide) (fit _ (by decide)), h3.d], by rw [e4, h3.zero], V, ?_, ?_⟩
    · rw [← h3.count]; exact BitVec.eq_of_toNat_eq (k4.slot (e := 16) (by decide) (by decide))
    · rw [k4.slot (by decide) (by decide), mV]
    · rw [k4.num (by decide) (by decide) (fit _ (by decide))]; exact iV
  exact WP.mono (setW_ok s4 (d' := aP) (by decide)
    (by rw [k4.num (by decide) (by decide) (fit _ (by decide)), h3.p]) hB.p_lt) fun t ⟨ht, et, _⟩ => ⟨ht, et⟩

theorem midW_eq : midW = seqs (([.block (ctx ++ bitOf sPodd aP), VG.Impl.Rsa.Arm.KeyDiv.mulLo aDR aP aQ] :
    List (Prog isa)) ++ (chunkW ++ ([VG.Impl.Rsa.Arm.KeyDiv.divW aD aDR2 aDD aDQ aDT aT1, copy aDD aQ,
      .block (clrLow aDD ++ VG.Impl.Rsa.Arm.KeyDiv.fixTop aDD), VG.Impl.Rsa.Arm.KeyDiv.divW aD aDR3 aDD aDQ aDT aT1] :
        List (Prog isa)))) :=
  rfl

/-- After the first division by words. -/
theorem div2W_ok {s0 s : State} (h : SW s0 (xW s0) s) (hB : BalCv s0)
    (e : num s.mem (cvB s0) (cvW s0) aDD = fP s0) :
    WP isa (VG.Impl.Rsa.Arm.KeyDiv.divW aD aDR2 aDD aDQ aDT aT1) s fun t =>
      SW s0 (xW s0) t ∧ num t.mem (cvB s0) (cvW s0) aDR2 = cvD s0 % fP s0 :=
  WP.mono (remW_ok h (r := aDR2) (by decide) e (Nat.lt_of_le_of_lt (by omega) hB.p_lt)) fun _ ⟨ht, et, _⟩ => ⟨ht, et⟩

theorem setQW_ok {s0 s : State} (h : SW s0 (xW s0) s) (hB : BalCv s0)
    (e : num s.mem (cvB s0) (cvW s0) aDR2 = cvD s0 % fP s0) :
    WP isa (seqs [copy aDD aQ, .block (clrLow aDD ++ VG.Impl.Rsa.Arm.KeyDiv.fixTop aDD)]) s fun t =>
      SW s0 (xW s0) t ∧ num t.mem (cvB s0) (cvW s0) aDR2 = cvD s0 % fP s0 ∧
      num t.mem (cvB s0) (cvW s0) aDD = fQ s0 :=
  WP.mono (setW_ok h (d' := aQ) (by decide) h.q hB.q_lt) fun _ ⟨ht, et, k⟩ =>
    ⟨ht, by rw [k _ (by decide) (by decide), e], et⟩

theorem div3W_ok {s0 s : State} (h : SW s0 (xW s0) s) (hB : BalCv s0)
    (e2 : num s.mem (cvB s0) (cvW s0) aDR2 = cvD s0 % fP s0) (e : num s.mem (cvB s0) (cvW s0) aDD = fQ s0) :
    WP isa (VG.Impl.Rsa.Arm.KeyDiv.divW aD aDR3 aDD aDQ aDT aT1) s (MidW s0) :=
  WP.mono (remW_ok h (r := aDR3) (by decide) e (Nat.lt_of_le_of_lt (by omega) hB.q_lt)) fun _ ⟨ht, et, k⟩ =>
    ⟨⟨ht.base, ht.mask⟩, by rw [k _ (by decide) (by decide), e2], et⟩

/-- A balanced key's checks and values. -/
theorem midW_ok [VG.Proof.Rsa.Arm.Keys.InvLaw] {s0 s : State} (h : StA s0 s) (hB : BalCv s0) :
    WP isa midW s (MidW s0) := by
  rw [midW_eq, wp_seqs_append (List.cons_ne_nil _ _) (by simp)]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (oddW_ok h) fun t1 h1 => ?_
  refine WP.mono (mulW_ok h1 hB) fun t2 ⟨h2, e2⟩ => ?_
  rw [wp_seqs_append (by simp) (List.cons_ne_nil _ _)]
  refine WP.mono (chunkW_ok h2 hB e2) fun t3 ⟨h3, e3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (div2W_ok h3 hB e3) fun t4 ⟨h4, e4⟩ => ?_
  rw [show ∀ a b c : Prog isa, seqs [a, b, c] = seqs ([a, b] ++ [c]) from fun _ _ _ => rfl,
    wp_seqs_append (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)]
  exact WP.mono (setQW_ok h4 hB e4) fun t5 ⟨h5, e5, e5'⟩ => div3W_ok h5 hB e5 e5'
end VG.Proof.Rsa.Arm.CrtValues
