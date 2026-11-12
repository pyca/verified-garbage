module

public import VerifiedGarbage.Proof.Rsa.Arm.CvFinish
public import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
public import VerifiedGarbage.Proof.Rsa.Arm.CvChecksB
public import VerifiedGarbage.Proof.Rsa.Arm.KcShape
public import VerifiedGarbage.Proof.Rsa.Arm.KcBodyW
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

theorem slot16 {s0 : State} {m : Mem} (pre : CvPre s0)
    (h : m.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0)) : slot m (cvB s0) 16 = cvW s0 := by
  have := pre.w16
  simp only [slot, w32]; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- The balanced key's first checks: `p` odd, and `p q mod 2^(32 w) = n` in place of the
division's quotient (and its remainder 0). -/
theorem pre4_ok {s0 s : State} (h : StA s0 s) (hp : cvP s0 < 2 ^ (32 * (cvW s0 / 2))) (hw : cvW s0 % 2 = 0) :
    WP isa (seqs [.block (ctx ++ bitOf sPodd aP), VG.Impl.Rsa.Arm.KeyDiv.mulLo aDR aP aQ, eqS sE1 aDR aDQ aT1,
      eqS sE2 aZero aZero aT1]) s (StC1 s0 (xW s0) 0) := by
  have pre := h.base.pre
  have w16 := pre.w16
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil (bitOf sPodd aP), ← List.append_assoc]
  refine ctx_ok h.base fun t1 b1 h1 r1 m1 => ?_
  have fit := fun j (hj : j < nArr) => h1.fit64 (j := j) hj
  refine bitOf_ok h1 (j := aP) (sl := sPodd) (by decide) (by decide) (by decide) fun t2 h2 k2 e2 r2 =>
    WP.block_nil ?_
  have z1 : ∀ j ∈ zeroArrs, num t1.mem (cvB s0) (cvW s0) j = 0 := fun j hj => by
    rw [m1]; exact num_of_zero (h.zeros j hj)
  have P2 : num t2.mem (cvB s0) (cvW s0) aP = cvP s0 := by
    rw [k2.num (by simp) (by decide) (fit _ (by decide)), m1, h.p]
  have Q2 : num t2.mem (cvB s0) (cvW s0) aQ = cvQ s0 := by
    rw [k2.num (by simp) (by decide) (fit _ (by decide)), m1, h.q]
  have c2 : slot t2.mem (cvB s0) 16 = cvW s0 := by
    rw [k2.slot (by decide) (by decide)]; rw [m1]; exact slot16 pre h.count
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (VG.Proof.Rsa.Arm.KeyDiv.mulLo_ok h2 (o := aDR) (x := aP) (y := aQ) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) c2 hw (by omega) P2 hp Q2
    (by rw [k2.num (by simp) (by decide) (fit _ (by decide))]; exact z1 0 (by decide)))
    fun t3 ⟨h3, e3, k3, r3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h3 (d := sE1) (a := aDR) (b := aDQ) (t := aT1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun t4 ⟨h4, k4, e4, r4⟩ => ?_
  refine WP.mono (eqS_ok h4 (d := sE2) (a := aZero) (b := aZero) (t := aT1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun t5 ⟨h5, k5, e5, r5⟩ => ?_
  have K : Keep (cvB s0) (cvW s0) [aDR, aT1] [sPodd, VG.Impl.Rsa.Arm.KeyDiv.sJ, sT, sE1, sE2] t1.mem t5.mem :=
    k2.mono.trans (k3.mono.trans (k4.mono.trans k5.mono))
  have R : Rest VG.Proof.Rsa.Arm.KeyDiv.divRegs t1 t5 :=
    (r2.mono (by decide)).trans (r3.trans ((r4.mono (by decide)).trans (r5.mono (by decide))))
  have K1 : ∀ j, j < nArr → j ∉ [aDR, aT1] → num t5.mem (cvB s0) (cvW s0) j = num s.mem (cvB s0) (cvW s0) j :=
    fun j hj hn => by rw [K.num (fun k hk e => hn (by subst e; exact hk)) (by decide) (fit j hj), m1]
  have N3 : num t3.mem (cvB s0) (cvW s0) aDQ = cvN s0 := by
    rw [k3.num (by decide) (by decide) (fit _ (by decide)), k2.num (by simp) (by decide) (fit _ (by decide)), m1, h.n]
  refine ⟨b1.keep K (by decide) (by decide) (by decide) R.sp R.rd R.wr, h5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h.count, ← m1]
    refine BitVec.eq_of_toNat_eq ?_
    exact K.slot (e := 16) (by decide) (by decide)
  · rw [k5.slot (by decide) (by decide), k4.slot (by decide) (by decide), k3.slot (by decide) (by decide), e2,
      m1, h.p]
  · rw [k5.slot (by decide) (by decide), e4, e3, N3]
    by_cases c : cvP s0 * cvQ s0 % 2 ^ (32 * cvW s0) = cvN s0 <;> simp [xW, c]
  · rw [e5]; simp
  · rw [K1 _ (by decide) (by decide), h.p]
  · rw [K1 _ (by decide) (by decide), h.q]
  · rw [K1 _ (by decide) (by decide), h.d]
  · rw [K.word (by simp only [S]; omega_arith) (by decide) (by decide) (fit _ (by decide)), m1]
    exact top_of_full (h.zeros aDD (by decide))
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;>
      (rw [K1 _ (by decide) (by decide)]; exact num_of_zero (h.zeros _ (by decide)))

/-- `[r] := [aD] mod fixT [d']'`, `d'` cleared of its low bit, by words. -/
theorem divKc_ok {s0 s : State} (b : Base s0 s) (h : Ws s (cvB s0) (cvZ s0) (cvW s0) nArr)
    (c : slot s.mem (cvB s0) 16 = cvW s0) {r d' : Nat} (hr : r ∈ [aDR2, aDR3]) (hd : d' ∈ [aP, aQ])
    {Dv : Nat} (hD : num s.mem (cvB s0) (cvW s0) d' = Dv) (hDl : Dv < 2 ^ (32 * (cvW s0 / 2)))
    (hz : num s.mem (cvB s0) (cvW s0) 0 = 0) :
    WP isa (seqs (divKc r d')) s fun t => Base s0 t ∧ Ws t (cvB s0) (cvZ s0) (cvW s0) nArr ∧
      Keep (cvB s0) (cvW s0) [aDD, r, aDQ, aT1, aDT] VG.Proof.Rsa.Arm.KeyDiv.divSlots s.mem t.mem ∧
      num t.mem (cvB s0) (cvW s0) r =
        num s.mem (cvB s0) (cvW s0) aD % VG.Proof.Rsa.fixT (cvW s0 / 2) (2 * (Dv / 2)) := by
  have pre := b.pre
  have w16 := pre.w16
  have fit := fun j (hj : j < nArr) => h.fit64 (j := j) hj
  have hr' : r < nArr ∧ r ≠ aD ∧ r ≠ aDD ∧ r ≠ aDQ ∧ r ≠ aT1 ∧ r ≠ aDT ∧ r ≠ 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> decide
  have hd' : d' < nArr ∧ d' ≠ aDD := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl <;> decide
  unfold divKc
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h (o := aDD) (a := d') (by decide) hd'.1 (by decide) (Ne.symm hd'.2))
    fun t1 ⟨h1, k1, e1, r1, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine clrLow_ok h1 (j := aDD) (by decide) (by decide) fun t2 h2 k2 e2 r2 _ => ?_
  have D2 : num t2.mem (cvB s0) (cvW s0) aDD = 2 * (Dv / 2) := by rw [e2, e1, hD]
  refine WP.mono (VG.Proof.Rsa.Arm.KeyDiv.fixTopW_ok h2 (m := aDD) (by decide) (by decide) D2
    (Nat.lt_of_le_of_lt (by omega) hDl) (by omega)) fun t3 ⟨h3, k3, e3, r3, _⟩ => ?_
  have c3 : slot t3.mem (cvB s0) 16 = cvW s0 := by
    rw [k3.slot (by decide) (by decide), k2.slot (by decide) (by decide), k1.slot (by decide) (by decide), c]
  have z3 : num t3.mem (cvB s0) (cvW s0) 0 = 0 := by
    rw [k3.num (by decide) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide)),
      k1.num (by decide) (by decide) (fit _ (by decide)), hz]
  have M3l : VG.Proof.Rsa.fixT (cvW s0 / 2) (2 * (Dv / 2)) < 2 ^ (32 * (cvW s0 / 2)) :=
    VG.Proof.Rsa.fixT_lt (by omega) (Nat.lt_of_le_of_lt (by omega) hDl)
  have T3 : 0 < w32 t3.mem (State.addr (cvB s0)) (arr (cvW s0) aDD + 4 * (cvW s0 / 2 - 1)) :=
    VG.Proof.Rsa.Arm.KeyCheck.top_word_pos (k := cvW s0 / 2 - 1) (n := cvW s0) (by omega) e3
      (by rw [show cvW s0 / 2 - 1 + 1 = cvW s0 / 2 by omega]; exact M3l) VG.Proof.Rsa.fixT_ge
  refine WP.mono (VG.Proof.Rsa.Arm.KeyDiv.divW_ok h3 (a := aD) (r := r) (m := aDD) (t := aDQ) (nm := aDT)
    (u := aT1) (by decide) hr'.1 (by decide) (by decide) (by decide) (by decide) (by decide) hr'.2.1
    hr'.2.2.2.1 hr'.2.2.2.2.1 (by decide) (Ne.symm hr'.2.2.1) (by decide) (by decide)
    (Ne.symm hr'.2.2.2.2.2.1) (by decide) (by decide) (by decide) hr'.2.2.2.2.2.2 (by decide) (by decide)
    (by decide) (by omega) c3 e3 M3l T3 z3) fun t ⟨ht, et, _, kt, rt⟩ => ?_
  have K : Keep (cvB s0) (cvW s0) [aDD, r, aDQ, aT1, aDT] VG.Proof.Rsa.Arm.KeyDiv.divSlots s.mem t.mem :=
    k1.mono.trans (k2.mono.trans (k3.mono.trans kt.mono))
  have R : Rest VG.Proof.Rsa.Arm.KeyDiv.divRegs s t :=
    (r1.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans rt))
  refine ⟨b.keep K (fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> first | decide | exact hr'.1) (by decide) (by decide)
    R.sp R.rd R.wr, ht, K, ?_⟩
  rw [et, k3.num (by decide) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide)),
    k1.num (by decide) (by decide) (fit _ (by decide))]

/-- What a balanced key's checks leave: the mask of `p` odd, `p q mod 2^(32 w) = n` (for the
quotient `xW`, and the remainder 0) and the inverse, and the remainders by words. -/
def MidW (s0 t : State) : Prop :=
  StM s0 (xW s0) 0 t ∧
  num t.mem (cvB s0) (cvW s0) aDR2 = cvD s0 % VG.Proof.Rsa.fixT (cvW s0 / 2) (2 * (cvP s0 / 2)) ∧
  num t.mem (cvB s0) (cvW s0) aDR3 = cvD s0 % VG.Proof.Rsa.fixT (cvW s0 / 2) (2 * (cvQ s0 / 2))

theorem tailW_ok {s0 s : State} {X₁ : Nat} (h : StD s0 X₁ 0 s) (hp : cvP s0 < 2 ^ (32 * (cvW s0 / 2)))
    (hq : cvQ s0 < 2 ^ (32 * (cvW s0 / 2))) :
    WP isa (seqs ([copy 0 aZero] ++ divKc aDR2 aP ++ divKc aDR3 aQ)) s fun t => StM s0 X₁ 0 t ∧
      num t.mem (cvB s0) (cvW s0) aDR2 = cvD s0 % VG.Proof.Rsa.fixT (cvW s0 / 2) (2 * (cvP s0 / 2)) ∧
      num t.mem (cvB s0) (cvW s0) aDR3 = cvD s0 % VG.Proof.Rsa.fixT (cvW s0 / 2) (2 * (cvQ s0 / 2)) := by
  have pre := h.base.pre
  have fit := fun j (hj : j < nArr) => h.ws.fit64 (j := j) hj
  rw [List.append_assoc, List.cons_append, List.nil_append, wp_seqs_cons (by unfold divKc; simp)]
  refine WP.mono (copy_ok h.ws (o := 0) (a := aZero) (by decide) (by decide) (by decide) (by decide))
    fun t1 ⟨h1, k1, e1, r1, _⟩ => ?_
  have b1 := h.base.keep k1 (by decide) (by decide) (by decide) r1.sp r1.rd r1.wr
  have c1 : slot t1.mem (cvB s0) 16 = cvW s0 := by
    rw [k1.slot (by decide) (by decide)]; exact slot16 pre h.count
  rw [wp_seqs_append (by unfold divKc; simp) (by unfold divKc; simp)]
  refine WP.mono (divKc_ok b1 h1 c1 (r := aDR2) (d' := aP) (by decide) (by decide)
    (by rw [k1.num (by decide) (by decide) (fit _ (by decide)), h.p]) hp (by rw [e1, h.zero]))
    fun t2 ⟨b2, h2, k2, e2⟩ => ?_
  have c2 : slot t2.mem (cvB s0) 16 = cvW s0 := by rw [k2.slot (by decide) (by decide), c1]
  refine WP.mono (divKc_ok b2 h2 c2 (r := aDR3) (d' := aQ) (by decide) (by decide)
    (by rw [k2.num (by decide) (by decide) (fit _ (by decide)), k1.num (by decide) (by decide) (fit _ (by decide)),
      h.q]) hq
    (by rw [k2.num (by decide) (by decide) (fit _ (by decide)), e1, h.zero]))
    fun t ⟨bt, _, kt, et⟩ => ?_
  have D : ∀ u : State, Keep (cvB s0) (cvW s0) [0] [] s.mem t1.mem →
      num t1.mem (cvB s0) (cvW s0) aD = cvD s0 := fun _ _ => by
    rw [k1.num (by decide) (by decide) (fit _ (by decide)), h.d]
  obtain ⟨V, mV, iV⟩ := h.mask
  refine ⟨⟨bt, V, ?_, ?_⟩, ?_, ?_⟩
  · rw [kt.slot (by decide) (by decide), k2.slot (by decide) (by decide), k1.slot (by decide) (by decide), mV]
  · rw [kt.num (by decide) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide)),
      k1.num (by decide) (by decide) (fit _ (by decide))]
    exact iV
  · rw [kt.num (by decide) (by decide) (fit _ (by decide)), e2, D s k1]
  · rw [et, k2.num (by decide) (by decide) (fit _ (by decide)), D s k1]

theorem bytes_lt_half {s0 : State} {b : List Byte} (hl : b.length = 2 * cvW s0) (hw : cvW s0 % 2 = 0) :
    Spec.Rsa.os2ip b < 2 ^ (32 * (cvW s0 / 2)) := by
  have := VG.Proof.Bignum.os2ip_lt b
  rw [hl, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  rw [show 32 * (cvW s0 / 2) = 8 * (2 * cvW s0) by omega]
  exact this

theorem midW_eq : midW = seqs ([.block (ctx ++ bitOf sPodd aP), VG.Impl.Rsa.Arm.KeyDiv.mulLo aDR aP aQ,
    eqS sE1 aDR aDQ aT1, eqS sE2 aZero aZero aT1] ++ (invSetup ++ (checksB ++
      ([copy 0 aZero] ++ divKc aDR2 aP ++ divKc aDR3 aQ)))) := rfl

/-- A balanced key's checks and values. -/
theorem midW_ok [VG.Proof.Rsa.Arm.Keys.InvLaw] {s0 s : State} (h : StA s0 s) (hB : BalCv s0) :
    WP isa midW s (MidW s0) := by
  have hp : cvP s0 < 2 ^ (32 * (cvW s0 / 2)) :=
    bytes_lt_half (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hB.1) hB.2.2
  have hq : cvQ s0 < 2 ^ (32 * (cvW s0 / 2)) :=
    bytes_lt_half (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hB.2.1) hB.2.2
  rw [midW_eq, wp_seqs_append (List.cons_ne_nil _ _) (by unfold invSetup; simp)]
  refine WP.mono (pre4_ok h hp hB.2.2) fun t1 h1 => ?_
  rw [wp_seqs_append (by unfold invSetup; simp) (by unfold checksB; simp)]
  refine WP.mono (invSetup_ok h1) fun t2 h2 => ?_
  rw [wp_seqs_append (by unfold checksB; simp) (by unfold divKc; simp)]
  exact WP.mono (checksB_ok h2) fun t3 h3 => tailW_ok h3 hp hq

end VG.Proof.Rsa.Arm.CrtValues
