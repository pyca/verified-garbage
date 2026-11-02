module
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
public import VerifiedGarbage.Proof.Rsa.Arm.RvKS
public import VerifiedGarbage.Impl.Rsa.Arm.RecoverDet

import VerifiedGarbage.Proof.Rsa.Arm.RvOps
import VerifiedGarbage.Proof.Rsa.Arm.RvOps2
import VerifiedGarbage.Proof.Rsa.Arm.RvSlots
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
import VerifiedGarbage.Proof.Rsa.Arm.KcStart
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeft
import VerifiedGarbage.Proof.Bignum.Arm.CopyWords
import VerifiedGarbage.Proof.Rsa.Arm.RvViews
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Rsa.RecoverSubtract
public import VerifiedGarbage.Proof.Rsa.RecoverExp

/-! # `vg_rsa_recover_primes_det` on ARMv7: the operations Appendix C.2 adds

On a stage of the key working space (`KS`): the switch between the narrow
and wide arrays from `r9` alone (`toW_ok`, `toN_ok`), a narrow halving
(`KS.half_w`), a shift left by one bit with its carry on either view
(`KS.shl_w`, `KS.shl_W`), the low word of a wide array set to one
(`KS.setOne_W`), and the header words of the checks and the counts.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm
open VG.Impl.Rsa.Arm.RecoverDet
open VG.Impl.Rsa.Arm.Recover (nArr)
open VG.Proof.Rsa (sub32 b2n)

/-- Evaluates the arrays' and header words' functions of a stage at their
indices: unfolds `upd` and the indices' names, then decides the `if`s. -/
macro "rd_ev" : tactic => `(tactic| (simp only [upd, VG.Impl.Rsa.Arm.RecoverDet.wZ, VG.Impl.Rsa.Arm.RecoverDet.wOne, VG.Impl.Rsa.Arm.RecoverDet.wX,
    VG.Impl.Rsa.Arm.RecoverDet.wX3, VG.Impl.Rsa.Arm.RecoverDet.wT1, VG.Impl.Rsa.Arm.RecoverDet.wT2,
    VG.Impl.Rsa.Arm.RecoverDet.wA, VG.Impl.Rsa.Arm.RecoverDet.wN, VG.Impl.Rsa.Arm.RecoverDet.wR,
    VG.Impl.Rsa.Arm.RecoverDet.wDt, VG.Impl.Rsa.Arm.RecoverDet.wB, VG.Impl.Rsa.Arm.RecoverDet.aN,
    VG.Impl.Rsa.Arm.RecoverDet.aZN, VG.Impl.Rsa.Arm.RecoverDet.aOneN, VG.Impl.Rsa.Arm.RecoverDet.aT1,
    VG.Impl.Rsa.Arm.RecoverDet.aT2, VG.Impl.Rsa.Arm.RecoverDet.aU, VG.Impl.Rsa.Arm.RecoverDet.aX2,
    VG.Impl.Rsa.Arm.RecoverDet.aGx, VG.Impl.Rsa.Arm.RecoverDet.aG1, VG.Impl.Rsa.Arm.RecoverDet.aG,
    VG.Impl.Rsa.Arm.RecoverDet.aMlo, VG.Impl.Rsa.Arm.RecoverDet.aM1, VG.Impl.Rsa.Arm.RecoverDet.aD,
    VG.Impl.Rsa.Arm.RecoverDet.aRlo, VG.Impl.Rsa.Arm.RecoverDet.aRem, VG.Impl.Rsa.Arm.RecoverDet.aDt,
    VG.Impl.Rsa.Arm.RecoverDet.aB, VG.Impl.Rsa.Arm.RecoverDet.aBy, VG.Impl.Rsa.Arm.RecoverDet.aRm,
    VG.Impl.Rsa.Arm.RecoverDet.aY, VG.Impl.Rsa.Arm.RecoverDet.aTy, VG.Impl.Rsa.Arm.RecoverDet.aDf,
    VG.Impl.Rsa.Arm.RecoverDet.aP, VG.Impl.Rsa.Arm.RecoverDet.aQ, VG.Impl.Rsa.Arm.RecoverDet.sB0,
    VG.Impl.Rsa.Arm.RecoverDet.sB1, VG.Impl.Rsa.Arm.RecoverDet.sOkDE, VG.Impl.Rsa.Arm.RecoverDet.sU,
    VG.Impl.Rsa.Arm.RecoverDet.sX, VG.Impl.Rsa.Arm.RecoverDet.sEven,
    VG.Impl.Rsa.Arm.RecoverDet.sBoth, VG.Impl.Rsa.Arm.RecoverDet.sY, VG.Impl.Rsa.Arm.RecoverDet.sLt,
    VG.Impl.Rsa.Arm.RecoverDet.sExact, VG.Impl.Rsa.Arm.RecoverDet.sC1,
    VG.Impl.Rsa.Arm.RecoverDet.sC2, VG.Impl.Rsa.Arm.RecoverDet.sOk4, VG.Impl.Rsa.Arm.RecoverDet.sBb,
    VG.Impl.Rsa.Arm.RecoverDet.sOk5, VG.Impl.Rsa.Arm.RecoverDet.sK, VG.Impl.Rsa.Arm.RecoverDet.sU1,
    VG.Impl.Rsa.Arm.RecoverDet.sMask, VG.Impl.Rsa.Arm.Recover.wM, VG.Impl.Rsa.Arm.Recover.wMod,
    VG.Impl.Rsa.Arm.Recover.wZ, VG.Impl.Rsa.Arm.Recover.wE, VG.Impl.Rsa.Arm.Recover.wD,
    VG.Impl.Rsa.Arm.Recover.aN, VG.Impl.Rsa.Arm.Recover.sMask]; try simp))

/-- Reads the functions of a stage through their updates at literal indices,
leaving the functions under them folded. -/
macro "rd_up" : tactic => `(tactic| simp (disch := decide) only [upd_ne, upd_self])

/-! ## The shift -/

/-- `shl j`: `[j] := 2 [j] + r11` modulo `2^(32 w)`, the bit shifted out in `r11`. -/
theorem shl_ok {s : State} {B : BitVec 32} {Z w N j : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 256) (carry : (s.gpr .r11).toNat ≤ 1) :
    WP isa (shl j) s fun t => Ws t B Z w N ∧ Keep B w [j] [] s.mem t.mem ∧
      num t.mem B w j = (2 * num s.mem B w j + (s.gpr .r11).toNat) % 2 ^ (32 * w) ∧
      (t.gpr .r11).toNat = (2 * num s.mem B w j + (s.gpr .r11).toNat) / 2 ^ (32 * w) ∧
      Rest opRegs s t := by
  have fit := h.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  rw [shl, WP.seq_iff]
  refine ptr_ok h (r := .r0) (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  refine wp_mov (op2_reg _ _) fun u u2 => WP.block_nil ?_
  have hu : Ws u B Z w N := h1.of_upd u2 (by decide) (by decide) (by decide)
  have r11 : u.gpr .r11 = s.gpr .r11 := by rw [u2.other _ (by decide), r1.gpr _ (by decide)]
  have mu : u.mem = s.mem := by rw [u2.mem, m1]
  refine WP.mono (VG.Proof.Bignum.Arm.shiftLeft_ok u (base := B) (size := Z) (o := arr w j) (n := w)
    ⟨nw, by omega, hu.writable⟩ h.wpos (by rw [u2.other _ (by decide), p1]) (by rw [u2.gpr, h1.r9])
    (by rw [r11]; exact carry)) fun t inv => ?_
  obtain ⟨res, cout⟩ := inv.result
  rw [mu, r11] at res cout
  refine ⟨hu.rest inv.rest, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero, mu] using inv.outside)
    (by omega) (by simp), res, cout, ((r1.mono (by simp)).trans (u2.rest (by simp))).trans
    (inv.rest.mono (by simp))⟩

/-- `copy o a`, with the words of `[o]` above its `w` kept. -/
theorem copy_out_ok {s : State} {B : BitVec 32} {Z w N o a : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hN : N ≤ 256) (hoa : o ≠ a) :
    WP isa (copy o a) s fun t => Ws t B Z w N ∧ Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o = num s.mem B w a ∧ Outside (State.addr B) (arr w o) (4 * w) s.mem t.mem ∧
      Rest opRegs s t := by
  rw [copy, WP.seq_iff]
  refine ptr3_ok h (by omega) (by omega) (by omega) fun s3 p0 p10 p12 r3 m3 h3 => ?_
  refine wp_mov (op2_reg _ _) fun s4 u4 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u5 => WP.block_nil ?_
  have hu : Ws u B Z w N := (h3.of_upd u4 (by decide) (by decide) (by decide)).of_upd u5 (by decide) (by decide) (by decide)
  have mu : u.mem = s.mem := u5.mem.trans (u4.mem.trans m3)
  have restU : Rest opRegs s u :=
    (r3.mono (by simp)).trans ((u4.rest (by simp)).trans (u5.rest (by simp)))
  refine WP.mono (VG.Proof.Bignum.Arm.copyWords_ok u (hu.subCtx ho ha ha hoa hoa) h.wpos
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p0])
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p10])
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p12])
    (by rw [u5.other _ (by decide), u4.gpr, h3.r9])) ?_
  intro t inv
  have v := inv.value
  rw [mu] at v
  have out : Outside (State.addr B) (arr w o) (4 * w) s.mem t.mem := by
    simpa only [Nat.add_zero, mu] using inv.outside
  refine ⟨hu.rest inv.rest, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
    (by simp only [S]; omega) (by simp), ?_, out, restU.trans (inv.rest.mono (by simp))⟩
  change val32 _ _ _ _ = _; rw [v]; split <;> rfl

/-- A number of `W` words: its low `w` words are the narrow array `2 j`'s number. -/
theorem numW_split (m : Mem) (B : BitVec 32) (w j : Nat) :
    num m B (2 * w + 2) j = num m B w (2 * j) +
      2 ^ (32 * w) * (val32 m (State.addr B) (arr w (2 * j) + 4 * w) 2 + 2 ^ 64 * num m B w (2 * j + 1)) := by
  have e : 2 ^ (32 * (w + 2)) = 2 ^ (32 * w) * 2 ^ 64 := by
    rw [← Nat.pow_add, show 32 * (w + 2) = 32 * w + 64 by omega]
  rw [numW, val32_append, e, Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]

section
variable {P : RP} {σ s : State} {A : Nat → Nat} {live : List Nat} {AW : Nat → Nat} {liveW : List Nat}
  {V : Nat → Nat} {ls : List Nat}

theorem KS.shl_w {j : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.w nArr)
    (hj : j ∈ live) (carry : (s.gpr .r11).toNat ≤ 1) (hlW : ∀ i ∈ liveW, j / 2 ≠ i) :
    WP isa (shl j) s fun t =>
      KS P σ (upd A j ((2 * A j + (s.gpr .r11).toNat) % 2 ^ (32 * P.w))) (j :: live) AW liveW V ls t ∧
      Ws t P.B P.Z P.w nArr ∧ (t.gpr .r11).toNat = (2 * A j + (s.gpr .r11).toNat) / 2 ^ (32 * P.w) ∧
      Rest opRegs s t :=
  WP.mono (shl_ok hv (h.live_lt j hj) (by decide) carry) fun _ ⟨ht, k, e, c, r⟩ =>
    ⟨h.write_w k (h.live_lt j hj) (by simp) (h.r8_of r) r.sp r.rd r.wr (by rw [e, h.arrs j hj]) hlW (by simp),
      ht, by rw [c, h.arrs j hj], r⟩

theorem KS.shl_W {j : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    (hj : j ∈ liveW) (carry : (s.gpr .r11).toNat ≤ 1) (hl : ∀ i ∈ live, i / 2 ≠ j) :
    WP isa (shl j) s fun t =>
      KS P σ A live (upd AW j ((2 * AW j + (s.gpr .r11).toNat) % 2 ^ (32 * P.W))) (j :: liveW) V ls t ∧
      Ws t P.B P.Z P.W 22 ∧ (t.gpr .r11).toNat = (2 * AW j + (s.gpr .r11).toNat) / 2 ^ (32 * P.W) ∧
      Rest opRegs s t :=
  WP.mono (shl_ok hv (h.liveW_lt j hj) (by decide) carry) fun _ ⟨ht, k, e, c, r⟩ =>
    ⟨h.write_W k (h.liveW_lt j hj) (by simp) (h.r8_of r) r.sp r.rd r.wr (by rw [e, h.arrsW j hj]) hl (by simp),
      ht, by rw [c, h.arrsW j hj], r⟩

theorem KS.half_w {j : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.w nArr)
    (hj : j ∈ live) (r11 : (s.gpr .r11).toNat = 0) (hlW : ∀ i ∈ liveW, j / 2 ≠ i) :
    WP isa (half j) s fun t => KS P σ (upd A j (A j / 2)) (j :: live) AW liveW V ls t ∧
      Ws t P.B P.Z P.w nArr ∧ Rest opRegs s t :=
  WP.mono (Keys.half_ok hv (h.live_lt j hj) (by decide) (by omega)) fun _ ⟨ht, k, e, r⟩ =>
    ⟨h.write_w k (h.live_lt j hj) (by simp) (h.r8_of r) r.sp r.rd r.wr
      (by rw [e, r11, Nat.mul_zero, Nat.add_zero, h.arrs j hj]) hlW (by simp), ht, r⟩

theorem KS.setOne_W {j : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    (hj : j ∈ liveW) (hl : ∀ i ∈ live, i / 2 ≠ j) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live (upd AW j (1 + 2 ^ 32 * (AW j / 2 ^ 32))) (j :: liveW) V ls t →
      Ws t P.B P.Z P.W 22 → Rest opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (setOne j ++ rest)) s Q :=
  Keys.setOne_ok hv (h.liveW_lt j hj) (by decide) fun t ht kt e r =>
    k t (h.write_W kt (h.liveW_lt j hj) (by simp) (h.r8_of r) r.sp r.rd r.wr (by rw [e, h.arrsW j hj]) hl
      (by simp)) ht r

/-- The narrow view of a wide array's low half. -/
theorem KS.narrow {j : Nat} (h : KS P σ A live AW liveW V ls s) (hj : j ∈ liveW) (h2 : 2 * j < nArr) :
    KS P σ (upd A (2 * j) (AW j % 2 ^ (32 * P.w))) (2 * j :: live) AW liveW V ls s := by
  refine ⟨h.bs, h.r8, h.cnt, fun i hi => ?_, h.arrsW, h.sl,
    fun i hi => (List.mem_cons.mp hi).elim (fun e => e ▸ h2) (h.live_lt i), h.liveW_lt, h.ls_ok⟩
  by_cases e : i = 2 * j
  · subst e
    rw [upd_self, ← h.arrsW j hj]
    change _ = num s.mem P.B (2 * P.w + 2) j % _
    rw [numW_split s.mem P.B P.w j, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val32_lt _ _ _ _)]
  · rw [upd_ne _ _ e]; exact h.arrs i ((List.mem_cons.mp hi).resolve_left e)

/-- `copy (2 j) a` into the low half of a zero wide array `j`: the wide array holds `[a]`. -/
theorem KS.widen {j a : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.w nArr)
    (hj : 2 * j + 1 < nArr) (z : num s.mem P.B P.W j = 0) (ha : a ∈ live) (h2a : 2 * j ≠ a)
    (hl : ∀ i ∈ live, i ≠ 2 * j) (hlW : ∀ i ∈ liveW, i ≠ j) :
    WP isa (copy (2 * j) a) s fun t =>
      KS P σ A live (upd AW j (A a)) (j :: liveW) V ls t ∧ Ws t P.B P.Z P.w nArr := by
  have sz := h.sizes
  refine WP.mono (copy_out_ok hv (by omega) (h.live_lt a ha) (by decide) h2a) fun t ⟨ht, k, e, out, r⟩ => ⟨?_, ht⟩
  have f2 := fit_w sz (show 2 * j < nArr by omega)
  have f2Z := fitZ_w sz (show 2 * j < nArr by omega)
  have f3 := fit_w sz hj
  have hS : S P.w = 4 * (P.w + 2) := rfl
  have hi : num t.mem P.B P.w (2 * j + 1) = num s.mem P.B P.w (2 * j + 1) :=
    k.num (by simp) (by simp) f3
  have hx : val32 t.mem (State.addr P.B) (arr P.w (2 * j) + 4 * P.w) 2 =
      val32 s.mem (State.addr P.B) (arr P.w (2 * j) + 4 * P.w) 2 := out.val32 (by omega) (by omega)
  change num s.mem P.B (2 * P.w + 2) j = 0 at z
  rw [numW_split s.mem P.B P.w j] at z
  have z1 : val32 s.mem (State.addr P.B) (arr P.w (2 * j) + 4 * P.w) 2 + 2 ^ 64 * num s.mem P.B P.w (2 * j + 1) = 0 := by
    have p : 0 < 2 ^ (32 * P.w) := Nat.two_pow_pos _
    rcases Nat.eq_zero_or_pos (val32 s.mem (State.addr P.B) (arr P.w (2 * j) + 4 * P.w) 2 +
      2 ^ 64 * num s.mem P.B P.w (2 * j + 1)) with c | c
    · exact c
    · have := Nat.mul_pos p c; omega
  have vt : num t.mem P.B P.W j = A a := by
    change num t.mem P.B (2 * P.w + 2) j = _
    rw [numW_split t.mem P.B P.w j, e, hi, hx, z1, Nat.mul_zero, Nat.add_zero, h.arrs a ha]
  refine h.core k (by simpa using f2Z) (by simp) (h.r8_of r) r.sp r.rd r.wr (h.arrs_w k (fun i hi o ho => by
      simp only [List.mem_singleton] at ho; subst ho; exact Ne.symm (hl i hi)) (by simp)) h.live_lt
    (fun i hi => ?_) (fun i hi => (List.mem_cons.mp hi).elim (fun e => by subst e; have : nArr = 44 := rfl; omega) (h.liveW_lt i))
    (h.sl_keep k (by simp)) h.ls_ok
  by_cases e' : i = j
  · subst e'; rw [upd_self, vt]
  · rw [upd_ne _ _ e']
    exact h.arrsW_w k (fun i hi o ho => by
      simp only [List.mem_singleton] at ho; subst ho; have := hlW i hi; omega) (by simp) i
      ((List.mem_cons.mp hi).resolve_left e')

/-- A narrow array recorded at the value it holds. -/
theorem KS.addLive {j : Nat} (h : KS P σ A live AW liveW V ls s) (hj : j < nArr) :
    KS P σ (upd A j (num s.mem P.B P.w j)) (j :: live) AW liveW V ls s := by
  refine ⟨h.bs, h.r8, h.cnt, fun i hi => ?_, h.arrsW, h.sl,
    fun i hi => (List.mem_cons.mp hi).elim (fun e => e ▸ hj) (h.live_lt i), h.liveW_lt, h.ls_ok⟩
  by_cases e : i = j
  · subst e; rw [upd_self]
  · rw [upd_ne _ _ e]; exact h.arrs i ((List.mem_cons.mp hi).resolve_left e)

/-! ## Values, differences and sums -/

theorem KS.lt_w {j : Nat} (h : KS P σ A live AW liveW V ls s) (hj : j ∈ live) : A j < 2 ^ (32 * P.w) := by
  rw [← h.arrs j hj]; exact val32_lt _ _ _ _

theorem KS.lt_W {j : Nat} (h : KS P σ A live AW liveW V ls s) (hj : j ∈ liveW) : AW j < 2 ^ (32 * P.W) := by
  rw [← h.arrsW j hj]; exact val32_lt _ _ _ _

/-- `[o] := [a] - [b]` with `w` words, and its borrow. -/
theorem KS.sub_w {o a b : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.w nArr)
    (ho : o < nArr) (ha : a ∈ live) (hb : b ∈ live) (hoa : o ≠ a) (hob : o ≠ b)
    (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (sub3 o a b) s fun t => KS P σ (upd A o (sub32 P.w (A a) (A b))) (o :: live) AW liveW V ls t ∧
      Ws t P.B P.Z P.w nArr ∧ Rest opRegs s t ∧ (t.gpr .r11).toNat = b2n (decide (A a < A b)) :=
  WP.mono (h.sub3_w hv ho ha hb hoa hob hlW) fun _ ⟨X, ht, hwt, r, e, c⟩ => by
    have hX : X < 2 ^ (32 * P.w) := by
      have := ht.lt_w (List.mem_cons_self ..); rwa [upd_self] at this
    obtain ⟨xv, cv⟩ := sub32_of hX (h.lt_w hb) e c
    subst xv
    exact ⟨ht, hwt, r, cv⟩

/-- `[o] := [a] - [b]` with `W` words, and its borrow. -/
theorem KS.sub_W {o a b : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    (ho : o < 22) (ha : a ∈ liveW) (hb : b ∈ liveW) (hoa : o ≠ a) (hob : o ≠ b)
    (hl : ∀ j ∈ live, j / 2 ≠ o) :
    WP isa (sub3 o a b) s fun t => KS P σ A live (upd AW o (sub32 P.W (AW a) (AW b))) (o :: liveW) V ls t ∧
      Ws t P.B P.Z P.W 22 ∧ Rest opRegs s t ∧ (t.gpr .r11).toNat = b2n (decide (AW a < AW b)) :=
  WP.mono (h.sub3_W hv ho ha hb hoa hob hl) fun _ ⟨X, ht, hwt, r, e, c⟩ => by
    have hX : X < 2 ^ (32 * P.W) := by
      have := ht.lt_W (List.mem_cons_self ..); rwa [upd_self] at this
    obtain ⟨xv, cv⟩ := sub32_of hX (h.lt_W hb) e c
    subst xv
    exact ⟨ht, hwt, r, cv⟩

@[simp] theorem sub32_self (w a : Nat) : sub32 w a a = 0 := by unfold sub32; simp

/-- A sum through a negation. -/
theorem sub32_neg {w a b : Nat} (ha : a < 2 ^ (32 * w)) (hb : b < 2 ^ (32 * w)) :
    sub32 w a (sub32 w 0 b) = (a + b) % 2 ^ (32 * w) := by
  unfold sub32
  rcases Nat.eq_zero_or_pos b with rfl | pos
  · simp [Nat.mod_eq_of_lt ha]
  · rw [Nat.zero_add, Nat.mod_eq_of_lt (a := 2 ^ (32 * w) - b) (by omega),
      show a + 2 ^ (32 * w) - (2 ^ (32 * w) - b) = a + b by omega]

/-- `add o a b t z`: `[o] := [a] + [b]` with `w` words, through `[t] := 0 - [b]`, `[z] = 0`. -/
theorem KS.add_w {o a b t z : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.w nArr)
    (ho : o < nArr) (ht : t < nArr) (ha : a ∈ live) (hb : b ∈ live) (hz : z ∈ live) (z0 : A z = 0)
    (hta : t ≠ a) (htb : t ≠ b) (htz : t ≠ z) (hoa : o ≠ a) (hot : o ≠ t)
    (hlW : ∀ j ∈ liveW, o / 2 ≠ j ∧ t / 2 ≠ j) :
    WP isa (add o a b t z) s fun u =>
      KS P σ (upd (upd A t (sub32 P.w 0 (A b))) o ((A a + A b) % 2 ^ (32 * P.w))) (o :: t :: live) AW liveW
        V ls u ∧ Ws u P.B P.Z P.w nArr := by
  unfold add
  refine WP.seq (WP.mono (h.sub_w hv ht hz hb htz htb fun j hj => (hlW j hj).2) fun s1 ⟨h1, hv1, _, _⟩ => ?_)
  rw [z0] at h1
  refine WP.mono (h1.sub_w hv1 ho (List.mem_cons_of_mem _ ha) (List.mem_cons_self ..) hoa hot
    fun j hj => (hlW j hj).1) fun u ⟨hu, hvu, _, _⟩ => ⟨?_, hvu⟩
  rwa [upd_ne _ _ (Ne.symm hta), upd_self, sub32_neg (h.lt_w ha) (h.lt_w hb)] at hu

/-- `add o a b t z` with `W` words. -/
theorem KS.add_W {o a b t z : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    (ho : o < 22) (ht : t < 22) (ha : a ∈ liveW) (hb : b ∈ liveW) (hz : z ∈ liveW) (z0 : AW z = 0)
    (hta : t ≠ a) (htb : t ≠ b) (htz : t ≠ z) (hoa : o ≠ a) (hot : o ≠ t)
    (hl : ∀ j ∈ live, j / 2 ≠ o ∧ j / 2 ≠ t) :
    WP isa (add o a b t z) s fun u =>
      KS P σ A live (upd (upd AW t (sub32 P.W 0 (AW b))) o ((AW a + AW b) % 2 ^ (32 * P.W))) (o :: t :: liveW)
        V ls u ∧ Ws u P.B P.Z P.W 22 := by
  unfold add
  refine WP.seq (WP.mono (h.sub_W hv ht hz hb htz htb fun j hj => (hl j hj).2) fun s1 ⟨h1, hv1, _, _⟩ => ?_)
  rw [z0] at h1
  refine WP.mono (h1.sub_W hv1 ho (List.mem_cons_of_mem _ ha) (List.mem_cons_self ..) hoa hot
    fun j hj => (hl j hj).1) fun u ⟨hu, hvu, _, _⟩ => ⟨?_, hvu⟩
  rwa [upd_ne _ _ (Ne.symm hta), upd_self, sub32_neg (h.lt_W ha) (h.lt_W hb)] at hu

/-! ## Header words -/

/-- `brw d`: the header word `d := r11`. -/
theorem KS.brw {d : Nat} {v N : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z v N)
    (hd : SlotOk d) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW (upd V d (s.gpr .r11).toNat) (d :: ls) t → Ws t P.B P.Z v N →
      t.gpr = s.gpr → WP isa (.block rest) t Q) :
    WP isa (.block (brw d ++ rest)) s Q :=
  h.strSlot hv hd fun t ht hvt g _ => k t ht hvt g

/-- `notS d a`: the header word `d :=` the bit `a` negated. -/
theorem KS.notS {d a : Nat} {v N : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z v N)
    (ha : a ∈ ls) (bit : V a ≤ 1) (hd : SlotOk d) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW (upd V d (1 - V a)) (d :: ls) t → Ws t P.B P.Z v N →
      WP isa (.block rest) t Q) :
    WP isa (.block (notS d a ++ rest)) s Q := by
  unfold VG.Impl.Rsa.Arm.RecoverDet.notS
  simp only [List.cons_append, List.nil_append]
  refine h.ldrSlot hv ha (r := .r1) (by decide) fun s1 h1 hv1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
  refine h2.strSlot hv2 (d := d) (r := .r1) hd fun t ht hvt _ _ => k t ?_ hvt
  have e : (s2.gpr .r1).toNat = 1 - V a := by
    rw [u2.gpr, dpVal, u1.gpr,
      VG.Proof.Rsa.KeyBits32.bv_xor_bits (by rw [BitVec.toNat_ofNat]; omega) (by decide), BitVec.toNat_ofNat]
    simp only [show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  rw [e] at ht; exact ht

/-- `norS d a b`: the header word `d :=` neither of the bits `a` and `b`. -/
theorem KS.norS {d a b : Nat} {v N : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z v N)
    (ha : a ∈ ls) (hb : b ∈ ls) (bita : V a ≤ 1) (bitb : V b ≤ 1) (hd : SlotOk d)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW (upd V d (if V a = 0 ∧ V b = 0 then 1 else 0)) (d :: ls) t →
      Ws t P.B P.Z v N → WP isa (.block rest) t Q) :
    WP isa (.block (norS d a b ++ rest)) s Q := by
  unfold VG.Impl.Rsa.Arm.RecoverDet.norS
  simp only [List.cons_append, List.nil_append]
  refine h.ldrSlot hv ha (r := .r1) (by decide) fun s1 h1 hv1 u1 => ?_
  refine h1.ldrSlot hv1 hb (r := .r2) (by decide) fun s2 h2 hv2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  obtain ⟨h3, hv3⟩ := h2.reg hv2 (u3.rest (ws := [.r1]) (by simp)) u3.mem
  refine wp_dp (op2_imm (by decide)) fun s4 u4 => ?_
  obtain ⟨h4, hv4⟩ := h3.reg hv3 (u4.rest (ws := [.r1]) (by simp)) u4.mem
  refine h4.strSlot hv4 (d := d) (r := .r1) hd fun t ht hvt _ _ => k t ?_ hvt
  have e : (s4.gpr .r1).toNat = if V a = 0 ∧ V b = 0 then 1 else 0 := by
    rw [u4.gpr, dpVal, u3.gpr, dpVal, u2.other .r1 (by decide), u1.gpr, u2.gpr]
    rw [VG.Proof.Rsa.KeyBits32.bv_nor_bits (by rw [BitVec.toNat_ofNat]; omega) (by rw [BitVec.toNat_ofNat]; omega),
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [e] at ht; exact ht

/-- `andS d a b`: the header word `d :=` the bits `a` and `b`. -/
theorem KS.andS {d a b : Nat} {v N : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z v N)
    (ha : a ∈ ls) (hb : b ∈ ls) (bita : V a ≤ 1) (bitb : V b ≤ 1) (hd : SlotOk d)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW (upd V d (if V a = 1 ∧ V b = 1 then 1 else 0)) (d :: ls) t →
      Ws t P.B P.Z v N → WP isa (.block rest) t Q) :
    WP isa (.block (andS d a b ++ rest)) s Q := by
  unfold VG.Impl.Rsa.Arm.Keys.andS
  simp only [List.cons_append, List.nil_append]
  refine h.ldrSlot hv ha (r := .r1) (by decide) fun s1 h1 hv1 u1 => ?_
  refine h1.ldrSlot hv1 hb (r := .r2) (by decide) fun s2 h2 hv2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  obtain ⟨h3, hv3⟩ := h2.reg hv2 (u3.rest (ws := [.r1]) (by simp)) u3.mem
  refine h3.strSlot hv3 (d := d) (r := .r1) hd fun t ht hvt _ _ => k t ?_ hvt
  have e : (s3.gpr .r1).toNat = if V a = 1 ∧ V b = 1 then 1 else 0 := by
    rw [u3.gpr, dpVal, u2.other .r1 (by decide), u1.gpr, u2.gpr]
    rw [VG.Proof.Rsa.KeyBits32.bv_and_bits (by rw [BitVec.toNat_ofNat]; omega) (by rw [BitVec.toNat_ofNat]; omega),
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [e] at ht; exact ht

/-- `mov r11, #0`. -/
theorem KS.clr11 {v N : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z v N)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW V ls t → Ws t P.B P.Z v N → (t.gpr .r11).toNat = 0 →
      WP isa (.block rest) t Q) :
    WP isa (.block (clr11 ++ rest)) s Q := by
  unfold VG.Impl.Rsa.Arm.RecoverDet.clr11
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun t u => ?_
  obtain ⟨ht, hvt⟩ := h.reg hv (u.rest (ws := [.r11]) (by simp)) u.mem
  exact k t ht hvt (by rw [u.gpr]; rfl)

/-! ## Counts -/

/-- `cntInit e`: the count `2^e r9` into `sK`. -/
theorem KS.cntInit {e v N : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z v N)
    (he : 1 ≤ e ∧ e ≤ 31) (small : 2 ^ e * v < 2 ^ 32) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW (upd V sK (2 ^ e * v)) (sK :: ls) t → Ws t P.B P.Z v N →
      WP isa (.block rest) t Q) :
    WP isa (.block (cntInit e ++ rest)) s Q := by
  unfold VG.Impl.Rsa.Arm.RecoverDet.cntInit
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_lsl he) fun s1 u1 => ?_
  obtain ⟨h1, hv1⟩ := h.reg hv (u1.rest (ws := [.r1]) (by simp)) u1.mem
  refine h1.strSlot hv1 (d := sK) (r := .r1) (by decide) fun t ht hvt _ _ => k t ?_ hvt
  have hw := hv.wle
  have c : (s1.gpr .r1).toNat = 2 ^ e * v := by
    rw [u1.gpr, hv.r9, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show v < 2 ^ 32 by omega), Nat.mul_comm, Nat.mod_eq_of_lt small]
  rw [c] at ht; exact ht

/-- `cntNext`: the count less one, and Z if it is zero. -/
theorem KS.cntNext {v N : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z v N)
    (hc : sK ∈ ls) (h1 : 1 ≤ V sK) (h2 : V sK < 2 ^ 32) :
    WP isa (.block VG.Impl.Rsa.Arm.RecoverDet.cntNext) s fun t =>
      KS P σ A live AW liveW (upd V sK (V sK - 1)) (sK :: ls) t ∧
      Ws t P.B P.Z v N ∧ t.z = decide (V sK - 1 = 0) := by
  unfold VG.Impl.Rsa.Arm.RecoverDet.cntNext
  refine h.ldrSlot hv hc (r := .r1) (by decide) fun s1 h1' hv1 u1 => ?_
  refine wp_subs (op2_imm (by decide)) fun s2 u2 z2 => ?_
  obtain ⟨h2', hv2⟩ := h1'.reg hv1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
  refine h2'.strSlot hv2 (d := sK) (r := .r1) (by decide) fun t ht hvt gt zt => WP.block_nil ⟨?_, hvt, ?_⟩
  · have e : (s2.gpr .r1).toNat = V sK - 1 := by
      rw [u2.gpr, u1.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [e] at ht; exact ht
  · rw [zt, z2, u1.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    rfl

/-! ## The widths -/

/-- `toW`: from the narrow arrays to the wide ones. -/
theorem KS.toW (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.w nArr)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW V ls t → Ws t P.B P.Z P.W 22 → Rest [.r9, .r7] s t →
      WP isa (.block rest) t Q) :
    WP isa (.block (toW ++ rest)) s Q := by
  have sz := h.sizes
  have wl := sz.wle
  unfold VG.Impl.Rsa.Arm.RecoverDet.toW
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_lsl (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  have e9 : s3.gpr .r9 = BitVec.ofNat 32 P.W := by
    rw [u3.gpr, dpVal, u2.gpr, hv.r9]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (2 : BitVec 32).toNat = 2 from rfl]
    simp only [RP.W]
    omega
  refine VG.Proof.Rsa.Arm.KeyCheck.stride_ok (by have := sz.Wle; omega) e9 fun t h7 r m => ?_
  have rt : Rest [.r9, .r7] s t := (u2.rest (by simp)).trans ((u3.rest (by simp)).trans (r.mono (by simp)))
  have mt : t.mem = s.mem := m.trans (u3.mem.trans u2.mem)
  refine k t (h.of_rest rt mt (by decide)) ⟨hv.nowrap, by rw [rt.wr]; exact hv.writable,
    by rw [arrW_end]; exact sz.fits, by show 0 < 2 * P.w + 2; omega, by have := sz.Wle; omega, h7,
    by rw [rt.gpr _ (by decide), hv.r8], by rw [r.gpr _ (by decide), e9]⟩ rt

/-- `toN`: from the wide arrays to the narrow ones. -/
theorem KS.toN (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW V ls t → Ws t P.B P.Z P.w nArr → Rest [.r9, .r7] s t →
      WP isa (.block rest) t Q) :
    WP isa (.block (toN ++ rest)) s Q := by
  have sz := h.sizes
  have wl := sz.wle
  unfold VG.Impl.Rsa.Arm.RecoverDet.toN
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
  have e9 : s3.gpr .r9 = BitVec.ofNat 32 P.w := by
    rw [u3.gpr, u2.gpr, dpVal, hv.r9]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, show (2 : BitVec 32).toNat = 2 from rfl]
    simp only [RP.W]
    omega
  refine VG.Proof.Rsa.Arm.KeyCheck.stride_ok (by omega) e9 fun t h7 r m => ?_
  have rt : Rest [.r9, .r7] s t := (u2.rest (by simp)).trans ((u3.rest (by simp)).trans (r.mono (by simp)))
  have mt : t.mem = s.mem := m.trans (u3.mem.trans u2.mem)
  refine k t (h.of_rest rt mt (by decide)) ⟨hv.nowrap, by rw [rt.wr]; exact hv.writable,
    sz.fits, by show 0 < 2 * P.w6 + 2; omega, by omega, h7,
    by rw [rt.gpr _ (by decide), hv.r8], by rw [r.gpr _ (by decide), e9]⟩ rt

end

end VG.Proof.Rsa.Arm.Recover
