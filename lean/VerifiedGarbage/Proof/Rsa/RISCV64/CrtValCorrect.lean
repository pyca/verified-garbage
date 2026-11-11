module

public import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValInv
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.CrtValuesMath
import VerifiedGarbage.Proof.Rsa.KeyCheckMath
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyWordDiv

/-!
# `vg_rsa_crt_values` on RISC-V: correctness

`clrLowW_ok`: `clrLow` writing only the array's low word; `dParts_ok`: the
remainders of `d` by `p` and `q` with their low bits cleared (`Dd`);
`stores_ok`: `dP` and `dQ` written under the mask and the mask's bit
returned; `valid_ok`: a valid modulus, from the set-up to the stores;
`code_correct`: the function, through `crtKey_masked`
(`Proof/Rsa/CrtValuesMath.lean`), on the registers and the stack (`fnPost`).
-/

-- separate module: its proofs (the divisions of `d`, the stores and `code_correct`) are not re-checked
-- with every change to the constant-time proof

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.CrtValues

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs copy clrLow ptr)
open VG.Impl.Rsa.RISCV64.Div (divL)
open VG.Impl.Rsa.RISCV64.CrtValues (dParts nArr aP aQ aD aDQ aDD aDT aDR2 aDR3 sMask)
open VG.Proof.Rsa.CrtValues (maskOf)

/-- `clrLow j`: the low bit of `[j]` cleared, and only its low word written. -/
theorem clrLowW_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) (hN : N ≤ 2048) :
    WP isa (.block (clrLow j)) s fun t => Ws t B Z w N ∧ Keys.Frame B w [j] [] s.mem t.mem ∧
      num t.mem B w j = num s.mem B w j / 2 * 2 ∧ Keep opRegs s t ∧
      Outside B (arr w j) 8 s.mem t.mem := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  refine ptr_ok h (r := .t0) (by decide) (by decide) (show j < 2048 by omega_arith) ?_
  have hk : WP isa (.block [.load .d .t5 .t0 0, .logicImm .and .t5 .t5 (-2), .store .d .t5 .t0 0])
      (s.write .t0 (off B (arr w j))) fun u =>
        (u.mem = s.mem.writeW (off B (arr w j)) (word s.mem B (arr w j) &&& BitVec.ofInt 64 (-2))) ∧
          Keep [.t5] (s.write .t0 (off B (arr w j))) u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h.scr.st (d := arr w j) (n := 8) (by omega_arith), h.scr.al8 (d := arr w j) (by omega_arith) (arr_al _ _),
      h.scr.ld (d := arr w j) (n := 8) (by omega_arith)]
  refine WP.mono hk fun u ⟨mu, ku⟩ => ?_
  have kt : Keep opRegs s u := ((Keep.write _ _ _).trans ku).mono (by decide)
  have lw := low_write (m := s.mem) (B := B) h.wpos (h.fit64 hj) (word s.mem B (arr w j) &&& BitVec.ofInt 64 (-2))
  rw [← mu] at lw
  refine ⟨h.of_keep kt, lw.1, ?_, kt, by rw [mu]; exact writeW_outside _ _ _ (by omega_arith)⟩
  rw [lw.2, clr_toNat]
  have e := wordsVal_mod64 s.mem B (d := arr w j) (k := w) h.wpos
  change num s.mem B w j % 2 ^ 64 = _ at e
  rw [← e]
  have := Nat.div_add_mod (num s.mem B w j) (2 ^ 64)
  omega_arith

/-- After the divisions of `d`. -/
structure Dd (s0 : State) (X₁ X₂ V : Nat) (M : Mem) (t : State) : Prop where
  cb : CB s0 M t
  ws : Ws t (bOf s0) (zOf s0) (wOf s0) nArr
  mask : slot t.mem (bOf s0) sMask = if maskOf (Pv s0) (Qv s0) X₁ X₂ V then 1 else 0
  r2 : maskOf (Pv s0) (Qv s0) X₁ X₂ V = true → 0 < 2 * (Pv s0 / 2) →
    num t.mem (bOf s0) (wOf s0) aDR2 = Dv s0 % (2 * (Pv s0 / 2))
  r3 : maskOf (Pv s0) (Qv s0) X₁ X₂ V = true → 0 < 2 * (Qv s0 / 2) →
    num t.mem (bOf s0) (wOf s0) aDR3 = Dv s0 % (2 * (Qv s0 / 2))

/-- One division of `d` by `[a]` with its low bit cleared, into `[r]`. -/
theorem dDiv_ok {s0 s : State} (h : PreC s0) {M : Mem} (c : CB s0 M s) (ws : Ws s (bOf s0) (zOf s0) (wOf s0) nArr)
    {a r : Nat} (ha : a = aP ∨ a = aQ) (hr : r = aDR2 ∨ r = aDR3)
    (hd : num s.mem (bOf s0) (wOf s0) aD = Dv s0)
    (hz : word s.mem (bOf s0) (arr (wOf s0) aDD + 8 * wOf s0) = 0)
    {len : Reg} {L : Nat} (hl : ∀ x, CB s0 M x → x.gpr len = BitVec.ofNat 64 L) (hL1 : 1 ≤ L)
    (hLw : L ≤ 8 * wOf s0) (hav : num s.mem (bOf s0) (wOf s0) a < 2 ^ (8 * L)) :
    WP isa (seqs [copy aDQ aD, copy aDD a, .block (clrLow aDD), divL aDQ r aDD len]) s fun t =>
      CB s0 M t ∧ Ws t (bOf s0) (zOf s0) (wOf s0) nArr ∧
      Keys.Frame (bOf s0) (wOf s0) [aDQ, aDD, r, aDT] [] s.mem t.mem ∧
      word t.mem (bOf s0) (arr (wOf s0) aDD + 8 * wOf s0) = 0 ∧
      (0 < num s.mem (bOf s0) (wOf s0) a / 2 * 2 →
        num t.mem (bOf s0) (wOf s0) r = Dv s0 % (num s.mem (bOf s0) (wOf s0) a / 2 * 2)) := by
  have ⟨w1, w2⟩ := h.w_bounds
  have fit : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => ws.fit64 hj
  have ha' : a < nArr ∧ a ≠ aDQ ∧ a ≠ aDD ∧ a ≠ aDT := by rcases ha with rfl | rfl <;> decide
  have hr' : r < nArr ∧ r ≠ aDQ ∧ r ≠ aDD ∧ r ≠ aDT ∧ r ≠ aD := by rcases hr with rfl | rfl <;> decide
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok ws (o := aDQ) (a := aD) (by cvx) (by cvx) (by decide) (by cvx))
    fun t1 ⟨ws1, f1, v1, k1, _⟩ => ?_
  have c1 := c.step h f1 (by cvx) (by simp) k1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok ws1 (o := aDD) (a := a) (by cvx) ha'.1 (by decide) (Ne.symm ha'.2.2.1))
    fun t2 ⟨ws2, f2, v2, k2, o2⟩ => ?_
  have c2 := c1.step h f2 (by cvx) (by simp) k2
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (clrLowW_ok ws2 (j := aDD) (by cvx) (by decide)) fun t3 ⟨ws3, f3, v3, k3, o3⟩ => ?_
  have c3 := c2.step h f3 (by cvx) (by simp) k3
  have hS : S (wOf s0) = 8 * (wOf s0 + 2) := rfl
  have fD := fit aDD (by cvx)
  have z3 : word t3.mem (bOf s0) (arr (wOf s0) aDD + 8 * wOf s0) = 0 := by
    rw [o3.word (.inr (by omega_arith)) (by omega_arith), o2.word (.inr (by omega_arith)) (by omega_arith),
      f1.word (i := wOf s0) (by omega_arith) (by cvx) (by simp) fD]
    exact hz
  have a1 : num t1.mem (bOf s0) (wOf s0) a = num s.mem (bOf s0) (wOf s0) a :=
    f1.num (fun _ hk => by rw [List.mem_singleton.mp hk]; exact Ne.symm ha'.2.1) (by simp) (fit _ ha'.1)
  rw [v2, a1] at v3
  have q3 : num t3.mem (bOf s0) (wOf s0) aDQ = Dv s0 := by
    rw [f3.num (j := aDQ) (by cvx) (by simp) (fit _ (by cvx)), f2.num (j := aDQ) (by cvx) (by simp) (fit _ (by cvx)),
      v1, hd]
  refine WP.mono (divL_ok ws3 (q := aDQ) (r := r) (d := aDD) (by cvx) hr'.1 (by cvx) (by decide)
    (Ne.symm hr'.2.1) (by cvx) hr'.2.2.1 (hl t3 c3) hL1 hLw z3
    (by rw [v3]; exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hav)) fun t ⟨ws4, f4, k4, _, v4⟩ => ?_
  have c4 := c3.step h f4 (by simp [hr'.1]; cvx) (by simp) k4
  refine ⟨c4, ws4, ?_, ?_, fun hp => ?_⟩
  · refine (f1.mono (by simp) (by simp)).trans ((f2.mono (by simp) (by simp)).trans
      ((f3.mono (by simp) (by simp)).trans (f4.mono (by simp) (by simp))))
  · have hjD : ∀ k ∈ [aDQ, r], k ≠ aDD := by
      simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      exact ⟨by decide, hr'.2.2.1⟩
    rw [f4.word (i := wOf s0) (by omega_arith) hjD (by simp) fD]
    exact z3
  · have := (v4 (by rw [v3]; exact hp)).2.2.1
    rw [this, q3, v3]

theorem dParts_eq : dParts = seqs ([copy aDQ aD, copy aDD aP, .block (clrLow aDD), divL aDQ aDR2 aDD .s4] ++
    [copy aDQ aD, copy aDD aQ, .block (clrLow aDD), divL aDQ aDR3 aDD .s6]) := rfl

theorem dParts_ok {s0 s : State} (h : PreC s0) {X₁ X₂ V X : Nat} (iv : Iv s0 X₁ X₂ V X s) :
    WP isa dParts s (Dd s0 X₁ X₂ V s.mem) := by
  have fit : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => iv.ws.fit64 hj
  rw [dParts_eq, wp_seqs_append (by simp) (by simp)]
  have w8 : ∀ L, L < kOf s0 → L ≤ 8 * wOf s0 := fun L hL => by simp only [wOf, kOf] at *; omega
  refine WP.mono (dDiv_ok h iv.cb iv.ws (a := aP) (r := aDR2) (.inl rfl) (.inl rfl) iv.d iv.ddz
    (fun _ c => c.s4.trans (toNat_ofNat_eq _)) h.p1 (w8 _ h.p2) (by rw [iv.p]; exact pv_lt s0))
    fun t1 ⟨c1, w1, f1, z1, v1⟩ => ?_
  have d1 : num t1.mem (bOf s0) (wOf s0) aD = Dv s0 := by rw [f1.num (j := aD) (by decide) (by simp) (fit _ (by decide)), iv.d]
  have q1 : num t1.mem (bOf s0) (wOf s0) aQ = Qv s0 := by rw [f1.num (j := aQ) (by decide) (by simp) (fit _ (by decide)), iv.q]
  refine WP.mono (dDiv_ok h c1 w1 (a := aQ) (r := aDR3) (.inr rfl) (.inr rfl) d1 z1
    (fun _ c => c.s6.trans (toNat_ofNat_eq _)) h.q1 (w8 _ h.q2) (by rw [q1]; exact qv_lt s0))
    fun t ⟨c2, w2, f2, _, v2⟩ => ⟨c2, w2, ?_, fun _ hp => ?_, fun _ hq => ?_⟩
  · rw [f2.slot (by decide) (by simp), f1.slot (by decide) (by simp)]; exact iv.mask
  · rw [f2.num (j := aDR2) (by decide) (by simp) (fit _ (by decide)), v1 (by rw [iv.p]; omega_arith), iv.p,
      Nat.mul_comm]
  · rw [v2 (by rw [q1]; omega_arith), q1, Nat.mul_comm]

end VG.Proof.Rsa.RISCV64.CrtValues

namespace VG.Proof.Rsa.RISCV64.InvBatch

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys VG.Impl.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr)
open VG.Impl.Rsa.RISCV64.InvBatch (zeroW zeros)
open VG.RISCV64.RegUpd

/-- `zeroW j` on the working space alone: `[j]` := 0. -/
theorem zeroWs_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) (hN : N ≤ 256) :
    WP isa (zeroW j) s fun t => Ws t B Z w N ∧ Keys.Frame B w [j] [] s.mem t.mem ∧ num t.mem B w j = 0 ∧
      Keep kRegs s t := by
  have fj := h.arr_fit hj
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wle
  have := arr_al4 w j
  rw [zeroW, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (by omega) ?_
  refine WP.mono (WP.keep [.t3] (Q := fun u => u.gpr .t3 = BitVec.ofNat 64 (2 * w + 2) ∧
    u.gpr .t0 = off B (arr w j) ∧ u.mem = s.mem) ?_ (by rfl) (by rfl)) fun u ⟨⟨u3, u0, um⟩, ku⟩ => ?_
  · brun [h.s9]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have k1 : Keep kRegs s u := ((Keep.write _ .t0 _).trans ku).mono (by decide)
  rw [zeros, WP.seq_iff]
  refine WP.mono (WP.keep [.t5] (Q := fun y => y.gpr .t5 = 0 ∧ y.mem = u.mem) (by brun [fin64_exec_li_zero])
    (by rfl) (by rfl)) fun y ⟨⟨y5, ym⟩, ky⟩ => ?_
  have k2 : Keep kRegs s y := Keep.trans' k1 (ky.mono (by decide))
  refine WP.mono (zeroLoop_ok (dO := arr w j) (n := 2 * w + 2) (h.of_keep k2).scr (by rw [ky.gpr (by decide)]; exact u0)
    (by rw [ky.gpr (by decide)]; exact u3) y5 (by omega) (by omega) (by omega) (by omega)) fun t ⟨z, out, kt⟩ => ?_
  rw [ym, um] at out
  refine ⟨h.of_keep (Keep.trans' k2 (kt.mono (by decide))), Keys.Frame.of_arr (d := 0)
    (by simpa only [Nat.add_zero] using out) (by omega) (by simp), ?_, Keep.trans' k2 (kt.mono (by decide))⟩
  rw [num_eq]
  exact val32_zero fun i hi => z i (by omega)

end VG.Proof.Rsa.RISCV64.InvBatch

namespace VG.Proof.Rsa.RISCV64.CrtValues

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs copy clrLow ptr)
open VG.Impl.Rsa.RISCV64.CrtValues (dParts nArr aP aQ aD aDQ aDD aDT aDR2 aDR3 sMask shape kept saveK restoreK
  divWP dPartsW dPartsAll)
open VG.Proof.Rsa.CrtValues (maskOf)

/-! ## The divisions by words, for a balanced key -/

theorem cv_exec_li32 {s : State} {d : Reg} : exec (.li d 32) s = some (s.write d 32#64) := by
  rw [exec_li (by decide)]; rfl

theorem wr_other {m : Mem} {B : Addr} {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (he : e + 8 ≤ 2 ^ 64) (hd : d + 8 ≤ 2 ^ 64) : word (m.writeW (off B e) v) B d = word m B d :=
  (writeW_outside m B v he).word h hd

theorem Outside.writeW_in {B : Addr} {o n e : Nat} {m m' : Mem} (h : Outside B o n m m') (v : BitVec 64)
    (he : o ≤ e) (he' : e + 8 ≤ o + n) (hf : e + 8 ≤ 2 ^ 64) : Outside B o n m (m'.writeW (off B e) v) :=
  h.trans ((writeW_outside m' B v hf).mono he he')

/-- `saveK`: `kept` into `aDQ`'s first nine words. -/
theorem saveK_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) (hq : aDQ < N) (hw : 7 ≤ w) :
    WP isa (.block saveK) s fun t => Ws t B Z w N ∧ Keys.Frame B w [aDQ] [] s.mem t.mem ∧ Keep [.t0] s t ∧
      word t.mem B (arr w aDQ) = s.gpr .s1 ∧ word t.mem B (arr w aDQ + 8) = s.gpr .s2 ∧
      word t.mem B (arr w aDQ + 16) = s.gpr .s3 ∧ word t.mem B (arr w aDQ + 24) = s.gpr .s4 ∧
      word t.mem B (arr w aDQ + 32) = s.gpr .a0 ∧ word t.mem B (arr w aDQ + 40) = s.gpr .a1 ∧
      word t.mem B (arr w aDQ + 48) = s.gpr .a2 ∧ word t.mem B (arr w aDQ + 56) = s.gpr .a3 ∧
      word t.mem B (arr w aDQ + 64) = s.gpr .a6 := by
  have fit := h.arr_fit hq
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have al := arr_al w aDQ
  unfold saveK
  refine ptr_ok h (by decide) (by decide) (show aDQ < 2048 by decide) ?_
  generalize hA : arr w aDQ = A at fit al
  refine WP.mono (WP.keep [] (Q := fun t => t.mem =
      ((((((((s.mem.writeW (off B A) (s.gpr .s1)).writeW (off B (A + 8)) (s.gpr .s2)).writeW (off B (A + 16)) (s.gpr .s3)).writeW (off B (A + 24)) (s.gpr .s4)).writeW (off B (A + 32)) (s.gpr .a0)).writeW (off B (A + 40)) (s.gpr .a1)).writeW (off B (A + 48)) (s.gpr .a2)).writeW (off B (A + 56)) (s.gpr .a3)).writeW (off B (A + 64)) (s.gpr .a6)) (by
    brun [BitVec.add_zero, h.scr.st (show A + 8 ≤ Z by omega), h.scr.al8 (show A + 8 ≤ Z by omega) al,
      h.scr.st (show A + 8 + 8 ≤ Z by omega), h.scr.al8 (show A + 8 + 8 ≤ Z by omega) (by omega),
      h.scr.st (show A + 16 + 8 ≤ Z by omega), h.scr.al8 (show A + 16 + 8 ≤ Z by omega) (by omega),
      h.scr.st (show A + 24 + 8 ≤ Z by omega), h.scr.al8 (show A + 24 + 8 ≤ Z by omega) (by omega),
      h.scr.st (show A + 32 + 8 ≤ Z by omega), h.scr.al8 (show A + 32 + 8 ≤ Z by omega) (by omega),
      h.scr.st (show A + 40 + 8 ≤ Z by omega), h.scr.al8 (show A + 40 + 8 ≤ Z by omega) (by omega),
      h.scr.st (show A + 48 + 8 ≤ Z by omega), h.scr.al8 (show A + 48 + 8 ≤ Z by omega) (by omega),
      h.scr.st (show A + 56 + 8 ≤ Z by omega), h.scr.al8 (show A + 56 + 8 ≤ Z by omega) (by omega),
      h.scr.st (show A + 64 + 8 ≤ Z by omega), h.scr.al8 (show A + 64 + 8 ≤ Z by omega) (by omega)])
    (by rfl) (by rfl)) fun t ⟨tm, k⟩ => ?_
  have kk : Keep [.t0] s t := ((Keep.write _ _ _).trans k).mono (by decide)
  refine ⟨h.of_keep kk, ?_, kk, ?_⟩
  · have o : Outside B A 72 s.mem t.mem := by
      rw [tm]
      repeat refine Outside.writeW_in ?_ _ (by omega) (by omega) (by omega)
      exact Outside.refl _ _ _ _
    rw [← hA] at o
    exact Keys.Frame.of_arr (o := aDQ) (d := 0) (n := 72) (by simpa using o) (by omega) (by simp)
  · rw [tm]
    simp (disch := omega) only [wr_other, Mont.word_writeW_self, and_self]

/-- `restoreK`: `kept` back from `aDQ`'s first nine words. -/
theorem restoreK_ok {u : State} {B : Addr} {Z w N : Nat} (h : Ws u B Z w N) (hq : aDQ < N) (hw : 7 ≤ w)
    {v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64}
    (e1 : word u.mem B (arr w aDQ) = v1) (e2 : word u.mem B (arr w aDQ + 8) = v2)
    (e3 : word u.mem B (arr w aDQ + 16) = v3) (e4 : word u.mem B (arr w aDQ + 24) = v4)
    (e5 : word u.mem B (arr w aDQ + 32) = v5) (e6 : word u.mem B (arr w aDQ + 40) = v6)
    (e7 : word u.mem B (arr w aDQ + 48) = v7) (e8 : word u.mem B (arr w aDQ + 56) = v8)
    (e9 : word u.mem B (arr w aDQ + 64) = v9) :
    WP isa (.block restoreK) u fun t => (t.gpr .s1 = v1 ∧ t.gpr .s2 = v2 ∧ t.gpr .s3 = v3 ∧ t.gpr .s4 = v4 ∧
      t.gpr .a0 = v5 ∧ t.gpr .a1 = v6 ∧ t.gpr .a2 = v7 ∧ t.gpr .a3 = v8 ∧ t.gpr .a6 = v9 ∧ t.mem = u.mem) ∧
      Keep [.t0, .s1, .s2, .s3, .s4, .a0, .a1, .a2, .a3, .a6] u t := by
  have fit := h.arr_fit hq
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have al := arr_al w aDQ
  unfold restoreK
  refine ptr_ok h (by decide) (by decide) (show aDQ < 2048 by decide) ?_
  generalize hA : arr w aDQ = A at fit al e1 e2 e3 e4 e5 e6 e7 e8 e9
  have r1 : u.mem.readW (off B A) 64 = v1 := e1
  have r2 : u.mem.readW (off B (A + 8)) 64 = v2 := e2
  have r3 : u.mem.readW (off B (A + 16)) 64 = v3 := e3
  have r4 : u.mem.readW (off B (A + 24)) 64 = v4 := e4
  have r5 : u.mem.readW (off B (A + 32)) 64 = v5 := e5
  have r6 : u.mem.readW (off B (A + 40)) 64 = v6 := e6
  have r7 : u.mem.readW (off B (A + 48)) 64 = v7 := e7
  have r8 : u.mem.readW (off B (A + 56)) 64 = v8 := e8
  have r9 : u.mem.readW (off B (A + 64)) 64 = v9 := e9
  refine WP.mono (WP.keep [.t0, .s1, .s2, .s3, .s4, .a0, .a1, .a2, .a3, .a6] (Q := fun t =>
      t.gpr .s1 = v1 ∧ t.gpr .s2 = v2 ∧ t.gpr .s3 = v3 ∧ t.gpr .s4 = v4 ∧ t.gpr .a0 = v5 ∧ t.gpr .a1 = v6 ∧
        t.gpr .a2 = v7 ∧ t.gpr .a3 = v8 ∧ t.gpr .a6 = v9 ∧ t.mem = u.mem) (by
    brun [BitVec.add_zero, r1, r2, r3, r4, r5, r6, r7, r8, r9,
      h.scr.ld (show A + 8 ≤ Z by omega), h.scr.al8 (show A + 8 ≤ Z by omega) al,
      h.scr.ld (show A + 8 + 8 ≤ Z by omega), h.scr.al8 (show A + 8 + 8 ≤ Z by omega) (by omega),
      h.scr.ld (show A + 16 + 8 ≤ Z by omega), h.scr.al8 (show A + 16 + 8 ≤ Z by omega) (by omega),
      h.scr.ld (show A + 24 + 8 ≤ Z by omega), h.scr.al8 (show A + 24 + 8 ≤ Z by omega) (by omega),
      h.scr.ld (show A + 32 + 8 ≤ Z by omega), h.scr.al8 (show A + 32 + 8 ≤ Z by omega) (by omega),
      h.scr.ld (show A + 40 + 8 ≤ Z by omega), h.scr.al8 (show A + 40 + 8 ≤ Z by omega) (by omega),
      h.scr.ld (show A + 48 + 8 ≤ Z by omega), h.scr.al8 (show A + 48 + 8 ≤ Z by omega) (by omega),
      h.scr.ld (show A + 56 + 8 ≤ Z by omega), h.scr.al8 (show A + 56 + 8 ≤ Z by omega) (by omega),
      h.scr.ld (show A + 64 + 8 ≤ Z by omega), h.scr.al8 (show A + 64 + 8 ≤ Z by omega) (by omega)])
    (by rfl) (by rfl)) fun t ⟨q, k⟩ => ⟨q, ((Keep.write _ _ _).trans k).mono (by decide)⟩

/-- The registers the divisions by words write. -/
abbrev dwRegs : List Reg :=
  [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

/-- `divWP a r`: `[r] := d mod (2 ⌊[a] / 2⌋)` by words, exact for a divisor of
exactly `w / 2` words. -/
theorem divWP_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w nArr) {a r : Nat} (ha : a = aP ∨ a = aQ)
    (hr : r = aDR2 ∨ r = aDR3) (hw : 8 ≤ w) (hw2 : w % 2 = 0) :
    WP isa (seqs (divWP a r)) s fun t => Ws t B Z w nArr ∧ Keys.Frame B w [r, aDD, aDT] [] s.mem t.mem ∧
      Keep dwRegs s t ∧
      (InW w (2 * (num s.mem B w a / 2)) → num t.mem B w r = num s.mem B w aD % (2 * (num s.mem B w a / 2))) := by
  have ha' : a < nArr ∧ a ≠ aDD ∧ a ≠ aDT ∧ a ≠ aD ∧ a ≠ r := by
    rcases ha with rfl | rfl <;> rcases hr with rfl | rfl <;> decide
  have hr' : r < nArr ∧ r ≠ aDD ∧ r ≠ aDT ∧ r ≠ aD := by rcases hr with rfl | rfl <;> decide
  have hS : S w = 8 * (w + 2) := rfl
  have fit : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  unfold divWP
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (InvBatch.zeroWs_ok h (j := r) hr'.1 (by decide)) fun t1 ⟨w1, f1, z1, k1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (Keys.copy_ok w1 (o := aDD) (a := a) (by decide) ha'.1 (by decide) (Ne.symm ha'.2.1))
    fun t2 ⟨w2, f2, v2, k2, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (clrLowW_ok w2 (j := aDD) (by decide) (by decide)) fun t3 ⟨w3, f3, v3, k3, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (fixTop_ok w3 (m := aDD) (by decide) (by decide) (by omega))
    fun t4 ⟨w4, f4, v4, p4, _, _, k4, _⟩ => ?_
  rw [show seqs [VG.Impl.Rsa.RISCV64.WordDiv.divW aD r aDD aDT] = VG.Impl.Rsa.RISCV64.WordDiv.divW aD r aDD aDT
    from rfl]
  -- `[r]` is zero in `t4`, `[aD]` and `[a]` as in `s`.
  have n1r : num t4.mem B w r = 0 := by
    rw [f4.num (by simp; exact hr'.2.1.symm) (by simp) (fit _ hr'.1),
      f3.num (by simp; exact hr'.2.1.symm) (by simp) (fit _ hr'.1),
      f2.num (by simp; exact hr'.2.1.symm) (by simp) (fit _ hr'.1), z1]
  have nD : num t4.mem B w aD = num s.mem B w aD := by
    rw [f4.num (by decide) (by simp) (fit _ (by decide)), f3.num (by decide) (by simp) (fit _ (by decide)),
      f2.num (by decide) (by simp) (fit _ (by decide)), f1.num (by simp; exact hr'.2.2.2) (by simp) (fit _ (by decide))]
  have na : num t1.mem B w a = num s.mem B w a :=
    f1.num (by simp; exact Ne.symm ha'.2.2.2.2) (by simp) (fit _ ha'.1)
  rw [v2, na] at v3
  have r0 : wordsVal t4.mem B (arr w r) (w / 2) = 0 := wordsVal_zero_part (a := 0) (c := w / 2) n1r (by omega) |>.symm ▸
    by simp
  refine WP.mono (divW_ok w4 (a := aD) (r := r) (m := aDD) (t := aDT) (by decide) (by decide) hr'.1 (by decide)
    (by decide) hr'.2.2.2 hr'.2.1 hr'.2.2.1 (by decide) (by decide) hw hw2 r0 p4)
    fun t ⟨w5, f5, k5, x5, top5, hi5⟩ => ?_
  refine ⟨w5, ?_, ?_, fun hin => ?_⟩
  · exact (f1.mono (by simp) (by simp)).trans ((f2.mono (by simp) (by simp)).trans ((f3.mono (by simp) (by simp)).trans
      ((f4.mono (by simp) (by simp)).trans (f5.mono (by simp) (by simp)))))
  · exact ((((k1.mono (rs' := dwRegs) (by decide)).trans (k2.mono (rs' := dwRegs) (by decide))).trans
      (k3.mono (rs' := dwRegs) (by decide))).trans (k4.mono (rs' := dwRegs) (by decide))).trans
      (k5.mono (rs' := dwRegs) (by decide)) |>.mono (by decide)
  · -- The divisor is `2 ⌊[a] / 2⌋`, whose top word is not zero.
    have mv : wordsVal t3.mem B (arr w aDD) (w / 2) = 2 * (num s.mem B w a / 2) :=
      words_low (w := w) (v := w / 2) (by omega) (show num t3.mem B w aDD = _ by rw [v3, Nat.mul_comm]) hin.2
    have tp := top_pos (m := t3.mem) (B := B) (d := arr w aDD) (v := w / 2) (by omega) (by rw [mv]; exact hin.1)
    have hne : ¬ (word t3.mem B (arr w aDD + 8 * (w / 2 - 1))).toNat = 0 := by omega
    rw [v4, mv, ite_eq_right hne, Nat.add_zero, nD] at x5
    refine num_of_low (v := w / 2) (by omega) x5 top5 ?_
    rw [hi5]
    exact wordsVal_zero_part n1r (by omega)

/-- A balanced key, from the lengths. -/
abbrev Bal (s0 : State) : Prop := pL s0 % 8 = 0 ∧ 4 * wOf s0 = pL s0 ∧ pL s0 = qL s0 ∧ 32 ≤ pL s0

/-- Under the mask, for a balanced key, `p - 1` and `q - 1` are numbers of
exactly `w / 2` words. -/
theorem bal_inW {s0 : State} (hv : Spec.Rsa.modulusValid (Nv s0) (kOf s0) = true) (hb : Bal s0)
    {X₁ X₂ V : Nat} (hx : 0 < Pv s0 → X₁ = Nv s0 / Pv s0 ∧ X₂ = Nv s0 % Pv s0)
    (hm : maskOf (Pv s0) (Qv s0) X₁ X₂ V = true) :
    InW (wOf s0) (2 * (Pv s0 / 2)) ∧ InW (wOf s0) (2 * (Qv s0 / 2)) := by
  obtain ⟨hp8, h4w, hpq, h32⟩ := hb
  simp only [maskOf, decide_eq_true_eq] at hm
  obtain ⟨podd, e1, e2, -⟩ := hm
  obtain ⟨x1, x2⟩ := hx (by omega)
  have hpqn : Pv s0 * Qv s0 = Nv s0 := VG.Proof.Rsa.mul_of_div (by rw [← x1, e1]) (by rw [← x2, e2])
  have hn := (VG.Proof.Rsa.modulusValid_facts hv).2
  have hkw : 8 * wOf s0 ≤ kOf s0 + 7 := by simp only [wOf]; omega
  have pv := pv_lt s0
  have qv := qv_lt s0
  rw [← hpq, ← h4w, ← Nat.mul_assoc] at qv
  rw [← h4w, ← Nat.mul_assoc] at pv
  rw [show 8 * 4 * wOf s0 = 32 * wOf s0 by omega] at pv qv
  have hw2 : wOf s0 % 2 = 0 := by omega
  have e64 : 64 * (wOf s0 / 2) = 32 * wOf s0 := by omega
  have plo := balanced_lo hpqn hn hkw qv (by omega) hw2
  have qlo := balanced_lo (p := Qv s0) (q := Pv s0) (by rw [Nat.mul_comm]; exact hpqn) hn hkw pv (by omega) hw2
  have qodd : Qv s0 % 2 = 1 := VG.Proof.Rsa.odd_factor (by rw [Nat.mul_comm]; exact hpqn) (VG.Proof.Rsa.modulusValid_facts hv).1
  exact ⟨⟨by omega, by rw [e64]; omega⟩, ⟨by omega, by rw [e64]; omega⟩⟩

/-- `shape`: `t0 = 0` exactly for `p_len` (`s4`) a multiple of 8 and at least
32, equal to `q_len` (`s6`) and to `4 w` (`s9`). -/
theorem shape_ok {s : State} {pl ql w : Nat} (h4 : s.gpr .s4 = BitVec.ofNat 64 pl)
    (h6 : s.gpr .s6 = BitVec.ofNat 64 ql) (h9 : s.gpr .s9 = BitVec.ofNat 64 w) (hpl : pl < 2 ^ 32)
    (hql : ql < 2 ^ 32) (hw : w ≤ 1024) :
    WP isa (.block shape) s fun t =>
      ((t.gpr .t0 = 0 ↔ (pl % 8 = 0 ∧ 4 * w = pl ∧ pl = ql ∧ 32 ≤ pl)) ∧ t.mem = s.mem) ∧ Keep [.t0, .t1] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have hP : ∀ x : Nat, x < 2 ^ 32 → (BitVec.ofNat 64 x).toNat = x := fun x hx => by
    rw [BitVec.toNat_ofNat]; omega
  unfold shape
  brun [h4, h6, h9, cv_exec_li32]
  simp only [Keys.bv_or0, Keys.bv_xor0, Keys.bv_lt_ite0]
  have l2 : BitVec.ofNat 64 w <<< 2 = BitVec.ofNat 64 (4 * w) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hP w (by omega), BitVec.toNat_ofNat]; omega
  simp only [l2, Keys.bv_and7, hP pl hpl, BitVec.lt_def, show (32#64).toNat = 32 from rfl, Nat.not_lt]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨h1, ?_, ?_, h4⟩
    · have := congrArg BitVec.toNat h2; rw [hP _ (by omega), hP pl hpl] at this; exact this
    · have := congrArg BitVec.toNat h3; rw [hP pl hpl, hP ql hql] at this; exact this
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, by rw [h2]⟩, by rw [h3]⟩, h4⟩

open VG.Impl.Rsa.RISCV64.Keys (storeBytes restore)
open VG.Impl.Rsa.RISCV64.CrtValues (code stores valid front mask checks invPart)

/-- The outputs, as the function leaves them. -/
structure Out (s0 : State) (X₁ X₂ V X R₂ R₃ : Nat) (u : State) : Prop where
  ce : CE s0 u
  dp : Spec.Rsa.bytesAt u.mem (s0.gpr .a0) (pL s0) = if maskOf (Pv s0) (Qv s0) X₁ X₂ V then
    Spec.Rsa.i2osp (R₂ % 256 ^ pL s0) (pL s0) else List.replicate (pL s0) 0
  dq : Spec.Rsa.bytesAt u.mem (s0.gpr .a2) (qL s0) = if maskOf (Pv s0) (Qv s0) X₁ X₂ V then
    Spec.Rsa.i2osp (R₃ % 256 ^ qL s0) (qL s0) else List.replicate (qL s0) 0
  qi : Spec.Rsa.bytesAt u.mem (s0.gpr .a4) (pL s0) = if maskOf (Pv s0) (Qv s0) X₁ X₂ V then
    Spec.Rsa.i2osp (X % 256 ^ pL s0) (pL s0) else List.replicate (pL s0) 0
  a0 : (u.gpr .a0).toNat = if maskOf (Pv s0) (Qv s0) X₁ X₂ V then 1 else 0

theorem stores_ok {s0 t : State} (h : PreC s0) {X₁ X₂ V X : Nat} {Mi : Mem} (dd : Dd s0 X₁ X₂ V Mi t)
    (hqi : Spec.Rsa.bytesAt Mi (s0.gpr .a4) (pL s0) = if maskOf (Pv s0) (Qv s0) X₁ X₂ V then
      Spec.Rsa.i2osp (X % 256 ^ pL s0) (pL s0) else List.replicate (pL s0) 0) :
    WP isa stores t (Out s0 X₁ X₂ V X (num t.mem (bOf s0) (wOf s0) aDR2) (num t.mem (bOf s0) (wOf s0) aDR3)) := by
  have ⟨w1, w2⟩ := h.w_bounds
  have hz := h.zk
  have ⟨lp, lq⟩ := lt32 h
  have hp1 := h.p1
  have hq1 := h.q1
  have hp2 := h.p2
  have hq2 := h.q2
  have pw : pL s0 ≤ 8 * wOf s0 := by
    show (stackArg s0 1).toNat ≤ 8 * (((s0.gpr .a7).toNat + 7) / 8); omega_arith
  have qw : qL s0 ≤ 8 * wOf s0 := by
    show (stackArg s0 3).toNat ≤ 8 * (((s0.gpr .a7).toNat + 7) / 8); omega_arith
  have ws := dd.ws
  have c := dd.cb
  have bit : slot t.mem (bOf s0) sMask ≤ 1 := by rw [dd.mask]; exact bit_ite
  have Z64 : zOf s0 ≤ 2 ^ 64 := by have := h.ws; simp only [zOf]; omega_arith
  have fitZ : ∀ j < nArr, arr (wOf s0) j + 8 * wOf s0 ≤ zOf s0 := fun j hj => by
    have := Nat.le_trans (arr_end hj) h.fits; simp only [S] at this; omega_arith
  -- The regions of the outputs.
  have wdp : (s0.gpr .a0).toNat + pL s0 ≤ 2 ^ 64 := by have := h.wdp; rw [h.h1] at this; exact this
  have wdq : (s0.gpr .a2).toNat + qL s0 ≤ 2 ^ 64 := by have := h.wdq; rw [h.h3] at this; exact this
  have dpw : (⟨s0.gpr .a0, pL s0⟩ : Region) ∈ s0.wr := by rw [← h.dpR_eq, h.hwr]; simp
  have dqw : (⟨s0.gpr .a2, qL s0⟩ : Region) ∈ s0.wr := by rw [← h.dqR_eq, h.hwr]; simp
  have dps : (⟨s0.gpr .a0, pL s0⟩ : Region).Disjoint (sR s0) := by rw [← h.dpR_eq]; exact h.dps
  have dqs : (⟨s0.gpr .a2, qL s0⟩ : Region).Disjoint (sR s0) := by rw [← h.dqR_eq]; exact h.dqs
  have qis : (⟨s0.gpr .a4, pL s0⟩ : Region).Disjoint (sR s0) := by rw [← h.qiR_eq]; exact h.qis
  have dp_dq : (⟨s0.gpr .a0, pL s0⟩ : Region).Disjoint ⟨s0.gpr .a2, qL s0⟩ := by
    rw [← h.dpR_eq, ← h.dqR_eq]; exact h.dpdq
  have qi_dp : (⟨s0.gpr .a4, pL s0⟩ : Region).Disjoint ⟨s0.gpr .a0, pL s0⟩ := by
    rw [← h.qiR_eq, ← h.dpR_eq]; exact fun a ha hb => h.dpqi a hb ha
  have qi_dq : (⟨s0.gpr .a4, pL s0⟩ : Region).Disjoint ⟨s0.gpr .a2, qL s0⟩ := by
    rw [← h.qiR_eq, ← h.dqR_eq]; exact fun a ha hb => h.dqqi a hb ha
  unfold stores
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (mask_ok ws bit) fun t1 ⟨⟨m4, m1⟩, k1⟩ => ?_
  have ws1 := ws.of_keep k1
  have c1 := c.of_keep k1 m1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (storeBytes_ok ws1 (j := aDR2) (by decide) (by decide) c1.a2
    (by rw [c1.s4]; exact toNat_ofNat_eq _) (by decide) (by decide) (by decide) m4 hp1 pw
    (fun i hi => by rw [c1.wr]; exact bytes_in dpw (by omega_arith) i hi) (bytes_sep dps (by omega_arith)) wdp)
    fun t2 ⟨ws2, b2, o2, k2⟩ => ?_
  have c2 := c1.of_out k2 o2 dps (by omega_arith)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (storeBytes_ok ws2 (j := aDR3) (b := decide (slot t.mem (bOf s0) sMask ≠ 0)) (by decide) (by decide) c2.a3
    (by rw [c2.s6]; exact toNat_ofNat_eq _) (by decide) (by decide) (by decide)
    (by rw [k2.gpr (by decide)]; exact m4) hq1 qw
    (fun i hi => by rw [c2.wr]; exact bytes_in dqw (by omega_arith) i hi) (bytes_sep dqs (by omega_arith)) wdq)
    fun t3 ⟨ws3, b3, o3, k3⟩ => ?_
  have c3 := c2.of_out k3 o3 dqs (by omega_arith)
  have hz3 := ws3.hdr_le
  have nw3 := ws3.nowrap
  have hM : sMask + 8 ≤ zOf s0 := by simp only [hdr_eq, sMask] at hz3 ⊢; omega_arith
  have hb : WP isa (.block [.load .d .a0 .s11 sMask]) t3 fun u =>
      (u.gpr .a0 = word t3.mem (bOf s0) sMask ∧ u.mem = t3.mem) ∧ Keep [.a0] t3 u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [ws3.s11, add_ofNat_zero', ws3.scr.al8 (d := sMask) (by omega_arith) (by decide),
      ws3.scr.ld (d := sMask) (n := 8) hM, show sMask < 2048 by decide]
  refine WP.mono hb fun u ⟨⟨ua, um⟩, ku⟩ => ?_
  have W1 : ∀ {m : Mem} {d : Nat}, wordsVal m (bOf s0) d 1 = (word m (bOf s0) d).toNat := by
    intro m d; simp [wordsVal]
  have r3 : num t2.mem (bOf s0) (wOf s0) aDR3 = num t.mem (bOf s0) (wOf s0) aDR3 := by
    exact (wordsVal_of_out (d := arr (wOf s0) aDR3) (k := wOf s0) dps o2 (fitZ _ (by decide)) Z64).trans (by rw [m1])
  have sM : slot t3.mem (bOf s0) sMask = slot t.mem (bOf s0) sMask := by
    have e := wordsVal_of_out (d := sMask) (k := 1) dqs o3 (by omega_arith) Z64
    have e2 := wordsVal_of_out (d := sMask) (k := 1) dps o2 (by omega_arith) Z64
    rw [W1, W1] at e e2
    change (word t3.mem (bOf s0) sMask).toNat = (word t.mem (bOf s0) sMask).toNat
    rw [e, e2, m1]
  have keepB : ∀ {O : Addr} {L : Nat}, (⟨O, L⟩ : Region).Disjoint ⟨s0.gpr .a2, qL s0⟩ → L ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt u.mem O L = Spec.Rsa.bytesAt t2.mem O L := fun hd hL => by
    rw [um]; exact bytesAt_congr fun c hc => zeros_keep hd hL o3 hc
  refine ⟨⟨(ku.gpr (by decide)).trans c3.s11, (ku.gpr (by decide)).trans c3.ra, ku.2.1.trans c3.rd,
    ku.2.2.trans c3.wr, fun i hi => by rw [um]; exact c3.hdr i hi⟩, ?_, ?_, ?_, ?_⟩
  · rw [keepB dp_dq (by omega_arith)]
    by_cases hm : maskOf (Pv s0) (Qv s0) X₁ X₂ V = true
    · simp only [hm, ↓reduceIte]
      rw [bytes_of_store (m := t1.mem) (B := bOf s0) (w := wOf s0) (j := aDR2) pw (fun c hc => by rw [b2 c hc, dd.mask]; simp [hm]), m1]
    · simp only [hm, ↓reduceIte, Bool.false_eq_true]
      exact bytesAt_zero fun c hc => by rw [b2 c hc, dd.mask]; simp [hm]
  · rw [um]
    by_cases hm : maskOf (Pv s0) (Qv s0) X₁ X₂ V = true
    · simp only [hm, ↓reduceIte]
      rw [bytes_of_store (m := t2.mem) (B := bOf s0) (w := wOf s0) (j := aDR3) qw (fun c hc => by rw [b3 c hc, dd.mask]; simp [hm]), r3]
    · simp only [hm, ↓reduceIte, Bool.false_eq_true]
      exact bytesAt_zero fun c hc => by rw [b3 c hc, dd.mask]; simp [hm]
  · rw [keepB qi_dq (by omega_arith), ← hqi]
    refine bytesAt_congr fun c hc => ?_
    rw [zeros_keep qi_dp (by omega_arith) o2 hc, m1]
    exact dd.cb.frame _ (bytes_past qis hc (by omega_arith))
  · rw [ua]
    change slot t3.mem (bOf s0) sMask = _
    rw [sM, dd.mask]

/-- The registers changed across the divisions by words and the restore. -/
abbrev dwOut : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a4, .a5, .a7, .s0]

/-- `dPartsW`: the divisions of `d` by words, for a balanced key. -/
theorem dPartsW_ok {s0 s : State} (h : PreC s0) (hv : Spec.Rsa.modulusValid (Nv s0) (kOf s0) = true)
    (hb : Bal s0) {X₁ X₂ V X : Nat} (iv : Iv s0 X₁ X₂ V X s) : WP isa dPartsW s (Dd s0 X₁ X₂ V s.mem) := by
  have ⟨w1', w2'⟩ := h.w_bounds
  have fit : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => iv.ws.fit64 hj
  have hS : S (wOf s0) = 8 * (wOf s0 + 2) := rfl
  have hw8 : 8 ≤ wOf s0 := w1'
  have hw2 : wOf s0 % 2 = 0 := by obtain ⟨_, h4, _, _⟩ := hb; omega
  unfold dPartsW
  rw [List.append_assoc, List.append_assoc, wp_seqs_append (by simp) (by simp [divWP]),
    show seqs [.block saveK] = .block saveK from rfl]
  refine WP.mono (saveK_ok iv.ws (by decide) (by omega)) fun t1 ⟨ws1, f1, k1, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ => ?_
  rw [wp_seqs_append (by simp [divWP]) (by simp [divWP])]
  refine WP.mono (divWP_ok ws1 (a := aP) (r := aDR2) (.inl rfl) (.inl rfl) hw8 hw2) fun t2 ⟨ws2, f2, k2, v2⟩ => ?_
  rw [wp_seqs_append (by simp [divWP]) (by simp)]
  refine WP.mono (divWP_ok ws2 (a := aQ) (r := aDR3) (.inr rfl) (.inr rfl) hw8 hw2) fun t3 ⟨ws3, f3, k3, v3⟩ => ?_
  rw [show seqs [.block restoreK] = .block restoreK from rfl]
  -- `aDQ`'s words, as `saveK` left them.
  have kq : ∀ i < wOf s0 + 2, word t3.mem (bOf s0) (arr (wOf s0) aDQ + 8 * i) =
      word t1.mem (bOf s0) (arr (wOf s0) aDQ + 8 * i) := fun i hi => by
    rw [f3.word hi (by decide) (by simp) (fit _ (by decide)), f2.word hi (by decide) (by simp) (fit _ (by decide))]
  have q : ∀ {c : Nat}, c % 8 = 0 → c < 72 → word t3.mem (bOf s0) (arr (wOf s0) aDQ + c) =
      word t1.mem (bOf s0) (arr (wOf s0) aDQ + c) := fun {c} h8 h72 => by
    have := kq (c / 8) (by omega)
    rwa [show 8 * (c / 8) = c by omega] at this
  have q0 := kq 0 (by omega)
  rw [Nat.mul_zero, Nat.add_zero] at q0
  refine WP.mono (restoreK_ok ws3 (by decide) (by omega) (q0.trans e1) ((q (by decide) (by decide)).trans e2)
    ((q (by decide) (by decide)).trans e3) ((q (by decide) (by decide)).trans e4) ((q (by decide) (by decide)).trans e5)
    ((q (by decide) (by decide)).trans e6) ((q (by decide) (by decide)).trans e7) ((q (by decide) (by decide)).trans e8)
    ((q (by decide) (by decide)).trans e9)) fun u ⟨⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, um⟩, k4⟩ => ?_
  have F : Keys.Frame (bOf s0) (wOf s0) [aDQ, aDR2, aDD, aDT, aDR3] [] s.mem u.mem := by
    rw [um]
    exact (f1.mono (by simp) (by simp)).trans ((f2.mono (by simp) (by simp)).trans (f3.mono (by simp) (by simp)))
  -- The registers: those of `kept` restored, the rest kept or in `dwOut`.
  have K : Keep dwOut s u := by
    refine ⟨fun r hr => ?_, k4.2.1.trans (k3.2.1.trans (k2.2.1.trans k1.2.1)),
      k4.2.2.trans (k3.2.2.trans (k2.2.2.trans k1.2.2))⟩
    by_cases hk : r ∈ VG.Impl.Rsa.RISCV64.CrtValues.kept
    · simp only [VG.Impl.Rsa.RISCV64.CrtValues.kept, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [r1, r2, r3, r4, r5, r6, r7, r8, r9]
    · have sub : ∀ x ∈ (([.t0] ++ dwRegs) ++ dwRegs) ++ [.t0, .s1, .s2, .s3, .s4, .a0, .a1, .a2, .a3, .a6],
          x ∈ dwOut ∨ x ∈ VG.Impl.Rsa.RISCV64.CrtValues.kept := by decide
      have hn : r ∉ (([.t0] ++ dwRegs) ++ dwRegs) ++ [.t0, .s1, .s2, .s3, .s4, .a0, .a1, .a2, .a3, .a6] :=
        fun hm => (sub r hm).elim hr hk
      exact (((k1.trans k2).trans k3).trans k4).gpr hn
  have cb := iv.cb.of_frame F (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      have := h.fits
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> exact Nat.le_trans (arr_end (by decide)) this)
    (by simp) (by have := iv.ws.hdr_le; omega) K
  refine ⟨cb, ws3.of_keep k4, ?_, fun hm hp => ?_, fun hm hq => ?_⟩
  · rw [F.slot (by decide) (by simp)]; exact iv.mask
  · have i := (bal_inW hv hb iv.x hm).1
    have p1 : num t1.mem (bOf s0) (wOf s0) aP = Pv s0 := by rw [f1.num (by decide) (by simp) (fit _ (by decide)), iv.p]
    have d1 : num t1.mem (bOf s0) (wOf s0) aD = Dv s0 := by rw [f1.num (by decide) (by simp) (fit _ (by decide)), iv.d]
    rw [p1] at v2
    rw [um, f3.num (by decide) (by simp) (fit _ (by decide)), v2 i, d1]
  · have i := (bal_inW hv hb iv.x hm).2
    have q2 : num t2.mem (bOf s0) (wOf s0) aQ = Qv s0 := by
      rw [f2.num (by decide) (by simp) (fit _ (by decide)), f1.num (by decide) (by simp) (fit _ (by decide)), iv.q]
    have d2 : num t2.mem (bOf s0) (wOf s0) aD = Dv s0 := by
      rw [f2.num (by decide) (by simp) (fit _ (by decide)), f1.num (by decide) (by simp) (fit _ (by decide)), iv.d]
    rw [q2] at v3
    rw [um, v3 i, d2]

/-- `dPartsAll`: the divisions of `d`, by words for a balanced key. -/
theorem dPartsAll_ok {s0 s : State} (h : PreC s0) (hv : Spec.Rsa.modulusValid (Nv s0) (kOf s0) = true)
    {X₁ X₂ V X : Nat} (iv : Iv s0 X₁ X₂ V X s) : WP isa dPartsAll s (Dd s0 X₁ X₂ V s.mem) := by
  have ⟨lp, lq⟩ := lt32 h
  unfold dPartsAll
  rw [WP.seq_iff]
  refine WP.mono (shape_ok (pl := pL s0) (ql := qL s0) (w := wOf s0) (iv.cb.s4.trans (toNat_ofNat_eq _))
    (iv.cb.s6.trans (toNat_ofNat_eq _)) iv.ws.s9 lp lq iv.ws.wle) fun t ⟨⟨hiff, tm⟩, kt⟩ => ?_
  have iv' : Iv s0 X₁ X₂ V X t := by
    refine ⟨?_, iv.ws.of_keep kt, ?_, ?_, ?_, ?_, iv.x, iv.ic, ?_, ?_⟩ <;> rw [tm]
    exacts [iv.cb.of_keep kt tm, iv.p, iv.q, iv.d, iv.ddz, iv.mask, iv.qi]
  rw [← tm]
  refine WP.ite _ (Steps.eval_zero t .t0) (fun hz => ?_) (fun _ => dParts_ok h iv')
  exact dPartsW_ok h hv (hiff.mp (by simpa using hz)) iv'

/-- The outputs of a valid modulus, and what the values in them are. -/
def VP (s0 u : State) : Prop :=
  ∃ X₁ X₂ V X R₂ R₃, Out s0 X₁ X₂ V X R₂ R₃ u ∧ (0 < Pv s0 → X₁ = Nv s0 / Pv s0 ∧ X₂ = Nv s0 % Pv s0) ∧
    IC s0 V X ∧ (maskOf (Pv s0) (Qv s0) X₁ X₂ V = true → 0 < 2 * (Pv s0 / 2) → R₂ = Dv s0 % (2 * (Pv s0 / 2))) ∧
    (maskOf (Pv s0) (Qv s0) X₁ X₂ V = true → 0 < 2 * (Qv s0 / 2) → R₃ = Dv s0 % (2 * (Qv s0 / 2)))

/-- `front`: the set-up, the loads, the checks and the inverse. -/
theorem front_ok [InvLaw] {s0 s : State} (h : PreC s0) (c : CB s0 s0.mem s) :
    WP isa front s fun t => ∃ X₁ X₂ V X, Iv s0 X₁ X₂ V X t := by
  unfold front
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (setup_ok h c) fun t1 ⟨c1, w1, z1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (loads_ok h c1 w1 z1) fun t2 l2 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (checks_ok h l2) fun t3 ⟨X₁, X₂, ck⟩ => ?_
  exact WP.mono (invPart_ok h ck) fun t4 ⟨V, X, iv⟩ => ⟨X₁, X₂, V, X, iv⟩

theorem valid_ok [InvLaw] {s0 s : State} (h : PreC s0) (hv : Spec.Rsa.modulusValid (Nv s0) (kOf s0) = true)
    (c : CB s0 s0.mem s) : WP isa valid s (VP s0) := by
  unfold valid
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (front_ok h c) fun t4 ⟨X₁, X₂, V, X, iv⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _), show seqs [stores] = stores from rfl]
  refine WP.mono (dPartsAll_ok h hv iv) fun t5 dd => ?_
  exact WP.mono (stores_ok h dd iv.qi) fun u o => ⟨X₁, X₂, V, X, _, _, o, iv.x, iv.ic, dd.r2, dd.r3⟩

theorem bytesAt_length (m : Mem) (p : Addr) (L : Nat) : (Spec.Rsa.bytesAt m p L).length = L := by
  simp [Spec.Rsa.bytesAt]

theorem pow256 (L : Nat) : (256 : Nat) ^ L = 2 ^ (8 * L) := by
  rw [Nat.pow_mul]

theorem post_valid {s0 u v : State} (h : PreC s0)
    (hv : Spec.Rsa.modulusValid (Nv s0) (kOf s0) = true) (vp : VP s0 u) (hm : v.mem = u.mem)
    (ha : v.gpr .a0 = u.gpr .a0) : fnPost s0 v := by
  obtain ⟨X₁, X₂, V, X, R₂, R₃, o, hx, ic, r2, r3⟩ := vp
  have e : Mv s0 = 2 * (Pv s0 / 2) + 1 := by simp only [Mv]; omega_arith
  have h2 := ic.vx
  rw [e] at h2
  unfold fnPost
  by_cases hk : maskOf (Pv s0) (Qv s0) X₁ X₂ V = true
  · have K := VG.Proof.Rsa.CrtValues.crtKey_masked (nb := nB s0) (pb := pB s0) (qb := qB s0) (db := dB s0)
      (by rw [bytesAt_length]; exact hv) (by rw [bytesAt_length, bytesAt_length]; exact h.p2)
      (by rw [bytesAt_length, bytesAt_length]; exact h.q2) hx h2 (r2 hk) (r3 hk)
    simp only [bytesAt_length, ← pow256] at K
    rw [K]
    simp only [hk, ↓reduceIte, Option.map_some, Spec.Rsa.writtenAll, List.map_cons, List.map_nil, hm]
    refine ⟨?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, ha, o.a0]
      simp [hk]
    · rw [o.dp, o.dq, o.qi]
      simp [hk]
  · have K := VG.Proof.Rsa.CrtValues.crtKey_masked (nb := nB s0) (pb := pB s0) (qb := qB s0) (db := dB s0)
      (R₂ := Dv s0 % (2 * (Pv s0 / 2))) (R₃ := Dv s0 % (2 * (Qv s0 / 2)))
      (by rw [bytesAt_length]; exact hv) (by rw [bytesAt_length, bytesAt_length]; exact h.p2)
      (by rw [bytesAt_length, bytesAt_length]; exact h.q2) hx h2 (fun _ => rfl) (fun _ => rfl)
    simp only [bytesAt_length, ← pow256] at K
    rw [K]
    simp only [hk, ↓reduceIte, Option.map_none, Spec.Rsa.writtenAll, hm, Bool.false_eq_true]
    refine ⟨?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, ha, o.a0]
      simp [hk]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      rw [o.dp, o.dq, o.qi]
      simp [hk]

theorem post_fail {s0 u v : State} (hv : ¬ Spec.Rsa.modulusValid (Nv s0) (kOf s0) = true)
    (hw : Spec.Rsa.writtenAll u.mem (outs s0) ((u.gpr .a0).setWidth 32) none) (hm : v.mem = u.mem)
    (ha : v.gpr .a0 = u.gpr .a0) : fnPost s0 v := by
  unfold fnPost
  have e : Spec.Rsa.crtKey (nB s0) (pB s0) (qB s0) (dB s0) = none := by
    unfold Spec.Rsa.crtKey
    simp only [bytesAt_length]
    rw [ite_eq_right_iff.mpr fun hc => absurd hc.1 hv]
  rw [e, hm, ha]
  exact hw

theorem code_correct [InvLaw] (s : State) (hpre : (Spec.Rsa.crtValuesContract RISCV64.abi).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ fnPost s t := by
  show WP isa code s fun t => abiPreserved s t ∧ fnPost s t
  have h := preC_of hpre
  refine WP.mono (WP.rdwr (Q := fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra ∧
    fnPost s t) ?_) fun t ⟨⟨hp, hra, hpost⟩, _, _, hsp⟩ => ⟨⟨hp, hsp, hra⟩, hpost⟩
  unfold code
  rw [WP.seq_iff]
  refine WP.mono (entry_ok h) fun e c => ?_
  rw [WP.seq_iff]
  refine WP.mono (nCheck_ok h c) fun t ⟨t0, tm, kt⟩ => ?_
  have ct := c.of_keep kt tm
  rw [WP.seq_iff]
  refine WP.ite _ (Steps.eval_zero t .s0) (fun hz => ?_) (fun hz => ?_)
  · have hz' : t.gpr .s0 = 0 := by simpa using hz
    have hv := t0.mp hz'
    refine WP.mono (valid_ok h hv ct) fun u vp => ?_
    have o := vp.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
    exact WP.mono (restore_ok' h o.ce) fun v ⟨vp', vra, vm, va⟩ => ⟨vp', vra, post_valid h hv vp vm va⟩
  · have hz' : t.gpr .s0 ≠ 0 := by simpa using hz
    have hv : ¬ Spec.Rsa.modulusValid (Nv s) (kOf s) = true := fun e => hz' (t0.mpr e)
    refine WP.mono (fail_ok h ct) fun u ⟨ce, hw⟩ => ?_
    exact WP.mono (restore_ok' h ce) fun v ⟨vp', vra, vm, va⟩ => ⟨vp', vra, post_fail hv hw vm va⟩

end VG.Proof.Rsa.RISCV64.CrtValues
