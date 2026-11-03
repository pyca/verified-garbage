module

public import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValFront
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyDiv
public import VerifiedGarbage.Proof.Rsa.RISCV64.RdOps
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.Octets

/-!
# `vg_rsa_crt_values` on RISC-V: the set-up, the reads and the checks of `p q = n`

`setup_ok`, `loads_ok`: the working space of `w = ⌈n_len / 8⌉` words, its
arrays zeroed and `n`, `p`, `q` and `d` read (`Ld`); `checks_ok`: `p`'s low
bit, and two bits whose product, for an odd `p`, is whether `n / p = q` and
`n mod p = 0` (`Ck`): `p q mod 2^(64 w) = n` and 1 when `p_len + q_len ≤ 8 w`
(`mulChecks_ok`), else the two checks by the division (`divChecks_ok`).
-/

-- separate module: its proofs (the reads and the checks of `p q = n`) are not re-checked with every
-- change to the inverse's

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.CrtValues

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs setW zeroArrays load copy bitOf eqS mov)
open VG.Impl.Rsa.RISCV64.CrtValues (setup loads checks divChecks mulChecks lenTest nArr aOne aZero aQ aP aDQ aDR aDD aDT aDR2 aDR3 aD
  sPodd sE1 sE2 sE3 sMask)

/-! ## The values -/

abbrev kOf (s0 : State) : Nat := (s0.gpr .a7).toNat
abbrev wOf (s0 : State) : Nat := (kOf s0 + 7) / 8
abbrev pL (s0 : State) : Nat := (stackArg s0 1).toNat
abbrev qL (s0 : State) : Nat := (stackArg s0 3).toNat
abbrev dL (s0 : State) : Nat := (stackArg s0 5).toNat
abbrev pB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (stackArg s0 0) (pL s0)
abbrev qB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (stackArg s0 2) (qL s0)
abbrev dB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (stackArg s0 4) (dL s0)
abbrev Nv (s0 : State) : Nat := Spec.Rsa.os2ip (nB s0)
abbrev Pv (s0 : State) : Nat := Spec.Rsa.os2ip (pB s0)
abbrev Qv (s0 : State) : Nat := Spec.Rsa.os2ip (qB s0)
abbrev Dv (s0 : State) : Nat := Spec.Rsa.os2ip (dB s0)

/-- `p` and `q` are below `2^(8 p_len)` and `2^(8 q_len)`. -/
theorem pv_lt (s0 : State) : Pv s0 < 2 ^ (8 * pL s0) := by
  have h := VG.Proof.Rsa.lt_of_os2ip (pB s0)
  have hl : (pB s0).length = pL s0 := by simp [Spec.Rsa.bytesAt]
  rw [hl] at h; rw [Nat.pow_mul]; exact h

theorem qv_lt (s0 : State) : Qv s0 < 2 ^ (8 * qL s0) := by
  have h := VG.Proof.Rsa.lt_of_os2ip (qB s0)
  have hl : (qB s0).length = qL s0 := by simp [Spec.Rsa.bytesAt]
  rw [hl] at h; rw [Nat.pow_mul]; exact h

/-- Index side conditions. -/
macro "cvx" : tactic => `(tactic| ((try simp only [nArr, aOne, aQ, aP, aDQ, aDR, aDD, aDT, aDR2, aDR3, aD,
  sPodd, sE1, sE2, sE3, sMask, aZero, hdr_eq, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
  implies_true, and_true, true_and, ne_eq]) <;> first | decide | omega_arith))

theorem PreC.w_bounds {s0 : State} (h : PreC s0) : 8 ≤ wOf s0 ∧ wOf s0 ≤ 128 := by
  have := h.k1; have := h.k2
  exact ⟨show 8 ≤ ((s0.gpr .a7).toNat + 7) / 8 by omega_arith, show ((s0.gpr .a7).toNat + 7) / 8 ≤ 128 by omega_arith⟩

theorem PreC.fits {s0 : State} (h : PreC s0) : arr (wOf s0) nArr ≤ zOf s0 := by
  have := h.zk; have := h.k1; have := h.k2
  show 256 + 25 * (8 * (((s0.gpr .a7).toNat + 7) / 8 + 2)) ≤ zOf s0
  omega_arith

theorem len_ofNat (s0 : State) : s0.gpr .a7 = BitVec.ofNat 64 (kOf s0) := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem toNat_ofNat_eq (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## The set-up and the reads -/

/-- The working space after the reads. -/
structure Ld (s0 t : State) : Prop where
  cb : CB s0 s0.mem t
  ws : Ws t (bOf s0) (zOf s0) (wOf s0) nArr
  n : num t.mem (bOf s0) (wOf s0) aDQ = Nv s0
  p : num t.mem (bOf s0) (wOf s0) aP = Pv s0
  q : num t.mem (bOf s0) (wOf s0) aQ = Qv s0
  d : num t.mem (bOf s0) (wOf s0) aD = Dv s0
  zero : ∀ j < nArr, j ≠ aDQ → j ≠ aP → j ≠ aQ → j ≠ aD →
    wordsVal t.mem (bOf s0) (arr (wOf s0) j) (wOf s0 + 2) = 0

theorem setup_ok {s0 s : State} (h : PreC s0) (c : CB s0 s0.mem s) :
    WP isa setup s fun t => CB s0 s0.mem t ∧ Ws t (bOf s0) (zOf s0) (wOf s0) nArr ∧
      ∀ j < nArr, wordsVal t.mem (bOf s0) (arr (wOf s0) j) (wOf s0 + 2) = 0 := by
  have ⟨w1, w2⟩ := h.w_bounds
  have hk := h.k2
  have hz := h.zk
  rw [setup, WP.seq_iff]
  refine WP.mono (setW_ok (k := kOf s0) (by rw [c.s2]; exact len_ofNat s0) (show (s0.gpr .a7).toNat < 2 ^ 32 by omega_arith))
    fun u ⟨⟨u9, u10, um⟩, ku⟩ => ?_
  have cu := c.of_keep ku um
  have wu : Ws u (bOf s0) (zOf s0) (wOf s0) nArr :=
    ⟨Scr.of_mem (by rw [cu.wr]; exact h.sR_wr) h.ws h.al, h.fits, by omega_arith, by omega_arith, u9, u10,
      cu.s11⟩
  refine WP.mono (zeroArrays_ok wu (by decide) (by decide) (by decide)) fun t ⟨wt, ft, zt, kt⟩ => ?_
  refine ⟨cu.of_frame ft (fun j hj => ?_) (by simp) (by simp only [hdr_eq, zOf] at hz ⊢; omega_arith) kt, wt, zt⟩
  have := List.mem_range.mp hj
  exact Nat.le_trans (arr_end (w := wOf s0) this) h.fits

/-- One read: the `L` bytes of the input region at `P` into the zero array `j`. -/
theorem ld1_ok {s0 t : State} (h : PreC s0) (c : CB s0 s0.mem t) (ws : Ws t (bOf s0) (zOf s0) (wOf s0) nArr)
    {j : Nat} (hj : j < nArr) {P : Addr} {L : Nat} {src len : Reg} (hl1 : len ≠ .t1)
    (hr : (⟨P, L⟩ : Region) ∈ s0.rd) (hd : (⟨P, L⟩ : Region).Disjoint (sR s0)) (hL64 : L ≤ 2 ^ 64)
    (hs : t.gpr src = P) (hl : t.gpr len = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hLw : L ≤ 8 * wOf s0)
    (hz : num t.mem (bOf s0) (wOf s0) j = 0) :
    WP isa (load j src len) t fun u => CB s0 s0.mem u ∧ Ws u (bOf s0) (zOf s0) (wOf s0) nArr ∧
      Keys.Frame (bOf s0) (wOf s0) [j] [] t.mem u.mem ∧
      num u.mem (bOf s0) (wOf s0) j = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem P L) := by
  have hz' := h.zk
  refine WP.mono (load_ok ws hj (by decide) hl1 hs hl hL hLw
    (fun i hi => by rw [c.rd]; exact inRegions_left (bytes_in hr hL64 i hi)) (bytes_sep hd hL64) hz)
    fun u ⟨wu, fu, vu, ku, _⟩ => ?_
  refine ⟨c.of_frame fu (by simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
    implies_true, and_true]; exact Nat.le_trans (arr_end hj) h.fits) (by simp)
    (by simp only [hdr_eq, zOf] at hz' ⊢; omega_arith) ku, wu, fu, ?_⟩
  rw [vu, c.bytes hd hL64]

theorem PreC.nR_rd {s : State} (h : PreC s) : nR s ∈ s.rd := by rw [h.hrd]; simp
theorem PreC.pR_rd {s : State} (h : PreC s) : pR s ∈ s.rd := by rw [h.hrd]; simp
theorem PreC.qR_rd {s : State} (h : PreC s) : qR s ∈ s.rd := by rw [h.hrd]; simp
theorem PreC.dR_rd {s : State} (h : PreC s) : dR s ∈ s.rd := by rw [h.hrd]; simp

theorem loads_ok {s0 s : State} (h : PreC s0) (c : CB s0 s0.mem s) (ws : Ws s (bOf s0) (zOf s0) (wOf s0) nArr)
    (hz : ∀ j < nArr, wordsVal s.mem (bOf s0) (arr (wOf s0) j) (wOf s0 + 2) = 0) :
    WP isa loads s (Ld s0) := by
  have ⟨w1, w2⟩ := h.w_bounds
  have hk1 := h.k1
  have hk2 := h.k2
  have hp1 := h.p1
  have hp2 := h.p2
  have hq1 := h.q1
  have hq2 := h.q2
  have hd1 := h.d1
  have hd2 := h.d2
  have hK8 : (s0.gpr .a7).toNat ≤ 8 * wOf s0 := by show (s0.gpr .a7).toNat ≤ 8 * (((s0.gpr .a7).toNat + 7) / 8); omega_arith
  have nz : ∀ {m : Mem} {j}, j < nArr → wordsVal m (bOf s0) (arr (wOf s0) j) (wOf s0 + 2) = 0 →
      num m (bOf s0) (wOf s0) j = 0 := fun _ h0 => wordsVal_zero_part (a := 0) h0 (by omega_arith)
  have fit : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => ws.fit64 hj
  unfold loads
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ld1_ok h c ws (j := aDQ) (by cvx) (by decide) h.nR_rd h.ns (by have := h.wn; omega_arith)
    c.s1 (by rw [c.s2]; exact len_ofNat s0) (by omega_arith) hK8 (nz (by cvx) (hz _ (by cvx))))
    fun t1 ⟨c1, w1', f1, v1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ld1_ok h c1 w1' (j := aP) (by cvx) (by decide) h.pR_rd h.ps (by have := h.wp; omega_arith)
    c1.s3 (by rw [c1.s4]; exact toNat_ofNat_eq _) hp1 (by omega_arith)
    (by rw [f1.num (by cvx) (by simp) (fit _ (by cvx))]; exact nz (by cvx) (hz _ (by cvx))))
    fun t2 ⟨c2, w2', f2, v2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ld1_ok h c2 w2' (j := aQ) (by cvx) (by decide) h.qR_rd h.qs (by have := h.wq; omega_arith)
    c2.s5 (by rw [c2.s6]; exact toNat_ofNat_eq _) hq1 (by omega_arith)
    (by rw [f2.num (by cvx) (by simp) (fit _ (by cvx)), f1.num (by cvx) (by simp) (fit _ (by cvx))]
        exact nz (by cvx) (hz _ (by cvx))))
    fun t3 ⟨c3, w3', f3, v3⟩ => ?_
  refine WP.mono (ld1_ok h c3 w3' (j := aD) (by cvx) (by decide) h.dR_rd h.ds (by have := h.wd; omega_arith)
    c3.a0 (by rw [c3.a1]; exact toNat_ofNat_eq _) hd1 (by omega_arith)
    (by rw [f3.num (by cvx) (by simp) (fit _ (by cvx)), f2.num (by cvx) (by simp) (fit _ (by cvx)),
          f1.num (by cvx) (by simp) (fit _ (by cvx))]
        exact nz (by cvx) (hz _ (by cvx))))
    fun t ⟨c4, w4, f4, v4⟩ => ?_
  refine ⟨c4, w4, ?_, ?_, ?_, v4, fun j hj e1 e2 e3 e4 => ?_⟩
  · rw [f4.num (by cvx) (by simp) (fit _ (by cvx)), f3.num (by cvx) (by simp) (fit _ (by cvx)),
      f2.num (by cvx) (by simp) (fit _ (by cvx)), v1]
  · rw [f4.num (by cvx) (by simp) (fit _ (by cvx)), f3.num (by cvx) (by simp) (fit _ (by cvx)), v2]
  · rw [f4.num (by cvx) (by simp) (fit _ (by cvx)), v3]
  · rw [f4.full (fun _ hk => by rw [List.mem_singleton.mp hk]; exact Ne.symm e4) (by simp) (fit j hj), f3.full (fun _ hk => by rw [List.mem_singleton.mp hk]; exact Ne.symm e3) (by simp) (fit j hj),
      f2.full (fun _ hk => by rw [List.mem_singleton.mp hk]; exact Ne.symm e2) (by simp) (fit j hj), f1.full (fun _ hk => by rw [List.mem_singleton.mp hk]; exact Ne.symm e1) (by simp) (fit j hj)]
    exact hz j hj

/-! ## The checks of `p q = n` -/

/-- After the checks: `X₁` and `X₂` are `n / p` and `n mod p` for `p > 0`, and the two
checks' bits, with `p`'s, give whether `X₁ = q` and `X₂ = 0`. -/
structure Ck (s0 : State) (X₁ X₂ : Nat) (t : State) : Prop where
  cb : CB s0 s0.mem t
  ws : Ws t (bOf s0) (zOf s0) (wOf s0) nArr
  p : num t.mem (bOf s0) (wOf s0) aP = Pv s0
  q : num t.mem (bOf s0) (wOf s0) aQ = Qv s0
  d : num t.mem (bOf s0) (wOf s0) aD = Dv s0
  x : 0 < Pv s0 → X₁ = Nv s0 / Pv s0 ∧ X₂ = Nv s0 % Pv s0
  podd : slot t.mem (bOf s0) sPodd = Pv s0 % 2
  b1 : slot t.mem (bOf s0) sE1 ≤ 1
  b2 : slot t.mem (bOf s0) sE2 ≤ 1
  e12 : Pv s0 % 2 * slot t.mem (bOf s0) sE1 * slot t.mem (bOf s0) sE2 =
    Pv s0 % 2 * (if X₁ = Qv s0 then 1 else 0) * (if X₂ = 0 then 1 else 0)
  ddz : word t.mem (bOf s0) (arr (wOf s0) aDD + 8 * wOf s0) = 0

theorem word_w_zero {m : Mem} {B : Addr} {w j : Nat} (h : wordsVal m B (arr w j) (w + 2) = 0) :
    word m B (arr w j + 8 * w) = 0 := by
  have := wordsVal_zero_part (a := w) (c := 1) h (by omega_arith)
  simp only [wordsVal, Nat.mul_zero, Nat.add_zero] at this
  exact BitVec.eq_of_toNat_eq (by simpa using this)

/-- A step of the body: `CB` kept, for a frame of arrays of the working space and slots of the header. -/
theorem CB.step {s0 s t : State} (h : PreC s0) {M : Mem} (c : CB s0 M s) {js ds : List Nat}
    (f : Keys.Frame (bOf s0) (wOf s0) js ds s.mem t.mem) (hjs : ∀ j ∈ js, j < nArr)
    (hds : ∀ d ∈ ds, 96 ≤ d ∧ d + 8 ≤ Keys.hdr) {rs : List Reg} (k : Keep rs s t)
    (hr : ∀ r ∈ cbRegs, r ∉ rs := by decide) : CB s0 M t := by
  have hz := h.zk
  exact c.of_frame f (fun j hj => Nat.le_trans (arr_end (hjs j hj)) h.fits) hds
    (by simp only [hdr_eq, zOf] at hz ⊢; omega_arith) k hr

/-- `Ck` from the two checks' exact bits. -/
theorem Ck.of_bits {s0 t : State} {X₁ X₂ : Nat} (cb : CB s0 s0.mem t) (ws : Ws t (bOf s0) (zOf s0) (wOf s0) nArr)
    (p : num t.mem (bOf s0) (wOf s0) aP = Pv s0) (q : num t.mem (bOf s0) (wOf s0) aQ = Qv s0)
    (d : num t.mem (bOf s0) (wOf s0) aD = Dv s0) (x : 0 < Pv s0 → X₁ = Nv s0 / Pv s0 ∧ X₂ = Nv s0 % Pv s0)
    (podd : slot t.mem (bOf s0) sPodd = Pv s0 % 2)
    (e1 : slot t.mem (bOf s0) sE1 = if X₁ = Qv s0 then 1 else 0)
    (e2 : slot t.mem (bOf s0) sE2 = if X₂ = 0 then 1 else 0)
    (ddz : word t.mem (bOf s0) (arr (wOf s0) aDD + 8 * wOf s0) = 0) : Ck s0 X₁ X₂ t :=
  ⟨cb, ws, p, q, d, x, podd, by rw [e1]; split <;> simp, by rw [e2]; split <;> simp, by rw [e1, e2], ddz⟩

theorem divChecks_ok {s0 s : State} (h : PreC s0) (l : Ld s0 s) :
    WP isa divChecks s fun t => ∃ X₁ X₂, Ck s0 X₁ X₂ t := by
  have ws := l.ws
  have fit : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => ws.fit64 hj
  have ⟨w1, w2⟩ := h.w_bounds
  unfold divChecks
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok ws (o := aDD) (a := aP) (by cvx) (by cvx) (by decide) (by cvx))
    fun t1 ⟨w1', f1, v1, k1, o1⟩ => ?_
  have c1 := l.cb.step h f1 (by cvx) (by simp) k1
  have z1 : word t1.mem (bOf s0) (arr (wOf s0) aDD + 8 * wOf s0) = 0 := by
    rw [o1.word (.inr (by omega_arith)) (by have := fit aDD (by cvx); simp only [S] at this; omega_arith)]
    exact word_w_zero (l.zero _ (by cvx) (by cvx) (by cvx) (by cvx) (by cvx))
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (bitOf_ok w1' (j := aP) (sl := sPodd) (by cvx) (by decide) (by cvx) (by cvx))
    fun t2 ⟨w2', f2, v2, k2⟩ => ?_
  have c2 := c1.step h f2 (by simp) (by cvx) k2
  have p1 : num t1.mem (bOf s0) (wOf s0) aP = Pv s0 := by
    rw [f1.num (by cvx) (by simp) (fit _ (by cvx)), l.p]
  rw [p1] at v2
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have dd2 : num t2.mem (bOf s0) (wOf s0) aDD = Pv s0 := by
    rw [f2.num (by simp) (by cvx) (fit _ (by cvx)), v1, l.p]
  have n2 : num t2.mem (bOf s0) (wOf s0) aDQ = Nv s0 := by
    rw [f2.num (by simp) (by cvx) (fit _ (by cvx)), f1.num (by cvx) (by simp) (fit _ (by cvx)), l.n]
  have z2 : word t2.mem (bOf s0) (arr (wOf s0) aDD + 8 * wOf s0) = 0 := by
    rw [f2.word (i := wOf s0) (by omega_arith) (by simp) (by cvx) (fit _ (by cvx))]; exact z1
  have hl : t2.gpr .s4 = BitVec.ofNat 64 (pL s0) := c2.s4.trans (toNat_ofNat_eq _)
  refine WP.mono (divL_ok w2' (q := aDQ) (r := aDR) (d := aDD) (by cvx) (by cvx) (by cvx) (by decide)
    (by cvx) (by cvx) (by cvx) hl h.p1 (by have := h.p2; simp only [wOf, kOf, pL] at *; omega) z2
    (by rw [dd2]; exact pv_lt s0))
    fun t3 ⟨w3, f3, k3, _, v3⟩ => ?_
  have c3 := c2.step h f3 (by cvx) (by simp) k3
  rw [dd2, n2] at v3
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok w3 (d := sE1) (a := aDQ) (b := aQ) (by cvx) (by cvx) (by decide) (by cvx) (by cvx))
    fun t4 ⟨w4, f4, v4, k4⟩ => ?_
  have c4 := c3.step h f4 (by simp) (by cvx) k4
  refine WP.mono (eqS_ok w4 (d := sE2) (a := aDR) (b := aZero) (by cvx) (by cvx) (by decide) (by cvx) (by cvx))
    fun t ⟨w5, f5, v5, k5⟩ => ?_
  have c5 := c4.step h f5 (by simp) (by cvx) k5
  -- The values, through the frames.
  have keepA : ∀ j < nArr, j ≠ aDD → j ≠ aDQ → j ≠ aDR → j ≠ aDT →
      num t.mem (bOf s0) (wOf s0) j = num s.mem (bOf s0) (wOf s0) j := fun j hj a1 a2 a3 a4 => by
    rw [f5.num (by simp) (by cvx) (fit _ hj), f4.num (by simp) (by cvx) (fit _ hj),
      f3.num (by simp [Ne.symm a2, Ne.symm a3]) (by simp) (fit _ hj),
      f2.num (by simp) (by cvx) (fit _ hj), f1.num (by simp [Ne.symm a1]) (by simp) (fit _ hj)]
  refine ⟨num t3.mem (bOf s0) (wOf s0) aDQ, num t3.mem (bOf s0) (wOf s0) aDR, Ck.of_bits c5 w5
    (by rw [keepA _ (by cvx) (by cvx) (by cvx) (by cvx) (by cvx), l.p])
    (by rw [keepA _ (by cvx) (by cvx) (by cvx) (by cvx) (by cvx), l.q])
    (by rw [keepA _ (by cvx) (by cvx) (by cvx) (by cvx) (by cvx), l.d])
    (fun hp => ⟨(v3 hp).1, (v3 hp).2.2.1⟩) ?_ ?_ ?_ ?_⟩
  · rw [f5.slot (by cvx) (by cvx), f4.slot (by cvx) (by cvx), f3.slot (by cvx) (by simp), v2]
  · have q3 : num t3.mem (bOf s0) (wOf s0) aQ = Qv s0 := by
      rw [f3.num (j := aQ) (by cvx) (by simp) (fit _ (by cvx)), f2.num (j := aQ) (by simp) (by cvx) (fit _ (by cvx)),
        f1.num (j := aQ) (by cvx) (by simp) (fit _ (by cvx)), l.q]
    rw [f5.slot (by cvx) (by cvx), v4, q3]
  · have z4 : num t4.mem (bOf s0) (wOf s0) aZero = 0 := by
      rw [f4.num (j := aZero) (by simp) (by cvx) (fit _ (by cvx)), f3.num (j := aZero) (by cvx) (by simp) (fit _ (by cvx)),
        f2.num (j := aZero) (by simp) (by cvx) (fit _ (by cvx)), f1.num (j := aZero) (by cvx) (by simp) (fit _ (by cvx))]
      exact wordsVal_zero_part (a := 0) (l.zero aZero (by cvx) (by cvx) (by cvx) (by cvx) (by cvx)) (by omega_arith)
    rw [v5, z4, f4.num (j := aDR) (by simp) (by cvx) (fit _ (by cvx))]
  · rw [f5.word (i := wOf s0) (by omega_arith) (by simp) (by cvx) (fit _ (by cvx)),
      f4.word (i := wOf s0) (by omega_arith) (by simp) (by cvx) (fit _ (by cvx)),
      f3.word (i := wOf s0) (by omega_arith) (by cvx) (by simp) (fit _ (by cvx))]
    exact z2

/-! ## The checks of `p q = n` by the product -/

/-- For `p q < R`, an odd `p`'s bit times `p q mod R = n` is its bit times
`n / p = q` and `n mod p = 0`. -/
theorem pq_bits {P Q N R : Nat} (hR : P * Q < R) :
    P % 2 * (if P * Q % R = N then 1 else 0) * 1 =
      P % 2 * (if N / P = Q then 1 else 0) * (if N % P = 0 then 1 else 0) := by
  rcases Nat.mod_two_eq_zero_or_one P with e | e
  · simp [e]
  have hP : 0 < P := by omega
  rw [Nat.mod_eq_of_lt hR]
  by_cases hq : P * Q = N
  · subst hq
    simp [Nat.mul_div_cancel_left _ hP]
  · have : ¬ (N / P = Q ∧ N % P = 0) := fun ⟨a, b⟩ => hq (by
      have := Nat.div_add_mod N P
      rw [a, b, Nat.add_zero] at this; exact this)
    by_cases a : N / P = Q <;> by_cases b : N % P = 0 <;> simp_all

theorem Ld.of_keep {s0 s t : State} (l : Ld s0 s) {rs : List Reg} (k : Keep rs s t) (hm : t.mem = s.mem)
    (hr : ∀ r ∈ cbRegs, r ∉ rs := by decide) (h9 : .s9 ∉ rs := by decide) (h10 : .s10 ∉ rs := by decide)
    (h11 : .s11 ∉ rs := by decide) : Ld s0 t :=
  ⟨l.cb.of_keep k hm hr, l.ws.of_keep k h9 h10 h11, by rw [hm]; exact l.n, by rw [hm]; exact l.p,
    by rw [hm]; exact l.q, by rw [hm]; exact l.d, fun j hj a b c d => by rw [hm]; exact l.zero j hj a b c d⟩

/-- `t5 := [8 w < p_len + q_len]`: zero when the lengths fit `w` words. -/
theorem lenTest_ok {s0 s : State} (h : PreC s0) (l : Ld s0 s) :
    WP isa (.block lenTest) s fun t => ((t.gpr .t5 = 0 ↔ pL s0 + qL s0 ≤ 8 * wOf s0) ∧ t.mem = s.mem) ∧
      Keep [.t5, .t6] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have ⟨lp, lq⟩ := lt32 h
  have ⟨w1, w2⟩ := h.w_bounds
  have hlt : (BitVec.ofNat 64 (wOf s0) <<< 3 < stackArg s0 1 + stackArg s0 3) ↔
      8 * wOf s0 < pL s0 + qL s0 := by
    rw [BitVec.lt_def, BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    simp only [pL, qL] at *
    omega_arith
  brun [lenTest, l.cb.s4, l.cb.s6, l.ws.s9]
  by_cases hc : BitVec.ofNat 64 (wOf s0) <<< 3 < stackArg s0 1 + stackArg s0 3
  · have := hlt.mp hc
    simp only [hc, ↓reduceIte]
    exact ⟨fun e => absurd e (by decide), fun e => by omega⟩
  · have := mt hlt.mpr hc
    simp only [hc, ↓reduceIte]
    exact ⟨fun _ => by omega, fun _ => trivial⟩

/-- `a2`, `a3`, `a6` into `s0`, `s7`, `a5`. -/
theorem save3_ok (s : State) :
    WP isa (.block [mov .s0 .a2, mov .s7 .a3, mov .a5 .a6]) s fun u =>
      (u.gpr .s0 = s.gpr .a2 ∧ u.gpr .s7 = s.gpr .a3 ∧ u.gpr .a5 = s.gpr .a6 ∧ u.mem = s.mem) ∧
        Keep [.s0, .s7, .a5] s u := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [mov, add_ofNat_zero']

/-- And back. -/
theorem restore3_ok (s : State) :
    WP isa (.block [mov .a2 .s0, mov .a3 .s7, mov .a6 .a5]) s fun u =>
      (u.gpr .a2 = s.gpr .s0 ∧ u.gpr .a3 = s.gpr .s7 ∧ u.gpr .a6 = s.gpr .a5 ∧ u.mem = s.mem) ∧
        Keep [.a2, .a3, .a6] s u := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [mov, add_ofNat_zero']

theorem mulChecks_ok {s0 s : State} (h : PreC s0) (l : Ld s0 s) (hlen : pL s0 + qL s0 ≤ 8 * wOf s0) :
    WP isa mulChecks s fun t => ∃ X₁ X₂, Ck s0 X₁ X₂ t := by
  have ws := l.ws
  have fit : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => ws.fit64 hj
  have ⟨w1, w2⟩ := h.w_bounds
  unfold mulChecks
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (bitOf_ok ws (j := aP) (sl := sPodd) (by cvx) (by decide) (by cvx) (by cvx))
    fun t1 ⟨w1', f1, v1, k1⟩ => ?_
  have c1 := l.cb.step h f1 (by simp) (by cvx) k1
  rw [l.p] at v1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (save3_ok t1) fun t2 ⟨⟨e0, e7, e5, m2⟩, k2⟩ => ?_
  have c2 := c1.of_keep k2 m2
  have w2' := w1'.of_keep k2
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have z2 : num t2.mem (bOf s0) (wOf s0) aDR = 0 := by
    clear hlen
    have hz0 := l.zero aDR (by cvx) (by cvx) (by cvx) (by cvx) (by cvx)
    rw [m2, f1.num (by simp) (by cvx) (fit _ (by cvx))]
    have e := wordsVal_zero_part (a := 0) (c := wOf s0) hz0 (by omega_arith)
    rw [Nat.mul_zero, Nat.add_zero] at e
    exact e
  refine WP.mono (mulLow_ok w2' (o := aDR) (y := aP) (x := aQ) (by cvx) (by cvx) (by cvx) (by decide)
    (by cvx) (by cvx) z2) fun t3 ⟨w3, f3, _, v3, k3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (restore3_ok t3) fun t4 ⟨⟨r2, r3, r6, m4⟩, k4⟩ => ?_
  -- `CB` back: the registers of `CB` are `t2`'s.
  have k24 : Keep [.s0, .s7, .a5, .t0, .t1, .t2, .t3, .t4, .t5, .t6, .a4, .s8] t2 t4 := by
    refine ⟨fun r hr => ?_, k4.2.1.trans k3.2.1, k4.2.2.trans k3.2.2⟩
    by_cases a2 : r = .a2
    · subst a2; rw [r2, k3.gpr (by decide), e0, k2.gpr (by decide)]
    by_cases a3 : r = .a3
    · subst a3; rw [r3, k3.gpr (by decide), e7, k2.gpr (by decide)]
    by_cases a6 : r = .a6
    · subst a6; rw [r6, k3.gpr (by decide), e5, k2.gpr (by decide)]
    rw [k4.gpr (by revert a2 a3 a6; cases r <;> decide), k3.gpr (by revert hr a2 a3 a6; cases r <;> decide)]
  have f3' : Keys.Frame (bOf s0) (wOf s0) [aDR] [] t2.mem t4.mem := by rw [m4]; exact f3
  have c4 := c2.step h f3' (by cvx) (by simp) k24
  have w4 := w3.of_keep k4
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok w4 (d := sE1) (a := aDR) (b := aDQ) (by cvx) (by cvx) (by decide) (by cvx) (by cvx))
    fun t5 ⟨w5, f5, v5, k5⟩ => ?_
  have c5 := c4.step h f5 (by simp) (by cvx) k5
  refine WP.mono (eqS_ok w5 (d := sE2) (a := aZero) (b := aZero) (by cvx) (by cvx) (by decide) (by cvx) (by cvx))
    fun t ⟨w6, f6, v6, k6⟩ => ?_
  have c6 := c5.step h f6 (by simp) (by cvx) k6
  -- The arrays but `aDR`, through the frames.
  have keepA : ∀ j < nArr, j ≠ aDR →
      num t.mem (bOf s0) (wOf s0) j = num s.mem (bOf s0) (wOf s0) j := fun j hj a1 => by
    rw [f6.num (by simp) (by cvx) (fit _ hj), f5.num (by simp) (by cvx) (fit _ hj),
      f3'.num (by simp [Ne.symm a1]) (by simp) (fit _ hj), m2, f1.num (by simp) (by cvx) (fit _ hj)]
  have pq : num t4.mem (bOf s0) (wOf s0) aDR = Pv s0 * Qv s0 % 2 ^ (64 * wOf s0) := by
    rw [m4, v3, m2, f1.num (by simp) (by cvx) (fit _ (by cvx)), f1.num (j := aQ) (by simp) (by cvx) (fit _ (by cvx)),
      l.p, l.q]
  have n4 : num t4.mem (bOf s0) (wOf s0) aDQ = Nv s0 := by
    rw [f3'.num (by cvx) (by simp) (fit _ (by cvx)), m2, f1.num (by simp) (by cvx) (fit _ (by cvx)), l.n]
  have hR : Pv s0 * Qv s0 < 2 ^ (64 * wOf s0) := by
    have := Nat.mul_lt_mul'' (pv_lt s0) (qv_lt s0)
    rw [← Nat.pow_add] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega_arith))
  have se1 : slot t.mem (bOf s0) sE1 = if Pv s0 * Qv s0 % 2 ^ (64 * wOf s0) = Nv s0 then 1 else 0 := by
    rw [f6.slot (by cvx) (by cvx), v5, pq, n4]
  have se2 : slot t.mem (bOf s0) sE2 = 1 := by rw [v6]; simp
  refine ⟨Nv s0 / Pv s0, Nv s0 % Pv s0, c6, w6,
    by rw [keepA _ (by cvx) (by cvx), l.p], by rw [keepA _ (by cvx) (by cvx), l.q],
    by rw [keepA _ (by cvx) (by cvx), l.d], fun _ => ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f6.slot (by cvx) (by cvx), f5.slot (by cvx) (by cvx), f3'.slot (by cvx) (by simp), m2, v1]
  · rw [se1]; split <;> simp
  · rw [se2]
  · rw [se1, se2]; exact pq_bits hR
  · rw [f6.word (i := wOf s0) (by omega_arith) (by simp) (by cvx) (fit _ (by cvx)),
      f5.word (i := wOf s0) (by omega_arith) (by simp) (by cvx) (fit _ (by cvx)),
      f3'.word (i := wOf s0) (by omega_arith) (by cvx) (by simp) (fit _ (by cvx)), m2,
      f1.word (i := wOf s0) (by omega_arith) (by simp) (by cvx) (fit _ (by cvx))]
    exact word_w_zero (l.zero _ (by cvx) (by cvx) (by cvx) (by cvx) (by cvx))

theorem checks_ok {s0 s : State} (h : PreC s0) (l : Ld s0 s) :
    WP isa checks s fun t => ∃ X₁ X₂, Ck s0 X₁ X₂ t := by
  unfold checks
  rw [WP.seq_iff]
  refine WP.mono (lenTest_ok h l) fun u ⟨⟨e, m⟩, k⟩ => ?_
  have lu := l.of_keep k m
  refine WP.ite _ (Steps.eval_zero u .t5) (fun hz => ?_) (fun _ => divChecks_ok h lu)
  exact mulChecks_ok h lu (e.mp (by simpa using hz))

end VG.Proof.Rsa.RISCV64.CrtValues
