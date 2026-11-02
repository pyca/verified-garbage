module

public import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValFront
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyDiv
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyInv
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_crt_values` on RISC-V: the set-up, the reads and the checks of `p q = n`

`setup_ok`, `loads_ok`: the working space of `w = ⌈n_len / 8⌉` words, its
arrays zeroed and `n`, `p`, `q` and `d` read (`Ld`); `checks_ok`: `p`'s low
bit, and whether `n / p = q` and `n mod p = 0` (`Ck`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.CrtValues

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs setW zeroArrays load copy bitOf eqS aZero)
open VG.Impl.Rsa.RISCV64.CrtValues (setup loads checks nArr aOne aQ aP aDQ aDR aDD aDT aDR2 aDR3 aD
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

/-- After the checks: `X₁` and `X₂` are `n / p` and `n mod p` for `p > 0`. -/
structure Ck (s0 : State) (X₁ X₂ : Nat) (t : State) : Prop where
  cb : CB s0 s0.mem t
  ws : Ws t (bOf s0) (zOf s0) (wOf s0) nArr
  p : num t.mem (bOf s0) (wOf s0) aP = Pv s0
  q : num t.mem (bOf s0) (wOf s0) aQ = Qv s0
  d : num t.mem (bOf s0) (wOf s0) aD = Dv s0
  x : 0 < Pv s0 → X₁ = Nv s0 / Pv s0 ∧ X₂ = Nv s0 % Pv s0
  podd : slot t.mem (bOf s0) sPodd = Pv s0 % 2
  e1 : slot t.mem (bOf s0) sE1 = if X₁ = Qv s0 then 1 else 0
  e2 : slot t.mem (bOf s0) sE2 = if X₂ = 0 then 1 else 0
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

theorem checks_ok {s0 s : State} (h : PreC s0) (l : Ld s0 s) :
    WP isa checks s fun t => ∃ X₁ X₂, Ck s0 X₁ X₂ t := by
  have ws := l.ws
  have fit : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => ws.fit64 hj
  have ⟨w1, w2⟩ := h.w_bounds
  unfold checks
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
  refine WP.mono (div_ok w2' (q := aDQ) (r := aDR) (d := aDD) (t := aDT) (by cvx) (by cvx) (by cvx) (by cvx)
    (by decide) (by cvx) (by cvx) (by cvx) (by cvx) (by cvx) (by cvx) z2)
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
      f3.num (by simp [Ne.symm a2, Ne.symm a3, Ne.symm a4]) (by simp) (fit _ hj),
      f2.num (by simp) (by cvx) (fit _ hj), f1.num (by simp [Ne.symm a1]) (by simp) (fit _ hj)]
  refine ⟨num t3.mem (bOf s0) (wOf s0) aDQ, num t3.mem (bOf s0) (wOf s0) aDR, c5, w5,
    by rw [keepA _ (by cvx) (by cvx) (by cvx) (by cvx) (by cvx), l.p],
    by rw [keepA _ (by cvx) (by cvx) (by cvx) (by cvx) (by cvx), l.q],
    by rw [keepA _ (by cvx) (by cvx) (by cvx) (by cvx) (by cvx), l.d],
    fun hp => ⟨(v3 hp).1, (v3 hp).2.2.1⟩, ?_, ?_, ?_, ?_⟩
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

end VG.Proof.Rsa.RISCV64.CrtValues
