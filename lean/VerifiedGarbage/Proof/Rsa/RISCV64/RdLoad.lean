module

public import VerifiedGarbage.Proof.Rsa.RISCV64.RdFront
public import VerifiedGarbage.Proof.Rsa.RISCV64.RdOps
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValFront
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyMulMod
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyInv
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on RISC-V: the set-up, the reads, `d e` and `d e - 1`

The working space in its two views (`RdOps`): `w = ⌈n_len / 8⌉ + 1` narrow
words (`nb = 64 w` bits) and `W = 2 w + 2` wide ones (`wb = 64 W`).
`setup_ok`: the narrow view and every array zero; `loads_ok`: `n`
(narrow), `e`, `d` and the modulus `2^(wb - 1)` (wide) read (`Ld`);
`prod_ok`: `d e` (`Pr`); `deMinus_ok`: one, `x = d e - 1` (`deX`) and the
borrows of `d e - 1` and `x - 1` (`Dm`), what `RecoverDet.okDE` tests. Each
stage also says which narrow arrays are still zero. `bounds`:
`RecoverDet.model_correct`'s bounds.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.RecDet

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Proof.Rsa.RecoverDet (deX wsub wsub_of_le wsub_of_lt)
open VG.Impl.Rsa.RISCV64.Keys (seqs ptr setOne stBorrow sub3 load zeroArrays)
open VG.Impl.Rsa.RISCV64.RecoverDet (setup loads prod deMinus ctxInit ctxW nArr aN wZ wE wD wM wMod wT wX
  wOne wT2 sB0 sB1)

/-! ## The sizes -/

/-- `w`, `W`, `nb`, `wb`, and `d e`. -/
abbrev wOf (s0 : State) : Nat := (kOf s0 + 7) / 8 + 1
abbrev WOf (s0 : State) : Nat := W2 (wOf s0)
abbrev nbOf (s0 : State) : Nat := 64 * wOf s0
abbrev wbOf (s0 : State) : Nat := 64 * WOf s0
abbrev deOf (s0 : State) : Nat := Dv s0 * Ev s0

/-- The wide arrays, 0–19. -/
abbrev nWide : Nat := 20

theorem PreC.fits {s0 : State} (h : PreC s0) : arr (wOf s0) nArr ≤ zOf s0 ∧ WOf s0 ≤ 1024 := by
  have ⟨a, b⟩ := rd_fits h.k1 h.k2
  have := h.zk
  exact ⟨Nat.le_trans a this, b⟩

theorem nb_ge (s0 : State) : 8 * kOf s0 + 64 ≤ nbOf s0 := by
  show 8 * kOf s0 + 64 ≤ 64 * ((kOf s0 + 7) / 8 + 1); omega_arith

theorem W_eq (s0 : State) : WOf s0 = 2 * wOf s0 + 2 := rfl
theorem w_eq (s0 : State) : wOf s0 = (kOf s0 + 7) / 8 + 1 := rfl

theorem PreC.fit64 {s0 : State} (h : PreC s0) {j : Nat} (hj : j < nArr) :
    arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := by
  have a := arr_end (w := wOf s0) hj; have b := h.fits.1; have c := h.ws
  simp only [zOf] at b; omega_arith

/-- `RecoverDet.model_correct`'s bounds, and `n`'s. -/
theorem bounds {s0 : State} (h : PreC s0) :
    8 * (Nv s0 + 2) ≤ 2 ^ nbOf s0 ∧ deOf s0 < 2 ^ nbOf s0 ∧ 2 * nbOf s0 ≤ wbOf s0 ∧
      wbOf s0 % 2 = 0 ∧ Nv s0 < 2 ^ (8 * kOf s0) := by
  have hw := nb_ge s0
  have bN : Nv s0 < 2 ^ (8 * kOf s0) := os2ip_bytes_lt _ _ _
  have bD : Dv s0 < 2 ^ (8 * kOf s0) :=
    Nat.lt_of_lt_of_le (os2ip_bytes_lt _ _ _) (Nat.pow_le_pow_right (by decide)
      (by have : (stackArg s0 1).toNat ≤ kOf s0 := h.d2; omega_arith))
  have bE : Ev s0 < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (os2ip_bytes_lt _ _ _) (Nat.pow_le_pow_right (by decide) (by have := h.e2; omega_arith))
  have p4 : 2 ^ (8 * kOf s0 + 4) ≤ 2 ^ nbOf s0 := Nat.pow_le_pow_right (by decide) (by omega_arith)
  have p64 : 2 ^ (8 * kOf s0 + 64) ≤ 2 ^ nbOf s0 := Nat.pow_le_pow_right (by decide) hw
  have one : 1 ≤ 2 ^ (8 * kOf s0) := Nat.one_le_two_pow
  refine ⟨?_, ?_, by simp only [nbOf, wbOf, WOf, W2]; omega_arith, by simp only [wbOf]; omega_arith, bN⟩
  · rw [Nat.pow_add] at p4; omega_arith
  · calc deOf s0 = Dv s0 * Ev s0 := rfl
      _ < 2 ^ (8 * kOf s0) * 2 ^ 64 := Nat.mul_lt_mul'' bD bE
      _ = 2 ^ (8 * kOf s0 + 64) := (Nat.pow_add _ _ _).symm
      _ ≤ _ := p64

/-! ## Zero arrays -/

/-- The narrow arrays `2 j` and `2 j + 1` zero: the wide array `j` is. -/
theorem wide_zero {m : Mem} {B : Addr} {w j : Nat} (h0 : wordsVal m B (arr w (2 * j)) (w + 2) = 0)
    (h1 : wordsVal m B (arr w (2 * j + 1)) (w + 2) = 0) : wordsVal m B (arr (W2 w) j) (W2 w + 2) = 0 := by
  rw [arr_W2, show W2 w + 2 = (w + 2) + (w + 2) by simp only [W2]; omega_arith, wordsVal_append, h0,
    show arr w (2 * j) + 8 * (w + 2) = arr w (2 * j + 1) by rw [arr_succ], h1]
  simp

theorem num_zero {m : Mem} {B : Addr} {w j : Nat} (h : wordsVal m B (arr w j) (w + 2) = 0) :
    num m B w j = 0 := by
  have := wordsVal_zero_part (a := 0) (c := w) h (by omega_arith)
  simpa using this

/-- Which narrow arrays are still zero, through a step's frame. -/
theorem free_step {m m' : Mem} {B : Addr} {w : Nat} {js ds U U' : List Nat}
    (f : Keys.Frame B w js ds m m') (hd : ∀ d ∈ ds, d + 8 ≤ hdr)
    (fit : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64) (hjs : ∀ j ∈ js, j ∈ U') (hU : ∀ j ∈ U, j ∈ U')
    (hz : ∀ j < nArr, j ∉ U → wordsVal m B (arr w j) (w + 2) = 0) :
    ∀ j < nArr, j ∉ U' → wordsVal m' B (arr w j) (w + 2) = 0 := fun j hj hn => by
  rw [f.full (fun k hk e => by subst e; exact hn (hjs _ hk)) hd (fit j hj)]
  exact hz j hj fun hu => hn (hU j hu)

/-- A step in any view of the working space keeps `CB`. -/
theorem CB.step {s0 s t u : State} {M : Mem} (c : CB s0 M s) {w N : Nat}
    (ws : Ws u (bOf s0) (zOf s0) w N) {js ds : List Nat} (f : Keys.Frame (bOf s0) w js ds s.mem t.mem)
    (hjs : ∀ j ∈ js, j < N) (hds : ∀ d ∈ ds, 96 ≤ d ∧ d + 8 ≤ Keys.hdr) {rs : List Reg} (k : Keep rs s t)
    (hr : ∀ r ∈ cbRegs, r ∉ rs := by decide) : CB s0 M t :=
  c.of_frame f (fun j hj => ws.arr_fit (hjs j hj)) hds ws.hdr_le k hr

/-- Index side conditions. -/
macro "rdx" : tactic => `(tactic| ((try simp only [nArr, nWide, aN, wZ, wE, wD, wM, wMod, wT, wX, wOne, wT2,
  sB0, sB1, halves, hdr_eq, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
  List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, ne_eq]) <;>
  first | decide | omega_arith))

/-! ## The set-up -/

theorem setup_ok {s0 s : State} (h : PreC s0) (c : CB s0 s0.mem s) :
    WP isa setup s fun t => CB s0 s0.mem t ∧ Ws t (bOf s0) (zOf s0) (wOf s0) nArr ∧
      ∀ j < nArr, wordsVal t.mem (bOf s0) (arr (wOf s0) j) (wOf s0 + 2) = 0 := by
  have hk : kOf s0 ≤ 1024 := h.k2
  have ⟨f1, f2⟩ := h.fits
  rw [setup, WP.seq_iff]
  refine WP.mono (ctxInit_ok (L := kOf s0) (by rw [c.s2, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by omega_arith)) fun u ⟨⟨u9, u10, um⟩, ku⟩ => ?_
  have cu := c.of_keep ku um
  have wu : Ws u (bOf s0) (zOf s0) (wOf s0) nArr :=
    ⟨Scr.of_mem (by rw [cu.wr]; exact h.sR_wr) h.ws h.al, f1, by rw [w_eq]; omega_arith,
      by rw [W_eq] at f2; omega_arith, u9, u10, cu.s11⟩
  refine WP.mono (zeroArrays_ok wu (by decide) (by decide) (by decide)) fun t ⟨wt, ft, zt, kt⟩ => ?_
  exact ⟨cu.step wu ft (fun j hj => List.mem_range.mp hj) (by simp) kt, wt, zt⟩

/-! ## The reads -/

/-- The narrow arrays the reads write: `n`, and `e`, `d` and the modulus (wide). -/
abbrev ldUsed : List Nat := [aN, 2, 3, 4, 5, 8, 9]

/-- After the reads, in the wide view. -/
structure Ld (s0 t : State) : Prop where
  cb : CB s0 s0.mem t
  ws : Ws t (bOf s0) (zOf s0) (WOf s0) nWide
  n : num t.mem (bOf s0) (wOf s0) aN = Nv s0
  e : num t.mem (bOf s0) (WOf s0) wE = Ev s0
  d : num t.mem (bOf s0) (WOf s0) wD = Dv s0
  m : num t.mem (bOf s0) (WOf s0) wMod = 2 ^ (wbOf s0 - 1)
  free : ∀ j < nArr, j ∉ ldUsed → wordsVal t.mem (bOf s0) (arr (wOf s0) j) (wOf s0 + 2) = 0

/-- `W` words, the top one written, the others zero. -/
theorem top_val {m : Mem} {B : Addr} {d W : Nat} (hW : 0 < W) (fit : d + 8 * W ≤ 2 ^ 64)
    (hz : wordsVal m B d W = 0) (v : BitVec 64) :
    wordsVal (m.writeW (off B (d + 8 * W - 8)) v) B d W = 2 ^ (64 * (W - 1)) * v.toNat := by
  obtain ⟨k, rfl⟩ : ∃ k, W = k + 1 := ⟨W - 1, by omega_arith⟩
  have o := writeW_outside m B (d := d + 8 * k) v (by omega_arith)
  rw [show d + 8 * (k + 1) - 8 = d + 8 * k by omega_arith]
  rw [wordsVal_append] at hz ⊢
  rw [o.wordsVal (by omega_arith) (by omega_arith)]
  have h0 : wordsVal m B d k = 0 := by
    have := Nat.two_pow_pos (64 * k); generalize wordsVal m B (d + 8 * k) 1 = c at hz; omega_arith
  rw [h0, Nat.zero_add, Nat.add_sub_cancel]
  simp only [wordsVal, word_writeW_self, Nat.mul_zero, Nat.add_zero]

theorem top_ok {s : State} {B : Addr} {Z W N j : Nat} (h : Ws s B Z W N) (hj : j < N) (hN : N ≤ 2048)
    (hz : wordsVal s.mem B (arr W j) W = 0) :
    WP isa (.block (ptr .t0 j ++ [.shift .sll .d .t5 .s9 3, .add .t0 .t0 .t5, .addi .t0 .t0 (-8),
      .li .t5 1, .shift .sll .d .t5 .t5 63, .store .d .t5 .t0 0])) s fun t =>
      Ws t B Z W N ∧ Keys.Frame B W [j] [] s.mem t.mem ∧ num t.mem B W j = 2 ^ (64 * W - 1) ∧
        Keep opRegs s t := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S W = 8 * (W + 2) := rfl
  have hpos := h.wpos
  have hle := h.wle
  refine ptr_ok h (by decide) (by decide) (show j < 2048 by omega_arith) ?_
  have hb : WP isa (.block [.shift .sll .d .t5 .s9 3, .add .t0 .t0 .t5, .addi .t0 .t0 (-8),
      .li .t5 1, .shift .sll .d .t5 .t5 63, .store .d .t5 .t0 0]) (s.write .t0 (off B (arr W j))) fun u =>
      (u.mem = s.mem.writeW (off B (arr W j + 8 * W - 8)) (BitVec.ofNat 64 (2 ^ 63))) ∧
        Keep [.t0, .t5] (s.write .t0 (off B (arr W j))) u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h.s9, shl3_ofNat, add_ofNat_zero', off_sub (p := B) (a := arr W j + 8 * W) (b := 8) (by omega_arith),
      keys_exec_li_one, h.scr.st (d := arr W j + 8 * W - 8) (n := 8) (by omega_arith),
      h.scr.al8 (d := arr W j + 8 * W - 8) (by omega_arith) (by have := arr_al W j; omega_arith)]
    rfl
  refine WP.mono hb fun u ⟨um, ku⟩ => ?_
  have k₁ : Keep opRegs s u := ((Keep.write _ _ _).trans ku).mono (by decide)
  have o := writeW_outside s.mem B (d := arr W j + 8 * W - 8) (BitVec.ofNat 64 (2 ^ 63)) (by omega_arith)
  refine ⟨h.of_keep k₁, ?_, ?_, k₁⟩
  · rw [um]
    exact Frame.of_arr (d := 8 * W - 8) (by rw [← Nat.add_sub_assoc (by omega_arith)]; exact o)
      (by omega_arith) (by simp)
  · show wordsVal u.mem B (arr W j) W = _
    rw [um, top_val hpos (by omega_arith) hz]
    rw [show (BitVec.ofNat 64 (2 ^ 63)).toNat = 2 ^ 63 by rfl, ← Nat.pow_add]
    congr 1; omega_arith

theorem loads_ok {s0 s : State} (h : PreC s0) (c : CB s0 s0.mem s) (ws : Ws s (bOf s0) (zOf s0) (wOf s0) nArr)
    (hz : ∀ j < nArr, wordsVal s.mem (bOf s0) (arr (wOf s0) j) (wOf s0 + 2) = 0) :
    WP isa loads s (Ld s0) := by
  have hk1 : 64 ≤ kOf s0 := h.k1
  have hk2 : kOf s0 ≤ 1024 := h.k2
  have he1 := h.e1
  have he2 := h.e2
  have hd1 := h.d1
  have hd2 : (stackArg s0 1).toNat ≤ kOf s0 := h.d2
  have hw := nb_ge s0
  have ⟨f1, f2⟩ := h.fits
  have fit : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have hK8 : kOf s0 ≤ 8 * wOf s0 := by rw [w_eq]; omega_arith
  have hW8 : kOf s0 ≤ 8 * WOf s0 := by rw [W_eq]; omega_arith
  have hW1 : 8 ≤ 8 * WOf s0 := by rw [W_eq]; omega_arith
  have hrd : ∀ {u : State}, u.rd = s0.rd → ∀ {r : Region}, r ∈ s0.rd → ∀ {P : Addr} {L : Nat}, r = ⟨P, L⟩ →
      L ≤ 2 ^ 64 → ∀ i < L, InRegions (u.rd ++ u.wr) (off P i) 1 := fun hu r hr P L e hL i hi => by
    subst e; rw [hu]; exact CrtValues.inRegions_left (CrtValues.bytes_in hr hL i hi)
  have mN : nR s0 ∈ s0.rd := by rw [h.hrd]; simp
  have mE : eR s0 ∈ s0.rd := by rw [h.hrd]; simp
  have mD : dR s0 ∈ s0.rd := by rw [h.hrd]; simp
  have lN : kOf s0 ≤ 2 ^ 64 := by omega_arith
  have lE : (s0.gpr .a7).toNat ≤ 2 ^ 64 := by omega_arith
  have lD : (stackArg s0 1).toNat ≤ 2 ^ 64 := by omega_arith
  unfold loads
  -- `n`, narrow.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (load_ok ws (j := aN) (by rdx) (by decide) (by decide) c.s1
    (by rw [c.s2, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega_arith) hK8 (hrd c.rd mN rfl lN)
    (CrtValues.bytes_sep h.ns lN) (num_zero (hz _ (by rdx))))
    fun t1 ⟨w1, fr1, v1, k1, _⟩ => ?_
  have c1 := c.step w1 fr1 (by rdx) (by simp) k1
  rw [c.bytes h.ns lN] at v1
  have z1 := free_step (U := []) (U' := [aN]) fr1 (by simp) fit (by rdx) (by simp)
    (fun j hj _ => hz j hj)
  -- The wide view.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxW_ok (M := nWide) w1 f2 (by decide)) fun t2 ⟨⟨w2, m2⟩, k2⟩ => ?_
  have c2 := c1.of_keep k2 m2
  rw [← m2] at v1 z1
  -- `e`, wide.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (load_ok w2 (j := wE) (by rdx) (by decide) (by decide) c2.s5
    (by rw [c2.s6, BitVec.ofNat_toNat, BitVec.setWidth_eq]) he1 (by show _ ≤ 8 * WOf s0; omega_arith)
    (hrd c2.rd mE rfl lE) (CrtValues.bytes_sep h.es lE)
    (num_zero (wide_zero (z1 _ (by rdx) (by rdx)) (z1 _ (by rdx) (by rdx)))))
    fun t3 ⟨w3, fr3, v3, k3, _⟩ => ?_
  have c3 := c2.step w3 fr3 (by rdx) (by simp) k3
  rw [c2.bytes h.es lE] at v3
  have z3 := free_step (U' := [aN, 2, 3]) fr3.toNarrow (by simp) fit (by rdx) (by rdx) z1
  -- `d`, wide.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (load_ok w3 (j := wD) (by rdx) (by decide) (by decide) c3.a0
    (by rw [c3.a1, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hd1 (by show _ ≤ 8 * WOf s0; omega_arith)
    (hrd c3.rd mD rfl lD) (CrtValues.bytes_sep h.ds lD)
    (num_zero (wide_zero (z3 _ (by rdx) (by rdx)) (z3 _ (by rdx) (by rdx)))))
    fun t4 ⟨w4, fr4, v4, k4, _⟩ => ?_
  have c4 := c3.step w4 fr4 (by rdx) (by simp) k4
  rw [c3.bytes h.ds lD] at v4
  have z4 := free_step (U' := [aN, 2, 3, 4, 5]) fr4.toNarrow (by simp) fit (by rdx) (by rdx) z3
  -- The modulus `2^(wb - 1)`, wide.
  have zm := wide_zero (z4 (2 * wMod) (by rdx) (by rdx)) (z4 (2 * wMod + 1) (by rdx) (by rdx))
  refine WP.mono (top_ok w4 (j := wMod) (by rdx) (by decide)
    (by simpa using wordsVal_zero_part (a := 0) (c := WOf s0) zm (by show 0 + WOf s0 ≤ WOf s0 + 2; omega_arith)))
    fun t ⟨w5, fr5, v5, k5⟩ => ?_
  have c5 := c4.step w5 fr5 (by rdx) (by simp) k5
  have z5 := free_step (U' := ldUsed) fr5.toNarrow (by simp) fit (by rdx) (by rdx) z4
  refine ⟨c5, w5, ?_, ?_, ?_, v5, z5⟩
  · rw [fr5.toNarrow.num (by rdx) (by simp) (fit _ (by rdx)), fr4.toNarrow.num (by rdx) (by simp) (fit _ (by rdx)),
      fr3.toNarrow.num (by rdx) (by simp) (fit _ (by rdx)), v1]
  · rw [fr5.num (by rdx) (by simp) (w5.fit64 (by rdx)), fr4.num (by rdx) (by simp) (w4.fit64 (by rdx)), v3]
  · rw [fr5.num (by rdx) (by simp) (w5.fit64 (by rdx)), v4]

end VG.Proof.Rsa.RISCV64.RecDet
