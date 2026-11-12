module

public import VerifiedGarbage.Proof.Rsa.RISCV64.RdFront
public import VerifiedGarbage.Proof.Rsa.RISCV64.RdOps
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValFront
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on RISC-V: the set-up, the reads, `d e` and `d e - 1`

The working space in its two views (`RdOps`): `w = ⌈n_len / 8⌉ + 1` narrow
words (`nb = 64 w` bits) and `W = 2 w + 2` wide ones (`wb = 64 W`).
`setup_ok`: the narrow view and every array zero; `loads_ok`: `n`
(narrow), `e` and `d` (wide) read (`Ld`); `prod_ok`: `d e`, one row of
`e`'s one word (`Pr`); `deMinus_ok`: one, `x = d e - 1` (`deX`) and the
borrows of `d e - 1` and `x - 1` (`Dm`), what `RecoverDet.okDE` tests. Each
stage also says which narrow arrays are still zero. `bounds`:
`RecoverDet.model_correct`'s bounds.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.RecDet

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Proof.Rsa.RecoverDet (deX wsub wsub_of_le wsub_of_lt)
open VG.Impl.Rsa.RISCV64.Keys (seqs ptr mov setOne stBorrow sub3 load zeroArrays sB sC)
open VG.Impl.Rsa.RISCV64.RecoverDet (setup loads prod deMinus ctxInit ctxW nArr aN wZ wE wD wM wX
  wOne wT2 sB0 sB1 mulRow)

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
macro "rdx" : tactic => `(tactic| ((try simp only [nArr, nWide, aN, wZ, wE, wD, wM, wX, wOne, wT2,
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

/-- The narrow arrays the reads write: `n`, and `e` and `d` (wide). -/
abbrev ldUsed : List Nat := [aN, 2, 3, 4, 5]

/-- After the reads, in the wide view. -/
structure Ld (s0 t : State) : Prop where
  cb : CB s0 s0.mem t
  ws : Ws t (bOf s0) (zOf s0) (WOf s0) nWide
  n : num t.mem (bOf s0) (wOf s0) aN = Nv s0
  e : num t.mem (bOf s0) (WOf s0) wE = Ev s0
  d : num t.mem (bOf s0) (WOf s0) wD = Dv s0
  free : ∀ j < nArr, j ∉ ldUsed → wordsVal t.mem (bOf s0) (arr (wOf s0) j) (wOf s0 + 2) = 0

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
  refine WP.mono (load_ok w3 (j := wD) (by rdx) (by decide) (by decide) c3.a0
    (by rw [c3.a1, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hd1 (by show _ ≤ 8 * WOf s0; omega_arith)
    (hrd c3.rd mD rfl lD) (CrtValues.bytes_sep h.ds lD)
    (num_zero (wide_zero (z3 _ (by rdx) (by rdx)) (z3 _ (by rdx) (by rdx)))))
    fun t ⟨w4, fr4, v4, k4, _⟩ => ?_
  have c4 := c3.step w4 fr4 (by rdx) (by simp) k4
  rw [c3.bytes h.ds lD] at v4
  have z4 := free_step (U' := ldUsed) fr4.toNarrow (by simp) fit (by rdx) (by rdx) z3
  refine ⟨c4, w4, ?_, ?_, v4, z4⟩
  · rw [fr4.toNarrow.num (by rdx) (by simp) (fit _ (by rdx)), fr3.toNarrow.num (by rdx) (by simp) (fit _ (by rdx)), v1]
  · rw [fr4.num (by rdx) (by simp) (w4.fit64 (by rdx)), v3]

/-! ## `d e` -/

/-- The narrow arrays written by now: `n`, `e`, `d` and `d e` (wide). -/
abbrev prUsed : List Nat := [aN, 2, 3, 4, 5, 6, 7]

/-- After `d e`, in the wide view. -/
structure Pr (s0 t : State) : Prop where
  cb : CB s0 s0.mem t
  ws : Ws t (bOf s0) (zOf s0) (WOf s0) nWide
  n : num t.mem (bOf s0) (wOf s0) aN = Nv s0
  de : num t.mem (bOf s0) (WOf s0) wM = deOf s0
  free : ∀ j < nArr, j ∉ prUsed → wordsVal t.mem (bOf s0) (arr (wOf s0) j) (wOf s0 + 2) = 0

/-- A number of `W` words, below `2^64`, is its first word. -/
theorem word0_of_lt {m : Mem} {B : Addr} {d W x : Nat} (hW : 1 ≤ W) (h : wordsVal m B d W = x) (hx : x < 2 ^ 64) :
    (word m B d).toNat = x := by
  have e := wordsVal_append m B d 1 (W - 1)
  rw [show 1 + (W - 1) = W by omega, h] at e
  simp only [wordsVal, Nat.mul_zero, Nat.add_zero, Nat.mul_one] at e
  have := Nat.two_pow_pos 64
  rcases Nat.eq_zero_or_pos (wordsVal m B (d + 8 * 1) (W - 1)) with z | z
  · rw [z, Nat.mul_zero, Nat.add_zero] at e; exact e.symm
  · have := Nat.le_mul_of_pos_right (2 ^ (64 * 1)) z; simp only [Nat.mul_one] at this; omega

theorem prod_ok {s0 s : State} (h : PreC s0) (l : Ld s0 s) : WP isa prod s (Pr s0) := by
  have he2 := h.e2
  have ⟨_, hde, hnw, _, _⟩ := bounds h
  have hw := nb_ge s0
  have fit : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have ws := l.ws
  have fW : ∀ j < nWide, arr (WOf s0) j + S (WOf s0) ≤ 2 ^ 64 := fun j hj => ws.fit64 hj
  have hWp := ws.wpos
  rw [prod, WP.seq_iff]
  refine ptr_ok ws (by decide) (by decide) (show wE < 2048 by decide) ?_
  refine ptr_ok (ws.of_keep (Keep.write _ .a2 _)) (by decide) (by decide) (show wM < 2048 by decide) ?_
  have hb : WP isa (.block [mov .s8 .s9]) ((s.write .a2 (off (bOf s0) (arr (WOf s0) wE))).write .a3
      (off (bOf s0) (arr (WOf s0) wM))) fun u =>
      (u.gpr .a2 = off (bOf s0) (arr (WOf s0) wE + 8 * 0) ∧ u.gpr .a3 = off (bOf s0) (arr (WOf s0) wM + 8 * 0) ∧
        u.gpr .s8 = BitVec.ofNat 64 (WOf s0 - 0) ∧ u.mem = s.mem) ∧
      Keep [.s8] ((s.write .a2 (off (bOf s0) (arr (WOf s0) wE))).write .a3 (off (bOf s0) (arr (WOf s0) wM))) u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    simp only [mov]
    brun [ws.s9, exec_addi_nat (m := 0) (by decide), BitVec.add_zero]
    rfl
  refine WP.mono hb fun u ⟨⟨u2, u3, u8, um⟩, ku⟩ => ?_
  have ku' : Keep [.a2, .a3, .s8] s u := (((Keep.write _ _ _).trans (Keep.write _ _ _)).trans ku).mono (by decide)
  have wu := ws.of_keep ku'
  have cu := l.cb.of_keep ku' um (by decide)
  refine WP.mono (mulRow_ok wu (o := wM) (y := wE) (x := wD) (i := 0) (by decide) (by decide) (by decide)
    (by decide) (by decide) hWp u2 u3 u8) fun t ⟨wt, _, _, _, ot, ⟨c, vt⟩, kt⟩ => ?_
  have zM : wordsVal u.mem (bOf s0) (arr (WOf s0) wM + 8 * 0) (WOf s0 - 0) = 0 := by
    rw [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, um]
    exact num_zero (wide_zero (l.free _ (by rdx) (by rdx)) (l.free _ (by rdx) (by rdx)))
  have bE : Ev s0 < 2 ^ 64 := Nat.lt_of_lt_of_le (os2ip_bytes_lt _ _ _)
    (Nat.pow_le_pow_right (by decide) (by omega_arith))
  have eE : (word u.mem (bOf s0) (arr (WOf s0) wE + 8 * 0)).toNat = Ev s0 := by
    rw [Nat.mul_zero, Nat.add_zero, um]; exact word0_of_lt hWp l.e bE
  have dD : wordsVal u.mem (bOf s0) (arr (WOf s0) wD) (WOf s0 - 0) = Dv s0 := by
    rw [Nat.sub_zero, um]; exact l.d
  rw [zM, eE, dD, Nat.zero_add] at vt
  simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at vt
  have pw : 2 ^ nbOf s0 ≤ 2 ^ (64 * WOf s0) :=
    Nat.pow_le_pow_right (by decide) (by show 64 * wOf s0 ≤ 64 * WOf s0; rw [W_eq]; omega)
  have deb : Ev s0 * Dv s0 < 2 ^ (64 * WOf s0) := by
    rw [Nat.mul_comm]; exact Nat.lt_of_lt_of_le hde pw
  have lt := wordsVal_lt t.mem (bOf s0) (arr (WOf s0) wM) (WOf s0)
  have c0 : c = 0 := by
    rcases Nat.eq_zero_or_pos c with z | z
    · exact z
    · have := Nat.le_mul_of_pos_right (2 ^ (64 * WOf s0)) z; omega
  rw [c0, Nat.mul_zero, Nat.add_zero] at vt
  have ft : Keys.Frame (bOf s0) (WOf s0) [wM] [] s.mem t.mem := by
    rw [← um]; exact Frame.of_arr (d := 0) (by simpa using ot) (by simp only [S]; omega) (by simp)
  have K : Keep (mulRegs ++ [.a2, .a3, .s8]) s t := Keep.trans' (ku'.mono (by decide)) (kt.mono (by decide))
  refine ⟨l.cb.step wt ft (by rdx) (by simp) K, wt, ?_, ?_, ?_⟩
  · rw [ft.toNarrow.num (by rdx) (by decide) (fit _ (by rdx))]; exact l.n
  · show wordsVal t.mem (bOf s0) (arr (WOf s0) wM) (WOf s0) = deOf s0
    rw [vt, Nat.mul_comm]
  · exact free_step (U := ldUsed) (U' := prUsed) (js := halves [wM]) ft.toNarrow
      (by decide) fit (by decide) (by decide) l.free

/-! ## `d e - 1` -/

/-- A subtraction of one and its borrow, as `RecoverDet.wsub`. -/
theorem sub1_arith {b X D c : Nat} (hb : 0 < b) (hX : X < 2 ^ b) (hD : D < 2 ^ b) (hc : c ≤ 1)
    (e : X + 1 = D + 2 ^ b * c) : X = wsub b D 1 ∧ c = if D < 1 then 1 else 0 := by
  have p : 2 ≤ 2 ^ b := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) hb
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
  · have : 1 ≤ D := by omega_arith
    refine ⟨?_, by split <;> omega_arith⟩
    rw [wsub_of_le hD this]; omega_arith
  · have : D = 0 := by omega_arith
    subst this
    refine ⟨?_, by split <;> omega_arith⟩
    rw [wsub_of_lt (by omega_arith) (by omega_arith)]; omega_arith

/-- The narrow arrays written by now: also `x`, one and the temporary. -/
abbrev dmUsed : List Nat := prUsed ++ [18, 19, 20, 21, 32, 33]

/-- After `deMinus`, in the wide view: zero, one, `d e`, `x = d e - 1`, and
the borrows of `d e - 1` and `x - 1` (`RecoverDet.okDE`'s tests). -/
structure Dm (s0 t : State) : Prop where
  cb : CB s0 s0.mem t
  ws : Ws t (bOf s0) (zOf s0) (WOf s0) nWide
  n : num t.mem (bOf s0) (wOf s0) aN = Nv s0
  zero : num t.mem (bOf s0) (WOf s0) wZ = 0
  one : num t.mem (bOf s0) (WOf s0) wOne = 1
  de : num t.mem (bOf s0) (WOf s0) wM = deOf s0
  x : num t.mem (bOf s0) (WOf s0) wX = deX (wbOf s0) (deOf s0)
  b0 : slot t.mem (bOf s0) sB0 = if deOf s0 < 1 then 1 else 0
  b1 : slot t.mem (bOf s0) sB1 = if deX (wbOf s0) (deOf s0) < 1 then 1 else 0
  free : ∀ j < nArr, j ∉ dmUsed → wordsVal t.mem (bOf s0) (arr (wOf s0) j) (wOf s0 + 2) = 0

theorem deMinus_ok {s0 s : State} (h : PreC s0) (p : Pr s0 s) : WP isa deMinus s (Dm s0) := by
  have ⟨_, hde, hnw, _, _⟩ := bounds h
  have fit : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have wpos : 0 < wbOf s0 := by have := W_eq s0; show 0 < 64 * WOf s0; omega_arith
  have deb : deOf s0 < 2 ^ wbOf s0 :=
    Nat.lt_of_lt_of_le hde (Nat.pow_le_pow_right (by decide) (by omega_arith))
  have xb : deX (wbOf s0) (deOf s0) < 2 ^ wbOf s0 := Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold deMinus
  -- One.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (setOne_ok p.ws (j := wOne) (by rdx) (by decide)) fun t1 ⟨w1, f1, v1, k1⟩ => ?_
  have c1 := p.cb.step w1 f1 (by rdx) (by simp) k1
  rw [num_zero (wide_zero (p.free _ (by rdx) (by rdx)) (p.free _ (by rdx) (by rdx))), Nat.zero_div,
    Nat.mul_zero, Nat.add_zero] at v1
  have de1 : num t1.mem (bOf s0) (WOf s0) wM = deOf s0 := by
    rw [f1.num (by rdx) (by simp) (w1.fit64 (by rdx)), p.de]
  -- `x = d e - 1`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok w1 (o := wX) (a := wM) (b := wOne) (by rdx) (by rdx) (by rdx) (by decide) (by rdx)
    (by rdx)) fun t2 ⟨w2, f2, v2, b2, k2⟩ => ?_
  have c2 := c1.step w2 f2 (by rdx) (by simp) k2
  rw [de1, v1] at v2
  have ⟨x2, t42⟩ := sub1_arith wpos (wordsVal_lt _ _ _ _) deb b2 v2
  -- The borrow of `d e - 1`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (stBorrow_ok w2 (sl := sB0) (by rdx) (by rdx)) fun t3 ⟨w3, f3, v3, k3⟩ => ?_
  have c3 := c2.step w3 f3 (by simp) (by rdx) k3
  rw [t42] at v3
  have x3 : num t3.mem (bOf s0) (WOf s0) wX = deX (wbOf s0) (deOf s0) := by
    rw [f3.num (by simp) (by rdx) (w3.fit64 (by rdx))]; exact x2
  have o3 : num t3.mem (bOf s0) (WOf s0) wOne = 1 := by
    rw [f3.num (by simp) (by rdx) (w3.fit64 (by rdx)), f2.num (by rdx) (by simp) (w2.fit64 (by rdx)), v1]
  -- `x - 1`, for its borrow.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok w3 (o := wT2) (a := wX) (b := wOne) (by rdx) (by rdx) (by rdx) (by decide) (by rdx)
    (by rdx)) fun t4 ⟨w4, f4, v4, b4, k4⟩ => ?_
  have c4 := c3.step w4 f4 (by rdx) (by simp) k4
  rw [x3, o3] at v4
  have ⟨_, t44⟩ := sub1_arith wpos (wordsVal_lt _ _ _ _) xb b4 v4
  -- Its borrow.
  refine WP.mono (stBorrow_ok w4 (sl := sB1) (by rdx) (by rdx)) fun t ⟨w5, f5, v5, k5⟩ => ?_
  have c5 := c4.step w5 f5 (by simp) (by rdx) k5
  rw [t44] at v5
  have keepW : ∀ j < nWide, j ≠ wOne → j ≠ wX → j ≠ wT2 →
      num t.mem (bOf s0) (WOf s0) j = num s.mem (bOf s0) (WOf s0) j := fun j hj a1 a2 a3 => by
    rw [f5.num (by simp) (by rdx) (w5.fit64 hj), f4.num (by simp [Ne.symm a3]) (by simp) (w4.fit64 hj),
      f3.num (by simp) (by rdx) (w3.fit64 hj), f2.num (by simp [Ne.symm a2]) (by simp) (w2.fit64 hj),
      f1.num (by simp [Ne.symm a1]) (by simp) (w1.fit64 hj)]
  have fr := free_step (U' := dmUsed) f1.toNarrow (by simp) fit (by rdx) (by rdx) p.free
  have fr := free_step (U' := dmUsed) f2.toNarrow (by simp) fit (by rdx) (by rdx) fr
  have fr := free_step (U' := dmUsed) f3.toNarrow (by rdx) fit (by rdx) (by rdx) fr
  have fr := free_step (U' := dmUsed) f4.toNarrow (by simp) fit (by rdx) (by rdx) fr
  have fr := free_step (U' := dmUsed) f5.toNarrow (by rdx) fit (by rdx) (by rdx) fr
  refine ⟨c5, w5, ?_, num_zero (wide_zero (fr _ (by rdx) (by rdx)) (fr _ (by rdx) (by rdx))), ?_,
    by rw [keepW _ (by rdx) (by rdx) (by rdx) (by rdx), p.de], ?_, ?_, v5, fr⟩
  · rw [f5.toNarrow.num (by rdx) (by rdx) (fit _ (by rdx)), f4.toNarrow.num (by rdx) (by simp) (fit _ (by rdx)),
      f3.toNarrow.num (by rdx) (by rdx) (fit _ (by rdx)), f2.toNarrow.num (by rdx) (by simp) (fit _ (by rdx)),
      f1.toNarrow.num (by rdx) (by simp) (fit _ (by rdx)), p.n]
  · rw [f5.num (by simp) (by rdx) (w5.fit64 (by rdx)), f4.num (by rdx) (by simp) (w4.fit64 (by rdx)), o3]
  · rw [f5.num (by simp) (by rdx) (w5.fit64 (by rdx)), f4.num (by rdx) (by simp) (w4.fit64 (by rdx)), x3]
  · rw [f5.slot (by rdx) (by rdx), f4.slot (by rdx) (by simp), v3]

end VG.Proof.Rsa.RISCV64.RecDet
