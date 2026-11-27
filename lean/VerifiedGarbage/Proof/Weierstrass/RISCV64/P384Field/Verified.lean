module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Fn
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Rows
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Words
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.FieldRV
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Impl.Weierstrass.RISCV64.P384Field
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Fn
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Lit
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Lit
meta import VerifiedGarbage.Impl.Weierstrass.Layout.Mont

/-!
# Arithmetic modulo P-384's prime on RISC-V: verified

Each function meets a contract by register (`mulRV`, `addRV`, `subRV`: `ws` in
`a0`, aligned, as a `[u64]` is, and the offsets' low words in `a1`–`a3`),
from `fn_ok` (`numAt` of an offset is the six doublewords there,
`numAt_d6`; the regions the function writes keep every other byte,
`keeps_of_frame`). A function is constant time (`fn_ct`) when the taint
analysis finds every branch and address of its core depends only on
`a0`–`a3`, which are public after the zero-extension, related by its
results (`mulZext_rel`).
-/

-- Checking `P` against the contract's modulus evaluates `2³⁸⁴`.
set_option exponentiation.threshold 512

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P384Field

open VG VG.RISCV64 VG.Impl.Weierstrass.RISCV64.P384Field
open VG.Proof.X448.RISCV64.R64 (colsV)
open VG.Impl.Weierstrass.Mont (numAt Keeps p384p Fits)
open VG.Proof.Weierstrass.RISCV64 (offArg rvPre arg res rvPub mulRV addRV subRV)

theorem numAt_d6 (m : Mem) (W : Addr) (o : BitVec 32) : numAt m W o 6 = d6 m (W + BitVec.ofNat 64 o.toNat) := by
  have h := VG.Proof.Mont.read_eq_wordsVal m (W + BitVec.ofNat 64 o.toNat) 6 0
  simp only [VG.Proof.Mont.off, BitVec.add_zero] at h
  rw [numAt, h]
  simp only [VG.Proof.Mont.wordsVal, VG.Proof.Mont.word, VG.Proof.Mont.off, d6, colsV,
    VG.Proof.X448.RISCV64.R64.dw, Nat.reduceAdd, Nat.mul_zero, Nat.mul_one, Nat.reduceMul]
  omega_using []

/-- A byte of the working space outside a range of it. -/
theorem byte_out {W : Addr} {i e k : Nat} (hi : i + 1 ≤ 8192) (he : e + k ≤ 8192) (h : i < e ∨ e + k ≤ i) :
    ¬ (⟨W + BitVec.ofNat 64 e, k⟩ : Region).Contains (W + BitVec.ofNat 64 i) 1 := fun hc =>
  Offset.disjoint W (d := i) (n := 1) (e := e) (k := k) (by omega_using [h]) (by omega_using [hi]) (by omega_using [he]) _
    (Region.contains_self _ _) hc

/-- The regions the functions write keep every byte the contracts do. -/
theorem keeps_of_frame {W : Addr} {o : BitVec 32} (ho : o.toNat + 48 ≤ 3712) {m m' : Mem}
    (hf : Frame (fnW W o.toNat) m m') : Keeps 6 W o m m' := by
  intro i hi hown hoi
  simp only [Impl.Weierstrass.Mont.wsBytes, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes] at hi hown
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact byte_out (by omega_using [hi]) (by omega_using []) (by omega_using [hown])
  · exact byte_out (by omega_using [hi]) (by omega_using [ho]) hoi

theorem p_eq : p384p.m = P := rfl

/-- `fn core` meets a contract by register, from `fn_ok`. -/
theorem fn_rv {core : Prog isa} {pre : Nat → Nat → Prop} {res : Nat → Nat → Nat → Prop}
    (hcore : CoreOk core pre res) {s : State} (hs : rvPre p384p s) (hp : pre (arg p384p s .a2) (arg p384p s .a3)) :
    ∃ t s', Exec isa (fn core) s t s' ∧ abiPreserved s s' ∧
      res (arg p384p s .a2) (arg p384p s .a3) (numAt s'.mem (s.gpr .a0) (offArg s .a1) 6) ∧
      Keeps 6 (s.gpr .a0) (offArg s .a1) s.mem s'.mem := by
  obtain ⟨-, hwr, hfit, ⟨fo, fa, fb⟩, hal⟩ := hs
  simp only [Fits, VG.Proof.Weierstrass.RISCV64.rvOwn_le (show p384p.k ≤ 6 by decide), Impl.Weierstrass.Mont.ownAt,
    Impl.Weierstrass.Mont.ownBytes] at fo fa fb
  simp only [arg, show p384p.k = 6 from rfl, numAt_d6] at hp ⊢
  obtain ⟨t, s', he, v, f, g, -, -, sp⟩ := fn_ok hcore rfl hal (by rw [hwr]; simp) hfit fo fa fb hp
  refine ⟨t, s', he, ⟨fun r hr => g r (by revert hr; revert r; decide), sp, g _ (by decide)⟩, v,
    keeps_of_frame fo f⟩

/-- `fnA core` meets a contract by register for offsets as the calls set
them, from `fnA_ok`, for any six-word modulus. -/
theorem fnA_rv {S : Impl.Weierstrass.Mont.Modulus} (hk : S.k = 6) {core : Prog isa} {pre : Nat → Nat → Prop}
    {res : Nat → Nat → Nat → Prop} (hcore : CoreOkA core pre res) {s : State} (hs : rvPre S s)
    (hoff : VG.Proof.Weierstrass.RISCV64.OffsOk s) (hp : pre (arg S s .a2) (arg S s .a3)) :
    ∃ t s', Exec isa (fnA core) s t s' ∧ abiPreserved s s' ∧
      res (arg S s .a2) (arg S s .a3) (numAt s'.mem (s.gpr .a0) (offArg s .a1) 6) ∧
      Keeps 6 (s.gpr .a0) (offArg s .a1) s.mem s'.mem := by
  obtain ⟨-, hwr, hfit, ⟨fo, fa, fb⟩, hal⟩ := hs
  simp only [Fits, hk, VG.Proof.Weierstrass.RISCV64.rvOwn_le (show 6 ≤ 6 by decide), Impl.Weierstrass.Mont.ownAt,
    Impl.Weierstrass.Mont.ownBytes] at fo fa fb
  simp only [arg, hk, numAt_d6] at hp ⊢
  obtain ⟨t, s', he, v, f, g, -, -, sp⟩ := fnA_ok hcore rfl hal (by rw [hwr]; simp) hfit fo fa fb
    (hoff _ (by simp)) (hoff _ (by simp)) (hoff _ (by simp)) hp
  refine ⟨t, s', he, ⟨fun r hr => g r (by revert hr; revert r; decide), sp, g _ (by decide)⟩, v,
    keeps_of_frame fo f⟩

/-! ## The multiplication for aligned offsets -/

open VG.RISCV64.Steps VG.RISCV64.Wide
open VG.Proof.X25519.RISCV64 (Ctx Rest wp_and)
open VG.Proof.X448.RISCV64.R64 (dw dw_write_self dw_write_other al8 Keeps.rest)
open VG.Proof.Weierstrass.RISCV64.P256Field (upd_keeps wp_lim1 sltu_toNat)
open VG.Proof.Weierstrass.RISCV64.GenWide (wp_xor' ov mont_nat)

theorem lay_ok : Rows.LOk lay :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

set_option linter.unusedSimpArgs false in
/-- `d + 2⁶⁴ c := x + y`. -/
theorem addc_ok {d x y c : Reg} (hdy : d ≠ y) (hdc : d ≠ c) {s : State} :
    WP isa (.block [.add d x y, .sltu c d y]) s fun s' =>
      (s'.gpr d).toNat + 2 ^ 64 * (s'.gpr c).toNat = (s.gpr x).toNat + (s.gpr y).toNat ∧ Keeps [d, c] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_sltu,
    RegUpd.gpr_write, hdy, hdc, Ne.symm hdy, Ne.symm hdc, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨carry _ _, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- The number in `s6`–`s11`. -/
abbrev dv (s : State) : Nat :=
  (s.gpr .s6).toNat + 2 ^ 64 * (s.gpr .s7).toNat + 2 ^ 128 * (s.gpr .s8).toNat + 2 ^ 192 * (s.gpr .s9).toNat +
    2 ^ 256 * (s.gpr .s10).toNat + 2 ^ 320 * (s.gpr .s11).toNat

theorem xv_eq (s : State) : xv s =
    (s.gpr .t5).toNat + 2 ^ 64 * (s.gpr .t6).toNat + 2 ^ 128 * (s.gpr .t3).toNat + 2 ^ 192 * (s.gpr .t4).toNat +
      2 ^ 256 * (s.gpr .a1).toNat + 2 ^ 320 * (s.gpr .a4).toNat := by
  simp only [xv, colsV, X, XR, List.getD_cons_zero, List.getD_cons_succ]
  omega_using []

theorem constR_ok {s : State} :
    WP isa (.block constR) s fun s' =>
      (s'.gpr .t0).toNat = 2 ^ 64 - 2 ^ 32 + 1 ∧ (s'.gpr .a5).toNat = 2 ^ 32 - 1 ∧ Keeps [.t0, .a5] s s' := by
  unfold constR
  refine wp_lim1 fun s1 u1 => wp_sll (by decide) fun s2 u2 => wp_addi (imm := 1) (by decide) fun s3 u3 =>
    wp_lim1 fun s4 u4 => wp_srl (by decide) fun s5 u5 => WP.block_nil ?_
  refine ⟨?_, by rw [u5.gpr, u4.gpr]; decide, ((((upd_keeps u1).trans (upd_keeps u2)).trans (upd_keeps u3)).trans
    (upd_keeps u4)).trans (upd_keeps u5) |>.mono⟩
  rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.gpr, u1.gpr]; decide

/-- `x + (2³⁸⁴ - p)`. -/
theorem sumR_ok {s : State} (h0 : (s.gpr .t0).toNat = 2 ^ 64 - 2 ^ 32 + 1) (h5 : (s.gpr .a5).toNat = 2 ^ 32 - 1) :
    WP isa (.block sumR) s fun s' =>
      dv s' + 2 ^ 384 * (s'.gpr .a7).toNat = xv s + (2 ^ 384 - P) ∧ (s'.gpr .a7).toNat ≤ 1 ∧
      Keeps [.s6, .s7, .s8, .s9, .s10, .s11, .a7, .a0] s s' := by
  unfold sumR
  refine WP.block_append (WP.mono (addc_ok (d := .s6) (x := .t5) (y := .t0) (c := .a7) (by decide) (by decide))
    fun s1 ⟨e1, k1⟩ => ?_)
  refine WP.block_append (WP.mono (addc_ok (d := .s7) (x := .t6) (y := .a5) (c := .a0) (by decide) (by decide))
    fun s2 ⟨e2, k2⟩ => ?_)
  refine WP.block_append (WP.mono (addc_ok (d := .s7) (x := .s7) (y := .a7) (c := .a7) (by decide) (by decide))
    fun s3 ⟨e3, k3⟩ => ?_)
  refine WP.block_append (wp_add fun s4 u4 => wp_addi (imm := 1) (by decide) fun s5 u5 => WP.block_nil ?_)
  refine WP.block_append (WP.mono (addc_ok (d := .s8) (x := .t3) (y := .a7) (c := .a7) (by decide) (by decide))
    fun s6 ⟨e6, k6⟩ => ?_)
  refine WP.block_append (WP.mono (addc_ok (d := .s9) (x := .t4) (y := .a7) (c := .a7) (by decide) (by decide))
    fun s7 ⟨e7, k7⟩ => ?_)
  refine WP.block_append (WP.mono (addc_ok (d := .s10) (x := .a1) (y := .a7) (c := .a7) (by decide) (by decide))
    fun s8 ⟨e8, k8⟩ => ?_)
  refine WP.mono (addc_ok (d := .s11) (x := .a4) (y := .a7) (c := .a7) (by decide) (by decide)) fun s9 ⟨e9, k9⟩ => ?_
  obtain K2 : Keeps [.s6, .s7, .a7, .a0] s s2 := (k1.trans k2).mono
  obtain K5 : Keeps [.s6, .s7, .a7, .a0] s s5 := (((K2.trans k3).trans (upd_keeps u4)).trans (upd_keeps u5)).mono
  obtain K6 := K5.trans k6
  obtain K7 := K6.trans k7
  obtain K8 := K7.trans k8
  rw [h0] at e1
  rw [k1.1 .t6 (by decide), k1.1 .a5 (by decide), h5] at e2
  rw [k2.1 .a7 (by decide)] at e3
  obtain a0 : s3.gpr .a0 = s2.gpr .a0 := k3.1 _ (by decide)
  obtain x0 := (s.gpr .t5).isLt
  obtain x1 := (s.gpr .t6).isLt
  obtain y1 := (s2.gpr .s7).isLt
  obtain y2 := (s3.gpr .s7).isLt
  obtain y0 := (s1.gpr .s6).isLt
  obtain a7 : (s5.gpr .a7).toNat = (s3.gpr .a7).toNat + (s2.gpr .a0).toNat + 1 := by
    rw [u5.gpr, u4.gpr, a0, BitVec.toNat_add, BitVec.toNat_add]
    simp only [BitVec.reduceToNat]
    omega_using [e1, e2, e3, x0, x1, y0, y1, y2]
  rw [K5.1 .t3 (by decide), a7] at e6
  rw [K6.1 .t4 (by decide)] at e7
  rw [K7.1 .a1 (by decide)] at e8
  rw [K8.1 .a4 (by decide)] at e9
  obtain o6 : s9.gpr .s6 = s1.gpr .s6 := by
    rw [k9.1 _ (by decide), k8.1 _ (by decide), k7.1 _ (by decide), k6.1 _ (by decide), u5.other _ (by decide),
      u4.other _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide)]
  obtain o7 : s9.gpr .s7 = s3.gpr .s7 := by
    rw [k9.1 _ (by decide), k8.1 _ (by decide), k7.1 _ (by decide), k6.1 _ (by decide), u5.other _ (by decide),
      u4.other _ (by decide)]
  obtain o8 : s9.gpr .s8 = s6.gpr .s8 := by rw [k9.1 _ (by decide), k8.1 _ (by decide), k7.1 _ (by decide)]
  obtain o9 : s9.gpr .s9 = s7.gpr .s9 := by rw [k9.1 _ (by decide), k8.1 _ (by decide)]
  obtain o10 : s9.gpr .s10 = s8.gpr .s10 := k9.1 _ (by decide)
  refine ⟨?_, ?_, (K8.trans k9).mono⟩
  · rw [xv_eq]
    simp only [dv, o6, o7, o8, o9, o10]
    rw [show 2 ^ 384 - P = 2 ^ 128 + 2 ^ 96 - 2 ^ 32 + 1 by decide]
    clear x0 x1 y0 y1 y2 a7 h0 h5
    omega_using [e1, e2, e3, e6, e7, e8, e9]
  · obtain l1 := (s.gpr .a4).isLt
    obtain l2 := (s8.gpr .a7).isLt
    obtain l3 := (s9.gpr .s11).isLt
    omega_using [e9, l1, l2, l3]

theorem selR_ok {O : Addr} {j : Nat} {d v : Reg} (hd : d ∉ [Reg.t0, .t2]) (hdv : d ≠ v) (hj : j < 6) {s : State}
    (h2 : s.gpr .t2 = O) (oal : O.toNat % 8 = 0) (ow : InRegions s.wr (O + BitVec.ofNat 64 (8 * j)) 8)
    (hm : IsMask (s.gpr .t0)) :
    WP isa (.block (selR j d v)) s fun s' =>
      s'.mem = s.mem.writeW (O + BitVec.ofNat 64 (8 * j))
        (if s.gpr .t0 = BitVec.allOnes 64 then s.gpr d else s.gpr v) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  unfold selR
  refine wp_xor' fun s2 u2 => wp_and fun s3 u3 => wp_xor' fun s4 u4 => ?_
  refine wp_sd (by omega_arith) (by rw [u4.other _ (Ne.symm hd.2), u3.other _ (Ne.symm hd.2), u2.other _ (Ne.symm hd.2),
    h2]) (al8 oal (by omega_arith)) (by rw [u4.wr, u3.wr, u2.wr]; exact ow) fun s5 u5 => WP.block_nil ?_
  obtain v4 : s4.gpr d = if s.gpr .t0 = BitVec.allOnes 64 then s.gpr d else s.gpr v := by
    rw [u4.gpr, u3.gpr, u3.other _ (Ne.symm hdv), u2.other _ (Ne.symm hdv), u2.gpr, u2.other _ (Ne.symm hd.1)]
    exact sel_mask hm
  refine ⟨by rw [u5.mem, u4.mem, u3.mem, u2.mem, v4], fun r hr => ?_, by rw [u5.rd, u4.rd, u3.rd, u2.rd],
    by rw [u5.wr, u4.wr, u3.wr, u2.wr], by rw [u5.sp, u4.sp, u3.sp, u2.sp]⟩
  rw [u5.gpr, u4.other r hr, u3.other r hr, u2.other r hr]

/-- After the first `j` words of the selection from `s0`, `f` the registers of the sum and `g` those of `x`. -/
structure SelR (O : Addr) (s0 : State) (f : Nat → Reg) (g : Nat → Reg) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, (∀ i < j, r ≠ f i) → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨O, 48⟩] s0.mem s.mem
  val : ∀ i < j, dw s.mem O (8 * i) =
    (if s0.gpr .t0 = BitVec.allOnes 64 then s0.gpr (f i) else s0.gpr (g i)).toNat

/-- The registers of the sum. -/
abbrev fR (j : Nat) : Reg := [Reg.s6, .s7, .s8, .s9, .s10, .s11].getD j .s6

theorem selR_step {O : Addr} {s0 s : State} {j : Nat} (hj : j < 6) (h2 : s0.gpr .t2 = O) (oal : O.toNat % 8 = 0)
    (ow : ∀ i < 6, InRegions s0.wr (O + BitVec.ofNat 64 (8 * i)) 8) (hm : IsMask (s0.gpr .t0))
    (h : SelR O s0 fR X j s) :
    WP isa (.block (selR j (fR j) (X j))) s (SelR O s0 fR X (j + 1)) := by
  obtain ⟨d1, d2, d3, d4⟩ : fR j ∉ [Reg.t0, .t2] ∧ fR j ≠ X j ∧ (∀ i < j, fR j ≠ fR i) ∧ (∀ i < j, X j ≠ fR i) := by
    obtain all : ∀ j < 6, fR j ∉ [Reg.t0, .t2] ∧ fR j ≠ X j ∧ (∀ i < j, fR j ≠ fR i) ∧ (∀ i < j, X j ≠ fR i) := by decide
    exact all j hj
  obtain z : ∀ i < 6, Reg.t0 ≠ fR i ∧ Reg.t2 ≠ fR i := by decide
  obtain t0 : s.gpr .t0 = s0.gpr .t0 := h.gpr _ fun i hi => (z i (by omega_arith)).1
  refine WP.mono (selR_ok d1 d2 hj (by rw [h.gpr _ fun i hi => (z i (by omega_arith)).2, h2]) oal
    (by rw [h.wr]; exact ow j hj) (by rw [t0]; exact hm)) fun s' ⟨m', g', rd', wr', sp'⟩ => ?_
  rw [t0, h.gpr _ d3, h.gpr _ d4] at m'
  refine ⟨fun r hr => ?_, by rw [rd', h.rd], by rw [wr', h.wr], by rw [sp', h.sp], ?_, fun i hi => ?_⟩
  · rw [g' r (hr j (by omega_arith)), h.gpr r fun i hi => hr i (by omega_arith)]
  · rw [m']
    exact h.frame.writeW (List.mem_singleton_self _) _ (out_contains O hj)
  · rw [m']
    by_cases e : i = j
    · subst e; exact dw_write_self ..
    · rw [dw_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact h.val i (by omega_arith)

theorem selsR_ok {O : Addr} {s : State} (h2 : s.gpr .t2 = O) (oal : O.toNat % 8 = 0)
    (ow : ∀ i < 6, InRegions s.wr (O + BitVec.ofNat 64 (8 * i)) 8) (c2 : (s.gpr XC).toNat ≤ 1)
    (c7 : (s.gpr .a7).toNat ≤ 1) :
    WP isa (.block selsR) s fun s' =>
      (∀ r, r ∉ [Reg.s6, .s7, .s8, .s9, .s10, .s11, .t0, .a7] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ Frame [⟨O, 48⟩] s.mem s'.mem ∧
      ov s'.mem O 6 = if (s.gpr XC).toNat + (s.gpr .a7).toNat = 0 then xv s else dv s := by
  unfold selsR
  simp only [List.cons_append, List.nil_append]
  refine wp_or fun s1 u1 => wp_li (imm := 0) (by decide) fun s2 u2 => wp_sub fun s3 u3 => ?_
  obtain K3 : Keeps [.t0, .a7] s s3 := (((upd_keeps u1).trans (upd_keeps u2)).trans (upd_keeps u3)).mono
  obtain b1 : ∀ {x : BitVec 64}, x.toNat ≤ 1 → x = 0 ∨ x = 1 := fun {x} h => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with e | e
    · exact .inl (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    · exact .inr (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
  obtain ⟨hm, hs⟩ : IsMask (s3.gpr .t0) ∧
      (s3.gpr .t0 = BitVec.allOnes 64 ↔ ¬ (s.gpr XC).toNat + (s.gpr .a7).toNat = 0) := by
    rw [u3.gpr, u2.gpr, u2.other .a7 (by decide), u1.gpr]
    rcases b1 c2 with e | e <;> rcases b1 c7 with e' | e' <;> rw [e, e'] <;>
      exact ⟨by unfold IsMask; decide, by decide⟩
  obtain st : ∀ j < 6, ∀ s', SelR O s3 fR X j s' → WP isa (.block (selR j (fR j) (X j))) s' (SelR O s3 fR X (j + 1)) :=
    fun j hj s' h => selR_step hj (by rw [K3.1 _ (by decide), h2]) oal (by rw [K3.2.2.2.1]; exact ow) hm h
  refine WP.block_append (WP.mono (st 0 (by decide) s3 ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s4 h4 => ?_)
  refine WP.block_append (WP.mono (st 1 (by decide) s4 h4) fun s5 h5 => ?_)
  refine WP.block_append (WP.mono (st 2 (by decide) s5 h5) fun s6 h6 => ?_)
  refine WP.block_append (WP.mono (st 3 (by decide) s6 h6) fun s7 h7 => ?_)
  refine WP.block_append (WP.mono (st 4 (by decide) s7 h7) fun s8 h8 => ?_)
  refine WP.mono (st 5 (by decide) s8 h8) fun s9 h9 => ?_
  refine ⟨fun r hr => ?_, by rw [h9.rd, K3.2.2.1], by rw [h9.wr, K3.2.2.2.1], by rw [h9.sp, K3.2.2.2.2],
    by rw [← K3.2.1]; exact h9.frame, ?_⟩
  · obtain nf : ∀ r, r ∉ [Reg.s6, .s7, .s8, .s9, .s10, .s11, .t0, .a7] → (∀ i < 6, r ≠ fR i) ∧ r ∉ [Reg.t0, .a7] := by
      intro r; cases r <;> decide
    rw [h9.gpr r (nf r hr).1, K3.1 r (nf r hr).2]
  · obtain kf : ∀ i < 6, fR i ∉ [Reg.t0, .a7] ∧ X i ∉ [Reg.t0, .a7] := by decide
    by_cases h : (s.gpr XC).toNat + (s.gpr .a7).toNat = 0
    · obtain n : ¬ s3.gpr .t0 = BitVec.allOnes 64 := fun e => hs.mp e h
      rw [ite_eq_left h]
      exact VG.Proof.Weierstrass.RISCV64.GenWide.colsV_congr fun i hi => by
        rw [h9.val i hi, ite_eq_right n, K3.1 _ (kf i hi).2]
    · rw [ite_eq_right h]
      obtain e : ov s9.mem O 6 = colsV (fun i => (s.gpr (fR i)).toNat) 6 :=
        VG.Proof.Weierstrass.RISCV64.GenWide.colsV_congr fun i hi => by
          rw [h9.val i hi, ite_eq_left (hs.mpr h), K3.1 _ (kf i hi).1]
      rw [e]
      simp only [colsV, fR, dv, List.getD_cons_zero, List.getD_cons_succ]
      omega_using []

private theorem csubR_nat {V D c t x r : Nat} (hV : V = x + 2 ^ 384 * t) (hV2 : V < 2 * P)
    (hs : D + 2 ^ 384 * c = x + (2 ^ 384 - P)) (hD : D < 2 ^ 384) (hx : x < 2 ^ 384)
    (hr : r = if t + c = 0 then x else D) : r = V % P := by
  rw [show P = 2 ^ 384 - 2 ^ 128 - 2 ^ 96 + 2 ^ 32 - 1 by decide] at *
  split at hr
  · rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  · rw [show V = r + (2 ^ 384 - 2 ^ 128 - 2 ^ 96 + 2 ^ 32 - 1) by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_arith)]

theorem csubR_ok {O : Addr} {s : State} (h2 : s.gpr .t2 = O) (oal : O.toNat % 8 = 0)
    (ow : ∀ i < 6, InRegions s.wr (O + BitVec.ofNat 64 (8 * i)) 8) (hc : (s.gpr XC).toNat ≤ 1)
    (hx : xv s + 2 ^ 384 * (s.gpr XC).toNat < 2 * P) :
    WP isa (.block csubR) s fun s' =>
      (∀ r, r ∉ [Reg.s6, .s7, .s8, .s9, .s10, .s11, .t0, .a0, .a5, .a7] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [⟨O, 48⟩] s.mem s'.mem ∧
      ov s'.mem O 6 = (xv s + 2 ^ 384 * (s.gpr XC).toNat) % P := by
  unfold csubR
  refine WP.block_append (WP.mono constR_ok fun s1 ⟨a1, b1, k1⟩ => ?_)
  refine WP.block_append (WP.mono (sumR_ok a1 b1) fun s2 ⟨v2, c2, k2⟩ => ?_)
  obtain K : Keeps [.t0, .a5, .s6, .s7, .s8, .s9, .s10, .s11, .a7, .a0] s s2 := (k1.trans k2).mono
  refine WP.mono (selsR_ok (O := O) (by rw [K.1 _ (by decide), h2]) oal (by rw [K.2.2.2.1]; exact ow)
    (by rw [K.1 XC (by decide)]; exact hc) c2) fun s3 ⟨g3, rd3, wr3, sp3, f3, v3⟩ => ?_
  obtain x1 : xv s1 = xv s := by
    simp only [xv_eq, k1.1 .t5 (by decide), k1.1 .t6 (by decide), k1.1 .t3 (by decide), k1.1 .t4 (by decide),
      k1.1 .a1 (by decide), k1.1 .a4 (by decide)]
  obtain x2 : xv s2 = xv s := by
    simp only [xv_eq, K.1 .t5 (by decide), K.1 .t6 (by decide), K.1 .t3 (by decide), K.1 .t4 (by decide),
      K.1 .a1 (by decide), K.1 .a4 (by decide)]
  rw [x1] at v2
  rw [x2, K.1 XC (by decide)] at v3
  refine ⟨fun r hr => ?_, by rw [rd3, K.2.2.1], by rw [wr3, K.2.2.2.1], by rw [sp3, K.2.2.2.2],
    by rw [← K.2.1]; exact f3, csubR_nat rfl hx v2 ?_ ?_ v3⟩
  · obtain nf : ∀ r, r ∉ [Reg.s6, .s7, .s8, .s9, .s10, .s11, .t0, .a0, .a5, .a7] →
        r ∉ [Reg.s6, .s7, .s8, .s9, .s10, .s11, .t0, .a7] ∧ r ∉ [Reg.t0, .a5, .s6, .s7, .s8, .s9, .s10, .s11, .a7, .a0] := by
      intro r; cases r <;> decide
    rw [g3 r (nf r hr).1, K.1 r (nf r hr).2]
  · obtain l1 := (s2.gpr .s6).isLt
    obtain l2 := (s2.gpr .s7).isLt
    obtain l3 := (s2.gpr .s8).isLt
    obtain l4 := (s2.gpr .s9).isLt
    obtain l5 := (s2.gpr .s10).isLt
    obtain l6 := (s2.gpr .s11).isLt
    simp only [dv]
    omega_using [l1, l2, l3, l4, l5, l6]
  · exact VG.Proof.Weierstrass.RISCV64.GenWide.colsV_lt _ (fun i => (s.gpr (X i)).isLt) 6

theorem redTail_ok : Rows.TailOk lay P (reduce ++ csubR) :=
  fun {b O s A Z} hc ht2 oal ow _ hX hZ hp => by
  refine WP.block_append (WP.mono (reduce_ok hc) fun s1 ⟨c1, r1, f1, x1, Q, hQ, hv⟩ => ?_)
  have hX' : A < 2 ^ 384 := hX
  obtain pv : prodV s.mem b = A * Z := by
    rw [← accW_prodV, VG.Proof.X25519.RISCV64.R64.accW_eq]; exact hp
  rw [pv] at hv
  obtain ⟨hV, hVm⟩ := mont_nat hv hX' hZ hQ
  refine WP.mono (csubR_ok (O := O) (by rw [r1.gpr _ (by decide), ht2]) oal (by rw [r1.wr]; exact ow) x1 hV)
    fun s2 ⟨g2, rd2, wr2, sp2, f2, v2⟩ => ?_
  refine ⟨fun r hr => ?_, by rw [rd2, r1.rd], by rw [wr2, r1.wr], by rw [sp2, r1.sp],
    (f1.mono (by simp [lay, VG.Proof.Weierstrass.RISCV64.P384Field.AR, ACC])).trans (f2.mono (by simp [lay])),
    by show ov s2.mem O 6 < P; rw [v2]; exact Nat.mod_lt _ P_pos, ?_⟩
  · obtain nf : ∀ r, r ∉ Rows.clobP lay →
        r ∉ [Reg.s6, .s7, .s8, .s9, .s10, .s11, .t0, .a0, .a5, .a7] ∧ r ∉ clobR := by
      intro r; cases r <;> decide
    rw [g2 r (nf r hr).1, r1.gpr r (nf r hr).2]
  · show ov s2.mem O 6 * 2 ^ 384 % P = A * Z % P
    rw [v2]; exact hVm

/-- A six-word product by rows, whose tail reduces it modulo `m`, meets `CoreOkA`. -/
theorem rows_core {m : Nat} {tail : List Instr} {L : Impl.Weierstrass.RISCV64.Rows.Lay} (hL : Rows.LOk L) (hk : L.k = 6)
    (hs : L.sv = 1664) (hp : L.pp = 1760) (hc : ∀ r, r ∉ clobM → r ∉ Rows.clobP L ∨ r ∈ L.KR)
    (o : Impl.Weierstrass.RISCV64.Rows.Order) (ht : Rows.TailOk L m tail) :
    CoreOkA (Impl.Weierstrass.RISCV64.Rows.fastWith L tail o) (fun _ B => B < m)
      (fun A B r => r < m ∧ r * 2 ^ 384 % m = A * B % m) :=
  fun {W s a bb o'} hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hB => by
  obtain own : Rows.own L (W + BitVec.ofNat 64 2048) = ⟨W + BitVec.ofNat 64 3712, 192⟩ := by
    rw [Rows.own, hk, hs, hp, off_add]
  obtain dis : ∀ x, x + 48 ≤ 3712 → ∀ i < L.k, Region.Disjoint ⟨W + BitVec.ofNat 64 x + BitVec.ofNat 64 (8 * i), 8⟩
      (Rows.own L (W + BitVec.ofNat 64 2048)) := fun x hx i hi => by
    rw [own, off_add]
    exact Offset.disjoint W (.inl (by omega_using [hx, hi, hk])) (by omega_using [hx, hi, hk]) (by decide)
  refine WP.mono (Rows.fastWith_ok hL (m := m) o ht hw.ctx h4 h5 h2 (al8 hw.al ha8) (al8 hw.al hb8) (al8 hw.al ho8)
    (by rw [hk]; exact hw.inR (by omega_using [ha])) (by rw [hk]; exact hw.inR (by omega_using [hb]))
    (by rw [hk]; exact hw.inW (by omega_using [ho])) (dis a ha) (dis bb hb) ?_ (by rw [hk]; exact hB))
    fun s' ⟨v1, v2, f, g, rd, wr, sp⟩ => ⟨⟨by rw [hk] at v1; exact v1, ?_⟩, ?_, fun r hr => g r (hc r hr), rd, wr, sp⟩
  · rw [own, hk]
    exact Offset.disjoint W (.inl (by omega_using [ho])) (by omega_using [ho]) (by decide)
  · rw [hk] at v2
    have v2 : d6 s'.mem (W + BitVec.ofNat 64 o') * (2 ^ 64) ^ 6 % m = _ := v2
    simp only [← Nat.pow_mul, Nat.reduceMul] at v2
    exact v2
  · rw [own, hk] at f
    refine f.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩

theorem fast_core : CoreOkA (Impl.Weierstrass.RISCV64.Rows.fastWith lay (reduce ++ csubR) order) (fun _ B => B < P) mulRes :=
  rows_core lay_ok rfl rfl rfl (by intro r; cases r <;> decide) _ redTail_ok

/-! ## The contracts for aligned offsets -/

theorem mulA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (mulRV p384p)).pre s) :
    ∃ t s', Exec isa mulFnA s t s' ∧ abiPreserved s s' ∧ (mulRV p384p).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fnA_rv rfl (@fast_core) hs.1.1 hs.2 (by rw [← p_eq]; exact hs.1.2)
  exact ⟨t, s', he, a, by rw [p_eq]; exact v1, by rw [p_eq]; exact v2, k⟩

theorem addA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (addRV p384p)).pre s) :
    ∃ t s', Exec isa addFnA s t s' ∧ abiPreserved s s' ∧ (addRV p384p).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fnA_rv rfl (@CoreOk.toA _ _ _ (@addCore_core)) hs.1.1 hs.2 (by rw [← p_eq]; exact hs.1.2)
  exact ⟨t, s', he, a, by rw [p_eq]; exact v, k⟩

theorem subA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (subRV p384p)).pre s) :
    ∃ t s', Exec isa subFnA s t s' ∧ abiPreserved s s' ∧ (subRV p384p).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fnA_rv rfl (@CoreOk.toA _ _ _ (@subCore_core)) hs.1.1 hs.2 (by rw [← p_eq]; exact hs.1.2)
  exact ⟨t, s', he, a, by rw [p_eq]; exact v, k⟩

theorem mul_rv (s : State) (hs : (mulRV p384p).pre s) :
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧ (mulRV p384p).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fn_rv (@mulCore_core) hs.1 (by rw [← p_eq]; exact hs.2)
  exact ⟨t, s', he, a, by rw [p_eq]; exact v1, by rw [p_eq]; exact v2, k⟩

theorem add_rv (s : State) (hs : (addRV p384p).pre s) :
    ∃ t s', Exec isa addFn s t s' ∧ abiPreserved s s' ∧ (addRV p384p).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fn_rv (@addCore_core) hs.1 (by rw [← p_eq]; exact hs.2)
  exact ⟨t, s', he, a, by rw [p_eq]; exact v, k⟩

theorem sub_rv (s : State) (hs : (subRV p384p).pre s) :
    ∃ t s', Exec isa subFn s t s' ∧ abiPreserved s s' ∧ (subRV p384p).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fn_rv (@subCore_core) hs.1 (by rw [← p_eq]; exact hs.2)
  exact ⟨t, s', he, a, by rw [p_eq]; exact v, k⟩

/-! ## Constant time -/

open VG.Proof.Ed25519.RISCV64 (mulAgreeLo mulZext_rel)

/-- `fn core` is constant time if the taint analysis finds `core` so, from the
pointers' and offsets' registers after the zero-extension. -/
theorem fn_ct {core : Prog isa} {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → mulAgreeLo s₁ s₂)
    (h : RelCT isa (VG.RISCV64.Taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3]))
      (.seq (.block ptrs) (.ite (.zero .t0) core
        (.seq (.block (([.addi .t1 .t2 0] : List Instr) ++ unpack .t4 SA 0 ++ unpack .t5 SB 0 ++
            ([.addi .t4 .a3 SA, .addi .t5 .a3 SB, .addi .t2 .a3 SO] : List Instr))) <|
          .seq core (.block (pack .t1 SO 0))))) fun _ _ => True) :
    ConstantTime isa Pre Pub (fn core) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold fn
  refine RelCT.seq (mulZext_rel.mono (fun _ _ ⟨h₁, h₂, hp⟩ => hpub _ _ h₁ h₂ hp) fun _ _ h => h) ?_
  exact h.mono (fun _ _ ⟨hsp, hr⟩ => ⟨hsp, fun r h => hr r (by simpa using h)⟩) fun _ _ h => h

/-! ## The shared contracts -/

theorem read_zero : ∀ (n : Nat) (a : Addr), (Mem.read (fun _ => 0) a n).toNat = 0
  | 0, _ => rfl
  | n + 1, a => by rw [VG.Proof.Mont.read_toNat_succ, read_zero n]; rfl

/-- A state satisfying the preconditions: `ws` at `0x1000`, every offset 0, memory zero. -/
def satWs : State where
  gpr r := match r with | .a0 => 0x1000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 8192⟩]

/-! The constant-time analyses of the calls of the functions from their arguments, each done once
for every check of code that calls it (`taint_decide_sum`), which keep what is public of
`s0`–`s5`, or `s11` for the sum and the difference: the functions write none of them. -/
taint_summary mulASum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.Mont.p384p.fn "mul") mulFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5])
taint_summary addASum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.Mont.p384p.fn "add") addFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
taint_summary subASum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.Mont.p384p.fn "sub") subFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])

end VG.Proof.Weierstrass.RISCV64.P384Field
