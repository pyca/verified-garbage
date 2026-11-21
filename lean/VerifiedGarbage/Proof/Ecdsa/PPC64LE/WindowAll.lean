module

public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.Window
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.WindowA
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.Window3
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.Window3A
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.LadderP
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Proof.Weierstrass.Law3
public import VerifiedGarbage.Impl.Ecdh.PPC64LE
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Flags
import VerifiedGarbage.Proof.Weierstrass.JacDblA
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `[k]P` by windows on PPC64LE, for every curve

The windows of `Impl/Ecdsa/PPC64LE/Window.lean` (four bits, `a = -3`),
`WindowA.lean` (any `a`), `Window3.lean` and `Window3A.lean` (three bits) on
the signature's layout, once for every curve, for `P` affine at ECDH's slots
of the peer's point (`PX`, `PY` and `ONEP`):

* the lemmas that depend on neither the curve nor the layout (namespace
  `Window`, as the curves' files had them): `ofN_ok` (a formula on numbered
  slots, renamed to the slots of a sum), `wstep` (a window, on points), the
  nibble's arithmetic and the masks (`eqMask_ok`);
* the layout as arithmetic in the configuration's number of words `c.n`
  (slot `i` at `64 + 8 n i`, the table from `4096 + 192 n`, `24 n` bytes an
  entry), for a configuration that is the signature's (`CfgOk`);
* `WAll.AKit`, what differs between `a = -3` and any `a`: the slot and value
  of `b`'s constant, the doubling and the addition with what they compute
  (`dbl_ok`, `add_ok`), and the programs built on them (`AKit.am3`,
  `AKit.anyA`); over it, `quad4_ok` and `quad3_ok`: `R = 16 R` and `R = 8 R`;
* `WAll.Kit`, what differs between four-bit and three-bit windows: the bits
  `wb` of a window, the table's `E = 2^wb` entries, the number of windows,
  `R = 2^wb R` and the window's bits read (`Kit.w4`, `Kit.w3`); over it,
  `build_ok` (the table holds `[e]P` in entry `e`), `select_ok` (the window
  `k_j` and its entry, by scanning under masks), `step_ok` (a window) and
  `mul_ok` (from `R = O`, `R = [k]P` for any `k` of `wb · nw` bits).

Each `<Curve>/Window.lean` is the curve's kit and the statements about it
that other modules use.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE.Window

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdsa.PPC64LE.Window
open VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Proof.Weierstrass.PPC64LE.Point (KeepR tmv)
open VG.Spec.Weierstrass (Point Fe mul onCurve)

/-! ## Formulas on numbered slots -/

/-- A formula on numbered slots (`NumOk`), renamed to the slots of a sum. -/
theorem ofN_ok {M : Impl.Mont.Mod} {base : Addr} {S' : Impl.Weierstrass.Mont.Modulus} [NeZero S'.m]
    (hM : ModOk S'.k S'.m) (hk : S'.k = M.n) {Sl : Nat → Prop} (hL : Lay M (own M.n) Sl)
    (hm : UnitMod S'.m (2 ^ (64 * M.n))) {N : List FOp} (hN : NumOk N) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {V : List Nat}
    {E : Nat → Fin S'.m} {s : State} (hI : Inv M.n base S'.m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprog S' (ofN N S p q o)) s fun s' => KeepR M.n (fun x => x) base (rcbW S o) s s' ∧
      Inv M.n base S'.m Sl ([o.x, o.y, o.z] ++ V) (runOps (ofN N S p q o) E) s' ∧
      (runOps (ofN N S p q o) E o.x, runOps (ofN N S p q o) E o.y, runOps (ofN N S p q o) E o.z) =
        (runOps N (fun y => E (rcbσ S p q o y)) 6, runOps N (fun y => E (rcbσ S p q o y)) 7,
          runOps N (fun y => E (rcbσ S p q o y)) 8) ∧
      ∀ x, x ∉ rcbW S o → runOps (ofN N S p q o) E x = E x := by
  obtain hR : readsOk (ofN N S p q o) V = true := readsOk_mono (ofN_readsOk hN S p q o) hV
  refine WP.mono (fprog_ok hM hk hL hm _ hI (fun op hop x hx => hSl x (ofN_slots op hop x hx)) hR)
    fun s' ⟨hk', hI'⟩ => ⟨hk'.mono fun w hw => ?_, hI'.sub fun x hx => ?_, ?_,
      fun x hx => runOps_of_not_out _ _ fun op hop h => hx (h ▸ ofN_out hN op hop)⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact ofN_out hN op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (ofN_out_mem hN hx)
    · exact Or.inl hx
  · exact congrArg₂ Prod.mk (ofN_run hN hA E 6) (congrArg₂ Prod.mk (ofN_run hN hA E 7) (ofN_run hN hA E 8))

/-- `2 P`. -/
abbrev d2 {C : Spec.Weierstrass.Curve} (P : Point C) : Point C := Spec.Weierstrass.add P P

/-- `16 P`, by four doublings. -/
abbrev d16 {C : Spec.Weierstrass.Curve} (P : Point C) : Point C := d2 (d2 (d2 (d2 P)))

/-- The slot of `b`: ECDH's (`BP`, slot 40). -/
abbrev BPs : Nat := 40

/-! ## The points -/

section
variable {C : Spec.Weierstrass.Curve}

/-- `R` before window `j - 1`: `[k >>> 4 j]P`. -/
abbrev wpt (Q : Point C) (k j : Nat) : Point C := mul (k >>> (4 * j)) Q

theorem shr_four (k j : Nat) : k >>> (4 * j) = 16 * (k >>> (4 * (j + 1))) + (k >>> (4 * j)) % 16 := by
  rw [show 4 * (j + 1) = 4 * j + 4 by omega_using [], Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (k >>> (4 * j)) 4]
  omega_using []

/-- A window: `16 R + [k_j]Q`, for `R` before it, is `R` after it. -/
theorem wstep (hL : Law C) {Q : Point C} (hQ : onCurve C Q = true) (k j : Nat) :
    Spec.Weierstrass.add (d16 (wpt Q k (j + 1))) (mul ((k >>> (4 * j)) % 16) Q) = wpt Q k j := by
  obtain ek := shr_four k j
  simp only [wpt, d16, d2]
  generalize (k >>> (4 * j)) % 16 = a at ek ⊢
  rw [ek]
  generalize k >>> (4 * (j + 1)) = m
  obtain hX := hL.onCurve_mul hQ m
  obtain h2 := hL.onCurve_add hX hX
  obtain h4 := hL.onCurve_add h2 h2
  obtain h8 := hL.onCurve_add h4 h4
  obtain h16 := hL.onCurve_add h8 h8
  obtain ⟨M, _, f, hf⟩ := hL.group
  apply hf.inj (hL.onCurve_add h16 (hL.onCurve_mul hQ _)) (hL.onCurve_mul hQ _)
  rw [hf.add h16 (hL.onCurve_mul hQ _), hf.add h8 h8, hf.add h4 h4, hf.add h2 h2, hf.add hX hX,
    hf.mul hQ, hf.mul hQ, hf.mul hQ]
  obtain hu : ((16 * m + a : Nat) : Int) = m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + a := by
    omega_using []
  rw [hu]
  simp only [Lean.Grind.IntModule.add_zsmul]
  grind

theorem mul_zero' (P : Point C) : mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; rfl

theorem mul_one' (P : Point C) : mul 1 P = P := by
  rw [Spec.Weierstrass.mul, ite_eq_right (by decide), show (1 : Nat) / 2 = 0 from rfl, mul_zero',
    ite_eq_right (by decide)]
  rfl

/-- `[n + 1]Q = [n]Q + Q`. -/
theorem mul_succ' (hL : Law C) {Q : Point C} (hQ : onCurve C Q = true) (n : Nat) :
    Spec.Weierstrass.add (mul n Q) Q = mul (n + 1) Q := by
  obtain ⟨M, _, f, hf⟩ := hL.group
  apply hf.inj (hL.onCurve_add (hL.onCurve_mul hQ _) hQ) (hL.onCurve_mul hQ _)
  rw [hf.add (hL.onCurve_mul hQ _) hQ, hf.mul hQ, hf.mul hQ, show ((n + 1 : Nat) : Int) = n + 1 by omega_using []]
  simp only [Lean.Grind.IntModule.add_zsmul, Lean.Grind.IntModule.one_zsmul]

end

/-! ## The nibble and the entry -/

/-- The bit `b` as a number. -/
abbrev bv (b : Bool) : Nat := if b then 1 else 0

theorem bv_shift (k off i : Nat) : bv (k.testBit (off + i)) = (k >>> off) / 2 ^ i % 2 := by
  rw [← Nat.testBit_shiftRight, ← Nat.toNat_testBit]
  cases (k >>> off).testBit i <;> rfl

theorem nib_eq (k j : Nat) : (k >>> (4 * j)) % 16 = bv (k.testBit (4 * j)) + 2 * bv (k.testBit (4 * j + 1)) +
    4 * bv (k.testBit (4 * j + 2)) + 8 * bv (k.testBit (4 * j + 3)) := by
  have h0 := bv_shift k (4 * j) 0
  simp only [Nat.add_zero] at h0
  rw [h0, bv_shift k (4 * j) 1, bv_shift k (4 * j) 2, bv_shift k (4 * j) 3]
  simp only [Nat.reducePow, Nat.div_one]
  generalize k >>> (4 * j) = m
  omega_arith

theorem byte_bit (b : Bool) : ((if b then 1 else 0 : BitVec 8)).setWidth 64 = BitVec.ofNat 64 (bv b) := by
  cases b <;> rfl

theorem horner_eq (b0 b1 b2 b3 : Bool) :
    let x1 := BitVec.ofNat 64 (bv b3) + BitVec.ofNat 64 (bv b3) + BitVec.ofNat 64 (bv b2)
    let x2 := x1 + x1 + BitVec.ofNat 64 (bv b1)
    x2 + x2 + BitVec.ofNat 64 (bv b0) = BitVec.ofNat 64 (bv b0 + 2 * bv b1 + 4 * bv b2 + 8 * bv b3) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> rfl

theorem eqm_eq : ∀ a < 16, ∀ e < 16, (0 : BitVec 64) - (((BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 e) -
    BitVec.ofNat 64 1) >>> 63) = if a = e then BitVec.allOnes 64 else 0 := by decide

/-- The mask `r10` of `r9 = e`. -/
theorem eqMask_ok {s : State} {a e : Nat} (ha : a < 16) (he : e < 16) (h9 : s.gpr .r9 = BitVec.ofNat 64 a) :
    WP isa (.block (Cfg.eqMask e)) s fun s' =>
      s'.gpr .r10 = (if decide (a = e) then BitVec.allOnes 64 else 0) ∧ Kp [.r5, .r10] s s' ∧ s'.mem = s.mem := by
  rw [Cfg.eqMask]
  refine wp_step (exec_li (by omega_using [he])) ?_
  refine wp_step exec_logic ?_
  refine wp_step (exec_subi (by decide) (by decide)) ?_
  refine wp_step (exec_lsr_d (by decide)) ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_sub (WP.block_nil ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩)
  · simp only [write_gpr, ite_true, reduceCtorEq, ite_false, h9, decide_eq_true_eq]
    exact eqm_eq a ha e he
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, hr.1, hr.2, ite_false]

theorem rk_of_kp {rs : List Reg} {s s' : State} (h : Kp rs s s') (hs : ∀ r ∈ rs, r ∈ powClob := by decide) :
    Rk powClob s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr, h.sp⟩

theorem rk_mono {rs : List Reg} {s s' : State} (h : Rk rs s s') (hs : ∀ r ∈ rs, r ∈ powClob := by decide) :
    Rk powClob s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr, h.sp⟩

end VG.Proof.Ecdsa.PPC64LE.Window

/-! # The windows, for every curve -/

namespace VG.Proof.Ecdsa.PPC64LE.WAll

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdsa.PPC64LE.Window
open VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Proof.Weierstrass.PPC64LE.Point (KeepR tmv)
open VG.Spec.Weierstrass (Point Fe mul onCurve)
open VG.Proof.Ecdsa.PPC64LE.Window

variable {c : Cfg}

/-- Slot `i` of the signature's layout, as arithmetic has it (`c.sl i`). -/
local notation "σ[" i "]" => 64 + 8 * Cfg.n c * i

/-- The table's start (`Cfg.tblAt c`). -/
local notation "τ" => 4096 + 64 * Cfg.n c * 3

/-! ## What the proof needs of a configuration -/

theorem n_le (h : CfgOk c) : c.n ≤ 9 := Nat.le_of_lt_succ h.n10

theorem unitP (h : CfgOk c) : UnitMod c.C.p (2 ^ (64 * c.n)) := unitMod_pow_two h.p_odd _

theorem fpP (h : CfgOk c) : ModOk c.SP.k c.C.p := by
  have := h.fp
  rwa [h.fpm] at this

variable (c) in
theorem p0 : 0 < c.C.p := Nat.pos_of_ne_zero (NeZero.ne _)

/-! ## The layout -/

theorem own_eq (n : Nat) : own n = 4096 - 64 * n := rfl

theorem rPt_eq : Cfg.rPt c = ⟨σ[14], σ[15], σ[16]⟩ := rfl
theorem dPt_eq : Cfg.dPt c = ⟨σ[17], σ[18], σ[19]⟩ := rfl
theorem tPt_eq : Cfg.tPt c = ⟨σ[20], σ[21], σ[22]⟩ := rfl
theorem zeroPt_eq : Cfg.zeroPt c = ⟨σ[3], σ[3], σ[3]⟩ := rfl
theorem zop_eq : c.pt ZERO ONEP ZERO = ⟨σ[3], σ[5], σ[3]⟩ := rfl

theorem rcbW_S (bs : Nat) (o : Pt) :
    rcbW (Cfg.slots c bs) o = [σ[23], σ[24], σ[25], σ[26], σ[27], σ[28], o.x, o.y, o.z] := rfl

theorem rcbR_S (bs : Nat) (p q : Pt) :
    rcbR (Cfg.slots c bs) p q = [σ[6], σ[bs], p.x, p.y, p.z, q.x, q.y, q.z] := rfl

variable (c) in
/-- Entry `e`'s slots. -/
abbrev ent (e : Nat) : Pt := Cfg.entry c e

theorem ent_eq (e : Nat) : ent c e = ⟨τ + 24 * c.n * e, τ + 24 * c.n * e + 8 * c.n, τ + 24 * c.n * e + 16 * c.n⟩ := rfl

variable (c) in
/-- `P`'s slots: ECDH's peer point, with `Z = 1`. -/
abbrev gPt : Pt := c.pt Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY ONEP

theorem gPt_eq : gPt c = ⟨σ[38], σ[43], σ[5]⟩ := rfl

theorem ent_mono (n : Nat) {e e' : Nat} (h : e < e') : 24 * n * e + 24 * n ≤ 24 * n * e' := by
  have := Nat.mul_le_mul_left (24 * n) (Nat.succ_le_of_lt h)
  rwa [Nat.mul_succ] at this

theorem ent_al (n e : Nat) : 24 * n * e % 4 = 0 := by
  rw [Nat.mul_assoc]; omega_using []

theorem sl_step (n : Nat) {i j : Nat} (h : i < j) : 8 * n * i + 8 * n ≤ 8 * n * j := by
  have := Nat.mul_le_mul_left (8 * n) (Nat.succ_le_of_lt h)
  rwa [Nat.mul_succ] at this

/-- A point's coordinate `i`. -/
def crd (p : Pt) : Nat → Nat
  | 0 => p.x
  | 1 => p.y
  | _ => p.z

theorem crd_ent {E e : Nat} (he : e < E) (i : Nat) :
    τ ≤ crd (ent c e) i ∧ crd (ent c e) i + 8 * c.n ≤ τ + 24 * c.n * E := by
  have em := ent_mono c.n he
  match i with
  | 0 => exact ⟨show τ ≤ τ + 24 * c.n * e by omega_using [],
      show τ + 24 * c.n * e + 8 * c.n ≤ _ by omega_using [em]⟩
  | 1 => exact ⟨show τ ≤ τ + 24 * c.n * e + 8 * c.n by omega_using [],
      show τ + 24 * c.n * e + 8 * c.n + 8 * c.n ≤ _ by omega_using [em]⟩
  | _ + 2 => exact ⟨show τ ≤ τ + 24 * c.n * e + 16 * c.n by omega_using [],
      show τ + 24 * c.n * e + 16 * c.n + 8 * c.n ≤ _ by omega_using [em]⟩

/-- The slots the windows' arithmetic may use: those from zero's (past `p`
and the temporary) up to the peer's point's, below the functions' own
working space. -/
def wS (n x : Nat) : Prop := ∃ i, x = 64 + 8 * n * i ∧ 3 ≤ i ∧ i ≤ 43

theorem wS_sl {i : Nat} (h : 3 ≤ i ∧ i ≤ 43) : wS c.n σ[i] := ⟨i, rfl, h⟩

theorem wLay (h : CfgOk c) : Lay c.MP' (own c.MP'.n) (wS c.n) := by
  have n9 := n_le h
  refine ⟨fun x hx => ?_, fun x y hx hy hne => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨i, rfl, -, hi⟩ := hx
    have := Nat.mul_le_mul_left (8 * c.n) hi
    show σ[i] + 8 * c.n ≤ 4096 - 64 * c.n
    omega_using [this, n9]
  · obtain ⟨i, rfl, -, -⟩ := hx
    obtain ⟨j, rfl, -, -⟩ := hy
    show σ[i] + 8 * c.n ≤ σ[j] ∨ σ[j] + 8 * c.n ≤ σ[i]
    rcases Nat.lt_or_gt_of_ne (fun e : i = j => hne (by rw [e])) with hij | hij
    · exact .inl (by have := sl_step c.n hij; omega_using [this])
    · exact .inr (by have := sl_step c.n hij; omega_using [this])
  · obtain ⟨i, rfl, hi, -⟩ := hx
    have := Nat.mul_le_mul_left (8 * c.n) hi
    show σ[i] + 8 * c.n ≤ σ[0] ∨ σ[0] + 8 * c.n ≤ σ[i]
    exact .inr (by omega_using [this])
  · obtain ⟨i, rfl, hi, -⟩ := hx
    have := Nat.mul_le_mul_left (8 * c.n) hi
    show σ[i] + 8 * c.n ≤ σ[2] ∨ σ[2] + 8 * c.n ≤ σ[i]
    exact .inr (by omega_using [this])

/-- The slots of an addition are among `wS`, for points of numbered slots. -/
theorem wS_rcb {bs : Nat} (hb : bs = 7 ∨ bs = 40) {i1 i2 i3 j1 j2 j3 k1 k2 k3 : Nat}
    (hi : ∀ i ∈ [k1, k2, k3, i1, i2, i3, j1, j2, j3], 3 ≤ i ∧ i ≤ 43) :
    ∀ x ∈ rcbW (Cfg.slots c bs) (c.pt k1 k2 k3) ++ rcbR (Cfg.slots c bs) (c.pt i1 i2 i3) (c.pt j1 j2 j3),
      wS c.n x := by
  intro x hx
  have e : rcbW (Cfg.slots c bs) (c.pt k1 k2 k3) ++ rcbR (Cfg.slots c bs) (c.pt i1 i2 i3) (c.pt j1 j2 j3) =
      List.map (fun i => 64 + 8 * c.n * i)
        [23, 24, 25, 26, 27, 28, k1, k2, k3, 6, bs, i1, i2, i3, j1, j2, j3] := rfl
  rw [e] at hx
  obtain ⟨i, hi', rfl⟩ := List.mem_map.mp hx
  refine ⟨i, rfl, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hi' hi
  omega

/-- The slots an addition writes are apart from those it reads, for points
of numbered slots. -/
theorem apart_rcb (n1 : 1 ≤ c.n) {bs : Nat} (hb : bs = 7 ∨ bs = 40) {i1 i2 i3 j1 j2 j3 k1 k2 k3 : Nat}
    (hk : [23, 24, 25, 26, 27, 28, k1, k2, k3].Nodup) (hr : ∀ k ∈ [k1, k2, k3], 14 ≤ k ∧ k ≤ 28)
    (ha : ∀ i ∈ [6, i1, i2, i3, j1, j2, j3], i ∉ [23, 24, 25, 26, 27, 28, k1, k2, k3]) :
    RcbApart (Cfg.slots c bs) (c.pt i1 i2 i3) (c.pt j1 j2 j3) (c.pt k1 k2 k3) := by
  have inj : ∀ i j, 64 + 8 * c.n * i = 64 + 8 * c.n * j → i = j := fun i j e =>
    Nat.eq_of_mul_eq_mul_left (show 0 < 8 * c.n by omega_using [n1]) (Nat.add_left_cancel e)
  have eW : rcbW (Cfg.slots c bs) (c.pt k1 k2 k3) =
      List.map (fun i => 64 + 8 * c.n * i) [23, 24, 25, 26, 27, 28, k1, k2, k3] := rfl
  have eR : rcbR (Cfg.slots c bs) (c.pt i1 i2 i3) (c.pt j1 j2 j3) =
      List.map (fun i => 64 + 8 * c.n * i) [6, bs, i1, i2, i3, j1, j2, j3] := rfl
  refine ⟨?_, fun x hx hx' => ?_⟩
  · rw [eW]
    exact List.Pairwise.map _ (fun a b hab e => hab (inj a b e)) hk
  · rw [eR] at hx
    rw [eW] at hx'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, hj, e⟩ := List.mem_map.mp hx'
    obtain rfl := inj _ _ e
    rcases List.mem_cons.mp hi with rfl | hi
    · exact ha _ (List.mem_cons_self ..) hj
    · rcases List.mem_cons.mp hi with rfl | hi
      · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hj hr
        omega
      · exact ha _ (List.mem_cons_of_mem _ hi) hj

/-! ## Points and constants -/

variable (c) in
/-- A point's slots hold numbers below `p` that represent `P`. -/
structure PtOk (base : Addr) (s : State) (p : Pt) (P : Point c.C) : Prop where
  rep : Rep c.C (tmv c.C c.n base s p.x) (tmv c.C c.n base s p.y) (tmv c.C c.n base s p.z) P
  x : wordsVal s.mem base p.x c.n < c.C.p
  y : wordsVal s.mem base p.y c.n < c.C.p
  z : wordsVal s.mem base p.z c.n < c.C.p

theorem PtOk.of_eq {base : Addr} {s s' : State} {p : Pt} {P : Point c.C} (h : PtOk c base s p P)
    (ex : wordsVal s'.mem base p.x c.n = wordsVal s.mem base p.x c.n)
    (ey : wordsVal s'.mem base p.y c.n = wordsVal s.mem base p.y c.n)
    (ez : wordsVal s'.mem base p.z c.n = wordsVal s.mem base p.z c.n) : PtOk c base s' p P :=
  ⟨by simp only [tmv]; rw [ex, ey, ez]; exact h.rep, by rw [ex]; exact h.x, by rw [ey]; exact h.y,
    by rw [ez]; exact h.z⟩

theorem PtOk.move {base : Addr} {s s' : State} {p o : Pt} {P : Point c.C} (h : PtOk c base s p P)
    (ex : wordsVal s'.mem base o.x c.n = wordsVal s.mem base p.x c.n)
    (ey : wordsVal s'.mem base o.y c.n = wordsVal s.mem base p.y c.n)
    (ez : wordsVal s'.mem base o.z c.n = wordsVal s.mem base p.z c.n) : PtOk c base s' o P :=
  ⟨by simp only [tmv]; rw [ex, ey, ez]; exact h.rep, by rw [ex]; exact h.x, by rw [ey]; exact h.y,
    by rw [ez]; exact h.z⟩

variable (c) in
/-- The constants the windows read: `a` and `bK` (`b`, or `3 b`) in
Montgomery's form (at the slot `bs`), zero and Montgomery's one. -/
structure KC (bs bK : Nat) (base : Addr) (s : State) : Prop where
  ap : wordsVal s.mem base σ[6] c.n = c.C.a * 2 ^ (64 * c.n) % c.C.p
  bp : wordsVal s.mem base σ[bs] c.n = bK * 2 ^ (64 * c.n) % c.C.p
  zero : wordsVal s.mem base σ[3] c.n = 0
  onep : wordsVal s.mem base σ[5] c.n = 2 ^ (64 * c.n) % c.C.p

theorem KC.of_eq {bs bK : Nat} {base : Addr} {s s' : State} (h : KC c bs bK base s)
    (e : ∀ d ∈ [σ[6], σ[bs], σ[3], σ[5]], wordsVal s'.mem base d c.n = wordsVal s.mem base d c.n) :
    KC c bs bK base s' :=
  ⟨(e _ (by simp)).trans h.ap, (e _ (by simp)).trans h.bp, (e _ (by simp)).trans h.zero,
    (e _ (by simp)).trans h.onep⟩

variable (c) in
/-- The table of `k`'s bits, one byte each at `4096`. -/
abbrev Bits (base : Addr) (s : State) (k : Nat) : Prop :=
  ∀ t < 64 * c.n, s.mem (off base (4096 + t)) = if k.testBit t then 1 else 0

theorem Bits.of_unch (n9 : c.n ≤ 9) {base : Addr} {s s' : State} {k : Nat} (h : Bits c base s k)
    {W : List (Nat × Nat)} (hU : Unch base W s.mem s'.mem)
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ 4096 ∨ 4096 + 64 * c.n ≤ w.1) : Bits c base s' k := fun t ht => by
  rw [hU.byte (fun w hw => by have := hW w hw; omega_using [ht, this]) (by omega_using [ht, n9])]; exact h t ht

/-- A scalar shifted by all its bits: `O`. -/
theorem mul_top {C : Spec.Weierstrass.Curve} (Q : Point C) {b k : Nat} (hk : k < 2 ^ b) :
    mul (k >>> b) Q = .infinity := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hk, Spec.Weierstrass.mul]
  rfl

/-! ## What is written -/

variable (c) in
/-- What `R = 16 R` writes: `R`, `D`, `T`, the temporaries and the
functions' own working space. -/
abbrev quadW : List (Nat × Nat) := [(σ[14], 8 * c.n * 15), (4096 - 64 * c.n, 64 * c.n)]

variable (c) in
/-- The slots its field operations write. -/
abbrev quadWl : List Nat :=
  [σ[23], σ[24], σ[25], σ[26], σ[27], σ[28], σ[14], σ[15], σ[16], σ[17], σ[18], σ[19], σ[20], σ[21], σ[22]]

variable (c) in
/-- What an addition writes. -/
abbrev addW (o : Pt) : List (Nat × Nat) :=
  (rcbW (Cfg.slots c 0) o).map (fun w => (w, 8 * c.n)) ++ [(own c.n, 64 * c.n)]

variable (c) in
/-- What the table's additions write: `D`, `T`, the temporaries, the
functions' own working space and the table. -/
abbrev addsW (E : Nat) : List (Nat × Nat) :=
  [(σ[17], 8 * c.n * 12), (4096 - 64 * c.n, 64 * c.n), (τ, 24 * c.n * E)]

variable (c) in
/-- What the windows write. -/
abbrev stepW : List (Nat × Nat) := [(σ[14], 8 * c.n * 15), (4096 - 64 * c.n, 64 * c.n)]

variable (c) in
/-- What `mul` writes. -/
abbrev mulW (E : Nat) : List (Nat × Nat) :=
  [(σ[14], 8 * c.n * 15), (4096 - 64 * c.n, 64 * c.n), (τ, 24 * c.n * E)]

/-- A fact about closed lists of slots and ranges: the lists as their
elements, then arithmetic. -/
local macro "wk_dec" : tactic => `(tactic| (
  (try simp only [rcbW_S, rcbR_S, rPt_eq, dPt_eq, tPt_eq, zeroPt_eq, zop_eq, gPt_eq, ent_eq, quadW, quadWl, addW,
    addsW, stepW, mulW, own_eq, List.cons_append, List.nil_append, List.append_nil, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left,
    Prod.mk.injEq, eq_self, true_or, or_true, and_self, and_true, true_and]) <;> omega_arith))

/-! ## Formulas on numbered slots, for the curve's field -/

/-- `ofN_ok`, for a field whose modulus is `m`. -/
theorem ofN_cast {M : Impl.Mont.Mod} {base : Addr} {S' : Impl.Weierstrass.Mont.Modulus} {m : Nat} [NeZero m]
    (hm' : S'.m = m) (hM : ModOk S'.k m) (hk : S'.k = M.n) {Sl : Nat → Prop} (hL : Lay M (own M.n) Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {N : List FOp} (hN : NumOk N) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {V : List Nat}
    {E : Nat → Fin m} {s : State} (hI : Inv M.n base m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprog S' (ofN N S p q o)) s fun s' => KeepR M.n (fun x => x) base (rcbW S o) s s' ∧
      Inv M.n base m Sl ([o.x, o.y, o.z] ++ V) (runOps (ofN N S p q o) E) s' ∧
      (runOps (ofN N S p q o) E o.x, runOps (ofN N S p q o) E o.y, runOps (ofN N S p q o) E o.z) =
        (runOps N (fun y => E (rcbσ S p q o y)) 6, runOps N (fun y => E (rcbσ S p q o y)) 7,
          runOps N (fun y => E (rcbσ S p q o y)) 8) ∧
      ∀ x, x ∉ rcbW S o → runOps (ofN N S p q o) E x = E x := by
  subst hm'
  exact ofN_ok hM hk hL hm hN hA hSl hI hV

/-- `rcb_ok`, for a field whose modulus is `m`. -/
theorem rcb_cast {M : Impl.Mont.Mod} {base : Addr} {S' : Impl.Weierstrass.Mont.Modulus} {m : Nat} [NeZero m]
    (hm' : S'.m = m) (hM : ModOk S'.k m) (hk : S'.k = M.n) {Sl : Nat → Prop} (hL : Lay M (own M.n) Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {V : List Nat}
    {E : Nat → Fin m} {s : State} (hI : Inv M.n base m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprog S' (rcb S p q o)) s fun s' => KeepR M.n (fun x => x) base (rcbW S o) s s' ∧
      Inv M.n base m Sl (rcbW S o ++ V) (runOps (rcb S p q o) E) s' ∧
      (runOps (rcb S p q o) E o.x, runOps (rcb S p q o) E o.y, runOps (rcb S p q o) E o.z) =
        VG.Proof.Weierstrass.rcbAdd (E S.a) (E S.b3) (E p.x) (E p.y) (E p.z) (E q.x) (E q.y)
          (E q.z) ∧
      ∀ x, x ∉ rcbW S o → runOps (rcb S p q o) E x = E x := by
  subst hm'
  exact rcb_ok hM hk hL hm hA hSl hI hV

/-- A formula on numbered slots, on the slots of `wS` and the curve's field. -/
theorem ofN_c (h : CfgOk c) {base : Addr} {N : List FOp} (hN : NumOk N) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, wS c.n x) {V : List Nat}
    {E : Nat → Fe c.C} {s : State} (hI : Inv c.n base c.C.p (wS c.n) V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprog c.SP (ofN N S p q o)) s fun s' => KeepR c.n (fun x => x) base (rcbW S o) s s' ∧
      Inv c.n base c.C.p (wS c.n) ([o.x, o.y, o.z] ++ V) (runOps (ofN N S p q o) E) s' ∧
      (runOps (ofN N S p q o) E o.x, runOps (ofN N S p q o) E o.y, runOps (ofN N S p q o) E o.z) =
        (runOps N (fun y => E (rcbσ S p q o y)) 6, runOps N (fun y => E (rcbσ S p q o y)) 7,
          runOps N (fun y => E (rcbσ S p q o y)) 8) ∧
      ∀ x, x ∉ rcbW S o → runOps (ofN N S p q o) E x = E x :=
  ofN_cast (M := c.MP') h.fpm (fpP h) h.fpk (wLay h) (unitP h) hN hA hSl hI hV

/-! ## The doublings and the addition, for `a = -3` and for any `a` -/

/-- A Jacobian doubling for `a = -3` from `p` to `o`, on `InvJ`. -/
theorem dblStep3_ok (h : CfgOk c) (ha3 : AM3 c.C) {bs : Nat} (hL : Law c.C) {base : Addr} {s : State} {p o : Pt}
    (hA : RcbApart (Cfg.slots c bs) p p o)
    (hsl : ∀ x ∈ rcbW (Cfg.slots c bs) o ++ rcbR (Cfg.slots c bs) p p, wS c.n x) {V : List Nat} {E : Nat → Fe c.C}
    (hI : Inv c.n base c.C.p (wS c.n) V E s) (hV : ∀ x ∈ rcbR (Cfg.slots c bs) p p, x ∈ V)
    (_ : E σ[6] = Fin.ofNat c.C.p c.C.a) {P : Point c.C}
    (hP : onCurve c.C P = true) (hJ : InvJ c.C (E p.x) (E p.y) (E p.z) P) :
    WP isa (fprog c.SP (dblJ (Cfg.slots c bs) p o)) s fun s' =>
      KeepR c.n (fun x => x) base (rcbW (Cfg.slots c bs) o) s s' ∧
      ∃ E', Inv c.n base c.C.p (wS c.n) ([o.x, o.y, o.z] ++ V) E' s' ∧ InvJ c.C (E' o.x) (E' o.y) (E' o.z) (d2 P) ∧
        ∀ x, x ∉ rcbW (Cfg.slots c bs) o → E' x = E x := by
  rw [dblJ_eq]
  refine WP.mono (ofN_c h dblJN_ok hA hsl hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, InvJ.dbl' hL ha3 hP hJ (v.trans (dblJN_run _)), kp⟩

/-- A Jacobian doubling for any `a` from `p` to `o`, on `InvJ`. -/
theorem dblStepA_ok (h : CfgOk c) {bs : Nat} (hL : Law c.C) {base : Addr} {s : State} {p o : Pt}
    (hA : RcbApart (Cfg.slots c bs) p p o)
    (hsl : ∀ x ∈ rcbW (Cfg.slots c bs) o ++ rcbR (Cfg.slots c bs) p p, wS c.n x) {V : List Nat} {E : Nat → Fe c.C}
    (hI : Inv c.n base c.C.p (wS c.n) V E s) (hV : ∀ x ∈ rcbR (Cfg.slots c bs) p p, x ∈ V)
    (ha : E σ[6] = Fin.ofNat c.C.p c.C.a) {P : Point c.C}
    (hP : onCurve c.C P = true) (hJ : InvJ c.C (E p.x) (E p.y) (E p.z) P) :
    WP isa (fprog c.SP (dblJa (Cfg.slots c bs) p o)) s fun s' =>
      KeepR c.n (fun x => x) base (rcbW (Cfg.slots c bs) o) s s' ∧
      ∃ E', Inv c.n base c.C.p (wS c.n) ([o.x, o.y, o.z] ++ V) E' s' ∧ InvJ c.C (E' o.x) (E' o.y) (E' o.z) (d2 P) ∧
        ∀ x, x ∉ rcbW (Cfg.slots c bs) o → E' x = E x := by
  rw [dblJa_eq]
  refine WP.mono (ofN_c h dblJaN_ok hA hsl hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, InvJ.dblA' hL hP hJ ha (v.trans (dblJaN_run _)), kp⟩

/-- `R` into Jacobian coordinates in `D`. -/
theorem toJStep_ok (h : CfgOk c) (hL : Law c.C) {bs : Nat} (hb : bs = 7 ∨ bs = 40) {base : Addr} {s : State}
    {V : List Nat} {E : Nat → Fe c.C} (hI : Inv c.n base c.C.p (wS c.n) V E s)
    (hV : ∀ x ∈ rcbR (Cfg.slots c bs) (Cfg.rPt c) (Cfg.zeroPt c), x ∈ V) {P : Point c.C}
    (hR : Rep c.C (E σ[14]) (E σ[15]) (E σ[16]) P) (hz : E σ[3] = 0) :
    WP isa (fprog c.SP (toJ (Cfg.slots c bs) (Cfg.rPt c) (Cfg.zeroPt c) (Cfg.dPt c))) s fun s' =>
      KeepR c.n (fun x => x) base (rcbW (Cfg.slots c bs) (Cfg.dPt c)) s s' ∧
      ∃ E', Inv c.n base c.C.p (wS c.n) ([σ[17], σ[18], σ[19]] ++ V) E' s' ∧
        InvJ c.C (E' σ[17]) (E' σ[18]) (E' σ[19]) P ∧
        ∀ x, x ∉ rcbW (Cfg.slots c bs) (Cfg.dPt c) → E' x = E x := by
  rw [toJ_eq]
  refine WP.mono (ofN_c h toJN_ok (apart_rcb h.n0 hb (by decide) (by decide) (by decide))
    (wS_rcb hb (by decide)) hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, InvJ.of_toJ hL hR hz (v.trans (toJN_run _)), kp⟩

/-- Jacobian coordinates in `p` back to projective ones in `o`. -/
theorem fromJStep_ok (h : CfgOk c) {base : Addr} {s : State} {S : RcbSlots} {p z o : Pt} (hA : RcbApart S p z o)
    (hsl : ∀ x ∈ rcbW S o ++ rcbR S p z, wS c.n x) {V : List Nat} {E : Nat → Fe c.C}
    (hI : Inv c.n base c.C.p (wS c.n) V E s) (hV : ∀ x ∈ rcbR S p z, x ∈ V) :
    WP isa (fprog c.SP (fromJ S p z o)) s fun s' => KeepR c.n (fun x => x) base (rcbW S o) s s' ∧
      ∃ E', Inv c.n base c.C.p (wS c.n) ([o.x, o.y, o.z] ++ V) E' s' ∧
        (E' o.x, E' o.y, E' o.z) = (E p.x * E p.z, E p.y + E z.x, E p.z * E p.z * E p.z) ∧
        ∀ x, x ∉ rcbW S o → E' x = E x := by
  rw [fromJ_eq]
  refine WP.mono (ofN_c h fromJN_ok hA hsl hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, v.trans (fromJN_run _), kp⟩

/-- `o = p + q` by the complete addition for `a = -3` (`b` at slot 40), for
points in slots of `wS`. -/
theorem addPt3_ok (h : CfgOk c) (ha3 : AM3 c.C) (hL : Law c.C) {base : Addr} {s : State} (hw : WsReg s base)
    (hK : KC c 40 c.C.b base s) {p q o : Pt} (hA : RcbApart (Cfg.slots c 40) p q o)
    (hsl : ∀ x ∈ rcbW (Cfg.slots c 40) o ++ rcbR (Cfg.slots c 40) p q, wS c.n x)
    {P P' : Point c.C} (hP : onCurve c.C P = true) (hP' : onCurve c.C P' = true)
    (hp : PtOk c base s p P) (hq : PtOk c base s q P') :
    WP isa (fprog c.SP (rcb3 (Cfg.slots c 40) p q o)) s fun s' =>
      Rk fnClob s s' ∧ Unch base (addW c o) s.mem s'.mem ∧ PtOk c base s' o (Spec.Weierstrass.add P P') := by
  obtain hp0 : 0 < c.C.p := p0 c
  obtain hI : Inv c.n base c.C.p (wS c.n) (rcbR (Cfg.slots c 40) p q)
      (fun x => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base x c.n)) s := by
    refine ⟨hw, fun x hx => hsl x (List.mem_append_right _ hx), fun x hx => ?_, fun x _ => rfl⟩
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt hK.ap (Nat.mod_lt _ hp0)
    · exact lt_of_eq_of_lt hK.bp (Nat.mod_lt _ hp0)
    exacts [hp.x, hp.y, hp.z, hq.x, hq.y, hq.z]
  rw [rcb3_eq]
  refine WP.mono (ofN_c h rcb3N_ok hA hsl hI (fun x hx => hx)) fun s₁ ⟨k₁, I₁, v₁, _⟩ => ?_
  obtain t₁ := v₁.trans (rcb3N_run _)
  obtain eb : toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base σ[40] c.n) = Fin.ofNat c.C.p c.C.b := by
    rw [hK.bp, toM_mont (unitP h)]
  generalize hE : (fun x => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base x c.n)) = E at I₁ t₁
  obtain hrep := hL.add3 ha3 hP hP' hp.rep hq.rep (X3 := runOps (rcb3 (Cfg.slots c 40) p q o) E o.x)
    (Y3 := runOps (rcb3 (Cfg.slots c 40) p q o) E o.y) (Z3 := runOps (rcb3 (Cfg.slots c 40) p q o) E o.z)
    (by
      subst hE
      show rcbAdd3 (Fin.ofNat c.C.p c.C.b) _ _ _ _ _ _ = _
      rw [← eb]
      exact t₁.symm)
  obtain hm : ∀ x ∈ [o.x, o.y, o.z], x ∈ [o.x, o.y, o.z] ++ rcbR (Cfg.slots c 40) p q :=
    fun x hx => List.mem_append_left _ hx
  refine ⟨⟨k₁.gpr, k₁.rd, k₁.wr, k₁.sp⟩, k₁.mem,
    ⟨?_, I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp))⟩⟩
  obtain vx : tmv c.C c.n base s₁ o.x = _ := I₁.val _ (hm _ (by simp))
  obtain vy : tmv c.C c.n base s₁ o.y = _ := I₁.val _ (hm _ (by simp))
  obtain vz : tmv c.C c.n base s₁ o.z = _ := I₁.val _ (hm _ (by simp))
  rw [vx, vy, vz]
  exact hrep

/-- `o = p + q` by the complete addition for any `a` (`3 b` at `B3P`), for
points in slots of `wS`. -/
theorem addPtA_ok (h : CfgOk c) (hL : Law c.C) {base : Addr} {s : State} (hw : WsReg s base)
    (hK : KC c 7 (3 * c.C.b) base s) {p q o : Pt} (hA : RcbApart (Cfg.slots c 7) p q o)
    (hsl : ∀ x ∈ rcbW (Cfg.slots c 7) o ++ rcbR (Cfg.slots c 7) p q, wS c.n x)
    {P P' : Point c.C} (hP : onCurve c.C P = true) (hP' : onCurve c.C P' = true)
    (hp : PtOk c base s p P) (hq : PtOk c base s q P') :
    WP isa (fprog c.SP (rcb (Cfg.slots c 7) p q o)) s fun s' =>
      Rk fnClob s s' ∧ Unch base (addW c o) s.mem s'.mem ∧ PtOk c base s' o (Spec.Weierstrass.add P P') := by
  obtain hp0 : 0 < c.C.p := p0 c
  obtain hI : Inv c.n base c.C.p (wS c.n) (rcbR (Cfg.slots c 7) p q)
      (fun x => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base x c.n)) s := by
    refine ⟨hw, fun x hx => hsl x (List.mem_append_right _ hx), fun x hx => ?_, fun x _ => rfl⟩
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt hK.ap (Nat.mod_lt _ hp0)
    · exact lt_of_eq_of_lt hK.bp (Nat.mod_lt _ hp0)
    exacts [hp.x, hp.y, hp.z, hq.x, hq.y, hq.z]
  refine WP.mono (rcb_cast (M := c.MP') h.fpm (fpP h) h.fpk (wLay h) (unitP h) hA hsl hI (fun x hx => hx))
    fun s₁ ⟨k₁, I₁, t₁, _⟩ => ?_
  obtain eb : toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base σ[7] c.n) = Fin.ofNat c.C.p (3 * c.C.b) := by
    rw [hK.bp, toM_mont (unitP h)]
  obtain ea : toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base σ[6] c.n) = Fin.ofNat c.C.p c.C.a := by
    rw [hK.ap, toM_mont (unitP h)]
  generalize hE : (fun x => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base x c.n)) = E at I₁ t₁
  obtain hrep := Rep.add hL hP hP' hp.rep hq.rep (X3 := runOps (rcb (Cfg.slots c 7) p q o) E o.x)
    (Y3 := runOps (rcb (Cfg.slots c 7) p q o) E o.y) (Z3 := runOps (rcb (Cfg.slots c 7) p q o) E o.z)
    (by
      subst hE
      show rcbAdd (Fin.ofNat c.C.p c.C.a) (Fin.ofNat c.C.p (3 * c.C.b)) _ _ _ _ _ _ = _
      rw [← eb, ← ea]
      exact t₁.symm)
  obtain hm : ∀ x ∈ [o.x, o.y, o.z], x ∈ rcbW (Cfg.slots c 7) o ++ rcbR (Cfg.slots c 7) p q :=
    fun x hx => List.mem_append_left _ (by simp only [rcbW] at hx ⊢; simp_all)
  refine ⟨⟨k₁.gpr, k₁.rd, k₁.wr, k₁.sp⟩, k₁.mem,
    ⟨?_, I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp))⟩⟩
  obtain vx : tmv c.C c.n base s₁ o.x = _ := I₁.val _ (hm _ (by simp))
  obtain vy : tmv c.C c.n base s₁ o.y = _ := I₁.val _ (hm _ (by simp))
  obtain vz : tmv c.C c.n base s₁ o.z = _ := I₁.val _ (hm _ (by simp))
  rw [vx, vy, vz]
  exact hrep

/-! ## Copies -/

/-- `o = p`, the three coordinates one after the other, for `o`'s slots in
order and `p`'s apart from them all. -/
theorem copyPt_ok {s : State} {base : Addr} (hw : WsReg s base) {o p : Pt}
    (h8 : ∀ x ∈ [o.x, o.y, o.z, p.x, p.y, p.z], x % 4 = 0 ∧ x + 8 * c.n ≤ 8192)
    (hxy : o.x + 8 * c.n ≤ o.y) (hyz : o.y + 8 * c.n ≤ o.z)
    (hp : ∀ a ∈ [p.x, p.y, p.z], a + 8 * c.n ≤ o.x ∨ o.z + 8 * c.n ≤ a) :
    WP isa (.block (Cfg.copyPt c o p)) s fun s' =>
      wordsVal s'.mem base o.x c.n = wordsVal s.mem base p.x c.n ∧
      wordsVal s'.mem base o.y c.n = wordsVal s.mem base p.y c.n ∧
      wordsVal s'.mem base o.z c.n = wordsVal s.mem base p.z c.n ∧ Kp [.r4] s s' ∧
      Unch base [(o.x, 8 * c.n), (o.y, 8 * c.n), (o.z, 8 * c.n)] s.mem s'.mem := by
  have hn := hw.nowrap
  obtain g := fun x hx => h8 x hx
  obtain gp := fun x hx => hp x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g gp
  obtain ⟨⟨ox8, ox⟩, ⟨oy8, oy⟩, ⟨oz8, oz⟩, ⟨px8, px⟩, ⟨py8, py⟩, ⟨pz8, pz⟩⟩ := g
  obtain ⟨hpx, hpy, hpz⟩ := gp
  rw [Cfg.copyPt, Point.copyPt, List.append_assoc]
  refine WP.block_append (WP.mono (copy_ok c.n hw.ws hw.at3 (o := o.x) (a := p.x) ox8 px8
    (by omega_using [ox]) (by omega_using [px]) (by omega_using [hxy, hyz, hpx])) fun s₁ ⟨e₁, r₁, O₁⟩ => ?_)
  obtain hw₁ := hw.of_kp r₁
  refine WP.block_append (WP.mono (copy_ok c.n hw₁.ws hw₁.at3 (o := o.y) (a := p.y) oy8 py8
    (by omega_using [oy]) (by omega_using [py]) (by omega_using [hxy, hyz, hpy])) fun s₂ ⟨e₂, r₂, O₂⟩ => ?_)
  obtain hw₂ := hw₁.of_kp r₂
  refine WP.mono (copy_ok c.n hw₂.ws hw₂.at3 (o := o.z) (a := p.z) oz8 pz8 (by omega_using [oz])
    (by omega_using [pz]) (by omega_using [hxy, hyz, hpz]))
    fun s₃ ⟨e₃, r₃, O₃⟩ => ⟨?_, ?_, ?_, (r₁.trans r₂).trans r₃, ?_⟩
  · rw [O₃.wordsVal (by omega_using [hxy, hyz]) (by omega_using [ox]),
      O₂.wordsVal (by omega_using [hxy]) (by omega_using [ox]), e₁]
  · rw [O₃.wordsVal (by omega_using [hyz]) (by omega_using [oy]), e₂,
      O₁.wordsVal (by omega_using [hxy, hyz, hpy]) (by omega_using [py])]
  · rw [e₃, O₂.wordsVal (by omega_using [hxy, hyz, hpz]) (by omega_using [pz]),
      O₁.wordsVal (by omega_using [hxy, hyz, hpz]) (by omega_using [pz])]
  · exact ((O₁.unch.trans O₂.unch).trans O₃.unch).mono (by simp)

/-! ## The nibble and the entry -/

/-- The nibble `k_j` into `r9`, for `j` in `r31`, from the table of `k`'s
bits. -/
theorem nibble_ok (n9 : c.n ≤ 9) {nw : Nat} (hnw : 4 * nw ≤ 64 * c.n) {s : State} {base : Addr} (hw : WsReg s base)
    {k j : Nat} (hj : j < nw)
    (h31 : s.gpr .r31 = BitVec.ofNat 64 j)
    (ht : ∀ t < 64 * c.n, s.mem (off base (4096 + t)) = if k.testBit t then 1 else 0) :
    WP isa (.block (Cfg.nibble c)) s fun s' =>
      s'.gpr .r9 = BitVec.ofNat 64 ((k >>> (4 * j)) % 16) ∧ Kp [.r4, .r5, .r9] s s' ∧ s'.mem = s.mem := by
  have hs := hw.ws
  have h3 := hw.at3
  rw [Cfg.nibble, show bitsAt c.n 0 = 4096 from rfl]
  obtain a₄ : s.gpr .r3 + s.gpr .r31 <<< 2 = off base (4 * j) := by
    rw [h3, h31]
    simp only [off]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega_using []
  refine wp_step (exec_lsl (by decide)) ?_
  refine wp_step exec_add ?_
  refine wp_step (lbz_ok (base := base) (size := 8192) (by repeat (first | exact hs | refine Ws.write ?_ _ _))
    (by simp only [At, write_gpr, ite_true, reduceCtorEq, ite_false]; exact a₄) (by decide)
    (by omega_using [hj, hnw, n9])) ?_
  refine wp_step exec_add ?_
  refine wp_step (lbz_ok (base := base) (size := 8192) (by repeat (first | exact hs | refine Ws.write ?_ _ _))
    (by simp only [At, write_gpr, ite_true, reduceCtorEq, ite_false]; exact a₄) (by decide)
    (by omega_using [hj, hnw, n9])) ?_
  refine wp_step exec_add ?_
  refine wp_step exec_add ?_
  refine wp_step (lbz_ok (base := base) (size := 8192) (by repeat (first | exact hs | refine Ws.write ?_ _ _))
    (by simp only [At, write_gpr, ite_true, reduceCtorEq, ite_false]; exact a₄) (by decide)
    (by omega_using [hj, hnw, n9])) ?_
  refine wp_step exec_add ?_
  refine wp_step exec_add ?_
  refine wp_step (lbz_ok (base := base) (size := 8192) (by repeat (first | exact hs | refine Ws.write ?_ _ _))
    (by simp only [At, write_gpr, ite_true, reduceCtorEq, ite_false]; exact a₄) (by decide)
    (by omega_using [hj, hnw, n9])) ?_
  refine wp_step exec_add (WP.block_nil ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩)
  · simp only [write_gpr, write_mem, ite_true, reduceCtorEq, ite_false]
    rw [show 4 * j + (4096 + 3) = 4096 + (4 * j + 3) by omega_using [],
      show 4 * j + (4096 + 2) = 4096 + (4 * j + 2) by omega_using [],
      show 4 * j + (4096 + 1) = 4096 + (4 * j + 1) by omega_using [],
      show 4 * j + 4096 = 4096 + 4 * j by omega_using [],
      ht _ (by omega_using [hj, hnw]), ht _ (by omega_using [hj, hnw]), ht _ (by omega_using [hj, hnw]),
      ht _ (by omega_using [hj, hnw]), byte_bit, byte_bit, byte_bit, byte_bit, nib_eq]
    exact horner_eq _ _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, hr.1, hr.2.1, hr.2.2, ite_false]

/-- `D = entry e` if the mask `r10` is all ones (`b`), else `D`. -/
theorem selD_ok (n9 : c.n ≤ 9) {E : Nat} (tf : τ + 24 * c.n * E ≤ 8192) {s : State} {base : Addr}
    (hw : WsReg s base) (b : Bool) (hc : s.gpr .r10 = (if b then BitVec.allOnes 64 else 0)) {e : Nat}
    (he : e < E) :
    WP isa (.block (selPt c.n (Cfg.dPt c) (Cfg.dPt c) (ent c e))) s fun s' =>
      (∀ i < 3, wordsVal s'.mem base (crd (Cfg.dPt c) i) c.n =
        if b then wordsVal s.mem base (crd (ent c e) i) c.n else wordsVal s.mem base (crd (Cfg.dPt c) i) c.n) ∧
      Kp [.r4, .r5] s s' ∧ Unch base [(σ[17], 24 * c.n)] s.mem s'.mem := by
  have hs := hw.ws
  have h3 := hw.at3
  have hn := hw.nowrap
  have em := ent_mono c.n he
  have ea := ent_al c.n e
  rw [selPt, dPt_eq, ent_eq, List.append_assoc]
  simp only
  refine WP.block_append (WP.mono (sel_ok b c.n hs h3 hc (o := σ[17]) (a := σ[17]) (b := τ + 24 * c.n * e)
    (by omega_using []) (by omega_using []) (by omega_using [ea]) (by omega_using [n9]) (by omega_using [n9])
    (by omega_using [em, tf]) (Or.inl (Nat.le_refl _)) (Or.inl (by omega_using []))) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  refine WP.block_append (WP.mono (sel_ok b c.n (k₁.ws hs) (k₁.at h3) (by rw [k₁.g]; exact hc) (o := σ[18])
    (a := σ[18]) (b := τ + 24 * c.n * e + 8 * c.n) (by omega_using []) (by omega_using []) (by omega_using [ea])
    (by omega_using [n9]) (by omega_using [n9]) (by omega_using [em, tf]) (Or.inl (Nat.le_refl _))
    (Or.inl (by omega_using []))) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  refine WP.mono (sel_ok b c.n (k₂.ws (k₁.ws hs)) (k₂.at (k₁.at h3)) (by rw [k₂.g, k₁.g]; exact hc) (o := σ[19])
    (a := σ[19]) (b := τ + 24 * c.n * e + 16 * c.n) (by omega_using []) (by omega_using []) (by omega_using [ea])
    (by omega_using [n9]) (by omega_using [n9]) (by omega_using [em, tf]) (Or.inl (Nat.le_refl _))
    (Or.inl (by omega_using []))) fun s₃ ⟨e₃, k₃, O₃⟩ => ⟨fun i hi => ?_, (k₁.trans k₂).trans k₃,
      ((O₁.unch.trans O₂.unch).trans O₃.unch).cover (by wk_dec)⟩
  obtain a₁ : ∀ d, d + 8 * c.n ≤ σ[17] ∨ σ[18] ≤ d → d + 8 * c.n ≤ 8192 →
      wordsVal s₁.mem base d c.n = wordsVal s.mem base d c.n :=
    fun d h h' => O₁.wordsVal (by omega_using [h]) (by omega_using [h'])
  obtain a₂ : ∀ d, d + 8 * c.n ≤ σ[18] ∨ σ[19] ≤ d → d + 8 * c.n ≤ 8192 →
      wordsVal s₂.mem base d c.n = wordsVal s₁.mem base d c.n :=
    fun d h h' => O₂.wordsVal (by omega_using [h]) (by omega_using [h'])
  obtain a₃ : ∀ d, d + 8 * c.n ≤ σ[19] ∨ σ[20] ≤ d → d + 8 * c.n ≤ 8192 →
      wordsVal s₃.mem base d c.n = wordsVal s₂.mem base d c.n :=
    fun d h h' => O₃.wordsVal (by omega_using [h]) (by omega_using [h'])
  have : i = 0 ∨ i = 1 ∨ i = 2 := by omega_using [hi]
  rcases this with rfl | rfl | rfl
  · show wordsVal s₃.mem base σ[17] c.n =
      if b then wordsVal s.mem base (τ + 24 * c.n * e) c.n else wordsVal s.mem base σ[17] c.n
    rw [a₃ _ (by omega_using []) (by omega_using [n9]), a₂ _ (by omega_using []) (by omega_using [n9]), e₁]
  · show wordsVal s₃.mem base σ[18] c.n =
      if b then wordsVal s.mem base (τ + 24 * c.n * e + 8 * c.n) c.n else wordsVal s.mem base σ[18] c.n
    rw [a₃ _ (by omega_using []) (by omega_using [n9]), e₂, a₁ _ (by omega_using []) (by omega_using [em, tf]),
      a₁ _ (by omega_using []) (by omega_using [n9])]
  · show wordsVal s₃.mem base σ[19] c.n =
      if b then wordsVal s.mem base (τ + 24 * c.n * e + 16 * c.n) c.n else wordsVal s.mem base σ[19] c.n
    rw [e₃, a₂ _ (by omega_using []) (by omega_using [em, tf]), a₂ _ (by omega_using []) (by omega_using [n9]),
      a₁ _ (by omega_using []) (by omega_using [em, tf]), a₁ _ (by omega_using []) (by omega_using [n9])]

/-- The entries below `e` scanned: `D` holds entry `a` if `a < e`, where `r9 = a`. -/
theorem scans_ok (n9 : c.n ≤ 9) {E : Nat} (tf : τ + 24 * c.n * E ≤ 8192) (hE : E ≤ 16) {base : Addr} {a : Nat}
    (ha : a < E) : ∀ e ≤ E, ∀ {s : State}, WsReg s base →
    s.gpr .r9 = BitVec.ofNat 64 a →
    WP isa (.block ((List.range e).flatMap (Cfg.scanEntry c))) s fun s' =>
      (a < e → ∀ i < 3, wordsVal s'.mem base (crd (Cfg.dPt c) i) c.n = wordsVal s.mem base (crd (ent c a) i) c.n) ∧
      Kp [.r4, .r5, .r10] s s' ∧ Unch base [(σ[17], 24 * c.n)] s.mem s'.mem
  | 0, _, s, _, _ => WP.block_nil ⟨fun h => absurd h (by omega_using []), Kp.refl _ _, Unch.refl _ _ _⟩
  | e + 1, he, s, hw, h9 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (scans_ok n9 tf hE ha e (by omega_using [he]) hw h9) fun s₁ ⟨v₁, k₁, U₁⟩ => ?_)
    obtain hw₁ := hw.of_kp k₁
    rw [Cfg.scanEntry]
    refine WP.block_append (WP.mono (eqMask_ok (a := a) (by omega_using [ha, hE]) (e := e) (by omega_using [he, hE]) (by rw [k₁.g]; exact h9))
      fun s₂ ⟨c₂, k₂, m₂⟩ => ?_)
    obtain hw₂ := hw₁.of_kp k₂
    refine WP.mono (selD_ok n9 tf hw₂ _ c₂ (e := e) (by omega_using [he])) fun s₃ ⟨v₃, k₃, U₃⟩ => ⟨fun hae i hi => ?_,
      ((k₁.trans (k₂.mono (by decide))).trans (k₃.mono (by decide))), ?_⟩
    · have hn := hw.nowrap
      obtain ent_u : ∀ d, τ ≤ d → d + 8 * c.n ≤ τ + 24 * c.n * E →
          wordsVal s₂.mem base d c.n = wordsVal s.mem base d c.n := fun d h h' => by
        rw [m₂]; exact U₁.wordsVal (by wk_dec) (by omega_using [h', tf])
      rw [v₃ i hi]
      by_cases h : a = e
      · subst h
        simp only [decide_true, ↓reduceIte]
        exact ent_u _ (crd_ent ha i).1 (crd_ent ha i).2
      · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [m₂]; exact v₁ (by omega_using [hae, h]) i hi
    · rw [m₂] at U₃; exact (U₁.trans U₃).cover (by wk_dec)

variable (c) in
/-- The table up to entry `m`: `[e]Q` in entry `e`. -/
abbrev TabTo (base : Addr) (s : State) (Q : Point c.C) (m : Nat) : Prop :=
  ∀ e ≤ m, PtOk c base s (ent c e) (mul e Q)

theorem TabTo.of_eq {base : Addr} {s s' : State} {Q : Point c.C} {E m : Nat} (h : TabTo c base s Q m)
    (he : ∀ d, τ ≤ d → d + 8 * c.n ≤ τ + 24 * c.n * E →
      wordsVal s'.mem base d c.n = wordsVal s.mem base d c.n) (hm : m < E) :
    TabTo c base s' Q m :=
  fun e hlt => by
    have em := ent_mono c.n (show e < E by omega_using [hm, hlt])
    exact (h e hlt).of_eq (he (τ + 24 * c.n * e) (by omega_using []) (by omega_using [em]))
      (he (τ + 24 * c.n * e + 8 * c.n) (by omega_using []) (by omega_using [em]))
      (he (τ + 24 * c.n * e + 16 * c.n) (by omega_using []) (by omega_using [em]))

/-! ## Three-bit windows: the points and the window's bits -/

/-- `8 P`, by three doublings. -/
abbrev d8 {C : Spec.Weierstrass.Curve} (P : Point C) : Point C := d2 (d2 (d2 P))

theorem shr_three (k j : Nat) : k >>> (3 * j) = 8 * (k >>> (3 * (j + 1))) + (k >>> (3 * j)) % 8 := by
  rw [show 3 * (j + 1) = 3 * j + 3 by omega_using [], Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (k >>> (3 * j)) 3]
  omega_using []

/-- A three-bit window: `8 R + [k_j]Q`, for `R` before it, is `R` after it. -/
theorem wstep3 {C : Spec.Weierstrass.Curve} (hL : Law C) {Q : Point C} (hQ : onCurve C Q = true) (k j : Nat) :
    Spec.Weierstrass.add (d8 (mul (k >>> (3 * (j + 1))) Q)) (mul ((k >>> (3 * j)) % 8) Q) =
      mul (k >>> (3 * j)) Q := by
  obtain ek := shr_three k j
  simp only [d8, d2]
  generalize (k >>> (3 * j)) % 8 = a at ek ⊢
  rw [ek]
  generalize k >>> (3 * (j + 1)) = m
  obtain hX := hL.onCurve_mul hQ m
  obtain h2 := hL.onCurve_add hX hX
  obtain h4 := hL.onCurve_add h2 h2
  obtain h8 := hL.onCurve_add h4 h4
  obtain ⟨M, _, f, hf⟩ := hL.group
  apply hf.inj (hL.onCurve_add h8 (hL.onCurve_mul hQ _)) (hL.onCurve_mul hQ _)
  rw [hf.add h8 (hL.onCurve_mul hQ _), hf.add h4 h4, hf.add h2 h2, hf.add hX hX,
    hf.mul hQ, hf.mul hQ, hf.mul hQ]
  obtain hu : ((8 * m + a : Nat) : Int) = m + m + m + m + m + m + m + m + a := by omega_using []
  rw [hu]
  simp only [Lean.Grind.IntModule.add_zsmul]
  grind

theorem nib3_eq (k j : Nat) : (k >>> (3 * j)) % 8 = Window.bv (k.testBit (3 * j)) +
    2 * Window.bv (k.testBit (3 * j + 1)) + 4 * Window.bv (k.testBit (3 * j + 2)) := by
  have h0 := Window.bv_shift k (3 * j) 0
  simp only [Nat.add_zero] at h0
  rw [h0, Window.bv_shift k (3 * j) 1, Window.bv_shift k (3 * j) 2]
  simp only [Nat.reducePow, Nat.div_one]
  generalize k >>> (3 * j) = m
  omega_arith

theorem horner3_eq (b0 b1 b2 : Bool) :
    let x1 := BitVec.ofNat 64 (Window.bv b2) + BitVec.ofNat 64 (Window.bv b2) + BitVec.ofNat 64 (Window.bv b1)
    x1 + x1 + BitVec.ofNat 64 (Window.bv b0) =
      BitVec.ofNat 64 (Window.bv b0 + 2 * Window.bv b1 + 4 * Window.bv b2) := by
  cases b0 <;> cases b1 <;> cases b2 <;> rfl

/-- The window `k_j` of three bits into `r9`, for `j` in `r31`, from the
table of `k`'s bits. -/
theorem nibble3_ok (n9 : c.n ≤ 9) {nw : Nat} (hnw : 3 * nw ≤ 64 * c.n) {s : State} {base : Addr}
    (hw : WsReg s base) {k j : Nat} (hj : j < nw) (h31 : s.gpr .r31 = BitVec.ofNat 64 j)
    (ht : ∀ t < 64 * c.n, s.mem (off base (4096 + t)) = if k.testBit t then 1 else 0) :
    WP isa (.block (Cfg.nibble3 c)) s fun s' =>
      s'.gpr .r9 = BitVec.ofNat 64 ((k >>> (3 * j)) % 8) ∧ Kp [.r4, .r5, .r9] s s' ∧ s'.mem = s.mem := by
  have hs := hw.ws
  have h3 := hw.at3
  rw [Cfg.nibble3, show bitsAt c.n 0 = 4096 from rfl]
  obtain a₄ : s.gpr .r3 + (s.gpr .r31 <<< 1 + s.gpr .r31) = off base (3 * j) := by
    rw [h3, h31]
    simp only [off]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega_using []
  refine wp_step (exec_lsl (by decide)) ?_
  refine wp_step exec_add ?_
  refine wp_step exec_add ?_
  refine wp_step (lbz_ok (base := base) (size := 8192) (by repeat (first | exact hs | refine Ws.write ?_ _ _))
    (by simp only [At, write_gpr, ite_true, reduceCtorEq, ite_false]; exact a₄) (by decide)
    (by omega_using [hj, hnw, n9])) ?_
  refine wp_step exec_add ?_
  refine wp_step (lbz_ok (base := base) (size := 8192) (by repeat (first | exact hs | refine Ws.write ?_ _ _))
    (by simp only [At, write_gpr, ite_true, reduceCtorEq, ite_false]; exact a₄) (by decide)
    (by omega_using [hj, hnw, n9])) ?_
  refine wp_step exec_add ?_
  refine wp_step exec_add ?_
  refine wp_step (lbz_ok (base := base) (size := 8192) (by repeat (first | exact hs | refine Ws.write ?_ _ _))
    (by simp only [At, write_gpr, ite_true, reduceCtorEq, ite_false]; exact a₄) (by decide)
    (by omega_using [hj, hnw, n9])) ?_
  refine wp_step exec_add (WP.block_nil ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩)
  · simp only [write_gpr, write_mem, ite_true, reduceCtorEq, ite_false]
    rw [show 3 * j + (4096 + 2) = 4096 + (3 * j + 2) by omega_using [],
      show 3 * j + (4096 + 1) = 4096 + (3 * j + 1) by omega_using [],
      show 3 * j + 4096 = 4096 + 3 * j by omega_using [],
      ht _ (by omega_using [hj, hnw]), ht _ (by omega_using [hj, hnw]), ht _ (by omega_using [hj, hnw]),
      byte_bit, byte_bit, byte_bit, nib3_eq]
    exact horner3_eq _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, hr.1, hr.2.1, hr.2.2, ite_false]

/-! ## The arithmetic's kit: `a = -3`, or any `a` -/

variable (c) in
/-- What differs between the windows for `a = -3` and for any `a`: where
`b`'s constant is and what it is, the doubling and the addition, and the
programs built on them. -/
structure AKit where
  ok : CfgOk c
  /-- The slot of `b`'s constant, and the constant (`b`, or `3 b`). -/
  bs : Nat
  bK : Nat
  bs_cases : bs = 7 ∨ bs = 40
  /-- The addition and the Jacobian doubling. -/
  addF : RcbSlots → Pt → Pt → Pt → List FOp
  dblF : RcbSlots → Pt → Pt → List FOp
  dbl_ok : Law c.C → ∀ {base : Addr} {s : State} {p o : Pt}, RcbApart (Cfg.slots c bs) p p o →
    (∀ x ∈ rcbW (Cfg.slots c bs) o ++ rcbR (Cfg.slots c bs) p p, wS c.n x) →
    ∀ {V : List Nat} {E : Nat → Fe c.C}, Inv c.n base c.C.p (wS c.n) V E s →
    (∀ x ∈ rcbR (Cfg.slots c bs) p p, x ∈ V) → E σ[6] = Fin.ofNat c.C.p c.C.a →
    ∀ {P : Point c.C}, onCurve c.C P = true → InvJ c.C (E p.x) (E p.y) (E p.z) P →
    WP isa (fprog c.SP (dblF (Cfg.slots c bs) p o)) s fun s' =>
      KeepR c.n (fun x => x) base (rcbW (Cfg.slots c bs) o) s s' ∧
      ∃ E', Inv c.n base c.C.p (wS c.n) ([o.x, o.y, o.z] ++ V) E' s' ∧
        InvJ c.C (E' o.x) (E' o.y) (E' o.z) (d2 P) ∧ ∀ x, x ∉ rcbW (Cfg.slots c bs) o → E' x = E x
  add_ok : Law c.C → ∀ {base : Addr} {s : State}, WsReg s base → KC c bs bK base s → ∀ {p q o : Pt},
    RcbApart (Cfg.slots c bs) p q o →
    (∀ x ∈ rcbW (Cfg.slots c bs) o ++ rcbR (Cfg.slots c bs) p q, wS c.n x) →
    ∀ {P P' : Point c.C}, onCurve c.C P = true → onCurve c.C P' = true → PtOk c base s p P →
    PtOk c base s q P' →
    WP isa (fprog c.SP (addF (Cfg.slots c bs) p q o)) s fun s' =>
      Rk fnClob s s' ∧ Unch base (addW c o) s.mem s'.mem ∧ PtOk c base s' o (Spec.Weierstrass.add P P')
  /-- `R = 16 R` by four doublings, and `R = 8 R` by three. -/
  quad4P : Prog isa
  quad4_eq : quad4P = progs [fprog c.SP (toJ (Cfg.slots c bs) (Cfg.rPt c) (Cfg.zeroPt c) (Cfg.dPt c)),
    fprog c.SP (dblF (Cfg.slots c bs) (Cfg.dPt c) (Cfg.tPt c)),
    fprog c.SP (dblF (Cfg.slots c bs) (Cfg.tPt c) (Cfg.dPt c)),
    fprog c.SP (dblF (Cfg.slots c bs) (Cfg.dPt c) (Cfg.tPt c)),
    fprog c.SP (dblF (Cfg.slots c bs) (Cfg.tPt c) (Cfg.dPt c)),
    fprog c.SP (fromJ (Cfg.slots c bs) (Cfg.dPt c) (Cfg.zeroPt c) (Cfg.rPt c)),
    .block (c.nonzero (c.sl RZ) ++ [mov .r10 .r5] ++ sel c.n (c.sl RY) (c.sl ONEP) (c.sl RY))]
  quad3P : Prog isa
  quad3_eq : quad3P = progs [fprog c.SP (toJ (Cfg.slots c bs) (Cfg.rPt c) (Cfg.zeroPt c) (Cfg.dPt c)),
    fprog c.SP (dblF (Cfg.slots c bs) (Cfg.dPt c) (Cfg.tPt c)),
    fprog c.SP (dblF (Cfg.slots c bs) (Cfg.tPt c) (Cfg.dPt c)),
    fprog c.SP (dblF (Cfg.slots c bs) (Cfg.dPt c) (Cfg.tPt c)),
    fprog c.SP (fromJ (Cfg.slots c bs) (Cfg.tPt c) (Cfg.zeroPt c) (Cfg.rPt c)),
    .block (c.nonzero (c.sl RZ) ++ [mov .r10 .r5] ++ sel c.n (c.sl RY) (c.sl ONEP) (c.sl RY))]
  /-- The table's additions. -/
  addsP : Nat → Prog isa
  adds_zero : addsP 0 = .block []
  adds_succ : ∀ e, addsP (e + 1) = .seq (addsP e) (.seq
    (fprog c.SP (addF (Cfg.slots c bs) (Cfg.dPt c) (gPt c) (Cfg.tPt c)))
    (.block (Cfg.copyPt c (Cfg.entry c (e + 2)) (Cfg.tPt c) ++ Cfg.copyPt c (Cfg.dPt c) (Cfg.tPt c))))

/-- The kit of a curve with `a = -3`: `rcb3` and `dblJ`, with `b` at ECDH's
slot (`BPs`, 40). -/
def AKit.am3 (h : CfgOk c) (ha : AM3 c.C) : AKit c where
  ok := h
  bs := 40
  bK := c.C.b
  bs_cases := .inr rfl
  addF := rcb3
  dblF := dblJ
  dbl_ok := dblStep3_ok h ha
  add_ok := addPt3_ok h ha
  quad4P := Cfg.quad c 40
  quad4_eq := rfl
  quad3P := Cfg.trip c 40
  quad3_eq := rfl
  addsP := Cfg.adds c Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY 40
  adds_zero := rfl
  adds_succ := fun _ => rfl

/-- The kit of a curve with any `a`: `rcb` and `dblJa`, with `3 b` at the
signature's slot (`B3P`, 7). -/
def AKit.anyA (h : CfgOk c) : AKit c where
  ok := h
  bs := 7
  bK := 3 * c.C.b
  bs_cases := .inl rfl
  addF := rcb
  dblF := dblJa
  dbl_ok := dblStepA_ok h
  add_ok := addPtA_ok h
  quad4P := WindowA.Cfg.quad c 7
  quad4_eq := rfl
  quad3P := WindowA.Cfg.trip c 7
  quad3_eq := rfl
  addsP := WindowA.Cfg.adds c Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY 7
  adds_zero := rfl
  adds_succ := fun _ => rfl

/-- `b`'s slot is below `R`, or between the temporaries and the functions'
own working space. -/
theorem AKit.bs_far (A : AKit c) : σ[A.bs] + 8 * c.n ≤ σ[14] ∨
    (σ[29] ≤ σ[A.bs] ∧ σ[A.bs] + 8 * c.n ≤ 4096 - 64 * c.n) := by
  have n9 := n_le A.ok
  rcases A.bs_cases with e | e <;> rw [e] <;> omega_using [n9]

/-! ## `R = 16 R` and `R = 8 R` -/

/-- `R` into Jacobian coordinates in `D`, then three doublings (to `T`, back
to `D`, and to `T`): `8 P` in `T`, for `R` representing `P`, before what
follows. -/
theorem quadHead_ok (A : AKit c) (hL : Law c.C) {base : Addr} {s : State} (hw : WsReg s base)
    (hK : KC c A.bs A.bK base s) {P : Point c.C} (hP : onCurve c.C P = true) (hR : PtOk c base s (Cfg.rPt c) P)
    {rest : Prog isa} {Qp : State → Prop}
    (hrest : ∀ (s₄ : State) (V : List Nat) (E : Nat → Fe c.C), KeepR c.n (fun x => x) base (quadWl c) s s₄ →
      Inv c.n base c.C.p (wS c.n) V E s₄ →
      (∀ x ∈ [σ[6], σ[A.bs], σ[3], σ[17], σ[18], σ[19], σ[20], σ[21], σ[22]], x ∈ V) →
      E σ[6] = Fin.ofNat c.C.p c.C.a → E σ[3] = 0 → InvJ c.C (E σ[20]) (E σ[21]) (E σ[22]) (d8 P) →
      WP isa rest s₄ Qp) :
    WP isa (.seq (fprog c.SP (toJ (Cfg.slots c A.bs) (Cfg.rPt c) (Cfg.zeroPt c) (Cfg.dPt c)))
      (.seq (fprog c.SP (A.dblF (Cfg.slots c A.bs) (Cfg.dPt c) (Cfg.tPt c)))
      (.seq (fprog c.SP (A.dblF (Cfg.slots c A.bs) (Cfg.tPt c) (Cfg.dPt c)))
      (.seq (fprog c.SP (A.dblF (Cfg.slots c A.bs) (Cfg.dPt c) (Cfg.tPt c))) rest)))) s Qp := by
  have n1 := A.ok.n0
  have hb := A.bs_cases
  obtain hp0 : 0 < c.C.p := p0 c
  -- The start: `a`, `b`, zero and `R`.
  obtain hI : Inv c.n base c.C.p (wS c.n) [σ[6], σ[A.bs], σ[3], σ[14], σ[15], σ[16]]
      (fun x => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base x c.n)) s := by
    refine ⟨hw, fun x hx => ?_, fun x hx => ?_, fun x _ => rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [wS_sl (by decide), wS_sl (by omega_using [hb]), wS_sl (by decide), wS_sl (by decide),
        wS_sl (by decide), wS_sl (by decide)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact lt_of_eq_of_lt hK.ap (Nat.mod_lt _ hp0)
      · exact lt_of_eq_of_lt hK.bp (Nat.mod_lt _ hp0)
      · exact lt_of_eq_of_lt hK.zero hp0
      exacts [hR.x, hR.y, hR.z]
  obtain e0 : toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base σ[3] c.n) = 0 := by
    rw [show wordsVal s.mem base σ[3] c.n = 0 from hK.zero]; exact toM_zero _ _
  obtain a0 : toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base σ[6] c.n) = Fin.ofNat c.C.p c.C.a := by
    rw [hK.ap, toM_mont (unitP A.ok)]
  -- To Jacobian coordinates.
  refine WP.seq (WP.mono (toJStep_ok A.ok hL hb hI (by wk_dec) hR.rep e0) fun s₁ ⟨k₁, E₁, I₁, J₁, p₁⟩ => ?_)
  obtain a1 : E₁ σ[6] = Fin.ofNat c.C.p c.C.a := by rw [p₁ _ (by wk_dec)]; exact a0
  -- Three doublings.
  refine WP.seq (WP.mono (A.dbl_ok hL (p := Cfg.dPt c) (o := Cfg.tPt c)
    (apart_rcb n1 hb (by decide) (by decide) (by decide)) (wS_rcb hb (by decide)) I₁ (by wk_dec) a1 hP J₁)
    fun s₂ ⟨k₂, E₂, I₂, J₂, p₂⟩ => ?_)
  obtain a2 : E₂ σ[6] = Fin.ofNat c.C.p c.C.a := by rw [p₂ _ (by wk_dec)]; exact a1
  refine WP.seq (WP.mono (A.dbl_ok hL (p := Cfg.tPt c) (o := Cfg.dPt c)
    (apart_rcb n1 hb (by decide) (by decide) (by decide)) (wS_rcb hb (by decide)) I₂ (by wk_dec) a2
    (hL.onCurve_add hP hP) J₂) fun s₃ ⟨k₃, E₃, I₃, J₃, p₃⟩ => ?_)
  obtain a3 : E₃ σ[6] = Fin.ofNat c.C.p c.C.a := by rw [p₃ _ (by wk_dec)]; exact a2
  obtain h4 := hL.onCurve_add (hL.onCurve_add hP hP) (hL.onCurve_add hP hP)
  refine WP.seq (WP.mono (A.dbl_ok hL (p := Cfg.dPt c) (o := Cfg.tPt c)
    (apart_rcb n1 hb (by decide) (by decide) (by decide)) (wS_rcb hb (by decide)) I₃ (by wk_dec) a3 h4 J₃)
    fun s₄ ⟨k₄, E₄, I₄, J₄, p₄⟩ => ?_)
  obtain a4 : E₄ σ[6] = Fin.ofNat c.C.p c.C.a := by rw [p₄ _ (by wk_dec)]; exact a3
  obtain z₄ : E₄ σ[3] = 0 := by
    rw [p₄ _ (by wk_dec), p₃ _ (by wk_dec), p₂ _ (by wk_dec), p₁ _ (by wk_dec)]; exact e0
  exact hrest s₄ _ E₄ (((k₁.mono (by wk_dec)).trans (k₂.mono (by wk_dec))).trans ((k₃.mono (by wk_dec)).trans
    (k₄.mono (by wk_dec)))) I₄ (by wk_dec) a4 z₄ J₄

/-- From Jacobian coordinates in `jp` (`D` or `T`) back to projective ones
in `R`, with `Y = 1` where `Z` is zero (the mask of `Z ≠ 0`, then the
selection): a representative again. -/
theorem quadTail_ok (A : AKit c) (hL : Law c.C) {base : Addr} {s s₅ : State} (hK : KC c A.bs A.bK base s)
    {jp : Pt} (hA : RcbApart (Cfg.slots c A.bs) jp (Cfg.zeroPt c) (Cfg.rPt c))
    (hsl : ∀ x ∈ rcbW (Cfg.slots c A.bs) (Cfg.rPt c) ++ rcbR (Cfg.slots c A.bs) jp (Cfg.zeroPt c), wS c.n x)
    {V : List Nat} {E₅ : Nat → Fe c.C} (I₅ : Inv c.n base c.C.p (wS c.n) V E₅ s₅)
    (hV : ∀ x ∈ rcbR (Cfg.slots c A.bs) jp (Cfg.zeroPt c), x ∈ V) (z₅ : E₅ σ[3] = 0)
    (KK₅ : KeepR c.n (fun x => x) base (quadWl c) s s₅) {P : Point c.C}
    (J₅ : InvJ c.C (E₅ jp.x) (E₅ jp.y) (E₅ jp.z) P) :
    WP isa (.seq (fprog c.SP (fromJ (Cfg.slots c A.bs) jp (Cfg.zeroPt c) (Cfg.rPt c)))
      (.block (c.nonzero (c.sl RZ) ++ [mov .r10 .r5] ++ sel c.n (c.sl RY) (c.sl ONEP) (c.sl RY)))) s₅ fun s' =>
      Rk fnClob s s' ∧ Unch base (quadW c) s.mem s'.mem ∧ PtOk c base s' (Cfg.rPt c) P := by
  have n1 := A.ok.n0
  have n9 := n_le A.ok
  obtain hp0 : 0 < c.C.p := p0 c
  refine WP.seq (WP.mono (fromJStep_ok A.ok hA hsl I₅ hV) fun s₆ ⟨k₆, E₆, I₆, v₆, p₆⟩ => ?_)
  obtain ⟨vx, vyz⟩ := Prod.mk.inj v₆
  obtain ⟨vy, vz⟩ := Prod.mk.inj vyz
  obtain vx : E₆ σ[14] = E₅ jp.x * E₅ jp.z := vx
  obtain vy : E₆ σ[15] = E₅ jp.y + E₅ σ[3] := vy
  obtain vz : E₆ σ[16] = E₅ jp.z * E₅ jp.z * E₅ jp.z := vz
  rw [z₅, Lean.Grind.AddCommMonoid.add_zero] at vy
  have hw₆ := I₆.ws
  have hn₆ := hw₆.nowrap
  obtain ltx := I₆.lt σ[14] (by wk_dec)
  obtain lty := I₆.lt σ[15] (by wk_dec)
  obtain ltz := I₆.lt σ[16] (by wk_dec)
  obtain vx' : tmv c.C c.n base s₆ σ[14] = E₆ σ[14] := I₆.val σ[14] (by wk_dec)
  obtain vy' : tmv c.C c.n base s₆ σ[15] = E₆ σ[15] := I₆.val σ[15] (by wk_dec)
  obtain vz' : tmv c.C c.n base s₆ σ[16] = E₆ σ[16] := I₆.val σ[16] (by wk_dec)
  obtain KK : KeepR c.n (fun x => x) base (quadWl c) s s₆ := KK₅.trans (k₆.mono (by wk_dec))
  obtain UK : Unch base (quadW c) s.mem s₆.mem :=
    Unch.cover (W := (quadWl c).map (fun w => (w, 8 * c.n)) ++ [(own c.n, 64 * c.n)]) KK.mem (by wk_dec)
  obtain onep₆ : wordsVal s₆.mem base σ[5] c.n = 2 ^ (64 * c.n) % c.C.p := by
    rw [UK.wordsVal (by wk_dec) (by omega_using [n9])]; exact hK.onep
  -- `Y = 1` where `Z = 0`: the mask of `Z ≠ 0`, then the selection.
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (nonzero_ok c hw₆.ws hw₆.at3 (a := σ[16]) (by omega_using [])
    (by omega_using [n1]) (by omega_using [n9])) fun s₇ ⟨g₇, k₇, m₇⟩ => ?_)
  rw [List.singleton_append]
  refine wp_step exec_logic ?_
  obtain hc : (s₇.write .r10 (s₇.gpr .r5 ||| s₇.gpr .r5)).gpr .r10 =
      if decide (wordsVal s₆.mem base σ[16] c.n ≠ 0) then BitVec.allOnes 64 else 0 := by
    simp only [write_gpr, ite_true, BitVec.or_self, g₇, mask64, decide_eq_true_eq]
  obtain hw₇ := (k₇.ws hw₆.ws).write .r10 (s₇.gpr .r5 ||| s₇.gpr .r5)
  refine WP.mono (sel_ok (decide (wordsVal s₆.mem base σ[16] c.n ≠ 0)) c.n hw₇ ((k₇.at hw₆.at3).write _) hc
    (o := σ[15]) (a := σ[5]) (b := σ[15]) (by omega_using []) (by omega_using []) (by omega_using [])
    (by omega_using [n9]) (by omega_using [n9]) (by omega_using [n9])
    (Or.inr (by omega_using [])) (Or.inl (Nat.le_refl _))) fun s₈ ⟨e₈, k₈, O₈⟩ => ?_
  simp only [write_mem] at e₈ O₈
  rw [m₇] at e₈ O₈
  obtain ex : wordsVal s₈.mem base σ[14] c.n = wordsVal s₆.mem base σ[14] c.n :=
    O₈.wordsVal (by omega_using []) (by omega_using [n9])
  obtain ez : wordsVal s₈.mem base σ[16] c.n = wordsVal s₆.mem base σ[16] c.n :=
    O₈.wordsVal (by omega_using []) (by omega_using [n9])
  obtain hZ : (wordsVal s₆.mem base σ[16] c.n ≠ 0) ↔ E₅ jp.z ≠ 0 := by
    rw [ne_eq, ne_eq, ← toM_eq_zero_iff (unitP A.ok) ltz]
    show ¬tmv c.C c.n base s₆ σ[16] = 0 ↔ _
    rw [vz', vz]
    exact not_congr ⟨fun h => Classical.byContradiction fun hz => cube_ne_zero hL hz h,
      fun h => by rw [h]; grind⟩
  obtain hrep := InvJ.out hL J₅
  obtain sub : ∀ r ∈ [Reg.r4, .r5], r ∈ fnClob := by decide
  obtain rk : Rk fnClob s s₈ := by
    refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
    · have h10 : r ≠ Reg.r10 := fun h => hr (h ▸ by decide)
      rw [k₈.gpr r (fun h => hr (sub r h)), write_gpr]
      simp only [h10, ↓reduceIte]
      rw [k₇.gpr r (fun h => hr (sub r h)), KK.gpr r hr]
    · rw [k₈.rd, write_rd, k₇.rd, KK.rd]
    · rw [k₈.wr, write_wr, k₇.wr, KK.wr]
    · rw [k₈.sp, write_sp, k₇.sp, KK.sp]
  refine ⟨rk, (UK.trans O₈.unch).cover (by wk_dec), ⟨?_, ?_, ?_, ?_⟩⟩
  · show Rep c.C (tmv c.C c.n base s₈ σ[14]) (tmv c.C c.n base s₈ σ[15]) (tmv c.C c.n base s₈ σ[16]) _
    simp only [tmv]
    rw [ex, ez]
    show Rep c.C (tmv c.C c.n base s₆ σ[14]) _ (tmv c.C c.n base s₆ σ[16]) _
    rw [vx', vz', vx, vz, e₈]
    by_cases h0 : E₅ jp.z = 0
    · have hc : decide (wordsVal s₆.mem base σ[16] c.n ≠ 0) = false :=
        decide_eq_false fun h => (hZ.mp h) h0
      rw [show (if E₅ jp.z = 0 then (1 : Fe c.C) else E₅ jp.y) = 1 from by simp [h0]] at hrep
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      rw [onep₆, toM_one (unitP A.ok)]
      exact hrep
    · have hc : decide (wordsVal s₆.mem base σ[16] c.n ≠ 0) = true := decide_eq_true (hZ.mpr h0)
      rw [show (if E₅ jp.z = 0 then (1 : Fe c.C) else E₅ jp.y) = E₅ jp.y from by simp [h0]] at hrep
      simp only [hc, ↓reduceIte]
      show Rep c.C _ (tmv c.C c.n base s₆ σ[15]) _ _
      rw [vy', vy]
      exact hrep
  · show wordsVal s₈.mem base σ[14] c.n < c.C.p
    rw [ex]; exact ltx
  · show wordsVal s₈.mem base σ[15] c.n < c.C.p
    rw [e₈]; split
    · exact lty
    · rw [onep₆]; exact Nat.mod_lt _ hp0
  · show wordsVal s₈.mem base σ[16] c.n < c.C.p
    rw [ez]; exact ltz

/-- `R = 16 R`, for `R` representing `P`: a fourth doubling, to `D`. -/
theorem quad4_ok (A : AKit c) (hL : Law c.C) {base : Addr} {s : State} (hw : WsReg s base)
    (hK : KC c A.bs A.bK base s) {P : Point c.C} (hP : onCurve c.C P = true) (hR : PtOk c base s (Cfg.rPt c) P) :
    WP isa A.quad4P s fun s' => Rk fnClob s s' ∧ Unch base (quadW c) s.mem s'.mem ∧
      PtOk c base s' (Cfg.rPt c) (d16 P) := by
  have n1 := A.ok.n0
  have hb := A.bs_cases
  rw [A.quad4_eq]
  simp only [progs]
  refine quadHead_ok A hL hw hK hP hR fun s₄ V E₄ KK₄ I₄ hm a4 z₄ J₄ => ?_
  obtain h4 := hL.onCurve_add (hL.onCurve_add hP hP) (hL.onCurve_add hP hP)
  refine WP.seq (WP.mono (A.dbl_ok hL (p := Cfg.tPt c) (o := Cfg.dPt c)
    (apart_rcb n1 hb (by decide) (by decide) (by decide)) (wS_rcb hb (by decide)) I₄
    (fun x hx => hm x ((by wk_dec : ∀ x ∈ rcbR (Cfg.slots c A.bs) (Cfg.tPt c) (Cfg.tPt c),
      x ∈ [σ[6], σ[A.bs], σ[3], σ[17], σ[18], σ[19], σ[20], σ[21], σ[22]]) x hx)) a4
    (hL.onCurve_add h4 h4) J₄) fun s₅ ⟨k₅, E₅, I₅, J₅, p₅⟩ => ?_)
  refine quadTail_ok A hL hK (jp := Cfg.dPt c) (apart_rcb n1 hb (by decide) (by decide) (by decide))
    (wS_rcb hb (by decide)) I₅
    (fun x hx => List.mem_append_right _ (hm x ((by wk_dec : ∀ x ∈ rcbR (Cfg.slots c A.bs) (Cfg.dPt c)
      (Cfg.zeroPt c), x ∈ [σ[6], σ[A.bs], σ[3], σ[17], σ[18], σ[19], σ[20], σ[21], σ[22]]) x hx)))
    (by rw [p₅ _ (by wk_dec)]; exact z₄) (KK₄.trans (k₅.mono (by wk_dec))) J₅

/-- `R = 8 R`, for `R` representing `P`. -/
theorem quad3_ok (A : AKit c) (hL : Law c.C) {base : Addr} {s : State} (hw : WsReg s base)
    (hK : KC c A.bs A.bK base s) {P : Point c.C} (hP : onCurve c.C P = true) (hR : PtOk c base s (Cfg.rPt c) P) :
    WP isa A.quad3P s fun s' => Rk fnClob s s' ∧ Unch base (quadW c) s.mem s'.mem ∧
      PtOk c base s' (Cfg.rPt c) (d8 P) := by
  have n1 := A.ok.n0
  have hb := A.bs_cases
  rw [A.quad3_eq]
  simp only [progs]
  refine quadHead_ok A hL hw hK hP hR fun s₄ V E₄ KK₄ I₄ hm a4 z₄ J₄ => ?_
  exact quadTail_ok A hL hK (jp := Cfg.tPt c) (apart_rcb n1 hb (by decide) (by decide) (by decide))
    (wS_rcb hb (by decide)) I₄
    (fun x hx => hm x ((by wk_dec : ∀ x ∈ rcbR (Cfg.slots c A.bs) (Cfg.tPt c) (Cfg.zeroPt c),
      x ∈ [σ[6], σ[A.bs], σ[3], σ[17], σ[18], σ[19], σ[20], σ[21], σ[22]]) x hx)) z₄ KK₄ J₄

/-! ## The windows' kit: four bits, or three -/

variable (c) in
/-- What differs between four-bit and three-bit windows, over the
arithmetic's kit: the window's bits `wb`, the table's `E = 2^wb` entries
(which fit the working space: `tf`), the number of windows `nw`, the
multiple `dq` of a point that `quadP` computes, and the program `nibP` that
reads a window's bits. -/
structure Kit extends AKit c where
  wb : Nat
  E : Nat
  nw : Nat
  E_ge : 2 ≤ E
  E_le : E ≤ 16
  tf : τ + 24 * c.n * E ≤ 8192
  nw1 : 1 ≤ nw
  nw15 : nw < 2 ^ 15
  /-- `R = 2^wb R`. -/
  dq : Point c.C → Point c.C
  dq_on : Law c.C → ∀ {P : Point c.C}, onCurve c.C P = true → onCurve c.C (dq P) = true
  wstep : Law c.C → ∀ {Q : Point c.C}, onCurve c.C Q = true → ∀ k j : Nat,
    Spec.Weierstrass.add (dq (mul (k >>> (wb * (j + 1))) Q)) (mul ((k >>> (wb * j)) % E) Q) =
      mul (k >>> (wb * j)) Q
  quadP : Prog isa
  quad_ok : Law c.C → ∀ {base : Addr} {s : State}, WsReg s base → KC c bs bK base s → ∀ {P : Point c.C},
    onCurve c.C P = true → PtOk c base s (Cfg.rPt c) P →
    WP isa quadP s fun s' => Rk fnClob s s' ∧ Unch base (quadW c) s.mem s'.mem ∧
      PtOk c base s' (Cfg.rPt c) (dq P)
  /-- The window `k_j` into `r9`, for `j` in `r31`. -/
  nibP : List Instr
  nib_ok : ∀ {s : State} {base : Addr}, WsReg s base → ∀ {k j : Nat}, j < nw →
    s.gpr .r31 = BitVec.ofNat 64 j → Bits c base s k →
    WP isa (.block nibP) s fun s' =>
      s'.gpr .r9 = BitVec.ofNat 64 ((k >>> (wb * j)) % E) ∧ Kp [.r4, .r5, .r9] s s' ∧ s'.mem = s.mem

/-- Four-bit windows, for at most seven words: sixteen entries, `16 n`
windows of four doublings. -/
def Kit.w4 (A : AKit c) (n7 : c.n ≤ 7) : Kit c where
  toAKit := A
  wb := 4
  E := 16
  nw := Cfg.windows c
  E_ge := by decide
  E_le := by decide
  tf := by omega_using [n7]
  nw1 := by have := A.ok.n0; show 1 ≤ 16 * c.n; omega_using [this]
  nw15 := by show 16 * c.n < 2 ^ 15; omega_using [n7]
  dq := d16
  dq_on := fun hL _ hP => hL.onCurve_add (hL.onCurve_add (hL.onCurve_add (hL.onCurve_add hP hP)
    (hL.onCurve_add hP hP)) (hL.onCurve_add (hL.onCurve_add hP hP) (hL.onCurve_add hP hP)))
    (hL.onCurve_add (hL.onCurve_add (hL.onCurve_add hP hP) (hL.onCurve_add hP hP))
    (hL.onCurve_add (hL.onCurve_add hP hP) (hL.onCurve_add hP hP)))
  wstep := fun hL _ hQ k j => Window.wstep hL hQ k j
  quadP := A.quad4P
  quad_ok := quad4_ok A
  nibP := Cfg.nibble c
  nib_ok := nibble_ok (n_le A.ok) (nw := Cfg.windows c) (by show 4 * (16 * c.n) ≤ 64 * c.n; omega_using [])

/-- Three-bit windows: eight entries, `nw` windows of three doublings, of
bits within the table of bits. -/
def Kit.w3 (A : AKit c) (nw : Nat) (h1 : 1 ≤ nw) (h3 : 3 * nw ≤ 64 * c.n) : Kit c where
  toAKit := A
  wb := 3
  E := 8
  nw := nw
  E_ge := by decide
  E_le := by decide
  tf := by have := n_le A.ok; omega_using [this]
  nw1 := h1
  nw15 := by have := n_le A.ok; omega_using [this, h3]
  dq := d8
  dq_on := fun hL _ hP => hL.onCurve_add (hL.onCurve_add (hL.onCurve_add hP hP) (hL.onCurve_add hP hP))
    (hL.onCurve_add (hL.onCurve_add hP hP) (hL.onCurve_add hP hP))
  wstep := fun hL _ hQ k j => wstep3 hL hQ k j
  quadP := A.quad3P
  quad_ok := quad3_ok A
  nibP := Cfg.nibble3 c
  nib_ok := nibble3_ok (n_le A.ok) h3

/-- The table: `O`, `P`, and `[e]P` for `e = 2 … E - 1`. -/
def Kit.buildP (K : Kit c) : Prog isa :=
  .seq (.block (Cfg.copyPt c (Cfg.entry c 0) (c.pt ZERO ONEP ZERO) ++ Cfg.copyPt c (Cfg.entry c 1) (gPt c) ++
    Cfg.copyPt c (Cfg.dPt c) (gPt c))) (K.addsP (K.E - 2))

/-- Entry `k_j` to `D`: the window's bits, then the entries scanned. -/
def Kit.selP (K : Kit c) : List Instr := K.nibP ++ (List.range K.E).flatMap (Cfg.scanEntry c)

/-- One window: `r31 -= 1`, `R = 2^wb R`, the entry `D` of the window's
bits, and `R = R + D` (through `T`). -/
def Kit.stepP (K : Kit c) : Prog isa :=
  .seq (.block [decCounter]) (.seq K.quadP (.seq (.block K.selP) (.seq
    (fprog c.SP (K.addF (Cfg.slots c K.bs) (Cfg.rPt c) (Cfg.dPt c) (Cfg.tPt c)))
    (.block (Cfg.copyPt c (Cfg.rPt c) (Cfg.tPt c))))))

/-- `R = [k]P`: the table, `R = O`, then the windows. -/
def Kit.mulP (K : Kit c) : Prog isa :=
  .seq K.buildP (.seq (.block (Cfg.copyPt c (Cfg.rPt c) (c.pt ZERO ONEP ZERO) ++ [.li .r31 K.nw]))
    (.loop K.stepP more))

/-! ## The table -/

/-- What the table's construction reads and keeps: the constants and `P`. -/
structure BPre (A : AKit c) (base : Addr) (s : State) (Q : Point c.C) : Prop where
  ws : WsReg s base
  kc : KC c A.bs A.bK base s
  g : PtOk c base s (gPt c) Q
  on : onCurve c.C Q = true

theorem far_addsW (n9 : c.n ≤ 9) {E d : Nat}
    (h : d + 8 * c.n ≤ σ[17] ∨ (σ[29] ≤ d ∧ d + 8 * c.n ≤ 4096 - 64 * c.n)) :
    ∀ w ∈ addsW c E, d + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ d := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> (simp only; omega_using [h, n9])

theorem BPre.of_eq {A : AKit c} {base : Addr} {s s' : State} {Q : Point c.C} (h : BPre A base s Q)
    (hw : WsReg s' base)
    (e : ∀ d, d + 8 * c.n ≤ σ[17] ∨ (σ[29] ≤ d ∧ d + 8 * c.n ≤ 4096 - 64 * c.n) →
      wordsVal s'.mem base d c.n = wordsVal s.mem base d c.n) :
    BPre A base s' Q := by
  have n9 := n_le A.ok
  have bf := A.bs_far
  exact ⟨hw, h.kc.of_eq fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> exact e _ (by omega_using [bf, n9]),
    h.g.of_eq (e σ[38] (by omega_using [n9])) (e σ[43] (by omega_using [n9])) (e σ[5] (by omega_using [n9])),
    h.on⟩

/-- The additions of `[e]Q` for `e = 2 … m + 1`, from `D = Q`: `D = [m + 1]Q`. -/
theorem adds_ok (K : Kit c) (hL : Law c.C) {base : Addr} {Q : Point c.C} :
    ∀ m ≤ K.E - 2, ∀ {s : State}, BPre K.toAKit base s Q → TabTo c base s Q 1 → PtOk c base s (Cfg.dPt c) Q →
      WP isa (K.addsP m) s fun s' =>
        Rk fnClob s s' ∧ Unch base (addsW c K.E) s.mem s'.mem ∧ BPre K.toAKit base s' Q ∧
          TabTo c base s' Q (m + 1) ∧
          PtOk c base s' (Cfg.dPt c) (mul (m + 1) Q)
  | 0, _, s, hp, hT, hD => by
    rw [K.adds_zero]
    exact WP.block_nil ⟨Rk.refl _ _, Unch.refl _ _ _, hp, hT, by rw [mul_one']; exact hD⟩
  | m + 1, hm, s, hp, hT, hD => by
    have n1 := K.ok.n0
    have n9 := n_le K.ok
    have tf := K.tf
    rw [K.adds_succ]
    refine WP.seq (WP.mono (adds_ok K hL m (by omega_using [hm]) hp hT hD) fun s₁ ⟨k₁, U₁, B₁, T₁, D₁⟩ => ?_)
    have hn := B₁.ws.nowrap
    -- `T = D + Q`.
    refine WP.seq (WP.mono (K.add_ok hL B₁.ws B₁.kc (p := Cfg.dPt c) (q := gPt c) (o := Cfg.tPt c)
      (apart_rcb n1 K.bs_cases (by decide) (by decide) (by decide)) (wS_rcb K.bs_cases (by decide))
      (hL.onCurve_mul B₁.on _) B₁.on D₁ B₁.g) fun s₂ ⟨k₂, U₂, p₂⟩ => ?_)
    rw [mul_succ' hL B₁.on] at p₂
    obtain hw₂ := B₁.ws.of_rk k₂
    -- Entry `m + 2` and `D`.
    obtain hm2 : m + 2 < K.E := by omega_using [hm]
    have em := ent_mono c.n hm2
    have ea := ent_al c.n (m + 2)
    refine WP.block_append (WP.mono (copyPt_ok hw₂ (o := ent c (m + 2)) (p := Cfg.tPt c)
      (by rw [ent_eq, tPt_eq]; simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro x (rfl | rfl | rfl | rfl | rfl | rfl) <;> omega_using [em, ea, tf, n9])
      (by rw [ent_eq]) (by rw [ent_eq]; simp only; omega_using [])
      (by rw [ent_eq, tPt_eq]; simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro x (rfl | rfl | rfl) <;> omega_using []))
      fun s₃ ⟨x₃, y₃, z₃, k₃, U₃⟩ => ?_)
    obtain hw₃ := hw₂.of_kp k₃
    refine WP.mono (copyPt_ok hw₃ (o := Cfg.dPt c) (p := Cfg.tPt c) (by wk_dec) (by wk_dec) (by wk_dec)
      (by wk_dec)) fun s₄ ⟨x₄, y₄, z₄, k₄, U₄⟩ => ?_
    obtain hw₄ := hw₃.of_kp k₄
    rw [ent_eq] at U₃ x₃ y₃ z₃
    rw [dPt_eq] at U₄ x₄ y₄ z₄
    rw [tPt_eq] at x₃ y₃ z₃ x₄ y₄ z₄
    simp only at U₃ U₄ x₃ y₃ z₃ x₄ y₄ z₄
    obtain U₃₄ : Unch base [(τ + 24 * c.n * (m + 2), 24 * c.n), (σ[17], 24 * c.n)] s₂.mem s₄.mem :=
      (U₃.trans U₄).cover fun w hw => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., by simp only; omega_using [], by simp only; omega_using []⟩
        · exact ⟨_, List.mem_cons_self .., by simp only; omega_using [], by simp only; omega_using []⟩
        · exact ⟨_, List.mem_cons_self .., by simp only; omega_using [], by simp only; omega_using []⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp only; omega_using [],
            by simp only; omega_using []⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp only; omega_using [],
            by simp only; omega_using []⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp only; omega_using [],
            by simp only; omega_using []⟩
    obtain hU : Unch base (addsW c K.E) s.mem s₄.mem := by
      refine ((U₁.trans U₂).trans U₃₄).cover fun w hw => ?_
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩
        · exact (by wk_dec : ∀ w ∈ addW c (Cfg.tPt c), ∃ w' ∈ addsW c K.E, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2) w hw
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact ⟨(τ, 24 * c.n * K.E), by simp, by simp only; omega_using [], by simp only; omega_using [em]⟩
        · exact ⟨(σ[17], 8 * c.n * 12), by simp, by simp only; omega_using [], by simp only; omega_using []⟩
    -- What each part leaves apart.
    obtain f₂ : ∀ d, d + 8 * c.n ≤ σ[20] ∨ (σ[29] ≤ d ∧ d + 8 * c.n ≤ 4096 - 64 * c.n) ∨ 4096 ≤ d →
        d + 8 * c.n ≤ 8192 → wordsVal s₂.mem base d c.n = wordsVal s₁.mem base d c.n := fun d h h' =>
      U₂.wordsVal (fun w hw => by
        have := (by wk_dec : ∀ w ∈ addW c (Cfg.tPt c),
          σ[20] ≤ w.1 ∧ w.1 + w.2 ≤ σ[29] ∨ w = (4096 - 64 * c.n, 64 * c.n)) w hw
        rcases this with h1 | rfl
        · omega_using [h, h1, n9]
        · simp only; omega_using [h, n9]) (by omega_using [h'])
    obtain f₄ : ∀ d, (d + 8 * c.n ≤ σ[17] ∨ σ[20] ≤ d) →
        (d + 8 * c.n ≤ τ + 24 * c.n * (m + 2) ∨ τ + 24 * c.n * (m + 2) + 24 * c.n ≤ d) →
        d + 8 * c.n ≤ 8192 → wordsVal s₄.mem base d c.n = wordsVal s₂.mem base d c.n := fun d h h2 h' =>
      U₃₄.wordsVal (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> (simp only; omega_using [h, h2])) (by omega_using [h'])
    obtain B₄ : BPre K.toAKit base s₄ Q := B₁.of_eq hw₄ fun d hd => by
      rw [f₄ d (by omega_using [hd]) (by omega_using [hd, n9]) (by omega_using [hd, n9]),
        f₂ d (by omega_using [hd]) (by omega_using [hd, n9])]
    refine ⟨(k₁.trans (k₂.mono (by decide))).trans ⟨fun r hr => ?_, ?_, ?_, ?_⟩, hU, B₄, fun e he => ?_, ?_⟩
    · rw [k₄.gpr r (fun h => hr (by simp only [List.mem_singleton] at h; subst h; decide)),
        k₃.gpr r (fun h => hr (by simp only [List.mem_singleton] at h; subst h; decide))]
    · rw [k₄.rd, k₃.rd]
    · rw [k₄.wr, k₃.wr]
    · rw [k₄.sp, k₃.sp]
    · rcases Nat.lt_or_ge e (m + 2) with h | h
      · have pe := T₁ e (by omega_using [h])
        have ee := ent_mono c.n h
        rw [ent_eq] at pe ⊢
        refine pe.of_eq ?_ ?_ ?_ <;> simp only
        · rw [f₄ _ (by omega_using []) (by omega_using [ee]) (by omega_using [ee, em, tf]),
            f₂ _ (by omega_using []) (by omega_using [ee, em, tf])]
        · rw [f₄ _ (by omega_using []) (by omega_using [ee]) (by omega_using [ee, em, tf]),
            f₂ _ (by omega_using []) (by omega_using [ee, em, tf])]
        · rw [f₄ _ (by omega_using []) (by omega_using [ee]) (by omega_using [ee, em, tf]),
            f₂ _ (by omega_using []) (by omega_using [ee, em, tf])]
      · obtain rfl : e = m + 2 := by omega_using [he, h]
        rw [ent_eq]
        refine p₂.move ?_ ?_ ?_ <;> rw [tPt_eq] <;> simp only
        · rw [U₄.wordsVal (by wk_dec) (by omega_using [em, tf]), x₃]
        · rw [U₄.wordsVal (by wk_dec) (by omega_using [em, tf]), y₃]
        · rw [U₄.wordsVal (by wk_dec) (by omega_using [em, tf]), z₃]
    · rw [show m + 1 + 1 = m + 2 by omega_using []]
      refine p₂.move ?_ ?_ ?_ <;> rw [dPt_eq, tPt_eq] <;> simp only
      · rw [x₄, ← U₃.wordsVal (by wk_dec) (by omega_using [n9])]
      · rw [y₄, ← U₃.wordsVal (by wk_dec) (by omega_using [n9])]
      · rw [z₄, ← U₃.wordsVal (by wk_dec) (by omega_using [n9])]

/-- The table of `[e]Q`, for `e < E`. -/
theorem build_ok (K : Kit c) (hL : Law c.C) {base : Addr} {Q : Point c.C} {s : State}
    (hp : BPre K.toAKit base s Q) :
    WP isa K.buildP s fun s' =>
      Rk fnClob s s' ∧ Unch base (addsW c K.E) s.mem s'.mem ∧ BPre K.toAKit base s' Q ∧
        TabTo c base s' Q (K.E - 1) := by
  have n9 := n_le K.ok
  have tf := K.tf
  have hE2 := K.E_ge
  have e2 := Nat.mul_le_mul_left (24 * c.n) hE2
  have hw := hp.ws
  have hn := hw.nowrap
  obtain hp0 : 0 < c.C.p := p0 c
  rw [Kit.buildP, List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (copyPt_ok hw (o := ent c 0) (p := c.pt ZERO ONEP ZERO) (by wk_dec)
    (by wk_dec) (by wk_dec) (by wk_dec)) fun s₁ ⟨x₁, y₁, z₁, k₁, U₁⟩ => ?_))
  obtain hw₁ := hw.of_kp k₁
  refine WP.block_append (WP.mono (copyPt_ok hw₁ (o := ent c 1) (p := gPt c) (by wk_dec) (by wk_dec)
    (by wk_dec) (by wk_dec)) fun s₂ ⟨x₂, y₂, z₂, k₂, U₂⟩ => ?_)
  obtain hw₂ := hw₁.of_kp k₂
  refine WP.mono (copyPt_ok hw₂ (o := Cfg.dPt c) (p := gPt c) (by wk_dec) (by wk_dec)
    (by wk_dec) (by wk_dec)) fun s₃ ⟨x₃, y₃, z₃, k₃, U₃⟩ => ?_
  obtain hw₃ := hw₂.of_kp k₃
  rw [ent_eq] at x₁ y₁ z₁ U₁ x₂ y₂ z₂ U₂
  rw [dPt_eq] at x₃ y₃ z₃ U₃
  rw [gPt_eq] at x₂ y₂ z₂ x₃ y₃ z₃
  rw [zop_eq] at x₁ y₁ z₁
  simp only at x₁ y₁ z₁ U₁ x₂ y₂ z₂ U₂ x₃ y₃ z₃ U₃
  obtain U₃' : Unch base (addsW c K.E) s.mem s₃.mem := ((U₁.trans U₂).trans U₃).cover (by wk_dec)
  obtain f : ∀ d, d + 8 * c.n ≤ σ[17] ∨ (σ[29] ≤ d ∧ d + 8 * c.n ≤ 4096 - 64 * c.n) →
      wordsVal s₃.mem base d c.n = wordsVal s.mem base d c.n :=
    fun d h => U₃'.wordsVal (far_addsW n9 h) (by omega_using [h, n9])
  obtain B₃ : BPre K.toAKit base s₃ Q := hp.of_eq hw₃ f
  have zv : wordsVal s.mem base σ[3] c.n = 0 := hp.kc.zero
  have ov : wordsVal s.mem base σ[5] c.n = 2 ^ (64 * c.n) % c.C.p := hp.kc.onep
  obtain g1 : ∀ d, d + 8 * c.n ≤ τ ∨ τ + 24 * c.n ≤ d → d + 8 * c.n ≤ 8192 →
      wordsVal s₁.mem base d c.n = wordsVal s.mem base d c.n := fun d h h' =>
    U₁.wordsVal (by wk_dec) (by omega_using [h'])
  obtain g2 : ∀ d, d + 8 * c.n ≤ τ + 24 * c.n ∨ τ + 24 * c.n * 2 ≤ d → d + 8 * c.n ≤ 8192 →
      wordsVal s₂.mem base d c.n = wordsVal s₁.mem base d c.n := fun d h h' =>
    U₂.wordsVal (by wk_dec) (by omega_using [h'])
  obtain g3 : ∀ d, d + 8 * c.n ≤ σ[17] ∨ σ[20] ≤ d → d + 8 * c.n ≤ 8192 →
      wordsVal s₃.mem base d c.n = wordsVal s₂.mem base d c.n := fun d h h' =>
    U₃.wordsVal (by wk_dec) (by omega_using [h'])
  obtain hT : TabTo c base s₃ Q 1 := by
    intro e he
    rcases Nat.lt_or_ge e 1 with h | h
    · obtain rfl : e = 0 := by omega_using [h]
      rw [mul_zero', ent_eq]
      obtain e0x : wordsVal s₃.mem base (τ + 24 * c.n * 0) c.n = 0 := by
        rw [g3 _ (by omega_using []) (by omega_using [n9, tf, e2]), g2 _ (by omega_using []) (by omega_using [n9, tf, e2]), x₁, zv]
      obtain e0y : wordsVal s₃.mem base (τ + 24 * c.n * 0 + 8 * c.n) c.n = 2 ^ (64 * c.n) % c.C.p := by
        rw [g3 _ (by omega_using []) (by omega_using [n9, tf, e2]), g2 _ (by omega_using []) (by omega_using [n9, tf, e2]), y₁, ov]
      obtain e0z : wordsVal s₃.mem base (τ + 24 * c.n * 0 + 16 * c.n) c.n = 0 := by
        rw [g3 _ (by omega_using []) (by omega_using [n9, tf, e2]), g2 _ (by omega_using []) (by omega_using [n9, tf, e2]), z₁, zv]
      refine ⟨?_, ?_, ?_, ?_⟩
      · show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₃.mem base (τ + 24 * c.n * 0) c.n))
          (toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₃.mem base (τ + 24 * c.n * 0 + 8 * c.n) c.n))
          (toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₃.mem base (τ + 24 * c.n * 0 + 16 * c.n) c.n)) _
        rw [e0x, e0y, e0z, toM_zero, toM_one (unitP K.ok)]
        exact rep_infinity' hL
      · show wordsVal s₃.mem base (τ + 24 * c.n * 0) c.n < c.C.p; rw [e0x]; exact hp0
      · show wordsVal s₃.mem base (τ + 24 * c.n * 0 + 8 * c.n) c.n < c.C.p; rw [e0y]; exact Nat.mod_lt _ hp0
      · show wordsVal s₃.mem base (τ + 24 * c.n * 0 + 16 * c.n) c.n < c.C.p; rw [e0z]; exact hp0
    · obtain rfl : e = 1 := by omega_using [he, h]
      rw [mul_one', ent_eq]
      refine hp.g.move ?_ ?_ ?_ <;> rw [gPt_eq] <;> simp only
      · rw [g3 _ (by omega_using []) (by omega_using [n9, tf, e2]), x₂, g1 _ (by omega_using [n9, tf, e2]) (by omega_using [n9, tf, e2])]
      · rw [g3 _ (by omega_using []) (by omega_using [n9, tf, e2]), y₂, g1 _ (by omega_using [n9, tf, e2]) (by omega_using [n9, tf, e2])]
      · rw [g3 _ (by omega_using []) (by omega_using [n9, tf, e2]), z₂, g1 _ (by omega_using [n9, tf, e2]) (by omega_using [n9, tf, e2])]
  obtain hD : PtOk c base s₃ (Cfg.dPt c) Q := by
    refine hp.g.move ?_ ?_ ?_ <;> rw [gPt_eq, dPt_eq] <;> simp only
    · rw [x₃, g2 _ (by omega_using [n9, tf, e2]) (by omega_using [n9, tf, e2]), g1 _ (by omega_using [n9, tf, e2]) (by omega_using [n9, tf, e2])]
    · rw [y₃, g2 _ (by omega_using [n9, tf, e2]) (by omega_using [n9, tf, e2]), g1 _ (by omega_using [n9, tf, e2]) (by omega_using [n9, tf, e2])]
    · rw [z₃, g2 _ (by omega_using [n9, tf, e2]) (by omega_using [n9, tf, e2]), g1 _ (by omega_using [n9, tf, e2]) (by omega_using [n9, tf, e2])]
  refine WP.mono (adds_ok K hL (K.E - 2) (Nat.le_refl _) B₃ hT hD) fun s₄ ⟨k₄, U₄, B₄, T₄, _⟩ => ?_
  rw [show K.E - 2 + 1 = K.E - 1 by omega_using [hE2]] at T₄
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, (U₃'.trans U₄).cover (by wk_dec), B₄, T₄⟩
  · have h4 : r ∉ [Reg.r4] := fun h => hr (by simp only [List.mem_singleton] at h; subst h; decide)
    rw [k₄.gpr r hr, k₃.gpr r h4, k₂.gpr r h4, k₁.gpr r h4]
  · rw [k₄.rd, k₃.rd, k₂.rd, k₁.rd]
  · rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr]
  · rw [k₄.sp, k₃.sp, k₂.sp, k₁.sp]

/-! ## The windows -/

/-- The window's entry `[k_j]Q` to `D`. -/
theorem select_ok (K : Kit c) {s : State} {base : Addr} (hw : WsReg s base) {k j : Nat} (hj : j < K.nw)
    (h31 : s.gpr .r31 = BitVec.ofNat 64 j) (ht : Bits c base s k)
    {Q : Point c.C} (hT : TabTo c base s Q (K.E - 1)) :
    WP isa (.block K.selP) s fun s' =>
      PtOk c base s' (Cfg.dPt c) (mul ((k >>> (K.wb * j)) % K.E) Q) ∧ Kp [.r4, .r5, .r9, .r10] s s' ∧
        Unch base [(σ[17], 24 * c.n)] s.mem s'.mem := by
  have hE2 := K.E_ge
  rw [Kit.selP]
  refine WP.block_append (WP.mono (K.nib_ok hw hj h31 ht) fun s₁ ⟨v₁, k₁, m₁⟩ => ?_)
  obtain ha : (k >>> (K.wb * j)) % K.E < K.E := Nat.mod_lt _ (by omega_using [hE2])
  refine WP.mono (scans_ok (n_le K.ok) K.tf K.E_le ha K.E (Nat.le_refl _) (hw.of_kp k₁) v₁)
    fun s₂ ⟨v₂, k₂, U₂⟩ => ⟨?_, (k₁.mono (by decide)).trans (k₂.mono (by decide)), by rw [← m₁]; exact U₂⟩
  obtain pe := hT ((k >>> (K.wb * j)) % K.E) (by omega_using [ha])
  rw [m₁] at v₂
  exact pe.move (v₂ ha 0 (by decide)) (v₂ ha 1 (by decide)) (v₂ ha 2 (by decide))

/-- What the windows read and keep, from `s₀`. -/
structure WFix (K : Kit c) (base : Addr) (s₀ : State) (Q : Point c.C) (k : Nat) : Prop where
  kc : KC c K.bs K.bK base s₀
  tab : TabTo c base s₀ Q (K.E - 1)
  bits : Bits c base s₀ k
  q : onCurve c.C Q = true

/-- The loop's invariant at `r31 = j`: `R` represents `[k >>> wb j]Q`. -/
structure WInv (K : Kit c) (base : Addr) (s₀ s : State) (Q : Point c.C) (k j : Nat) : Prop where
  ws : WsReg s base
  ctr : s.gpr .r31 = BitVec.ofNat 64 j
  keep : Rk powClob s₀ s
  unch : Unch base (stepW c) s₀.mem s.mem
  rep : PtOk c base s (Cfg.rPt c) (mul (k >>> (K.wb * j)) Q)

theorem far_stepW (n9 : c.n ≤ 9) {d : Nat}
    (h : d + 8 * c.n ≤ σ[14] ∨ (σ[29] ≤ d ∧ d + 8 * c.n ≤ 4096 - 64 * c.n) ∨ 4096 ≤ d) :
    ∀ w ∈ stepW c, d + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ d := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> (simp only; omega_using [h, n9])

/-- A window. -/
theorem step_ok (K : Kit c) (hL : Law c.C) {base : Addr} {s₀ : State} {Q : Point c.C} {k : Nat}
    (hP : WFix K base s₀ Q k) {j : Nat} (hj1 : 1 ≤ j) (hj : j ≤ K.nw) {s : State}
    (hI : WInv K base s₀ s Q k j) :
    WP isa K.stepP s fun s' => WInv K base s₀ s' Q k (j - 1) := by
  have n1 := K.ok.n0
  have n9 := n_le K.ok
  have tf := K.tf
  have hE2 := K.E_ge
  have bf := K.bs_far
  have hn := hI.ws.nowrap
  obtain uS : ∀ d, d + 8 * c.n ≤ σ[14] ∨ (σ[29] ≤ d ∧ d + 8 * c.n ≤ 4096 - 64 * c.n) ∨ 4096 ≤ d →
      d + 8 * c.n ≤ 8192 → wordsVal s.mem base d c.n = wordsVal s₀.mem base d c.n := fun d h h' =>
    hI.unch.wordsVal (far_stepW n9 h) (by omega_using [h'])
  rw [Kit.stepP]
  refine WP.seq (wp_decCounter hj1 hI.ctr (WP.block_nil ?_))
  generalize hs₁ : s.write .r31 (BitVec.ofNat 64 (j - 1)) = s₁
  obtain k₁ : Kp [.r31] s s₁ := hs₁ ▸ Kp.write _ _ (by decide)
  obtain c₁ : s₁.gpr .r31 = BitVec.ofNat 64 (j - 1) := by rw [← hs₁, write_gpr]; simp
  obtain m₁ : s₁.mem = s.mem := by rw [← hs₁]; rfl
  obtain hw₁ := hI.ws.of_kp k₁
  obtain hK₁ : KC c K.bs K.bK base s₁ := hP.kc.of_eq fun d hd => by
    rw [m₁]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> exact uS _ (by omega_using [bf, n9]) (by omega_using [bf, n9])
  obtain pR₁ : PtOk c base s₁ (Cfg.rPt c) (mul (k >>> (K.wb * j)) Q) := hI.rep.of_eq (by rw [m₁]) (by rw [m₁]) (by rw [m₁])
  obtain hX := hL.onCurve_mul hP.q (k >>> (K.wb * j))
  obtain h16 := K.dq_on hL hX
  obtain hE := hL.onCurve_mul hP.q ((k >>> (K.wb * (j - 1))) % K.E)
  -- `R = 2^wb R`.
  refine WP.seq (WP.mono (K.quad_ok hL hw₁ hK₁ hX pR₁) fun s₂ ⟨K₂, U₂, pR₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rk K₂
  obtain u₂ : ∀ d, d + 8 * c.n ≤ σ[14] ∨ (σ[29] ≤ d ∧ d + 8 * c.n ≤ 4096 - 64 * c.n) ∨ 4096 ≤ d →
      d + 8 * c.n ≤ 8192 → wordsVal s₂.mem base d c.n = wordsVal s₀.mem base d c.n := fun d h h' => by
    rw [U₂.wordsVal (far_stepW n9 h) (by omega_using [h']), m₁]; exact uS d h h'
  obtain hT₂ : TabTo c base s₂ Q (K.E - 1) :=
    hP.tab.of_eq (E := K.E) (fun d h1 h2 => u₂ d (by omega_using [h1]) (by omega_using [h2, tf]))
      (by omega_using [hE2])
  obtain hBs : Bits c base s k := hP.bits.of_unch n9 hI.unch (by wk_dec)
  obtain hB₁ : Bits c base s₁ k := fun t ht => by rw [m₁]; exact hBs t ht
  obtain hB₂ : Bits c base s₂ k := hB₁.of_unch n9 U₂ (by wk_dec)
  -- The entry.
  refine WP.seq (WP.mono (select_ok K hw₂ (j := j - 1) (by omega_using [hj, hj1])
    (by rw [K₂.gpr _ (by decide)]; exact c₁) hB₂ hT₂) fun s₃ ⟨pE, k₃, U₃⟩ => ?_)
  obtain hw₃ := hw₂.of_kp k₃
  obtain pR₃ : PtOk c base s₃ (Cfg.rPt c) (K.dq (mul (k >>> (K.wb * j)) Q)) :=
    pR₂.of_eq (U₃.wordsVal (by wk_dec) (by wk_dec)) (U₃.wordsVal (by wk_dec) (by wk_dec))
      (U₃.wordsVal (by wk_dec) (by wk_dec))
  obtain hK₃ : KC c K.bs K.bK base s₃ := hP.kc.of_eq fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      exact (U₃.wordsVal (by wk_dec) (by omega_using [bf, n9])).trans
        (u₂ _ (by omega_using [bf, n9]) (by omega_using [bf, n9]))
  -- `T = R + D`.
  refine WP.seq (WP.mono (K.add_ok hL hw₃ hK₃ (p := Cfg.rPt c) (q := Cfg.dPt c) (o := Cfg.tPt c)
    (apart_rcb n1 K.bs_cases (by decide) (by decide) (by decide)) (wS_rcb K.bs_cases (by decide)) h16 hE pR₃ pE)
    fun s₄ ⟨K₄, U₄, pT⟩ => ?_)
  obtain hw₄ := hw₃.of_rk K₄
  -- `R = T`.
  refine WP.mono (copyPt_ok hw₄ (o := Cfg.rPt c) (p := Cfg.tPt c) (by wk_dec) (by wk_dec)
    (by wk_dec) (by wk_dec)) fun s₅ ⟨x₅, y₅, z₅, k₅, U₅⟩ => ?_
  refine ⟨hw₄.of_kp k₅, ?_, ?_, ?_, ?_⟩
  · rw [k₅.gpr _ (by decide), K₄.gpr _ (by decide), k₃.gpr _ (by decide), K₂.gpr _ (by decide), c₁]
  · exact ((((hI.keep.trans (rk_of_kp k₁)).trans (rk_mono K₂)).trans (rk_of_kp k₃)).trans (rk_mono K₄)).trans
      (rk_of_kp k₅)
  · have U₁ : Unch base [] s.mem s₁.mem := fun x _ => by rw [m₁]
    exact (((((hI.unch.trans U₁).trans U₂).trans U₃).trans U₄).trans U₅).cover (by wk_dec)
  · have e := K.wstep hL hP.q k (j - 1)
    rw [show j - 1 + 1 = j by omega_using [hj1]] at e
    rw [← e]
    exact pT.move x₅ y₅ z₅

/-- What `mul` reads: the constants, `Q` at the peer point's slots, and the
table of `k`'s bits. -/
structure MPre (K : Kit c) (base : Addr) (s : State) (Q : Point c.C) (k : Nat) : Prop where
  ws : WsReg s base
  kc : KC c K.bs K.bK base s
  g : PtOk c base s (gPt c) Q
  on : onCurve c.C Q = true
  bits : Bits c base s k
  lt : k < 2 ^ (K.wb * K.nw)

/-- `R = [k]Q`. -/
theorem mul_ok (K : Kit c) (hL : Law c.C) {base : Addr} {s : State} {Q : Point c.C} {k : Nat}
    (hp : MPre K base s Q k) :
    WP isa K.mulP s fun s' =>
      Rk powClob s s' ∧ Unch base (mulW c K.E) s.mem s'.mem ∧ PtOk c base s' (Cfg.rPt c) (mul k Q) := by
  have n9 := n_le K.ok
  have tf := K.tf
  have hE2 := K.E_ge
  have bf := K.bs_far
  have hn := hp.ws.nowrap
  obtain hp0 : 0 < c.C.p := p0 c
  rw [Kit.mulP]
  refine WP.seq (WP.mono (build_ok K hL ⟨hp.ws, hp.kc, hp.g, hp.on⟩) fun s₁ ⟨K₁, U₁, B₁, T₁⟩ => ?_)
  have hw₁ := B₁.ws
  refine WP.seq (WP.block_append (WP.mono (copyPt_ok hw₁ (o := Cfg.rPt c) (p := c.pt ZERO ONEP ZERO)
    (by wk_dec) (by wk_dec) (by wk_dec) (by wk_dec)) fun s₂ ⟨x₂, y₂, z₂, r₂, U₂⟩ => ?_))
  obtain hw₂ := hw₁.of_kp r₂
  refine wp_step (exec_li (imm := K.nw) K.nw15) (WP.block_nil ?_)
  generalize hs₃ : s₂.write .r31 (BitVec.ofNat 64 K.nw) = s₃
  obtain ku₃ : Kp [.r31] s₂ s₃ := hs₃ ▸ Kp.write _ _ (by decide)
  obtain m₃ : s₃.mem = s₂.mem := by rw [← hs₃]; rfl
  obtain c₃ : s₃.gpr .r31 = BitVec.ofNat 64 K.nw := by rw [← hs₃, write_gpr]; simp
  obtain hw₃ : WsReg s₃ base := hw₂.of_kp ku₃
  obtain U₃ : Unch base [(σ[14], 24 * c.n)] s₁.mem s₃.mem := by rw [m₃]; exact U₂.cover (by wk_dec)
  obtain k₃ : ∀ d, d + 8 * c.n ≤ σ[14] ∨ σ[17] ≤ d → d + 8 * c.n ≤ 8192 →
      wordsVal s₃.mem base d c.n = wordsVal s₁.mem base d c.n :=
    fun d h h' => U₃.wordsVal (by wk_dec) (by omega_using [h'])
  obtain hP : WFix K base s₃ Q k :=
    ⟨B₁.kc.of_eq fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> exact k₃ _ (by omega_using [bf, n9]) (by omega_using [bf, n9]),
     T₁.of_eq (E := K.E) (fun d h1 h2 => k₃ d (by omega_using [h1]) (by omega_using [h2, tf]))
       (by omega_using [hE2]),
     (hp.bits.of_unch n9 U₁ (by wk_dec)).of_unch n9 U₃ (by wk_dec), hp.on⟩
  have zv : wordsVal s₁.mem base σ[3] c.n = 0 := B₁.kc.zero
  have ov : wordsVal s₁.mem base σ[5] c.n = 2 ^ (64 * c.n) % c.C.p := B₁.kc.onep
  rw [rPt_eq, zop_eq] at x₂ y₂ z₂
  obtain rx : wordsVal s₃.mem base σ[14] c.n = 0 := by rw [m₃]; exact x₂.trans zv
  obtain ry : wordsVal s₃.mem base σ[15] c.n = 2 ^ (64 * c.n) % c.C.p := by rw [m₃]; exact y₂.trans ov
  obtain rz : wordsVal s₃.mem base σ[16] c.n = 0 := by rw [m₃]; exact z₂.trans zv
  obtain hI : WInv K base s₃ s₃ Q k K.nw := by
    refine ⟨hw₃, c₃, Rk.refl _ _, Unch.refl _ _ _, ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [mul_top _ hp.lt]
      show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₃.mem base σ[14] c.n))
        (toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₃.mem base σ[15] c.n))
        (toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₃.mem base σ[16] c.n)) _
      rw [rx, ry, rz, toM_zero, toM_one (unitP K.ok)]
      exact rep_infinity' hL
    · show wordsVal _ _ σ[14] c.n < _; rw [rx]; exact hp0
    · show wordsVal _ _ σ[15] c.n < _; rw [ry]; exact Nat.mod_lt _ hp0
    · show wordsVal _ _ σ[16] c.n < _; rw [rz]; exact hp0
  refine countLoop_ok (Inv := fun j s' => WInv K base s₃ s' Q k j) (n := K.nw) (fun j s' hi => hi.ctr)
    (fun j s' h1 h2 hi => step_ok K hL hP h1 h2 hi) (fun s' hi => ?_) K.nw1
    (by have := K.nw15; omega_using [this]) hI
  refine ⟨((rk_mono K₁).trans (rk_of_kp ((r₂.mono (rs' := [.r4, .r31]) (by decide)).trans
    (ku₃.mono (by decide))))).trans hi.keep, ((U₁.trans U₃).trans hi.unch).cover (by wk_dec), ?_⟩
  obtain e : mul (k >>> (K.wb * 0)) Q = mul k Q := by rw [Nat.mul_zero, Nat.shiftRight_zero]
  rw [← e]
  exact hi.rep

end VG.Proof.Ecdsa.PPC64LE.WAll
