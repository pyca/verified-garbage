module

import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlKem.EkCheck
public import VerifiedGarbage.Impl.MlKem.AArch64.Encode
public import VerifiedGarbage.Spec.MlKem.Contract
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecLanes
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecInput
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.MlKem.EkCheck
meta import VerifiedGarbage.Impl.MlKem.AArch64.Encode
meta import VerifiedGarbage.Spec.MlKem.Contract
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.MlKem.AArch64.Wp
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecLanes
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecInput
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecLoop
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd64
meta import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-!
# ML-KEM on AArch64: `vg_mlkem768_check_ek` and `vg_mlkem1024_check_ek`

For a parameter set `p` of rank `k ≤ 4` (the instances are at the end of this
file). Word `e` of the low and high fields of group `g` of 12 bytes is field 0
and 1 of the group of 3 bytes `4 g + e` (`low_lanes`, `high_lanes`); word `e`
of `v19` is all ones exactly when one of them, in a group so far, is at least
`q` (`Inv`), and their sum is 0 exactly when the key passes the check
(`ekCheck_iff`).
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- AArch64 contract for `check_ek(ek = x0) -> w0` of the parameter set `p`:
returns 1 if the `384k + 32` bytes at `ek` pass the encapsulation key check,
and 0 otherwise. The code may read `ek`. -/
def checkEkAArch64 (p : Params) : Contract AArch64.isa where
  pre s := s.rd = [⟨s.gpr .x0, p.ekLen⟩] ∧ s.wr = []
  post s s' := (s'.gpr .x0).setWidth 32 =
    if ekCheck p (bytesAt s.mem (s.gpr .x0) p.ekLen) then 1 else 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.CheckEk

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Codec16
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.MlKem.AArch64.Codec16 (maskVec)


/-- The words at least `q` of `y`, all ones, and the others 0 (`cmhs` with `q`). -/
def geq (y : BitVec 128) : BitVec 128 :=
  VArr.s4.map2 (fun w a b => if VCmpOp.hs.test a b then BitVec.allOnes w else 0) y qvec

theorem ck_math_ok (s : State) (h16 : s.v .v16 = decMask) (h17 : s.v .v17 = mask12) (h18 : s.v .v18 = qvec) :
    WP isa (.block ckMath) s fun t =>
      t.v .v19 = s.v .v19 ||| geq (low (ofVDwords (s.gpr .x9) (s.gpr .x10))) |||
        geq (high (ofVDwords (s.gpr .x9) (s.gpr .x10))) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∀ r, r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v19 → t.v r = s.v r) := by
  unfold ckMath
  rrun [h16, h17, h18, VG.AArch64.setLane_pair_hi, VShiftOp.eval, low, high, tbl, geq, RegUpd.sp_setV]
  refine ⟨by rfl, ?_⟩
  intro r h0 h1 h2 h3 h19
  simp only [h0, h1, h2, h3, h19, ite_false]


theorem vword_geq (y : BitVec 128) {e : Nat} (he : e < 4) :
    vword (geq y) e = if (vword y e).toNat < q then 0 else BitVec.allOnes 32 := by
  rw [geq, vword_map2 _ _ _ he, qvec, vword_dup_s4 _ he]
  simp only [VCmpOp.test, ge_iff_le, show (3329 : BitVec 32).toNat = q from rfl]
  by_cases h : (vword y e).toNat < q
  · rw [decide_eq_false (Nat.not_le.mpr h)]; simp [h]
  · rw [decide_eq_true (Nat.le_of_not_lt h)]; simp [h]

/-- The fields of group `g` of 3 bytes of the key `B` are less than `q`. -/
abbrev good (B : List Byte) (t : Nat) : Prop := field0 B t < q ∧ field1 B t < q

/-- Word `e` of `v19` after `k` groups of 12 bytes. -/
abbrev accW (B : List Byte) (k e : Nat) : BitVec 32 :=
  if ∀ g < k, good B (4 * g + e) then 0 else BitVec.allOnes 32

section
variable (p : Params) (s₀ : State)
abbrev eP : Addr := s₀.gpr .x0
abbrev B : List Byte := bytesAt s₀.mem (eP s₀) p.ekLen
end

/-- After `k` groups of 12 bytes. -/
structure Inv (p : Params) (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = s₀.mem
  x0 : s.gpr .x0 = eP s₀ + BitVec.ofNat 64 (12 * k)
  x11 : (s.gpr .x11).toNat = 32 * p.k - k
  mask : s.v .v16 = decMask
  bits : s.v .v17 = mask12
  q : s.v .v18 = qvec
  acc : ∀ e < 4, vword (s.v .v19) e = accW (B p s₀) k e

theorem acc_step (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R] :
    ((if P then 0 else BitVec.allOnes 32) ||| (if Q then 0 else BitVec.allOnes 32) |||
      (if R then 0 else BitVec.allOnes 32) : BitVec 32) = if P ∧ Q ∧ R then 0 else BitVec.allOnes 32 := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP, hQ, hR]

variable {p : Params}

theorem step {s₀ : State} (hp : (checkEkAArch64 p).pre s₀) (hk4 : p.k ≤ 4) {k : Nat} (hk : k < 32 * p.k)
    {s : State} (h : Inv p s₀ k s) :
    WP isa (.block checkEkBody) s fun t => Inv p s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 32 * p.k) := by
  have hE : p.ekLen = 384 * p.k + 32 := rfl
  have load : WP isa (.block [.ldr .x .x9 .x0 0, .ldr .w .x10 .x0 8]) s fun t =>
      Only [.x9, .x10] s t ∧ t.gpr .x9 = s.mem.readW (s.gpr .x0) 64 ∧
      t.gpr .x10 = (s.mem.readW (s.gpr .x0 + 8) 32).setWidth 64 := by
    refine wp_ldrx (a := s.gpr .x0) (by decide) (by simp) ?_ fun s1 h1 e1 => ?_
    · rw [h.rd, h.wr, hp.1, hp.2, h.x0]
      exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by omega_arith) (by simp only [Params.ekLen]; omega_arith)))
    refine wp_ldrw (a := s.gpr .x0 + 8) (by decide) (by rw [h1.get .x0]; rfl) ?_ fun s2 h2 e2 => wp_nil ?_
    · rw [h1.rd, h1.wr, h.rd, h.wr, hp.1, hp.2, h.x0, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ptr_add]
      exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by omega_arith) (by simp only [Params.ekLen]; omega_arith)))
    refine ⟨h1.trans h2, by rw [h2.get .x9, e1], ?_⟩
    rw [e2, h1.mem]
  unfold checkEkBody
  rw [List.append_assoc]
  refine wp_scalar (by decide) load ?_
  intro s2 ⟨hl, x9, x10⟩ vl
  rw [WP.block_append_iff]
  refine WP.mono (ck_math_ok s2 (by rw [vl, h.mask]) (by rw [vl, h.bits]) (by rw [vl, h.q])) ?_
  intro s3 ⟨v19, g3, m3, rd3, wr3, sp3, hv3⟩
  let x := ofVDwords (s2.gpr .x9) (s2.gpr .x10)
  have xb : ∀ j < 12, (vbyte x j).toNat = ((B p s₀).getD (12 * k + j) 0).toNat := by
    intro j hj
    rw [show x = ofVDwords (s.mem.readW (s.gpr .x0) 64) ((s.mem.readW (s.gpr .x0 + 8) 32).setWidth 64) by
      dsimp only [x]; rw [x9, x10], input_byte _ _ hj, h.x0, ptr_add, h.mem,
      bytesAt_getD _ _ (by simp only [Params.ekLen]; omega_arith)]
  have hacc : ∀ e < 4, vword (s3.v .v19) e = accW (B p s₀) (k + 1) e := by
    intro e he
    have hl := low_lanes x e he
    have hh := high_lanes x e he
    simp only at hl hh
    rw [xb _ (by omega_arith), xb _ (by omega_arith), xb _ (by omega_arith)] at hl hh
    have f0 : (vword (low x) e).toNat = field0 (B p s₀) (4 * k + e) := by
      rw [hl, field0, show 12 * k + 3 * e = 3 * (4 * k + e) by omega_arith,
        show 12 * k + (3 * e + 1) = 3 * (4 * k + e) + 1 by omega_arith,
        show 12 * k + (3 * e + 2) = 3 * (4 * k + e) + 2 by omega_arith]
      have := ((B p s₀).getD (3 * (4 * k + e)) 0).isLt
      have := ((B p s₀).getD (3 * (4 * k + e) + 1) 0).isLt
      have := ((B p s₀).getD (3 * (4 * k + e) + 2) 0).isLt
      omega_arith
    have f1 : (vword (high x) e).toNat = field1 (B p s₀) (4 * k + e) := by
      rw [hh, field1, show 12 * k + 3 * e = 3 * (4 * k + e) by omega_arith,
        show 12 * k + (3 * e + 1) = 3 * (4 * k + e) + 1 by omega_arith,
        show 12 * k + (3 * e + 2) = 3 * (4 * k + e) + 2 by omega_arith]
      have := ((B p s₀).getD (3 * (4 * k + e)) 0).isLt
      have := ((B p s₀).getD (3 * (4 * k + e) + 1) 0).isLt
      have := ((B p s₀).getD (3 * (4 * k + e) + 2) 0).isLt
      omega_arith
    rw [v19, vword_or, vword_or, vl, h.acc e he, vword_geq _ he, vword_geq _ he, f0, f1, accW, acc_step]
    simp only [accW]
    congr 1
    apply propext
    constructor
    · intro ⟨h₁, h₂, h₃⟩ g hg
      by_cases hgk : g = k
      · subst hgk; exact ⟨h₂, h₃⟩
      · exact h₁ g (by omega_arith)
    · intro h'; exact ⟨fun g hg => h' g (by omega_arith), (h' k (by omega_arith)).1, (h' k (by omega_arith)).2⟩
  have gp (r : Reg) (hr : r ∉ [.x9, .x10]) : s3.gpr r = s.gpr r := by rw [g3, hl.gpr _ hr]
  have scalar : WP isa (.block [.addImm .x .x0 .x0 12, .subImm .x .x11 .x11 1]) s3
      fun t => Only [.x0, .x11] s3 t ∧ t.gpr .x0 = s3.gpr .x0 + 12 ∧ (t.gpr .x11).toNat = 32 * p.k - (k + 1) := by
    refine wp_addImm (by decide) fun s6 h6 e6 => wp_subImm (by decide) fun s7 h7 e7 => wp_nil ?_
    refine ⟨(h6.trans h7).mono (by decide), by rw [h7.get .x0, e6]; rfl, ?_⟩
    have cnt : (s6.gpr .x11).toNat = 32 * p.k - k := by rw [h6.get .x11, gp .x11 (by decide), h.x11]
    rw [e7, toNat_sub_n (by rw [cnt]; simp; omega_arith), cnt]; simp; omega_arith
  refine WP.mono (WP.keepV (by decide) scalar) ?_
  intro t ⟨⟨ht, p0, cnt⟩, vt⟩
  have keepv (r : VReg) (r0 : r ≠ .v0) (r1 : r ≠ .v1) (r2 : r ≠ .v2) (r3 : r ≠ .v3) (r19 : r ≠ .v19) :
      t.v r = s.v r := by rw [vt, hv3 r r0 r1 r2 r3 r19, vl]
  refine ⟨⟨by rw [ht.rd, rd3, hl.rd, h.rd], by rw [ht.wr, wr3, hl.wr, h.wr], by rw [ht.sp, sp3, hl.sp, h.sp],
    by rw [ht.mem, m3, hl.mem, h.mem], ?_, cnt,
    by rw [keepv .v16 (by decide) (by decide) (by decide) (by decide) (by decide), h.mask],
    by rw [keepv .v17 (by decide) (by decide) (by decide) (by decide) (by decide), h.bits],
    by rw [keepv .v18 (by decide) (by decide) (by decide) (by decide) (by decide), h.q],
    fun e he => by rw [vt]; exact hacc e he⟩, by rw [cnt]; omega_arith⟩
  rw [p0, gp .x0 (by decide), h.x0, show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl, ptr_add]
  congr 2

theorem init (s : State) (n : Nat) :
    WP isa (.block (maskVec .v16 [0,1,2,255,3,4,5,255,6,7,8,255,9,10,11,255] ++
      ([.movz .x .x9 4095 0, .vop (.dup .s4 .v17 .x9), .movz .x .x9 3329 0, .vop (.dup .s4 .v18 .x9),
        .vop (.movi0 .v19), .movz .x .x11 (BitVec.ofNat 16 n) 0] : List Instr))) s fun t =>
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.gpr .x0 = s.gpr .x0 ∧
      t.gpr .x11 = (BitVec.ofNat 16 n).setWidth 64 ∧ t.v .v16 = decMask ∧ t.v .v17 = mask12 ∧
      t.v .v18 = qvec ∧ t.v .v19 = 0 := by
  dsimp [maskVec, VG.Impl.MlKem.AArch64.movImm]
  rrun [RegUpd.sp_write, RegUpd.sp_setV]

theorem fin (s : State) :
    WP isa (.block [.vop (.uaddlv .s4 .v20 .v19), .umov .x .x9 .v20 0, .subImm .x .x0 .x9 1, .lsr .x .x0 .x0 63]) s
      fun t => t.gpr .x0 = ((BitVec.ofNat 128 (VArr.s4.laneSum (s.v .v19) % 2 ^ 64)).extractLsb' 0 64 -
        BitVec.ofNat 64 1) >>> 63 ∧ t.sp = s.sp := by
  rrun [RegUpd.sp_write, RegUpd.sp_setV]
  rfl

theorem laneSum_s4 (x : BitVec 128) :
    VArr.s4.laneSum x = (vword x 0).toNat + (vword x 1).toNat + (vword x 2).toNat + (vword x 3).toNat := by
  simp [VArr.laneSum, VArr.lanes, BitVec.toNat_setWidth]
  omega_arith

theorem sgn (L : Nat) (hL : L < 2 ^ 63) :
    (((BitVec.ofNat 128 (L % 2 ^ 64)).extractLsb' 0 64 - BitVec.ofNat 64 1) >>> 63).toNat =
      if L = 0 then 1 else 0 := by
  have hx : ((BitVec.ofNat 128 (L % 2 ^ 64)).extractLsb' 0 64).toNat = L := by
    rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]; omega_arith
  rw [toNat_lsr, BitVec.toNat_sub, hx, BitVec.toNat_ofNat]
  split <;> omega_arith

theorem correct (hk : 1 ≤ p.k ∧ p.k ≤ 4) (s₀ : State) (hs : (checkEkAArch64 p).pre s₀) :
    ∃ t s', Exec isa (checkEkWith (32 * p.k)) s₀ t s' ∧ abiPreserved s₀ s' ∧ (checkEkAArch64 p).post s₀ s' := by
  suffices h : WP isa (checkEkWith (32 * p.k)) s₀ fun s' => (checkEkAArch64 p).post s₀ s' by
    obtain ⟨t, s', he, hpost⟩ := h
    exact ⟨t, s', he, abi_of rfl (by rfl) he (hv := by rfl), hpost⟩
  unfold checkEkWith
  refine WP.seq (WP.mono (init s₀ (32 * p.k)) fun s₁ ⟨r₁, w₁, sp₁, m₁, x0₁, x11₁, v16₁, v17₁, v18₁, v19₁⟩ => ?_)
  have i₀ : Inv p s₀ 0 s₁ := ⟨r₁, w₁, sp₁, m₁, by rw [x0₁, Nat.mul_zero, ptr_zero],
    by rw [x11₁]; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_arith, v16₁, v17₁, v18₁,
    fun e he => by rw [v19₁]; simp [accW, vword]⟩
  refine WP.seq (WP.mono (count_loop (by omega_arith) (Inv p s₀) (fun j hj s h => step hs hk.2 hj h) i₀)
    fun s h => ?_)
  refine WP.mono (fin s) fun t ⟨ht, _⟩ => ?_
  have hsum := laneSum_s4 (s.v .v19)
  rw [h.acc 0 (by decide), h.acc 1 (by decide), h.acc 2 (by decide), h.acc 3 (by decide)] at hsum
  have hall : (∀ e < 4, ∀ g < 32 * p.k, good (B p s₀) (4 * g + e)) ↔
      ekCheck p (bytesAt s₀.mem (s₀.gpr .x0) p.ekLen) = true := by
    rw [ekCheck_iff p _ (bytesAt_length _ _ _)]
    constructor
    · intro h t ht
      have := h (t % 4) (by omega_arith) (t / 4) (by omega_arith)
      rwa [show 4 * (t / 4) + t % 4 = t by omega_arith] at this
    · intro h e he g hg; exact h _ (by omega_arith)
  have hv : ∀ e < 4, (accW (B p s₀) (32 * p.k) e).toNat =
      if ∀ g < 32 * p.k, good (B p s₀) (4 * g + e) then 0 else 2 ^ 32 - 1 := fun e _ => by
    unfold accW; split <;> simp
  rw [hv 0 (by decide), hv 1 (by decide), hv 2 (by decide), hv 3 (by decide)] at hsum
  show (t.gpr .x0).setWidth 32 = if ekCheck p (bytesAt s₀.mem (s₀.gpr .x0) p.ekLen) then 1 else 0
  apply BitVec.eq_of_toNat_eq
  have hlt : VArr.s4.laneSum (s.v .v19) < 2 ^ 34 := by rw [hsum]; split <;> split <;> split <;> split <;> omega_arith
  rw [BitVec.toNat_setWidth, ht, sgn _ (by omega_arith)]
  by_cases hc : ekCheck p (bytesAt s₀.mem (s₀.gpr .x0) p.ekLen) = true
  · have h4 := hall.mpr hc
    rw [ite_eq_left (h4 0 (by decide)), ite_eq_left (h4 1 (by decide)), ite_eq_left (h4 2 (by decide)),
      ite_eq_left (h4 3 (by decide))] at hsum
    rw [hsum, ite_eq_left hc]; rfl
  · rw [ite_eq_right hc]
    have hne : VArr.s4.laneSum (s.v .v19) ≠ 0 := by
      intro h0
      apply hc; apply hall.mp
      intro e he
      rw [h0] at hsum
      by_contra hn
      rcases (by omega_arith : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;>
        (rw [ite_eq_right hn] at hsum; omega_arith)
    rw [ite_eq_right hne]; rfl

/-! ## ML-KEM-768 -/

theorem ct : ConstantTime isa (checkEkAArch64 mlKem768).pre (checkEkAArch64 mlKem768).pub checkEk :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ ⟨h0, hsp⟩ => agree_of hsp (by simp [h0])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 1184⟩]
  wr := []

theorem checkEk_verified : Verified AArch64.target checkEk (Spec.MlKem.checkEkContract AArch64.abi) :=
  Verified.of_correct (correct (p := mlKem768) ⟨by decide, by decide⟩) ct (by
    mlkem_implies [Spec.MlKem.checkEkContract, Spec.MlKem.checkEkSig, checkEkAArch64, Spec.MlKem.mlKem768,
      Params.ekLen, AArch64.abi, AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem.AArch64.CheckEk
