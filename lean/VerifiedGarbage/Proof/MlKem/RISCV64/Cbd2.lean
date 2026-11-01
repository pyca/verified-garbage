module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.MlKem.RISCV64.Common
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Impl.MlKem.RISCV64.Codec
public import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.Proof.MlKem.RISCV64.Add
import VerifiedGarbage.Proof.MlKem.RISCV64.Bytes
public import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Common
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.MlKem.RISCV64.Codec
meta import VerifiedGarbage.Spec.MlKem.Poly
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Bytes
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.MlKem.Arith
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import Init.Data.Nat.Bitwise.Basic

/-!
# ML-KEM on RISC-V: `vg_mlkem_cbd2`

As on PPC64LE (`Proof/MlKem/PPC64LE/Cbd2.lean`). One symbolic execution of the loop body for any pointers (`body_ok`); the
invariant says which coefficients of the output are written (`Inv`); the
values are those of `samplePolyCBD2_val`.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64.Cbd2

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## The loop body -/

/-- The number of bits set in the 2-bit field of `b` from bit `k`, as `pop2`
computes it. -/
def pc (b : Byte) (k : Nat) : BitVec 64 :=
  ((b.setWidth 64 <<< (62 - k)) >>> 62) - (((b.setWidth 64 <<< (62 - k)) >>> 62) >>> 1)

/-- The coefficient of the nibble of `b` from bit `k`. -/
def coef (b : Byte) (k : Nat) : BitVec 64 := fixq (pc b k - pc b (k + 2))

/-- What an iteration does. -/
def Step (s : State) (x y c : BitVec 64) (s' : State) : Prop :=
  s'.gpr .a0 = x + 1 ∧ s'.gpr .a1 = y + 8 ∧ s'.gpr .a2 = c - 1 ∧ s'.gpr .a5 = s.gpr .a5 ∧
    s'.mem = (s.mem.writeW y ((coef (s.mem x) 0).setWidth 32)).writeW (y + BitVec.ofNat 64 4)
      ((coef (s.mem x) 4).setWidth 32) ∧
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .ra = s.gpr .ra ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r

theorem body_ok {s : State} {x y c : BitVec 64} (h3 : s.gpr .a0 = x) (h4 : s.gpr .a1 = y)
    (h5 : s.gpr .a2 = c) (h8 : s.gpr .a5 = 3329)
    (i0 : InRegions (s.rd ++ s.wr) x 1)
    (o0 : InRegions s.wr y 4) (o1 : InRegions s.wr (y + BitVec.ofNat 64 4) 4) (ay : y.toNat % 4 = 0)
    (ay' : (y + BitVec.ofNat 64 4).toNat % 4 = 0)
    (hsep : ∀ (m : Mem) (v : BitVec 32), (m.write y 4 v) x = m x) :
    WP isa (.block cbd2Body) s (Step s x y c) := by
  crun [cbd2Body, cbdCoeff, pop2, fixup, Step, coef, pc, fixq, h3, h4, h5, h8, i0, o0, o1, ay, ay', hsep, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, setWidth_zero_append]

/-! ## The values -/

theorem byte64 (b : Byte) : (b.setWidth 64).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := b.isLt; omega)

theorem pc_toNat (b : Byte) {k : Nat} (hk : k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 6) :
    (pc b k).toNat = b.toNat / 2 ^ k % 2 + b.toNat / 2 ^ k / 2 % 2 := by
  have hb := b.isLt
  have e : ((b.setWidth 64 <<< (62 - k)) >>> 62).toNat = b.toNat / 2 ^ k % 4 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, byte64, Nat.shiftRight_eq_div_pow,
      Nat.shiftLeft_eq]
    rcases hk with rfl | rfl | rfl | rfl <;> simp only [Nat.reduceSub, Nat.reducePow] <;> omega
  unfold pc
  rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, e, Nat.shiftRight_eq_div_pow]
  omega

theorem coef_toNat (b : Byte) {k : Nat} (hk : k = 0 ∨ k = 4) :
    (coef b k).toNat = (cbdX (b.toNat / 2 ^ k) + q - cbdY (b.toNat / 2 ^ k)) % q := by
  have ex := pc_toNat b (k := k) (by omega)
  have ey := pc_toNat b (k := k + 2) (by omega)
  have hb := b.isLt
  unfold coef
  rw [fixq_sub (by rw [ex, q_eq]; omega) (by rw [ey, q_eq]; omega), ex, ey, cbdX, cbdY, Nat.pow_add]
  rw [← Nat.div_div_eq_div_mul, show (2 : Nat) ^ 2 = 4 from rfl]
  congr 1
  omega

/-! ## The loop -/

section
variable (s₀ : State)

abbrev B : Addr := s₀.gpr .a0
abbrev F : Addr := s₀.gpr .a1
abbrev inR : Region := ⟨B s₀, 128⟩
abbrev D : Poly := samplePolyCBD 2 (bytesAt s₀.mem (B s₀) 128)

/-- The value stored in coefficient `j`. -/
def out (j : Nat) : BitVec 32 := BitVec.ofNat 32 ((D s₀)[j]!).val

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [inR s₀]
  wr : s₀.wr = [polyRegion (F s₀)]
  disj : (inR s₀).Disjoint (polyRegion (F s₀))
  fitB : (B s₀).toNat + 128 ≤ 2 ^ 64
  fitF : (F s₀).toNat + 1024 ≤ 2 ^ 64
  alF : (F s₀).toNat % 4 = 0

structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = B s₀ + BitVec.ofNat 64 (1 * i)
  a1 : s.gpr .a1 = F s₀ + BitVec.ofNat 64 (8 * i)
  a2 : s.gpr .a2 = BitVec.ofNat 64 (128 - i)
  a5 : s.gpr .a5 = 3329
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  ra : s.gpr .ra = s₀.gpr .ra
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [polyRegion (F s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, coeffAt s.mem (F s₀) j = if j < 2 * i then out s₀ j else coeffAt s₀.mem (F s₀) j

theorem step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 128) {s : State} (h : Inv s₀ i s) :
    WP isa (.block cbd2Body) s fun s' => Inv s₀ (i + 1) s' ∧ (s'.gpr .a2 != 0) = decide (i + 1 ≠ 128) := by
  have fB := hp.fitB
  have fF := hp.fitF
  have eb : B s₀ + BitVec.ofNat 64 (1 * i) = B s₀ + BitVec.ofNat 64 i := by rw [Nat.one_mul]
  have e0 : F s₀ + BitVec.ofNat 64 (8 * i) = coeffAddr (F s₀) (2 * i) := by
    rw [show 8 * i = 4 * (2 * i) by omega]
  have e1 : F s₀ + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 4 = coeffAddr (F s₀) (2 * i + 1) := by
    rw [ptr_add, show 8 * i + 4 = 4 * (2 * i + 1) by omega]
  have hrw : s.rd ++ s.wr = [inR s₀, polyRegion (F s₀)] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hw : s.wr = [polyRegion (F s₀)] := by rw [h.wr, hp.wr]
  have c0 := coeff_contains (F s₀) (i := 2 * i) (by rw [n_eq]; omega)
  have c1 := coeff_contains (F s₀) (i := 2 * i + 1) (by rw [n_eq]; omega)
  have cb : (inR s₀).Contains (B s₀ + BitVec.ofNat 64 i) 1 := Offset.contains_base _ (by omega) (by omega)
  have rb : s.mem (B s₀ + BitVec.ofNat 64 i) = (bytesAt s₀.mem (B s₀) 128).getD i 0 := by
    rw [bytesAt_getD _ _ (by omega)]
    exact h.frame.bytes (R := inR s₀) (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj)
      (by show 128 ≤ 2 ^ 64; decide) (show i < 128 by omega)
  refine WP.mono (body_ok h.a0 h.a1 h.a2 h.a5 ?_ ?_ ?_ (by rw [e0]; exact align4_add hp.alF _)
    (by rw [e1]; exact align4_add hp.alF _) ?_)
    fun s' ⟨r3, r4, r5, r8, m, rd, wr, sp, ra, pres⟩ =>
    ⟨⟨?_, ?_, ?_, r8.trans h.a5, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ra.trans h.ra,
      fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, ?_⟩
  · rw [eb, hrw]; exact ⟨_, by simp, cb⟩
  · rw [e0, hw]; exact ⟨_, by simp, c0⟩
  · rw [e1, hw]; exact ⟨_, by simp, c1⟩
  · intro m v
    rw [e0, eb]
    exact Mem.write_apply fun h' => hp.disj _ cb (c0.byte h')
  · rw [r3]; exact ptr_succ _ 1 i
  · rw [r4]; exact ptr_succ _ 8 i
  · rw [r5]; exact count_sub hi
  · rw [m, e1, e0]
    exact (h.frame.writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1
  · have v0 : (coef ((bytesAt s₀.mem (B s₀) 128).getD i 0) 0).setWidth 32 = out s₀ (2 * i) := by
      refine setWidth32_ofNat ?_ (by have := val_lt (D s₀)[2 * i]!; omega)
      rw [coef_toNat _ (.inl rfl), samplePolyCBD2_val _ (by rw [n_eq]; omega), nibble,
        show 2 * i / 2 = i by omega, show 2 * i % 2 = 0 by omega]
    have v1 : (coef ((bytesAt s₀.mem (B s₀) 128).getD i 0) 4).setWidth 32 = out s₀ (2 * i + 1) := by
      refine setWidth32_ofNat ?_ (by have := val_lt (D s₀)[2 * i + 1]!; omega)
      rw [coef_toNat _ (.inr rfl), samplePolyCBD2_val _ (by rw [n_eq]; omega), nibble,
        show (2 * i + 1) / 2 = i by omega, show (2 * i + 1) % 2 = 1 by omega]
    rw [m, e1, e0, eb, rb, v0, v1, show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
    exact coeff_one (by omega) (coeff_one (by omega) h.coeff rfl) rfl
  · rw [r5, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]
    exact count_nz hi (by decide)

theorem init_ok {s₀ : State} : WP isa (.block ([.li .a2 128] ++ liq .a5 3329)) s₀ (Inv s₀ 0) := by
  simp only [liq, Nat.reduceLT, ite_false, List.cons_append, List.nil_append,
    Int.reduceSub, Int.reduceNeg, Int.cast_ofNat_Int]
  crun []
  refine ⟨by simp, by simp, by simp, by simp; decide, rfl, rfl, rfl, by simp, fun r hr => ?_, Frame.refl _ _,
    fun k _ => rfl⟩
  have : r ≠ .a2 ∧ r ≠ .a5 := by revert r hr; decide
  simp [this.1, this.2]

theorem loop_ok {s₀ : State} (hp : Pre s₀) : WP isa cbd2 s₀ (Inv s₀ 128) := by
  refine WP.seq (WP.mono (init_ok (s₀ := s₀)) fun s h => ?_)
  exact wp_loop_nz (Inv s₀) (N := 128) (by decide) (fun i hi s h => step hp hi h) (fun _ h => h) h

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlKem.cbd2Contract RISCV64.abi).pre s) : Pre s := by
  sig_pre [Spec.MlKem.cbd2Contract, Spec.MlKem.cbd2Sig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 1024⟩]

theorem verified :
    Verified RISCV64.target Impl.MlKem.RISCV64.cbd2 (Spec.MlKem.cbd2Contract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, Add.ctRegs [.a0, .a1] (fun s₁ s₂ h => ?_) (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, h⟩ := loop_ok (pre_of hs)
    refine ⟨t, s', he, ⟨h.pres, h.sp, h.ra⟩, ?_⟩
    sig_post [Spec.MlKem.cbd2Contract, Spec.MlKem.cbd2Sig, RISCV64.abi, RISCV64.argRegs]
    exact polyIs_of_coeffAt (p := F s) fun j hj => by
      rw [h.coeff j (by rw [n_eq] at hj; exact hj), ite_eq_left (by rw [n_eq] at hj; omega)]; rfl
  · sig_pub [Spec.MlKem.cbd2Contract, Spec.MlKem.cbd2Sig, RISCV64.abi, RISCV64.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · sig_pub [Spec.MlKem.cbd2Contract, Spec.MlKem.cbd2Sig, RISCV64.abi, RISCV64.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlKem.cbd2Contract, Spec.MlKem.cbd2Sig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlKem.RISCV64.Cbd2
