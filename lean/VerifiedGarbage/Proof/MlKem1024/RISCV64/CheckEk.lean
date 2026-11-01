module

public import VerifiedGarbage.Proof.MlKem.RISCV64.CheckEk
public import VerifiedGarbage.Impl.MlKem1024.RISCV64.Poly
public import VerifiedGarbage.Spec.MlKem.Contract1024
import VerifiedGarbage.Proof.MlKem.RISCV64.Add
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.RISCV64.CheckEk
meta import VerifiedGarbage.Impl.MlKem1024.RISCV64.Poly
meta import VerifiedGarbage.Spec.MlKem.Contract1024
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Bytes
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Common
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM-1024 on RISC-V: `vg_mlkem1024_check_ek`

The loop of `vg_mlkem768_check_ek` (`Proof/MlKem/RISCV64/CheckEk.lean`, whose
body, counting and return value this uses) over the 512 groups of three bytes
of a 1568-byte key: it counts the 12-bit fields that are at least `q`
(`badCount`), and the key passes the check exactly when there are none
(`ekCheck1024`, `badCount_eq_zero`). As on PPC64LE
(`Proof/MlKem1024/PPC64LE/CheckEk.lean`), with `3328` kept in `a5`.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.RISCV64.CheckEk

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64 VG.Impl.MlKem1024.RISCV64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.RISCV64
open VG.Proof.MlKem.RISCV64.CheckEk (bad fld0 fld1 body_ok bad_toNat fld0_toNat fld1_toNat badN
  badCount badCount_le badN_le badCount_eq_zero ret_eq end_ok)

section
variable (s₀ : State)

abbrev K : Addr := s₀.gpr .a0
abbrev E : List Byte := bytesAt s₀.mem (K s₀) 1568

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨K s₀, 1568⟩]
  wr : s₀.wr = []
  fitK : (K s₀).toNat + 1568 ≤ 2 ^ 64

structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = K s₀ + BitVec.ofNat 64 (3 * i)
  a1 : s.gpr .a1 = BitVec.ofNat 64 (512 - i)
  a2 : s.gpr .a2 = BitVec.ofNat 64 (badCount (E s₀) i)
  a5 : s.gpr .a5 = 3328
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  ra : s.gpr .ra = s₀.gpr .ra
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem

theorem step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 512) {s : State} (h : Inv s₀ i s) :
    WP isa (.block checkEkBody) s fun s' =>
      Inv s₀ (i + 1) s' ∧ (s'.gpr .a1 != 0) = decide (i + 1 ≠ 512) := by
  have fK := hp.fitK
  have eb : ∀ k < 3, K s₀ + BitVec.ofNat 64 (3 * i) + BitVec.ofNat 64 k =
      K s₀ + BitVec.ofNat 64 (3 * i + k) := fun k _ => ptr_add _ _ _
  have x0 : K s₀ + BitVec.ofNat 64 (3 * i) = K s₀ + BitVec.ofNat 64 (3 * i + 0) := rfl
  have hrw : s.rd ++ s.wr = [⟨K s₀, 1568⟩] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have ib : ∀ k < 3, InRegions (s.rd ++ s.wr) (K s₀ + BitVec.ofNat 64 (3 * i + k)) 1 := fun k hk => by
    rw [hrw]; exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  have rb : ∀ k < 3, s.mem (K s₀ + BitVec.ofNat 64 (3 * i + k)) = (E s₀).getD (3 * i + k) 0 :=
    fun k hk => by rw [h.mem, bytesAt_getD _ _ (by omega)]
  refine WP.mono (body_ok h.a0 h.a1 h.a2 h.a5 (by rw [x0]; exact ib 0 (by omega))
    (by rw [eb 1 (by omega)]; exact ib 1 (by omega))
    (by rw [eb 2 (by omega)]; exact ib 2 (by omega)))
    fun s' ⟨r3, r4, r8, r5, m, rd, wr, sp, ra, pres⟩ =>
    ⟨⟨?_, ?_, ?_, r8.trans h.a5, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ra.trans h.ra,
      fun r hr => (pres r hr).trans (h.pres r hr), m.trans h.mem⟩, ?_⟩
  · rw [r3]; exact ptr_succ _ 3 i
  · rw [r4]; exact count_sub hi
  · rw [r5, eb 1 (by omega), eb 2 (by omega), x0, rb 0 (by omega), rb 1 (by omega), rb 2 (by omega),
      Nat.add_zero]
    have l0 := ((E s₀).getD (3 * i) 0).isLt
    have l1 := ((E s₀).getD (3 * i + 1) 0).isLt
    have l2 := ((E s₀).getD (3 * i + 2) 0).isLt
    have c0 := bad_toNat (F := fld0 ((E s₀).getD (3 * i) 0) ((E s₀).getD (3 * i + 1) 0))
      (by rw [fld0_toNat]; omega)
    have c1 := bad_toNat (F := fld1 ((E s₀).getD (3 * i + 1) 0) ((E s₀).getD (3 * i + 2) 0))
      (by rw [fld1_toNat]; omega)
    rw [fld0_toNat] at c0
    rw [fld1_toNat] at c1
    have hb := badCount_le (E s₀) i
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, c0, c1, BitVec.toNat_ofNat, BitVec.toNat_ofNat, badCount]
    simp only [field0, field1]
    have := badN_le (((E s₀).getD (3 * i) 0).toNat + 256 * (((E s₀).getD (3 * i + 1) 0).toNat % 16))
    have := badN_le (((E s₀).getD (3 * i + 1) 0).toNat / 16 + 16 * ((E s₀).getD (3 * i + 2) 0).toNat)
    omega
  · rw [r4, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]
    exact count_nz hi (by decide)

theorem init_ok {s₀ : State} :
    WP isa (.block (([.li .a1 512, .li .a2 0] : List Instr) ++ liq .a5 3328)) s₀ (Inv s₀ 0) := by
  simp only [liq, Nat.reduceLT, ite_false, List.cons_append, List.nil_append,
    Int.reduceSub, Int.reduceNeg, Int.cast_ofNat_Int]
  crun []
  refine ⟨by simp, by simp, by simp [badCount], by simp; decide, rfl, rfl, rfl, by simp, fun r hr => ?_, rfl⟩
  have : r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a5 := by revert r hr; decide
  simp [this.1, this.2.1, this.2.2]

theorem loop_ok {s₀ : State} (hp : Pre s₀) :
    WP isa checkEk1024 s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧
      s'.gpr .ra = s₀.gpr .ra ∧ s'.gpr .a0 = if badCount (E s₀) 512 = 0 then 1 else 0 := by
  refine WP.seq (WP.mono (init_ok (s₀ := s₀)) fun s h => ?_)
  refine WP.seq (wp_loop_nz (Inv s₀) (N := 512) (by decide) (fun i hi s h => step hp hi h)
    (fun s h => ?_) h)
  have hb := badCount_le (E s₀) 512
  refine WP.mono (end_ok h.a2) fun s' ⟨r3, sp, ra, pres⟩ =>
    ⟨fun r hr => (pres r hr).trans (h.pres r hr), sp.trans h.sp, ra.trans h.ra, ?_⟩
  rw [r3, ret_eq _ (by omega_arith)]

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlKem1024.checkEkContract RISCV64.abi).pre s) : Pre s := by
  sig_pre [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, RISCV64.abi,
    RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3⟩ := h
  exact ⟨h1, h2, h3⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 1568⟩]
  wr := []

theorem verified :
    Verified RISCV64.target checkEk1024 (Spec.MlKem1024.checkEkContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, Add.ctRegs [.a0] (fun s₁ s₂ h => ?_) (fun s₁ s₂ h => ?_)
    (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hra, h3⟩ := loop_ok (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp, hra⟩, ?_⟩
    sig_post [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, RISCV64.abi,
      RISCV64.argRegs]
    rw [h3]
    have hE : (E s).length = 1568 := bytesAt_length _ _ _
    by_cases hc : ekCheck mlKem1024 (E s) = true
    · rw [ite_eq_left ((badCount_eq_zero _ 512).mpr ((ekCheck1024 _ hE).mp hc)), ite_eq_left hc]; rfl
    · rw [ite_eq_right (fun h => hc ((ekCheck1024 _ hE).mpr ((badCount_eq_zero _ 512).mp h))),
        ite_eq_right hc]; rfl
  · sig_pub [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, RISCV64.abi,
      RISCV64.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h.2
  · sig_pub [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, RISCV64.abi,
      RISCV64.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, RISCV64.abi,
        RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlKem1024.RISCV64.CheckEk
