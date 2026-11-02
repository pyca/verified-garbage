module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.Bits
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.Bits
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-DSA on RISCV64: `vg_mldsa_high_bits` and `vg_mldsa_low_bits` against their contracts

The selection of `γ₂` (`sel_ok`), the head of the loop for it (`head_ok`),
the loop (`loop_ok`) with the values `hbv_toNat` (`highBits_eq`) and
`fixk_diff` (`lowBits_val`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Round.HighLow

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Round
open VG.Impl.MlDsa.RISCV64.Arith (loadImm)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Round (polyAt_val natPolyIs_of_toNat polyIs_of_toNat map_get highBits_eq lowBits_val mem_gamma2s
  hbF hbM hbF_le hbM_mul reduced_zero)
open VG.Proof.MlDsa.RISCV64.Round
open VG.Proof.MlDsa.RISCV64.Round.Bits

/-! ## Values -/

/-- A reduced coefficient, as loaded: its value. -/
theorem load_toNat {m : Mem} {p : Addr} (hr : Reduced m p) {i : Nat} (hi : i < 256) :
    ((coeffAt m p i).setWidth 64).toNat = ((polyAt m p)[i]!).val ∧ ((coeffAt m p i).setWidth 64).toNat < q := by
  have := polyAt_val hr (i := i) hi
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (coeffAt m p i).isLt; omega_arith)]
  exact ⟨this.symm, hr i hi⟩

/-- The value `highBits` stores for coefficient `j`. -/
def hbOut (g : Nat) (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (((polyAt s₀.mem (R s₀)).map fun c => (highBits g c).toNat)[j]!)

/-- The value `lowBits` stores for coefficient `j`. -/
def lbOut (g : Nat) (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (((polyAt s₀.mem (R s₀)).map fun c => ofInt (lowBits g c))[j]!).val

theorem hb_lt {g : Nat} (hg : g ∈ gamma2s) (a : Nat) : hbF g a % hbM g < 64 :=
  Nat.lt_of_lt_of_le (Nat.mod_lt _ (by rcases mem_gamma2s hg with rfl | rfl <;> decide))
    (by rcases mem_gamma2s hg with rfl | rfl <;> decide)

theorem hbOut_toNat {g : Nat} (hg : g ∈ gamma2s) (s₀ : State) {j : Nat} (hj : j < 256) :
    (hbOut g s₀ j).toNat = ((polyAt s₀.mem (R s₀)).map fun c => (highBits g c).toNat)[j]! := by
  rw [hbOut, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  rw [map_get _ _ hj, highBits_eq hg, Int.toNat_natCast]
  exact Nat.lt_trans (hb_lt hg _) (by decide)

theorem lbOut_toNat (g : Nat) (s₀ : State) {j : Nat} :
    (lbOut g s₀ j).toNat = (((polyAt s₀.mem (R s₀)).map fun c => ofInt (lowBits g c))[j]!).val := by
  rw [lbOut, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact Nat.lt_trans (Fin.isLt _) (by decide)

theorem hb_val {g : Nat} (hg : g ∈ gamma2s) {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) :
    (hbv g ((coeffAt s₀.mem (R s₀) i).setWidth 64)).setWidth 32 = hbOut g s₀ i := by
  obtain ⟨e, hq⟩ := load_toNat hp.red hi
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, hbv_toNat hg hq, hbOut_toNat hg s₀ hi, map_get _ _ hi, highBits_eq hg,
    Int.toNat_natCast, e]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (hb_lt hg _) (by decide))

theorem lb_val {g : Nat} (hg : g ∈ gamma2s) {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) :
    (fixk 8380417 ((coeffAt s₀.mem (R s₀) i).setWidth 64 -
      hbv g ((coeffAt s₀.mem (R s₀) i).setWidth 64) * BitVec.ofNat 64 (2 * g))).setWidth 32 = lbOut g s₀ i := by
  obtain ⟨e, hq⟩ := load_toNat hp.red hi
  generalize hA : (coeffAt s₀.mem (R s₀) i).setWidth 64 = A at e hq
  have hm := hbM_mul hg
  have hlt : hbF g A.toNat % hbM g < hbM g := Nat.mod_lt _ (by rcases mem_gamma2s hg with rfl | rfl <;> decide)
  have hb : (hbv g A * BitVec.ofNat 64 (2 * g)).toNat = hbF g A.toNat % hbM g * (2 * g) := by
    rw [BitVec.toNat_mul, hbv_toNat hg hq, BitVec.toNat_ofNat]
    have : g ≤ 261888 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
    rw [Nat.mod_eq_of_lt (by omega_arith : 2 * g < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_of_lt hlt))
      (by rw [hm]; rw [VG.Proof.MlDsa.Round.q_eq]; decide))
  have hbq : hbF g A.toNat % hbM g * (2 * g) ≤ q := by
    have := Nat.mul_le_mul_right (2 * g) (Nat.le_of_lt hlt); omega_arith
  have := fixk_diff (k := 8380417) (by decide) (a := A) (b := hbv g A * BitVec.ofNat 64 (2 * g))
    (by rw [VG.Proof.MlDsa.Round.q_eq] at hq; omega_arith) (by rw [hb]; rw [VG.Proof.MlDsa.Round.q_eq] at hbq; omega_arith)
    (by rw [hb]; rw [VG.Proof.MlDsa.Round.q_eq] at hbq; omega_arith)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, show (8380417 : BitVec 64) = BitVec.ofNat 64 8380417 from rfl, this, lbOut_toNat,
    map_get _ _ hi, lowBits_val hg, ← e, hb, VG.Proof.MlDsa.Round.q_eq]
  rw [VG.Proof.MlDsa.Round.q_eq] at hbq hq
  split <;> exact Nat.mod_eq_of_lt (by omega_arith)

/-! ## The functions -/

/-- What the functions leave. -/
def Post (out : Nat → BitVec 32) (s₀ s : State) : Prop :=
  (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.gpr .ra = s₀.gpr .ra ∧ ∀ j < 256, coeffAt s.mem (O s₀) j = out j

theorem kgpr_pres {g : Nat} {s₀ s : State}
    (hgpr : s.gpr = selGpr .a1 s₀.gpr) :
    ∀ r ∈ preserved, ((({ s with gpr := kgpr g s.gpr } : State).write .a3 (BitVec.ofNat 64 256)).gpr r) = s₀.gpr r := by
  intro r hr
  have : r ≠ .t0 ∧ r ≠ .a3 ∧ r ≠ .a4 ∧ r ≠ .a7 ∧ r ≠ .t1 ∧ r ≠ .t2 := by revert r hr; decide
  simp [State.write, kgpr, hgpr, selGpr, this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1,
    this.2.2.2.2.2]

theorem high_correct {s₀ : State} (hp : Pre s₀) : WP isa highBits s₀ (Post (hbOut (G s₀).toNat s₀) s₀) := by
  refine sel_ok hp fun g hg hG s hgpr hm hrd hwr hsp => ?_
  have e : (if g = g32 then hbLoop g32 else hbLoop g88) = hbLoop g := by
    rcases mem_gamma2s hg with rfl | rfl <;> rfl
  rw [e, hG]
  refine WP.seq (head_ok (extra := []) (Steps.WP.cons (exec_li (by decide)) (WP.block_nil ?_)))
  refine WP.mono (loop_ok (g := g) (k4 := s₀.gpr .a1) (k7 := BitVec.ofNat 64 261888)
    (f := fun a => (hbv g a).setWidth 32) hp
    (fun i hi s h x z c h3 h5 h6 ia oc ax az => hbBody_ok h3 h5 h6 h.k.r10 h.k.r11 h.k.r12 ia oc ax az)
    (fun i hi => hb_val hg hp hi) ?_)
    fun s' h' => ⟨h'.pres, h'.sp, h'.lr, fun j hj => h'.coeff j hj hj⟩
  refine ⟨?_, ?_, by simp [State.write], ⟨?_, ?_, ?_, ?_, ?_⟩, hrd, hwr, hsp, ?_, kgpr_pres hgpr,
    by rw [show _ = s.mem from rfl, hm]; exact Frame.refl _ _, fun j _ h => absurd h (by omega_arith)⟩ <;>
    simp [State.write, kgpr, hgpr, selGpr]

theorem low_correct {s₀ : State} (hp : Pre s₀) : WP isa lowBits s₀ (Post (lbOut (G s₀).toNat s₀) s₀) := by
  refine sel_ok hp fun g hg hG s hgpr hm hrd hwr hsp => ?_
  have e : (if g = g32 then lbLoop g32 else lbLoop g88) = lbLoop g := by
    rcases mem_gamma2s hg with rfl | rfl <;> rfl
  rw [e, hG]
  have b2 : 2 * g < 2 ^ 31 - 2048 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  unfold lbLoop
  rw [show hbConsts g ++ loadImm .a1 (2 * g) ++ loadQ .a4 ++ [Instr.li .a3 256] =
    hbConsts g ++ (loadImm .a1 (2 * g) ++ loadQ .a4) ++ [Instr.li .a3 256] by simp]
  simp only [loadQ, loadImm, List.cons_append, List.nil_append]
  refine WP.seq (head_ok (Steps.WP.cons exec_lui (Steps.WP.cons (exec_addi (VG.Proof.MlDsa.RISCV64.Arith.loadImm_imm _))
    (Steps.WP.cons exec_lui (Steps.WP.cons (exec_addi (VG.Proof.MlDsa.RISCV64.Arith.loadImm_imm _))
    (Steps.WP.cons (exec_li (by decide)) (WP.block_nil ?_)))))))
  refine WP.mono (loop_ok (g := g) (k4 := BitVec.ofNat 64 (2 * g)) (k7 := 8380417)
    (f := fun a => (fixk 8380417 (a - hbv g a * BitVec.ofNat 64 (2 * g))).setWidth 32) hp
    (fun i hi s h x z c h3 h5 h6 ia oc ax az => lbBody_ok h3 h5 h6 h.k.r10 h.k.r11 h.k.r12 ia oc ax az h.k.r4 h.k.r7)
    (fun i hi => lb_val hg hp hi) ?_)
    fun s' h' => ⟨h'.pres, h'.sp, h'.lr, fun j hj => h'.coeff j hj hj⟩
  have e4 := VG.Proof.MlDsa.RISCV64.Arith.loadImm_val b2
  have e7 := VG.Proof.MlDsa.RISCV64.Arith.loadImm_val (v := 8380417) (by decide)
  refine ⟨?_, ?_, by simp [State.write], ⟨?_, ?_, ?_, ?_, ?_⟩, hrd, hwr, hsp, ?_, fun r hr => ?_,
    by rw [show _ = s.mem from rfl, hm]; exact Frame.refl _ _, fun j _ h => absurd h (by omega_arith)⟩
  · simp [State.write, kgpr, hgpr, selGpr]
  · simp [State.write, kgpr, hgpr, selGpr]
  · simp only [State.write, ite_true, ite_false, reduceCtorEq]; exact e4
  · simp only [State.write, ite_true, ite_false, reduceCtorEq]; exact e7
  · simp [State.write, kgpr]
  · simp [State.write, kgpr]
  · simp [State.write, kgpr]
  · simp [State.write, kgpr, hgpr, selGpr]
  · have : r ≠ .t0 ∧ r ≠ .a1 ∧ r ≠ .a3 ∧ r ≠ .a4 ∧ r ≠ .a7 ∧ r ≠ .t1 ∧ r ≠ .t2 := by revert r hr; decide
    simp [State.write, kgpr, hgpr, selGpr, this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1,
      this.2.2.2.2.2.1, this.2.2.2.2.2.2]

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlDsa.highBitsContract RISCV64.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.highBitsContract, Proof.MlDsa.bitsSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem pre_of_low {s : State} (h : (Proof.MlDsa.lowBitsContract RISCV64.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.lowBitsContract, Proof.MlDsa.bitsSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 95232 | .a2 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 1024⟩]

theorem high_verified : Verified RISCV64.target highBits (Proof.MlDsa.highBitsContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, sel_ct (rg := .a1) (by decide) [.a0, .a2] (by decide) (fun s₁ s₂ h => ?_)
    (by taint_decide) (by taint_decide) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h⟩ := high_correct hp
    refine ⟨t, s', he, ⟨h.1, h.2.1, h.2.2.1⟩, ?_⟩
    sig_post [Proof.MlDsa.highBitsContract, Proof.MlDsa.bitsSig, RISCV64.abi, RISCV64.argRegs]
    refine natPolyIs_of_toNat fun j hj => ?_
    rw [h.2.2.2 j hj]
    exact hbOut_toNat hp.g s hj
  · sig_pub [Proof.MlDsa.highBitsContract, Proof.MlDsa.bitsSig, RISCV64.abi, RISCV64.argRegs] at h
    refine ⟨fun r hr => ?_, h.1, h.2.2.1⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2.2
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.highBitsContract, Proof.MlDsa.bitsSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

theorem low_verified : Verified RISCV64.target lowBits (Proof.MlDsa.lowBitsContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, sel_ct (rg := .a1) (by decide) [.a0, .a2] (by decide) (fun s₁ s₂ h => ?_)
    (by taint_decide) (by taint_decide) (by taint_decide), ?_⟩
  · have hp := pre_of_low hs
    obtain ⟨t, s', he, h⟩ := low_correct hp
    refine ⟨t, s', he, ⟨h.1, h.2.1, h.2.2.1⟩, ?_⟩
    sig_post [Proof.MlDsa.lowBitsContract, Proof.MlDsa.bitsSig, RISCV64.abi, RISCV64.argRegs]
    refine polyIs_of_toNat fun j hj => ?_
    rw [h.2.2.2 j hj]
    exact lbOut_toNat _ s
  · sig_pub [Proof.MlDsa.lowBitsContract, Proof.MlDsa.bitsSig, RISCV64.abi, RISCV64.argRegs] at h
    refine ⟨fun r hr => ?_, h.1, h.2.2.1⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2.2
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.lowBitsContract, Proof.MlDsa.bitsSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Round.HighLow
