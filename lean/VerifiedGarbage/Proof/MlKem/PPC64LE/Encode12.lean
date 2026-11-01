module

import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Impl.MlKem.PPC64LE.Codec
public import VerifiedGarbage.Proof.MlKem.PolyContract
import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
import VerifiedGarbage.Proof.MlKem.PPC64LE.Bytes
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.MlKem.PPC64LE.Codec
meta import VerifiedGarbage.Proof.MlKem.PolyContract
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Bytes
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.MlKem.Arith
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# ML-KEM on PPC64LE: `vg_mlkem_encode12`

One symbolic execution of the loop body for any pointers (`body_ok`); the
invariant says which bytes of the output are written (`Inv`); the bytes are
those of `encode12_byte0`–`encode12_byte2`.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.Encode12

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem

/-! ## The loop body -/

/-- The three bytes of a pair `a`, `b` of coefficients. -/
def b0 (a : BitVec 64) : Byte := a.setWidth 8
def b1 (a b : BitVec 64) : Byte := ((a >>> 8) + (b <<< 4)).setWidth 8
def b2 (b : BitVec 64) : Byte := (b >>> 4).setWidth 8

/-- What an iteration does. -/
def Step (s : State) (x y c : BitVec 64) (s' : State) : Prop :=
  s'.gpr .r3 = x + 8 ∧ s'.gpr .r4 = y + 3 ∧ s'.gpr .r5 = c - 1 ∧
    s'.mem = ((s.mem.writeW y (b0 ((s.mem.readW x 32).setWidth 64))).writeW (y + BitVec.ofNat 64 1)
        (b1 ((s.mem.readW x 32).setWidth 64) ((s.mem.readW (x + BitVec.ofNat 64 4) 32).setWidth 64))).writeW
      (y + BitVec.ofNat 64 2) (b2 ((s.mem.readW (x + BitVec.ofNat 64 4) 32).setWidth 64)) ∧
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r

theorem body_ok {s : State} {x y c : BitVec 64} (h3 : s.gpr .r3 = x) (h4 : s.gpr .r4 = y)
    (h5 : s.gpr .r5 = c)
    (ia : InRegions (s.rd ++ s.wr) x 4) (ib : InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 4) 4)
    (o0 : InRegions s.wr y 1) (o1 : InRegions s.wr (y + BitVec.ofNat 64 1) 1)
    (o2 : InRegions s.wr (y + BitVec.ofNat 64 2) 1) :
    WP isa (.block encode12Body) s (Step s x y c) := by
  crun [encode12Body, Step, b0, b1, b2, h3, h4, h5, ia, ib, o0, o1, o2, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  simp [Mem.writeW, Mem.readW, Mem.read]

/-! ## The loop -/

section
variable (s₀ : State)

abbrev F : Addr := s₀.gpr .r3
abbrev O : Addr := s₀.gpr .r4
abbrev outR : Region := ⟨O s₀, 384⟩
abbrev E : List Byte := encode12 (polyAt s₀.mem (F s₀))

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (F s₀)]
  wr : s₀.wr = [outR s₀]
  disj : (polyRegion (F s₀)).Disjoint (outR s₀)
  fitF : (F s₀).toNat + 1024 ≤ 2 ^ 64
  fitO : (O s₀).toNat + 384 ≤ 2 ^ 64
  red : Reduced s₀.mem (F s₀)

structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = F s₀ + BitVec.ofNat 64 (8 * i)
  r4 : s.gpr .r4 = O s₀ + BitVec.ofNat 64 (3 * i)
  r5 : s.gpr .r5 = BitVec.ofNat 64 (128 - i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [outR s₀] s₀.mem s.mem
  bytes : ∀ k < 384, s.mem (O s₀ + BitVec.ofNat 64 k) =
    if k < 3 * i then (E s₀)[k]! else s₀.mem (O s₀ + BitVec.ofNat 64 k)

/-- The bytes of group `i`. -/
theorem bytes_eq {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 128) :
    b0 ((coeffAt s₀.mem (F s₀) (2 * i)).setWidth 64) = (E s₀)[3 * i]! ∧
    b1 ((coeffAt s₀.mem (F s₀) (2 * i)).setWidth 64) ((coeffAt s₀.mem (F s₀) (2 * i + 1)).setWidth 64) =
      (E s₀)[3 * i + 1]! ∧
    b2 ((coeffAt s₀.mem (F s₀) (2 * i + 1)).setWidth 64) = (E s₀)[3 * i + 2]! := by
  have ea := polyAt_val hp.red (i := 2 * i) (by rw [n_eq]; omega_arith)
  have eb := polyAt_val hp.red (i := 2 * i + 1) (by rw [n_eq]; omega_arith)
  have la := val_lt (polyAt s₀.mem (F s₀))[2 * i]!
  have lb := val_lt (polyAt s₀.mem (F s₀))[2 * i + 1]!
  rw [encode12_byte0 _ hi, encode12_byte1 _ hi, encode12_byte2 _ hi]
  refine ⟨?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [b0, b1, b2, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, ← ea, ← eb] <;> omega_arith

theorem step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 128) {s : State} (h : Inv s₀ i s) :
    WP isa (.block encode12Body) s fun s' => Inv s₀ (i + 1) s' ∧ (s'.gpr .r5 != 0) = decide (i + 1 ≠ 128) := by
  have fF := hp.fitF
  have fO := hp.fitO
  have eA : F s₀ + BitVec.ofNat 64 (8 * i) = coeffAddr (F s₀) (2 * i) := by
    rw [show 8 * i = 4 * (2 * i) by omega_arith]
  have eB : F s₀ + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 4 = coeffAddr (F s₀) (2 * i + 1) := by
    rw [ptr_add, show 8 * i + 4 = 4 * (2 * i + 1) by omega_arith]
  have e1 : O s₀ + BitVec.ofNat 64 (3 * i) + BitVec.ofNat 64 1 = O s₀ + BitVec.ofNat 64 (3 * i + 1) := ptr_add _ _ _
  have e2 : O s₀ + BitVec.ofNat 64 (3 * i) + BitVec.ofNat 64 2 = O s₀ + BitVec.ofNat 64 (3 * i + 2) := ptr_add _ _ _
  have hrw : s.rd ++ s.wr = [polyRegion (F s₀), outR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hw : s.wr = [outR s₀] := by rw [h.wr, hp.wr]
  have cO : ∀ {k : Nat}, k < 384 → (outR s₀).Contains (O s₀ + BitVec.ofNat 64 k) 1 := fun hk =>
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have dF : ∀ r ∈ [outR s₀], (⟨F s₀, 1024⟩ : Region).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.disj
  have ra : s.mem.readW (coeffAddr (F s₀) (2 * i)) 32 = coeffAt s₀.mem (F s₀) (2 * i) :=
    coeffAt_congr (bytes_frame h.frame dF (by decide)) (by rw [n_eq]; omega_arith)
  have rb : s.mem.readW (coeffAddr (F s₀) (2 * i + 1)) 32 = coeffAt s₀.mem (F s₀) (2 * i + 1) :=
    coeffAt_congr (bytes_frame h.frame dF (by decide)) (by rw [n_eq]; omega_arith)
  obtain ⟨v0, v1, v2⟩ := bytes_eq hp hi
  refine WP.mono (body_ok h.r3 h.r4 h.r5 ?_ ?_ ?_ ?_ ?_) fun s' ⟨r3, r4, r5, m, rd, wr, sp, lr, pres⟩ =>
    ⟨⟨?_, ?_, ?_, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, lr.trans h.lr,
      fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, ?_⟩
  · rw [eA, hrw]; exact ⟨_, by simp, coeff_contains _ (by rw [n_eq]; omega_arith)⟩
  · rw [eB, hrw]; exact ⟨_, by simp, coeff_contains _ (by rw [n_eq]; omega_arith)⟩
  · rw [hw]; exact ⟨_, List.mem_singleton_self _, cO (by omega_arith)⟩
  · rw [e1, hw]; exact ⟨_, List.mem_singleton_self _, cO (by omega_arith)⟩
  · rw [e2, hw]; exact ⟨_, List.mem_singleton_self _, cO (by omega_arith)⟩
  · rw [r3]; exact ptr_succ _ 8 i
  · rw [r4]; exact ptr_succ _ 3 i
  · rw [r5]; exact count_sub hi
  · rw [m, e1, e2]
    exact ((h.frame.writeW (List.mem_singleton_self _) _ (cO (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (cO (by omega_arith))).writeW (List.mem_singleton_self _) _ (cO (by omega_arith))
  · rw [m, e1, e2, eB, eA, ra, rb, v0, v1, v2]
    exact byte_one (by omega_arith) (by decide) (byte_one (by omega_arith) (by decide)
      (byte_one (by omega_arith) (by decide) h.bytes rfl) rfl) rfl
  · rw [r5, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]
    exact count_nz hi (by decide)

theorem loop_ok {s₀ : State} (hp : Pre s₀) : WP isa encode12 s₀ (Inv s₀ 128) := by
  refine WP.seq (WP.cons (exec_li (by decide)) (wp_nil ?_))
  refine wp_loop_nz (Inv s₀) (N := 128) (by decide) (fun i hi s h => step hp hi h) (fun _ h => h) ?_
  refine ⟨by simp [State.write], by simp [State.write], by simp [State.write], rfl, rfl, rfl, rfl,
    fun r hr => ?_, Frame.refl _ _, fun k _ => rfl⟩
  have : r ≠ .r5 := by revert r hr; decide
  simp [State.write, this]

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlKem.encode12Contract PPC64LE.abi).pre s) : Pre s := by
  sig_pre [Proof.MlKem.encode12Contract, Proof.MlKem.encode12Sig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 384⟩]

theorem verified :
    Verified PPC64LE.target Impl.MlKem.PPC64LE.encode12 (Proof.MlKem.encode12Contract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, Add.ctRegs [.r3, .r4] (fun s₁ s₂ h => ?_) (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, h⟩ := loop_ok (pre_of hs)
    refine ⟨t, s', he, ⟨h.pres, h.sp, h.lr⟩, ?_⟩
    sig_post [Proof.MlKem.encode12Contract, Proof.MlKem.encode12Sig, PPC64LE.abi, PPC64LE.argRegs]
    exact bytesAt_eq! (p := O s) (encode12_length _) fun k hk => by
      rw [h.bytes k hk, ite_eq_left (by omega_arith)]
  · sig_pub [Proof.MlKem.encode12Contract, Proof.MlKem.encode12Sig, PPC64LE.abi, PPC64LE.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · sig_pub [Proof.MlKem.encode12Contract, Proof.MlKem.encode12Sig, PPC64LE.abi, PPC64LE.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.encode12Contract, Proof.MlKem.encode12Sig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact Add.reduced_zero _
        | decide +kernel

end VG.Proof.MlKem.PPC64LE.Encode12
