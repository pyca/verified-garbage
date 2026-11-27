module

public import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
public import VerifiedGarbage.Proof.MlKem.Arm.CallF
public import VerifiedGarbage.Proof.MlKem.Arm.CompressEncode
public import VerifiedGarbage.Proof.MlKem.Arm.Decompress
public import VerifiedGarbage.Proof.MlKem.Arm.NttInv
public import VerifiedGarbage.Impl.MlKem.Arm.Top
public import VerifiedGarbage.Proof.MlKem.Arm.Sample
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.Arm.Add
public import VerifiedGarbage.Proof.MlKem.Encode
public import VerifiedGarbage.Impl.MlKem.Arm.Poly
public import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.Arm.Add
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Impl.MlKem.Arm.Poly
meta import VerifiedGarbage.Proof.MlKem.Arm.Common
meta import VerifiedGarbage.Proof.MlKem.Arith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.TCB.Arm.Target

/-! ### `MlKem.Arm.Encode12`, which only this module used -/

section

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_encode12`

One symbolic execution of the loop body for any pointers (`body_ok`); the
invariant says which bytes of the output are written (`Inv`); the bytes are
those of `encode12_byte0`–`encode12_byte2`.
-/

@[expose] public section

namespace VG.Proof.MlKem.Arm.Encode12

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Proof.MlKem.Arm.Add (ptr_succ reduced_zero)

/-! ## The loop body -/

/-- The three bytes of a pair `a`, `b` of coefficients. -/
def b0 (a : BitVec 32) : Byte := a.setWidth 8
def b1 (a b : BitVec 32) : Byte := ((a >>> 8) + (b <<< 4)).setWidth 8
def b2 (b : BitVec 32) : Byte := (b >>> 4).setWidth 8

theorem body_ok {s : State} {x y c : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y)
    (h2 : s.gpr .r2 = c)
    (ia : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
    (ib : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 4)) 4)
    (o0 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 1)
    (o1 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 1)) 1)
    (o2 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 2)) 1) :
    WP isa (.block encode12Body) s fun s' =>
      s'.gpr .r0 = x + 8 ∧ s'.gpr .r1 = y + 3 ∧ s'.gpr .r2 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = ((s.mem.writeW (State.addr (y + BitVec.ofNat 32 0))
          (b0 (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32))).writeW
        (State.addr (y + BitVec.ofNat 32 1)) (b1 (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32)
          (s.mem.readW (State.addr (x + BitVec.ofNat 32 4)) 32))).writeW
        (State.addr (y + BitVec.ofNat 32 2)) (b2 (s.mem.readW (State.addr (x + BitVec.ofNat 32 4)) 32)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  run_block [encode12Body, b0, b1, b2, h0, h1, h2, ia, ib, o0, o1, o2, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

/-! ## The loop -/

section
variable (s₀ : State)

abbrev pf : BitVec 32 := s₀.gpr .r0
abbrev po : BitVec 32 := s₀.gpr .r1
abbrev F : Addr := State.addr (pf s₀)
abbrev O : Addr := State.addr (po s₀)
abbrev outR : Region := ⟨O s₀, 384⟩
abbrev E : List Byte := encode12 (polyAt s₀.mem (F s₀))

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (F s₀)]
  wr : s₀.wr = [outR s₀]
  disj : (polyRegion (F s₀)).Disjoint (outR s₀)
  fitF : (pf s₀).toNat + 1024 ≤ 2 ^ 32
  fitO : (po s₀).toNat + 384 ≤ 2 ^ 32
  red : Reduced s₀.mem (F s₀)

structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pf s₀ + BitVec.ofNat 32 (8 * i)
  r1 : s.gpr .r1 = po s₀ + BitVec.ofNat 32 (3 * i)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (1 * (128 - i))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [outR s₀] s₀.mem s.mem
  bytes : ∀ k < 384, s.mem (O s₀ + BitVec.ofNat 64 k) =
    if k < 3 * i then (E s₀)[k]! else s₀.mem (O s₀ + BitVec.ofNat 64 k)

/-- The bytes of group `i`. -/
theorem bytes_eq {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 128) :
    b0 (coeffAt s₀.mem (F s₀) (2 * i)) = (E s₀)[3 * i]! ∧
    b1 (coeffAt s₀.mem (F s₀) (2 * i)) (coeffAt s₀.mem (F s₀) (2 * i + 1)) = (E s₀)[3 * i + 1]! ∧
    b2 (coeffAt s₀.mem (F s₀) (2 * i + 1)) = (E s₀)[3 * i + 2]! := by
  have ea := polyAt_val hp.red (i := 2 * i) (by rw [n_eq]; omega_arith)
  have eb := polyAt_val hp.red (i := 2 * i + 1) (by rw [n_eq]; omega_arith)
  have la := val_lt (polyAt s₀.mem (F s₀))[2 * i]!
  have lb := val_lt (polyAt s₀.mem (F s₀))[2 * i + 1]!
  rw [encode12_byte0 _ hi, encode12_byte1 _ hi, encode12_byte2 _ hi]
  simp only [b0, b1, b2, setWidth8]
  refine ⟨ofNat8_eq ?_, ofNat8_eq ?_, ofNat8_eq ?_⟩
  · rw [← ea, Nat.mod_mod]
  · rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, ← ea, ← eb,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    omega_arith
  · rw [BitVec.toNat_ushiftRight, ← eb, Nat.shiftRight_eq_div_pow]

theorem step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 128) {s : State} (h : Inv s₀ i s) :
    WP isa (.block encode12Body) s fun s' => Inv s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 128) := by
  have fF := hp.fitF
  have fO := hp.fitO
  have eA : State.addr (pf s₀ + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 0) = coeffAddr (F s₀) (2 * i) :=
    addr_coeff fF (by omega_arith) (by omega_arith)
  have eB : State.addr (pf s₀ + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 4) =
      coeffAddr (F s₀) (2 * i + 1) := addr_coeff fF (by omega_arith) (by omega_arith)
  have e0 : State.addr (po s₀ + BitVec.ofNat 32 (3 * i) + BitVec.ofNat 32 0) = O s₀ + BitVec.ofNat 64 (3 * i) :=
    addr_byte fO (by omega_arith) (by omega_arith)
  have e1 : State.addr (po s₀ + BitVec.ofNat 32 (3 * i) + BitVec.ofNat 32 1) =
      O s₀ + BitVec.ofNat 64 (3 * i + 1) := addr_byte fO rfl (by omega_arith)
  have e2 : State.addr (po s₀ + BitVec.ofNat 32 (3 * i) + BitVec.ofNat 32 2) =
      O s₀ + BitVec.ofNat 64 (3 * i + 2) := addr_byte fO rfl (by omega_arith)
  have hrw : s.rd ++ s.wr = [polyRegion (F s₀), outR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hw : s.wr = [outR s₀] := by rw [h.wr, hp.wr]
  have dF : ∀ r ∈ [outR s₀], (polyRegion (F s₀)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.disj
  have ra : s.mem.readW (coeffAddr (F s₀) (2 * i)) 32 = coeffAt s₀.mem (F s₀) (2 * i) :=
    frame_coeff h.frame dF (by rw [n_eq]; omega_arith)
  have rb : s.mem.readW (coeffAddr (F s₀) (2 * i + 1)) 32 = coeffAt s₀.mem (F s₀) (2 * i + 1) :=
    frame_coeff h.frame dF (by rw [n_eq]; omega_arith)
  obtain ⟨v0, v1, v2⟩ := bytes_eq hp hi
  refine WP.mono (body_ok h.r0 h.r1 h.r2 ?_ ?_ ?_ ?_ ?_) fun s' ⟨r0, r1, r2, z, m, rd, wr, sp, pres⟩ =>
    ⟨⟨?_, ?_, ?_, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, fun r hr => (pres r hr).trans (h.pres r hr),
      ?_, ?_⟩, ?_⟩
  · rw [eA, hrw]; exact inRegions_of (by simp) (coeff_contains _ (by rw [n_eq]; omega_arith))
  · rw [eB, hrw]; exact inRegions_of (by simp) (coeff_contains _ (by rw [n_eq]; omega_arith))
  · rw [e0, hw]; exact inRegions_off (List.mem_singleton_self _) (by omega_arith) (by omega_arith)
  · rw [e1, hw]; exact inRegions_off (List.mem_singleton_self _) (by omega_arith) (by omega_arith)
  · rw [e2, hw]; exact inRegions_off (List.mem_singleton_self _) (by omega_arith) (by omega_arith)
  · rw [r0]; exact ptr_succ _ 8 i
  · rw [r1]; exact ptr_succ _ 3 i
  · rw [r2]; exact count_sub (k := 1) hi
  · rw [m, e0, e1, e2]
    exact ((h.frame.writeW (List.mem_singleton_self _) _ (contains_off (by omega_arith) (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (contains_off (by omega_arith) (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (contains_off (by omega_arith) (by omega_arith))
  · intro k hk
    rw [m, e0, e1, e2, eA, eB, ra, rb, v0, v1, v2,
      byte_writeW8 _ _ (by omega_arith) (by omega_arith), byte_writeW8 _ _ (by omega_arith) (by omega_arith),
      byte_writeW8 _ _ (by omega_arith) (by omega_arith), h.bytes k hk]
    rcases (by omega_arith : k < 3 * i ∨ k = 3 * i ∨ k = 3 * i + 1 ∨ k = 3 * i + 2 ∨ 3 * i + 3 ≤ k) with
      hk' | rfl | rfl | rfl | hk'
    · resolve_ifs
    · resolve_ifs
    · resolve_ifs
    · resolve_ifs
    · resolve_ifs
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

theorem loop_ok {s₀ : State} (hp : Pre s₀) : WP isa encode12 s₀ (Inv s₀ 128) := by
  refine WP.seq (WP.of_runBlock ?_)
  refine ⟨_, runBlock_cons.trans (by rfl), wp_loop_ne (Inv s₀) (N := 128) (by decide)
    (fun i hi s h => step hp hi h) (fun _ h => h) ?_⟩
  refine ⟨by simp [State.setReg], by simp [State.setReg], rfl, rfl, rfl, rfl,
    fun r hr => ?_, Frame.refl _ _, fun k _ => rfl⟩
  simp only [State.setReg]
  rw [ite_eq_right]
  intro e; subst e; simp [preserved] at hr

end VG.Proof.MlKem.Arm.Encode12

end

end

/-! ### `MlKem.Arm.Decode12`, which only this module used -/

section

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_decode12`

One symbolic execution of the loop body for any pointers (`body_ok`), which
loads bytes after storing a coefficient: `hsep` says the store does not change
them. The invariant says which coefficients are written (`Inv`); their values
are `decode12_even` and `decode12_odd`, reduced by `fixq_subq`.
-/

@[expose] public section

namespace VG.Proof.MlKem.Arm.Decode12

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Add (ptr_succ reduced_zero)

/-! ## The loop body -/

/-- The first field of the bytes `b₀`, `b₁`, reduced. -/
def fieldLo (b₀ b₁ : Byte) : BitVec 32 :=
  fixq (b₀.setWidth 32 + ((b₁.setWidth 32 <<< 28) >>> 20) - 3328 - 1)

/-- The second field of the bytes `b₁`, `b₂`, reduced. -/
def fieldHi (b₁ b₂ : Byte) : BitVec 32 :=
  fixq ((b₁.setWidth 32 >>> 4) + (b₂.setWidth 32 <<< 4) - 3328 - 1)

theorem body_ok {s : State} {x y c : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y)
    (h2 : s.gpr .r2 = c)
    (i0 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 1)
    (i1 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 1)) 1)
    (i2 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 2)) 1)
    (o0 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 4)
    (o1 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 4)) 4)
    (hsep : ∀ (m : Mem) (v : BitVec 32) (k : Nat), k < 3 →
      (m.writeW (State.addr (y + BitVec.ofNat 32 0)) v) (State.addr (x + BitVec.ofNat 32 k)) =
        m (State.addr (x + BitVec.ofNat 32 k))) :
    WP isa (.block decode12Body) s fun s' =>
      s'.gpr .r0 = x + 3 ∧ s'.gpr .r1 = y + 8 ∧ s'.gpr .r2 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = (s.mem.writeW (State.addr (y + BitVec.ofNat 32 0))
          (fieldLo (s.mem (State.addr (x + BitVec.ofNat 32 0))) (s.mem (State.addr (x + BitVec.ofNat 32 1))))).writeW
        (State.addr (y + BitVec.ofNat 32 4))
          (fieldHi (s.mem (State.addr (x + BitVec.ofNat 32 1))) (s.mem (State.addr (x + BitVec.ofNat 32 2)))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  run_block [decode12Body, decode12Lo, decode12Hi, subQ, fixup, fieldLo, fieldHi, fixq, h0, h1, h2, i0, i1, i2,
    o0, o1, hsep, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_self, and_true]

/-! ## The values -/

theorem lo_toNat (b₀ b₁ : Byte) : (fieldLo b₀ b₁).toNat = (b₀.toNat + 256 * (b₁.toNat % 16)) % q := by
  have h₀ := b₀.isLt
  have h₁ := b₁.isLt
  have e : (b₀.setWidth 32 + ((b₁.setWidth 32 <<< 28) >>> 20)).toNat = b₀.toNat + 256 * (b₁.toNat % 16) := by
    rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, setWidth32_toNat,
      setWidth32_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    omega_arith
  unfold fieldLo
  rw [fixq_subq (by rw [e, q_eq]; omega_arith), e]

theorem hi_toNat (b₁ b₂ : Byte) : (fieldHi b₁ b₂).toNat = (b₁.toNat / 16 + 16 * b₂.toNat) % q := by
  have h₁ := b₁.isLt
  have h₂ := b₂.isLt
  have e : ((b₁.setWidth 32 >>> 4) + (b₂.setWidth 32 <<< 4)).toNat = b₁.toNat / 16 + 16 * b₂.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, setWidth32_toNat,
      setWidth32_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    omega_arith
  unfold fieldHi
  rw [fixq_subq (by rw [e, q_eq]; omega_arith), e]

/-! ## The loop -/

section
variable (s₀ : State)

abbrev pb : BitVec 32 := s₀.gpr .r0
abbrev pf : BitVec 32 := s₀.gpr .r1
abbrev B : Addr := State.addr (pb s₀)
abbrev F : Addr := State.addr (pf s₀)
abbrev inR : Region := ⟨B s₀, 384⟩
abbrev D : Poly := decode12 (bytesAt s₀.mem (B s₀) 384)

/-- The value stored in coefficient `j`. -/
def out (j : Nat) : BitVec 32 := BitVec.ofNat 32 ((D s₀)[j]!).val

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [inR s₀]
  wr : s₀.wr = [polyRegion (F s₀)]
  disj : (inR s₀).Disjoint (polyRegion (F s₀))
  fitB : (pb s₀).toNat + 384 ≤ 2 ^ 32
  fitF : (pf s₀).toNat + 1024 ≤ 2 ^ 32

structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pb s₀ + BitVec.ofNat 32 (3 * i)
  r1 : s.gpr .r1 = pf s₀ + BitVec.ofNat 32 (8 * i)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (1 * (128 - i))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [polyRegion (F s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, coeffAt s.mem (F s₀) j = if j < 2 * i then out s₀ j else coeffAt s₀.mem (F s₀) j

theorem step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 128) {s : State} (h : Inv s₀ i s) :
    WP isa (.block decode12Body) s fun s' => Inv s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 128) := by
  have fB := hp.fitB
  have fF := hp.fitF
  have eb : ∀ k < 3, State.addr (pb s₀ + BitVec.ofNat 32 (3 * i) + BitVec.ofNat 32 k) =
      B s₀ + BitVec.ofNat 64 (3 * i + k) := fun k hk => addr_byte fB rfl (by omega_arith)
  have e0 : State.addr (pf s₀ + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 0) = coeffAddr (F s₀) (2 * i) :=
    addr_coeff fF (by omega_arith) (by omega_arith)
  have e1 : State.addr (pf s₀ + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 4) =
      coeffAddr (F s₀) (2 * i + 1) := addr_coeff fF (by omega_arith) (by omega_arith)
  have hrw : s.rd ++ s.wr = [inR s₀, polyRegion (F s₀)] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hw : s.wr = [polyRegion (F s₀)] := by rw [h.wr, hp.wr]
  have c0 := coeff_contains (F s₀) (i := 2 * i) (by rw [n_eq]; omega_arith)
  have c1 := coeff_contains (F s₀) (i := 2 * i + 1) (by rw [n_eq]; omega_arith)
  have cb : ∀ k < 3, (inR s₀).Contains (B s₀ + BitVec.ofNat 64 (3 * i + k)) 1 :=
    fun k hk => contains_off (by omega_arith) (by omega_arith)
  -- The bytes read are those on entry.
  have rb : ∀ k < 3, s.mem (B s₀ + BitVec.ofNat 64 (3 * i + k)) = (bytesAt s₀.mem (B s₀) 384).getD (3 * i + k) 0 :=
    fun k hk => by
      rw [bytesAt_getD _ _ (by omega_arith)]
      exact frame_byte h.frame (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj)
        (by decide) (by omega_arith)
  have hB : (bytesAt s₀.mem (B s₀) 384).length = 384 := bytesAt_length _ _ _
  refine WP.mono (body_ok h.r0 h.r1 h.r2 ?_ ?_ ?_ ?_ ?_ ?_) fun s' ⟨r0, r1, r2, z, m, rd, wr, sp, pres⟩ =>
    ⟨⟨?_, ?_, ?_, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, fun r hr => (pres r hr).trans (h.pres r hr),
      ?_, ?_⟩, ?_⟩
  · rw [eb 0 (by omega_arith), hrw]; exact inRegions_of (by simp) (cb 0 (by omega_arith))
  · rw [eb 1 (by omega_arith), hrw]; exact inRegions_of (by simp) (cb 1 (by omega_arith))
  · rw [eb 2 (by omega_arith), hrw]; exact inRegions_of (by simp) (cb 2 (by omega_arith))
  · rw [e0, hw]; exact inRegions_of (by simp) c0
  · rw [e1, hw]; exact inRegions_of (by simp) c1
  · intro m v k hk
    rw [e0, eb k hk]
    exact byte_writeW_disj hp.disj v c0 (cb k hk)
  · rw [r0]; exact ptr_succ _ 3 i
  · rw [r1]; exact ptr_succ _ 8 i
  · rw [r2]; exact count_sub (k := 1) hi
  · rw [m, e0, e1]
    exact (h.frame.writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1
  · intro j hj
    rw [m, e0, e1, eb 0 (by omega_arith), eb 1 (by omega_arith), eb 2 (by omega_arith), rb 0 (by omega_arith), rb 1 (by omega_arith),
      rb 2 (by omega_arith), coeffAt_writeW _ _ hj (by rw [n_eq]; omega_arith),
      coeffAt_writeW _ _ hj (by rw [n_eq]; omega_arith), h.coeff j hj]
    have v0 : fieldLo ((bytesAt s₀.mem (B s₀) 384).getD (3 * i + 0) 0)
        ((bytesAt s₀.mem (B s₀) 384).getD (3 * i + 1) 0) = out s₀ (2 * i) := by
      refine ofNat_val_eq ?_
      rw [lo_toNat, decode12_even _ hB hi, val_ofNat, Nat.add_zero]
    have v1 : fieldHi ((bytesAt s₀.mem (B s₀) 384).getD (3 * i + 1) 0)
        ((bytesAt s₀.mem (B s₀) 384).getD (3 * i + 2) 0) = out s₀ (2 * i + 1) := by
      refine ofNat_val_eq ?_
      rw [hi_toNat, decode12_odd _ hB hi, val_ofNat]
    rw [v0, v1]
    rcases (by omega_arith : j < 2 * i ∨ j = 2 * i ∨ j = 2 * i + 1 ∨ 2 * i + 2 ≤ j) with hj' | rfl | rfl | hj'
    · resolve_ifs
    · resolve_ifs
    · resolve_ifs
    · resolve_ifs
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

theorem loop_ok {s₀ : State} (hp : Pre s₀) : WP isa decode12 s₀ (Inv s₀ 128) := by
  refine WP.seq (WP.of_runBlock ?_)
  refine ⟨_, runBlock_cons.trans (by rfl), wp_loop_ne (Inv s₀) (N := 128) (by decide)
    (fun i hi s h => step hp hi h) (fun _ h => h) ?_⟩
  refine ⟨by simp [State.setReg], by simp [State.setReg], rfl, rfl, rfl, rfl,
    fun r hr => ?_, Frame.refl _ _, fun k _ => rfl⟩
  simp only [State.setReg]
  rw [ite_eq_right]
  intro e; subst e; simp [preserved] at hr

end VG.Proof.MlKem.Arm.Decode12

end

end

/-! ### `MlKem.Arm.Cbd2`, which only this module used -/

section

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_cbd2`

One symbolic execution of the loop body for any pointers (`body_ok`); the
invariant says which coefficients are written (`Inv`); their values are
`samplePolyCBD2_val`: the number of bits set in a 2-bit field `v` is `v - ⌊v /
2⌋`.
-/

@[expose] public section

namespace VG.Proof.MlKem.Arm.Cbd2

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Add (ptr_succ reduced_zero)

/-! ## The loop body -/

/-- The number of bits set in the 2-bit field of `b` from bit `k`, as `pop2`
computes it. -/
def pc (b : Byte) (k : Nat) : BitVec 32 :=
  ((b.setWidth 32 <<< (30 - k)) >>> 30) - (((b.setWidth 32 <<< (30 - k)) >>> 30) >>> 1)

/-- The coefficient of the nibble of `b` from bit `k`. -/
def coef (b : Byte) (k : Nat) : BitVec 32 := fixq (pc b k - pc b (k + 2))

theorem body_ok {s : State} {x y c : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y)
    (h2 : s.gpr .r2 = c)
    (i0 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 1)
    (o0 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 4)
    (o1 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 4)) 4)
    (hsep : ∀ (m : Mem) (v : BitVec 32),
      (m.writeW (State.addr (y + BitVec.ofNat 32 0)) v) (State.addr (x + BitVec.ofNat 32 0)) =
        m (State.addr (x + BitVec.ofNat 32 0))) :
    WP isa (.block cbd2Body) s fun s' =>
      s'.gpr .r0 = x + 1 ∧ s'.gpr .r1 = y + 8 ∧ s'.gpr .r2 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = (s.mem.writeW (State.addr (y + BitVec.ofNat 32 0))
          (coef (s.mem (State.addr (x + BitVec.ofNat 32 0))) 0)).writeW
        (State.addr (y + BitVec.ofNat 32 4)) (coef (s.mem (State.addr (x + BitVec.ofNat 32 0))) 4) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  run_block [cbd2Body, cbdCoeff, pop2, fixup, coef, pc, fixq, h0, h1, h2, i0, o0, o1, hsep, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

/-! ## The values -/

theorem pc_toNat (b : Byte) {k : Nat} (hk : k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 6) :
    (pc b k).toNat = b.toNat / 2 ^ k % 2 + b.toNat / 2 ^ k / 2 % 2 := by
  have hb := b.isLt
  have e : ((b.setWidth 32 <<< (30 - k)) >>> 30).toNat = b.toNat / 2 ^ k % 4 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, setWidth32_toNat, Nat.shiftRight_eq_div_pow,
      Nat.shiftLeft_eq]
    rcases hk with rfl | rfl | rfl | rfl <;> simp only [Nat.reduceSub, Nat.reducePow] <;> omega_arith
  unfold pc
  rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, e, Nat.shiftRight_eq_div_pow]
  omega_arith

theorem coef_toNat (b : Byte) {k : Nat} (hk : k = 0 ∨ k = 4) :
    (coef b k).toNat = (cbdX (b.toNat / 2 ^ k) + q - cbdY (b.toNat / 2 ^ k)) % q := by
  have ex := pc_toNat b (k := k) (by omega_arith)
  have ey := pc_toNat b (k := k + 2) (by omega_arith)
  have hb := b.isLt
  unfold coef
  rw [fixq_sub (by rw [ex, q_eq]; omega_arith) (by rw [ey, q_eq]; omega_arith), ex, ey, cbdX, cbdY, Nat.pow_add]
  rw [← Nat.div_div_eq_div_mul, show (2 : Nat) ^ 2 = 4 from rfl]
  congr 1
  omega_arith

/-! ## The loop -/

section
variable (s₀ : State)

abbrev pb : BitVec 32 := s₀.gpr .r0
abbrev pf : BitVec 32 := s₀.gpr .r1
abbrev B : Addr := State.addr (pb s₀)
abbrev F : Addr := State.addr (pf s₀)
abbrev inR : Region := ⟨B s₀, 128⟩
abbrev D : Poly := samplePolyCBD 2 (bytesAt s₀.mem (B s₀) 128)

/-- The value stored in coefficient `j`. -/
def out (j : Nat) : BitVec 32 := BitVec.ofNat 32 ((D s₀)[j]!).val

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [inR s₀]
  wr : s₀.wr = [polyRegion (F s₀)]
  disj : (inR s₀).Disjoint (polyRegion (F s₀))
  fitB : (pb s₀).toNat + 128 ≤ 2 ^ 32
  fitF : (pf s₀).toNat + 1024 ≤ 2 ^ 32

structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pb s₀ + BitVec.ofNat 32 (1 * i)
  r1 : s.gpr .r1 = pf s₀ + BitVec.ofNat 32 (8 * i)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (1 * (128 - i))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [polyRegion (F s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, coeffAt s.mem (F s₀) j = if j < 2 * i then out s₀ j else coeffAt s₀.mem (F s₀) j

theorem step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 128) {s : State} (h : Inv s₀ i s) :
    WP isa (.block cbd2Body) s fun s' => Inv s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 128) := by
  have fB := hp.fitB
  have fF := hp.fitF
  have eb : State.addr (pb s₀ + BitVec.ofNat 32 (1 * i) + BitVec.ofNat 32 0) = B s₀ + BitVec.ofNat 64 i :=
    addr_byte fB (by omega_arith) (by omega_arith)
  have e0 : State.addr (pf s₀ + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 0) = coeffAddr (F s₀) (2 * i) :=
    addr_coeff fF (by omega_arith) (by omega_arith)
  have e1 : State.addr (pf s₀ + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 4) =
      coeffAddr (F s₀) (2 * i + 1) := addr_coeff fF (by omega_arith) (by omega_arith)
  have hrw : s.rd ++ s.wr = [inR s₀, polyRegion (F s₀)] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hw : s.wr = [polyRegion (F s₀)] := by rw [h.wr, hp.wr]
  have c0 := coeff_contains (F s₀) (i := 2 * i) (by rw [n_eq]; omega_arith)
  have c1 := coeff_contains (F s₀) (i := 2 * i + 1) (by rw [n_eq]; omega_arith)
  have cb : (inR s₀).Contains (B s₀ + BitVec.ofNat 64 i) 1 := contains_off (by omega_arith) (by omega_arith)
  have rb : s.mem (B s₀ + BitVec.ofNat 64 i) = (bytesAt s₀.mem (B s₀) 128).getD i 0 := by
    rw [bytesAt_getD _ _ (by omega_arith)]
    exact frame_byte h.frame (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj)
      (by decide) (by omega_arith)
  refine WP.mono (body_ok h.r0 h.r1 h.r2 ?_ ?_ ?_ ?_) fun s' ⟨r0, r1, r2, z, m, rd, wr, sp, pres⟩ =>
    ⟨⟨?_, ?_, ?_, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, fun r hr => (pres r hr).trans (h.pres r hr),
      ?_, ?_⟩, ?_⟩
  · rw [eb, hrw]; exact inRegions_of (by simp) cb
  · rw [e0, hw]; exact inRegions_of (by simp) c0
  · rw [e1, hw]; exact inRegions_of (by simp) c1
  · intro m v
    rw [e0, eb]
    exact byte_writeW_disj hp.disj v c0 cb
  · rw [r0]; exact ptr_succ _ 1 i
  · rw [r1]; exact ptr_succ _ 8 i
  · rw [r2]; exact count_sub (k := 1) hi
  · rw [m, e0, e1]
    exact (h.frame.writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1
  · intro j hj
    rw [m, e0, e1, eb, rb, coeffAt_writeW _ _ hj (by rw [n_eq]; omega_arith),
      coeffAt_writeW _ _ hj (by rw [n_eq]; omega_arith), h.coeff j hj]
    have v0 : coef ((bytesAt s₀.mem (B s₀) 128).getD i 0) 0 = out s₀ (2 * i) := by
      refine ofNat_val_eq ?_
      rw [coef_toNat _ (.inl rfl), samplePolyCBD2_val _ (by rw [n_eq]; omega_arith), nibble,
        show 2 * i / 2 = i by omega_arith, show 2 * i % 2 = 0 by omega_arith]
    have v1 : coef ((bytesAt s₀.mem (B s₀) 128).getD i 0) 4 = out s₀ (2 * i + 1) := by
      refine ofNat_val_eq ?_
      rw [coef_toNat _ (.inr rfl), samplePolyCBD2_val _ (by rw [n_eq]; omega_arith), nibble,
        show (2 * i + 1) / 2 = i by omega_arith, show (2 * i + 1) % 2 = 1 by omega_arith]
    rw [v0, v1]
    rcases (by omega_arith : j < 2 * i ∨ j = 2 * i ∨ j = 2 * i + 1 ∨ 2 * i + 2 ≤ j) with hj' | rfl | rfl | hj'
    · resolve_ifs
    · resolve_ifs
    · resolve_ifs
    · resolve_ifs
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

theorem loop_ok {s₀ : State} (hp : Pre s₀) : WP isa cbd2 s₀ (Inv s₀ 128) := by
  refine WP.seq (WP.of_runBlock ?_)
  refine ⟨_, runBlock_cons.trans (by rfl), wp_loop_ne (Inv s₀) (N := 128) (by decide)
    (fun i hi s h => step hp hi h) (fun _ h => h) ?_⟩
  refine ⟨by simp [State.setReg], by simp [State.setReg], rfl, rfl, rfl, rfl,
    fun r hr => ?_, Frame.refl _ _, fun k _ => rfl⟩
  simp only [State.setReg]
  rw [ite_eq_right]
  intro e; subst e; simp [preserved] at hr

end VG.Proof.MlKem.Arm.Cbd2

end

end

/-!
# ML-KEM-768 on 32-bit ARM: calling the primitives on buffers

For each primitive, a contract written with the precondition of its proof and
what its correctness proof shows (`kNtt`, …, as `kAdd` in `Prims.lean`), and
the call of it with its arguments at offsets in the buffers of a layout
(`addL`, …): what it needs (the arguments in the registers, the regions apart
and permitted), what it changes (`Kept`, with the regions as triples) and what
it computes.
-/

@[expose] public section

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The address at offset `o` of buffer `i`. -/
abbrev Lay.A (L : Lay) (i o : Nat) : Addr := State.addr (L.ptr i) + BitVec.ofNat 64 o

/-- A whole buffer, as a permitted region. -/
abbrev Lay.buf (L : Lay) (i : Nat) : Region := ⟨State.addr (L.ptr i), L.size i⟩

theorem Lay.ptr_ok {L : Lay} (hL : L.Ok) {i o l : Nat} (hb : i < L.sizes.length ∧ o + l ≤ L.sizes.getD i 0)
    (hl : 0 < l) :
    State.addr (L.ptr i + BitVec.ofNat 32 o) = L.A i o ∧ (L.ptr i + BitVec.ofNat 32 o).toNat + l ≤ 2 ^ 32 :=
  ⟨Lay.addr_off hL hb.1 (by have := hb.2; simp only [Lay.size]; omega_using [hb, hl]), Lay.fit_off hL hb.1 hb.2 hl⟩

theorem view_r0 (s : State) (rd wr : List Region) : (view s rd wr).gpr .r0 = s.gpr .r0 := view_gpr' _ _ _ (by decide)
theorem view_r1 (s : State) (rd wr : List Region) : (view s rd wr).gpr .r1 = s.gpr .r1 := view_gpr' _ _ _ (by decide)
theorem view_r2 (s : State) (rd wr : List Region) : (view s rd wr).gpr .r2 = s.gpr .r2 := view_gpr' _ _ _ (by decide)
theorem view_r3 (s : State) (rd wr : List Region) : (view s rd wr).gpr .r3 = s.gpr .r3 := view_gpr' _ _ _ (by decide)

theorem Ctx.buf0 {L : Lay} {s : State} (hc : Ctx L s) : L.buf 0 ∈ s.wr := by
  exact hc.cw

theorem mem_rd_wr {r : Region} {s : State} (h : r ∈ s.wr) : r ∈ s.rd ++ s.wr := List.mem_append_right _ h

/-! ## `vg_mlkem_add`, `vg_mlkem_sub` -/

theorem accL {L : Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (hs : sepB L.sizes (i, o, 1024) (j, o', 1024) = true) (hw : L.buf i ∈ s.wr) (hr : L.buf j ∈ s.rd ++ s.wr)
    {f g : Poly} (hf : PolyIs s.mem (L.A i o) f) (hg : PolyIs s.mem (L.A j o') g) :
    AccArgs s (L.ptr i + BitVec.ofNat 32 o) (L.ptr j + BitVec.ofNat 32 o') ∧
      State.addr (L.ptr i + BitVec.ofNat 32 o) = L.A i o ∧ State.addr (L.ptr j + BitVec.ofNat 32 o') = L.A j o' := by
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (sepB_bounds hs) (by decide)
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (sepB_bounds (sepB_symm hs)) (by decide)
  refine ⟨⟨g0, g1, ?_, fa, fb, by rw [ea]; exact hf.1, by rw [eb]; exact hg.1, ?_, ?_⟩, ea, eb⟩
  · rw [ea, eb]; exact Lay.disj hL hs
  · rw [ea]; exact Lay.covers hw (sepB_bounds hs).2
  · rw [eb]; exact Lay.covers hr (sepB_bounds (sepB_symm hs)).2

theorem addL {L : Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (hs : sepB L.sizes (i, o, 1024) (j, o', 1024) = true) (hw : L.buf i ∈ s.wr) (hr : L.buf j ∈ s.rd ++ s.wr)
    {f g : Poly} (hf : PolyIs s.mem (L.A i o) f) (hg : PolyIs s.mem (L.A j o') g) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(i, o, 1024)]) s s' → PolyIs s'.mem (L.A i o) (add f g) → Q s') :
    WP isa callAdd s Q := by
  obtain ⟨h, ea, eb⟩ := accL hL g0 g1 hs hw hr hf hg
  refine add_call h fun s' hk hp => hQ s' (by rw [ea] at hk; exact hk) ?_
  rw [ea, eb, hf.2, hg.2] at hp; exact hp

theorem subL {L : Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (hs : sepB L.sizes (i, o, 1024) (j, o', 1024) = true) (hw : L.buf i ∈ s.wr) (hr : L.buf j ∈ s.rd ++ s.wr)
    {f g : Poly} (hf : PolyIs s.mem (L.A i o) f) (hg : PolyIs s.mem (L.A j o') g) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(i, o, 1024)]) s s' → PolyIs s'.mem (L.A i o) (sub f g) → Q s') :
    WP isa callSub s Q := by
  obtain ⟨h, ea, eb⟩ := accL hL g0 g1 hs hw hr hf hg
  refine sub_call h fun s' hk hp => hQ s' (by rw [ea] at hk; exact hk) ?_
  rw [ea, eb, hf.2, hg.2] at hp; exact hp

/-! ## `vg_mlkem_multiply_ntts` -/

theorem mulL {L : Lay} {s : State} (hL : L.Ok) {ih oh jf of kg og ls os : Nat}
    (g0 : s.gpr .r0 = L.ptr ih + BitVec.ofNat 32 oh) (g1 : s.gpr .r1 = L.ptr jf + BitVec.ofNat 32 of)
    (g2 : s.gpr .r2 = L.ptr kg + BitVec.ofNat 32 og) (g3 : s.gpr .r3 = L.ptr ls + BitVec.ofNat 32 os)
    (s_hf : sepB L.sizes (ih, oh, 1024) (jf, of, 1024) = true) (s_hg : sepB L.sizes (ih, oh, 1024) (kg, og, 1024) = true)
    (s_hs : sepB L.sizes (ih, oh, 1024) (ls, os, 1024) = true) (s_fs : sepB L.sizes (jf, of, 1024) (ls, os, 1024) = true)
    (s_gs : sepB L.sizes (kg, og, 1024) (ls, os, 1024) = true)
    (wh : L.buf ih ∈ s.wr) (wf : L.buf jf ∈ s.rd ++ s.wr) (wg : L.buf kg ∈ s.rd ++ s.wr) (ws : L.buf ls ∈ s.wr)
    {f g : Poly} (hf : PolyIs s.mem (L.A jf of) f) (hg : PolyIs s.mem (L.A kg og) g) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(ih, oh, 1024), (ls, os, 1024)]) s s' → PolyIs s'.mem (L.A ih oh) (multiplyNTTs f g) →
      Q s') :
    WP isa callMul s Q := by
  obtain ⟨eh, fh⟩ := Lay.ptr_ok hL (sepB_bounds s_hf) (by decide)
  obtain ⟨ef, ff⟩ := Lay.ptr_ok hL (sepB_bounds s_fs) (by decide)
  obtain ⟨eg, fg⟩ := Lay.ptr_ok hL (sepB_bounds s_gs) (by decide)
  obtain ⟨es, fs⟩ := Lay.ptr_ok hL (sepB_bounds (sepB_symm s_hs)) (by decide)
  have a : MulArgs s (L.ptr ih + BitVec.ofNat 32 oh) (L.ptr jf + BitVec.ofNat 32 of) (L.ptr kg + BitVec.ofNat 32 og)
      (L.ptr ls + BitVec.ofNat 32 os) := by
    refine ⟨g0, g1, g2, g3, ?_, ?_, ?_, ?_, ?_, fh, ff, fg, fs, by rw [ef]; exact hf.1, by rw [eg]; exact hg.1, ?_, ?_⟩
    · rw [eh, ef]; exact Lay.disj hL s_hf
    · rw [eh, eg]; exact Lay.disj hL s_hg
    · rw [eh, es]; exact Lay.disj hL s_hs
    · rw [ef, es]; exact Lay.disj hL s_fs
    · rw [eg, es]; exact Lay.disj hL s_gs
    · rw [eh, es]
      exact covers_cons' (Lay.covers wh (sepB_bounds s_hf).2)
        (covers_cons' (Lay.covers ws (sepB_bounds (sepB_symm s_hs)).2) covers_nil')
    · rw [ef, eg]
      exact covers_cons' (Lay.covers wf (sepB_bounds s_fs).2)
        (covers_cons' (Lay.covers wg (sepB_bounds s_gs).2) covers_nil')
  refine mul_call a fun s' hk hp => hQ s' (by simp only [mulWr, eh, es] at hk; exact hk) ?_
  rw [eh, ef, eg, hf.2, hg.2] at hp; exact hp

/-! ## `vg_mlkem_ntt`, `vg_mlkem_inv_ntt` -/

def kNtt : Contract isa := mkK Ntt.Pre (fun s₀ s => PolyIs s.mem (Ntt.F s₀) (ntt (Ntt.P s₀))) (regsEq [.r0, .r1])

def kNttInv : Contract isa :=
  mkK Ntt.Pre (fun s₀ s => PolyIs s.mem (Ntt.F s₀) (nttInv (Ntt.P s₀))) (regsEq [.r0, .r1])

theorem kNtt_ok : ∀ s, kNtt.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.ntt s t s' ∧ abiPreserved s s' ∧
    kNtt.post s s' := mkK_ok fun _ hp => Ntt.correct hp

theorem kNttInv_ok : ∀ s, kNttInv.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.nttInv s t s' ∧ abiPreserved s s' ∧
    kNttInv.post s s' := mkK_ok fun _ hp => NttInv.correct hp

theorem ntt_pre {L : Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (hs : sepB L.sizes (i, o, 1024) (j, o', 1024) = true) (wi : L.buf i ∈ s.wr) (wj : L.buf j ∈ s.wr)
    {f : Poly} (hf : PolyIs s.mem (L.A i o) f) :
    Ntt.Pre (view s [] [polyRegion (L.A i o), polyRegion (L.A j o')]) ∧
      Covers ([] ++ [polyRegion (L.A i o), polyRegion (L.A j o')]) (s.rd ++ s.wr) ∧
      Covers [polyRegion (L.A i o), polyRegion (L.A j o')] s.wr ∧
      Ntt.F (view s [] [polyRegion (L.A i o), polyRegion (L.A j o')]) = L.A i o ∧
      Ntt.P (view s [] [polyRegion (L.A i o), polyRegion (L.A j o')]) = f := by
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (sepB_bounds hs) (by decide)
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (sepB_bounds (sepB_symm hs)) (by decide)
  have cw : Covers [polyRegion (L.A i o), polyRegion (L.A j o')] s.wr :=
    covers_cons' (Lay.covers wi (sepB_bounds hs).2) (covers_cons' (Lay.covers wj (sepB_bounds (sepB_symm hs)).2)
      covers_nil')
  have eF : Ntt.F (view s [] [polyRegion (L.A i o), polyRegion (L.A j o')]) = L.A i o := by
    simp only [Ntt.F, Ntt.pf, view_r0, g0, ea]
  have eS : Ntt.S (view s [] [polyRegion (L.A i o), polyRegion (L.A j o')]) = L.A j o' := by
    simp only [Ntt.S, Ntt.ps, view_r1, g1, eb]
  refine ⟨⟨rfl, by rw [eF, eS]; rfl, by rw [eF, eS]; exact Lay.disj hL hs, by simp only [Ntt.pf, view_r0, g0]; exact fa,
    by simp only [Ntt.ps, view_r1, g1]; exact fb, by rw [eF]; exact hf.1⟩, covers_wr cw, cw, eF, ?_⟩
  simp only [Ntt.P, eF, State.withRegions_mem, State.callEntry_mem, hf.2]

theorem nttL {L : Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (hs : sepB L.sizes (i, o, 1024) (j, o', 1024) = true) (wi : L.buf i ∈ s.wr) (wj : L.buf j ∈ s.wr)
    {f : Poly} (hf : PolyIs s.mem (L.A i o) f) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(i, o, 1024), (j, o', 1024)]) s s' → PolyIs s'.mem (L.A i o) (ntt f) → Q s') :
    WP isa callNtt s Q := by
  obtain ⟨hp, c1, c2, eF, eP⟩ := ntt_pre hL g0 g1 hs wi wj hf
  refine call_kept (k := kNtt) kNtt_ok (by decide +kernel) hp c1 c2 fun s' hk hq => hQ s' hk ?_
  simp only [kNtt, mkK, eF, eP, State.withRegions_mem] at hq; exact hq

theorem nttInvL {L : Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (hs : sepB L.sizes (i, o, 1024) (j, o', 1024) = true) (wi : L.buf i ∈ s.wr) (wj : L.buf j ∈ s.wr)
    {f : Poly} (hf : PolyIs s.mem (L.A i o) f) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(i, o, 1024), (j, o', 1024)]) s s' → PolyIs s'.mem (L.A i o) (nttInv f) → Q s') :
    WP isa callNttInv s Q := by
  obtain ⟨hp, c1, c2, eF, eP⟩ := ntt_pre hL g0 g1 hs wi wj hf
  refine call_kept (k := kNttInv) kNttInv_ok (by decide +kernel) hp c1 c2 fun s' hk hq => hQ s' hk ?_
  simp only [kNttInv, mkK, eF, eP, State.withRegions_mem] at hq; exact hq

/-! ## `vg_mlkem_cbd2`, `vg_mlkem_decode12`, `vg_mlkem_encode12` -/

def kCbd : Contract isa := mkK Cbd2.Pre (fun s₀ s => PolyIs s.mem (Cbd2.F s₀) (Cbd2.D s₀)) (regsEq [.r0, .r1])

theorem kCbd_ok : ∀ s, kCbd.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.cbd2 s t s' ∧ abiPreserved s s' ∧
    kCbd.post s s' :=
  mkK_ok fun s₀ hp => WP.mono (Cbd2.loop_ok hp) fun _ h => ⟨h.pres, h.sp,
    polyIs_of_coeffAt (p := Cbd2.F s₀) fun j hj => by
      rw [h.coeff j hj, ite_eq_left (by rw [VG.Proof.MlKem.n_eq] at hj; omega_using [hj])]; rfl⟩

def kDec : Contract isa := mkK Decode12.Pre (fun s₀ s => PolyIs s.mem (Decode12.F s₀) (Decode12.D s₀))
  (regsEq [.r0, .r1])

theorem kDec_ok : ∀ s, kDec.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.decode12 s t s' ∧ abiPreserved s s' ∧
    kDec.post s s' :=
  mkK_ok fun s₀ hp => WP.mono (Decode12.loop_ok hp) fun _ h => ⟨h.pres, h.sp,
    polyIs_of_coeffAt (p := Decode12.F s₀) fun j hj => by
      rw [h.coeff j hj, ite_eq_left (by rw [VG.Proof.MlKem.n_eq] at hj; omega_using [hj])]; rfl⟩

def kEnc : Contract isa := mkK Encode12.Pre (fun s₀ s => bytesAt s.mem (Encode12.O s₀) 384 = Encode12.E s₀)
  (regsEq [.r0, .r1])

theorem kEnc_ok : ∀ s, kEnc.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.encode12 s t s' ∧ abiPreserved s s' ∧
    kEnc.post s s' :=
  mkK_ok fun s₀ hp => WP.mono (Encode12.loop_ok hp) fun _ h => ⟨h.pres, h.sp,
    bytesAt_eq! (p := Encode12.O s₀) (encode12_length _) fun k hk => by
      rw [h.bytes k hk, ite_eq_left (by omega_using [hk])]⟩

/-- `SamplePolyCBD₂` of the 128 bytes at `(i, o)` into the polynomial at `(j, o')`. -/
theorem cbd2L {L : Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (hs : sepB L.sizes (i, o, 128) (j, o', 1024) = true) (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 1024)]) s s' →
      PolyIs s'.mem (L.A j o') (samplePolyCBD 2 (bytesAt s.mem (L.A i o) 128)) → Q s') :
    WP isa callCbd2 s Q := by
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (sepB_bounds hs) (by decide)
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (sepB_bounds (sepB_symm hs)) (by decide)
  have eB : Cbd2.B (view s [⟨L.A i o, 128⟩] [polyRegion (L.A j o')]) = L.A i o := by
    simp only [Cbd2.B, Cbd2.pb, view_r0, g0, ea]
  have eF : Cbd2.F (view s [⟨L.A i o, 128⟩] [polyRegion (L.A j o')]) = L.A j o' := by
    simp only [Cbd2.F, Cbd2.pf, view_r1, g1, eb]
  have cw : Covers [polyRegion (L.A j o')] s.wr := Lay.covers wj (sepB_bounds (sepB_symm hs)).2
  refine call_kept (k := kCbd) kCbd_ok (by decide +kernel) (rd := [⟨L.A i o, 128⟩]) (wr := [polyRegion (L.A j o')])
    ⟨by simp only [Cbd2.inR, eB, State.withRegions_rd], by simp only [eF, State.withRegions_wr],
      by simp only [Cbd2.inR, eB, eF]; exact Lay.disj hL hs,
      by simp only [Cbd2.pb, view_r0, g0]; exact fa, by simp only [Cbd2.pf, view_r1, g1]; exact fb⟩
    (covers_append (Lay.covers wi (sepB_bounds hs).2) (covers_wr cw)) cw fun s' hk hq => hQ s' hk ?_
  simp only [kCbd, mkK, Cbd2.D, eB, eF, State.withRegions_mem, State.callEntry_mem] at hq; exact hq

/-- `ByteDecode₁₂` of the 384 bytes at `(i, o)` into the polynomial at `(j, o')`. -/
theorem decode12L {L : Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (hs : sepB L.sizes (i, o, 384) (j, o', 1024) = true) (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 1024)]) s s' →
      PolyIs s'.mem (L.A j o') (decode12 (bytesAt s.mem (L.A i o) 384)) → Q s') :
    WP isa callDecode12 s Q := by
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (sepB_bounds hs) (by decide)
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (sepB_bounds (sepB_symm hs)) (by decide)
  have eB : Decode12.B (view s [⟨L.A i o, 384⟩] [polyRegion (L.A j o')]) = L.A i o := by
    simp only [Decode12.B, Decode12.pb, view_r0, g0, ea]
  have eF : Decode12.F (view s [⟨L.A i o, 384⟩] [polyRegion (L.A j o')]) = L.A j o' := by
    simp only [Decode12.F, Decode12.pf, view_r1, g1, eb]
  have cw : Covers [polyRegion (L.A j o')] s.wr := Lay.covers wj (sepB_bounds (sepB_symm hs)).2
  refine call_kept (k := kDec) kDec_ok (by decide +kernel) (rd := [⟨L.A i o, 384⟩]) (wr := [polyRegion (L.A j o')])
    ⟨by simp only [Decode12.inR, eB, State.withRegions_rd], by simp only [eF, State.withRegions_wr],
      by simp only [Decode12.inR, eB, eF]; exact Lay.disj hL hs,
      by simp only [Decode12.pb, view_r0, g0]; exact fa, by simp only [Decode12.pf, view_r1, g1]; exact fb⟩
    (covers_append (Lay.covers wi (sepB_bounds hs).2) (covers_wr cw)) cw fun s' hk hq => hQ s' hk ?_
  simp only [kDec, mkK, Decode12.D, eB, eF, State.withRegions_mem, State.callEntry_mem] at hq; exact hq

/-- `ByteEncode₁₂` of the polynomial at `(i, o)` into the 384 bytes at `(j, o')`. -/
theorem encode12L {L : Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (hs : sepB L.sizes (i, o, 1024) (j, o', 384) = true) (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr)
    {f : Poly} (hf : PolyIs s.mem (L.A i o) f) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 384)]) s s' → bytesAt s'.mem (L.A j o') 384 = encode12 f → Q s') :
    WP isa callEncode12 s Q := by
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (sepB_bounds hs) (by decide)
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (sepB_bounds (sepB_symm hs)) (by decide)
  have eF : Encode12.F (view s [polyRegion (L.A i o)] [⟨L.A j o', 384⟩]) = L.A i o := by
    simp only [Encode12.F, Encode12.pf, view_r0, g0, ea]
  have eO : Encode12.O (view s [polyRegion (L.A i o)] [⟨L.A j o', 384⟩]) = L.A j o' := by
    simp only [Encode12.O, Encode12.po, view_r1, g1, eb]
  have cw : Covers [⟨L.A j o', 384⟩] s.wr := Lay.covers wj (sepB_bounds (sepB_symm hs)).2
  refine call_kept (k := kEnc) kEnc_ok (by decide +kernel) (rd := [polyRegion (L.A i o)]) (wr := [⟨L.A j o', 384⟩])
    ⟨by simp only [eF, State.withRegions_rd], by simp only [Encode12.outR, eO, State.withRegions_wr],
      by simp only [Encode12.outR, eF, eO]; exact Lay.disj hL hs,
      by simp only [Encode12.pf, view_r0, g0]; exact fa, by simp only [Encode12.po, view_r1, g1]; exact fb,
      by rw [eF]; exact hf.1⟩
    (covers_append (Lay.covers wi (sepB_bounds hs).2) (covers_wr cw)) cw fun s' hk hq => hQ s' hk ?_
  simp only [kEnc, mkK, Encode12.E, eF, eO, State.withRegions_mem, State.callEntry_mem, hf.2] at hq; exact hq

/-! ## `vg_mlkem_compress_encode`, `vg_mlkem_decode_decompress` -/

def kCmp : Contract isa := mkK CompressEncode.Pre
  (fun s₀ s => bytesAt s.mem (CompressEncode.O s₀) (CompressEncode.len s₀) = CompressEncode.CE s₀)
  (regsEq [.r0, .r1, .r2, .r3])

theorem kCmp_ok : ∀ s, kCmp.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.compressEncode s t s' ∧
    abiPreserved s s' ∧ kCmp.post s s' := mkK_ok fun _ hp => CompressEncode.correct hp

def kDcm : Contract isa := mkK Decompress.Pre (fun s₀ s => PolyIs s.mem (Decompress.F s₀) (Decompress.D s₀))
  (regsEq [.r0, .r1, .r2, .r3])

theorem kDcm_ok : ∀ s, kDcm.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.decodeDecompress s t s' ∧
    abiPreserved s s' ∧ kDcm.post s s' := mkK_ok fun _ hp => Decompress.correct hp

theorem width_lt {d : Nat} (hd : d ∈ compressWidths) : d < 2 ^ 32 ∧ 32 * d < 2 ^ 32 := by
  rcases VG.Proof.MlKem.mem_compressWidths hd with rfl | rfl | rfl <;> decide

/-- `ByteEncode_d(Compress_d(f))` of the polynomial at `(i, o)` into the `32 d` bytes at `(j, o')`. -/
theorem compressL {L : Lay} {s : State} (hL : L.Ok) {i o j o' d : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = BitVec.ofNat 32 d)
    (g2 : s.gpr .r2 = L.ptr j + BitVec.ofNat 32 o') (g3 : s.gpr .r3 = BitVec.ofNat 32 (32 * d))
    (hd : d ∈ compressWidths) (hs : sepB L.sizes (i, o, 1024) (j, o', 32 * d) = true)
    (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) {f : Poly} (hf : PolyIs s.mem (L.A i o) f)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 32 * d)]) s s' → bytesAt s'.mem (L.A j o') (32 * d) = compressEncode d f →
      Q s') :
    WP isa callCompress s Q := by
  have ⟨d1, d2⟩ := width_lt hd
  have hd0 : 0 < 32 * d := by rcases VG.Proof.MlKem.mem_compressWidths hd with rfl | rfl | rfl <;> decide
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (sepB_bounds hs) (by decide)
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (sepB_bounds (sepB_symm hs)) hd0
  have eF : CompressEncode.F (view s [polyRegion (L.A i o)] [⟨L.A j o', 32 * d⟩]) = L.A i o := by
    simp only [CompressEncode.F, CompressEncode.pf, view_r0, g0, ea]
  have eO : CompressEncode.O (view s [polyRegion (L.A i o)] [⟨L.A j o', 32 * d⟩]) = L.A j o' := by
    simp only [CompressEncode.O, CompressEncode.po, view_r2, g2, eb]
  have eD : CompressEncode.dd (view s [polyRegion (L.A i o)] [⟨L.A j o', 32 * d⟩]) = d := by
    simp only [CompressEncode.dd, view_r1, g1, toNat_ofNat32 d1]
  have eL : CompressEncode.len (view s [polyRegion (L.A i o)] [⟨L.A j o', 32 * d⟩]) = 32 * d := by
    simp only [CompressEncode.len, view_r3, g3, toNat_ofNat32 d2]
  have cw : Covers [⟨L.A j o', 32 * d⟩] s.wr := Lay.covers wj (sepB_bounds (sepB_symm hs)).2
  refine call_kept (k := kCmp) kCmp_ok (by decide +kernel) (rd := [polyRegion (L.A i o)])
    (wr := [⟨L.A j o', 32 * d⟩])
    ⟨by simp only [eF, State.withRegions_rd], by simp only [CompressEncode.outR, eO, eL, State.withRegions_wr],
      by simp only [CompressEncode.outR, eF, eO, eL]; exact Lay.disj hL hs,
      by simp only [CompressEncode.pf, view_r0, g0]; exact fa, by rw [eL]; simp only [CompressEncode.po, view_r2, g2]; exact fb,
      by rw [eD]; exact hd, by rw [eL, eD], by rw [eF]; exact hf.1⟩
    (covers_append (Lay.covers wi (sepB_bounds hs).2) (covers_wr cw)) cw fun s' hk hq => hQ s' hk ?_
  simp only [kCmp, mkK, CompressEncode.CE, CompressEncode.fp, eF, eO, eL, eD, State.withRegions_mem,
    State.callEntry_mem, hf.2] at hq
  exact hq

/-- `Decompress_d(ByteDecode_d(·))` of the `32 d` bytes at `(i, o)` into the polynomial at `(j, o')`. -/
theorem decompressL {L : Lay} {s : State} (hL : L.Ok) {i o j o' d : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = BitVec.ofNat 32 (32 * d))
    (g2 : s.gpr .r2 = BitVec.ofNat 32 d) (g3 : s.gpr .r3 = L.ptr j + BitVec.ofNat 32 o')
    (hd : d ∈ compressWidths) (hs : sepB L.sizes (i, o, 32 * d) (j, o', 1024) = true)
    (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 1024)]) s s' →
      PolyIs s'.mem (L.A j o') (decodeDecompress d (bytesAt s.mem (L.A i o) (32 * d))) → Q s') :
    WP isa callDecompress s Q := by
  have ⟨d1, d2⟩ := width_lt hd
  have hd0 : 0 < 32 * d := by rcases VG.Proof.MlKem.mem_compressWidths hd with rfl | rfl | rfl <;> decide
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (sepB_bounds hs) hd0
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (sepB_bounds (sepB_symm hs)) (by decide)
  have eB : Decompress.B (view s [⟨L.A i o, 32 * d⟩] [polyRegion (L.A j o')]) = L.A i o := by
    simp only [Decompress.B, Decompress.pb, view_r0, g0, ea]
  have eF : Decompress.F (view s [⟨L.A i o, 32 * d⟩] [polyRegion (L.A j o')]) = L.A j o' := by
    simp only [Decompress.F, Decompress.pf, view_r3, g3, eb]
  have eD : Decompress.dd (view s [⟨L.A i o, 32 * d⟩] [polyRegion (L.A j o')]) = d := by
    simp only [Decompress.dd, view_r2, g2, toNat_ofNat32 d1]
  have eL : Decompress.len (view s [⟨L.A i o, 32 * d⟩] [polyRegion (L.A j o')]) = 32 * d := by
    simp only [Decompress.len, view_r1, g1, toNat_ofNat32 d2]
  have cw : Covers [polyRegion (L.A j o')] s.wr := Lay.covers wj (sepB_bounds (sepB_symm hs)).2
  refine call_kept (k := kDcm) kDcm_ok (by decide +kernel) (rd := [⟨L.A i o, 32 * d⟩])
    (wr := [polyRegion (L.A j o')])
    ⟨by simp only [Decompress.inR, eB, eL, State.withRegions_rd], by simp only [eF, State.withRegions_wr],
      by simp only [Decompress.inR, eB, eF, eL]; exact Lay.disj hL hs,
      by rw [eL]; simp only [Decompress.pb, view_r0, g0]; exact fa, by simp only [Decompress.pf, view_r3, g3]; exact fb,
      by rw [eD]; exact hd, by rw [eL, eD]⟩
    (covers_append (Lay.covers wi (sepB_bounds hs).2) (covers_wr cw)) cw fun s' hk hq => hQ s' hk ?_
  simp only [kDcm, mkK, Decompress.D, Decompress.bs, eB, eF, eL, eD, State.withRegions_mem,
    State.callEntry_mem] at hq
  exact hq

/-! ## `vg_mlkem_sample_ntt` -/

/-- What `vg_mlkem_sample_ntt` computes, with its loop bounded by 280
iterations: the return value says whether `SampleNTT` finished, and if it
did, `a` holds its result. -/
def kSample : Contract isa := mkK Sample.Pre
  (fun s₀ s => s.gpr .r0 = (if (sampleNTT 280 (Sample.B s₀)).isSome then 1 else 0) ∧
    ∀ a, sampleNTT 280 (Sample.B s₀) = some a → PolyIs s.mem (Sample.A s₀) a)
  (fun a b => a.sp = b.sp ∧ regsEq [.r0, .r1, .r2] a b ∧ Sample.B a = Sample.B b)

theorem kSample_ok : ∀ s, kSample.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.sampleNTT s t s' ∧
    abiPreserved s s' ∧ kSample.post s s' :=
  mkK_ok fun s₀ hp => WP.mono (Sample.correct hp) fun s ⟨h1, h2, h0, hc⟩ => ⟨h1, h2, by
    by_cases hl : (Sample.Ls s₀ 280).length = 256
    · have e : sampleNTT 280 (Sample.B s₀) = some (VG.Proof.MlKem.toPoly (Sample.Ls s₀ 280)) :=
        VG.Proof.MlKem.sampleNTT_of_full (Nat.le_refl _) (by rw [VG.Proof.MlKem.n_eq]; exact hl)
      refine ⟨by rw [h0, ite_eq_left hl, e]; rfl, fun a ha => ?_⟩
      rw [e, Option.some.injEq] at ha; subst ha
      exact Sample.polyAt_toPoly (by rw [VG.Proof.MlKem.n_eq]; exact hl) hc
    · have e : sampleNTT 280 (Sample.B s₀) = none :=
        VG.Proof.MlKem.sampleNTT_none (by rw [VG.Proof.MlKem.n_eq]; exact hl)
      refine ⟨by rw [h0, ite_eq_right hl, e]; rfl, fun a ha => ?_⟩
      rw [e] at ha; cases ha⟩

theorem stackUse_sample : stackUse Impl.MlKem.Arm.sampleNTT = 8 := by decide +kernel

/-- `SampleNTT` of the seed at `(i, o)` into the polynomial at `(j, o')`,
with the working space at `(k, o'')`. -/
theorem sampleL {L : Lay} {s : State} (hc : Ctx L s) {i o j o' k o'' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (g2 : s.gpr .r2 = L.ptr k + BitVec.ofNat 32 o'')
    (s_ij : sepB L.sizes (i, o, 34) (j, o', 1024) = true) (s_ik : sepB L.sizes (i, o, 34) (k, o'', 2048) = true)
    (s_jk : sepB L.sizes (j, o', 1024) (k, o'', 2048) = true) (s_i1 : sepB L.sizes (i, o, 34) (1, 0, 8) = true)
    (s_j1 : sepB L.sizes (j, o', 1024) (1, 0, 8) = true) (s_k1 : sepB L.sizes (k, o'', 2048) (1, 0, 8) = true)
    (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) (wk : L.buf k ∈ s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 1024), (k, o'', 2048), (1, 0, 8)]) s s' →
      s'.gpr .r0 = (if (sampleNTT 280 (bytesAt s.mem (L.A i o) 34)).isSome then 1 else 0) →
      (∀ a, sampleNTT 280 (bytesAt s.mem (L.A i o) 34) = some a → PolyIs s'.mem (L.A j o') a) → Q s') :
    WP isa callSample s Q := by
  have hL := hc.ok
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (sepB_bounds s_ij) (by decide)
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (sepB_bounds s_jk) (by decide)
  obtain ⟨ec, fc⟩ := Lay.ptr_ok hL (sepB_bounds (sepB_symm s_ik)) (by decide)
  let V := view s [⟨L.A i o, 34⟩] [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩]
  have eS : Sample.SEED V = L.A i o := by simp only [V, Sample.SEED, Sample.pseed, view_r0, g0, ea]
  have eA : Sample.A V = L.A j o' := by simp only [V, Sample.A, Sample.pa, view_r1, g1, eb]
  have eC : Sample.S V = L.A k o'' := by simp only [V, Sample.S, Sample.pscr, view_r2, g2, ec]
  have eb8 : below V 8 = L.R 1 0 8 := hc.bel
  have eBv : Sample.B V = bytesAt s.mem (L.A i o) 34 := by
    show bytesAt s.mem (Sample.SEED V) 34 = _
    rw [eS]
  have cw : Covers [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩] s.wr :=
    covers_cons' (Lay.covers wj (sepB_bounds s_jk).2) (covers_cons' (Lay.covers wk (sepB_bounds (sepB_symm s_ik)).2)
      covers_nil')
  have hpre : Sample.Pre V := by
    refine ⟨hc.sp8, by simp only [V, eS, State.withRegions_rd], by simp only [V, eA, eC, State.withRegions_wr],
      by rw [eS, eA]; exact Lay.disj hL s_ij, by rw [eS, eC]; exact Lay.disj hL s_ik,
      by rw [eA, eC]; exact Lay.disj hL s_jk, by rw [eb8, eS]; exact Lay.disj hL (sepB_symm s_i1),
      by rw [eb8, eA]; exact Lay.disj hL (sepB_symm s_j1), by rw [eb8, eC]; exact Lay.disj hL (sepB_symm s_k1),
      by simp only [V, Sample.pseed, view_r0, g0]; exact fa, by simp only [V, Sample.pa, view_r1, g1]; exact fb,
      by simp only [V, Sample.pscr, view_r2, g2]; exact fc⟩
  refine WP.callF (k := kSample) kSample_ok hpre (covers_append (Lay.covers wi (sepB_bounds s_ij).2) (covers_wr cw))
    cw (by rw [stackUse_sample]; exact hc.sp8) fun s' hrd hwr hsp hf hcs hq => hQ s' ⟨hcs, hsp, hrd, hwr, ?_⟩ ?_ ?_
  · rw [stackUse_sample] at hf
    have : belowA s.sp 8 = L.R 1 0 8 := hc.bel
    rw [this] at hf; exact hf
  · have h1 : s'.gpr .r0 = _ := hq.1
    rw [eBv] at h1; exact h1
  · intro a ha
    have h2 : PolyIs s'.mem (Sample.A V) a := hq.2 a (by rw [eBv]; exact ha)
    rw [eA] at h2; exact h2

end VG.Proof.MlKem.Arm
