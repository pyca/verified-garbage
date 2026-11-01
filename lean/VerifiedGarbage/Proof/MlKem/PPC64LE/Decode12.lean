module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
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
import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RunR

/-!
# ML-KEM on PPC64LE: `vg_mlkem_decode12`

One symbolic execution of the loop body for any pointers (`body_ok`); the
invariant says which coefficients of the output are written (`Inv`); the
fields reduced are those of `decode12_even` and `decode12_odd`.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.Decode12

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## The loop body -/

/-- The first field of the bytes `b₀`, `b₁`, reduced. -/
def fieldLo (b₀ b₁ : Byte) : BitVec 64 :=
  fixq (b₀.setWidth 64 + ((b₁.setWidth 64 <<< 60) >>> 52) - 3329)

/-- The second field of the bytes `b₁`, `b₂`, reduced. -/
def fieldHi (b₁ b₂ : Byte) : BitVec 64 :=
  fixq ((b₁.setWidth 64 >>> 4) + (b₂.setWidth 64 <<< 4) - 3329)

/-- What an iteration does. -/
def Step (s : State) (x y c : BitVec 64) (s' : State) : Prop :=
  s'.gpr .r3 = x + 3 ∧ s'.gpr .r4 = y + 8 ∧ s'.gpr .r5 = c - 1 ∧ s'.gpr .r8 = s.gpr .r8 ∧
    s'.mem = (s.mem.writeW y ((fieldLo (s.mem x) (s.mem (x + BitVec.ofNat 64 1))).setWidth 32)).writeW
      (y + BitVec.ofNat 64 4)
        ((fieldHi (s.mem (x + BitVec.ofNat 64 1)) (s.mem (x + BitVec.ofNat 64 2))).setWidth 32) ∧
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r

theorem body_ok {s : State} {x y c : BitVec 64} (h3 : s.gpr .r3 = x) (h4 : s.gpr .r4 = y)
    (h5 : s.gpr .r5 = c) (h8 : s.gpr .r8 = 3329)
    (i0 : InRegions (s.rd ++ s.wr) x 1) (i1 : InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 1) 1)
    (i2 : InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 2) 1)
    (o0 : InRegions s.wr y 4) (o1 : InRegions s.wr (y + BitVec.ofNat 64 4) 4)
    (hsep : ∀ (m : Mem) (v : BitVec (8 * 4)) (k : Nat), k < 3 →
      (m.write y 4 v) (x + BitVec.ofNat 64 k) = m (x + BitVec.ofNat 64 k)) :
    WP isa (.block decode12Body) s (Step s x y c) := by
  have s1 : ∀ (m : Mem) (v : BitVec 32), (m.write y 4 v) (x + 1#64) = m (x + 1#64) :=
    fun m v => hsep m v 1 (by decide)
  have s2 : ∀ (m : Mem) (v : BitVec 32), (m.write y 4 v) (x + 2#64) = m (x + 2#64) :=
    fun m v => hsep m v 2 (by decide)
  crunr [decode12Body, decode12Lo, decode12Hi, fixup, Step, fieldLo, fieldHi, fixq, h3, h4, h5, h8, i0, i1, i2,
    o0, o1, s1, s2, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append,
    List.nil_append]
  simp [Mem.writeW, setWidth_zero_append]

/-! ## The values -/

theorem byte64 (b : Byte) : (b.setWidth 64).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := b.isLt; omega_arith)

theorem lo_toNat (b₀ b₁ : Byte) : (fieldLo b₀ b₁).toNat = (b₀.toNat + 256 * (b₁.toNat % 16)) % q := by
  have h₀ := b₀.isLt
  have h₁ := b₁.isLt
  have e : (b₀.setWidth 64 + ((b₁.setWidth 64 <<< 60) >>> 52)).toNat = b₀.toNat + 256 * (b₁.toNat % 16) := by
    rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, byte64, byte64,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    omega_arith
  unfold fieldLo
  rw [fixq_subq (by rw [e, q_eq]; omega_arith), e]

theorem hi_toNat (b₁ b₂ : Byte) : (fieldHi b₁ b₂).toNat = (b₁.toNat / 16 + 16 * b₂.toNat) % q := by
  have h₁ := b₁.isLt
  have h₂ := b₂.isLt
  have e : ((b₁.setWidth 64 >>> 4) + (b₂.setWidth 64 <<< 4)).toNat = b₁.toNat / 16 + 16 * b₂.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, byte64, byte64,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    omega_arith
  unfold fieldHi
  rw [fixq_subq (by rw [e, q_eq]; omega_arith), e]

/-! ## The loop -/

section
variable (s₀ : State)

abbrev B : Addr := s₀.gpr .r3
abbrev F : Addr := s₀.gpr .r4
abbrev inR : Region := ⟨B s₀, 384⟩
abbrev D : Poly := Spec.MlKem.decode12 (bytesAt s₀.mem (B s₀) 384)

/-- The value stored in coefficient `j`. -/
def out (j : Nat) : BitVec 32 := BitVec.ofNat 32 ((D s₀)[j]!).val

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [inR s₀]
  wr : s₀.wr = [polyRegion (F s₀)]
  disj : (inR s₀).Disjoint (polyRegion (F s₀))
  fitB : (B s₀).toNat + 384 ≤ 2 ^ 64
  fitF : (F s₀).toNat + 1024 ≤ 2 ^ 64

structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = B s₀ + BitVec.ofNat 64 (3 * i)
  r4 : s.gpr .r4 = F s₀ + BitVec.ofNat 64 (8 * i)
  r5 : s.gpr .r5 = BitVec.ofNat 64 (128 - i)
  r8 : s.gpr .r8 = 3329
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [polyRegion (F s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, coeffAt s.mem (F s₀) j = if j < 2 * i then out s₀ j else coeffAt s₀.mem (F s₀) j

theorem step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 128) {s : State} (h : Inv s₀ i s) :
    WP isa (.block decode12Body) s fun s' => Inv s₀ (i + 1) s' ∧ (s'.gpr .r5 != 0) = decide (i + 1 ≠ 128) := by
  have fB := hp.fitB
  have fF := hp.fitF
  have eb : ∀ k < 3, B s₀ + BitVec.ofNat 64 (3 * i) + BitVec.ofNat 64 k = B s₀ + BitVec.ofNat 64 (3 * i + k) :=
    fun k _ => ptr_add _ _ _
  have e0 : F s₀ + BitVec.ofNat 64 (8 * i) = coeffAddr (F s₀) (2 * i) := by
    rw [show 8 * i = 4 * (2 * i) by omega_arith]
  have e1 : F s₀ + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 4 = coeffAddr (F s₀) (2 * i + 1) := by
    rw [ptr_add, show 8 * i + 4 = 4 * (2 * i + 1) by omega_arith]
  have hrw : s.rd ++ s.wr = [inR s₀, polyRegion (F s₀)] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hw : s.wr = [polyRegion (F s₀)] := by rw [h.wr, hp.wr]
  have c0 := coeff_contains (F s₀) (i := 2 * i) (by rw [n_eq]; omega_arith)
  have c1 := coeff_contains (F s₀) (i := 2 * i + 1) (by rw [n_eq]; omega_arith)
  have cb : ∀ k < 3, (inR s₀).Contains (B s₀ + BitVec.ofNat 64 (3 * i + k)) 1 :=
    fun k hk => Offset.contains_base _ (by omega_arith) (by omega_arith)
  -- The bytes read are those on entry.
  have rb : ∀ k < 3, s.mem (B s₀ + BitVec.ofNat 64 (3 * i + k)) =
      (bytesAt s₀.mem (B s₀) 384).getD (3 * i + k) 0 := fun k hk => by
    rw [bytesAt_getD _ _ (by omega_arith)]
    exact h.frame.bytes (R := inR s₀) (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj)
      (by show 384 ≤ 2 ^ 64; decide) (show 3 * i + k < 384 by omega_arith)
  have hB : (bytesAt s₀.mem (B s₀) 384).length = 384 := bytesAt_length _ _ _
  have x0 : B s₀ + BitVec.ofNat 64 (3 * i) = B s₀ + BitVec.ofNat 64 (3 * i + 0) := rfl
  refine WP.mono (body_ok h.r3 h.r4 h.r5 h.r8 ?_ ?_ ?_ ?_ ?_ ?_)
    fun s' ⟨r3, r4, r5, r8, m, rd, wr, sp, lr, pres⟩ =>
    ⟨⟨?_, ?_, ?_, r8.trans h.r8, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, lr.trans h.lr,
      fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, ?_⟩
  · rw [x0, hrw]; exact ⟨_, by simp, cb 0 (by omega_arith)⟩
  · rw [eb 1 (by omega_arith), hrw]; exact ⟨_, by simp, cb 1 (by omega_arith)⟩
  · rw [eb 2 (by omega_arith), hrw]; exact ⟨_, by simp, cb 2 (by omega_arith)⟩
  · rw [e0, hw]; exact ⟨_, by simp, c0⟩
  · rw [e1, hw]; exact ⟨_, by simp, c1⟩
  · intro m v k hk
    rw [e0, eb k hk]
    exact Mem.write_apply fun h' => hp.disj _ (cb k hk) (c0.byte h')
  · rw [r3]; exact ptr_succ _ 3 i
  · rw [r4]; exact ptr_succ _ 8 i
  · rw [r5]; exact count_sub hi
  · rw [m, e1, e0]
    exact (h.frame.writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1
  · have v0 : (fieldLo ((bytesAt s₀.mem (B s₀) 384).getD (3 * i + 0) 0)
        ((bytesAt s₀.mem (B s₀) 384).getD (3 * i + 1) 0)).setWidth 32 = out s₀ (2 * i) := by
      refine setWidth32_ofNat ?_ (by have := val_lt (D s₀)[2 * i]!; omega_arith)
      rw [lo_toNat, decode12_even _ hB hi, val_ofNat, Nat.add_zero]
    have v1 : (fieldHi ((bytesAt s₀.mem (B s₀) 384).getD (3 * i + 1) 0)
        ((bytesAt s₀.mem (B s₀) 384).getD (3 * i + 2) 0)).setWidth 32 = out s₀ (2 * i + 1) := by
      refine setWidth32_ofNat ?_ (by have := val_lt (D s₀)[2 * i + 1]!; omega_arith)
      rw [hi_toNat, decode12_odd _ hB hi, val_ofNat]
    rw [m, e1, e0, eb 1 (by omega_arith), eb 2 (by omega_arith), x0, rb 0 (by omega_arith), rb 1 (by omega_arith),
      rb 2 (by omega_arith), v0, v1, show 2 * (i + 1) = 2 * i + 1 + 1 by omega_arith]
    exact coeff_one (by omega_arith) (coeff_one (by omega_arith) h.coeff rfl) rfl
  · rw [r5, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]
    exact count_nz hi (by decide)

theorem loop_ok {s₀ : State} (hp : Pre s₀) : WP isa decode12 s₀ (Inv s₀ 128) := by
  refine WP.seq (WP.cons (exec_li (by decide)) (WP.cons (exec_li (by decide)) (wp_nil ?_)))
  refine wp_loop_nz (Inv s₀) (N := 128) (by decide) (fun i hi s h => step hp hi h) (fun _ h => h) ?_
  refine ⟨by simp [State.write], by simp [State.write], by simp [State.write], by simp [State.write], rfl, rfl,
    rfl, rfl, fun r hr => ?_, Frame.refl _ _, fun k _ => rfl⟩
  have : r ≠ .r5 ∧ r ≠ .r8 := by revert r hr; decide
  simp [State.write, this.1, this.2]

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlKem.decode12Contract PPC64LE.abi).pre s) : Pre s := by
  sig_pre [Proof.MlKem.decode12Contract, Proof.MlKem.decode12Sig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 1024⟩]

theorem verified :
    Verified PPC64LE.target Impl.MlKem.PPC64LE.decode12 (Proof.MlKem.decode12Contract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, Add.ctRegs [.r3, .r4] (fun s₁ s₂ h => ?_) (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, h⟩ := loop_ok (pre_of hs)
    refine ⟨t, s', he, ⟨h.pres, h.sp, h.lr⟩, ?_⟩
    sig_post [Proof.MlKem.decode12Contract, Proof.MlKem.decode12Sig, PPC64LE.abi, PPC64LE.argRegs]
    exact polyIs_of_coeffAt (p := F s) fun j hj => by
      rw [h.coeff j (by rw [n_eq] at hj; exact hj), ite_eq_left (by rw [n_eq] at hj; omega_arith)]; rfl
  · sig_pub [Proof.MlKem.decode12Contract, Proof.MlKem.decode12Sig, PPC64LE.abi, PPC64LE.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · sig_pub [Proof.MlKem.decode12Contract, Proof.MlKem.decode12Sig, PPC64LE.abi, PPC64LE.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.decode12Contract, Proof.MlKem.decode12Sig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlKem.PPC64LE.Decode12
