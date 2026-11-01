module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.AddSub
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.AddSub
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Spec.MlDsa
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.RISCV64.Add
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Spec.MlDsa
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Common
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Straight
meta import VerifiedGarbage.Proof.Framework.RISCV64.Straight
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics

/-!
# ML-DSA on RISC-V: `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt`

As `add` and `sub` (`AddSub.lean`) and PPC64LE's (`Proof/MlDsa/PPC64LE/Arith/Mul.lean`),
with three pointers: one symbolic execution of each loop body, for any
pointers (`mulBody_ok`, `mulAddBody_ok`), which runs the product (plus
`h[i]`), then `reduce_ok`, then the store; the loop invariant says which
coefficients of `h` are done (`Inv`); the arithmetic is `red_mul` and
`red_mulAdd`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Arith.Mul

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Arith
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.RISCV64.Arith
open VG.Proof.MlKem.RISCV64 (wp_loop_nz count_sub count_nz ptr_succ align4_add toNat_setWidth64
  setWidth32_ofNat)

/-! ## The loop bodies -/

/-- What an iteration of either loop does, but for the value stored. -/
def Step (s : State) (x y z c : BitVec 64) (v : BitVec 32) (s' : State) : Prop :=
  s'.gpr .a0 = x + 4 ∧ s'.gpr .a1 = y + 4 ∧ s'.gpr .a2 = z + 4 ∧ s'.gpr .t1 = c - 1 ∧
    s'.gpr .a5 = s.gpr .a5 ∧ s'.gpr .a6 = s.gpr .a6 ∧
    s'.mem = s.mem.writeW x v ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .ra = s.gpr .ra ∧
    ∀ r ∈ preserved, s'.gpr r = s.gpr r

section
variable {s : State} {x y z c : BitVec 64} (h3 : s.gpr .a0 = x) (h4 : s.gpr .a1 = y) (h5 : s.gpr .a2 = z)
  (h6 : s.gpr .t1 = c) (h8 : s.gpr .a5 = 2201172575745) (h9 : s.gpr .a6 = 8380417)
  (ia : InRegions (s.rd ++ s.wr) y 4) (ib : InRegions (s.rd ++ s.wr) z 4) (oa : InRegions s.wr x 4)
  (ax : x.toNat % 4 = 0) (ay : y.toNat % 4 = 0) (az : z.toNat % 4 = 0)
include h3 h4 h5 h6 h8 h9 ia ib oa ax ay az

theorem mulBody_ok :
    WP isa (.block mulBody) s (Step s x y z c ((red ((s.mem.readW y 32).setWidth 64 *
      (s.mem.readW z 32).setWidth 64)).setWidth 32)) := by
  rw [mulBody, mulTail]
  refine WP.block_append ?_
  crun [mulHead, h4, h5, ia, ib, ay, az]
  refine reduce_ok (by decide) (by decide) (by decide) (by simp [h8]) (by simp [h9])
    fun s' k => ?_
  have g := k.other
  crun [Step, k.gpr, g, k.mem, k.rd, k.wr, k.sp, h3, h4, h5, h6, h8, h9, oa, ax, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

theorem mulAddBody_ok (ic : InRegions (s.rd ++ s.wr) x 4) :
    WP isa (.block mulAddBody) s (Step s x y z c ((red ((s.mem.readW y 32).setWidth 64 *
      (s.mem.readW z 32).setWidth 64 + (s.mem.readW x 32).setWidth 64)).setWidth 32)) := by
  rw [show mulAddBody = (mulHead ++ ([.load .w .t2 .a0 0, .add .t0 .t0 .t2] : List Instr)) ++
      (reduce .t0 .t2 ++ ([.store .w .t0 .a0 0, .addi .a0 .a0 4, .addi .a1 .a1 4, .addi .a2 .a2 4,
        .addi .t1 .t1 (-1)] : List Instr)) by simp only [mulAddBody, mulTail, List.append_assoc]]
  refine WP.block_append ?_
  crun [mulHead, h3, h4, h5, ia, ib, ic, ax, ay, az, List.cons_append, List.nil_append]
  refine reduce_ok (by decide) (by decide) (by decide) (by simp [h8]) (by simp [h9])
    fun s' k => ?_
  have g := k.other
  crun [Step, k.gpr, g, k.mem, k.rd, k.wr, k.sp, h3, h4, h5, h6, h8, h9, oa, ax, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev H : Addr := s₀.gpr .a0
abbrev F : Addr := s₀.gpr .a1
abbrev G : Addr := s₀.gpr .a2

end

/-- The precondition of both functions (`h` is reduced for `multiplyAddNTT`). -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (F s₀), polyRegion (G s₀)]
  wr : s₀.wr = [polyRegion (H s₀)]
  hf : (polyRegion (H s₀)).Disjoint (polyRegion (F s₀))
  hg : (polyRegion (H s₀)).Disjoint (polyRegion (G s₀))
  fitH : (H s₀).toNat + 1024 ≤ 2 ^ 64
  fitF : (F s₀).toNat + 1024 ≤ 2 ^ 64
  fitG : (G s₀).toNat + 1024 ≤ 2 ^ 64
  redF : Reduced s₀.mem (F s₀)
  redG : Reduced s₀.mem (G s₀)
  alH : (H s₀).toNat % 4 = 0
  alF : (F s₀).toNat % 4 = 0
  alG : (G s₀).toNat % 4 = 0

/-- After `i` iterations, writing `out j` to coefficient `j` of `h`. -/
structure Inv (out : Nat → BitVec 32) (s₀ : State) (i : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = H s₀ + BitVec.ofNat 64 (4 * i)
  a1 : s.gpr .a1 = F s₀ + BitVec.ofNat 64 (4 * i)
  a2 : s.gpr .a2 = G s₀ + BitVec.ofNat 64 (4 * i)
  t1 : s.gpr .t1 = BitVec.ofNat 64 (256 - i)
  a5 : s.gpr .a5 = 2201172575745
  a6 : s.gpr .a6 = 8380417
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  ra : s.gpr .ra = s₀.gpr .ra
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [polyRegion (H s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, coeffAt s.mem (H s₀) j = if j < i then out j else coeffAt s₀.mem (H s₀) j

/-- One iteration, from the value the body stores. -/
theorem inv_step {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256)
    {s : State} (h : Inv out s₀ i s) {body : List Instr}
    (hb : ∀ {x y z c : BitVec 64}, s.gpr .a0 = x → s.gpr .a1 = y → s.gpr .a2 = z → s.gpr .t1 = c →
      InRegions (s.rd ++ s.wr) x 4 → InRegions (s.rd ++ s.wr) y 4 → InRegions (s.rd ++ s.wr) z 4 →
      InRegions s.wr x 4 → x.toNat % 4 = 0 → y.toNat % 4 = 0 → z.toNat % 4 = 0 →
      WP isa (.block body) s (Step s x y z c (out i))) :
    WP isa (.block body) s fun s' => Inv out s₀ (i + 1) s' ∧ (s'.gpr .t1 != 0) = decide (i + 1 ≠ 256) := by
  have cH := coeff_contains (H s₀) (i := i) hi
  have cF := coeff_contains (F s₀) (i := i) hi
  have cG := coeff_contains (G s₀) (i := i) hi
  refine WP.mono (hb h.a0 h.a1 h.a2 h.t1 ?_ ?_ ?_ ?_ (align4_add hp.alH i) (align4_add hp.alF i)
    (align4_add hp.alG i))
    fun s' ⟨r3, r4, r5, r6, r8, r9, m, rd, wr, sp, lr, pres⟩ => ⟨⟨?_, ?_, ?_, ?_,
    r8.trans h.a5, r9.trans h.a6, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, lr.trans h.ra,
    fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, ?_⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cH⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cF⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cG⟩
  · rw [h.wr, hp.wr]; exact ⟨_, by simp, cH⟩
  · rw [r3]; exact ptr_succ _ 4 i
  · rw [r4]; exact ptr_succ _ 4 i
  · rw [r5]; exact ptr_succ _ 4 i
  · rw [r6]; exact count_sub hi
  · rw [m]
    exact h.frame.writeW (List.mem_singleton_self _) _ cH
  · intro j hj
    rw [m, show H s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (H s₀) i from rfl, coeffAt_writeW _ _ hj hi,
      h.coeff j hj]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right hij]
      by_cases hj' : j < i
      · rw [ite_eq_left hj', ite_eq_left (by omega)]
      · rw [ite_eq_right hj', ite_eq_right (by omega)]
  · rw [r6, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]; exact count_nz hi (by decide)

/-- `consts` and the count. -/
theorem head_ok {s₀ : State} {Q : State → Prop}
    (h : ∀ s, s.gpr .a0 = s₀.gpr .a0 → s.gpr .a1 = s₀.gpr .a1 → s.gpr .a2 = s₀.gpr .a2 →
      s.gpr .t1 = BitVec.ofNat 64 256 → s.gpr .a5 = 2201172575745 → s.gpr .a6 = 8380417 → s.mem = s₀.mem →
      s.rd = s₀.rd → s.wr = s₀.wr → s.sp = s₀.sp → s.gpr .ra = s₀.gpr .ra →
      (∀ r ∈ preserved, s.gpr r = s₀.gpr r) → Q s) :
    WP isa (.block (consts ++ ([.li .t1 256] : List Instr))) s₀ Q := by
  simp only [consts, loadM_eq, loadImm_q, List.cons_append, List.nil_append]
  crun []
  refine h _ (by simp) (by simp) (by simp) (by simp) (by simp; decide) (by simp; decide) rfl rfl rfl rfl
    (by simp) fun r hr => ?_
  have : r ≠ .t1 ∧ r ≠ .a5 ∧ r ≠ .a6 := by revert r hr; decide
  simp [this.1, this.2.1, this.2.2]

/-- The whole loop. -/
theorem loop_ok {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {body : List Instr}
    (hb : ∀ i < 256, ∀ s, Inv out s₀ i s → ∀ {x y z c : BitVec 64}, s.gpr .a0 = x → s.gpr .a1 = y →
      s.gpr .a2 = z → s.gpr .t1 = c → InRegions (s.rd ++ s.wr) x 4 → InRegions (s.rd ++ s.wr) y 4 →
      InRegions (s.rd ++ s.wr) z 4 → InRegions s.wr x 4 → x.toNat % 4 = 0 → y.toNat % 4 = 0 → z.toNat % 4 = 0 →
      WP isa (.block body) s (Step s x y z c (out i))) :
    WP isa (.seq (.block (consts ++ ([.li .t1 256] : List Instr))) (.loop (.block body) (.nonzero .t1))) s₀
      (Inv out s₀ 256) := by
  refine WP.seq (head_ok fun s r3 r4 r5 r6 r8 r9 m rd wr sp lr pres => ?_)
  refine wp_loop_nz (Inv out s₀) (N := 256) (by decide)
    (fun i hi s h => inv_step hp hi h (hb i hi s h)) (fun _ h => h) ?_
  exact ⟨by rw [r3]; simp, by rw [r4]; simp, by rw [r5]; simp, r6, r8, r9, rd, wr, sp, lr, pres,
    m ▸ Frame.refl _ _, fun j _ => by rw [m]; rfl⟩

/-! ## Correctness -/

/-- The value stored in coefficient `j` by `vg_mldsa_multiply_ntt`. -/
def mulOut (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((multiplyNTT (polyAt s₀.mem (F s₀)) (polyAt s₀.mem (G s₀)))[j]!).val

/-- The value stored in coefficient `j` by `vg_mldsa_multiply_add_ntt`. -/
def mulAddOut (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((add (polyAt s₀.mem (H s₀)) (multiplyNTT (polyAt s₀.mem (F s₀)) (polyAt s₀.mem (G s₀))))[j]!).val

/-- What an iteration reads: coefficient `i` of each polynomial, as on entry. -/
theorem reads {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) {s : State}
    (h : Inv out s₀ i s) {x y z : BitVec 64} (h3 : s.gpr .a0 = x) (h4 : s.gpr .a1 = y) (h5 : s.gpr .a2 = z) :
    s.mem.readW x 32 = coeffAt s₀.mem (H s₀) i ∧ s.mem.readW y 32 = coeffAt s₀.mem (F s₀) i ∧
      s.mem.readW z 32 = coeffAt s₀.mem (G s₀) i := by
  rw [← h3, ← h4, ← h5, h.a0, h.a1, h.a2]
  refine ⟨?_, ?_, ?_⟩
  · show coeffAt s.mem (H s₀) i = _
    rw [h.coeff i hi, ite_eq_right (Nat.lt_irrefl i)]
  · show coeffAt s.mem (F s₀) i = _
    exact coeffAt_congr (bytes_frame h.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.hf.symm) (by decide)) hi
  · show coeffAt s.mem (G s₀) i = _
    exact coeffAt_congr (bytes_frame h.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.hg.symm) (by decide)) hi

/-- A reduced coefficient, as loaded. -/
theorem load_val {m : Mem} {p : Addr} (hr : Reduced m p) {i : Nat} (hi : i < n) :
    (coeffAt m p i).setWidth 64 = BitVec.ofNat 64 ((polyAt m p)[i]!).val := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_setWidth64, polyAt_val hr hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hr i hi; omega)]

theorem mul_hb {s₀ : State} (hp : Pre s₀) : ∀ i < 256, ∀ s, Inv (mulOut s₀) s₀ i s →
    ∀ {x y z c : BitVec 64}, s.gpr .a0 = x → s.gpr .a1 = y → s.gpr .a2 = z → s.gpr .t1 = c →
      InRegions (s.rd ++ s.wr) x 4 → InRegions (s.rd ++ s.wr) y 4 → InRegions (s.rd ++ s.wr) z 4 →
      InRegions s.wr x 4 → x.toNat % 4 = 0 → y.toNat % 4 = 0 → z.toNat % 4 = 0 →
      WP isa (.block mulBody) s (Step s x y z c (mulOut s₀ i)) := by
  intro i hi s h x y z c h3 h4 h5 h6 _ ia ib oa ax ay az
  obtain ⟨-, ea, eb⟩ := reads hp hi h h3 h4 h5
  refine WP.mono (mulBody_ok h3 h4 h5 h6 h.a5 h.a6 ia ib oa ax ay az) fun s' hs => ?_
  rw [ea, eb, load_val hp.redF hi, load_val hp.redG hi] at hs
  refine (?_ : _ = mulOut s₀ i) ▸ hs
  refine setWidth32_ofNat ?_ (by have := val_lt ((multiplyNTT (polyAt s₀.mem (F s₀)) (polyAt s₀.mem (G s₀)))[i]!); omega)
  rw [red_mul, mul_get _ _ hi]

theorem mulAdd_hb {s₀ : State} (hp : Pre s₀) (hrH : Reduced s₀.mem (H s₀)) :
    ∀ i < 256, ∀ s, Inv (mulAddOut s₀) s₀ i s →
    ∀ {x y z c : BitVec 64}, s.gpr .a0 = x → s.gpr .a1 = y → s.gpr .a2 = z → s.gpr .t1 = c →
      InRegions (s.rd ++ s.wr) x 4 → InRegions (s.rd ++ s.wr) y 4 → InRegions (s.rd ++ s.wr) z 4 →
      InRegions s.wr x 4 → x.toNat % 4 = 0 → y.toNat % 4 = 0 → z.toNat % 4 = 0 →
      WP isa (.block mulAddBody) s (Step s x y z c (mulAddOut s₀ i)) := by
  intro i hi s h x y z c h3 h4 h5 h6 ic ia ib oa ax ay az
  obtain ⟨ec, ea, eb⟩ := reads hp hi h h3 h4 h5
  refine WP.mono (mulAddBody_ok h3 h4 h5 h6 h.a5 h.a6 ia ib oa ax ay az ic) fun s' hs => ?_
  rw [ea, eb, ec, load_val hp.redF hi, load_val hp.redG hi, load_val hrH hi] at hs
  refine (?_ : _ = mulAddOut s₀ i) ▸ hs
  refine setWidth32_ofNat ?_ (by
    have := val_lt ((add (polyAt s₀.mem (H s₀)) (multiplyNTT (polyAt s₀.mem (F s₀)) (polyAt s₀.mem (G s₀))))[i]!)
    omega)
  rw [red_mulAdd, add_get _ _ hi, mul_get _ _ hi]

/-- The loop's result: `h` is `out` of each coefficient. -/
theorem polyIs_of_inv {out : Nat → BitVec 32} {s₀ s : State} {g : Poly}
    (h : Inv out s₀ 256 s) (hg : ∀ j < 256, out j = BitVec.ofNat 32 (g[j]!).val) :
    PolyIs s.mem (H s₀) g :=
  polyIs_of_toNat fun j hj => by
    rw [h.coeff j hj, ite_eq_left hj, hg j hj, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := val_lt g[j]!; omega)]

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlDsa.mulContract RISCV64.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.mulContract, Proof.MlDsa.mulSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem pre_of_add {s : State} (h : (Proof.MlDsa.mulAddContract RISCV64.abi).pre s) :
    Pre s ∧ Reduced s.mem (H s) := by
  sig_pre [Proof.MlDsa.mulAddContract, Proof.MlDsa.mulSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h9, h10, h11, h12, h13⟩, h8⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem mul_verified : Verified RISCV64.target mul (Proof.MlDsa.mulContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlKem.RISCV64.Add.ctRegs [.a0, .a1, .a2] (fun s₁ s₂ h => ?_)
    (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h⟩ := loop_ok hp (mul_hb hp)
    refine ⟨t, s', he, ⟨h.pres, h.sp, h.ra⟩, ?_⟩
    sig_post [Proof.MlDsa.mulContract, Proof.MlDsa.mulSig, RISCV64.abi, RISCV64.argRegs]
    exact polyIs_of_inv h fun j _ => rfl
  · sig_pub [Proof.MlDsa.mulContract, Proof.MlDsa.mulSig, RISCV64.abi, RISCV64.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
  · sig_pub [Proof.MlDsa.mulContract, Proof.MlDsa.mulSig, RISCV64.abi, RISCV64.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.mulContract, Proof.MlDsa.mulSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact AddSub.reduced_zero _
        | decide +kernel

theorem mulAdd_verified : Verified RISCV64.target mulAdd (Proof.MlDsa.mulAddContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlKem.RISCV64.Add.ctRegs [.a0, .a1, .a2] (fun s₁ s₂ h => ?_)
    (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨hp, hrH⟩ := pre_of_add hs
    obtain ⟨t, s', he, h⟩ := loop_ok hp (mulAdd_hb hp hrH)
    refine ⟨t, s', he, ⟨h.pres, h.sp, h.ra⟩, ?_⟩
    sig_post [Proof.MlDsa.mulAddContract, Proof.MlDsa.mulSig, RISCV64.abi, RISCV64.argRegs]
    exact polyIs_of_inv h fun j _ => rfl
  · sig_pub [Proof.MlDsa.mulAddContract, Proof.MlDsa.mulSig, RISCV64.abi, RISCV64.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
  · sig_pub [Proof.MlDsa.mulAddContract, Proof.MlDsa.mulSig, RISCV64.abi, RISCV64.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.mulAddContract, Proof.MlDsa.mulSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact AddSub.reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Arith.Mul
