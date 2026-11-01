module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.AddSub
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Common
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.AddSub
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# ML-DSA on PPC64LE: `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt`

As `add` and `sub` (`AddSub.lean`), with three pointers: one symbolic
execution of each loop body, for any pointers (`mulBody_ok`,
`mulAddBody_ok`), which stores `red` of the product (plus `h[i]`); the loop
invariant says which coefficients of `h` are done (`Inv`); the arithmetic is
`red_mul` and `red_mulAdd`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Arith.Mul

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.Arith
open VG.Impl.MlKem.PPC64LE (fixup)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.PPC64LE.Arith
open VG.Proof.MlKem.PPC64LE (wp_loop_nz count_sub count_nz ptr_succ)

/-! ## The loop bodies -/

/-- What an iteration of either loop does, but for the value stored. -/
def Step (s : State) (x y z c : BitVec 64) (v : BitVec 32) (s' : State) : Prop :=
  s'.gpr .r3 = x + 4 ∧ s'.gpr .r4 = y + 4 ∧ s'.gpr .r5 = z + 4 ∧ s'.gpr .r6 = c - 1 ∧
    s'.gpr .r8 = s.gpr .r8 ∧ s'.gpr .r9 = s.gpr .r9 ∧
    s'.mem = s.mem.writeW x v ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧
    ∀ r ∈ preserved, s'.gpr r = s.gpr r

section
variable {s : State} {x y z c : BitVec 64} (h3 : s.gpr .r3 = x) (h4 : s.gpr .r4 = y) (h5 : s.gpr .r5 = z)
  (h6 : s.gpr .r6 = c) (h8 : s.gpr .r8 = M) (h9 : s.gpr .r9 = 8380417)
  (ia : InRegions (s.rd ++ s.wr) y 4) (ib : InRegions (s.rd ++ s.wr) z 4) (oa : InRegions s.wr x 4)
include h3 h4 h5 h6 h8 h9 ia ib oa

theorem mulBody_ok :
    WP isa (.block mulBody) s (Step s x y z c ((red ((s.mem.readW y 32).setWidth 64 *
      (s.mem.readW z 32).setWidth 64)).setWidth 32)) := by
  crun [mulBody, mulHead, mulTail, reduce, fixup, Step, red, bar, fixd, h3, h4, h5, h6, h8, h9, ia, ib, oa,
    preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

theorem mulAddBody_ok (ic : InRegions (s.rd ++ s.wr) x 4) :
    WP isa (.block mulAddBody) s (Step s x y z c ((red ((s.mem.readW y 32).setWidth 64 *
      (s.mem.readW z 32).setWidth 64 + (s.mem.readW x 32).setWidth 64)).setWidth 32)) := by
  crun [mulAddBody, mulHead, mulTail, reduce, fixup, Step, red, bar, fixd, h3, h4, h5, h6, h8, h9, ia, ib, oa,
    ic, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev H : Addr := s₀.gpr .r3
abbrev F : Addr := s₀.gpr .r4
abbrev G : Addr := s₀.gpr .r5

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

/-- After `i` iterations, writing `out j` to coefficient `j` of `h`. -/
structure Inv (out : Nat → BitVec 32) (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = H s₀ + BitVec.ofNat 64 (4 * i)
  r4 : s.gpr .r4 = F s₀ + BitVec.ofNat 64 (4 * i)
  r5 : s.gpr .r5 = G s₀ + BitVec.ofNat 64 (4 * i)
  r6 : s.gpr .r6 = BitVec.ofNat 64 (256 - i)
  r8 : s.gpr .r8 = M
  r9 : s.gpr .r9 = 8380417
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [polyRegion (H s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, coeffAt s.mem (H s₀) j = if j < i then out j else coeffAt s₀.mem (H s₀) j

/-- One iteration, from the value the body stores. -/
theorem inv_step {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256)
    {s : State} (h : Inv out s₀ i s) {body : List Instr}
    (hb : ∀ {x y z c : BitVec 64}, s.gpr .r3 = x → s.gpr .r4 = y → s.gpr .r5 = z → s.gpr .r6 = c →
      InRegions (s.rd ++ s.wr) x 4 → InRegions (s.rd ++ s.wr) y 4 → InRegions (s.rd ++ s.wr) z 4 →
      InRegions s.wr x 4 → WP isa (.block body) s (Step s x y z c (out i))) :
    WP isa (.block body) s fun s' => Inv out s₀ (i + 1) s' ∧ (s'.gpr .r6 != 0) = decide (i + 1 ≠ 256) := by
  have cH := coeff_contains (H s₀) (i := i) hi
  have cF := coeff_contains (F s₀) (i := i) hi
  have cG := coeff_contains (G s₀) (i := i) hi
  refine WP.mono (hb h.r3 h.r4 h.r5 h.r6 ?_ ?_ ?_ ?_)
    fun s' ⟨r3, r4, r5, r6, r8, r9, m, rd, wr, sp, lr, pres⟩ => ⟨⟨?_, ?_, ?_, ?_,
    r8.trans h.r8, r9.trans h.r9, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, lr.trans h.lr,
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
    (h : ∀ s, s.gpr .r3 = s₀.gpr .r3 → s.gpr .r4 = s₀.gpr .r4 → s.gpr .r5 = s₀.gpr .r5 →
      s.gpr .r6 = BitVec.ofNat 64 256 → s.gpr .r8 = M → s.gpr .r9 = 8380417 → s.mem = s₀.mem →
      s.rd = s₀.rd → s.wr = s₀.wr → s.sp = s₀.sp → s.lr = s₀.lr →
      (∀ r ∈ preserved, s.gpr r = s₀.gpr r) → Q s) :
    WP isa (.block (consts ++ ([.li .r6 256] : List Instr))) s₀ Q := by
  refine WP.cons exec_lis (WP.cons exec_ori (WP.cons (exec_lsl (by decide)) (WP.cons exec_ori
    (WP.cons exec_lis (WP.cons exec_ori (WP.cons (exec_li (by decide)) (wp_nil ?_)))))))
  refine h _ (by simp [State.write]) (by simp [State.write]) (by simp [State.write]) (by simp [State.write])
    ?_ ?_ rfl rfl rfl rfl rfl fun r hr => ?_
  · simp only [State.write, reduceCtorEq, ite_false, ite_true]; exact consts_r8
  · simp only [State.write, reduceCtorEq, ite_false, ite_true]; exact loadImm_val (by decide)
  · have : r ≠ .r6 ∧ r ≠ .r8 ∧ r ≠ .r9 := by revert r hr; decide
    simp [State.write, this.1, this.2.1, this.2.2]

/-- The whole loop. -/
theorem loop_ok {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {body : List Instr}
    (hb : ∀ i < 256, ∀ s, Inv out s₀ i s → ∀ {x y z c : BitVec 64}, s.gpr .r3 = x → s.gpr .r4 = y →
      s.gpr .r5 = z → s.gpr .r6 = c → InRegions (s.rd ++ s.wr) x 4 → InRegions (s.rd ++ s.wr) y 4 →
      InRegions (s.rd ++ s.wr) z 4 → InRegions s.wr x 4 → WP isa (.block body) s (Step s x y z c (out i))) :
    WP isa (.seq (.block (consts ++ ([.li .r6 256] : List Instr))) (.loop (.block body) (.nonzero .d .r6))) s₀
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
    (h : Inv out s₀ i s) {x y z : BitVec 64} (h3 : s.gpr .r3 = x) (h4 : s.gpr .r4 = y) (h5 : s.gpr .r5 = z) :
    s.mem.readW x 32 = coeffAt s₀.mem (H s₀) i ∧ s.mem.readW y 32 = coeffAt s₀.mem (F s₀) i ∧
      s.mem.readW z 32 = coeffAt s₀.mem (G s₀) i := by
  rw [← h3, ← h4, ← h5, h.r3, h.r4, h.r5]
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
    ∀ {x y z c : BitVec 64}, s.gpr .r3 = x → s.gpr .r4 = y → s.gpr .r5 = z → s.gpr .r6 = c →
      InRegions (s.rd ++ s.wr) x 4 → InRegions (s.rd ++ s.wr) y 4 → InRegions (s.rd ++ s.wr) z 4 →
      InRegions s.wr x 4 → WP isa (.block mulBody) s (Step s x y z c (mulOut s₀ i)) := by
  intro i hi s h x y z c h3 h4 h5 h6 _ ia ib oa
  obtain ⟨-, ea, eb⟩ := reads hp hi h h3 h4 h5
  refine WP.mono (mulBody_ok h3 h4 h5 h6 h.r8 h.r9 ia ib oa) fun s' hs => ?_
  rw [ea, eb, load_val hp.redF hi, load_val hp.redG hi] at hs
  refine (?_ : _ = mulOut s₀ i) ▸ hs
  refine setWidth32_ofNat ?_ (by have := val_lt ((multiplyNTT (polyAt s₀.mem (F s₀)) (polyAt s₀.mem (G s₀)))[i]!); omega)
  rw [red_mul, mul_get _ _ hi]

theorem mulAdd_hb {s₀ : State} (hp : Pre s₀) (hrH : Reduced s₀.mem (H s₀)) :
    ∀ i < 256, ∀ s, Inv (mulAddOut s₀) s₀ i s →
    ∀ {x y z c : BitVec 64}, s.gpr .r3 = x → s.gpr .r4 = y → s.gpr .r5 = z → s.gpr .r6 = c →
      InRegions (s.rd ++ s.wr) x 4 → InRegions (s.rd ++ s.wr) y 4 → InRegions (s.rd ++ s.wr) z 4 →
      InRegions s.wr x 4 → WP isa (.block mulAddBody) s (Step s x y z c (mulAddOut s₀ i)) := by
  intro i hi s h x y z c h3 h4 h5 h6 ic ia ib oa
  obtain ⟨ec, ea, eb⟩ := reads hp hi h h3 h4 h5
  refine WP.mono (mulAddBody_ok h3 h4 h5 h6 h.r8 h.r9 ia ib oa ic) fun s' hs => ?_
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

theorem pre_of {s : State} (h : (Proof.MlDsa.mulContract PPC64LE.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.mulContract, Proof.MlDsa.mulSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem pre_of_add {s : State} (h : (Proof.MlDsa.mulAddContract PPC64LE.abi).pre s) :
    Pre s ∧ Reduced s.mem (H s) := by
  sig_pre [Proof.MlDsa.mulAddContract, Proof.MlDsa.mulSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h9, h10⟩, h8⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem mul_verified : Verified PPC64LE.target mul (Proof.MlDsa.mulContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlKem.PPC64LE.Add.ctRegs [.r3, .r4, .r5] (fun s₁ s₂ h => ?_)
    (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h⟩ := loop_ok hp (mul_hb hp)
    refine ⟨t, s', he, ⟨h.pres, h.sp, h.lr⟩, ?_⟩
    sig_post [Proof.MlDsa.mulContract, Proof.MlDsa.mulSig, PPC64LE.abi, PPC64LE.argRegs]
    exact polyIs_of_inv h fun j _ => rfl
  · sig_pub [Proof.MlDsa.mulContract, Proof.MlDsa.mulSig, PPC64LE.abi, PPC64LE.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
  · sig_pub [Proof.MlDsa.mulContract, Proof.MlDsa.mulSig, PPC64LE.abi, PPC64LE.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.mulContract, Proof.MlDsa.mulSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact AddSub.reduced_zero _
        | decide +kernel

theorem mulAdd_verified : Verified PPC64LE.target mulAdd (Proof.MlDsa.mulAddContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlKem.PPC64LE.Add.ctRegs [.r3, .r4, .r5] (fun s₁ s₂ h => ?_)
    (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨hp, hrH⟩ := pre_of_add hs
    obtain ⟨t, s', he, h⟩ := loop_ok hp (mulAdd_hb hp hrH)
    refine ⟨t, s', he, ⟨h.pres, h.sp, h.lr⟩, ?_⟩
    sig_post [Proof.MlDsa.mulAddContract, Proof.MlDsa.mulSig, PPC64LE.abi, PPC64LE.argRegs]
    exact polyIs_of_inv h fun j _ => rfl
  · sig_pub [Proof.MlDsa.mulAddContract, Proof.MlDsa.mulSig, PPC64LE.abi, PPC64LE.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
  · sig_pub [Proof.MlDsa.mulAddContract, Proof.MlDsa.mulSig, PPC64LE.abi, PPC64LE.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.mulAddContract, Proof.MlDsa.mulSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact AddSub.reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.Arith.Mul
