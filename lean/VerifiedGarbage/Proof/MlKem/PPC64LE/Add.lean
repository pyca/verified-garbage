module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Impl.MlKem.PPC64LE.Poly
public import VerifiedGarbage.Proof.MlKem.PolyContract
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.MlKem.Arith
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.MlKem.PPC64LE.Poly
meta import VerifiedGarbage.Proof.MlKem.PolyContract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.MlKem.Arith
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RunR

/-!
# ML-KEM on PPC64LE: `vg_mlkem_add` and `vg_mlkem_sub`

One symbolic execution of each loop body, for any pointers (`addBody_ok`,
`subBody_ok`); the loop invariant says which coefficients of `f` are done
(`Inv`); the arithmetic is `fixq_add` and `fixq_sub`.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.Add

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem

/-! ## The loop bodies -/

/-- What an iteration of either loop does, but for the value stored. -/
def Step (s : State) (x y c : BitVec 64) (v : BitVec 32) (s' : State) : Prop :=
  s'.gpr .r3 = x + 4 ∧ s'.gpr .r4 = y + 4 ∧ s'.gpr .r5 = c - 1 ∧ s'.gpr .r8 = s.gpr .r8 ∧
    s'.mem = s.mem.writeW x v ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧
    ∀ r ∈ preserved, s'.gpr r = s.gpr r

section
variable {s : State} {x y c : BitVec 64} (h3 : s.gpr .r3 = x) (h4 : s.gpr .r4 = y) (h5 : s.gpr .r5 = c)
  (h8 : s.gpr .r8 = 3329)
  (ia : InRegions (s.rd ++ s.wr) x 4) (ib : InRegions (s.rd ++ s.wr) y 4) (oa : InRegions s.wr x 4)
include h3 h4 h5 h8 ia ib oa

theorem addBody_ok :
    WP isa (.block addBody) s (Step s x y c ((fixq ((s.mem.readW x 32).setWidth 64 +
      (s.mem.readW y 32).setWidth 64 - 3329)).setWidth 32)) := by
  crunr [addBody, fixup, accTail, Step, fixq, h3, h4, h5, h8, ia, ib, oa, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

theorem subBody_ok :
    WP isa (.block subBody) s (Step s x y c ((fixq ((s.mem.readW x 32).setWidth 64 -
      (s.mem.readW y 32).setWidth 64)).setWidth 32)) := by
  crunr [subBody, fixup, accTail, Step, fixq, h3, h4, h5, h8, ia, ib, oa, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev F : Addr := s₀.gpr .r3
abbrev G : Addr := s₀.gpr .r4

end

/-- The precondition of both functions. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (G s₀)]
  wr : s₀.wr = [polyRegion (F s₀)]
  disj : (polyRegion (F s₀)).Disjoint (polyRegion (G s₀))
  fitF : (F s₀).toNat + 1024 ≤ 2 ^ 64
  fitG : (G s₀).toNat + 1024 ≤ 2 ^ 64
  redF : Reduced s₀.mem (F s₀)
  redG : Reduced s₀.mem (G s₀)

/-- After `i` iterations, writing `out j` to coefficient `j`. -/
structure Inv (out : Nat → BitVec 32) (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = F s₀ + BitVec.ofNat 64 (4 * i)
  r4 : s.gpr .r4 = G s₀ + BitVec.ofNat 64 (4 * i)
  r5 : s.gpr .r5 = BitVec.ofNat 64 (256 - i)
  r8 : s.gpr .r8 = 3329
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [polyRegion (F s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, coeffAt s.mem (F s₀) j = if j < i then out j else coeffAt s₀.mem (F s₀) j

/-- One iteration, from the value the body stores. -/
theorem inv_step {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256)
    {s : State} (h : Inv out s₀ i s) {body : List Instr}
    (hb : ∀ {x y c : BitVec 64}, s.gpr .r3 = x → s.gpr .r4 = y → s.gpr .r5 = c →
      InRegions (s.rd ++ s.wr) x 4 → InRegions (s.rd ++ s.wr) y 4 → InRegions s.wr x 4 →
      WP isa (.block body) s (Step s x y c (out i))) :
    WP isa (.block body) s fun s' => Inv out s₀ (i + 1) s' ∧ (s'.gpr .r5 != 0) = decide (i + 1 ≠ 256) := by
  have cF := coeff_contains (F s₀) (i := i) hi
  have cG := coeff_contains (G s₀) (i := i) hi
  refine WP.mono (hb h.r3 h.r4 h.r5 ?_ ?_ ?_) fun s' ⟨r3, r4, r5, r8, m, rd, wr, sp, lr, pres⟩ => ⟨⟨?_, ?_, ?_,
    r8.trans h.r8, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, lr.trans h.lr,
    fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, ?_⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cF⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cG⟩
  · rw [h.wr, hp.wr]; exact ⟨_, by simp, cF⟩
  · rw [r3]; exact ptr_succ _ 4 i
  · rw [r4]; exact ptr_succ _ 4 i
  · rw [r5]; exact count_sub hi
  · rw [m]
    exact h.frame.writeW (List.mem_singleton_self _) _ cF
  · intro j hj
    rw [m, show F s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (F s₀) i from rfl, coeffAt_writeW _ _ hj hi,
      h.coeff j hj]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right hij]
      by_cases hj' : j < i
      · rw [ite_eq_left hj', ite_eq_left (by omega)]
      · rw [ite_eq_right hj', ite_eq_right (by omega)]
  · rw [r5, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]; exact count_nz hi (by decide)

/-- The whole loop. -/
theorem loop_ok {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {body : List Instr}
    (hb : ∀ i < 256, ∀ s, Inv out s₀ i s → ∀ {x y c : BitVec 64}, s.gpr .r3 = x → s.gpr .r4 = y →
      s.gpr .r5 = c → InRegions (s.rd ++ s.wr) x 4 → InRegions (s.rd ++ s.wr) y 4 →
      InRegions s.wr x 4 → WP isa (.block body) s (Step s x y c (out i))) :
    WP isa (.seq (.block [.li .r5 256, .li .r8 3329]) (.loop (.block body) (.nonzero .d .r5))) s₀
      (Inv out s₀ 256) := by
  refine WP.seq (WP.cons (exec_li (by decide)) (WP.cons (exec_li (by decide)) (wp_nil ?_)))
  refine wp_loop_nz (Inv out s₀) (N := 256) (by decide)
    (fun i hi s h => inv_step hp hi h (hb i hi s h)) (fun _ h => h) ?_
  refine ⟨by simp [State.write], by simp [State.write], by simp [State.write], by simp [State.write], rfl, rfl,
    rfl, rfl, fun r hr => ?_, Frame.refl _ _, fun j _ => rfl⟩
  have : r ≠ .r5 ∧ r ≠ .r8 := by revert r hr; decide
  simp [State.write, this.1, this.2]

/-! ## Correctness -/

/-- The value stored in coefficient `j` by `vg_mlkem_add`. -/
def addOut (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((add (polyAt s₀.mem (F s₀)) (polyAt s₀.mem (G s₀)))[j]!).val

/-- The value stored in coefficient `j` by `vg_mlkem_sub`. -/
def subOut (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((sub (polyAt s₀.mem (F s₀)) (polyAt s₀.mem (G s₀)))[j]!).val

/-- What an iteration reads: coefficient `i` of each polynomial, as on entry. -/
theorem reads {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) {s : State}
    (h : Inv out s₀ i s) {x y : BitVec 64} (h3 : s.gpr .r3 = x) (h4 : s.gpr .r4 = y) :
    s.mem.readW x 32 = coeffAt s₀.mem (F s₀) i ∧ s.mem.readW y 32 = coeffAt s₀.mem (G s₀) i := by
  rw [← h3, ← h4, h.r3, h.r4]
  refine ⟨?_, ?_⟩
  · show coeffAt s.mem (F s₀) i = _
    rw [h.coeff i hi, ite_eq_right (Nat.lt_irrefl i)]
  · show coeffAt s.mem (G s₀) i = _
    exact coeffAt_congr (bytes_frame h.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.disj.symm) (by decide)) hi

theorem add_hb {s₀ : State} (hp : Pre s₀) : ∀ i < 256, ∀ s, Inv (addOut s₀) s₀ i s →
    ∀ {x y c : BitVec 64}, s.gpr .r3 = x → s.gpr .r4 = y → s.gpr .r5 = c →
      InRegions (s.rd ++ s.wr) x 4 → InRegions (s.rd ++ s.wr) y 4 → InRegions s.wr x 4 →
      WP isa (.block addBody) s (Step s x y c (addOut s₀ i)) := by
  intro i hi s h x y c h3 h4 h5 ia ib oa
  obtain ⟨ea, eb⟩ := reads hp hi h h3 h4
  refine WP.mono (addBody_ok h3 h4 h5 h.r8 ia ib oa) fun s' hs => ?_
  rw [ea, eb] at hs
  refine (?_ : _ = addOut s₀ i) ▸ hs
  refine ofNat_val_eq ?_
  have ha := hp.redF i hi
  have hb := hp.redG i hi
  rw [BitVec.toNat_setWidth, fixq_add (by rw [toNat_setWidth64]; exact ha)
      (by rw [toNat_setWidth64]; exact hb), toNat_setWidth64, toNat_setWidth64,
    Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide : 0 < q)) (by decide : q < 2 ^ 32)),
    add_get _ _ hi, val_add', polyAt_val hp.redF hi, polyAt_val hp.redG hi]

theorem sub_hb {s₀ : State} (hp : Pre s₀) : ∀ i < 256, ∀ s, Inv (subOut s₀) s₀ i s →
    ∀ {x y c : BitVec 64}, s.gpr .r3 = x → s.gpr .r4 = y → s.gpr .r5 = c →
      InRegions (s.rd ++ s.wr) x 4 → InRegions (s.rd ++ s.wr) y 4 → InRegions s.wr x 4 →
      WP isa (.block subBody) s (Step s x y c (subOut s₀ i)) := by
  intro i hi s h x y c h3 h4 h5 ia ib oa
  obtain ⟨ea, eb⟩ := reads hp hi h h3 h4
  refine WP.mono (subBody_ok h3 h4 h5 h.r8 ia ib oa) fun s' hs => ?_
  rw [ea, eb] at hs
  refine (?_ : _ = subOut s₀ i) ▸ hs
  refine ofNat_val_eq ?_
  have ha := hp.redF i hi
  have hb := hp.redG i hi
  rw [BitVec.toNat_setWidth, fixq_sub (by rw [toNat_setWidth64]; exact ha)
      (by rw [toNat_setWidth64]; exact hb), toNat_setWidth64, toNat_setWidth64,
    Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide : 0 < q)) (by decide : q < 2 ^ 32)),
    sub_get _ _ hi, val_sub', polyAt_val hp.redF hi, polyAt_val hp.redG hi,
    Nat.add_sub_assoc (by omega)]

/-- The loop's result: `f` is `out` of each coefficient. -/
theorem polyIs_of_inv {out : Nat → BitVec 32} {s₀ s : State} {g : Poly}
    (h : Inv out s₀ 256 s) (hg : ∀ j < 256, out j = BitVec.ofNat 32 (g[j]!).val) :
    PolyIs s.mem (F s₀) g :=
  polyIs_of_coeffAt fun j hj => by rw [h.coeff j hj, ite_eq_left hj, hg j hj]

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlKem.addContract PPC64LE.abi).pre s) : Pre s := by
  sig_pre [Proof.MlKem.addContract, Proof.MlKem.accSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem pre_of_sub {s : State} (h : (Proof.MlKem.subContract PPC64LE.abi).pre s) : Pre s := by
  sig_pre [Proof.MlKem.subContract, Proof.MlKem.accSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem reduced_zero (p : Addr) : Reduced (fun _ => 0) p := fun i _ => by
  rw [coeffAt_eq]
  have : Mem.readW (fun _ => (0 : Byte)) (coeffAddr p i) 32 = 0 := by
    simp [Mem.readW, Mem.read]
  rw [this]; decide

/-- The taint analysis, with the registers `rs` public. -/
theorem ctRegs {k : Contract isa} (rs : List Reg)
    (hpub : ∀ s₁ s₂, k.pub s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hsp : ∀ s₁ s₂, k.pub s₁ s₂ → s₁.sp = s₂.sp)
    {c : Prog isa} {hc : VG.Taint.Hint VG.PPC64LE.taint.T}
    (h : (VG.PPC64LE.taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    ConstantTime isa k.pre k.pub c :=
  VG.Taint.constantTime (A := VG.PPC64LE.taint) (Taint.ofRegs rs)
    (fun s₁ s₂ _ _ hp => ⟨hsp s₁ s₂ hp, fun r hr => hpub s₁ s₂ hp r (Taint.mem_ofRegs.mp hr)⟩) h

theorem add_verified : Verified PPC64LE.target Impl.MlKem.PPC64LE.add (Proof.MlKem.addContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, ctRegs [.r3, .r4] (fun s₁ s₂ h => ?_) (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h⟩ := loop_ok hp (add_hb hp)
    refine ⟨t, s', he, ⟨h.pres, h.sp, h.lr⟩, ?_⟩
    sig_post [Proof.MlKem.addContract, Proof.MlKem.accSig, PPC64LE.abi, PPC64LE.argRegs]
    exact polyIs_of_inv h fun j _ => rfl
  · sig_pub [Proof.MlKem.addContract, Proof.MlKem.accSig, PPC64LE.abi, PPC64LE.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · sig_pub [Proof.MlKem.addContract, Proof.MlKem.accSig, PPC64LE.abi, PPC64LE.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.addContract, Proof.MlKem.accSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

theorem sub_verified : Verified PPC64LE.target Impl.MlKem.PPC64LE.sub (Proof.MlKem.subContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, ctRegs [.r3, .r4] (fun s₁ s₂ h => ?_) (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of_sub hs
    obtain ⟨t, s', he, h⟩ := loop_ok hp (sub_hb hp)
    refine ⟨t, s', he, ⟨h.pres, h.sp, h.lr⟩, ?_⟩
    sig_post [Proof.MlKem.subContract, Proof.MlKem.accSig, PPC64LE.abi, PPC64LE.argRegs]
    exact polyIs_of_inv h fun j _ => rfl
  · sig_pub [Proof.MlKem.subContract, Proof.MlKem.accSig, PPC64LE.abi, PPC64LE.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · sig_pub [Proof.MlKem.subContract, Proof.MlKem.accSig, PPC64LE.abi, PPC64LE.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.subContract, Proof.MlKem.accSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

end VG.Proof.MlKem.PPC64LE.Add
