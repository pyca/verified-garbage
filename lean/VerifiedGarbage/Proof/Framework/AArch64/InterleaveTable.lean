module

public import VerifiedGarbage.Proof.Framework.AArch64.Interleave
public import VerifiedGarbage.Proof.Framework.Interleave

/-!
# AArch64: interleaving scalar code with loads from a table

`Interleave.lean`'s class reads memory at a second base only as "memory at
any address", independent only of code that stores nothing. Here a block of
scalar code (`scalOk`: of the class, no vector registers, its stores within
the `W` bytes at `xb`, writing neither `xb` nor the table's base `xt`)
commutes with a block of AdvSIMD operations that read no general register
and 16-byte loads from the `T` bytes at `xt` (`vecOk`), from states where
those `T` bytes are apart from the `W` at `xb` (`TabApart`), which both keep:
the scalar code writes no vector register and none of the table's bytes, and
the vector code writes vector registers only (`indeps_tab`).
-/

@[expose] public section

namespace VG.AArch64.Interleave

open VG

/-- The `T` bytes at `xt` are apart from the `W` bytes at `xb`. -/
def TabApart (xb xt : Reg) (W T : Nat) (s : State) : Prop :=
  ∀ o < W, ∀ o' < T, s.gpr xb + BitVec.ofNat 64 o ≠ s.gpr xt + BitVec.ofNat 64 o'

/-- Scalar code of the class, with no vector registers, its stores within the
`W` bytes at `xb`, writing neither `xb` nor `xt`. -/
def scalOk (xb xt : Reg) (W : Nat) (i : Instr) : Bool :=
  match fp xb i with
  | some F => F.vr == 0 && F.vw == 0 && F.mw >>> W == 0 &&
      !F.gw.testBit xb.ctorIdx && !F.gw.testBit xt.ctorIdx
  | none => false

/-- An AdvSIMD operation of the class reading no general register, or a
16-byte load from the `T` bytes at `xt`. -/
def vecOk (xt : Reg) (T : Nat) : Instr → Bool
  | .vop op => match VOp.fp op with
    | some F => F.gr == 0
    | none => false
  | .ldrq _ n off => n == xt && decide (off + 16 ≤ T)
  | _ => false

/-- The vector register and value a vector instruction sets. -/
def vres (s : State) : Instr → Option (VReg × BitVec 128)
  | .vop op => op.eval s
  | .ldrq t n off => (addr s 16 n off).bind fun a => (s.load a 16).map fun x => (t, x)
  | _ => none

theorem exec_vres {xt : Reg} {T : Nat} {y : Instr} (hy : vecOk xt T y = true) (s : State) :
    exec y s = (vres s y).map fun p => s.setV p.1 p.2 := by
  cases y <;> simp only [vecOk, Bool.false_eq_true] at hy
  case vop op => rfl
  case ldrq t n off =>
    simp only [exec, vres, Option.map_bind]
    congr 1
    funext a
    rw [Function.comp_apply, Option.map_map]
    rfl

/-- What scalar code of `scalOk` keeps. -/
structure ScalKeeps (xb xt : Reg) (W : Nat) (s s' : State) : Prop where
  v : s'.v = s.v
  hxb : s'.gpr xb = s.gpr xb
  hxt : s'.gpr xt = s.gpr xt
  mem : ∀ z, (∀ o < W, z ≠ s.gpr xb + BitVec.ofNat 64 o) → s'.mem z = s.mem z
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem scalOk_fp {xb xt : Reg} {W : Nat} {i : Instr} (h : scalOk xb xt W i = true) :
    ∃ F, fp xb i = some F ∧ F.vr = 0 ∧ F.vw = 0 ∧ F.mw >>> W = 0 ∧
      F.gw.testBit xb.ctorIdx = false ∧ F.gw.testBit xt.ctorIdx = false := by
  unfold scalOk at h
  cases e : fp xb i with
  | none => rw [e] at h; cases h
  | some F =>
    rw [e] at h
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
    exact ⟨F, rfl, h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem mw_lt {m W o : Nat} (hm : m >>> W = 0) (h : m.testBit o = true) : o < W := by
  by_contra hc
  have := Nat.testBit_shiftRight m (i := W) (j := o - W)
  rw [hm, Nat.zero_testBit, show W + (o - W) = o by omega, h] at this
  exact Bool.noConfusion this

theorem scal_keeps {xb xt : Reg} {W : Nat} {i : Instr} (h : scalOk xb xt W i = true) {s s' : State}
    (he : exec i s = some s') : ScalKeeps xb xt W s s' := by
  obtain ⟨F, hf, -, hvw, hmw, hb, ht⟩ := scalOk_fp h
  have fr := frame hf he
  exact ⟨funext fun r => fr.v r (by rw [hvw, Nat.zero_testBit]), fr.gpr _ hb, fr.gpr _ ht,
    fun z hz => fr.mem z fun o ho => hz o (mw_lt hmw ho), fr.rd, fr.wr⟩

/-- Scalar code runs alike with a vector register set, which it keeps. -/
theorem scal_setV {xb xt : Reg} {W : Nat} {i : Instr} (h : scalOk xb xt W i = true) (s : State)
    (d : VReg) (x : BitVec 128) : exec i (s.setV d x) = (exec i s).map fun u => u.setV d x := by
  obtain ⟨F, hf, hvr, hvw, -, hb, -⟩ := scalOk_fp h
  have rd : Reads xb F s (s.setV d x) :=
    { gpr := fun _ _ => rfl, v := fun r hr => by rw [hvr] at hr; simp at hr, c := fun _ => rfl,
      base := rfl, mem := fun _ _ => rfl, any := fun _ => rfl, rd := rfl, wr := rfl }
  cases e : exec i s with
  | none =>
    cases e' : exec i (s.setV d x) with
    | none => rfl
    | some t' =>
      obtain ⟨_, h', _⟩ := det hf (s.setV d x) s rd.symm t' e'
      rw [e] at h'; cases h'
  | some s' =>
    obtain ⟨t', ht, w⟩ := det hf s (s.setV d x) rd s' e
    rw [ht]
    simp only [Option.map_some, Option.some.injEq]
    have f1 := frame hf e
    have g1 := frame hf ht
    have x1 : s'.gpr xb = s.gpr xb := f1.gpr _ hb
    apply state_ext
    · funext r
      cases hF : F.gw.testBit r.ctorIdx
      · rw [g1.gpr r hF]; exact (f1.gpr r hF).symm
      · exact (w.gpr r hF).symm
    · rw [g1.sp]; exact f1.sp.symm
    · cases hc : F.cw
      · rw [g1.c hc]; exact (f1.c hc).symm
      · exact (w.c hc).symm
    · funext r
      rw [g1.v r (by rw [hvw, Nat.zero_testBit])]
      simp only [State.setV]
      split
      · rfl
      · exact (f1.v r (by rw [hvw, Nat.zero_testBit])).symm
    · funext z
      by_cases hz : ∃ o, F.mw.testBit o = true ∧ z = s.gpr xb + BitVec.ofNat 64 o
      · obtain ⟨o, ho, rfl⟩ := hz
        have := w.mem o ho
        rw [x1] at this
        exact this.symm
      · have nz : ∀ o, F.mw.testBit o = true → z ≠ s.gpr xb + BitVec.ofNat 64 o :=
          fun o ho e => hz ⟨o, ho, e⟩
        rw [g1.mem z nz]; exact (f1.mem z nz).symm
    · rw [g1.rd]; exact f1.rd.symm
    · rw [g1.wr]; exact f1.wr.symm
    · rw [g1.unknowns]; exact f1.unknowns.symm
    · rw [g1.syms]; exact f1.syms.symm

/-- What a vector instruction of `vecOk` sets is the same after scalar code
of `scalOk`, from a state where the table is apart from its stores. -/
theorem vres_keeps {xb xt : Reg} {W T : Nat} {y : Instr} (hy : vecOk xt T y = true) {s s' : State}
    (hk : ScalKeeps xb xt W s s') (ha : TabApart xb xt W T s) : vres s' y = vres s y := by
  cases y <;> simp only [vecOk, Bool.false_eq_true] at hy
  case vop op =>
    cases e : VOp.fp op with
    | none => rw [e] at hy; cases hy
    | some G =>
      rw [e] at hy
      simp only [beq_iff_eq] at hy
      have rd : Reads xb G s' s :=
        { gpr := fun r hr => by rw [hy] at hr; simp at hr, v := fun r _ => by rw [hk.v],
          c := fun hc => by
            cases op <;> simp only [VOp.fp, reduceCtorEq, Option.some.injEq] at e <;> subst e <;>
              simp [vecFp] at hc,
          base := hk.hxb, mem := fun o ho => by
            cases op <;> simp only [VOp.fp, reduceCtorEq, Option.some.injEq] at e <;> subst e <;>
              simp [vecFp] at ho,
          any := fun ha => by
            cases op <;> simp only [VOp.fp, reduceCtorEq, Option.some.injEq] at e <;> subst e <;>
              simp [vecFp] at ha,
          rd := hk.rd, wr := hk.wr }
      exact VOp.det e rd
  case ldrq t n off =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hy
    obtain ⟨rfl, hT⟩ := hy
    simp only [vres, addr, hk.hxt]
    split
    · simp only [Option.bind_some, State.load, hk.rd, hk.wr]
      split
      · congr 2
        apply read_congr
        intro k hk16
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact hk.mem _ fun o ho e => ha o ho (off + k) (by omega) e.symm
      · rfl
    · rfl

/-- Scalar code of `scalOk` and a vector instruction of `vecOk` commute from a
state where the table is apart from the scalar code's stores. -/
theorem comm_tab {xb xt : Reg} {W T : Nat} {x y : Instr} (hx : scalOk xb xt W x = true)
    (hy : vecOk xt T y = true) : VG.Interleave.CommuteOn isa (TabApart xb xt W T) x y := by
  intro s hs
  show (exec x s).bind (exec y) = (exec y s).bind (exec x)
  rw [exec_vres hy s]
  cases e : exec x s with
  | none =>
    cases ev : vres s y with
    | none => rfl
    | some p =>
      simp only [Option.bind_none, Option.map_some, Option.bind_some]
      rw [scal_setV hx, e]; rfl
  | some s' =>
    simp only [Option.bind_some]
    rw [exec_vres hy s', vres_keeps hy (scal_keeps hx e) hs]
    cases ev : vres s y with
    | none => rfl
    | some p =>
      simp only [Option.map_some, Option.bind_some]
      rw [scal_setV hx, e]; rfl

theorem scal_preserves {xb xt : Reg} {W T : Nat} {x : Instr} (hx : scalOk xb xt W x = true) :
    VG.Interleave.Preserves isa (TabApart xb xt W T) x := by
  intro s s' hs he
  have hk := scal_keeps hx he
  intro o ho o' ho'
  rw [hk.hxb, hk.hxt]
  exact hs o ho o' ho'

theorem vec_preserves {xb xt : Reg} {W T : Nat} {y : Instr} (hy : vecOk xt T y = true) :
    VG.Interleave.Preserves isa (TabApart xb xt W T) y := by
  intro s s' hs he
  change exec y s = some s' at he
  rw [exec_vres hy s] at he
  cases ev : vres s y with
  | none => rw [ev] at he; cases he
  | some p =>
    rw [ev] at he
    simp only [Option.map_some, Option.some.injEq] at he
    subst he
    exact hs

/-- A block of `scalOk` code and one of `vecOk` code are independent from the
states where the table is apart from the scalar code's stores. -/
theorem indeps_tab {xb xt : Reg} {W T : Nat} {a b : List Instr} (ha : a.all (scalOk xb xt W) = true)
    (hb : b.all (vecOk xt T) = true) : VG.Interleave.Indeps isa (TabApart xb xt W T) a b where
  left x hx := scal_preserves (List.all_eq_true.mp ha x hx)
  right y hy := vec_preserves (List.all_eq_true.mp hb y hy)
  comm x hx y hy := comm_tab (List.all_eq_true.mp ha x hx) (List.all_eq_true.mp hb y hy)

theorem merge_swap {α : Type} {c a b : List α} (h : VG.Interleave.Merge c a b) : VG.Interleave.Merge c b a := by
  induction h with
  | nil => exact .nil
  | left _ ih => exact .right ih
  | right _ ih => exact .left ih

/-- Scalar code woven with loads from the table, from a state where the table
is apart: it runs as the loads and then the scalar code. -/
theorem WP.weave_tab {xb xt : Reg} {W T : Nat} {a b : List Instr} (ha : a.all (scalOk xb xt W) = true)
    (hb : b.all (vecOk xt T) = true) {s : State} (hs : TabApart xb xt W T s) {Q : State → Prop}
    (h : WP isa (.block b) s fun t => WP isa (.block a) t Q) :
    WP isa (.block (VG.Impl.Weave.weave a b)) s Q :=
  have hi := indeps_tab ha hb
  VG.Interleave.WP.merge (merge_swap (VG.Interleave.weave_merge a b))
    ⟨hi.right, hi.left, fun y hy x hx => (hi.comm x hx y hy).symm⟩ hs (WP.block_append_iff.mpr h)

end VG.AArch64.Interleave
