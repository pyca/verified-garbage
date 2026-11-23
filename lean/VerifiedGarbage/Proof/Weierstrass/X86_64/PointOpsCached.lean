module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.PointOps
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacField
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
public import VerifiedGarbage.Proof.Weierstrass.JacMul
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafState
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointFieldTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacAdd

/-! # Point operations as functions on x86-64: the cached addition

What every curve's table by calls (`Joint.tableCall`) needs of
`vg_<curve>_jac_add_cached`'s body (`PointOps.addCachedBody`): the slots it
reads and writes (`CachedLay`), and its timing (`addCachedBody_relCT`). -/

section

/-!
# Point operations as functions on x86-64: what the cached addition computes

`addCachedBody`'s value: `R` becomes `jacAddCached` of the values of `R`,
`E` and `E`'s cached `Z²` and `Z³` at `sel`, whatever they are, through
its branches (`CachedJac.add`): `E` copied for `R`'s `Z = 0`, `R` for
`E`'s, else the header's `H` and `r`, then the doubling or the point at
infinity for `H = 0`, else the tail.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.PointOps

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Weierstrass.X86_64.CachedJac (headN rename rename_inj head_eq tail_eq slots out)

/-- What the cached addition's body needs of the slots: those of
`CachedJac.add`'s proofs, and that its programs read only `V` (`R`, `E`
and the cached powers) or what they wrote. -/
structure CachedLay (K : WinCfg) (sel size : Nat) (Sl : Nat → Prop) (dbl : RcbSlots → Pt → Pt → List FOp := dblJMul) : Prop where
  lay : Lay K.M size Sl
  apart : RcbApart K.S K.R K.E K.D
  c2 : sel ∉ rcbW K.S K.D
  c3 : sel + 8 * K.M.n ∉ rcbW K.S K.D
  sl : ∀ x ∈ (rcbW K.S K.D ++ rcbR K.S K.R K.E) ++ [sel, sel + 8 * K.M.n], Sl x
  head : readsOk (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S K.R K.E sel)
    (jacCoords K.R ++ jacCoords K.E ++ [sel, sel + 8 * K.M.n]) = true
  tail : readsOk (jacTail K.S K.R K.E K.D) (validAfter
    (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S K.R K.E sel)
    (jacCoords K.R ++ jacCoords K.E ++ [sel, sel + 8 * K.M.n])) = true
  dbl : readsOk (dbl K.S K.R K.D) (jacCoords K.R) = true
  accum : (jacCoords K.R).Nodup
  copy : ∀ x ∈ jacCoords K.D, ∀ y ∈ jacCoords K.R, x ≠ y

section
variable {K : WinCfg} {sel : Nat} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
  {dbl : RcbSlots → Pt → Pt → List FOp}

/-- The values the cached addition reads. -/
abbrev cV (K : WinCfg) (sel : Nat) : List Nat := jacCoords K.R ++ jacCoords K.E ++ [sel, sel + 8 * K.M.n]

end

section
variable {K : WinCfg} {sel : Nat} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
  {dbl : RcbSlots → Pt → Pt → List FOp}

end
end VG.Proof.Weierstrass.X86_64.PointOps

end

end

section

/-!
# Point operations as functions on x86-64: the cached addition's timing

The cached Jacobian addition branches on the values it reads: two runs from
states whose slots `V` hold the same values `E` (`FieldPair`) leak the same
trace, as `cachedJacAdd_relCT` shows for the joint verifier, here for any
values (`CachedLay`: the program reads only `V` or what it wrote), with the
pieces' taint checks (`CachedJacChecks`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.PointOps

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

/-- A program `ops` reading `V` or what it wrote, constant time if its code is. -/
theorem programB_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay M size Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {ops : List FOp}
    (hS : ∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) {V : List Nat} (hR : readsOk ops V = true)
    {E : Nat → Fin m} (hc : ScratchCT (ForwardField.programB M ops).inline) :
    RelCT isa (FieldPair M base size m Sl V E) (ForwardField.programB M ops).inline
      (FieldPair M base size m Sl (validAfter ops V) (runOps ops E)) :=
  fieldProgram_relCT hc fun _ hi => WP.mono (ForwardField.programB_ok hL hm _ hi hS hR) fun _ ht => ht.2

theorem validAfter_sub {ops : List FOp} {V : List Nat} {o : Pt}
    (ho : ∀ x ∈ jacCoords o, x ∈ ops.map FOp.out) :
    ∀ x ∈ jacCoords o ++ V, x ∈ validAfter ops V := by
  intro x hx
  rw [mem_validAfter]
  rcases List.mem_append.mp hx with hx | hx
  · exact Or.inr (ho x hx)
  · exact Or.inl hx

section
variable {K : WinCfg} {sel : Nat} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}

/-- The cached addition into `D`, from any slots `V` holding `R`, `E` and the
selected pair: the timing needs no relation among their values. -/
theorem cachedAdd_relCT {dbl : RcbSlots → Pt → Pt → List FOp} (hL : CachedLay K sel size Sl dbl)
    (hm : UnitMod m (2 ^ (64 * K.M.n))) (hOne : K.one < m) (hc : CachedJacChecks K K.R K.E K.D sel dbl) {V : List Nat}
    {E : Nat → Fin m} (hV : ∀ x ∈ cV K sel, x ∈ V) (hds : JDblShape dbl := by exact jdblShape_dblJMul) :
    RelCT isa (FieldPair K.M base size m Sl V E)
      (Impl.Weierstrass.X86_64.CachedJac.add K K.R K.E K.D sel dbl).inline
      (fun s t => ∃ E', FieldPair K.M base size m Sl (jacCoords K.D ++ V) E' s t) := by
  obtain dW : ∀ w ∈ jacCoords K.D, w ∈ rcbW K.S K.D := by
    intro w hw; simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> simp [rcbW]
  obtain dSl : ∀ x ∈ jacCoords K.D, Sl x := fun x hx => hL.sl x (List.mem_append_left _
    (List.mem_append_left _ (dW x hx)))
  obtain rV : ∀ x ∈ jacCoords K.R, x ∈ V := fun x hx => hV x (by simp [cV, hx])
  obtain eV : ∀ x ∈ jacCoords K.E, x ∈ V := fun x hx => hV x (by simp [cV, hx])
  rw [Impl.Weierstrass.X86_64.CachedJac.add]
  apply fieldBranch_relCT hL.lay hm (rV _ (by simp [jacCoords])) hc.zeroP
  · intro _
    exact (copyPoint_relCT hL.lay dSl eV hc.copyQ).mono (fun _ _ h => h) (fun _ _ h => ⟨_, h⟩)
  intro _
  apply fieldBranch_relCT hL.lay hm (eV _ (by simp [jacCoords])) hc.zeroQ
  · intro _
    exact (copyPoint_relCT hL.lay dSl rV hc.copyP).mono (fun _ _ h => h) (fun _ _ h => ⟨_, h⟩)
  intro _
  obtain hsH : ∀ op ∈ Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S K.R K.E sel, ∀ x ∈ op.out :: op.ins, Sl x := by
    rw [CachedJac.head_eq K.M.n K.S K.R K.E K.D sel]
    exact fun op hop x hx => hL.sl x (CachedJac.slots op hop x hx)
  apply RelCT.seq (programB_relCT hL.lay hm hsH (readsOk_mono hL.head hV) hc.head)
  obtain oldV : ∀ x ∈ V, x ∈ validAfter (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S K.R K.E sel) V :=
    fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)
  obtain subV : ∀ x ∈ jacCoords K.D ++ V, x ∈ jacCoords K.D ++
      validAfter (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S K.R K.E sel) V := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (oldV x hx)
  apply fieldBranch_relCT hL.lay hm (a := K.S.t3) (by
    rw [mem_validAfter]; right; simp [Impl.Weierstrass.X86_64.CachedJac.head, FOp.out]) hc.zeroH
  · intro _
    apply fieldBranch_relCT hL.lay hm (a := K.S.t5) (by
      rw [mem_validAfter]; right; simp [Impl.Weierstrass.X86_64.CachedJac.head, FOp.out]) hc.zeroR
    · intro _
      obtain ⟨N, hN, hE⟩ := hds
      obtain he : dbl K.S K.R K.D = ofN N K.S K.R K.R K.D := hE _ _ _
      refine (programB_relCT hL.lay hm (fun op hop x hx => hL.sl x (by
          rw [he] at hop
          rcases List.mem_append.mp (ofN_slots op hop x hx) with h | h
          · exact List.mem_append_left _ (List.mem_append_left _ h)
          · exact List.mem_append_left _ (List.mem_append_right _ (rcbR_self_mem _ _ _ h))))
        (readsOk_mono hL.dbl fun x hx => oldV x (rV x hx)) hc.double).mono (fun _ _ h => h)
        (fun _ _ h => ⟨_, (h.sub (validAfter_sub fun x hx => by
          rw [he]; exact ofN_out_mem hN (by simpa [jacCoords] using hx))).sub subV⟩)
    · intro _
      exact (infinity_relCT hL.lay dSl hOne hc.infinity).mono
        (fun _ _ h => h) (fun _ _ h => ⟨_, h.sub subV⟩)
  · intro _
    refine (programB_relCT hL.lay hm (fun op hop x hx => hL.sl x (by
        rw [CachedJac.tail_eq K.M.n K.S K.R K.E K.D sel] at hop
        exact CachedJac.slots op hop x hx)) (readsOk_mono hL.tail fun x hx => by
          rw [mem_validAfter] at hx ⊢
          exact hx.imp_left (hV x)) hc.tail).mono (fun _ _ h => h)
      (fun _ _ h => ⟨_, (h.sub (validAfter_sub fun x hx => by
        simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> simp [jacTail, FOp.out])).sub subV⟩)

/-- The cached addition's body, its sum copied to `R`, from any slots `V`
holding `R`, `E` and the selected pair. -/
theorem addCachedBody_relCT {dbl : RcbSlots → Pt → Pt → List FOp} (hL : CachedLay K sel size Sl dbl)
    (hm : UnitMod m (2 ^ (64 * K.M.n))) (hOne : K.one < m)
    (hc : CachedJacChecks K K.R K.E K.D sel dbl) (hcp : ScratchCT (.block (copyPt K.M.n K.R K.D)))
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x ∈ cV K sel, x ∈ V)
    (hds : JDblShape dbl := by exact jdblShape_dblJMul) :
    RelCT isa (FieldPair K.M base size m Sl V E) (PointOps.addCachedBody K sel dbl).inline
      (fun s t => ∃ E', FieldPair K.M base size m Sl (jacCoords K.R ++ V) E' s t) := by
  rw [PointOps.addCachedBody]
  apply RelCT.seq (cachedAdd_relCT hL hm hOne hc hV hds)
  apply RelCT.exists_
  intro E'
  obtain rSl : ∀ x ∈ jacCoords K.R, Sl x := fun x hx => hL.sl x (List.mem_append_left _
    (List.mem_append_right _ (by
      simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [rcbR])))
  exact (copyPoint_relCT (E := E') hL.lay rSl (fun x hx => List.mem_append_left _ hx) hcp).mono
    (fun _ _ h => h) (fun _ _ h => ⟨_, h.sub fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (List.mem_append_right _ hx)⟩)

end

end VG.Proof.Weierstrass.X86_64.PointOps

end

end
