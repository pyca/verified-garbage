module
public import VerifiedGarbage.Impl.MlDsa.Arm.Sign.Sign
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Top
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract


/-!
# ML-DSA signing on ARMv7: what holds of the state between the pieces

The inputs of the function entered in `σ` (`skOf`, `muOf`, `rndOf`); what
holds of every state of it (`St`: `Top`, the layout, and the inputs where they
were), kept by each piece that writes only where `stChk` allows (`St.step`);
and polynomials in slots of the working space (`Pl`), in families of
consecutive slots (`Fam`), kept by pieces that write apart from them
(`Fam.keep`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The inputs -/

section
variable (p : Params)

/-- `sk`, `μ` and `rnd`, in the state `σ` the function is entered in. -/
abbrev skOf (σ : State) : List Byte := bytesAt σ.mem (State.addr (σ.gpr .r0)) p.skLen
abbrev muOf (σ : State) : List Byte := bytesAt σ.mem (State.addr (σ.gpr .r1)) 64
abbrev rndOf (σ : State) : List Byte := bytesAt σ.mem (State.addr (σ.gpr .r2)) 32

end

/-- The three parameter sets. -/
def Ok3 (p : Params) : Prop := p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87

/-! ## Every state -/

/-- If the kernel was given prepared polynomials (`cache ≠ 0`): they lie apart
from `sig`, `scratch` and the stack, and are where they were. -/
def CK (p : Params) (D : Nat) (σ s : State) : Prop :=
  stackArg σ 1 ≠ 0 →
    (cacheR p σ).Disjoint ⟨State.addr (σ.gpr .r3), p.sigLen⟩ ∧
    (cacheR p σ).Disjoint ⟨State.addr (stackArg σ 0), scrLen p⟩ ∧ (belowA σ.sp D).Disjoint (cacheR p σ) ∧
    cacheLen p ≤ 2 ^ 64 ∧
    bytesAt s.mem (State.addr (stackArg σ 1)) (cacheLen p) = bytesAt σ.mem (State.addr (stackArg σ 1)) (cacheLen p)

/-- What holds of every state of the function entered in `σ`. -/
structure St (p : Params) (D : Nat) (σ s : State) : Prop where
  top : Top σ s
  lay : Lay D (sgR p) (sgW p) s
  sk : bytesAt s.mem (pa s (.r4, 0)) p.skLen = skOf p σ
  mu : bytesAt s.mem (pa s (.r5, 0)) 64 = muOf σ
  rnd : bytesAt s.mem (pa s (.r6, 0)) 32 = rndOf σ
  ck : CK p D σ s

/-- A piece that writes `ws` keeps `St`. -/
def stChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  topChk (sgB p) ws && keepB (sgB p) ws (.r4, 0) p.skLen && keepB (sgB p) ws (.r5, 0) 64 &&
    keepB (sgB p) ws (.r6, 0) 32 && ws.all fun w => inB (sgW p) w.1 w.2

/-- The prepared polynomials lie apart from what the function writes. -/
theorem cacheR_disj {p : Params} {σ s : State} (d1 : (cacheR p σ).Disjoint ⟨State.addr (σ.gpr .r3), p.sigLen⟩)
    (d2 : (cacheR p σ).Disjoint ⟨State.addr (stackArg σ 0), scrLen p⟩) (ht : Top σ s) {q : Ptr} {l : Nat}
    (hw : inB (sgW p) q l = true) : (cacheR p σ).Disjoint ⟨pa s q, l⟩ := by
  obtain ⟨n, hn, hs⟩ := sub_of_inB (s := s) (rbs := []) (wbs := sgW p) (p := q) (l := l) (by simpa using hw)
  simp only [sgW, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, Prod.ext_iff] at hn
  rcases hn with ⟨e1, rfl⟩ | ⟨e1, rfl⟩
  · rw [e1, ht.regs .r7 (by decide)] at hs; exact d2.sub_right hs
  · rw [e1, ht.regs .r8 (by decide)] at hs; exact d1.sub_right hs

theorem CK.step {p : Params} {D : Nat} {σ s s' : State} (h : CK p D σ s) (ht : Top σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB D s s' ws) (hw : ∀ w ∈ ws, inB (sgW p) w.1 w.2 = true) : CK p D σ s' := by
  intro hne
  obtain ⟨d1, d2, d3, hl, hb⟩ := h hne
  refine ⟨d1, d2, d3, hl, ?_⟩
  rw [← hb]
  refine VG.Proof.MlKem.bytesAt_frame hP.frame (fun R hR => ?_) hl
  rcases List.mem_append.mp hR with hR | hR
  · obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hR
    exact cacheR_disj d1 d2 ht (hw w hw')
  · rw [List.mem_singleton] at hR; subst hR; rw [ht.sp]; exact d3.symm

theorem St.step {p : Params} {D : Nat} {σ s s' : State} (h : St p D σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB D s s' ws) (hc : stChk p ws = true) : St p D σ s' := by
  simp only [stChk, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
  exact ⟨h.top.step h.lay hP h1, h.lay.post hP (sgB_bases p), (h.lay.keepBytes hP h2).trans h.sk,
    (h.lay.keepBytes hP h3).trans h.mu, (h.lay.keepBytes hP h4).trans h.rnd, h.ck.step h.top hP h5⟩

/-! ## Polynomials in slots -/

/-- Slot `j` holds `f`. -/
abbrev Pl (s : State) (j : Nat) (f : Poly) : Prop := PolyIs s.mem (pa s (pS j)) f

/-- The `m` slots from `b` hold `f 0, …, f (m - 1)`. -/
def Fam (s : State) (b m : Nat) (f : Nat → Poly) : Prop := ∀ j < m, Pl s (b + j) (f j)

/-- The `m` slots from `b` lie apart from `ws`. -/
def famChk (bs : List (Reg × Nat)) (ws : List (Ptr × Nat)) (b m : Nat) : Bool := m == 0 || keepB bs ws (pS b) (1024 * m)

theorem famChk_one {bs : List (Reg × Nat)} {ws : List (Ptr × Nat)} {b m j : Nat} (h : famChk bs ws b m = true) (hj : j < m) :
    keepB bs ws (pS (b + j)) 1024 = true := by
  simp only [famChk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · exact absurd hj (Nat.not_lt_zero _)
  · refine keepB_sub h ?_ ?_ <;> simp only [oP] <;> omega

theorem Fam.keep {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay D rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) {b m : Nat} {f : Nat → Poly}
    (hc : famChk (rbs ++ wbs) ws b m = true) (h : Fam s b m f) : Fam s' b m f :=
  fun j hj => L.keepPoly hP (famChk_one hc hj) (h j hj)

end VG.Proof.MlDsa.Arm.Sign
