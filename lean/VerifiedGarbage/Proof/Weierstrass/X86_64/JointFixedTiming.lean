module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedEntry
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedEntryW
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldTiming
public import VerifiedGarbage.Proof.Framework.X86_64.TaintSym
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! The signed generator lookup depends only on the public digit and table address. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

/-- A signed generator lookup `p` is constant time given its digit `r8`, the scratch and the table. -/
abbrev FixedLookupCT (tsym : String) (p : Prog isa) : Prop :=
  ConstantTime isa (fun _ => True) (Taint.AgreeS [tsym] (Taint.ofRegs [.rdi,.r8])) p

abbrev FixedEntryCT (K : WinCfg) (tsym : String) : Prop :=
  FixedLookupCT tsym (Joint.fixedEntry K tsym)

abbrev FixedEntryCTW (K : WinCfg) (tsym : String) : Prop :=
  FixedLookupCT tsym (Joint.fixedEntryW K tsym)

theorem jointFixedEntry_relCT {K : WinCfg} {base T : Addr} {size x y m : Nat} [NeZero m]
    {tsym : String} {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m} {b : BitVec 8}
    (hL : Lay K.M size Sl) (hn : K.M.n=4 ∨ K.M.n=6 ∨ K.M.n=9) (hm : UnitMod m (2^(64*K.M.n)))
    (ha : 1≤nafMagnitude b) (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    (hD : ∀ v∈jacCoords K.E,Sl v) (hx : x<m) (hyy : y<m) (hOne : K.one<m)
    (hZero : K.zero∈V) (heZero : E K.zero=0) (hApart : K.zero∉jacCoords K.E)
    (hc : FixedEntryCT K tsym) :
    RelCT isa (fun s t => FieldPair K.M base size m Sl V E s t ∧
      FixedSource K.M.n base T tsym size (nafMagnitude b) x y s ∧
      FixedSource K.M.n base T tsym size (nafMagnitude b) x y t ∧
      s.gpr .r8=b.setWidth 64 ∧ t.gpr .r8=b.setWidth 64)
      (Joint.fixedEntry K tsym)
      (FieldPair K.M base size m Sl (jacCoords K.E++V) (fixedEntryEnv K m E b x y)) := by
  let P := fun s t => FieldPair K.M base size m Sl V E s t ∧
    FixedSource K.M.n base T tsym size (nafMagnitude b) x y s ∧
    FixedSource K.M.n base T tsym size (nafMagnitude b) x y t ∧
    s.gpr .r8=b.setWidth 64 ∧ t.gpr .r8=b.setWidth 64
  have hct : RelCT isa P (Joint.fixedEntry K tsym) (fun _ _ => True) := by
    intro s t _ _ _ _ ⟨p,ss,st,ds,dt⟩ es et
    refine ⟨hc _ _ _ _ _ _ trivial trivial ⟨Taint.agree_ofRegs ?_,?_⟩ es et,trivial⟩
    · intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact p.1.scr.rdi.trans p.2.scr.rdi.symm
      · exact ds.trans dt.symm
    · intro n hn
      rw [List.mem_singleton.mp hn]
      exact ss.symbol.trans st.symbol.symm
  exact (hct.wp (fun s t ⟨p,ss,st,ds,dt⟩ =>
    ⟨WP.mono (jointFixedEntry_fields_ok hL hn hm p.1 ha ds ss hy hz hD hx hyy hOne hZero heZero hApart)
       (fun _ h => h.2),
     WP.mono (jointFixedEntry_fields_ok hL hn hm p.2 ha dt st hy hz hD hx hyy hOne hZero heZero hApart)
       (fun _ h => h.2)⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem jointFixedEntryW_relCT {K : WinCfg} {base T : Addr} {size x y m : Nat} [NeZero m]
    {tsym : String} {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m} {d : BitVec 16}
    (hL : Lay K.M size Sl) (hn : K.M.n=4 ∨ K.M.n=6 ∨ K.M.n=9) (hm : UnitMod m (2^(64*K.M.n)))
    (ha : 1≤nafMagnitudeW d) (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    (hD : ∀ v∈jacCoords K.E,Sl v) (hx : x<m) (hyy : y<m) (hOne : K.one<m)
    (hZero : K.zero∈V) (heZero : E K.zero=0) (hApart : K.zero∉jacCoords K.E)
    (hc : FixedEntryCTW K tsym) :
    RelCT isa (fun s t => FieldPair K.M base size m Sl V E s t ∧
      FixedSource K.M.n base T tsym size (nafMagnitudeW d) x y s ∧
      FixedSource K.M.n base T tsym size (nafMagnitudeW d) x y t ∧
      s.gpr .r8=d.setWidth 64 ∧ t.gpr .r8=d.setWidth 64)
      (Joint.fixedEntryW K tsym)
      (FieldPair K.M base size m Sl (jacCoords K.E++V) (fixedEntryEnvW K m E d x y)) := by
  let P := fun s t => FieldPair K.M base size m Sl V E s t ∧
    FixedSource K.M.n base T tsym size (nafMagnitudeW d) x y s ∧
    FixedSource K.M.n base T tsym size (nafMagnitudeW d) x y t ∧
    s.gpr .r8=d.setWidth 64 ∧ t.gpr .r8=d.setWidth 64
  have hct : RelCT isa P (Joint.fixedEntryW K tsym) (fun _ _ => True) := by
    intro s t _ _ _ _ ⟨p,ss,st,ds,dt⟩ es et
    refine ⟨hc _ _ _ _ _ _ trivial trivial ⟨Taint.agree_ofRegs ?_,?_⟩ es et,trivial⟩
    · intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact p.1.scr.rdi.trans p.2.scr.rdi.symm
      · exact ds.trans dt.symm
    · intro n hn
      rw [List.mem_singleton.mp hn]
      exact ss.symbol.trans st.symbol.symm
  exact (hct.wp (fun s t ⟨p,ss,st,ds,dt⟩ =>
    ⟨WP.mono (jointFixedEntryW_fields_ok hL hn hm p.1 ha ds ss hy hz hD hx hyy hOne hZero heZero hApart)
       (fun _ h => h.2),
     WP.mono (jointFixedEntryW_fields_ok hL hn hm p.2 ha dt st hy hz hD hx hyy hOne hZero heZero hApart)
       (fun _ h => h.2)⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

end VG.Proof.Weierstrass.X86_64
