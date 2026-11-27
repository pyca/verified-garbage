module

public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideStep
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParsePublic
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideStep
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParsePublic
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejParser
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.TaintSumGeneric
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejParser
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.TaintSumGeneric
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sums
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.RegSet
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet

/-! ### `MlDsa.AArch64.Optimized.ResidentRejChoiceTiming`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def choicePublic (vs : List VReg) : VectorTaint.T :=
  (Taint.ofRegs [.x3,.x4,.x6,.x9],RegSet.ofList vs)

theorem fourChoice_ct : ConstantTime isa (fun _ => True)
    (VectorTaint.Agree (choicePublic [.v1]))
    (.ite (.zero .x .x6) (.block vectorAccept) (.block vectorReject)) :=
  VG.Taint.constantTime (A := VectorTaint.taint) (choicePublic [.v1])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem wideChoice_ct : ConstantTime isa (fun _ => True)
    (VectorTaint.Agree (choicePublic [.v16,.v17,.v18,.v19]))
    (.ite (.zero .x .x6) (.block wideAccept) (.block wideReject)) :=
  VG.Taint.constantTime (A := VectorTaint.taint) (choicePublic [.v16,.v17,.v18,.v19])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem vectorTry_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x2])) (.block vectorTry) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x2])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem wideTry_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x2])) (.block wideTry) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x2])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

end

/-! ### `MlDsa.AArch64.Optimized.ResidentRejProbePublic`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def CandidatesEq (s t : State) (n : Nat) : Prop :=
  ∀j<n,candidate s.mem (s.gpr .x2+BitVec.ofNat 64 (3*j))=
    candidate t.mem (t.gpr .x2+BitVec.ofNat 64 (3*j))

theorem vector_eq_of_words {a b : BitVec 128}
    (h : ∀e<4,vword a e=vword b e) : a=b := by
  rw [← VG.AArch64.ofVWords_vword a,← VG.AArch64.ofVWords_vword b]
  rw [h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide)]

theorem quarterValues_eq {s t : State} (hs : Constants s) (ht : Constants t)
    (he : CandidatesEq s t 16) {j : Nat} (hj : j<4) : quarterValues s j=quarterValues t j := by
  apply vector_eq_of_words
  intro e he4
  apply BitVec.eq_of_toNat_eq
  unfold quarterValues
  rw [candidates_word _ _ _ he4 (hs.mask e he4),candidates_word _ _ _ he4 (ht.mask e he4),
    Offset.add_add,Offset.add_add]
  rw [show 12*j+3*e=3*(4*j+e) by omega_using []]
  exact he _ (by omega_using [hj, he4])

theorem quarterMask_eq {s t : State} (hs : Constants s) (ht : Constants t)
    (he : CandidatesEq s t 16) : quarterMask (wideInitial s) 4=quarterMask (wideInitial t) 4 := by
  apply vector_eq_of_words
  intro e he4
  rw [quarterMask_word hs 4 he4,quarterMask_word ht 4 he4]
  congr 1
  apply propext
  have eqc (j : Nat) (hj : j<4) :
      candidate s.mem (s.gpr .x2+BitVec.ofNat 64 (12*j+3*e))=
      candidate t.mem (t.gpr .x2+BitVec.ofNat 64 (12*j+3*e)) := by
    rw [show 12*j+3*e=3*(4*j+e) by omega_using []]
    exact he _ (by omega_using [he4, hj])
  exact ⟨fun h j hj => by rw [← eqc j hj]; exact h j hj,
    fun h j hj => by rw [eqc j hj]; exact h j hj⟩

theorem fourDecoded_eq {s t : State} (hs : Constants s) (ht : Constants t)
    (he : CandidatesEq s t 4) :
    candidates (s.mem.read (s.gpr .x2) 16) (s.v .v4)=
    candidates (t.mem.read (t.gpr .x2) 16) (t.v .v4) := by
  apply vector_eq_of_words
  intro e he4
  apply BitVec.eq_of_toNat_eq
  rw [candidates_word _ _ _ he4 (hs.mask e he4),candidates_word _ _ _ he4 (ht.mask e he4)]
  exact he e he4

theorem modulusVector_eq {s t : State} (hs : Constants s) (ht : Constants t) : s.v .v5=t.v .v5 := by
  apply vector_eq_of_words
  intro e he
  rw [hs.modulus e he,ht.modulus e he]

theorem InputEq.candidate {σ τ : State} {b : Addr} {n j : Nat}
    (h : InputEq σ τ b n) (hj : j<n) :
    candidate σ.mem (b+BitVec.ofNat 64 (3*j))=candidate τ.mem (b+BitVec.ofNat 64 (3*j)) := by
  unfold ResidentRej.candidate
  have h1 : b+BitVec.ofNat 64 (3*j)+1=b+BitVec.ofNat 64 (3*j+1) := by bv_omega_arith
  have h2 : b+BitVec.ofNat 64 (3*j)+2=b+BitVec.ofNat 64 (3*j+2) := by bv_omega_arith
  rw [h1,h2,h _ (by omega_using [hj]),h _ (by omega_using [hj]),h _ (by omega_using [hj])]

theorem ParseInv.candidates_eq {σ τ s t : State} {b p : Addr} {n d k : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (he : InputEq σ τ b n) (ps : ParseInv σ b p n L d s) (pt : ParseInv τ b p n L d t)
    (hk : d+k≤n) : CandidatesEq s t k := by
  intro j hj
  rw [ps.candidate hs (by omega_using [hk, hj]),pt.candidate ht (by omega_using [hk, hj])]
  exact he.candidate (by omega_using [hk, hj])

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

end

/-! ## From `ResidentRejFourTiming.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def FourPublic (s t : State) : Prop :=
  Constants s ∧ Constants t ∧ CandidatesEq s t 4 ∧
  InRegions (s.rd++s.wr) (s.gpr .x2) 16 ∧ InRegions (t.rd++t.wr) (t.gpr .x2) 16 ∧
  VG.AArch64.Taint.Agree (Taint.ofRegs [.x2,.x3,.x4,.x9]) s t

theorem fourStep_relCT : RelCT isa FourPublic
    (.seq (.block vectorTry) (.ite (.zero .x .x6) (.block vectorAccept) (.block vectorReject)))
    (fun _ _ => True) := by
  intro s t tr ur s' t' hp es et
  obtain ⟨cs,ct,hcand,rs,rt,hpub⟩ := hp
  cases es with
  | seq ep ec =>
    cases et with
    | seq fp fc =>
      have hx (r : Reg) (hr : r∈[Reg.x2,.x3,.x4,.x9]) : s.gpr r=t.gpr r :=
        hpub.2 r (by simpa only [Taint.ofRegs,RegSet.mem_ofList] using hr)
      have htr := vectorTry_ct _ _ _ _ _ _ trivial trivial
        ⟨hpub.1,fun r hr => hx r (by
          simp only [Taint.ofRegs,RegSet.mem_ofList,List.mem_singleton] at hr
          subst r; simp)⟩ ep fp
      obtain ⟨_,a,ea,ha,ma,va,da,fa⟩ := vectorTry_ok rs cs.index
      obtain ⟨_,b,eb,hb,mb,vb,db,fb⟩ := vectorTry_ok rt ct.index
      have hd := fourDecoded_eq cs ct hcand
      have hf : a.gpr .x6=b.gpr .x6 := by
        rw [fa,fb,hd,modulusVector_eq cs ct,cs.ones,ct.ones]
      obtain ⟨_,rfl⟩ := Exec.det ep ea
      obtain ⟨_,rfl⟩ := Exec.det fp eb
      have hc := fourChoice_ct _ _ _ _ _ _ trivial trivial ?_ ec fc
      · exact ⟨by rw [htr,hc],trivial⟩
      · refine ⟨⟨ha.sp.trans (hpub.1.trans hb.sp.symm),?_⟩,?_⟩
        · intro r hr
          simp only [choicePublic,Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · rw [ha.get .x3,hb.get .x3]; exact hx .x3 (by simp)
          · rw [ha.get .x4,hb.get .x4]; exact hx .x4 (by simp)
          · exact hf
          · rw [ha.get .x9,hb.get .x9]; exact hx .x9 (by simp)
        · intro v hv
          simp only [choicePublic,RegSet.mem_ofList,List.mem_singleton] at hv
          subst v
          rw [da,db,hd]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejWideTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def WidePublic (s t : State) : Prop :=
  Constants s ∧ Constants t ∧ CandidatesEq s t 16 ∧
  (∀j<4,InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (12*j)) 16) ∧
  (∀j<4,InRegions (t.rd++t.wr) (t.gpr .x2+BitVec.ofNat 64 (12*j)) 16) ∧
  VG.AArch64.Taint.Agree (Taint.ofRegs [.x2,.x3,.x4,.x9]) s t

theorem wideStep_relCT : RelCT isa WidePublic
    (.seq (.block wideTry) (.ite (.zero .x .x6) (.block wideAccept) (.block wideReject)))
    (fun _ _ => True) := by
  intro s t tr ur s' t' hp es et
  obtain ⟨cs,ct,hcand,rs,rt,hpub⟩ := hp
  cases es with
  | seq ep ec =>
    cases et with
    | seq fp fc =>
      have hx (r : Reg) (hr : r∈[Reg.x2,.x3,.x4,.x9]) : s.gpr r=t.gpr r :=
        hpub.2 r (by simpa only [Taint.ofRegs,RegSet.mem_ofList] using hr)
      have htr := wideTry_ct _ _ _ _ _ _ trivial trivial
        ⟨hpub.1,fun r hr => hx r (by
          simp only [Taint.ofRegs,RegSet.mem_ofList,List.mem_singleton] at hr
          subst r; simp)⟩ ep fp
      obtain ⟨_,a,ea,haf,da,fa⟩ := wideTry_ok cs.index rs
      have ha := haf.only
      obtain ⟨_,b,eb,hbf,db,fb⟩ := wideTry_ok ct.index rt
      have hb := hbf.only
      have hd := quarterMask_eq cs ct hcand
      have hf : a.gpr .x6=b.gpr .x6 := by
        rw [fa,fb,hd,cs.ones,ct.ones]
      obtain ⟨_,rfl⟩ := Exec.det ep ea
      obtain ⟨_,rfl⟩ := Exec.det fp eb
      have hc := wideChoice_ct _ _ _ _ _ _ trivial trivial ?_ ec fc
      · exact ⟨by rw [htr,hc],trivial⟩
      · refine ⟨⟨ha.sp.trans (hpub.1.trans hb.sp.symm),?_⟩,?_⟩
        · intro r hr
          simp only [choicePublic,Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · rw [ha.get .x3,hb.get .x3]; exact hx .x3 (by simp)
          · rw [ha.get .x4,hb.get .x4]; exact hx .x4 (by simp)
          · exact hf
          · rw [ha.get .x9,hb.get .x9]; exact hx .x9 (by simp)
        · intro v hv
          simp only [choicePublic,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false] at hv
          have hh (j : Nat) (hj : j<4) := (da j hj).trans ((quarterValues_eq cs ct hcand hj).trans (db j hj).symm)
          rcases hv with rfl | rfl | rfl | rfl
          · exact hh 0 (by decide)
          · exact hh 1 (by decide)
          · exact hh 2 (by decide)
          · exact hh 3 (by decide)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejBodyTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

private theorem keep_sp {P : State → State → Prop} {c : Prog isa}
    (h : RelCT isa P c (fun _ _ => True)) (hp : ∀s t,P s t → s.sp=t.sp) :
    RelCT isa P c (fun s t => s.sp=t.sp) := by
  intro s t tr ur s' t' hab es et
  exact ⟨(h _ _ _ _ _ _ hab es et).1,(AArch64.Exec.sp es).trans ((hp _ _ hab).trans (AArch64.Exec.sp et).symm)⟩

theorem fourBody_relCT : RelCT isa FourPublic vectorBody (fun _ _ => True) := by
  unfold vectorBody
  apply RelCT.assoc
  apply RelCT.seq (keep_sp fourStep_relCT (fun _ _ h => h.2.2.2.2.2.1))
  exact RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ h => ⟨h,by simp [Taint.ofRegs,RegSet.mem_ofList]⟩) (by taint_decide)

theorem wideBody_relCT : RelCT isa WidePublic wideBody (fun _ _ => True) := by
  unfold wideBody
  apply RelCT.assoc
  apply RelCT.seq (keep_sp wideStep_relCT (fun _ _ h => h.2.2.2.2.2.1))
  exact RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ h => ⟨h,by simp [Taint.ofRegs,RegSet.mem_ofList]⟩) (by taint_decide)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end
