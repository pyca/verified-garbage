module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FieldMul
public import VerifiedGarbage.Proof.Mont.AArch64.P521Linear
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.OrdinaryUpdate
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FieldSquare
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointOps

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass

theorem field_prime_relation : fieldPrime+1=512*(2^64)^8 := by
  dsimp only [fieldPrime]
  rw [VG.Proof.Mont.AArch64.P521Square.prime_value]

theorem field_add_ok {base : Addr} {W : Nat} {s : State} {loc : Nat → Nat} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat} {o a b : Nat}
    (hs : Scr s base W) (inv : OrdinaryInv base fieldPrime loc V E caps s)
    (readA : a∈V) (readB : b∈V) (capA : caps a=1) (capB : caps b=1)
    (outFits : loc o+72≤W) (inputFits : ∀x∈V,loc x+72≤W)
    (aligned : ∀x∈o::V,loc x%8=0)
    (apart : ∀x∈V,x≠o → loc x+72≤loc o ∨ loc o+72≤loc x) :
    WP isa (.block (VG.Impl.Mont.AArch64.P521Linear.add (loc o) (loc a) (loc b))) s fun t =>
      OrdinaryInv base fieldPrime loc (o::V) (Function.update E o (E a+E b)) (Function.update caps o 1) t ∧
      Scr t base W ∧ KeepRegs (clob 9) s t ∧ Outside base (loc o) 72 s.mem t.mem := by
  have ba := inv.bound a readA
  have bb := inv.bound b readB
  rw [capA,Nat.one_mul] at ba
  rw [capB,Nat.one_mul] at bb
  refine WP.mono (P521Linear.add_ok hs outFits (inputFits a readA) (inputFits b readB)
    (aligned o (by simp)) (aligned a (by simp [readA])) (aligned b (by simp [readB]))
    field_prime_relation (by omega_arith)) fun t ⟨value,bound,k,outside⟩ => ?_
  have ni := inv.add_update readA readB outside apart
    (fun x hx => by have h:=inputFits x hx; have e:=hs.enc; omega_arith)
    (cap:=1) (by simpa only [Nat.one_mul] using bound) value
  exact ⟨ni,hs.of_keepRegs k (by decide),k,outside⟩

theorem field_sub_ok {base : Addr} {W : Nat} {s : State} {loc : Nat → Nat} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat} {o a b : Nat}
    (hs : Scr s base W) (inv : OrdinaryInv base fieldPrime loc V E caps s)
    (readA : a∈V) (readB : b∈V) (capA : caps a=1) (capB : caps b=1)
    (outFits : loc o+72≤W) (inputFits : ∀x∈V,loc x+72≤W)
    (aligned : ∀x∈o::V,loc x%8=0)
    (apart : ∀x∈V,x≠o → loc x+72≤loc o ∨ loc o+72≤loc x) :
    WP isa (.block (VG.Impl.Mont.AArch64.P521Linear.sub (loc o) (loc a) (loc b))) s fun t =>
      OrdinaryInv base fieldPrime loc (o::V) (Function.update E o (E a-E b)) (Function.update caps o 1) t ∧
      Scr t base W ∧ KeepRegs (clob 9) s t ∧ Outside base (loc o) 72 s.mem t.mem := by
  have ba := inv.bound a readA
  have bb := inv.bound b readB
  rw [capA,Nat.one_mul] at ba
  rw [capB,Nat.one_mul] at bb
  refine WP.mono (P521Linear.sub_ok hs outFits (inputFits a readA) (inputFits b readB)
    (aligned o (by simp)) (aligned a (by simp [readA])) (aligned b (by simp [readB]))
    field_prime_relation ba bb) fun t ⟨value,bound,k,outside⟩ => ?_
  have ni := inv.sub_update readA readB outside apart
    (fun x hx => by have h:=inputFits x hx; have e:=hs.enc; omega_arith)
    (cap:=1) (by simpa only [Nat.one_mul] using bound) (by omega_arith) value
  exact ⟨ni,hs.of_keepRegs k (by decide),k,outside⟩

theorem field_cms_ok {base : Addr} {W : Nat} {s : State} {loc : Nat → Nat} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat} {o a b C D : Nat}
    (coeffC : C≤16) (coeffD : D≤16) (hs : Scr s base W) (inv : OrdinaryInv base fieldPrime loc V E caps s)
    (readA : a∈V) (readB : b∈V) (capA : caps a=1) (capB : caps b=1)
    (outFits : loc o+72≤W) (inputFits : ∀x∈V,loc x+72≤W)
    (aligned : ∀x∈o::V,loc x%8=0)
    (apart : ∀x∈V,x≠o → loc x+72≤loc o ∨ loc o+72≤loc x) :
    WP isa (.block (VG.Impl.Mont.AArch64.P521Linear.cms (loc o) C (loc a) D (loc b))) s fun t =>
      OrdinaryInv base fieldPrime loc (o::V) (Function.update E o (VG.Proof.Weierstrass.Cms.smulN C (E a)-VG.Proof.Weierstrass.Cms.smulN D (E b))) (Function.update caps o 1) t ∧
      Scr t base W ∧ KeepRegs (clob 9) s t ∧ Outside base (loc o) 72 s.mem t.mem := by
  have ba := inv.bound a readA
  have bb := inv.bound b readB
  rw [capA,Nat.one_mul] at ba
  rw [capB,Nat.one_mul] at bb
  refine WP.mono (P521Linear.cms_ok hs outFits (inputFits a readA) (inputFits b readB)
    (aligned o (by simp)) (aligned a (by simp [readA])) (aligned b (by simp [readB]))
    field_prime_relation coeffC coeffD ba bb) fun t ⟨value,bound,k,outside⟩ => ?_
  have valueCanon : wordsVal t.mem base (loc o) 9=(C*wordsVal s.mem base (loc a) 9+D*(fieldPrime-wordsVal s.mem base (loc b) 9))%fieldPrime := by
    simpa only [Nat.mul_comm] using value
  have ni := inv.cms_update readA readB outside apart
    (fun x hx => by have h:=inputFits x hx; have e:=hs.enc; omega_arith)
    (cap:=1) (by simpa only [Nat.one_mul] using bound) C D (Nat.le_of_lt bb) valueCanon
  exact ⟨ni,hs.of_keepRegs k (by decide),k,outside⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Mont.AArch64

-- Structural certificates avoid expanding every limb of the scalar instruction generators.
private theorem correctStore_novec (rs : List Reg) (o : Nat) :
    ∀i∈P521Linear.correctStore rs o,vdstOf i=none := by
  induction rs generalizing o with
  | nil => simp [P521Linear.correctStore]
  | cons r rs ih =>
    rw [P521Linear.correctStore,List.forall_mem_append]
    exact ⟨by simp [st,vdstOf],ih _⟩

private theorem cmsComplement_novec (last : Bool) :
    ∀i∈P521Linear.cmsComplement last,vdstOf i=none := by
  cases last <;> simp [P521Linear.cmsComplement,vdstOf]

private theorem cmsRows_novec (rs : List Reg) (a b : Nat) :
    ∀i∈P521Linear.cmsRows rs a b,vdstOf i=none := by
  induction rs generalizing a b with
  | nil => simp [P521Linear.cmsRows]
  | cons r rs ih =>
    rw [P521Linear.cmsRows,List.forall_mem_append]
    refine ⟨?_,ih _ _⟩
    simp only [P521Linear.cmsRow,List.forall_mem_append]
    exact ⟨⟨by simp [ld,vdstOf],cmsComplement_novec _⟩,by simp [P521Linear.cmsMul,vdstOf]⟩

private theorem loads_novec (rs : List Reg) (a : Nat) :
    ∀i∈loads rs a,vdstOf i=none := by
  induction rs generalizing a with
  | nil => simp [loads]
  | cons r rs ih =>
    rw [loads,List.forall_mem_cons]
    exact ⟨rfl,ih _⟩

private theorem chain_novec (op op' : Reg → Reg → Reg → Instr)
    (first : ∀r,vdstOf (op r r .x2)=none) (rest : ∀r,vdstOf (op' r r .x2)=none)
    (rs : List Reg) (b : Nat) : ∀i∈chain op op' rs b,vdstOf i=none := by
  induction rs generalizing b op op' with
  | nil => simp [chain]
  | cons r rs ih =>
    rw [chain,List.forall_mem_append]
    refine ⟨?_,ih op' op' rest rest _⟩
    rw [List.forall_mem_cons,List.forall_mem_cons]
    exact ⟨rfl,first r,List.forall_mem_nil _⟩

private theorem canonicalStore_novec (o : Nat) :
    ∀i∈P521Linear.canonicalStore o,vdstOf i=none := by
  rw [P521Linear.canonicalStore,List.forall_mem_append]
  exact ⟨by simp [P521Linear.canonicalPrefix,vdstOf],correctStore_novec _ _⟩

 theorem field_add_novec (o a b : Nat) :
    ∀i∈P521Linear.add o a b,vdstOf i=none := by
  simp only [P521Linear.add,List.forall_mem_append]
  exact ⟨⟨⟨by simp [P521Linear.addInit,zero7,vdstOf],loads_novec _ _⟩,
    chain_novec _ _ (fun _ => rfl) (fun _ => rfl) _ _⟩,canonicalStore_novec _⟩

 theorem field_sub_novec (o a b : Nat) :
    ∀i∈P521Linear.sub o a b,vdstOf i=none := by
  simp only [P521Linear.sub,List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨by simp [zero7,vdstOf],loads_novec _ _⟩,
    chain_novec _ _ (fun _ => rfl) (fun _ => rfl) _ _⟩,correctStore_novec _ _⟩,
    by simp [vdstOf]⟩,by simp [P521Linear.maskStoreTop,st,vdstOf]⟩

 theorem field_cms_novec (o C a D b : Nat) :
    ∀i∈P521Linear.cms o C a D b,vdstOf i=none := by
  simp only [P521Linear.cms,List.forall_mem_append]
  refine ⟨⟨⟨by simp [P521Linear.cmsInit,vdstOf],cmsRows_novec _ _ _⟩,?_⟩,?_⟩
  · rw [P521Linear.cmsFold,List.forall_mem_append]
    refine ⟨by simp [P521Linear.cmsFoldPrefix,vdstOf],?_⟩
    intro i hi
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hi
    rfl
  · exact canonicalStore_novec _

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

structure FieldLayout (loc : Nat → Nat) (Sl : Nat → Prop) : Prop where
  low : ∀x,Sl x → loc x+72≤3304
  aligned : ∀x,Sl x → loc x%8=0
  apart : ∀x y,Sl x → Sl y → x≠y → loc x+72≤loc y ∨ loc y+72≤loc x

def fieldCode (loc : Nat → Nat) : PointOp → Prog isa
  | .mul o a b _ => if a=b then normalizeSquareStep (loc o) (loc a) else normalizeMulStep (loc o) (loc a) (loc b)
  | .add o a b => .block (VG.Impl.Mont.AArch64.P521Linear.add (loc o) (loc a) (loc b))
  | .sub o a b => .block (VG.Impl.Mont.AArch64.P521Linear.sub (loc o) (loc a) (loc b))
  | .cms o C a D b => .block (VG.Impl.Mont.AArch64.P521Linear.cms (loc o) C (loc a) D (loc b))

def fieldCoeffs : PointOp → Prop
  | .cms _ C _ D _ => C≤16 ∧ D≤16
  | _ => True

def fieldPublicRegs : List Reg := [.x19,.x20,.x26,.x27,.x28,.x30]

structure FieldPublic (s t : State) : Prop where
  gpr : ∀r∈fieldPublicRegs,t.gpr r=s.gpr r
  sp : t.sp=s.sp
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  v31 : t.v .v31=s.v .v31

theorem public_call {s t : State} (gp : ∀r∈preserved,t.gpr r=s.gpr r)
    (sp : t.sp=s.sp) (rd : t.rd=s.rd) (wr : t.wr=s.wr) (v : t.v .v31=s.v .v31) : FieldPublic s t :=
  ⟨fun r hr => gp r ((by decide : ∀r∈fieldPublicRegs,r∈preserved) r hr),sp,rd,wr,v⟩

theorem public_linear {s t : State} (k : KeepRegs (clob 9) s t) (v : t.v=s.v) : FieldPublic s t :=
  ⟨fun r hr => k.gpr r ((by decide : ∀r∈fieldPublicRegs,r∉clob 9) r hr),k.sp,k.rd,k.wr,congrFun v .v31⟩

theorem field_step_ok {base : Addr} {W : Nat} {s : State} {loc : Nat → Nat} {Sl : Nat → Prop}
    {V : List Nat} {E : Nat → Fin fieldPrime} (hs : Scr s base W) (hW : 4024≤W) (hMax : W≤8192)
    (layout : FieldLayout loc Sl) (inv : OrdinaryInv base fieldPrime loc V E (fun _ => 1) s)
    (live : ∀x∈V,Sl x) (op : PointOp) (slots : ∀x∈op.out::op.ins,Sl x)
    (reads : ∀x∈op.ins,x∈V) (coeff : fieldCoeffs op) :
    WP isa (fieldCode loc op) s fun t =>
      OrdinaryInv base fieldPrime loc (op.out::V) (op.run E) (fun _ => 1) t ∧ Scr t base W ∧ FieldPublic s t ∧ FieldFrame base (loc op.out) s.mem t.mem := by
  have capConst (o : Nat) : Function.update (fun _ : Nat => 1) o 1=(fun _ => 1) := by
    funext x; simp only [Function.update_apply,ite_self]
  have fit (x : Nat) (hx : Sl x) : loc x+72≤W := by have h:=layout.low x hx; omega_arith
  have fits (x : Nat) (hx : x∈V) : loc x+72≤W := fit x (live x hx)
  have scratch (x : Nat) (hx : x∈V) : loc x+72≤3952 ∨ 4016≤loc x :=
    Or.inl (by have h:=layout.low x (live x hx); omega_arith)
  have separated (o : Nat) (ho : Sl o) : ∀x∈V,x≠o → loc x+72≤loc o ∨ loc o+72≤loc x :=
    fun x hx hn => layout.apart x o (live x hx) ho hn
  have align (o : Nat) (ho : Sl o) : ∀x∈o::V,loc x%8=0 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl|hx
    · exact layout.aligned x ho
    · exact layout.aligned x (live x hx)
  cases op with
  | mul o a b weak =>
    have so := slots o (by simp [PointOp.out])
    have sa := slots a (by simp [PointOp.out,PointOp.ins])
    have sb := slots b (by simp [PointOp.out,PointOp.ins])
    have ra := reads a (by simp [PointOp.ins])
    have rb := reads b (by simp [PointOp.ins])
    by_cases same : a=b
    · subst b
      simp only [fieldCode,ite_true]
      refine WP.mono (field_square_ok hs hW hMax inv ra rfl (by have h:=layout.low o so; omega_arith)
        (by have h:=layout.low a sa; omega_arith) fits
        (fun x hx => Or.inl (by have h:=layout.low x (live x hx); change loc x+72≤3952; omega_arith))
        (separated o so)) fun t ⟨ni,nt,gp,sp,v31,rd,wr,frame⟩ => ?_
      rw [capConst] at ni
      exact ⟨ni,nt,public_call gp sp rd wr v31,frame⟩
    · simp only [fieldCode,same,ite_false]
      refine WP.mono (field_mul_ok hs (by omega_arith) inv ra rb rfl rfl (fit o so) fits scratch
        (separated o so)) fun t ⟨ni,nt,gp,sp,v31,rd,wr,frame⟩ => ?_
      rw [capConst] at ni
      exact ⟨ni,nt,public_call gp sp rd wr v31,frame⟩
  | add o a b =>
    have so := slots o (by simp [PointOp.out])
    refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (field_add_novec (loc o) (loc a) (loc b)) (field_add_ok hs inv (reads a (by simp [PointOp.ins])) (reads b (by simp [PointOp.ins]))
      rfl rfl (fit o so) fits (align o so) (separated o so))) fun t ⟨⟨ni,nt,k,outside⟩,vec⟩ => ?_
    rw [capConst] at ni
    exact ⟨ni,nt,public_linear k vec,fun x ho _ => outside x ho⟩
  | sub o a b =>
    have so := slots o (by simp [PointOp.out])
    refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (field_sub_novec (loc o) (loc a) (loc b)) (field_sub_ok hs inv (reads a (by simp [PointOp.ins])) (reads b (by simp [PointOp.ins]))
      rfl rfl (fit o so) fits (align o so) (separated o so))) fun t ⟨⟨ni,nt,k,outside⟩,vec⟩ => ?_
    rw [capConst] at ni
    exact ⟨ni,nt,public_linear k vec,fun x ho _ => outside x ho⟩
  | cms o C a D b =>
    have so := slots o (by simp [PointOp.out])
    refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (field_cms_novec (loc o) C (loc a) D (loc b)) (field_cms_ok coeff.1 coeff.2 hs inv (reads a (by simp [PointOp.ins]))
      (reads b (by simp [PointOp.ins])) rfl rfl (fit o so) fits (align o so) (separated o so))) fun t ⟨⟨ni,nt,k,outside⟩,vec⟩ => ?_
    rw [capConst] at ni
    exact ⟨ni,nt,public_linear k vec,fun x ho _ => outside x ho⟩

end VG.Proof.Weierstrass.AArch64.P521Native
