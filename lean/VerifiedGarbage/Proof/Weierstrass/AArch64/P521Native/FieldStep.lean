module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FieldVectors
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FieldSquare
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointOps
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves
import VerifiedGarbage.Proof.Framework.Omega

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
