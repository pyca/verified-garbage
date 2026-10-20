module
public import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Framework.Contract


/-! # Output pointers and permissions survive fixed word copies -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64

theorem squeeze_ne : ∀r∈preserved,r∉[Reg.x2,.x9] := by decide

theorem hsetup_copy {s t : State} {sc : Reg} {st wk rate : Nat}
    (h : HSetup sc st wk rate s) (k : Keep [.x2,.x9] s t) : HSetup sc st wk rate t := by
  have eq := k.get sc (squeeze_ne _ h.hsc.1)
  refine ⟨h.hsc,h.hst,h.hwk,h.hrate,?_,?_,?_,?_,?_⟩
  · simpa only [eq] using h.d
  · simpa only [k.sp] using h.sp16
  · simpa only [eq,stk,k.sp] using h.kst
  · simpa only [eq,stk,k.sp] using h.kwk
  · simpa only [eq,k.wr] using h.cov

theorem piece_copy {s t : State} {sc : Reg} {st wk rate : Nat} {p : Piece}
    (h : HSetup sc st wk rate s) (hp : PieceOk sc st wk s true p) (k : Keep [.x2,.x9] s t) :
    PieceOk sc st wk t true p := by
  have eq := k.get sc (squeeze_ne _ h.hsc.1)
  have eb := k.get p.base (squeeze_ne _ hp.base.1)
  refine ⟨hp.base,hp.off,hp.len,?_,?_,?_,?_⟩
  · simpa only [preg,STr,eq,eb] using hp.dst
  · simpa only [preg,WKr,eq,eb] using hp.dwk
  · simpa only [preg,stk,eb,k.sp] using hp.stk
  · simpa only [preg,eb,k.wr,↓reduceIte] using hp.cov

theorem preg_copy {s t : State} {sc : Reg} {st wk : Nat} {p : Piece}
    (hp : PieceOk sc st wk s true p) (k : Keep [.x2,.x9] s t) : preg t p=preg s p := by
  unfold preg
  rw [k.get p.base (squeeze_ne _ hp.base.1)]

theorem outs_copy {s t : State} {sc : Reg} {st wk : Nat} {ps : List Piece}
    (hp : ∀p∈ps,PieceOk sc st wk s true p) (k : Keep [.x2,.x9] s t)
    {m : Mem} {rate pos : Nat} {A : Spec.Sha3.State} : Outs t m rate A pos ps↔Outs s m rate A pos ps := by
  induction ps generalizing pos with
  | nil=>rfl
  | cons p ps ih=>
    simp only [Outs,k.get p.base (squeeze_ne _ (hp _ (by simp)).base.1)]
    exact and_congr Iff.rfl (ih (fun p hh=>hp p (by simp [hh])))

end VG.Proof.MlKem.AArch64.FixedHash
