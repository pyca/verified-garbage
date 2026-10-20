module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.AbsorbPlan
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64

theorem hsetup_rg {s t : State} {sc : Reg} {st wk rate : Nat}
 (h : HSetup sc st wk rate s) (g : Rg s t) : HSetup sc st wk rate t := by
 have e:=g.cs sc h.hsc.1 h.hsc.2
 refine ⟨h.hsc,h.hst,h.hwk,h.hrate,?_,?_,?_,?_,?_⟩
 · simpa only [e] using h.d
 · simpa only [g.sp] using h.sp16
 · simpa only [e,stk,g.sp] using h.kst
 · simpa only [e,stk,g.sp] using h.kwk
 · simpa only [e,g.wr] using h.cov

theorem piece_rg {s t : State} {sc : Reg} {st wk rate : Nat} {p : Piece} {w : Bool}
 (h : HSetup sc st wk rate s) (hp : PieceOk sc st wk s w p) (g : Rg s t) :
 PieceOk sc st wk t w p := by
 have e:=g.cs sc h.hsc.1 h.hsc.2
 have b:=g.cs p.base hp.base.1 hp.base.2
 refine ⟨hp.base,hp.off,hp.len,?_,?_,?_,?_⟩
 · simpa only [preg,STr,e,b] using hp.dst
 · simpa only [preg,WKr,e,b] using hp.dwk
 · simpa only [preg,stk,b,g.sp] using hp.stk
 · simpa only [preg,b,g.wr,g.rd] using hp.cov

theorem preg_rg {s t : State} {sc : Reg} {st wk : Nat} {p : Piece} {w : Bool}
 (hp : PieceOk sc st wk s w p) (g : Rg s t) : preg t p=preg s p := by
 unfold preg
 rw [g.cs p.base hp.base.1 hp.base.2]

theorem outs_rg {s t : State} {sc : Reg} {st wk : Nat} {ps : List Piece}
 (hp : ∀p∈ps,PieceOk sc st wk s true p) (g : Rg s t)
 {m : Mem} {rate pos : Nat} {A : Spec.Sha3.State} :
 Outs t m rate A pos ps↔Outs s m rate A pos ps := by
 induction ps generalizing pos with
 | nil=>rfl
 | cons p ps ih=>
   simp only [Outs,g.cs p.base (hp _ (by simp)).base.1 (hp _ (by simp)).base.2]
   exact and_congr Iff.rfl (ih (fun p hh=>hp p (by simp [hh])))

theorem remaining_zero (s : State) (ps : List Piece) :
 remainingBytes s ps 0=(ps.map (pbytes s)).flatten := by
 cases ps with
 | nil=>rfl
 | cons p ps=>simp [remainingBytes,chunkBytes,pbytes]
end VG.Proof.MlKem.AArch64.FixedHash
