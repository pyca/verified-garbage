module

public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Table
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Const
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.TableInit
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.MulSlots

/-! Normalize negative A's X coordinate once to the product output bound. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (slot)
open VG.Proof.X448.AArch64 (Scr)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same)
open VG.Proof.Curve448.AArch64.Fast (Mb)
open VG.Proof.Ed448.AArch64.Window (slotPt)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem normalizeKey_ok {s:State} {base:Addr} (hs:Scr s base) (hb:BEnv s.mem base) :
    WP isa normalizeKey s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Bnd Mb t.mem base (slot 6) ∧
      Same base [6,20] s.mem t.mem ∧ slotPt t.mem base=slotPt s.mem base := by
  unfold normalizeKey
  refine WP.seq (WP.mono (constE hs hb 20 1) fun a ⟨ab,asm,ae,_,ao,ak⟩ => ?_)
  have af:FKeep base s a:=⟨ak.mono (by decide),fun x hx _ => ao x (by simp only [slot] at hx ⊢;omega)⟩
  refine Point56.mulOpK (af.scr hs) ab 6 6 20 (Or.inr (by decide))
    fun t tk tb tm tsm te => WP.block_nil ?_
  refine ⟨af.trans tk,tb,tm,?_,?_⟩
  · exact VG.Proof.X448.AArch64.Base.Same.mono (asm.append tsm) (by decide)
  · rw [slotPt,slotPt,te,ae]
    change (⟨EV s.mem base 6*1,EV s.mem base 7,1⟩:VG.Spec.Ed448.Point)=_
    rw [Fin.mul_one]

end VG.Proof.Ed448.AArch64.Sparse
