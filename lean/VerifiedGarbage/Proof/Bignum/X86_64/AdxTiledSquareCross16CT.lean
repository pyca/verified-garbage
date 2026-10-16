module

public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsCT
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareCross16
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareCross16
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.X86_64.Call

/-! # The 16-word square's cross tile is constant time

Its indices and addresses are the public layout's; the rest is checked by
taint from them. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (Layout GoodV ranges frame_hdr frame_ops)
open VG.Proof.MlKem.X86_64 (Keep)

/-- After `init16`: the tile's row and column indices in the header. -/
def Idx16 (ps : List (Nat × Nat)) (L : Layout) (s : State) : Prop :=
  L.w = 16 ∧ GoodV ps L s ∧ word s.mem L.B (8*sFn 12) = BitVec.ofNat 64 0 ∧
    word s.mem L.B (8*sFn 13) = BitVec.ofNat 64 8

/-- After the tile's `setup`: its addresses, the public layout's. -/
def Addr16 (a : Nat) (L : Layout) (s : State) : Prop :=
  s.gpr .rdi = L.B ∧ s.gpr .rcx = off L.B (slot L.w a+8*0) ∧ s.gpr .rbp = off L.B (slot L.w a+8*8) ∧
    s.gpr .rsi = off L.B (slot L.w aAcc+16+8*(0+8))

theorem init16_fw {ps : List (Nat × Nat)} (L : Layout) (s : State)
    (h : StartGood ps L s ∧ L.w = 16) : WP isa (.block AdxTiledSquare.init16) s (Idx16 ps L) := by
  obtain ⟨⟨_,⟨mi,hg⟩,hv⟩,h16⟩ := h
  refine WP.mono (init16_ok hg.scr hg.rdi L.hZ) fun t ⟨it,jt,ot,kt⟩ => ?_
  have f : Frm L.B (ranges L.w) s.mem t.mem :=
    Frm.of_outside (ot.mono (o' := 8*sFn 12) (n' := 32) (by omega) (by omega)) (by simp [ranges])
  exact ⟨h16,⟨⟨mi,hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,frame_hdr hg.hdr f⟩,frame_ops hv f⟩,it,jt⟩

theorem setup16_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (L : Layout) (s : State)
    (h : Idx16 ps L s) : WP isa (.block (AdxRect8.setup ca ca)) s (Addr16 a L) := by
  obtain ⟨_,⟨⟨mi,hg⟩,hv⟩,it,jt⟩ := h
  exact WP.mono (AdxRect8.setup_ok hg.scr hg.rdi hg.hdr L.hZ hv pa pa it jt)
    fun t ⟨ta,tb,to,_,kt⟩ => ⟨(kt.gpr (by decide)).trans hg.rdi,ta,tb,to⟩

theorem cross16_body_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) hint).isSome=true) :
    RelCT isa (Two fun L s => StartGood ps L s ∧ L.w = 16) (AdxTiledSquare.cross16 ca)
      (fun _ _ => True) := by
  unfold AdxTiledSquare.cross16
  refine RelCT.seq (two_piece [.rdi] ?_ (by taint_decide) init16_fw) ?_
  · rintro L s t ⟨⟨_,⟨mi,hs⟩,_⟩,_⟩ ⟨⟨_,⟨mj,ht⟩,_⟩,_⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.rdi.trans ht.rdi.symm
  refine RelCT.seq (two_piece [.rdi] ?_ hS (setup16_fw pa)) ?_
  · rintro L s t ⟨_,⟨⟨mi,hs⟩,_⟩,_⟩ ⟨_,⟨⟨mj,ht⟩,_⟩,_⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.rdi.trans ht.rdi.symm
  refine two_taint [.rdi,.rcx,.rbp,.rsi] ?_ (by taint_decide)
  rintro L s t ⟨s1,s2,s3,s4⟩ ⟨t1,t2,t3,t4⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact s1.trans t1.symm
  · exact s2.trans t2.symm
  · exact s3.trans t3.symm
  · exact s4.trans t4.symm

theorem cross16_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) hint).isSome=true) :
    RelCT isa (Two fun L s => StartGood ps L s ∧ L.w = 16) (AdxTiledSquare.cross16 ca) (Two (GoodV ps)) := by
  refine two_post (cross16_body_ct pa hS) ?_
  rintro L s ⟨⟨_,⟨mi,hg⟩,hv⟩,h16⟩
  exact WP.mono (cross16_ok hg.scr hg.rdi hg.hdr L.hZ hv pa h16 ha ha1 ha2)
    fun t ⟨_,ht,ft,kt⟩ => ⟨⟨mi,hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,ht⟩,frame_ops hv ft⟩

end VG.Proof.Bignum.X86_64.AdxTiledSquare
