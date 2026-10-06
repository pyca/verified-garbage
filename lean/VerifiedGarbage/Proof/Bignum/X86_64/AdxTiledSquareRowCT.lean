import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTailCT

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRect8 (RowLayout RowState rawBase)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)
open VG.Proof.Bignum.X86_64.AdxTiledProduct (ranges frame_hdr TailReady tail_ok tail_ct)

def RowStart (L : RowLayout) (s : State) : Prop :=
  (∃ q, L.w=L.i+8+8*q) ∧ L.j₀=L.i+8 ∧ (∃ mi, Good s L.B L.Z L.w mi) ∧ word s.mem L.B (8*sFn 12)=BitVec.ofNat 64 L.i

def RowReady (L : RowLayout) (s : State) : Prop :=
  (∃ q, L.w=L.i+8+8*q) ∧ L.j₀=L.i+8 ∧ RowState L 0 s ∧ word s.mem L.B carryOffset=0

theorem init_fw (L : RowLayout) (s : State) (h : RowStart L s) :
    WP isa (.block AdxTiledSquare.rowInit) s (RowReady L) := by
  obtain ⟨tail,j0,⟨mi,hg⟩,idx⟩ := h
  refine WP.mono (rowInit_ok hg.scr hg.rdi L.hZ idx) fun t ⟨c,j,o,k⟩ => ?_
  have hh : Hdr t.mem L.B L.w mi := frame_hdr hg.hdr (by
    intro x hx
    apply o x
    have := hx (8*sFn 12,32) (by simp [ranges])
    simp only [sFn] at *; omega)
  have it : word t.mem L.B (8*sFn 12)=BitVec.ofNat 64 L.i := by
    rw [o.word (by decide) (by decide)]; exact idx
  exact ⟨tail,j0,⟨mi,⟨hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,hh⟩,it,
    by rw [j0]; exact j⟩,c⟩

theorem inner_fw {a : Nat} (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    (L : RowLayout) (s : State) (h : RowReady L s) :
    WP isa (AdxRect8.row a a) s (fun t => TailReady L t ∧ ∃ q, L.w=L.i+8+8*q) := by
  obtain ⟨tail,j0,⟨mi,hg,idx,jdx⟩,carry⟩ := h
  simp only [Nat.mul_zero,Nat.add_zero] at jdx
  refine WP.mono (AdxRect8.row_ok hg.scr hg.rdi hg.hdr L.hZ L.hw L.hi ha ha ha1 ha2 ha1 ha2
    L.hwN L.hn idx jdx (by rw [carry]; rfl)) fun t ht => ?_
  have ptr := ht.endPtr.resolve_left (by have := L.hn; omega)
  have wn := L.hwN
  exact ⟨⟨⟨mi,ht.scr,ht.rdi,ht.hdr⟩,ht.indexI,by simpa only [show L.i+L.j₀+8*L.n=L.i+L.w by omega] using ptr⟩,tail⟩

theorem row_ct {a : Nat} (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a a)) hint).isSome=true) :
    RelCT isa (Two RowStart) (AdxTiledSquare.row a) (fun _ _ => True) := by
  unfold AdxTiledSquare.row
  refine RelCT.seq (two_piece [.rdi] ?_ (by taint_decide) init_fw) ?_
  · rintro L s t ⟨_,_,⟨mi,hs⟩,_⟩ ⟨_,_,⟨mj,ht⟩,_⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.rdi.trans ht.rdi.symm
  refine RelCT.seq (two_post (two_map id (fun _ _ h => h.2.2.1)
    ((AdxRect8.row_ct ha ha ha1 ha2 ha1 ha2 hS).mono (fun _ _ h => h) (fun _ _ _ => True.intro)))
    (inner_fw ha ha1 ha2)) ?_
  refine RelCT.seq (two_post (two_map id (fun _ _ h => h.1) tail_ct)
    (Ψ := fun L s => s.gpr .rdi=L.B) ?_)
    (two_taint [.rdi] ?_ (by taint_decide))
  · rintro L s ⟨⟨⟨mi,hg⟩,idx,ptr⟩,q,hq⟩
    exact WP.mono (AdxTiledProduct.tail_ok hg.scr hg.rdi hg.hdr L.hZ L.hw hq idx ptr)
      fun t ⟨_,_,k⟩ => (k.gpr (by decide)).trans hg.rdi
  · intro L s t hs ht r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.trans ht.symm

end VG.Proof.Bignum.X86_64.AdxTiledSquare
