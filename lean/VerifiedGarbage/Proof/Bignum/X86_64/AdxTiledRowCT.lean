import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTailCT

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRect8 (RowLayout RowState rawBase)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

def RowStart (ps : List (Nat × Nat)) (L : RowLayout) (s : State) : Prop :=
  (∃ q, L.w=L.i+8+8*q) ∧ L.j₀=0 ∧ (∃ mi, Good s L.B L.Z L.w mi) ∧ Ops s.mem L.B L.w ps ∧
    word s.mem L.B (8*sFn 12)=BitVec.ofNat 64 L.i

def RowReady (ps : List (Nat × Nat)) (L : RowLayout) (s : State) : Prop :=
  (∃ q, L.w=L.i+8+8*q) ∧ L.j₀=0 ∧ RowState ps L 0 s ∧ word s.mem L.B carryOffset=0

theorem init_fw {ps : List (Nat × Nat)} (L : RowLayout) (s : State) (h : RowStart ps L s) :
    WP isa (.block AdxTiledProduct.rowInit) s (RowReady ps L) := by
  obtain ⟨tail,j0,⟨mi,hg⟩,hv,idx⟩ := h
  refine WP.mono (rowInit_ok hg.scr hg.rdi L.hZ) fun t ⟨c,j,o,k⟩ => ?_
  have f : Frm L.B (ranges L.w) s.mem t.mem := by
    intro x hx
    apply o x
    have := hx (8*sFn 12,32) (by simp [ranges])
    simp only [sFn] at *; omega
  have hh : Hdr t.mem L.B L.w mi := frame_hdr hg.hdr f
  have it : word t.mem L.B (8*sFn 12)=BitVec.ofNat 64 L.i := by
    rw [o.word (by decide) (by decide)]; exact idx
  exact ⟨tail,j0,⟨mi,⟨hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,hh⟩,frame_ops hv f,it,
    by rw [j0]; exact j⟩,c⟩

theorem inner_fw {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    (L : RowLayout) (s : State) (h : RowReady ps L s) :
    WP isa (AdxRect8.row ca cb) s (fun t => TailReady L t ∧ ∃ q, L.w=L.i+8+8*q) := by
  obtain ⟨tail,j0,⟨mi,hg,hv,idx,jdx⟩,carry⟩ := h
  simp only [Nat.mul_zero,Nat.add_zero] at jdx
  refine WP.mono (AdxRect8.row_ok hg.scr hg.rdi hg.hdr hv pa pb L.hZ L.hw L.hi ha hb ha1 ha2 hb1 hb2
    L.hwN L.hn idx jdx (by rw [carry]; rfl)) fun t ht => ?_
  have ptr := ht.endPtr.resolve_left (by have := L.hn; omega)
  have wn := L.hwN
  rw [j0,Nat.add_zero] at ptr
  rw [j0,Nat.zero_add] at wn
  exact ⟨⟨⟨mi,ht.scr,ht.rdi,ht.hdr⟩,ht.indexI,by simpa only [← wn] using ptr⟩,tail⟩

theorem row_ct {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca cb)) hint).isSome=true) :
    RelCT isa (Two (RowStart ps)) (AdxTiledProduct.row ca cb) (fun _ _ => True) := by
  unfold AdxTiledProduct.row
  refine RelCT.seq (two_piece [.rdi] ?_ (by taint_decide) init_fw) ?_
  · rintro L s t ⟨_,_,⟨mi,hs⟩,_,_⟩ ⟨_,_,⟨mj,ht⟩,_,_⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.rdi.trans ht.rdi.symm
  refine RelCT.seq (two_post (two_map id (fun _ _ h => h.2.2.1)
    ((AdxRect8.row_ct pa pb ha hb ha1 ha2 hb1 hb2 hS).mono (fun _ _ h => h) (fun _ _ _ => True.intro)))
    (inner_fw pa pb ha hb ha1 ha2 hb1 hb2)) ?_
  refine RelCT.seq (two_post (two_map id (fun _ _ h => h.1) tail_ct)
    (Ψ := fun L s => s.gpr .rdi=L.B) ?_)
    (two_taint [.rdi] ?_ (by taint_decide))
  · rintro L s ⟨⟨⟨mi,hg⟩,idx,ptr⟩,q,hq⟩
    exact WP.mono (tail_ok hg.scr hg.rdi hg.hdr L.hZ L.hw hq idx ptr)
      fun t ⟨_,_,k⟩ => (k.gpr (by decide)).trans hg.rdi
  · intro L s t hs ht r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.trans ht.symm

end VG.Proof.Bignum.X86_64.AdxTiledProduct
