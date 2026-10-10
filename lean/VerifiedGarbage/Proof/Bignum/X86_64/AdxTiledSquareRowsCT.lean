import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTailCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRowsCT

/-! ## AdxTiledSquareRowCT -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRect8 (RowLayout RowState rawBase)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)
open VG.Proof.Bignum.X86_64.AdxTiledProduct (ranges frame_hdr frame_ops TailReady tail_ok tail_ct)

def RowStart (ps : List (Nat × Nat)) (L : RowLayout) (s : State) : Prop :=
  (∃ q, L.w=L.i+8+8*q) ∧ L.j₀=L.i+8 ∧ (∃ mi, Good s L.B L.Z L.w mi) ∧ Ops s.mem L.B L.w ps ∧
    word s.mem L.B (8*sFn 12)=BitVec.ofNat 64 L.i

def RowReady (ps : List (Nat × Nat)) (L : RowLayout) (s : State) : Prop :=
  (∃ q, L.w=L.i+8+8*q) ∧ L.j₀=L.i+8 ∧ RowState ps L 0 s ∧ word s.mem L.B carryOffset=0

theorem init_fw {ps : List (Nat × Nat)} (L : RowLayout) (s : State) (h : RowStart ps L s) :
    WP isa (.block AdxTiledSquare.rowInit) s (RowReady ps L) := by
  obtain ⟨tail,j0,⟨mi,hg⟩,hv,idx⟩ := h
  refine WP.mono (rowInit_ok hg.scr hg.rdi L.hZ idx) fun t ⟨c,j,o,k⟩ => ?_
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

theorem inner_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    (L : RowLayout) (s : State) (h : RowReady ps L s) :
    WP isa (AdxRect8.row ca ca) s (fun t => TailReady L t ∧ ∃ q, L.w=L.i+8+8*q) := by
  obtain ⟨tail,j0,⟨mi,hg,hv,idx,jdx⟩,carry⟩ := h
  simp only [Nat.mul_zero,Nat.add_zero] at jdx
  refine WP.mono (AdxRect8.row_ok hg.scr hg.rdi hg.hdr hv pa pa L.hZ L.hw L.hi ha ha ha1 ha2 ha1 ha2
    L.hwN L.hn idx jdx (by rw [carry]; rfl)) fun t ht => ?_
  have ptr := ht.endPtr.resolve_left (by have := L.hn; omega)
  have wn := L.hwN
  exact ⟨⟨⟨mi,ht.scr,ht.rdi,ht.hdr⟩,ht.indexI,by simpa only [show L.i+L.j₀+8*L.n=L.i+L.w by omega] using ptr⟩,tail⟩

theorem row_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) hint).isSome=true) :
    RelCT isa (Two (RowStart ps)) (AdxTiledSquare.row ca) (fun _ _ => True) := by
  unfold AdxTiledSquare.row
  refine RelCT.seq (two_piece [.rdi] ?_ (by taint_decide) init_fw) ?_
  · rintro L s t ⟨_,_,⟨mi,hs⟩,_,_⟩ ⟨_,_,⟨mj,ht⟩,_,_⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.rdi.trans ht.rdi.symm
  refine RelCT.seq (two_post (two_map id (fun _ _ h => h.2.2.1)
    ((AdxRect8.row_ct pa pa ha ha ha1 ha2 ha1 ha2 hS).mono (fun _ _ h => h) (fun _ _ _ => True.intro)))
    (inner_fw pa ha ha1 ha2)) ?_
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

end

/-! ## AdxTiledSquareRowsCT -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

open VG.Proof.Bignum.X86_64.AdxTiledProduct (Layout LoopState GoodV frame_ops)

def StartGood (ps : List (Nat × Nat)) (L : Layout) (s : State) : Prop := 1<L.n ∧ GoodV ps L s

theorem row_loop_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) hint).isSome=true) :
    RelCT isa (Two fun p : Layout × Nat => fun s => p.2<p.1.n-1 ∧ LoopState ps p.1 p.2 s)
      (AdxTiledSquare.row ca) (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨⟨L,k⟩,⟨hk,mi,gs,vs,is⟩,⟨_,mj,gt,vt,it⟩⟩ es et
  dsimp only at hk
  have wn := L.hwN
  let R : AdxRect8.RowLayout := ⟨L.B,L.Z,L.w,8*k,8*k+8,L.n-k-1,L.hZ,L.hw,by omega,by omega,by omega⟩
  apply row_ct pa ha ha1 ha2 hS s t ts tt s' t' ?_ es et
  exact ⟨R,⟨⟨L.n-k-1,by dsimp [R]; omega⟩,rfl,⟨mi,gs⟩,vs,is⟩,
    ⟨L.n-k-1,by dsimp [R]; omega⟩,rfl,⟨mj,gt⟩,vt,it⟩

theorem row_loop_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    (L : Layout) (k : Nat) (s : State) (hk : k<L.n-1) (h : LoopState ps L k s) :
    WP isa (AdxTiledSquare.row ca) s fun t =>
      isa.eval .ne t=some (decide (k+1<L.n-1)) ∧
      (k+1<L.n-1 → LoopState ps L (k+1) t) ∧ (k+1=L.n-1 → GoodV ps L t) := by
  obtain ⟨mi,hg,hv,idx⟩ := h
  have wn := L.hwN
  refine WP.mono (row_ok hg.scr hg.rdi hg.hdr hv pa L.hZ L.hw
    (by omega : L.w=8*k+8+8*(L.n-k-1)) (by omega) ha ha1 ha2 idx)
    fun t ⟨zt,it,_,ht,ft,kt⟩ => ?_
  have good : Good t L.B L.Z L.w mi := ⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,ht⟩
  have vt := frame_ops hv ft
  refine ⟨?_,fun _ => ⟨mi,good,vt,?_⟩,fun _ => ⟨⟨mi,good⟩,vt⟩⟩
  · simp only [eval,zt,Option.map_some]
    by_cases he : k+1=L.n-1
    · simp only [show 8*k+8=L.w-8 by omega,decide_true,Bool.not_true,
        show ¬(k+1<L.n-1) by omega,decide_false]
    · simp only [show ¬(8*k+8=L.w-8) by omega,decide_false,Bool.not_false,
        show k+1<L.n-1 by omega,decide_true]
  · simpa only [show 8*(k+1)=8*k+8 by omega] using it

theorem rows_init_fw {ps : List (Nat × Nat)} (L : Layout) (s : State) (h : StartGood ps L s) :
    WP isa (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax]) s
      (fun t => 0<L.n-1 ∧ LoopState ps L 0 t) :=
  WP.mono (AdxTiledProduct.rows_init_fw L s h.2) fun _ ht => ⟨by have := h.1; omega,ht.2⟩

theorem rows_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) hint).isSome=true) :
    RelCT isa (Two (StartGood ps)) (AdxTiledSquare.rows ca) (Two (GoodV ps)) := by
  unfold AdxTiledSquare.rows
  refine RelCT.seq (two_piece [.rdi] ?_ (by taint_decide) rows_init_fw)
    (two_loop (fun L : Layout => L.n-1) (row_loop_ct pa ha ha1 ha2 hS)
      (row_loop_fw pa ha ha1 ha2))
  rintro L s t ⟨_,⟨mi,hs⟩,_⟩ ⟨_,⟨mj,ht⟩,_⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.rdi.trans ht.rdi.symm

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end
