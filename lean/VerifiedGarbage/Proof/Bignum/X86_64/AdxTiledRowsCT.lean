import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTailCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRows

/-! ## AdxTiledRowCT -/
section

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
  refine RelCT.seq (two_post (two_map id (fun _ _ h => ⟨h.2.2.1,h.2.2.2⟩)
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

end

/-! ## AdxTiledRowsCT -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

structure Layout where
  B : Addr
  Z : Nat
  w : Nat
  n : Nat
  hZ : slot w 8 ≤ Z
  hw : w<2^31
  hwN : w=8*n
  hn : 0<n

def LoopState (ps : List (Nat × Nat)) (L : Layout) (k : Nat) (s : State) : Prop :=
  ∃ mi, Good s L.B L.Z L.w mi ∧ Ops s.mem L.B L.w ps ∧ word s.mem L.B (8*sFn 12)=BitVec.ofNat 64 (8*k)

def GoodL (L : Layout) (s : State) : Prop := ∃ mi, Good s L.B L.Z L.w mi

/-- `GoodL`, with the header slots `ps` holding the operands' bases. -/
def GoodV (ps : List (Nat × Nat)) (L : Layout) (s : State) : Prop := GoodL L s ∧ Ops s.mem L.B L.w ps

theorem row_loop_ct {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca cb)) hint).isSome=true) :
    RelCT isa (Two fun p : Layout × Nat => fun s => p.2<p.1.n ∧ LoopState ps p.1 p.2 s)
      (AdxTiledProduct.row ca cb) (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨⟨L,k⟩,⟨hk,mi,gs,vs,is⟩,⟨_,mj,gt,vt,it⟩⟩ es et
  dsimp only at hk
  have wn := L.hwN
  let R : AdxRect8.RowLayout := ⟨L.B,L.Z,L.w,8*k,0,L.n,L.hZ,L.hw,by omega,by omega,L.hn⟩
  apply row_ct pa pb ha hb ha1 ha2 hb1 hb2 hS s t ts tt s' t' ?_ es et
  exact ⟨R,⟨⟨L.n-k-1,by dsimp [R]; omega⟩,rfl,⟨mi,gs⟩,vs,is⟩,
    ⟨L.n-k-1,by dsimp [R]; omega⟩,rfl,⟨mj,gt⟩,vt,it⟩

theorem row_loop_fw {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    (L : Layout) (k : Nat) (s : State) (hk : k<L.n) (h : LoopState ps L k s) :
    WP isa (AdxTiledProduct.row ca cb) s fun t =>
      isa.eval .ne t=some (decide (k+1<L.n)) ∧
      (k+1<L.n → LoopState ps L (k+1) t) ∧ (k+1=L.n → GoodV ps L t) := by
  obtain ⟨mi,hg,hv,idx⟩ := h
  have wn := L.hwN
  refine WP.mono (row_ok hg.scr hg.rdi hg.hdr hv pa pb L.hZ L.hw L.hwN L.hn
    (by omega : L.w=8*k+8+8*(L.n-k-1)) ha hb ha1 ha2 hb1 hb2 idx)
    fun t ⟨zt,it,_,ht,ft,kt⟩ => ?_
  have good : Good t L.B L.Z L.w mi := ⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,ht⟩
  have hv' := frame_ops hv ft
  refine ⟨?_,fun _ => ⟨mi,good,hv',?_⟩,fun _ => ⟨⟨mi,good⟩,hv'⟩⟩
  · simp only [eval,zt,Option.map_some]
    by_cases he : k+1=L.n
    · simp only [show 8*k+8=L.w by omega,decide_true,Bool.not_true,
        show ¬(k+1<L.n) by omega,decide_false]
    · simp only [show ¬(8*k+8=L.w) by omega,decide_false,Bool.not_false,
        show k+1<L.n by omega,decide_true]
  · simpa only [show 8*(k+1)=8*k+8 by omega] using it

theorem rows_init_fw {ps : List (Nat × Nat)} (L : Layout) (s : State) (h : GoodV ps L s) :
    WP isa (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax]) s
      (fun t => 0<L.n ∧ LoopState ps L 0 t) := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  have hZ := L.hZ
  have iZ : 8*sFn 12+8 ≤ L.Z := by
    have := hdr_lt_slot L.w 8 (show sFn 12<32 by decide); omega
  have nowrap := hg.scr.nowrap
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem=s.mem.writeW (off L.B (8*sFn 12)) (0 : BitVec 64)) ?_ rfl)
    fun t ⟨mt,kt⟩ => ?_
  · xrun [State.ea,hdr,hg.rdi,hdrOff,hg.scr.st iZ]; rfl
  have ot : Outside L.B (8*sFn 12) 8 s.mem t.mem := by rw [mt]; exact writeW_outside _ _ _ (by decide)
  have ft : Frm L.B (ranges L.w) s.mem t.mem := by
    intro x hx
    apply ot x
    have := hx (8*sFn 12,32) (by simp [ranges]); omega
  exact ⟨L.hn,mi,⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,frame_hdr hg.hdr ft⟩,
    frame_ops hv ft,by rw [mt,word_writeW_self]; rfl⟩

theorem rows_ct {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca cb)) hint).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTiledProduct.rows ca cb) (Two (GoodV ps)) := by
  unfold AdxTiledProduct.rows
  refine RelCT.seq (two_piece [.rdi] ?_ (by taint_decide) rows_init_fw)
    (two_loop (fun L : Layout => L.n) (row_loop_ct pa pb ha hb ha1 ha2 hb1 hb2 hS)
      (row_loop_fw pa pb ha hb ha1 ha2 hb1 hb2))
  rintro L s t ⟨⟨mi,hs⟩,_⟩ ⟨⟨mj,ht⟩,_⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.rdi.trans ht.rdi.symm

end VG.Proof.Bignum.X86_64.AdxTiledProduct

end
