import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRowCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRows

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

def LoopState (L : Layout) (k : Nat) (s : State) : Prop :=
  ∃ mi, Good s L.B L.Z L.w mi ∧ word s.mem L.B (8*sFn 12)=BitVec.ofNat 64 (8*k)

def GoodL (L : Layout) (s : State) : Prop := ∃ mi, Good s L.B L.Z L.w mi

theorem row_loop_ct {a b : Nat} (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a b)) hint).isSome=true) :
    RelCT isa (Two fun p : Layout × Nat => fun s => p.2<p.1.n ∧ LoopState p.1 p.2 s)
      (AdxTiledProduct.row a b) (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨⟨L,k⟩,⟨hk,mi,gs,is⟩,⟨_,mj,gt,it⟩⟩ es et
  dsimp only at hk
  have wn := L.hwN
  let R : AdxRect8.RowLayout := ⟨L.B,L.Z,L.w,8*k,0,L.n,L.hZ,L.hw,by omega,by omega,L.hn⟩
  apply row_ct ha hb ha1 ha2 hb1 hb2 hS s t ts tt s' t' ?_ es et
  exact ⟨R,⟨⟨L.n-k-1,by dsimp [R]; omega⟩,rfl,⟨mi,gs⟩,is⟩,
    ⟨L.n-k-1,by dsimp [R]; omega⟩,rfl,⟨mj,gt⟩,it⟩

theorem row_loop_fw {a b : Nat} (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    (L : Layout) (k : Nat) (s : State) (hk : k<L.n) (h : LoopState L k s) :
    WP isa (AdxTiledProduct.row a b) s fun t =>
      isa.eval .ne t=some (decide (k+1<L.n)) ∧
      (k+1<L.n → LoopState L (k+1) t) ∧ (k+1=L.n → GoodL L t) := by
  obtain ⟨mi,hg,idx⟩ := h
  have wn := L.hwN
  refine WP.mono (row_ok hg.scr hg.rdi hg.hdr L.hZ L.hw L.hwN L.hn
    (by omega : L.w=8*k+8+8*(L.n-k-1)) ha hb ha1 ha2 hb1 hb2 idx)
    fun t ⟨zt,it,_,ht,_,kt⟩ => ?_
  have good : Good t L.B L.Z L.w mi := ⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,ht⟩
  refine ⟨?_,fun _ => ⟨mi,good,?_⟩,fun _ => ⟨mi,good⟩⟩
  · simp only [eval,zt,Option.map_some]
    by_cases he : k+1=L.n
    · simp only [show 8*k+8=L.w by omega,decide_true,Bool.not_true,
        show ¬(k+1<L.n) by omega,decide_false]
    · simp only [show ¬(8*k+8=L.w) by omega,decide_false,Bool.not_false,
        show k+1<L.n by omega,decide_true]
  · simpa only [show 8*(k+1)=8*k+8 by omega] using it

theorem rows_init_fw (L : Layout) (s : State) (h : GoodL L s) :
    WP isa (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax]) s
      (fun t => 0<L.n ∧ LoopState L 0 t) := by
  obtain ⟨mi,hg⟩ := h
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
    by rw [mt,word_writeW_self]; rfl⟩

theorem rows_ct {a b : Nat} (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a b)) hint).isSome=true) :
    RelCT isa (Two GoodL) (AdxTiledProduct.rows a b) (Two GoodL) := by
  unfold AdxTiledProduct.rows
  refine RelCT.seq (two_piece [.rdi] ?_ (by taint_decide) rows_init_fw)
    (two_loop (fun L : Layout => L.n) (row_loop_ct ha hb ha1 ha2 hb1 hb2 hS)
      (row_loop_fw ha hb ha1 ha2 hb1 hb2))
  rintro L s t ⟨mi,hs⟩ ⟨mj,ht⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.rdi.trans ht.rdi.symm

end VG.Proof.Bignum.X86_64.AdxTiledProduct
