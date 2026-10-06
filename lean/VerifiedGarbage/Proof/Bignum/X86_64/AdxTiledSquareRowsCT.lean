import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRowsCT

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

open VG.Proof.Bignum.X86_64.AdxTiledProduct (Layout LoopState)

def StartGood (L : Layout) (s : State) : Prop := 1<L.n ∧ AdxTiledProduct.GoodL L s

theorem row_loop_ct {a : Nat} (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a a)) hint).isSome=true) :
    RelCT isa (Two fun p : Layout × Nat => fun s => p.2<p.1.n-1 ∧ LoopState p.1 p.2 s)
      (AdxTiledSquare.row a) (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨⟨L,k⟩,⟨hk,mi,gs,is⟩,⟨_,mj,gt,it⟩⟩ es et
  dsimp only at hk
  have wn := L.hwN
  let R : AdxRect8.RowLayout := ⟨L.B,L.Z,L.w,8*k,8*k+8,L.n-k-1,L.hZ,L.hw,by omega,by omega,by omega⟩
  apply row_ct ha ha1 ha2 hS s t ts tt s' t' ?_ es et
  exact ⟨R,⟨⟨L.n-k-1,by dsimp [R]; omega⟩,rfl,⟨mi,gs⟩,is⟩,
    ⟨L.n-k-1,by dsimp [R]; omega⟩,rfl,⟨mj,gt⟩,it⟩

theorem row_loop_fw {a : Nat} (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    (L : Layout) (k : Nat) (s : State) (hk : k<L.n-1) (h : LoopState L k s) :
    WP isa (AdxTiledSquare.row a) s fun t =>
      isa.eval .ne t=some (decide (k+1<L.n-1)) ∧
      (k+1<L.n-1 → LoopState L (k+1) t) ∧ (k+1=L.n-1 → AdxTiledProduct.GoodL L t) := by
  obtain ⟨mi,hg,idx⟩ := h
  have wn := L.hwN
  refine WP.mono (row_ok hg.scr hg.rdi hg.hdr L.hZ L.hw
    (by omega : L.w=8*k+8+8*(L.n-k-1)) (by omega) ha ha1 ha2 idx)
    fun t ⟨zt,it,_,ht,_,kt⟩ => ?_
  have good : Good t L.B L.Z L.w mi := ⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,ht⟩
  refine ⟨?_,fun _ => ⟨mi,good,?_⟩,fun _ => ⟨mi,good⟩⟩
  · simp only [eval,zt,Option.map_some]
    by_cases he : k+1=L.n-1
    · simp only [show 8*k+8=L.w-8 by omega,decide_true,Bool.not_true,
        show ¬(k+1<L.n-1) by omega,decide_false]
    · simp only [show ¬(8*k+8=L.w-8) by omega,decide_false,Bool.not_false,
        show k+1<L.n-1 by omega,decide_true]
  · simpa only [show 8*(k+1)=8*k+8 by omega] using it

theorem rows_init_fw (L : Layout) (s : State) (h : StartGood L s) :
    WP isa (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax]) s
      (fun t => 0<L.n-1 ∧ LoopState L 0 t) :=
  WP.mono (AdxTiledProduct.rows_init_fw L s h.2) fun _ ht => ⟨by have := h.1; omega,ht.2⟩

theorem rows_ct {a : Nat} (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a a)) hint).isSome=true) :
    RelCT isa (Two StartGood) (AdxTiledSquare.rows a) (Two AdxTiledProduct.GoodL) := by
  unfold AdxTiledSquare.rows
  refine RelCT.seq (two_piece [.rdi] ?_ (by taint_decide) rows_init_fw)
    (two_loop (fun L : Layout => L.n-1) (row_loop_ct ha ha1 ha2 hS)
      (row_loop_fw ha ha1 ha2))
  rintro L s t ⟨_,mi,hs⟩ ⟨_,mj,ht⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.rdi.trans ht.rdi.symm

end VG.Proof.Bignum.X86_64.AdxTiledSquare
