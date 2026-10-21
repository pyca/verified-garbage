module

import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Args
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Finish
public import VerifiedGarbage.Proof.Mont.X86.Rt.RowFull
import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.RowsFinal
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.RowsLoop
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Store
public import VerifiedGarbage.Impl.Mont.X86

@[expose] public section

namespace VG.Proof.Mont.X86.PreparedSquare
open VG.Proof.Mont.X86.Square
open VG.Impl.Mont.X86.PreparedSquare
open VG VG.X86 VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem store_top_value (mem : Mem) (W : Addr) {L S N c : Nat}
    (nw : W.toNat+L≤2^32) (sl : S+24+8*N+8≤L) (cc : c<2^32) :
    val32 (mem.writeW (off W (S+24+8*N)) (BitVec.ofNat 64 c)) W (S+24+4*N) (N+1) =
      val32 mem W (S+24+4*N) N+(2^32)^N*c := by
  have O := writeW_outside mem W (d := S+24+8*N) (BitVec.ofNat 64 c) (by omega)
  rw [val32_succ,O.val32 (by omega) (by omega),show S+24+4*N+4*N=S+24+8*N by omega,
    write64_w32,Nat.mod_eq_of_lt cc,← pow32]

theorem columns_ok {s : State} {W : Addr} {L S m inv a o N : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (hw : Ws s W L) (V : ArgVals A W N S m inv o a a)
    (lay : VG.Proof.Mont.X86.PreparedSquare.Lay L N S m inv a a) (np : 0<N)
    (edi : PtrAt s W .edi S) (hinv : (w32 s.mem W m*w32 s.mem W inv+1)%2^32=0)
    (hlt : val32 s.mem W a N<val32 s.mem W m N) :
    WP isa VG.Impl.Mont.X86.PreparedSquare.columns s fun u => Outside W S (8*N+32) s.mem u.mem ∧
      Outs W [(S+16,8),(S+24,8*N+8)] s.mem u.mem ∧ PtrAt u W .ebp (S+24+4*N) ∧
      val32 u.mem W (S+24+4*N) (N+1)<2*val32 s.mem W m N ∧
      (∃ q,(2^32)^N*val32 u.mem W (S+24+4*N) (N+1)=
        val32 s.mem W a N*val32 s.mem W a N+q*val32 s.mem W m N) ∧
      Keeps [.eax,.edx,.ecx,.ebp,.ebx,.esi] s u := by
  have n : N=2*(A 2).toNat := by have := V.n;omega
  have nw := hw.nowrap
  have sl : S+24+8*N+8≤L := by have := lay.scr;omega
  have h4 : 4*N<2^32 := by have := lay.scr;omega
  have body : WP isa (.seq (.seq (.block initCode) (.loop VG.Impl.Mont.X86.PreparedSquare.column .ne)) (.block finishCode)) s fun u =>
      Outside W S (8*N+32) s.mem u.mem ∧
      Outs W [(S+16,8),(S+24,8*N+8)] s.mem u.mem ∧ PtrAt u W .ebp (S+24+4*N) ∧
      val32 u.mem W (S+24+4*N) (N+1)<2*val32 s.mem W m N ∧
      (∃ q,(2^32)^N*val32 u.mem W (S+24+4*N) (N+1)=
        val32 s.mem W a N*val32 s.mem W a N+q*val32 s.mem W m N) ∧
      Keeps [.eax,.edx,.ecx,.ebp,.ebx,.esi] s u := by
    refine WP.seq (WP.mono (start_ok ha hw V lay np edi hinv) fun t ⟨c,I⟩ => ?_)
    have final := I.final_bound hlt
    have cc : c<2^32 := by have := final.2;omega
    have haT := ha.of_keeps I.keep (by decide)
      (Outs.of_outside (I.out.mono (Nat.zero_le _) (by have := lay.scr;omega)) (List.mem_singleton_self _))
    have count : t.gpr .esi=BitVec.ofNat 32 (8*N) := by simpa only [show 4*(2*N)=8*N by omega] using I.count
    refine WP.mono (finish_ok haT I.ws n h4 sl I.edi count I.carry) fun u ⟨memU,bpU,KU⟩ => ?_
    have O : Outside W (S+24+8*N) 8 t.mem u.mem := by
      rw [memU]
      exact writeW_outside _ _ _ (by omega)
    have Oall : Outside W S (8*N+32) t.mem u.mem := O.mono (by omega) (by have := lay.scr;omega)
    have F : Outs W [(S+16,8),(S+24,8*N+8)] t.mem u.mem :=
      Outs.of_outside (O.mono (by omega : S+24≤S+24+8*N) (by omega : S+24+8*N+8≤S+24+(8*N+8))) (by simp)
    have value : val32 u.mem W (S+24+4*N) (N+1)=val32 t.mem W (S+24+4*N) N+(2^32)^N*c := by
      rw [memU]
      exact store_top_value _ _ nw sl cc
    refine ⟨I.out.trans Oall,I.frame.trans F,bpU,?_,?_,I.keep.trans (KU.mono (by decide))⟩
    · rw [value];exact final.1
    · refine ⟨val32 t.mem W (S+24) N,?_⟩
      rw [value]
      exact I.final_eq
  simpa only [VG.Impl.Mont.X86.PreparedSquare.columns,VG.Impl.Mont.X86.PreparedSquare.seqs,initCode,finishCode,finishPtr,finishTail,
    List.cons_append,List.nil_append] using WP.assoc body

end VG.Proof.Mont.X86.PreparedSquare
