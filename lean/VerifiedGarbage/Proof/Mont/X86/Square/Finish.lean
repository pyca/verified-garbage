module

public import VerifiedGarbage.Proof.Mont.X86.Square.RowsFinal

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def finishPtr : List Instr := [.mov .ebp (.reg .edi), .alu .add .ebp (.imm 52), .alu .add .ebp (.reg .esi)]
def finishTail : List Instr := lenTimes .eax 0 ++ [.alu .sub .ebp (.reg .eax)]
def finishCode : List Instr := finishPtr ++ [.movqStore (at_ .ebp 0) .xmm3] ++ finishTail

theorem finishPtr_ok {s : State} {W : Addr} {S N : Nat}
    (edi : PtrAt s W .edi S) (si : s.gpr .esi=BitVec.ofNat 32 (8*N)) :
    WP isa (.block finishPtr) s fun t => PtrAt t W .ebp (S+52+8*N) ∧
      t.mem=s.mem ∧ Keeps [.ebp] s t ∧ t.xmm=s.xmm := by
  have body : WP isa (.block finishPtr) s fun t => PtrAt t W .ebp (S+52+8*N) ∧
      t.mem=s.mem ∧ Keeps [.ebp] s t := by
    unfold finishPtr
    refine wp_movS rfl fun t1 u1 _ => wp_addS rfl fun t2 u2 _ => wp_addS rfl fun t3 u3 _ => WP.block_nil ?_
    have ed : s.gpr .edi=BitVec.ofNat 32 (W.toNat+S) := by
      apply BitVec.eq_of_toNat_eq; rw [edi,BitVec.toNat_ofNat]
    refine ⟨?_,u3.mem.trans (u2.mem.trans u1.mem),u1.keeps.trans (u2.keeps.trans u3.keeps)⟩
    rw [PtrAt,u3.gpr,u2.gpr,u1.gpr,ed,u2.other _ (by decide),u1.other _ (by decide),si]
    change (((BitVec.ofNat 32 (W.toNat+S)+BitVec.ofNat 32 52)+BitVec.ofNat 32 (8*N))).toNat = _
    rw [← BitVec.ofNat_add,← BitVec.ofNat_add,BitVec.toNat_ofNat];congr 1;omega
  exact WP.mono (scalar_frame (by simp [finishPtr,scalar]) body)
    fun t ⟨⟨p,mem,keep⟩,xmm⟩ => ⟨p,mem,keep,xmm⟩

theorem finishTail_ok {s : State} {W : Addr} {L S N : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (hN : N=2*(A 2).toNat) (h4 : 4*N<2^32)
    (ptr : PtrAt s W .ebp (S+52+8*N)) :
    WP isa (.block finishTail) s fun t => PtrAt t W .ebp (S+52+4*N) ∧ t.mem=s.mem ∧ Keeps [.eax,.ebp] s t := by
  unfold finishTail
  apply WP.block_append
  refine WP.mono (lenTimes_ok ha (r := .eax) 0) fun t1 ⟨len,mem,K⟩ => ?_
  have ea : t1.gpr .eax=BitVec.ofNat 32 (4*N) := by
    apply BitVec.eq_of_toNat_eq;rw [len,BitVec.toNat_ofNat,hN];congr 1;omega
  have bp : PtrAt t1 W .ebp (S+52+8*N) := by rw [PtrAt,K.1 _ (by decide)];exact ptr
  refine wp_subS rfl fun t2 u2 _ => WP.block_nil ?_
  refine ⟨?_,u2.mem.trans mem,(K.mono (by decide)).trans (u2.keeps.mono (by decide))⟩
  rw [PtrAt,u2.gpr,ea]
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt h4,show S+52+8*N-4*N=S+52+4*N by omega] using
    ptr_sub bp (BitVec.ofNat 32 (4*N)) (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt h4];omega)

theorem finish_ok {s : State} {W : Addr} {L S N c : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (hw : Ws s W L) (hN : N=2*(A 2).toNat) (h4 : 4*N<2^32)
    (sl : S+52+8*N+8≤L) (edi : PtrAt s W .edi S) (si : s.gpr .esi=BitVec.ofNat 32 (8*N))
    (carry : s.xmm .xmm3=packed (BitVec.ofNat 64 c)) :
    WP isa (.block finishCode) s fun t =>
      t.mem=s.mem.writeW (off W (S+52+8*N)) (BitVec.ofNat 64 c) ∧
      PtrAt t W .ebp (S+52+4*N) ∧ Keeps [.eax,.ebp] s t := by
  unfold finishCode
  rw [List.append_assoc]
  apply WP.block_append
  refine WP.mono (finishPtr_ok edi si) fun t1 ⟨p1,m1,K1,x1⟩ => ?_
  have hw1 := hw.of_keeps K1
  have ha1 := ha.of_keeps K1 (by decide) (by rw [m1];exact Outs.refl _ _ _)
  apply WP.block_append
  refine WP.mono (storePacked_ok hw1 p1 (by simpa using sl) (by rw [x1];exact carry)) fun t2 eq => ?_
  subst t2
  have K2 := writeState_keep t1 (off W (S+52+8*N+0)) (BitVec.ofNat 64 c)
  have O : Outside W (S+52+8*N) 8 t1.mem (writeState t1 (off W (S+52+8*N+0)) (BitVec.ofNat 64 c)).mem := by
    simp only [writeState,Nat.add_zero]
    exact writeW_outside _ _ _ (by have := hw.nowrap;omega)
  have ha2 := ha1.of_keeps K2 (by simp)
    (Outs.of_outside (O.mono (Nat.zero_le _) (by omega)) (List.mem_singleton_self _))
  have p2 : PtrAt (writeState t1 (off W (S+52+8*N+0)) (BitVec.ofNat 64 c)) W .ebp (S+52+8*N) := by
    rw [PtrAt,K2.1 _ (by simp)];exact p1
  refine WP.mono (finishTail_ok ha2 hN h4 p2) fun t ⟨p3,m3,K3⟩ => ?_
  refine ⟨?_,p3,(K1.mono (by decide)).trans ((K2.mono (by simp)).trans K3)⟩
  simpa only [writeState,Nat.add_zero,m1] using m3

end VG.Proof.Mont.X86.Square
