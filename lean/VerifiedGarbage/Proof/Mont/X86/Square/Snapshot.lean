module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
import VerifiedGarbage.Proof.Mont.X86.Square.EndCtl
public import VerifiedGarbage.Proof.Mont.X86.Square.Width
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Proof.Mont.X86.Square.Packed
import VerifiedGarbage.Proof.Mont.X86.Square.Store
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def snapshot : List Instr := [.movqStore (sc 20) .xmm0] ++ widthTest

theorem snapshot_ok {s : State} {W : Addr} {L S N k l : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (hw : Ws s W L) (sl : S+20+8≤L)
    (hN : N=2*(A 2).toNat) (h8 : 8*N<2^32) (hk : k<2*N)
    (edi : PtrAt s W .edi S) (si : s.gpr .esi = BitVec.ofNat 32 (4*k))
    (low : s.xmm .xmm0 = packed (BitVec.ofNat 64 l)) :
    WP isa (.block snapshot) s fun t =>
      t.mem = s.mem.writeW (off W (S+20)) (BitVec.ofNat 64 l) ∧
      t.cf = some (decide (k<N)) ∧ Keeps [.eax] s t ∧ t.xmm = s.xmm := by
  unfold snapshot
  apply WP.block_append
  refine WP.mono (storePacked_ok hw edi sl low) fun t1 eq => ?_
  subst t1
  have K1 := writeState_keep s (off W (S+20)) (BitVec.ofNat 64 l)
  have O : Outside W (S+20) 8 s.mem (writeState s (off W (S+20)) (BitVec.ofNat 64 l)).mem := by
    exact writeW_outside _ _ _ (by have := hw.nowrap; omega)
  have ha1 := ha.of_keeps K1 (by simp) (Outs.of_outside (O.mono (Nat.zero_le _) (by omega)) (List.mem_singleton_self _))
  refine WP.mono (widthTest_ok ha1 hN h8 hk si) fun t ⟨cf, mem, keep, xmm⟩ => ?_
  exact ⟨mem, cf, (K1.mono (by simp)).trans keep, xmm⟩

end VG.Proof.Mont.X86.Square
