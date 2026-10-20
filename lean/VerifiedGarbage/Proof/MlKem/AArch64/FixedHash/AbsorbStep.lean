module
public import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
public import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.WordSemantic
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Word
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Proof.Sha3 (xorAt)

theorem absorbWord_piece_ok {s₀ s : State} {sc : Reg} {st wk rate pos i : Nat} {p : Piece}
 (hS : HSetup sc st wk rate s₀) (hp : PieceOk sc st wk s₀ false p) (hg : Rg s₀ s)
 (hi : i+8≤p.len) (ho : p.off+i<65536) (hpos : pos+8≤rate)
 (hd : (st+pos)%8=0 ∧ st+pos<32768) :
 WP isa (.block (ptrTo .x2 p.base (p.off+i) ++
   ([.ldr .x .x9 .x2 0,.ldr .x .x10 sc (st+pos),.logic .eor .x .x9 .x9 .x10,
     .str .x .x9 sc (st+pos)] : List Instr))) s fun t=>
 Kept [STr sc st s₀] s t ∧
 stateAt t.mem (s₀.gpr sc+BitVec.ofNat 64 st)=
   xorAt (stateAt s.mem (s₀.gpr sc+BitVec.ofNat 64 st)) pos
     (bytesAt s.mem (s₀.gpr p.base+BitVec.ofNat 64 (p.off+i)) 8) := by
 have ns : sc≠.x2 ∧ sc≠.x9 ∧ sc≠.x10 := by
   have all : ∀r∈preserved,r≠.x2 ∧ r≠.x9 ∧ r≠.x10 := by decide
   exact all sc hS.hsc.1
 have nb : p.base≠.x2 := (pres_not hp.base.1).2.2.1
 have gs := hg.cs sc hS.hsc.1 hS.hsc.2
 have gb := hg.cs p.base hp.base.1 hp.base.2
 have addr : s.gpr sc+BitVec.ofNat 64 (st+pos)=s₀.gpr sc+BitVec.ofNat 64 st+BitVec.ofNat 64 pos := by
   rw [gs,BitVec.add_assoc,←BitVec.ofNat_add]
 have cs : (STr sc st s₀).Contains (s.gpr sc+BitVec.ofNat 64 (st+pos)) 8 := by
   rw [addr]
   exact Offset.contains_base _ (by have:= (rate_bounds hS.hrate).2; omega) (by have:= (rate_bounds hS.hrate).2; omega)
 refine WP.mono (absorbWord_ok nb ns.1 ns.2.1 ns.2.2 ho hd ?_ ?_) fun t ⟨kt,mt⟩=> ?_
 · rw [hg.rd,hg.wr,gb]
   apply hp.cov
   refine ⟨preg s₀ p,List.mem_singleton_self _,?_⟩
   rw [BitVec.ofNat_add,←BitVec.add_assoc]
   exact Offset.contains_base _ hi (by have:=hp.len; omega)
 · rw [hg.wr]
   exact hS.cov _ _ ⟨_,List.mem_cons_self ..,cs⟩
 · refine ⟨⟨fun r hr hn=>kt.gpr r (by revert r hr; decide),kt.sp,kt.rd,kt.wr,?_,kt.vcs⟩,?_⟩
   · rw [mt]
     exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cs
   · rw [mt,addr,gb]
     exact absorbWord_state _ _ _ (by have:= (rate_bounds hS.hrate).2; omega)
theorem absorbByte_piece_ok {s₀ s : State} {sc : Reg} {st wk rate pos i : Nat} {p : Piece}
 (hS : HSetup sc st wk rate s₀) (hp : PieceOk sc st wk s₀ false p) (hg : Rg s₀ s)
 (hi : i+1≤p.len) (ho : p.off+i<65536) (hpos : pos+1≤rate)
 (hd : st+pos<4096) :
 WP isa (.block (ptrTo .x2 p.base (p.off+i) ++
   ([.ldrb .x9 .x2 0,.ldrb .x10 sc (st+pos),.logic .eor .x .x9 .x9 .x10,
     .strb .x9 sc (st+pos)] : List Instr))) s fun t=>
 Kept [STr sc st s₀] s t ∧
 stateAt t.mem (s₀.gpr sc+BitVec.ofNat 64 st)=
   xorAt (stateAt s.mem (s₀.gpr sc+BitVec.ofNat 64 st)) pos
     (bytesAt s.mem (s₀.gpr p.base+BitVec.ofNat 64 (p.off+i)) 1) := by
 have ns : sc≠.x2 ∧ sc≠.x9 ∧ sc≠.x10 := by
   have all : ∀r∈preserved,r≠.x2 ∧ r≠.x9 ∧ r≠.x10 := by decide
   exact all sc hS.hsc.1
 have nb : p.base≠.x2 := (pres_not hp.base.1).2.2.1
 have gs := hg.cs sc hS.hsc.1 hS.hsc.2
 have gb := hg.cs p.base hp.base.1 hp.base.2
 have addr : s.gpr sc+BitVec.ofNat 64 (st+pos)=s₀.gpr sc+BitVec.ofNat 64 st+BitVec.ofNat 64 pos := by
   rw [gs,BitVec.add_assoc,←BitVec.ofNat_add]
 have cs : (STr sc st s₀).Contains (s.gpr sc+BitVec.ofNat 64 (st+pos)) 1 := by
   rw [addr]
   exact Offset.contains_base _ (by have:= (rate_bounds hS.hrate).2; omega) (by have:= (rate_bounds hS.hrate).2; omega)
 refine WP.mono (absorbByte_ok nb ns.1 ns.2.1 ns.2.2 ho hd ?_ ?_) fun t ⟨kt,mt⟩=> ?_
 · rw [hg.rd,hg.wr,gb]
   apply hp.cov
   refine ⟨preg s₀ p,List.mem_singleton_self _,?_⟩
   rw [BitVec.ofNat_add,←BitVec.add_assoc]
   exact Offset.contains_base _ hi (by have:=hp.len; omega)
 · rw [hg.wr]
   exact hS.cov _ _ ⟨_,List.mem_cons_self ..,cs⟩
 · refine ⟨⟨fun r hr hn=>kt.gpr r (by revert r hr; decide),kt.sp,kt.rd,kt.wr,?_,kt.vcs⟩,?_⟩
   · rw [mt]
     exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cs
   · rw [mt,addr,gb]
     simpa [bytesAt,Proof.Sha3.xorAt_single] using
       absorbByte_state s.mem (s₀.gpr sc+BitVec.ofNat 64 st)
         (s₀.gpr p.base+BitVec.ofNat 64 (p.off+i)) (by have:= (rate_bounds hS.hrate).2; omega)
end VG.Proof.MlKem.AArch64.FixedHash
