module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamMemory
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulFirst
import VerifiedGarbage.Proof.Framework.Block

/-! A pair of arithmetic rows followed by its spill and next operand loads. -/

-- separate module: generic composition shared by all four multiplication chunks
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

theorem chunk_ok {s : State} {pa pt : Addr} {so ao : Nat} {r0 r1 : Reg}
    {code : List Instr} {out next clob : List Reg} {P B : Nat}
    (ha : Ptr s .x1 pa 72) (ht : PtrW s .x27 pt 64)
    (hs : so+16≤64) (hs8 : so%8=0) (hd : ao+16≤72) (hd8 : ao%8=0)
    (hnd : r0≠r1) (ho : out=[r0,r1]++next)
    (hc1 : .x1∉clob) (hc27 : .x27∉clob)
    (hn : ∀r∈next,r∉([.x3,.x4] : List Reg))
    (hread : ∀m,Outside pt so 16 s.mem m →
      word m pa ao=word s.mem pa ao ∧ word m pa (ao+8)=word s.mem pa (ao+8))
    (arith : WP isa (.block code) s fun u => regsVal u out=P ∧ regsVal u bRegs=B ∧ u.gpr .x2=0 ∧ Keeps clob s u) :
    WP isa (.block (code++(spillPair r0 r1 so++loadPair ao))) s fun t =>
      wordsVal t.mem pt so 2 + 2^128*regsVal t next=P ∧
      t.gpr .x3=word s.mem pa ao ∧ t.gpr .x4=word s.mem pa (ao+8) ∧
      regsVal t bRegs=B ∧ t.gpr .x2=0 ∧
      KeepRegs (.x3::.x4::clob) s t ∧ Outside pt so 16 s.mem t.mem := by
  rw [WP.block_append_iff]
  refine WP.mono arith fun u ⟨prod,bval,z,ku⟩ => ?_
  refine WP.mono (spill_load_ok (ha.of_keeps ku hc1)
    (ht.of_keepRegs (VG.Proof.Mont.AArch64.Keeps.regs ku) hc27)
    hs hs8 hd hd8 hnd (fun m hm => by
      rw [ku.mem] at hm ⊢
      exact hread m hm)) fun t ⟨stored,a0,a1,kt,ot⟩ => ?_
  have eout : regsVal u out=regsVal u [r0,r1]+2^128*regsVal u next := by
    rw [ho,regsVal_append]
    rfl
  have en : regsVal t next=regsVal u next := regsVal_congr fun r hr => kt.gpr r (hn r hr)
  have eb : regsVal t bRegs=B := by
    rw [regsVal_congr (s:=u) (fun r hr => kt.gpr r
      ((show ∀r∈bRegs,r∉([.x3,.x4] : List Reg) from by decide) r hr))]
    exact bval
  refine ⟨?_,?_,?_,eb,(kt.gpr _ (by decide)).trans z,
    ((VG.Proof.Mont.AArch64.Keeps.regs ku).mono (by sub_regs)).trans
      (kt.mono (by sub_regs)),?_⟩
  · rw [stored,en,←eout]; exact prod
  · rw [a0,ku.mem]
  · rw [a1,ku.mem]
  · rw [ku.mem] at ot; exact ot

end VG.Proof.Mont.AArch64.P521Field
