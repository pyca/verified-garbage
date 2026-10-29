module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
meta import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! Exponent bytes remain secret; their addresses are public. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.WindowFive (loadGroup groupBytes loadTailByte)

def ReadPre (p : XPub × Addr × Nat) (s : State) : Prop :=
  ∃ mi X Xc, TableCtx s (off p.1.B p.1.o) p.1.wx mi X Xc ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sExp) = p.2.1 ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sI) = BitVec.ofNat 64 p.2.2

def ReadReady (p : XPub × Addr × Nat) (s : State) : Prop :=
  s.gpr .x0 = off p.1.B p.1.o ∧ s.gpr .x3 = p.2.1 + BitVec.ofNat 64 p.2.2

theorem readAddr_ct : RelCT isa (Two ReadPre) (.block byteAddr) (Two ReadReady) := by
  refine two_post (x0_ct (fun p : XPub × Addr × Nat => off p.1.B p.1.o)
    (fun _ _ ⟨_,_,_,hc,_⟩ => hc.good.x0) (by taint_decide)) ?_
  rintro p s ⟨mi,X,Xc,hc,he,hi⟩
  exact WP.mono (byteAddr_run hc.base he hi) fun t ⟨h3,kt⟩ =>
    ⟨(kt.gpr .x0 (by decide)).trans hc.good.x0,h3⟩

theorem pins_readReady : Pins ReadReady [.x0,.x3] := by
  intro p s t hs ht r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.1.trans ht.1.symm
  · exact hs.2.trans ht.2.symm

theorem loadGroup_ct : RelCT isa (Two ReadPre) (.block loadGroup) (fun _ _ => True) := by
  change RelCT isa (Two ReadPre)
    (.block (byteAddr ++ ([movi .x4 0] ++ groupBytes 5 ++ [sth .x4 Crt.sV]))) _
  exact RelCT.block_append (RelCT.seq readAddr_ct (two_taint [.x0,.x3] pins_readReady (by taint_decide)))

theorem loadTailByte_ct : RelCT isa (Two ReadPre) (.block loadTailByte) (fun _ _ => True) := by
  change RelCT isa (Two ReadPre)
    (.block (byteAddr ++ [.ldrb .x3 .x3 0,sth .x3 Crt.sV])) _
  exact RelCT.block_append (RelCT.seq readAddr_ct (two_taint [.x0,.x3] pins_readReady (by taint_decide)))

end VG.Proof.Bignum.AArch64.WindowFive
