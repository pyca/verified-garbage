module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! A vector tile leaks only public addresses; the table digit remains secret. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt

/-- The selection's hypotheses for a table of `n` entries: `SelP` of
`CrtCTExp.lean` at 16, and of `CrtWindowTableCT.lean` at 32. -/
def SelPn (n : Nat) (p : XPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (X Xc v : Nat), CExpCtx s (off p.B p.o) p.wx minv X Xc n ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧
    v < n ∧ word s.mem (off p.B p.o) (8 * Crt.sTab) = off (off p.B p.o) (slot p.wx 8) ∧
    word s.mem (off p.B p.o) (8 * Crt.sNib) = BitVec.ofNat 64 v

def StepPre (n : Nat) (q : XPub × Nat) (s : State) : Prop :=
  ∃ mi X Xc v, CExpCtx s (off q.1.B q.1.o) q.1.wx mi X Xc n ∧
    word s.mem (off q.1.B q.1.o) (8 * Crt.sTab) = off (off q.1.B q.1.o) (slot q.1.wx 8) ∧
    s.gpr .x6 = BitVec.ofNat 64 (8 * (q.1.wx + 2)) ∧
    s.gpr .x17 = off (off q.1.B q.1.o) (slot q.1.wx Crt.aT + 64 * q.2) ∧
    s.v .v22 = dup2 (BitVec.ofNat 64 v) ∧ s.v .v24 = dup2 1

def ScanPins (n : Nat) (q : XPub × Nat) (s : State) : Prop :=
  s.gpr .x16 = off (off q.1.B q.1.o) (slot q.1.wx 8 + 64 * q.2) ∧
  s.gpr .x6 = BitVec.ofNat 64 (8 * (q.1.wx + 2)) ∧
  s.gpr .x14 = BitVec.ofNat 64 n ∧
  s.gpr .x17 = off (off q.1.B q.1.o) (slot q.1.wx Crt.aT + 64 * q.2)

theorem step_pins (n : Nat) : Pins (StepPre n) [.x0,.x17] := by
  intro q s t hs ht r hr
  obtain ⟨_,_,_,_,cs,_,_,ps,_⟩ := hs
  obtain ⟨_,_,_,_,ct,_,_,pt,_⟩ := ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact cs.good.x0.trans ct.good.x0.symm
  · exact ps.trans pt.symm

theorem scan_pins (n : Nat) : Pins (ScanPins n) [.x16,.x6,.x14,.x17] := by
  intro q s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hs.1.trans ht.1.symm
  · exact hs.2.1.trans ht.2.1.symm
  · exact hs.2.2.1.trans ht.2.2.1.symm
  · exact hs.2.2.2.trans ht.2.2.2.symm

theorem step_ct {n : Nat} (hN : n = 16 ∨ n = 32) :
    RelCT isa (Two (StepPre n)) (rawStep n) (fun _ _ => True) := by
  rcases hN with rfl | rfl
  · unfold rawStep
    refine RelCT.seq (two_piece (Ψ := ScanPins 16) [.x0,.x17] (step_pins 16) (by taint_decide) ?_)
      (two_taint [.x16,.x6,.x14,.x17] (scan_pins 16) (by taint_decide))
    rintro q s ⟨mi,X,Xc,v,hc,ht,h6,h17,h22,h24⟩
    exact WP.mono (startScan_ok (by decide) hc ht h17 h22 h24) fun u ⟨h14,h0,_,ku⟩ =>
      ⟨by simpa using h0.ptr, (ku.gpr .x6 (by decide)).trans h6, h14,
        (ku.gpr .x17 (by decide)).trans h17⟩
  · unfold rawStep
    refine RelCT.seq (two_piece (Ψ := ScanPins 32) [.x0,.x17] (step_pins 32) (by taint_decide) ?_)
      (two_taint [.x16,.x6,.x14,.x17] (scan_pins 32) (by taint_decide))
    rintro q s ⟨mi,X,Xc,v,hc,ht,h6,h17,h22,h24⟩
    exact WP.mono (startScan_ok (by decide) hc ht h17 h22 h24) fun u ⟨h14,h0,_,ku⟩ =>
      ⟨by simpa using h0.ptr, (ku.gpr .x6 (by decide)).trans h6, h14,
        (ku.gpr .x17 (by decide)).trans h17⟩

end VG.Proof.Bignum.AArch64.WindowVector
