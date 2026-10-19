module

public import VerifiedGarbage.Proof.Dsa.X86_64.LoadCheckCT
public import VerifiedGarbage.Proof.Dsa.X86_64.OneScan
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroMask
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.LoadCheckCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.OneScan
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Dsa.X86_64.ZeroMask
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant time of comparing a subgroup result with one -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.X86_64 VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def OneRegs (L : Ws) (s : State) : Prop :=
  s.gpr .r12 = BitVec.ofNat 64 L.w ∧ s.gpr .rbx = off L.B (slot L.w aX)

theorem pins_oneRegs : Pins OneRegs [.r12, .rbx] :=
  pins_of (fun L r => if r = .r12 then BitVec.ofNat 64 L.w else off L.B (slot L.w aX)) (by
    intro L s h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2)

theorem oneScanHead_ct : RelCT isa (Two GoodW) (.block oneScanHead) (fun _ _ => True) := by
  change RelCT isa _ (.block (([.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aX)))] : List Instr) ++
    [.mov .r15 (.mem (at0 .rbx)), .alu .xor .r15 (.imm 1)])) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := OneRegs) [.rdi]
    (pins_of (fun L _ => L.B) (by
      intro L s ⟨_, hg, _⟩ r hr
      obtain rfl := List.mem_singleton.mp hr
      exact hg.rdi)) (by taint_decide) ?_) ?_
  · intro L s ⟨minv, hg, hz⟩
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off L.B (8 * i)) 8 :=
      fun i hi => hg.scr.ld (Nat.le_trans (hdr_lt_slot L.w 8 hi) hz)
    xrun [OneRegs, State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aX) (by decide),
      hg.hdr.hw, hg.hdr.harr aX (by decide)]
  exact two_taint [.r12, .rbx] pins_oneRegs (by taint_decide)

theorem oneScan_ct : RelCT isa (Two GoodW)
    (.seq (.block oneScanHead) (wordLoop 1 [.mov .rax (.mem (ix .rbx .r14)), .alu .or .r15 (.reg .rax)]))
    (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := OneRegs) oneScanHead_ct ?_)
    (two_taint [.r12, .rbx] pins_oneRegs (by taint_decide))
  intro L s ⟨minv, hg, hz⟩
  exact WP.mono (oneScanHead_ok hg hz) fun _ h => ⟨h.1, h.2.1⟩

theorem oneReturn_ct : RelCT isa (Two LoadedCheck)
    (.seq (.block oneScanHead) (.seq
      (wordLoop 1 [.mov .rax (.mem (ix .rbx .r14)), .alu .or .r15 (.reg .rax)])
      (.block (([.alu .cmp .r15 (.imm 1), .alu .sbb .rax (.reg .rax), Crt.leave] : List Instr) ++ Checks.accumulate))))
    (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq (two_post (Ψ := fun p s => LinkedPre p.x s)
    (two_map (fun p : BPub => p.x.ws) (fun _ _ ⟨minv, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩) oneScan_ct) ?_) ?_
  · intro p s ⟨minv, hc, hw, hw'⟩
    exact WP.mono (oneScan_ok hc.good (Nat.le_refl _) hw hw')
      fun t ⟨_, hm, hk⟩ => ⟨minv, hc.of_keep hm hk (by decide)⟩
  change RelCT isa _ (.block (([.alu .cmp .r15 (.imm 1), .alu .sbb .rax (.reg .rax)] : List Instr) ++
    (([Crt.leave] : List Instr) ++ Checks.accumulate))) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun p s => LinkedPre p.x s) []
    (by intro p s t hs ht r hr; cases hr) (by taint_decide) ?_) ?_
  · intro p s ⟨minv, hc⟩
    exact WP.mono (zeroMask_ok .r15 false) fun t ⟨_, hm, hk⟩ => ⟨minv, hc.of_keep hm hk (by decide)⟩
  exact two_map (fun p : BPub => p.x) (fun _ _ h => h) leaveAccumulate_ct

end VG.Proof.Dsa.X86_64
