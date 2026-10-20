module
public import VerifiedGarbage.Proof.Dsa.X86_64.FinishCT
public import VerifiedGarbage.Proof.Dsa.X86_64.MinusCore
public import VerifiedGarbage.Proof.Dsa.X86_64.Product

import VerifiedGarbage.Proof.Dsa.X86_64.Minus
import VerifiedGarbage.Proof.Dsa.X86_64.CallFinishCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.FinishCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.MinusCore
meta import VerifiedGarbage.Proof.Dsa.X86_64.Product
meta import VerifiedGarbage.Proof.Dsa.X86_64.Minus
meta import VerifiedGarbage.Proof.Dsa.X86_64.CallFinishCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Timing of modulus-minus constants used in DSA validation -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def MinusRegs (L : Ws) (s : State) : Prop :=
  s.gpr .r12 = BitVec.ofNat 64 L.w ∧ s.gpr .rsi = off L.B (slot L.w aN) ∧ s.gpr .rbx = off L.B (slot L.w aY)

theorem pins_minusRegs : Pins MinusRegs [.r12, .rsi, .rbx] :=
  pins_of (fun L r => if r = .r12 then BitVec.ofNat 64 L.w else if r = .rsi then off L.B (slot L.w aN)
    else off L.B (slot L.w aY)) (by
      intro L s h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2)

theorem minusHead_ct (amount : Nat) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.r12, .rsi, .rbx]) (.block
      [.mov .rax (.mem (at0 .rsi)), .alu .sub .rax (.imm (BitVec.ofNat 32 amount)),
        .store (at0 .rbx) .rax, cfToRbp]) hc).isSome = true) :
    RelCT isa (Two GoodW) (.block (minusHead amount)) (fun _ _ => True) := by
  change RelCT isa _ (.block (([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN))),
      .mov .rbx (.mem (hdr (sArr aY)))] : List Instr) ++
    [.mov .rax (.mem (at0 .rsi)), .alu .sub .rax (.imm (BitVec.ofNat 32 amount)), .store (at0 .rbx) .rax, cfToRbp])) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := MinusRegs) [.rdi]
    (pins_of (fun L _ => L.B) (by
      intro L s ⟨_, hg, _⟩ r hr
      obtain rfl := List.mem_singleton.mp hr
      exact hg.rdi)) (by taint_decide) ?_)
    (two_taint [.r12, .rsi, .rbx] pins_minusRegs hT)
  intro L s ⟨minv, hg, hz⟩
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off L.B (8 * i)) 8 :=
    fun i hi => hg.scr.ld (Nat.le_trans (hdr_lt_slot L.w 8 hi) hz)
  xrun [MinusRegs, State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aN) (by decide),
    hl (sArr aY) (by decide), hg.hdr.hw, hg.hdr.harr aN (by decide), hg.hdr.harr aY (by decide)]

theorem minusCore_ct (amount : Nat) (ha : amount < 2 ^ 31) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.r12, .rsi, .rbx]) (.block
      [.mov .rax (.mem (at0 .rsi)), .alu .sub .rax (.imm (BitVec.ofNat 32 amount)),
        .store (at0 .rbx) .rax, cfToRbp]) hc).isSome = true) :
    RelCT isa (Two GoodW) (.seq (.block (minusHead amount)) (wordLoop 1 minusTail)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := MinusRegs) (minusHead_ct amount hT) ?_)
    (two_taint [.r12, .rsi, .rbx] pins_minusRegs (by taint_decide))
  intro L s ⟨minv, hg, hz⟩
  exact WP.mono (minusHead_ok hg hz ha) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

structure MinusPublic (amount : Nat) extends BPub where
  minv : BitVec 64
  modulus : Nat
  lower : 2 ≤ x.wx
  upper : x.wx < 2 ^ 31
  enough : amount ≤ modulus

def MinusPre {amount : Nat} (p : MinusPublic amount) (s : State) : Prop :=
  SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx p.minv ∧
  ModCtx s (off p.x.B p.x.o) (slot p.x.wx 8) p.x.wx p.minv p.modulus ∧ FinishPre p.toBPub s

theorem minusFinish_ct (amount : Nat) (ha : amount < 2 ^ 31) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.r12, .rsi, .rbx]) (.block
      [.mov .rax (.mem (at0 .rsi)), .alu .sub .rax (.imm (BitVec.ofNat 32 amount)),
        .store (at0 .rbx) .rax, cfToRbp]) hc).isSome = true) :
    RelCT isa (Two (@MinusPre amount))
      (.seq (.seq (.block (minusHead amount)) (wordLoop 1 minusTail)) (seqs Core.finish)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun p s => FinishPre p.toBPub s)
    (two_map (fun p : MinusPublic amount => p.x.ws)
      (fun _ _ h => ⟨_, h.1.good, Nat.le_refl _⟩) (minusCore_ct amount ha hT)) ?_)
    (two_map MinusPublic.toBPub (fun _ _ h => h) finish_ct)
  intro p s ⟨hc, hm, hf⟩
  exact WP.mono (minus_ok hc hm p.lower p.upper ha p.enough)
    fun t ⟨hct, _, _, hft, hkt⟩ => hf.work hc hct hft hkt

end VG.Proof.Dsa.X86_64
