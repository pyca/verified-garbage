module
public import VerifiedGarbage.Proof.Dsa.AArch64.FinishCT
public import VerifiedGarbage.Proof.Dsa.AArch64.MinusHead
public import VerifiedGarbage.Proof.Dsa.AArch64.MinusStep
public import VerifiedGarbage.Proof.Dsa.AArch64.Product

import VerifiedGarbage.Proof.Dsa.AArch64.Minus
import VerifiedGarbage.Proof.Dsa.AArch64.CTBlocks
import VerifiedGarbage.Proof.Dsa.AArch64.CallFinishCT
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.FinishCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.MinusHead
meta import VerifiedGarbage.Proof.Dsa.AArch64.MinusStep
meta import VerifiedGarbage.Proof.Dsa.AArch64.Product
meta import VerifiedGarbage.Proof.Dsa.AArch64.Minus
meta import VerifiedGarbage.Proof.Dsa.AArch64.CTBlocks
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallFinishCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Timing of modulus-minus constants used in DSA validation -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def MinusRegs (L : Ws) (s : State) : Prop :=
  s.gpr .x14 = BitVec.ofNat 64 L.w ∧ s.gpr .x16 = off L.B (slot L.w aN) ∧ s.gpr .x17 = off L.B (slot L.w aY)

theorem pins_minusRegs : Pins MinusRegs [.x14, .x16, .x17] :=
  pins_of (fun L r => if r = .x14 then BitVec.ofNat 64 L.w else if r = .x16 then off L.B (slot L.w aN)
    else off L.B (slot L.w aY)) (by
      intro L s h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2)

def minusRest (amount : Nat) : Prog isa :=
  .seq (.block ([movi .x4 amount, movi .x7 0, ld .x3 .x16, .subs .x .x3 .x3 .x4,
      st .x3 .x17, next .x16, next .x17, .subImm .x .x14 .x14 1] : List Instr)) (countLoop .x14 minusTail)

theorem minusCore_ct (amount : Nat) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x14, .x16, .x17]) (minusRest amount) hc).isSome = true) :
    RelCT isa (Two GoodW) (.seq (.block (minusHead amount)) (countLoop .x14 minusTail)) (fun _ _ => True) := by
  apply fuseBlocks_ct (a := [ldh .x14 sW, ldh .x16 (sArr aN), ldh .x17 (sArr aY)])
  refine RelCT.seq (two_piece (Ψ := MinusRegs) [.x0]
    (pins_of (fun L _ => L.B) (by
      intro L s ⟨_, hg, _⟩ r hr
      obtain rfl := List.mem_singleton.mp hr
      exact hg.x0)) (by taint_decide) ?_)
    (two_taint [.x14, .x16, .x17] pins_minusRegs hT)
  intro L s ⟨minv, hg, hz⟩
  brun [MinusRegs, hg.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show sArr aN < 32 by decide),
    hdr_enc (show sArr aY < 32 by decide), hg.ld hz (show sW < 32 by decide),
    hg.ld hz (show sArr aN < 32 by decide), hg.ld hz (show sArr aY < 32 by decide),
    hg.hdr.hw, hg.hdr.harr aN (by decide), hg.hdr.harr aY (by decide)]

structure MinusPublic (amount : Nat) extends BPub where
  minv : BitVec 64
  modulus : Nat
  lower : 2 ≤ x.wx
  upper : x.wx < 2 ^ 31
  enough : amount ≤ modulus

def MinusPre {amount : Nat} (p : MinusPublic amount) (s : State) : Prop :=
  SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx p.minv ∧
  ModCtx s (off p.x.B p.x.o) (slot p.x.wx 8) p.x.wx p.minv p.modulus ∧ FinishPre p.toBPub s

theorem minusFinish_ct (amount : Nat) (ha : amount < 2 ^ 16) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x14, .x16, .x17]) (minusRest amount) hc).isSome = true) :
    RelCT isa (Two (@MinusPre amount))
      (.seq (.seq (.block (minusHead amount)) (countLoop .x14 minusTail)) (seqs Core.finish)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun p s => FinishPre p.toBPub s)
    (two_map (fun p : MinusPublic amount => p.x.ws)
      (fun _ _ h => ⟨_, h.1.good, Nat.le_refl _⟩) (minusCore_ct amount hT)) ?_)
    (two_map MinusPublic.toBPub (fun _ _ h => h) finish_ct)
  intro p s ⟨hc, hm, hf⟩
  exact WP.mono (minus_ok hc hm p.lower p.upper ha p.enough)
    fun t ⟨hct, _, _, hft, hkt⟩ => hf.work hc hct hft hkt

end VG.Proof.Dsa.AArch64
