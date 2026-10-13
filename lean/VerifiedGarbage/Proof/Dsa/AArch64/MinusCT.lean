module

public import VerifiedGarbage.Proof.Dsa.AArch64.Minus
meta import VerifiedGarbage.Proof.Dsa.AArch64.Minus
public import VerifiedGarbage.Proof.Dsa.AArch64.CallFinishCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallFinishCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Timing of modulus-minus constants used in DSA validation -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- After `minusHead`'s loads from the header. -/
def MinusRegs (L : Ws) (s : State) : Prop :=
  s.gpr .x12 = BitVec.ofNat 64 L.w ∧ s.gpr .x16 = off L.B (slot L.w aN) ∧ s.gpr .x17 = off L.B (slot L.w aY)

theorem pins_minusRegs : Pins MinusRegs [.x12, .x16, .x17] :=
  pins_of (fun L r => if r = .x12 then BitVec.ofNat 64 L.w else if r = .x16 then off L.B (slot L.w aN)
    else off L.B (slot L.w aY)) (by
      intro L s h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2)

/-- Before `minusLoop`. -/
def MinusLoopRegs (L : Ws) (s : State) : Prop :=
  s.gpr .x14 = BitVec.ofNat 64 (L.w - 1) ∧ s.gpr .x16 = off L.B (slot L.w aN + 8) ∧
    s.gpr .x17 = off L.B (slot L.w aY + 8)

theorem pins_minusLoopRegs : Pins MinusLoopRegs [.x14, .x16, .x17] :=
  pins_of (fun L r => if r = .x14 then BitVec.ofNat 64 (L.w - 1) else if r = .x16 then off L.B (slot L.w aN + 8)
    else off L.B (slot L.w aY + 8)) (by
      intro L s h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2)

/-- A workspace of at least one word. -/
def MinusW (L : Ws) (s : State) : Prop := GoodW L s ∧ 1 ≤ L.w

theorem minusHead_ct (amount : Nat) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x12, .x16, .x17]) (.block
      [movi .x7 0, movi .x4 amount, ld .x3 .x16, .subs .x .x3 .x3 .x4, st .x3 .x17, next .x16, next .x17,
        .subImm .x .x14 .x12 1]) hc).isSome = true) :
    RelCT isa (Two GoodW) (.block (minusHead amount)) (fun _ _ => True) := by
  change RelCT isa _ (.block (([ldh .x12 sW, ldh .x16 (sArr aN), ldh .x17 (sArr aY)] : List Instr) ++
    [movi .x7 0, movi .x4 amount, ld .x3 .x16, .subs .x .x3 .x3 .x4, st .x3 .x17, next .x16, next .x17,
      .subImm .x .x14 .x12 1])) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := MinusRegs) [.x0] pins_goodW (by taint_decide) ?_)
    (two_taint [.x12, .x16, .x17] pins_minusRegs hT)
  intro L s ⟨minv, hg, hz⟩
  brun [MinusRegs, hg.x0, hdr_enc (show sW < 32 by decide), hdr_enc (sArr_lt (show aN < 8 by decide)),
    hdr_enc (sArr_lt (show aY < 8 by decide)), hg.ld hz (show sW < 32 by decide),
    hg.ld hz (sArr_lt (show aN < 8 by decide)), hg.ld hz (sArr_lt (show aY < 8 by decide)), hg.hdr.hw,
    hg.hdr.harr aN (by decide), hg.hdr.harr aY (by decide)]

theorem minusCore_ct (amount : Nat) (ha : amount < 2 ^ 16) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x12, .x16, .x17]) (.block
      [movi .x7 0, movi .x4 amount, ld .x3 .x16, .subs .x .x3 .x3 .x4, st .x3 .x17, next .x16, next .x17,
        .subImm .x .x14 .x12 1]) hc).isSome = true) :
    RelCT isa (Two MinusW) (.seq (.block (minusHead amount)) minusLoop) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := MinusLoopRegs)
    (two_map (fun L => L) (fun _ _ h => h.1) (minusHead_ct amount hT)) ?_)
    (two_taint [.x14, .x16, .x17] pins_minusLoopRegs (by taint_decide))
  intro L s ⟨⟨minv, hg, hz⟩, hw⟩
  exact WP.mono (minusHead_ok hg hz hw ha) fun _ h => ⟨h.2.2.2.1, h.2.1, h.2.2.1⟩

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
    (hT : (taint.check (Taint.ofRegs [.x12, .x16, .x17]) (.block
      [movi .x7 0, movi .x4 amount, ld .x3 .x16, .subs .x .x3 .x3 .x4, st .x3 .x17, next .x16, next .x17,
        .subImm .x .x14 .x12 1]) hc).isSome = true) :
    RelCT isa (Two (@MinusPre amount))
      (.seq (.seq (.block (minusHead amount)) minusLoop) (seqs Core.finish)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun p s => FinishPre p.toBPub s)
    (two_map (fun p : MinusPublic amount => p.x.ws)
      (fun p _ h => ⟨⟨_, h.1.good, Nat.le_refl _⟩, Nat.le_trans (by decide) p.lower⟩) (minusCore_ct amount ha hT)) ?_)
    (two_map MinusPublic.toBPub (fun _ _ h => h) finish_ct)
  intro p s ⟨hc, hm, hf⟩
  exact WP.mono (minus_ok hc hm p.lower p.upper ha p.enough)
    fun t ⟨hct, _, _, hft, hkt⟩ => hf.work hc hct hft hkt

end VG.Proof.Dsa.AArch64
