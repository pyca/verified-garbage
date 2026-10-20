module

import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationFacts
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedSample
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGeneration

/-! Load canonical public scalar metadata from the caller's saved context. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedSample
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

def bits (p : Inputs) : Nat := Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom)
def shiftCount (n : Nat) : BitVec 32 := 7 - ((BitVec.ofNat 32 n - 1) &&& 7)

theorem head_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (environment : CachedGenerationContext p s) (h52 : 52 ∈ slots) :
    WP isa (.block VG.Impl.Ffdh.Arm.CachedSample.head) s fun t =>
      (t.gpr .r6 = BitVec.ofNat 32 ((bits p + 7) / 8) ∧
        t.gpr .r9 = shiftCount (bits p) ∧ t.gpr .r3 = 255 ∧ t.mem = s.mem) ∧
      Rest [.r3, .r6, .r9, .r10] s t := by
  have ctxFit := environment.fit
  have words : 3 ≤ p.cachedWords := by
    rw [environment.canonical.1, Spec.Ffdh.generationPrecomputedWords]
    omega
  have addr52 : State.addr (s.sp + BitVec.ofNat 32 52) = off (State.addr s.sp) 52 :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega)
  have addr8 : State.addr (p.cachedContext + BitVec.ofNat 32 8) = off (State.addr p.cachedContext) 8 :=
    VG.Arm.addr_add (by have := environment.fit; omega)
  have read0 : InRegions (s.rd ++ s.wr) (State.addr p.cachedContext) 4 := by
    simpa only [BitVec.add_zero] using CallLay.inRegions_sub (off := 0) environment.readable (by omega) (by omega)
  have read8 : InRegions (s.rd ++ s.wr) (off (State.addr p.cachedContext) 8) 4 :=
    CallLay.inRegions_sub environment.readable (by omega) (by omega)
  have n := environment.header32 0 (by decide)
  have width := environment.header32 1 (by decide)
  simp only [List.getD_cons_zero, BitVec.ofNat_eq_ofNat, Nat.mul_zero, BitVec.add_zero] at n
  change s.mem.readW (off (State.addr p.cachedContext) 8) 32 =
    BitVec.ofNat 32 ((bits p + 7) / 8) at width
  refine withRest [.r3, .r6, .r9, .r10] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.CachedSample.head : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.CachedSample.head
  ffrun [addr52, addr8, h.locals.read (d := 52) (by decide), h.saved 52 h52,
    Inputs.slotValue, BitVec.add_zero, read0, read8, n, width, bits, shiftCount]

end VG.Proof.Ffdh.Arm.CachedSample
