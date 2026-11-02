module

import VerifiedGarbage.Proof.Dsa.Arm.Prime.Top4
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Body
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Frame
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Fin
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Top3
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Top1

/-! # DSA's probable-prime test on ARMv7: a call's result (`prime_ok`)

The allocation, `pre`, the push, the body (run with the regions `xRegs` and
the candidate, and widened to the caller's), the restore, the pop and the
release.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords layout)

/-- The test's result, from the caller's memory. -/
def resC (bits : Nat) (s : State) : Option (Bool × Spec.RsaKeyGen.Rand) :=
  Spec.Dsa.probablePrime (Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (State.addr (s.gpr .r0)))
    (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)

/-- A call's result. -/
def CPost (bits : Nat) (s t : State) : Prop :=
  (t.gpr .r0).toNat = Proof.Dsa.ProbablePrime.status (resC bits s) ∧
    Proof.Dsa.ModPow.Keeps (State.addr (s.gpr .r0)) (s.gpr .r1).toNat [(keyOff, 8 * keyWords bits)] s.mem t.mem ∧
    ∀ b rest, resC bits s = some (b, rest) →
      Spec.Rsa.wordsAt t.mem (State.addr (stackArg s 0)) 1 = [BitVec.ofNat 64 ((s.gpr .r3).toNat - rest.length)]

section
variable {bits : Nat} {s t : State}

theorem res_c {σ : State} (pre : In (mkP bits s) σ) : res (mkP bits s) σ = resC bits s := by
  unfold res resC; rw [pre.cand, pre.rnd]; rfl

/-- The body's regions are among the caller's, the allocation's and the frame's. -/
theorem xCovers (h : CIn bits s) (o : PreOut bits s t) :
    Covers (xRegs (mkP bits s)) (pcPushed t).wr := by
  have spLo := h.spLo; have fw := h.fw; have size := h.size
  have kpos : 0 < keyWords bits := by simp [keyWords, Spec.Rsa.scratchWords]
  have wT : (pcPushed t).wr = (mkP bits s).rFr :: ⟨fB s + BitVec.ofNat 64 112, 32⟩ :: [cW s, cU s] := by
    show ⟨State.addr (t.sp - BitVec.ofNat 32 56), 56⟩ :: t.wr = _
    rw [show t.sp - BitVec.ofNat 32 56 = (mkP bits s).sp from pushed_sp o, o.rest.wr]
    show _ :: ⟨aA s, 32⟩ :: s.wr = _
    rw [aA_eq h, h.wr]
  have eAl : (mkP bits s).rAl = ⟨fB s + BitVec.ofNat 64 112, 32⟩ := by
    show (⟨State.addr ((mkP bits s).sp + BitVec.ofNat 32 56), 32⟩ : Region) = _
    rw [addr_add (by show (s.sp - BitVec.ofNat 32 88).toNat + 56 < _; rw [sub_toNat' (by omega)]; have := h.spHi; omega),
      spP h, Offset.add_add]
  have hkw : keyWords bits = 16 * (8 * Impl.Dsa.Arm.ProbablePrime.words bits) + 32 := rfl
  have hw : (mkP bits s).w = Impl.Dsa.Arm.ProbablePrime.words bits := by
    show 8 * Impl.Dsa.Arm.ProbablePrime.words bits / 8 = _; omega
  have hoM : (mkP bits s).oM = 8 * (21 * Impl.Dsa.Arm.ProbablePrime.words bits + 30) := by
    show 8 * (21 * (mkP bits s).w + 30) = _; rw [hw]
  have hlM : (mkP bits s).lenM = 8 * Impl.Dsa.Arm.ProbablePrime.words bits + 48 := by
    show 8 * (mkP bits s).w + 48 = _; rw [hw]
  have w4 : 4 ≤ Impl.Dsa.Arm.ProbablePrime.words bits := Nat.le_max_left _ _
  simp only [keyOff] at size ⊢
  rw [wT]
  refine Covers.of_forall fun r hr => ?_
  simp only [xRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self
  · exact Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [eAl]; exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · refine Covers.of_sub fun r hr => ⟨cW s, by simp, 384, ?_, ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; rw [rS_eq h]; rfl
    · simp only [List.mem_singleton] at hr; subst hr
      show 384 + keyWords bits * 8 ≤ (s.gpr .r1).toNat * 8; omega
  · refine Covers.of_sub fun r hr => ⟨cW s, by simp, 384 + (mkP bits s).oM, ?_, ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr
      show State.addr (s.gpr .r0 + BitVec.ofNat 32 keyOff + BitVec.ofNat 32 (mkP bits s).oM) = _
      rw [Offset.add_add, addr_add (by simp only [keyOff]; rw [hoM]; omega)]; rfl
    · simp only [List.mem_singleton] at hr; subst hr
      show 384 + (mkP bits s).oM + 8 * (mkP bits s).lenM ≤ (s.gpr .r1).toNat * 8
      rw [hoM, hlM]; omega

theorem rdT (o : PreOut bits s t) : (pcPushed t).rd = s.rd := o.rest.rd

/-- Every region the body may access, the caller's. -/
theorem allCovers (hb : Bits bits) (h : CIn bits s) (o : PreOut bits s t) :
    Covers ((sx bits s t).rd ++ (sx bits s t).wr) (s.rd ++ (pcPushed t).wr) := by
  have := h.size; have hl := hb.facts.2.2.1
  simp only [keyOff] at this
  refine Covers.cons ?_ (Covers.append (Covers.refl _) (xCovers h o))
  refine Covers.right (Covers.of_sub fun r hr => ⟨cW s, ?_, 0, ?_, ?_⟩)
  · show cW s ∈ (pcPushed t).wr
    rw [show (pcPushed t).wr = _ :: t.wr from rfl, o.rest.wr]
    show cW s ∈ _ :: ⟨aA s, 32⟩ :: s.wr
    rw [h.wr]; simp
  · simp only [List.mem_singleton] at hr; subst hr; exact (BitVec.add_zero _).symm
  · simp only [List.mem_singleton] at hr; subst hr
    show 0 + Impl.Dsa.Arm.ProbablePrime.len bits ≤ (s.gpr .r1).toNat * 8; omega

/-- The body's run, widened to the caller's regions. -/
theorem body_wide (v : RoundImpl) (hb : Bits bits) (h : CIn bits s) (o : PreOut bits s t) :
    ∃ tr w, Exec isa (Impl.Dsa.Arm.ProbablePrime.body v.name v.code) (sx bits s t) tr w ∧
      Exec isa (Impl.Dsa.Arm.ProbablePrime.body v.name v.code) (pcPushed t) tr
        (w.withRegions s.rd (pcPushed t).wr) ∧
      RF (mkP bits s) (In (mkP bits s)) (statD (mkP bits s)) (usedD (mkP bits s)) (sx bits s t) w := by
  have pre := in_c hb h o
  obtain ⟨tr, w, e, rf⟩ := (body_vp v (P := mkP bits s) (E := In (mkP bits s)) fun _ e => e).wp _ _
    ⟨pre, ⟨pre, rfl, rfl, rfl, Frame.refl _ _⟩⟩
  have run := Exec.widen (rd := s.rd) (wr := (pcPushed t).wr) e (allCovers hb h o) (xCovers h o)
  rw [State.withRegions_withRegions, ← rdT o, State.withRegions_self] at run
  exact ⟨tr, w, e, by rw [← rdT o]; exact run, rf⟩

theorem subC (h : CIn bits s) : Region.Sub (mkP bits s).rC (cF s) := by rw [rC_eq h]; exact cF_sub (by decide)

theorem subW0 (h : CIn bits s) : Region.Sub (mkP bits s).rW0 (cF s) := by
  show Region.Sub ⟨State.addr (mkP bits s).sp, 4⟩ _; rw [spP h]; exact cF_sub (by decide)

/-- The candidate's bytes are outside the key working space, the stack and `used`. -/
theorem keeps (h : CIn bits s) (o : PreOut bits s t) {w : State}
    (bk : Bk (mkP bits s) (sx bits s t) w) :
    Proof.Dsa.ModPow.Keeps (State.addr (s.gpr .r0)) (s.gpr .r1).toNat [(keyOff, 8 * keyWords bits)] s.mem w.mem := by
  have fw := h.fw
  intro i hi hr
  have hr' := hr _ List.mem_cons_self
  simp only at hr'
  have inW : (cW s).Contains (State.addr (s.gpr .r0) + BitVec.ofNat 64 i) 1 := by
    simpa using Offset.contains_base (State.addr (s.gpr .r0)) (d := i) (n := 1) (k := (s.gpr .r1).toNat * 8)
      (by omega) (by omega)
  have own : (⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 i, 1⟩ : Region).Contains
      (State.addr (s.gpr .r0) + BitVec.ofNat 64 i) 1 := Region.contains_self _ _
  have pre := bk.pre
  refine (bk.frame _ fun r hr hc => ?_).trans (tFrame h o _ fun r hr hc => ?_)
  · simp only [CP.chg, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [rS_eq h] at hc
      have := h.size; simp only [keyOff] at this hr' ⊢
      exact Offset.disjoint (State.addr (s.gpr .r0)) (d := i) (n := 1) (e := 384) (k := keyWords bits * 8)
        (by omega) (by omega) (by omega) _ own hc
    · exact h.wU _ inW hc
    · exact h.FW _ (subC h _ hc) inW
    · exact h.FW _ (subW0 h _ hc) inW
  · simp only [List.mem_singleton] at hr; subst hr; exact h.FW _ hc inW

end

end VG.Proof.Dsa.Arm.Prime
