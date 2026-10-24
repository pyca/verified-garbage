module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Top2
public import VerifiedGarbage.Proof.Bignum.Arm.PcPush
public import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Top1

/-! # DSA's probable-prime test on ARMv7: the body's start (`in_c`)

After the allocation, `pre` (`PreOut`) and the push, with the regions
`xRegs` and the candidate readable, the body starts (`In`). The allocation,
the frame and the round's frame below it are the 144 bytes below the
caller's stack pointer (`cF`), at offsets of its base (`fB`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords layout)

/-- What `pre` leaves. -/
structure PreOut (bits : Nat) (s t : State) : Prop where
  rest : Rest [.r1, .r2, .r3, .r12] (allocated 32 s) t
  frame : Frame [⟨aA s, 32⟩] s.mem t.mem
  vals : ∀ p ∈ allocVals bits s, t.mem.readW (aA s + BitVec.ofNat 64 p.1) 32 = p.2
  r1 : t.gpr .r1 = BitVec.ofNat 32 (8 * Impl.Dsa.Arm.ProbablePrime.words bits)
  r2 : t.gpr .r2 = stackArg s 0

/-- The candidate's region. -/
abbrev cCd (bits : Nat) (s : State) : Region := ⟨State.addr (s.gpr .r0), Impl.Dsa.Arm.ProbablePrime.len bits⟩

/-- The regions the body runs with. -/
def xRegs (P : CP) : List Region := [P.rFr, P.rAl, P.rU, P.rS, P.rM]

/-- The state the body runs from. -/
abbrev sx (bits : Nat) (s t : State) : State := (pcPushed t).withRegions (cCd bits s :: s.rd) (xRegs (mkP bits s))

/-- `cF`'s base. -/
abbrev fB (s : State) : Addr := State.addr s.sp - 144#64

/-- The widths `In` needs. -/
abbrev Bits (bits : Nat) : Prop := bits = 160 ∨ bits = 256 ∨ bits = 1024 ∨ bits = 2048 ∨ bits = 3072

section
variable {bits : Nat} {s t : State}

theorem Bits.facts (hb : Bits bits) :
    32 ≤ 8 * Impl.Dsa.Arm.ProbablePrime.words bits ∧ 8 * Impl.Dsa.Arm.ProbablePrime.words bits ≤ 512 ∧
      Impl.Dsa.Arm.ProbablePrime.len bits ≤ 384 ∧
      keyWords bits = Spec.Rsa.scratchWords (8 * Impl.Dsa.Arm.ProbablePrime.words bits) ∧
      Impl.Dsa.Arm.ProbablePrime.checks bits = Spec.Dsa.primeChecks bits := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide

theorem below_eq (h : 144 ≤ s.sp.toNat) {a : Nat} (ha : a ≤ 144) :
    State.addr (s.sp - BitVec.ofNat 32 a) = fB s + BitVec.ofNat 64 (144 - a) := by
  rw [addr_sub' (by omega)]; exact Offset.sub_ofNat_eq _ ha

theorem spP (h : CIn bits s) : State.addr (mkP bits s).sp = fB s + BitVec.ofNat 64 56 :=
  below_eq h.spLo (a := 88) (by decide)

theorem aA_eq (h : CIn bits s) : aA s = fB s + BitVec.ofNat 64 112 := below_eq h.spLo (a := 32) (by decide)

theorem pushed_sp (o : PreOut bits s t) : (pcPushed t).sp = (mkP bits s).sp := by
  show t.sp - BitVec.ofNat 32 56 = s.sp - BitVec.ofNat 32 88
  rw [o.rest.sp]; show s.sp - BitVec.ofNat 32 32 - BitVec.ofNat 32 56 = _
  rw [BitVec.sub_sub, ← BitVec.ofNat_add]

theorem cF_sub {d n : Nat} (hd : d + n ≤ 144) :
    Region.Sub ⟨fB s + BitVec.ofNat 64 d, n⟩ (cF s) := Offset.sub_base _ hd

/-- Memory after `pre` and the push: changed only in `cF`. -/
theorem tFrame (h : CIn bits s) (o : PreOut bits s t) : Frame [cF s] s.mem (pcPushed t).mem := by
  have f := pushed_frameA (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (s := t) (by
      rw [o.rest.sp]; show 56 ≤ (s.sp - BitVec.ofNat 32 32).toNat
      rw [sub_toNat' (by have := h.spLo; omega)]; have := h.spLo; omega)
  have e : belowA t.sp (4 * 14) = ⟨fB s + BitVec.ofNat 64 56, 56⟩ := by
    show (⟨State.addr (t.sp - BitVec.ofNat 32 56), 56⟩ : Region) = _
    rw [show t.sp - BitVec.ofNat 32 56 = (mkP bits s).sp from pushed_sp o, spP h]
  rw [show [Reg.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr].length = 14 from rfl, e] at f
  have a := o.frame
  rw [aA_eq h] at a
  exact (a.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, cF_sub (by decide)⟩).trans
    (f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, cF_sub (by decide)⟩)

theorem bytesT (h : CIn bits s) (o : PreOut bits s t) {R : Region} (hR : (cF s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (pcPushed t).mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
  VG.Proof.Rsa.Arm.CrtValues.bytes_frame (tFrame h o) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hR.symm) hl

/-- The allocation's words after the push. -/
theorem allocW (h : CIn bits s) (o : PreOut bits s t) {k : Nat} {v : BitVec 32} (hk : (k, v) ∈ allocVals bits s) :
    fw (pcPushed t).mem (mkP bits s) (56 + k) = v := by
  have hk' : k + 4 ≤ 32 := by
    simp only [allocVals, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hk
    rcases hk with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have ea : off (State.addr (mkP bits s).sp) (56 + k) = aA s + BitVec.ofNat 64 k := by
    show State.addr (mkP bits s).sp + BitVec.ofNat 64 (56 + k) = _
    rw [spP h, aA_eq h, Offset.add_add, Offset.add_add, show 56 + (56 + k) = 112 + k by omega]
  have f := pushed_frameA (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (s := t) (by
      rw [o.rest.sp]; show 56 ≤ (s.sp - BitVec.ofNat 32 32).toNat
      rw [sub_toNat' (by have := h.spLo; omega)]; have := h.spLo; omega)
  have e : belowA t.sp (4 * [Reg.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr].length) =
      ⟨fB s + BitVec.ofNat 64 56, 56⟩ := by
    show (⟨State.addr (t.sp - BitVec.ofNat 32 56), 56⟩ : Region) = _
    rw [show t.sp - BitVec.ofNat 32 56 = (mkP bits s).sp from pushed_sp o, spP h]
  rw [e] at f
  show (pcPushed t).mem.readW (off (State.addr (mkP bits s).sp) (56 + k)) 32 = v
  have fr := f.readW (r := ⟨aA s + BitVec.ofNat 64 k, 4⟩) (a := aA s + BitVec.ofNat 64 k) (w := 32)
    (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [aA_eq h, Offset.add_add]
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by decide)) (by decide)
  rw [ea]
  exact fr.trans (o.vals (k, v) hk)


end

end VG.Proof.Dsa.Arm.Prime
