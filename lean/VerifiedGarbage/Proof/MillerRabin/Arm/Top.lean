module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Contract
public import VerifiedGarbage.Proof.Bignum.Arm.PcPush
public import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rsa.Arm.RvVP
import VerifiedGarbage.Proof.MillerRabin.Arm.Words
import VerifiedGarbage.Proof.Rsa.Arm.RvKS

/-! # The Miller–Rabin round on ARMv7: a call's result and constant time

`mkP s`: the public parameters of a call from `s`. The body runs from the
state after the push with the regions narrowed to the frame, the working
space and its key view (`xRegs`), and is widened back; the frame then
restores the callee-saved registers (`round_ok`). Two calls with the same
public parameters leak the same (`round_ct`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- The public parameters of a call. -/
def mkP (s : State) : MP where
  ws := s.gpr .r0
  len := (s.gpr .r1).toNat
  w := wOf s.mem (State.addr (s.gpr .r0))
  sp := s.sp - BitVec.ofNat 32 56

/-- The body's regions. -/
def xRegs (s : State) : List Region := [(mkP s).rF, (mkP s).rS, (mkP s).rK]

/-- The state the body starts from. -/
abbrev bodyIn (s : State) : State := (pcPushed s).withRegions (pcPushed s).rd (xRegs s)

section
variable {s : State}

theorem roundPre.spAddr (h : roundPre s) : State.addr (s.sp - BitVec.ofNat 32 56) = State.addr s.sp - 56#64 :=
  FrameStack.addr_sub' h.2.2.2.1

/-- The push writes only the frame, apart from the working space. -/
theorem roundPre.pushedWs (h : roundPre s) :
    ∀ i < 8 * (s.gpr .r1).toNat, (pcPushed s).mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 i) =
      s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 i) := by
  obtain ⟨_, _, fit, spLo, disj, _⟩ := h
  have f := FrameStack.pushed_frameA (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (s := s) spLo
  intro i hi
  refine f _ fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  refine disj _ hc ?_
  simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  omega_arith

theorem in_x (h : roundPre s) : In (mkP s) (bodyIn s) := by
  have h0 := h
  obtain ⟨rd, wr, fit, spLo, disj, lay, prep⟩ := h0
  have ew := h.pushedWs
  obtain ⟨lay', hw⟩ := layout_congr ew lay
  have prep' := prepared_congr ew lay prep
  have spN : (s.sp - BitVec.ofNat 32 56).toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' spLo
  obtain ⟨lM, w4, w128, fits⟩ := lay'
  rw [hw] at w4 w128 fits
  obtain ⟨c3, codd, inv, x5, one, m1, ex, lo⟩ := prep'
  simp only [hw] at c3 codd inv x5 one m1 ex lo
  refine ⟨rfl, rfl, by simp only [mkP]; omega_arith, by simp only [mkP]; rw [spN]; have := s.sp.isLt; omega_arith, ?_,
    w4, w128, fits, ?_, hw, inv, c3, codd, x5, one, m1, ex, lo, ?_⟩
  · show (⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ : Region).Disjoint _
    exact disj
  · simpa [mkP] using lM
  · show (pcPushed s).mem.readW (State.addr (s.sp - BitVec.ofNat 32 56)) 32 = s.gpr .r0
    have := pc_push_saved s spLo (.r0, 0) (by simp [pcAllSaved])
    simpa using this

end

/-- What a stage keeps of `σ`, as the contract states it. -/
theorem KS.keepsLite {P : MP} {σ s : State} {A : Nat → Nat} {L : List Nat} {V : Nat → Nat} {LS : List Nat}
    (h : KS P σ A L V LS s) : KeepsLite (State.addr P.ws) P.len P.w σ.mem s.mem := by
  have pre := h.pre
  have fit := pre.fit
  have len := pre.len
  have hS := pre.S_eq
  intro i hi hk hj
  by_cases hlo : i < kOff
  · exact h.mem_out (pre.ofsB_lo hlo)
  · have hof : ofs (State.addr P.ws) (State.addr P.ws + BitVec.ofNat 64 i) = i := ofs_off0 _ (by omega_arith)
    have hB := pre.ofsB (x := State.addr P.ws + BitVec.ofNat 64 i) (by rw [hof]; omega_arith)
    rw [hof] at hB
    refine h.keep _ fun r hr => ?_
    rw [hB]
    simp only [ranges, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨j, hjm, rfl⟩ | ⟨d, hd, rfl⟩
    · have := hj j hjm
      have := pre.arr_eq j
      dsimp only; rw [hS]; omega_arith
    · have := wDs_ok d hd
      have h23 := hk 23 (by simp)
      have h26 := hk 26 (by simp)
      have h29 := hk 29 (by simp)
      have h30 := hk 30 (by simp)
      dsimp only
      simp only [wDs, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [sE1, sE2, sT, sV, sF, sK, sQ, sR, kOff] at * <;> omega_arith

end VG.Proof.MillerRabin.Arm
