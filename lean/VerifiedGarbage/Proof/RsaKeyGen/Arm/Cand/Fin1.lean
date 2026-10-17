module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Mr11
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint8
public import VerifiedGarbage.Proof.Rsa.Arm.RvStore
public import VerifiedGarbage.Proof.Rsa.Arm.RvTaint5
public import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
public import VerifiedGarbage.Proof.Bignum.Arm.Store64
import VerifiedGarbage.Proof.Framework.Omega
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A candidate on ARMv7: the results (`finNone_vp`, `finUsed_vp`, `finPrime_vp`)

`RF P E st out used`: the status `st` returned, `out` written to `out`,
and `used` to `used`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)

/-- The end: the status `st`, `out` and `used`. -/
abbrev RF (P : CP) (E : State → Prop) (st : State → Nat) (out : State → List Byte) (used : State → Nat)
    (σ s : State) : Prop :=
  E σ ∧ Bk P σ s ∧ (s.gpr .r0).toNat = st σ ∧ Spec.Rsa.bytesAt s.mem (State.addr P.oP) P.L = out σ ∧
    Spec.Rsa.wordsAt s.mem (State.addr P.uP) 1 = [BitVec.ofNat 64 (used σ)]

theorem finish_eq (r : Nat) : finish r = [.ldrSp .r2 foUsed] ++ finTail r := rfl

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

theorem In.oW {σ : State} (pre : In P σ) : P.rO ∈ σ.wr := by rw [pre.wr]; simp
theorem In.uW {σ : State} (pre : In P σ) : P.rU ∈ σ.wr := by rw [pre.wr]; simp

/-- Zeros to `out`, keeping `Y`. -/
theorem zeroO_vp {Y : State → State → Prop}
    (hY : ∀ σ s t, Y σ s → Bk P σ s → Frame [P.rO] s.mem t.mem → Rest [.r0, .r1, .r2, .lr] s t → Y σ t) :
    VP (fun σ s => E σ ∧ Bk P σ s ∧ Y σ s) (VG.Impl.RsaKeyGen.Arm.Key.zeroOut foOut foL)
      (fun σ s => (E σ ∧ Bk P σ s ∧ Y σ s) ∧ Spec.Rsa.bytesAt s.mem (State.addr P.oP) P.L = List.replicate P.L 0) := by
  unfold VG.Impl.RsaKeyGen.Arm.Key.zeroOut
  refine VP.seq (G := fun σ s => (E σ ∧ Bk P σ s ∧ Y σ s) ∧ s.gpr .r0 = P.oP ∧
    s.gpr .lr = BitVec.ofNat 32 P.L ∧ s.gpr .r2 = 0) ?_ ?_
  · show VP _ (.block (([(Reg.r0, foOut), (Reg.lr, foL)].map fun p => Instr.ldrSp p.1 p.2) ++
      [.mov .r2 (.imm 0)])) _
    refine VP.block_append (G := fun σ s => (E σ ∧ Bk P σ s ∧ Y σ s) ∧ s.gpr .r0 = P.oP ∧
      s.gpr .lr = BitVec.ofNat 32 P.L) ?_ ?_
    · refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, y⟩ => ?_
      · rw [h₁.2.1.sp, h₁.2.1.pre.sp, h₂.2.1.sp, h₂.2.1.pre.sp]
      · show WP isa (.block [.ldrSp .r0 foOut, .ldrSp .lr foL]) s _
        refine h.ldrSp (o := foOut) (by decide) fun s1 u1 => ?_
        refine (h.of_upd u1).ldrSp (o := foL) (by decide) fun t u2 => WP.block_nil ?_
        have r : Rest [.r0, .r1, .r2, .lr] s t := (u1.rest (by simp)).trans (u2.rest (by simp))
        have f : Frame [P.rO] s.mem t.mem := by rw [u2.mem, u1.mem]; exact Frame.refl _ _
        exact ⟨⟨e, (h.of_upd u1).of_upd u2, hY σ s t y h f r⟩,
          by rw [u2.other _ (by decide), u1.gpr, h.pre.wO], by rw [u2.gpr, h.pre.wL]⟩
    · refine VP.taint [.r0, .lr] VG.Proof.Rsa.Arm.Recover.movR2_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
        fun σ s ⟨⟨e, h, y⟩, p0, plr⟩ => ?_
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]
      · refine wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ⟨⟨e, h.of_upd u,
          hY σ s t y h (by rw [u.mem]; exact Frame.refl _ _) (u.rest (by simp))⟩,
          by rw [u.other _ (by decide), p0], by rw [u.other _ (by decide), plr], by rw [u.gpr]⟩
  · refine VP.taint [.r0, .lr] VG.Proof.Rsa.Arm.Recover.mask_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
      fun σ s ⟨⟨e, h, y⟩, p0, plr, p2⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
    have pre := h.pre
    have hL := pre.k2
    have hwr : InRegions s.wr (State.addr P.oP) P.L :=
      ⟨_, by rw [h.wr]; exact pre.oW, Region.contains_self _ _⟩
    refine WP.mono (maskBuffer_ok s (by have := pre.k1; omega) (by omega) pre.fO hwr p0 plr)
      fun t ⟨b, f, r⟩ => ⟨⟨e, h.of_frame (f.mono fun r' hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp) r.sp r.rd r.wr, hY σ s t y h f (r.mono (by simp))⟩, ?_⟩
    rw [b, p2, VG.Proof.Rsa.Arm.CrtValues.zero_mask_bytes, VG.Proof.Rsa.Arm.CrtValues.bytesAt_length]

/-- `finish r`: `used := r3`, and `r` returned. -/
theorem finish_vp {r : Nat} {O : State → List Byte} {u : State → Nat}
    (cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r2]) (.block (finTail r)) hc).isSome = true)
    (henc : encodable (BitVec.ofNat 32 r) = true) (hr : r < 2 ^ 32) :
    VP (fun σ s => (E σ ∧ Bk P σ s ∧ Spec.Rsa.bytesAt s.mem (State.addr P.oP) P.L = O σ) ∧
        s.gpr .r3 = BitVec.ofNat 32 (u σ) ∧ u σ < 2 ^ 32)
      (.block (finish r)) (RF P E (fun _ => r) O u) := by
  rw [finish_eq]
  refine VP.block_append (G := fun σ s => ((E σ ∧ Bk P σ s ∧ Spec.Rsa.bytesAt s.mem (State.addr P.oP) P.L = O σ) ∧
    s.gpr .r3 = BitVec.ofNat 32 (u σ) ∧ u σ < 2 ^ 32) ∧ s.gpr .r2 = P.uP) ?_ ?_
  · show VP _ (.block ([(Reg.r2, foUsed)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h, o⟩, p3, hu⟩ => ?_
    · rw [h₁.1.2.1.sp, h₁.1.2.1.pre.sp, h₂.1.2.1.sp, h₂.1.2.1.pre.sp]
    refine h.ldrSp (o := foUsed) (by decide) fun t u1 => WP.block_nil ⟨⟨⟨e, h.of_upd u1, by rw [u1.mem]; exact o⟩,
      by rw [u1.other _ (by decide), p3], hu⟩, by rw [u1.gpr, h.pre.wU]⟩
  · refine VP.taint [.r2] cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨⟨e, h, o⟩, p3, hu⟩, p2⟩ => ?_
    · simp only [List.mem_singleton]; rintro r rfl; rw [h₁.2, h₂.2]
    have pre := h.pre
    have fU := pre.fU
    have wa : InRegions s.wr (State.addr P.uP) 4 :=
      ⟨_, by rw [h.wr]; exact pre.uW, by
        simpa using Offset.contains_base (State.addr P.uP) (d := 0) (n := 4) (k := 8) (by decide) (by decide)⟩
    have wb : InRegions s.wr (State.addr P.uP + BitVec.ofNat 64 4) 4 :=
      ⟨_, by rw [h.wr]; exact pre.uW, Offset.contains_base (State.addr P.uP) (d := 4) (n := 4) (k := 8) (by decide)
        (by decide)⟩
    refine wp_str (a := State.addr P.uP) (by decide) (by rw [p2, BitVec.add_zero]) wa fun s1 m1 => ?_
    refine wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
    refine wp_str (a := State.addr P.uP + BitVec.ofNat 64 4) (by decide)
      (by rw [u2.other _ (by decide), m1.gpr, p2]; exact addr_add (by omega)) (by rw [u2.wr, m1.wr]; exact wb)
      fun s3 m3 => ?_
    refine wp_mov (op2_imm henc) fun t u4 => WP.block_nil ?_
    have mt : t.mem = s.mem.writeW (State.addr P.uP) (0#32 ++ BitVec.ofNat 32 (u σ)) := by
      rw [u4.mem, m3.mem, u2.gpr, u2.mem, m1.mem, ← p3, VG.Proof.Rc2.Word32.write64_pair]
      rfl
    have fr : Frame [P.rU] s.mem t.mem := by
      rw [mt]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have rt : Rest [.r0, .r1] s t := (m1.rest _).trans ((u2.rest (by simp)).trans ((m3.rest _).trans (u4.rest (by simp))))
    refine ⟨e, h.of_frame (fr.mono fun r' hr => by simp only [List.mem_singleton] at hr; subst hr; simp)
      rt.sp rt.rd rt.wr, ?_, ?_, ?_⟩
    · rw [u4.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
    · rw [VG.Proof.Rsa.Arm.CrtValues.bytes_frame fr (fun r' hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact pre.oU) (by have := pre.fO; omega)]
      exact o
    · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
      rw [mt, Mem.readW_writeW_self64]
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu]
      simp
      omega

end

end VG.Proof.RsaKeyGen.Arm.Cand
