module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Top2
import VerifiedGarbage.Proof.Framework.Omega
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A candidate on ARMv7: the entry (`entry_ok`, `in_c`)

The entry moves `out` to frame word 12; then the body starts (`In`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.RsaKeyGen (ite_t ite_f)

section
variable {s t : State}

theorem CIn.argSub (h : CIn s) {i : Nat} (hi : i < 7) : Region.Sub ⟨stackArgAddr s i, 4⟩ (cA s) := by
  have := h.spHi
  have e : stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (4 * i) := by
    simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]; exact addr_add (by omega)
  rw [e]; exact Offset.sub_base _ (by omega)

/-- The body's start, after the push and the entry. -/
theorem in_c (h : CIn s) (sp : t.sp = (mkP s).sp) (rd : t.rd = s.rd) (wr : t.wr = xRegs s)
    (mem : t.mem = (pcPushed s).mem.writeW (off (State.addr (mkP s).sp) 48) (s.gpr .r0)) : In (mkP s) t := by
  have spLo := h.spLo; have spHi := h.spHi
  have spN : (mkP s).sp.toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' (by omega)
  have hk := h.valid
  simp only [Spec.RsaKeyGen.primeLenValid] at hk
  have rdm : ∀ r ∈ [cE s, cP s, cR s, cA s], r ∈ t.rd ++ t.wr := fun r hr =>
    List.mem_append_left _ (by rw [rd, h.rd]; exact hr)
  have fr := h.tFrame mem
  have fwArg : ∀ i < 7, fw t.mem (mkP s) (56 + 4 * i) = stackArg s i := fun i hi => by
    simp only [fw]
    rw [h.argAddr hi]
    refine fr.readW (r := ⟨stackArgAddr s i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact h.FA.symm.sub_left (h.argSub hi)
  have w48 : Frame [⟨off (State.addr (mkP s).sp) 48, 4⟩] (pcPushed s).mem t.mem := by
    rw [mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fwSaved : ∀ p ∈ [(Reg.r1, 4), (Reg.r2, 8), (Reg.r3, 12)], fw t.mem (mkP s) p.2 = s.gpr p.1 := fun p hp => by
    have hs := pc_push_saved s (by omega) p (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp [pcAllSaved])
    rw [← hs]
    refine w48.readW (r := ⟨off (State.addr (mkP s).sp) p.2, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    have : p.2 + 4 ≤ 48 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> decide
    exact Offset.disjoint _ (.inl this) (by omega) (by decide)
  have bE := h.bytesT mem (R := cE s) h.Fe (by have := h.fe; show (stackArg s 0).toNat ≤ _; omega)
  have bP := h.bytesT mem (R := cP s) h.Fp (by have := h.fp; show (stackArg s 2).toNat ≤ _; omega)
  have bR := h.bytesT mem (R := cR s) h.Fr (by have := h.fr; show (stackArg s 4).toNat ≤ _; omega)
  have a0 := h.argAddr (i := 0) (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at a0
  refine ⟨sp, by omega, by omega, wr, ⟨cE s, rdm _ (by simp), Region.contains_self _ _⟩,
    ⟨cP s, rdm _ (by simp), Region.contains_self _ _⟩, ⟨cR s, rdm _ (by simp), Region.contains_self _ _⟩,
    ⟨cA s, rdm _ (by simp), by rw [a0]; exact Region.contains_self _ _⟩, hk.1, hk.2.1, hk.2.2, h.el1, h.el2, h.plv,
    h.scr, h.fo, h.fu, h.fe, h.fp, h.fr, BitVec.isLt _, h.fS,
    h.oS.symm, h.uS.symm, h.eS.symm, h.pS.symm, h.rS.symm, h.disjF h.FS.symm h.SA, h.FS.symm.sub_right h.rcSub,
    h.oU, h.oE, h.oP, h.oR, h.disjF h.Fo.symm h.oA, h.Fo.symm.sub_right h.rcSub,
    h.uE, h.uP, h.uR, h.disjF h.Fu.symm h.uA, h.Fu.symm.sub_right h.rcSub,
    h.Fe.symm.sub_right h.frSub, h.Fe.symm.sub_right h.rcSub, h.Fp.symm.sub_right h.frSub,
    h.Fp.symm.sub_right h.rcSub, h.Fr.symm.sub_right h.frSub, h.Fr.symm.sub_right h.rcSub,
    ?_, ?_, fwSaved (.r2, 8) (by simp), fwSaved (.r3, 12) (by simp), ?_, fwArg 1 (by decide), ?_,
    fwArg 3 (by decide), ?_, fwArg 5 (by decide), ?_, bE, fun hL => ?_⟩
  · show t.mem.readW (off (State.addr (mkP s).sp) 48) 32 = s.gpr .r0
    rw [mem]; exact Mem.readW_writeW_self32 _ _ _
  · rw [show fw t.mem (mkP s) foL = s.gpr .r1 from fwSaved (.r1, 4) (by simp)]; simp [mkP]
  · show fw _ _ (56 + 4 * 0) = _; rw [fwArg 0 (by decide)]; simp [mkP]
  · show fw _ _ (56 + 4 * 2) = _; rw [fwArg 2 (by decide)]; simp [mkP]
  · show fw _ _ (56 + 4 * 4) = _; rw [fwArg 4 (by decide)]; simp [mkP]
  · show fw _ _ (56 + 4 * 6) = _; rw [fwArg 6 (by decide)]; simp [mkP]
  · show VG.Proof.RsaKeyGen.schedOf (s.gpr .r1).toNat (Spec.Rsa.os2ip (mkP s).eB)
      (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt t.mem (cP s).base (cP s).len))
      (Spec.Rsa.bytesAt t.mem (cR s).base (cR s).len) = (mkP s).sch
    rw [bP, bR]
    exact (ite_t hL _ _).symm

/-- The entry: `out` to frame word 12, and the body's start. -/
theorem entry_ok (h : CIn s) :
    WP isa (.block entry) (sx s) fun t => In (mkP s) t ∧ t.sp = (mkP s).sp ∧ t.rd = s.rd ∧ t.wr = xRegs s ∧
      t.mem = (pcPushed s).mem.writeW (off (State.addr (mkP s).sp) 48) (s.gpr .r0) := by
  have spLo := h.spLo; have spHi := h.spHi
  have spN : (mkP s).sp.toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' (by omega)
  unfold entry
  refine wp_stackAddr (r := .r12) (d := 0) (by decide) fun u1 h1 => ?_
  refine wp_str (a := off (State.addr (mkP s).sp) 48) (by decide) ?_ ⟨(mkP s).rFr, by rw [h1.wr]; simp [xRegs],
    Offset.contains_base _ (by decide) (by decide)⟩ fun t m => WP.block_nil ?_
  · rw [h1.gpr, BitVec.add_zero]
    exact addr_add (by show (mkP s).sp.toNat + 48 < 2 ^ 32; omega)
  · have e0 : u1.gpr .r0 = s.gpr .r0 := by rw [h1.other _ (by decide)]; rfl
    have mt : t.mem = (pcPushed s).mem.writeW (off (State.addr (mkP s).sp) 48) (s.gpr .r0) := by
      rw [m.mem, h1.mem, e0]; rfl
    have st : t.sp = (mkP s).sp := by rw [m.sp, h1.sp]; rfl
    have rt : t.rd = s.rd := by rw [m.rd, h1.rd]; rfl
    have wt : t.wr = xRegs s := by rw [m.wr, h1.wr]; rfl
    exact ⟨in_c h st rt wt mt, st, rt, wt, mt⟩

end

end VG.Proof.RsaKeyGen.Arm.Cand
