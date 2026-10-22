module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Bytes
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: q's top and low bits

The block after q's hash sets the top bit of its first byte and the low bit
of its last (`shapeQ_vp`): the bytes become `shapedOctets digest 7`, whose
value is `qCandidate` (`Proof.Dsa.Generation.qShape_memory`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_dp wp_ldrb wp_strb op2_imm dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- The bit operations of the block. -/
abbrev shapeOps (N : Nat) : List Instr :=
  [.ldrb .r1 .r0 0, .dp .orr .r1 .r1 (.imm 0x80), .strb .r1 .r0 0,
    .ldrb .r1 .r0 (N - 1), .dp .orr .r1 .r1 (.imm 1), .strb .r1 .r0 (N - 1)]

theorem orr_byte (b : Byte) (x : BitVec 32) :
    (b.setWidth 32 ||| x).setWidth 8 = b ||| x.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or]
  simp [hi, show i < 32 by omega]

section
variable {G : GP}

theorem shapeQ_vp {P Q : State → State → Prop} {c : State → Cfg} {L N : Nat} {bs : List Byte}
    (hF : ∀ σ s, P σ s → SS G σ (c σ) s) (hL : L = G.pLen) (hN : 2 ≤ N) (hN' : N ≤ 32)
    (hb : ∀ σ s, P σ s → Spec.Rsa.bytesAt s.mem (G.sa sQ) N = bs)
    (k : ∀ σ s t, P σ s → Rest [.r0, .r1, .r12] s t → Frame [G.rs sQ N] s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa sQ) N = VG.Proof.Ffdh.ParameterCandidate.shapedOctets bs 7 → Q σ t) :
    VP P (.block (scr L .r0 sQ ++ shapeOps N)) Q := by
  refine VP.taint [.r8] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8])
      (.block (scr 128 .r0 sQ ++ shapeOps 20)), rfl⟩ (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s hs => ?_
  · simp only [List.mem_singleton] at hr; subst hr; rw [(hF _ _ h₁).r8, (hF _ _ h₂).r8]
  have h := hF σ s hs
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have sk : 4096 ≤ sK G.pLen := by simp only [sK, sA]; omega
  have nq : sQ = 128 := rfl
  have kz0 : 0 < kz G.pLen := by simp only [kz]; omega
  subst hL
  refine scr_ok (d := .r0) h.r8 rfl h.lens (by omega) fun s₁ v₁ R₁ M₁ => ?_
  have aq := h.addr (o := sQ) (n := N) (by omega) (by omega)
  have w : ∀ j < N, InRegions s.wr (G.sa sQ + BitVec.ofNat 64 j) 1 := fun j hj =>
    Covers.one (gi.inScr (o := sQ) (n := N) (by omega)) _ _
      ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  have r_of : ∀ j < N, InRegions (s.rd ++ s.wr) (G.sa sQ + BitVec.ofNat 64 j) 1 := fun j hj =>
    let ⟨r, hr, hc⟩ := w j hj; ⟨r, List.mem_append_right _ hr, hc⟩
  have a0 : State.addr (s₁.gpr .r0 + BitVec.ofNat 32 0) = G.sa sQ := by rw [BitVec.add_zero, v₁, aq]
  have aN : State.addr (s₁.gpr .r0 + BitVec.ofNat 32 (N - 1)) = G.sa sQ + BitVec.ofNat 64 (N - 1) := by
    rw [v₁, BitVec.add_assoc, ← BitVec.ofNat_add, addr_add (by omega), Offset.add_add]
  simp only [shapeOps]
  refine wp_ldrb (by decide) a0 (by rw [R₁.rd, R₁.wr]; simpa using r_of 0 (by omega)) fun s₂ u₂ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_strb (a := G.sa sQ) (by decide) (by rw [u₃.other .r0 (by decide), u₂.other .r0 (by decide)]; exact a0)
    (by rw [u₃.wr, u₂.wr, R₁.wr]; simpa using w 0 (by omega)) fun s₄ u₄ => ?_
  have a4 : State.addr (s₄.gpr .r0 + BitVec.ofNat 32 (N - 1)) = G.sa sQ + BitVec.ofNat 64 (N - 1) := by
    rw [u₄.gpr, u₃.other .r0 (by decide), u₂.other .r0 (by decide)]; exact aN
  refine wp_ldrb (by omega) a4 (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, R₁.rd, R₁.wr]; exact r_of _ (by omega))
    fun s₅ u₅ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₆ u₆ => ?_
  refine wp_strb (a := G.sa sQ + BitVec.ofNat 64 (N - 1)) (by omega)
    (by rw [u₆.other .r0 (by decide), u₅.other .r0 (by decide)]; exact a4)
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, R₁.wr]; exact w _ (by omega)) fun t u₇ => WP.block_nil ?_
  have R : Rest [.r0, .r1, .r12] s t := ((R₁.mono (by simp)).trans ((u₂.rest (by simp)).trans (u₃.rest (by simp)))).trans
    ((u₄.rest _).trans ((u₅.rest (by simp)).trans ((u₆.rest (by simp)).trans (u₇.rest _))))
  have m₄ : s₄.mem = s.mem.writeW (G.sa sQ) (s.mem (G.sa sQ) ||| 128#8) := by
    rw [u₄.mem, u₃.mem, u₂.mem, M₁, u₃.gpr, dpVal, u₂.gpr, M₁, orr_byte]; rfl
  have b₄ : s₄.mem (G.sa sQ + BitVec.ofNat 64 (N - 1)) = s.mem (G.sa sQ + BitVec.ofNat 64 (N - 1)) := by
    rw [m₄, VG.WriteBytes.writeW8_apply, ite_eq_right (by
      have := Offset.add_ofNat_ne (G.sa sQ) (a := N - 1) (b := 0) (by omega) (by omega) (by omega)
      simpa using this)]
  have mt : t.mem = (s.mem.writeW (G.sa sQ) (s.mem (G.sa sQ) ||| 128#8)).writeW
      (G.sa sQ + BitVec.ofNat 64 (N - 1)) (s.mem (G.sa sQ + BitVec.ofNat 64 (N - 1)) ||| 1#8) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₆.gpr, dpVal, u₅.gpr, b₄, orr_byte, ← m₄]; rfl
  have hb' := hb σ s hs
  have bl : bs.length = N := by rw [← hb', bytesAt_length']
  refine k σ s t hs R ?_ ?_
  · rw [mt]
    have c0 : (G.rs sQ N).Contains (G.sa sQ) (8 / 8) := by
      show (_ - _ : Addr).toNat + 1 ≤ N
      rw [BitVec.sub_self, BitVec.toNat_zero]; omega
    exact ((Frame.refl [G.rs sQ N] s.mem).writeW List.mem_cons_self (w := 8) _ c0).writeW List.mem_cons_self
      (w := 8) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [mt, ← bl]
    refine VG.Proof.Dsa.Generation.qShape_memory (by omega) (by omega) fun i hi => ?_
    rw [← hb']
    simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, bl ▸ hi]

end

end VG.Proof.Dsa.Arm.Gen
