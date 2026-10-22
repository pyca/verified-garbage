module

public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Unmask
import VerifiedGarbage.Proof.RsaOaep.X86.Certs
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.VfTail
import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP decryption on x86: `EM`'s first byte and `lHash`

As on ARMv7 (`Proof/RsaOaep/Arm/DecAcc.lean`): `lHash'` compared with
`lHash` (`cmpLoop_vp`, of RSASSA-PSS), then the accumulator `acc` (in its
slot) zero exactly when `EM`'s first byte is zero and `lHash' = lHash`
(`acc_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes oRsa oEm arg ld st mi atS addi sAcc countLoop cmpBody)

variable (h g : OHash)

/-- What the checks keep: `X1` and `EM` unmasked. -/
abbrev Y (P : EP) (σ : State) (m : Mem) : Prop := X1 h P σ m ∧ EMv P m (V5 h g P σ)

/-- `EM`'s first byte is zero and `lHash' = lHash`. -/
abbrev hdOk (P : EP) (σ : State) : Prop :=
  V P σ 0 = 0 ∧ ∀ i < h.H.D, V5 h g P σ (1 + h.H.D + i) = (lhB h P σ).getD i 0

/-- After the checks of `EM`'s first byte and `lHash'`. -/
abbrev A1 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Y h g P σ s.mem ∧ ∃ a : BitVec 32, s.mem.readW (P.lay.fr sAcc) 32 = a ∧
    (a = 0 ↔ hdOk h g P σ)

theorem setWidth_byte_eq_zero (b : Byte) : b.setWidth 32 = 0 ↔ b = 0 := by
  constructor
  · intro e; have := congrArg (BitVec.setWidth 8) e; simpa using this
  · rintro rfl; rfl

theorem or_eq_zero32 (a b : BitVec 32) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := BitVec.or_eq_zero_iff

theorem acc_vp (P : EP) :
    VP (U5 h g P) (.seq (.block (cmpSet h.H)) (.seq (countLoop cmpBody) (.block accPut))) (A1 h g P) := by
  by_cases hP : ∃ σ, In P σ ∧ 2 * h.H.D + 2 ≤ P.K
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1.1.1, hs.2.1.1.2.1⟩
  obtain ⟨σ₀, hi₀, hfit⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi₀.k1024
  have hD := h.D_le
  have hD0 := h.D_pos
  -- The comparison's registers.
  refine VP.seq (G := fun σ s => Ctx P.lay P.scr σ s ∧ Y h g P σ s.mem ∧
      s.gpr .esi = P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D) ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 oLh ∧
      s.gpr .ecx = BitVec.ofNat 32 h.H.D ∧ s.gpr .edx = 0)
    (VP.taint [.esp, .ebp] h.certs.cmpSet (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hx, he⟩ => ?_) ?_
  · simp only [cmpSet, atS, addi, mi, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_mov fun t3 u3 => wp_addi fun t4 u4 =>
      wp_movi fun t5 u5 => wp_movi fun t6 u6 => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (((((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3 (by decide)
        (by decide)).upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)).upd u6 (by decide) (by decide)
    · rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]; exact ⟨hx, he⟩
    · simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
    · simp (disch := decide) only [u6.other, u5.other, u4.gpr, u3.gpr, u2.other, u1.other, hc.ebp]
    · rw [u6.gpr]
    · rw [u6.other _ (by decide), u5.gpr]; rfl
  refine VP.seq (Vf.cmpLoop_vp hg (oa := oEm + 1 + h.H.D) (ob := oLh) (n := h.H.D) hD0 (by oomega) (by oomega)
    (X := Y h g P) (f := fun σ i => V5 h g P σ (1 + h.H.D + i)) (g := fun σ i => (lhB h P σ).getD i 0)
    (fun σ m hy i hi => by
      rw [show oEm + 1 + h.H.D + i = oEm + (1 + h.H.D + i) by omega]; exact hy.2 _ (by omega))
    fun σ m hy i hi => hy.1.2.1 i hi) ?_
  -- `acc := EM[0] ∨ edx`, to its slot.
  refine VP.taint [.esp, .ebp] accPut_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hy, he⟩ => ?_
  have hi := hy.1.1.1
  simp only [accPut, atS, addi, st, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  have c2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
  have e2 : t2.gpr .esi = P.scr + BitVec.ofNat 32 oEm := by rw [u2.gpr, u1.gpr, hc.ebp]
  have m2 : t2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine wp_movzx8 (a := sa P.scr (oEm + 0)) (by show t2.ea ⟨.esi, 0⟩ = _; rw [ea_at, e2]; exact hg.addrD (by oomega))
    (hg.rd c2.st (by oomega)) fun t3 u3 => wp_or fun t4 u4 => ?_
  have c4 := (c2.upd u3 (by decide) (by decide)).upd u4 (by decide) (by decide)
  refine c4.wp_st hg (d := sAcc) (by decide) fun t5 c5 m5 => WP.block_nil ?_
  have fr : Frame [slotR P.lay sAcc] s.mem t5.mem := by
    rw [m5.mem, u4.mem, u3.mem, m2]; exact slot_frame _ _ _ _
  have dS : ∀ {o n : Nat}, o + n ≤ oRsa → ∀ r ∈ [slotR P.lay sAcc], (sR P.scr o n).Disjoint r :=
    fun hon r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  refine ⟨c5, ⟨⟨hy.1.1.keep h fr fun r hr => ?_, hy.1.2.1.keep h fr (dS (by oomega)), ?_⟩,
    hy.2.keep fr hK (dS (by oomega))⟩, t4.gpr .edx, by rw [m5.mem, Mem.readW_writeW_self32], ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact slotSep (by decide) (by decide) (by decide)
  · rw [← hy.1.2.2]
    exact sbytes_keep (o := oEm) (n := 1) fr (dS (by oomega)) (by oomega) (f := fun _ => s.mem (sa P.scr (oEm + 0)))
      (fun i hi => by rw [show i = 0 by omega]) 0 (by decide)
  · rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), u3.gpr, m2,
      or_eq_zero32, he, setWidth_byte_eq_zero, hy.1.2.2]
    exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩

end VG.Proof.RsaOaep.X86.Dec
