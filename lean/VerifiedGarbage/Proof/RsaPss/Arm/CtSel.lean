module

public import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.RsaPss.Arm.Step
meta import VerifiedGarbage.Proof.RsaPss.Arm.Step

/-!
# RSASSA-PSS on ARMv7: hashing, the selection of the hash value

`sel_vp`: the selection loop copies the hash value at `oSt` to `oSel` under
a mask (all ones or zero, as a condition `c` on the run decides), and leaves
`oSel` as it was otherwise.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

/-- The mask of a condition. -/
def maskOf (c : Prop) [Decidable c] : BitVec 32 := if c then BitVec.allOnes 32 else 0

/-- The byte the selection stores. -/
theorem selByte (a b : Byte) (c : Prop) [Decidable c] :
    (b.setWidth 32 ^^^ ((a.setWidth 32 ^^^ b.setWidth 32) &&& maskOf c)).setWidth 8 = if c then a else b := by
  have e1 : ∀ x : BitVec 8, (x.setWidth 32).setWidth 8 = x := fun x => by simp
  by_cases hc : c <;> simp only [maskOf, hc, ite_true, ite_false, BitVec.and_allOnes, BitVec.setWidth_xor, e1]
  · rw [← BitVec.xor_assoc, BitVec.xor_comm b, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · simp

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- After `j` bytes of the selection, from memory `m₀`. -/
structure SI (scr : BitVec 32) (c : Prop) [Decidable c] (m₀ : Mem) (j : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = scr + BitVec.ofNat 32 (oSt + j)
  r1 : s.gpr .r1 = scr + BitVec.ofNat 32 (oSel + j)
  lr : s.gpr .lr = BitVec.ofNat 32 (h.N - j)
  r2 : s.gpr .r2 = maskOf c
  fr : Frame [sR scr oSel h.N] m₀ s.mem
  sel : ∀ i < h.N, s.mem (sa scr (oSel + i)) = if i < j ∧ c then m₀ (sa scr (oSt + i)) else m₀ (sa scr (oSel + i))

theorem selBody_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .lr])
    (.block selBody) hc).isSome = true := ⟨_, by taint_decide⟩

/-- The selection: the hash value at `oSt` copied to `oSel` if `c`. -/
theorem sel_vp (hg : Geo L scr) {c : State → Prop} [∀ σ, Decidable (c σ)] {X : State → Mem → Prop} :
    VP (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .r0 = scr + BitVec.ofNat 32 oSt ∧
        s.gpr .r1 = scr + BitVec.ofNat 32 oSel ∧ s.gpr .lr = BitVec.ofNat 32 h.N ∧ s.gpr .r2 = maskOf (c σ))
      (countLoop selBody)
      (fun σ s => Ctx L scr σ s ∧ ∃ m₀, X σ m₀ ∧ Frame [sR scr oSel h.N] m₀ s.mem ∧
        ∀ i < h.N, s.mem (sa scr (oSel + i)) = if c σ then m₀ (sa scr (oSt + i)) else m₀ (sa scr (oSel + i))) := by
  have hN := h.N_le
  have hN0 : 0 < h.N := by have := h.D_pos; have := h.D_le; omega_arith
  have fit := hg.fit
  obtain ⟨σ', ok⟩ := hg.ok
  let I : Nat → State → State → Prop := fun n σ s => n ≤ h.N ∧ Ctx L scr σ s ∧
    ∃ m₀, X σ m₀ ∧ SI h scr (c σ) m₀ (h.N - n) s
  refine (VP.loop (I := I) (fun n => ?_) (h.N - 1)).mono (fun σ s ⟨hc, hx, r0, r1, lr, r2⟩ => ⟨by omega_arith, hc,
    s.mem, hx, ⟨by rw [r0, show h.N - (h.N - 1 + 1) = 0 by omega_arith]; rfl, by rw [r1, show h.N - (h.N - 1 + 1) = 0 by omega_arith]; rfl,
      by rw [lr, show h.N - (h.N - (h.N - 1 + 1)) = h.N by omega_arith], r2, Frame.refl _ _, fun i _ => by
        rw [ite_eq_right (by omega_arith)]⟩⟩) fun _ _ h => h
  refine VP.taint _ selBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hn, hc, m₀, hx, hp⟩ => ?_
  · obtain ⟨-, -, _, -, p₁⟩ := h₁
    obtain ⟨-, -, _, -, p₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [p₁.r0, p₂.r0]
    · rw [p₁.r1, p₂.r1]
    · rw [p₁.lr, p₂.lr]
  generalize hj : h.N - (n + 1) = j at hp
  have hjN : j < h.N := by omega_arith
  have aS : State.addr (scr + BitVec.ofNat 32 (oSt + j)) = sa scr (oSt + j) := hg.addr (by pomega)
  have aE : State.addr (scr + BitVec.ofNat 32 (oSel + j)) = sa scr (oSel + j) := hg.addr (by pomega)
  have rS : InRegions (s.rd ++ s.wr) (sa scr (oSt + j)) 1 := hg.rd hc.st (by pomega)
  have rE : InRegions (s.rd ++ s.wr) (sa scr (oSel + j)) 1 := hg.rd hc.st (by pomega)
  have wE : InRegions s.wr (sa scr (oSel + j)) 1 := hg.wr hc.st (by pomega)
  have stj : s.mem (sa scr (oSt + j)) = m₀ (sa scr (oSt + j)) :=
    hp.fr _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Geo.sep (scr := scr) (o := oSt + j) (n := 1) (by pomega) (by pomega) (by pomega) _ (Region.contains_self _ _)
  have lr1 : BitVec.ofNat 32 (h.N - j) - 1 = BitVec.ofNat 32 (h.N - (j + 1)) := by
    rw [show h.N - j = (h.N - (j + 1)) + 1 by omega_arith]; exact sub_one_ofNat (by omega_arith)
  have hw : WP isa (.block selBody) s fun t => t.mem = s.mem.writeW (sa scr (oSel + j))
      (if c σ then m₀ (sa scr (oSt + j)) else s.mem (sa scr (oSel + j))) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ t.gpr .r0 = scr + BitVec.ofNat 32 (oSt + (j + 1)) ∧
      t.gpr .r1 = scr + BitVec.ofNat 32 (oSel + (j + 1)) ∧ t.gpr .lr = BitVec.ofNat 32 (h.N - (j + 1)) ∧
      t.gpr .r2 = s.gpr .r2 ∧ t.z = decide (h.N - (j + 1) = 0) := by
    prun [selBody, hp.r0, hp.r1, hp.r2, hp.lr, aS, aE, rS, rE, wE, stj, selByte, lr1, dpVal]
    refine ⟨?_, ?_, ?_⟩
    · rw [BitVec.add_assoc, VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, Nat.add_assoc]
    · rw [BitVec.add_assoc, VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, Nat.add_assoc]
    · rw [VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_arith)]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, r2, z⟩ => ?_
  have fr1 : Frame [sR scr oSel h.N] s.mem t.mem := by
    rw [m]; exact frame_byte scr _ _ (by omega_arith) (by omega_arith) (by pomega)
  have hc' : Ctx L scr σ t := hc.write fr1 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by pomega))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by pomega) (by rw [hg.F]; decide))
    rd wr sp
  have sk : SI h scr (c σ) m₀ (j + 1) t := by
    refine ⟨r0, r1, lr, r2.trans hp.r2, hp.fr.trans fr1, fun i hi => ?_⟩
    rw [m, sa_write scr _ _ (by pomega) (by pomega)]
    by_cases e : i = j
    · subst e
      rw [ite_eq_left rfl, hp.sel i hi, ite_eq_right (show ¬ (i < i ∧ c σ) from fun h => absurd h.1 (Nat.lt_irrefl _))]
      by_cases hc' : c σ
      · rw [ite_eq_left hc', ite_eq_left ⟨Nat.lt_succ_self _, hc'⟩]
      · rw [ite_eq_right hc', ite_eq_right (fun h => hc' h.2)]
    · rw [ite_eq_right (show ¬ (oSel + i = oSel + j) by omega_arith), hp.sel i hi]
      by_cases e' : i < j
      · simp only [e', show i < j + 1 by omega_arith, true_and]
      · simp only [e', show ¬ i < j + 1 by omega_arith, false_and, ite_false]
  refine ⟨by rw [VG.Proof.X25519.Arm.eval_ne, z, show h.N - (j + 1) = n by omega_arith]; cases n <;> simp,
    fun h0 => ⟨hc', m₀, hx, sk.fr, fun i hi => ?_⟩, fun hpos => ⟨by omega_arith, hc', m₀, hx, ?_⟩⟩
  · rw [sk.sel i hi]
    by_cases hc'' : c σ
    · rw [ite_eq_left hc'', ite_eq_left ⟨by omega_arith, hc''⟩]
    · rw [ite_eq_right hc'', ite_eq_right (fun h => hc'' h.2)]
  · rw [show h.N - n = j + 1 by omega_arith]; exact sk

end VG.Proof.RsaPss.Arm
