module
public import VerifiedGarbage.Proof.RsaPss.Arm.CtSel

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
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtSel
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
# RSASSA-PSS verification with a precomputed public key on ARMv7: a pass of the shift

`pass_vp`: each of the `n` bytes at `o` replaced by the byte `d` after it if
`c`, under a mask, so that its addresses do not depend on `c`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable {L : Lay} {scr : BitVec 32}

/-- After `j` bytes of a pass, from memory `m₀`. -/
structure ShI (scr : BitVec 32) (c : Prop) [Decidable c] (o d n : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = scr + BitVec.ofNat 32 (o + j)
  r1 : s.gpr .r1 = scr + BitVec.ofNat 32 (o + d + j)
  lr : s.gpr .lr = BitVec.ofNat 32 (n - j)
  r2 : s.gpr .r2 = maskOf c
  fr : Frame [sR scr o n] m₀ s.mem
  sel : ∀ i < n, s.mem (sa scr (o + i)) = if i < j ∧ c then m₀ (sa scr (o + d + i)) else m₀ (sa scr (o + i))

theorem passBody_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .lr])
    (.block passBody) hc).isSome = true := ⟨_, by taint_decide⟩

/-- A pass: the `n` bytes at `o` replaced by the bytes `d` after them if `c`. -/
theorem pass_vp (hg : Geo L scr) {o d n : Nat} (hn : 0 < n) (hd : 0 < d) (ho : o + d + n ≤ oRsa)
    {c : State → Prop} [∀ σ, Decidable (c σ)] {X : State → Mem → Prop} :
    VP (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .r0 = scr + BitVec.ofNat 32 o ∧
        s.gpr .r1 = scr + BitVec.ofNat 32 (o + d) ∧ s.gpr .lr = BitVec.ofNat 32 n ∧ s.gpr .r2 = maskOf (c σ))
      (countLoop passBody)
      (fun σ s => Ctx L scr σ s ∧ ∃ m₀, X σ m₀ ∧ Frame [sR scr o n] m₀ s.mem ∧
        ∀ i < n, s.mem (sa scr (o + i)) = if c σ then m₀ (sa scr (o + d + i)) else m₀ (sa scr (o + i))) := by
  have fit := hg.fit
  have e2 : oRsa = 8192 := rfl
  obtain ⟨σ', ok⟩ := hg.ok
  let I : Nat → State → State → Prop := fun k σ s => k ≤ n ∧ Ctx L scr σ s ∧
    ∃ m₀, X σ m₀ ∧ ShI scr (c σ) o d n m₀ (n - k) s
  refine (VP.loop (I := I) (fun k => ?_) (n - 1)).mono (fun σ s ⟨hc, hx, r0, r1, lr, r2⟩ => ⟨by omega_arith, hc,
    s.mem, hx, ⟨by rw [r0, show n - (n - 1 + 1) = 0 by omega_arith]; rfl, by rw [r1, show n - (n - 1 + 1) = 0 by omega_arith]; rfl,
      by rw [lr, show n - (n - (n - 1 + 1)) = n by omega_arith], r2, Frame.refl _ _, fun i _ => by
        rw [ite_eq_right (by omega_arith)]⟩⟩) fun _ _ h => h
  refine VP.taint _ passBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hk, hc, m₀, hx, hp⟩ => ?_
  · obtain ⟨-, -, _, -, p₁⟩ := h₁
    obtain ⟨-, -, _, -, p₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [p₁.r0, p₂.r0]
    · rw [p₁.r1, p₂.r1]
    · rw [p₁.lr, p₂.lr]
  generalize hj : n - (k + 1) = j at hp
  have hjn : j < n := by omega_arith
  have aS : State.addr (scr + BitVec.ofNat 32 (o + d + j)) = sa scr (o + d + j) := hg.addr (by omega_arith)
  have aD : State.addr (scr + BitVec.ofNat 32 (o + j)) = sa scr (o + j) := hg.addr (by omega_arith)
  have rS : InRegions (s.rd ++ s.wr) (sa scr (o + d + j)) 1 := hg.rd hc.st (by omega_arith)
  have rD : InRegions (s.rd ++ s.wr) (sa scr (o + j)) 1 := hg.rd hc.st (by omega_arith)
  have wD : InRegions s.wr (sa scr (o + j)) 1 := hg.wr hc.st (by omega_arith)
  have stj : s.mem (sa scr (o + d + j)) = m₀ (sa scr (o + d + j)) := by
    by_cases e : d + j < n
    · rw [show o + d + j = o + (d + j) by omega, hp.sel _ e, ite_eq_right (fun h => by omega)]
    · exact hp.fr _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := scr) (o := o + d + j) (n := 1) (by omega_arith) (by omega_arith) (by omega_arith) _
          (Region.contains_self _ _)
  have dj : s.mem (sa scr (o + j)) = m₀ (sa scr (o + j)) := by
    rw [hp.sel j hjn, ite_eq_right (fun h => Nat.lt_irrefl _ h.1)]
  have lr1 : BitVec.ofNat 32 (n - j) - 1 = BitVec.ofNat 32 (n - (j + 1)) := by
    rw [show n - j = (n - (j + 1)) + 1 by omega_arith]; exact sub_one_ofNat (by omega_arith)
  have hw : WP isa (.block passBody) s fun t => t.mem = s.mem.writeW (sa scr (o + j))
      (if c σ then m₀ (sa scr (o + d + j)) else m₀ (sa scr (o + j))) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ t.gpr .r0 = scr + BitVec.ofNat 32 (o + (j + 1)) ∧
      t.gpr .r1 = scr + BitVec.ofNat 32 (o + d + (j + 1)) ∧ t.gpr .lr = BitVec.ofNat 32 (n - (j + 1)) ∧
      t.gpr .r2 = s.gpr .r2 ∧ t.z = decide (n - (j + 1) = 0) := by
    prun [passBody, hp.r0, hp.r1, hp.r2, hp.lr, aS, aD, rS, rD, wD, stj, dj, selByte, lr1, dpVal]
    refine ⟨?_, ?_, ?_⟩
    · rw [BitVec.add_assoc, VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, Nat.add_assoc]
    · rw [BitVec.add_assoc, VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, Nat.add_assoc]
    · rw [VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_arith)]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, r2, z⟩ => ?_
  have fr1 : Frame [sR scr o n] s.mem t.mem := by
    rw [m]; exact frame_byte scr _ _ (by omega_arith) (by omega_arith) (by omega_arith)
  have hc' : Ctx L scr σ t := hc.write fr1 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by omega_arith))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by omega_arith) (by rw [hg.F]; decide))
    rd wr sp
  have sk : ShI scr (c σ) o d n m₀ (j + 1) t := by
    refine ⟨r0, r1, lr, r2.trans hp.r2, hp.fr.trans fr1, fun i hi => ?_⟩
    rw [m, sa_write scr _ _ (by omega_arith) (by omega_arith)]
    by_cases e : i = j
    · subst e
      rw [ite_eq_left rfl]
      by_cases hc' : c σ
      · rw [ite_eq_left hc', ite_eq_left ⟨Nat.lt_succ_self _, hc'⟩]
      · rw [ite_eq_right hc', ite_eq_right (fun h => hc' h.2)]
    · rw [ite_eq_right (show ¬ (o + i = o + j) by omega_arith), hp.sel i hi]
      by_cases e' : i < j
      · simp only [e', show i < j + 1 by omega_arith, true_and]
      · simp only [e', show ¬ i < j + 1 by omega_arith, false_and, ite_false]
  refine ⟨by rw [VG.Proof.X25519.Arm.eval_ne, z, show n - (j + 1) = k by omega_arith]; cases k <;> simp,
    fun h0 => ⟨hc', m₀, hx, sk.fr, fun i hi => ?_⟩, fun hpos => ⟨by omega_arith, hc', m₀, hx, ?_⟩⟩
  · rw [sk.sel i hi]
    by_cases hc'' : c σ
    · rw [ite_eq_left hc'', ite_eq_left ⟨by omega_arith, hc''⟩]
    · rw [ite_eq_right hc'', ite_eq_right (fun h => hc'' h.2)]
  · rw [show n - k = j + 1 by omega_arith]; exact sk

end VG.Proof.RsaPss.Arm
