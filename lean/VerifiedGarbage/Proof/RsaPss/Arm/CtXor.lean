module

import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.RsaPss.Arm.Base
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.RsaPss.Arm.Base
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# RSASSA-PSS on ARMv7: XOR of bytes, and arithmetic of the masks

`xor_vp`: the loop `xorBody` XORs the `n` bytes at one offset of our part
of `scratch` into those at another. With the facts about the top bit of a
difference that the code's comparisons use (`ltBit`), and the bytes of a
counter (`shrByte`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

/-- The top bit of a difference of numbers below `2^31`: whether the first
is less. -/
theorem ltBit {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b) >>> 31 = if a < b then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (a := b) (by omega)]
  split
  · show _ = 1; omega
  · show _ = 0; omega

/-- A byte of a word shifted right. -/
theorem shrByte {c : Nat} (hc : c < 2 ^ 32) (k : Nat) :
    (BitVec.ofNat 32 c >>> (8 * k)).setWidth 8 = BitVec.ofNat 8 (c / 256 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
    Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- The XOR of two bytes, as `eor` of their zero extensions. -/
theorem xorByte (a b : Byte) : (a.setWidth 32 ^^^ b.setWidth 32).setWidth 8 = a ^^^ b := by
  have e1 : ∀ x : BitVec 8, (x.setWidth 32).setWidth 8 = x := fun x => by simp
  rw [BitVec.setWidth_xor, e1, e1]

variable {L : Lay} {scr : BitVec 32}

/-- After `j` bytes of the XOR, from memory `m₀`. -/
structure XI (scr : BitVec 32) (od os n : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = scr + BitVec.ofNat 32 (od + j)
  r1 : s.gpr .r1 = scr + BitVec.ofNat 32 (os + j)
  lr : s.gpr .lr = BitVec.ofNat 32 (n - j)
  fr : Frame [sR scr od n] m₀ s.mem
  x : ∀ i < n, s.mem (sa scr (od + i)) =
    if i < j then m₀ (sa scr (od + i)) ^^^ m₀ (sa scr (os + i)) else m₀ (sa scr (od + i))

theorem xorBody_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .lr])
    (.block xorBody) hc).isSome = true := ⟨_, by taint_decide⟩

/-- The `n` bytes at `os` XORed into those at `od`. -/
theorem xor_vp (hg : Geo L scr) {od os n : Nat} (hn : 0 < n) (hd : od + n ≤ oRsa) (hs : os + n ≤ oRsa)
    (hsep : od + n ≤ os ∨ os + n ≤ od) {X : State → Mem → Prop} :
    VP (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .r0 = scr + BitVec.ofNat 32 od ∧
        s.gpr .r1 = scr + BitVec.ofNat 32 os ∧ s.gpr .lr = BitVec.ofNat 32 n)
      (countLoop xorBody)
      (fun σ s => Ctx L scr σ s ∧ ∃ m₀, X σ m₀ ∧ Frame [sR scr od n] m₀ s.mem ∧
        ∀ i < n, s.mem (sa scr (od + i)) = m₀ (sa scr (od + i)) ^^^ m₀ (sa scr (os + i))) := by
  have fit := hg.fit
  obtain ⟨σ', ok⟩ := hg.ok
  let I : Nat → State → State → Prop := fun k σ s => k ≤ n ∧ Ctx L scr σ s ∧
    ∃ m₀, X σ m₀ ∧ XI scr od os n m₀ (n - k) s
  refine (VP.loop (I := I) (fun k => ?_) (n - 1)).mono (fun σ s ⟨hc, hx, r0, r1, lr⟩ => ⟨by omega, hc,
    s.mem, hx, ⟨by rw [r0, show n - (n - 1 + 1) = 0 by omega]; rfl, by rw [r1, show n - (n - 1 + 1) = 0 by omega]; rfl,
      by rw [lr, show n - (n - (n - 1 + 1)) = n by omega], Frame.refl _ _, fun i _ => by
        rw [ite_eq_right (by omega)]⟩⟩) fun _ _ h => h
  refine VP.taint _ xorBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hk, hc, m₀, hx, hp⟩ => ?_
  · obtain ⟨-, -, _, -, p₁⟩ := h₁
    obtain ⟨-, -, _, -, p₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [p₁.r0, p₂.r0]
    · rw [p₁.r1, p₂.r1]
    · rw [p₁.lr, p₂.lr]
  generalize hj : n - (k + 1) = j at hp
  have hjn : j < n := by omega
  have aD : State.addr (scr + BitVec.ofNat 32 (od + j)) = sa scr (od + j) := hg.addr (by omega)
  have aS : State.addr (scr + BitVec.ofNat 32 (os + j)) = sa scr (os + j) := hg.addr (by omega)
  have rS : InRegions (s.rd ++ s.wr) (sa scr (os + j)) 1 := hg.rd hc.st (by omega)
  have rD : InRegions (s.rd ++ s.wr) (sa scr (od + j)) 1 := hg.rd hc.st (by omega)
  have wD : InRegions s.wr (sa scr (od + j)) 1 := hg.wr hc.st (by omega)
  have stj : s.mem (sa scr (os + j)) = m₀ (sa scr (os + j)) :=
    hp.fr _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Geo.sep (scr := scr) (o := os + j) (n := 1) (by omega) (by omega) (by omega) _ (Region.contains_self _ _)
  have dj : s.mem (sa scr (od + j)) = m₀ (sa scr (od + j)) := by
    rw [hp.x j hjn, ite_eq_right (Nat.lt_irrefl _)]
  have lr1 : BitVec.ofNat 32 (n - j) - 1 = BitVec.ofNat 32 (n - (j + 1)) := by
    rw [show n - j = (n - (j + 1)) + 1 by omega]; exact sub_one_ofNat (by unfold oRsa at hd; omega)
  have hw : WP isa (.block xorBody) s fun t => t.mem = s.mem.writeW (sa scr (od + j))
      (m₀ (sa scr (od + j)) ^^^ m₀ (sa scr (os + j))) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ t.gpr .r0 = scr + BitVec.ofNat 32 (od + (j + 1)) ∧
      t.gpr .r1 = scr + BitVec.ofNat 32 (os + (j + 1)) ∧ t.gpr .lr = BitVec.ofNat 32 (n - (j + 1)) ∧
      t.z = decide (n - (j + 1) = 0) := by
    prun [xorBody, hp.r0, hp.r1, hp.lr, aS, aD, rS, rD, wD, stj, dj, xorByte, lr1, dpVal]
    refine ⟨?_, ?_, ?_⟩
    · rw [BitVec.add_assoc, VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, Nat.add_assoc]
    · rw [BitVec.add_assoc, VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, Nat.add_assoc]
    · rw [VG.Proof.X25519.Arm.ofNat_beq_zero (by unfold oRsa at hd; omega)]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, z⟩ => ?_
  have fr1 : Frame [sR scr od n] s.mem t.mem := by
    rw [m]; exact frame_byte scr _ _ (by omega) (by omega) (by unfold oRsa at hd; omega)
  have hc' : Ctx L scr σ t := hc.write fr1 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.inW hd)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok hd (by rw [hg.F]; decide))
    rd wr sp
  have sk : XI scr od os n m₀ (j + 1) t := by
    refine ⟨r0, r1, lr, hp.fr.trans fr1, fun i hi => ?_⟩
    rw [m, sa_write scr _ _ (by unfold oRsa at hd; omega) (by unfold oRsa at hd; omega)]
    by_cases e : i = j
    · subst e
      rw [ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self _)]
    · rw [ite_eq_right (show ¬ (od + i = od + j) by omega), hp.x i hi]
      by_cases e' : i < j
      · rw [ite_eq_left e', ite_eq_left (by omega)]
      · rw [ite_eq_right e', ite_eq_right (by omega)]
  refine ⟨by rw [VG.Proof.X25519.Arm.eval_ne, z, show n - (j + 1) = k by omega]; cases k <;> simp,
    fun h0 => ⟨hc', m₀, hx, sk.fr, fun i hi => ?_⟩, fun hpos => ⟨by omega, hc', m₀, hx, ?_⟩⟩
  · rw [sk.x i hi, ite_eq_left (by omega)]
  · rw [show n - k = j + 1 by omega]; exact sk

end VG.Proof.RsaPss.Arm
