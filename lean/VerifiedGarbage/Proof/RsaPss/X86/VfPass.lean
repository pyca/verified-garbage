module

public import VerifiedGarbage.Proof.RsaPss.X86.CtSel
import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.RsaPss.X86.CtXor
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS verification with a precomputed public key on x86: a pass of the shift

As on ARMv7 (`Proof/RsaPss/Arm/VfPass.lean`): `pass_vp`: each of the `n`
bytes at `o` replaced by the byte `d` after it if `c`, under a mask, so that
its addresses do not depend on `c`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

variable {L : Lay} {scr : BitVec 32}

/-- After `j` bytes of a pass, from memory `m₀`. -/
structure ShI (scr : BitVec 32) (c : Prop) [Decidable c] (o d n : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop where
  esi : s.gpr .esi = scr + BitVec.ofNat 32 (o + j)
  edi : s.gpr .edi = scr + BitVec.ofNat 32 (o + d + j)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (n - j)
  edx : s.gpr .edx = maskOf c
  fr : Frame [sR scr o n] m₀ s.mem
  sel : ∀ i < n, s.mem (sa scr (o + i)) = if i < j ∧ c then m₀ (sa scr (o + d + i)) else m₀ (sa scr (o + i))

/-- A pass: the `n` bytes at `o` replaced by the bytes `d` after them if `c`. -/
theorem pass_vp (hg : Geo L scr) {o d n : Nat} (hn : 0 < n) (hd : 0 < d) (ho : o + d + n ≤ oRsa)
    {c : State → Prop} [∀ σ, Decidable (c σ)] {X : State → Mem → Prop} :
    VP (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .esi = scr + BitVec.ofNat 32 o ∧
        s.gpr .edi = scr + BitVec.ofNat 32 (o + d) ∧ s.gpr .ecx = BitVec.ofNat 32 n ∧ s.gpr .edx = maskOf (c σ))
      (countLoop passBody)
      (fun σ s => Ctx L scr σ s ∧ ∃ m₀, X σ m₀ ∧ Frame [sR scr o n] m₀ s.mem ∧
        ∀ i < n, s.mem (sa scr (o + i)) = if c σ then m₀ (sa scr (o + d + i)) else m₀ (sa scr (o + i))) := by
  have fit := hg.fit
  have e2 : oRsa = 8192 := rfl
  obtain ⟨σ', ok⟩ := hg.ok
  let I : Nat → State → State → Prop := fun k σ s => k ≤ n ∧ Ctx L scr σ s ∧
    ∃ m₀, X σ m₀ ∧ ShI scr (c σ) o d n m₀ (n - k) s
  refine (VP.loop (I := I) (fun k => ?_) (n - 1)).mono (fun σ s ⟨hc, hx, si, di, cx, dx⟩ => ⟨by omega, hc,
    s.mem, hx, ⟨by rw [si, show n - (n - 1 + 1) = 0 by omega]; rfl, by rw [di, show n - (n - 1 + 1) = 0 by omega]; rfl,
      by rw [cx, show n - (n - (n - 1 + 1)) = n by omega], dx, Frame.refl _ _, fun i _ => by
        rw [ite_eq_right (by omega)]⟩⟩) fun _ _ h => h
  refine VP.taint _ passBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hk, hc, m₀, hx, hp⟩ => ?_
  · obtain ⟨-, -, _, -, p₁⟩ := h₁
    obtain ⟨-, -, _, -, p₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [p₁.esi, p₂.esi]
    · rw [p₁.edi, p₂.edi]
    · rw [p₁.ecx, p₂.ecx]
  generalize hj : n - (k + 1) = j at hp
  have hjn : j < n := by omega
  have aS : VG.X86.addr (scr + BitVec.ofNat 32 (o + d + j)) 0 = sa scr (o + d + j) := by
    rw [hg.addrD (by omega), Nat.add_zero]
  have aD : VG.X86.addr (scr + BitVec.ofNat 32 (o + j)) 0 = sa scr (o + j) := by
    rw [hg.addrD (by omega), Nat.add_zero]
  have rS : InRegions (s.rd ++ s.wr) (sa scr (o + d + j)) 1 := hg.rd hc.st (by omega)
  have rD : InRegions (s.rd ++ s.wr) (sa scr (o + j)) 1 := hg.rd hc.st (by omega)
  have wD : InRegions s.wr (sa scr (o + j)) 1 := hg.wr hc.st (by omega)
  have stj : s.mem (sa scr (o + d + j)) = m₀ (sa scr (o + d + j)) := by
    by_cases e : d + j < n
    · rw [show o + d + j = o + (d + j) by omega, hp.sel _ e, ite_eq_right (fun h => by omega)]
    · exact hp.fr _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := scr) (o := o + d + j) (n := 1) (by omega) (by omega) (by omega) _
          (Region.contains_self _ _)
  have dj : s.mem (sa scr (o + j)) = m₀ (sa scr (o + j)) := by
    rw [hp.sel j hjn, ite_eq_right (fun h => Nat.lt_irrefl _ h.1)]
  simp only [passBody, addi, Impl.RsaPkcs1Sig.X86.at_]
  refine wp_movzx8 (a := sa scr (o + j)) (by rw [ea_at, hp.esi]; exact aD) rD fun t1 u1 => ?_
  refine wp_movzx8 (a := sa scr (o + d + j)) (by rw [ea_at, u1.other _ (by decide), hp.edi]; exact aS)
    (by rw [u1.rd, u1.wr]; exact rS) fun t2 u2 => ?_
  refine wp_xor fun t3 u3 => wp_and fun t4 u4 => wp_xor fun t5 u5 => ?_
  refine wp_store8 (a := sa scr (o + j)) (by
      rw [ea_at]; simp (disch := decide) only [u5.other, u4.other, u3.other, u2.other, u1.other, hp.esi]; exact aD)
    (by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]; exact wD) fun t6 u6 => ?_
  refine wp_addi fun t7 u7 => wp_addi fun t8 u8 => wp_subi fun t9 u9 _ z9 => WP.block_nil ?_
  have m9 : t9.mem = s.mem.writeW (sa scr (o + j))
      (if c σ then m₀ (sa scr (o + d + j)) else m₀ (sa scr (o + j))) := by
    rw [u9.mem, u8.mem, u7.mem, u6.mem, Reg8.reg]
    simp (disch := decide) only [u5.gpr, u4.gpr, u4.other, u3.gpr, u3.other, u2.gpr, u2.other, u1.gpr, u1.other,
      u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, hp.edx, stj, dj]
    rw [← selByte (m₀ (sa scr (o + d + j))) (m₀ (sa scr (o + j))) (c σ), BitVec.xor_comm (BitVec.setWidth 32 _)]
  have cx8 : t8.gpr .ecx = BitVec.ofNat 32 (n - j) := by
    simp (disch := decide) only [u8.other, u7.other, u6.gpr, u5.other, u4.other, u3.other, u2.other, u1.other,
      hp.ecx]
  have fr1 : Frame [sR scr o n] s.mem t9.mem := by
    rw [m9]; exact frame_byte scr _ _ (by omega) (by omega) (by omega)
  have hc' : Ctx L scr σ t9 := hc.write fr1 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by omega))
    (by rw [u9.rd, u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd])
    (by rw [u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
    (by simp (disch := decide) only [u9.other, u8.other, u7.other, u6.gpr, u5.other, u4.other, u3.other, u2.other,
      u1.other])
    (by simp (disch := decide) only [u9.other, u8.other, u7.other, u6.gpr, u5.other, u4.other, u3.other, u2.other,
      u1.other])
  have sk : ShI scr (c σ) o d n m₀ (j + 1) t9 := by
    refine ⟨?_, ?_, ?_, ?_, hp.fr.trans fr1, fun i hi => ?_⟩
    · simp (disch := decide) only [u9.other, u8.other, u7.gpr, u6.gpr, u5.other, u4.other, u3.other, u2.other,
        u1.other, hp.esi]
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_assoc]
    · simp (disch := decide) only [u9.other, u8.gpr, u7.other, u6.gpr, u5.other, u4.other, u3.other, u2.other,
        u1.other, hp.edi]
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_assoc]
    · rw [u9.gpr, cx8, ofNat_pred (by omega), Nat.sub_sub]
    · simp (disch := decide) only [u9.other, u8.other, u7.other, u6.gpr, u5.other, u4.other, u3.other, u2.other,
        u1.other, hp.edx]
    · rw [m9, sa_write scr _ _ (by omega) (by omega)]
      by_cases e : i = j
      · subst e
        rw [ite_eq_left rfl]
        by_cases hc' : c σ
        · rw [ite_eq_left hc', ite_eq_left ⟨Nat.lt_succ_self _, hc'⟩]
        · rw [ite_eq_right hc', ite_eq_right (fun h => hc' h.2)]
      · rw [ite_eq_right (show ¬ (o + i = o + j) by omega), hp.sel i hi]
        by_cases e' : i < j
        · simp only [e', show i < j + 1 by omega, true_and]
        · simp only [e', show ¬ i < j + 1 by omega, false_and, ite_false]
  rw [cx8, ofNat_pred (by omega), Nat.sub_sub, ofNat_beq_zero (by omega), show n - (j + 1) = k by omega] at z9
  refine ⟨?_, fun h0 => ⟨hc', m₀, hx, sk.fr, fun i hi => ?_⟩, fun hpos => ⟨by omega, hc', m₀, hx, ?_⟩⟩
  · show eval .ne t9 = _
    simp only [eval, z9]
    by_cases h0 : k = 0 <;> simp [h0] <;> omega
  · rw [sk.sel i hi]
    by_cases hc'' : c σ
    · rw [ite_eq_left hc'', ite_eq_left ⟨by omega, hc''⟩]
    · rw [ite_eq_right hc'', ite_eq_right (fun h => hc'' h.2)]
  · rw [show n - k = j + 1 by omega]; exact sk

end VG.Proof.RsaPss.X86
