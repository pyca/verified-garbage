module

public import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# RSASSA-PSS on x86: XOR of bytes

`xor_vp`: the loop `xorBody` XORs the `n` bytes at one offset of our part
of `scratch` into those at another.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

/-- The XOR of two bytes, as `xor` of their zero extensions. -/
theorem xorByte (a b : Byte) : (a.setWidth 32 ^^^ b.setWidth 32).setWidth 8 = a ^^^ b := by
  have e1 : ∀ x : BitVec 8, (x.setWidth 32).setWidth 8 = x := fun x => by simp
  rw [BitVec.setWidth_xor, e1, e1]

variable {L : Lay} {scr : BitVec 32}

/-- After `j` bytes of the XOR, from memory `m₀`. -/
structure XI (scr : BitVec 32) (od os n : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop where
  edi : s.gpr .edi = scr + BitVec.ofNat 32 (od + j)
  esi : s.gpr .esi = scr + BitVec.ofNat 32 (os + j)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (n - j)
  fr : Frame [sR scr od n] m₀ s.mem
  x : ∀ i < n, s.mem (sa scr (od + i)) =
    if i < j then m₀ (sa scr (od + i)) ^^^ m₀ (sa scr (os + i)) else m₀ (sa scr (od + i))

/-- The `n` bytes at `os` XORed into those at `od`. -/
theorem xor_vp (hg : Geo L scr) {od os n : Nat} (hn : 0 < n) (hd : od + n ≤ oRsa) (hs : os + n ≤ oRsa)
    (hsep : od + n ≤ os ∨ os + n ≤ od) {X : State → Mem → Prop} :
    VP (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .edi = scr + BitVec.ofNat 32 od ∧
        s.gpr .esi = scr + BitVec.ofNat 32 os ∧ s.gpr .ecx = BitVec.ofNat 32 n)
      (countLoop xorBody)
      (fun σ s => Ctx L scr σ s ∧ ∃ m₀, X σ m₀ ∧ Frame [sR scr od n] m₀ s.mem ∧
        ∀ i < n, s.mem (sa scr (od + i)) = m₀ (sa scr (od + i)) ^^^ m₀ (sa scr (os + i))) := by
  have fit := hg.fit
  unfold oRsa at fit hd hs
  let I : Nat → State → State → Prop := fun k σ s => k ≤ n ∧ Ctx L scr σ s ∧
    ∃ m₀, X σ m₀ ∧ XI scr od os n m₀ (n - k) s
  refine (VP.loop (I := I) (fun k => ?_) (n - 1)).mono (fun σ s ⟨hc, hx, di, si, cx⟩ => ⟨by omega, hc,
    s.mem, hx, ⟨by rw [di, show n - (n - 1 + 1) = 0 by omega]; rfl, by rw [si, show n - (n - 1 + 1) = 0 by omega]; rfl,
      by rw [cx, show n - (n - (n - 1 + 1)) = n by omega], Frame.refl _ _, fun i _ => by
        rw [ite_eq_right (by omega)]⟩⟩) fun _ _ h => h
  refine VP.taint _ xorBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hk, hc, m₀, hx, hp⟩ => ?_
  · obtain ⟨-, -, _, -, p₁⟩ := h₁
    obtain ⟨-, -, _, -, p₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [p₁.esi, p₂.esi]
    · rw [p₁.edi, p₂.edi]
    · rw [p₁.ecx, p₂.ecx]
  generalize hj : n - (k + 1) = j at hp
  have hjn : j < n := by omega
  have aD : VG.X86.addr (scr + BitVec.ofNat 32 (od + j)) 0 = sa scr (od + j) := by
    rw [hg.addrD (by unfold oRsa; omega), Nat.add_zero]
  have aS : VG.X86.addr (scr + BitVec.ofNat 32 (os + j)) 0 = sa scr (os + j) := by
    rw [hg.addrD (by unfold oRsa; omega), Nat.add_zero]
  have rS : InRegions (s.rd ++ s.wr) (sa scr (os + j)) 1 := hg.rd hc.st (by unfold oRsa; omega)
  have rD : InRegions (s.rd ++ s.wr) (sa scr (od + j)) 1 := hg.rd hc.st (by unfold oRsa; omega)
  have wD : InRegions s.wr (sa scr (od + j)) 1 := hg.wr hc.st (by unfold oRsa; omega)
  have stj : s.mem (sa scr (os + j)) = m₀ (sa scr (os + j)) :=
    hp.fr _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Geo.sep (scr := scr) (o := os + j) (n := 1) (by omega) (by unfold oRsa; omega) (by unfold oRsa; omega) _
        (Region.contains_self _ _)
  have dj : s.mem (sa scr (od + j)) = m₀ (sa scr (od + j)) := by
    rw [hp.x j hjn, ite_eq_right (Nat.lt_irrefl _)]
  simp only [xorBody, addi, Impl.RsaPkcs1Sig.X86.at_]
  refine wp_movzx8 (a := sa scr (od + j)) (by rw [ea_at, hp.edi]; exact aD) rD fun t1 u1 => ?_
  refine wp_movzx8 (a := sa scr (os + j)) (by rw [ea_at, u1.other _ (by decide), hp.esi]; exact aS)
    (by rw [u1.rd, u1.wr]; exact rS) fun t2 u2 => ?_
  refine wp_xor fun t3 u3 => ?_
  refine wp_store8 (a := sa scr (od + j)) (by
      rw [ea_at]; simp (disch := decide) only [u3.other, u2.other, u1.other, hp.edi]; exact aD)
    (by rw [u3.wr, u2.wr, u1.wr]; exact wD) fun t4 u4 => ?_
  refine wp_addi fun t5 u5 => wp_addi fun t6 u6 => wp_subi fun t7 u7 _ z7 => WP.block_nil ?_
  have m7 : t7.mem = s.mem.writeW (sa scr (od + j)) (m₀ (sa scr (od + j)) ^^^ m₀ (sa scr (os + j))) := by
    rw [u7.mem, u6.mem, u5.mem, u4.mem, Reg8.reg]
    simp (disch := decide) only [u3.gpr, u2.gpr, u2.other, u1.gpr, u3.mem, u2.mem, u1.mem, xorByte, stj, dj]
  have cx6 : t6.gpr .ecx = BitVec.ofNat 32 (n - j) := by
    simp (disch := decide) only [u6.other, u5.other, u4.gpr, u3.other, u2.other, u1.other, hp.ecx]
  have fr1 : Frame [sR scr od n] s.mem t7.mem := by
    rw [m7]; exact frame_byte scr _ _ (by omega) (by omega) (by omega)
  have hc' : Ctx L scr σ t7 := hc.write fr1 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by unfold oRsa; omega))
    (by rw [u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd])
    (by rw [u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
    (by simp (disch := decide) only [u7.other, u6.other, u5.other, u4.gpr, u3.other, u2.other, u1.other])
    (by simp (disch := decide) only [u7.other, u6.other, u5.other, u4.gpr, u3.other, u2.other, u1.other])
  have sk : XI scr od os n m₀ (j + 1) t7 := by
    refine ⟨?_, ?_, ?_, hp.fr.trans fr1, fun i hi => ?_⟩
    · simp (disch := decide) only [u7.other, u6.other, u5.gpr, u4.gpr, u3.other, u2.other, u1.other, hp.edi]
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_assoc]
    · simp (disch := decide) only [u7.other, u6.gpr, u5.other, u4.gpr, u3.other, u2.other, u1.other, hp.esi]
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_assoc]
    · rw [u7.gpr, cx6, ofNat_pred (by omega), Nat.sub_sub]
    · rw [m7, sa_write scr _ _ (by omega) (by omega)]
      by_cases e : i = j
      · subst e
        rw [ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self _)]
      · rw [ite_eq_right (show ¬ (od + i = od + j) by omega), hp.x i hi]
        by_cases e' : i < j
        · rw [ite_eq_left e', ite_eq_left (by omega)]
        · rw [ite_eq_right e', ite_eq_right (by omega)]
  rw [cx6, ofNat_pred (by omega), Nat.sub_sub, ofNat_beq_zero (by omega), show n - (j + 1) = k by omega] at z7
  refine ⟨?_, fun h0 => ⟨hc', m₀, hx, sk.fr, fun i hi => ?_⟩, fun hpos => ⟨by omega, hc', m₀, hx, ?_⟩⟩
  · show eval .ne t7 = _
    simp only [eval, z7]
    by_cases h0 : k = 0 <;> simp [h0] <;> omega
  · rw [sk.x i hi, ite_eq_left (by omega)]
  · rw [show n - k = j + 1 by omega]; exact sk

end VG.Proof.RsaPss.X86
