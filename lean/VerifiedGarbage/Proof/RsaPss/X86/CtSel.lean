module

public import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# RSASSA-PSS on x86: hashing, the selection of the hash value

`sel_vp`: the selection loop copies the hash value at `oSt` to `oSel` under
a mask (all ones or zero, as a condition `c` on the run decides), and leaves
`oSel` as it was otherwise.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

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
  esi : s.gpr .esi = scr + BitVec.ofNat 32 (oSt + j)
  edi : s.gpr .edi = scr + BitVec.ofNat 32 (oSel + j)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (h.N - j)
  edx : s.gpr .edx = maskOf c
  fr : Frame [sR scr oSel h.N] m₀ s.mem
  sel : ∀ i < h.N, s.mem (sa scr (oSel + i)) = if i < j ∧ c then m₀ (sa scr (oSt + i)) else m₀ (sa scr (oSel + i))

/-- The selection: the hash value at `oSt` copied to `oSel` if `c`. -/
theorem sel_vp (hg : Geo L scr) {c : State → Prop} [∀ σ, Decidable (c σ)] {X : State → Mem → Prop} :
    VP (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .esi = scr + BitVec.ofNat 32 oSt ∧
        s.gpr .edi = scr + BitVec.ofNat 32 oSel ∧ s.gpr .ecx = BitVec.ofNat 32 h.N ∧ s.gpr .edx = maskOf (c σ))
      (countLoop selBody)
      (fun σ s => Ctx L scr σ s ∧ ∃ m₀, X σ m₀ ∧ Frame [sR scr oSel h.N] m₀ s.mem ∧
        ∀ i < h.N, s.mem (sa scr (oSel + i)) = if c σ then m₀ (sa scr (oSt + i)) else m₀ (sa scr (oSel + i))) := by
  have _ : oCW = 0 := rfl
  have _ : oSt = 512 := rfl
  have _ : oSel = 768 := rfl
  have _ : oDig = 832 := rfl
  have _ : oLen = 896 := rfl
  have _ : oEm = 1024 := rfl
  have _ : oY = 2048 := rfl
  have _ : oRsa = 8192 := rfl
  have _ : frameBytes = 144 := rfl

  have hN := h.N_le
  have hN0 : 0 < h.N := by have := h.D_pos; have := h.D_le; omega
  have fit := hg.fit
  unfold oRsa at fit
  let I : Nat → State → State → Prop := fun n σ s => n ≤ h.N ∧ Ctx L scr σ s ∧
    ∃ m₀, X σ m₀ ∧ SI h scr (c σ) m₀ (h.N - n) s
  refine (VP.loop (I := I) (fun n => ?_) (h.N - 1)).mono (fun σ s ⟨hc, hx, si, di, cx, dx⟩ => ⟨by omega, hc,
    s.mem, hx, ⟨by rw [si, show h.N - (h.N - 1 + 1) = 0 by omega]; rfl,
      by rw [di, show h.N - (h.N - 1 + 1) = 0 by omega]; rfl,
      by rw [cx, show h.N - (h.N - (h.N - 1 + 1)) = h.N by omega], dx, Frame.refl _ _, fun i _ => by
        rw [ite_eq_right (by omega)]⟩⟩) fun _ _ h => h
  refine VP.taint _ selBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hn, hc, m₀, hx, hp⟩ => ?_
  · obtain ⟨-, -, _, -, p₁⟩ := h₁
    obtain ⟨-, -, _, -, p₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [p₁.esi, p₂.esi]
    · rw [p₁.edi, p₂.edi]
    · rw [p₁.ecx, p₂.ecx]
  generalize hj : h.N - (n + 1) = j at hp
  have hjN : j < h.N := by omega
  have aS : VG.X86.addr (scr + BitVec.ofNat 32 (oSt + j)) 0 = sa scr (oSt + j) := by
    rw [hg.addrD (by omega_arith), Nat.add_zero]
  have aE : VG.X86.addr (scr + BitVec.ofNat 32 (oSel + j)) 0 = sa scr (oSel + j) := by
    rw [hg.addrD (by omega_arith), Nat.add_zero]
  have rS : InRegions (s.rd ++ s.wr) (sa scr (oSt + j)) 1 := hg.rd hc.st (by omega_arith)
  have rE : InRegions (s.rd ++ s.wr) (sa scr (oSel + j)) 1 := hg.rd hc.st (by omega_arith)
  have wE : InRegions s.wr (sa scr (oSel + j)) 1 := hg.wr hc.st (by omega_arith)
  have stj : s.mem (sa scr (oSt + j)) = m₀ (sa scr (oSt + j)) :=
    hp.fr _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Geo.sep (scr := scr) (o := oSt + j) (n := 1) (by omega_arith) (by omega_arith) (by omega_arith) _ (Region.contains_self _ _)
  simp only [selBody, addi, Impl.RsaPkcs1Sig.X86.at_]
  refine wp_movzx8 (a := sa scr (oSt + j)) (by rw [ea_at, hp.esi]; exact aS) rS fun t1 u1 => ?_
  refine wp_movzx8 (a := sa scr (oSel + j)) (by rw [ea_at, u1.other _ (by decide), hp.edi]; exact aE) (by rw [u1.rd, u1.wr]; exact rE)
    fun t2 u2 => ?_
  refine wp_xor fun t3 u3 => wp_and fun t4 u4 => wp_xor fun t5 u5 => ?_
  refine wp_store8 (a := sa scr (oSel + j)) (by
      rw [ea_at]; simp (disch := decide) only [u5.other, u4.other, u3.other, u2.other, u1.other, hp.edi]; exact aE)
    (by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]; exact wE) fun t6 u6 => ?_
  refine wp_addi fun t7 u7 => wp_addi fun t8 u8 => wp_subi fun t9 u9 _ z9 => WP.block_nil ?_
  have m9 : t9.mem = s.mem.writeW (sa scr (oSel + j))
      (if c σ then m₀ (sa scr (oSt + j)) else s.mem (sa scr (oSel + j))) := by
    rw [u9.mem, u8.mem, u7.mem, u6.mem, Reg8.reg]
    simp (disch := decide) only [u5.gpr, u4.gpr, u4.other, u3.gpr, u3.other, u2.gpr, u2.other, u1.gpr, u1.other,
      u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, hp.edx, selByte, stj]
  have cx8 : t8.gpr .ecx = BitVec.ofNat 32 (h.N - j) := by
    simp (disch := decide) only [u8.other, u7.other, u6.gpr, u5.other, u4.other, u3.other, u2.other, u1.other, hp.ecx]
  have fr1 : Frame [sR scr oSel h.N] s.mem t9.mem := by
    rw [m9]; exact frame_byte scr _ _ (by omega) (by omega) (by omega_arith)
  have hc' : Ctx L scr σ t9 := hc.write fr1 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by omega_arith))
    (by rw [u9.rd, u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd])
    (by rw [u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
    (by simp (disch := decide) only [u9.other, u8.other, u7.other, u6.gpr, u5.other, u4.other, u3.other, u2.other,
      u1.other])
    (by simp (disch := decide) only [u9.other, u8.other, u7.other, u6.gpr, u5.other, u4.other, u3.other, u2.other,
      u1.other])
  have sk : SI h scr (c σ) m₀ (j + 1) t9 := by
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
    · rw [m9, sa_write scr _ _ (by omega_arith) (by omega_arith)]
      by_cases e : i = j
      · subst e
        rw [ite_eq_left rfl, hp.sel i hi, ite_eq_right (show ¬ (i < i ∧ c σ) from fun h => absurd h.1 (Nat.lt_irrefl _))]
        by_cases hc' : c σ
        · rw [ite_eq_left hc', ite_eq_left ⟨Nat.lt_succ_self _, hc'⟩]
        · rw [ite_eq_right hc', ite_eq_right (fun h => hc' h.2)]
      · rw [ite_eq_right (show ¬ (oSel + i = oSel + j) by omega), hp.sel i hi]
        by_cases e' : i < j
        · simp only [e', show i < j + 1 by omega, true_and]
        · simp only [e', show ¬ i < j + 1 by omega, false_and, ite_false]
  rw [cx8, ofNat_pred (by omega), Nat.sub_sub, ofNat_beq_zero (by omega), show h.N - (j + 1) = n by omega] at z9
  refine ⟨?_, fun h0 => ⟨hc', m₀, hx, sk.fr, fun i hi => ?_⟩, fun hpos => ⟨by omega, hc', m₀, hx, ?_⟩⟩
  · show eval .ne t9 = _
    simp only [eval, z9]
    by_cases h0 : n = 0 <;> simp [h0] <;> omega
  · rw [sk.sel i hi]
    by_cases hc'' : c σ
    · rw [ite_eq_left hc'', ite_eq_left ⟨by omega, hc''⟩]
    · rw [ite_eq_right hc'', ite_eq_right (fun h => hc'' h.2)]
  · rw [show h.N - n = j + 1 by omega]; exact sk

end VG.Proof.RsaPss.X86
