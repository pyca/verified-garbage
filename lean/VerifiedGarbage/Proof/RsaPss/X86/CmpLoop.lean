module

public import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS on x86: the comparison of two byte strings of our part of `scratch`

`cmpLoop_vp`: the loop `cmpBody` ORs the differences of the `n` bytes at
`oa` and those at `ob` into `edx`, which is zero exactly when they are
equal.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

variable {L : Lay} {scr : BitVec 32}

theorem xor_zero (a b : Byte) : a.setWidth 32 ^^^ b.setWidth 32 = 0 ↔ a = b := by
  have xz : ∀ x y : BitVec 32, x ^^^ y = 0 ↔ x = y := fun x y => BitVec.xor_eq_zero_iff
  rw [xz]
  refine ⟨fun e => ?_, fun e => e ▸ rfl⟩
  have := congrArg (BitVec.setWidth 8) e
  simpa using this

/-- After `j` bytes of the comparison. -/
structure CI (scr : BitVec 32) (oa ob n : Nat) (f g : Nat → Byte) (j : Nat) (s : State) : Prop where
  esi : s.gpr .esi = scr + BitVec.ofNat 32 (oa + j)
  edi : s.gpr .edi = scr + BitVec.ofNat 32 (ob + j)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (n - j)
  edx : s.gpr .edx = 0 ↔ ∀ i < j, f i = g i

/-- The `n` bytes at `oa` compared with those at `ob`: `edx` is zero exactly
when they are equal. -/
theorem cmpLoop_vp (hg : Geo L scr) {oa ob n : Nat} (hn : 0 < n) (ha : oa + n ≤ oRsa) (hb : ob + n ≤ oRsa)
    {X : State → Mem → Prop} {f g : State → Nat → Byte}
    (hfa : ∀ σ m, X σ m → ∀ i < n, m (sa scr (oa + i)) = f σ i)
    (hgb : ∀ σ m, X σ m → ∀ i < n, m (sa scr (ob + i)) = g σ i) :
    VP (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .esi = scr + BitVec.ofNat 32 oa ∧
        s.gpr .edi = scr + BitVec.ofNat 32 ob ∧ s.gpr .ecx = BitVec.ofNat 32 n ∧ s.gpr .edx = 0)
      (countLoop cmpBody)
      (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ (s.gpr .edx = 0 ↔ ∀ i < n, f σ i = g σ i)) := by
  have fit := hg.fit
  unfold oRsa at fit ha hb
  let I : Nat → State → State → Prop := fun k σ s => k ≤ n ∧ Ctx L scr σ s ∧ X σ s.mem ∧
    CI scr oa ob n (f σ) (g σ) (n - k) s
  refine (VP.loop (I := I) (fun k => ?_) (n - 1)).mono (fun σ s ⟨hc, hx, si, di, cx, dx⟩ => ⟨by omega, hc, hx,
    ⟨by rw [si, show n - (n - 1 + 1) = 0 by omega]; rfl, by rw [di, show n - (n - 1 + 1) = 0 by omega]; rfl,
      by rw [cx, show n - (n - (n - 1 + 1)) = n by omega], by
        rw [dx, show n - (n - 1 + 1) = 0 by omega]; exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _),
          fun _ => rfl⟩⟩⟩) fun _ _ h => h
  refine VP.taint _ cmpBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hk, hc, hx, hp⟩ => ?_
  · obtain ⟨-, -, -, p₁⟩ := h₁
    obtain ⟨-, -, -, p₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [p₁.esi, p₂.esi]
    · rw [p₁.edi, p₂.edi]
    · rw [p₁.ecx, p₂.ecx]
  generalize hj : n - (k + 1) = j at hp
  have hjn : j < n := by omega
  have aA : VG.X86.addr (scr + BitVec.ofNat 32 (oa + j)) 0 = sa scr (oa + j) := by
    rw [hg.addrD (by unfold oRsa; omega), Nat.add_zero]
  have aB : VG.X86.addr (scr + BitVec.ofNat 32 (ob + j)) 0 = sa scr (ob + j) := by
    rw [hg.addrD (by unfold oRsa; omega), Nat.add_zero]
  have rA : InRegions (s.rd ++ s.wr) (sa scr (oa + j)) 1 := hg.rd hc.st (by unfold oRsa; omega)
  have rB : InRegions (s.rd ++ s.wr) (sa scr (ob + j)) 1 := hg.rd hc.st (by unfold oRsa; omega)
  simp only [cmpBody, addi, Impl.RsaPkcs1Sig.X86.at_]
  refine wp_movzx8 (a := sa scr (oa + j)) (by rw [ea_at, hp.esi]; exact aA) rA fun t1 u1 => ?_
  refine wp_movzx8 (a := sa scr (ob + j)) (by rw [ea_at, u1.other _ (by decide), hp.edi]; exact aB)
    (by rw [u1.rd, u1.wr]; exact rB) fun t2 u2 => ?_
  refine wp_xor fun t3 u3 => wp_or fun t4 u4 => ?_
  refine wp_addi fun t5 u5 => wp_addi fun t6 u6 => wp_subi fun t7 u7 _ z7 => WP.block_nil ?_
  have m7 : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have c7 : Ctx L scr σ t7 :=
    ((((((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3 (by decide) (by decide)).upd u4
      (by decide) (by decide)).upd u5 (by decide) (by decide)).upd u6 (by decide) (by decide)).upd u7 (by decide)
      (by decide)
  have cx6 : t6.gpr .ecx = BitVec.ofNat 32 (n - j) := by
    simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, u2.other, u1.other, hp.ecx]
  have dx : t7.gpr .edx = s.gpr .edx ||| ((f σ j).setWidth 32 ^^^ (g σ j).setWidth 32) := by
    simp (disch := decide) only [u7.other, u6.other, u5.other, u4.gpr, u3.gpr, u3.other, u2.gpr, u2.other, u1.gpr,
      u1.other]
    rw [u1.mem, hfa σ s.mem hx j hjn, hgb σ s.mem hx j hjn]
  have sk : CI scr oa ob n (f σ) (g σ) (j + 1) t7 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u7.other, u6.other, u5.gpr, u4.other, u3.other, u2.other, u1.other, hp.esi]
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_assoc]
    · simp (disch := decide) only [u7.other, u6.gpr, u5.other, u4.other, u3.other, u2.other, u1.other, hp.edi]
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_assoc]
    · rw [u7.gpr, cx6, ofNat_pred (by omega), Nat.sub_sub]
    · have oz : ∀ x y : BitVec 32, (x ||| y = 0) ↔ (x = 0 ∧ y = 0) := fun x y => BitVec.or_eq_zero_iff
      rw [dx, oz, hp.edx, xor_zero]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases (by omega : i < j ∨ i = j) with hi | rfl
        · exact h1 i hi
        · exact h2
      · intro h'
        exact ⟨fun i hi => h' i (by omega), h' j (by omega)⟩
  rw [cx6, ofNat_pred (by omega), Nat.sub_sub, ofNat_beq_zero (by omega), show n - (j + 1) = k by omega] at z7
  refine ⟨?_, fun h0 => ⟨c7, m7 ▸ hx, by rw [show n = j + 1 by omega]; exact sk.edx⟩,
    fun hpos => ⟨by omega, c7, m7 ▸ hx, by rw [show n - k = j + 1 by omega]; exact sk⟩⟩
  show eval .ne t7 = _
  simp only [eval, z7]
  by_cases h0 : k = 0 <;> simp [h0] <;> omega

end VG.Proof.RsaPss.X86.Vf
