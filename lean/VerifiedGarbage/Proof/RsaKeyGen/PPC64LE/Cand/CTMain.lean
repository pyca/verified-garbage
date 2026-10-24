module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.CTTest
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Bits
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Gcd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.CTTest
meta import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Bits
meta import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Gcd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-!
# A candidate on PPC64LE: the candidate in constant time

`main_ct`: two runs with the same public data, once `rand` holds a
candidate, leak the same trace. The taint analysis checks the setup, the
candidate's load and the test of its closeness to `p` from the pointers and
lengths; whether it is too close (`close_agree`) and whether
`gcd(c − 1, e) = 1` (`gcd_agree`) are the same in both runs, and
`gcdCheck`'s own branches depend on `e` alone, which the leak gives.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (main setup loadC closeCheck gcdCheck gcdE loadE finish)
open VG.Proof.MillerRabin.PPC64LE (Env arr RoundImpl)
open VG.Proof.Bignum (slot)

/-- A stage of `main`, from the call `s0`. -/
def SG (X : State → State → Prop) (a : CD) (s : State) : Prop := ∃ s0, KRel a s0 ∧ X s0 s

theorem pins_MIn : Pins (SG MIn) [.r11, .r24, .r31] := by
  rintro a s₁ s₂ ⟨s0, k, h⟩ ⟨s0', k', h'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.r11, h'.r11]; exact k.arg k' (by decide)
  · rw [h.ctx.r24, h'.ctx.r24]; exact k.reg k' (by decide)
  · rw [h.r31, h'.r31]; exact k.arg k' (by decide)

theorem pins_M1 : Pins (SG M1) [.r24, .r26, .r10, .r11, .r29, .r31] := by
  rintro a s₁ s₂ ⟨s0, k, h⟩ ⟨s0', k', h'⟩ r hr
  have ea := env_agree k k' h.env h'.env
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.ctx.r24, h'.ctx.r24]; exact k.reg k' (by decide)
  · rw [h.r26, h'.r26]; exact k.reg k' (by decide)
  all_goals exact ea _ (by simp)

theorem pins_M2 : Pins (SG M2) [.r18, .r19, .r24, .r10, .r11, .r29, .r31] := by
  rintro a s₁ s₂ ⟨s0, k, h⟩ ⟨s0', k', h'⟩ r hr
  have ea := env_agree k k' h.env h'.env
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.r18, h'.r18]; exact k.reg k' (by decide)
  · rw [h.r19, h'.r19]; exact k.reg k' (by decide)
  · rw [h.ctx.r24, h'.ctx.r24]; exact k.reg k' (by decide)
  all_goals exact ea _ (by simp)

theorem pins_M3 : Pins (SG M3) [.r21, .r30, .r25] := by
  rintro a s₁ s₂ ⟨s0, k, h⟩ ⟨s0', k', h'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.r21, h'.r21]; exact k.reg k' (by decide)
  · rw [h.r30, h'.r30]; exact k.reg k' (by decide)
  · rw [h.ctx.r25, h'.ctx.r25]; exact k.reg k' (by decide)

theorem pins_M4 : Pins (SG M4) [.r25] := by
  rintro a s₁ s₂ ⟨s0, k, h⟩ ⟨s0', k', h'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [h.ctx.r25, h'.ctx.r25]; exact k.reg k' (by decide)

theorem close_eval : ∀ (a : CD) (s₁ s₂ : State), SG M3 a s₁ → SG M3 a s₂ →
    isa.eval (.nonzero .d .r22) s₁ = isa.eval (.nonzero .d .r22) s₂ := by
  rintro a s₁ s₂ ⟨s0, k, h⟩ ⟨s0', k', h'⟩
  rw [eval_nonzero_ofNat' _ _ (by split <;> decide) h.f, eval_nonzero_ofNat' _ _ (by split <;> decide) h'.f]
  have hav := h.hav
  have hav' := h'.hav
  obtain ⟨hw, -, -⟩ := cw_facts k.1
  obtain ⟨hw', -, -⟩ := cw_facts k'.1
  have e := close_agree k k' hav
  rw [candS_eq k.1 hav, candS_eq k'.1 hav', hw, hw', show 8 * (8 * cw s0) = 64 * cw s0 by omega,
    show 8 * (8 * cw s0') = 64 * cw s0' by omega] at e
  rw [e]

/-! ## `gcdCheck` -/

/-- `gcdCheck`'s states: `M3` with the registers `rs` changed. -/
def GS (rs : List Reg) (V : State → State → Prop) (a : CD) (t : State) : Prop :=
  ∃ s0 sM, KRel a s0 ∧ M3 s0 sM ∧
    Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = false ∧
    Keep rs sM t ∧ V s0 t

theorem pins_GS {rs : List Reg} {V : State → State → Prop}
    (hr : ∀ r ∈ VG.Proof.MillerRabin.PPC64LE.envRegs, r ∉ rs := by decide) :
    Pins (GS rs V) [.r10, .r11, .r29, .r31] := by
  rintro a s₁ s₂ ⟨s0, sM, k, h, -, kk, -⟩ ⟨s0', sM', k', h', -, kk', -⟩ r hr'
  have ea := env_agree k k' (h.env.keep kk hr) (h'.env.keep kk' hr)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl <;> exact ea _ (by simp)

/-- `e`. -/
abbrev eV (s0 : State) : Nat := Spec.Rsa.os2ip (eB s0)

theorem eV_lt {s0 : State} (hp : CIn s0) : eV s0 < 2 ^ 64 := by
  have := os2ip_bytes_lt s0.mem (s0.gpr .r6) (s0.gpr .r7).toNat
  have : 256 ^ (s0.gpr .r7).toNat ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) hp.el2
  have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  show Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r6) (s0.gpr .r7).toNat) < 2 ^ 64
  omega

/-- `gcdCheck`'s start. -/
def G0 (a : CD) (s : State) : Prop :=
  ∃ s0, KRel a s0 ∧ M3 s0 s ∧
    Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = false

theorem pins_G0 : Pins G0 [.r21, .r30] := by
  rintro a s₁ s₂ ⟨s0, k, h, -⟩ ⟨s0', k', h', -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h.r21, h'.r21]; exact k.reg k' (by decide)
  · rw [h.r30, h'.r30]; exact k.reg k' (by decide)

abbrev g1Regs : List Reg := [.r0, .r3, .r14, .r17, .r21]
abbrev g2Regs : List Reg := g1Regs ++ [.r0, .r5]
abbrev g3Regs : List Reg := g2Regs ++ [.r5]

theorem gcd_ct : RelCT isa (Two G0) gcdCheck fun _ _ => True := by
  unfold gcdCheck
  refine RelCT.seq (two_post (Ψ := GS g1Regs fun s0 t => t.gpr .r21 = BitVec.ofNat 64 (eV s0))
    (two_taint _ pins_G0 (by taint_decide)) fun a s ⟨s0, k, h, hn⟩ => ?_)
    (RelCT.seq (two_post (Ψ := GS g2Regs fun s0 t => t.gpr .r21 = BitVec.ofNat 64 (eV s0) ∧
      t.gpr .r5 = BitVec.ofNat 64 (eV s0 % 2)) (two_taint [] (fun _ _ _ _ _ _ hr => by simp at hr) (by taint_decide))
      fun a s ⟨s0, sM, k, h, hn, kk, h21⟩ => ?_)
    (two_ite ?_ (two_taint [] (fun _ _ _ _ _ _ hr => by simp at hr) (by taint_decide))
      (RelCT.seq (two_post (Ψ := GS g3Regs fun s0 t => t.gpr .r5 = BitVec.ofNat 64 (eV s0 - 1))
        (two_taint [] (fun _ _ _ _ _ _ hr => by simp at hr) (by taint_decide))
        fun a s ⟨⟨s0, sM, k, h, hn, kk, h21, h5⟩, ev⟩ => ?_)
        (two_ite ?_ (two_taint [] (fun _ _ _ _ _ _ hr => by simp at hr) (by taint_decide))
          (two_taint _ (pins_and pins_GS) (by taint_decide))))))
  · have hp := k.1
    have hfe := hp.fe
    have bE : Spec.Rsa.bytesAt s.mem (s0.gpr .r6) (s0.gpr .r7).toNat = eB s0 :=
      in_bytes h.ctx.bx (ρ := cE s0) (hE_dj hp) (Nat.le_refl _) (by omega)
    refine WP.mono (loadE_ok (h.r21.trans (BitVec.add_zero _).symm) (h.r30.trans (ofNat_toNat64 _).symm)
      hp.el1 hp.el2 (rd_bytes (n := (s0.gpr .r7).toNat) (by rw [h.ctx.bx.rd]; exact hp.rE) hfe (by omega)))
      fun t ⟨⟨a21, _⟩, kt⟩ => ⟨s0, s, k, h, hn, kt, by show t.gpr .r21 = _; rw [a21, bE]⟩
  · have hEl := eV_lt k.1
    refine WP.mono (WP.keep [.r0, .r5] (Q := fun t => t.gpr .r5 = BitVec.ofNat 64 (eV s0 % 2) ∧
        t.gpr .r21 = s.gpr .r21) (by
      prun [h21, VG.Proof.RsaKeyGen.PPC64LE.Cand.and1_val]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hEl]
      split <;> (congr 1; omega)) (by decide))
      fun t ⟨⟨a5, a21⟩, kt⟩ => ⟨s0, sM, k, h, hn, kk.trans kt, a21.trans h21, a5⟩
  · rintro a s₁ s₂ ⟨s0, sM, k, -, -, -, -, h5⟩ ⟨s0', sM', k', -, -, -, -, h5'⟩
    rw [eval_zero_ofNat _ _ (by have := Nat.mod_lt (eV s0) (show 0 < 2 by decide); omega) h5,
      eval_zero_ofNat _ _ (by have := Nat.mod_lt (eV s0') (show 0 < 2 by decide); omega) h5']
    simp only [eV, k.e k']
  · have hEl := eV_lt k.1
    have he1 : eV s0 % 2 = 1 := by
      rw [eval_zero_ofNat _ _ (by have := Nat.mod_lt (eV s0) (show 0 < 2 by decide); omega) h5] at ev
      simp at ev; omega
    refine WP.mono (WP.keep [.r5] (Q := fun t => t.gpr .r5 = BitVec.ofNat 64 (eV s0 - 1)) (by
      prun [h21]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega) (by decide))
      fun t ⟨a5, kt⟩ => ⟨s0, sM, k, h, hn, kk.trans kt, a5⟩
  · rintro a s₁ s₂ ⟨s0, sM, k, -, -, -, h5⟩ ⟨s0', sM', k', -, -, -, h5'⟩
    have := eV_lt k.1
    have := eV_lt k'.1
    rw [eval_zero_ofNat _ _ (by omega) h5, eval_zero_ofNat _ _ (by omega) h5']
    simp only [eV, k.e k']

theorem gcd_eval : ∀ (a : CD) (s₁ s₂ : State), SG M4 a s₁ → SG M4 a s₂ →
    isa.eval (.nonzero .d .r22) s₁ = isa.eval (.nonzero .d .r22) s₂ := by
  rintro a s₁ s₂ ⟨s0, k, h⟩ ⟨s0', k', h'⟩
  rw [VG.PPC64LE.eval_nonzero, VG.PPC64LE.eval_nonzero]
  have hav := h.hav
  have hav' := h'.hav
  obtain ⟨hw, -, -⟩ := cw_facts k.1
  obtain ⟨hw', -, -⟩ := cw_facts k'.1
  have e := gcd_agree k k' hav (by rw [candS_eq k.1 hav, show 8 * oL s0 = 64 * cw s0 by omega]; exact h.ncl)
  rw [candS_eq k.1 hav, candS_eq k'.1 hav'] at e
  have i : s₁.gpr .r22 = 0 ↔ s₂.gpr .r22 = 0 := h.g.trans (e.trans h'.g.symm)
  congr 1
  by_cases z : s₁.gpr .r22 = 0
  · rw [z, i.mp z]
  · have z' : ¬ s₂.gpr .r22 = 0 := fun e' => z (i.mpr e')
    rw [bne_iff_ne.mpr z, bne_iff_ne.mpr z']

theorem main_ct {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) :
    RelCT isa (Two (SG MIn)) (main trial R.name R.code) fun _ _ => True := by
  unfold main
  simp only [VG.Impl.RsaKeyGen.PPC64LE.Candidate.seqs]
  refine RelCT.seq (two_post (Ψ := SG M1) (two_taint _ pins_MIn (by taint_decide))
    fun a s ⟨s0, k, h⟩ => WP.mono (setupS h) fun t ht => ⟨s0, k, ht⟩)
    (RelCT.seq (two_post (Ψ := SG M2) (two_taint _ pins_M1 (by taint_decide))
      fun a s ⟨s0, k, h⟩ => WP.mono (loadCS h) fun t ht => ⟨s0, k, ht⟩)
    (RelCT.seq (two_post (Ψ := SG M3) (two_taint _ pins_M2 (by taint_decide))
      fun a s ⟨s0, k, h⟩ => WP.mono (closeS h) fun t ht => ⟨s0, k, ht⟩)
    (two_ite close_eval (two_taint _ (pins_and pins_M3) (by taint_decide))
      (RelCT.seq (two_post (Ψ := SG M4) (two_mono (Ψ := G0) (fun a s ⟨⟨s0, k, h⟩, ev⟩ => ⟨s0, k, h, ?_⟩) gcd_ct)
        fun a s ⟨⟨s0, k, h⟩, ev⟩ => WP.mono (gcdS h ?_) fun t ht => ⟨s0, k, ht⟩)
        (two_ite gcd_eval (two_taint _ (pins_and pins_M4) (by taint_decide))
          (two_mono (Ψ := TI) (fun a s ⟨⟨s0, k, h⟩, ev⟩ => ⟨s0, ⟨k, h.ncl, ?_⟩, toTIn h ?_⟩) (test_ct D R)))))))
  · rw [eval_nonzero_ofNat' _ _ (by split <;> decide) h.f] at ev
    revert ev; cases Spec.RsaKeyGen.tooClose _ _ (candOf s0) <;> decide
  · rw [eval_nonzero_ofNat' _ _ (by split <;> decide) h.f] at ev
    revert ev; cases Spec.RsaKeyGen.tooClose _ _ (candOf s0) <;> decide
  · rw [VG.PPC64LE.eval_nonzero] at ev
    exact h.g.mp (by simpa using ev)
  · rw [VG.PPC64LE.eval_nonzero] at ev
    exact h.g.mp (by simpa using ev)

end VG.Proof.RsaKeyGen.PPC64LE.Cand
