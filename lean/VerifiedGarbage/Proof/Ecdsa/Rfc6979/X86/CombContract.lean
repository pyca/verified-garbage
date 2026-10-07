import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Verified
import VerifiedGarbage.Proof.Ecdsa.X86.CombSat

/-! # The shared RFC 6979 contract with the x86 P-256 comb table -/
namespace VG.Proof.Ecdsa.Rfc6979.X86
open VG VG.X86 VG.Impl.Ecdsa.X86
open VG.Proof.Ecdsa.X86 (p256W p256W_length p256Comb_consts combSatState combSat_arg combSatMem_held)

/-- The existing signing witness, with RFC 6979's four arguments and table. -/
def rfcCombSat (D : Nat) : State := { combSatState with
  rd := [⟨0x2000, 32⟩, ⟨0x3000, D⟩, ⟨0x100000, 151552⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8192⟩, ⟨0x20004, 16⟩] }

theorem rfcCombSat_spec (I : Spec.Ecdsa.Rfc6979.Instance)
    (hI : I.ecdsa = Spec.Ecdsa.P256.inst) (hD : I.hashLen ≤ 64) :
    (I.signContract (X86.abi.withConsts p256Comb.combConsts) 272).pre (rfcCombSat I.hashLen) := by
  have a0 : arg (rfcCombSat I.hashLen) 0 = 0x1000 := (combSat_arg 0 (by decide)).trans (by decide)
  have a1 : arg (rfcCombSat I.hashLen) 1 = 0x2000 := (combSat_arg 1 (by decide)).trans (by decide)
  have a2 : arg (rfcCombSat I.hashLen) 2 = 0x3000 := (combSat_arg 2 (by decide)).trans (by decide)
  have a3 : arg (rfcCombSat I.hashLen) 3 = 0x4000 := (combSat_arg 3 (by decide)).trans (by decide)
  have esp : (rfcCombSat I.hashLen).gpr .esp = 0x20000 := rfl
  have sy : (rfcCombSat I.hashLen).syms "VG_P256_COMB" = 0x100000 := rfl
  have aa : argAddr (rfcCombSat I.hashLen) 0 = 0x20004 := rfl
  have held : ∀ i < p256W.length, (rfcCombSat I.hashLen).mem.readW
      (((rfcCombSat I.hashLen).syms "VG_P256_COMB").setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 =
      p256W.getD i 0 := combSatMem_held
  generalize e : rfcCombSat I.hashLen = s
  sig_pre [Spec.Ecdsa.Rfc6979.Instance.signContract, Spec.Ecdsa.Rfc6979.Instance.signSig,
    hI, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p256Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  simp only [hI, Spec.Ecdsa.P256.inst, Spec.P256.curve, esp, sy, aa]
  refine ⟨by decide, by decide, ?_, held, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p256W_length]; rfl
  · rw [p256W_length]; decide
  · rw [p256W_length]
    intro r hr
    change r ∈ [⟨0x1000, 64⟩, ⟨0x4000, 8192⟩, ⟨0x20004, 16⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · rw [p256W_length]; exact Region.disjoint_of_sep (by decide)
  · rw [p256W_length]; exact Region.disjoint_of_sep (by decide)
  · rw [a0, a1, a2, a3]
    refine ⟨rfl, rfl, ?_⟩
    repeat' apply And.intro
    all_goals first
      | exact Region.disjoint_of_sep (by decide)
      | exact Region.disjoint_of_sep (by simp [Region.sep] <;> omega)
      | (change 12288 + I.hashLen ≤ 2 ^ 32; omega)
      | decide

/-- The existing shared contract supplies every table and stack permission
used by deterministic P-256 signing, for either hash. -/
theorem comb_implies (I : Spec.Ecdsa.Rfc6979.Instance)
    (hI : I.ecdsa = Spec.Ecdsa.P256.inst) (hD : I.hashLen ≤ 64) :
    (rfcWide I 272 p256Comb.combConsts).Implies
      (I.signContract (X86.abi.withConsts p256Comb.combConsts) 272) where
  pre s h := by
    sig_pre [Spec.Ecdsa.Rfc6979.Instance.signContract, Spec.Ecdsa.Rfc6979.Instance.signSig,
      hI, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, p256Comb_consts,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    simp only [hI, Spec.Ecdsa.P256.inst, Spec.P256.curve] at h
    obtain ⟨lo, sp, hd, held, fit, dw, rt, st, ht, wr,
      od, og, oc, oa, dc, da, gc, ga, ca, ro, rd, rg, rc, ra,
      ko, kd, kg, kc, ka, no, nd, ng, nc⟩ := h
    change (rfcWide I 272 p256Comb.combConsts).pre s
    simp only [rfcWide, hI, Spec.Ecdsa.P256.inst, Spec.P256.curve]
    refine ⟨lo, sp, ?_, wr, od, og, oc, dc, gc, oa.symm, ca.symm, ro, rc,
      ko, kd, kg, kc, no, nd, ng, nc, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]
      simp only [p256Comb_consts, Abi.constRegions_cons, Abi.constRegions_nil]
    · refine ⟨?_, ?_⟩
      · intro c hc
        simp only [p256Comb_consts, List.mem_singleton] at hc
        subst c
        exact held
      · intro T hT
        simp only [p256Comb_consts, Abi.constRegions_cons, Abi.constRegions_nil, List.mem_singleton] at hT
        subst T
        refine ⟨by simp only [BitVec.toNat_setWidth]; omega, ?_⟩
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact dw _ (by rw [wr]; simp)
        · exact dw _ (by rw [wr]; simp)
        · exact rt
        · exact st
  post := by
    sig_implies_post [Spec.Ecdsa.Rfc6979.Instance.signContract, Spec.Ecdsa.Rfc6979.Instance.signSig,
      hI, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, p256Comb_consts, Abi.withConsts, rfcWide, rfcX86]
  pub s t _ _ h := by
    sig_pub [Spec.Ecdsa.Rfc6979.Instance.signContract, Spec.Ecdsa.Rfc6979.Instance.signSig,
      hI, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, p256Comb_consts, Abi.withConsts] at h
    obtain ⟨he, hs, hl, a0, a1, a2, a3⟩ := h
    refine ⟨he, a0, a1, a2, a3, (List.cons.inj hl).1, ?_⟩
    intro c hc
    simp only [p256Comb_consts, List.mem_singleton] at hc
    subst c
    have hs' := congrArg (BitVec.setWidth 32) hs
    simpa only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq] using hs'
  sat := ⟨_, rfcCombSat_spec I hI hD⟩

end VG.Proof.Ecdsa.Rfc6979.X86
