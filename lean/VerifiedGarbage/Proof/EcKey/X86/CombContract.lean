import VerifiedGarbage.Proof.EcKey.X86.CombFunction
import VerifiedGarbage.Spec.EcKey.P256

/-! # Shared public-key contract for the x86 fixed-base comb -/
namespace VG.Proof.EcKey.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86

abbrev pkCombSpec : Contract isa := Spec.EcKey.P256.inst.publicKeyContract (X86.abi.withConsts p256Comb.combConsts) 20

def pkCombLocal : Contract isa where
  pre := PkCombPre p256Comb
  post := PkPost p256Comb
  pub := PkCombPub

def pkCombRd (s : State) : List Region := [⟨ptr s 1, 32⟩, ⟨argAddr s 0, 12⟩] ++
  Abi.constRegions (fun n => (s.syms n).setWidth 64) p256Comb.combConsts

def pkCombWr (s : State) : List Region := [⟨ptr s 0, 65⟩, ⟨ptr s 2, 8192⟩]

theorem pkComb_pre {s : State} (h : pkCombSpec.pre s) :
    pkCombLocal.pre (s.withRegions (pkCombRd s) (pkCombWr s)) := by
  sig_pre [pkCombSpec, Spec.EcKey.P256.inst, Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig, Spec.P256.curve, Spec.EcKey.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p256Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
  obtain ⟨lo, sp, _drop, held, fit, dw, _ret, st, _take, wr,
    od, os, oa, ds, _da, sa, ro, _rd, rs, _ra, _so, sd, _ss, _sa, fo, fd, fs⟩ := h
  have hb : below (s.gpr .esp) 20 = ⟨(s.gpr .esp).setWidth 64 - 20#64, 20⟩ := by
    unfold below
    rw [VG.X86.Taint.sub_setWidth lo]
  rw [← hb] at st sd
  have h4 := VG.Proof.Weierstrass.X86.below_le_sub (sp := s.gpr .esp) (a := 4) (b := 20) (by decide) lo
  refine ⟨⟨rfl, rfl, os, od, ds, oa.symm, sa.symm, ro, rs, fo, fd, fs, sp, lo, _so, _ss⟩, ?_, ?_⟩
  · change TblsHeld p256Comb (s.withRegions (pkCombRd s) (pkCombWr s))
      (below (s.gpr .esp) 20 :: pkCombWr s)
    simp only [TblsHeld, p256Comb_consts, Abi.constRegions_cons, Abi.constRegions_nil,
      Sig.forall_mem_const_single]
    simp only [Abi.constsHeld, List.mem_singleton, forall_eq, State.withRegions_mem]
    change (∀ i < p256W.length, s.mem.readW ((s.syms "VG_P256_COMB").setWidth 64 +
      BitVec.ofNat 64 (8 * i)) 64 = p256W.getD i 0) ∧
      ((s.syms "VG_P256_COMB").setWidth 64).toNat + 8 * p256W.length ≤ 2 ^ 32 ∧
      ∀ r ∈ below (s.gpr .esp) 20 :: pkCombWr s,
        Region.Disjoint ⟨(s.syms "VG_P256_COMB").setWidth 64, 8 * p256W.length⟩ r
    refine ⟨held, ?_, ?_⟩
    · simp only [BitVec.toNat_setWidth]; omega
    · intro r hr
      simp only [pkCombWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact st
      · exact dw _ (by rw [wr]; simp [ptr])
      · exact dw _ (by rw [wr]; simp [ptr])
  · exact sd.symm.sub_right h4

theorem pkComb_regions {s : State} (h : pkCombSpec.pre s) :
    s.rd = [⟨ptr s 1, 32⟩] ++ Abi.constRegions (fun n => (s.syms n).setWidth 64) p256Comb.combConsts ∧
    s.wr = [⟨ptr s 0, 65⟩, ⟨ptr s 2, 8192⟩, ⟨argAddr s 0, 12⟩] := by
  sig_pre [pkCombSpec, Spec.EcKey.P256.inst, Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig, Spec.P256.curve, Spec.EcKey.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p256Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
  obtain ⟨_, _, hd, _, _, _, _, _, ht, hw, _⟩ := h
  refine ⟨?_, hw⟩
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]
  simp only [p256Comb_consts, Abi.constRegions_cons, Abi.constRegions_nil, ptr]

end VG.Proof.EcKey.X86
