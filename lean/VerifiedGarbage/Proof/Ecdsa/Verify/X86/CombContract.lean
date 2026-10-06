import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombFunction
import VerifiedGarbage.Spec.Ecdsa.Verify.P256

/-! # Shared verification contract for the x86 fixed-base comb -/
namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86

abbrev vCombSpec : Contract isa := Spec.Ecdsa.P256.inst.verifyContract (X86.abi.withConsts p256Comb.combConsts) 4

def vCombLocal : Contract isa where
  pre := VCombPre p256Comb
  post := VPost p256Comb
  pub := VCombPub

def vCombRd (s : State) : List Region := [⟨ptr s 0, 65⟩, ⟨ptr s 1, 32⟩, ⟨ptr s 2, 64⟩, ⟨argAddr s 0, 16⟩] ++
  Abi.constRegions (fun n => (s.syms n).setWidth 64) p256Comb.combConsts

def vCombWr (s : State) : List Region := [⟨ptr s 3, 8192⟩]

theorem vComb_pre {s : State} (h : vCombSpec.pre s) :
    vCombLocal.pre (s.withRegions (vCombRd s) (vCombWr s)) := by
  sig_pre [vCombSpec, Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract,
    Spec.Ecdsa.Instance.verifySig, Spec.P256.curve, Spec.Ecdsa.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p256Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
  obtain ⟨lo, sp, _drop, held, fit, dw, _ret, st, _take, wr,
    ps, _pa, ds, _da, ss, _sia, sa, _rp, _rd, _rsi, rs, _ra,
    spk, sdg, ssi, _ss, _sa, fp, fd, fsi, fs⟩ := h
  have hb : below (s.gpr .esp) 4 = ⟨(s.gpr .esp).setWidth 64 - 4, 4⟩ := by
    unfold below
    rw [VG.X86.Taint.sub_setWidth lo]; rfl
  refine ⟨⟨rfl, rfl, ps, ds, ss, sa.symm, rs, fp, fd, fsi, fs, sp⟩, ?_, lo, ?_, ?_, ?_⟩
  · change TblsHeld p256Comb (s.withRegions (vCombRd s) (vCombWr s))
      (below (s.gpr .esp) 4 :: vCombWr s)
    simp only [TblsHeld, p256Comb_consts, Abi.constRegions, Abi.constsHeld,
      List.map_cons, List.map_nil, List.mem_singleton, forall_eq, State.withRegions_mem]
    change (∀ i < p256W.length, s.mem.readW ((s.syms "VG_P256_COMB").setWidth 64 +
      BitVec.ofNat 64 (8 * i)) 64 = p256W.getD i 0) ∧
      ((s.syms "VG_P256_COMB").setWidth 64).toNat + 8 * p256W.length ≤ 2 ^ 32 ∧
      ∀ r ∈ below (s.gpr .esp) 4 :: vCombWr s,
        Region.Disjoint ⟨(s.syms "VG_P256_COMB").setWidth 64, 8 * p256W.length⟩ r
    refine ⟨held, ?_, ?_⟩
    · simp only [BitVec.toNat_setWidth]; omega
    · intro r hr
      simp only [vCombWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hb]; exact st
      · exact dw _ (by rw [wr]; simp [ptr])
  · change Region.Disjoint ⟨ptr s 0, 1 + 2 * p256Comb.C.len⟩ (below (s.gpr .esp) 4)
    rw [hb]; exact spk.symm
  · change Region.Disjoint ⟨ptr s 1, p256Comb.C.len⟩ (below (s.gpr .esp) 4)
    rw [hb]; exact sdg.symm
  · change Region.Disjoint ⟨ptr s 2, 2 * p256Comb.C.len⟩ (below (s.gpr .esp) 4)
    rw [hb]; exact ssi.symm

theorem vComb_regions {s : State} (h : vCombSpec.pre s) :
    s.rd = [⟨ptr s 0, 65⟩, ⟨ptr s 1, 32⟩, ⟨ptr s 2, 64⟩] ++ Abi.constRegions (fun n => (s.syms n).setWidth 64) p256Comb.combConsts ∧
    s.wr = [⟨ptr s 3, 8192⟩, ⟨argAddr s 0, 16⟩] := by
  sig_pre [vCombSpec, Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract,
    Spec.Ecdsa.Instance.verifySig, Spec.P256.curve, Spec.Ecdsa.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p256Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
  obtain ⟨_, _, hd, _, _, _, _, _, ht, hw, _⟩ := h
  refine ⟨?_, hw⟩
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]
  simp only [p256Comb_consts, Abi.constRegions, List.map_cons, List.map_nil, ptr]

end VG.Proof.Ecdsa.Verify.X86
