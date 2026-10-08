import VerifiedGarbage.Proof.Ecdsa.X86.CombFacts

/-! # The shared x86 signing contract with a 20-byte stack: the calls', which holds the
four-byte static-address frame -/
namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86

abbrev combSignSpec : Contract isa := Spec.Ecdsa.P256.inst.signContract (X86.abi.withConsts p256Comb.combConsts) 20

def combSignLocal : Contract isa where
  pre := CombSignPre p256Comb
  post := SignPost p256Comb
  pub := CombSignPub

def combSignRd (s : State) : List Region := signRd s ++
  Abi.constRegions (fun n => (s.syms n).setWidth 64) p256Comb.combConsts

def combSignWr (s : State) : List Region := signWr s

theorem combSign_pre {s : State} (h : combSignSpec.pre s) :
    combSignLocal.pre (s.withRegions (combSignRd s) (combSignWr s)) := by
  sig_pre [combSignSpec, Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.signContract,
    Spec.Ecdsa.Instance.signSig, Spec.P256.curve, Spec.Ecdsa.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p256Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
  obtain ⟨lo, sp, hdrop, held, fit, dw, _ret, st, _take, wr,
    od, oh, ok, os, oa, ds, _da, hs, _ha, ks, _ka, sa,
    ro, _rd, _rh, _rk, rs, _ra, _so, sd, sh, sk, _ss, _sa,
    fo, fd, fh, fk, fs⟩ := h
  have hb : below (s.gpr .esp) 20 = ⟨(s.gpr .esp).setWidth 64 - 20#64, 20⟩ := by
    unfold below
    rw [VG.X86.Taint.sub_setWidth lo]
  rw [← hb] at st sd sh sk
  have h4 := VG.Proof.Weierstrass.X86.below_le_sub (sp := s.gpr .esp) (a := 4) (b := 20) (by decide) lo
  refine ⟨⟨rfl, rfl, os, od, oh, ok, ds, hs, ks, oa.symm, sa.symm,
    ro, rs, fo, fd, fh, fk, fs, sp, lo, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact _so
  · exact _ss
  · change TblsHeld p256Comb (s.withRegions (combSignRd s) (combSignWr s))
      (below (s.gpr .esp) 20 :: combSignWr s)
    simp only [TblsHeld, p256Comb_consts, Abi.constRegions_cons, Abi.constRegions_nil,
      Sig.forall_mem_const_single]
    simp only [Abi.constsHeld, List.mem_singleton, forall_eq, State.withRegions_mem]
    change (∀ i < p256W.length, s.mem.readW ((s.syms "VG_P256_COMB").setWidth 64 +
      BitVec.ofNat 64 (8 * i)) 64 = p256W.getD i 0) ∧
      ((s.syms "VG_P256_COMB").setWidth 64).toNat + 8 * p256W.length ≤ 2 ^ 32 ∧
      ∀ r ∈ below (s.gpr .esp) 20 :: combSignWr s,
        Region.Disjoint ⟨(s.syms "VG_P256_COMB").setWidth 64, 8 * p256W.length⟩ r
    refine ⟨held, ?_, ?_⟩
    · simp only [BitVec.toNat_setWidth]; omega
    · intro r hr
      simp only [combSignWr, signWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact st
      · exact dw _ (by rw [wr]; simp)
      · exact dw _ (by rw [wr]; simp)
  · exact sd.symm.sub_right h4
  · exact sh.symm.sub_right h4
  · exact sk.symm.sub_right h4

end VG.Proof.Ecdsa.X86
