import VerifiedGarbage.Proof.TripleDes.X86_64.EcbCall.Lit
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Verified
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Verified
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Verified
import VerifiedGarbage.Proof.TripleDes.X86_64.SpSafe
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified

/-!
# Triple DES ECB on x86-64, calling the core, verified

Each ECB function's code around the call of the core (`EcbCall.sse`, `avx2`,
`avx512`) is, with the core's code inlined, the code the bitsliced proofs
verify (`inline_eq`): correct by those proofs, constant time by taint
tracking, which follows the call (the summaries of the SSE2 code apply to its
body), and verified against the contract with the working space as an
argument and 8 bytes of stack, for the call's return address, which no
buffer overlaps (`Verified.of_inline_ct`).
-/

namespace VG.Proof.TripleDes.X86_64.EcbCall

open VG VG.X86_64 VG.Impl.TripleDes.X86_64.EcbCall
open VG.Proof.TripleDes.X86_64.Bitsliced (contract ecbTaint ecbTaint_agree satState publicRegs_five)

/-! ## Constant time -/

taint_summary sseEncSum : taintS ecbTaint sseEncrypt using BitslicedSse.encSum
taint_summary sseDecSum : taintS ecbTaint sseDecrypt using BitslicedSse.decSum
taint_summary avx2EncSum : taintS ecbTaint avx2Encrypt using BitslicedSse.encSum
taint_summary avx2DecSum : taintS ecbTaint avx2Decrypt using BitslicedSse.decSum
taint_summary avx512EncSum : taintS ecbTaint avx512Encrypt using avx2EncSum
taint_summary avx512DecSum : taintS ecbTaint avx512Decrypt using avx2DecSum

theorem sse_ct (d : Spec.TripleDes.Direction) :
    ConstantTime isa (contract d).pre (contract d).pub (sse d) := by
  cases d
  · exact let ⟨_, h⟩ := VG.Taint.exists_check_of_sumOk sseEncSum (by decide +kernel)
      VG.Taint.constantTime (A := taintS) ecbTaint (ecbTaint_agree _) h
  · exact let ⟨_, h⟩ := VG.Taint.exists_check_of_sumOk sseDecSum (by decide +kernel)
      VG.Taint.constantTime (A := taintS) ecbTaint (ecbTaint_agree _) h

theorem avx2_ct (d : Spec.TripleDes.Direction) :
    ConstantTime isa (contract d).pre (contract d).pub (avx2 d) := by
  cases d
  · exact let ⟨_, h⟩ := VG.Taint.exists_check_of_sumOk avx2EncSum (by decide +kernel)
      VG.Taint.constantTime (A := taintS) ecbTaint (ecbTaint_agree _) h
  · exact let ⟨_, h⟩ := VG.Taint.exists_check_of_sumOk avx2DecSum (by decide +kernel)
      VG.Taint.constantTime (A := taintS) ecbTaint (ecbTaint_agree _) h

theorem avx512_ct (d : Spec.TripleDes.Direction) :
    ConstantTime isa (contract d).pre (contract d).pub (avx512 d) := by
  cases d
  · exact let ⟨_, h⟩ := VG.Taint.exists_check_of_sumOk avx512EncSum (by decide +kernel)
      VG.Taint.constantTime (A := taintS) ecbTaint (ecbTaint_agree _) h
  · exact let ⟨_, h⟩ := VG.Taint.exists_check_of_sumOk avx512DecSum (by decide +kernel)
      VG.Taint.constantTime (A := taintS) ecbTaint (ecbTaint_agree _) h

/-! ## Correctness, with the core inlined -/

theorem sse_correct (d : Spec.TripleDes.Direction) (s : State) (hs : (contract d).pre s) :
    ∃ t s', Exec isa (sse d).inline s t s' ∧ abiPreserved s s' ∧ (contract d).post s s' := by
  cases d
  · exact BitslicedSse.encrypt_correct s hs
  · exact BitslicedSse.decrypt_correct s hs

theorem avx2_correct (d : Spec.TripleDes.Direction) (s : State) (hs : (contract d).pre s) :
    ∃ t s', Exec isa (avx2 d).inline s t s' ∧ abiPreserved s s' ∧ (contract d).post s s' := by
  cases d
  · exact BitslicedAvx2.encrypt_correct s hs
  · exact BitslicedAvx2.decrypt_correct s hs

theorem avx512_correct (d : Spec.TripleDes.Direction) (s : State) (hs : (contract d).pre s) :
    ∃ t s', Exec isa (avx512 d).inline s t s' ∧ abiPreserved s s' ∧ (contract d).post s s' := by
  cases d
  · exact BitslicedAvx512.encrypt_correct s hs
  · exact BitslicedAvx512.decrypt_correct s hs

/-! ## The contract with 8 bytes of stack -/

theorem implies (d : Spec.TripleDes.Direction) :
    (contract d).Implies (Proof.TripleDes.ecbScratchContract abi d) := by
  sig_implies [Proof.TripleDes.ecbScratchContract, Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost,
    abi, argRegs, contract, publicRegs_five] [satState] using satState

theorem implies8 (d : Spec.TripleDes.Direction) :
    (contract d).Implies (Proof.TripleDes.ecbScratchContract abi d 8) :=
  (implies d).stack8_abi (by
    sig_implies_sat [Proof.TripleDes.ecbScratchContract, Proof.TripleDes.ecbScratchSig, abi, argRegs,
      satState] [satState] using satState)

/-- The data are apart from the call's return address. -/
theorem patch (d : Spec.TripleDes.Direction) (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Proof.TripleDes.ecbScratchContract abi d 8).pre s) (hp : (contract d).post s b) :
    (contract d).post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -, -, -, -, -, fit⟩ := (implies8 d).pre s hs
  have hb := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rsi) (n := 8 * (s.gpr .rdx).toNat)
    (by rw [hwr]; simp) (by omega)
  refine Eq.trans ?_ hp
  simp only [Spec.TripleDes.blocksAt, Spec.TripleDes.blockAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  refine congrArg Vector.ofFn (funext fun j => ?_)
  rw [Offset.add_add]
  simp only [State.patch, overlay, hb (8 * i + j.val) (by have := j.isLt; omega), ite_false]

theorem verified {c : Prog isa} {d : Spec.TripleDes.Direction} (hc : c.InlineOk = true)
    (hcor : ∀ s, (contract d).pre s →
      ∃ t s', Exec isa c.inline s t s' ∧ abiPreserved s s' ∧ (contract d).post s s')
    (hct : ConstantTime isa (contract d).pre (contract d).pub c) :
    Verified target c (Proof.TripleDes.ecbScratchContract abi d 8) :=
  Verified.of_inline_ct hc hcor hct (implies8 d) (fun _ h => Sig.clear_of_pre h) (patch d)

theorem sse_verified (d : Spec.TripleDes.Direction) :
    Verified target (sse d) (Proof.TripleDes.ecbScratchContract abi d 8) :=
  verified (by cases d <;> lit_decide) (sse_correct d) (sse_ct d)

theorem avx2_verified (d : Spec.TripleDes.Direction) :
    Verified target (avx2 d) (Proof.TripleDes.ecbScratchContract abi d 8) :=
  verified (by cases d <;> lit_decide) (avx2_correct d) (avx2_ct d)

theorem avx512_verified (d : Spec.TripleDes.Direction) :
    Verified target (avx512 d) (Proof.TripleDes.ecbScratchContract abi d 8) :=
  verified (by cases d <;> lit_decide) (avx512_correct d) (avx512_ct d)

/-! ## The frame's side conditions -/

theorem sse_sp (d : Spec.TripleDes.Direction) : (sse d).allInstrs (fun i => !isa.writesSp i) = true := by
  cases d <;> exact sse_ecb_sp _

theorem avx2_sp (d : Spec.TripleDes.Direction) : (avx2 d).allInstrs (fun i => !isa.writesSp i) = true := by
  cases d <;> exact avx2_ecb_sp _

theorem avx512_sp (d : Spec.TripleDes.Direction) :
    (avx512 d).allInstrs (fun i => !isa.writesSp i) = true := by
  cases d <;> exact avx512_ecb_sp _

theorem sse_depth (d : Spec.TripleDes.Direction) : (sse d).x86_64Depth ≤ 8 := by
  cases d <;> lit_decide

theorem avx2_depth (d : Spec.TripleDes.Direction) : (avx2 d).x86_64Depth ≤ 8 := by
  cases d <;> lit_decide

theorem avx512_depth (d : Spec.TripleDes.Direction) : (avx512 d).x86_64Depth ≤ 8 := by
  cases d <;> lit_decide

end VG.Proof.TripleDes.X86_64.EcbCall
