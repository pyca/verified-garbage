module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Sign.Verified
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT

/-! # `vg_rsa_pkcs1_sign_precomputed` on RISC-V

`codeP`, the code of `vg_rsa_pkcs1_sign` calling
`vg_rsa_private_checked_precomputed` (`codeG true`), as on PPC64LE
(`Proof/RsaPkcs1Sig/PPC64LE/SignP.lean`): its precondition gives `SPre true`
and `PreX` (`sPreP_of`), its public data `PubS true` (`pubS_ofP`), and the
proofs shared with `vg_rsa_pkcs1_sign` (`codeG_correct`, `codeG_rel`) the
rest. A state meeting the precondition holds a real key (`preState`,
`Rsa.PreKey`).
-/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.RISCV64.Sign
open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64.Sign

/-! ## A state that meets the contract -/

open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

/-- The stack arguments of `preState`: `digest_len`, `p` at `0x4200`, `q` at
`0x4300`, `dp`, `dq` and `qinv` at `0x4400`, `0x4500` and `0x4600`,
`scratch` at `0xA000`, `pre` at `0x4800`. -/
def preArgs : List Nat := [64, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0xa000, 0x420,
  0x4800, 24]

/-- The memory of `preState`: the stack arguments at `0x10000`, and the key
(`keyMem`: `n` at `0x2000`, `p`, `q` and `pre`). -/
def preMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10000 i && Nat.blt i 0x10078 then
    BitVec.ofNat 8 (preArgs.getD ((i - 0x10000) / 8) 0 / 256 ^ ((i - 0x10000) % 8))
  else bif keyIn i then keyMem a else 0

/-- `out` at `0x1000`, `n` (64 bytes) at `0x2000`, `e` at `0x3000`, the
digest at `0x4000`, the stack arguments at `sp = 0x10000`. -/
def preState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x2000 | .a3 => 64 | .a4 => 0x3000 | .a5 => 1 | .a7 => 0x4000
    | _ => 0
  sp := 0x10000
  mem := preMem
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 64⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩,
    ⟨0x4500, 32⟩, ⟨0x4600, 32⟩, ⟨0x4800, 192⟩, ⟨0x10000, 120⟩]
  wr := [⟨0x1000, 64⟩, ⟨0xA000, 8448⟩]

theorem stackArgs_fifteen (s : State) :
    List.map (stackArg s) (List.range 15) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14] := rfl

theorem pre_args : stackArg preState 0 = 64 ∧ stackArg preState 1 = 0x4200 ∧ stackArg preState 2 = 32 ∧
    stackArg preState 3 = 0x4300 ∧ stackArg preState 4 = 32 ∧ stackArg preState 5 = 0x4400 ∧
    stackArg preState 6 = 32 ∧ stackArg preState 7 = 0x4500 ∧ stackArg preState 8 = 32 ∧
    stackArg preState 9 = 0x4600 ∧ stackArg preState 10 = 32 ∧ stackArg preState 11 = 0xA000 ∧
    stackArg preState 12 = 1056 ∧ stackArg preState 13 = 0x4800 ∧ stackArg preState 14 = 24 := by
  decide

theorem preState_key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt preState.mem 0x2000 64)
    (Spec.Rsa.bytesAt preState.mem 0x4200 32) (Spec.Rsa.bytesAt preState.mem 0x4300 32) =
      some (Spec.Rsa.wordsAt preState.mem 0x4800 24) :=
  key_pre_of fun a ha => by
    have hs : (Nat.ble 0x10000 a.toNat && Nat.blt a.toNat 0x10078) = false := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha
      refine Bool.eq_false_iff.mpr fun h => ?_
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
      omega
    show (bif _ then _ else _) = _
    rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem satisfiablePre : ∃ s, (Spec.RsaPkcs1Sig.signPrecomputedContract abi stackBytes).pre s := by
  refine ⟨preState, ?_⟩
  have e : stackBytes = 4431 + 1 := rfl
  rw [e]
  sig_pre [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
    Spec.RsaPkcs1Sig.signSig, abi, argRegs, stackArgs_fifteen, List.append_eq, List.range, List.range.loop]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := pre_args
  have ha : stackArgAddr preState 0 = 0x10000 := by decide
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, ha]
  sig_and_intros
  rotate_right 3
  · exact preState_key
  all_goals first
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (unfold Spec.Rsa.lenValid; decide)

/-- The precondition, `SPre true` and `PreX`. -/
theorem sPreP_of {s : State} (h : (Spec.RsaPkcs1Sig.signPrecomputedContract abi stackBytes).pre s) :
    SPre true s ∧ PreX s := by
  have e : stackBytes = 4431 + 1 := rfl
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
    Spec.RsaPkcs1Sig.signSig, abi, argRegs, stackArgs_fifteen, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp16, sp1, sp2, hrd, hwr, on, oe, od, op, oq, odp, odq, oqi, os, oP, oa, ns, es, ds, ps, qs, dps, dqs, qis,
    sP, sa, ko, kn, ke, kd, kp, kq, kdp, kdq, kqi, ks, kP, ka, wo, wn, we, wd, wp, wq, wdp, wdq, wqi, ws, wP,
    ⟨k1, k2⟩, h1, e1, e2, p1, p2, q1, q2, h6, h10, h8, hs, hpl, hyp, al, alP⟩ := h
  exact ⟨⟨sp16, sp1, by simp only [↓reduceIte]; omega, hrd, hwr, on, oe, od, op, oq, odp, odq, oqi, os, oa, ns, es,
    ds, ps, qs, dps, dqs, qis, sa, ko, kn, ke, kd, kp, kq, kdp, kdq, kqi, ks, ka, wo, wn, we, wd, wp, wq, wdp, wdq,
    wqi, ws, k1, k2, h1, e1, e2, p1, p2, q1, q2, h6, h10, h8, hs, al⟩, ⟨oP, sP, kP, wP, hpl, alP, fun _ => hyp⟩⟩

theorem pubS_ofP {s₁ s₂ : State} (h : (Spec.RsaPkcs1Sig.signPrecomputedContract abi stackBytes).pub s₁ s₂) :
    PubS true s₁ s₂ := by
  have e : stackBytes = 4431 + 1 := rfl
  rw [e] at h
  sig_pub [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
    Spec.RsaPkcs1Sig.signSig, abi, argRegs, stackArgs_fifteen, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
    a14⟩ := h
  obtain ⟨hne, hlk⟩ := List.append_inj hl (by
    simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', h6, h8])
  rw [List.map_append, List.map_append] at hne
  obtain ⟨hn, he⟩ := List.append_inj hne (by simp only [List.length_map, Proof.Rsa.bytesAt_length', h6])
  refine ⟨hsp.symm, fun r hr => ?_, h9.symm, fun i hi => ?_,
    ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hn).symm,
    ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 he).symm, fun _ => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h10.symm]
  · simp only [nA, ↓reduceIte] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
      i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm, a8.symm, a9.symm, a10.symm,
      a11.symm, a12.symm, a13.symm, a14.symm]
  · exact hlk.symm

theorem codeP_correct (s : State) (hpre : (Spec.RsaPkcs1Sig.signPrecomputedContract abi stackBytes).pre s) :
    ∃ tr t, Exec isa codeP s tr t ∧ abiPreserved s t ∧ fnPost s t := by
  obtain ⟨h, X⟩ := sPreP_of hpre
  exact codeG_correct s h fun _ => X

theorem codeP_ct : ConstantTime isa (Spec.RsaPkcs1Sig.signPrecomputedContract abi stackBytes).pre
    (Spec.RsaPkcs1Sig.signPrecomputedContract abi stackBytes).pub codeP :=
  RelCT.constantTime ((codeG_rel (pc := true)).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨(sPreP_of h₁).1, PubS.refl _, fun _ => (sPreP_of h₁).2⟩,
      ⟨(sPreP_of h₂).1, pubS_ofP hp, fun _ => (sPreP_of h₂).2⟩⟩)
    fun _ _ h => h)

/-- `vg_rsa_pkcs1_sign_precomputed`. -/
theorem codeP_verified :
    Verified target codeP (Spec.RsaPkcs1Sig.signPrecomputedContract abi stackBytes) :=
  ⟨codeP_correct, codeP_ct, satisfiablePre⟩

end VG.Proof.RsaPkcs1Sig.RISCV64.Sign
