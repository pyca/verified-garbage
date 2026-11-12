module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Verified
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.CT3

/-! # `vg_rsa_pkcs1_decrypt_precomputed` on RISC-V

`codeP`, the code of `vg_rsa_pkcs1_decrypt` calling
`vg_rsa_private_checked_precomputed` (`codeG true`), as on PPC64LE: its
precondition gives `DPre true` and `PreX` (`dPreP_of`), its public data
`Same true` (`same_ofP`), and the proofs shared with `vg_rsa_pkcs1_decrypt`
(`codeG_correct`, `codeG_rel`) the rest. A state meeting the precondition
holds a real key (`preState`, `Rsa.PreKey`).
-/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec
open VG VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt

/-! ## A state that meets the contract -/

open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

/-- The stack arguments of `preState`: `d_len`, the input at `0x3000`, `p`
at `0x4200`, `q` at `0x4300`, `dp`, `dq` and `qinv` at `0x4400`, `0x4500`
and `0x4600`, `scratch` at `0xA000`, `pre` at `0x4800`. -/
def preArgs : List Nat := [1, 0x3000, 64, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32,
  0xa000, 0x420, 0x4800, 24]

/-- The memory of `preState`: the stack arguments at `0x10000`, and the key
(`keyMem`: `n` at `0x2000`, `p`, `q` and `pre`). -/
def preMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10000 i && Nat.blt i 0x10088 then
    BitVec.ofNat 8 (preArgs.getD ((i - 0x10000) / 8) 0 / 256 ^ ((i - 0x10000) % 8))
  else bif keyIn i then keyMem a else 0

/-- `out` at `0x1000`, the message's length at `0x6800`, `n` (64 bytes) at
`0x2000`, `e` and `d` at `0x2100` and `0x2200`, the stack arguments at
`sp = 0x10000`. -/
def preState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x6800 | .a3 => 0x2000 | .a4 => 64 | .a5 => 0x2100 | .a6 => 1
    | .a7 => 0x2200 | _ => 0
  sp := 0x10000
  mem := preMem
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x2200, 1⟩, ⟨0x3000, 64⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩,
    ⟨0x4500, 32⟩, ⟨0x4600, 32⟩, ⟨0x4800, 192⟩, ⟨0x10000, 136⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x6800, 8⟩, ⟨0xA000, 8448⟩]

theorem stackArgs_seventeen (s : State) :
    List.map (stackArg s) (List.range 17) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16] := rfl

theorem pre_args : stackArg preState 0 = 1 ∧ stackArg preState 1 = 0x3000 ∧ stackArg preState 2 = 64 ∧
    stackArg preState 3 = 0x4200 ∧ stackArg preState 4 = 32 ∧ stackArg preState 5 = 0x4300 ∧
    stackArg preState 6 = 32 ∧ stackArg preState 7 = 0x4400 ∧ stackArg preState 8 = 32 ∧
    stackArg preState 9 = 0x4500 ∧ stackArg preState 10 = 32 ∧ stackArg preState 11 = 0x4600 ∧
    stackArg preState 12 = 32 ∧ stackArg preState 13 = 0xA000 ∧ stackArg preState 14 = 1056 ∧
    stackArg preState 15 = 0x4800 ∧ stackArg preState 16 = 24 := by
  decide

theorem preState_key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt preState.mem 0x2000 64)
    (Spec.Rsa.bytesAt preState.mem 0x4200 32) (Spec.Rsa.bytesAt preState.mem 0x4300 32) =
      some (Spec.Rsa.wordsAt preState.mem 0x4800 24) :=
  key_pre_of fun a ha => by
    have hs : (Nat.ble 0x10000 a.toNat && Nat.blt a.toNat 0x10088) = false := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha
      refine Bool.eq_false_iff.mpr fun h => ?_
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
      omega
    show (bif _ then _ else _) = _
    rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem satisfiablePre : ∃ s, (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pre s := by
  refine ⟨preState, ?_⟩
  have e : stackBytes = 3455 + 1 := rfl
  rw [e]
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, stackArgs_seventeen, List.append_eq, List.range,
    List.range.loop]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := pre_args
  have ha : stackArgAddr preState 0 = 0x10000 := by decide
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, ha]
  sig_and_intros
  rotate_right 4
  · exact preState_key
  all_goals first
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (unfold Spec.Rsa.lenValid; decide)

theorem dPreP_of {s : State} (h : (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pre s) :
    DPre true s ∧ PreX s := by
  have e : stackBytes = 3455 + 1 := rfl
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, stackArgs_seventeen, List.append_eq, List.range,
    List.range.loop] at h
  obtain ⟨sp16, sp1, sp2, hrd, hwr, om, on, oe, od, oi, op, oq, odp, odq, oqi, os, oP, oa, mn, me, md, mi, mp, mq,
    mdp, mdq, mqi, ms, mP, ma, ns, es, ds, is, ps, qs, dps, dqs, qis, sP, sa, ko, km, kn, ke, kd, ki, kp, kq, kdp,
    kdq, kqi, ks, kP, ka, wo, wm, wn, we, wd, wi, wp, wq, wdp, wdq, wqi, ws, wP, ⟨k1, k2⟩, h1, hi, e1, e2, d1, d2,
    p1, p2, q1, q2, h8, h12, h10, hs, hpl, hyp, mal, al, alP⟩ := h
  exact ⟨⟨sp16, sp1, by simp only [↓reduceIte]; omega, hrd, hwr, om, on, oe, od, oi, op, oq, odp, odq, oqi, os,
    oa, mn, me, md, mi, mp, mq, mdp, mdq, mqi, ms, ma, ns, es, ds, is, ps, qs, dps, dqs, qis, sa, ko, km, kn, ke,
    kd, ki, kp, kq, kdp, kdq, kqi, ks, ka, wo, wm, wn, we, wd, wi, wp, wq, wdp, wdq, wqi, ws, k1, k2, h1, hi, e1,
    e2, d1, d2, p1, p2, q1, q2, h8, h12, h10, hs, mal, al⟩, ⟨oP, mP, sP, kP, wP, hpl, alP, fun _ => hyp⟩⟩

theorem same_ofP {s₁ s₂ : State} (h : (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pub s₁ s₂) :
    Same true s₁ s₂ := by
  have e : stackBytes = 3455 + 1 := rfl
  rw [e] at h
  sig_pub [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, stackArgs_seventeen, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
    a14, a15, a16⟩ := h
  obtain ⟨hne, hlk⟩ := List.append_inj hl (by
    simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', h7, h9])
  rw [List.map_append, List.map_append] at hne
  obtain ⟨hn, he⟩ := List.append_inj hne (by simp only [List.length_map, Proof.Rsa.bytesAt_length', h7])
  refine ⟨fun r hr => ?_, fun i hi => ?_, hsp,
    ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hn),
    ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 he), fun _ => hlk⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3, h4, h5, h6, h7, h8, h9, h10]
  · simp only [nA, ↓reduceIte] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
      i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16]

theorem codeP_correct (s : State) (hpre : (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pre s) :
    ∃ tr t, Exec isa codeP s tr t ∧ abiPreserved s t ∧ fnPost s t := by
  obtain ⟨h, X⟩ := dPreP_of hpre
  exact codeG_correct s h fun _ => X

theorem codeP_ct : ConstantTime isa (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pre
    (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pub codeP :=
  RelCT.constantTime ((codeG_rel (pc := true)).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ =>
    ⟨⟨s₁, s₂, (dPreP_of h₁).1, (dPreP_of h₂).1, same_ofP hp, fun _ => (dPreP_of h₁).2, fun _ => (dPreP_of h₂).2⟩,
      rfl, rfl⟩)
    fun _ _ h => h)

/-- The precomputed contract, its postcondition on the registers and the stack. -/
def fnContractP : Contract isa where
  pre := (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pre
  post := fnPost
  pub := (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pub

theorem decP_implies : fnContractP.Implies (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes) where
  pre := fun _ h => h
  post := by
    sig_implies_post [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
      Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, fnContractP, fnPost, stackArgs_seventeen, List.append_eq,
      dBytes, cOf]
  pub := fun _ _ _ _ h => h
  sat := satisfiablePre

/-- `vg_rsa_pkcs1_decrypt_precomputed`, calling `vg_rsa_private_checked_precomputed`. -/
theorem codeP_verified :
    Verified target codeP (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes) :=
  Verified.of_correct codeP_correct codeP_ct decP_implies

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec
