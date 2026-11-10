module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecVerified
public import VerifiedGarbage.Proof.Rsa.PreKey
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecCTBase
import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecCT4
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# `vg_rsa_pkcs1_decrypt_precomputed` on PPC64LE: `Verified`

`codeP`, the code of `vg_rsa_pkcs1_decrypt` calling
`vg_rsa_private_checked_precomputed` (`codeG true`), against
`Spec.RsaPkcs1Enc.decryptPrecomputedContract`: its precondition gives
`DPre true` and `PreX` (`dPreP_of`), its public data `dataOf true`
(`pub_dataP`), and the proofs shared with `vg_rsa_pkcs1_decrypt`
(`codeG_correct`, `body_ct`) the rest. A state meeting the precondition
holds a real key (`satP`, `Rsa.PreKey`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Rsa.PreKey

theorem stackArgs_seventeen (s : State) :
    List.map (stackArg s) (List.range 17) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16] := rfl

/-- The precondition, `DPre true` and `PreX`. -/
theorem dPreP_of {s : State} (h : (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pre s) :
    DPre true s ∧ PreX s := by
  have e : stackBytes = 3647 + 1 := rfl
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, stackArgs_seventeen, List.append_eq] at h
  simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
    Bool.true_or, Bool.false_or, List.cons_append, List.nil_append, Sig.conj, List.append_nil] at h
  obtain ⟨sp1, sp2, hrd, hwr, om, on, ⟨oe, od, oi, op, oq, odp, odq, oqi, os, oP, oa, mn, me, md, mi, mp, mq, mdp,
    mdq, mqi, ms, mP, ma, ns, es, ds, is, ps, qs, dps, dqs, qis, sP, sa⟩,
    ko, km, kn, ke, kd, ki, kp, kq, kdp, kdq, kqi, ks, kP, ka,
    wo, wm, wn, we, wd, wi, wp, wq, wdp, wdq, wqi, ws, wP, ⟨k1, k2⟩, h4, hi, e1, e2, d1, d2, p1, p2, q1, q2, h8, h12,
    h10, hs, hpl, hyp⟩ := h
  exact ⟨⟨sp1, by simp only [↓reduceIte]; omega, hrd, hwr, om, on, oe, od, oi, op, oq, odp, odq, oqi, os, oa, mn,
    me, md, mi, mp, mq, mdp, mdq, mqi, ms, ma, ns, es, ds, is, ps, qs, dps, dqs, qis, sa, ko, km, kn, ke, kd, ki, kp,
    kq, kdp, kdq, kqi, ks, ka, wo, wm, wn, we, wd, wi, wp, wq, wdp, wdq, wqi, ws, k1, k2, h4, hi, e1, e2, d1, d2, p1,
    p2, q1, q2, h8, h12, h10, hs⟩, ⟨oP, mP, sP, kP, wP, hpl, fun _ => hyp⟩⟩

theorem pub_dataP {s₁ s₂ : State} (h : (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pub s₁ s₂) :
    dataOf true s₁ = dataOf true s₂ := by
  have e : stackBytes = 3647 + 1 := rfl
  rw [e] at h
  sig_pub [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, stackArgs_seventeen, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
    a14, a15, a16⟩ := h
  obtain ⟨hne, hlk⟩ := List.append_inj hl (by
    simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', h7, h9])
  unfold dataOf
  rw [hne, hlk]
  simp only [argRegs, nArgs, ↓reduceIte, List.map_cons, List.map_nil, stackArgs_seventeen, h3, h4, h5, h6, h7, h8,
    h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, hsp]

/-- The precomputed contract, its postcondition on the registers and the stack. -/
def fnContractP : Contract isa where
  pre := (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pre
  post := fnPost
  pub := (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pub

theorem codeP_correct (s : State) (hpre : (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pre s) :
    ∃ tr t, Exec isa codeP s tr t ∧ abiPreserved s t ∧ fnPost s t :=
  let ⟨h, X⟩ := dPreP_of hpre
  codeG_correct s h fun _ => X

theorem codeP_ct : ConstantTime isa (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pre
    (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pub codeP :=
  RelCT.constantTime (RelCT.alloc (fun _ _ ⟨_, _, hp⟩ => (same_of (pub_dataP hp)).sp)
    ((RelCT.exists_ fun e : Env true => body_ct (e := e)).mono
      (fun _ _ ⟨s, t, ⟨hs, ht, hp⟩, ea, eb⟩ =>
        ⟨⟨s, t, (dPreP_of hs).1, (dPreP_of ht).1, fun _ => (dPreP_of hs).2, fun _ => (dPreP_of ht).2,
          same_of (pub_dataP hp)⟩, ea, eb⟩)
      fun _ _ h => h))

/-! ## A state meeting the precondition

`n`, `p` and `q` and the precomputed values at `keyMem`'s addresses (`n` of
64 octets at `0x2000`, `p` and `q` of 32 at `0x4200` and `0x4300`, `pre` of
24 words at `0x4800`); `out` at `0x1000`, `msg_len` at `0x1100`, `e` and `d`
(one octet each) at `0x3000` and `0x3100`, the ciphertext at `0x4000`, `dp`,
`dq` and `qinv` at `0x4400`–`0x4600`, and the stack arguments at `0x10060`. -/

/-- The stack arguments that are not zero, by their bytes. -/
def argMem (i : Nat) : Byte :=
  if i = 0x10060 then 1 else if i = 0x10069 then 0x40 else if i = 0x10070 then 0x40
  else if i = 0x10079 then 0x42 else if i = 0x10080 then 0x20 else if i = 0x10089 then 0x43
  else if i = 0x10090 then 0x20 else if i = 0x10099 then 0x44 else if i = 0x100A0 then 0x20
  else if i = 0x100A9 then 0x45 else if i = 0x100B0 then 0x20 else if i = 0x100B9 then 0x46
  else if i = 0x100C0 then 0x20 else if i = 0x100CA then 0x02 else if i = 0x100D0 then 0x20
  else if i = 0x100D1 then 0x04 else if i = 0x100D9 then 0x48 else if i = 0x100E0 then 24 else 0

def satP : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x1100 | .r6 => 0x2000 | .r7 => 64 | .r8 => 0x3000
    | .r9 => 1 | .r10 => 0x3100 | _ => 0
  lr := 0
  sp := 0x10000
  mem a := bif keyIn a.toNat then keyMem a else argMem a.toNat
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x4000, 64⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩,
    ⟨0x4500, 32⟩, ⟨0x4600, 32⟩, ⟨0x4800, 192⟩, ⟨0x10060, 136⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 8⟩, ⟨0x20000, 8448⟩]

/-- The stack arguments of `satP`. -/
def satArgs (j : Nat) : BitVec 64 :=
  if j = 0 then 1 else if j = 1 then 0x4000 else if j = 2 then 64 else if j = 3 then 0x4200
  else if j = 5 then 0x4300 else if j = 7 then 0x4400 else if j = 9 then 0x4500 else if j = 11 then 0x4600
  else if j = 13 then 0x20000 else if j = 14 then 1056 else if j = 15 then 0x4800 else if j = 16 then 24
  else if j = 4 ∨ j = 6 ∨ j = 8 ∨ j = 10 ∨ j = 12 then 32 else 0

theorem satP_args : ∀ j < 17, stackArg satP j = satArgs j := by decide

theorem satP_key {a : Addr} (h : keyIn a.toNat = true) : satP.mem a = keyMem a := by
  show (bif keyIn a.toNat then keyMem a else argMem a.toNat) = keyMem a
  rw [h]
  exact Bool.cond_true

/-- The precondition, from the facts of a state. -/
theorem pre_of_facts {s : State} (hg : s.gpr = satP.gpr) (hsp : s.sp = 0x10000)
    (ha : ∀ j < 17, stackArg s j = satArgs j) (hrd : s.rd = satP.rd) (hwr : s.wr = satP.wr)
    (hk : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem 0x2000 64) (Spec.Rsa.bytesAt s.mem 0x4200 32)
      (Spec.Rsa.bytesAt s.mem 0x4300 32) = some (Spec.Rsa.wordsAt s.mem 0x4800 24)) :
    (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pre s := by
  have e : stackBytes = 3647 + 1 := rfl
  rw [e]
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, stackArgs_seventeen, List.append_eq]
  simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
    Bool.true_or, Bool.false_or, List.cons_append, List.nil_append, Sig.conj, List.append_nil]
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (32 + 8 * (8 + j)) := fun j => by
    simp only [stackArgAddr, hsp]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide),
    ha 16 (by decide), hg, hsp, hrd, hwr, hA, satArgs, satP]
  simp only [Nat.reduceEqDiff, ↓reduceIte, or_self, or_false, false_or]
  sig_and_intros
  all_goals first
    | exact hk
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (simp only [Spec.Rsa.lenValid]; decide)
    | skip

theorem satP_pre : (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pre satP :=
  pre_of_facts rfl rfl satP_args rfl rfl (key_pre_of fun _ ha => satP_key ha)

theorem dec_impliesP : fnContractP.Implies (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes) where
  pre := fun _ h => h
  post := by
    sig_implies_post [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
      Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, fnContractP, fnPost, stackArgs_seventeen, List.append_eq, dOf, cOf]
  pub := fun _ _ _ _ h => h
  sat := ⟨satP, satP_pre⟩

/-- `vg_rsa_pkcs1_decrypt_precomputed`. -/
theorem codeP_verified :
    Verified target codeP (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes) :=
  Verified.of_correct codeP_correct codeP_ct dec_impliesP

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
