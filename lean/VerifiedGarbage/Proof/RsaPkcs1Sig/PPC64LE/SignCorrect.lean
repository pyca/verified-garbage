module

import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Sign
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCorrect
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivVerified
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPCT
import VerifiedGarbage.Proof.Framework.Covers

/-! ### `RsaPkcs1Sig.PPC64LE.SignCall`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Sig.PPC64LE.SignArgs`, which only this module used -/

section

/-! ### `RsaPkcs1Sig.PPC64LE.SignEnc`, which only this module used -/

section

/-! ### `RsaPkcs1Sig.PPC64LE.SignSetup`, which only this module used -/

section

/-! ### `RsaPkcs1Sig.PPC64LE.SignFrame`, which only this module used -/

section

/-! ### `RsaPkcs1Sig.PPC64LE.SignPre`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_sign` on PPC64LE: the precondition

`SPre pc s`: the shared contract's precondition (`signContract`, or with
`pc` `signPrecomputedContract`, with the stack of the frame and of
`vg_rsa_private_checked`'s, `stackBytes`), by name (`sPre_of`); with `pc`,
what it says of `pre` (`PreX`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

open VG VG.PPC64LE

/-- The stack the function uses: its frame and `vg_rsa_private_checked`'s
(or `vg_rsa_private_checked_precomputed`'s, the same). -/
def stackBytes : Nat := Impl.RsaPkcs1Sig.PPC64LE.Sign.frameBytes + Impl.Rsa.PPC64LE.Priv.frameBytes

theorem stackArgs_thirteen (s : State) :
    List.map (stackArg s) (List.range 13) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12] := rfl

/-! ## The buffers -/

abbrev oR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
abbrev nR (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
abbrev dR (s : State) : Region := ⟨s.gpr .r10, (stackArg s 0).toNat⟩
abbrev pR (s : State) : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
abbrev qR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat⟩
abbrev dpR (s : State) : Region := ⟨stackArg s 5, (stackArg s 6).toNat⟩
abbrev dqR (s : State) : Region := ⟨stackArg s 7, (stackArg s 8).toNat⟩
abbrev qiR (s : State) : Region := ⟨stackArg s 9, (stackArg s 10).toNat⟩
abbrev sR (s : State) : Region := ⟨stackArg s 11, (stackArg s 12).toNat * 8⟩
/-- Our stack arguments: thirteen, or with `pc` fifteen. -/
abbrev aR (pc : Bool) (s : State) : Region := ⟨stackArgAddr s 0, if pc then 120 else 104⟩
/-- With `pc`, the key's precomputed values, `pre_len` words. -/
abbrev preR (s : State) : Region := ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩

/-- The buffers the function reads. -/
abbrev rdL (pc : Bool) (s : State) : List Region :=
  [nR s, eR s, dR s, pR s, qR s, dpR s, dqR s, qiR s] ++ (if pc then [preR s] else []) ++ [aR pc s]

/-- The base of the frame. -/
abbrev fb (s : State) : Addr := s.sp - BitVec.ofNat 64 Impl.RsaPkcs1Sig.PPC64LE.Sign.frameBytes

/-- The stack the function and its callee use. -/
abbrev kR (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩

/-- The precondition, by name. -/
structure SPre (pc : Bool) (s : State) : Prop where
  sp1 : stackBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + (if pc then 216 else 200) ≤ 2 ^ 64
  hrd : s.rd = rdL pc s
  hwr : s.wr = [oR s, sR s]
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  od : (oR s).Disjoint (dR s)
  op : (oR s).Disjoint (pR s)
  oq : (oR s).Disjoint (qR s)
  odp : (oR s).Disjoint (dpR s)
  odq : (oR s).Disjoint (dqR s)
  oqi : (oR s).Disjoint (qiR s)
  os : (oR s).Disjoint (sR s)
  oa : (oR s).Disjoint (aR pc s)
  ns : (nR s).Disjoint (sR s)
  es : (eR s).Disjoint (sR s)
  ds : (dR s).Disjoint (sR s)
  ps : (pR s).Disjoint (sR s)
  qs : (qR s).Disjoint (sR s)
  dps : (dpR s).Disjoint (sR s)
  dqs : (dqR s).Disjoint (sR s)
  qis : (qiR s).Disjoint (sR s)
  sa : (sR s).Disjoint (aR pc s)
  ko : (kR s).Disjoint (oR s)
  kn : (kR s).Disjoint (nR s)
  ke : (kR s).Disjoint (eR s)
  kd : (kR s).Disjoint (dR s)
  kp : (kR s).Disjoint (pR s)
  kq : (kR s).Disjoint (qR s)
  kdp : (kR s).Disjoint (dpR s)
  kdq : (kR s).Disjoint (dqR s)
  kqi : (kR s).Disjoint (qiR s)
  ks : (kR s).Disjoint (sR s)
  ka : (kR s).Disjoint (aR pc s)
  wo : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  wn : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  we : (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  wd : (s.gpr .r10).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  wp : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  wq : (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 64
  wdp : (stackArg s 5).toNat + (stackArg s 6).toNat ≤ 2 ^ 64
  wdq : (stackArg s 7).toNat + (stackArg s 8).toNat ≤ 2 ^ 64
  wqi : (stackArg s 9).toNat + (stackArg s 10).toNat ≤ 2 ^ 64
  ws : (stackArg s 11).toNat + (stackArg s 12).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .r6).toNat
  k2 : (s.gpr .r6).toNat ≤ 1024
  h4 : (s.gpr .r4).toNat = (s.gpr .r6).toNat
  e1 : 1 ≤ (s.gpr .r8).toNat
  e2 : (s.gpr .r8).toNat ≤ (s.gpr .r6).toNat
  p1 : 1 ≤ (stackArg s 2).toNat
  p2 : (stackArg s 2).toNat < (s.gpr .r6).toNat
  q1 : 1 ≤ (stackArg s 4).toNat
  q2 : (stackArg s 4).toNat < (s.gpr .r6).toNat
  h6 : (stackArg s 6).toNat = (stackArg s 2).toNat
  h10 : (stackArg s 10).toNat = (stackArg s 2).toNat
  h8 : (stackArg s 8).toNat = (stackArg s 4).toNat
  hs : Spec.Rsa.scratchWords (s.gpr .r6).toNat ≤ (stackArg s 12).toNat

/-- With `pc`, `pre` holds the key's precomputed values. -/
abbrev HypS (pc : Bool) (s : State) : Prop :=
  pc = true → Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 13) (stackArg s 14).toNat)

/-- What `vg_rsa_pkcs1_sign_precomputed`'s precondition adds: `pre`'s facts. -/
structure PreX (s : State) : Prop where
  oP : (oR s).Disjoint (preR s)
  sP : (sR s).Disjoint (preR s)
  kP : (kR s).Disjoint (preR s)
  wP : (stackArg s 13).toNat + (stackArg s 14).toNat * 8 ≤ 2 ^ 64
  pl : (stackArg s 14).toNat =
    Spec.Rsa.privatePrecomputedWords (s.gpr .r6).toNat (stackArg s 2).toNat (stackArg s 4).toNat
  hyp : HypS true s

theorem sPre_of {s : State} (h : (Spec.RsaPkcs1Sig.signContract abi stackBytes).pre s) : SPre false s := by
  have e : stackBytes = 4607 + 1 := rfl
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi, argRegs,
    stackArgs_thirteen, List.append_eq, List.range, List.range.loop] at h
  sig_split h
  rename_i sp1 sp2 hrd hwr on oe od op oq odp odq oqi os oa ns es ds ps qs dps dqs qis sa
    ko kn ke kd kp kq kdp kdq kqi ks ka wo wn we wd wp wq wdp wdq wqi ws k12 h4
    e1 e2 p1 p2 q1 q2 h6 h10 h8
  obtain ⟨k1, k2⟩ := k12
  exact ⟨sp1, by simp only [Bool.false_eq_true, ↓reduceIte]; omega_using [sp2], hrd, hwr, on, oe, od, op, oq, odp, odq, oqi, os, oa, ns, es, ds, ps, qs, dps, dqs, qis, sa,
    ko, kn, ke, kd, kp, kq, kdp, kdq, kqi, ks, ka, wo, wn, we, wd, wp, wq, wdp, wdq, wqi, ws, k1, k2, h4, e1, e2,
    p1, p2, q1, q2, h6, h10, h8, h⟩

end VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

end

end


/-!
# `vg_rsa_pkcs1_sign` on PPC64LE: the frame

The stack the function uses, `kR`, is `vg_rsa_private_checked`'s frame
(from `kb`) and then ours (from `fb`); the push makes our local variable
space `fr` writable.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.Sign

variable {pc : Bool}

/-- The base of the stack the function and its callee use. -/
abbrev kb (s : State) : Addr := s.sp - BitVec.ofNat 64 stackBytes

/-- Our frame's local variable space, which its push makes writable. -/
abbrev fr (s : State) : Region := ⟨fb s + BitVec.ofNat 64 32, frameBytes - 32⟩

theorem fb_eq (s : State) : fb s = kb s + BitVec.ofNat 64 Impl.Rsa.PPC64LE.Priv.frameBytes := by
  simp only [fb, kb, stackBytes, frameBytes, Impl.Rsa.PPC64LE.Priv.frameBytes]
  bv_omega

theorem fb_toNat {s : State} (h : SPre pc s) : (fb s).toNat + frameBytes = s.sp.toNat := by
  have := h.sp1
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold stackBytes frameBytes at *
  unfold Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega_using [this]

theorem kb_toNat {s : State} (h : SPre pc s) : (kb s).toNat + stackBytes = s.sp.toNat := by
  have := h.sp1
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold stackBytes frameBytes at *
  unfold Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega_using [this]

/-- A region of our frame is in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    Region.Sub ⟨fb s + BitVec.ofNat 64 d, n⟩ (kR s) := by
  rw [fb_eq, Offset.add_add]
  exact Offset.sub_base _ (by unfold stackBytes; omega_using [h])

theorem frame_contains (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    (kR s).Contains (fb s + BitVec.ofNat 64 d) n := by
  rw [fb_eq, Offset.add_add]
  exact Offset.contains_base _ (by unfold stackBytes; omega_using [h])
    (by unfold frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega_using [h])

/-- The callee's frame is in the stack the function uses. -/
theorem callee_sub (s : State) :
    Region.Sub ⟨fb s - BitVec.ofNat 64 Impl.Rsa.PPC64LE.Priv.frameBytes,
      Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (kR s) := by
  rw [fb_eq, BitVec.add_sub_cancel]
  have := Offset.sub_base (kb s) (d := 0) (n := Impl.Rsa.PPC64LE.Priv.frameBytes) (k := stackBytes)
    (by unfold stackBytes; omega_using [])
  rwa [BitVec.add_zero] at this

/-- The local variable space is writable. -/
theorem in_fr (s : State) (rs : List Region) {d n : Nat} (h₁ : 32 ≤ d) (h : d + n ≤ frameBytes) :
    InRegions (fr s :: rs) (fb s + BitVec.ofNat 64 d) n :=
  ⟨_, List.mem_cons_self .., Offset.contains _ h₁ (by unfold frameBytes at *; omega_using [h])
    (by unfold frameBytes; omega_using [])⟩

theorem in_fr' (s : State) (rd rs : List Region) {d n : Nat} (h₁ : 32 ≤ d) (h : d + n ≤ frameBytes) :
    InRegions (rd ++ fr s :: rs) (fb s + BitVec.ofNat 64 d) n := by
  obtain ⟨r, hr, hc⟩ := in_fr s rs h₁ h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- Our stack arguments, from the frame. -/
theorem stackArgAddr_fb (s : State) (j : Nat) :
    stackArgAddr s j = fb s + BitVec.ofNat 64 (arg j) := by
  obtain e : BitVec.ofNat 64 (arg j) = BitVec.ofNat 64 frameBytes + BitVec.ofNat 64 (32 + 8 * (8 + j)) := by
    rw [BitVec.ofNat_add_ofNat]; unfold arg; congr 1; omega_using []
  rw [stackArgAddr, e, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem stackArgAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, Nat.add_zero]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, show 32 + 8 * 8 + 8 * j = 32 + 8 * (8 + j) by omega_using []]

theorem lt_args {j : Nat} (hj : j < 13) : j < if pc then 15 else 13 := by
  cases pc <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega_using [hj]

theorem in_aR {s : State} {j : Nat} (hj : j < if pc then 15 else 13) : (aR pc s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]
  cases pc <;> simp only [aR, Bool.false_eq_true, ↓reduceIte] at hj ⊢ <;>
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

/-! ## The saves -/

/-- The slots of our caller's `r26`–`r30`. -/
def saved : List (Reg × Nat) :=
  [(.r26, oSave), (.r27, oSave + 8), (.r28, oSave + 16), (.r29, oSave + 24), (.r30, oSave + 32)]

/-- The callee-saved registers other than `r26`–`r30`. -/
def hiRegs : List Reg :=
  [.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r31]

theorem save_eq : save = ([.addSp .r12 0] : List Instr) ++ Spill.saveCode .r12 saved ++
    ([.mflr .r0, .store .d .r0 .r12 oLr] : List Instr) ++
    ([.logic .or .r26 .r3 .r3, .logic .or .r27 .r5 .r5, .logic .or .r28 .r6 .r6, .logic .or .r29 .r7 .r7,
      .logic .or .r30 .r8 .r8] : List Instr) :=
  rfl

theorem restore_eq :
    restore = ([.addSp .r12 0, .load .d .r0 .r12 oLr, .mtlr .r0] : List Instr) ++ Spill.restoreCode .r12 saved :=
  rfl

theorem saved_offs : ∀ p ∈ saved, oSave ≤ p.2 ∧ p.2 + 8 ≤ oSave + 40 := by decide

theorem saved_ho : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide

theorem preserved_split {r : Reg} (h : r ∈ preserved) : r ∈ saved.map Prod.fst ∨ r ∈ hiRegs := by
  revert r; decide

end VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

end

end


/-!
# `vg_rsa_pkcs1_sign` on PPC64LE: up to `encode`

From the state after the frame's push: the saves, the values kept in
`r26`–`r30` and `encode`'s arguments (`setup_ok`, into `AtEnc`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.Sign
open VG.Proof.Bignum.PPC64LE (Keep)
open VG.PPC64LE.RegUpd (gpr_write_self gpr_write_of_ne mem_write)

variable {pc : Bool}

theorem exec_addSp0 {s : State} {d : Reg} : exec (.addSp d 0) s = some (s.write d s.sp) := by
  simp [exec]

/-- In the frame, from the entry state `s`: our caller's registers and
return address in their slots, the other callee-saved registers as on entry,
memory changed only in the stack the function uses. -/
structure Fr (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = fr s :: s.wr
  lr : t.lr = s.lr
  hi : ∀ r ∈ hiRegs, t.gpr r = s.gpr r
  mem : Frame [kR s] s.mem t.mem
  sv : Spill.Saved (fb s) s.gpr saved t.mem
  ls : t.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr

/-- At `encode`. -/
structure AtEnc (s t : State) : Prop extends Fr s t where
  r4 : t.gpr .r4 = fb s + BitVec.ofNat 64 oEM
  r5 : t.gpr .r5 = s.gpr .r6
  r6 : t.gpr .r6 = ((s.gpr .r9).setWidth 32).setWidth 64
  r7 : t.gpr .r7 = s.gpr .r10
  r8 : t.gpr .r8 = stackArg s 0
  r12 : t.gpr .r12 = fb s
  r26 : t.gpr .r26 = s.gpr .r3
  r27 : t.gpr .r27 = s.gpr .r5
  r28 : t.gpr .r28 = s.gpr .r6
  r29 : t.gpr .r29 = s.gpr .r7
  r30 : t.gpr .r30 = s.gpr .r8

/-- The frame's push stores the back chain at its base. -/
theorem fb_contains (s : State) : (kR s).Contains (fb s) 8 := by
  have := frame_contains s (d := 0) (n := 8) (by decide)
  rwa [BitVec.add_zero] at this

theorem fR_sub (s : State) : Region.Sub ⟨fb s, frameBytes⟩ (kR s) := by
  have := frame_sub s (d := 0) (n := frameBytes) (by omega_using [])
  rwa [BitVec.add_zero] at this

/-- The saves, from the state after the frame's push. -/
theorem save_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ v, Fr s v → v.gpr .r12 = fb s → (∀ r, r ≠ .r12 → r ≠ .r0 → v.gpr r = s.gpr r) →
      WP isa (.block rest) v Q) :
    WP isa (.block (([.addSp .r12 0] : List Instr) ++ Spill.saveCode .r12 saved ++
      ([.mflr .r0, .store .d .r0 .r12 oLr] : List Instr) ++ rest)) (allocated frameBytes s) Q := by
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_cons_iff.mpr ⟨_, exec_addSp0, ?_⟩
  generalize hu : (allocated frameBytes s).write .r12 (allocated frameBytes s).sp = u
  obtain u12 : u.gpr .r12 = fb s := by rw [← hu, gpr_write_self]; rfl
  obtain uwr : u.wr = fr s :: s.wr := by rw [← hu]; rfl
  refine Spill.save_ok (b := .r12) (l := saved) (by decide) saved_ho (fun p hp => ?_) ?_
  · have := saved_offs p hp
    rw [uwr, u12]; exact in_fr s _ (by unfold oSave at this; omega_using [this]) (by unfold oSave frameBytes at *; omega_using [this])
  generalize hu₂ : ({ u with mem := Spill.saveMem u.mem (u.gpr .r12) u.gpr saved } : State) = u₂
  obtain g₂ : u₂.gpr = u.gpr := by rw [← hu₂]
  obtain m₂ : u₂.mem = Spill.saveMem u.mem (fb s) u.gpr saved := by rw [← hu₂, u12]
  obtain hin : InRegions u₂.wr (u₂.gpr .r12 + BitVec.ofNat 64 oLr) 8 := by
    have : u₂.wr = fr s :: s.wr := by rw [← hu₂]; exact uwr
    rw [this, g₂, u12]; exact in_fr s _ (by decide) (by decide)
  refine WP.block_cons_iff.mpr ⟨_, exec_mflr, WP.block_cons_iff.mpr ⟨_, exec_store_d (t := .r0) (n := .r12)
    (off := oLr) (by decide) ⟨by decide, by decide⟩
    (by rw [gpr_write_of_ne _ _ (show Reg.r12 ≠ .r0 by decide)]; exact hin), ?_⟩⟩
  obtain hum : u.mem = s.mem.write (fb s) 8 s.sp := by rw [← hu]; rfl
  obtain fr₂ : Frame [kR s] s.mem u₂.mem := by
    rw [m₂]
    obtain f1 : Frame [kR s] s.mem u.mem := by
      rw [hum]; exact Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ (fb_contains s)
    exact f1.trans ((Spill.saveMem_frame_base (n := frameBytes) (fun p hp => by
      have := saved_offs p hp; unfold oSave frameBytes at *; omega_using [this]) (by decide) _ _ _).sub
      fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, fR_sub s⟩)
  obtain sv₂ : Spill.Saved (fb s) s.gpr saved u₂.mem := by
    rw [m₂]
    refine fun p hp => (Spill.saveMem_saved (by decide) _ _ _ p hp).trans ?_
    obtain h12 : p.1 ≠ .r12 := by revert p; decide
    rw [← hu, gpr_write_of_ne _ _ h12]; rfl
  obtain hd : ∀ p ∈ saved, ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 oLr, 8⟩ : Region)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 p.2, 8⟩ r := fun p hp r hr => by
    have := saved_offs p hp
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by unfold oSave oLr at *; omega_using [this])) (by unfold oSave at *; omega_using [this]) (by decide)
  obtain e12 : (u₂.write .r0 u₂.lr).gpr .r12 = fb s := by rw [gpr_write_of_ne _ _ (show Reg.r12 ≠ .r0 by decide), g₂, u12]
  rw [e12]
  refine k _ ⟨?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩ ?_ fun r h12 h0 => ?_
  · show u₂.sp = fb s; rw [← hu₂, ← hu]; rfl
  · show u₂.rd = s.rd; rw [← hu₂, ← hu]; rfl
  · show u₂.wr = fr s :: s.wr; rw [← hu₂]; exact uwr
  · show u₂.lr = s.lr; rw [← hu₂, ← hu]; rfl
  · show (u₂.write .r0 u₂.lr).gpr r = s.gpr r
    obtain h0 : r ≠ .r0 := by revert r; decide
    obtain h12 : r ≠ .r12 := by revert r; decide
    rw [gpr_write_of_ne _ _ h0, g₂, ← hu, gpr_write_of_ne _ _ h12]; rfl
  · show Frame [kR s] s.mem ((u₂.write .r0 u₂.lr).mem.writeW (fb s + BitVec.ofNat 64 oLr) _)
    rw [mem_write]
    exact fr₂.writeW (List.mem_singleton_self _) _ (frame_contains s (by decide))
  · show Spill.Saved (fb s) s.gpr saved ((u₂.write .r0 u₂.lr).mem.writeW (fb s + BitVec.ofNat 64 oLr) _)
    rw [mem_write]
    exact sv₂.frame (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)) hd
  · show ((u₂.write .r0 u₂.lr).mem.writeW (fb s + BitVec.ofNat 64 oLr) _).readW _ 64 = s.lr
    rw [Mem.readW_writeW_self64, gpr_write_self]; show u₂.lr = s.lr; rw [← hu₂, ← hu]; rfl
  · show (u₂.write .r0 u₂.lr).gpr .r12 = fb s; exact e12
  · show (u₂.write .r0 u₂.lr).gpr r = s.gpr r
    rw [gpr_write_of_ne _ _ h0, g₂, ← hu, gpr_write_of_ne _ _ h12]; rfl

/-- Our stack argument `j` is in the arguments' region, apart from the stack. -/
theorem arg_readG {s : State} (h : SPre pc s) {m : Mem} (hm : Frame [kR s] s.mem m) {j : Nat}
    (hj : j < if pc then 15 else 13) : m.readW (fb s + BitVec.ofNat 64 (arg j)) 64 = stackArg s j := by
  rw [← stackArgAddr_fb]
  exact hm.readW (in_aR (pc := pc) hj) (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.ka.symm) (by decide)

theorem arg_inG {s t : State} (h : SPre pc s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < if pc then 15 else 13) :
    InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 (arg j)) 8 := by
  rw [← stackArgAddr_fb, hrd, h.hrd]
  exact ⟨aR pc s, List.mem_append_left _ (by simp [rdL]), in_aR hj⟩

theorem arg_read {s : State} (h : SPre pc s) {m : Mem} (hm : Frame [kR s] s.mem m) {j : Nat} (hj : j < 13) :
    m.readW (fb s + BitVec.ofNat 64 (arg j)) 64 = stackArg s j :=
  arg_readG h hm (lt_args hj)

theorem arg_in {s t : State} (h : SPre pc s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 13) :
    InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 (arg j)) 8 :=
  arg_inG h hrd (lt_args hj)

theorem setup_ok {s : State} (h : SPre pc s) :
    WP isa (.block (save ++ encArgs)) (allocated frameBytes s) (AtEnc s) := by
  obtain e : save ++ encArgs = ([.addSp .r12 0] : List Instr) ++ Spill.saveCode .r12 saved ++
      ([.mflr .r0, .store .d .r0 .r12 oLr] : List Instr) ++
      (([.logic .or .r26 .r3 .r3, .logic .or .r27 .r5 .r5, .logic .or .r28 .r6 .r6, .logic .or .r29 .r7 .r7,
        .logic .or .r30 .r8 .r8] : List Instr) ++ encArgs) := by
    rw [save_eq]; simp only [List.append_assoc]
  rw [e]
  refine save_ok fun v F h12 hg => ?_
  obtain a0 := arg_read h F.mem (j := 0) (by decide)
  obtain i0 := arg_in h F.rd (j := 0) (by decide)
  obtain c0 : arg 0 < 2 ^ 15 := by decide
  obtain d0 : arg 0 % 4 = 0 := by decide
  obtain c1 : oEM < 2 ^ 15 := by decide
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r26, .r27, .r28, .r29, .r30, .r4, .r5, .r6, .r7, .r8]
    (Q := fun w => w.gpr .r4 = fb s + BitVec.ofNat 64 oEM ∧ w.gpr .r5 = s.gpr .r6 ∧ w.gpr .r6 = ((s.gpr .r9).setWidth 32).setWidth 64 ∧
      w.gpr .r7 = s.gpr .r10 ∧ w.gpr .r8 = stackArg s 0 ∧ w.gpr .r26 = s.gpr .r3 ∧ w.gpr .r27 = s.gpr .r5 ∧
      w.gpr .r28 = s.gpr .r6 ∧ w.gpr .r29 = s.gpr .r7 ∧ w.gpr .r30 = s.gpr .r8 ∧ w.mem = v.mem) ?_ rfl)
    fun w ⟨⟨w4, w5, w6, w7, w8, w26, w27, w28, w29, w30, wm⟩, kw⟩ => ?_
  · unfold encArgs
    prun [c0, d0, c1, i0, a0, h12, hg .r3 (by decide) (by decide), hg .r5 (by decide) (by decide),
      hg .r6 (by decide) (by decide), hg .r7 (by decide) (by decide), hg .r8 (by decide) (by decide),
      hg .r9 (by decide) (by decide), hg .r10 (by decide) (by decide), BitVec.or_self,
      exec_addi (show Reg.r12 ≠ .r0 by decide) c1, Impl.AesGcm.PPC64LE.mov,
      exec_lsr_w (show 0 < 32 by decide), BitVec.ushiftRight_zero]
  · refine ⟨⟨kw.sp.trans F.sp, kw.rd.trans F.rd, kw.wr.trans F.wr, kw.lr.trans F.lr,
      fun r hr => (kw.gpr _ (by revert r; decide)).trans (F.hi r hr), wm ▸ F.mem, wm ▸ F.sv, wm ▸ F.ls⟩,
      w4, w5, w6, w7, w8, (kw.gpr _ (by decide)).trans h12, w26, w27, w28, w29, w30⟩

end VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

end

end


/-!
# `vg_rsa_pkcs1_sign` on PPC64LE: the encoding

`encode` (`Proof/RsaPkcs1Sig/PPC64LE/Encode.lean`) from `AtEnc`: its
precondition (`AtEnc.epre`) and what follows it (`enc_ok`, into `AtAft`):
`EM` in the frame and 1, or 0, as the encoding of the hash value succeeds
(`encOut`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.Sign
open VG.Proof.RsaPkcs1Sig.PPC64LE (EPre EPost EOut encodeId encode_ok)

variable {pc : Bool}

/-- `EM`, in the frame. -/
abbrev emR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oEM, (s.gpr .r6).toNat⟩

theorem em_sub {s : State} (h : SPre pc s) : Region.Sub (emR s) (kR s) :=
  frame_sub s (by have := h.k2; unfold oEM frameBytes; omega_using [this])

/-- The hash value. -/
abbrev hashOf (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat

/-- The encoding of the hash value, if it succeeds. -/
abbrev encOut (s : State) : Option (List Byte) :=
  encodeId ((s.gpr .r9).setWidth 32) (hashOf s) (s.gpr .r6).toNat

/-- A byte of `EM` is in the local variable space. -/
theorem em_in {s : State} (h : SPre pc s) (rs : List Region) {i : Nat} (hi : i < (s.gpr .r6).toNat) :
    InRegions (fr s :: rs) (fb s + BitVec.ofNat 64 oEM + BitVec.ofNat 64 i) 1 := by
  rw [Offset.add_add]; exact in_fr s rs (by unfold oEM; omega_using []) (by have := h.k2; unfold oEM frameBytes; omega_using [hi, this])

theorem bytes_of_frame {s : State} {rs : List Region} {m : Mem} (hf : Frame rs s.mem m) {p : Addr}
    {len : Nat} (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, len⟩ r) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) hd hl (List.mem_range.mp hi)

theorem AtEnc.epre {s t : State} (h : SPre pc s) (A : AtEnc s t) :
    EPre t ((s.gpr .r9).setWidth 32) (s.gpr .r6).toNat := by
  refine ⟨by rw [A.r6, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq], by rw [A.r5], h.k2, fun i hi => ?_, fun j hj => ?_, fun j hj i hi e => ?_⟩
  · rw [A.r4, A.wr]; exact em_in h _ hi
  · rw [A.r7, A.rd, h.hrd]
    rw [A.r8] at hj
    exact ⟨dR s, List.mem_append_left _ (by simp), Offset.contains_base _ (by omega_using [hj]) (by have := h.wd; omega_using [hj])⟩
  · rw [A.r8] at hj
    rw [A.r7, A.r4] at e
    obtain c1 : (dR s).Contains (s.gpr .r10 + BitVec.ofNat 64 j) 1 :=
      Offset.contains_base _ (by omega_using [hj]) (by have := h.wd; omega_using [hj])
    obtain c2 : (kR s).Contains (s.gpr .r10 + BitVec.ofNat 64 j) 1 := by
      rw [e, Offset.add_add]; exact frame_contains s (by have := h.k2; unfold oEM frameBytes; omega_using [hi, this])
    exact h.kd _ c2 c1

theorem encodeId_len {x : BitVec 32} {H em : List Byte} {k : Nat} (h : encodeId x H k = some em) :
    em.length = k := by
  unfold encodeId at h
  split at h
  · exact Proof.RsaPkcs1Sig.encode_length h
  · cases h

/-- After `encode`. -/
structure AtAft (s u : State) : Prop extends Fr s u where
  r12 : u.gpr .r12 = fb s
  r26 : u.gpr .r26 = s.gpr .r3
  r27 : u.gpr .r27 = s.gpr .r5
  r28 : u.gpr .r28 = s.gpr .r6
  r29 : u.gpr .r29 = s.gpr .r7
  r30 : u.gpr .r30 = s.gpr .r8
  enc : match encOut s with
    | some em => u.gpr .r3 = 1 ∧ Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oEM) (s.gpr .r6).toNat = em
    | none => u.gpr .r3 = 0

/-- The frame's words below `EM` are apart from it. -/
theorem below_em {s : State} (h : SPre pc s) {d : Nat} (hd : d + 8 ≤ oEM) {r : Region} (hr : r ∈ [emR s]) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := by
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ (.inl hd) (by unfold oEM at hd; omega_using [hd]) (by have := h.k2; unfold oEM; omega_using [this])

theorem enc_ok {s t : State} (h : SPre pc s) (A : AtEnc s t) :
    WP isa Impl.RsaPkcs1Sig.PPC64LE.encode t (AtAft s) := by
  have hk := h.k2
  obtain hH : Spec.Rsa.bytesAt t.mem (t.gpr .r7) (t.gpr .r8).toNat = hashOf s := by
    rw [A.r7, A.r8]
    exact bytes_of_frame A.mem (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.kd.symm)
      (by have := h.wd; omega_using [])
  refine WP.mono (encode_ok (A.epre h)) fun u ⟨kp, eo⟩ => ?_
  rw [hH] at eo
  obtain hf : Frame [emR s] t.mem u.mem ∧ (match encOut s with
      | some em => u.gpr .r3 = 1 ∧ Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oEM) (s.gpr .r6).toNat = em
      | none => u.gpr .r3 = 0) := by
    show Frame _ _ _ ∧ match encOut s with | some em => _ | none => _
    unfold encOut
    revert eo
    cases he : encodeId ((s.gpr .r9).setWidth 32) (hashOf s) (s.gpr .r6).toNat with
    | none => intro eo; simp only [EOut] at eo; exact ⟨eo.2 ▸ Frame.refl _ _, eo.1⟩
    | some em =>
      intro eo
      obtain hl := encodeId_len he
      simp only [EOut] at eo
      rw [A.r4] at eo
      refine ⟨eo.2 ▸ VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _), eo.1, ?_⟩
      rw [eo.2, ← hl]; exact Proof.RsaPkcs1Sig.bytesAt_writeBytes _ _ _ (by omega_using [hl])
  obtain ⟨hf, he⟩ := hf
  refine ⟨⟨kp.sp.trans A.sp, kp.rd.trans A.rd, kp.wr.trans A.wr, kp.lr.trans A.lr,
    fun r hr => (kp.gpr r (by revert r; decide)).trans (A.hi r hr),
    A.mem.trans (hf.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, em_sub h⟩),
    A.sv.frame hf fun p hp r hr => below_em h (by have := saved_offs p hp; unfold oSave oEM at *; omega_using [this]) hr, ?_⟩,
    (kp.gpr _ (by decide)).trans A.r12, (kp.gpr _ (by decide)).trans A.r26, (kp.gpr _ (by decide)).trans A.r27,
    (kp.gpr _ (by decide)).trans A.r28, (kp.gpr _ (by decide)).trans A.r29, (kp.gpr _ (by decide)).trans A.r30, he⟩
  rw [hf.readW (Region.contains_self _ _) (fun r hr => below_em h (by decide) hr) (by decide)]; exact A.ls

end VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

end

end


/-!
# `vg_rsa_pkcs1_sign` on PPC64LE: the call's arguments

`vg_rsa_private_checked`'s twelve stack arguments copied from ours and its
arguments in registers (`callArgs_ok`, into `AtCall`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.Sign
open VG.Proof.Bignum.PPC64LE (Keep)
open VG.PPC64LE.RegUpd (gpr_write_self gpr_write_of_ne mem_write)

variable {pc : Bool}

/-- The Parameter Save Area of the call: its twelve, or with `pc` fourteen,
stack arguments. -/
abbrev psaR (pc : Bool) (s : State) : Region := ⟨fb s + BitVec.ofNat 64 96, if pc then 112 else 96⟩

theorem psa_le : (if pc then 112 else 96) ≤ 112 := by cases pc <;> decide

theorem psa_sub (s : State) : Region.Sub (psaR pc s) (kR s) := frame_sub s (by cases pc <;> decide)

theorem nCall_lt {n : Nat} (hn : n < nCallArgs pc) : n < 14 ∧ 1 + n < if pc then 15 else 13 := by
  cases pc <;> simp only [nCallArgs, Bool.false_eq_true, ↓reduceIte] at hn ⊢ <;> omega_using [hn]

/-- A slot of the frame above the Parameter Save Area. -/
theorem psa_dis (s : State) {d n : Nat} (hd : 208 ≤ d) (hd' : d + n ≤ frameBytes) :
    ∀ r ∈ [psaR pc s], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r := fun r hr => by
  rw [List.mem_singleton.mp hr]
  have := psa_le (pc := pc)
  exact Offset.disjoint _ (.inr (by omega_using [hd, this])) (by unfold frameBytes at hd'; omega_using [hd']) (by omega_using [this])

/-- At the call of `vg_rsa_private_checked`, with `EM` holding `em`. -/
structure AtCall (pc : Bool) (s t : State) (em : List Byte) : Prop extends Fr s t where
  em : Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM) (s.gpr .r6).toNat = em
  r3 : t.gpr .r3 = s.gpr .r3
  r4 : t.gpr .r4 = s.gpr .r6
  r5 : t.gpr .r5 = s.gpr .r5
  r6 : t.gpr .r6 = s.gpr .r6
  r7 : t.gpr .r7 = s.gpr .r7
  r8 : t.gpr .r8 = s.gpr .r8
  r9 : t.gpr .r9 = fb s + BitVec.ofNat 64 oEM
  r10 : t.gpr .r10 = s.gpr .r6
  r26 : t.gpr .r26 = s.gpr .r3
  r28 : t.gpr .r28 = s.gpr .r6
  psa : ∀ i < nCallArgs pc, t.mem.readW (fb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = stackArg s (1 + i)

/-- After copying the first `n` stack arguments, from `w`. -/
structure CI (pc : Bool) (s w : State) (n : Nat) (t : State) : Prop where
  keep : Keep [.r0] w t
  mem : Frame [psaR pc s] w.mem t.mem
  psa : ∀ i < n, t.mem.readW (fb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = stackArg s (1 + i)

theorem copy_step {s w : State} (h : SPre pc s) (hw12 : w.gpr .r12 = fb s) (hrd : w.rd = s.rd)
    (hwr : w.wr = fr s :: s.wr) (hm : Frame [kR s] s.mem w.mem) {n : Nat} (hn : n < nCallArgs pc) {t : State}
    (hc : CI pc s w n t) : WP isa (.block (copyArg n)) t (CI pc s w (n + 1)) := by
  obtain ⟨hn14, hn'⟩ := nCall_lt hn
  obtain t12 : t.gpr .r12 = fb s := (hc.keep.gpr _ (by decide)).trans hw12
  obtain hmt : Frame [kR s] s.mem t.mem := hm.trans (hc.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, psa_sub s⟩)
  obtain hin : InRegions (t.rd ++ t.wr) (t.gpr .r12 + BitVec.ofNat 64 (arg (1 + n))) 8 := by
    rw [t12]; exact arg_inG h (hc.keep.rd.trans hrd) hn'
  obtain hv : t.mem.readW (t.gpr .r12 + BitVec.ofNat 64 (arg (1 + n))) 64 = stackArg s (1 + n) := by
    rw [t12]; exact arg_readG h hmt hn'
  obtain ho : InRegions t.wr (t.gpr .r12 + BitVec.ofNat 64 (96 + 8 * n)) 8 := by
    rw [t12, hc.keep.wr, hwr]; exact in_fr s _ (by omega_using []) (by unfold frameBytes; omega_using [hn14])
  obtain harg : arg (1 + n) < 2 ^ 15 ∧ arg (1 + n) % 4 = 0 := by unfold arg frameBytes; omega_using [hn14]
  apply WP.of_runBlock
  simp only [copyArg, runBlock_cons, runStep_some, exec_load_d (show Reg.r12 ≠ .r0 by decide) harg hin]
  rw [exec_store_d (show Reg.r12 ≠ .r0 by decide) ⟨by omega_using [hn14], by omega_using []⟩
    (by rw [gpr_write_of_ne _ _ (show Reg.r12 ≠ .r0 by decide)]; exact ho)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  rw [gpr_write_of_ne _ _ (show Reg.r12 ≠ .r0 by decide), gpr_write_self, mem_write, hv, t12]
  refine ⟨⟨fun r hr => ?_, hc.keep.rd, hc.keep.wr, hc.keep.sp, hc.keep.lr⟩, ?_, fun i hi => ?_⟩
  · show (t.write .r0 _).gpr r = w.gpr r
    rw [gpr_write_of_ne _ _ (by simpa using hr)]; exact hc.keep.gpr r hr
  · have := psa_le (pc := pc)
    have := hn
    exact hc.mem.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using [])
      (by cases pc <;> simp only [nCallArgs, Bool.false_eq_true, ↓reduceIte] at hn ⊢ <;> omega_arith) (by omega_arith))
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega_using [hi])) (by omega_arith) (by omega_using [hn14])) (by decide)]
      exact hc.psa i hi
    · rw [Mem.readW_writeW_self64]

theorem copies_ok {s w : State} (h : SPre pc s) (hw12 : w.gpr .r12 = fb s) (hrd : w.rd = s.rd)
    (hwr : w.wr = fr s :: s.wr) (hm : Frame [kR s] s.mem w.mem) :
    WP isa (.block ((List.range (nCallArgs pc)).flatMap copyArg)) w (CI pc s w (nCallArgs pc)) :=
  wp_range_flatMap (M := isa) (CI pc s w) (fun _ _ hn hc => copy_step h hw12 hrd hwr hm hn hc) (nCallArgs pc)
    (Nat.le_refl _) w
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem callArgs_ok {s u : State} (h : SPre pc s) (A : AtAft s u) {em : List Byte}
    (hem : Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oEM) (s.gpr .r6).toNat = em) :
    WP isa (.block (callArgs pc)) u fun t => AtCall pc s t em := by
  have hk := h.k2
  unfold callArgs
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12] (Q := fun w => w.gpr .r12 = fb s ∧ w.mem = u.mem) ?_ rfl)
    fun w ⟨⟨w12, wm⟩, kw⟩ => ?_
  · prun [exec_addSp0, A.sp]
  rw [WP.block_append_iff]
  refine WP.mono (copies_ok h w12 (kw.rd.trans A.rd) (kw.wr.trans A.wr) (wm ▸ A.mem)) fun v hc => ?_
  obtain v12 : v.gpr .r12 = fb s := (hc.keep.gpr _ (by decide)).trans w12
  obtain c1 : oEM < 2 ^ 15 := by decide
  obtain kv : ∀ r, r ≠ .r12 → r ≠ .r0 → v.gpr r = u.gpr r := fun r h1 h2 =>
    (hc.keep.gpr r (by simpa using h2)).trans (kw.gpr r (by simpa using h1))
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] (Q := fun t =>
    t.gpr .r3 = s.gpr .r3 ∧ t.gpr .r4 = s.gpr .r6 ∧ t.gpr .r5 = s.gpr .r5 ∧ t.gpr .r6 = s.gpr .r6 ∧
      t.gpr .r7 = s.gpr .r7 ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = fb s + BitVec.ofNat 64 oEM ∧
      t.gpr .r10 = s.gpr .r6 ∧ t.mem = v.mem) ?_ rfl) fun t ⟨⟨t3, t4, t5, t6, t7, t8, t9, t10, tm⟩, kt⟩ => ?_
  · prun [v12, c1, kv .r26 (by decide) (by decide), kv .r27 (by decide) (by decide),
      kv .r28 (by decide) (by decide), kv .r29 (by decide) (by decide), kv .r30 (by decide) (by decide),
      A.r26, A.r27, A.r28, A.r29, A.r30, BitVec.or_self, exec_addi (show Reg.r12 ≠ .r0 by decide) c1,
      Impl.AesGcm.PPC64LE.mov]
  obtain hm : Frame [psaR pc s] u.mem t.mem := by rw [tm, ← wm]; exact hc.mem
  obtain hd : ∀ {d n : Nat}, 208 ≤ d → d + n ≤ frameBytes →
      ∀ r ∈ [psaR pc s], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r := fun hdn hdn' => psa_dis s hdn hdn'
  obtain kk : ∀ r, r ∉ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12, .r0] → t.gpr r = u.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kt.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1]), kv r hr.2.2.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2.2]
  refine ⟨⟨kt.sp.trans (hc.keep.sp.trans (kw.sp.trans A.sp)), kt.rd.trans (hc.keep.rd.trans (kw.rd.trans A.rd)),
    kt.wr.trans (hc.keep.wr.trans (kw.wr.trans A.wr)), kt.lr.trans (hc.keep.lr.trans (kw.lr.trans A.lr)),
    fun r hr => (kk r (by revert r; decide)).trans (A.hi r hr),
    A.mem.trans (hm.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, psa_sub s⟩),
    A.sv.frame hm fun p hp => by
      have := saved_offs p hp; exact hd (by unfold oSave at this; omega_using [this]) (by unfold oSave frameBytes at *; omega_using [this]),
    ?_⟩, ?_, t3, t4, t5, t6, t7, t8, t9, t10, (kk _ (by decide)).trans A.r26, (kk _ (by decide)).trans A.r28,
    fun i hi => by rw [tm]; exact hc.psa i hi⟩
  · rw [hm.readW (Region.contains_self _ _) (hd (by decide) (by decide)) (by decide)]; exact A.ls
  · rw [← hem]
    exact bytes_of_frame (s := u) hm (hd (by decide) (by unfold oEM frameBytes; omega_using [hk])) (by omega_using [])

end VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

end

end


/-!
# `vg_rsa_pkcs1_sign` on PPC64LE: the call of `vg_rsa_private_checked`

The regions the call is narrowed to (`callRd`, `callWr`), its precondition
(`preP_entry`, `Priv.pre_of_preP`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.Sign

variable {pc : Bool}

/-- The regions the call reads and writes. -/
abbrev callRd (pc : Bool) (s : State) : List Region :=
  [nR s, eR s, emR s, pR s, qR s, dpR s, dqR s, qiR s] ++ (if pc then [preR s] else []) ++ [psaR pc s]

abbrev callWr (s : State) : List Region := [⟨s.gpr .r3, (s.gpr .r6).toNat⟩, sR s]

/-- The call's narrowed entry state. -/
abbrev callE (pc : Bool) (s t : State) : State := t.callEntry.withRegions (callRd pc s) (callWr s)

theorem callE_gpr (s t : State) {r : Reg} (hr : r ∉ linkRegs := by decide) : (callE pc s t).gpr r = t.gpr r :=
  State.callEntry_gpr t hr

theorem callE_stackArg {s t : State} {em : List Byte} (A : AtCall pc s t em) {i : Nat} (hi : i < nCallArgs pc) :
    stackArg (callE pc s t) i = stackArg s (1 + i) := by
  show t.mem.readW (stackArgAddr (callE pc s t) i) 64 = _
  rw [stackArgAddr, show (callE pc s t).sp = fb s from A.sp, show 32 + 8 * (8 + i) = 96 + 8 * i by omega_using []]
  exact A.psa i hi

theorem callE_addr {s t : State} {em : List Byte} (A : AtCall pc s t em) :
    stackArgAddr (callE pc s t) 0 = fb s + BitVec.ofNat 64 96 := by
  rw [stackArgAddr, show (callE pc s t).sp = fb s from A.sp]

theorem lt_nCall {i : Nat} (hi : i < 12) : i < nCallArgs pc := by
  cases pc <;> simp only [nCallArgs, Bool.false_eq_true, ↓reduceIte] <;> omega_using [hi]

theorem preP_entry {s t : State} {em : List Byte} (h : SPre pc s) (A : AtCall pc s t em) :
    Rsa.PPC64LE.Priv.PreP pc (callE pc s t) := by
  have hk := h.k2
  obtain fbt := fb_toNat h
  obtain kbt := kb_toNat h
  unfold stackBytes frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes at kbt
  unfold frameBytes at fbt
  obtain sa := fun i (hi : i < 12) => callE_stackArg A (i := i) (lt_nCall hi)
  have hsp : (callE pc s t).sp = fb s := A.sp
  obtain pl := psa_le (pc := pc)
  obtain hOo : (⟨s.gpr .r3, (s.gpr .r6).toNat⟩ : Region) = oR s := by simp only [oR, h.h4]
  obtain cs := callee_sub s
  obtain es := em_sub h
  obtain ps : Region.Sub (psaR pc s) (kR s) := psa_sub s
  obtain hK : Rsa.PPC64LE.Priv.kR (callE pc s t) = ⟨kb s, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := by
    simp only [Rsa.PPC64LE.Priv.kR, Rsa.PPC64LE.Priv.fb, hsp, fb_eq, BitVec.add_sub_cancel]
  obtain ki : Region.Disjoint ⟨kb s, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (emR s) := by
    show Region.Disjoint _ ⟨fb s + BitVec.ofNat 64 oEM, _⟩
    rw [fb_eq, Offset.add_add]
    exact (Offset.disjoint_base _ (by unfold Impl.Rsa.PPC64LE.Priv.frameBytes; omega_using [])
      (by unfold oEM Impl.Rsa.PPC64LE.Priv.frameBytes; omega_using [hk])).symm
  obtain ka : Region.Disjoint ⟨kb s, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (psaR pc s) := by
    show Region.Disjoint _ ⟨fb s + BitVec.ofNat 64 96, _⟩
    rw [fb_eq, Offset.add_add]
    exact (Offset.disjoint_base _ (by unfold Impl.Rsa.PPC64LE.Priv.frameBytes; omega_using [])
      (by unfold Impl.Rsa.PPC64LE.Priv.frameBytes; omega_using [pl])).symm
  obtain cs' : Region.Sub ⟨kb s, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (kR s) := by
    have := cs; rwa [fb_eq, BitVec.add_sub_cancel] at this
  obtain g3 : (callE pc s t).gpr .r3 = s.gpr .r3 := (callE_gpr (pc := pc) s t).trans A.r3
  obtain g4 : (callE pc s t).gpr .r4 = s.gpr .r6 := (callE_gpr (pc := pc) s t).trans A.r4
  obtain g5 : (callE pc s t).gpr .r5 = s.gpr .r5 := (callE_gpr (pc := pc) s t).trans A.r5
  obtain g6 : (callE pc s t).gpr .r6 = s.gpr .r6 := (callE_gpr (pc := pc) s t).trans A.r6
  obtain g7 : (callE pc s t).gpr .r7 = s.gpr .r7 := (callE_gpr (pc := pc) s t).trans A.r7
  obtain g8 : (callE pc s t).gpr .r8 = s.gpr .r8 := (callE_gpr (pc := pc) s t).trans A.r8
  obtain g9 : (callE pc s t).gpr .r9 = fb s + BitVec.ofNat 64 oEM := (callE_gpr (pc := pc) s t).trans A.r9
  obtain g10 : (callE pc s t).gpr .r10 = s.gpr .r6 := (callE_gpr (pc := pc) s t).trans A.r10
  obtain hO : Rsa.PPC64LE.Priv.oR (callE pc s t) = oR s := by simp only [Rsa.PPC64LE.Priv.oR, g3, g4, oR, h.h4]
  obtain hN : Rsa.PPC64LE.Priv.nR (callE pc s t) = nR s := by simp only [Rsa.PPC64LE.Priv.nR, g5, g6]
  obtain hE : Rsa.PPC64LE.Priv.eR (callE pc s t) = eR s := by simp only [Rsa.PPC64LE.Priv.eR, g7, g8]
  obtain hI : Rsa.PPC64LE.Priv.iR (callE pc s t) = emR s := by simp only [Rsa.PPC64LE.Priv.iR, g9, g10]
  obtain hP : Rsa.PPC64LE.Priv.pR (callE pc s t) = pR s := by
    simp only [Rsa.PPC64LE.Priv.pR, sa 0 (by decide), sa 1 (by decide)]
  obtain hQ : Rsa.PPC64LE.Priv.qR (callE pc s t) = qR s := by
    simp only [Rsa.PPC64LE.Priv.qR, sa 2 (by decide), sa 3 (by decide)]
  obtain hDP : Rsa.PPC64LE.Priv.dpR (callE pc s t) = dpR s := by
    simp only [Rsa.PPC64LE.Priv.dpR, sa 4 (by decide), sa 5 (by decide)]
  obtain hDQ : Rsa.PPC64LE.Priv.dqR (callE pc s t) = dqR s := by
    simp only [Rsa.PPC64LE.Priv.dqR, sa 6 (by decide), sa 7 (by decide)]
  obtain hQI : Rsa.PPC64LE.Priv.qiR (callE pc s t) = qiR s := by
    simp only [Rsa.PPC64LE.Priv.qiR, sa 8 (by decide), sa 9 (by decide)]
  obtain hS : Rsa.PPC64LE.Priv.sR (callE pc s t) = sR s := by
    simp only [Rsa.PPC64LE.Priv.sR, sa 10 (by decide), sa 11 (by decide)]
  obtain hA : Rsa.PPC64LE.Priv.aR pc (callE pc s t) = psaR pc s := by simp only [Rsa.PPC64LE.Priv.aR, callE_addr A]
  obtain s1 := sa 1 (by decide)
  obtain s3 := sa 3 (by decide)
  obtain s5 := sa 5 (by decide)
  obtain s7 := sa 7 (by decide)
  obtain s9 := sa 9 (by decide)
  obtain s11 := sa 11 (by decide)
  obtain wo' : (s.gpr .r3).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 := h.h4 ▸ h.wo
  refine ⟨by rw [hsp]; unfold Impl.Rsa.PPC64LE.Priv.frameBytes; omega_using [fbt, kbt], by rw [hsp]; omega_using [fbt], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Rsa.PPC64LE.Priv.rdL, hN, hE, hI, hP, hQ, hDP, hDQ, hQI, hA]
    cases pc
    · simp only [Bool.false_eq_true, ↓reduceIte]; rfl
    · simp only [↓reduceIte, Rsa.PPC64LE.Priv.preR, callE_stackArg A (i := 12) (by decide),
        callE_stackArg A (i := 13) (by decide)]
      rfl
  · rw [hO, hS, ← hOo]; rfl
  · rw [hO, hN]; exact h.on
  · rw [hO, hE]; exact h.oe
  · rw [hO, hI]; exact (h.ko.sub_left es).symm
  · rw [hO, hP]; exact h.op
  · rw [hO, hQ]; exact h.oq
  · rw [hO, hDP]; exact h.odp
  · rw [hO, hDQ]; exact h.odq
  · rw [hO, hQI]; exact h.oqi
  · rw [hO, hS]; exact h.os
  · rw [hO, hA]; exact (h.ko.sub_left ps).symm
  · rw [hN, hS]; exact h.ns
  · rw [hE, hS]; exact h.es
  · rw [hI, hS]; exact h.ks.sub_left es
  · rw [hP, hS]; exact h.ps
  · rw [hQ, hS]; exact h.qs
  · rw [hDP, hS]; exact h.dps
  · rw [hDQ, hS]; exact h.dqs
  · rw [hQI, hS]; exact h.qis
  · rw [hS, hA]; exact (h.ks.sub_left ps).symm
  · rw [hK, hO]; exact h.ko.sub_left cs'
  · rw [hK, hN]; exact h.kn.sub_left cs'
  · rw [hK, hE]; exact h.ke.sub_left cs'
  · rw [hK, hI]; exact ki
  · rw [hK, hP]; exact h.kp.sub_left cs'
  · rw [hK, hQ]; exact h.kq.sub_left cs'
  · rw [hK, hDP]; exact h.kdp.sub_left cs'
  · rw [hK, hDQ]; exact h.kdq.sub_left cs'
  · rw [hK, hQI]; exact h.kqi.sub_left cs'
  · rw [hK, hS]; exact h.ks.sub_left cs'
  · rw [hK, hA]; exact ka
  · rw [g3, g4]; exact wo'
  · rw [g5, g6]; exact h.wn
  · rw [g7, g8]; exact h.we
  · rw [g9, g10, Offset.toNat_add_ofNat]; unfold oEM; omega_using [hk, fbt]
  · rw [sa 0 (by decide), s1]; exact h.wp
  · rw [sa 2 (by decide), s3]; exact h.wq
  · rw [sa 4 (by decide), s5]; exact h.wdp
  · rw [sa 6 (by decide), s7]; exact h.wdq
  · rw [sa 8 (by decide), s9]; exact h.wqi
  · rw [sa 10 (by decide), s11]; exact h.ws
  · rw [g6]; exact h.k1
  · rw [g6]; exact h.k2
  · rw [g4, g6]
  · rw [g10, g6]
  · rw [g8]; exact h.e1
  · rw [g8, g6]; exact h.e2
  · rw [s1]; exact h.p1
  · rw [s1, g6]; exact h.p2
  · rw [s3]; exact h.q1
  · rw [s3, g6]; exact h.q2
  · rw [s5, s1]; exact h.h6
  · rw [s9, s1]; exact h.h10
  · rw [s7, s3]; exact h.h8
  · rw [g6, s11]; exact h.hs

/-- From the call on: `Fr`, with `out` and the working space written too. -/
structure Fr2 (s u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = fr s :: s.wr
  hi : ∀ r ∈ hiRegs, u.gpr r = s.gpr r
  mem : Frame [kR s, oR s, sR s] s.mem u.mem
  sv : Spill.Saved (fb s) s.gpr saved u.mem
  ls : u.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr

/-- The outcome of `vg_rsa_private_checked` of `em`, from the caller's
buffers. -/
abbrev privOut (s : State) (em : List Byte) (u : State) : Prop :=
  Spec.Rsa.writtenOutcome u.mem (s.gpr .r3) (s.gpr .r6).toNat ((u.gpr .r3).setWidth 32)
    (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) em
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 2).toNat))

/-- After the call. -/
structure AtRet (s u : State) (em : List Byte) : Prop extends Fr2 s u where
  r28 : u.gpr .r28 = s.gpr .r6
  out : privOut s em u

theorem call_covers {s t : State} {em : List Byte} (h : SPre pc s) (A : AtCall pc s t em) :
    Covers (callRd pc s ++ callWr s) (t.rd ++ t.wr) ∧ Covers (callWr s) t.wr := by
  have hk := h.k2
  obtain pl := psa_le (pc := pc)
  obtain hOo : (⟨s.gpr .r3, (s.gpr .r6).toNat⟩ : Region) = oR s := by simp only [oR, h.h4]
  obtain hw : Covers (callWr s) t.wr := by
    rw [A.wr, h.hwr, ← hOo]
    exact Covers.of_mem fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  rw [A.rd, A.wr, h.hrd]
  obtain hleft : r ∈ rdL pc s → Covers [r] (rdL pc s ++ fr s :: s.wr) := fun h =>
    Covers.left (Covers.of_mem fun r' hr' => by rw [List.mem_singleton.mp hr']; exact h)
  simp only [callRd, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hp) | rfl
  · exact hleft (by simp [rdL])
  · exact hleft (by simp [rdL])
  · exact Covers.right (Covers.one (in_fr s _ (by decide) (by unfold oEM frameBytes; omega_using [hk])))
  · exact hleft (by simp [rdL])
  · exact hleft (by simp [rdL])
  · exact hleft (by simp [rdL])
  · exact hleft (by simp [rdL])
  · exact hleft (by simp [rdL])
  · cases pc
    · simp at hp
    · simp only [↓reduceIte, List.mem_singleton] at hp
      subst hp; exact hleft (by simp [rdL])
  · exact Covers.right (Covers.one (in_fr s _ (by decide) (by unfold frameBytes; omega_using [pl])))

theorem priv_sdepth : sdepth Impl.Rsa.PPC64LE.Priv.code = Impl.Rsa.PPC64LE.Priv.frameBytes := by decide +kernel

theorem privP_sdepth : sdepth Impl.Rsa.PPC64LE.Priv.codeP = Impl.Rsa.PPC64LE.Priv.frameBytes := by decide +kernel

/-- With `pc`, the facts of `pre` at the call. -/
theorem preX_entry {s t : State} {em : List Byte} (h : SPre true s) (X : PreX s) (A : AtCall true s t em) :
    Rsa.PPC64LE.Priv.PreX (callE true s t) := by
  obtain sa := fun i (hi : i < 14) => callE_stackArg A (i := i) hi
  have hsp : (callE true s t).sp = fb s := A.sp
  obtain fbt := fb_toNat h
  have sp2 := h.sp2
  simp only [↓reduceIte] at sp2
  unfold frameBytes at fbt
  obtain hPre : Rsa.PPC64LE.Priv.preR (callE true s t) = preR s := by
    simp only [Rsa.PPC64LE.Priv.preR, sa 12 (by decide), sa 13 (by decide)]
  obtain hO : Rsa.PPC64LE.Priv.oR (callE true s t) = oR s := by
    simp only [Rsa.PPC64LE.Priv.oR, callE_gpr (pc := true) s t (r := .r3), callE_gpr (pc := true) s t (r := .r4),
      A.r3, A.r4, oR, h.h4]
  obtain hS : Rsa.PPC64LE.Priv.sR (callE true s t) = sR s := by
    simp only [Rsa.PPC64LE.Priv.sR, sa 10 (by decide), sa 11 (by decide)]
  obtain hK : Rsa.PPC64LE.Priv.kR (callE true s t) = ⟨kb s, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := by
    simp only [Rsa.PPC64LE.Priv.kR, Rsa.PPC64LE.Priv.fb, hsp, fb_eq, BitVec.add_sub_cancel]
  obtain cs' : Region.Sub ⟨kb s, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (kR s) := by
    have := callee_sub s; rwa [fb_eq, BitVec.add_sub_cancel] at this
  refine ⟨by rw [hO, hPre]; exact X.oP, by rw [hS, hPre]; exact X.sP, by rw [hK, hPre]; exact X.kP.sub_left cs',
    ?_, ?_, ?_, ?_⟩
  · rw [sa 12 (by decide), sa 13 (by decide)]; exact X.wP
  · rw [sa 13 (by decide), sa 1 (by decide), sa 3 (by decide), callE_gpr (pc := true) s t (r := .r6), A.r6]
    exact X.pl
  · rw [hsp]; omega_using [fbt]
  · have hb := fun {p : Addr} {len : Nat} (hd : Region.Disjoint ⟨p, len⟩ (kR s)) (hl : len ≤ 2 ^ 64) =>
      bytes_of_frame (s := s) (rs := [kR s]) A.mem (p := p) (len := len)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl
    obtain hw := VG.Proof.Rsa.PPC64LE.Priv.words_of_frame A.mem (p := stackArg s 13) (n := (stackArg s 14).toNat)
      (fun r hr => by rw [List.mem_singleton.mp hr, Nat.mul_comm]; exact X.kP.symm) (by have := X.wP; omega_using [this])
    simp only [Rsa.PPC64LE.Priv.PreHyp, State.withRegions_mem, State.callEntry_mem,
      callE_gpr (pc := true) s t (r := .r5), callE_gpr (pc := true) s t (r := .r6), A.r5, A.r6, sa 0 (by decide),
      sa 1 (by decide), sa 2 (by decide), sa 3 (by decide), sa 12 (by decide), sa 13 (by decide), hw]
    rw [hb h.kn.symm (by have := h.wn; omega_using []), hb h.kp.symm (by have := h.wp; omega_using []),
      hb h.kq.symm (by have := h.wq; omega_using [])]
    exact X.hyp rfl

/-- The call of `vg_rsa_private_checked`, or with `pc` of
`vg_rsa_private_checked_precomputed`. -/
theorem call_priv {s t : State} {em : List Byte} (h : SPre pc s) (X : pc = true → PreX s) (A : AtCall pc s t em) :
    WP isa (privCall pc) t fun u => u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧
      Frame (callWr s ++ [below (fb s) Impl.Rsa.PPC64LE.Priv.frameBytes]) t.mem u.mem ∧
      (∀ r ∈ preserved, u.gpr r = t.gpr r) ∧
      Rsa.PPC64LE.Priv.fnPost (callE pc s t) (u.withRegions (callRd pc s) (callWr s)) := by
  obtain ⟨hc, hw⟩ := call_covers h A
  cases pc with
  | false =>
    refine WP.callAny (k := Rsa.PPC64LE.Priv.fnContract) Rsa.PPC64LE.Priv.code_correct
      (Rsa.PPC64LE.Priv.pre_of_preP (preP_entry h A)) hc hw (fun u hrd hwr hsp hf hpres hpost => ?_)
      (by rw [priv_sdepth]; decide)
    rw [priv_sdepth, A.sp] at hf
    exact ⟨hrd, hwr, hsp, hf, hpres, hpost⟩
  | true =>
    refine WP.callAny (k := Rsa.PPC64LE.Priv.fnContractP) Rsa.PPC64LE.Priv.codeP_correct
      (Rsa.PPC64LE.Priv.pre_of_prePX (preP_entry h A) (preX_entry h (X rfl) A)) hc hw
      (fun u hrd hwr hsp hf hpres hpost => ?_) (by rw [privP_sdepth]; decide)
    rw [privP_sdepth, A.sp] at hf
    exact ⟨hrd, hwr, hsp, hf, hpres, hpost⟩

theorem call_ok {s t : State} {em : List Byte} (h : SPre pc s) (X : pc = true → PreX s) (A : AtCall pc s t em)
    {Q : State → Prop} (hQ : ∀ u, AtRet s u em → Q u) : WP isa (privCall pc) t Q := by
  have hk := h.k2
  obtain hOo : (⟨s.gpr .r3, (s.gpr .r6).toNat⟩ : Region) = oR s := by simp only [oR, h.h4]
  obtain cs := callee_sub s
  refine WP.mono (call_priv h X A) fun u ⟨hrd, hwr, hsp, hf, hpres, hpost⟩ => hQ u ?_
  have hb : below (fb s) Impl.Rsa.PPC64LE.Priv.frameBytes =
      ⟨fb s - BitVec.ofNat 64 Impl.Rsa.PPC64LE.Priv.frameBytes, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := rfl
  rw [hb] at hf
  simp only [callWr, List.cons_append, List.nil_append, hOo] at hf
  have hp : ∀ r ∈ preserved, u.gpr r = t.gpr r := hpres
  obtain ap : ∀ {d : Nat}, d + 8 ≤ frameBytes → ∀ r ∈ [oR s, sR s, (⟨fb s - BitVec.ofNat 64
      Impl.Rsa.PPC64LE.Priv.frameBytes, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ : Region)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := by
    intro d hd r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.ko.sub_left (frame_sub s hd)
    · exact h.ks.sub_left (frame_sub s hd)
    · rw [fb_eq, BitVec.add_sub_cancel, Offset.add_add]
      exact Offset.disjoint_base _ (by omega_using []) (by unfold frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega_using [hd])
  refine ⟨⟨hsp.trans A.sp, hrd.trans A.rd, hwr.trans A.wr, fun r hr => (hp r (by revert r; decide)).trans
    (A.hi r hr), ?_, A.sv.frame hf fun p hp' r hr =>
      ap (by have := saved_offs p hp'; unfold oSave frameBytes at *; omega_using [this]) r hr, ?_⟩,
    (hp _ (by decide)).trans A.r28, ?_⟩
  · refine A.mem.sub (fun r hr => ?_) |>.trans (hf.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self .., cs⟩
  · rw [hf.readW (Region.contains_self _ _) (ap (by decide)) (by decide)]; exact A.ls
  · have sa := fun i (hi : i < 12) => callE_stackArg A (i := i) (lt_nCall hi)
    simp only [Rsa.PPC64LE.Priv.fnPost, State.withRegions_mem,
      State.withRegions_gpr, State.callEntry_mem, callE_gpr (pc := pc) s t (r := .r3),
      callE_gpr (pc := pc) s t (r := .r5), callE_gpr (pc := pc) s t (r := .r6), callE_gpr (pc := pc) s t (r := .r7),
      callE_gpr (pc := pc) s t (r := .r8), callE_gpr (pc := pc) s t (r := .r9),
      A.r3, A.r5, A.r6, A.r7, A.r8, A.r9, sa 0 (by decide), sa 1 (by decide), sa 2 (by decide), sa 3 (by decide),
      sa 4 (by decide), sa 6 (by decide), sa 8 (by decide), Nat.reduceAdd, A.em] at hpost
    obtain hb := fun {p : Addr} {len : Nat} (hd : Region.Disjoint ⟨p, len⟩ (kR s)) (hl : len ≤ 2 ^ 64) =>
      bytes_of_frame (s := s) (rs := [kR s]) A.mem (p := p) (len := len)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl
    rw [hb h.kn.symm (by have := h.wn; omega_using []), hb h.ke.symm (by have := h.we; omega_using []),
      hb h.kp.symm (by have := h.wp; omega_using []), hb h.kq.symm (by have := h.wq; omega_using []),
      hb (h.h6 ▸ h.kdp.symm) (by have := h.wdp; omega_using []), hb (h.h8 ▸ h.kdq.symm) (by have := h.wdq; omega_using []),
      hb (h.h10 ▸ h.kqi.symm) (by have := h.wqi; omega_using [])] at hpost
    exact hpost

end VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

end

end

/-! ### `RsaPkcs1Sig.PPC64LE.SignTail`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_sign` on PPC64LE: zeros and the restores

`zeroLoop` writes zeros (`zero_ok`): to `out` when the encoding fails
(`zeroOut_ok`), and over `EM` after the call (`wipe_ok`). Then the restores
give back our caller's registers (`restore_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.Sign VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.PPC64LE (wp_stb wp_addi wp_subi wp_nil ofNat_succ')

variable {pc : Bool}

/-- `zeroLoop` writes `n` zeros from `r7 = p`, counted down in `r8`. -/
theorem zero_ok {s : State} {p : Addr} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h7 : s.gpr .r7 = p) (h8 : s.gpr .r8 = BitVec.ofNat 64 n) (h0 : (s.gpr .r0).setWidth 8 = 0)
    (hw : ∀ i < n, InRegions s.wr (p + BitVec.ofNat 64 i) 1) :
    WP isa zeroLoop s fun t =>
      RsaPkcs1Sig.PPC64LE.Keep [.r7, .r8] s t ∧ t.mem = writeBytes s.mem p (List.replicate n 0) := by
  refine WP.mono (Proof.Bignum.PPC64LE.wp_countdown (cnt := .r8) hn' hn
    (fun i t => RsaPkcs1Sig.PPC64LE.Keep [.r7, .r8] s t ∧ t.mem = writeBytes s.mem p (List.replicate i 0) ∧
      t.gpr .r7 = p + BitVec.ofNat 64 i) ?_
    ⟨RsaPkcs1Sig.PPC64LE.Keep.refl _ _, by simp [writeBytes_nil], by simp [h7]⟩ h8)
    fun t h => ⟨h.1, h.2.1⟩
  intro i hi t ⟨hK, hm, h7'⟩ _
  have hA : InRegions t.wr (t.gpr .r7 + BitVec.ofNat 64 0) 1 := by
    rw [h7', hK.wr, BitVec.add_zero]; exact hw _ hi
  refine wp_stb rfl hA fun s₁ m₁ => ?_
  refine wp_addi fun s₂ o₂ e₂ => ?_
  refine wp_subi fun s₃ o₃ e₃ => wp_nil ?_
  have hK' : RsaPkcs1Sig.PPC64LE.Keep [.r7, .r8] t s₃ := (m₁.keep.trans (o₂.keep.trans o₃.keep)).mono
  refine ⟨⟨(hK.trans hK').mono, ?_, ?_⟩, ?_⟩
  · rw [o₃.mem, o₂.mem, m₁.mem, hK.get .r0, h0, h7', BitVec.add_zero, hm, List.replicate_succ',
      writeBytes_snoc _ _ _ _ (by simp; omega_using [hn', hi])]
    simp
  · rw [o₃.get .r7, e₂, m₁.gpr, h7', ofNat_succ']
  · rw [e₃, o₂.get .r8, m₁.gpr]

theorem gpr_ofNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by simp

/-- `out` is in the regions it may write. -/
theorem out_in {s : State} (h : SPre pc s) {i : Nat} (hi : i < (s.gpr .r6).toNat) :
    InRegions (fr s :: s.wr) (s.gpr .r3 + BitVec.ofNat 64 i) 1 := by
  rw [h.hwr]
  exact ⟨oR s, by simp, Offset.contains_base _ (by rw [h.h4]; omega_using [hi]) (by have := h.wo; omega_using [hi])⟩

theorem Fr.fr2 {s t : State} (F : Fr s t) : Fr2 s t :=
  ⟨F.sp, F.rd, F.wr, F.hi, F.mem.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩,
    F.sv, F.ls⟩

/-- Zeros to `out`, once the encoding failed. -/
theorem zeroOut_ok {s u : State} (h : SPre pc s) (A : AtAft s u) (h3 : u.gpr .r3 = 0) :
    WP isa zeroOut u fun v => Fr2 s v ∧ v.gpr .r3 = 0 ∧
      Spec.Rsa.bytesAt v.mem (s.gpr .r3) (s.gpr .r6).toNat = List.replicate (s.gpr .r6).toNat 0 := by
  have hk := h.k2
  have hk1 := h.k1
  unfold zeroOut
  refine WP.seq (WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r7, .r8, .r0] (Q := fun w =>
    w.gpr .r7 = s.gpr .r3 ∧ w.gpr .r8 = BitVec.ofNat 64 (s.gpr .r6).toNat ∧ w.gpr .r0 = 0 ∧ w.mem = u.mem) ?_ rfl)
    fun w ⟨⟨w7, w8, w0, wm⟩, kw⟩ => ?_)
  · prun [A.r26, A.r28, BitVec.or_self, Impl.AesGcm.PPC64LE.mov]
    exact ⟨gpr_ofNat _, rfl⟩
  refine WP.mono (zero_ok (by omega_using [hk1]) (by omega_using []) w7 w8 (by rw [w0]; rfl) fun i hi => by
    rw [kw.wr, A.wr]; exact out_in h hi) fun v ⟨kv, vm⟩ => ?_
  have hO : (oR s).Contains (s.gpr .r3) (List.replicate (s.gpr .r6).toNat (0 : Byte)).length := by
    rw [List.length_replicate, ← h.h4]; exact Region.contains_self _ _
  have fo : Frame [oR s] u.mem v.mem := by rw [vm, wm]; exact writeBytes_frame _ _ _ hO
  refine ⟨⟨kv.sp.trans (kw.sp.trans A.sp), kv.rd.trans (kw.rd.trans A.rd), kv.wr.trans (kw.wr.trans A.wr),
    fun r hr => (kv.gpr r (by revert r; decide)).trans ((kw.gpr r (by revert r; decide)).trans (A.hi r hr)),
    (A.fr2.mem).trans (fo.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩),
    A.sv.frame fo fun p hp r hr => by
      rw [List.mem_singleton.mp hr]; exact h.ko.sub_left (frame_sub s (by have := saved_offs p hp; unfold oSave frameBytes at *; omega_using [this])),
    ?_⟩, ?_, ?_⟩
  · rw [fo.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact h.ko.sub_left (frame_sub s (by decide))) (by decide)]; exact A.ls
  · rw [kv.gpr _ (by decide), kw.gpr _ (by decide)]; exact h3
  · rw [vm, wm]
    have := Proof.RsaPkcs1Sig.bytesAt_writeBytes u.mem (s.gpr .r3) (List.replicate (s.gpr .r6).toNat (0 : Byte))
      (by simp; omega_using [])
    rwa [List.length_replicate] at this

theorem wo_congr {m m' : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (hb : Spec.Rsa.bytesAt m' out k = Spec.Rsa.bytesAt m out k) (h : Spec.Rsa.writtenOutcome m out k r o) :
    Spec.Rsa.writtenOutcome m' out k r o := by
  cases o <;> simp only [Spec.Rsa.writtenOutcome, hb] at h ⊢ <;> exact h

/-- `EM` overwritten with zeros, after the call. -/
theorem wipe_ok {s u : State} {em : List Byte} (h : SPre pc s) (R : AtRet s u em) :
    WP isa wipe u fun v => Fr2 s v ∧ privOut s em v := by
  have hk := h.k2
  have hk1 := h.k1
  have c1 : oEM < 2 ^ 15 := by decide
  unfold wipe
  refine WP.seq (WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r7, .r8, .r0] (Q := fun w =>
    w.gpr .r7 = fb s + BitVec.ofNat 64 oEM ∧ w.gpr .r8 = BitVec.ofNat 64 (s.gpr .r6).toNat ∧ w.gpr .r0 = 0 ∧
      w.mem = u.mem) ?_ rfl) fun w ⟨⟨w7, w8, w0, wm⟩, kw⟩ => ?_)
  · prun [exec_addSp0, R.sp, R.r28, BitVec.or_self, Impl.AesGcm.PPC64LE.mov,
      exec_addi (show Reg.r12 ≠ .r0 by decide) c1]
    exact ⟨gpr_ofNat _, rfl⟩
  refine WP.mono (zero_ok (by omega_using [hk1]) (by omega_using []) w7 w8 (by rw [w0]; rfl) fun i hi => by
    rw [kw.wr, R.wr]; exact em_in h _ hi) fun v ⟨kv, vm⟩ => ?_
  have hE : (emR s).Contains (fb s + BitVec.ofNat 64 oEM) (List.replicate (s.gpr .r6).toNat (0 : Byte)).length := by
    rw [List.length_replicate]; exact Region.contains_self _ _
  have fe : Frame [emR s] u.mem v.mem := by rw [vm, wm]; exact writeBytes_frame _ _ _ hE
  refine ⟨⟨kv.sp.trans (kw.sp.trans R.sp), kv.rd.trans (kw.rd.trans R.rd), kv.wr.trans (kw.wr.trans R.wr),
    fun r hr => (kv.gpr r (by revert r; decide)).trans ((kw.gpr r (by revert r; decide)).trans (R.hi r hr)),
    R.mem.trans (fe.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., em_sub h⟩),
    R.sv.frame fe fun p hp r hr => below_em h (by have := saved_offs p hp; unfold oSave oEM at *; omega_using [this]) hr, ?_⟩, ?_⟩
  · rw [fe.readW (Region.contains_self _ _) (fun r hr => below_em h (by decide) hr) (by decide)]; exact R.ls
  · have hb : Spec.Rsa.bytesAt v.mem (s.gpr .r3) (s.gpr .r6).toNat = Spec.Rsa.bytesAt u.mem (s.gpr .r3) (s.gpr .r6).toNat :=
      bytes_of_frame (s := u) fe (fun r hr => by
        rw [List.mem_singleton.mp hr, show (⟨s.gpr .r3, (s.gpr .r6).toNat⟩ : Region) = oR s by simp only [oR, h.h4]]
        exact (h.ko.sub_left (em_sub h)).symm) (by omega_using [])
    show Spec.Rsa.writtenOutcome _ _ _ ((v.gpr .r3).setWidth 32) _
    rw [kv.gpr _ (by decide), kw.gpr _ (by decide)]
    exact wo_congr hb R.out

/-- The restores. -/
theorem restore_ok {s w : State} (F : Fr2 s w) :
    WP isa (.block restore) w fun v =>
      (∀ r ∈ preserved, v.gpr r = s.gpr r) ∧ v.lr = s.lr ∧ v.sp = fb s ∧ v.mem = w.mem ∧ v.gpr .r3 = w.gpr .r3 := by
  have iLr : InRegions (w.rd ++ w.wr) (fb s + BitVec.ofNat 64 oLr) 8 := by
    rw [F.wr]; exact in_fr' s _ _ (by decide) (by decide)
  have c1 : oLr < 2 ^ 15 := by decide
  have c2 : oLr % 4 = 0 := by decide
  rw [restore_eq]
  refine WP.block_append_iff.mpr (WP.mono (Q := fun v => v = { ((w.write .r12 w.sp).write .r0
      (w.mem.readW (fb s + BitVec.ofNat 64 oLr) 64)) with lr := w.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 })
    ?_ fun v e => ?_)
  · prun [exec_addSp0, F.sp, iLr, c1, c2, exec_mtlr]
  · subst e
    refine WP.mono (Spill.restore_wp (b := .r12) (B := fb s) (by decide) (by simp [State.write, F.sp])
      saved_ho (by decide) (fun p hp => by
        have := saved_offs p hp
        show InRegions (w.rd ++ w.wr) _ 8
        rw [F.wr]; exact in_fr' s _ _ (by unfold oSave at this; omega_using [this]) (by unfold oSave at this; unfold frameBytes; omega_using [this]))
      F.sv) fun v R => ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · rcases preserved_split hr with hs | hs
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
        exact R.gpr p hp
      · have : r ∉ saved.map Prod.fst := by revert r; decide
        rw [R.other r this]
        have h12 : r ≠ .r12 := by revert r; decide
        have h0 : r ≠ .r0 := by revert r; decide
        simp only [State.write, h12, h0, ite_false]
        exact F.hi r hs
    · rw [R.lr]; exact F.ls
    · rw [R.sp]; exact F.sp
    · rw [R.mem]; rfl
    · rw [R.other _ (by decide)]; simp [State.write]

end VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

end

end


/-!
# `vg_rsa_pkcs1_sign` on PPC64LE: correctness

The blocks and the call in order (`code_correct`), from the frame's push to
its pop, to the outcome of `signId` on the registers and the stack
(`fnPost`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.Sign

variable {pc : Bool}

/-- The outcome, on the registers and the stack. -/
def fnPost (s s' : State) : Prop :=
  Spec.Rsa.writtenOutcome s'.mem (s.gpr .r3) (s.gpr .r6).toNat ((s'.gpr .r3).setWidth 32)
    (Spec.RsaPkcs1Sig.signId (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 2).toNat)
      ((s.gpr .r9).setWidth 32).toNat (hashOf s))

/-- `signId` from the encoding. -/
theorem signId_eq (s : State) :
    Spec.RsaPkcs1Sig.signId (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 2).toNat)
      ((s.gpr .r9).setWidth 32).toNat (hashOf s) =
    match encOut s with
    | some em => Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) em
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 2).toNat)
    | none => .invalid := by
  simp only [Spec.RsaPkcs1Sig.signId, encOut, RsaPkcs1Sig.PPC64LE.encodeId, Spec.RsaPkcs1Sig.sign,
    Proof.RsaPkcs1Sig.bytesAt_length]
  cases Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .r9).setWidth 32).toNat with
  | none => rfl
  | some h => cases Spec.RsaPkcs1Sig.encode h (hashOf s) (s.gpr .r6).toNat <;> rfl

theorem freed_sp (b : Nat) (s : State) : (freed b s).sp = s.sp + BitVec.ofNat 64 b := rfl
theorem freed_lr (b : Nat) (s : State) : (freed b s).lr = s.lr := rfl
theorem freed_gpr (b : Nat) (s : State) : (freed b s).gpr = s.gpr := rfl
theorem freed_mem (b : Nat) (s : State) : (freed b s).mem = s.mem := rfl

/-- After the encoding: zeros and 0 if it failed, else the signature, and `EM`
overwritten. -/
theorem afterEnc_ok {s u : State} (h : SPre pc s) (X : pc = true → PreX s) (B : AtAft s u) :
    WP isa (afterEnc pc) u fun v => Fr2 s v ∧ fnPost s v := by
  unfold afterEnc fnPost
  rw [signId_eq]
  have he := B.enc
  revert he
  cases encOut s with
  | none =>
    intro h3
    refine WP.ite true (by rw [eval_zero, h3]; rfl) (fun _ => WP.mono (zeroOut_ok h B h3)
      fun v ⟨F, v3, vb⟩ => ⟨F, by rw [v3]; exact ⟨rfl, vb⟩⟩) (fun h => absurd h (by decide))
  | some em =>
    intro ⟨h3, hb⟩
    refine WP.ite false (by rw [eval_zero, h3]; rfl) (fun h => absurd h (by decide)) fun _ => ?_
    refine WP.seq (WP.mono (callArgs_ok h B hb) fun t₃ C => ?_)
    refine WP.seq (call_ok h X C fun t₄ R => WP.mono (wipe_ok h R) fun v ⟨F, o⟩ => ⟨F, o⟩)

/-- `writtenOutcome` reads the memory only in the output. -/
private theorem writtenOutcome_congr {m m' : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (hb : Spec.Rsa.bytesAt m' out k = Spec.Rsa.bytesAt m out k) (h : Spec.Rsa.writtenOutcome m out k r o) :
    Spec.Rsa.writtenOutcome m' out k r o := by
  cases o <;> simp only [Spec.Rsa.writtenOutcome, hb] at h ⊢ <;> exact h

theorem codeG_correct (s : State) (h : SPre pc s) (X : pc = true → PreX s) :
    WP isa (codeG pc) s fun t => abiPreserved s t ∧ fnPost s t := by
  have hk := h.k2
  unfold codeG
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := h.sp1; unfold stackBytes at this; omega_using [this]) ?_
  unfold body
  refine WP.seq (WP.mono (setup_ok h) fun t₁ A => ?_)
  refine WP.seq (WP.mono (enc_ok h A) fun t₂ B => ?_)
  refine WP.seq (Q := fun _ => _) (WP.mono (Q := fun v => Fr2 s v ∧ fnPost s v) ?_ fun v ⟨F, hp⟩ =>
    WP.mono (restore_ok F) fun w ⟨wp, wl, ws, wm, w3⟩ mL _ fl => ?_)
  · exact afterEnc_ok h X B
  · -- The `free` loses the frame's bytes, which lie apart from the output.
    have hb : Spec.Rsa.bytesAt mL (s.gpr .r3) (s.gpr .r6).toNat =
        Spec.Rsa.bytesAt (freed frameBytes w).mem (s.gpr .r3) (s.gpr .r6).toNat := by
      rw [freed_mem]
      have hfb : frameBytes ≤ stackBytes := by unfold stackBytes; omega_using []
      exact List.map_congr_left fun i hi => lost_byte fl (R := oR s)
        (h.ko.symm.sub_right (Offset.sub_below _ hfb (by omega_using [hfb])))
        (by show i < (s.gpr .r4).toNat; have h₁ := List.mem_range.mp hi; have h₂ := h.h4; omega_using [h₁, h₂])
    refine ⟨abiPreserved_lost ⟨fun r hr => ?_, ?_, ?_⟩, writtenOutcome_congr hb (?_ : fnPost s _)⟩
    · rw [freed_gpr]; exact wp r hr
    · rw [freed_sp, ws]; exact BitVec.sub_add_cancel _ _
    · rw [freed_lr]; exact wl
    · unfold fnPost at hp ⊢
      rw [freed_mem, freed_gpr, wm, w3]; exact hp

theorem code_correct (s : State) (hpre : (Spec.RsaPkcs1Sig.signContract abi stackBytes).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ fnPost s t :=
  codeG_correct s (sPre_of hpre) nofun

end VG.Proof.RsaPkcs1Sig.PPC64LE.Sign
