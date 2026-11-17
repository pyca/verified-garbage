module

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
public import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Rsa.Octets
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.Proof.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtFront
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCorrect
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreFn
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Impl.Rsa.PPC64LE.Priv
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Rsa.PPC64LE.PrivResult`, which this module and modules that import it used -/

section

/-! ### `Rsa.PPC64LE.PrivCmp`, which this module and modules that import it used -/

section

/-! ### `Rsa.PPC64LE.PrivPubCall`, which this module and modules that import it used -/

section

/-! ### `Rsa.PPC64LE.PrivPre`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_private_checked` on PPC64LE: the precondition

`PreP s`: the shared contract's precondition (`privateCheckedContract`, with
the stack of the frame, `frameBytes`), by name (`preP_of`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv

theorem stackArgs_twelve (s : State) :
    List.map (stackArg s) (List.range 12) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11] := rfl

/-! ## The buffers -/

abbrev oR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
abbrev nR (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
abbrev iR (s : State) : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
abbrev pR (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
abbrev qR (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
abbrev dpR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
abbrev dqR (s : State) : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
abbrev qiR (s : State) : Region := ⟨stackArg s 8, (stackArg s 9).toNat⟩
abbrev sR (s : State) : Region := ⟨stackArg s 10, (stackArg s 11).toNat * 8⟩
/-- The stack arguments: 12, or with `pc` (`vg_rsa_private_checked_precomputed`) 14. -/
abbrev aR (pc : Bool) (s : State) : Region := ⟨stackArgAddr s 0, if pc then 112 else 96⟩
/-- With `pc`, the key's precomputed values, `pre_len` words. -/
abbrev preR (s : State) : Region := ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩

/-- The buffers the function reads. -/
abbrev rdL (pc : Bool) (s : State) : List Region :=
  [nR s, eR s, iR s, pR s, qR s, dpR s, dqR s, qiR s] ++ (if pc then [preR s] else []) ++ [aR pc s]

/-- The frame's base: the stack pointer in the frame. -/
abbrev fb (s : State) : Addr := s.sp - BitVec.ofNat 64 frameBytes

/-- The stack the function uses: the frame. -/
abbrev kR (s : State) : Region := ⟨fb s, frameBytes⟩

/-- What the code needs of `privateCheckedContract.pre`, by name. -/
structure PreP (pc : Bool) (s : State) : Prop where
  sp1 : frameBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + 192 ≤ 2 ^ 64
  hrd : s.rd = rdL pc s
  hwr : s.wr = [oR s, sR s]
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  oi : (oR s).Disjoint (iR s)
  op : (oR s).Disjoint (pR s)
  oq : (oR s).Disjoint (qR s)
  odp : (oR s).Disjoint (dpR s)
  odq : (oR s).Disjoint (dqR s)
  oqi : (oR s).Disjoint (qiR s)
  os : (oR s).Disjoint (sR s)
  oa : (oR s).Disjoint (aR pc s)
  ns : (nR s).Disjoint (sR s)
  es : (eR s).Disjoint (sR s)
  is : (iR s).Disjoint (sR s)
  ps : (pR s).Disjoint (sR s)
  qs : (qR s).Disjoint (sR s)
  dps : (dpR s).Disjoint (sR s)
  dqs : (dqR s).Disjoint (sR s)
  qis : (qiR s).Disjoint (sR s)
  sa : (sR s).Disjoint (aR pc s)
  ko : (kR s).Disjoint (oR s)
  kn : (kR s).Disjoint (nR s)
  ke : (kR s).Disjoint (eR s)
  ki : (kR s).Disjoint (iR s)
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
  wi : (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64
  wp : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wq : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wdp : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64
  wdq : (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64
  wqi : (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64
  ws : (stackArg s 10).toNat + (stackArg s 11).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .r6).toNat
  k2 : (s.gpr .r6).toNat ≤ 1024
  h4 : (s.gpr .r4).toNat = (s.gpr .r6).toNat
  h10 : (s.gpr .r10).toNat = (s.gpr .r6).toNat
  e1 : 1 ≤ (s.gpr .r8).toNat
  e2 : (s.gpr .r8).toNat ≤ (s.gpr .r6).toNat
  p1 : 1 ≤ (stackArg s 1).toNat
  p2 : (stackArg s 1).toNat < (s.gpr .r6).toNat
  q1 : 1 ≤ (stackArg s 3).toNat
  q2 : (stackArg s 3).toNat < (s.gpr .r6).toNat
  h5 : (stackArg s 5).toNat = (stackArg s 1).toNat
  h9 : (stackArg s 9).toNat = (stackArg s 1).toNat
  h7 : (stackArg s 7).toNat = (stackArg s 3).toNat
  hs : Spec.Rsa.scratchWords (s.gpr .r6).toNat ≤ (stackArg s 11).toNat

theorem preP_of {s : State} (h : (Proof.Rsa.privateCheckedContract abi frameBytes).pre s) : PreP false s := by
  have e : frameBytes = 3327 + 1 := rfl
  rw [e] at h
  sig_pre [Proof.Rsa.privateCheckedContract, Proof.Rsa.privateCheckedSig, abi, argRegs,
    stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp1, sp2, hrd, hwr, on, oe, oi, op, oq, odp, odq, oqi, os, oa, ns, es, is, ps, qs, dps, dqs, qis, sa,
    ko, kn, ke, ki, kp, kq, kdp, kdq, kqi, ks, ka, wo, wn, we, wi, wp, wq, wdp, wdq, wqi, ws, ⟨k1, k2⟩, h4, h10,
    e1, e2, p1, p2, q1, q2, h5, h9, h7, hs⟩ := h
  exact ⟨sp1, by omega_using [sp2], hrd, hwr, on, oe, oi, op, oq, odp, odq, oqi, os, oa, ns, es, is, ps, qs, dps, dqs, qis, sa,
    ko, kn, ke, ki, kp, kq, kdp, kdq, kqi, ks, ka, wo, wn, we, wi, wp, wq, wdp, wdq, wqi, ws, k1, k2, h4, h10, e1,
    e2, p1, p2, q1, q2, h5, h9, h7, hs⟩

theorem pre_of_preP {s : State} (h : PreP false s) : (Proof.Rsa.privateCheckedContract abi frameBytes).pre s := by
  obtain ⟨sp1, sp2, hrd, hwr, on, oe, oi, op, oq, odp, odq, oqi, os, oa, ns, es, is, ps, qs, dps, dqs, qis, sa,
    ko, kn, ke, ki, kp, kq, kdp, kdq, kqi, ks, ka, wo, wn, we, wi, wp, wq, wdp, wdq, wqi, ws, k1, k2, h4, h10, e1,
    e2, p1, p2, q1, q2, h5, h9, h7, hs⟩ := h
  have e : frameBytes = 3327 + 1 := rfl
  rw [e]
  sig_pre [Proof.Rsa.privateCheckedContract, Proof.Rsa.privateCheckedSig, abi, argRegs, stackArgs_twelve,
    List.append_eq, List.range, List.range.loop]
  exact ⟨sp1, by omega_using [sp2], hrd, hwr, on, oe, oi, op, oq, odp, odq, oqi, os, oa, ns, es, is, ps, qs, dps, dqs, qis, sa,
    ko, kn, ke, ki, kp, kq, kdp, kdq, kqi, ks, ka, wo, wn, we, wi, wp, wq, wdp, wdq, wqi, ws, ⟨k1, k2⟩, h4, h10,
    e1, e2, p1, p2, q1, q2, h5, h9, h7, hs⟩

end VG.Proof.Rsa.PPC64LE.Priv

end

end

/-! ### `Rsa.PPC64LE.PrivPreCall`, which only this module used -/

section

/-! ### `Rsa.PPC64LE.PrivCrt`, which only this module used -/

section

/-! ### `Rsa.PPC64LE.PrivSetup`, which only this module used -/

section

/-! ### `Rsa.PPC64LE.PrivFrame`, which only this module used -/

section

/-!
# `vg_rsa_private_checked` on PPC64LE: the frame

The frame (`Impl/Rsa/PPC64LE/Priv.lean`) is all of the stack the function
uses, `kR`, from its base `fb`; the push makes its local variable space `fr`
writable. `saveRegs_ok`: the saves of `r24`–`r29` and of the return address.
`restore_ok`: the restores give back the caller's registers.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)

/-! ## Addresses -/

/-- The frame's local variable space, which its push makes writable. -/
abbrev fr (s : State) : Region := ⟨fb s + BitVec.ofNat 64 32, frameBytes - 32⟩

theorem fb_toNat {s : State} (h : frameBytes ≤ s.sp.toNat) : (fb s).toNat + frameBytes = s.sp.toNat := by
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega_using [h]

/-- A region of the frame is in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    Region.Sub ⟨fb s + BitVec.ofNat 64 d, n⟩ (kR s) := Offset.sub_base _ h

theorem frame_contains (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    (kR s).Contains (fb s + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by unfold frameBytes at h; omega_using [h])

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

/-- A call's stack arguments, in the frame. -/
theorem stackArgAddr_in (t : State) (j : Nat) :
    stackArgAddr t j = t.sp + BitVec.ofNat 64 (96 + 8 * j) := by
  rw [stackArgAddr, show 32 + 8 * (8 + j) = 96 + 8 * j by omega_using []]

theorem stackArgAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, Nat.add_zero]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, show 32 + 8 * 8 + 8 * j = 32 + 8 * (8 + j) by omega_using []]

theorem in_aR {s : State} {j : Nat} (hj : j < 12) : (aR pc s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; cases pc <;> exact Offset.contains_base _ (by simp only [Bool.false_eq_true, ↓reduceIte]; omega_using [hj]) (by omega_using [hj])

/-! ## The saves -/

/-- The slots of our caller's `r24`–`r29`. -/
def saved : List (Reg × Nat) :=
  [(.r24, oSave), (.r25, oSave + 8), (.r26, oSave + 16), (.r27, oSave + 24), (.r28, oSave + 32),
    (.r29, oSave + 40)]

/-- The callee-saved registers other than `r24`–`r29`. -/
def hiRegs : List Reg := [.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r30, .r31]

theorem save_eq : save = ([.addSp .r12 0] : List Instr) ++ Spill.saveCode .r12 saved ++
    ([.mflr .r0, .store .d .r0 .r12 oLr] : List Instr) ++
    ([.logic .or .r24 .r3 .r3, .logic .or .r25 .r5 .r5, .logic .or .r26 .r6 .r6, .logic .or .r27 .r7 .r7,
      .logic .or .r28 .r8 .r8, .logic .or .r29 .r9 .r9] : List Instr) :=
  rfl

theorem restore_eq :
    restore = ([.addSp .r12 0, .load .d .r0 .r12 oLr, .mtlr .r0] : List Instr) ++ Spill.restoreCode .r12 saved :=
  rfl

theorem saved_offs : ∀ p ∈ saved, oSave ≤ p.2 ∧ p.2 + 8 ≤ oSave + 48 := by decide

theorem saved_ho : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide

theorem preserved_split {r : Reg} (h : r ∈ preserved) : r ∈ saved.map Prod.fst ∨ r ∈ hiRegs := by
  revert r; decide

end VG.Proof.Rsa.PPC64LE.Priv

end

end


/-!
# `vg_rsa_private_checked` on PPC64LE: up to the call of `vg_rsa_private_crt`

From the state after the frame's push: the saves, the values kept in
`r24`–`r29`, the call's arguments, and its ten stack arguments copied from
ours (`setup_ok`, into `AtCrt`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)
open VG.PPC64LE.RegUpd (gpr_write_self gpr_write_of_ne mem_write)

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

/-- At the call of `vg_rsa_private_crt`. -/
structure AtCrt (s t : State) : Prop extends Fr s t where
  r3 : t.gpr .r3 = fb s + BitVec.ofNat 64 oM
  r4 : t.gpr .r4 = s.gpr .r6
  r5 : t.gpr .r5 = s.gpr .r5
  r6 : t.gpr .r6 = s.gpr .r6
  r7 : t.gpr .r7 = s.gpr .r9
  r8 : t.gpr .r8 = s.gpr .r6
  r9 : t.gpr .r9 = stackArg s 0
  r10 : t.gpr .r10 = stackArg s 1
  r12 : t.gpr .r12 = fb s
  r24 : t.gpr .r24 = s.gpr .r3
  r25 : t.gpr .r25 = s.gpr .r5
  r26 : t.gpr .r26 = s.gpr .r6
  r27 : t.gpr .r27 = s.gpr .r7
  r28 : t.gpr .r28 = s.gpr .r8
  r29 : t.gpr .r29 = s.gpr .r9
  psa : ∀ i < 10, t.mem.readW (fb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = stackArg s (2 + i)

/-- The frame's push stores the back chain at its base. -/
theorem fb_contains (s : State) : (kR s).Contains (fb s) 8 := by
  have := frame_contains s (d := 0) (n := 8) (by decide)
  rwa [BitVec.add_zero] at this

/-- The saves, from the state after the frame's push: `r12` holds the frame's
base, `r24`–`r29` and the return address are in their slots, and memory is
changed only in the frame. -/
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
    rw [uwr, u12]; exact in_fr s _ (by unfold oSave at this; omega_arith) (by unfold oSave frameBytes at *; omega_arith)
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
    exact f1.trans (Spill.saveMem_frame_base (fun p hp => by
      have := saved_offs p hp; unfold oSave frameBytes at *; omega_arith) (by decide) _ _ _)
  obtain sv₂ : Spill.Saved (fb s) s.gpr saved u₂.mem := by
    rw [m₂]
    refine fun p hp => (Spill.saveMem_saved (by decide) _ _ _ p hp).trans ?_
    obtain h12 : p.1 ≠ .r12 := by revert p; decide
    rw [← hu, gpr_write_of_ne _ _ h12]; rfl
  obtain hd : ∀ p ∈ saved, ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 oLr, 8⟩ : Region)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 p.2, 8⟩ r := fun p hp r hr => by
    have := saved_offs p hp
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by unfold oSave oLr at *; omega_arith)) (by unfold oSave at *; omega_arith) (by decide)
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

/-- Our stack argument `j` is in the arguments' region, apart from the frame. -/
theorem arg_read {s : State} (h : PreP pc s) {m : Mem} (hm : Frame [kR s] s.mem m) {j : Nat} (hj : j < 12) :
    m.readW (fb s + BitVec.ofNat 64 (arg j)) 64 = stackArg s j := by
  rw [← stackArgAddr_fb]
  exact hm.readW (in_aR (pc := pc) hj) (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.ka.symm) (by decide)

theorem arg_in {s t : State} (h : PreP pc s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 12) :
    InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 (arg j)) 8 := by
  rw [← stackArgAddr_fb, hrd, h.hrd]
  exact ⟨aR pc s, List.mem_append_left _ (by simp), in_aR hj⟩

/-- The values kept in `r24`–`r29` and `vg_rsa_private_crt`'s arguments in
registers. -/
theorem head_ok {s v : State} (h : PreP pc s) (F : Fr s v) (h12 : v.gpr .r12 = fb s)
    (hg : ∀ r, r ≠ .r12 → r ≠ .r0 → v.gpr r = s.gpr r) :
    WP isa (.block (([.logic .or .r24 .r3 .r3, .logic .or .r25 .r5 .r5, .logic .or .r26 .r6 .r6,
      .logic .or .r27 .r7 .r7, .logic .or .r28 .r8 .r8, .logic .or .r29 .r9 .r9] : List Instr) ++
      ([.addi .r3 .r12 oM, .logic .or .r4 .r26 .r26, .logic .or .r7 .r29 .r29, .logic .or .r8 .r26 .r26,
        .load .d .r9 .r12 (arg 0), .load .d .r10 .r12 (arg 1)] : List Instr))) v fun w =>
      (w.gpr .r3 = fb s + BitVec.ofNat 64 oM ∧ w.gpr .r4 = s.gpr .r6 ∧ w.gpr .r7 = s.gpr .r9 ∧
        w.gpr .r8 = s.gpr .r6 ∧ w.gpr .r9 = stackArg s 0 ∧ w.gpr .r10 = stackArg s 1 ∧
        w.gpr .r24 = s.gpr .r3 ∧ w.gpr .r25 = s.gpr .r5 ∧ w.gpr .r26 = s.gpr .r6 ∧ w.gpr .r27 = s.gpr .r7 ∧
        w.gpr .r28 = s.gpr .r8 ∧ w.gpr .r29 = s.gpr .r9 ∧ w.mem = v.mem) ∧
      Keep [.r24, .r25, .r26, .r27, .r28, .r29, .r3, .r4, .r7, .r8, .r9, .r10] v w := by
  obtain a0 := arg_read h F.mem (j := 0) (by decide)
  obtain a1 := arg_read h F.mem (j := 1) (by decide)
  obtain i0 := arg_in h F.rd (j := 0) (by decide)
  obtain i1 := arg_in h F.rd (j := 1) (by decide)
  obtain c0 : arg 0 < 2 ^ 15 := by decide
  obtain c1 : arg 1 < 2 ^ 15 := by decide
  obtain d0 : arg 0 % 4 = 0 := by decide
  obtain d1 : arg 1 % 4 = 0 := by decide
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  prun [c0, c1, d0, d1, i0, i1, a0, a1, h12, hg .r3 (by decide) (by decide), hg .r5 (by decide) (by decide),
    hg .r6 (by decide) (by decide), hg .r7 (by decide) (by decide), hg .r8 (by decide) (by decide),
    hg .r9 (by decide) (by decide), BitVec.or_self,
    exec_addi (show Reg.r12 ≠ .r0 by decide) (show oM < 2 ^ 15 by decide)]

/-- The Parameter Save Area of the calls. -/
abbrev psaR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 96, 80⟩

/-- After copying the first `n` stack arguments, from `w`. -/
structure CI (s w : State) (n : Nat) (t : State) : Prop where
  keep : Keep [.r0] w t
  mem : Frame [psaR s] w.mem t.mem
  psa : ∀ i < n, t.mem.readW (fb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = stackArg s (2 + i)

theorem copy_step {s w : State} (h : PreP pc s) (hw12 : w.gpr .r12 = fb s) (hrd : w.rd = s.rd)
    (hwr : w.wr = fr s :: s.wr) (hm : Frame [kR s] s.mem w.mem) {n : Nat} (hn : n < 10) {t : State}
    (hc : CI s w n t) : WP isa (.block (argCopy n)) t (CI s w (n + 1)) := by
  obtain t12 : t.gpr .r12 = fb s := (hc.keep.gpr _ (by decide)).trans hw12
  obtain psa_sub : Region.Sub (psaR s) (kR s) := frame_sub s (by decide)
  obtain hmt : Frame [kR s] s.mem t.mem := hm.trans (hc.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, psa_sub⟩)
  obtain hin : InRegions (t.rd ++ t.wr) (t.gpr .r12 + BitVec.ofNat 64 (arg (2 + n))) 8 := by
    rw [t12]; exact arg_in h (hc.keep.rd.trans hrd) (by omega_arith)
  obtain hv : t.mem.readW (t.gpr .r12 + BitVec.ofNat 64 (arg (2 + n))) 64 = stackArg s (2 + n) := by
    rw [t12]; exact arg_read h hmt (by omega_arith)
  obtain ho : InRegions t.wr (t.gpr .r12 + BitVec.ofNat 64 (96 + 8 * n)) 8 := by
    rw [t12, hc.keep.wr, hwr]; exact in_fr s _ (by omega_arith) (by unfold frameBytes; omega_arith)
  obtain harg : arg (2 + n) < 2 ^ 15 ∧ arg (2 + n) % 4 = 0 := by unfold arg frameBytes; omega_arith
  apply WP.of_runBlock
  simp only [argCopy, runBlock_cons, runStep_some, exec_load_d (show Reg.r12 ≠ .r0 by decide) harg hin]
  rw [exec_store_d (show Reg.r12 ≠ .r0 by decide) ⟨by omega_arith, by omega_arith⟩
    (by rw [gpr_write_of_ne _ _ (show Reg.r12 ≠ .r0 by decide)]; exact ho)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  rw [gpr_write_of_ne _ _ (show Reg.r12 ≠ .r0 by decide), gpr_write_self, mem_write, hv, t12]
  refine ⟨⟨fun r hr => ?_, hc.keep.rd, hc.keep.wr, hc.keep.sp, hc.keep.lr⟩, ?_, fun i hi => ?_⟩
  · show (t.write .r0 _).gpr r = w.gpr r
    rw [gpr_write_of_ne _ _ (by simpa using hr)]; exact hc.keep.gpr r hr
  · exact hc.mem.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith) (by decide))
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide)]
      exact hc.psa i hi
    · rw [Mem.readW_writeW_self64]

theorem copies_ok {s w : State} (h : PreP pc s) (hw12 : w.gpr .r12 = fb s) (hrd : w.rd = s.rd)
    (hwr : w.wr = fr s :: s.wr) (hm : Frame [kR s] s.mem w.mem) :
    WP isa (.block ((List.range 10).flatMap argCopy)) w (CI s w 10) :=
  wp_range_flatMap (M := isa) (CI s w) (fun _ _ hn hc => copy_step h hw12 hrd hwr hm hn hc) 10 (Nat.le_refl _) w
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem setup_ok {s : State} (h : PreP pc s) :
    WP isa (.block (save ++ crtArgs)) (allocated frameBytes s) (AtCrt s) := by
  obtain e : save ++ crtArgs = ([.addSp .r12 0] : List Instr) ++ Spill.saveCode .r12 saved ++
      ([.mflr .r0, .store .d .r0 .r12 oLr] : List Instr) ++
      ((([.logic .or .r24 .r3 .r3, .logic .or .r25 .r5 .r5, .logic .or .r26 .r6 .r6, .logic .or .r27 .r7 .r7,
        .logic .or .r28 .r8 .r8, .logic .or .r29 .r9 .r9] : List Instr) ++
      ([.addi .r3 .r12 oM, .logic .or .r4 .r26 .r26, .logic .or .r7 .r29 .r29, .logic .or .r8 .r26 .r26,
        .load .d .r9 .r12 (arg 0), .load .d .r10 .r12 (arg 1)] : List Instr)) ++
      (List.range 10).flatMap argCopy) := by
    rw [save_eq, crtArgs]; simp only [List.append_assoc]; rfl
  rw [e]
  refine save_ok fun v F h12 hg => ?_
  rw [WP.block_append_iff]
  refine WP.mono (head_ok h F h12 hg) fun w ⟨⟨w3, w4, w7, w8, w9, w10, w24, w25, w26, w27, w28, w29, wm⟩, kw⟩ => ?_
  obtain w12 : w.gpr .r12 = fb s := (kw.gpr _ (by decide)).trans h12
  refine WP.mono (copies_ok h w12 (kw.rd.trans F.rd) (kw.wr.trans F.wr) (by rw [wm]; exact F.mem))
    fun t hc => ?_
  have k := hc.keep
  obtain psa_sub : Region.Sub (psaR s) (kR s) := frame_sub s (by decide)
  obtain hd : ∀ {d n : Nat}, 96 + 80 ≤ d → d + n ≤ frameBytes →
      ∀ r ∈ [psaR s], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r :=
    fun hdn hdn' r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr hdn) (by unfold frameBytes at hdn'; omega_arith) (by decide)
  refine ⟨⟨k.sp.trans (kw.sp.trans F.sp), k.rd.trans (kw.rd.trans F.rd), k.wr.trans (kw.wr.trans F.wr),
    k.lr.trans (kw.lr.trans F.lr), fun r hr => ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, hc.psa⟩
  · rw [k.gpr _ (by revert r; decide), kw.gpr _ (by revert r; decide)]; exact F.hi r hr
  · have hm : Frame [kR s] w.mem t.mem := hc.mem.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, psa_sub⟩
    rw [wm] at hm
    exact F.mem.trans hm
  · have hm : Frame [psaR s] v.mem t.mem := by rw [← wm]; exact hc.mem
    exact F.sv.frame hm fun p hp => by
      have := saved_offs p hp; exact hd (by unfold oSave at this; omega_arith) (by unfold oSave frameBytes at *; omega_arith)
  · rw [hc.mem.readW (Region.contains_self _ _) (hd (by decide) (by decide)) (by decide), wm]; exact F.ls
  · rw [k.gpr _ (by decide)]; exact w3
  · rw [k.gpr _ (by decide)]; exact w4
  · rw [k.gpr _ (by decide), kw.gpr _ (by decide)]; exact hg _ (by decide) (by decide)
  · rw [k.gpr _ (by decide), kw.gpr _ (by decide)]; exact hg _ (by decide) (by decide)
  · rw [k.gpr _ (by decide)]; exact w7
  · rw [k.gpr _ (by decide)]; exact w8
  · rw [k.gpr _ (by decide)]; exact w9
  · rw [k.gpr _ (by decide)]; exact w10
  · exact (k.gpr _ (by decide)).trans w12
  · rw [k.gpr _ (by decide)]; exact w24
  · rw [k.gpr _ (by decide)]; exact w25
  · rw [k.gpr _ (by decide)]; exact w26
  · rw [k.gpr _ (by decide)]; exact w27
  · rw [k.gpr _ (by decide)]; exact w28
  · rw [k.gpr _ (by decide)]; exact w29

/-- Between the calls, from the entry state `s`: the frame, the values kept
in `r24`–`r29`, the other callee-saved registers as on entry, our caller's
registers and return address in their slots, and memory changed only in the
frame and the working space. -/
structure Mid (s u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = fr s :: s.wr
  r24 : u.gpr .r24 = s.gpr .r3
  r25 : u.gpr .r25 = s.gpr .r5
  r26 : u.gpr .r26 = s.gpr .r6
  r27 : u.gpr .r27 = s.gpr .r7
  r28 : u.gpr .r28 = s.gpr .r8
  r29 : u.gpr .r29 = s.gpr .r9
  hi : ∀ r ∈ hiRegs, u.gpr r = s.gpr r
  mem : Frame [kR s, sR s] s.mem u.mem
  sv : Spill.Saved (fb s) s.gpr saved u.mem
  ls : u.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr

/-- A buffer of the caller that the function does not write. -/
theorem bytes_of_frame {s : State} {rs : List Region} {m : Mem} (hf : Frame rs s.mem m) {p : Addr}
    {len : Nat} (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, len⟩ r) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) hd hl (List.mem_range.mp hi)

end VG.Proof.Rsa.PPC64LE.Priv

end

end


/-!
# `vg_rsa_private_checked` on PPC64LE: the call of `vg_rsa_private_crt`

By the callee's contract on its registers and stack (`Crt.fnContract`,
`Crt.fn_correct`): the regions it is narrowed to (`crtRd`, `crtWr`), its
precondition at the call (`crt_pre`), and the call (`crtCall_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)

/-- `m`, in the frame. -/
abbrev mR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oM, (s.gpr .r6).toNat⟩

/-- The regions the call reads and writes. -/
abbrev crtRd (s : State) : List Region :=
  [nR s, ⟨s.gpr .r9, (s.gpr .r6).toNat⟩, pR s, qR s, dpR s, dqR s, qiR s, psaR s]

abbrev crtWr (s : State) : List Region := [mR s, sR s]

/-- The call's narrowed entry state. -/
abbrev crtEntry (s t : State) : State := t.callEntry.withRegions (crtRd s) (crtWr s)

/-- The narrowed entry state of a call from `u`, with the regions `X` read
too. -/
abbrev crtEntryG (s u : State) (X : List Region) : State := u.callEntry.withRegions (crtRd s ++ X) (crtWr s)

theorem crtEntryG_stackArg {s t u : State} (A : AtCrt s t)
    (hpsa : ∀ i < 10, u.mem.readW (fb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = stackArg s (2 + i))
    (hsp : u.sp = t.sp) {X : List Region} {i : Nat} (hi : i < 10) :
    stackArg (crtEntryG s u X) i = stackArg s (2 + i) := by
  show u.mem.readW (stackArgAddr (crtEntryG s u X) i) 64 = _
  rw [stackArgAddr_in, show (crtEntryG s u X).sp = fb s from hsp.trans A.sp]
  exact hpsa i hi

theorem crtEntry_stackArg {s t : State} (A : AtCrt s t) {i : Nat} (hi : i < 10) :
    stackArg (crtEntry s t) i = stackArg s (2 + i) := by
  show t.mem.readW (stackArgAddr (crtEntry s t) i) 64 = _
  rw [stackArgAddr_in, show (crtEntry s t).sp = fb s from A.sp]
  exact A.psa i hi

/-- `vg_rsa_private_crt`'s precondition but its regions, at the call from `u`
(with `t`'s arguments), with the regions `X` read too. -/
theorem crt_preG {s t u : State} (h : PreP pc s) (A : AtCrt s t)
    (k : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10], u.gpr r = t.gpr r)
    (hpsa : ∀ i < 10, u.mem.readW (fb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = stackArg s (2 + i))
    (hsp : u.sp = t.sp) {X : List Region} :
    Proof.Bignum.PPC64LE.Crt.preCore (Proof.Bignum.PPC64LE.Crt.baseRd (crtEntryG s u X) ++ X) (crtEntryG s u X) := by
  obtain g : ∀ r, r ∉ linkRegs → r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] →
      (crtEntryG s u X).gpr r = t.gpr r := fun r h1 h2 => (State.callEntry_gpr u h1).trans (k r h2)
  obtain sa := fun i hi => crtEntryG_stackArg A hpsa hsp (X := X) (i := i) hi
  obtain hsp' : (crtEntryG s u X).sp = fb s := hsp.trans A.sp
  obtain ha : stackArgAddr (crtEntryG s u X) 0 = fb s + BitVec.ofNat 64 96 := by rw [stackArgAddr_in, hsp']
  simp only [Proof.Bignum.PPC64LE.Crt.preCore,
    Proof.Bignum.PPC64LE.Crt.baseRd, g .r3 (by decide) (by decide), g .r4 (by decide) (by decide),
    g .r5 (by decide) (by decide), g .r6 (by decide) (by decide), g .r7 (by decide) (by decide),
    g .r8 (by decide) (by decide), g .r9 (by decide) (by decide), g .r10 (by decide) (by decide),
    A.r3, A.r4, A.r5, A.r6, A.r7, A.r8, A.r9, A.r10, sa 0 (by decide), sa 1 (by decide), sa 2 (by decide),
    sa 3 (by decide), sa 4 (by decide), sa 5 (by decide), sa 6 (by decide), sa 7 (by decide), sa 8 (by decide),
    sa 9 (by decide), hsp', ha, State.withRegions_rd, State.withRegions_wr, Nat.reduceAdd]
  have hk := h.k2
  obtain fbt := fb_toNat h.sp1
  unfold frameBytes at fbt
  obtain ei : (⟨s.gpr .r9, (s.gpr .r6).toNat⟩ : Region) = iR s := by simp only [iR, h.h10]
  obtain mk : Region.Sub (mR s) (kR s) := frame_sub s (by unfold oM frameBytes; omega_arith)
  obtain pk : Region.Sub (psaR s) (kR s) := frame_sub s (by decide)
  obtain mp : (mR s).Disjoint (psaR s) := Offset.disjoint _ (.inr (by decide)) (by unfold oM; omega_arith) (by decide)
  rw [ei]
  refine ⟨by omega_arith, trivial, trivial, h.kn.sub_left mk, h.ki.sub_left mk, h.kp.sub_left mk, h.kq.sub_left mk,
    h.kdp.sub_left mk, h.kdq.sub_left mk, h.kqi.sub_left mk, h.ks.sub_left mk, mp, h.ns, h.is, h.ps, h.qs,
    h.dps, h.dqs, h.qis, (h.ks.sub_left pk).symm, ?_, h.wn, by rw [← h.h10]; exact h.wi, h.wp, h.wq, h.wdp, h.wdq, h.wqi, h.ws,
    ⟨h.k1, h.k2⟩, trivial, trivial, h.p1, h.p2, h.q1, h.q2, h.h5, h.h9, h.h7, h.hs⟩
  · rw [Offset.toNat_add_ofNat]; unfold oM at *; omega_arith

theorem crt_pre {s t : State} (h : PreP pc s) (A : AtCrt s t) :
    Proof.Bignum.PPC64LE.Crt.fnContract.pre (crtEntry s t) := by
  have := crt_preG (X := []) h A (fun _ _ => rfl) A.psa rfl
  simp only [List.append_nil] at this
  exact this

/-- The bytes of `m` after the call: `vg_rsa_private_crt`'s result for the
caller's buffers, and its status. -/
abbrev crtOut (s u : State) : Prop :=
  Spec.Rsa.written u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat ((u.gpr .r3).setWidth 32)
    (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat))

/-- The frame below `m` is apart from what the call writes. -/
theorem below_apart {s : State} (h : PreP pc s) {d : Nat} (hd : d + 8 ≤ oM) {r : Region} (hr : r ∈ crtWr s) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (.inl hd) (by unfold oM at hd; omega_arith) (by have := h.k2; unfold oM; omega_arith)
  · exact h.ks.sub_left (frame_sub s (by unfold oM frameBytes at *; omega_arith))

theorem crt_noFrames : Impl.Bignum.PPC64LE.Crt.crt.noFrames = true := by decide +kernel

theorem crt_covers {s t : State} (h : PreP pc s) (A : AtCrt s t) :
    Covers (crtRd s ++ crtWr s) (t.rd ++ t.wr) ∧ Covers (crtWr s) t.wr := by
  have hk := h.k2
  obtain ei : (⟨s.gpr .r9, (s.gpr .r6).toNat⟩ : Region) = iR s := by simp only [iR, h.h10]
  obtain hw : Covers (crtWr s) t.wr := by
    rw [A.wr, h.hwr]
    refine Covers.of_forall fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Covers.one (in_fr s _ (by unfold oM; omega_arith) (by unfold oM frameBytes; omega_arith))
    · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  rw [A.rd, A.wr, h.hrd]
  simp only [crtRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_left 7
  · exact Covers.right (Covers.one (in_fr s _ (by decide) (by decide)))
  all_goals exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp [ei])

theorem crtCall_ok {s t : State} (h : PreP pc s) (A : AtCrt s t) {Q : State → Prop}
    (hQ : ∀ u, Mid s u → crtOut s u → Q u) : WP isa crtCall t Q := by
  have hk := h.k2
  obtain mk : Region.Sub (mR s) (kR s) := frame_sub s (by unfold oM frameBytes; omega_arith)
  obtain ei : (⟨s.gpr .r9, (s.gpr .r6).toNat⟩ : Region) = iR s := by simp only [iR, h.h10]
  obtain ⟨hc, hw⟩ := crt_covers h A
  unfold crtCall
  refine WP.call (k := Proof.Bignum.PPC64LE.Crt.fnContract) Proof.Bignum.PPC64LE.Crt.fn_correct (crt_pre h A) hc hw
    (fun u hrd hwr hsp hf hpres _ hpost => hQ u ?_ ?_) crt_noFrames
  · have hp : ∀ r ∈ preserved, u.gpr r = t.gpr r := hpres
    refine ⟨hsp.trans A.sp, hrd.trans A.rd, hwr.trans A.wr, (hp _ (by decide)).trans A.r24,
      (hp _ (by decide)).trans A.r25, (hp _ (by decide)).trans A.r26, (hp _ (by decide)).trans A.r27,
      (hp _ (by decide)).trans A.r28, (hp _ (by decide)).trans A.r29,
      fun r hr => (hp r (by revert r; decide)).trans (A.hi r hr), ?_, A.sv.frame hf fun p hp' r hr => below_apart h (by
        have := saved_offs p hp'; unfold oSave oM at *; omega_arith) hr, ?_⟩
    · refine (A.mem.mono fun r hr => ?_).trans (hf.sub fun r hr => ?_)
      · rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..
      · simp only [crtWr, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self .., mk⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
    · rw [hf.readW (Region.contains_self _ _) (fun r hr => below_apart h (by decide) hr) (by decide)]; exact A.ls
  · have g : ∀ r, r ∉ linkRegs → (crtEntry s t).gpr r = t.gpr r := fun r hr => State.callEntry_gpr t hr
    obtain sa := fun i hi => crtEntry_stackArg A (i := i) hi
    simp only [Proof.Bignum.PPC64LE.Crt.fnContract, Proof.Bignum.PPC64LE.Crt.postCore, g .r3 (by decide),
      g .r5 (by decide), g .r6 (by decide),
      g .r7 (by decide), g .r9 (by decide), g .r10 (by decide), A.r3, A.r5, A.r6, A.r7, A.r9, A.r10,
      sa 0 (by decide), sa 1 (by decide), sa 2 (by decide), sa 4 (by decide), sa 6 (by decide),
      State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem, Nat.reduceAdd] at hpost
    obtain hb := fun {p : Addr} {len : Nat} (hd : Region.Disjoint ⟨p, len⟩ (kR s)) (hl : len ≤ 2 ^ 64) =>
      bytes_of_frame (s := s) (rs := [kR s]) A.mem (p := p) (len := len)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl
    rw [hb h.kn.symm (by have := h.wn; omega_arith), hb (ei ▸ h.ki.symm) (by have := h.k2; omega_arith),
      hb h.kp.symm (by have := h.wp; omega_arith), hb h.kq.symm (by have := h.wq; omega_arith),
      hb (h.h5 ▸ h.kdp.symm) (by have := h.wdp; omega_arith), hb (h.h7 ▸ h.kdq.symm) (by have := h.wdq; omega_arith),
      hb (h.h9 ▸ h.kqi.symm) (by have := h.wqi; omega_arith)] at hpost
    exact hpost

end VG.Proof.Rsa.PPC64LE.Priv

end

end


/-!
# `vg_rsa_private_checked` on PPC64LE: the call of `vg_rsa_public_precompute`

The CRT's status kept in the frame (`preArgs_ok`, into `AtPre`), then the
call by the callee's contract on its registers (`Pre.fnContract`,
`Pre.fn_correct`): `n`'s values into the frame (`preCall_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)

theorem written_congr {m m' : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {o : Option (List Byte)}
    (hb : Spec.Rsa.bytesAt m' out k = Spec.Rsa.bytesAt m out k) (h : Spec.Rsa.written m out k r o) :
    Spec.Rsa.written m' out k r o := by
  cases o <;> simp only [Spec.Rsa.written, hb] at h ⊢ <;> exact h

/-- `m` and the CRT's status kept in the frame. -/
abbrev crtOutM (s u : State) : Prop :=
  Spec.Rsa.written u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat
    ((u.mem.readW (fb s + BitVec.ofNat 64 oSt) 64).setWidth 32)
    (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat))

/-- A word of the frame above the slots, in it. -/
theorem word_in {s : State} {d : Nat} (hd : oLr + 8 ≤ d) (hd' : d + 8 ≤ frameBytes) (rs : List Region) :
    InRegions (fr s :: rs) (fb s + BitVec.ofNat 64 d) 8 :=
  in_fr s rs (by unfold oLr at hd; omega_arith) hd'

/-- `Mid` is kept by a write of a word of the frame apart from the slots. -/
theorem Mid.store {s t : State} (M : Mid s t) {d : Nat} (hd : oLr + 8 ≤ d ∨ d + 8 ≤ oSave)
    (hd' : d + 8 ≤ frameBytes)
    (v : BitVec 64) {u : State} (hg : ∀ r ∈ preserved, u.gpr r = t.gpr r) (hsp : u.sp = t.sp)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hm : u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 d) v) :
    Mid s u := by
  obtain hd1 : ∀ {e : Nat}, oSave ≤ e → e + 8 ≤ oLr + 8 →
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 e, 8⟩ ⟨fb s + BitVec.ofNat 64 d, 8⟩ := fun he he' =>
    Offset.disjoint _ (by unfold oSave oLr at *; omega_arith) (by unfold oLr at he'; omega_arith)
      (by unfold frameBytes at hd'; omega_arith)
  obtain fw : Frame [⟨fb s + BitVec.ofNat 64 d, 8⟩] t.mem u.mem := by
    rw [hm]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hsp.trans M.sp, hrd.trans M.rd, hwr.trans M.wr, (hg _ (by decide)).trans M.r24,
    (hg _ (by decide)).trans M.r25, (hg _ (by decide)).trans M.r26, (hg _ (by decide)).trans M.r27,
    (hg _ (by decide)).trans M.r28, (hg _ (by decide)).trans M.r29,
    fun r hr => (hg r (by revert r; decide)).trans (M.hi r hr), ?_,
    M.sv.frame fw fun p hp r hr => by
      rw [List.mem_singleton.mp hr]
      have := saved_offs p hp
      exact hd1 this.1 (by unfold oSave oLr at *; omega_arith), ?_⟩
  · rw [hm]; exact M.mem.writeW (List.mem_cons_self ..) _ (frame_contains s hd')
  · rw [fw.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd1 (by decide) (by decide)) (by decide)]
    exact M.ls

/-- Our stack argument `j`, after the frame and the working space changed. -/
theorem arg_read2 {s : State} (h : PreP pc s) {m : Mem} (hm : Frame [kR s, sR s] s.mem m) {j : Nat} (hj : j < 12) :
    m.readW (fb s + BitVec.ofNat 64 (arg j)) 64 = stackArg s j := by
  rw [← stackArgAddr_fb]
  refine hm.readW (in_aR (pc := pc) hj) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.ka.symm
  · exact h.sa.symm

/-- At the call of `vg_rsa_public_precompute`. -/
structure AtPre (s u : State) : Prop extends Mid s u where
  crt : crtOutM s u
  r3 : u.gpr .r3 = fb s + BitVec.ofNat 64 oPre
  r4 : u.gpr .r4 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .r6).toNat)
  r5 : u.gpr .r5 = s.gpr .r5
  r6 : u.gpr .r6 = s.gpr .r6
  r7 : u.gpr .r7 = stackArg s 10
  r8 : u.gpr .r8 = stackArg s 11

theorem gpr_ofNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by simp

theorem preLen_val {k : Nat} (hk : k ≤ 1024) :
    (BitVec.ofNat 64 k + BitVec.ofNat 64 7) >>> 3 <<< 1 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords k) := by
  rw [Proof.Bignum.PPC64LE.Pre.ofNat_add7_shr3 k (by omega_arith), Proof.Bignum.PPC64LE.Pre.ofNat_shl1]; rfl

theorem preArgs_ok {s t : State} (h : PreP pc s) (M : Mid s t) (C : crtOut s t) :
    WP isa (.block preArgs) t (AtPre s) := by
  have hk := h.k2
  obtain e26 : t.gpr .r26 = BitVec.ofNat 64 (s.gpr .r6).toNat := M.r26.trans (gpr_ofNat _)
  obtain ho : InRegions t.wr (fb s + BitVec.ofNat 64 oSt) 8 := by
    rw [M.wr]; exact word_in (by decide) (by decide) _
  have rdm : t.rd = s.rd := M.rd
  obtain hrdw : ∀ {j : Nat}, j < 12 → (t.mem.writeW (fb s + BitVec.ofNat 64 oSt) (t.gpr .r3)).readW
      (fb s + BitVec.ofNat 64 (arg j)) 64 = stackArg s j := fun hj => by
    rw [Mem.readW_writeW_sep (Offset.sep _ (.inr (by unfold oSt arg frameBytes; omega_arith))
      (by unfold arg frameBytes; omega_arith) (by decide)) (by decide)]
    exact arg_read2 h M.mem hj
  obtain a10 := hrdw (j := 10) (by decide)
  obtain a11 := hrdw (j := 11) (by decide)
  obtain i10 := arg_in h rdm (j := 10) (by decide)
  obtain i11 := arg_in h rdm (j := 11) (by decide)
  obtain c1 : oSt < 2 ^ 15 := by decide
  obtain c2 : oSt % 4 = 0 := by decide
  obtain c3 : oPre < 2 ^ 15 := by decide
  obtain c4 : arg 10 < 2 ^ 15 := by decide
  obtain c5 : arg 11 < 2 ^ 15 := by decide
  obtain c6 : arg 10 % 4 = 0 := by decide
  obtain c7 : arg 11 % 4 = 0 := by decide
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r3, .r4, .r5, .r6, .r7, .r8] (Q := fun u =>
    u.gpr .r3 = fb s + BitVec.ofNat 64 oPre ∧
      u.gpr .r4 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .r6).toNat) ∧ u.gpr .r5 = s.gpr .r5 ∧
      u.gpr .r6 = s.gpr .r6 ∧ u.gpr .r7 = stackArg s 10 ∧ u.gpr .r8 = stackArg s 11 ∧
      u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oSt) (t.gpr .r3)) ?_ rfl) fun u ⟨⟨u3, u4, u5, u6, u7, u8, um⟩, k⟩ => ?_
  · unfold preArgs preLen
    prun [exec_addSp0, M.sp, ho, c1, c2, c3, c4, c5, c6, c7, i10, i11, a10, a11, e26, preLen_val hk, M.r25, M.r26,
      BitVec.or_self, exec_addi (show Reg.r12 ≠ .r0 by decide) c3, Impl.AesGcm.PPC64LE.mov]
    all_goals exact (gpr_ofNat _).symm
  · refine ⟨M.store (d := oSt) (.inl (by decide)) (by decide) _ (fun r hr => k.gpr r (by revert r; decide)) k.sp k.rd
      k.wr um, ?_, u3, u4, u5, u6, u7, u8⟩
    obtain hb : Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat =
        Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat := by
      simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      obtain hi := List.mem_range.mp hi
      rw [um]
      exact Frame.bytes (R := mR s) (Frame.writeW (Frame.refl [⟨fb s + BitVec.ofNat 64 oSt, 8⟩] t.mem)
        (List.mem_singleton_self _) _ (Region.contains_self _ _))
        (fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact Offset.disjoint _ (.inr (by decide)) (by unfold oM; omega_arith) (by decide))
        (show (s.gpr .r6).toNat ≤ 2 ^ 64 by omega_arith) hi
    show Spec.Rsa.written _ _ _ _ _
    rw [um, Mem.readW_writeW_self64, ← um]
    exact written_congr hb C

/-- `n`'s values, in the frame. -/
abbrev pwR (s : State) : Region :=
  ⟨fb s + BitVec.ofNat 64 oPre, Spec.Rsa.precomputedWords (s.gpr .r6).toNat * 8⟩

/-- The regions the call writes. -/
abbrev preWr (s : State) : List Region := [pwR s, sR s]

theorem pw_le {k : Nat} (hk : k ≤ 1024) : Spec.Rsa.precomputedWords k ≤ 256 := by
  unfold Spec.Rsa.precomputedWords Spec.Rsa.modulusWords; omega_arith

theorem pwR_sub {s : State} (h : PreP pc s) : Region.Sub (pwR s) (kR s) :=
  frame_sub s (by have := pw_le h.k2; unfold oPre frameBytes; omega_arith)

/-- The frame below `n`'s values is apart from what the call writes. -/
theorem below_pre {s : State} (h : PreP pc s) {d n : Nat} (hd : d + n ≤ oPre) {r : Region} (hr : r ∈ preWr s) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (.inl hd) (by unfold oPre at hd; omega_arith)
      (by have := pw_le h.k2; unfold oPre; omega_arith)
  · exact h.ks.sub_left (frame_sub s (by unfold oPre frameBytes at *; omega_arith))

/-- `n`'s values: computed (`publicPrecompute`, or zeros if they are
invalid), or, with `pc`, the first words of `pre`. -/
abbrev preVal (pc : Bool) (s : State) : List (BitVec 64) :=
  if pc then Spec.Rsa.wordsAt s.mem (stackArg s 12) (Spec.Rsa.precomputedWords (s.gpr .r6).toNat)
  else (Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)).getD
    (List.replicate (Spec.Rsa.precomputedWords (s.gpr .r6).toNat) 0)

/-- `n`'s values in the frame. -/
abbrev preW (pc : Bool) (s : State) (m : Mem) : Prop :=
  Spec.Rsa.wordsAt m (fb s + BitVec.ofNat 64 oPre) (Spec.Rsa.precomputedWords (s.gpr .r6).toNat) = preVal pc s

theorem preW_of {s : State} {r : BitVec 64} {m : Mem}
    (h : Proof.Bignum.PPC64LE.Pre.preOut (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (fb s + BitVec.ofNat 64 oPre) (Spec.Rsa.precomputedWords (s.gpr .r6).toNat) r m) : preW false s m := by
  simp only [preW, preVal, Bool.false_eq_true, ↓reduceIte]
  cases hw : Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) <;>
    simp only [Proof.Bignum.PPC64LE.Pre.preOut, hw] at h <;> exact h.2

/-- After `n`'s values. -/
structure AtPub (pc : Bool) (s u : State) : Prop extends Mid s u where
  crt : crtOutM s u
  pre : preW pc s u.mem

theorem pre_noFrames : Impl.Bignum.PPC64LE.Precompute.precompute.noFrames = true := by decide +kernel

theorem pre_covers {s t : State} (h : PreP pc s) (A : AtPre s t) :
    Covers ([nR s] ++ preWr s) (t.rd ++ t.wr) ∧ Covers (preWr s) t.wr := by
  have hk := h.k2
  obtain pwl := pw_le hk
  obtain hw : Covers (preWr s) t.wr := by
    rw [A.wr, h.hwr]
    refine Covers.of_forall fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Covers.one (in_fr s _ (by unfold oPre; omega_arith) (by unfold oPre frameBytes; omega_arith))
    · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp
  refine ⟨Covers.append_left (Covers.of_mem fun r hr => ?_) (Covers.right hw), hw⟩
  rw [List.mem_singleton.mp hr, A.rd, h.hrd]; simp

theorem pre_toNat {s : State} (h : PreP pc s) :
    (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .r6).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .r6).toNat := by
  have := pw_le h.k2
  rw [BitVec.toNat_ofNat]; omega_arith

theorem pre_pre {s t : State} (h : PreP pc s) (A : AtPre s t) :
    Proof.Bignum.PPC64LE.Pre.fnContract.pre (t.callEntry.withRegions [nR s] (preWr s)) := by
  have hk := h.k2
  obtain pk := pwR_sub h
  obtain pwl := pw_le hk
  obtain fbt := fb_toNat h.sp1
  unfold frameBytes at fbt
  obtain g : ∀ r, r ∉ linkRegs → (t.callEntry.withRegions [nR s] (preWr s)).gpr r = t.gpr r :=
    fun r hr => State.callEntry_gpr t hr
  simp only [Proof.Bignum.PPC64LE.Pre.fnContract, g .r3 (by decide), g .r4 (by decide), g .r5 (by decide),
    g .r6 (by decide), g .r7 (by decide), g .r8 (by decide), A.r3, A.r4, A.r5, A.r6, A.r7, A.r8, pre_toNat h,
    State.withRegions_rd, State.withRegions_wr, Proof.Bignum.PPC64LE.Pre.nR, Proof.Bignum.PPC64LE.Pre.preR,
    Proof.Bignum.PPC64LE.Pre.scrR]
  refine ⟨trivial, trivial, h.kn.sub_left pk, h.ks.sub_left pk, h.ns, ?_, h.wn, h.ws, ⟨h.k1, h.k2⟩, trivial, ?_⟩
  · rw [Offset.toNat_add_ofNat]; unfold oPre at *; omega_arith
  · have := h.hs; have := h.k1; unfold Spec.Rsa.scratchWords at *
    unfold Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords; omega_arith

theorem preCall_ok {s t : State} (h : PreP pc s) (A : AtPre s t) {Q : State → Prop}
    (hQ : ∀ u, AtPub false s u → Q u) : WP isa preCall t Q := by
  have hk := h.k2
  obtain pk := pwR_sub h
  obtain ⟨hc, hw⟩ := pre_covers h A
  obtain g : ∀ r, r ∉ linkRegs → (t.callEntry.withRegions [nR s] (preWr s)).gpr r = t.gpr r :=
    fun r hr => State.callEntry_gpr t hr
  obtain e4 := pre_toNat h
  obtain hn : Spec.Rsa.bytesAt t.mem (s.gpr .r5) (s.gpr .r6).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat :=
    bytes_of_frame A.mem (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.kn.symm
      · exact h.ns) (by have := h.wn; omega_arith)
  unfold preCall
  refine WP.call (k := Proof.Bignum.PPC64LE.Pre.fnContract) (rd := [nR s]) (wr := preWr s)
    Proof.Bignum.PPC64LE.Pre.fn_correct (pre_pre h A) hc hw
    (fun u hrd hwr hsp hf hpres _ hpost => hQ u ?_) pre_noFrames
  · have hp : ∀ r ∈ preserved, u.gpr r = t.gpr r := hpres
    obtain ft : Frame [kR s, sR s] s.mem u.mem := by
      refine (A.mem.trans (hf.sub fun r hr => ?_))
      simp only [preWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., pk⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
    obtain hm : Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat =
        Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat :=
      bytes_of_frame (s := t) hf (fun r hr => below_pre h (by unfold oM oPre; omega_arith) hr) (by omega_arith)
    obtain hst : u.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 :=
      hf.readW (Region.contains_self _ _) (fun r hr => below_pre h (by decide) hr) (by decide)
    refine ⟨⟨hsp.trans A.sp, hrd.trans A.rd, hwr.trans A.wr, (hp _ (by decide)).trans A.r24,
      (hp _ (by decide)).trans A.r25, (hp _ (by decide)).trans A.r26, (hp _ (by decide)).trans A.r27,
      (hp _ (by decide)).trans A.r28, (hp _ (by decide)).trans A.r29,
      fun r hr => (hp r (by revert r; decide)).trans (A.hi r hr), ft, A.sv.frame hf fun p hp' r hr => below_pre h (by
        have := saved_offs p hp'; unfold oSave oPre at *; omega_arith) hr, ?_⟩, ?_, ?_⟩
    · rw [hf.readW (Region.contains_self _ _) (fun r hr => below_pre h (by decide) hr) (by decide)]; exact A.ls
    · show Spec.Rsa.written _ _ _ _ _
      rw [hst]; exact written_congr hm A.crt
    · simp only [Proof.Bignum.PPC64LE.Pre.fnContract, g .r3 (by decide), g .r4 (by decide), g .r5 (by decide),
        g .r6 (by decide), A.r3, A.r4, A.r5, A.r6, e4, State.withRegions_mem, State.withRegions_gpr,
        State.callEntry_mem, hn] at hpost
      exact preW_of hpost

end VG.Proof.Rsa.PPC64LE.Priv

end

end


/-!
# `vg_rsa_private_checked` on PPC64LE: the call of `vg_rsa_public_precomputed_checked`

Its arguments (`pubArgs_ok`, into `AtPubC`), then the call by the callee's
contract on its registers and stack (`Pub.fnContract`, `Pub.fn_correct`):
`m^e mod n` into `out` (`pubCall_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)

/-- Words of a region apart from what changed. -/
theorem words_of_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 8 * n⟩ r) (hl : 8 * n ≤ 2 ^ 64) :
    Spec.Rsa.wordsAt m' p n = Spec.Rsa.wordsAt m p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  obtain hi := List.mem_range.mp hi
  exact hf.readW (Offset.contains_base p (by omega_arith) (by omega_arith)) hd (by decide)

/-- At the call of `vg_rsa_public_precomputed_checked`. -/
structure AtPubC (pc : Bool) (s u : State) : Prop extends Mid s u where
  crt : crtOutM s u
  pre : preW pc s u.mem
  r3 : u.gpr .r3 = s.gpr .r3
  r4 : u.gpr .r4 = s.gpr .r6
  r5 : u.gpr .r5 = fb s + BitVec.ofNat 64 oPre
  r6 : u.gpr .r6 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .r6).toNat)
  r7 : u.gpr .r7 = s.gpr .r7
  r8 : u.gpr .r8 = s.gpr .r8
  r9 : u.gpr .r9 = fb s + BitVec.ofNat 64 oM
  r10 : u.gpr .r10 = s.gpr .r6
  psa0 : u.mem.readW (fb s + BitVec.ofNat 64 96) 64 = stackArg s 10
  psa1 : u.mem.readW (fb s + BitVec.ofNat 64 104) 64 = stackArg s 11

theorem pubArgs_ok {s t : State} (h : PreP pc s) (A : AtPub pc s t) :
    WP isa (.block pubArgs) t (AtPubC pc s) := by
  have hk := h.k2
  obtain e26 : t.gpr .r26 = BitVec.ofNat 64 (s.gpr .r6).toNat := A.r26.trans (gpr_ofNat _)
  have rdm : t.rd = s.rd := A.rd
  obtain w0 : InRegions t.wr (fb s + BitVec.ofNat 64 96) 8 := by
    rw [A.wr]; exact in_fr s _ (by decide) (by decide)
  obtain w1 : InRegions t.wr (fb s + BitVec.ofNat 64 104) 8 := by
    rw [A.wr]; exact in_fr s _ (by decide) (by decide)
  obtain a10 : t.mem.readW (fb s + BitVec.ofNat 64 (arg 10)) 64 = stackArg s 10 := arg_read2 h A.mem (by decide)
  obtain a11 : (t.mem.writeW (fb s + BitVec.ofNat 64 96) (stackArg s 10)).readW
      (fb s + BitVec.ofNat 64 (arg 11)) 64 = stackArg s 11 := by
    rw [Mem.readW_writeW_sep (Offset.sep _ (.inr (by unfold arg frameBytes; omega_arith))
      (by unfold arg frameBytes; omega_arith) (by decide)) (by decide)]
    exact arg_read2 h A.mem (by decide)
  obtain i10 := arg_in h rdm (j := 10) (by decide)
  obtain i11 := arg_in h rdm (j := 11) (by decide)
  obtain c3 : oPre < 2 ^ 15 := by decide
  obtain c4 : arg 10 < 2 ^ 15 := by decide
  obtain c5 : arg 11 < 2 ^ 15 := by decide
  obtain c6 : arg 10 % 4 = 0 := by decide
  obtain c7 : arg 11 % 4 = 0 := by decide
  obtain c8 : oM < 2 ^ 15 := by decide
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]
    (Q := fun u =>
      u.gpr .r3 = s.gpr .r3 ∧ u.gpr .r4 = s.gpr .r6 ∧ u.gpr .r5 = fb s + BitVec.ofNat 64 oPre ∧
      u.gpr .r6 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .r6).toNat) ∧ u.gpr .r7 = s.gpr .r7 ∧
      u.gpr .r8 = s.gpr .r8 ∧ u.gpr .r9 = fb s + BitVec.ofNat 64 oM ∧ u.gpr .r10 = s.gpr .r6 ∧
      u.mem = (t.mem.writeW (fb s + BitVec.ofNat 64 96) (stackArg s 10)).writeW (fb s + BitVec.ofNat 64 104)
        (stackArg s 11)) ?_ rfl) fun u ⟨⟨u3, u4, u5, u6, u7, u8, u9, u10, um⟩, k⟩ => ?_
  · unfold pubArgs preLen
    prun [exec_addSp0, A.sp, w0, w1, c3, c4, c5, c6, c7, c8, i10, i11, a10, a11, e26, preLen_val hk, A.r24,
      A.r27, A.r28, BitVec.or_self, BitVec.add_zero, exec_addi (show Reg.r12 ≠ .r0 by decide) c3,
      exec_addi (show Reg.r12 ≠ .r0 by decide) c8, Impl.AesGcm.PPC64LE.mov]
    all_goals exact (gpr_ofNat _).symm
  · have hg : ∀ r ∈ preserved, u.gpr r = t.gpr r := fun r hr => k.gpr r (by revert r; decide)
    obtain M1 : Mid s { u with mem := t.mem.writeW (fb s + BitVec.ofNat 64 96) (stackArg s 10) } :=
      A.store (.inr (by decide)) (by decide) _ hg k.sp k.rd k.wr rfl
    obtain M2 : Mid s u := M1.store (d := 104) (.inr (by decide)) (by decide) _ (fun _ _ => rfl) rfl rfl rfl um
    obtain fw : Frame [⟨fb s + BitVec.ofNat 64 96, 8⟩, ⟨fb s + BitVec.ofNat 64 104, 8⟩] t.mem u.mem := by
      rw [um]
      exact Frame.writeW (Frame.writeW (Frame.refl [⟨fb s + BitVec.ofNat 64 96, 64 / 8⟩,
        ⟨fb s + BitVec.ofNat 64 104, 64 / 8⟩] t.mem) (List.mem_cons_self ..) _ (Region.contains_self _ _))
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
    obtain ap : ∀ {d n : Nat}, 112 ≤ d → d + n ≤ 2 ^ 64 → ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 96, 8⟩ : Region),
        ⟨fb s + BitVec.ofNat 64 104, 8⟩], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r := by
      intro d n hd hn r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inr (by omega_arith)) hn (by decide)
      · exact Offset.disjoint _ (.inr (by omega_arith)) hn (by decide)
    obtain pwl := pw_le hk
    refine ⟨M2, ?_, ?_, u3, u4, u5, u6, u7, u8, u9, u10, ?_, ?_⟩
    · show Spec.Rsa.written _ _ _ _ _
      rw [fw.readW (Region.contains_self _ _) (ap (by decide) (by decide)) (by decide)]
      exact written_congr (bytes_of_frame (s := t) fw (ap (by decide) (by omega_arith)) (by omega_arith)) A.crt
    · show Spec.Rsa.wordsAt _ _ _ = _
      rw [words_of_frame fw (ap (by decide) (by omega_arith)) (by omega_arith)]
      exact A.pre
    · rw [um, Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64]
    · rw [um, Mem.readW_writeW_self64]

/-- `out`, of `k` bytes. -/
abbrev outR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r6).toNat⟩

theorem outR_eq {s : State} (h : PreP pc s) : outR s = oR s := by simp only [outR, oR, h.h4]

/-- The regions the call reads and writes. -/
abbrev pubRd (s : State) : List Region := [pwR s, eR s, mR s, ⟨fb s + BitVec.ofNat 64 96, 16⟩]

abbrev pubWr (s : State) : List Region := [outR s, sR s]

/-- The frame is apart from what the call writes. -/
theorem frame_pub {s : State} (h : PreP pc s) {d n : Nat} (hd : d + n ≤ frameBytes) {r : Region}
    (hr : r ∈ pubWr s) : Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [outR_eq h]; exact h.ko.sub_left (frame_sub s hd)
  · exact h.ks.sub_left (frame_sub s hd)

/-- `m^e mod n` in `out`, if `n`'s values are valid. -/
abbrev pubOut (pc : Bool) (s u : State) : Prop :=
  ∀ ws, Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) = some ws → preVal pc s = ws →
    Spec.Rsa.written u.mem (s.gpr .r3) (s.gpr .r6).toNat ((u.gpr .r3).setWidth 32)
      (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
        (Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat))

/-- From the call of `vg_rsa_public_precomputed_checked` on: `Mid`, with
`out` written too. -/
structure Late (s u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = fr s :: s.wr
  r24 : u.gpr .r24 = s.gpr .r3
  r25 : u.gpr .r25 = s.gpr .r5
  r26 : u.gpr .r26 = s.gpr .r6
  r27 : u.gpr .r27 = s.gpr .r7
  r28 : u.gpr .r28 = s.gpr .r8
  r29 : u.gpr .r29 = s.gpr .r9
  hi : ∀ r ∈ hiRegs, u.gpr r = s.gpr r
  mem : Frame [kR s, oR s, sR s] s.mem u.mem
  sv : Spill.Saved (fb s) s.gpr saved u.mem
  ls : u.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr

/-- After the call of `vg_rsa_public_precomputed_checked`. -/
structure AtCmp (pc : Bool) (s u : State) : Prop extends Late s u where
  crt : crtOutM s u
  pub : pubOut pc s u

theorem pub_noFrames : Impl.Bignum.PPC64LE.PublicChecked.publicChecked.noFrames = true := by decide +kernel

/-- The call's narrowed entry state. -/
abbrev pubEntry (s t : State) : State := t.callEntry.withRegions (pubRd s) (pubWr s)

theorem pubEntry_sa {s t : State} (A : AtPubC pc s t) :
    stackArg (pubEntry s t) 0 = stackArg s 10 ∧ stackArg (pubEntry s t) 1 = stackArg s 11 := by
  have hsp : (pubEntry s t).sp = fb s := A.sp
  refine ⟨?_, ?_⟩
  · show t.mem.readW _ 64 = _; rw [stackArgAddr_in, hsp]; exact A.psa0
  · show t.mem.readW _ 64 = _; rw [stackArgAddr_in, hsp]; exact A.psa1

theorem pub_pre {s t : State} (h : PreP pc s) (A : AtPubC pc s t) :
    Proof.Bignum.PPC64LE.Pub.fnContract.pre (pubEntry s t) ∧ Covers (pubRd s ++ pubWr s) (t.rd ++ t.wr) ∧
      Covers (pubWr s) t.wr := by
  have hk := h.k2
  obtain pk := pwR_sub h
  obtain pwl := pw_le hk
  obtain mk : Region.Sub (mR s) (kR s) := frame_sub s (by unfold oM frameBytes; omega_arith)
  obtain fbt := fb_toNat h.sp1
  unfold frameBytes at fbt
  obtain hw : Covers (pubWr s) t.wr := by
    rw [A.wr, h.hwr, ← outR_eq h]
    exact Covers.of_mem fun r hr => by
      simp only [pubWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  obtain hc : Covers (pubRd s ++ pubWr s) (t.rd ++ t.wr) := by
    refine Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw)
    rw [A.rd, A.wr, h.hrd]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Covers.right (Covers.one (in_fr s _ (by decide) (by unfold oPre frameBytes; omega_arith)))
    · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
    · exact Covers.right (Covers.one (in_fr s _ (by decide) (by unfold oM frameBytes; omega_arith)))
    · exact Covers.right (Covers.one (in_fr s _ (by decide) (by decide)))
  obtain g : ∀ r, r ∉ linkRegs → (t.callEntry.withRegions (pubRd s) (pubWr s)).gpr r = t.gpr r :=
    fun r hr => State.callEntry_gpr t hr
  have hsp : (t.callEntry.withRegions (pubRd s) (pubWr s)).sp = fb s := A.sp
  obtain ha : stackArgAddr (t.callEntry.withRegions (pubRd s) (pubWr s)) 0 = fb s + BitVec.ofNat 64 96 := by
    rw [stackArgAddr_in, hsp]
  obtain sa0 : stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 0 = stackArg s 10 := by
    show t.mem.readW _ 64 = _; rw [ha]; exact A.psa0
  obtain sa1 : stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 1 = stackArg s 11 := by
    show t.mem.readW _ 64 = _; rw [stackArgAddr_in, hsp]; exact A.psa1
  obtain e6 : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .r6).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .r6).toNat := by
    rw [BitVec.toNat_ofNat]; omega_arith
  obtain psk : Region.Sub ⟨fb s + BitVec.ofNat 64 96, 16⟩ (kR s) := frame_sub s (by decide)
  refine ⟨?_, hc, hw⟩
  simp only [Proof.Bignum.PPC64LE.Pub.fnContract, Proof.Bignum.PPC64LE.Pub.stackArgs, g .r3 (by decide),
    g .r4 (by decide), g .r5 (by decide), g .r6 (by decide), g .r7 (by decide), g .r8 (by decide),
    g .r9 (by decide), g .r10 (by decide), A.r3, A.r4, A.r5, A.r6, A.r7, A.r8, A.r9, A.r10, e6, sa0, sa1, hsp,
    ha, State.withRegions_rd, State.withRegions_wr]
  rw [show (⟨s.gpr .r3, (s.gpr .r6).toNat⟩ : Region) = oR s from outR_eq h]
  refine ⟨by omega_arith, trivial, trivial, (h.ko.sub_left pk).symm, h.oe, (h.ko.sub_left mk).symm, h.os,
    (h.ko.sub_left psk).symm, h.ks.sub_left pk, h.es, h.ks.sub_left mk, (h.ks.sub_left psk).symm,
    h.h4 ▸ h.wo, ?_, h.we, ?_, h.ws, ⟨h.k1, h.k2⟩, trivial, trivial, h.e1, h.e2, ?_⟩
  · rw [Offset.toNat_add_ofNat]; unfold oPre at *; omega_arith
  · rw [Offset.toNat_add_ofNat]; unfold oM at *; omega_arith
  · have := h.hs; have := h.k1; unfold Spec.Rsa.scratchWords at *
    unfold Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords; omega_arith

theorem pubCall_ok {s t : State} (h : PreP pc s) (A : AtPubC pc s t) {Q : State → Prop}
    (hQ : ∀ u, AtCmp pc s u → Q u) : WP isa pubCall t Q := by
  have hk := h.k2
  obtain pwl := pw_le hk
  obtain ⟨hpre, hc, hw⟩ := pub_pre h A
  obtain g : ∀ r, r ∉ linkRegs → (t.callEntry.withRegions (pubRd s) (pubWr s)).gpr r = t.gpr r :=
    fun r hr => State.callEntry_gpr t hr
  obtain e6 : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .r6).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .r6).toNat := by
    rw [BitVec.toNat_ofNat]; omega_arith
  unfold pubCall
  refine WP.call (k := Proof.Bignum.PPC64LE.Pub.fnContract) (rd := pubRd s) (wr := pubWr s)
    Proof.Bignum.PPC64LE.Pub.fn_correct hpre hc hw
    (fun u hrd hwr hsp' hf hpres _ hpost => hQ u ?_) pub_noFrames
  · have hp : ∀ r ∈ preserved, u.gpr r = t.gpr r := hpres
    obtain ft : Frame [kR s, oR s, sR s] s.mem u.mem := by
      refine ((A.mem.sub fun r hr => ?_).trans (hf.sub fun r hr => ?_))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩
      · simp only [pubWr, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [outR_eq h]; exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩
    obtain hm : Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat =
        Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat :=
      bytes_of_frame (s := t) hf (fun r hr => frame_pub h (by unfold oM frameBytes; omega_arith) hr) (by omega_arith)
    refine ⟨⟨hsp'.trans A.sp, hrd.trans A.rd, hwr.trans A.wr, (hp _ (by decide)).trans A.r24,
      (hp _ (by decide)).trans A.r25, (hp _ (by decide)).trans A.r26, (hp _ (by decide)).trans A.r27,
      (hp _ (by decide)).trans A.r28, (hp _ (by decide)).trans A.r29,
      fun r hr => (hp r (by revert r; decide)).trans (A.hi r hr), ft, A.sv.frame hf fun p hp' r hr => frame_pub h (by
        have := saved_offs p hp'; unfold oSave frameBytes at *; omega_arith) hr, ?_⟩, ?_, ?_⟩
    · rw [hf.readW (Region.contains_self _ _) (fun r hr => frame_pub h (by decide) hr) (by decide)]; exact A.ls
    · show Spec.Rsa.written _ _ _ _ _
      rw [hf.readW (Region.contains_self _ _) (fun r hr => frame_pub h (by decide) hr) (by decide)]
      exact written_congr hm A.crt
    · intro ws hw hv
      obtain he : Spec.Rsa.bytesAt t.mem (s.gpr .r7) (s.gpr .r8).toNat =
          Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat :=
        bytes_of_frame A.mem (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact h.ke.symm
          · exact h.es) (by have := h.we; omega_arith)
      simp only [Proof.Bignum.PPC64LE.Pub.fnContract, g .r3 (by decide), g .r4 (by decide), g .r5 (by decide),
        g .r6 (by decide), g .r7 (by decide), g .r8 (by decide), g .r9 (by decide), A.r3, A.r4, A.r5, A.r6,
        A.r7, A.r8, A.r9, e6, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem, he] at hpost
      rw [hm]
      exact hpost _ (by simp [Spec.Rsa.bytesAt]) (by rw [A.pre, hv, hw])

end VG.Proof.Rsa.PPC64LE.Priv
end

end

/-!
# `vg_rsa_private_checked` on PPC64LE: the comparison

The public operation's status kept in the frame (`cmpArgs_ok`, into
`AtLoop`), then the comparison of `out` with the input (`compare_ok`): the
OR of their bytes' XORs (`cmpAcc`), zero exactly if they are equal.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)

/-- `Late` is kept by a write of a word of the frame apart from the slots. -/
theorem Late.store {s t : State} (M : Late s t) {d : Nat} (hd : oLr + 8 ≤ d ∨ d + 8 ≤ oSave)
    (hd' : d + 8 ≤ frameBytes)
    (v : BitVec 64) {u : State} (hg : ∀ r ∈ preserved, u.gpr r = t.gpr r) (hsp : u.sp = t.sp)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hm : u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 d) v) :
    Late s u := by
  have hd1 : ∀ {e : Nat}, oSave ≤ e → e + 8 ≤ oLr + 8 →
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 e, 8⟩ ⟨fb s + BitVec.ofNat 64 d, 8⟩ := fun he he' =>
    Offset.disjoint _ (by unfold oSave oLr at *; omega_arith) (by unfold oLr at he'; omega_arith)
      (by unfold frameBytes at hd'; omega_arith)
  have fw : Frame [⟨fb s + BitVec.ofNat 64 d, 8⟩] t.mem u.mem := by
    rw [hm]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hsp.trans M.sp, hrd.trans M.rd, hwr.trans M.wr, (hg _ (by decide)).trans M.r24,
    (hg _ (by decide)).trans M.r25, (hg _ (by decide)).trans M.r26, (hg _ (by decide)).trans M.r27,
    (hg _ (by decide)).trans M.r28, (hg _ (by decide)).trans M.r29,
    fun r hr => (hg r (by revert r; decide)).trans (M.hi r hr), ?_,
    M.sv.frame fw fun p hp r hr => by
      rw [List.mem_singleton.mp hr]
      have := saved_offs p hp
      exact hd1 this.1 (by unfold oSave oLr at *; omega_arith), ?_⟩
  · rw [hm]; exact M.mem.writeW (List.mem_cons_self ..) _ (frame_contains s hd')
  · rw [fw.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd1 (by decide) (by decide)) (by decide)]
    exact M.ls

/-- `m^e mod n` in `out` and the public operation's status kept in the
frame, if `n`'s values are valid. -/
abbrev pubOutM (pc : Bool) (s u : State) : Prop :=
  ∀ ws, Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) = some ws → preVal pc s = ws →
    Spec.Rsa.written u.mem (s.gpr .r3) (s.gpr .r6).toNat
      ((u.mem.readW (fb s + BitVec.ofNat 64 oEs) 64).setWidth 32)
      (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
        (Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat))

/-- At the comparison. -/
structure AtLoop (pc : Bool) (s u : State) : Prop extends Late s u where
  crt : crtOutM s u
  pub : pubOutM pc s u
  r3 : u.gpr .r3 = s.gpr .r3
  r4 : u.gpr .r4 = s.gpr .r9
  r5 : u.gpr .r5 = 0
  r6 : u.gpr .r6 = s.gpr .r6

theorem cmpArgs_ok {s t : State} (h : PreP pc s) (A : AtCmp pc s t) :
    WP isa (.block cmpArgs) t (AtLoop pc s) := by
  have hk := h.k2
  have ho : InRegions t.wr (fb s + BitVec.ofNat 64 oEs) 8 := by
    rw [A.wr]; exact in_fr s _ (by decide) (by decide)
  have c1 : oEs < 2 ^ 15 := by decide
  have c2 : oEs % 4 = 0 := by decide
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r3, .r4, .r5, .r6] (Q := fun u =>
    u.gpr .r3 = s.gpr .r3 ∧ u.gpr .r4 = s.gpr .r9 ∧ u.gpr .r5 = 0 ∧ u.gpr .r6 = s.gpr .r6 ∧
      u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oEs) (t.gpr .r3)) ?_ rfl)
    fun u ⟨⟨u3, u4, u5, u6, um⟩, k⟩ => ?_
  · unfold cmpArgs
    prun [exec_addSp0, A.sp, ho, c1, c2, A.r24, A.r26, A.r29, BitVec.or_self, Impl.AesGcm.PPC64LE.mov]
    rfl
  · have fw : Frame [⟨fb s + BitVec.ofNat 64 oEs, 8⟩] t.mem u.mem := by
      rw [um]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have ap : ∀ {d n : Nat}, (d + n ≤ oEs ∨ oEs + 8 ≤ d) → d + n ≤ 2 ^ 64 →
        ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 oEs, 8⟩ : Region)], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r :=
      fun hd hn r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ hd hn (by decide)
    have hm : Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat =
        Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat :=
      bytes_of_frame (s := t) fw (ap (.inr (by decide)) (by unfold oM; omega_arith)) (by omega_arith)
    have ho' : Spec.Rsa.bytesAt u.mem (s.gpr .r3) (s.gpr .r6).toNat =
        Spec.Rsa.bytesAt t.mem (s.gpr .r3) (s.gpr .r6).toNat :=
      bytes_of_frame (s := t) fw (fun r hr => by
        rw [List.mem_singleton.mp hr, show (⟨s.gpr .r3, (s.gpr .r6).toNat⟩ : Region) = oR s from outR_eq h]
        exact (h.ko.sub_left (frame_sub s (by decide))).symm) (by have := h.wo; rw [h.h4] at this; omega_arith)
    refine ⟨A.store (.inl (by decide)) (by decide) _ (fun r hr => k.gpr r (by revert r; decide)) k.sp k.rd
      k.wr um, ?_, ?_, u3, u4, u5, u6⟩
    · show Spec.Rsa.written _ _ _ _ _
      rw [fw.readW (Region.contains_self _ _) (ap (.inl (by decide)) (by decide)) (by decide)]
      exact written_congr hm A.crt
    · intro ws hw hv
      have := A.pub ws hw hv
      rw [← hm] at this
      rw [um, Mem.readW_writeW_self64, ← um]
      exact written_congr ho' this

/-- A byte, as `lbz` loads it. -/
abbrev zb (m : Mem) (a : Addr) : BitVec 64 := (m.read a 1).setWidth 64

/-- The OR of the XORs of the first `j` bytes at `a` and `b`. -/
def cmpAcc (m : Mem) (a b : Addr) : Nat → BitVec 64
  | 0 => 0
  | j + 1 => cmpAcc m a b j ||| (zb m (a + BitVec.ofNat 64 j) ^^^ zb m (b + BitVec.ofNat 64 j))

theorem zb_lt (m : Mem) (a : Addr) : (zb m a).toNat < 2 ^ 8 := by
  simp only [zb, BitVec.toNat_setWidth]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (m.read a 1).isLt

theorem cmpAcc_lt (m : Mem) (a b : Addr) (j : Nat) : (cmpAcc m a b j).toNat < 2 ^ 8 := by
  induction j with
  | zero => simp [cmpAcc]
  | succ j ih =>
    simp only [cmpAcc, BitVec.toNat_or, BitVec.toNat_xor]
    exact Nat.or_lt_two_pow ih (Nat.xor_lt_two_pow (zb_lt _ _) (zb_lt _ _))

theorem zb_xor_eq_zero (m : Mem) (a b : Addr) : zb m a ^^^ zb m b = 0#64 ↔ m a = m b := by
  rw [BitVec.xor_eq_zero_iff]
  constructor
  · intro h; rw [← Proof.Bignum.PPC64LE.read_one' m a, ← Proof.Bignum.PPC64LE.read_one' m b]; exact congrArg (BitVec.setWidth 8) h
  · intro h
    simp only [zb]
    congr 1
    show (m.read (a + 1) 0 ++ m a) = (m.read (b + 1) 0 ++ m b)
    rw [h]; simp only [Mem.read]

theorem cmpAcc_eq_zero (m : Mem) (a b : Addr) (j : Nat) :
    cmpAcc m a b j = 0#64 ↔ ∀ i < j, m (a + BitVec.ofNat 64 i) = m (b + BitVec.ofNat 64 i) := by
  induction j with
  | zero => simp [cmpAcc]
  | succ j ih =>
    rw [cmpAcc, BitVec.or_eq_zero_iff, ih, zb_xor_eq_zero]
    constructor
    · rintro ⟨h, h'⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h i hi
      · exact h'
    · intro h; exact ⟨fun i hi => h i (by omega_arith), h j (by omega_arith)⟩

theorem add_ofNat_one (p : Addr) (j : Nat) :
    p + BitVec.ofNat 64 j + BitVec.ofNat 64 1 = p + BitVec.ofNat 64 (j + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- The comparison: the OR of the XORs of `out`'s bytes and the input's in `r5`. -/
theorem compare_ok {s t : State} (h : PreP pc s) (A : AtLoop pc s t) :
    WP isa compare t fun u => u.gpr .r5 = cmpAcc t.mem (s.gpr .r3) (s.gpr .r9) (s.gpr .r6).toNat ∧
      u.mem = t.mem ∧ Keep [.r3, .r4, .r5, .r6, .r7, .r8] t u := by
  have hk := h.k2
  have hk1 := h.k1
  let Inv : Nat → State → Prop := fun j u =>
    u.gpr .r3 = s.gpr .r3 + BitVec.ofNat 64 j ∧ u.gpr .r4 = s.gpr .r9 + BitVec.ofNat 64 j ∧
      u.gpr .r5 = cmpAcc t.mem (s.gpr .r3) (s.gpr .r9) j ∧ u.mem = t.mem ∧ Keep [.r3, .r4, .r5, .r6, .r7, .r8] t u
  refine WP.mono (Proof.Bignum.PPC64LE.wp_countdown (N := (s.gpr .r6).toNat) (by omega_arith) (by omega_arith) Inv
    (fun j hj u ⟨u3, u4, u5, um, uk⟩ hc => ?_)
    ⟨by rw [A.r3]; simp, by rw [A.r4]; simp, A.r5, rfl, Keep.refl _ _⟩ (by rw [A.r6]; simp))
    fun u ⟨_, _, u5, um, uk⟩ => ⟨u5, um, uk⟩
  have io : InRegions (u.rd ++ u.wr) (s.gpr .r3 + BitVec.ofNat 64 j) 1 := by
    rw [uk.rd, uk.wr, A.wr, h.hwr]
    exact ⟨oR s, by simp, Offset.contains_base _ (by rw [h.h4]; omega_arith) (by omega_arith)⟩
  have ii : InRegions (u.rd ++ u.wr) (s.gpr .r9 + BitVec.ofNat 64 j) 1 := by
    rw [uk.rd, A.rd, h.hrd]
    exact ⟨iR s, by simp, Offset.contains_base _ (by rw [h.h10]; omega_arith) (by omega_arith)⟩
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r3, .r4, .r5, .r6, .r7, .r8] (Q := fun u' =>
    u'.gpr .r3 = s.gpr .r3 + BitVec.ofNat 64 (j + 1) ∧ u'.gpr .r4 = s.gpr .r9 + BitVec.ofNat 64 (j + 1) ∧
      u'.gpr .r5 = cmpAcc t.mem (s.gpr .r3) (s.gpr .r9) (j + 1) ∧ u'.mem = u.mem ∧
      u'.gpr .r6 = u.gpr .r6 - BitVec.ofNat 64 1) ?_ rfl) fun u' ⟨⟨v3, v4, v5, vm, v6⟩, k⟩ =>
    ⟨⟨v3, v4, v5, vm.trans um, uk.trans k |>.mono⟩, v6⟩
  prun [u3, u4, u5, um, io, ii, BitVec.add_zero, add_ofNat_one, cmpAcc,
    Proof.Bignum.PPC64LE.exec_lbz' (show Reg.r3 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
    Proof.Bignum.PPC64LE.exec_lbz' (show Reg.r4 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide)]

end VG.Proof.Rsa.PPC64LE.Priv

end

end

/-!
# `vg_rsa_private_checked` on PPC64LE: the result

From the statuses kept in the frame and the comparison's accumulator,
without a branch: the result and the release mask (`result_ok`), as the
check's logic on every target computes them (`Proof.Rsa.result`,
`Proof.Rsa.relMask`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)

theorem eqBit (acc : BitVec 64) (h : acc.toNat < 2 ^ 8) :
    (acc - BitVec.ofNat 64 1) >>> 63 = if acc = 0#64 then 1 else 0 := by
  split
  · next he => subst he; decide
  · next he =>
    apply BitVec.eq_of_toNat_eq
    have h0 : acc.toNat ≠ 0 := fun h' => he (BitVec.eq_of_toNat_eq (by simpa using h'))
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat]
    have : (0 : BitVec 64).toNat = 0 := rfl
    omega_arith

theorem and1_cases (x : BitVec 64) : x &&& 1 = 0 ∨ x &&& 1 = 1 := by
  have h := Proof.Rsa.and1_toNat x
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h0 | h1
  · exact .inl (BitVec.eq_of_toNat_eq (by rw [h, h0]; rfl))
  · exact .inr (BitVec.eq_of_toNat_eq (by rw [h, h1]; rfl))

theorem res_val (x : BitVec 64) (P : Prop) [Decidable P] :
    (0#64 - (x &&& 1#64) &&& 2#64 - if P then 1 else 0) = Proof.Rsa.result (x &&& 1) (decide P) := by
  unfold Proof.Rsa.result
  rcases and1_cases x with h | h <;> rw [show (1#64 : BitVec 64) = 1 from rfl, h] <;> by_cases hp : P <;>
    simp only [hp, ↓reduceIte, decide_true, decide_false] <;> decide

theorem mask_val (x : BitVec 64) (P : Prop) [Decidable P] :
    0#64 - ((if P then 1 else 0) &&& (x &&& 1#64)) = Proof.Rsa.relMask (x &&& 1) (decide P) := by
  unfold Proof.Rsa.relMask
  rcases and1_cases x with h | h <;> rw [show (1#64 : BitVec 64) = 1 from rfl, h] <;> by_cases hp : P <;>
    simp only [hp, ↓reduceIte, decide_true, decide_false] <;> decide

/-- The result and the release mask. -/
theorem result_ok {s w : State} {cs es acc : BitVec 64} (hsp : w.sp = fb s)
    (iSt : InRegions (w.rd ++ w.wr) (fb s + BitVec.ofNat 64 oSt) 8)
    (iEs : InRegions (w.rd ++ w.wr) (fb s + BitVec.ofNat 64 oEs) 8)
    (hst : w.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = cs)
    (hes : w.mem.readW (fb s + BitVec.ofNat 64 oEs) 64 = es) (h5 : w.gpr .r5 = acc)
    (hacc : acc.toNat < 2 ^ 8) (h24 : w.gpr .r24 = s.gpr .r3) (h26 : w.gpr .r26 = s.gpr .r6) :
    WP isa (.block Impl.Rsa.PPC64LE.Priv.result) w fun u =>
      (u.gpr .r3 = Proof.Rsa.result (cs &&& es &&& 1) (decide (acc = 0#64)) ∧
        u.gpr .r9 = Proof.Rsa.relMask (cs &&& es &&& 1) (decide (acc = 0#64)) ∧
        u.gpr .r6 = s.gpr .r6 ∧ u.gpr .r7 = s.gpr .r3 ∧ u.gpr .r8 = fb s + BitVec.ofNat 64 oM ∧
        u.mem = w.mem) ∧
      Keep [.r12, .r3, .r4, .r5, .r6, .r7, .r8, .r9] w u := by
  have c1 : oSt < 2 ^ 15 := by decide
  have c2 : oSt % 4 = 0 := by decide
  have c3 : oEs < 2 ^ 15 := by decide
  have c4 : oEs % 4 = 0 := by decide
  have c5 : oM < 2 ^ 15 := by decide
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  unfold Impl.Rsa.PPC64LE.Priv.result
  prun [exec_addSp0, hsp, iSt, iEs, hst, hes, h5, h24, h26, c1, c2, c3, c4, c5, BitVec.or_self,
    exec_addi (show Reg.r12 ≠ .r0 by decide) c5, Impl.AesGcm.PPC64LE.mov, eqBit acc hacc]
  exact ⟨res_val _ _, mask_val _ _⟩

theorem write1_ne (m : Mem) {b x : Addr} (v : BitVec (8 * 1)) (h : x ≠ b) : m.write b 1 v x = m x :=
  Mem.write_apply fun h' => h (by bv_omega)

theorem off_ne (p : Addr) {i j : Nat} (h : i ≠ j) (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    p + BitVec.ofNat 64 i ≠ p + BitVec.ofNat 64 j := fun e => h (by
  have := congrArg (fun x => (x - p).toNat) e
  simp only [Mem.sub_ofNat_toNat p hi, Mem.sub_ofNat_toNat p hj] at this
  exact this)

theorem off_ne_of_disjoint {O M : Addr} {k i j : Nat} (hd : Region.Disjoint ⟨O, k⟩ ⟨M, k⟩) (hi : i < k)
    (hj : j < k) (hk : k ≤ 2 ^ 64) : O + BitVec.ofNat 64 i ≠ M + BitVec.ofNat 64 j := fun e =>
  hd _ (Offset.contains_base O (by omega_arith) (by omega_arith)) (e ▸ Offset.contains_base M (by omega_arith) (by omega_arith))

theorem zb_eq (m : Mem) (a : Addr) : zb m a = (m a).setWidth 64 := by
  have h := congrArg BitVec.toNat (Proof.Bignum.PPC64LE.read_one' m a)
  simp only [BitVec.toNat_setWidth] at h
  apply BitVec.eq_of_toNat_eq
  simp only [zb, BitVec.toNat_setWidth]
  have h1 := (m.read a 1).isLt
  have h2 := (m a).isLt
  simp only [Nat.reduceMul, Nat.reducePow] at h1 h2 h ⊢
  omega_arith

/-- The release: `out` := `m` under the mask, `m` := 0. -/
theorem release_ok {s w : State} (h : PreP pc s) (L : Late s w) {mask : BitVec 64} {c : Prop} [Decidable c]
    (hb : ∀ b : Byte, ((b.setWidth 64) &&& mask).setWidth 8 = if c then b else 0)
    (h6 : w.gpr .r6 = s.gpr .r6) (h7 : w.gpr .r7 = s.gpr .r3) (h8 : w.gpr .r8 = fb s + BitVec.ofNat 64 oM)
    (h9 : w.gpr .r9 = mask) :
    WP isa release w fun u =>
      Spec.Rsa.bytesAt u.mem (s.gpr .r3) (s.gpr .r6).toNat =
        (if c then Spec.Rsa.bytesAt w.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat
          else List.replicate (s.gpr .r6).toNat 0) ∧
      Frame [oR s, mR s] w.mem u.mem ∧ Keep [.r0, .r6, .r7, .r8] w u := by
  have hk := h.k2
  have hk1 := h.k1
  have fbt := fb_toNat h.sp1
  unfold frameBytes at fbt
  have om : Region.Disjoint (oR s) (mR s) :=
    (h.ko.sub_left (frame_sub s (by unfold oM frameBytes; omega_arith))).symm
  have om' : Region.Disjoint ⟨s.gpr .r3, (s.gpr .r6).toNat⟩ (mR s) := by rw [← h.h4] at *; exact om
  let O := s.gpr .r3
  let M := fb s + BitVec.ofNat 64 oM
  let k := (s.gpr .r6).toNat
  let Inv : Nat → State → Prop := fun j u =>
    u.gpr .r7 = O + BitVec.ofNat 64 j ∧ u.gpr .r8 = M + BitVec.ofNat 64 j ∧ Frame [oR s, mR s] w.mem u.mem ∧
      (∀ i < j, u.mem (O + BitVec.ofNat 64 i) = if c then w.mem (M + BitVec.ofNat 64 i) else 0) ∧
      (∀ i, j ≤ i → i < k → u.mem (M + BitVec.ofNat 64 i) = w.mem (M + BitVec.ofNat 64 i)) ∧
      Keep [.r0, .r6, .r7, .r8] w u
  refine WP.mono (Proof.Bignum.PPC64LE.wp_countdown (N := k) (by omega_arith) (by omega_arith) Inv
    (fun j hj u ⟨u7, u8, uf, uo, um, uk⟩ hc => ?_)
    ⟨by rw [h7]; simp [O], by rw [h8]; simp [M], Frame.refl _ _, fun _ h => absurd h (by omega_arith),
      fun _ _ _ => rfl, Keep.refl _ _⟩ (by rw [h6]; simp [k]))
    fun u ⟨_, _, uf, uo, _, uk⟩ => ⟨?_, uf, uk⟩
  · have u9 : u.gpr .r9 = mask := (uk.gpr .r9 (by decide)).trans h9
    have fw : u.wr = fr s :: oR s :: [sR s] := by rw [uk.wr, L.wr, h.hwr]
    have io : InRegions u.wr (O + BitVec.ofNat 64 j) 1 := by
      rw [fw]; exact ⟨oR s, by simp, Offset.contains_base _ (by rw [h.h4]; omega_arith) (by omega_arith)⟩
    have mc : (mR s).Contains (M + BitVec.ofNat 64 j) 1 := Offset.contains_base _ (by omega_arith) (by omega_arith)
    have e : M + BitVec.ofNat 64 j = fb s + BitVec.ofNat 64 (oM + j) := by
      simp only [M]; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    have im : InRegions u.wr (M + BitVec.ofNat 64 j) 1 := by
      rw [fw, e]; exact in_fr s _ (by unfold oM; omega_arith) (by unfold oM frameBytes; omega_arith)
    have imr : InRegions (u.rd ++ u.wr) (M + BitVec.ofNat 64 j) 1 := by
      obtain ⟨r, hr, hc⟩ := im; exact ⟨r, List.mem_append_right _ hr, hc⟩
    refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r0, .r6, .r7, .r8] (Q := fun u' =>
      u'.gpr .r7 = O + BitVec.ofNat 64 (j + 1) ∧ u'.gpr .r8 = M + BitVec.ofNat 64 (j + 1) ∧
        u'.mem = (u.mem.write (O + BitVec.ofNat 64 j) 1 ((zb u.mem (M + BitVec.ofNat 64 j) &&& mask).setWidth 8)).write
          (M + BitVec.ofNat 64 j) 1 ((0#64 : BitVec 64).setWidth 8) ∧
        u'.gpr .r6 = u.gpr .r6 - BitVec.ofNat 64 1) ?_ rfl) fun u' ⟨⟨v7, v8, vm, v6⟩, k'⟩ => ?_
    · prun [u7, u8, u9, io, im, imr, BitVec.add_zero, add_ofNat_one,
        Proof.Bignum.PPC64LE.exec_lbz' (show Reg.r8 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
        exec_stb (show Reg.r7 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
        exec_stb (show Reg.r8 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide)]
    · have hOM : ∀ {i j : Nat}, i < k → j < k → O + BitVec.ofNat 64 i ≠ M + BitVec.ofNat 64 j :=
        fun hi hj => off_ne_of_disjoint om' hi hj (by omega_arith)
      have hMj : u.mem (M + BitVec.ofNat 64 j) = w.mem (M + BitVec.ofNat 64 j) := um j (by omega_arith) hj
      refine ⟨⟨v7, v8, ?_, fun i hi => ?_, fun i hi hi' => ?_, uk.trans k' |>.mono⟩, v6⟩
      · rw [vm]
        refine Frame.write (Frame.write uf (List.mem_cons_self ..) _ ?_) (List.mem_cons_of_mem _
          (List.mem_singleton_self _)) _ mc
        exact Offset.contains_base _ (by rw [h.h4]; omega_arith) (by omega_arith)
      · rw [vm, write1_ne _ _ (hOM (by omega_arith) hj)]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · rw [write1_ne _ _ (off_ne O (by omega_arith) (by omega_arith) (by omega_arith))]; exact uo i hi
        · rw [Proof.Bignum.PPC64LE.write1_self, zb_eq, hMj]; exact hb _
      · rw [vm, write1_ne _ _ (off_ne M (by omega_arith) (by omega_arith) (by omega_arith)),
          write1_ne _ _ (Ne.symm (hOM hj hi'))]
        exact um i (by omega_arith) hi'
  · simp only [Spec.Rsa.bytesAt]
    split
    · exact List.map_congr_left fun i hi => by
        have := uo i (List.mem_range.mp hi); simp only [*, ↓reduceIte] at this; exact this
    · rw [List.eq_replicate_iff]
      refine ⟨by simp, fun b hb => ?_⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
      have := uo i (List.mem_range.mp hi); simp only [*, ↓reduceIte] at this; exact this

end VG.Proof.Rsa.PPC64LE.Priv
end

end

/-! ### `Rsa.PPC64LE.PrivRestore`, which only this module used -/

section

/-!
# `vg_rsa_private_checked` on PPC64LE: the restores

`Late` through the blocks after the public operation (`Late.keep`,
`Late.release`), and the restores of our caller's registers and return
address (`restore_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)

theorem Late.keep {s t u : State} (L : Late s t) {rs : List Reg} (k : Keep rs t u) (hm : u.mem = t.mem)
    (hrs : ∀ r ∈ preserved, r ∉ rs := by decide) : Late s u :=
  ⟨k.sp.trans L.sp, k.rd.trans L.rd, k.wr.trans L.wr, (k.gpr _ (hrs _ (by decide))).trans L.r24,
    (k.gpr _ (hrs _ (by decide))).trans L.r25, (k.gpr _ (hrs _ (by decide))).trans L.r26,
    (k.gpr _ (hrs _ (by decide))).trans L.r27, (k.gpr _ (hrs _ (by decide))).trans L.r28,
    (k.gpr _ (hrs _ (by decide))).trans L.r29,
    fun r hr => (k.gpr r (hrs r (by revert r; decide))).trans (L.hi r hr), hm ▸ L.mem, hm ▸ L.sv, hm ▸ L.ls⟩

/-- The frame's words are apart from `out` and `m`. -/
theorem slot_apart {s : State} (h : PreP pc s) {d : Nat} (hd : d + 8 ≤ oM) {r : Region} (hr : r ∈ [oR s, mR s]) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.ko.sub_left (frame_sub s (by unfold oM frameBytes at *; omega_using [hd]))
  · exact Offset.disjoint _ (.inl hd) (by unfold oM at hd; omega_using [hd]) (by have := h.k2; unfold oM; omega_using [this])

theorem Late.release {s t u : State} (h : PreP pc s) (L : Late s t) (k : Keep [.r0, .r6, .r7, .r8] t u)
    (hf : Frame [oR s, mR s] t.mem u.mem) : Late s u := by
  have mk : Region.Sub (mR s) (kR s) := frame_sub s (by have := h.k2; unfold oM frameBytes; omega_using [this])
  refine ⟨k.sp.trans L.sp, k.rd.trans L.rd, k.wr.trans L.wr, (k.gpr _ (by decide)).trans L.r24,
    (k.gpr _ (by decide)).trans L.r25, (k.gpr _ (by decide)).trans L.r26, (k.gpr _ (by decide)).trans L.r27,
    (k.gpr _ (by decide)).trans L.r28, (k.gpr _ (by decide)).trans L.r29,
    fun r hr => (k.gpr r (by revert r; decide)).trans (L.hi r hr), L.mem.trans (hf.sub fun r hr => ?_),
    L.sv.frame hf fun p hp r hr => slot_apart h (by have := saved_offs p hp; unfold oSave oM at *; omega_using [this]) hr, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., mk⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => slot_apart h (by decide) hr) (by decide)]; exact L.ls

/-- The restores. -/
theorem restore_ok {s w : State} (L : Late s w) :
    WP isa (.block restore) w fun v =>
      (∀ r ∈ preserved, v.gpr r = s.gpr r) ∧ v.lr = s.lr ∧ v.sp = fb s ∧ v.mem = w.mem ∧ v.gpr .r3 = w.gpr .r3 := by
  have iLr : InRegions (w.rd ++ w.wr) (fb s + BitVec.ofNat 64 oLr) 8 := by
    rw [L.wr]; exact in_fr' s _ _ (by decide) (by decide)
  have c1 : oLr < 2 ^ 15 := by decide
  have c2 : oLr % 4 = 0 := by decide
  rw [restore_eq]
  refine WP.block_append_iff.mpr (WP.mono (Q := fun v => v = { ((w.write .r12 w.sp).write .r0
      (w.mem.readW (fb s + BitVec.ofNat 64 oLr) 64)) with lr := w.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 })
    ?_ fun v e => ?_)
  · prun [exec_addSp0, L.sp, iLr, c1, c2, exec_mtlr]
  · subst e
    refine WP.mono (Spill.restore_wp (b := .r12) (B := fb s) (by decide) (by simp [State.write, L.sp])
      saved_ho (by decide) (fun p hp => by
        have := saved_offs p hp
        show InRegions (w.rd ++ w.wr) _ 8
        rw [L.wr]; exact in_fr' s _ _ (by unfold oSave at this; omega_using [this]) (by unfold oSave at this; unfold frameBytes; omega_using [this]))
      L.sv) fun v R => ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · rcases preserved_split hr with hs | hs
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
        exact R.gpr p hp
      · have : r ∉ saved.map Prod.fst := by revert r; decide
        rw [R.other r this]
        have h12 : r ≠ .r12 := by revert r; decide
        have h0 : r ≠ .r0 := by revert r; decide
        simp only [State.write, h12, h0, ite_false]
        exact L.hi r hs
    · rw [R.lr]; exact L.ls
    · rw [R.sp]; exact L.sp
    · rw [R.mem]; rfl
    · rw [R.other _ (by decide)]; simp [State.write]

end VG.Proof.Rsa.PPC64LE.Priv
end

end

/-! ### `Rsa.PPC64LE.PrivFinal`, which only this module used -/

section

/-!
# `vg_rsa_private_checked` on PPC64LE: the outcome

The outcome from what the calls returned and wrote (`final_ok`): the check's
logic on every target (`Proof.Rsa.check_logic`, `Proof.Rsa.outcome_eq`),
without the status of `vg_rsa_public_precompute`, which this check does not
read: `n`'s values are invalid only when `n` is, and then so is the CRT's
result.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.Proof.Rsa

theorem final_ok {m m' : Mem} {O M : Addr} {k : Nat} {cs es acc : BitVec 64}
    {nB eB xB pB qB dPB dQB qInvB : List Byte} (hn : nB.length = k) (hx : xB.length = k)
    (hcrt : Spec.Rsa.written m M k (cs.setWidth 32) (Spec.Rsa.privateCrt nB xB pB qB dPB dQB qInvB))
    (hpub : ∀ ws, Spec.Rsa.publicPrecompute nB = some ws →
      Spec.Rsa.written m O k (es.setWidth 32) (Spec.Rsa.publicOpChecked nB eB (Spec.Rsa.bytesAt m M k)))
    (heq : acc = 0#64 ↔ Spec.Rsa.bytesAt m O k = xB)
    (hout : Spec.Rsa.bytesAt m' O k =
      if cs &&& es &&& 1 = 1 ∧ decide (acc = 0#64) = true then Spec.Rsa.bytesAt m M k else List.replicate k 0) :
    Spec.Rsa.writtenOutcome m' O k ((result (cs &&& es &&& 1) (decide (acc = 0#64))).setWidth 32)
      (Spec.Rsa.privateChecked nB eB xB pB qB dPB dQB qInvB) := by
  let r₃ : BitVec 64 := if (Spec.Rsa.publicPrecompute nB).isSome then 1 else 0
  have hv : cs &&& es &&& 1 = gOf es cs r₃ := by
    by_cases hp : (Spec.Rsa.publicPrecompute nB).isSome
    · simp only [gOf, r₃, hp, ↓reduceIte]
      rw [BitVec.and_assoc (es &&& cs) 1 1, BitVec.and_self, BitVec.and_comm cs es]
    · have hm : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) nB.length = false := by
        rw [← precompute_isSome]; simpa using hp
      have hc : Spec.Rsa.privateCrt nB xB pB qB dPB dQB qInvB = none := by
        simp only [Spec.Rsa.privateCrt, hm]; rfl
      rw [hc] at hcrt
      have h1 : cs &&& 1 = 0 := by
        rcases gOf_cases cs cs 1 with h | h <;> simp only [gOf] at h
        all_goals
          have := and1_of_setWidth_zero hcrt.1
          have e : cs &&& cs &&& 1 &&& 1 = cs &&& 1 := by
            rw [BitVec.and_self, BitVec.and_assoc, BitVec.and_self]
          rw [e] at h
          first | exact h | exact absurd h this
      simp only [gOf, r₃, hp, Bool.false_eq_true, ↓reduceIte]
      rw [show cs &&& es &&& 1 = (cs &&& 1) &&& es by ac_rfl, h1]
      rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.zero_and, BitVec.and_zero, BitVec.zero_and]
  have h3 : match Spec.Rsa.publicPrecompute nB with
      | some _ => r₃.setWidth 32 = 1
      | none => r₃.setWidth 32 = 0 := by
    cases hpc : Spec.Rsa.publicPrecompute nB <;> simp [r₃, hpc]
  have h2 : (Spec.Rsa.publicPrecompute nB).isSome = true →
      match Spec.Rsa.publicOpChecked nB eB (Spec.Rsa.bytesAt m M k) with
      | some y => es.setWidth 32 = 1 ∧ Spec.Rsa.bytesAt m O k = y
      | none => es.setWidth 32 = 0 := by
    intro hs
    obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp hs
    have := hpub ws hws
    cases hpo : Spec.Rsa.publicOpChecked nB eB (Spec.Rsa.bytesAt m M k) <;>
      simp only [hpo, Spec.Rsa.written] at this ⊢
    · exact this.1
    · exact this
  have hL := check_logic (r₁ := cs) (xB := xB) h3 h2
  have hd : decide (acc = 0#64) = decide (Spec.Rsa.bytesAt m O k = xB) := decide_eq_decide.mpr heq
  refine outcome_eq hn hx hcrt (by rw [hv, hd]; exact hL.1) ?_
  have hc : (gOf es cs r₃ = 1 ∧ decide (Spec.Rsa.bytesAt m O k = xB) = true) ↔
      released cs nB eB xB (Spec.Rsa.bytesAt m M k) := by
    rw [decide_eq_true_eq]; exact hL.2
  rw [hout, hv, hd]
  by_cases hr : released cs nB eB xB (Spec.Rsa.bytesAt m M k)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (hc.mpr hr)), ite_eq_left_of_eq_true _ _ (eq_true hr)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hr (hc.mp h)), ite_eq_right_of_eq_false _ _ (eq_false hr)]

end VG.Proof.Rsa.PPC64LE.Priv

end

end


/-!
# `vg_rsa_private_checked` on PPC64LE: correctness

The blocks and calls in order (`code_correct`), from the frame's push to its
pop, to the outcome (`final_ok`), on the registers and the stack (`fnPost`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)

/-- The outcome, on the registers and the stack. -/
def fnPost (s s' : State) : Prop :=
  Spec.Rsa.writtenOutcome s'.mem (s.gpr .r3) (s.gpr .r6).toNat ((s'.gpr .r3).setWidth 32)
    (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat))

theorem freed_sp (b : Nat) (s : State) : (freed b s).sp = s.sp + BitVec.ofNat 64 b := rfl
theorem freed_lr (b : Nat) (s : State) : (freed b s).lr = s.lr := rfl
theorem freed_gpr (b : Nat) (s : State) : (freed b s).gpr = s.gpr := rfl
theorem freed_mem (b : Nat) (s : State) : (freed b s).mem = s.mem := rfl

/-- The CRT's result in the frame, from the state after the setup. -/
def CrtOk (pc : Bool) (s : State) : Prop :=
  ∀ t (Q : State → Prop), AtCrt s t → (∀ u, Mid s u → crtOut s u → Q u) → WP isa (crtStep pc) t Q

/-- `n`'s values put in the frame, from the state after `vg_rsa_private_crt`. -/
def StepOk (pc : Bool) (s : State) : Prop :=
  ∀ t (c : Prog isa) (Q : State → Prop), Mid s t → crtOut s t → (∀ u, AtPub pc s u → WP isa c u Q) →
    WP isa (.seq (preStep pc) c) t Q

/-- `writtenOutcome` reads the memory only in the output. -/
private theorem writtenOutcome_congr {m m' : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (hb : Spec.Rsa.bytesAt m' out k = Spec.Rsa.bytesAt m out k) (h : Spec.Rsa.writtenOutcome m out k r o) :
    Spec.Rsa.writtenOutcome m' out k r o := by
  cases o <;> simp only [Spec.Rsa.writtenOutcome, hb] at h ⊢ <;> exact h

/-- `n`'s values in the frame are its precomputed values, if they are valid. -/
abbrev PreValOk (pc : Bool) (s : State) : Prop :=
  ∀ ws, Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) = some ws →
    preVal pc s = ws

theorem codeG_correct {pc : Bool} (s : State) (h : PreP pc s) (hcrt : CrtOk pc s) (hstep : StepOk pc s) :
    WP isa (.frame (.alloc frameBytes) (bodyG pc) (.free frameBytes)) s fun t =>
      abiPreserved s t ∧ (PreValOk pc s → fnPost s t) := by
  have hk := h.k2
  refine WP.alloc ⟨by decide, by decide, by decide⟩ h.sp1 ?_
  unfold bodyG
  refine WP.seq (WP.mono (setup_ok h) fun t₁ A => ?_)
  refine WP.seq (hcrt t₁ _ A fun t₂ M C => ?_)
  refine hstep t₂ _ _ M C fun t₄ Q4 => ?_
  refine WP.seq (WP.mono (pubArgs_ok h Q4) fun t₅ R => ?_)
  refine WP.seq (pubCall_ok h R fun t₆ C6 => ?_)
  refine WP.seq (WP.mono (cmpArgs_ok h C6) fun t₇ L => ?_)
  refine WP.seq (WP.mono (compare_ok h L) fun t₈ ⟨a8, m8, k8⟩ => ?_)
  have L8 : Late s t₈ := L.toLate.keep k8 m8
  have iSt : InRegions (t₈.rd ++ t₈.wr) (fb s + BitVec.ofNat 64 oSt) 8 := by
    rw [L8.wr]; exact in_fr' s _ _ (by decide) (by decide)
  have iEs : InRegions (t₈.rd ++ t₈.wr) (fb s + BitVec.ofNat 64 oEs) 8 := by
    rw [L8.wr]; exact in_fr' s _ _ (by decide) (by decide)
  refine WP.seq (WP.mono (result_ok (cs := t₇.mem.readW (fb s + BitVec.ofNat 64 oSt) 64)
    (es := t₇.mem.readW (fb s + BitVec.ofNat 64 oEs) 64) L8.sp iSt iEs (by rw [m8]) (by rw [m8]) a8 (cmpAcc_lt _ _ _ _) L8.r24 L8.r26)
    fun t₉ ⟨⟨r3, r9, r6, r7, r8, m9⟩, k9⟩ => ?_)
  have L9 : Late s t₉ := L8.keep k9 m9
  refine WP.seq (WP.mono (release_ok h L9 (fun b => Proof.Rsa.low_and_mask b _ _) r6 r7 r8 r9)
    fun t₁₀ ⟨hout, f10, k10⟩ => ?_)
  have L10 := L9.release h k10 f10
  refine WP.mono (restore_ok L10) fun v ⟨vp, vl, vs, vm, v3⟩ mL _ fl => ?_
  -- The `free` loses the frame's bytes, which lie apart from the output.
  have hb : Spec.Rsa.bytesAt mL (s.gpr .r3) (s.gpr .r6).toNat =
      Spec.Rsa.bytesAt (freed frameBytes v).mem (s.gpr .r3) (s.gpr .r6).toNat := by
    rw [freed_mem]
    exact List.map_congr_left fun i hi => lost_byte fl (R := outR s) (by rw [outR_eq h]; exact h.ko.symm)
      (List.mem_range.mp hi)
  refine ⟨abiPreserved_lost ⟨fun r hr => ?_, ?_, ?_⟩, fun hv => writtenOutcome_congr hb (?_ : fnPost s _)⟩
  · rw [freed_gpr]; exact vp r hr
  · rw [freed_sp, vs]; exact BitVec.sub_add_cancel _ _
  · rw [freed_lr]; exact vl
  · unfold fnPost
    rw [freed_mem, freed_gpr, vm, v3, k10.gpr .r3 (by decide), r3]
    have m97 : t₉.mem = t₇.mem := m9.trans m8
    rw [m97] at hout
    have hx : Spec.Rsa.bytesAt t₇.mem (s.gpr .r9) (s.gpr .r6).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r6).toNat :=
      bytes_of_frame L.mem (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have ei : (⟨s.gpr .r9, (s.gpr .r6).toNat⟩ : Region) = iR s := by simp only [iR, h.h10]
        rw [ei]
        rcases hr with rfl | rfl | rfl
        · exact h.ki.symm
        · exact h.oi.symm
        · exact h.is) (by have := h.wi; rw [h.h10] at this; omega_using [])
    refine final_ok (Proof.Rsa.bytesAt_length' _ _ _) (Proof.Rsa.bytesAt_length' _ _ _) L.crt (fun ws hw => L.pub ws hw (hv ws hw)) ?_ hout
    rw [cmpAcc_eq_zero, ← hx, Proof.Rsa.bytesAt_eq_iff]

theorem step_false (s : State) (h : PreP false s) : StepOk false s := fun _ _ _ M C hc =>
  WP.seq (WP.seq (WP.mono (preArgs_ok h M C) fun _ P => preCall_ok h P hc))

theorem code_correct (s : State) (hpre : (Proof.Rsa.privateCheckedContract abi frameBytes).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ fnPost s t := by
  have h := preP_of hpre
  exact WP.mono (codeG_correct s h (fun _ _ A hQ => crtCall_ok h A hQ) (step_false s h)) fun t ⟨ha, hf⟩ =>
    ⟨ha, hf fun ws hw => by simp only [preVal, Bool.false_eq_true, ↓reduceIte, hw, Option.getD_some]⟩

end VG.Proof.Rsa.PPC64LE.Priv
