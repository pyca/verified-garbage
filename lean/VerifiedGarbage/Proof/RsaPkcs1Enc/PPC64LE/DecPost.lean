module

public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPre
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivVerified
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
import VerifiedGarbage.Proof.Framework.Covers

/-! ### `RsaPkcs1Enc.PPC64LE.DecPriv`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.PPC64LE.DecSetup`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.PPC64LE.DecFrame`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.PPC64LE.DecPre`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: the precondition

`DPre pc s`: the shared contract's precondition (`decryptContract`, or with
`pc` `decryptPrecomputedContract`, with the stack of the frame and of
`vg_rsa_private_checked`'s, `stackBytes`), by name (`dPre_of`); with `pc`,
what it says of `pre` (`PreX`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE

/-- The stack the function uses: its frame and `vg_rsa_private_checked`'s. -/
def stackBytes : Nat := Impl.RsaPkcs1Enc.PPC64LE.Decrypt.frameBytes + Impl.Rsa.PPC64LE.Priv.frameBytes

theorem stackArgs_fifteen (s : State) :
    List.map (stackArg s) (List.range 15) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14] := rfl

/-! ## The buffers -/

abbrev oR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
abbrev mlR (s : State) : Region := ⟨s.gpr .r5, 8⟩
abbrev nR (s : State) : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
abbrev dR (s : State) : Region := ⟨s.gpr .r10, (stackArg s 0).toNat⟩
abbrev iR (s : State) : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
abbrev pR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat⟩
abbrev qR (s : State) : Region := ⟨stackArg s 5, (stackArg s 6).toNat⟩
abbrev dpR (s : State) : Region := ⟨stackArg s 7, (stackArg s 8).toNat⟩
abbrev dqR (s : State) : Region := ⟨stackArg s 9, (stackArg s 10).toNat⟩
abbrev qiR (s : State) : Region := ⟨stackArg s 11, (stackArg s 12).toNat⟩
abbrev sR (s : State) : Region := ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
/-- Our stack arguments: fifteen, or with `pc` seventeen. -/
abbrev aR (pc : Bool) (s : State) : Region := ⟨stackArgAddr s 0, if pc then 136 else 120⟩
/-- With `pc`, the key's precomputed values, `pre_len` words. -/
abbrev preR (s : State) : Region := ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩

/-- The buffers the function reads. -/
abbrev rdL (pc : Bool) (s : State) : List Region :=
  [nR s, eR s, dR s, iR s, pR s, qR s, dpR s, dqR s, qiR s] ++ (if pc then [preR s] else []) ++ [aR pc s]

/-- The base of the frame. -/
abbrev fb (s : State) : Addr := s.sp - BitVec.ofNat 64 Impl.RsaPkcs1Enc.PPC64LE.Decrypt.frameBytes

/-- The stack the function and its callees use. -/
abbrev kR (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩

/-- The precondition, by name. -/
structure DPre (pc : Bool) (s : State) : Prop where
  sp1 : stackBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + (if pc then 232 else 216) ≤ 2 ^ 64
  hrd : s.rd = rdL pc s
  hwr : s.wr = [oR s, mlR s, sR s]
  om : (oR s).Disjoint (mlR s)
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  od : (oR s).Disjoint (dR s)
  oi : (oR s).Disjoint (iR s)
  op : (oR s).Disjoint (pR s)
  oq : (oR s).Disjoint (qR s)
  odp : (oR s).Disjoint (dpR s)
  odq : (oR s).Disjoint (dqR s)
  oqi : (oR s).Disjoint (qiR s)
  os : (oR s).Disjoint (sR s)
  oa : (oR s).Disjoint (aR pc s)
  mn : (mlR s).Disjoint (nR s)
  me : (mlR s).Disjoint (eR s)
  md : (mlR s).Disjoint (dR s)
  mi : (mlR s).Disjoint (iR s)
  mp : (mlR s).Disjoint (pR s)
  mq : (mlR s).Disjoint (qR s)
  mdp : (mlR s).Disjoint (dpR s)
  mdq : (mlR s).Disjoint (dqR s)
  mqi : (mlR s).Disjoint (qiR s)
  ms : (mlR s).Disjoint (sR s)
  ma : (mlR s).Disjoint (aR pc s)
  ns : (nR s).Disjoint (sR s)
  es : (eR s).Disjoint (sR s)
  ds : (dR s).Disjoint (sR s)
  is : (iR s).Disjoint (sR s)
  ps : (pR s).Disjoint (sR s)
  qs : (qR s).Disjoint (sR s)
  dps : (dpR s).Disjoint (sR s)
  dqs : (dqR s).Disjoint (sR s)
  qis : (qiR s).Disjoint (sR s)
  sa : (sR s).Disjoint (aR pc s)
  ko : (kR s).Disjoint (oR s)
  km : (kR s).Disjoint (mlR s)
  kn : (kR s).Disjoint (nR s)
  ke : (kR s).Disjoint (eR s)
  kd : (kR s).Disjoint (dR s)
  ki : (kR s).Disjoint (iR s)
  kp : (kR s).Disjoint (pR s)
  kq : (kR s).Disjoint (qR s)
  kdp : (kR s).Disjoint (dpR s)
  kdq : (kR s).Disjoint (dqR s)
  kqi : (kR s).Disjoint (qiR s)
  ks : (kR s).Disjoint (sR s)
  ka : (kR s).Disjoint (aR pc s)
  wo : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  wm : (s.gpr .r5).toNat + 8 ≤ 2 ^ 64
  wn : (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64
  we : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wd : (s.gpr .r10).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  wi : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  wp : (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 64
  wq : (stackArg s 5).toNat + (stackArg s 6).toNat ≤ 2 ^ 64
  wdp : (stackArg s 7).toNat + (stackArg s 8).toNat ≤ 2 ^ 64
  wdq : (stackArg s 9).toNat + (stackArg s 10).toNat ≤ 2 ^ 64
  wqi : (stackArg s 11).toNat + (stackArg s 12).toNat ≤ 2 ^ 64
  ws : (stackArg s 13).toNat + (stackArg s 14).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .r7).toNat
  k2 : (s.gpr .r7).toNat ≤ 1024
  h4 : (s.gpr .r4).toNat = (s.gpr .r7).toNat
  hi : (stackArg s 2).toNat = (s.gpr .r7).toNat
  e1 : 1 ≤ (s.gpr .r9).toNat
  e2 : (s.gpr .r9).toNat ≤ (s.gpr .r7).toNat
  d1 : 1 ≤ (stackArg s 0).toNat
  d2 : (stackArg s 0).toNat ≤ (s.gpr .r7).toNat
  p1 : 1 ≤ (stackArg s 4).toNat
  p2 : (stackArg s 4).toNat < (s.gpr .r7).toNat
  q1 : 1 ≤ (stackArg s 6).toNat
  q2 : (stackArg s 6).toNat < (s.gpr .r7).toNat
  h8 : (stackArg s 8).toNat = (stackArg s 4).toNat
  h12 : (stackArg s 12).toNat = (stackArg s 4).toNat
  h10 : (stackArg s 10).toNat = (stackArg s 6).toNat
  hs : Spec.Rsa.scratchWords (s.gpr .r7).toNat ≤ (stackArg s 14).toNat

/-- With `pc`, `pre` holds the key's precomputed values. -/
abbrev HypS (pc : Bool) (s : State) : Prop :=
  pc = true → Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 15) (stackArg s 16).toNat)

/-- What `vg_rsa_pkcs1_decrypt_precomputed`'s precondition adds: `pre`'s facts. -/
structure PreX (s : State) : Prop where
  oP : (oR s).Disjoint (preR s)
  mP : (mlR s).Disjoint (preR s)
  sP : (sR s).Disjoint (preR s)
  kP : (kR s).Disjoint (preR s)
  wP : (stackArg s 15).toNat + (stackArg s 16).toNat * 8 ≤ 2 ^ 64
  pl : (stackArg s 16).toNat =
    Spec.Rsa.privatePrecomputedWords (s.gpr .r7).toNat (stackArg s 4).toNat (stackArg s 6).toNat
  hyp : HypS true s

theorem dPre_of {s : State} (h : (Spec.RsaPkcs1Enc.decryptContract abi stackBytes).pre s) : DPre false s := by
  have e : stackBytes = 3647 + 1 := rfl
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi, argRegs,
    stackArgs_fifteen, List.append_eq] at h
  simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
    Bool.true_or, Bool.false_or, List.cons_append, List.nil_append, Sig.conj, List.append_nil] at h
  obtain ⟨sp1, sp2, hrd, hwr, om, on, ⟨oe, od, oi, op, oq, odp, odq, oqi, os, oa, mn, me, md, mi, mp, mq, mdp, mdq, mqi, ms, ma, ns, es, ds, is, ps, qs, dps, dqs, qis, sa⟩,
    ko, km, kn, ke, kd, ki, kp, kq, kdp, kdq, kqi, ks, ka,
    wo, wm, wn, we, wd, wi, wp, wq, wdp, wdq, wqi, ws, ⟨k1, k2⟩, h4, hi, e1, e2, d1, d2, p1, p2, q1, q2, h8, h12, h10, hs⟩ := h
  exact ⟨sp1, by simp only [Bool.false_eq_true, ↓reduceIte]; omega_using [sp2], hrd, hwr, om, on, oe, od, oi, op, oq, odp, odq, oqi, os, oa, mn, me, md, mi, mp, mq, mdp, mdq, mqi, ms, ma, ns, es, ds, is, ps, qs, dps, dqs, qis, sa, ko, km, kn, ke, kd, ki, kp, kq, kdp, kdq, kqi, ks, ka, wo, wm, wn, we, wd, wi, wp, wq, wdp, wdq, wqi, ws, k1, k2, h4, hi, e1, e2, d1, d2, p1, p2, q1, q2, h8, h12, h10, hs⟩

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

end

end


/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: the frame

The stack the function uses, `kR`, is `vg_rsa_private_checked`'s frame
(from `kb`) and then ours (from `fb`); the push makes our local variable
space `fr` writable.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt

variable {pc : Bool}

/-- The base of the stack the function and its callee use. -/
abbrev kb (s : State) : Addr := s.sp - BitVec.ofNat 64 stackBytes

/-- Our frame's local variable space, which its push makes writable. -/
abbrev fr (s : State) : Region := ⟨fb s + BitVec.ofNat 64 32, frameBytes - 32⟩

theorem fb_eq (s : State) : fb s = kb s + BitVec.ofNat 64 Impl.Rsa.PPC64LE.Priv.frameBytes := by
  simp only [fb, kb, stackBytes, frameBytes, Impl.Rsa.PPC64LE.Priv.frameBytes]
  bv_omega

theorem fb_toNat {s : State} (h : DPre pc s) : (fb s).toNat + frameBytes = s.sp.toNat := by
  have := h.sp1
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold stackBytes frameBytes at *
  unfold Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega_using [this]

theorem kb_toNat {s : State} (h : DPre pc s) : (kb s).toNat + stackBytes = s.sp.toNat := by
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

theorem lt_args {j : Nat} (hj : j < 15) : j < if pc then 17 else 15 := by
  cases pc <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega_using [hj]

theorem in_aR {s : State} {j : Nat} (hj : j < if pc then 17 else 15) : (aR pc s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]
  cases pc <;> simp only [aR, Bool.false_eq_true, ↓reduceIte] at hj ⊢ <;>
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

end

end


/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: up to the private-key operation

From the state after the frame's push: our return address and the arguments
in their slots (`Slots`), the private-key operation's twelve stack arguments
copied from ours, and its arguments in registers (`setup_ok`, into
`AtPriv`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)
open VG.PPC64LE.RegUpd (gpr_write_self gpr_write_of_ne mem_write)

variable {pc : Bool}

theorem exec_addSp0 {s : State} {d : Reg} : exec (.addSp d 0) s = some (s.write d s.sp) := by
  simp [exec]

/-- What the slots hold from the entry state `s`. -/
def slotVal (s : State) (r : Reg) : BitVec 64 := if r = .r0 then s.lr else s.gpr r

/-- The slots: our return address and the arguments. -/
structure Slots (s : State) (m : Mem) : Prop where
  sv : Spill.Saved (fb s) (slotVal s) savedSlots m
  dl : m.readW (fb s + BitVec.ofNat 64 oDl) 64 = stackArg s 0
  inp : m.readW (fb s + BitVec.ofNat 64 oIn) 64 = stackArg s 1
  scr : m.readW (fb s + BitVec.ofNat 64 oScr) 64 = stackArg s 13

/-- The slots' region. -/
abbrev slotR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oOut, frameBytes - oOut⟩

theorem savedSlots_offs : ∀ p ∈ savedSlots, oOut ≤ p.2 ∧ p.2 + 8 ≤ oOut + (frameBytes - oOut) := by decide

theorem Slots.frame {s : State} {m m' : Mem} (S : Slots s m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (slotR s) r) : Slots s m' := by
  obtain one : ∀ {d : Nat}, oOut ≤ d → d + 8 ≤ frameBytes → m'.readW (fb s + BitVec.ofNat 64 d) 64 =
      m.readW (fb s + BitVec.ofNat 64 d) 64 := fun h₁ h₂ =>
    hf.readW (Region.contains_self _ _) (fun r hr => (hd r hr).sub_left
      (Offset.sub _ h₁ (by unfold oOut frameBytes at *; omega_using [h₂]))) (by decide)
  refine ⟨S.sv.frame hf fun p hp r hr => (hd r hr).sub_left (Offset.sub _ (savedSlots_offs p hp).1
    (savedSlots_offs p hp).2), ?_, ?_, ?_⟩
  · rw [one (by decide) (by decide)]; exact S.dl
  · rw [one (by decide) (by decide)]; exact S.inp
  · rw [one (by decide) (by decide)]; exact S.scr

/-- In the frame, from the entry state `s`: the callee-saved registers as on
entry, the slots, memory changed only in the stack the function uses. -/
structure Fr (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = fr s :: s.wr
  hi : ∀ r ∈ preserved, t.gpr r = s.gpr r
  mem : Frame [kR s] s.mem t.mem
  sl : Slots s t.mem

/-- At the call of `vg_rsa_private_checked`. -/
structure AtPriv (pc : Bool) (s t : State) : Prop extends Fr s t where
  r3 : t.gpr .r3 = s.gpr .r3
  r4 : t.gpr .r4 = s.gpr .r7
  r5 : t.gpr .r5 = s.gpr .r6
  r6 : t.gpr .r6 = s.gpr .r7
  r7 : t.gpr .r7 = s.gpr .r8
  r8 : t.gpr .r8 = s.gpr .r9
  r9 : t.gpr .r9 = stackArg s 1
  r10 : t.gpr .r10 = s.gpr .r7
  psa : ∀ i < nCallArgs pc, t.mem.readW (fb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = stackArg s (3 + i)

/-- The frame's push stores the back chain at its base. -/
theorem fb_contains (s : State) : (kR s).Contains (fb s) 8 := by
  have := frame_contains s (d := 0) (n := 8) (by decide)
  rwa [BitVec.add_zero] at this

/-- Our stack argument `j` is in the arguments' region, apart from the stack. -/
theorem arg_readG {s : State} (h : DPre pc s) {m : Mem} (hm : Frame [kR s] s.mem m) {j : Nat}
    (hj : j < if pc then 17 else 15) : m.readW (fb s + BitVec.ofNat 64 (arg j)) 64 = stackArg s j := by
  rw [← stackArgAddr_fb]
  exact hm.readW (in_aR (pc := pc) hj) (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.ka.symm) (by decide)

theorem arg_inG {s t : State} (h : DPre pc s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < if pc then 17 else 15) :
    InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 (arg j)) 8 := by
  rw [← stackArgAddr_fb, hrd, h.hrd]
  exact ⟨aR pc s, List.mem_append_left _ (by simp [rdL]), in_aR hj⟩

theorem arg_read {s : State} (h : DPre pc s) {m : Mem} (hm : Frame [kR s] s.mem m) {j : Nat} (hj : j < 15) :
    m.readW (fb s + BitVec.ofNat 64 (arg j)) 64 = stackArg s j :=
  arg_readG h hm (lt_args hj)

theorem arg_in {s t : State} (h : DPre pc s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 15) :
    InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 (arg j)) 8 :=
  arg_inG h hrd (lt_args hj)

/-- The Parameter Save Area of the call: its twelve, or with `pc` fourteen,
stack arguments. -/
abbrev psaR (pc : Bool) (s : State) : Region := ⟨fb s + BitVec.ofNat 64 96, if pc then 112 else 96⟩

theorem psa_le : (if pc then 112 else 96) ≤ 112 := by cases pc <;> decide

theorem psa_sub (s : State) : Region.Sub (psaR pc s) (kR s) := frame_sub s (by cases pc <;> decide)

theorem nCall_lt {n : Nat} (hn : n < nCallArgs pc) : n < 14 ∧ 3 + n < if pc then 17 else 15 := by
  cases pc <;> simp only [nCallArgs, Bool.false_eq_true, ↓reduceIte] at hn ⊢ <;> omega_using [hn]

theorem fR_sub (s : State) : Region.Sub ⟨fb s, frameBytes⟩ (kR s) := by
  have := frame_sub s (d := 0) (n := frameBytes) (by omega_using [])
  rwa [BitVec.add_zero] at this

/-- The saves, from the state after the frame's push: `r12` holds the frame's
base, the slots of `savedSlots` hold our return address and the arguments,
and memory is changed only in the frame. -/
theorem saves_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ v, v.sp = fb s → v.rd = s.rd → v.wr = fr s :: s.wr → v.gpr .r12 = fb s →
      (∀ r, r ≠ .r12 → r ≠ .r0 → v.gpr r = s.gpr r) → Frame [kR s] s.mem v.mem →
      Spill.Saved (fb s) (slotVal s) savedSlots v.mem → WP isa (.block rest) v Q) :
    WP isa (.block (saves ++ rest)) (allocated frameBytes s) Q := by
  rw [show saves = [fp, .mflr .r0] ++ Spill.saveCode .r12 savedSlots from rfl, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine WP.block_cons_iff.mpr ⟨_, exec_addSp0, WP.block_cons_iff.mpr ⟨_, exec_mflr, ?_⟩⟩
  generalize hu : ((allocated frameBytes s).write .r12 (allocated frameBytes s).sp).write .r0
    ((allocated frameBytes s).write .r12 (allocated frameBytes s).sp).lr = u
  obtain u12 : u.gpr .r12 = fb s := by
    rw [← hu, gpr_write_of_ne _ _ (show Reg.r12 ≠ .r0 by decide), gpr_write_self]; rfl
  obtain uwr : u.wr = fr s :: s.wr := by rw [← hu]; rfl
  obtain ug : ∀ p ∈ savedSlots, u.gpr p.1 = slotVal s p.1 := by
    intro p hp
    simp only [savedSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [← hu, State.write, slotVal, allocated]
  refine Spill.save_ok (b := .r12) (l := savedSlots) (by decide) (by decide) (fun p hp => ?_) ?_
  · have := savedSlots_offs p hp
    rw [uwr, u12]; exact in_fr s _ (by unfold oOut at this; omega_using [this]) (by unfold oOut frameBytes at *; omega_using [this])
  refine k _ (by rw [← hu]; rfl) (by rw [← hu]; rfl) uwr u12 (fun r h12 h0 => ?_) ?_ ?_
  · show u.gpr r = s.gpr r
    rw [← hu, gpr_write_of_ne _ _ h0, gpr_write_of_ne _ _ h12]; rfl
  · show Frame [kR s] s.mem (Spill.saveMem u.mem (u.gpr .r12) u.gpr savedSlots)
    obtain hum : u.mem = s.mem.write (fb s) 8 s.sp := by rw [← hu]; rfl
    obtain f1 : Frame [kR s] s.mem u.mem := by
      rw [hum]; exact Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ (fb_contains s)
    rw [u12]
    exact f1.trans ((Spill.saveMem_frame_base (n := frameBytes) (fun p hp => by
      have := savedSlots_offs p hp; unfold oOut frameBytes at *; omega_using [this]) (by decide) _ _ _).sub
      fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, fR_sub s⟩)
  · show Spill.Saved (fb s) (slotVal s) savedSlots (Spill.saveMem u.mem (u.gpr .r12) u.gpr savedSlots)
    rw [u12]
    exact fun p hp => (Spill.saveMem_saved (by decide) _ _ _ p hp).trans (ug p hp)

/-- After copying the first `n` stack arguments, from `w`. -/
structure CI (pc : Bool) (s w : State) (n : Nat) (t : State) : Prop where
  keep : Keep [.r0] w t
  mem : Frame [psaR pc s] w.mem t.mem
  psa : ∀ i < n, t.mem.readW (fb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = stackArg s (3 + i)

theorem copy_step {s w : State} (h : DPre pc s) (hw12 : w.gpr .r12 = fb s) (hrd : w.rd = s.rd)
    (hwr : w.wr = fr s :: s.wr) (hm : Frame [kR s] s.mem w.mem) {n : Nat} (hn : n < nCallArgs pc) {t : State}
    (hc : CI pc s w n t) : WP isa (.block (copyArg n)) t (CI pc s w (n + 1)) := by
  obtain ⟨hn14, hn'⟩ := nCall_lt hn
  obtain t12 : t.gpr .r12 = fb s := (hc.keep.gpr _ (by decide)).trans hw12
  obtain hmt : Frame [kR s] s.mem t.mem := hm.trans (hc.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, psa_sub s⟩)
  obtain hin : InRegions (t.rd ++ t.wr) (t.gpr .r12 + BitVec.ofNat 64 (arg (3 + n))) 8 := by
    rw [t12]; exact arg_inG h (hc.keep.rd.trans hrd) hn'
  obtain hv : t.mem.readW (t.gpr .r12 + BitVec.ofNat 64 (arg (3 + n))) 64 = stackArg s (3 + n) := by
    rw [t12]; exact arg_readG h hmt hn'
  obtain ho : InRegions t.wr (t.gpr .r12 + BitVec.ofNat 64 (96 + 8 * n)) 8 := by
    rw [t12, hc.keep.wr, hwr]; exact in_fr s _ (by omega_using []) (by unfold frameBytes; omega_using [hn14])
  obtain harg : arg (3 + n) < 2 ^ 15 ∧ arg (3 + n) % 4 = 0 := by unfold arg frameBytes; omega_using [hn14]
  apply WP.of_runBlock
  simp only [copyArg, mvArg, runBlock_cons, runStep_some, exec_load_d (show Reg.r12 ≠ .r0 by decide) harg hin]
  rw [exec_store_d (show Reg.r12 ≠ .r0 by decide) ⟨by omega_using [hn14], by omega_using []⟩
    (by rw [gpr_write_of_ne _ _ (show Reg.r12 ≠ .r0 by decide)]; exact ho)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  rw [gpr_write_of_ne _ _ (show Reg.r12 ≠ .r0 by decide), gpr_write_self, mem_write, hv, t12]
  refine ⟨⟨fun r hr => ?_, hc.keep.rd, hc.keep.wr, hc.keep.sp, hc.keep.lr⟩, ?_, fun i hi => ?_⟩
  · show (t.write .r0 _).gpr r = w.gpr r
    rw [gpr_write_of_ne _ _ (by simpa using hr)]; exact hc.keep.gpr r hr
  · have := psa_le (pc := pc)
    exact hc.mem.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using [])
      (by cases pc <;> simp only [nCallArgs, Bool.false_eq_true, ↓reduceIte] at hn ⊢ <;> omega_arith) (by omega_using [this]))
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega_using [hi])) (by omega_arith) (by omega_using [hn14])) (by decide)]
      exact hc.psa i hi
    · rw [Mem.readW_writeW_self64]

theorem copies_ok {s w : State} (h : DPre pc s) (hw12 : w.gpr .r12 = fb s) (hrd : w.rd = s.rd)
    (hwr : w.wr = fr s :: s.wr) (hm : Frame [kR s] s.mem w.mem) :
    WP isa (.block ((List.range (nCallArgs pc)).flatMap copyArg)) w (CI pc s w (nCallArgs pc)) :=
  wp_range_flatMap (M := isa) (CI pc s w) (fun _ _ hn hc => copy_step h hw12 hrd hwr hm hn hc) (nCallArgs pc)
    (Nat.le_refl _) w
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- A word of the frame's slots or Parameter Save Area is writable and in
the stack the function uses. -/
theorem slot_in (s : State) {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ frameBytes) :
    InRegions (fr s :: s.wr) (fb s + BitVec.ofNat 64 d) 8 := in_fr s _ h₁ h₂

theorem slotMoves_ok {s v : State} (h : DPre pc s) (h12 : v.gpr .r12 = fb s) (hrd : v.rd = s.rd)
    (hwr : v.wr = fr s :: s.wr) (hm : Frame [kR s] s.mem v.mem) :
    WP isa (.block slotMoves) v fun w =>
      (w.mem = ((v.mem.writeW (fb s + BitVec.ofNat 64 oDl) (stackArg s 0)).writeW (fb s + BitVec.ofNat 64 oIn)
        (stackArg s 1)).writeW (fb s + BitVec.ofNat 64 oScr) (stackArg s 13)) ∧ Keep [.r0] v w := by
  obtain fw : ∀ {m : Mem} {d : Nat}, Frame [kR s] s.mem m → d + 8 ≤ frameBytes → ∀ x : BitVec 64,
      Frame [kR s] s.mem (m.writeW (fb s + BitVec.ofNat 64 d) x) :=
    fun hm hd x => hm.writeW (List.mem_singleton_self _) _ (frame_contains s hd)
  obtain a0 := arg_read h hm (j := 0) (by decide)
  obtain a1 := arg_read h (fw hm (d := oDl) (by decide) (stackArg s 0)) (j := 1) (by decide)
  obtain a13 := arg_read h (fw (fw hm (d := oDl) (by decide) (stackArg s 0)) (d := oIn) (by decide)
    (stackArg s 1)) (j := 13) (by decide)
  obtain i0 := arg_in h hrd (j := 0) (by decide)
  obtain i1 := arg_in h hrd (j := 1) (by decide)
  obtain i13 := arg_in h hrd (j := 13) (by decide)
  obtain o1 : InRegions v.wr (fb s + BitVec.ofNat 64 oDl) 8 := by rw [hwr]; exact slot_in s (by decide) (by decide)
  obtain o2 : InRegions v.wr (fb s + BitVec.ofNat 64 oIn) 8 := by rw [hwr]; exact slot_in s (by decide) (by decide)
  obtain o3 : InRegions v.wr (fb s + BitVec.ofNat 64 oScr) 8 := by rw [hwr]; exact slot_in s (by decide) (by decide)
  obtain c0 : arg 0 < 2 ^ 15 ∧ arg 0 % 4 = 0 := by decide
  obtain c1 : arg 1 < 2 ^ 15 ∧ arg 1 % 4 = 0 := by decide
  obtain c13 : arg 13 < 2 ^ 15 ∧ arg 13 % 4 = 0 := by decide
  obtain d1 : oDl < 2 ^ 15 := by decide
  obtain d2 : oDl % 4 = 0 := by decide
  obtain d3 : oIn < 2 ^ 15 := by decide
  obtain d4 : oIn % 4 = 0 := by decide
  obtain d5 : oScr < 2 ^ 15 := by decide
  obtain d6 : oScr % 4 = 0 := by decide
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  unfold slotMoves mvArg
  prun [h12, c0, c1, c13, d1, d2, d3, d4, d5, d6, i0, i1, i13, o1, o2, o3, a0, a1, a13]

theorem setup_ok {s : State} (h : DPre pc s) :
    WP isa (.block (setup pc)) (allocated frameBytes s) (AtPriv pc s) := by
  rw [show setup pc = saves ++ (slotMoves ++ ((List.range (nCallArgs pc)).flatMap copyArg ++ privRegs)) by
    simp only [setup, List.append_assoc]]
  refine saves_ok fun v vsp vrd vwr v12 hg vm vsv => ?_
  rw [WP.block_append_iff]
  refine WP.mono (slotMoves_ok h v12 vrd vwr vm) fun w ⟨wm, kw⟩ => ?_
  obtain w12 : w.gpr .r12 = fb s := (kw.gpr _ (by decide)).trans v12
  -- the slots after the moves
  obtain sep : ∀ {d e : Nat}, d + 8 ≤ e ∨ e + 8 ≤ d → e + 8 ≤ frameBytes → d + 8 ≤ frameBytes →
      Mem.Sep (fb s + BitVec.ofNat 64 d) 8 (fb s + BitVec.ofNat 64 e) 8 := fun h₁ h₂ h₃ =>
    Offset.sep _ h₁ (by unfold frameBytes at *; omega_using [h₃]) (by unfold frameBytes at *; omega_using [h₂])
  obtain fm : Frame [kR s] s.mem w.mem := by
    rw [wm]
    exact ((vm.writeW (List.mem_singleton_self _) _ (frame_contains s (by decide))).writeW
      (List.mem_singleton_self _) _ (frame_contains s (by decide))).writeW (List.mem_singleton_self _) _
      (frame_contains s (by decide))
  obtain sl : Slots s w.mem := by
    obtain f3 : Frame [⟨fb s + BitVec.ofNat 64 oDl, 24⟩] v.mem w.mem := by
      rw [wm]
      exact ((Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
        (Offset.contains _ (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by decide) (by decide) (by decide))
    refine ⟨vsv.frame f3 fun p hp r hr => ?_, ?_, ?_, ?_⟩
    · rw [List.mem_singleton.mp hr]
      have : p ∈ savedSlots := hp
      simp only [savedSlots, List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · rw [wm, Mem.readW_writeW_sep (sep (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_sep (sep (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
    · rw [wm, Mem.readW_writeW_sep (sep (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
    · rw [wm, Mem.readW_writeW_self64]
  rw [WP.block_append_iff]
  refine WP.mono (copies_ok h w12 (kw.rd.trans vrd) (kw.wr.trans vwr) fm) fun t hc => ?_
  obtain t12 : t.gpr .r12 = fb s := (hc.keep.gpr _ (by decide)).trans w12
  obtain pl := psa_le (pc := pc)
  obtain tm : Frame [kR s] s.mem t.mem := fm.trans (hc.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, psa_sub s⟩)
  obtain tsl : Slots s t.mem := sl.frame hc.mem fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by unfold oOut; omega_using [pl])) (by unfold oOut frameBytes; omega_using []) (by omega_using [pl])
  obtain kt : ∀ r, r ≠ .r12 → r ≠ .r0 → t.gpr r = s.gpr r := fun r h1 h2 =>
    (hc.keep.gpr r (by simpa using h2)).trans ((kw.gpr r (by simpa using h2)).trans (hg r h1 h2))
  have i1 : t.mem.readW (fb s + BitVec.ofNat 64 oIn) 64 = stackArg s 1 := tsl.inp
  obtain hIn : InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 oIn) 8 := by
    rw [hc.keep.rd, hc.keep.wr, kw.rd, kw.wr, vwr]; exact in_fr' s _ _ (by decide) (by decide)
  obtain c1 : oIn < 2 ^ 15 := by decide
  obtain c2 : oIn % 4 = 0 := by decide
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r4, .r5, .r6, .r7, .r8, .r9, .r10] (Q := fun u =>
    u.gpr .r4 = s.gpr .r7 ∧ u.gpr .r5 = s.gpr .r6 ∧ u.gpr .r6 = s.gpr .r7 ∧ u.gpr .r7 = s.gpr .r8 ∧
      u.gpr .r8 = s.gpr .r9 ∧ u.gpr .r9 = stackArg s 1 ∧ u.gpr .r10 = s.gpr .r7 ∧ u.mem = t.mem) ?_ rfl)
    fun u ⟨⟨u4, u5, u6, u7, u8, u9, u10, um⟩, ku⟩ => ?_
  · unfold privRegs
    prun [t12, c1, c2, hIn, i1, kt .r6 (by decide) (by decide), kt .r7 (by decide) (by decide),
      kt .r8 (by decide) (by decide), kt .r9 (by decide) (by decide), BitVec.or_self, Impl.AesGcm.PPC64LE.mov]
  obtain kall : ∀ r, r ∉ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12, .r0] → u.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [ku.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]),
      kt r hr.2.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2]
  refine ⟨⟨ku.sp.trans (hc.keep.sp.trans (kw.sp.trans vsp)), ku.rd.trans (hc.keep.rd.trans (kw.rd.trans vrd)),
    ku.wr.trans (hc.keep.wr.trans (kw.wr.trans vwr)), fun r hr => kall r (by revert r; decide), um ▸ tm,
    um ▸ tsl⟩, kall _ (by decide), u4, u5, u6, u7, u8, u9, u10, fun i hi => by rw [um]; exact hc.psa i hi⟩

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
end

end


/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: the call of `vg_rsa_private_checked`

The regions the call is narrowed to (`callRd`, `callWr`), its precondition
(`preP_entry`, `Priv.pre_of_preP`), and the call (`call_ok`, into `AtD`):
`EM` or zeros in `out`, and the result.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt

variable {pc : Bool}

/-- `out`, of `k` bytes. -/
abbrev outR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r7).toNat⟩

theorem outR_eq {s : State} (h : DPre pc s) : outR s = oR s := by simp only [outR, oR, h.h4]

/-- The input, of `k` bytes. -/
abbrev inR (s : State) : Region := ⟨stackArg s 1, (s.gpr .r7).toNat⟩

theorem inR_eq {s : State} (h : DPre pc s) : inR s = iR s := by simp only [inR, iR, h.hi]

/-- The regions the call reads and writes. -/
abbrev callRd (pc : Bool) (s : State) : List Region :=
  [nR s, eR s, inR s, pR s, qR s, dpR s, dqR s, qiR s] ++ (if pc then [preR s] else []) ++ [psaR pc s]

abbrev callWr (s : State) : List Region := [outR s, sR s]

/-- The call's narrowed entry state. -/
abbrev callE (pc : Bool) (s t : State) : State := t.callEntry.withRegions (callRd pc s) (callWr s)

theorem callE_gpr (s t : State) {r : Reg} (hr : r ∉ linkRegs := by decide) : (callE pc s t).gpr r = t.gpr r :=
  State.callEntry_gpr t hr

theorem callE_stackArg {s t : State} (A : AtPriv pc s t) {i : Nat} (hi : i < nCallArgs pc) :
    stackArg (callE pc s t) i = stackArg s (3 + i) := by
  show t.mem.readW (stackArgAddr (callE pc s t) i) 64 = _
  rw [stackArgAddr, show (callE pc s t).sp = fb s from A.sp, show 32 + 8 * (8 + i) = 96 + 8 * i by omega_using []]
  exact A.psa i hi

theorem callE_addr {s t : State} (A : AtPriv pc s t) :
    stackArgAddr (callE pc s t) 0 = fb s + BitVec.ofNat 64 96 := by
  rw [stackArgAddr, show (callE pc s t).sp = fb s from A.sp]

theorem lt_nCall {i : Nat} (hi : i < 12) : i < nCallArgs pc := by
  cases pc <;> simp only [nCallArgs, Bool.false_eq_true, ↓reduceIte] <;> omega_using [hi]

theorem preP_entry {s t : State} (h : DPre pc s) (A : AtPriv pc s t) : Rsa.PPC64LE.Priv.PreP pc (callE pc s t) := by
  have hk := h.k2
  obtain fbt := fb_toNat h
  obtain kbt := kb_toNat h
  unfold stackBytes frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes at kbt
  unfold frameBytes at fbt
  obtain sa := fun i (hi : i < 12) => callE_stackArg A (i := i) (lt_nCall hi)
  have hsp : (callE pc s t).sp = fb s := A.sp
  obtain pl := psa_le (pc := pc)
  obtain ps : Region.Sub (psaR pc s) (kR s) := psa_sub s
  obtain hK : Rsa.PPC64LE.Priv.kR (callE pc s t) = ⟨kb s, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := by
    simp only [Rsa.PPC64LE.Priv.kR, Rsa.PPC64LE.Priv.fb, hsp, fb_eq, BitVec.add_sub_cancel]
  obtain ka : Region.Disjoint ⟨kb s, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (psaR pc s) := by
    show Region.Disjoint _ ⟨fb s + BitVec.ofNat 64 96, _⟩
    rw [fb_eq, Offset.add_add]
    exact (Offset.disjoint_base _ (by unfold Impl.Rsa.PPC64LE.Priv.frameBytes; omega_using [])
      (by unfold Impl.Rsa.PPC64LE.Priv.frameBytes; omega_using [pl])).symm
  obtain cs' : Region.Sub ⟨kb s, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (kR s) := by
    have := callee_sub s; rwa [fb_eq, BitVec.add_sub_cancel] at this
  obtain g3 : (callE pc s t).gpr .r3 = s.gpr .r3 := (callE_gpr (pc := pc) s t).trans A.r3
  obtain g4 : (callE pc s t).gpr .r4 = s.gpr .r7 := (callE_gpr (pc := pc) s t).trans A.r4
  obtain g5 : (callE pc s t).gpr .r5 = s.gpr .r6 := (callE_gpr (pc := pc) s t).trans A.r5
  obtain g6 : (callE pc s t).gpr .r6 = s.gpr .r7 := (callE_gpr (pc := pc) s t).trans A.r6
  obtain g7 : (callE pc s t).gpr .r7 = s.gpr .r8 := (callE_gpr (pc := pc) s t).trans A.r7
  obtain g8 : (callE pc s t).gpr .r8 = s.gpr .r9 := (callE_gpr (pc := pc) s t).trans A.r8
  obtain g9 : (callE pc s t).gpr .r9 = stackArg s 1 := (callE_gpr (pc := pc) s t).trans A.r9
  obtain g10 : (callE pc s t).gpr .r10 = s.gpr .r7 := (callE_gpr (pc := pc) s t).trans A.r10
  obtain hO : Rsa.PPC64LE.Priv.oR (callE pc s t) = oR s := by simp only [Rsa.PPC64LE.Priv.oR, g3, g4, oR, h.h4]
  obtain hN : Rsa.PPC64LE.Priv.nR (callE pc s t) = nR s := by simp only [Rsa.PPC64LE.Priv.nR, g5, g6]
  obtain hE : Rsa.PPC64LE.Priv.eR (callE pc s t) = eR s := by simp only [Rsa.PPC64LE.Priv.eR, g7, g8]
  obtain hI : Rsa.PPC64LE.Priv.iR (callE pc s t) = iR s := by simp only [Rsa.PPC64LE.Priv.iR, g9, g10, iR, h.hi]
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
  obtain wo' : (s.gpr .r3).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64 := h.h4 ▸ h.wo
  refine ⟨by rw [hsp]; unfold Impl.Rsa.PPC64LE.Priv.frameBytes; omega_using [fbt, kbt], by rw [hsp]; omega_using [fbt], ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Rsa.PPC64LE.Priv.rdL]
    rw [hN, hE, hI, hP, hQ, hDP, hDQ, hQI, hA, ← inR_eq h]
    cases pc
    · rfl
    · simp only [↓reduceIte, Rsa.PPC64LE.Priv.preR, callE_stackArg A (i := 12) (by decide),
        callE_stackArg A (i := 13) (by decide)]
      rfl
  · rw [hO, hS, ← outR_eq h]; rfl
  · rw [hO, hN]; exact h.on
  · rw [hO, hE]; exact h.oe
  · rw [hO, hI]; exact h.oi
  · rw [hO, hP]; exact h.op
  · rw [hO, hQ]; exact h.oq
  · rw [hO, hDP]; exact h.odp
  · rw [hO, hDQ]; exact h.odq
  · rw [hO, hQI]; exact h.oqi
  · rw [hO, hS]; exact h.os
  · rw [hO, hA]; exact (h.ko.sub_left ps).symm
  · rw [hN, hS]; exact h.ns
  · rw [hE, hS]; exact h.es
  · rw [hI, hS]; exact h.is
  · rw [hP, hS]; exact h.ps
  · rw [hQ, hS]; exact h.qs
  · rw [hDP, hS]; exact h.dps
  · rw [hDQ, hS]; exact h.dqs
  · rw [hQI, hS]; exact h.qis
  · rw [hS, hA]; exact (h.ks.sub_left ps).symm
  · rw [hK, hO]; exact h.ko.sub_left cs'
  · rw [hK, hN]; exact h.kn.sub_left cs'
  · rw [hK, hE]; exact h.ke.sub_left cs'
  · rw [hK, hI]; exact h.ki.sub_left cs'
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
  · rw [g9, g10, ← h.hi]; exact h.wi
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
  · rw [s5, s1]; exact h.h8
  · rw [s9, s1]; exact h.h12
  · rw [s7, s3]; exact h.h10
  · rw [g6, s11]; exact h.hs

/-- From the call on: `Fr`, with `out` and the working space written too. -/
structure Fr2 (s u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = fr s :: s.wr
  hi : ∀ r ∈ preserved, u.gpr r = s.gpr r
  mem : Frame [kR s, oR s, sR s] s.mem u.mem
  sl : Slots s u.mem

/-- The outcome of `vg_rsa_private_checked` of the input, from the caller's
buffers. -/
abbrev privOut (s u : State) : Prop :=
  Spec.Rsa.writtenOutcome u.mem (s.gpr .r3) (s.gpr .r7).toNat ((u.gpr .r3).setWidth 32)
    (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .r7).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat))

/-- After the call. -/
structure AtD (s u : State) : Prop extends Fr2 s u where
  out : privOut s u

theorem bytes_of_frame {s : State} {rs : List Region} {m : Mem} (hf : Frame rs s.mem m) {p : Addr}
    {len : Nat} (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, len⟩ r) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) hd hl (List.mem_range.mp hi)

theorem call_covers {s t : State} (h : DPre pc s) (A : AtPriv pc s t) :
    Covers (callRd pc s ++ callWr s) (t.rd ++ t.wr) ∧ Covers (callWr s) t.wr := by
  obtain pl := psa_le (pc := pc)
  obtain hw : Covers (callWr s) t.wr := by
    rw [A.wr, h.hwr, ← outR_eq h]
    exact Covers.of_mem fun r hr => by
      simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  rw [A.rd, A.wr, h.hrd]
  obtain hleft : r ∈ rdL pc s → Covers [r] (rdL pc s ++ fr s :: s.wr) := fun h =>
    Covers.left (Covers.of_mem fun r' hr' => by rw [List.mem_singleton.mp hr']; exact h)
  simp only [callRd, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, inR_eq h] at hr
  rcases hr with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hp) | rfl
  · exact hleft (by simp [rdL])
  · exact hleft (by simp [rdL])
  · exact hleft (by simp [rdL])
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
theorem preX_entry {s t : State} (h : DPre true s) (X : PreX s) (A : AtPriv true s t) :
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
    obtain hw := VG.Proof.Rsa.PPC64LE.Priv.words_of_frame A.mem (p := stackArg s 15) (n := (stackArg s 16).toNat)
      (fun r hr => by rw [List.mem_singleton.mp hr, Nat.mul_comm]; exact X.kP.symm) (by have := X.wP; omega_using [this])
    simp only [Rsa.PPC64LE.Priv.PreHyp, State.withRegions_mem, State.callEntry_mem,
      callE_gpr (pc := true) s t (r := .r5), callE_gpr (pc := true) s t (r := .r6), A.r5, A.r6, sa 0 (by decide),
      sa 1 (by decide), sa 2 (by decide), sa 3 (by decide), sa 12 (by decide), sa 13 (by decide), hw]
    rw [hb h.kn.symm (by have := h.wn; omega_using []), hb h.kp.symm (by have := h.wp; omega_using []),
      hb h.kq.symm (by have := h.wq; omega_using [])]
    exact X.hyp rfl

/-- The call of `vg_rsa_private_checked`, or with `pc` of
`vg_rsa_private_checked_precomputed`. -/
theorem call_priv {s t : State} (h : DPre pc s) (X : pc = true → PreX s) (A : AtPriv pc s t) :
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

theorem call_ok {s t : State} (h : DPre pc s) (X : pc = true → PreX s) (A : AtPriv pc s t) {Q : State → Prop}
    (hQ : ∀ u, AtD s u → Q u) : WP isa (privCall pc) t Q := by
  have hk := h.k2
  obtain cs := callee_sub s
  refine WP.mono (call_priv h X A) fun u ⟨hrd, hwr, hsp, hf, hpres, hpost⟩ => hQ u ?_
  have hb : below (fb s) Impl.Rsa.PPC64LE.Priv.frameBytes =
      ⟨fb s - BitVec.ofNat 64 Impl.Rsa.PPC64LE.Priv.frameBytes, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := rfl
  rw [hb] at hf
  simp only [callWr, List.cons_append, List.nil_append, outR_eq h] at hf
  have hp : ∀ r ∈ preserved, u.gpr r = t.gpr r := hpres
  obtain sd : ∀ r ∈ [oR s, sR s, (⟨fb s - BitVec.ofNat 64 Impl.Rsa.PPC64LE.Priv.frameBytes,
      Impl.Rsa.PPC64LE.Priv.frameBytes⟩ : Region)], Region.Disjoint (slotR s) r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.ko.sub_left (frame_sub s (by decide))
    · exact h.ks.sub_left (frame_sub s (by decide))
    · show Region.Disjoint ⟨fb s + BitVec.ofNat 64 oOut, _⟩ _
      rw [fb_eq, BitVec.add_sub_cancel, Offset.add_add]
      exact Offset.disjoint_base _ (by decide) (by decide)
  refine ⟨⟨hsp.trans A.sp, hrd.trans A.rd, hwr.trans A.wr, fun r hr => (hp r hr).trans (A.hi r hr), ?_,
    A.sl.frame hf sd⟩, ?_⟩
  · refine A.mem.sub (fun r hr => ?_) |>.trans (hf.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self .., cs⟩
  · have sa := fun i (hi : i < 12) => callE_stackArg A (i := i) (lt_nCall hi)
    simp only [Rsa.PPC64LE.Priv.fnPost, State.withRegions_mem,
      State.withRegions_gpr, State.callEntry_mem, callE_gpr (pc := pc) s t (r := .r3),
      callE_gpr (pc := pc) s t (r := .r5), callE_gpr (pc := pc) s t (r := .r6), callE_gpr (pc := pc) s t (r := .r7),
      callE_gpr (pc := pc) s t (r := .r8), callE_gpr (pc := pc) s t (r := .r9),
      A.r3, A.r5, A.r6, A.r7, A.r8, A.r9, sa 0 (by decide), sa 1 (by decide), sa 2 (by decide), sa 3 (by decide),
      sa 4 (by decide), sa 6 (by decide), sa 8 (by decide), Nat.reduceAdd] at hpost
    obtain hb := fun {p : Addr} {len : Nat} (hd : Region.Disjoint ⟨p, len⟩ (kR s)) (hl : len ≤ 2 ^ 64) =>
      bytes_of_frame (s := s) (rs := [kR s]) A.mem (p := p) (len := len)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl
    rw [hb h.kn.symm (by have := h.wn; omega_using []), hb h.ke.symm (by have := h.we; omega_using []),
      hb (h.hi ▸ h.ki.symm) (by have := h.wi; rw [h.hi] at this; omega_using []),
      hb h.kp.symm (by have := h.wp; omega_using []), hb h.kq.symm (by have := h.wq; omega_using []),
      hb (h.h8 ▸ h.kdp.symm) (by have := h.wdp; omega_using []), hb (h.h10 ▸ h.kdq.symm) (by have := h.wdq; omega_using []),
      hb (h.h12 ▸ h.kqi.symm) (by have := h.wqi; omega_using [])] at hpost
    exact hpost

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

end

end


/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: after the private-key operation

From the private-key operation's result in its slot to the output, the
function writes only the first `scrBytes` bytes of `scratch`, the stack
below its frame and its slots `oI` and `oNB` (`Safe`): through all of it,
`Fr2`, the result `R` in its slot and `EM` in `out` stay as they are
(`Post`, `Post.step`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt

variable {pc : Bool}

/-- The part of `scratch` used after the private-key operation. -/
def scrBytes : Nat := 3440

/-- `scratch + a`. -/
abbrev scA (s : State) (a : Nat) : Addr := stackArg s 13 + BitVec.ofNat 64 a

/-- The part of `scratch` used. -/
abbrev SC (s : State) : Region := ⟨stackArg s 13, scrBytes⟩

/-- The stack below our frame, which the private-key operation used and the
hash functions' frames use. -/
abbrev LOW (s : State) : Region :=
  ⟨fb s - BitVec.ofNat 64 Impl.Rsa.PPC64LE.Priv.frameBytes, Impl.Rsa.PPC64LE.Priv.frameBytes⟩

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x hx => h₂ x (h₁ x hx)

theorem scr_le {s : State} (h : DPre pc s) : scrBytes ≤ (stackArg s 14).toNat * 8 := by
  have := h.hs; have := h.k1; unfold Spec.Rsa.scratchWords at *; unfold scrBytes; omega_arith

theorem sc_sub {s : State} (h : DPre pc s) : Region.Sub (SC s) (sR s) := Region.sub_prefix (scr_le h)

theorem scSub {s : State} {a n : Nat} (ha : a + n ≤ scrBytes) : Region.Sub ⟨scA s a, n⟩ (SC s) :=
  Offset.sub_base _ ha

theorem scD {s : State} (h : DPre pc s) {a n b m : Nat} (hab : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ scrBytes)
    (hb : b + m ≤ scrBytes) : Region.Disjoint ⟨scA s a, n⟩ ⟨scA s b, m⟩ := by
  have := h.ws; have := scr_le h
  exact Offset.disjoint _ hab (by omega_arith) (by omega_arith)

theorem low_sub (s : State) {n : Nat} (hn : n ≤ Impl.Rsa.PPC64LE.Priv.frameBytes) :
    Region.Sub (below (fb s) n) (LOW s) :=
  Offset.sub_below _ hn (by omega_using [hn])

/-- A word of our frame misses the stack below it. -/
theorem fr_low (s : State) {d n : Nat} (hd : d + n ≤ frameBytes) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ (LOW s) :=
  Offset.disjoint_below _ (by unfold frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega_using [hd])

/-- What a step after the private-key operation may write. -/
def Safe (s : State) (r : Region) : Prop :=
  Region.Sub r (SC s) ∨ Region.Sub r (LOW s) ∨
    ∃ d, oI ≤ d ∧ d + r.len ≤ oLr ∧ r.base = fb s + BitVec.ofNat 64 d

theorem safe_frame {s : State} (h : DPre pc s) {r : Region} (hr : Safe s r) {d n : Nat}
    (hd : d + n ≤ oI ∨ oLr ≤ d) (hn : d + n ≤ frameBytes) : Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r := by
  rcases hr with hr | hr | ⟨e, h₁, h₂, hb⟩
  · exact ((h.ks.sub_left (frame_sub s hn)).sub_right (sc_sub h)).sub_right hr
  · exact (fr_low s hn).sub_right hr
  · obtain ⟨b, l⟩ := r
    simp only at hb h₂; subst hb
    unfold oI oLr at *; unfold frameBytes at hn
    exact Offset.disjoint _ (by omega_using [hd, h₁, h₂]) (by omega_using [hn]) (by omega_using [h₂])

theorem safe_out {s : State} (h : DPre pc s) {r : Region} (hr : Safe s r) : Region.Disjoint (oR s) r := by
  rcases hr with hr | hr | ⟨e, h₁, h₂, hb⟩
  · exact (h.os.sub_right (sc_sub h)).sub_right hr
  · exact h.ko.symm.sub_right (sub_trans hr (callee_sub s))
  · obtain ⟨b, l⟩ := r
    simp only at hb h₂; subst hb
    exact h.ko.symm.sub_right (frame_sub s (by unfold oLr frameBytes at *; omega_using [h₂]))

theorem safe_in {s : State} (h : DPre pc s) {r : Region} (hr : Safe s r) :
    ∃ X ∈ [kR s, oR s, sR s], Region.Sub r X := by
  rcases hr with hr | hr | ⟨e, h₁, h₂, hb⟩
  · exact ⟨_, by simp, sub_trans hr (sc_sub h)⟩
  · exact ⟨_, by simp, sub_trans hr (callee_sub s)⟩
  · obtain ⟨b, l⟩ := r
    simp only at hb h₂; subst hb
    exact ⟨_, by simp, frame_sub s (by unfold oLr frameBytes at *; omega_using [h₂])⟩

theorem savedSlots_words : ∀ p ∈ savedSlots, p.2 + 8 ≤ Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR ∨ oLr ≤ p.2 := by
  decide

/-- The slots stay through a step that writes none of their words. -/
theorem Slots.words {s : State} {m m' : Mem} (S : Slots s m) {ws : List Region} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, ∀ d, d + 8 ≤ Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR ∨ oLr ≤ d → d + 8 ≤ frameBytes →
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r) : Slots s m' := by
  obtain one : ∀ {d : Nat}, d + 8 ≤ Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR → m'.readW (fb s + BitVec.ofNat 64 d) 64 =
      m.readW (fb s + BitVec.ofNat 64 d) 64 := fun h₁ =>
    hf.readW (Region.contains_self _ _) (fun r hr => hd r hr _ (.inl h₁)
      (by unfold Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR frameBytes at *; omega_using [h₁])) (by decide)
  refine ⟨S.sv.frame hf fun p hp r hr => hd r hr _ (savedSlots_words p hp) ?_, ?_, ?_, ?_⟩
  · have : p ∈ savedSlots := hp
    simp only [savedSlots, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [one (by decide)]; exact S.dl
  · rw [one (by decide)]; exact S.inp
  · rw [one (by decide)]; exact S.scr

/-- The slots stay through a step that writes only where it may. -/
theorem Slots.safe {s : State} (h : DPre pc s) {m m' : Mem} (S : Slots s m) {ws : List Region}
    (hf : Frame ws m m') (hs : ∀ r ∈ ws, Safe s r) : Slots s m' :=
  S.words hf fun r hr d hd hn => safe_frame h (hs r hr)
    (hd.imp_left fun h' => by unfold Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR oI at *; omega_using [h']) hn

section
variable {s : State} {m : Mem} (S : Slots s m)
include S

theorem Slots.out : m.readW (fb s + BitVec.ofNat 64 oOut) 64 = s.gpr .r3 :=
  (S.sv (.r3, oOut) (by decide)).trans (by simp [slotVal])
theorem Slots.ml : m.readW (fb s + BitVec.ofNat 64 oML) 64 = s.gpr .r5 :=
  (S.sv (.r5, oML) (by decide)).trans (by simp [slotVal])
theorem Slots.k : m.readW (fb s + BitVec.ofNat 64 oK) 64 = s.gpr .r7 :=
  (S.sv (.r7, oK) (by decide)).trans (by simp [slotVal])
theorem Slots.d : m.readW (fb s + BitVec.ofNat 64 oD) 64 = s.gpr .r10 :=
  (S.sv (.r10, oD) (by decide)).trans (by simp [slotVal])
theorem Slots.lr : m.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr :=
  (S.sv (.r0, oLr) (by decide)).trans (by simp [slotVal])

end

/-- A slot of the frame can be read. -/
theorem slotIn {s u : State} (hwr : u.wr = fr s :: s.wr) {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ frameBytes) :
    InRegions (u.rd ++ u.wr) (fb s + BitVec.ofNat 64 d) 8 := by
  rw [hwr]; exact in_fr' s _ _ h₁ h₂

theorem slotOut {s u : State} (hwr : u.wr = fr s :: s.wr) {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ frameBytes) :
    InRegions u.wr (fb s + BitVec.ofNat 64 d) 8 := by
  rw [hwr]; exact in_fr s _ h₁ h₂

/-- After the private-key operation: `Fr2`, its result `R` in its slot and
`EM` in `out`. -/
structure Post (s : State) (R : BitVec 64) (EM : List Byte) (u : State) : Prop extends Fr2 s u where
  r : u.mem.readW (fb s + BitVec.ofNat 64 Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR) 64 = R
  em : Spec.Rsa.bytesAt u.mem (s.gpr .r3) (s.gpr .r7).toNat = EM
  /-- The result is a 32-bit value. -/
  rb : (R ^^^ BitVec.ofNat 64 1).toNat < 2 ^ 63

section
variable {s : State} {R : BitVec 64} {EM : List Byte} {t t' : State}

/-- A step that writes only where it may keeps `Post`. -/
theorem Post.step (h : DPre pc s) (hc : Post s R EM t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) {ws : List Region}
    (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe s r) : Post s R EM t' := by
  refine ⟨⟨hsp.trans hc.sp, hrd.trans hc.rd, hwr.trans hc.wr, fun r hr => (hg r hr).trans (hc.hi r hr),
    hc.mem.trans (hf.sub fun r hr => safe_in h (hs r hr)), hc.sl.safe h hf hs⟩, ?_, ?_, hc.rb⟩
  · rw [hf.readW (Region.contains_self _ _) (fun X hX => safe_frame h (hs X hX) (.inl (by decide)) (by decide))
      (by decide)]
    exact hc.r
  · rw [← hc.em]
    exact bytes_of_frame (s := t) hf (fun X hX => by have := safe_out h (hs X hX); rwa [← outR_eq h] at this)
      (by have := h.wo; rw [h.h4] at this; omega_using [])

/-- Code that changes only registers but the callee-saved ones keeps `Post`. -/
theorem Post.regs (hc : Post s R EM t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hm : t'.mem = t.mem) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) : Post s R EM t' :=
  ⟨⟨hsp.trans hc.sp, hrd.trans hc.rd, hwr.trans hc.wr, fun r hr => (hg r hr).trans (hc.hi r hr),
    hm ▸ hc.mem, hm ▸ hc.sl⟩, by rw [hm]; exact hc.r, by rw [hm]; exact hc.em, hc.rb⟩

end

/-- A range of `scratch` is writable. -/
theorem scCov {s u : State} (h : DPre pc s) (hwr : u.wr = fr s :: s.wr) {a n : Nat} (ha : a + n ≤ scrBytes) :
    Covers [⟨scA s a, n⟩] u.wr :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨sR s, by rw [hwr, h.hwr]; simp, a, rfl, by have := scr_le h; dsimp only; omega_using [ha, this]⟩

theorem scIn {s u : State} (h : DPre pc s) (hwr : u.wr = fr s :: s.wr) {a n : Nat} (ha : a + n ≤ scrBytes) :
    InRegions u.wr (scA s a) n :=
  scCov h hwr ha _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem scInR {s u : State} (h : DPre pc s) (hwr : u.wr = fr s :: s.wr) {a n : Nat} (ha : a + n ≤ scrBytes) :
    InRegions (u.rd ++ u.wr) (scA s a) n :=
  let ⟨r, hr, hc⟩ := scIn h hwr ha
  ⟨r, List.mem_append_right _ hr, hc⟩

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
