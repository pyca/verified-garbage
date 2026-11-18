module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Encode
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.RndCallee
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.EncVerified
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Impl.RsaPkcs1Enc.PPC64LE.Random
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Random
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-! ### `RsaPkcs1Enc.PPC64LE.RndScan`, which only this module used -/

section

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on PPC64LE: the frame and the scan

The precondition by name (`RPre`), with the stack `rndStack` (the frame and
the stack of `vg_rsa_pkcs1_encrypt_precomputed`, `kR`); the frame at
`fb s = sp - frameBytes`, whose push makes its local variable space `fr`
writable; the saves of `r28`–`r31` and of the return address (`save_ok`),
what keeps them (`Saves`), and the restores (`restore_ok`), as
`Proof/RsaPkcs1Sig/PPC64LE/Frame.lean` for this frame. The contract's
postcondition by name (`post`).

From the frame's push, the saves and the scan's registers (`setup_ok`);
after `i` octets of the tape `randB s`, the scan has kept their nonzero
octets, `kept s i`, at the start of `PS` in the frame (`At`); it goes on
while it has kept fewer than `psLen s` and has octets left (`step_ok`), and
ends with `PS` full, the padding string of `nonzeroPrefix`, or with the tape
read (`scan_ok`); then whether `PS` is full (`full_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Rnd

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Random VG.Proof.RsaPkcs1Sig.PPC64LE
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame)
open VG.Proof.RsaPkcs1Enc (nz nz_zero nz_ne)

/-- The stack: the frame and the callee's. -/
def rndStack : Nat := frameBytes + Impl.RsaPkcs1Sig.PPC64LE.frameBytes

theorem rndStack_eq : rndStack = 3440 := rfl

theorem stackArgs_seven (s : State) :
    List.map (stackArg s) (List.range 7) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6] := rfl

/-! ## The regions -/

abbrev outR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩

abbrev tapeR (s : State) : Region := ⟨s.gpr .r5, 16⟩

abbrev nR (s : State) : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩

abbrev eR (s : State) : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩

abbrev msgR (s : State) : Region := ⟨s.gpr .r10, (stackArg s 0).toNat⟩

abbrev randR (s : State) : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩

abbrev scrR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩

abbrev preR (s : State) : Region := ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩

abbrev argsR (s : State) : Region := ⟨stackArgAddr s 0, 56⟩

/-- The stack the function and its callee use. -/
abbrev kR (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 rndStack, rndStack⟩

/-- The contract's precondition, by name. -/
structure RPre (s : State) : Prop where
  sp1 : rndStack ≤ s.sp.toNat
  sp2 : s.sp.toNat + 152 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, msgR s, randR s, preR s, argsR s]
  hwr : s.wr = [outR s, tapeR s, scrR s]
  dOt : (outR s).Disjoint (tapeR s)
  dOn : (outR s).Disjoint (nR s)
  dOe : (outR s).Disjoint (eR s)
  dOm : (outR s).Disjoint (msgR s)
  dOr : (outR s).Disjoint (randR s)
  dOs : (outR s).Disjoint (scrR s)
  dOq : (outR s).Disjoint (preR s)
  dOa : (outR s).Disjoint (argsR s)
  dTn : (tapeR s).Disjoint (nR s)
  dTe : (tapeR s).Disjoint (eR s)
  dTm : (tapeR s).Disjoint (msgR s)
  dTr : (tapeR s).Disjoint (randR s)
  dTs : (tapeR s).Disjoint (scrR s)
  dTq : (tapeR s).Disjoint (preR s)
  dTa : (tapeR s).Disjoint (argsR s)
  dNs : (nR s).Disjoint (scrR s)
  dEs : (eR s).Disjoint (scrR s)
  dMs : (msgR s).Disjoint (scrR s)
  dRs : (randR s).Disjoint (scrR s)
  dSq : (scrR s).Disjoint (preR s)
  dSa : (scrR s).Disjoint (argsR s)
  dKo : (kR s).Disjoint (outR s)
  dKt : (kR s).Disjoint (tapeR s)
  dKn : (kR s).Disjoint (nR s)
  dKe : (kR s).Disjoint (eR s)
  dKm : (kR s).Disjoint (msgR s)
  dKr : (kR s).Disjoint (randR s)
  dKs : (kR s).Disjoint (scrR s)
  dKq : (kR s).Disjoint (preR s)
  dKa : (kR s).Disjoint (argsR s)
  wO : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  wT : (s.gpr .r5).toNat + 16 ≤ 2 ^ 64
  wN : (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64
  wE : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wM : (s.gpr .r10).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  wR : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  wS : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  wQ : (stackArg s 5).toNat + (stackArg s 6).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .r7).toNat
  k2 : (s.gpr .r7).toNat ≤ 1024
  hok : (s.gpr .r4).toNat = (s.gpr .r7).toNat
  L1 : 1 ≤ (s.gpr .r9).toNat
  L2 : (s.gpr .r9).toNat ≤ (s.gpr .r7).toNat
  hml : (stackArg s 0).toNat + 11 ≤ (s.gpr .r7).toNat
  hrl : (stackArg s 2).toNat ≤ Spec.RsaPkcs1Enc.padEntropy ((s.gpr .r7).toNat - (stackArg s 0).toNat - 3)
  hsl : Spec.Rsa.publicScratchWords (s.gpr .r7).toNat ≤ (stackArg s 4).toNat
  hql : (stackArg s 6).toNat = Spec.Rsa.precomputedWords (s.gpr .r7).toNat

theorem pre_of {s : State} (h : (Spec.RsaPkcs1Enc.encryptRandomContract abi rndStack).pre s) : RPre s := by
  rw [rndStack_eq] at h
  sig_pre [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, abi, argRegs,
    stackArgs_seven, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp1, sp2, hrd, hwr, dOt, dOn, dOe, dOm, dOr, dOs, dOq, dOa, dTn, dTe, dTm, dTr, dTs, dTq, dTa,
    dNs, dEs, dMs, dRs, dSq, dSa, dKo, dKt, dKn, dKe, dKm, dKr, dKs, dKq, dKa,
    wO, wT, wN, wE, wM, wR, wS, wQ, ⟨k1, k2⟩, hok, L1, L2, hml, hrl, hsl, hql⟩ := h
  exact ⟨sp1, by omega_using [sp2], hrd, hwr, dOt, dOn, dOe, dOm, dOr, dOs, dOq, dOa, dTn, dTe, dTm, dTr, dTs, dTq, dTa,
    dNs, dEs, dMs, dRs, dSq, dSa, dKo, dKt, dKn, dKe, dKm, dKr, dKs, dKq, dKa,
    wO, wT, wN, wE, wM, wR, wS, wQ, k1, k2, hok, L1, L2, hml, hrl, hsl, hql⟩

/-! ## The values -/

def kOf (s : State) : Nat := (s.gpr .r7).toNat

def psLen (s : State) : Nat := kOf s - (stackArg s 0).toNat - 3

def nB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r6) (kOf s)

def eB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat

def msgB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat

def randB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat

def preW (s : State) : List (BitVec 64) := Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat

theorem RPre.ps {s : State} (hp : RPre s) : 8 ≤ psLen s ∧ psLen s + (stackArg s 0).toNat + 3 = kOf s ∧
    psLen s ≤ 1021 := by
  have := hp.hml; have := hp.k2; unfold psLen kOf; omega_arith

theorem RPre.randLen {s : State} (hp : RPre s) : (stackArg s 2).toNat ≤ psLen s + 128 := hp.hrl

/-! ## The frame -/

/-- The frame's base: the stack pointer in the frame. -/
abbrev fb (s : State) : Addr := s.sp - BitVec.ofNat 64 frameBytes

/-- The frame's local variable space, which its push makes writable. -/
abbrev fr (s : State) : Region := ⟨fb s + BitVec.ofNat 64 32, frameBytes - 32⟩

/-- The base of the stack the function uses. -/
abbrev kb (s : State) : Addr := s.sp - BitVec.ofNat 64 rndStack

theorem fb_eq (s : State) : fb s = kb s + BitVec.ofNat 64 Impl.RsaPkcs1Sig.PPC64LE.frameBytes := by
  simp only [fb, kb, rndStack]
  rw [BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem kb_toNat {s : State} (hp : RPre s) : (kb s).toNat + rndStack = s.sp.toNat ∧
    s.sp.toNat + 152 ≤ 2 ^ 64 := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold rndStack at *; omega_arith

theorem fb_toNat {s : State} (hp : RPre s) : (fb s).toNat + frameBytes = s.sp.toNat ∧
    Impl.RsaPkcs1Sig.PPC64LE.frameBytes ≤ (fb s).toNat := by
  have := hp.sp1
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold rndStack frameBytes at *; omega_using [this]

/-- The frame. -/
abbrev fR (s : State) : Region := ⟨fb s, frameBytes⟩

theorem frame_sub0 (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    Region.Sub ⟨fb s + BitVec.ofNat 64 d, n⟩ (fR s) := Offset.sub_base _ h

/-- The frame is in the stack the function uses. -/
theorem fR_sub (s : State) : (fR s).Sub (kR s) := by
  show Region.Sub ⟨fb s, frameBytes⟩ ⟨kb s, rndStack⟩
  rw [fb_eq]
  exact Offset.sub_base _ (by decide)

/-- A region of the frame is in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    Region.Sub ⟨fb s + BitVec.ofNat 64 d, n⟩ (kR s) := fun x hx => fR_sub s x (frame_sub0 s h x hx)

theorem frame_contains (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    (kR s).Contains (fb s + BitVec.ofNat 64 d) n := by
  show Region.Contains ⟨kb s, rndStack⟩ _ _
  rw [fb_eq, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact Offset.contains_base _ (by unfold rndStack Impl.RsaPkcs1Sig.PPC64LE.frameBytes frameBytes at *; omega_using [h])
    (by unfold Impl.RsaPkcs1Sig.PPC64LE.frameBytes frameBytes at *; omega_using [h])

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
  have e : BitVec.ofNat 64 (arg j) = BitVec.ofNat 64 frameBytes + BitVec.ofNat 64 (32 + 8 * (8 + j)) := by
    rw [BitVec.ofNat_add_ofNat]; unfold arg; congr 1; omega_using []
  rw [stackArgAddr, e, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem stackArgAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, Nat.add_zero]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, show 32 + 8 * 8 + 8 * j = 32 + 8 * (8 + j) by omega_using []]

theorem in_argsR {s : State} {j : Nat} (hj : j < 7) : (argsR s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

/-- A stack argument is readable. -/
theorem arg_in {s : State} (hp : RPre s) (wr : List Region) {j : Nat} (hj : j < 7) :
    InRegions (s.rd ++ wr) (stackArgAddr s j) 8 := by
  rw [hp.hrd]; exact ⟨argsR s, by simp, in_argsR hj⟩

/-! ## The saves -/

/-- The callee-saved registers other than `r28`–`r31`. -/
def hiRegs : List Reg := [.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26,
  .r27]

theorem freed_lr (n : Nat) (s : State) : (freed n s).lr = s.lr := rfl

/-- The slots of our caller's `r28`–`r31`. -/
def saved : List (Reg × Nat) := [(.r28, oSave), (.r29, oSave + 8), (.r30, oSave + 16), (.r31, oSave + 24)]

theorem save_eq : save = ([.addSp .r12 0] : List Instr) ++ Spill.saveCode .r12 saved ++
    ([.mflr .r0, .store .d .r0 .r12 oLr] : List Instr) :=
  rfl

theorem restore_eq :
    restore = ([.addSp .r12 0, .load .d .r0 .r12 oLr, .mtlr .r0] : List Instr) ++ Spill.restoreCode .r12 saved :=
  rfl

theorem saved_offs : ∀ p ∈ saved, oSave ≤ p.2 ∧ p.2 + 8 ≤ oSave + 32 := by decide

theorem saved_ho : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide

theorem preserved_split {r : Reg} (h : r ∈ preserved) : r ∈ saved.map Prod.fst ∨ r ∈ hiRegs := by
  revert r; decide

/-- What the restores need, from the entry state `s`: the frame, our
caller's registers and return address in their slots, and the other
callee-saved registers as on entry. -/
structure Saves (s t : State) : Prop where
  sp : t.sp = fb s
  wr : t.wr = fr s :: s.wr
  hi : ∀ r ∈ hiRegs, t.gpr r = s.gpr r
  sv : Spill.Saved (fb s) s.gpr saved t.mem
  ls : t.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr

/-- The saves, from the state after the frame's push (`u`): `r12` holds
the frame's base, `r28`–`r31` and the return address are in their slots, and
memory is changed only in the frame. -/
theorem save_ok {s u : State} (hsp : u.sp = fb s) (hwr : u.wr = fr s :: s.wr)
    (hm : Frame [kR s] s.mem u.mem) (hg : ∀ r ∈ preserved, u.gpr r = s.gpr r) (hlr : u.lr = s.lr)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ v, Keep [.r12, .r0] u v → v.gpr .r12 = fb s → Frame [kR s] s.mem v.mem →
      Saves s v → WP isa (.block rest) v Q) :
    WP isa (.block (save ++ rest)) u Q := by
  rw [save_eq]
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_addSp fun u₁ o₁ e₁ => ?_
  rw [hsp, BitVec.add_zero] at e₁
  refine Spill.save_ok (b := .r12) (l := saved) (by decide) saved_ho (fun p hp => ?_) ?_
  · have := saved_offs p hp
    rw [e₁, o₁.wr, hwr]; exact in_fr s _ (by unfold oSave at this; omega_using [this]) (by unfold oSave frameBytes at *; omega_using [this])
  generalize hu₂ : ({ u₁ with mem := Spill.saveMem u₁.mem (u₁.gpr .r12) u₁.gpr saved } : State) = u₂
  have g₂ : u₂.gpr = u₁.gpr := by rw [← hu₂]
  have m₂ : u₂.mem = Spill.saveMem u.mem (fb s) u₁.gpr saved := by rw [← hu₂, e₁, o₁.mem]
  have k₂ : Keep [.r12] u u₂ := by
    rw [← hu₂]; exact ⟨fun r hr => o₁.gpr r hr, o₁.rd, o₁.wr, o₁.sp, o₁.lr⟩
  refine wp_mflr fun u₃ o₃ e₃ => wp_std (a := fb s + BitVec.ofNat 64 oLr)
    (by rw [o₃.get .r12, g₂, e₁]) (by rw [o₃.wr, k₂.wr, hwr]; exact in_fr s _ (by decide) (by decide))
    fun u₄ m₄ => ?_
  have fr₂ : Frame [kR s] s.mem u₂.mem := by
    rw [m₂]
    refine hm.trans (Frame.sub (Spill.saveMem_frame_base (n := frameBytes) (fun p hp => by
      have := saved_offs p hp; unfold oSave frameBytes at *; omega_using [this]) (by decide) _ _ _) fun r hr => ?_)
    rw [List.mem_singleton.mp hr]
    exact ⟨kR s, List.mem_singleton_self _, fR_sub s⟩
  have sv₂ : Spill.Saved (fb s) s.gpr saved u₂.mem := by
    rw [m₂]
    refine fun p hp => (Spill.saveMem_saved (by decide) _ _ _ p hp).trans ?_
    have h12 : p.1 ∉ [Reg.r12] := by revert p; decide
    rw [o₁.gpr _ h12, hg _ (by revert p; decide)]
  have hd : ∀ p ∈ saved, ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 oLr, 8⟩ : Region)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 p.2, 8⟩ r := fun p hp r hr => by
    have := saved_offs p hp
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by unfold oSave oLr at *; omega_using [this])) (by unfold oSave at *; omega_using [this]) (by decide)
  have fw : Frame [⟨fb s + BitVec.ofNat 64 oLr, 8⟩] u₃.mem u₄.mem := by
    rw [m₄.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have kk : Keep [.r12, .r0] u u₄ := ⟨fun r hr => by
      have h0 : r ∉ [Reg.r0] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; exact fun h => hr (.inr h)
      have h12 : r ∉ [Reg.r12] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; exact fun h => hr (.inl h)
      rw [m₄.gpr, o₃.gpr r h0, k₂.gpr r h12],
    by rw [m₄.rd, o₃.rd, k₂.rd], by rw [m₄.wr, o₃.wr, k₂.wr], by rw [m₄.sp, o₃.sp, k₂.sp],
    by rw [m₄.lr, o₃.lr, k₂.lr]⟩
  refine k u₄ kk (by rw [m₄.gpr, o₃.get .r12, g₂, e₁]) ?_ ⟨kk.sp.trans hsp, kk.wr.trans hwr, fun r hr => ?_, ?_, ?_⟩
  · rw [m₄.mem, o₃.mem]
    exact fr₂.writeW (List.mem_singleton_self _) _ (frame_contains s (d := oLr) (by decide))
  · have hr' : r ∉ [Reg.r12, .r0] := by revert r; decide
    rw [kk.gpr r hr', hg r (by revert r; decide)]
  · have : Spill.Saved (fb s) s.gpr saved u₃.mem := by rw [o₃.mem]; exact sv₂
    exact this.frame fw hd
  · rw [m₄.mem, Mem.readW_writeW_self64, e₃, k₂.lr, hlr]

/-- The restores: the caller's registers and return address are back, and
`r3` and memory are kept. -/
theorem restore_ok {s w : State} (hm : Saves s w) :
    WP isa (.block restore) w fun w' =>
      abiPreserved s (freed frameBytes w') ∧ w'.gpr .r3 = w.gpr .r3 ∧ w'.mem = w.mem := by
  rw [restore_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp fun w₁ o₁ e₁ => ?_
  rw [hm.sp, BitVec.add_zero] at e₁
  have hin : ∀ {e : Nat}, oSave ≤ e → e + 8 ≤ oLr + 8 →
      InRegions (w₁.rd ++ w₁.wr) (fb s + BitVec.ofNat 64 e) 8 := fun h₁ h₂ => by
    rw [o₁.wr, hm.wr]; exact in_fr' s _ _ (by unfold oSave at h₁; omega_using [h₁]) (by unfold oLr frameBytes at *; omega_using [h₂])
  refine wp_ld (a := fb s + BitVec.ofNat 64 oLr) (by rw [e₁]) (hin (by decide) (by decide)) fun w₂ o₂ e₂ =>
    wp_mtlr fun w₃ g₃ m₃ rd₃ wr₃ sp₃ lr₃ => ?_
  refine WP.mono (Spill.restore_wp (b := .r12) (l := saved) (B := fb s) (g := s.gpr) (by decide)
    (by rw [g₃, o₂.get .r12, e₁]) saved_ho (by decide)
    (fun p hp => by
      have := saved_offs p hp
      rw [rd₃, wr₃, o₂.rd, o₂.wr]; exact hin this.1 (by unfold oSave oLr at *; omega_using [this]))
    (by rw [m₃, o₂.mem, o₁.mem]; exact hm.sv)) fun w' hr => ⟨⟨fun r hr' => ?_, ?_, ?_⟩, ?_, ?_⟩
  · show w'.gpr r = s.gpr r
    rcases preserved_split hr' with h | h
    · exact hr.gpr_of (.inl h)
    · have h0 : r ∉ saved.map Prod.fst := by revert r; decide
      have h1 : r ∉ [Reg.r0] := by revert r; decide
      have h2 : r ∉ [Reg.r12] := by revert r; decide
      rw [hr.other r h0, g₃, o₂.gpr r h1, o₁.gpr r h2]; exact hm.hi r h
  · show w'.sp + BitVec.ofNat 64 frameBytes = s.sp
    rw [hr.sp, sp₃, o₂.sp, o₁.sp, hm.sp, BitVec.sub_add_cancel]
  · have h₁ := hr.lr
    have h₂ : w₁.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr := by rw [o₁.mem]; exact hm.ls
    rw [freed_lr]; exact h₁.trans (lr₃.trans (e₂.trans h₂))
  · show w'.gpr .r3 = w.gpr .r3
    rw [hr.other .r3 (by decide), g₃, o₂.get .r3, o₁.get .r3]
  · rw [hr.mem, m₃, o₂.mem, o₁.mem]

/-- `PS` in the frame. -/
abbrev pb (s : State) : Addr := fb s + BitVec.ofNat 64 oBuf

/-- The tape's length. -/
abbrev rl (s : State) : Nat := (stackArg s 2).toNat

/-- The octets kept after `i` octets of the tape. -/
abbrev kept (s : State) (i : Nat) : List Byte := nz ((randB s).take i)

/-- The slots of the saves. -/
abbrev slR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oSave, 40⟩

/-! ## Memory -/

/-- Memory in the frame: changed only in the stack, with the saves in their
slots. -/
structure Mm (s : State) (m : Mem) : Prop where
  fr : Frame [kR s] s.mem m
  sv : Spill.Saved (fb s) s.gpr saved m
  ls : m.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr

theorem slot_sub (s : State) {p : Reg × Nat} (hp : p ∈ saved) :
    Region.Sub ⟨fb s + BitVec.ofNat 64 p.2, 8⟩ (slR s) :=
  Offset.sub (fb s) (saved_offs p hp).1 (by have := saved_offs p hp; omega_using [this])

theorem lr_sub (s : State) : Region.Sub ⟨fb s + BitVec.ofNat 64 oLr, 8⟩ (slR s) :=
  Offset.sub (fb s) (by decide) (by decide)

theorem Mm.frame {s : State} {m m' : Mem} (h : Mm s m) {R : List Region} (hf : Frame R m m')
    (hk : ∀ r ∈ R, Region.Sub r (kR s)) (hd : ∀ r ∈ R, (slR s).Disjoint r) : Mm s m' :=
  ⟨h.fr.trans (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, hk r hr⟩),
    h.sv.frame hf fun p hp r hr => (hd r hr).sub_left (slot_sub s hp),
    by rw [hf.readW (Region.contains_self _ _) (fun r hr => (hd r hr).sub_left (lr_sub s)) (by decide)]; exact h.ls⟩

theorem buf_sub (s : State) {n : Nat} (h : n ≤ 1024) : Region.Sub ⟨pb s, n⟩ (kR s) :=
  frame_sub s (d := oBuf) (by unfold oBuf frameBytes; omega_using [h])

theorem slR_buf (s : State) {n : Nat} (h : n ≤ 1024) : (slR s).Disjoint ⟨pb s, n⟩ :=
  Offset.disjoint _ (.inl (by decide)) (by decide) (by unfold oBuf; omega_using [h])

theorem Mm.buf {s : State} {m : Mem} (h : Mm s m) (xs : List Byte) (hx : xs.length ≤ 1024) :
    Mm s (writeBytes m (pb s) xs) :=
  h.frame (writeBytes_frame m (pb s) xs (Region.contains_self _ _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact buf_sub s hx)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact slR_buf s hx)

/-- A region apart from the stack keeps its bytes. -/
theorem Mm.bytes {s : State} {m : Mem} (h : Mm s m) {R : Region} (hd : R.Disjoint (kR s)) (hR : R.len ≤ 2 ^ 64)
    {i : Nat} (hi : i < R.len) : m (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) :=
  h.fr.bytes (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hR hi

/-- The registers and permissions in the frame that the whole body keeps. -/
structure Fx (s u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = fr s :: s.wr
  hi : ∀ r ∈ hiRegs, u.gpr r = s.gpr r
  r6 : u.gpr .r6 = s.gpr .r6
  r8 : u.gpr .r8 = s.gpr .r8
  r9 : u.gpr .r9 = s.gpr .r9
  r10 : u.gpr .r10 = s.gpr .r10
  r28 : u.gpr .r28 = BitVec.ofNat 64 (psLen s)
  r29 : u.gpr .r29 = s.gpr .r7
  r30 : u.gpr .r30 = s.gpr .r5
  r31 : u.gpr .r31 = s.gpr .r3

/-- The registers `Fx` fixes. -/
def fxRegs : List Reg := [.r6, .r8, .r9, .r10, .r28, .r29, .r30, .r31] ++ hiRegs

theorem Fx.keep {s u v : State} (h : Fx s u) {rs : List Reg} (k : Keep rs u v)
    (hrs : ∀ r ∈ rs, r ∉ fxRegs := by decide) : Fx s v :=
  have g : ∀ r ∈ fxRegs, v.gpr r = u.gpr r := fun r hr => k.gpr r fun h => hrs r h hr
  ⟨k.sp.trans h.sp, k.rd.trans h.rd, k.wr.trans h.wr,
    fun r hr => (g r (List.mem_append_right _ hr)).trans (h.hi r hr),
    (g _ (by decide)).trans h.r6, (g _ (by decide)).trans h.r8, (g _ (by decide)).trans h.r9,
    (g _ (by decide)).trans h.r10, (g _ (by decide)).trans h.r28, (g _ (by decide)).trans h.r29,
    (g _ (by decide)).trans h.r30, (g _ (by decide)).trans h.r31⟩

/-! ## Values -/

theorem psLen_bv {s : State} (hp : RPre s) :
    s.gpr .r7 - stackArg s 0 - BitVec.ofNat 64 3 = BitVec.ofNat 64 (psLen s) := by
  have := hp.hml
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, psLen, kOf]
  have h1 := (s.gpr .r7).isLt
  have h2 := (stackArg s 0).isLt
  omega_using [this]

theorem ofNat_succ (i : Nat) : BitVec.ofNat 64 i + BitVec.ofNat 64 1 = BitVec.ofNat 64 (i + 1) :=
  (BitVec.ofNat_add i 1).symm

theorem rl_lt (s : State) : rl s < 2 ^ 64 := (stackArg s 2).isLt

theorem RPre.rl {s : State} (hp : RPre s) : rl s ≤ psLen s + 128 := hp.randLen

theorem rl_bv (s : State) : stackArg s 2 = BitVec.ofNat 64 (rl s) := by simp [rl]

theorem sub_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b != 0) = !decide (a = b) := by
  by_cases h : a = b
  · subst h; rw [BitVec.sub_self]; simp
  · rw [ne_zero_iff, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb]
    simp only [h, decide_false, Bool.not_false, decide_eq_true_eq]; omega_using [ha, hb, h]

theorem byte_ne : ∀ b : Byte, (b.setWidth 64 != 0) = !decide (b = 0) := by decide

theorem byte_trunc (b : Byte) : (b.setWidth 64).setWidth 8 = b := by
  ext i hi; simp

theorem randB_length (s : State) : (randB s).length = rl s := by
  simp [randB, Spec.Rsa.bytesAt]

theorem randB_getD {s : State} {i : Nat} (hi : i < rl s) :
    (randB s).getD i 0 = s.mem (stackArg s 1 + BitVec.ofNat 64 i) := by
  simp [randB, Spec.Rsa.bytesAt, hi]

theorem take_succ_eq {s : State} {i : Nat} (hi : i < rl s) :
    (randB s).take (i + 1) = (randB s).take i ++ [(randB s).getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [randB_length]; exact hi)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [randB_length]; exact hi)]

theorem kept_succ {s : State} {i : Nat} (hi : i < rl s) :
    kept s (i + 1) = if (randB s).getD i 0 = 0 then kept s i else kept s i ++ [(randB s).getD i 0] := by
  simp only [kept, take_succ_eq hi]
  split
  · rename_i h; rw [h, nz_zero]
  · rename_i h; exact nz_ne h _

theorem kept_zero (s : State) : kept s 0 = [] := by simp [kept, VG.Proof.RsaPkcs1Enc.nz_nil]

theorem kept_all (s : State) : kept s (rl s) = nz (randB s) := by
  simp only [kept]; rw [← randB_length, List.take_length]

/-- `PS` filled at octet `i`: the padding string of `nonzeroPrefix`. -/
theorem prefix_of_fill {s : State} {i : Nat} (hi : i < rl s)
    (hc : (kept s i).length < psLen s) (hf : (kept s (i + 1)).length = psLen s) :
    Spec.RsaPkcs1Enc.nonzeroPrefix (psLen s) (randB s) = some (kept s (i + 1), i + 1) := by
  have hz : (randB s).getD i 0 ≠ 0 := by
    intro hz; rw [kept_succ hi, ite_eq_left hz] at hf; omega_using [hc, hf]
  have hk : kept s (i + 1) = kept s i ++ [(randB s).getD i 0] := by rw [kept_succ hi, ite_eq_right hz]
  have hl : i < (randB s).length := by rw [randB_length]; exact hi
  have e : randB s = (randB s).take i ++ (randB s).getD i 0 :: (randB s).drop (i + 1) := by
    conv => lhs; rw [← List.take_append_drop i (randB s)]
    congr 1
    rw [List.drop_eq_getElem_cons hl]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  have hlen : ((randB s).take i).length = i := by rw [List.length_take]; omega_using [hl]
  rw [e, VG.Proof.RsaPkcs1Enc.nonzeroPrefix_last _ hz (by rw [hk] at hf; simpa using hf), hk, hlen]

/-! ## The setup -/

/-- After `i` octets of the tape, from the memory `M` before the scan. -/
structure At (s : State) (M : Mem) (i : Nat) (u : State) : Prop extends Fx s u where
  mem : u.mem = writeBytes M (pb s) (kept s i)
  r3 : u.gpr .r3 = stackArg s 1
  r4 : u.gpr .r4 = BitVec.ofNat 64 i
  r5 : u.gpr .r5 = BitVec.ofNat 64 (kept s i).length
  r7 : u.gpr .r7 = pb s
  r11 : u.gpr .r11 = stackArg s 2
  hi' : i ≤ rl s
  hc : (kept s i).length ≤ psLen s

theorem fb_contains (s : State) : (kR s).Contains (fb s) 8 := by
  have := frame_contains s (d := 0) (n := 8) (by decide)
  rwa [BitVec.add_zero] at this

/-- An argument on the stack, from memory in the frame. -/
theorem arg_read {s : State} (hp : RPre s) {m : Mem} (hm : Frame [kR s] s.mem m) {j : Nat} (hj : j < 7) :
    m.readW (fb s + BitVec.ofNat 64 (arg j)) 64 = stackArg s j := by
  rw [← stackArgAddr_fb]
  exact hm.readW (in_argsR hj) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.dKa.symm) (by decide)

theorem arg_in' {s t : State} (hp : RPre s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 7) :
    InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 (arg j)) 8 := by
  rw [← stackArgAddr_fb, hrd]; exact arg_in hp _ hj

theorem setup_ok {s : State} (hp : RPre s) :
    WP isa (.block setup) (allocated frameBytes s) fun t => Mm s t.mem ∧ At s t.mem 0 t := by
  have hP := hp.ps
  have e : setup = save ++ [Impl.AesGcm.PPC64LE.mov .r31 .r3, Impl.AesGcm.PPC64LE.mov .r30 .r5,
      Impl.AesGcm.PPC64LE.mov .r29 .r7, .load .d .r0 .r12 (arg 0), .sub .r28 .r7 .r0,
      .subi .r28 .r28 3, .load .d .r3 .r12 (arg 1), .load .d .r11 .r12 (arg 2), .addi .r7 .r12 oBuf,
      .li .r4 0, .li .r5 0] := rfl
  rw [e]
  have fm : Frame [kR s] s.mem (allocated frameBytes s).mem :=
    Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ (fb_contains s)
  refine save_ok rfl rfl fm (fun _ _ => rfl) rfl fun v kv h12 hm sv => ?_
  have hrd : v.rd = s.rd := kv.rd
  have g : ∀ r, r ∉ [Reg.r12, .r0] → v.gpr r = s.gpr r := fun r hr => kv.gpr r hr
  have a0 := arg_read hp hm (j := 0) (by decide)
  have a1 := arg_read hp hm (j := 1) (by decide)
  have a2 := arg_read hp hm (j := 2) (by decide)
  have i0 := arg_in' hp hrd (j := 0) (by decide)
  have i1 := arg_in' hp hrd (j := 1) (by decide)
  have i2 := arg_in' hp hrd (j := 2) (by decide)
  have c0 : arg 0 < 2 ^ 15 := by decide
  have c1 : arg 1 < 2 ^ 15 := by decide
  have c2 : arg 2 < 2 ^ 15 := by decide
  have d0 : arg 0 % 4 = 0 := by decide
  have d1 : arg 1 % 4 = 0 := by decide
  have d2 : arg 2 % 4 = 0 := by decide
  have cb : oBuf < 2 ^ 15 := by decide
  have hps := psLen_bv hp
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r31, .r30, .r29, .r0, .r28, .r3, .r11, .r7, .r4, .r5]
    (Q := fun w => w.gpr .r31 = s.gpr .r3 ∧ w.gpr .r30 = s.gpr .r5 ∧ w.gpr .r29 = s.gpr .r7 ∧
      w.gpr .r28 = BitVec.ofNat 64 (psLen s) ∧ w.gpr .r3 = stackArg s 1 ∧ w.gpr .r11 = stackArg s 2 ∧
      w.gpr .r7 = pb s ∧ w.gpr .r4 = BitVec.ofNat 64 0 ∧ w.gpr .r5 = BitVec.ofNat 64 0 ∧ w.mem = v.mem) ?_ rfl)
    fun w ⟨⟨w31, w30, w29, w28, w3, w11, w7, w4, w5, wm⟩, kw⟩ => ?_
  · prun [c0, c1, c2, d0, d1, d2, cb, i0, i1, i2, a0, a1, a2, h12, g .r3 (by decide), g .r5 (by decide),
      g .r7 (by decide), BitVec.or_self, exec_addi (show Reg.r12 ≠ .r0 by decide) cb, Impl.AesGcm.PPC64LE.mov,
      exec_subi (show Reg.r28 ≠ .r0 by decide) (show 3 ≤ 32768 by decide), hps]
  · have hmw : Mm s w.mem := ⟨wm ▸ hm, wm ▸ sv.sv, wm ▸ sv.ls⟩
    have g' : ∀ r, r ∉ [Reg.r31, .r30, .r29, .r0, .r28, .r3, .r11, .r7, .r4, .r5] → w.gpr r = v.gpr r :=
      fun r hr => kw.gpr r hr
    have gg : ∀ r ∈ [Reg.r6, .r8, .r9, .r10], w.gpr r = s.gpr r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact (g' _ (by decide)).trans (g _ (by decide))
    refine ⟨hmw, ⟨⟨kw.sp.trans sv.sp, kw.rd.trans hrd, kw.wr.trans sv.wr,
      fun r hr => (g' r (by revert r; decide)).trans (sv.hi r hr),
      gg _ (by decide), gg _ (by decide), gg _ (by decide), gg _ (by decide), w28, w29, w30, w31⟩,
      by rw [kept_zero, writeBytes_nil], w3, w4, by rw [w5, kept_zero]; rfl, w7, w11, Nat.zero_le _,
      by rw [kept_zero]; simp⟩⟩

/-! ## The scan -/

theorem At.only {s : State} {M : Mem} {i : Nat} {u v : State} (h : At s M i u) {rs : List Reg} (o : Only rs u v)
    (hrs : ∀ r ∈ rs, r ∉ fxRegs ++ ([.r3, .r4, .r5, .r7, .r11] : List Reg) := by decide) : At s M i v :=
  have g : ∀ r ∈ fxRegs ++ ([.r3, .r4, .r5, .r7, .r11] : List Reg), v.gpr r = u.gpr r := fun r hr => o.gpr r fun h => hrs r h hr
  ⟨h.toFx.keep o.keep (fun r hr h' => hrs r hr (List.mem_append_left _ h')), o.mem.trans h.mem,
    (g _ (by decide)).trans h.r3, (g _ (by decide)).trans h.r4, (g _ (by decide)).trans h.r5,
    (g _ (by decide)).trans h.r7, (g _ (by decide)).trans h.r11, h.hi', h.hc⟩

theorem kept_le {s : State} (hp : RPre s) {M : Mem} {i : Nat} {u : State} (h : At s M i u) :
    (kept s i).length ≤ 1021 := by have := hp.ps; have := h.hc; omega_arith

/-- A byte of the tape, read from memory in the scan. -/
theorem tape_byte {s : State} (hp : RPre s) {M : Mem} (hM : Mm s M) {i : Nat} (hi : i < rl s) (xs : List Byte)
    (hx : xs.length ≤ 1024) :
    writeBytes M (pb s) xs (stackArg s 1 + BitVec.ofNat 64 i) = (randB s).getD i 0 := by
  have hwR : (stackArg s 1).toNat + rl s ≤ 2 ^ 64 := hp.wR
  rw [randB_getD hi]
  exact ((writeBytes_frame M (pb s) xs (Region.contains_self _ _)).bytes (R := randR s)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.dKr.symm.sub_right (buf_sub s hx))
    (by show rl s ≤ 2 ^ 64; omega_using [hwR]) hi).trans (hM.bytes hp.dKr.symm (by show rl s ≤ 2 ^ 64; omega_using [hwR]) hi)

/-- After the load of octet `i`. -/
def LoadPt (s : State) (M : Mem) (i : Nat) (v : State) : Prop :=
  ∃ u, At s M i u ∧ Only [.r12, .r0, .r4] u v ∧ v.gpr .r0 = ((randB s).getD i 0).setWidth 64 ∧
    v.gpr .r4 = BitVec.ofNat 64 (i + 1)

theorem load_ok {s : State} (hp : RPre s) {M : Mem} (hM : Mm s M) {i : Nat} {u : State} (hI : At s M i u)
    (hi : i < rl s) : WP isa (.block load) u (LoadPt s M i) := by
  have hrl := hp.rl
  have hP := hp.ps
  have hwR : (stackArg s 1).toNat + rl s ≤ 2 ^ 64 := hp.wR
  have hk := kept_le hp hI
  unfold load
  refine wp_add fun u₁ o₁ e₁ => wp_lbz (a := stackArg s 1 + BitVec.ofNat 64 i)
    (by rw [e₁, hI.r3, hI.r4, BitVec.add_zero]) ?_ fun u₂ o₂ e₂ => wp_addi fun u₃ o₃ e₃ => wp_nil ?_
  · rw [o₁.rd, o₁.wr, hI.rd, hp.hrd]
    exact ⟨randR s, by simp, Offset.contains_base _ (show i + 1 ≤ rl s by omega_using [hi]) (by omega_using [hi, hwR])⟩
  · refine ⟨u, hI, (o₁.trans (o₂.trans o₃)).mono, ?_, ?_⟩
    · rw [o₃.get .r0, e₂, o₁.mem, hI.mem, tape_byte hp hM hi _ (by omega_using [hk])]
    · rw [e₃, o₂.get .r4, o₁.get .r4, hI.r4, ofNat_succ]

theorem branch_ok {s : State} (hp : RPre s) {M : Mem} {i : Nat} {v : State} (hL : LoadPt s M i v)
    (hi : i < rl s) (hc : (kept s i).length < psLen s) :
    WP isa (.ite (.nonzero .d .r0) (.block keep) (.block [])) v (At s M (i + 1)) := by
  obtain ⟨u, hI, o, h0, h4⟩ := hL
  have hk := kept_le hp hI
  have hrl := hp.rl
  have hP := hp.ps
  have g : ∀ r, r ∉ [Reg.r12, .r0, .r4] → v.gpr r = u.gpr r := fun r hr => o.gpr r hr
  have ev : isa.eval (.nonzero .d .r0) v = some (!decide ((randB s).getD i 0 = 0)) := by
    rw [eval_nonzero, h0, byte_ne]
  by_cases hz : (randB s).getD i 0 = 0
  · have hks : kept s (i + 1) = kept s i := by rw [kept_succ hi, ite_eq_left hz]
    refine WP.ite false (by rw [ev, decide_eq_true hz]; rfl) (fun h => absurd h (by decide)) fun _ => wp_nil ?_
    exact ⟨hI.toFx.keep o.keep, by rw [o.mem, hI.mem, hks], (g _ (by decide)).trans hI.r3, h4,
      by rw [(g _ (by decide)).trans hI.r5, hks], (g _ (by decide)).trans hI.r7, (g _ (by decide)).trans hI.r11,
      by omega_using [hi], by rw [hks]; omega_using [hc]⟩
  · have hks : kept s (i + 1) = kept s i ++ [(randB s).getD i 0] := by rw [kept_succ hi, ite_eq_right hz]
    have hl : (kept s (i + 1)).length = (kept s i).length + 1 := by rw [hks]; simp
    refine WP.ite true (by rw [ev, decide_eq_false hz]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    have v7 : v.gpr .r7 = pb s := (g _ (by decide)).trans hI.r7
    have v5 : v.gpr .r5 = BitVec.ofNat 64 (kept s i).length := (g _ (by decide)).trans hI.r5
    unfold keep
    refine wp_add fun v₁ o₁ e₁ => wp_stb (a := pb s + BitVec.ofNat 64 (kept s i).length)
      (by rw [e₁, v7, v5, BitVec.add_zero]) ?_ fun v₂ m₂ => wp_addi fun v₃ o₃ e₃ => wp_nil ?_
    · rw [o₁.wr, o.wr, hI.wr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact in_fr s _ (by unfold oBuf; omega_using []) (by unfold oBuf frameBytes; omega_using [hk])
    · have k := (o₁.keep.trans (m₂.keep.trans o₃.keep)).mono (rs' := [.r12, .r5])
      have g' : ∀ r, r ∉ [Reg.r12, .r5] → v₃.gpr r = v.gpr r := fun r hr => k.gpr r hr
      refine ⟨(hI.toFx.keep o.keep).keep k, ?_, (g' _ (by decide)).trans ((g _ (by decide)).trans hI.r3),
        (g' _ (by decide)).trans h4, ?_, (g' _ (by decide)).trans v7,
        (g' _ (by decide)).trans ((g _ (by decide)).trans hI.r11), by omega_using [hi], by omega_using [hc, hl]⟩
      · rw [o₃.mem, m₂.mem, o₁.mem, o₁.get .r0, h0, byte_trunc, o.mem, hI.mem, hks,
          writeBytes_snoc _ _ _ _ (by omega_using [hk])]
      · rw [e₃, m₂.gpr, o₁.get .r5, v5, ofNat_succ, hl]

theorem more_ok {s : State} (hp : RPre s) {M : Mem} {i : Nat} {w : State} (hI : At s M (i + 1) w) :
    WP isa more w fun x => At s M (i + 1) x ∧
      (x.gpr .r12 != 0) = !decide ((kept s (i + 1)).length = psLen s ∨ i + 1 = rl s) := by
  have hk := kept_le hp hI
  have hrl := hp.rl
  have hP := hp.ps
  have hi := hI.hi'
  unfold more
  refine WP.seq (wp_sub fun w₁ o₁ e₁ => wp_nil ?_)
  have hw := hI.only o₁
  have ev : isa.eval (.nonzero .d .r12) w₁ = some (!decide (psLen s = (kept s (i + 1)).length)) := by
    rw [eval_nonzero, e₁, hI.r28, hI.r5, sub_ne (by omega_using [hP]) (by omega_using [hk])]
  by_cases hf : (kept s (i + 1)).length = psLen s
  · refine WP.ite false (by rw [ev, decide_eq_true hf.symm]; rfl) (fun h => absurd h (by decide))
      fun _ => wp_nil ⟨hw, ?_⟩
    rw [e₁, hI.r28, hI.r5, hf, sub_ne (by omega_using [hP]) (by omega_using [hP])]; simp
  · refine WP.ite true (by rw [ev, decide_eq_false (Ne.symm hf)]; rfl) (fun _ => wp_sub fun x o₂ e₂ =>
      wp_nil ⟨hw.only o₂, ?_⟩) (fun h => absurd h (by decide))
    rw [e₂, o₁.get .r11, o₁.get .r4, hI.r11, hI.r4, rl_bv, sub_ne (by omega_using [hrl, hP]) (by omega_using [hrl, hP, hi])]
    simp only [hf, false_or]; congr 1; exact decide_eq_decide.mpr eq_comm

theorem step_ok {s : State} (hp : RPre s) {M : Mem} (hM : Mm s M) {i : Nat} {u : State} (hI : At s M i u)
    (hi : i < rl s) (hc : (kept s i).length < psLen s) :
    WP isa step u fun x => At s M (i + 1) x ∧
      (x.gpr .r12 != 0) = !decide ((kept s (i + 1)).length = psLen s ∨ i + 1 = rl s) :=
  WP.seq (WP.mono (load_ok hp hM hI hi) fun _ hL =>
    WP.seq (WP.mono (branch_ok hp hL hi hc) fun _ hI' => more_ok hp hI'))

/-- What the scan leaves: after `i` octets, `PS` full with the padding
string, or the tape read with fewer nonzero octets. -/
def Done (s : State) (M : Mem) (u : State) : Prop :=
  ∃ i, At s M i u ∧ (((kept s i).length = psLen s ∧
      Spec.RsaPkcs1Enc.nonzeroPrefix (psLen s) (randB s) = some (kept s i, i)) ∨
    (i = rl s ∧ (kept s i).length < psLen s))

/-- The loop's invariant, with the octets left as its measure. -/
def LoopInv (s : State) (M : Mem) (n : Nat) (u : State) : Prop :=
  ∃ i, n = rl s - i ∧ At s M i u ∧ i < rl s ∧ (kept s i).length < psLen s

theorem scan_ok {s : State} (hp : RPre s) {M : Mem} (hM : Mm s M) {t : State} (h0 : At s M 0 t) :
    WP isa scan t (Done s M) := by
  have hP := hp.ps
  have ev : isa.eval (.nonzero .d .r11) t = some (stackArg s 2 != 0) := by rw [eval_nonzero, h0.r11]
  unfold scan
  by_cases hl : stackArg s 2 = 0
  · refine WP.ite false (by rw [ev, hl]; rfl) (fun h => absurd h (by decide)) fun _ => wp_nil ?_
    have hl' : rl s = 0 := by simp [rl, hl]
    exact ⟨0, h0, .inr ⟨hl'.symm, by rw [kept_zero]; simp; omega_using [hP]⟩⟩
  have hl' : 0 < rl s := by
    rcases Nat.eq_zero_or_pos (rl s) with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa [rl] using h)) hl
    · exact h
  refine WP.ite true (by rw [ev, show (stackArg s 2 != 0) = true from bne_iff_ne.mpr hl])
    (fun _ => ?_) (fun h => absurd h (by decide))
  refine WP.loop (M := isa) (LoopInv s M) ?_ (rl s - 0) t ⟨0, rfl, h0, hl', by rw [kept_zero]; simp; omega_using [hP]⟩
  rintro n u ⟨i, rfl, hI, hi, hc⟩
  refine WP.mono (step_ok hp hM hI hi hc) fun x ⟨hI', hz⟩ => ?_
  have ev' : isa.eval (.nonzero .d .r12) x = some (!decide ((kept s (i + 1)).length = psLen s ∨ i + 1 = rl s)) := by
    rw [eval_nonzero, hz]
  by_cases hstop : (kept s (i + 1)).length = psLen s ∨ i + 1 = rl s
  · refine .inl ⟨by rw [ev', decide_eq_true hstop]; rfl, ⟨i + 1, hI', ?_⟩⟩
    by_cases hf : (kept s (i + 1)).length = psLen s
    · exact .inl ⟨hf, prefix_of_fill hi hc hf⟩
    · exact .inr ⟨hstop.resolve_left hf, by have := hI'.hc; omega_using [hf, this]⟩
  · refine .inr ⟨by rw [ev', decide_eq_false hstop]; rfl, _, by omega_using [hi], i + 1, rfl, hI', by omega_using [hi, hstop],
      by have := hI'.hc; omega_using [hstop, this]⟩

/-! ## Shared by both ends -/

/-- What the rest of the body keeps of the frame. -/
structure Fy (s u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = fr s :: s.wr
  hi : ∀ r ∈ hiRegs, u.gpr r = s.gpr r
  r28 : u.gpr .r28 = BitVec.ofNat 64 (psLen s)

theorem Fx.fy {s u : State} (h : Fx s u) : Fy s u := ⟨h.sp, h.rd, h.wr, h.hi, h.r28⟩

theorem Fy.keep {s u v : State} (h : Fy s u) {rs : List Reg} (k : Keep rs u v)
    (hrs : ∀ r ∈ rs, r ∉ .r28 :: hiRegs := by decide) : Fy s v :=
  have g : ∀ r ∈ Reg.r28 :: hiRegs, v.gpr r = u.gpr r := fun r hr => k.gpr r fun h => hrs r h hr
  ⟨k.sp.trans h.sp, k.rd.trans h.rd, k.wr.trans h.wr,
    fun r hr => (g r (List.mem_cons_of_mem _ hr)).trans (h.hi r hr), (g _ (by decide)).trans h.r28⟩

theorem bytes_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun j hj => hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hj)

theorem words_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n * 8⟩ : Region).Disjoint r) :
    Spec.Rsa.wordsAt m' p n = Spec.Rsa.wordsAt m p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  exact hf.readW (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega_using [hj]))) (by decide)

theorem tape_c0 (s : State) : (tapeR s).Contains (s.gpr .r5) 8 := Region.contains_self' (by decide)

theorem tape_c8 (s : State) : (tapeR s).Contains (s.gpr .r5 + BitVec.ofNat 64 8) 8 :=
  Offset.contains_base _ (by decide) (by decide)

theorem in_tape {s : State} (hp : RPre s) (u : State) (hwr : u.wr = fr s :: s.wr) {a : Addr}
    (ha : (tapeR s).Contains a 8) : InRegions u.wr a 8 := by
  rw [hwr, hp.hwr]; exact ⟨tapeR s, by simp, ha⟩

theorem rd_t80 (s : State) (m : Mem) (v : BitVec 64) :
    (m.writeW (s.gpr .r5 + BitVec.ofNat 64 8) v).readW (s.gpr .r5) 64 = m.readW (s.gpr .r5) 64 :=
  Mem.readW_writeW_sep (Offset.sep_base _ (by decide) (by decide)) (by decide)

/-- The bytes just written. -/
theorem bytesAt_writeBytes (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem
  · simp [Spec.Rsa.bytesAt]
  · intro i h₁ h₂
    have hi : i < xs.length := h₂
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, writeBytes,
      Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hi h), hi,
      ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- The contract's postcondition, by name. -/
def post (s u : State) : Prop :=
  let res := Spec.RsaPkcs1Enc.padSearch (psLen s) (randB s)
  (∃ req, u.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 res.used ∧
    u.mem.readW (s.gpr .r5 + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 req ∧
    res.Requests (Spec.RsaPkcs1Enc.padEntropy (psLen s)) req) ∧
  match res.outcome with
  | .accepted ps => Spec.Rsa.publicPrecompute (nB s) = some (preW s) →
      Spec.RsaPkcs1Enc.writtenRandom u.mem (s.gpr .r3) (kOf s) ((u.gpr .r3).setWidth 32)
        (Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) ps)
  | .entropy .. => (u.gpr .r3).setWidth 32 = 0 ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .r3) (kOf s) = List.replicate (kOf s) 0
  | .exhausted => (u.gpr .r3).setWidth 32 = 3 ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .r3) (kOf s) = List.replicate (kOf s) 0

theorem pb_add (s : State) (j : Nat) : pb s + BitVec.ofNat 64 j = fb s + BitVec.ofNat 64 (oBuf + j) := by
  rw [pb, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem in_ps (s : State) (u : State) (hwr : u.wr = fr s :: s.wr) {n : Nat} (hn : n ≤ 1024) :
    ∀ j < n, InRegions u.wr (pb s + BitVec.ofNat 64 j) 1 := fun j hj => by
  rw [hwr, pb_add]; exact in_fr s _ (by unfold oBuf; omega_using []) (by unfold oBuf frameBytes; omega_using [hn, hj])

/-- A wipe of the first `n` octets of `PS`. -/
theorem wipe_frame (s : State) (m : Mem) (n : Nat) :
    Frame [⟨pb s, n⟩] m (writeBytes m (pb s) (List.replicate n 0)) :=
  writeBytes_frame _ _ _ (by rw [List.length_replicate]; exact Region.contains_self _ _)

/-- What the end of the body leaves. -/
structure Fin (s x : State) : Prop where
  sv : Saves s x
  rd : x.rd = s.rd
  post : post s x

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
  have := sub_ne ha hb
  rw [bne] at this
  cases h : (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) <;> rw [h] at this <;> simp at this <;> simp [this]

theorem sub_ofNat {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega_using [h, ha]), Nat.mod_eq_of_lt (show a - b < 2 ^ 64 by omega_using [ha])]
  omega_using [h, ha]

/-- Whether `PS` is full, after the scan. -/
theorem full_ok {s : State} (hp : RPre s) {M : Mem} {i : Nat} {u : State} (hI : At s M i u) :
    WP isa (.block [.sub .r12 .r28 .r5]) u fun v => At s M i v ∧
      isa.eval (.zero .d .r12) v = some (decide (psLen s = (kept s i).length)) := by
  have hk := kept_le hp hI
  have hP := hp.ps
  refine wp_sub fun v o e => wp_nil ⟨hI.only o, ?_⟩
  rw [eval_zero, e, hI.r28, hI.r5, sub_beq (by omega_using [hP]) (by omega_using [hk])]

end VG.Proof.RsaPkcs1Enc.PPC64LE.Rnd

end

end

/-! ### `RsaPkcs1Enc.PPC64LE.RndCall`, which the modules that import this one used -/

section

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on PPC64LE: accepting

With `PS` full after `i` octets: `tape` is `[i, 0]`, and the arguments of
`vg_rsa_pkcs1_encrypt_precomputed` in registers and at `sp + 96` of the
frame (`prep_ok`, into `Args`); the call by its contract (`call_ok`, into
`AfterCall`), narrowed to the regions it reads and writes (`callRd`,
`callWr`), from its precondition at the entry (`preE_entry`); the status
`2 - r` and the wipe of `PS` (`accTail_ok`, `accept_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Rnd

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Random VG.Proof.RsaPkcs1Sig.PPC64LE
open VG.WriteBytes (writeBytes)
open VG.Impl.RsaPkcs1Sig.PPC64LE (fillLoop)

/-- The callee's stack arguments. -/
def callArg (s : State) : Nat → Addr
  | 0 => pb s
  | 1 => BitVec.ofNat 64 (psLen s)
  | 2 => stackArg s 3
  | 3 => stackArg s 4
  | 4 => stackArg s 5
  | _ => stackArg s 6

/-- The callee's stack arguments in the frame. -/
abbrev caR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 96, 48⟩

/-- After the call's arguments. -/
structure Args (s : State) (i : Nat) (w : State) : Prop extends Fy s w where
  fr : Frame [kR s, tapeR s] s.mem w.mem
  sv : Spill.Saved (fb s) s.gpr saved w.mem
  ls : w.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr
  t0 : w.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 i
  t1 : w.mem.readW (s.gpr .r5 + BitVec.ofNat 64 8) 64 = 0
  c0 : w.mem.readW (fb s + BitVec.ofNat 64 96) 64 = callArg s 0
  c1 : w.mem.readW (fb s + BitVec.ofNat 64 104) 64 = callArg s 1
  c2 : w.mem.readW (fb s + BitVec.ofNat 64 112) 64 = callArg s 2
  c3 : w.mem.readW (fb s + BitVec.ofNat 64 120) 64 = callArg s 3
  c4 : w.mem.readW (fb s + BitVec.ofNat 64 128) 64 = callArg s 4
  c5 : w.mem.readW (fb s + BitVec.ofNat 64 136) 64 = callArg s 5
  buf : Spec.Rsa.bytesAt w.mem (pb s) (psLen s) = kept s i
  g3 : w.gpr .r3 = s.gpr .r3
  g4 : w.gpr .r4 = s.gpr .r7
  g5 : w.gpr .r5 = s.gpr .r6
  g6 : w.gpr .r6 = s.gpr .r7
  g7 : w.gpr .r7 = s.gpr .r8
  g8 : w.gpr .r8 = s.gpr .r9
  g9 : w.gpr .r9 = s.gpr .r10
  g10 : w.gpr .r10 = stackArg s 0
  g12 : w.gpr .r12 = fb s

/-! ## Memory -/

/-- A frame write leaves a tape word. -/
theorem rd_tf {s : State} (hp : RPre s) (m : Mem) {e : Nat} (he : e + 8 ≤ frameBytes) (v : BitVec 64)
    {a : Addr} (ha : (tapeR s).Contains a 8) :
    (m.writeW (fb s + BitVec.ofNat 64 e) v).readW a 64 = m.readW a 64 :=
  Mem.readW_writeW_sep (hp.dKt.symm.sep ha (frame_contains s he)) (by decide)

/-- A frame write leaves another frame word. -/
theorem rd_ff (s : State) (m : Mem) {d e : Nat} (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (v : BitVec 64) :
    (m.writeW (fb s + BitVec.ofNat 64 e) v).readW (fb s + BitVec.ofNat 64 d) 64 =
      m.readW (fb s + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega_using [hd]) (by omega_using [he])) (by decide)

/-- The stack arguments are read from memory changed only in the stack and
the tape. -/
theorem arg_read' {s : State} (hp : RPre s) {m : Mem} (hm : Frame [kR s, tapeR s] s.mem m) {j : Nat} (hj : j < 7) :
    m.readW (fb s + BitVec.ofNat 64 (arg j)) 64 = stackArg s j := by
  rw [← stackArgAddr_fb]
  refine hm.readW (in_argsR hj) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.dKa.symm
  · exact hp.dTa.symm

theorem caR_sub (s : State) : Region.Sub (caR s) (kR s) := frame_sub s (by decide)

theorem fr_cw {s : State} {m : Mem} (h : Frame [kR s, tapeR s] s.mem m) {e : Nat} (he : e + 8 ≤ frameBytes)
    (v : BitVec 64) : Frame [kR s, tapeR s] s.mem (m.writeW (fb s + BitVec.ofNat 64 e) v) :=
  h.writeW (List.mem_cons_self ..) _ (frame_contains s he)

theorem fr_tw {s : State} {m : Mem} (h : Frame [kR s, tapeR s] s.mem m) {a : Addr} (ha : (tapeR s).Contains a 8)
    (v : BitVec 64) : Frame [kR s, tapeR s] s.mem (m.writeW a v) :=
  h.writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ ha

theorem gr_cw {s : State} {m₀ m : Mem} (h : Frame [tapeR s, caR s] m₀ m) {e : Nat} (he₁ : 96 ≤ e) (he : e + 8 ≤ 144)
    (v : BitVec 64) : Frame [tapeR s, caR s] m₀ (m.writeW (fb s + BitVec.ofNat 64 e) v) :=
  h.writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Offset.contains _ he₁ (by omega_using [he]) (by decide))

theorem gr_tw {s : State} {m₀ m : Mem} (h : Frame [tapeR s, caR s] m₀ m) {a : Addr} (ha : (tapeR s).Contains a 8)
    (v : BitVec 64) : Frame [tapeR s, caR s] m₀ (m.writeW a v) :=
  h.writeW (List.mem_cons_self ..) _ ha

/-! ## The arguments -/

theorem prep_ok {s : State} (hp : RPre s) {M : Mem} (hM : Mm s M) {i : Nat} {u : State} (hI : At s M i u)
    (hf : (kept s i).length = psLen s) :
    WP isa (.block (stackArgs ++ Impl.RsaPkcs1Enc.PPC64LE.Random.regArgs)) u (Args s i) := by
  have hP := hp.ps
  have hk2 := hp.k2
  obtain hMu : Mm s u.mem := by rw [hI.mem]; exact hM.buf _ (by omega_using [hf, hP])
  obtain F0 : Frame [kR s, tapeR s] s.mem u.mem := hMu.fr.mono (by simp)
  have hw := hI.wr
  unfold stackArgs Impl.RsaPkcs1Enc.PPC64LE.Random.regArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_std (a := s.gpr .r5) (by rw [hI.r30, BitVec.add_zero]) (in_tape hp u hw (tape_c0 s))
    fun u₁ m₁ => wp_li (by decide) fun u₂ o₂ e₂ => wp_std (a := s.gpr .r5 + BitVec.ofNat 64 8)
    (by rw [o₂.get .r30, m₁.gpr, hI.r30]) (in_tape hp u₂ (by rw [o₂.wr, m₁.wr, hw]) (tape_c8 s))
    fun u₃ m₃ => wp_addSp fun u₄ o₄ e₄ => ?_
  obtain sp₄ : u₄.sp = fb s := by rw [o₄.sp, m₃.sp, o₂.sp, m₁.sp, hI.sp]
  obtain r12 : u₄.gpr .r12 = fb s := by rw [e₄, BitVec.add_zero, m₃.sp, o₂.sp, m₁.sp, hI.sp]
  obtain wr₄ : u₄.wr = fr s :: s.wr := by rw [o₄.wr, m₃.wr, o₂.wr, m₁.wr, hw]
  obtain rd₄ : u₄.rd = s.rd := by rw [o₄.rd, m₃.rd, o₂.rd, m₁.rd, hI.rd]
  obtain k₄ : Keep [.r0, .r12] u u₄ := (m₁.keep.trans (o₂.keep.trans (m₃.keep.trans o₄.keep))).mono
  obtain mem₄ : u₄.mem = (u.mem.writeW (s.gpr .r5) (BitVec.ofNat 64 i)).writeW (s.gpr .r5 + BitVec.ofNat 64 8)
      (BitVec.ofNat 64 0) := by
    rw [o₄.mem, m₃.mem, e₂, o₂.mem, m₁.mem, hI.r4]
  obtain fin : ∀ {e : Nat}, e + 8 ≤ frameBytes → 32 ≤ e → ∀ v : State, v.wr = u₄.wr →
      InRegions v.wr (fb s + BitVec.ofNat 64 e) 8 := fun h₁ h₂ v hv => by
    rw [hv, wr₄]; exact in_fr s _ h₂ h₁
  refine wp_std (a := fb s + BitVec.ofNat 64 96) (by rw [r12]) (fin (by decide) (by decide) _ rfl)
    fun u₅ m₅ => wp_std (a := fb s + BitVec.ofNat 64 104) (by rw [m₅.gpr, r12])
    (fin (by decide) (by decide) _ m₅.wr) fun u₆ m₆ => ?_
  obtain g6 : u₆.gpr = u₄.gpr := by rw [m₆.gpr, m₅.gpr]
  obtain F6 : Frame [kR s, tapeR s] s.mem u₆.mem := by
    rw [m₆.mem, m₅.mem, mem₄]
    exact fr_cw (fr_cw (fr_tw (fr_tw F0 (tape_c0 s) _) (tape_c8 s) _) (by decide) _) (by decide) _
  refine wp_ld (a := fb s + BitVec.ofNat 64 (arg 3)) (by rw [g6, r12])
    (arg_in' hp (by rw [m₆.rd, m₅.rd, rd₄]) (j := 3) (by decide)) fun u₇ o₇ e₇ => ?_
  rw [arg_read' hp F6 (by decide)] at e₇
  refine wp_std (a := fb s + BitVec.ofNat 64 112) (by rw [o₇.get .r12, g6, r12])
    (fin (by decide) (by decide) _ (by rw [o₇.wr, m₆.wr, m₅.wr])) fun u₈ m₈ => ?_
  obtain F8 : Frame [kR s, tapeR s] s.mem u₈.mem := by rw [m₈.mem, o₇.mem]; exact fr_cw F6 (by decide) _
  refine wp_ld (a := fb s + BitVec.ofNat 64 (arg 4)) (by rw [m₈.gpr, o₇.get .r12, g6, r12])
    (arg_in' hp (by rw [m₈.rd, o₇.rd, m₆.rd, m₅.rd, rd₄]) (j := 4) (by decide))
    fun u₉ o₉ e₉ => ?_
  rw [arg_read' hp F8 (by decide)] at e₉
  refine wp_std (a := fb s + BitVec.ofNat 64 120) (by rw [o₉.get .r12, m₈.gpr, o₇.get .r12, g6, r12])
    (fin (by decide) (by decide) _ (by rw [o₉.wr, m₈.wr, o₇.wr, m₆.wr, m₅.wr])) fun u₁₀ m₁₀ => ?_
  obtain F10 : Frame [kR s, tapeR s] s.mem u₁₀.mem := by rw [m₁₀.mem, o₉.mem]; exact fr_cw F8 (by decide) _
  obtain k₁₀ : Keep [.r0] u₄ u₁₀ := (m₅.keep.trans (m₆.keep.trans (o₇.keep.trans (m₈.keep.trans
    (o₉.keep.trans m₁₀.keep))))).mono
  refine wp_ld (a := fb s + BitVec.ofNat 64 (arg 5)) (by rw [k₁₀.get .r12, r12])
    (arg_in' hp (by rw [k₁₀.rd, rd₄]) (j := 5) (by decide)) fun u₁₁ o₁₁ e₁₁ => ?_
  rw [arg_read' hp F10 (by decide)] at e₁₁
  refine wp_std (a := fb s + BitVec.ofNat 64 128) (by rw [o₁₁.get .r12, k₁₀.get .r12, r12])
    (fin (by decide) (by decide) _ (by rw [o₁₁.wr, k₁₀.wr])) fun u₁₂ m₁₂ => ?_
  obtain F12 : Frame [kR s, tapeR s] s.mem u₁₂.mem := by rw [m₁₂.mem, o₁₁.mem]; exact fr_cw F10 (by decide) _
  obtain k₁₂ : Keep [.r0] u₄ u₁₂ := (k₁₀.trans (o₁₁.keep.trans m₁₂.keep)).mono
  refine wp_ld (a := fb s + BitVec.ofNat 64 (arg 6)) (by rw [k₁₂.get .r12, r12])
    (arg_in' hp (by rw [k₁₂.rd, rd₄]) (j := 6) (by decide)) fun u₁₃ o₁₃ e₁₃ => ?_
  rw [arg_read' hp F12 (by decide)] at e₁₃
  refine wp_std (a := fb s + BitVec.ofNat 64 136) (by rw [o₁₃.get .r12, k₁₂.get .r12, r12])
    (fin (by decide) (by decide) _ (by rw [o₁₃.wr, k₁₂.wr])) fun u₁₄ m₁₄ => ?_
  obtain k₁₄ : Keep [.r0] u₄ u₁₄ := (k₁₂.trans (o₁₃.keep.trans m₁₄.keep)).mono
  obtain mem₁₄ : u₁₄.mem = ((((((u₄.mem.writeW (fb s + BitVec.ofNat 64 96) (pb s)).writeW
      (fb s + BitVec.ofNat 64 104) (BitVec.ofNat 64 (psLen s))).writeW (fb s + BitVec.ofNat 64 112)
      (stackArg s 3)).writeW (fb s + BitVec.ofNat 64 120) (stackArg s 4)).writeW (fb s + BitVec.ofNat 64 128)
      (stackArg s 5)).writeW (fb s + BitVec.ofNat 64 136) (stackArg s 6)) := by
    rw [m₁₄.mem, o₁₃.mem, m₁₂.mem, o₁₁.mem, m₁₀.mem, o₉.mem, m₈.mem, o₇.mem, m₆.mem, m₅.mem, e₁₃, e₁₁, e₉, e₇,
      m₅.gpr, k₄.get .r28, hI.r28, k₄.get .r7, hI.r7]
  obtain F14 : Frame [kR s, tapeR s] s.mem u₁₄.mem := by rw [m₁₄.mem, o₁₃.mem]; exact fr_cw F12 (by decide) _
  obtain G14 : Frame [tapeR s, caR s] u.mem u₁₄.mem := by
    rw [mem₁₄, mem₄]
    exact gr_cw (gr_cw (gr_cw (gr_cw (gr_cw (gr_cw (gr_tw (gr_tw (Frame.refl _ _) (tape_c0 s) _) (tape_c8 s) _)
      (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _)
      (by decide) (by decide) _) (by decide) (by decide) _
  obtain K : Keep ([.r0, .r12] ++ [.r0]) u u₁₄ := k₄.trans k₁₄
  obtain gK : ∀ r, r ∉ [Reg.r0, .r12, .r0] → u₁₄.gpr r = u.gpr r := fun r hr => K.gpr r hr
  obtain h12 : u₁₄.gpr .r12 = fb s := (k₁₄.get .r12).trans r12
  obtain a0 : u₁₄.mem.readW (fb s + BitVec.ofNat 64 (arg 0)) 64 = stackArg s 0 := arg_read' hp F14 (by decide)
  obtain i0 : InRegions (u₁₄.rd ++ u₁₄.wr) (fb s + BitVec.ofNat 64 (arg 0)) 8 :=
    arg_in' hp (by rw [k₁₄.rd, rd₄]) (by decide)
  obtain c0 : arg 0 < 2 ^ 15 := by decide
  obtain d0 : arg 0 % 4 = 0 := by decide
  obtain g31 := (gK .r31 (by decide)).trans hI.r31
  obtain g29 := (gK .r29 (by decide)).trans hI.r29
  obtain g6 := (gK .r6 (by decide)).trans hI.r6
  obtain g8 := (gK .r8 (by decide)).trans hI.r8
  obtain g9 := (gK .r9 (by decide)).trans hI.r9
  obtain g10 := (gK .r10 (by decide)).trans hI.r10
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]
    (Q := fun w => w.gpr .r3 = s.gpr .r3 ∧ w.gpr .r4 = s.gpr .r7 ∧ w.gpr .r5 = s.gpr .r6 ∧
      w.gpr .r6 = s.gpr .r7 ∧ w.gpr .r7 = s.gpr .r8 ∧ w.gpr .r8 = s.gpr .r9 ∧ w.gpr .r9 = s.gpr .r10 ∧
      w.gpr .r10 = stackArg s 0 ∧ w.mem = u₁₄.mem) ?_ rfl)
    fun w ⟨⟨w3, w4, w5, w6, w7, w8, w9, w10, wm⟩, kw'⟩ => ?_
  · prun [Impl.AesGcm.PPC64LE.mov, BitVec.or_self, c0, d0, i0, a0, h12, g31, g29, g6, g8, g9, g10]
  obtain kw : Keep [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] u₁₄ w := ⟨kw'.gpr, kw'.rd, kw'.wr, kw'.sp, kw'.lr⟩
  obtain slK : Region.Sub (slR s) (kR s) := frame_sub s (by decide)
  obtain slD : ∀ r ∈ [tapeR s, caR s], (slR s).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dKt.sub_left slK
    · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
  obtain psD : ∀ r ∈ [tapeR s, caR s], (⟨pb s, psLen s⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dKt.sub_left (buf_sub s (by omega_using [hP]))
    · exact Offset.disjoint _ (.inr (by decide)) (by unfold oBuf; omega_using [hP]) (by decide)
  obtain hb := bytesAt_writeBytes M (pb s) (kept s i) (by omega_using [hf, hP])
  rw [hf] at hb
  refine ⟨((hI.toFx.fy.keep k₄).keep k₁₄).keep kw, wm ▸ F14,
    wm ▸ hMu.sv.frame G14 fun p hp' r hr => (slD r hr).sub_left (slot_sub s hp'), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, by rw [wm, bytes_frame G14 psD (by omega_using [hP]), hI.mem, hb], w3, w4, w5, w6, w7, w8, w9, w10,
    (kw.get .r12).trans h12⟩
  · rw [wm, G14.readW (Region.contains_self _ _) (fun r hr => (slD r hr).sub_left (lr_sub s)) (by decide)]
    exact hMu.ls
  · rw [wm, mem₁₄, rd_tf hp _ (by decide) _ (tape_c0 s), rd_tf hp _ (by decide) _ (tape_c0 s),
      rd_tf hp _ (by decide) _ (tape_c0 s), rd_tf hp _ (by decide) _ (tape_c0 s),
      rd_tf hp _ (by decide) _ (tape_c0 s), rd_tf hp _ (by decide) _ (tape_c0 s), mem₄, rd_t80,
      Mem.readW_writeW_self64]
  · rw [wm, mem₁₄, rd_tf hp _ (by decide) _ (tape_c8 s), rd_tf hp _ (by decide) _ (tape_c8 s),
      rd_tf hp _ (by decide) _ (tape_c8 s), rd_tf hp _ (by decide) _ (tape_c8 s),
      rd_tf hp _ (by decide) _ (tape_c8 s), rd_tf hp _ (by decide) _ (tape_c8 s), mem₄,
      Mem.readW_writeW_self64]; rfl
  · rw [wm, mem₁₄, rd_ff s _ (.inl (by decide)) (by decide) (by decide), rd_ff s _ (.inl (by decide)) (by decide)
      (by decide), rd_ff s _ (.inl (by decide)) (by decide) (by decide), rd_ff s _ (.inl (by decide)) (by decide)
      (by decide), rd_ff s _ (.inl (by decide)) (by decide) (by decide), Mem.readW_writeW_self64]; rfl
  · rw [wm, mem₁₄, rd_ff s _ (.inl (by decide)) (by decide) (by decide), rd_ff s _ (.inl (by decide)) (by decide)
      (by decide), rd_ff s _ (.inl (by decide)) (by decide) (by decide), rd_ff s _ (.inl (by decide)) (by decide)
      (by decide), Mem.readW_writeW_self64]; rfl
  · rw [wm, mem₁₄, rd_ff s _ (.inl (by decide)) (by decide) (by decide), rd_ff s _ (.inl (by decide)) (by decide)
      (by decide), rd_ff s _ (.inl (by decide)) (by decide) (by decide), Mem.readW_writeW_self64]; rfl
  · rw [wm, mem₁₄, rd_ff s _ (.inl (by decide)) (by decide) (by decide), rd_ff s _ (.inl (by decide)) (by decide)
      (by decide), Mem.readW_writeW_self64]; rfl
  · rw [wm, mem₁₄, rd_ff s _ (.inl (by decide)) (by decide) (by decide), Mem.readW_writeW_self64]; rfl
  · rw [wm, mem₁₄, Mem.readW_writeW_self64]; rfl

/-- What the callee reads: `n`, `e`, `msg`, `PS`, `pre` and its stack
arguments. -/
abbrev callRd (s : State) : List Region := [nR s, eR s, msgR s, ⟨pb s, psLen s⟩, preR s, caR s]

/-- What it writes: `out` and the working space. -/
abbrev callWr (s : State) : List Region := [outR s, scrR s]

/-- The callee's narrowed entry state. -/
abbrev callE (s w : State) : State := w.callEntry.withRegions (callRd s) (callWr s)

theorem callE_gpr (s w : State) {r : Reg} (hr : r ∉ linkRegs := by decide) : (callE s w).gpr r = w.gpr r :=
  State.callEntry_gpr w hr

theorem callE_sp {s w : State} {i : Nat} (A : Args s i w) : (callE s w).sp = fb s := A.sp

/-- The callee's stack base, below the frame. -/
theorem kb_callee (s : State) : fb s - BitVec.ofNat 64 Impl.RsaPkcs1Sig.PPC64LE.frameBytes = kb s := by
  rw [fb_eq, BitVec.add_sub_cancel]

theorem callee_kR {s w : State} {i : Nat} (A : Args s i w) :
    VG.Proof.RsaPkcs1Sig.PPC64LE.kR (callE s w) = ⟨kb s, Impl.RsaPkcs1Sig.PPC64LE.frameBytes⟩ := by
  simp only [VG.Proof.RsaPkcs1Sig.PPC64LE.kR, VG.Proof.RsaPkcs1Sig.PPC64LE.fb, callE_sp A, kb_callee]

theorem callee_sub (s : State) : Region.Sub ⟨kb s, Impl.RsaPkcs1Sig.PPC64LE.frameBytes⟩ (kR s) :=
  Region.sub_prefix (by decide)

theorem fb_kb (s : State) (d : Nat) :
    fb s + BitVec.ofNat 64 d = kb s + BitVec.ofNat 64 (Impl.RsaPkcs1Sig.PPC64LE.frameBytes + d) := by
  rw [fb_eq, Offset.add_add]

theorem enc_sdepth : sdepth Impl.RsaPkcs1Enc.PPC64LE.Precomputed.code = Impl.RsaPkcs1Sig.PPC64LE.frameBytes := by
  decide +kernel

theorem psLen_toNat {s : State} (hp : RPre s) : (BitVec.ofNat 64 (psLen s)).toNat = psLen s := by
  have := hp.ps; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [this])

theorem pb_toNat {s : State} (hp : RPre s) : (pb s).toNat + psLen s ≤ 2 ^ 64 := by
  obtain hF := fb_toNat hp
  have := hp.ps
  have := hp.sp2
  rw [pb, Offset.toNat_add_ofNat]; unfold oBuf frameBytes at *; omega_arith

theorem callE_arg {s w : State} {i : Nat} (A : Args s i w) :
    stackArg (callE s w) 0 = callArg s 0 ∧ stackArg (callE s w) 1 = callArg s 1 ∧
      stackArg (callE s w) 2 = callArg s 2 ∧ stackArg (callE s w) 3 = callArg s 3 ∧
      stackArg (callE s w) 4 = callArg s 4 ∧ stackArg (callE s w) 5 = callArg s 5 := by
  obtain e : ∀ j, stackArg (callE s w) j = w.mem.readW (fb s + BitVec.ofNat 64 (32 + 8 * (8 + j))) 64 := fun j => by
    show w.mem.readW (w.sp + _) 64 = _; rw [A.sp]
  exact ⟨(e 0).trans A.c0, (e 1).trans A.c1, (e 2).trans A.c2, (e 3).trans A.c3, (e 4).trans A.c4,
    (e 5).trans A.c5⟩

theorem preE_entry {s w : State} (hp : RPre s) {i : Nat} (A : Args s i w) : Enc.PreE (callE s w) := by
  have hP := hp.ps
  obtain hF := fb_toNat hp
  obtain hK := kb_toNat hp
  have hk2 := hp.k2
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := callE_arg A
  obtain g3 : (callE s w).gpr .r3 = s.gpr .r3 := (callE_gpr s w).trans A.g3
  obtain g4 : (callE s w).gpr .r4 = s.gpr .r7 := (callE_gpr s w).trans A.g4
  obtain g5 : (callE s w).gpr .r5 = s.gpr .r6 := (callE_gpr s w).trans A.g5
  obtain g6 : (callE s w).gpr .r6 = s.gpr .r7 := (callE_gpr s w).trans A.g6
  obtain g7 : (callE s w).gpr .r7 = s.gpr .r8 := (callE_gpr s w).trans A.g7
  obtain g8 : (callE s w).gpr .r8 = s.gpr .r9 := (callE_gpr s w).trans A.g8
  obtain g9 : (callE s w).gpr .r9 = s.gpr .r10 := (callE_gpr s w).trans A.g9
  obtain g10 : (callE s w).gpr .r10 = stackArg s 0 := (callE_gpr s w).trans A.g10
  obtain hO : Enc.oR (callE s w) = outR s := by simp only [Enc.oR, g3, g4, outR, hp.hok]
  obtain hN : Enc.nR (callE s w) = nR s := by simp only [Enc.nR, g5, g6]
  obtain hE : Enc.eR (callE s w) = eR s := by simp only [Enc.eR, g7, g8]
  obtain hM : Enc.mR (callE s w) = msgR s := by simp only [Enc.mR, g9, g10]
  obtain hPS : Enc.psR (callE s w) = ⟨pb s, psLen s⟩ := by simp only [Enc.psR, a0, a1, callArg, psLen_toNat hp]
  obtain hS : Enc.scR (callE s w) = scrR s := by simp only [Enc.scR, a2, a3, callArg]
  obtain hQ : Enc.pR (callE s w) = preR s := by simp only [Enc.pR, a4, a5, callArg]
  obtain hA : Enc.a6R (callE s w) = caR s := by
    simp only [Enc.a6R, caR]; congr 1; show (callE s w).sp + _ = _; rw [callE_sp A]
  obtain hKR := callee_kR A
  obtain cs := callee_sub s
  obtain ps : Region.Sub ⟨pb s, psLen s⟩ (kR s) := buf_sub s (by omega_using [hP])
  obtain ca := caR_sub s
  obtain kps : Region.Disjoint ⟨kb s, Impl.RsaPkcs1Sig.PPC64LE.frameBytes⟩ ⟨pb s, psLen s⟩ := by
    rw [pb, fb_kb]
    exact Offset.base_disjoint _ (by omega_using []) (by unfold rndStack oBuf Impl.RsaPkcs1Sig.PPC64LE.frameBytes at *; omega_using [hP])
  obtain ka : Region.Disjoint ⟨kb s, Impl.RsaPkcs1Sig.PPC64LE.frameBytes⟩ (caR s) := by
    rw [caR, fb_kb]
    exact Offset.base_disjoint _ (by omega_using []) (by unfold rndStack Impl.RsaPkcs1Sig.PPC64LE.frameBytes at *; omega_using [])
  exact {
    sp1 := by rw [callE_sp A]; exact hF.2
    sp2 := by rw [callE_sp A]; have := hp.sp2; unfold frameBytes at hF; omega_using [hF]
    hrd := by rw [hN, hE, hM, hPS, hQ, hA]; rfl
    hwr := by rw [hO, hS]; rfl
    on := by rw [hO, hN]; exact hp.dOn
    oe := by rw [hO, hE]; exact hp.dOe
    om := by rw [hO, hM]; exact hp.dOm
    ops := by rw [hO, hPS]; exact hp.dKo.symm.sub_right ps
    osc := by rw [hO, hS]; exact hp.dOs
    op := by rw [hO, hQ]; exact hp.dOq
    oa := by rw [hO, hA]; exact hp.dKo.symm.sub_right ca
    ns := by rw [hN, hS]; exact hp.dNs
    es := by rw [hE, hS]; exact hp.dEs
    ms := by rw [hM, hS]; exact hp.dMs
    pss := by rw [hPS, hS]; exact hp.dKs.sub_left ps
    sp := by rw [hS, hQ]; exact hp.dSq
    sa := by rw [hS, hA]; exact hp.dKs.symm.sub_right ca
    ko := by rw [hKR, hO]; exact hp.dKo.sub_left cs
    kn := by rw [hKR, hN]; exact hp.dKn.sub_left cs
    ke := by rw [hKR, hE]; exact hp.dKe.sub_left cs
    km := by rw [hKR, hM]; exact hp.dKm.sub_left cs
    kps := by rw [hKR, hPS]; exact kps
    ksc := by rw [hKR, hS]; exact hp.dKs.sub_left cs
    kp := by rw [hKR, hQ]; exact hp.dKq.sub_left cs
    ka := by rw [hKR, hA]; exact ka
    wo := by rw [g3, g4]; have := hp.wO; rw [hp.hok] at this; exact this
    wn := by rw [g5, g6]; exact hp.wN
    we := by rw [g7, g8]; exact hp.wE
    wm := by rw [g9, g10]; exact hp.wM
    wps := by rw [a0, a1]; simp only [callArg]; rw [psLen_toNat hp]; exact pb_toNat hp
    wsc := by rw [a2, a3]; exact hp.wS
    wp := by rw [a4, a5]; exact hp.wQ
    k1 := by rw [g6]; exact hp.k1
    k2 := by rw [g6]; exact hp.k2
    ok := by rw [g4, g6]
    e1 := by rw [g8]; exact hp.L1
    e2 := by rw [g8, g6]; exact hp.L2
    ml := by rw [g10, g6]; exact hp.hml
    pl := by rw [a1, g6, g10]; simp only [callArg]; rw [psLen_toNat hp]; rfl
    hs := by rw [g6, a3]; exact hp.hsl
    hp := by rw [g6, a5]; exact hp.hql }

theorem call_covers {s w : State} (hp : RPre s) {i : Nat} (A : Args s i w) :
    Covers (callRd s ++ callWr s) (w.rd ++ w.wr) ∧ Covers (callWr s) w.wr := by
  have hP := hp.ps
  obtain hw : Covers (callWr s) w.wr := by
    rw [A.wr, hp.hwr]
    exact Covers.of_mem fun r hr => by
      simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  rw [A.rd, A.wr, hp.hrd]
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.right (Covers.one (in_fr s _ (by decide) (by unfold oBuf frameBytes; omega_using [hP])))
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.right (Covers.one (in_fr s _ (by decide) (by decide)))

/-- After the call. -/
structure AfterCall (s : State) (i : Nat) (y : State) : Prop extends Fy s y where
  fr : Frame [kR s, tapeR s, outR s, scrR s] s.mem y.mem
  sv : Spill.Saved (fb s) s.gpr saved y.mem
  ls : y.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr
  t0 : y.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 i
  t1 : y.mem.readW (s.gpr .r5 + BitVec.ofNat 64 8) 64 = 0
  res : Spec.Rsa.publicPrecompute (nB s) = some (preW s) →
    Spec.Rsa.written y.mem (s.gpr .r3) (kOf s) ((y.gpr .r3).setWidth 32)
      (Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) (kept s i))

theorem call_ok {s w : State} (hp : RPre s) {i : Nat} (A : Args s i w) :
    WP isa encCall w (AfterCall s i) := by
  have hP := hp.ps
  obtain ⟨hc, hw⟩ := call_covers hp A
  unfold encCall
  refine WP.callAny (k := encK) Enc.code_verified.1 (enc_pre (preE_entry hp A)) hc hw
    (fun y hrd hwr hsp hf hpres hpost => ?_) (by rw [enc_sdepth]; decide)
  obtain hb : below w.sp (sdepth Impl.RsaPkcs1Enc.PPC64LE.Precomputed.code) =
      ⟨kb s, Impl.RsaPkcs1Sig.PPC64LE.frameBytes⟩ := by
    rw [enc_sdepth, A.sp]
    show (⟨fb s - BitVec.ofNat 64 Impl.RsaPkcs1Sig.PPC64LE.frameBytes, _⟩ : Region) = _
    rw [kb_callee]
  rw [hb] at hf
  simp only [callWr, List.cons_append, List.nil_append] at hf
  have hpr : ∀ r ∈ preserved, y.gpr r = w.gpr r := hpres
  obtain cs := callee_sub s
  obtain kd : ∀ {R : Region}, R.Disjoint (outR s) → R.Disjoint (scrR s) →
      R.Disjoint ⟨kb s, Impl.RsaPkcs1Sig.PPC64LE.frameBytes⟩ →
      ∀ r ∈ [outR s, scrR s, (⟨kb s, Impl.RsaPkcs1Sig.PPC64LE.frameBytes⟩ : Region)], R.Disjoint r :=
    fun h₁ h₂ h₃ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [h₁, h₂, h₃]
  obtain slK : Region.Sub (slR s) (kR s) := frame_sub s (by decide)
  obtain slC : (slR s).Disjoint ⟨kb s, Impl.RsaPkcs1Sig.PPC64LE.frameBytes⟩ := by
    rw [slR, fb_kb]
    exact Offset.disjoint_base _ (by omega_using []) (by unfold Impl.RsaPkcs1Sig.PPC64LE.frameBytes; decide)
  obtain slD := kd (hp.dKo.sub_left slK) (hp.dKs.sub_left slK) slC
  obtain tD := kd hp.dOt.symm hp.dTs (hp.dKt.sub_left cs).symm
  refine ⟨⟨hsp.trans A.sp, hrd.trans A.rd, hwr.trans A.wr,
      fun r hr => (hpr r (by revert r; decide)).trans (A.hi r hr), (hpr _ (by decide)).trans A.r28⟩,
    ?_, A.sv.frame hf fun p hp' r hr => (slD r hr).sub_left (slot_sub s hp'), ?_, ?_, ?_, ?_⟩
  · refine (A.fr.mono (by simp)).trans (hf.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨outR s, by simp, fun _ h => h⟩
    · exact ⟨scrR s, by simp, fun _ h => h⟩
    · exact ⟨kR s, by simp, cs⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => (slD r hr).sub_left (lr_sub s)) (by decide)]; exact A.ls
  · rw [hf.readW (tape_c0 s) tD (by decide)]; exact A.t0
  · rw [hf.readW (tape_c8 s) tD (by decide)]; exact A.t1
  · intro hq
    obtain hpo := enc_post hpost
    obtain ⟨a0, a1, -, -, a4, a5⟩ := callE_arg A
    simp only [State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem, callE_gpr s w (r := .r3),
      callE_gpr s w (r := .r5), callE_gpr s w (r := .r6), callE_gpr s w (r := .r7), callE_gpr s w (r := .r8),
      callE_gpr s w (r := .r9), callE_gpr s w (r := .r10), A.g3, A.g5, A.g6, A.g7, A.g8, A.g9, A.g10, a0, a1,
      a4, a5, callArg, psLen_toNat hp, A.buf] at hpo
    obtain hn : Spec.Rsa.bytesAt w.mem (s.gpr .r6) (s.gpr .r7).toNat = nB s :=
      bytes_frame A.fr (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [hp.dKn.symm, hp.dTn.symm]) (by have := hp.wN; omega_using [])
    obtain he : Spec.Rsa.bytesAt w.mem (s.gpr .r8) (s.gpr .r9).toNat = eB s :=
      bytes_frame A.fr (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [hp.dKe.symm, hp.dTe.symm]) (by have := hp.wE; omega_using [])
    obtain hm : Spec.Rsa.bytesAt w.mem (s.gpr .r10) (stackArg s 0).toNat = msgB s :=
      bytes_frame A.fr (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [hp.dKm.symm, hp.dTm.symm]) (by have := hp.wM; omega_using [])
    obtain hw' : Spec.Rsa.wordsAt w.mem (stackArg s 5) (stackArg s 6).toNat = preW s :=
      words_frame A.fr fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [hp.dKq.symm, hp.dTq.symm]
    rw [hn, he, hm, hw'] at hpo
    exact hpo hq

/-! ## The status and the wipe -/

/-- `writtenRandom` from `written` and the status `2 - r`. -/
theorem written_random {m : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {res : Option (List Byte)}
    (h : Spec.Rsa.written m out k r res) :
    Spec.RsaPkcs1Enc.writtenRandom m out k (2 - r) res := by
  cases res with
  | some C => obtain ⟨h1, h2⟩ := h; subst h1; exact ⟨rfl, h2⟩
  | none => obtain ⟨h1, h2⟩ := h; subst h1; exact ⟨rfl, h2⟩

theorem trunc_sub2 (a : BitVec 64) : (BitVec.ofNat 64 2 - a).setWidth 32 = 2 - a.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  have h2 : (2 : BitVec 32).toNat = 2 := rfl
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, h2]
  have := a.isLt
  omega_using []

theorem accTail_ok {s y : State} (hp : RPre s) {i : Nat} (A : AfterCall s i y) :
    WP isa (.seq (.block status) (.seq fillLoop (.block [Impl.AesGcm.PPC64LE.mov .r3 .r5]))) y fun x =>
      Saves s x ∧ x.rd = s.rd ∧ x.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 i ∧
      x.mem.readW (s.gpr .r5 + BitVec.ofNat 64 8) 64 = 0 ∧
      (Spec.Rsa.publicPrecompute (nB s) = some (preW s) →
        Spec.RsaPkcs1Enc.writtenRandom x.mem (s.gpr .r3) (kOf s) ((x.gpr .r3).setWidth 32)
          (Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) (kept s i))) := by
  have hP := hp.ps
  unfold status
  refine WP.seq (wp_li (by decide) fun y₁ o₁ e₁ => wp_sub fun y₂ o₂ e₂ => wp_addSp fun y₃ o₃ e₃ =>
    wp_addi fun y₄ o₄ e₄ => wp_mov fun y₅ o₅ e₅ => wp_li (by decide) fun z o₆ e₆ => wp_nil ?_)
  obtain k : Keep [.r5, .r12, .r4, .r11, .r0] y z :=
    (o₁.keep.trans (o₂.keep.trans (o₃.keep.trans (o₄.keep.trans (o₅.keep.trans o₆.keep))))).mono
  obtain zm : z.mem = y.mem := by rw [o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  obtain z4 : z.gpr .r4 = pb s := by
    rw [o₆.get .r4, o₅.get .r4, e₄, e₃, BitVec.add_zero, o₂.sp, o₁.sp, A.sp]
  obtain z11 : z.gpr .r11 = BitVec.ofNat 64 (psLen s) := by
    rw [o₆.get .r11, e₅, o₄.get .r28, o₃.get .r28, o₂.get .r28, o₁.get .r28, A.r28]
  obtain z5 : z.gpr .r5 = BitVec.ofNat 64 2 - y.gpr .r3 := by
    rw [o₆.get .r5, o₅.get .r5, o₄.get .r5, o₃.get .r5, e₂, e₁, o₁.get .r3]
  obtain zw : z.wr = fr s :: s.wr := k.wr.trans A.wr
  refine WP.seq (WP.mono (fill_ok (n := psLen s) (p := pb s) (b := 0) (by omega_using [hP]) (by omega_using [hP]) z4 z11
    (by rw [e₆]; rfl) (in_ps s z zw (by omega_using [hP]))) fun x₁ ⟨k₁, m₁⟩ => ?_)
  refine wp_mov fun x o₂' e₂' => wp_nil ?_
  obtain kk : Keep ([.r5, .r12, .r4, .r11, .r0] ++ ([.r4, .r11] ++ [.r3])) y x := k.trans (k₁.trans o₂'.keep)
  obtain fy : Fy s x := A.toFy.keep kk
  obtain hf : Frame [⟨pb s, psLen s⟩] y.mem x.mem := by rw [o₂'.mem, m₁, zm]; exact wipe_frame s _ _
  obtain slD : (slR s).Disjoint ⟨pb s, psLen s⟩ := slR_buf s (by omega_using [hP])
  obtain bs := buf_sub s (n := psLen s) (by omega_using [hP])
  obtain tD : ∀ r ∈ [(⟨pb s, psLen s⟩ : Region)], (tapeR s).Disjoint r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (hp.dKt.sub_left bs).symm
  refine ⟨⟨fy.sp, fy.wr, fy.hi, A.sv.frame hf fun p hp' r hr => by
      rw [List.mem_singleton.mp hr]; exact slD.sub_left (slot_sub s hp'),
    by rw [hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact slD.sub_left (lr_sub s)) (by decide)]; exact A.ls⟩, fy.rd,
    by rw [hf.readW (tape_c0 s) tD (by decide)]; exact A.t0, by rw [hf.readW (tape_c8 s) tD (by decide)]; exact A.t1,
    fun hq => ?_⟩
  obtain hw := written_random (A.res hq)
  obtain hx3 : (x.gpr .r3).setWidth 32 = 2 - (y.gpr .r3).setWidth 32 := by
    rw [e₂', k₁.get .r5, z5, trunc_sub2]
  obtain hout : Spec.Rsa.bytesAt x.mem (s.gpr .r3) (kOf s) = Spec.Rsa.bytesAt y.mem (s.gpr .r3) (kOf s) :=
    bytes_frame hf (fun r hr => by
      rw [List.mem_singleton.mp hr]
      obtain e : (⟨s.gpr .r3, kOf s⟩ : Region) = outR s := by simp only [outR, kOf, hp.hok]
      rw [e]; exact hp.dKo.symm.sub_right bs) (by have := hp.k2; unfold kOf; omega_using [])
  rw [hx3]
  cases hres : Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) (kept s i) <;> rw [hres] at hw <;>
    exact ⟨hw.1, hout.trans hw.2⟩

theorem accept_ok {s : State} (hp : RPre s) {M : Mem} (hM : Mm s M) {i : Nat} {u : State} (hI : At s M i u)
    (hf : (kept s i).length = psLen s)
    (hpre : Spec.RsaPkcs1Enc.nonzeroPrefix (psLen s) (randB s) = some (kept s i, i)) :
    WP isa accept u (Fin s) := by
  unfold accept
  refine WP.seq (WP.mono (prep_ok hp hM hI hf) fun w A => WP.seq (WP.mono (call_ok hp A) fun y C => ?_))
  refine WP.mono (accTail_ok hp C) fun x ⟨sv, rd, t0, t1, hr⟩ => ⟨sv, rd, ?_⟩
  obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_accepted hpre
  show (∃ req, _ ∧ _ ∧ _) ∧ _
  unfold Spec.Entropy.Result.Requests
  rw [ho, hu]
  exact ⟨⟨0, t0, t1, rfl⟩, hr⟩

end VG.Proof.RsaPkcs1Enc.PPC64LE.Rnd

end

end

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on PPC64LE: rejecting

With fewer than `psLen` nonzero octets in the tape: `out` zeroed
(`zero_ok`), the octets drawn wiped (`wipe_ok`), and the tape and the status
for the budget (`budget_ok`, `reject_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Rnd

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Random VG.Proof.RsaPkcs1Sig.PPC64LE
open VG.WriteBytes (writeBytes writeBytes_frame)
open VG.Impl.RsaPkcs1Sig.PPC64LE (fillLoop)

/-! ## Rejecting -/

/-- The registers the rejecting path writes. -/
abbrev rjRegs : List Reg := [.r0, .r3, .r4, .r10, .r11, .r12]

/-- On the rejecting path, from `u`: the frame, `r5` and `r30` kept, memory
changed only in the stack, `out` and the tape, and the saves in their
slots. -/
structure Rj (s u : State) (c : Nat) (x : State) : Prop extends Fy s x where
  keep : Keep rjRegs u x
  fr : Frame [kR s, outR s, tapeR s] s.mem x.mem
  sv : Spill.Saved (fb s) s.gpr saved x.mem
  ls : x.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr

theorem r7_bv (s : State) : s.gpr .r7 = BitVec.ofNat 64 (kOf s) := by simp [kOf]

theorem shift_ne {d : Nat} (hd : d < 2 ^ 63) :
    ((BitVec.ofNat 64 d - BitVec.ofNat 64 129) >>> 63 != 0) = decide (d < 129) := by
  rw [ne_zero_iff, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow]
  by_cases h : d < 129 <;> simp only [h, decide_true, decide_false, decide_eq_true_eq, decide_eq_false_iff_not,
    Decidable.not_not] <;> omega_arith

theorem slK (s : State) : Region.Sub (slR s) (kR s) := frame_sub s (by decide)

/-- `out` zeroed. -/
theorem zero_ok {s : State} (hp : RPre s) {M : Mem} (hM : Mm s M) {i : Nat} {u : State} (hI : At s M i u) :
    WP isa (.seq (.block zeroArgs) fillLoop) u fun x => Rj s u (kept s i).length x ∧
      x.mem = writeBytes u.mem (s.gpr .r3) (List.replicate (kOf s) 0) ∧ x.gpr .r0 = 0 ∧
      x.gpr .r10 = BitVec.ofNat 64 i := by
  have hk := hp.k1
  have hk2 := hp.k2
  have wO := hp.wO
  have hok := hp.hok
  obtain hMu : Mm s u.mem := by rw [hI.mem]; exact hM.buf _ (by have := hp.ps; have := hI.hc; omega_arith)
  unfold zeroArgs
  refine WP.seq (wp_mov fun z₀ o₀ e₀ => wp_mov fun z₁ o₁ e₁ => wp_mov fun z₂ o₂ e₂ =>
    wp_li (by decide) fun z o₃ e₃ => wp_nil ?_)
  obtain k : Keep [.r10, .r4, .r11, .r0] u z := (o₀.keep.trans (o₁.keep.trans (o₂.keep.trans o₃.keep))).mono
  refine WP.mono (fill_ok (n := kOf s) (p := s.gpr .r3) (b := 0) (by unfold kOf; omega_using [hk]) (by unfold kOf; omega_using [])
    (by rw [o₃.get .r4, o₂.get .r4, e₁, o₀.get .r31, hI.r31])
    (by rw [o₃.get .r11, e₂, o₁.get .r29, o₀.get .r29, hI.r29, r7_bv])
    (by rw [e₃]; rfl) fun j hj => ?_) fun x ⟨kx, mx⟩ => ?_
  · rw [k.wr, hI.wr, hp.hwr]
    exact ⟨outR s, by simp, Offset.contains_base _ (by unfold kOf at hj; omega_using [hok, hj]) (by unfold kOf at hj; omega_using [hj])⟩
  · have K : Keep rjRegs u x := (k.trans kx).mono
    obtain zm : z.mem = u.mem := by rw [o₃.mem, o₂.mem, o₁.mem, o₀.mem]
    obtain hf : Frame [outR s] u.mem x.mem := by
      rw [mx, zm]
      exact writeBytes_frame _ _ _ (by
        rw [List.length_replicate]; exact Region.contains_self' (by unfold kOf; omega_using [hok]))
    refine ⟨⟨hI.toFx.fy.keep K, K, (hMu.fr.mono (by simp)).trans (hf.mono (by simp)),
      hMu.sv.frame hf fun p hp' r hr => by
        rw [List.mem_singleton.mp hr]; exact (hp.dKo.sub_left (slK s)).sub_left (slot_sub s hp'),
      by rw [hf.readW (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact (hp.dKo.sub_left (slK s)).sub_left (lr_sub s)) (by decide)]
         exact hMu.ls⟩, by rw [mx, zm], by rw [kx.get .r0, e₃]; rfl,
      by rw [kx.get .r10, o₃.get .r10, o₂.get .r10, o₁.get .r10, e₀, hI.r4]⟩

/-- The octets drawn wiped. -/
theorem wipe_ok {s : State} {u v : State} {c : Nat} (hc : c ≤ 1021) (R : Rj s u c v)
    (h5 : v.gpr .r5 = BitVec.ofNat 64 c) (h0 : v.gpr .r0 = 0) :
    WP isa (.seq (.block wipeArgs) (.ite (.nonzero .d .r11) fillLoop (.block []))) v fun x =>
      Rj s u c x ∧ Frame [⟨pb s, c⟩] v.mem x.mem ∧ x.gpr .r10 = v.gpr .r10 := by
  unfold wipeArgs
  refine WP.seq (wp_addSp fun z₁ o₁ e₁ => wp_addi fun z₂ o₂ e₂ => wp_mov fun z o₃ e₃ => wp_nil ?_)
  obtain k : Keep [.r12, .r4, .r11] v z := (o₁.keep.trans (o₂.keep.trans o₃.keep)).mono
  obtain zm : z.mem = v.mem := by rw [o₃.mem, o₂.mem, o₁.mem]
  obtain z11 : z.gpr .r11 = BitVec.ofNat 64 c := by rw [e₃, o₂.get .r5, o₁.get .r5, h5]
  obtain Rz : Rj s u c z := ⟨R.toFy.keep k, (R.keep.trans k).mono, zm ▸ R.fr, zm ▸ R.sv, zm ▸ R.ls⟩
  obtain ev : isa.eval (.nonzero .d .r11) z = some (decide (c ≠ 0)) := by
    rw [eval_nonzero, z11, ne_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hc])]
  by_cases h : c = 0
  · refine WP.ite false (by rw [ev, decide_eq_false (by omega_using [h])]) (fun h => absurd h (by decide))
      fun _ => wp_nil ⟨Rz, by rw [zm]; exact Frame.refl _ _, k.get .r10⟩
  · refine WP.ite true (by rw [ev, decide_eq_true h]) (fun _ => ?_) (fun h => absurd h (by decide))
    obtain zw : z.wr = fr s :: s.wr := k.wr.trans R.wr
    refine WP.mono (fill_ok (n := c) (p := pb s) (b := 0) (by omega_using [h]) (by omega_using [hc])
      (by rw [o₃.get .r4, e₂, e₁, BitVec.add_zero, R.sp]) z11 (by rw [k.get .r0, h0]; rfl)
      (in_ps s z zw (by omega_using [hc]))) fun x ⟨kx, mx⟩ => ?_
    obtain hf : Frame [⟨pb s, c⟩] z.mem x.mem := by rw [mx]; exact wipe_frame s _ _
    obtain slD : (slR s).Disjoint ⟨pb s, c⟩ := slR_buf s (by omega_using [hc])
    refine ⟨⟨Rz.toFy.keep kx, (Rz.keep.trans kx).mono,
      Rz.fr.trans (hf.sub fun r hr => by
        rw [List.mem_singleton.mp hr]; exact ⟨kR s, by simp, buf_sub s (by omega_using [hc])⟩),
      Rz.sv.frame hf fun p hp' r hr => by rw [List.mem_singleton.mp hr]; exact slD.sub_left (slot_sub s hp'),
      by rw [hf.readW (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact slD.sub_left (lr_sub s)) (by decide)]; exact Rz.ls⟩, by rw [← zm]; exact hf,
      by rw [kx.get .r10, k.get .r10]⟩

theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q := by
  obtain ⟨t, s', he, hq⟩ := h
  cases he with
  | seq h12 h3 => cases h12 with
    | seq h1 h2 => exact ⟨_, _, .seq h1 (.seq h2 h3), hq⟩

/-- The tape and the status for the budget. -/
theorem budget_ok {s u v : State} (hp : RPre s) {c : Nat} (hc : c < psLen s) (hcl : c ≤ rl s) (R : Rj s u c v)
    (h5 : v.gpr .r5 = BitVec.ofNat 64 c) (h30 : v.gpr .r30 = s.gpr .r5) (h10 : v.gpr .r10 = BitVec.ofNat 64 (rl s)) :
    WP isa (.seq (.block budget) (.ite (.zero .d .r0) (.block exhausted) request)) v fun x =>
      Rj s u c x ∧ Frame [tapeR s] v.mem x.mem ∧
      (Spec.RsaPkcs1Enc.padEntropy (psLen s) ≤ rl s → x.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 (rl s) ∧
        x.mem.readW (s.gpr .r5 + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 0 ∧ (x.gpr .r3).setWidth 32 = 3) ∧
      (rl s < Spec.RsaPkcs1Enc.padEntropy (psLen s) → ∃ req, x.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 0 ∧
        x.mem.readW (s.gpr .r5 + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 req ∧ rl s < req ∧
        req ≤ Spec.RsaPkcs1Enc.padEntropy (psLen s) ∧ (x.gpr .r3).setWidth 32 = 0) := by
  have hP := hp.ps
  have hrl := hp.rl
  have hcap : Spec.RsaPkcs1Enc.padEntropy (psLen s) = psLen s + 128 := rfl
  unfold budget
  refine WP.seq (wp_addi fun v₃ o₃ e₃ => wp_sub fun w o₄ e₄ => wp_nil ?_)
  have kw : Keep [.r12, .r0] v w := (o₃.keep.trans o₄.keep).mono
  have wm : w.mem = v.mem := by rw [o₄.mem, o₃.mem]
  have w11 : w.gpr .r10 = BitVec.ofNat 64 (rl s) := by rw [kw.get .r10, h10]
  have w12 : w.gpr .r12 = BitVec.ofNat 64 (psLen s + 128) := by
    rw [o₄.get .r12, e₃, R.r28, BitVec.ofNat_add_ofNat]
  have w0 : w.gpr .r0 = BitVec.ofNat 64 (psLen s + 128) - BitVec.ofNat 64 (rl s) := by
    rw [e₄, e₃, o₃.get .r10, R.r28, BitVec.ofNat_add_ofNat, h10]
  have w30 : w.gpr .r30 = s.gpr .r5 := by rw [kw.get .r30, h30]
  have w5 : w.gpr .r5 = BitVec.ofNat 64 c := by rw [kw.get .r5, h5]
  have Rw : Rj s u c w := ⟨R.toFy.keep kw, (R.keep.trans kw).mono, wm ▸ R.fr, wm ▸ R.sv, wm ▸ R.ls⟩
  have ev : isa.eval (.zero .d .r0) w = some (decide (psLen s + 128 = rl s)) := by
    rw [eval_zero, w0, sub_beq (by omega_using [hP]) (by have := rl_lt s; omega_using [this])]
  have ww : w.wr = fr s :: s.wr := Rw.wr
  have T0 := in_tape hp w ww (tape_c0 s)
  have T1 := in_tape hp w ww (tape_c8 s)
  -- the tape's writes keep `Rj`
  have key : ∀ r ∈ [Reg.r0, .r3, .r4], r ∉ Reg.r28 :: hiRegs := by decide
  have key' : ∀ r ∈ [Reg.r0, .r3, .r4], r ∈ rjRegs := by decide
  have tapeRj : ∀ {x : State} {rs : List Reg}, Keep rs w x → (∀ r ∈ rs, r ∈ [Reg.r0, .r3, .r4]) →
      Frame [tapeR s] w.mem x.mem → Rj s u c x ∧ Frame [tapeR s] v.mem x.mem := fun kx hrs hf =>
    have slD : (slR s).Disjoint (tapeR s) := hp.dKt.sub_left (slK s)
    ⟨⟨Rw.toFy.keep kx (fun r hr => key r (hrs r hr)), (Rw.keep.trans kx).mono (fun r hr => by
        simp only [List.mem_append] at hr; rcases hr with h | h; exact h; exact key' r (hrs r h)),
      Rw.fr.trans (hf.mono (by simp)),
      Rw.sv.frame hf fun p hp' r hr => by rw [List.mem_singleton.mp hr]; exact slD.sub_left (slot_sub s hp'),
      by rw [hf.readW (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact slD.sub_left (lr_sub s)) (by decide)]; exact Rw.ls⟩,
      wm ▸ hf⟩
  have tf : ∀ (m : Mem) (a b : BitVec 64), Frame [tapeR s] m ((m.writeW (s.gpr .r5) a).writeW
      (s.gpr .r5 + BitVec.ofNat 64 8) b) := fun m a b =>
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (tape_c0 s)).writeW (List.mem_singleton_self _) _
      (tape_c8 s)
  by_cases hex : psLen s + 128 = rl s
  · refine WP.ite true (by rw [ev, decide_eq_true hex]) (fun _ => ?_) (fun h => absurd h (by decide))
    unfold exhausted
    refine wp_std (a := s.gpr .r5) (by rw [w30, BitVec.add_zero]) T0 fun x₁ m₁ => wp_li (by decide)
      fun x₂ o₂' e₂' => wp_std (a := s.gpr .r5 + BitVec.ofNat 64 8) (by rw [o₂'.get .r30, m₁.gpr, w30])
      (by rw [o₂'.wr, m₁.wr]; exact T1) fun x₃ m₃ => wp_li (by decide) fun x o₄' e₄' => wp_nil ?_
    have kx : Keep [.r0, .r3] w x := (m₁.keep.trans (o₂'.keep.trans (m₃.keep.trans o₄'.keep))).mono
    have xm : x.mem = (w.mem.writeW (s.gpr .r5) (BitVec.ofNat 64 (rl s))).writeW (s.gpr .r5 + BitVec.ofNat 64 8)
        (BitVec.ofNat 64 0) := by
      rw [o₄'.mem, m₃.mem, e₂', o₂'.mem, m₁.mem, w11]
    obtain ⟨Rx, fx⟩ := tapeRj kx (by decide) (by rw [xm]; exact tf _ _ _)
    refine ⟨Rx, fx, fun _ => ⟨by rw [xm, rd_t80, Mem.readW_writeW_self64], by rw [xm, Mem.readW_writeW_self64],
      by rw [e₄']; rfl⟩, fun h => absurd h (by rw [hcap]; omega_using [hex])⟩
  · refine WP.ite false (by rw [ev, decide_eq_false hex]) (fun h => absurd h (by decide)) fun _ => ?_
    have hlt : rl s < psLen s + 128 := by omega_using [hrl, hex]
    unfold request reqHead
    refine WP.seq (wp_li (by decide) fun x₁ o₁' e₁' => wp_std (a := s.gpr .r5) (by rw [o₁'.get .r30, w30,
      BitVec.add_zero]) (by rw [o₁'.wr]; exact T0) fun x₂ m₂ => wp_sub fun x₃ o₃' e₃' => wp_subi
      fun x₄ o₄' e₄' => wp_lsr fun y o₅' e₅' => wp_nil ?_)
    have ky : Keep [.r0, .r4] w y := (o₁'.keep.trans (m₂.keep.trans (o₃'.keep.trans (o₄'.keep.trans o₅'.keep)))).mono
    have ym : y.mem = w.mem.writeW (s.gpr .r5) (BitVec.ofNat 64 0) := by
      rw [o₅'.mem, o₄'.mem, o₃'.mem, m₂.mem, e₁', o₁'.mem]
    have hd : rl s - c < 2 ^ 63 := by omega_using [hP, hrl]
    have y4 : y.gpr .r4 = (BitVec.ofNat 64 (rl s - c) - BitVec.ofNat 64 129) >>> 63 := by
      rw [e₅', e₄', e₃', m₂.gpr, o₁'.get .r10, o₁'.get .r5, w11, w5, sub_ofNat hcl (rl_lt s)]
    have ev' : isa.eval (.nonzero .d .r4) y = some (decide (rl s - c < 129)) := by
      rw [eval_nonzero, y4, shift_ne hd]
    have tail : ∀ (z : State) (req : Nat), Keep [.r0] y z → z.mem = y.mem → z.gpr .r0 = BitVec.ofNat 64 req →
        rl s < req → req ≤ psLen s + 128 →
        WP isa (.block [.store .d .r0 .r30 8, .li .r3 0]) z fun x =>
          Rj s u c x ∧ Frame [tapeR s] v.mem x.mem ∧
          (Spec.RsaPkcs1Enc.padEntropy (psLen s) ≤ rl s → x.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 (rl s) ∧
            x.mem.readW (s.gpr .r5 + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 0 ∧ (x.gpr .r3).setWidth 32 = 3) ∧
          (rl s < Spec.RsaPkcs1Enc.padEntropy (psLen s) → ∃ req, x.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 0 ∧
            x.mem.readW (s.gpr .r5 + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 req ∧ rl s < req ∧
            req ≤ Spec.RsaPkcs1Enc.padEntropy (psLen s) ∧ (x.gpr .r3).setWidth 32 = 0) := by
      intro z req kz zm z0 h1 h2
      refine wp_std (a := s.gpr .r5 + BitVec.ofNat 64 8) (by rw [kz.get .r30, ky.get .r30, w30])
        (by rw [kz.wr, ky.wr]; exact T1) fun x₁ m₁ => wp_li (by decide) fun x o₂ e₂ => wp_nil ?_
      have kx : Keep [.r0, .r3, .r4] w x := ((ky.trans kz).trans (m₁.keep.trans o₂.keep)).mono
      have xm : x.mem = (w.mem.writeW (s.gpr .r5) (BitVec.ofNat 64 0)).writeW (s.gpr .r5 + BitVec.ofNat 64 8)
          (BitVec.ofNat 64 req) := by rw [o₂.mem, m₁.mem, z0, zm, ym]
      obtain ⟨Rx, fx⟩ := tapeRj kx (by decide) (by rw [xm]; exact tf _ _ _)
      exact ⟨Rx, fx, fun h => absurd h (by rw [hcap]; omega_using [hrl, hex]), fun _ => ⟨req,
        by rw [xm, rd_t80, Mem.readW_writeW_self64], by rw [xm, Mem.readW_writeW_self64], h1, h2,
        by rw [e₂]; rfl⟩⟩
    by_cases hs : rl s - c < 129
    · refine WP.seq (WP.ite true (by rw [ev', decide_eq_true hs]) (fun _ => wp_add fun z₁ o₁'' e₁'' =>
        wp_sub fun z o₂'' e₂'' => wp_nil ?_) (fun h => absurd h (by decide)))
      refine tail z (psLen s + rl s - c) (o₁''.keep.trans o₂''.keep).mono (by rw [o₂''.mem, o₁''.mem]) ?_
        (by omega_using [hc]) (by omega_using [hs])
      rw [e₂'', o₁''.get .r5, e₁'', ky.get .r28, ky.get .r10, ky.get .r5, Rw.r28, w11, w5,
        BitVec.ofNat_add_ofNat, sub_ofNat (by omega_using [hc]) (by omega_using [hP, hrl])]
    · refine WP.seq (WP.ite false (by rw [ev', decide_eq_false hs]) (fun h => absurd h (by decide))
        fun _ => wp_mov fun z o₁'' e₁'' => wp_nil ?_)
      exact tail z (psLen s + 128) o₁''.keep (by rw [o₁''.mem]) (by rw [e₁'', ky.get .r12, w12]) hlt (by omega_using [])

theorem reject_ok {s : State} (hp : RPre s) {M : Mem} (hM : Mm s M) {u : State} (hI : At s M (rl s) u)
    (hc : (kept s (rl s)).length < psLen s) : WP isa reject u (Fin s) := by
  have hP := hp.ps
  have hk2 := hp.k2
  have hcl := hI.hc
  obtain hcr : (kept s (rl s)).length ≤ rl s := by
    have := VG.Proof.RsaPkcs1Enc.nz_length_le ((randB s).take (rl s))
    simp only [List.length_take, randB_length] at this; simp only [kept]; omega_using [this]
  unfold reject
  refine seq_assoc (WP.seq (WP.mono (zero_ok hp hM hI) fun v ⟨R, hm, h0, h10⟩ => ?_))
  obtain h5 : v.gpr .r5 = BitVec.ofNat 64 (kept s (rl s)).length := by rw [R.keep.get .r5, hI.r5]
  refine seq_assoc (WP.seq (WP.mono (wipe_ok (by omega_using [hc, hP]) R h5 h0) fun w ⟨R', hf', h10'⟩ => ?_))
  refine WP.mono (budget_ok hp hc hcr R' (by rw [R'.keep.get .r5, hI.r5]) (by rw [R'.keep.get .r30, hI.r30])
    (by rw [h10', h10]))
    fun x ⟨Rx, fx, hex, hen⟩ => ⟨⟨Rx.sp, Rx.wr, Rx.hi, Rx.sv, Rx.ls⟩, Rx.rd, ?_⟩
  -- `out`
  obtain bs := buf_sub s (n := (kept s (rl s)).length) (by omega_using [hc, hP])
  obtain outZ : Spec.Rsa.bytesAt x.mem (s.gpr .r3) (kOf s) = List.replicate (kOf s) 0 := by
    obtain e : (⟨s.gpr .r3, kOf s⟩ : Region) = outR s := by simp only [outR, kOf, hp.hok]
    rw [bytes_frame fx (fun r hr => by rw [List.mem_singleton.mp hr, e]; exact hp.dOt) (by unfold kOf; omega_using []),
      bytes_frame hf' (fun r hr => by rw [List.mem_singleton.mp hr, e]; exact hp.dKo.symm.sub_right bs)
        (by unfold kOf; omega_using []), hm]
    have := bytesAt_writeBytes u.mem (s.gpr .r3) (List.replicate (kOf s) 0) (by simp; unfold kOf; omega_using [])
    rwa [List.length_replicate] at this
  obtain hnz : (VG.Proof.RsaPkcs1Enc.nz (randB s)).length < psLen s := by rw [← kept_all]; exact hc
  show (∃ req, _ ∧ _ ∧ _) ∧ _
  unfold Spec.Entropy.Result.Requests
  by_cases hge : Spec.RsaPkcs1Enc.padEntropy (psLen s) ≤ rl s
  · obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_exhausted hnz (by rw [randB_length]; exact hge)
    obtain ⟨h0, h1, hr⟩ := hex hge
    rw [ho, hu, randB_length]
    exact ⟨⟨0, h0, h1, rfl⟩, hr, outZ⟩
  · obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_entropy hnz (by rw [randB_length]; omega_using [hge])
    obtain ⟨req, h0, h1, hr1, hr2, hr⟩ := hen (by omega_using [hge])
    rw [ho, hu]
    exact ⟨⟨req, h0, h1, by rw [randB_length]; exact ⟨hr1, hr2⟩⟩, hr, outZ⟩

end VG.Proof.RsaPkcs1Enc.PPC64LE.Rnd
