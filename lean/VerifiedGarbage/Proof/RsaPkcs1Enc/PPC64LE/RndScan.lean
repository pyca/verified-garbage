module

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
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

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
  exact ⟨sp1, by omega, hrd, hwr, dOt, dOn, dOe, dOm, dOr, dOs, dOq, dOa, dTn, dTe, dTm, dTr, dTs, dTq, dTa,
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
  have := hp.hml; have := hp.k2; unfold psLen kOf; omega

theorem RPre.randLen {s : State} (hp : RPre s) : (stackArg s 2).toNat ≤ psLen s + 128 := hp.hrl

/-! ## The frame -/

/-- The frame's base: the stack pointer in the frame. -/
abbrev fb (s : State) : Addr := s.sp - BitVec.ofNat 64 frameBytes

/-- The frame's local variable space, which its push makes writable. -/
abbrev fr (s : State) : Region := ⟨fb s + BitVec.ofNat 64 32, frameBytes - 32⟩

/-- The base of the stack the function uses. -/
abbrev kb (s : State) : Addr := s.sp - BitVec.ofNat 64 rndStack

theorem frameR_eq (s : State) : frameR frameBytes s = fr s := rfl

theorem fb_eq (s : State) : fb s = kb s + BitVec.ofNat 64 Impl.RsaPkcs1Sig.PPC64LE.frameBytes := by
  simp only [fb, kb, rndStack]
  rw [BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem kb_toNat {s : State} (hp : RPre s) : (kb s).toNat + rndStack = s.sp.toNat ∧
    s.sp.toNat + 152 ≤ 2 ^ 64 := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold rndStack at *; omega

theorem fb_toNat {s : State} (hp : RPre s) : (fb s).toNat + frameBytes = s.sp.toNat ∧
    Impl.RsaPkcs1Sig.PPC64LE.frameBytes ≤ (fb s).toNat := by
  have := hp.sp1
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold rndStack frameBytes at *; omega

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
  exact Offset.contains_base _ (by unfold rndStack Impl.RsaPkcs1Sig.PPC64LE.frameBytes frameBytes at *; omega)
    (by unfold Impl.RsaPkcs1Sig.PPC64LE.frameBytes frameBytes at *; omega)

/-- The local variable space is writable. -/
theorem in_fr (s : State) (rs : List Region) {d n : Nat} (h₁ : 32 ≤ d) (h : d + n ≤ frameBytes) :
    InRegions (fr s :: rs) (fb s + BitVec.ofNat 64 d) n :=
  ⟨_, List.mem_cons_self .., Offset.contains _ h₁ (by unfold frameBytes at *; omega)
    (by unfold frameBytes; omega)⟩

theorem in_fr' (s : State) (rd rs : List Region) {d n : Nat} (h₁ : 32 ≤ d) (h : d + n ≤ frameBytes) :
    InRegions (rd ++ fr s :: rs) (fb s + BitVec.ofNat 64 d) n := by
  obtain ⟨r, hr, hc⟩ := in_fr s rs h₁ h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- Our stack arguments, from the frame. -/
theorem stackArgAddr_fb (s : State) (j : Nat) :
    stackArgAddr s j = fb s + BitVec.ofNat 64 (arg j) := by
  have e : BitVec.ofNat 64 (arg j) = BitVec.ofNat 64 frameBytes + BitVec.ofNat 64 (32 + 8 * (8 + j)) := by
    rw [BitVec.ofNat_add_ofNat]; unfold arg; congr 1; omega
  rw [stackArgAddr, e, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem stackArgAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, Nat.add_zero]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, show 32 + 8 * 8 + 8 * j = 32 + 8 * (8 + j) by omega]

theorem in_argsR {s : State} {j : Nat} (hj : j < 7) : (argsR s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)

/-- A stack argument is readable. -/
theorem arg_in {s : State} (hp : RPre s) (wr : List Region) {j : Nat} (hj : j < 7) :
    InRegions (s.rd ++ wr) (stackArgAddr s j) 8 := by
  rw [hp.hrd]; exact ⟨argsR s, by simp, in_argsR hj⟩

/-! ## The saves -/

/-- The callee-saved registers other than `r28`–`r31`. -/
def hiRegs : List Reg := [.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26,
  .r27]

/-- The callee-saved registers. -/
def keptRegs : List Reg := [.r28, .r29, .r30, .r31] ++ hiRegs

theorem not_kept {rs : List Reg} {r : Reg} (hrs : ∀ r ∈ rs, r ∉ keptRegs) (hr : r ∈ keptRegs) : r ∉ rs :=
  fun h => hrs r h hr

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

/-- The saves are kept by code writing registers other than the callee-saved
ones and memory apart from the slots. -/
theorem Saves.keep {s t w : State} {rs : List Reg} (h : Saves s t) (o : Keep rs t w) {R : List Region}
    (hm : Frame R t.mem w.mem)
    (hR : ∀ r ∈ R, (fR s).Disjoint r) (hrs : ∀ r ∈ rs, r ∉ keptRegs := by decide) : Saves s w where
  sp := o.sp.trans h.sp
  wr := o.wr.trans h.wr
  hi := fun r hr => (o.gpr _ (not_kept hrs (List.mem_append_right _ hr))).trans (h.hi r hr)
  sv := h.sv.frame hm fun p hp r hr => (hR r hr).sub_left (frame_sub0 s (by
    have := saved_offs p hp; unfold oSave frameBytes at *; omega))
  ls := by rw [hm.readW (Region.contains_self _ _) (fun r hr => (hR r hr).sub_left (frame_sub0 s (by decide)))
    (by decide)]; exact h.ls

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
    rw [e₁, o₁.wr, hwr]; exact in_fr s _ (by unfold oSave at this; omega) (by unfold oSave frameBytes at *; omega)
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
      have := saved_offs p hp; unfold oSave frameBytes at *; omega) (by decide) _ _ _) fun r hr => ?_)
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
    exact Offset.disjoint _ (.inl (by unfold oSave oLr at *; omega)) (by unfold oSave at *; omega) (by decide)
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
    rw [o₁.wr, hm.wr]; exact in_fr' s _ _ (by unfold oSave at h₁; omega) (by unfold oLr frameBytes at *; omega)
  refine wp_ld (a := fb s + BitVec.ofNat 64 oLr) (by rw [e₁]) (hin (by decide) (by decide)) fun w₂ o₂ e₂ =>
    wp_mtlr fun w₃ g₃ m₃ rd₃ wr₃ sp₃ lr₃ => ?_
  refine WP.mono (Spill.restore_wp (b := .r12) (l := saved) (B := fb s) (g := s.gpr) (by decide)
    (by rw [g₃, o₂.get .r12, e₁]) saved_ho (by decide)
    (fun p hp => by
      have := saved_offs p hp
      rw [rd₃, wr₃, o₂.rd, o₂.wr]; exact hin this.1 (by unfold oSave oLr at *; omega))
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
  Offset.sub (fb s) (saved_offs p hp).1 (by have := saved_offs p hp; omega)

theorem lr_sub (s : State) : Region.Sub ⟨fb s + BitVec.ofNat 64 oLr, 8⟩ (slR s) :=
  Offset.sub (fb s) (by decide) (by decide)

theorem Mm.frame {s : State} {m m' : Mem} (h : Mm s m) {R : List Region} (hf : Frame R m m')
    (hk : ∀ r ∈ R, Region.Sub r (kR s)) (hd : ∀ r ∈ R, (slR s).Disjoint r) : Mm s m' :=
  ⟨h.fr.trans (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, hk r hr⟩),
    h.sv.frame hf fun p hp r hr => (hd r hr).sub_left (slot_sub s hp),
    by rw [hf.readW (Region.contains_self _ _) (fun r hr => (hd r hr).sub_left (lr_sub s)) (by decide)]; exact h.ls⟩

theorem buf_sub (s : State) {n : Nat} (h : n ≤ 1024) : Region.Sub ⟨pb s, n⟩ (kR s) :=
  frame_sub s (d := oBuf) (by unfold oBuf frameBytes; omega)

theorem slR_buf (s : State) {n : Nat} (h : n ≤ 1024) : (slR s).Disjoint ⟨pb s, n⟩ :=
  Offset.disjoint _ (.inl (by decide)) (by decide) (by unfold oBuf; omega)

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

theorem Fx.saves {s u : State} (h : Fx s u) (hm : Mm s u.mem) : Saves s u :=
  ⟨h.sp, h.wr, h.hi, hm.sv, hm.ls⟩

/-! ## Values -/

theorem psLen_bv {s : State} (hp : RPre s) :
    s.gpr .r7 - stackArg s 0 - BitVec.ofNat 64 3 = BitVec.ofNat 64 (psLen s) := by
  have := hp.hml
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, psLen, kOf]
  have h1 := (s.gpr .r7).isLt
  have h2 := (stackArg s 0).isLt
  omega

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
    simp only [h, decide_false, Bool.not_false, decide_eq_true_eq]; omega

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
    intro hz; rw [kept_succ hi, ite_eq_left hz] at hf; omega
  have hk : kept s (i + 1) = kept s i ++ [(randB s).getD i 0] := by rw [kept_succ hi, ite_eq_right hz]
  have hl : i < (randB s).length := by rw [randB_length]; exact hi
  have e : randB s = (randB s).take i ++ (randB s).getD i 0 :: (randB s).drop (i + 1) := by
    conv => lhs; rw [← List.take_append_drop i (randB s)]
    congr 1
    rw [List.drop_eq_getElem_cons hl]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  have hlen : ((randB s).take i).length = i := by rw [List.length_take]; omega
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
    (kept s i).length ≤ 1021 := by have := hp.ps; have := h.hc; omega

/-- A byte of the tape, read from memory in the scan. -/
theorem tape_byte {s : State} (hp : RPre s) {M : Mem} (hM : Mm s M) {i : Nat} (hi : i < rl s) (xs : List Byte)
    (hx : xs.length ≤ 1024) :
    writeBytes M (pb s) xs (stackArg s 1 + BitVec.ofNat 64 i) = (randB s).getD i 0 := by
  have hwR : (stackArg s 1).toNat + rl s ≤ 2 ^ 64 := hp.wR
  rw [randB_getD hi]
  exact ((writeBytes_frame M (pb s) xs (Region.contains_self _ _)).bytes (R := randR s)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.dKr.symm.sub_right (buf_sub s hx))
    (by show rl s ≤ 2 ^ 64; omega) hi).trans (hM.bytes hp.dKr.symm (by show rl s ≤ 2 ^ 64; omega) hi)

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
    exact ⟨randR s, by simp, Offset.contains_base _ (show i + 1 ≤ rl s by omega) (by omega)⟩
  · refine ⟨u, hI, (o₁.trans (o₂.trans o₃)).mono, ?_, ?_⟩
    · rw [o₃.get .r0, e₂, o₁.mem, hI.mem, tape_byte hp hM hi _ (by omega)]
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
      by omega, by rw [hks]; omega⟩
  · have hks : kept s (i + 1) = kept s i ++ [(randB s).getD i 0] := by rw [kept_succ hi, ite_eq_right hz]
    have hl : (kept s (i + 1)).length = (kept s i).length + 1 := by rw [hks]; simp
    refine WP.ite true (by rw [ev, decide_eq_false hz]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    have v7 : v.gpr .r7 = pb s := (g _ (by decide)).trans hI.r7
    have v5 : v.gpr .r5 = BitVec.ofNat 64 (kept s i).length := (g _ (by decide)).trans hI.r5
    unfold keep
    refine wp_add fun v₁ o₁ e₁ => wp_stb (a := pb s + BitVec.ofNat 64 (kept s i).length)
      (by rw [e₁, v7, v5, BitVec.add_zero]) ?_ fun v₂ m₂ => wp_addi fun v₃ o₃ e₃ => wp_nil ?_
    · rw [o₁.wr, o.wr, hI.wr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact in_fr s _ (by unfold oBuf; omega) (by unfold oBuf frameBytes; omega)
    · have k := (o₁.keep.trans (m₂.keep.trans o₃.keep)).mono (rs' := [.r12, .r5])
      have g' : ∀ r, r ∉ [Reg.r12, .r5] → v₃.gpr r = v.gpr r := fun r hr => k.gpr r hr
      refine ⟨(hI.toFx.keep o.keep).keep k, ?_, (g' _ (by decide)).trans ((g _ (by decide)).trans hI.r3),
        (g' _ (by decide)).trans h4, ?_, (g' _ (by decide)).trans v7,
        (g' _ (by decide)).trans ((g _ (by decide)).trans hI.r11), by omega, by omega⟩
      · rw [o₃.mem, m₂.mem, o₁.mem, o₁.get .r0, h0, byte_trunc, o.mem, hI.mem, hks,
          writeBytes_snoc _ _ _ _ (by omega)]
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
    rw [eval_nonzero, e₁, hI.r28, hI.r5, sub_ne (by omega) (by omega)]
  by_cases hf : (kept s (i + 1)).length = psLen s
  · refine WP.ite false (by rw [ev, decide_eq_true hf.symm]; rfl) (fun h => absurd h (by decide))
      fun _ => wp_nil ⟨hw, ?_⟩
    rw [e₁, hI.r28, hI.r5, hf, sub_ne (by omega) (by omega)]; simp
  · refine WP.ite true (by rw [ev, decide_eq_false (Ne.symm hf)]; rfl) (fun _ => wp_sub fun x o₂ e₂ =>
      wp_nil ⟨hw.only o₂, ?_⟩) (fun h => absurd h (by decide))
    rw [e₂, o₁.get .r11, o₁.get .r4, hI.r11, hI.r4, rl_bv, sub_ne (by omega) (by omega)]
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
    exact ⟨0, h0, .inr ⟨hl'.symm, by rw [kept_zero]; simp; omega⟩⟩
  have hl' : 0 < rl s := by
    rcases Nat.eq_zero_or_pos (rl s) with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa [rl] using h)) hl
    · exact h
  refine WP.ite true (by rw [ev, show (stackArg s 2 != 0) = true from bne_iff_ne.mpr hl])
    (fun _ => ?_) (fun h => absurd h (by decide))
  refine WP.loop (M := isa) (LoopInv s M) ?_ (rl s - 0) t ⟨0, rfl, h0, hl', by rw [kept_zero]; simp; omega⟩
  rintro n u ⟨i, rfl, hI, hi, hc⟩
  refine WP.mono (step_ok hp hM hI hi hc) fun x ⟨hI', hz⟩ => ?_
  have ev' : isa.eval (.nonzero .d .r12) x = some (!decide ((kept s (i + 1)).length = psLen s ∨ i + 1 = rl s)) := by
    rw [eval_nonzero, hz]
  by_cases hstop : (kept s (i + 1)).length = psLen s ∨ i + 1 = rl s
  · refine .inl ⟨by rw [ev', decide_eq_true hstop]; rfl, ⟨i + 1, hI', ?_⟩⟩
    by_cases hf : (kept s (i + 1)).length = psLen s
    · exact .inl ⟨hf, prefix_of_fill hi hc hf⟩
    · exact .inr ⟨hstop.resolve_left hf, by have := hI'.hc; omega⟩
  · refine .inr ⟨by rw [ev', decide_eq_false hstop]; rfl, _, by omega, i + 1, rfl, hI', by omega,
      by have := hI'.hc; omega⟩

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
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega))) (by decide)

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
  rw [hwr, pb_add]; exact in_fr s _ (by unfold oBuf; omega) (by unfold oBuf frameBytes; omega)

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
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show a - b < 2 ^ 64 by omega)]
  omega

/-- Whether `PS` is full, after the scan. -/
theorem full_ok {s : State} (hp : RPre s) {M : Mem} {i : Nat} {u : State} (hI : At s M i u) :
    WP isa (.block [.sub .r12 .r28 .r5]) u fun v => At s M i v ∧
      isa.eval (.zero .d .r12) v = some (decide (psLen s = (kept s i).length)) := by
  have hk := kept_le hp hI
  have hP := hp.ps
  refine wp_sub fun v o e => wp_nil ⟨hI.only o, ?_⟩
  rw [eval_zero, e, hI.r28, hI.r5, sub_beq (by omega) (by omega)]

end VG.Proof.RsaPkcs1Enc.PPC64LE.Rnd
