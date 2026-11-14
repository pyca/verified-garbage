module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivContractGeometry
public import VerifiedGarbage.Proof.Rsa.Arm.PrivFnInput
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.Arm.PrivEntryReady
import VerifiedGarbage.Proof.Rsa.Arm.PrivRegions
import VerifiedGarbage.Proof.Rsa.Arm.PrivFn
import VerifiedGarbage.Proof.Rsa.Arm.PrivFnCT
public import VerifiedGarbage.Proof.Rsa.Arm.PrivBody
import VerifiedGarbage.Proof.Rsa.Arm.PrivBodyCT
import VerifiedGarbage.Proof.Rsa.Arm.PrivCheck
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Bignum.Arm.PrivPreModulus
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.PrivPcCall
public import VerifiedGarbage.Proof.Rsa.Arm.PrivPcArgs
public import VerifiedGarbage.Proof.Rsa.Arm.PrivStages
import VerifiedGarbage.Proof.Rsa.Arm.PrivCheckFrame
import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
import VerifiedGarbage.Proof.Bignum.Arm.CopyBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.PcHead
import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import VerifiedGarbage.Proof.Rsa.Arm.PrivSetupCT
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Rsa.Arm.PrivCrtArgs
import VerifiedGarbage.Proof.Rsa.Arm.PrivCopyArgs
import VerifiedGarbage.Proof.Rsa.Arm.PrivCrtCall
import VerifiedGarbage.Proof.Rsa.Arm.PrivStatusPreserved
public import VerifiedGarbage.Proof.Rsa.Arm.PrivContext
public import VerifiedGarbage.Proof.Rsa.Arm.PrivSlots
public import VerifiedGarbage.Proof.Rsa.Arm.PrivCrtArgs
import VerifiedGarbage.Proof.Rsa.Arm.PrivStackWord
import VerifiedGarbage.Proof.Rsa.Arm.PrivPreWords
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Rsa.Arm.PrivCrtPre
public import VerifiedGarbage.Proof.Rsa.Arm.PrivCrtCall
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Rsa.Arm.PrivCall
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Rsa.CrtPrecomputedContract

/-! # `vg_rsa_private_checked_precomputed` on ARMv7

`vg_rsa_private_checked`'s body, but for the public precomputation, which
it copies from the key's precomputed values `pre` (`pcCopy`): the
contract's `privatePrecompute` fixes their first `2 w` words to what
`vg_rsa_public_precompute` computes. -/

/-! ## The call of `vg_rsa_private_crt_precomputed`

`vg_rsa_private_checked_precomputed` calls it with `vg_rsa_private_crt`'s
arguments and, as its arguments 14 and 15, the rest of `pre` after the
modulus' `2 w` words, the factors' `R²` (`r2Args`). -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_dp wp_str op2_reg op2_lsl dpVal)

/-- The words of the factors' `R²`. -/
def r2Words (g : PrivGeometry) : Nat := Spec.Rsa.primeWords g.pLength + Spec.Rsa.primeWords g.qLength

/-- The incoming `pre_len` (argument 17), and the rest of `pre`, after its
first `2 w` words: the factors' `R²`, of a key whose factors' product is the
modulus. -/
structure R2In (g : PrivGeometry) (bs : Fin 8 → List Byte) (pre preLen : BitVec 32) (s : State) : Prop where
  lenRead : InRegions (s.rd ++ s.wr) (off (State.addr g.stack) (arg 17)) 4
  lenSlot : s.mem.readW (off (State.addr g.stack) (arg 17)) 32 = preLen
  lenSeparate : ∀ r ∈ bodyWrites g, (⟨off (State.addr g.stack) (arg 17), 4⟩ : Region).Disjoint r
  lenFit : g.stack.toNat + arg 17 + 4 ≤ 2 ^ 32
  len : preLen.toNat = 2 * Spec.Rsa.modulusWords g.length + r2Words g
  fit : pre.toNat + 8 * preLen.toNat ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (State.addr pre) (8 * preLen.toNat)
  separate : ∀ r ∈ bodyWrites g, (⟨State.addr pre, 8 * preLen.toNat⟩ : Region).Disjoint r
  words : Spec.Rsa.wordsAt s.mem (State.addr (pre + BitVec.ofNat 32 (16 * Spec.Rsa.modulusWords g.length)))
    (r2Words g) = Spec.Rsa.primeR2 (bs 3) ++ Spec.Rsa.primeR2 (bs 4)
  pq : Spec.Rsa.os2ip (bs 3) * Spec.Rsa.os2ip (bs 4) = Spec.Rsa.os2ip (bs 0)

theorem r2Words_lt {g : PrivGeometry} (h : g.Valid) : r2Words g ≤ 256 := by
  have := h.maxLength; have := h.pFits; have := h.qFits
  simp only [r2Words, Spec.Rsa.primeWords, Spec.Rsa.modulusWords]
  omega_arith

theorem r2Words_lt' {g : PrivGeometry} {bs : Fin 8 → List Byte} {pre preLen : BitVec 32} {s : State}
    (r : R2In g bs pre preLen s) : r2Words g < 2 ^ 32 := by
  have := r.len; have := preLen.isLt; omega_arith

theorem r2Words_pos (g : PrivGeometry) : 4 ≤ r2Words g := by
  simp only [r2Words, Spec.Rsa.primeWords]; omega_using []

/-- The factors' `R²`, as a region. -/
def r2Region (g : PrivGeometry) (pre : BitVec 32) : Region :=
  ⟨State.addr (pre + BitVec.ofNat 32 (16 * Spec.Rsa.modulusWords g.length)), 8 * r2Words g⟩

theorem R2In.r2Sub {g : PrivGeometry} {bs : Fin 8 → List Byte} {pre preLen : BitVec 32} {s : State}
    (r : R2In g bs pre preLen s) : (r2Region g pre).Sub ⟨State.addr pre, 8 * preLen.toNat⟩ := by
  have := r.fit; have := r.len; have := r2Words_pos g
  unfold r2Region
  rw [addr_add (by omega_arith)]
  exact Offset.sub_base _ (by omega_arith)

theorem R2In.r2Fit {g : PrivGeometry} {bs : Fin 8 → List Byte} {pre preLen : BitVec 32} {s : State}
    (r : R2In g bs pre preLen s) :
    (pre + BitVec.ofNat 32 (16 * Spec.Rsa.modulusWords g.length)).toNat + 8 * r2Words g ≤ 2 ^ 32 := by
  have := r.fit; have := r.len; have := r2Words_pos g
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : 16 * Spec.Rsa.modulusWords g.length < 2 ^ 32 := by omega_arith
  rw [Nat.mod_eq_of_lt this]
  omega_arith

theorem r2In_kept (g : PrivGeometry) (bs : Fin 8 → List Byte) (pre preLen : BitVec 32) :
    Kept g (R2In g bs pre preLen) := by
  intro s t rs h frame rest
  have fit : 8 * r2Words g < 2 ^ 64 := by have := r2Words_lt' h; omega_using [this]
  refine ⟨by rw [rest.rd, rest.wr]; exact h.lenRead, ?_, h.lenSeparate, h.lenFit, h.len, h.fit,
    by rw [rest.rd, rest.wr]; exact h.read, h.separate, ?_, h.pq⟩
  · rw [frame.readW (r := ⟨off (State.addr g.stack) (arg 17), 4⟩) (Region.contains_self _ _)
      h.lenSeparate (by decide)]
    exact h.lenSlot
  · rw [wordsAt_frame frame fit (fun r hr => (h.separate r hr).sub_left h.r2Sub)]
    exact h.words

/-- What `r2Args` leaves: the outgoing arguments 14 and 15. -/
def R2Out (g : PrivGeometry) (pre : BitVec 32) (m : Mem) : Prop :=
  m.readW (off (State.addr g.stack) 56) 32 = pre + BitVec.ofNat 32 (16 * Spec.Rsa.modulusWords g.length) ∧
    m.readW (off (State.addr g.stack) 60) 32 = BitVec.ofNat 32 (r2Words g)

theorem r2Args_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} {pre preLen : BitVec 32}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) (ptr : s.gpr .r12 = g.stack)
    (preRead : InRegions (s.rd ++ s.wr) (off (State.addr g.stack) (arg 16)) 4)
    (preSlot : s.mem.readW (off (State.addr g.stack) (arg 16)) 32 = pre)
    (preFit : g.stack.toNat + arg 16 + 8 ≤ 2 ^ 32)
    (r : R2In g bs pre preLen s) :
    WP isa (.block r2Args) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧ R2Out g pre t.mem ∧
      (∀ j < 14, t.mem.readW (off (State.addr g.stack) (4 * j)) 32 = s.mem.readW (off (State.addr g.stack) (4 * j)) 32) ∧
      Frame [⟨State.addr g.stack, 64⟩] s.mem t.mem ∧ Rest [.r0, .r1, .lr] s t := by
  have wfit := h.valid.maxLength
  have rfit := r2Words_lt h.valid
  have fit := h.valid.stackHigh
  have lenFit := r.lenFit
  simp only [arg, frameBytes] at fit lenFit preFit
  unfold r2Args
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_loadStack (a := off (State.addr g.stack) (arg 17)) (by decide)
    (by rw [h.sp]; exact addr_add (by rw [show arg 17 = 3452 from rfl]; omega_using [preFit])) r.lenRead fun u a => WP.block_nil ?_
  have hu : PrivContext g bs u := h.after (by rw [a.mem]; exact Frame.refl _ _) (show Rest [.r0] s u from a.rest (by simp))
  refine WP.mono (preWords_ok .r1 u hu (by rw [a.mem]; exact slots)) ?_
  rintro v ⟨r1V, memV, restV⟩
  refine wp_loadStack (a := off (State.addr g.stack) (arg 16)) (by decide)
    (by rw [restV.sp, a.sp, h.sp]; exact addr_add (by rw [show arg 16 = 3448 from rfl]; omega_using [preFit]))
    (by rw [restV.rd, restV.wr, a.rd, a.wr]; exact preRead) fun x b => ?_
  refine wp_dp (op2_reg _ _) fun y c => ?_
  refine wp_dp (op2_lsl (by decide)) fun z d => ?_
  have r12Z : z.gpr .r12 = g.stack := by
    rw [d.other .r12 (by decide), c.other .r12 (by decide), b.other .r12 (by decide),
      restV.gpr .r12 (by simp), a.other .r12 (by decide), ptr]
  have spZ : z.sp = g.stack := by rw [d.sp, c.sp, b.sp, restV.sp, a.sp, h.sp]
  have wrZ : z.wr = s.wr := by rw [d.wr, c.wr, b.wr, restV.wr, a.wr]
  have memZ : z.mem = s.mem := by rw [d.mem, c.mem, b.mem, memV, a.mem]
  refine wp_str (a := off (State.addr g.stack) 60) (by decide)
    (by rw [r12Z]; exact addr_add (by omega_using [preFit]))
    (by rw [wrZ]; exact h.inner.write (by simp only [frameBytes]; omega_using [])) fun z2 e => ?_
  refine wp_str (a := off (State.addr g.stack) 56) (by decide)
    (by rw [e.gpr, r12Z]; exact addr_add (by omega_using [preFit]))
    (by rw [e.wr, wrZ]; exact h.inner.write (by simp only [frameBytes]; omega_using [])) fun t f => WP.block_nil ?_
  have r0Val : z.gpr .r0 = BitVec.ofNat 32 (r2Words g) := by
    rw [d.other .r0 (by decide), c.gpr, dpVal, b.other .r0 (by decide),
      b.other .r1 (by decide), r1V, restV.gpr .r0 (by simp), a.gpr, r.lenSlot]
    apply BitVec.eq_of_toNat_eq
    have := r.len
    have := preLen.isLt
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_arith
  have lrVal : z.gpr .lr = pre + BitVec.ofNat 32 (16 * Spec.Rsa.modulusWords g.length) := by
    rw [d.gpr, dpVal, c.other .lr (by decide), c.other .r1 (by decide), b.gpr, b.other .r1 (by decide), r1V,
      memV, a.mem, preSlot, BitVec.shiftLeft_eq_mul_twoPow]
    change pre + BitVec.ofNat 32 (2 * Spec.Rsa.modulusWords g.length) * BitVec.ofNat 32 8 = _
    rw [← BitVec.ofNat_mul]
    congr 2
    omega_using []
  have memT : t.mem = (s.mem.writeW (off (State.addr g.stack) 60) (BitVec.ofNat 32 (r2Words g))).writeW
      (off (State.addr g.stack) 56) (pre + BitVec.ofNat 32 (16 * Spec.Rsa.modulusWords g.length)) := by
    rw [f.mem, e.mem, e.gpr, memZ, r0Val, lrVal]
  have frameT : Frame [⟨State.addr g.stack, 64⟩] s.mem t.mem := by
    rw [memT]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide : 60 + 4 ≤ 64) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide : 56 + 4 ≤ 64) (by decide))
  have restT : Rest [.r0, .r1, .lr] s t :=
    (show Rest [.r0] s u from a.rest (by simp)).mono (by simp) |>.trans
      ((restV.mono (by simp)).trans ((show Rest [.lr] v x from b.rest (by simp)).mono (by simp) |>.trans
        ((show Rest [.r0] x y from c.rest (by simp)).mono (by simp) |>.trans
        ((show Rest [.lr] y z from d.rest (by simp)).mono (by simp) |>.trans
        ((e.rest _).trans (f.rest _))))))
  have frameB : Frame (bodyWrites g) s.mem t.mem := frameT.sub (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨g.innerRegion, by simp [bodyWrites], Region.sub_prefix (by decide : 64 ≤ frameBytes)⟩)
  refine ⟨h.after frameB restT, slots.after frameT ?_, ⟨?_, ?_⟩, ?_, frameT, restT⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact Offset.disjoint_base _ (by decide) (by decide)
  · rw [memT, Mem.readW_writeW_self32]
  · have outside := writeW32_outside (s.mem.writeW (off (State.addr g.stack) 60) (BitVec.ofNat 32 (r2Words g)))
      (State.addr g.stack) (d := 56) (pre + BitVec.ofNat 32 (16 * Spec.Rsa.modulusWords g.length)) (by decide)
    rw [memT, outside_read32 outside (d := 60) (by omega_using []) (by omega_using []), Mem.readW_writeW_self32]
  · intro j hj
    have o56 := writeW32_outside (s.mem.writeW (off (State.addr g.stack) 60) (BitVec.ofNat 32 (r2Words g)))
      (State.addr g.stack) (d := 56) (pre + BitVec.ofNat 32 (16 * Spec.Rsa.modulusWords g.length)) (by decide)
    have o60 := writeW32_outside s.mem (State.addr g.stack) (d := 60) (BitVec.ofNat 32 (r2Words g)) (by decide)
    rw [memT, outside_read32 o56 (d := 4 * j) (by omega_using [hj]) (by omega_using [hj]), outside_read32 o60 (d := 4 * j) (by omega_using [hj]) (by omega_using [hj])]
def crtRdP (g : PrivGeometry) (pre : BitVec 32) : List Region :=
  [g.sourceRegion 0, g.sourceRegion 2, g.sourceRegion 3, g.sourceRegion 4,
    g.sourceRegion 5, g.sourceRegion 6, g.sourceRegion 7, r2Region g pre, ⟨State.addr g.stack, 64⟩]

theorem crtArgs_stackP {g : PrivGeometry} {bs : Fin 8 → List Byte} {pre : BitVec 32} {s : State}
    (h : PrivContext g bs s) (a : CrtArgs g s) {j : Nat} (hj : j < 14) :
    stackArg (s.callEntry.withRegions (crtRdP g pre) (crtWr g)) j = g.argument (j + 2) := by
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.callEntry_mem,
    State.withRegions_sp, State.callEntry_sp, h.sp]
  rw [addr_add (by have := h.valid.stackHigh; simp only [frameBytes] at this; omega_using [hj, this])]
  exact a.arguments j hj

theorem r2Out_stack {g : PrivGeometry} {bs : Fin 8 → List Byte} {pre : BitVec 32} {s : State} {rd wr : List Region}
    (h : PrivContext g bs s) (o : R2Out g pre s.mem) :
    stackArg ((s.callEntry.withRegions rd wr)) 14 = pre + BitVec.ofNat 32 (16 * Spec.Rsa.modulusWords g.length) ∧
      stackArg ((s.callEntry.withRegions rd wr)) 15 = BitVec.ofNat 32 (r2Words g) := by
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.callEntry_mem,
    State.withRegions_sp, State.callEntry_sp, h.sp]
  have := h.valid.stackHigh; simp only [frameBytes] at this
  rw [addr_add (by omega_using [this]), addr_add (by omega_using [this])]
  exact o

theorem crtCall_preP {g : PrivGeometry} {bs : Fin 8 → List Byte} {pre preLen : BitVec 32} {s : State}
    (h : PrivContext g bs s) (a : CrtArgs g s) (o : R2Out g pre s.mem) (r : R2In g bs pre preLen s) :
    (Proof.Rsa.privateCrtPrecomputedContract abi 56).pre (s.callEntry.withRegions (crtRdP g pre) (crtWr g)) := by
  have sa := fun {j} (hj : j < 14) => crtArgs_stackP (pre := pre) h a hj
  have r2a := r2Out_stack (rd := crtRdP g pre) (wr := crtWr g) h o
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega_using [this]
  have pfit : g.pLength < 2 ^ 32 := by have := h.valid.pFits; omega_using [kfit, this]
  have qfit : g.qLength < 2 ^ 32 := by have := h.valid.qFits; omega_using [kfit, this]
  have wfit : g.scratchLength < 2 ^ 32 := by have := h.valid.workspaceFit; omega_using [this]
  sig_pre [Proof.Rsa.privateCrtPrecomputedContract, Proof.Rsa.privateCrtPrecomputedSig, Proof.Rsa.privateCrtSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  simp only [
    h.sp, a.output, a.outputLength, a.modulus, a.length,
    sa (by decide : 0 < 14), sa (by decide : 1 < 14), sa (by decide : 2 < 14),
    sa (by decide : 3 < 14), sa (by decide : 4 < 14), sa (by decide : 5 < 14),
    sa (by decide : 6 < 14), sa (by decide : 7 < 14), sa (by decide : 8 < 14),
    sa (by decide : 9 < 14), sa (by decide : 10 < 14), sa (by decide : 11 < 14),
    sa (by decide : 12 < 14), sa (by decide : 13 < 14), PrivGeometry.argument,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt pfit,
    Nat.mod_eq_of_lt qfit, Nat.mod_eq_of_lt wfit, r2a.1, r2a.2, Nat.mod_eq_of_lt (r2Words_lt' r)]
  have argAddr : stackArgAddr (s.callEntry.withRegions (crtRdP g pre) (crtWr g)) 0 = State.addr g.stack := by
    simp [stackArgAddr, h.sp]
  rw [argAddr]
  have temporarySub : (⟨State.addr g.temporary, g.length⟩ : Region).Sub g.innerRegion := by
    rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [oM, frameBytes]; omega_using [this])
  have outgoingSub : (⟨State.addr g.stack, 56⟩ : Region).Sub g.innerRegion :=
    Region.sub_prefix (by decide : 56 ≤ frameBytes)
  have tempSources := fun i => (h.valid.stackSources i).sub_left (fun x hx => h.valid.innerSub x (temporarySub x hx))
  have tempWorkspace := h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (temporarySub x hx))
  have tempArgs : (⟨State.addr g.temporary, g.length⟩ : Region).Disjoint ⟨State.addr g.stack, 56⟩ := by
    rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
    exact Offset.disjoint_base _ (by decide : 56 ≤ oM) (by have := h.valid.maxLength; simp only [oM]; omega_using [kfit])
  have callee : (⟨State.addr g.stack - BitVec.ofNat 64 56, 56⟩ : Region) = g.calleeRegion := by
    unfold PrivGeometry.calleeRegion FrameStack.belowA
    rw [FrameStack.addr_sub' h.valid.stackLow]
  simp only [State.addr] at callee
  have calleeSources := fun i => (h.valid.stackSources i).sub_left h.valid.calleeSub
  have calleeWorkspace := h.valid.stackWorkspace.sub_left h.valid.calleeSub
  have argsWorkspace := (h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (outgoingSub x hx))).symm
  have outgoing64 : (⟨State.addr g.stack, 64⟩ : Region).Sub g.innerRegion :=
    Region.sub_prefix (by decide : 64 ≤ frameBytes)
  have tempArgs64 : (⟨State.addr g.temporary, g.length⟩ : Region).Disjoint ⟨State.addr g.stack, 64⟩ := by
    rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
    exact Offset.disjoint_base _ (by decide : 64 ≤ oM) (by have := h.valid.maxLength; simp only [oM]; omega_using [kfit])
  have argsWorkspace64 :=
    (h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (outgoing64 x hx))).symm
  have r2Sep : ∀ R ∈ bodyWrites g, (r2Region g pre).Disjoint R := fun R hR => (r.separate R hR).sub_left r.r2Sub
  have r2Temp : (r2Region g pre).Disjoint ⟨State.addr g.temporary, g.length⟩ :=
    (r2Sep _ (by simp [bodyWrites])).sub_right temporarySub
  have r2Ws : (r2Region g pre).Disjoint g.workspaceRegion := r2Sep _ (by simp [bodyWrites])
  have r2Callee : (r2Region g pre).Disjoint g.calleeRegion := r2Sep _ (by simp [bodyWrites])
  have r2Fit := r.r2Fit
  refine ⟨h.valid.stackLow, by have := h.valid.stackHigh; omega_using [this],
    by simp only [crtRdP, r2Region, PrivGeometry.sourceRegion, PrivGeometry.sourceLength, State.addr, Nat.mul_comm]; rfl, ?_,
    tempSources 0, tempSources 2, tempSources 3, tempSources 4, tempSources 5, tempSources 6, tempSources 7,
    ?_, ?_, tempArgs64, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    h.valid.temporaryFit, h.valid.sourceFits 0, h.valid.sourceFits 2, h.valid.sourceFits 3,
    h.valid.sourceFits 4, h.valid.sourceFits 5, h.valid.sourceFits 6, h.valid.sourceFits 7,
    ?_, ?_, ⟨h.valid.minLength, h.valid.maxLength⟩, trivial, trivial,
    h.valid.pPositive, h.valid.pFits, h.valid.qPositive, h.valid.qFits, trivial, trivial, trivial, h.valid.space,
    ?_, ?_, ?_⟩
  · simp only [crtWr, PrivGeometry.workspaceRegion, State.addr, Nat.mul_comm]
  · simpa only [PrivGeometry.workspaceRegion, State.addr, Nat.mul_comm] using tempWorkspace
  · simpa only [r2Region, State.addr, Nat.mul_comm] using r2Temp.symm
  · change (g.sourceRegion 0).Disjoint ⟨State.addr g.workspace, g.scratchLength * 8⟩
    rw [Nat.mul_comm]; exact h.valid.sourcesWorkspace 0
  · change (g.sourceRegion 2).Disjoint ⟨State.addr g.workspace, g.scratchLength * 8⟩
    rw [Nat.mul_comm]; exact h.valid.sourcesWorkspace 2
  · change (g.sourceRegion 3).Disjoint ⟨State.addr g.workspace, g.scratchLength * 8⟩
    rw [Nat.mul_comm]; exact h.valid.sourcesWorkspace 3
  · change (g.sourceRegion 4).Disjoint ⟨State.addr g.workspace, g.scratchLength * 8⟩
    rw [Nat.mul_comm]; exact h.valid.sourcesWorkspace 4
  · change (g.sourceRegion 5).Disjoint ⟨State.addr g.workspace, g.scratchLength * 8⟩
    rw [Nat.mul_comm]; exact h.valid.sourcesWorkspace 5
  · change (g.sourceRegion 6).Disjoint ⟨State.addr g.workspace, g.scratchLength * 8⟩
    rw [Nat.mul_comm]; exact h.valid.sourcesWorkspace 6
  · change (g.sourceRegion 7).Disjoint ⟨State.addr g.workspace, g.scratchLength * 8⟩
    rw [Nat.mul_comm]; exact h.valid.sourcesWorkspace 7
  · simpa only [r2Region, PrivGeometry.workspaceRegion, State.addr, Nat.mul_comm] using r2Ws.symm
  · simpa only [PrivGeometry.workspaceRegion, State.addr, Nat.mul_comm] using argsWorkspace64
  · rw [callee]; exact h.valid.calleeInner.sub_right temporarySub
  · rw [callee]; exact calleeSources 0
  · rw [callee]; exact calleeSources 2
  · rw [callee]; exact calleeSources 3
  · rw [callee]; exact calleeSources 4
  · rw [callee]; exact calleeSources 5
  · rw [callee]; exact calleeSources 6
  · rw [callee]; exact calleeSources 7
  · rw [callee]; simpa only [PrivGeometry.workspaceRegion, State.addr, Nat.mul_comm] using calleeWorkspace
  · rw [callee]; simpa only [r2Region, State.addr, Nat.mul_comm] using r2Callee.symm
  · rw [callee]; exact h.valid.calleeInner.sub_right outgoing64
  · simpa only [Nat.mul_comm] using h.valid.workspaceFit
  · simpa only [Nat.mul_comm] using r2Fit
  · rfl
  all_goals
    have b0 : Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (g.sources 0)) g.length = bs 0 := (h.sources 0).bytes
    have b3 : Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (g.sources 3)) g.pLength = bs 3 := (h.sources 3).bytes
    have b4 : Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (g.sources 4)) g.qLength = bs 4 := (h.sources 4).bytes
  · rw [b3, b4]; exact r.words
  · rw [b0, b3, b4]; exact r.pq

theorem R2In.r2Read {g : PrivGeometry} {bs : Fin 8 → List Byte} {pre preLen : BitVec 32} {s : State}
    (r : R2In g bs pre preLen s) : InRegions (s.rd ++ s.wr) (r2Region g pre).base (r2Region g pre).len := by
  have := r.fit; have := r.len; have := r2Words_pos g
  unfold r2Region
  dsimp only
  rw [addr_add (by omega_arith)]
  exact CallLay.inRegions_sub r.read (by omega_arith) (by omega_using [])

theorem crtCoversP {g : PrivGeometry} {bs : Fin 8 → List Byte} {pre preLen : BitVec 32} {s : State}
    (h : PrivContext g bs s) (r : R2In g bs pre preLen s) :
    Covers (crtRdP g pre ++ crtWr g) (s.rd ++ s.wr) ∧ Covers (crtWr g) s.wr := by
  have wr : Covers (crtWr g) s.wr := (crtCovers h).2
  refine ⟨Covers.append_left ?_ wr.right, wr⟩
  refine (Covers.one (h.sources 0).read).cons ((Covers.one (h.sources 2).read).cons
    ((Covers.one (h.sources 3).read).cons ((Covers.one (h.sources 4).read).cons
    ((Covers.one (h.sources 5).read).cons ((Covers.one (h.sources 6).read).cons
    ((Covers.one (h.sources 7).read).cons ((Covers.one r.r2Read).cons ?_)))))))
  exact (Covers.one (show InRegions s.wr (State.addr g.stack) 64 from
    ⟨_, h.inner.writable, by simp [Region.Contains, frameBytes]⟩)).right

theorem crt_callP (v : CrtImpl) {g : PrivGeometry} {bs : Fin 8 → List Byte} {pre preLen : BitVec 32} {s : State}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) (args : CrtArgs g s) (o : R2Out g pre s.mem)
    (r : R2In g bs pre preLen s) :
    WP isa (.call v.crtPName v.crtP) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧
      Frame (crtWr g ++ [g.calleeRegion]) s.mem t.mem ∧ Rest callClobbers s t ∧ CrtOut g bs t := by
  refine WP.mono (private_call_ok h slots v.crtPVerified v.crtPStack (crtCall_preP h args o r)
    (crtCoversP h r).1 (crtCoversP h r).2 (crtWrites_sub h.valid) (crtWrites_slots h.valid)) ?_
  rintro t ⟨ht, slotsT, frame, rest, post⟩
  refine ⟨ht, slotsT, frame, rest, ?_⟩
  sig_post [Proof.Rsa.privateCrtPrecomputedContract, Proof.Rsa.privateCrtPrecomputedSig, Proof.Rsa.privateCrtSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at post
  have sa := fun {j} (hj : j < 14) => crtArgs_stackP (pre := pre) h args hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega_using [this]
  have pfit : g.pLength < 2 ^ 32 := by have := h.valid.pFits; omega_using [kfit, this]
  have qfit : g.qLength < 2 ^ 32 := by have := h.valid.qFits; omega_using [kfit, this]
  simp only [args.output, args.modulus, args.length,
    sa (by decide : 0 < 14), sa (by decide : 2 < 14), sa (by decide : 3 < 14),
    sa (by decide : 4 < 14), sa (by decide : 5 < 14), sa (by decide : 6 < 14),
    sa (by decide : 8 < 14), sa (by decide : 10 < 14), PrivGeometry.argument,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt pfit, Nat.mod_eq_of_lt qfit] at post
  rw [BitVec.setWidth_append_eq_right] at post
  change Spec.Rsa.written t.mem (State.addr g.temporary) g.length (t.gpr .r0)
    (Spec.Rsa.privateCrt
      (Spec.Rsa.bytesAt s.mem (State.addr (g.sources 0)) (g.sourceLength 0))
      (Spec.Rsa.bytesAt s.mem (State.addr (g.sources 2)) (g.sourceLength 2))
      (Spec.Rsa.bytesAt s.mem (State.addr (g.sources 3)) (g.sourceLength 3))
      (Spec.Rsa.bytesAt s.mem (State.addr (g.sources 4)) (g.sourceLength 4))
      (Spec.Rsa.bytesAt s.mem (State.addr (g.sources 5)) (g.sourceLength 5))
      (Spec.Rsa.bytesAt s.mem (State.addr (g.sources 6)) (g.sourceLength 6))
      (Spec.Rsa.bytesAt s.mem (State.addr (g.sources 7)) (g.sourceLength 7))) at post
  rw [(h.sources 0).bytes, (h.sources 2).bytes, (h.sources 3).bytes, (h.sources 4).bytes,
    (h.sources 5).bytes, (h.sources 6).bytes, (h.sources 7).bytes] at post
  exact post

theorem crtCall_pubP {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte} {pre : BitVec 32} {s t : State}
    (hs : PrivContext g bs1 s) (ht : PrivContext g bs2 t) (as : CrtArgs g s) (argT : CrtArgs g t)
    (os : R2Out g pre s.mem) (ot : R2Out g pre t.mem) (nb : bs1 0 = bs2 0) :
    (Proof.Rsa.privateCrtPrecomputedContract abi 56).pub
      (s.callEntry.withRegions (crtRdP g pre) (crtWr g)) (t.callEntry.withRegions (crtRdP g pre) (crtWr g)) := by
  sig_pub [Proof.Rsa.privateCrtPrecomputedContract, Proof.Rsa.privateCrtPrecomputedSig, Proof.Rsa.privateCrtSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr]
  have sa := fun {j} (hj : j < 14) => crtArgs_stackP (pre := pre) hs as hj
  have ta := fun {j} (hj : j < 14) => crtArgs_stackP (pre := pre) ht argT hj
  have sr := r2Out_stack (rd := crtRdP g pre) (wr := crtWr g) hs os
  have tr := r2Out_stack (rd := crtRdP g pre) (wr := crtWr g) ht ot
  simp only [hs.sp, ht.sp, as.output, argT.output, as.outputLength, argT.outputLength, as.modulus, argT.modulus,
    as.length, argT.length,
    sa (by decide : 0 < 14), ta (by decide : 0 < 14), sa (by decide : 2 < 14), ta (by decide : 2 < 14),
    sa (by decide : 3 < 14), ta (by decide : 3 < 14), sa (by decide : 4 < 14), ta (by decide : 4 < 14),
    sa (by decide : 5 < 14), ta (by decide : 5 < 14), sa (by decide : 6 < 14), ta (by decide : 6 < 14),
    sa (by decide : 8 < 14), ta (by decide : 8 < 14), sa (by decide : 10 < 14), ta (by decide : 10 < 14),
    sa (by decide : 12 < 14), ta (by decide : 12 < 14), sa (by decide : 13 < 14), ta (by decide : 13 < 14),
    sa (by decide : 1 < 14), ta (by decide : 1 < 14), sa (by decide : 7 < 14), ta (by decide : 7 < 14),
    sa (by decide : 9 < 14), ta (by decide : 9 < 14), sa (by decide : 11 < 14), ta (by decide : 11 < 14),
    sr.1, sr.2, tr.1, tr.2, true_and, and_true]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hs.valid.maxLength; omega_using [this] : g.length < 2 ^ 32)]
  have bytes : Spec.Rsa.bytesAt s.mem ((g.sources 0).setWidth 64) g.length =
      Spec.Rsa.bytesAt t.mem ((g.sources 0).setWidth 64) g.length :=
    (hs.sources 0).bytes.trans (nb.trans (ht.sources 0).bytes.symm)
  rw [bytes]

/-- Ready to call `vg_rsa_private_crt_precomputed`. -/
structure CrtReadyP (g : PrivGeometry) (bs : Fin 8 → List Byte) (pre preLen : BitVec 32) (s : State) : Prop
    extends CrtReady g bs s where
  out : R2Out g pre s.mem
  r2 : R2In g bs pre preLen s

theorem crtCall_ctP (v : CrtImpl) {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte} {pre preLen : BitVec 32}
    (nb : bs1 0 = bs2 0) :
    RelCT isa (fun s t => CrtReadyP g bs1 pre preLen s ∧ CrtReadyP g bs2 pre preLen t ∧ s.sp = t.sp)
      (.call v.crtPName v.crtP) (fun _ _ => True) := by
  apply RelCT.call v.crtPVerified.1 v.crtPVerified.2.1 (crtRdP g pre) (crtWr g)
  intro s t h
  exact ⟨crtCall_preP h.1.context h.1.args h.1.out h.1.r2, crtCall_preP h.2.1.context h.2.1.args h.2.1.out h.2.1.r2,
    crtCall_pubP h.1.context h.2.1.context h.1.args h.2.1.args h.1.out h.2.1.out nb,
    (crtCoversP h.1.context h.1.r2).1, (crtCoversP h.1.context h.1.r2).2,
    (crtCoversP h.2.1.context h.2.1.r2).1, (crtCoversP h.2.1.context h.2.1.r2).2⟩
end VG.Proof.Rsa.Arm
end

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont

open VG.Proof.X25519.Arm (Rest wp_mov op2_imm op2_lsl)

/-! ## Copying the public precomputation

`pcCopy` stands in for the call of `vg_rsa_public_precompute`: it copies the
first `2 w` words of `pre`, which are what that call writes, into the same
frame slot, and returns its status 1. -/


/-- The incoming `pre` (argument 16), its first `2 w` words `ws`. -/
structure PreIn (g : PrivGeometry) (pre : BitVec 32) (ws : List (BitVec 64)) (s : State) : Prop where
  slotFit : g.stack.toNat + arg 16 + 8 ≤ 2 ^ 32
  slotRead : InRegions (s.rd ++ s.wr) (off (State.addr g.stack) (arg 16)) 4
  slot : s.mem.readW (off (State.addr g.stack) (arg 16)) 32 = pre
  slotSeparate : ∀ r ∈ bodyWrites g, (⟨off (State.addr g.stack) (arg 16), 4⟩ : Region).Disjoint r
  fit : pre.toNat + 16 * Spec.Rsa.modulusWords g.length ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (State.addr pre) (16 * Spec.Rsa.modulusWords g.length)
  separate : ∀ r ∈ bodyWrites g,
    (⟨State.addr pre, 16 * Spec.Rsa.modulusWords g.length⟩ : Region).Disjoint r
  words : Spec.Rsa.wordsAt s.mem (State.addr pre) (2 * Spec.Rsa.modulusWords g.length) = ws

theorem preIn_kept (g : PrivGeometry) (pre : BitVec 32) (ws : List (BitVec 64)) :
    Kept g (PreIn g pre ws) := by
  intro s t rs h frame rest
  have fit : 16 * Spec.Rsa.modulusWords g.length < 2 ^ 64 := by have := h.fit; omega_using [this]
  refine ⟨h.slotFit, by rw [rest.rd, rest.wr]; exact h.slotRead, ?_, h.slotSeparate, h.fit,
    by rw [rest.rd, rest.wr]; exact h.read, h.separate, ?_⟩
  · rw [frame.readW (r := ⟨off (State.addr g.stack) (arg 16), 4⟩) (Region.contains_self _ _)
      h.slotSeparate (by decide)]
    exact h.slot
  · rw [wordsAt_frame frame (by omega_using [fit]) (by
      rw [show 8 * (2 * Spec.Rsa.modulusWords g.length) = 16 * Spec.Rsa.modulusWords g.length by omega_using []]
      exact h.separate)]
    exact h.words

theorem precomputation_inner {g : PrivGeometry} (h : g.Valid) :
    Region.Sub ⟨State.addr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ g.innerRegion := by
  have := h.maxLength
  rw [PrivGeometry.precomputation, h.offsetAddr (by decide)]
  exact Offset.sub_base _ (by simp only [oPre, frameBytes, Spec.Rsa.modulusWords]; omega_using [this])

theorem precomputation_toNat {g : PrivGeometry} (h : g.Valid) :
    g.precomputation.toNat = g.stack.toNat + oPre := by
  have := h.stackHigh
  rw [PrivGeometry.precomputation, BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [oPre, frameBytes] at *
  omega_using [this]

theorem bytesAt_of_read {m m' : Mem} {a b : Addr} {n : Nat} (h : m'.read a n = m.read b n) :
    Spec.Rsa.bytesAt m' a n = Spec.Rsa.bytesAt m b n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [← Mem.extractLsb'_read m' a hi, ← Mem.extractLsb'_read m b hi, h]

theorem wordsAt_of_bytes {m m' : Mem} {a b : Addr} {n : Nat}
    (h : Spec.Rsa.bytesAt m' a (8 * n) = Spec.Rsa.bytesAt m b (8 * n)) :
    Spec.Rsa.wordsAt m' a n = Spec.Rsa.wordsAt m b n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [Mem.readW]
  congr 1
  refine Mem.read_eq_of_bytes fun k hk => ?_
  have hk : k < 8 := hk
  rw [Mem.extractLsb'_read m _ hk]
  have e := congrArg (fun l : List Byte => l[8 * i + k]?) h
  simp only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range (by omega_arith : 8 * i + k < 8 * n),
    Option.map_some, Option.some.injEq] at e
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact e

/-- The copy's first block: the byte count and the source. -/
theorem pcCopyHead_ok {g : PrivGeometry} {bs : Fin 8 → List Byte} {pre : BitVec 32}
    {ws : List (BitVec 64)} (s : State) (h : PrivContext g bs s) (args : PcArgs g s)
    (q : PreIn g pre ws s) :
    WP isa (.block [.mov .lr (.shifted .r1 .lsl 3), .ldrSp .r1 (arg 16)]) s fun t =>
      t.gpr .r0 = g.precomputation ∧ t.gpr .r1 = pre ∧
      t.gpr .lr = BitVec.ofNat 32 (16 * Spec.Rsa.modulusWords g.length) ∧
      t.mem = s.mem ∧ Rest [.r1, .lr] s t := by
  have words : 2 * Spec.Rsa.modulusWords g.length < 2 ^ 32 := by
    have := h.valid.maxLength; simp only [Spec.Rsa.modulusWords]; omega_using [this]
  refine wp_mov (op2_lsl (by decide)) fun u a => ?_
  refine wp_loadStack (a := off (State.addr g.stack) (arg 16)) (by decide)
    (by rw [a.sp, h.sp]; exact addr_add (by have := q.slotFit; omega_using [this]))
    (by rw [a.rd, a.wr]; exact q.slotRead) fun t b => WP.block_nil ?_
  refine ⟨?_, by rw [b.gpr, a.mem]; exact q.slot, ?_, b.mem.trans a.mem,
    (a.rest (by simp)).trans (b.rest (by simp))⟩
  · rw [b.other .r0 (by decide), a.other .r0 (by decide)]; exact args.output
  · rw [b.other .lr (by decide), a.gpr, args.outputLength, BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 32 (2 * Spec.Rsa.modulusWords g.length) * BitVec.ofNat 32 8 = _
    rw [← BitVec.ofNat_mul]
    congr 1
    omega_using []

/-- `pcCopy` leaves what the call of `vg_rsa_public_precompute` leaves. -/
theorem pcCopy_ok {g : PrivGeometry} {bs : Fin 8 → List Byte} {pre : BitVec 32}
    {ws : List (BitVec 64)} (pc : Spec.Rsa.publicPrecompute (bs 0) = some ws)
    (s : State) (h : PrivContext g bs s) (slots : PrivSlots g s.mem) (args : PcArgs g s)
    (q : PreIn g pre ws s) : WP isa pcCopy s (PcPost g bs s) := by
  have bound := h.valid.maxLength
  have low := h.valid.minLength
  have nbytes : 0 < 16 * Spec.Rsa.modulusWords g.length := by
    simp only [Spec.Rsa.modulusWords]; omega_using [low]
  have nfit : 16 * Spec.Rsa.modulusWords g.length < 2 ^ 32 := by
    simp only [Spec.Rsa.modulusWords]; omega_using [bound]
  have sub := precomputation_inner h.valid
  unfold pcCopy
  refine WP.seq (WP.mono (pcCopyHead_ok s h args q) ?_)
  rintro u ⟨r0U, r1U, lrU, memU, restU⟩
  have dstFit : g.precomputation.toNat + 16 * Spec.Rsa.modulusWords g.length ≤ 2 ^ 32 := by
    rw [precomputation_toNat h.valid]
    have := h.valid.stackHigh
    simp only [oPre, frameBytes, Spec.Rsa.modulusWords] at *
    omega_using [bound, this]
  have sep : Region.Disjoint ⟨State.addr pre, 16 * Spec.Rsa.modulusWords g.length⟩
      ⟨State.addr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ :=
    ((q.separate _ (by simp [bodyWrites])).symm.sub_left sub).symm
  refine WP.seq (WP.mono (copyBuffer_ok u nbytes q.fit dstFit nfit
    (by rw [restU.rd, restU.wr]; exact q.read)
    (by rw [restU.wr]; exact h.precomputationWrite) sep r0U r1U lrU) ?_)
  rintro z ⟨copied, frameZ, _, restZ⟩
  refine wp_mov (op2_imm (by decide)) fun t d => WP.block_nil ?_
  have frameT : Frame [⟨State.addr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩] s.mem t.mem := by
    rw [d.mem, ← memU]; exact frameZ
  have restT : Rest callClobbers s t :=
    (restU.mono (by simp [callClobbers])).trans ((restZ.mono (by simp [callClobbers])).trans
      (d.rest (by simp [callClobbers])))
  have frameB : Frame (bodyWrites g) s.mem t.mem := frameT.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r
    exact ⟨g.innerRegion, by simp [bodyWrites], sub⟩
  have framePc : Frame (pcWr g ++ [g.calleeRegion]) s.mem t.mem :=
    frameT.mono (by simp [pcWr])
  unfold PcPost
  refine ⟨h.after frameB restT, slots.after frameT fun r hr => ?_, framePc, restT, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r
    exact pcWrites_slots h.valid _ List.mem_cons_self
  · simp only [PcOut, pc]
    refine ⟨by rw [d.gpr], ?_⟩
    rw [← q.words, ← memU, d.mem]
    refine wordsAt_of_bytes (bytesAt_of_read ?_)
    rw [show 8 * (2 * Spec.Rsa.modulusWords g.length) = 16 * Spec.Rsa.modulusWords g.length by omega_using []]
    exact copied

theorem pcCopy_ready {g : PrivGeometry} {bs : Fin 8 → List Byte} {pre : BitVec 32}
    {ws : List (BitVec 64)} (pc : Spec.Rsa.publicPrecompute (bs 0) = some ws)
    (s : State) (h : PcReady g bs s ∧ PreIn g pre ws s) : WP isa pcCopy s (PcReturned g bs) := by
  refine WP.mono (pcCopy_ok pc s h.1.context h.1.slots h.1.args h.2) ?_
  rintro t ⟨ht, slots, _, _, output⟩
  refine ⟨⟨ht, slots⟩, ?_⟩
  simp only [PcOut, PcPublic, pc, Option.getD] at output ⊢
  exact output.2

/-! ## The copy's trace depends only on the layout -/

theorem spBlock_ct (code : List Instr)
    (leak : ∀ i ∈ code, ∀ s t : State, s.sp = t.sp → addrs i s = addrs i t) :
    RelCT isa (fun s t => s.sp = t.sp) (.block code) (fun s t => s.sp = t.sp) := by
  induction code with
  | nil => exact RelCT.block_nil (fun _ _ h => h)
  | cons i rest ih =>
    have first : RelCT isa (fun s t => s.sp = t.sp) (.block [i]) (fun s t => s.sp = t.sp) := by
      apply single_ct (fun s t h => leak i (by simp) s t h)
      intro s t u v h e1 e2
      exact (exec_sp e1).trans (h.trans (exec_sp e2).symm)
    exact RelCT.block_append (first.seq (ih (fun j hj => leak j (by simp [hj]))))

def CopyReady (g : PrivGeometry) (pre : BitVec 32) (s : State) : Prop :=
  s.gpr .r0 = g.precomputation ∧ s.gpr .r1 = pre ∧
    s.gpr .lr = BitVec.ofNat 32 (16 * Spec.Rsa.modulusWords g.length)

theorem pcCopy_ct {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte} {pre : BitVec 32}
    {ws1 ws2 : List (BitVec 64)} :
    RelCT isa (fun s t => (PcReady g bs1 s ∧ PreIn g pre ws1 s) ∧ (PcReady g bs2 t ∧ PreIn g pre ws2 t) ∧
      s.sp = t.sp) pcCopy (fun _ _ => True) := by
  unfold pcCopy
  have head := (spBlock_ct [.mov .lr (.shifted .r1 .lsl 3), .ldrSp .r1 (arg 16)] (by
      intro i hi s t h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> simp [addrs, h])).mono
    (P' := fun (s t : State) => (PcReady g bs1 s ∧ PreIn g pre ws1 s) ∧ (PcReady g bs2 t ∧ PreIn g pre ws2 t) ∧
      s.sp = t.sp) (fun _ _ h => h.2.2) (fun _ _ h => h)
  have head' := head.wp (F₁ := CopyReady g pre) (F₂ := CopyReady g pre) fun s t h =>
    ⟨WP.mono (pcCopyHead_ok s h.1.1.context h.1.1.args h.1.2) fun _ hu => ⟨hu.1, hu.2.1, hu.2.2.1⟩,
      WP.mono (pcCopyHead_ok t h.2.1.1.context h.2.1.1.args h.2.1.2) fun _ hu => ⟨hu.1, hu.2.1, hu.2.2.1⟩⟩
  refine head'.seq (RelCT.seq (R := fun _ _ => True) ?_ ?_)
  · intro s t tr1 tr2 u v h e1 e2
    obtain ⟨_, ⟨s0, s1, slr⟩, ⟨t0, t1, tlr⟩⟩ := h
    exact ⟨copyBytes_ct s t tr1 tr2 u v trivial trivial
      ⟨s0.trans t0.symm, s1.trans t1.symm, slr.trans tlr.symm⟩ e1 e2, trivial⟩
  · exact single_ct (fun _ _ _ => by simp [addrs]) (fun _ _ _ _ _ _ _ => trivial)
/-! ## The call of `vg_rsa_private_crt_precomputed` -/

/-- What the body keeps of `pre`. -/
def PreQ (g : PrivGeometry) (bs : Fin 8 → List Byte) (pre preLen : BitVec 32) (ws : List (BitVec 64))
    (s : State) : Prop :=
  PreIn g pre ws s ∧ R2In g bs pre preLen s

theorem preQ_kept (g : PrivGeometry) (bs : Fin 8 → List Byte) (pre preLen : BitVec 32) (ws : List (BitVec 64)) :
    Kept g (PreQ g bs pre preLen ws) :=
  fun q frame rest => ⟨preIn_kept g pre ws q.1 frame rest, r2In_kept g bs pre preLen q.2 frame rest⟩

theorem crtArgsP_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} {pre preLen : BitVec 32}
    {ws : List (BitVec 64)} (h : PrivContext g bs s)
    (output : s.gpr .r0 = g.output) (modulus : s.gpr .r2 = g.sources 0) (count : s.gpr .r3 = BitVec.ofNat 32 g.length)
    (q : PreQ g bs pre preLen ws s) :
    WP isa (.block crtArgsP) s fun t => CrtReadyP g bs pre preLen t ∧ PreQ g bs pre preLen ws t ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Rest [.r0, .r1, .r12, .lr] s t := by
  unfold crtArgsP
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (saveSlots_ok s h output modulus count) ?_
  rintro u ⟨hu, slotsU, ptr, frameU, restU⟩
  refine WP.mono (copyArgs_ok u hu slotsU ptr) ?_
  rintro v ⟨hv, slotsV, args, frameV, restV⟩
  have restUV : Rest [.r0, .r12] s v := restU.trans (restV.mono (by simp))
  have frameSV : Frame (bodyWrites g) s.mem v.mem := (frameU.trans (frameV.sub (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨g.innerRegion, by simp, Region.sub_prefix (by decide : 56 ≤ frameBytes)⟩))).mono (by simp [bodyWrites])
  have qV := preQ_kept g bs pre preLen ws q frameSV restUV
  refine WP.mono (r2Args_ok v hv slotsV ((restV.gpr .r12 (by simp)).trans ptr) qV.1.slotRead qV.1.slot
    (by have := qV.1.slotFit; omega_using [this]) qV.2) ?_
  rintro w ⟨hw, slotsW, outW, keepW, frameW, restW⟩
  have frameVW : Frame (bodyWrites g) v.mem w.mem := frameW.sub (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨g.innerRegion, by simp [bodyWrites], Region.sub_prefix (by decide : 64 ≤ frameBytes)⟩)
  have qW := preQ_kept g bs pre preLen ws qV frameVW restW
  have restVW : Rest [.r0, .r1, .r12, .lr] s w := (restUV.mono (by simp)).trans (restW.mono (by simp))
  refine WP.mono (crtRegs_ok w hw ((restVW.gpr .r2 (by simp)).trans modulus) ((restVW.gpr .r3 (by simp)).trans count)
    (fun j hj => (keepW j hj).trans (args j hj))) ?_
  rintro t ⟨argsT, mem, restT⟩
  have frameWT : Frame (bodyWrites g) w.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨⟨⟨⟨hw.after frameWT restT, by simpa only [mem] using slotsW⟩, argsT⟩, by rw [mem]; exact outW,
    (r2In_kept g bs pre preLen qW.2 frameWT restT)⟩, preQ_kept g bs pre preLen ws qW frameWT restT,
    frameSV.trans (frameVW.trans frameWT), restVW.trans (restT.mono (by simp))⟩

theorem crtCallP_readyQ (v : CrtImpl) {g : PrivGeometry} {bs : Fin 8 → List Byte} {pre preLen : BitVec 32}
    {ws : List (BitVec 64)} (s : State) (h : CrtReadyP g bs pre preLen s ∧ PreQ g bs pre preLen ws s) :
    WP isa (.call v.crtPName v.crtP) s fun t => (PrivateState g bs t ∧ PreQ g bs pre preLen ws t) ∧ CrtOut g bs t := by
  refine WP.mono (crt_callP v h.1.context h.1.slots h.1.args h.1.out h.1.r2) ?_
  rintro t ⟨ht, slots, frame, rest, out⟩
  exact ⟨⟨⟨ht, slots⟩, preQ_kept g bs pre preLen ws h.2
    (frame.sub (calleeWrites_sub (crtWrites_sub h.1.context.valid))) rest⟩, out⟩

theorem bodyP_ok (v : CrtImpl) {g : PrivGeometry} {bs : Fin 8 → List Byte} {pre preLen : BitVec 32}
    {ws : List (BitVec 64)} (pc : Spec.Rsa.publicPrecompute (bs 0) = some ws)
    (s : State) (h : PrivContext g bs s) (output : s.gpr .r0 = g.output)
    (modulus : s.gpr .r2 = g.sources 0) (count : s.gpr .r3 = BitVec.ofNat 32 g.length)
    (q : PreQ g bs pre preLen ws s) :
    WP isa (bodyP v.crtPName v.crtP v.pdName v.pd) s (BodyPost g bs s) := by
  unfold bodyP
  refine WP.seq (WP.mono (crtArgsP_ok s h output modulus count q) ?_)
  rintro u ⟨hu, qu, frameU', restU⟩
  refine WP.seq (WP.mono (crt_callP v hu.context hu.slots hu.args hu.out hu.r2) ?_)
  rintro z ⟨hz, slotsZ, frameZ, restZ, crt⟩
  have frameZ' := frameZ.sub (calleeWrites_sub (crtWrites_sub h.valid))
  refine WP.mono (checkWith_ok v (preIn_kept g pre ws) (fun s h sl a q => pcCopy_ok pc s h sl a q)
    z hz slotsZ (preQ_kept g bs pre preLen ws qu frameZ' restZ).1) ?_
  rintro t ⟨_, status, bytes, cleared, frameT, restT⟩
  unfold BodyPost
  refine ⟨?_, cleared, frameU'.trans (frameZ'.trans frameT),
    (restU.mono (by simp)).trans ((restZ.mono (by simp [callClobbers])).trans restT)⟩
  have narrow : ((z.gpr .r0).setWidth 64).setWidth 32 = z.gpr .r0 := by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  have outcome := Rsa.outcome_eq (rc := (z.gpr .r0).setWidth 64)
    (r := Rsa.checkResult ((z.gpr .r0).setWidth 64) (bs 0) (bs 1) (bs 2)
      (Spec.Rsa.bytesAt z.mem (State.addr g.temporary) g.length))
    (h.sources 0).length (h.sources 2).length (by rw [narrow]; exact crt) rfl bytes
  rw [status]
  exact outcome


theorem crtArgsP_ct : RelCT isa (fun s t => s.sp = t.sp) (.block crtArgsP) (fun s t => s.sp = t.sp) :=
  setupChecked_ct _ (by decide) (by decide)

theorem privateBodyP_ct (v : CrtImpl) {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte} {pre preLen : BitVec 32}
    {ws1 ws2 : List (BitVec 64)}
    (pc1 : Spec.Rsa.publicPrecompute (bs1 0) = some ws1) (pc2 : Spec.Rsa.publicPrecompute (bs2 0) = some ws2)
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => (PrivateStart g bs1 s ∧ PreQ g bs1 pre preLen ws1 s) ∧
      (PrivateStart g bs2 t ∧ PreQ g bs2 pre preLen ws2 t) ∧ s.sp = t.sp)
      (bodyP v.crtPName v.crtP v.pdName v.pd) (fun _ _ => True) := by
  have args (bs : Fin 8 → List Byte) (ws : List (BitVec 64)) (s : State)
      (h : PrivateStart g bs s ∧ PreQ g bs pre preLen ws s) :
      WP isa (.block crtArgsP) s fun t => CrtReadyP g bs pre preLen t ∧ PreQ g bs pre preLen ws t :=
    (crtArgsP_ok s h.1.context h.1.output h.1.modulus h.1.count h.2).mono fun _ ht => ⟨ht.1, ht.2.1⟩
  have call (bs : Fin 8 → List Byte) (ws : List (BitVec 64)) (s : State)
      (h : CrtReadyP g bs pre preLen s ∧ PreQ g bs pre preLen ws s) :
      WP isa (.call v.crtPName v.crtP) s fun t => PrivateState g bs t ∧ PreQ g bs pre preLen ws t :=
    (crtCallP_readyQ v s h).mono fun _ ht => ht.1
  have chk := privateCheckWith_ct v (preQ_kept g bs1 pre preLen ws1) (preQ_kept g bs2 pre preLen ws2)
    (pcCopy_ct.mono (fun _ _ h => ⟨⟨h.1.1, h.1.2.1⟩, ⟨h.2.1.1, h.2.1.2.1⟩, h.2.2⟩) (fun _ _ _ => trivial))
    (fun s h => pcCopy_ready pc1 s ⟨h.1, h.2.1⟩) (fun s h => pcCopy_ready pc2 s ⟨h.1, h.2.1⟩) nb eb
  unfold bodyP
  apply crt_seq_ct (crtArgsP_ct.mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)) (args bs1 ws1) (args bs2 ws2)
  exact crt_seq_ct ((crtCall_ctP v nb).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial))
    (call bs1 ws1) (call bs2 ws2) chk

/-! ## The function -/

theorem publicPrecompute_of_private {nB pB qB : List Byte} {ws : List (BitVec 64)}
    (h : Spec.Rsa.privatePrecompute nB pB qB = some ws) :
    Spec.Rsa.publicPrecompute nB = some (ws.take (Spec.Rsa.precomputedWords nB.length)) := by
  unfold Spec.Rsa.privatePrecompute at h
  split at h
  · cases hp : Spec.Rsa.publicPrecompute nB with
    | none => simp [hp] at h
    | some w =>
      simp only [hp, Option.map_some, Option.some.injEq] at h
      subst h
      have length : w.length = Spec.Rsa.precomputedWords nB.length := by
        unfold Spec.Rsa.publicPrecompute at hp
        dsimp only at hp
        split at hp
        · cases hp
          simp only [List.length_append, Spec.Rsa.toWords, List.length_map, List.length_range,
            Spec.Rsa.precomputedWords]; omega_using []
        · cases hp
      rw [List.append_assoc, List.take_left' length]
  · cases h

theorem wordsAt_take {m : Mem} {p : Addr} {n L : Nat} (h : n ≤ L) :
    Spec.Rsa.wordsAt m p n = (Spec.Rsa.wordsAt m p L).take n := by
  simp only [Spec.Rsa.wordsAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-- The first `2 w` words of the incoming `pre`, as the wrapper sees them. -/
def preWordsOf (s : State) : List (BitVec 64) :=
  Spec.Rsa.wordsAt (entered s).mem (State.addr (stackArg s 16)) (2 * Spec.Rsa.modulusWords (s.gpr .r3).toNat)

theorem privatePrecompute_r2 {nB pB qB : List Byte} {W : List (BitVec 64)}
    (h : Spec.Rsa.privatePrecompute nB pB qB = some W) :
    Spec.Rsa.os2ip pB * Spec.Rsa.os2ip qB = Spec.Rsa.os2ip nB ∧
      W.drop (Spec.Rsa.precomputedWords nB.length) = Spec.Rsa.primeR2 pB ++ Spec.Rsa.primeR2 qB := by
  unfold Spec.Rsa.privatePrecompute at h
  split at h
  · rename_i pq
    refine ⟨pq, ?_⟩
    cases hp : Spec.Rsa.publicPrecompute nB with
    | none => simp [hp] at h
    | some w =>
      simp only [hp, Option.map_some, Option.some.injEq] at h
      subst h
      have length : w.length = Spec.Rsa.precomputedWords nB.length := by
        unfold Spec.Rsa.publicPrecompute at hp
        dsimp only at hp
        split at hp
        · cases hp
          simp only [List.length_append, Spec.Rsa.toWords, List.length_map, List.length_range,
            Spec.Rsa.precomputedWords]; omega_using []
        · cases hp
      rw [List.append_assoc, ← length, List.drop_left]
  · cases h

theorem wordsAt_drop (m : Mem) (p : Addr) (a b : Nat) :
    (Spec.Rsa.wordsAt m p (a + b)).drop a = Spec.Rsa.wordsAt m (p + BitVec.ofNat 64 (8 * a)) b := by
  simp only [Spec.Rsa.wordsAt]
  rw [List.range_add, List.map_append, List.drop_left' (by simp), List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 3
  omega_using []

theorem private_contract_preP (s : State)
    (h : (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes).pre s) :
    PrivFnInput (privateGeometry s) (privateBytes s) s ∧
      PreQ (privateGeometry s) (privateBytes s) (stackArg s 16) (stackArg s 17) (preWordsOf s) (entered s) ∧
      Spec.Rsa.publicPrecompute (privateBytes s 0) = some (preWordsOf s) := by
  sig_pre [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  have addr : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [addr] at h
  obtain ⟨stackFit, argFit, rd, wr, outN, outE, outI, outP, outQ, outDP, outDQ, outQI, outWs, outPre, outArgs,
    nWs, eWs, iWs, pWs, qWs, dpWs, dqWs, qiWs, wsPre, wsArgs,
    stackOut, stackN, stackE, stackI, stackP, stackQ, stackDP, stackDQ, stackQI, stackWs, stackPre, stackArgs,
    outFit, nFit, eFit, iFit, pFit, qFit, dpFit, dqFit, qiFit, wsFit, preFit,
    valid, outLen, inputLen, ePositive, eFits, pPositive, pShort, qPositive, qShort, dpLen, qiLen, dqLen, space,
    preLen, preVal⟩ := h
  rw [outLen] at wr outN outE outI outP outQ outDP outDQ outQI outWs outPre outArgs stackOut outFit
  rw [inputLen] at rd outI iWs stackI iFit
  rw [dpLen] at rd outDP dpWs stackDP dpFit
  rw [dqLen] at rd outDQ dqWs stackDQ dqFit
  rw [qiLen] at rd outQI qiWs stackQI qiFit
  rw [show (stackArg s 15).toNat * 8 = 8 * (stackArg s 15).toNat from Nat.mul_comm _ _]
    at wr outWs nWs eWs iWs pWs qWs dpWs dqWs qiWs wsPre wsArgs stackWs wsFit
  have args64 : Region.Sub ⟨State.addr s.sp, 64⟩ ⟨State.addr s.sp, 72⟩ := Region.sub_prefix (by decide)
  have sourceFit : ∀ i, ((privateGeometry s).sources i).toNat + (privateGeometry s).sourceLength i ≤ 2 ^ 32 := by
    intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega_arith) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [nFit, eFit, iFit, pFit, qFit, dpFit, dqFit, qiFit]
  have geometry : (privateGeometry s).Valid := by
    refine ⟨valid.1, valid.2, ePositive, eFits, pPositive, pShort, qPositive, qShort, space,
      ?_, ?_, outFit, sourceFit, wsFit, ?_, outWs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [privateGeometry_stackNat s stackFit]
      simp only [stackBytes, frameBytes] at stackFit ⊢; omega_arith
    · rw [privateGeometry_stackNat s stackFit]
      simp only [stackBytes, frameBytes] at stackFit ⊢; omega_arith
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega_arith) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [outN, outE, outI, outP, outQ, outDP, outDQ, outQI]
    · rw [privateGeometry_arguments s stackFit]; exact outArgs.sub_right args64
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega_arith) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [nWs, eWs, iWs, pWs, qWs, dpWs, dqWs, qiWs]
    · rw [privateGeometry_arguments s stackFit]; exact wsArgs.sub_right args64
    · rw [privateGeometry_wholeStack s stackFit]; exact stackOut
    · intro i
      rw [privateGeometry_wholeStack s stackFit]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega_arith) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [stackN, stackE, stackI, stackP, stackQ, stackDP, stackDQ, stackQI]
    · rw [privateGeometry_wholeStack s stackFit]; exact stackWs
    · rw [privateGeometry_wholeStack s stackFit, privateGeometry_arguments s stackFit]
      exact stackArgs.sub_right args64
  have entry : PrivEntryInput (privateGeometry s) (privateBytes s) s := by
    refine ⟨geometry, stackFit, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, by simp [privateGeometry]⟩
    · intro i
      refine ⟨sourceFit i, ?_, rfl⟩
      refine ⟨(privateGeometry s).sourceRegion i, List.mem_append_left _ ?_, Region.contains_self _ _⟩
      rw [rd]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega_arith) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_self)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
    · rw [wr]
      exact ⟨_, by simp [privateGeometry, State.addr], Region.contains_self _ _⟩
    · rw [wr]
      exact ⟨_, by simp [privateGeometry, State.addr], Region.contains_self _ _⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]),
        by simp [Region.Contains]⟩
    · intro j hj
      have read : s.mem.readW (off (State.addr s.sp) (4 * j)) 32 = stackArg s j := by
        unfold stackArg stackArgAddr
        rw [addr_add (by omega_arith : s.sp.toNat + 4 * j < 2 ^ 32)]
      rw [read]
      have ie : stackArg s 3 = s.gpr .r3 := BitVec.eq_of_toNat_eq inputLen
      have de : stackArg s 9 = stackArg s 5 := BitVec.eq_of_toNat_eq dpLen
      have qe : stackArg s 13 = stackArg s 5 := BitVec.eq_of_toNat_eq qiLen
      have dqe : stackArg s 11 = stackArg s 7 := BitVec.eq_of_toNat_eq dqLen
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
          j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 by omega_arith) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [privateGeometry, PrivGeometry.argument, ie, de, qe, dqe]
      all_goals rfl
  -- `pre`
  have kfit := valid.2
  have w2 : 2 * Spec.Rsa.modulusWords (privateGeometry s).length ≤ (stackArg s 17).toNat := by
    rw [preLen]
    simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords]
    change 2 * Spec.Rsa.modulusWords (s.gpr .r3).toNat ≤ _
    omega_using []
  have preSub : Region.Sub ⟨State.addr (stackArg s 16), 16 * Spec.Rsa.modulusWords (privateGeometry s).length⟩
      ⟨State.addr (stackArg s 16), (stackArg s 17).toNat * 8⟩ := Region.sub_prefix (by omega_using [w2])
  have args72 : ∀ r ∈ bodyWrites (privateGeometry s), (⟨State.addr s.sp, 72⟩ : Region).Disjoint r := by
    intro r hr
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    have whole : (privateGeometry s).wholeStack.Disjoint ⟨State.addr s.sp, 72⟩ := by
      rw [privateGeometry_wholeStack s stackFit]; exact stackArgs
    rcases hr with rfl | rfl | rfl | rfl
    · exact (whole.sub_left geometry.innerSub).symm
    · exact (whole.sub_left geometry.calleeSub).symm
    · exact outArgs.symm
    · exact wsArgs.symm
  have preSep : ∀ r ∈ bodyWrites (privateGeometry s),
      (⟨State.addr (stackArg s 16), 16 * Spec.Rsa.modulusWords (privateGeometry s).length⟩ : Region).Disjoint r := by
    intro r hr
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    have whole : (privateGeometry s).wholeStack.Disjoint ⟨State.addr (stackArg s 16), (stackArg s 17).toNat * 8⟩ := by
      rw [privateGeometry_wholeStack s stackFit]; exact stackPre
    rcases hr with rfl | rfl | rfl | rfl
    · exact ((whole.sub_left geometry.innerSub).symm).sub_left preSub
    · exact ((whole.sub_left geometry.calleeSub).symm).sub_left preSub
    · exact outPre.symm.sub_left preSub
    · exact wsPre.symm.sub_left preSub
  have slotAddr : off (State.addr (privateGeometry s).stack) (arg 16) = State.addr s.sp + BitVec.ofNat 64 64 := by
    have b := congrArg Region.base (privateGeometry_arguments s stackFit)
    simp only [PrivGeometry.argumentsRegion] at b
    rw [← b, Offset.add_add]
    rfl
  have slotSub : Region.Sub ⟨off (State.addr (privateGeometry s).stack) (arg 16), 4⟩ ⟨State.addr s.sp, 72⟩ := by
    rw [slotAddr]; exact Offset.sub_base _ (by decide)
  have savedSep : ∀ r ∈ [(privateGeometry s).savedRegion], (⟨State.addr s.sp, 72⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r
    have whole : (privateGeometry s).wholeStack.Disjoint ⟨State.addr s.sp, 72⟩ := by
      rw [privateGeometry_wholeStack s stackFit]; exact stackArgs
    exact (whole.sub_left geometry.savedSub).symm
  have preSaved : ∀ r ∈ [(privateGeometry s).savedRegion],
      (⟨State.addr (stackArg s 16), (stackArg s 17).toNat * 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r
    have whole : (privateGeometry s).wholeStack.Disjoint ⟨State.addr (stackArg s 16), (stackArg s 17).toNat * 8⟩ := by
      rw [privateGeometry_wholeStack s stackFit]; exact stackPre
    exact (whole.sub_left geometry.savedSub).symm
  have frameE := entry.enteredFrame
  have wordsE : Spec.Rsa.wordsAt (entered s).mem (State.addr (stackArg s 16)) (stackArg s 17).toNat =
      Spec.Rsa.wordsAt s.mem (State.addr (stackArg s 16)) (stackArg s 17).toNat :=
    wordsAt_frame frameE (by omega_using []) (by rw [Nat.mul_comm]; exact preSaved)
  refine ⟨entry.ready, ⟨⟨?_, ?_, ?_, fun r hr => (args72 r hr).sub_left slotSub, by
      have := w2; change 2 * Spec.Rsa.modulusWords (s.gpr .r3).toNat ≤ _ at this
      change _ + 16 * Spec.Rsa.modulusWords (s.gpr .r3).toNat ≤ _; omega_using [preFit, this],
    entered_read ⟨⟨State.addr (stackArg s 16), (stackArg s 17).toNat * 8⟩,
      List.mem_append_left _ (by rw [rd]; simp [State.addr]), ?_⟩, preSep, rfl⟩, ?_⟩, ?_⟩
  · rw [privateGeometry_stackNat s stackFit]
    simp only [arg, stackBytes, frameBytes] at stackFit ⊢; omega_using [argFit]
  · exact entered_read ⟨⟨State.addr s.sp, 72⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), by
      rw [slotAddr]; exact Offset.contains_base _ (by decide : 64 + 4 ≤ 72) (by decide)⟩
  · rw [frameE.readW (r := ⟨off (State.addr (privateGeometry s).stack) (arg 16), 4⟩) (Region.contains_self _ _)
      (fun r hr => (savedSep r hr).sub_left slotSub) (by decide), slotAddr]
    unfold stackArg stackArgAddr
    rw [addr_add (by omega_using [argFit] : s.sp.toNat + 4 * 16 < 2 ^ 32)]
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
    change 16 * Spec.Rsa.modulusWords (s.gpr .r3).toNat ≤ _
    have := w2; change 2 * Spec.Rsa.modulusWords (s.gpr .r3).toNat ≤ _ at this
    omega_using [this]
  · have slot17Addr : off (State.addr (privateGeometry s).stack) (arg 17) = State.addr s.sp + BitVec.ofNat 64 68 := by
      have b := congrArg Region.base (privateGeometry_arguments s stackFit)
      simp only [PrivGeometry.argumentsRegion] at b
      rw [← b, Offset.add_add]
      rfl
    have slot17Sub : Region.Sub ⟨off (State.addr (privateGeometry s).stack) (arg 17), 4⟩ ⟨State.addr s.sp, 72⟩ := by
      rw [slot17Addr]; exact Offset.sub_base _ (by decide)
    have preSepFull : ∀ r ∈ bodyWrites (privateGeometry s),
        (⟨State.addr (stackArg s 16), 8 * (stackArg s 17).toNat⟩ : Region).Disjoint r := by
      intro r hr
      simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      have whole : (privateGeometry s).wholeStack.Disjoint ⟨State.addr (stackArg s 16), (stackArg s 17).toNat * 8⟩ := by
        rw [privateGeometry_wholeStack s stackFit]; exact stackPre
      rw [Nat.mul_comm]
      rcases hr with rfl | rfl | rfl | rfl
      · exact (whole.sub_left geometry.innerSub).symm
      · exact (whole.sub_left geometry.calleeSub).symm
      · exact outPre.symm
      · exact wsPre.symm
    obtain ⟨pq, drop⟩ := privatePrecompute_r2 preVal
    have lenEq : (stackArg s 17).toNat = 2 * Spec.Rsa.modulusWords (privateGeometry s).length + r2Words (privateGeometry s) := by
      rw [preLen]
      simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, r2Words]
      change _ = 2 * Spec.Rsa.modulusWords (s.gpr .r3).toNat +
        (Spec.Rsa.primeWords (stackArg s 5).toNat + Spec.Rsa.primeWords (stackArg s 7).toNat)
      omega_using []
    have r2pos := r2Words_pos (privateGeometry s)
    have hw : (privateGeometry s).length = (s.gpr .r3).toNat := rfl
    refine ⟨entered_read ⟨⟨State.addr s.sp, 72⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), by
        rw [slot17Addr]; exact Offset.contains_base _ (by decide : 68 + 4 ≤ 72) (by decide)⟩, ?_,
      fun r hr => (args72 r hr).sub_left slot17Sub, ?_, lenEq, by rw [Nat.mul_comm]; exact preFit,
      entered_read ⟨⟨State.addr (stackArg s 16), (stackArg s 17).toNat * 8⟩,
        List.mem_append_left _ (by rw [rd]; simp [State.addr]), by rw [Nat.mul_comm]; exact Region.contains_self _ _⟩,
      preSepFull, ?_, pq⟩
    · rw [frameE.readW (r := ⟨off (State.addr (privateGeometry s).stack) (arg 17), 4⟩) (Region.contains_self _ _)
        (fun r hr => (savedSep r hr).sub_left slot17Sub) (by decide), slot17Addr]
      unfold stackArg stackArgAddr
      rw [addr_add (by omega_using [argFit] : s.sp.toNat + 4 * 17 < 2 ^ 32)]
    · rw [privateGeometry_stackNat s stackFit]
      simp only [arg, stackBytes, frameBytes] at stackFit ⊢; omega_using [argFit]
    · have fit16 : (stackArg s 16).toNat + 16 * Spec.Rsa.modulusWords (privateGeometry s).length < 2 ^ 32 := by
        omega_using [preFit, lenEq, r2pos]
      have r2fit : 8 * r2Words (privateGeometry s) < 2 ^ 64 := by omega_using [lenEq]
      have sub : Region.Sub ⟨State.addr (stackArg s 16) + BitVec.ofNat 64 (16 * Spec.Rsa.modulusWords (privateGeometry s).length),
          8 * r2Words (privateGeometry s)⟩ ⟨State.addr (stackArg s 16), (stackArg s 17).toNat * 8⟩ :=
        Offset.sub_base _ (by omega_using [lenEq])
      rw [addr_add fit16, wordsAt_frame frameE r2fit (fun r hr => (preSaved r hr).sub_left sub),
        show 16 * Spec.Rsa.modulusWords (privateGeometry s).length =
          8 * (2 * Spec.Rsa.modulusWords (privateGeometry s).length) by omega_using [],
        ← wordsAt_drop, ← lenEq]
      have nl : (Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (s.gpr .r2)) (s.gpr .r3).toNat).length =
          (s.gpr .r3).toNat := by simp [Spec.Rsa.bytesAt]
      rw [nl] at drop
      simp only [Spec.Rsa.precomputedWords] at drop
      exact drop
  · have pc := publicPrecompute_of_private preVal
    change Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (s.gpr .r2)) (s.gpr .r3).toNat) = _
    rw [pc]
    have w2' : 2 * Spec.Rsa.modulusWords (s.gpr .r3).toNat ≤ (stackArg s 17).toNat := w2
    unfold preWordsOf
    rw [wordsAt_take w2', wordsE]
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range, Spec.Rsa.precomputedWords]
    rfl

theorem privateFnP_ok (v : CrtImpl) (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    {pre preLen : BitVec 32} {ws : List (BitVec 64)}
    (h : PrivFnInput g bs s) (q : PreQ g bs pre preLen ws (entered s))
    (pc : Spec.Rsa.publicPrecompute (bs 0) = some ws) :
    WP isa (privCodeP v) s fun t => abiPreserved s t ∧
      Spec.Rsa.writtenOutcome t.mem (State.addr g.output) g.length (t.gpr .r0)
        (Spec.Rsa.privateChecked (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6) (bs 7)) :=
  codeWith_ok s (fun s h o m c q => bodyP_ok v pc s h o m c q) h q

theorem privateFnP_ct (v : CrtImpl) {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte}
    {pre preLen : BitVec 32} {ws1 ws2 : List (BitVec 64)}
    (pc1 : Spec.Rsa.publicPrecompute (bs1 0) = some ws1) (pc2 : Spec.Rsa.publicPrecompute (bs2 0) = some ws2)
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => (PrivFnInput g bs1 s ∧ PreQ g bs1 pre preLen ws1 (entered s)) ∧
      (PrivFnInput g bs2 t ∧ PreQ g bs2 pre preLen ws2 (entered t)) ∧ s.sp = t.sp) (privCodeP v) (fun _ _ => True) :=
  codeWith_ct (privateBodyP_ct v pc1 pc2 nb eb)

theorem private_contract_correctP (v : CrtImpl) (s : State)
    (h : (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes).pre s) :
    ∃ tr t, Exec isa (privCodeP v) s tr t ∧ abiPreserved s t ∧
      (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes).post s t := by
  obtain ⟨hf, q, pc⟩ := private_contract_preP s h
  obtain ⟨tr, t, run, preserved, post⟩ := privateFnP_ok v s hf q pc
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact post

theorem private_contract_ctP (v : CrtImpl) :
    ConstantTime isa (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes).pre
      (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes).pub (privCodeP v) := by
  intro s t tr1 tr2 u w hs ht hp e1 e2
  obtain ⟨is, qs, pcs⟩ := private_contract_preP s hs
  obtain ⟨it, qt, pct⟩ := private_contract_preP t ht
  sig_pub [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, p3, a0, a1, a2, _, a4, a5, a6, a7, a8, _, a10, _, a12, _, a14, a15,
    a16, a17⟩ := hp
  have geometry : privateGeometry s = privateGeometry t := by
    simp only [privateGeometry, sp, p0, p2, p3, a0, a1, a2, a4, a5, a6, a7, a8, a10, a12, a14, a15]
  have keyLength : (List.map (fun x => BitVec.toNat x)
      (Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (s.gpr Reg.r2)) (s.gpr Reg.r3).toNat ++
        Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (stackArg s 0)) (stackArg s 1).toNat)).length =
      (List.map (fun x => BitVec.toNat x)
      (Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (t.gpr Reg.r2)) (t.gpr Reg.r3).toNat ++
        Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (stackArg t 0)) (stackArg t 1).toNat)).length := by
    simp only [List.length_map, List.length_append, Spec.Rsa.bytesAt, List.length_range, p3, a1]
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) (List.append_inj_left bytes keyLength)
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] at byteEq
  have both : privateBytes s 0 ++ privateBytes s 1 = privateBytes t 0 ++ privateBytes t 1 := byteEq
  have sameLength : (privateBytes s 0).length = (privateBytes t 0).length := by
    simp only [privateBytes, Spec.Rsa.bytesAt, List.length_map, List.length_range]
    change (s.gpr .r3).toNat = (t.gpr .r3).toNat
    rw [p3]
  have nb := List.append_inj_left both sameLength
  have eb := List.append_inj_right both sameLength
  rw [← geometry] at it qt
  rw [← a16, ← a17] at qt
  exact (privateFnP_ct v pcs pct nb eb s t tr1 tr2 u w ⟨⟨is, qs⟩, ⟨it, qt⟩, sp⟩ e1 e2).1

theorem privCodeP_stack (v : CrtImpl) : FrameStack.armStack (privCodeP v) ≤ stackBytes := by
  have := v.crtPStack
  have := v.pdStack
  simp only [privCodeP, codeP, codeWith, bodyP, checkP, checkWith, pcCopy,
    Impl.Bignum.Arm.copyBytes, tail, releaseTail, release, Impl.Bignum.Arm.compareBytes,
    FrameStack.armStack, List.length_cons, List.length_nil, frameBytes, stackBytes]
  omega_arith
end VG.Proof.Rsa.Arm
