module

public import VerifiedGarbage.Impl.Camellia.X86.CtrFinal
public import VerifiedGarbage.Proof.Camellia.CtrFinal
public import VerifiedGarbage.Proof.Camellia.CtrScratch
public import VerifiedGarbage.Proof.Camellia.X86.CtrVerified
public import VerifiedGarbage.Proof.AesCtr.X86.Final
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.ArgTaint
import VerifiedGarbage.Proof.Camellia.X86.CtrLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.MdStream.X86.Common
import VerifiedGarbage.Proof.Modes.X86.SeqFinal
import VerifiedGarbage.Proof.Modes.CtrFinal
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.Camellia.X86.CtrFinal
meta import VerifiedGarbage.Proof.Camellia.CtrFinal
meta import VerifiedGarbage.Proof.Camellia.CtrScratch
meta import VerifiedGarbage.Proof.Camellia.X86.CtrVerified
meta import VerifiedGarbage.Proof.AesCtr.X86.Final
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.X86.Spill
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.ArgTaint
meta import VerifiedGarbage.Proof.Camellia.X86.CtrLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.MdStream.X86.Common
meta import VerifiedGarbage.Proof.Modes.X86.SeqFinal
meta import VerifiedGarbage.Proof.Modes.CtrFinal
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86.RelCT

/-!
# Camellia-CTR of a message's last piece on x86 (32-bit)

`ctrFinal_framed`: `vg_camellia_ctr_final` (`Impl/Camellia/X86/CtrFinal.lean`)
meets `Spec.Camellia.ctrFinalContract`, from `Proof.Camellia.ctrFinalContractSk`
(`Proof.Camellia.ctrFinal_of_sk`).

The code is proven against `ctrFinalX86`, with a sixth stack argument `save`
of 32 bytes, for its caller's registers and a block of its own, its
arguments read only (`verified_wide`: the shared contract on the subkeys
with `save`, `finalScratchContract`, by `wide_implies`, from `wideX86`, which
has them writable), as a caller of `vg_camellia_ctr` (framed by its own working space on the stack,
`ctrFramed`), through its contract on the subkeys, `ctrContractSk`
(`ctrFramed_sk`; `CCall.callPre`, `calleeK_post`, `calleeK_pub`, from
`Sig.contract`'s form for arguments on the stack). It is AES-CTR's final
function's proof (`Proof/AesCtr/X86/Final.lean`) with Camellia's arguments:

* `setup_wp`, `whole_wp`: the registers saved, and the call on the
  `n = len / 16` whole blocks (`ctr_call`, `Whole`);
* `mid_wp`: if `u = len % 16` bytes are left, the block after the registers
  in `save` zeroed and the call on it (`tail_args_wp`, `tail_call_wp`), which
  leaves `CIPH_K(Tₙ₊₁)` there and `Tₙ₊₂` in `ctr`, and its first `u` bytes
  XORed into them (`Modes.X86.tailLoop_wp`, `xor_wp`); what is left before
  the registers are restored is `Done`;
* `end_wp`: the registers restored from `save`;
* `final_post`: `Done` gives `Spec.Ctr.CryptFinal`
  (`Proof.Modes.CtrFinal.cryptFinal_of`).

Every argument is reloaded from the stack, which nothing writes (`Pt`).
Constant time (`final_rel`): the blocks by the taint analysis from the
stack arguments (`argTaint`), the calls by the callee's constant time
(`RelCT.callWith`), whose public arguments, the pointers, `rounds` and the
number of blocks, agree in both runs. `ctrFinal_framed` runs the code with
`save` in a frame of 60 bytes (`Verified.stackScratchWiped`), zeroed on
return, the block included; with the 2796 bytes its calls use below it
(the callee's five arguments, its return address and its 2772 bytes), 2856
in all.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86.CtrFinal

open VG VG.X86
open VG.Spec.Aes (bytesAt)

/-- The code's contract, with the arguments on the stack `(schedule, rounds,
ctr, data, len, save)`, `save` of 32 bytes: the data and the counter block
as `Spec.Ctr.CryptFinal` says, by Camellia with the subkeys at `schedule`.
The code only reads its arguments (`wideX86` has them writable, as the
signature's contract does). -/
def ctrFinalX86 : Contract isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 272⟩
    let ctr : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let sv : Region := ⟨(arg s 5).setWidth 64, 32⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 2796, 2796⟩
    s.rd = [sched, args] ∧ s.wr = [ctr, data, sv] ∧
      sched.Disjoint ctr ∧ sched.Disjoint data ∧ sched.Disjoint sv ∧
      ctr.Disjoint data ∧ ctr.Disjoint sv ∧ ctr.Disjoint args ∧
      data.Disjoint sv ∧ data.Disjoint args ∧ sv.Disjoint args ∧
      ret.Disjoint ctr ∧ ret.Disjoint data ∧ ret.Disjoint sv ∧
      stack.Disjoint sched ∧ stack.Disjoint ctr ∧ stack.Disjoint data ∧ stack.Disjoint sv ∧
      (arg s 0).toNat + 272 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 32 ≤ 2 ^ 32 ∧
      2796 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
      ((arg s 1).toNat = 18 ∨ (arg s 1).toNat = 24)
  post s s' :=
    Spec.Ctr.CryptFinal (Spec.Camellia.cipher (Spec.Camellia.subkeysAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat))
      s.mem s'.mem ((arg s 2).setWidth 64) ((arg s 3).setWidth 64) (arg s 4).toNat
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

/-- `ctrFinalX86` with the argument slots writable, as the signature's
contract has them. -/
def wideX86 : Contract isa :=
  { ctrFinalX86 with
    pre := fun s =>
      let sched : Region := ⟨(arg s 0).setWidth 64, 272⟩
      let ctr : Region := ⟨(arg s 2).setWidth 64, 16⟩
      let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
      let sv : Region := ⟨(arg s 5).setWidth 64, 32⟩
      let args : Region := ⟨argAddr s 0, 24⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 2796, 2796⟩
      s.rd = [sched] ∧ s.wr = [ctr, data, sv, args] ∧
        sched.Disjoint ctr ∧ sched.Disjoint data ∧ sched.Disjoint sv ∧
        ctr.Disjoint data ∧ ctr.Disjoint sv ∧ ctr.Disjoint args ∧
        data.Disjoint sv ∧ data.Disjoint args ∧ sv.Disjoint args ∧
        ret.Disjoint ctr ∧ ret.Disjoint data ∧ ret.Disjoint sv ∧
        stack.Disjoint sched ∧ stack.Disjoint ctr ∧ stack.Disjoint data ∧ stack.Disjoint sv ∧
        (arg s 0).toNat + 272 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
        (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 32 ≤ 2 ^ 32 ∧
        2796 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
        ((arg s 1).toNat = 18 ∨ (arg s 1).toNat = 24) }

/-- The contract the frame needs: the shared one on the subkeys, with
`save`, 32 bytes, as a sixth argument, and 2796 bytes of stack (the callee's
five arguments, its return address and its own 2772 bytes). -/
abbrev finalScratchContract : Contract isa :=
  Sig.scratchContract X86.abi Spec.Camellia.ctrFinalSig "save" .u64 4 (Spec.Camellia.ctrFinalPre X86.abi.ptrBits)
    (Proof.Camellia.ctrFinalPostSk X86.abi.ptrBits) true 2796

/-- A state satisfying the precondition: the subkeys at `0x1000`, 18
rounds, the counter block at `0x2000`, no data at `0x3000` and `save` at
`0x4000`, as stack arguments at `0x8004`. -/
def finalSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 0x12
    else if a = 0x800d then 0x20 else if a = 0x8011 then 0x30 else if a = 0x8019 then 0x40 else 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 32⟩, ⟨0x8004, 24⟩]

theorem wide_implies : wideX86.Implies finalScratchContract := by
  have a0 : arg finalSat 0 = 0x1000 := by decide
  have a1 : arg finalSat 1 = 0x12 := by decide
  have a2 : arg finalSat 2 = 0x2000 := by decide
  have a3 : arg finalSat 3 = 0x3000 := by decide
  have a4 : arg finalSat 4 = 0 := by decide
  have a5 : arg finalSat 5 = 0x4000 := by decide
  have e : argAddr finalSat 0 = 0x8004 := by decide
  have esp : finalSat.gpr .esp = 0x8000 := rfl
  sig_implies [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Camellia.ctrFinalSig, Spec.Camellia.ctrFinalPre, Proof.Camellia.ctrFinalPostSk, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, wideX86, ctrFinalX86] [a0, a1, a2, a3, a4, a5, e, esp] using finalSat

/-- The regions `ctrFinalX86` gives: the arguments read only. -/
def narrowRd (s : State) : List Region := [⟨(arg s 0).setWidth 64, 272⟩, ⟨argAddr s 0, 24⟩]
def narrowWr (s : State) : List Region :=
  [⟨(arg s 2).setWidth 64, 16⟩, ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩, ⟨(arg s 5).setWidth 64, 32⟩]

theorem narrow_pre (s : State) (h : wideX86.pre s) : ctrFinalX86.pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  simp only [ctrFinalX86, narrowRd, narrowWr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial, h⟩

/-- `ctrFinalX86` gives `wideX86`. -/
theorem verified_wide {c : Prog isa} (h : ∀ s, ctrFinalX86.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧
      ctrFinalX86.post s s')
    (hct : ConstantTime isa ctrFinalX86.pre ctrFinalX86.pub c) : Verified X86.target c finalScratchContract := by
  have hsat := wide_implies.sat_left
  have narrowSat : ∃ s, ctrFinalX86.pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, narrow_pre s hs⟩
  apply Verified.of_implies _ wide_implies
  refine Verified.narrowTo (k := ctrFinalX86) (Verified.of_correct h hct (.refl narrowSat))
    narrowRd narrowWr narrow_pre ?_ ?_ (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp_all only [or_true, true_or]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp_all only [or_true, true_or]

/-! ## The callee -/

open VG.Impl.Camellia.X86 (ctrFramed ctrCall ctrFinalSave ctrFinalArgs ctrFinalTailArgs ctrFinalXorArgs
  ctrFinalRestore ctrFinalTail ctrFinal)

/-- `vg_camellia_ctr` meets its contract on the subkeys. -/
theorem ctrFramed_sk : Verified X86.target ctrFramed (Proof.Camellia.ctrContractSk X86.abi 2772) :=
  X86.Verified.stackScratchWiped (sig := Spec.Camellia.ctrSig) (nm := "scratch") (e := .u64)
    (n := 341) (pre := Spec.Camellia.ctrPre X86.abi.ptrBits) (post := Proof.Camellia.ctrPostSk X86.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 2756) Ctr.ctr_verified (by decide) (by lit_decide) (by lit_decide)
    (by decide) (Proof.Camellia.ctrPre_local _) (Proof.Camellia.ctrPost_local _)
    (Proof.Camellia.ctrPostOut_local _) (Ctr.frameSat_ctr _)

/-- The contract `vg_camellia_ctr` is called by. -/
abbrev calleeK : Contract isa := Proof.Camellia.ctrContractSk X86.abi 2772

abbrev ctrRegs : List Reg := [.esi, .ebx, .edx, .ecx, .eax]

theorem ctrRegs_esp : Reg.esp ∉ ctrRegs := by decide

theorem ctr_stack : stackUse ctrFramed = 2772 := by
  have h : stackUse Impl.Camellia.X86.ctr = 16 := by lit_decide
  simp only [ctrFramed, Impl.StackScratch.X86.withStackScratchWiped, Impl.StackScratch.X86.withStackScratch,
    stackUse, h, X86.frameBytes]
  decide

theorem ctr_nosp : NoSp ctrFramed := NoSp.of_all (by unfold ctrFramed; lit_decide)

theorem sw32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq; simp

theorem toNat_sw (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

/-- The bytes `[d, d + n)` of the `b` bytes below `E`, from their bottom. -/
theorem below_off {E : BitVec 32} {b d k : Nat} (hb : b ≤ E.toNat) (hk : k ≤ b) (hd : d = b - k) :
    ((E - BitVec.ofNat 32 k).setWidth 64) = (below E b).base + BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toNat_eq
  have := E.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [sub_toNat (by omega), sub_toNat hb]
  subst hd
  rw [Nat.mod_eq_of_lt (a := E.toNat - k) (by omega), Nat.mod_eq_of_lt (a := E.toNat - b) (by omega),
    Nat.mod_eq_of_lt (a := b - k) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem subkeysAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {R : Nat}
    (hR : R = 18 ∨ R = 24) (hd : ∀ r ∈ rs, (⟨p, 272⟩ : Region).Disjoint r) :
    Spec.Camellia.subkeysAt m' p R = Spec.Camellia.subkeysAt m p R :=
  Proof.Camellia.subkeysAt_congr (by rcases hR with rfl | rfl <;> decide)
    fun i hi => hf.bytes (R := ⟨p, 272⟩) hd (by show 272 ≤ 2 ^ 64; omega) hi

theorem one_disj {k : Region} {p : Addr} {n : Nat} (h : k.Disjoint ⟨p, n⟩) :
    ∀ r ∈ [k], (⟨p, n⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact h.symm

/-- What a call of `vg_camellia_ctr` needs: the subkeys at `W` with `R`
rounds, the counter block at `C` and `n` blocks at `D`, and 2796 bytes of
stack for the arguments, the return address and the callee's frames. -/
structure CCall (s : State) (W R C D : BitVec 32) (n : Nat) : Prop where
  eax : s.gpr .eax = W
  ecx : s.gpr .ecx = R
  edx : s.gpr .edx = C
  ebx : s.gpr .ebx = D
  esi : s.gpr .esi = BitVec.ofNat 32 n
  esp : 2796 ≤ (s.gpr .esp).toNat
  rounds : R.toNat = 18 ∨ R.toNat = 24
  wc : (⟨W.setWidth 64, 272⟩ : Region).Disjoint ⟨C.setWidth 64, 16⟩
  wd : (⟨W.setWidth 64, 272⟩ : Region).Disjoint ⟨D.setWidth 64, 16 * n⟩
  cd : (⟨C.setWidth 64, 16⟩ : Region).Disjoint ⟨D.setWidth 64, 16 * n⟩
  bw : (below (s.gpr .esp) 2796).Disjoint ⟨W.setWidth 64, 272⟩
  bc : (below (s.gpr .esp) 2796).Disjoint ⟨C.setWidth 64, 16⟩
  bd : (below (s.gpr .esp) 2796).Disjoint ⟨D.setWidth 64, 16 * n⟩
  fW : W.toNat + 272 ≤ 2 ^ 32
  fC : C.toNat + 16 ≤ 2 ^ 32
  fD : D.toNat + 16 * n ≤ 2 ^ 32
  reads : Covers [⟨W.setWidth 64, 272⟩] (s.rd ++ s.wr)
  writes : Covers [⟨C.setWidth 64, 16⟩, ⟨D.setWidth 64, 16 * n⟩] s.wr

/-- What a call of `vg_camellia_ctr` leaves. -/
structure CPost (s : State) (W R C D : BitVec 32) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C.setWidth 64, 16⟩, ⟨D.setWidth 64, 16 * n⟩, below (s.gpr .esp) 2796] s.mem s'.mem
  out : Spec.Cbc.blocksAt s'.mem (D.setWidth 64) n =
    Spec.Ctr.crypt (Spec.Camellia.cipher (Spec.Camellia.subkeysAt s.mem (W.setWidth 64) R.toNat))
      (bytesAt s.mem (C.setWidth 64) 16) (Spec.Cbc.blocksAt s.mem (D.setWidth 64) n)
  ctr : bytesAt s'.mem (C.setWidth 64) 16 = Spec.Ctr.next (bytesAt s.mem (C.setWidth 64) 16) n

abbrev calleeRd (W : BitVec 32) : List Region := [⟨W.setWidth 64, 272⟩]
abbrev calleeWr (E C D : BitVec 32) (n : Nat) : List Region :=
  [⟨C.setWidth 64, 16⟩, ⟨D.setWidth 64, n * 16⟩, below E 20]

namespace CCall
variable {s : State} {W R C D : BitVec 32} {n : Nat} (h : CCall s W R C D n)
include h

theorem fit : 4 * ctrRegs.length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem n_lt : n < 2 ^ 32 := by have := h.fD; omega

theorem args : arg (pushed ctrRegs s).callEntry 0 = W ∧ arg (pushed ctrRegs s).callEntry 1 = R ∧
    arg (pushed ctrRegs s).callEntry 2 = C ∧ arg (pushed ctrRegs s).callEntry 3 = D ∧
    arg (pushed ctrRegs s).callEntry 4 = BitVec.ofNat 32 n := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit ctrRegs_esp (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebx, h.esi]

theorem callPre : CallPre calleeK ctrRegs (calleeRd W) (calleeWr (s.gpr .esp) C D n) s := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := h.args
  have hn : (BitVec.ofNat 32 n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.n_lt]
  have hE := h.esp
  have := (s.gpr .esp).isLt
  have eA : argAddr (pushed ctrRegs s).callEntry 0 = (below (s.gpr .esp) 2796).base + BitVec.ofNat 64 2776 := by
    rw [callEntry_argAddr0]; exact below_off (by omega) (by decide) rfl
  have eB : (below (s.gpr .esp) 20) = ⟨(below (s.gpr .esp) 2796).base + BitVec.ofNat 64 2776, 20⟩ :=
    congrArg (fun x => (⟨x, 20⟩ : Region)) (below_off (by omega) (by decide) rfl)
  have e6 : s.gpr .esp - 4 - 4 - 4 - 4 - 4 - 4 = s.gpr .esp - BitVec.ofNat 32 24 := by
    simp only [BitVec.sub_sub]; rfl
  have eR : (s.gpr .esp - BitVec.ofNat 32 24).setWidth 64 =
      (below (s.gpr .esp) 2796).base + BitVec.ofNat 64 2772 :=
    below_off (by omega) (by decide) rfl
  have eS : (below (s.gpr .esp) 2796).base + BitVec.ofNat 64 2772 - 2772#64 = (below (s.gpr .esp) 2796).base :=
    BitVec.add_sub_cancel _ _
  have eN : (s.gpr .esp - BitVec.ofNat 32 24).toNat = (s.gpr .esp).toNat - 24 := sub_toNat (by omega)
  let B := (below (s.gpr .esp) 2796).base
  try rewrite [show (below (s.gpr .esp) 2796).base = B from rfl] at *
  have hb : below (s.gpr .esp) 2796 = ⟨B, 2796⟩ := rfl
  have sb {d k : Nat} (hd : d + k ≤ 2796) {r : Region} (hr : (below (s.gpr .esp) 2796).Disjoint r) :
      (⟨B + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    rw [hb] at hr; exact hr.sub_left (Offset.sub_base _ hd)
  have sb0 {r : Region} (hr : (below (s.gpr .esp) 2796).Disjoint r) : (⟨B, 2772⟩ : Region).Disjoint r := by
    rw [hb] at hr; exact hr.sub_left (Region.sub_prefix (by decide))
  have hwd := h.wd
  have hcd := h.cd
  have hbd := h.bd
  have hfD := h.fD
  rw [Nat.mul_comm] at hwd hcd hbd hfD
  refine ⟨?_, ?_, ?_⟩
  · sig_pre [calleeK, Proof.Camellia.ctrContractSk, Spec.Camellia.ctrSig, Spec.Camellia.ctrPre, X86.abi, argVal,
      ↓reduceIte, Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd,
      Nat.reduceMul, sw32, toNat_sw]
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, hn, eA, e6, eN, eR, eS]
    have r1 : (⟨B + BitVec.ofNat 64 2772, 4⟩ : Region).Disjoint ⟨B + BitVec.ofNat 64 2776, 20⟩ :=
      Offset.disjoint B (.inl (by decide)) (by omega) (by omega)
    have r2 : (⟨B, 2772⟩ : Region).Disjoint ⟨B + BitVec.ofNat 64 2776, 20⟩ :=
      Offset.base_disjoint B (by decide) (by omega)
    exact ⟨by omega, by omega, trivial, by rw [calleeWr, eB], h.wc, hwd, (sb (by decide) h.bw).symm, hcd,
      (sb (by decide) h.bc).symm, (sb (by decide) hbd).symm, sb (by decide) h.bw, sb (by decide) h.bc,
      sb (by decide) hbd, r1, sb0 h.bw, sb0 h.bc, sb0 hbd, r2, h.fW, h.fC, hfD, h.rounds⟩
  · intro a m ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a m ⟨_, List.mem_singleton_self _, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · obtain ⟨r', hr', hc'⟩ := h.writes a m ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
    · obtain ⟨r', hr', hc'⟩ := h.writes a m ⟨⟨D.setWidth 64, 16 * n⟩, by simp, by rwa [Nat.mul_comm]⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
  · intro a m ⟨r, hr, hcn⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.writes a m ⟨_, by simp, hcn⟩
      exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩
    · obtain ⟨r', hr', hc'⟩ := h.writes a m ⟨⟨D.setWidth 64, 16 * n⟩, by simp, by rwa [Nat.mul_comm]⟩
      exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩
    · exact ⟨_, List.mem_cons_self .., hcn⟩

end CCall

/-- `vg_camellia_ctr`'s postcondition. -/
theorem calleeK_post {s s' : State} (h : calleeK.post s s') (hR : (arg s 1).toNat = 18 ∨ (arg s 1).toNat = 24) :
    Spec.Cbc.blocksAt s'.mem ((arg s 3).setWidth 64) (arg s 4).toNat =
        Spec.Ctr.crypt (Spec.Camellia.cipher (Spec.Camellia.subkeysAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat))
          (bytesAt s.mem ((arg s 2).setWidth 64) 16) (Spec.Cbc.blocksAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat) ∧
      bytesAt s'.mem ((arg s 2).setWidth 64) 16 = Spec.Ctr.next (bytesAt s.mem ((arg s 2).setWidth 64) 16) (arg s 4).toNat := by
  sig_post [calleeK, Proof.Camellia.ctrContractSk, Proof.Camellia.ctrPostSk, Spec.Camellia.ctrSig, X86.abi, argVal,
    ↓reduceIte, Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul,
    sw32, toNat_sw] at h
  exact h hR

/-- Its public data, from the arguments. -/
theorem calleeK_pub {s₁ s₂ : State} (h : s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i) :
    calleeK.pub s₁ s₂ := by
  obtain ⟨a₁, a₂⟩ := h
  sig_pub [calleeK, Proof.Camellia.ctrContractSk, Proof.Camellia.ctrPostSk, Spec.Camellia.ctrSig, X86.abi, argVal,
    ↓reduceIte, Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul,
    sw32, toNat_sw]
  exact ⟨a₁, a₂ 0 (by decide), a₂ 1 (by decide), a₂ 2 (by decide), a₂ 3 (by decide), a₂ 4 (by decide)⟩

theorem ctr_call {s : State} {W R C D : BitVec 32} {n : Nat} (h : CCall s W R C D n) :
    WP isa ctrCall s (CPost s W R C D n) := by
  have hn : (BitVec.ofNat 32 n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.n_lt]
  unfold ctrCall
  refine WP.callWith (rs := ctrRegs) (k := calleeK) ctrFramed_sk.1 ctr_nosp (by simp) ctrRegs_esp
    (by rw [ctr_stack]; have := h.esp; simp only [List.length_cons, List.length_nil]; omega)
    h.callPre fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, a4⟩ := h.args
  rw [ctr_stack] at f'
  have fE := callEntry_frame h.fit ctrRegs_esp
  rw [show 4 * ctrRegs.length + 4 = 24 from rfl] at fE
  have fE' : Frame [below (s.gpr .esp) 2796] s.mem (pushed ctrRegs s).callEntry.mem :=
    fE.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, VG.X86.below_sub (by decide) h.esp⟩
  have hR := h.rounds
  obtain ⟨hdata, hctr⟩ := calleeK_post post (by simp only [arg_withRegions, a1]; exact hR)
  simp only [arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4, hn, m₂] at hdata hctr
  rw [Proof.Cmac.bytesAt_frame fE' (one_disj h.bc) (by decide), AesCfb.X86.blocksAt_frame' fE' (one_disj h.bd),
    subkeysAt_frame fE' hR (one_disj h.bw)] at hdata
  rw [Proof.Cmac.bytesAt_frame fE' (one_disj h.bc) (by decide)] at hctr
  refine ⟨rd', wr', cs', ?_, hdata, hctr⟩
  refine f'.sub fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨⟨D.setWidth 64, 16 * n⟩, by simp, by rw [Nat.mul_comm]; exact fun _ h => h⟩
  · exact ⟨below (s.gpr .esp) 2796, by simp, VG.X86.below_sub (by decide) h.esp⟩
  · exact ⟨below (s.gpr .esp) 2796, by simp, VG.X86.below_sub (by decide) h.esp⟩

/-- Calls of `vg_camellia_ctr` with the same arguments and stack pointer in
both runs are constant time. -/
theorem ctr_rel {P : State → State → Prop} {W R C D E : BitVec 32} {n : Nat}
    (h : ∀ s₁ s₂, P s₁ s₂ → CCall s₁ W R C D n ∧ CCall s₂ W R C D n ∧ s₁.gpr .esp = E ∧ s₂.gpr .esp = E) :
    RelCT isa P ctrCall fun _ _ => True := by
  unfold ctrCall
  refine RelCT.callWith (rs := ctrRegs) ctrFramed_sk.1 ctrFramed_sk.2.1 (calleeRd W) (calleeWr E C D n)
    fun s₁ s₂ hP => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hP
  have p₁ := h₁.callPre
  have p₂ := h₂.callPre
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, calleeK_pub ⟨?_, fun i hi => ?_⟩⟩
  · simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂]
  obtain ⟨a0, a1, a2, a3, a4⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3, b4⟩ := h₂.args
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]

theorem cipher_length (sk : Spec.Camellia.Subkeys) (b : List Byte) : (Spec.Camellia.cipher sk b).length = 16 := by
  simp [Spec.Camellia.cipher]

/-! ## The arguments, by name -/

open VG.Impl.CmacAes.X86 (argOp)
open VG.Impl.AesCfb.X86 (finalSaved tailTest)
open VG.Impl.AesCtr.X86 (zeroSlots)
open VG.Proof.CmacAes.X86 (wp_arg ofNat_and_self_beq)
open VG.Proof.MdStream.X86 (wp_mov wp_movi wp_andi wp_test wp_shr wp_sub wp_add wp_addi eval_e)

section
variable (s₀ : State)

abbrev fE : BitVec 32 := s₀.gpr .esp
abbrev fW : BitVec 32 := arg s₀ 0
abbrev fRr : BitVec 32 := arg s₀ 1
abbrev fR : Nat := (arg s₀ 1).toNat
abbrev fIv : BitVec 32 := arg s₀ 2
abbrev fD : BitVec 32 := arg s₀ 3
abbrev fL : Nat := (arg s₀ 4).toNat
abbrev fV : BitVec 32 := arg s₀ 5
/-- The whole blocks, the bytes after them, and where those start. -/
abbrev fN : Nat := fL s₀ / 16
abbrev fU : Nat := fL s₀ % 16
abbrev fT : BitVec 32 := fD s₀ + BitVec.ofNat 32 (16 * fN s₀)
abbrev fSch : Region := ⟨(fW s₀).setWidth 64, 272⟩
abbrev fIvR : Region := ⟨(fIv s₀).setWidth 64, 16⟩
abbrev fData : Region := ⟨(fD s₀).setWidth 64, fL s₀⟩
abbrev fBlk : Region := ⟨(fD s₀).setWidth 64, 16 * fN s₀⟩
abbrev fTail : Region := ⟨(fD s₀).setWidth 64 + BitVec.ofNat 64 (16 * fN s₀), fU s₀⟩
/-- The registers in `save`; all of `save`; the block after the registers,
as the code computes it and as a region. -/
abbrev fSv : Region := ⟨(fV s₀).setWidth 64, 16⟩
abbrev cSv : Region := ⟨(fV s₀).setWidth 64, 32⟩
abbrev cBk : BitVec 32 := fV s₀ + BitVec.ofNat 32 16
abbrev cBlk : Region := ⟨(fV s₀).setWidth 64 + BitVec.ofNat 64 16, 16⟩
abbrev fArgs : Region := ⟨argAddr s₀ 0, 24⟩
abbrev fRet : Region := ⟨(fE s₀).setWidth 64, 4⟩
abbrev fStk : Region := below (fE s₀) 2796
/-- The cipher, the counter block and the whole blocks on entry. -/
abbrev fCiph : Spec.Cbc.Cipher := Spec.Camellia.cipher (Spec.Camellia.subkeysAt s₀.mem ((fW s₀).setWidth 64) (fR s₀))
abbrev fIv0 : List Byte := bytesAt s₀.mem ((fIv s₀).setWidth 64) 16
abbrev fBlks : List (List Byte) := Spec.Cbc.blocksAt s₀.mem ((fD s₀).setWidth 64) (fN s₀)

/-- The memory once the registers are saved. -/
def svMem : Mem := Spill.saveMem s₀.mem ((fV s₀).setWidth 64 + BitVec.ofNat 64 ·) s₀.gpr finalSaved

/-- What the function writes. -/
abbrev cBig : List Region := [fIvR s₀, fData s₀, cSv s₀, fStk s₀]
/-- What the function writes after saving the registers, with the whole
blocks rather than the data; and with the data. -/
abbrev cW1 : List Region := [fIvR s₀, fBlk s₀, cBlk s₀, fStk s₀]
abbrev cW : List Region := [fIvR s₀, fData s₀, cBlk s₀, fStk s₀]

end

/-- The precondition, by name. -/
structure CPre (s₀ : State) : Prop where
  rd : s₀.rd = [fSch s₀, fArgs s₀]
  wr : s₀.wr = [fIvR s₀, fData s₀, cSv s₀]
  sch_iv : (fSch s₀).Disjoint (fIvR s₀)
  sch_data : (fSch s₀).Disjoint (fData s₀)
  sch_sv : (fSch s₀).Disjoint (cSv s₀)
  iv_data : (fIvR s₀).Disjoint (fData s₀)
  iv_sv : (fIvR s₀).Disjoint (cSv s₀)
  iv_args : (fIvR s₀).Disjoint (fArgs s₀)
  data_sv : (fData s₀).Disjoint (cSv s₀)
  data_args : (fData s₀).Disjoint (fArgs s₀)
  sv_args : (cSv s₀).Disjoint (fArgs s₀)
  ret_iv : (fRet s₀).Disjoint (fIvR s₀)
  ret_data : (fRet s₀).Disjoint (fData s₀)
  ret_sv : (fRet s₀).Disjoint (cSv s₀)
  stk_sch : (fStk s₀).Disjoint (fSch s₀)
  stk_iv : (fStk s₀).Disjoint (fIvR s₀)
  stk_data : (fStk s₀).Disjoint (fData s₀)
  stk_sv : (fStk s₀).Disjoint (cSv s₀)
  sch_fit : (fW s₀).toNat + 272 ≤ 2 ^ 32
  iv_fit : (fIv s₀).toNat + 16 ≤ 2 ^ 32
  data_fit : (fD s₀).toNat + fL s₀ ≤ 2 ^ 32
  sv_fit : (fV s₀).toNat + 32 ≤ 2 ^ 32
  espB : 2796 ≤ (fE s₀).toNat
  esp_fit : (fE s₀).toNat + 28 ≤ 2 ^ 32
  rounds : fR s₀ = 18 ∨ fR s₀ = 24

theorem stk_eq {s₀ : State} (h : 2796 ≤ (fE s₀).toNat) :
    fStk s₀ = ⟨(fE s₀).setWidth 64 - BitVec.ofNat 64 2796, 2796⟩ := by
  show (⟨(fE s₀ - BitVec.ofNat 32 2796).setWidth 64, 2796⟩ : Region) = _
  rw [Taint.sub_setWidth h]

theorem CPre.of {s₀ : State} (h : ctrFinalX86.pre s₀) : CPre s₀ := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25⟩ := h
  have e := stk_eq a23
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, e ▸ a15, e ▸ a16, e ▸ a17, e ▸ a18,
    a19, a20, a21, a22, a23, a24, a25⟩

/-! ## Addresses and regions -/

theorem sv16_sub (s₀ : State) : Region.Sub (fSv s₀) (cSv s₀) := Region.sub_prefix (by decide)
theorem blk_sv_sub (s₀ : State) : Region.Sub (cBlk s₀) (cSv s₀) := Offset.sub_base _ (by decide)
theorem sv_blk (s₀ : State) : (fSv s₀).Disjoint (cBlk s₀) := Offset.base_disjoint _ (Nat.le_refl _) (by decide)
theorem blk_sub (s₀ : State) : Region.Sub (fBlk s₀) (fData s₀) := Region.sub_prefix (Nat.mul_div_le _ _)
theorem tail_sub (s₀ : State) : Region.Sub (fTail s₀) (fData s₀) :=
  Offset.sub_base _ (by rw [Nat.div_add_mod])
theorem fU_lt (s₀ : State) : fU s₀ < 16 := Nat.mod_lt _ (by decide)

section
variable {s₀ : State} (hp : CPre s₀)
include hp

theorem CPre.cBk_addr : (cBk s₀).setWidth 64 = (cBlk s₀).base := addr_eq (by have := hp.sv_fit; omega)

theorem CPre.cBk_toNat : (cBk s₀).toNat = (fV s₀).toNat + 16 := by
  have := hp.sv_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16) (by decide), Nat.mod_eq_of_lt (by omega)]

theorem CPre.cBlk1 : (⟨(cBk s₀).setWidth 64, 16 * 1⟩ : Region) = cBlk s₀ := by rw [hp.cBk_addr]

theorem CPre.argA {i : Nat} (hi : i < 6) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  simp only [argAddr]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * i) from rfl,
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * 0) from rfl,
    addr_eq (by omega), addr_eq (by omega), Offset.add_add]

theorem CPre.arg_sub {i : Nat} (hi : i < 6) : Region.Sub ⟨argAddr s₀ i, 4⟩ (fArgs s₀) := by
  rw [hp.argA hi]; exact Offset.sub_base _ (by omega)

theorem CPre.arg_in {i : Nat} (hi : i < 6) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 := by
  refine ⟨fArgs s₀, by simp [hp.rd], ?_⟩
  rw [hp.argA hi]; exact Offset.contains_base _ (by omega) (by omega)

theorem CPre.args_stk : (fArgs s₀).Disjoint (fStk s₀) := by
  have : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  have e : argAddr s₀ 0 = (fE s₀).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
  rw [stk_eq hp.espB]
  show Region.Disjoint ⟨argAddr s₀ 0, 24⟩ _
  rw [e]; exact (Offset.disjoint_below_above _ (by decide)).symm

theorem CPre.ret_stk : (fRet s₀).Disjoint (fStk s₀) := by
  rw [stk_eq hp.espB]
  have := Offset.disjoint_below_above ((fE s₀).setWidth 64) (m := 2796) (a := 0) (l := 4) (by decide)
  rw [BitVec.add_zero] at this
  exact this.symm

/-- The stack arguments are unchanged where only `cBig` changes. -/
theorem CPre.arg_keep {m : Mem} (hf : Frame (cBig s₀) s₀.mem m) {i : Nat} (hi : i < 6) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.iv_args.symm.sub_left (hp.arg_sub hi)
    · exact hp.data_args.symm.sub_left (hp.arg_sub hi)
    · exact hp.sv_args.symm.sub_left (hp.arg_sub hi)
    · exact hp.args_stk.sub_left (hp.arg_sub hi)) (by decide)

/-- The return address is unchanged where only `cBig` changes. -/
theorem CPre.ret_keep {m : Mem} (hf : Frame (cBig s₀) s₀.mem m) :
    m.readW ((fE s₀).setWidth 64) 32 = s₀.mem.readW ((fE s₀).setWidth 64) 32 :=
  hf.readW (r := fRet s₀) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.ret_iv
    · exact hp.ret_data
    · exact hp.ret_sv
    · exact hp.ret_stk) (by decide)

/-- The subkeys are unchanged where only `cBig` changes. -/
theorem CPre.sched_keep {m : Mem} (hf : Frame (cBig s₀) s₀.mem m) :
    Spec.Camellia.subkeysAt m ((fW s₀).setWidth 64) (fR s₀) =
      Spec.Camellia.subkeysAt s₀.mem ((fW s₀).setWidth 64) (fR s₀) :=
  subkeysAt_frame hf hp.rounds fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.sch_iv
    · exact hp.sch_data
    · exact hp.sch_sv
    · exact hp.stk_sch.symm

theorem CPre.blk_fit : (fD s₀).toNat + 16 * fN s₀ ≤ 2 ^ 32 := by
  have := hp.data_fit; have := Nat.mul_div_le (fL s₀) 16; have : fN s₀ = fL s₀ / 16 := rfl; omega

theorem CPre.blk_tail : (fBlk s₀).Disjoint (fTail s₀) := by
  have := hp.data_fit
  have := Nat.div_add_mod (fL s₀) 16
  have : fN s₀ = fL s₀ / 16 := rfl
  have : fU s₀ = fL s₀ % 16 := rfl
  exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)

end

/-! ## Frames -/

/-- The save changes only `save`. -/
theorem svMem_frame (s₀ : State) : Frame [fSv s₀] s₀.mem (svMem s₀) :=
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp =>
    have : p.2 + 4 ≤ 16 := (show Spill.Fits 16 finalSaved by decide).1 p hp
    Offset.contains_base _ (by omega) (by omega)

theorem cW1_cW {s₀ : State} {m : Mem} (hf : Frame (cW1 s₀) (svMem s₀) m) : Frame (cW s₀) (svMem s₀) m :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨fData s₀, by simp, blk_sub s₀⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- Everything the function writes, from the save on. -/
theorem big_of {s₀ : State} {m : Mem} (hf : Frame (cW s₀) (svMem s₀) m) : Frame (cBig s₀) s₀.mem m :=
  ((svMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨cSv s₀, by simp, sv16_sub s₀⟩).trans
    (hf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨cSv s₀, by simp, blk_sv_sub s₀⟩
      · exact ⟨_, by simp, fun _ h => h⟩)

section
variable {s₀ : State} (hp : CPre s₀)
include hp

theorem CPre.sv_sched : Spec.Camellia.subkeysAt (svMem s₀) ((fW s₀).setWidth 64) (fR s₀) =
    Spec.Camellia.subkeysAt s₀.mem ((fW s₀).setWidth 64) (fR s₀) :=
  hp.sched_keep (big_of (Frame.refl _ _))

theorem CPre.sv_iv : bytesAt (svMem s₀) ((fIv s₀).setWidth 64) 16 = fIv0 s₀ :=
  Proof.Cmac.bytesAt_frame (svMem_frame s₀) (one_disj (hp.iv_sv.sub_right (sv16_sub s₀)).symm) (by decide)

theorem CPre.sv_blocks : Spec.Cbc.blocksAt (svMem s₀) ((fD s₀).setWidth 64) (fN s₀) = fBlks s₀ :=
  AesCfb.X86.blocksAt_frame' (svMem_frame s₀)
    (one_disj ((hp.data_sv.sub_left (blk_sub s₀)).sub_right (sv16_sub s₀)).symm)

end

/-! ## Saving the registers, and the arguments of the call on the whole blocks -/

theorem setup_eq : ctrFinalSave ++ ctrFinalArgs =
    .mov .eax (argOp 5) :: (Spill.saveCode .eax finalSaved ++ ctrFinalArgs) := rfl

theorem args_eq : ctrFinalArgs = [.mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .edx (argOp 2),
    .mov .ebx (argOp 3), .mov .esi (argOp 4), .shift .shr .esi 4] := rfl

/-- What saving the registers and setting up the arguments leaves. -/
structure Setup (s₀ s : State) : Prop where
  eax : s.gpr .eax = fW s₀
  ecx : s.gpr .ecx = fRr s₀
  edx : s.gpr .edx = fIv s₀
  ebx : s.gpr .ebx = fD s₀
  esi : s.gpr .esi = BitVec.ofNat 32 (fN s₀)
  esp : s.gpr .esp = fE s₀
  mem : s.mem = svMem s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem setup_wp {s₀ : State} (hp : CPre s₀) :
    WP isa (.block (ctrFinalSave ++ ctrFinalArgs)) s₀ (Setup s₀) := by
  rw [setup_eq]
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  have h₁ : s₁.gpr .eax = fV s₀ := u₁.gpr
  refine Spill.save_ofNat_ok finalSaved AesCfb.X86.finalSaved_fits
    (by rw [h₁]; have := hp.sv_fit; omega) (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb : p.2 + 4 ≤ 16 := AesCfb.X86.finalSaved_fits.1 p hp'
    rw [h₁, u₁.wr, hp.wr]
    exact ⟨cSv s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hm₂ : s₂.mem = svMem s₀ := by
    rw [u₂.mem, u₁.mem, h₁, svMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' =>
      u₁.other _ (AesCfb.X86.finalSaved_ne_eax p hp')
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [u₂.gpr, u₁.other _ (by decide)]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
  have big := big_of (s₀ := s₀) (Frame.refl _ (svMem s₀))
  have ak : ∀ i < 6, (svMem s₀).readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => hp.arg_keep big hi
  rw [args_eq]
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rw₂]; exact hp.arg_in (by decide))
    (by rw [hm₂]; exact ak 0 (by decide)) fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rw₂]; exact hp.arg_in (by decide))
    (by rw [u₃.mem, hm₂]; exact ak 1 (by decide)) fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rw₂]; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem, hm₂]; exact ak 2 (by decide)) fun s₅ u₅ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rw₂]; exact hp.arg_in (by decide))
    (by rw [u₅.mem, u₄.mem, u₃.mem, hm₂]; exact ak 3 (by decide)) fun s₆ u₆ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rw₂]; exact hp.arg_in (by decide))
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂]; exact ak 4 (by decide)) fun s₇ u₇ => ?_
  refine wp_shr (by decide) fun s₈ u₈ => ?_
  refine WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]
  · rw [u₈.gpr, u₇.gpr, AesCfb.X86.shr4]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), esp₂]
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂]
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-! ## The call on the whole blocks -/

theorem Setup.call {s₀ s : State} (hp : CPre s₀) (h : Setup s₀ s) :
    CCall s (fW s₀) (fRr s₀) (fIv s₀) (fD s₀) (fN s₀) where
  eax := h.eax
  ecx := h.ecx
  edx := h.edx
  ebx := h.ebx
  esi := h.esi
  esp := by rw [h.esp]; exact hp.espB
  rounds := hp.rounds
  wc := hp.sch_iv
  wd := hp.sch_data.sub_right (blk_sub s₀)
  cd := hp.iv_data.sub_right (blk_sub s₀)
  bw := by rw [h.esp]; exact hp.stk_sch
  bc := by rw [h.esp]; exact hp.stk_iv
  bd := by rw [h.esp]; exact hp.stk_data.sub_right (blk_sub s₀)
  fW := hp.sch_fit
  fC := hp.iv_fit
  fD := hp.blk_fit
  reads := by
    rw [h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨fSch s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨fIvR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨fData s₀, by simp, 0, by simp, by simpa using Nat.mul_div_le (fL s₀) 16⟩

/-- What the call on the whole blocks leaves. -/
structure Whole (s₀ s : State) : Prop where
  esp : s.gpr .esp = fE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [fIvR s₀, fBlk s₀, fStk s₀] (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem ((fD s₀).setWidth 64) (fN s₀) = Spec.Ctr.crypt (fCiph s₀) (fIv0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem ((fIv s₀).setWidth 64) 16 = Spec.Ctr.next (fIv0 s₀) (fN s₀)

theorem whole_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Setup s₀ s) : WP isa ctrCall s (Whole s₀) := by
  refine WP.mono (ctr_call (h.call hp)) fun s' c => ?_
  have f := c.frame
  rw [h.esp, h.mem] at f
  refine ⟨by rw [c.saved .esp (by simp [calleeSaved]), h.esp], by rw [c.rd, h.rd], by rw [c.wr, h.wr], f, ?_, ?_⟩
  · rw [c.out, h.mem, hp.sv_sched, hp.sv_iv, hp.sv_blocks]
  · rw [c.ctr, h.mem, hp.sv_iv]

theorem Whole.of_eq {s₀ s s' : State} (h : Whole s₀ s) (esp : s'.gpr .esp = s.gpr .esp)
    (mem : s'.mem = s.mem) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) : Whole s₀ s' :=
  ⟨by rw [esp, h.esp], by rw [rd, h.rd], by rw [wr, h.wr], by rw [mem]; exact h.frame,
    by rw [mem]; exact h.blocks, by rw [mem]; exact h.ctr⟩

theorem whole_cW1 {s₀ s : State} (h : Whole s₀ s) : Frame (cW1 s₀) (svMem s₀) s.mem :=
  h.frame.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp [h]

theorem whole_cW {s₀ s : State} (h : Whole s₀ s) : Frame (cW s₀) (svMem s₀) s.mem :=
  cW1_cW (whole_cW1 h)

/-- The test sets ZF if no bytes are left after the whole blocks. -/
theorem test_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Whole s₀ s) :
    WP isa (.block tailTest) s fun s' => Whole s₀ s' ∧ s'.zf = some (decide (fU s₀ = 0)) := by
  have big := big_of (whole_cW h)
  rw [AesCfb.X86.tailTest_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [h.rd, h.wr]; exact hp.arg_in (by decide)) (hp.arg_keep big (by decide))
    fun s₁ u₁ => wp_andi fun s₂ u₂ => wp_test fun s₃ f₃ z₃ => WP.block_nil
      ⟨h.of_eq (by rw [f₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)])
        (by rw [f₃.mem, u₂.mem, u₁.mem]) (by rw [f₃.rd, u₂.rd, u₁.rd]) (by rw [f₃.wr, u₂.wr, u₁.wr]), ?_⟩
  have := fU_lt s₀
  rw [z₃, u₂.gpr, u₁.gpr, AesCfb.X86.and15, ofNat_and_self_beq (by omega)]

/-! ## The partial last block: its arguments -/

theorem tailArgs_eq : ctrFinalTailArgs = .mov .eax (argOp 5) :: .mov .ecx (.imm 0) ::
    (Spill.saveCode .eax zeroSlots ++ ([.mov .ebx (.reg .eax), .alu .add .ebx (.imm 16), .mov .eax (argOp 0),
      .mov .ecx (argOp 1), .mov .edx (argOp 2), .mov .esi (.imm 1)] : List Instr)) := rfl

/-- What zeroing the block and setting up the arguments leaves. -/
structure TArgs (s₀ s : State) : Prop where
  eax : s.gpr .eax = fW s₀
  ecx : s.gpr .ecx = fRr s₀
  edx : s.gpr .edx = fIv s₀
  ebx : s.gpr .ebx = cBk s₀
  esi : s.gpr .esi = 1
  esp : s.gpr .esp = fE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW1 s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem ((fD s₀).setWidth 64) (fN s₀) = Spec.Ctr.crypt (fCiph s₀) (fIv0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem ((fIv s₀).setWidth 64) 16 = Spec.Ctr.next (fIv0 s₀) (fN s₀)
  zero : bytesAt s.mem (cBlk s₀).base 16 = List.replicate 16 0

theorem tail_args_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Whole s₀ s) :
    WP isa (.block ctrFinalTailArgs) s (TArgs s₀) := by
  have f₁ := whole_cW1 h
  have big := big_of (cW1_cW f₁)
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have ak : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => hp.arg_keep big hi
  rw [tailArgs_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (ak 5 (by decide)) fun s₁ u₁ => ?_
  refine wp_movi fun s₂ u₂ => ?_
  have eax₂ : s₂.gpr .eax = fV s₀ := by rw [u₂.other _ (by decide), u₁.gpr]
  refine Spill.save_ofNat_ok zeroSlots AesCtr.X86.zeroSlots_fits (by rw [eax₂]; exact hp.sv_fit)
    (fun p hp' => ?_) fun s₃ u₃ => ?_
  · have hb : p.2 + 4 ≤ 32 := AesCtr.X86.zeroSlots_fits.1 p hp'
    rw [eax₂, u₂.wr, u₁.wr, h.wr, hp.wr]
    exact ⟨cSv s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hm₃ : s₃.mem = Spill.saveMem s.mem ((fV s₀).setWidth 64 + BitVec.ofNat 64 ·) s₂.gpr zeroSlots := by
    rw [u₃.mem, eax₂, u₂.mem, u₁.mem]
  have fz : Frame [cBlk s₀] s.mem s₃.mem := by
    rw [hm₃]
    exact Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp' => by
      simp only [zeroSlots, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl
      · exact Offset.contains _ (by decide) (by decide) (by decide)
      · exact Offset.contains _ (by decide) (by decide) (by decide)
      · exact Offset.contains _ (by decide) (by decide) (by decide)
      · exact Offset.contains _ (by decide) (by decide) (by decide)
  have g₃ : s₃.gpr = s₂.gpr := u₃.gpr
  have esp₃ : s₃.gpr .esp = fE s₀ := by rw [g₃, u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
  have rw₃ : s₃.rd ++ s₃.wr = s₀.rd ++ s₀.wr := by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]
  have ak₃ : ∀ i < 6, s₃.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by
    rw [fz.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.sv_args.symm.sub_left (hp.arg_sub hi)).sub_right (blk_sv_sub s₀)) (by decide)]
    exact ak i hi
  refine wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₅.other _ (by decide), u₄.other _ (by decide), esp₃])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, rw₃]; exact hp.arg_in (by decide))
    (by rw [u₅.mem, u₄.mem]; exact ak₃ 0 (by decide)) fun s₆ u₆ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), esp₃])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, rw₃]; exact hp.arg_in (by decide))
    (by rw [u₆.mem, u₅.mem, u₄.mem]; exact ak₃ 1 (by decide)) fun s₇ u₇ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), esp₃])
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, rw₃]; exact hp.arg_in (by decide))
    (by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]; exact ak₃ 2 (by decide)) fun s₈ u₈ => wp_movi fun s₉ u₉ => ?_
  have m₉ : s₉.mem = s₃.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have blkZ : ∀ r ∈ [cBlk s₀], (fBlk s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (hp.data_sv.sub_left (blk_sub s₀)).sub_right (blk_sv_sub s₀)
  have ivZ : ∀ r ∈ [cBlk s₀], (fIvR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_sv.sub_right (blk_sv_sub s₀)
  refine WP.block_nil ⟨?_, ?_, ?_, ?_, u₉.gpr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr]
  · rw [u₉.other _ (by decide), u₈.gpr]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.gpr, u₄.gpr, g₃, eax₂]; rfl
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), esp₃]
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [m₉]; exact f₁.trans (fz.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  · rw [m₉, AesCfb.X86.blocksAt_frame' fz blkZ]; exact h.blocks
  · rw [m₉, Proof.Cmac.bytesAt_frame fz ivZ (by decide)]; exact h.ctr
  · rw [m₉, hm₃]
    exact AesCtr.X86.zero_bytes _ _ (by rw [u₂.gpr])

/-! ## The partial last block: the call -/

theorem TArgs.call {s₀ s : State} (hp : CPre s₀) (h : TArgs s₀ s) :
    CCall s (fW s₀) (fRr s₀) (fIv s₀) (cBk s₀) 1 where
  eax := h.eax
  ecx := h.ecx
  edx := h.edx
  ebx := h.ebx
  esi := h.esi
  esp := by rw [h.esp]; exact hp.espB
  rounds := hp.rounds
  wc := hp.sch_iv
  wd := by rw [hp.cBlk1]; exact hp.sch_sv.sub_right (blk_sv_sub s₀)
  cd := by rw [hp.cBlk1]; exact hp.iv_sv.sub_right (blk_sv_sub s₀)
  bw := by rw [h.esp]; exact hp.stk_sch
  bc := by rw [h.esp]; exact hp.stk_iv
  bd := by rw [hp.cBlk1, h.esp]; exact hp.stk_sv.sub_right (blk_sv_sub s₀)
  fW := hp.sch_fit
  fC := hp.iv_fit
  fD := by rw [hp.cBk_toNat]; have := hp.sv_fit; omega
  reads := by
    rw [h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨fSch s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hp.cBlk1, h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨fIvR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨cSv s₀, by simp, 16, by simp, by simp⟩

/-- What the call on the block leaves. -/
structure TCall (s₀ s : State) : Prop where
  esp : s.gpr .esp = fE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW1 s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem ((fD s₀).setWidth 64) (fN s₀) = Spec.Ctr.crypt (fCiph s₀) (fIv0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem ((fIv s₀).setWidth 64) 16 = Spec.Ctr.next (Spec.Ctr.next (fIv0 s₀) (fN s₀)) 1
  out : bytesAt s.mem (cBlk s₀).base 16 = fCiph s₀ (Spec.Ctr.next (fIv0 s₀) (fN s₀))

theorem tail_call_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : TArgs s₀ s) : WP isa ctrCall s (TCall s₀) := by
  have big := big_of (cW1_cW h.frame)
  refine WP.mono (ctr_call (h.call hp)) fun s' c => ?_
  have f := c.frame
  rw [hp.cBlk1, h.esp] at f
  have out := c.out
  rw [hp.cBk_addr, hp.sched_keep big, h.ctr] at out
  refine ⟨by rw [c.saved .esp (by simp [calleeSaved]), h.esp], by rw [c.rd, h.rd], by rw [c.wr, h.wr],
    h.frame.trans (f.mono fun r hr => ?_), ?_, by rw [c.ctr, h.ctr],
    Modes.CtrFinal.bytesAt_of_blocksAt_one (cipher_length _) h.zero out⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp [h]
  · rw [AesCfb.X86.blocksAt_frame' f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.iv_data.symm.sub_left (blk_sub s₀)
      · exact (hp.data_sv.sub_left (blk_sub s₀)).sub_right (blk_sv_sub s₀)
      · exact hp.stk_data.symm.sub_left (blk_sub s₀)]
    exact h.blocks

/-! ## The partial last block: the bytes XORed -/

theorem xorArgs_eq : ctrFinalXorArgs = [.mov .ebx (argOp 5), .alu .add .ebx (.imm 16), .mov .esi (argOp 3),
    .mov .ebp (argOp 4), .mov .eax (.reg .ebp), .alu .and .ebp (.imm 15), .alu .sub .eax (.reg .ebp),
    .alu .add .esi (.reg .eax)] := rfl

/-- The tail loop's operands. -/
structure XArgs (s₀ s : State) : Prop where
  call : TCall s₀ s
  ebx : s.gpr .ebx = cBk s₀
  esi : s.gpr .esi = fT s₀
  ebp : s.gpr .ebp = BitVec.ofNat 32 (fU s₀)

theorem xorArgs_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : TCall s₀ s) :
    WP isa (.block ctrFinalXorArgs) s (XArgs s₀) := by
  have big := big_of (cW1_cW h.frame)
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have ak : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => hp.arg_keep big hi
  rw [xorArgs_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (ak 5 (by decide)) fun s₁ u₁ => ?_
  refine wp_addi fun s₁' u₁' => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁'.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₁'.rd, u₁'.wr, u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₁'.mem, u₁.mem]; exact ak 3 (by decide)) fun s₂ u₂ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₂.other _ (by decide), u₁'.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₂.rd, u₂.wr, u₁'.rd, u₁'.wr, u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₂.mem, u₁'.mem, u₁.mem]; exact ak 4 (by decide)) fun s₃ u₃ => ?_
  refine wp_mov fun s₄ u₄ => wp_andi fun s₅ u₅ => wp_sub fun s₆ u₆ _ => wp_add fun s₇ u₇ => WP.block_nil ?_
  have e₅ : s₅.gpr .ebp = BitVec.ofNat 32 (fU s₀) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, AesCfb.X86.and15]
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁'.mem, u₁.mem]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁'.other _ (by decide), u₁.other _ (by decide), h.esp]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁'.rd, u₁.rd, h.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁'.wr, u₁.wr, h.wr]
  · rw [m₇]; exact h.frame
  · rw [m₇]; exact h.blocks
  · rw [m₇]; exact h.ctr
  · rw [m₇]; exact h.out
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁'.gpr, u₁.gpr]; rfl
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, e₅, AesCfb.X86.sub_mod16]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), e₅]

/-- What the function leaves before restoring the registers. -/
structure Done (s₀ s : State) : Prop where
  esp : s.gpr .esp = fE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem ((fD s₀).setWidth 64) (fN s₀) = Spec.Ctr.crypt (fCiph s₀) (fIv0 s₀) (fBlks s₀)
  tail : ∀ q < fU s₀, s.mem ((fTail s₀).base + BitVec.ofNat 64 q) = s₀.mem ((fTail s₀).base + BitVec.ofNat 64 q) ^^^
    (fCiph s₀ (Spec.Ctr.next (fIv0 s₀) (fN s₀))).getD q 0
  ctr : bytesAt s.mem ((fIv s₀).setWidth 64) 16 =
    Spec.Ctr.next (fIv0 s₀) (if fU s₀ = 0 then fN s₀ else fN s₀ + 1)

theorem done_of_zero {s₀ s : State} (h : Whole s₀ s) (hu : fU s₀ = 0) : Done s₀ s :=
  ⟨h.esp, h.rd, h.wr, whole_cW h, h.blocks, fun q hq => absurd hq (by omega), by
    rw [ite_eq_left hu, h.ctr]⟩

theorem CPre.tail_addr {s₀ : State} (hp : CPre s₀) (hu : fU s₀ ≠ 0) : (fT s₀).setWidth 64 = (fTail s₀).base := by
  have := hp.data_fit
  have := Nat.div_add_mod (fL s₀) 16
  have : fN s₀ = fL s₀ / 16 := rfl
  have : fU s₀ = fL s₀ % 16 := rfl
  exact addr_eq (by omega)

theorem CPre.toNat_tail {s₀ : State} (hp : CPre s₀) (hu : fU s₀ ≠ 0) : (fT s₀).toNat = (fD s₀).toNat + 16 * fN s₀ := by
  have := hp.data_fit
  have := Nat.div_add_mod (fL s₀) 16
  have : fN s₀ = fL s₀ / 16 := rfl
  have : fU s₀ = fL s₀ % 16 := rfl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * fN s₀) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem xor_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : XArgs s₀ s) (hu : fU s₀ ≠ 0) :
    WP isa (.loop (.block Impl.Modes.X86.tailByte) .ne) s (Done s₀) := by
  have hU := fU_lt s₀
  have hT := hp.toNat_tail hu
  have eT := hp.tail_addr hu
  have hL := Nat.div_add_mod (fL s₀) 16
  have hDw := hp.data_fit
  have hVw := hp.sv_fit
  have hB := hp.cBk_toNat
  have eB := hp.cBk_addr
  have eN : fN s₀ = fL s₀ / 16 := rfl
  have eU : fU s₀ = fL s₀ % 16 := rfl
  have hc := h.call
  have xp : Modes.X86.XPre s (cBk s₀) (fT s₀) (fU s₀) := {
    pos := by omega
    fitK := by omega
    fitR := by rw [hT]; omega
    disj := by
      rw [eT, eB]
      exact ((((hp.data_sv.sub_left (tail_sub s₀)).sub_right (blk_sv_sub s₀)).sub_right
        (Region.sub_prefix (by omega)))).symm
    rdK := fun q hq => by
      rw [hc.rd, hc.wr, hp.rd, hp.wr, eB]
      refine ⟨cSv s₀, by simp, ?_⟩
      rw [Offset.add_add]
      exact Offset.contains_base _ (by omega) (by omega)
    wrR := fun q hq => by
      rw [hc.wr, hp.wr, eT]
      refine ⟨fData s₀, by simp, ?_⟩
      rw [show (fTail s₀).base + BitVec.ofNat 64 q = (fD s₀).setWidth 64 + BitVec.ofNat 64 (16 * fN s₀ + q) from
        Offset.add_add _ _ _]
      exact Offset.contains_base _ (by omega) (by omega) }
  have x0 : Modes.X86.XInv s (cBk s₀) (fT s₀) (fU s₀) 0 s := {
    ebx := by rw [h.ebx]; exact (BitVec.add_zero _).symm
    esi := by rw [h.esi]; exact (BitVec.add_zero _).symm
    ebp := by rw [h.ebp, Nat.sub_zero]
    lt := by omega
    data := fun q _ => by rw [ite_eq_right (Nat.not_lt_zero q)]
    frame := Frame.refl _ _
    rd := rfl
    wr := rfl
    syms := rfl
    gpr := fun _ _ _ _ _ _ => rfl }
  refine WP.mono (Modes.X86.tailLoop_wp xp x0) fun s' d => ?_
  have fT' : Frame [fTail s₀] s.mem s'.mem := by have := d.frame; rw [eT] at this; exact this
  have tailD : ∀ r ∈ cW1 s₀, (fTail s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hp.iv_data.sub_right (tail_sub s₀)).symm
    · exact hp.blk_tail.symm
    · exact (hp.data_sv.sub_left (tail_sub s₀)).sub_right (blk_sv_sub s₀)
    · exact (hp.stk_data.sub_right (tail_sub s₀)).symm
  have tailS : ∀ r ∈ [fSv s₀], (fTail s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.data_sv.sub_left (tail_sub s₀)).sub_right (sv16_sub s₀)
  have hlen : (fTail s₀).len ≤ 2 ^ 64 := by show fU s₀ ≤ 2 ^ 64; omega
  refine ⟨by rw [d.gpr .esp (by decide) (by decide) (by decide) (by decide) (by decide), hc.esp],
    by rw [d.rd, hc.rd], by rw [d.wr, hc.wr], ?_, ?_, fun q hq => ?_, ?_⟩
  · exact (cW1_cW hc.frame).trans (fT'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨fData s₀, by simp, tail_sub s₀⟩)
  · rw [AesCfb.X86.blocksAt_frame' fT' fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.blk_tail]
    exact hc.blocks
  · have := d.data q hq
    rw [eT, eB] at this
    rw [this, hc.frame.bytes tailD hlen hq, (svMem_frame s₀).bytes tailS hlen hq,
      MdStream.X86.bytesAt_getD hc.out (show q < 16 by omega)]
  · rw [ite_eq_right hu, Proof.Cmac.bytesAt_frame fT' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_data.sub_right (tail_sub s₀))
      (by decide), hc.ctr, ← Proof.AesCtr.next_add]

theorem mid_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Whole s₀ s) (hz : s.zf = some (decide (fU s₀ = 0))) :
    WP isa (.ite .e (.block []) ctrFinalTail) s (Done s₀) := by
  have ev : isa.eval .e s = some (decide (fU s₀ = 0)) := by
    show VG.X86.eval .e s = _; rw [VG.Proof.MdStream.X86.eval_e, hz]
  by_cases hu : fU s₀ = 0
  · exact WP.ite true (by rw [ev, decide_eq_true hu]) (fun _ => WP.block_nil (done_of_zero h hu))
      (fun h => by cases h)
  · refine WP.ite false (by rw [ev, decide_eq_false hu]) (fun h => by cases h) fun _ => ?_
    exact WP.seq (WP.mono (tail_args_wp hp h) fun _ h₁ =>
      WP.seq (WP.mono (tail_call_wp hp h₁) fun _ h₂ =>
        WP.seq (WP.mono (xorArgs_wp hp h₂) fun _ h₃ => xor_wp hp h₃ hu)))

/-! ## Restoring the registers -/

theorem restore_eq : ctrFinalRestore = .mov .eax (argOp 5) :: (Spill.restoreCode .eax finalSaved ++ []) := rfl

theorem end_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Done s₀ s) :
    WP isa (.block ctrFinalRestore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem := by
  have big := big_of h.frame
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have hs : Spill.Saved s.mem ((fV s₀).setWidth 64 + BitVec.ofNat 64 ·) s₀.gpr finalSaved :=
    (Spill.saveMem_saved_ofNat s₀.mem _ s₀.gpr AesCfb.X86.finalSaved_fits (by decide)).of_frame h.frame
      (fun p hp' => Offset.contains_base _ (AesCfb.X86.finalSaved_fits.1 p hp')
        (by have := AesCfb.X86.finalSaved_fits.1 p hp'; omega))
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (hp.iv_sv.sub_right (sv16_sub s₀)).symm
        · exact (hp.data_sv.sub_right (sv16_sub s₀)).symm
        · exact sv_blk s₀
        · exact (hp.stk_sv.sub_right (sv16_sub s₀)).symm
  rw [restore_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hp.arg_keep big (by decide))
    fun s₁ u₁ => ?_
  refine Spill.restore_ofNat_ok finalSaved AesCfb.X86.finalSaved_fits
    (by rw [u₁.gpr]; have h32 : (arg s₀ 5).toNat + 32 ≤ 2 ^ 32 := hp.sv_fit; omega) AesCfb.X86.finalSaved_ne_eax
    (fun p hp' => ?_) (by rw [u₁.gpr, u₁.mem]; exact hs) fun s₂ r₂ => WP.block_nil ?_
  · have := AesCfb.X86.finalSaved_fits.1 p hp'
    rw [u₁.gpr, u₁.rd, u₁.wr, hrw, hp.rd, hp.wr]
    exact ⟨cSv s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine ⟨⟨r₂.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), h.esp]), ?_⟩, by rw [r₂.mem, u₁.mem]⟩
  rw [r₂.mem, u₁.mem]; exact hp.ret_keep big

/-! ## The whole function -/

theorem final_wp {s₀ : State} (hp : CPre s₀) :
    WP isa ctrFinal s₀ fun s' => abiPreserved s₀ s' ∧ ∃ s₁, Done s₀ s₁ ∧ s'.mem = s₁.mem := by
  refine WP.seq (WP.mono (setup_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (whole_wp hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (test_wp hp h₂) fun s₃ ⟨h₃, z₃⟩ => ?_)
  refine WP.seq (WP.mono (mid_wp hp h₃ z₃) fun s₄ h₄ => ?_)
  exact WP.mono (end_wp hp h₄) fun _ ⟨g, m⟩ => ⟨g, s₄, h₄, m⟩

/-- `Spec.Ctr.CryptFinal`, from what the function leaves. -/
theorem final_post {s₀ s₁ s' : State} (h : Done s₀ s₁) (hm : s'.mem = s₁.mem) : ctrFinalX86.post s₀ s' := by
  show Spec.Ctr.CryptFinal (fCiph s₀) s₀.mem s'.mem ((fIv s₀).setWidth 64) ((fD s₀).setWidth 64) (fL s₀)
  exact Modes.CtrFinal.cryptFinal_of (cipher_length _) (by rw [hm]; exact h.blocks)
    (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.ctr)

theorem final_correct (s : State) (hs : ctrFinalX86.pre s) :
    ∃ t s', Exec isa ctrFinal s t s' ∧ abiPreserved s s' ∧ ctrFinalX86.post s s' := by
  obtain ⟨t, s', he, hg, s₁, h₁, hm⟩ := final_wp (CPre.of hs)
  exact ⟨t, s', he, hg, final_post h₁ hm⟩

/-! ## Constant time -/

/-- What every state between the blocks keeps: the stack pointer, the
writable regions and the stack arguments. -/
structure Pt (s₀ s : State) : Prop where
  esp : s.gpr .esp = fE s₀
  wr : s.wr = s₀.wr
  args : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i

theorem CPre.argsOut {s₀ : State} (hp : CPre s₀) {s : State} (h : Pt s₀ s) : ArgsOut 6 s := by
  have hs := hp.esp_fit
  refine ⟨by rw [h.esp]; omega, ?_⟩
  rw [h.wr, hp.wr, h.esp]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact Taint.frame_disjoint (n := 24) (by omega) hp.ret_iv hp.iv_args.symm
  · exact Taint.frame_disjoint (n := 24) (by omega) hp.ret_data hp.data_args.symm
  · exact Taint.frame_disjoint (n := 24) (by omega) hp.ret_sv hp.sv_args.symm

/-- Two runs agree on `esp`, the stack arguments and the registers `rs`. -/
theorem Pt.agree {s₀ s₀' : State} (hq : ctrFinalX86.pub s₀ s₀') (hp : CPre s₀) (hp' : CPre s₀')
    {rs : List Reg} {s₁ s₂ : State} (h₁ : Pt s₀ s₁) (h₂ : Pt s₀' s₂) (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.X86.Taint.Agree (argTaint rs (4 + 4 * 6)) s₁ s₂ :=
  agree_argTaint hr (by rw [h₁.esp, h₂.esp, fE, fE, hq.1]) (hp.argsOut h₁) (hp'.argsOut h₂)
    fun i hi => by
      rw [AesCfb.X86.arg_cur h₁.esp (h₁.args i hi), AesCfb.X86.arg_cur h₂.esp (h₂.args i hi), hq.2 i hi]

theorem whole_pt {s₀ s : State} (hp : CPre s₀) (h : Whole s₀ s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (big_of (whole_cW h)) hi⟩

theorem TArgs.pt {s₀ s : State} (hp : CPre s₀) (h : TArgs s₀ s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (big_of (cW1_cW h.frame)) hi⟩

theorem TCall.pt {s₀ s : State} (hp : CPre s₀) (h : TCall s₀ s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (big_of (cW1_cW h.frame)) hi⟩

theorem Done.pt {s₀ s : State} (hp : CPre s₀) (h : Done s₀ s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (big_of h.frame) hi⟩

theorem setup_taint : ∃ h, (taint.check (argTaint [] (4 + 4 * 6)) (.block (ctrFinalSave ++ ctrFinalArgs)) h).isSome =
    true := ⟨_, by taint_decide⟩

theorem test_taint : ∃ h, (taint.check (argTaint [] (4 + 4 * 6)) (.block tailTest) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tailArgs_taint : ∃ h, (taint.check (argTaint [] (4 + 4 * 6)) (.block ctrFinalTailArgs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem xor_taint : ∃ h, (taint.check (argTaint [] (4 + 4 * 6))
    (.seq (.block ctrFinalXorArgs) (.loop (.block Impl.Modes.X86.tailByte) .ne)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (taint.check (argTaint [] (4 + 4 * 6)) (.block ctrFinalRestore) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem final_rel {s₀ s₀' : State} (h0 : ctrFinalX86.pre s₀) (h0' : ctrFinalX86.pre s₀')
    (hq : ctrFinalX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') ctrFinal fun _ _ => True := by
  have hp := CPre.of h0
  have hp' := CPre.of h0'
  have qE : fE s₀ = fE s₀' := hq.1
  have qA : ∀ i < 6, arg s₀ i = arg s₀' i := hq.2
  have qW : fW s₀ = fW s₀' := qA 0 (by decide)
  have qR : fRr s₀ = fRr s₀' := qA 1 (by decide)
  have qIv : fIv s₀ = fIv s₀' := qA 2 (by decide)
  have qL : fL s₀ = fL s₀' := by simp only [fL, qA 4 (by decide)]
  have qD : fD s₀ = fD s₀' := qA 3 (by decide)
  have qV : fV s₀ = fV s₀' := qA 5 (by decide)
  have qU : fU s₀ = fU s₀' := by simp only [fU, qL]
  have qN : fN s₀ = fN s₀' := by simp only [fN, qL]
  have qB : cBk s₀ = cBk s₀' := by simp only [cBk, qV]
  have pt₀ : ∀ {t : State}, Pt t t := ⟨rfl, rfl, fun _ _ => rfl⟩
  -- The registers saved and the arguments of the first call.
  obtain ⟨_, t₁⟩ := setup_taint
  have r₁ := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact Pt.agree (rs := []) hq hp hp' pt₀ pt₀ fun r hr => by simp at hr) t₁).wp
    (F₁ := Setup s₀) (F₂ := Setup s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨setup_wp hp, setup_wp hp'⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  -- The whole blocks.
  have c₂ := ctr_rel (P := fun a b => Setup s₀ a ∧ Setup s₀' b) (E := fE s₀) fun a b ⟨ha, hb⟩ => by
    have cb := hb.call hp'
    rw [← qW, ← qR, ← qIv, ← qD, ← qN] at cb
    exact ⟨ha.call hp, cb, ha.esp, hb.esp.trans qE.symm⟩
  have r₂ : RelCT isa (fun a b => Setup s₀ a ∧ Setup s₀' b) ctrCall (fun a b => Whole s₀ a ∧ Whole s₀' b) :=
    (RelCT.wp (c := ctrCall) (F₁ := Whole s₀) (F₂ := Whole s₀') c₂
      fun a b h => ⟨whole_wp hp h.1, whole_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  -- The test.
  obtain ⟨_, t₃⟩ := test_taint
  have r₃ := ((RelCT.taint (A := taint) (P := fun a b => Whole s₀ a ∧ Whole s₀' b) _
    (fun a b h => Pt.agree (rs := []) hq hp hp' (whole_pt hp h.1) (whole_pt hp' h.2) fun r hr => by simp at hr)
      t₃).wp
    (F₁ := fun (s : State) => Whole s₀ s ∧ s.zf = some (decide (fU s₀ = 0)))
    (F₂ := fun (s : State) => Whole s₀' s ∧ s.zf = some (decide (fU s₀' = 0)))
    fun a b h => ⟨test_wp hp h.1, test_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  -- The partial last block.
  obtain ⟨_, t₄⟩ := tailArgs_taint
  obtain ⟨_, t₅⟩ := xor_taint
  have tail (hu : fU s₀ ≠ 0) :
      RelCT isa (fun a b => Whole s₀ a ∧ Whole s₀' b) ctrFinalTail fun a b => Done s₀ a ∧ Done s₀' b := by
    have hu' : fU s₀' ≠ 0 := qU ▸ hu
    have a₄ := ((RelCT.taint (A := taint) (P := fun a b => Whole s₀ a ∧ Whole s₀' b) _
      (fun a b h => Pt.agree (rs := []) hq hp hp' (whole_pt hp h.1) (whole_pt hp' h.2) fun r hr => by simp at hr)
        t₄).wp
      (F₁ := TArgs s₀) (F₂ := TArgs s₀')
      fun a b h => ⟨tail_args_wp hp h.1, tail_args_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
    have c₅ := ctr_rel (P := fun a b => TArgs s₀ a ∧ TArgs s₀' b) (E := fE s₀) fun a b ⟨ha, hb⟩ => by
      have cb := hb.call hp'
      rw [← qW, ← qR, ← qIv, ← qB] at cb
      exact ⟨ha.call hp, cb, ha.esp, hb.esp.trans qE.symm⟩
    have a₅ : RelCT isa (fun a b => TArgs s₀ a ∧ TArgs s₀' b) ctrCall (fun a b => TCall s₀ a ∧ TCall s₀' b) :=
      (RelCT.wp (c := ctrCall) (F₁ := TCall s₀) (F₂ := TCall s₀') c₅
        fun a b h => ⟨tail_call_wp hp h.1, tail_call_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
    have a₆ := ((RelCT.taint (A := taint) (P := fun a b => TCall s₀ a ∧ TCall s₀' b) _
      (fun a b h => Pt.agree (rs := []) hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by simp at hr) t₅).wp
      (F₁ := Done s₀) (F₂ := Done s₀')
      fun a b h => ⟨WP.seq (WP.mono (xorArgs_wp hp h.1) fun _ h₃ => xor_wp hp h₃ hu),
        WP.seq (WP.mono (xorArgs_wp hp' h.2) fun _ h₃ => xor_wp hp' h₃ hu')⟩).mono
          (fun _ _ h => h) fun _ _ h => h.2
    exact a₄.seq (a₅.seq a₆)
  have r₄ : RelCT isa (fun a b => (Whole s₀ a ∧ a.zf = some (decide (fU s₀ = 0))) ∧
      (Whole s₀' b ∧ b.zf = some (decide (fU s₀' = 0))))
      (.ite .e (.block []) ctrFinalTail) (fun a b => Done s₀ a ∧ Done s₀' b) := by
    refine RelCT.ite (fun a b h => ?_) ?_ ?_
    · show a.zf = b.zf; rw [h.1.2, h.2.2, qU]
    · refine RelCT.block_nil fun a b h => ?_
      have h0 : fU s₀ = 0 := by
        have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this; simpa using this
      exact ⟨done_of_zero h.1.1.1 h0, done_of_zero h.1.2.1 (qU ▸ h0)⟩
    · refine (RelCT.exists_ fun (hu : fU s₀ ≠ 0) => tail hu).mono
        (fun a b h => ⟨?_, h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this; simpa using this
  -- The registers restored.
  obtain ⟨_, t₆⟩ := restore_taint
  have r₅ := RelCT.taint (A := taint) (P := fun a b => Done s₀ a ∧ Done s₀' b) _
    (fun a b h => Pt.agree (rs := []) hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by simp at hr) t₆
  exact r₁.seq (r₂.seq (r₃.seq (r₄.seq r₅)))

theorem final_ct : ConstantTime isa ctrFinalX86.pre ctrFinalX86.pub ctrFinal :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (final_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## The code's properties -/

theorem ctrFinal_noSp : ctrFinal.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [ctrFinal, ctrCall, ctrFinalTail, Code.allInstrs, AesCfb.X86.all_of_noSp ctr_nosp]
  decide

theorem ctrFinal_stack : stackUse ctrFinal ≤ 2796 := by
  simp only [ctrFinal, ctrCall, ctrFinalTail, stackUse, ctr_stack]
  decide

theorem ctrFinal_verified : Verified X86.target ctrFinal finalScratchContract :=
  verified_wide final_correct final_ct

/-! ## With `save` on the stack

The final function has five argument slots, so `save` is its sixth argument:
it runs its code in a frame of 60 bytes (`withStackScratchWiped 60 5 8`): the
word standing for the return address, a copy of the five arguments, `save`'s
address, and `save`'s 32 bytes (the registers, then the block that held the
last output block), which it zeroes before returning. The code's calls use
2796 bytes below it, so 2856 in all. -/

private theorem bytesAt_congr' {m₁ m₂ : Mem} {p : Addr} {k : Nat}
    (h : ∀ i < k, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m₂ p k = Spec.Aes.bytesAt m₁ p k := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- `ctrFinalPre` reads no memory. -/
theorem ctrFinalPre_local (pb : Nat) : ∀ vs m₁ m₂, vs.length = (Spec.Camellia.ctrFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Camellia.ctrFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Camellia.ctrFinalSig.words pb) (Spec.Camellia.ctrFinalPre pb) vs m₁ →
      Curry.apply (Spec.Camellia.ctrFinalSig.words pb) (Spec.Camellia.ctrFinalPre pb) vs m₂ := by
  intro vs m₁ m₂ hlen _ h
  match vs, hlen with
  | [_, _, _, _, _], _ => exact h

/-- `ctrFinalPostSk` reads the memory on entry only within the buffers. -/
theorem ctrFinalPost_local (pb : Nat) : ∀ vs m₁ m₂ m' r, vs.length = (Spec.Camellia.ctrFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Camellia.ctrFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Camellia.ctrFinalSig.words pb) (Proof.Camellia.ctrFinalPostSk pb) vs m₁ m' r →
      Curry.apply (Spec.Camellia.ctrFinalSig.words pb) (Proof.Camellia.ctrFinalPostSk pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  match vs, hlen with
  | [k, rounds, ctr, data, len], _ =>
    simp only [Spec.Camellia.ctrFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hs := Proof.Camellia.agree_of hb.1
    have hc := Proof.Camellia.agree_of hb.2.1
    have hd := Proof.Camellia.agree_of hb.2.2
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (Proof.Camellia.ctrFinalPostSk pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (Proof.Camellia.ctrFinalPostSk pb) _ m₂ m' r
    dsimp only [Curry.apply, Proof.Camellia.ctrFinalPostSk, ArgWord.ofRaw, Spec.Ctr.CryptFinal] at h ⊢
    have := Nat.mod_le len.toNat (2 ^ pb)
    intro hR
    rw [Proof.Camellia.subkeysAt_congr (by rcases hR with h | h <;> rw [h] <;> decide) fun i hi => hs i hi,
      bytesAt_congr' hc, bytesAt_congr' fun i hi => hd i (by rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h hR

theorem frameSat_pre : ∃ s, (Proof.Camellia.ctrFinalContractSk X86.abi 2856).pre s := by
  implies_sat [Proof.Camellia.ctrFinalContractSk, Spec.Camellia.ctrFinalSig, Spec.Camellia.ctrFinalPre, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] [Fb.frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using Fb.frameSat

theorem ctrFinal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 60 5 8 ctrFinal)
      (Spec.Camellia.ctrFinalContract X86.abi 2856) :=
  Proof.Camellia.ctrFinal_of_sk <|
  X86.Verified.stackScratchWiped (sig := Spec.Camellia.ctrFinalSig) (nm := "save") (e := .u64) (n := 4)
    (pre := Spec.Camellia.ctrFinalPre X86.abi.ptrBits) (post := Proof.Camellia.ctrFinalPostSk X86.abi.ptrBits)
    (wa := true) (stack := 2796) (bytes := 60) (words := 8) ctrFinal_verified (by decide) ctrFinal_noSp
    ctrFinal_stack (by decide) (ctrFinalPre_local _) (ctrFinalPost_local _)
    (Proof.Camellia.ctrFinalPostOut_local _) frameSat_pre

theorem ctrFinal_framed_spSafe :
    (Impl.StackScratch.X86.withStackScratchWiped 60 5 8 ctrFinal).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by lit_decide)

end VG.Proof.Camellia.X86.CtrFinal
