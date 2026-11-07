module

public import VerifiedGarbage.Impl.Camellia.X86_64.CtrFinal
public import VerifiedGarbage.Proof.Camellia.CtrFinal
public import VerifiedGarbage.Proof.Camellia.CtrScratch
public import VerifiedGarbage.Proof.Camellia.X86_64.CtrVerified
public import VerifiedGarbage.Proof.AesCfb.X86_64.Final
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.X86_64.Spill
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.AesCtr.X86_64.Final
import VerifiedGarbage.Proof.AesCtr.X86_64.CT
import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit
import VerifiedGarbage.Proof.Modes.CtrFinal
import VerifiedGarbage.Proof.Modes.X86_64.FbFinal
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Impl.Camellia.X86_64.CtrFinal
meta import VerifiedGarbage.Proof.Camellia.CtrFinal
meta import VerifiedGarbage.Proof.Camellia.CtrScratch
meta import VerifiedGarbage.Proof.Camellia.X86_64.CtrVerified
meta import VerifiedGarbage.Proof.AesCfb.X86_64.Final
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.X86_64.Spill
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.AesCtr.X86_64.Final
meta import VerifiedGarbage.Proof.AesCtr.X86_64.CT
meta import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Modes.CtrFinal
meta import VerifiedGarbage.Proof.Modes.X86_64.FbFinal
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Reduce
meta import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe

/-!
# Camellia-CTR of a message's last piece on x86-64

`ctrFinal_framed`: `vg_camellia_ctr_final` (`Impl/Camellia/X86_64/CtrFinal.lean`)
meets `Spec.Camellia.ctrFinalContract`, from `Proof.Camellia.ctrFinalContractSk`
(`Proof.Camellia.ctrFinal_of_sk`).

The code is proven against `ctrFinalX86_64`, with a sixth argument `save` of
64 bytes in `r9` (`ctrFinal_implies`: the shared contract with it), as a
caller of `vg_camellia_ctr` (framed by its own working space on the stack,
`ctrFramed`), through its contract on the subkeys, `ctrContractSk`
(`ctrFramed_sk`; `callee_pre`, `callee_post`, `callee_pub`, from
`Sig.contract`'s form for arguments in registers):

* `setup_wp`, `whole_wp`: the registers saved in `save`, whose address is
  kept in `r15`, and the call on the `n = len / 16` whole blocks (`KWhole`);
* `mid_wp`: if `u = len % 16` bytes are left, the block after the registers
  in `save` zeroed and the call on it (`tail_args_wp`, `tail_call_wp`), which
  leaves `CIPH_K(Tₙ₊₁)` there and `Tₙ₊₂` in `ctr`, and its first `u` bytes
  XORed into them (`Modes.X86_64.xorLoop_wp`, `tail_xor_wp`); what is left
  before the registers are restored is `KDone`;
* `end_wp`: the registers restored;
* `final_post`: `KDone` gives `Spec.Ctr.CryptFinal`
  (`Proof.Modes.CtrFinal.cryptFinal_of`).

Constant time (`final_rel`): the blocks by the taint analysis, the calls by
the callee's constant time (`RelCT.callEx`), whose public arguments agree.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.X86_64.RegUpd
open VG.Impl.Camellia.X86_64 (ctrFramed ctrFinalMoves ctrFinalSetup ctrFinalLoad ctrFinalTailMoves
  ctrFinalTailArgs ctrFinalTail ctrFinal)
open VG.Impl.AesCfb.X86_64 (finalSave finalRestore finalSaved)
open VG.Impl.AesCtr.X86_64 (zeroSlots tailKey)
open VG.Proof.AesCfb.X86_64 (fW fR fIv fD fL fN fU fT fData fBlk fTail fSp)

/-- The code's contract, with the arguments `(schedule = rdi, rounds = rsi,
ctr = rdx, data = rcx, len = r8, save = r9)`, `save` of 64 bytes: the data
and the counter block as `Spec.Ctr.CryptFinal` says, by Camellia with the
subkeys at `schedule`. -/
def ctrFinalX86_64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 272⟩
    let ctr : Region := ⟨s.gpr .rdx, 16⟩
    let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let sv : Region := ⟨s.gpr .r9, 64⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 3296
    3296 ≤ (s.gpr .rsp).toNat ∧ s.rd = [sched] ∧ s.wr = [ctr, data, sv] ∧
      sched.Disjoint ctr ∧ sched.Disjoint data ∧ sched.Disjoint sv ∧ ctr.Disjoint data ∧ ctr.Disjoint sv ∧
      data.Disjoint sv ∧
      ret.Disjoint sched ∧ ret.Disjoint ctr ∧ ret.Disjoint data ∧ ret.Disjoint sv ∧
      stack.Disjoint sched ∧ stack.Disjoint ctr ∧ stack.Disjoint data ∧ stack.Disjoint sv ∧
      (s.gpr .rdi).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + 64 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 18 ∨ (s.gpr .rsi).toNat = 24)
  post s s' :=
    Spec.Ctr.CryptFinal (Spec.Camellia.cipher (Spec.Camellia.subkeysAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat))
      s.mem s'.mem (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8).toNat
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .rsp = s₂.gpr .rsp

/-- The contract the frame needs: the shared one on the subkeys, with `save`,
64 bytes, as a sixth argument, and 3296 bytes of stack (the return address of
`vg_camellia_ctr`, and its frame and calls). -/
abbrev ctrFinalScratchContract : Contract isa :=
  Sig.scratchContract X86_64.abi Spec.Camellia.ctrFinalSig "save" .u64 8
    (Spec.Camellia.ctrFinalPre X86_64.abi.ptrBits) (Proof.Camellia.ctrFinalPostSk X86_64.abi.ptrBits) true 3296

/-- A state satisfying the precondition (no data, 18 rounds). -/
def ctrFinalSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 18 | .rdx => 0x2000 | .rcx => 0x3000 | .r9 => 0x4000 | .rsp => 0x8000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 64⟩]

theorem ctrFinal_implies : ctrFinalX86_64.Implies ctrFinalScratchContract := by
  sig_implies [ctrFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Camellia.ctrFinalSig, Spec.Camellia.ctrFinalPre, Proof.Camellia.ctrFinalPostSk, ctrFinalX86_64,
    X86_64.abi, X86_64.argRegs] [ctrFinalSat] using ctrFinalSat

/-! ## The callee -/

/-- `vg_camellia_ctr` meets its contract on the subkeys. -/
theorem ctrFramed_sk : Verified X86_64.target ctrFramed (Proof.Camellia.ctrContractSk X86_64.abi 3288) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Camellia.ctrSig) (nm := "scratch") (e := .u64)
    (n := 409) (pre := Spec.Camellia.ctrPre X86_64.abi.ptrBits)
    (post := Proof.Camellia.ctrPostSk X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3280) (by rw [← Proof.Camellia.ctrScratchContract_eq]; exact ctr_verified)
    (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide) (by decide) (Proof.Camellia.ctrPostOut_local _) ctrFrameSat_pre

theorem ctrFramed_spSafe : SpSafe ctrFramed := SpSafe.of_all (Code.all_of_allInstrs (by lit_decide))

theorem ctrFramed_depth : ctrFramed.x86_64Depth = 3288 := by lit_decide

/-- The callee's contract at a call. -/
abbrev calleeK : Contract isa := Proof.Camellia.ctrContractSk X86_64.abi 3288

theorem callee_args {s : State} {W C D : Addr} {R n : Nat} (hrdi : s.gpr .rdi = W)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 R) (hrdx : s.gpr .rdx = C) (hrcx : s.gpr .rcx = D)
    (hr8 : s.gpr .r8 = BitVec.ofNat 64 n) (rd wr : List Region) :
    regArgs Spec.Camellia.ctrSig (s.callEntry.withRegions rd wr) = [W, BitVec.ofNat 64 R, C, D, BitVec.ofNat 64 n] := by
  simp only [regArgs, State.withRegions_gpr, show (Spec.Camellia.ctrSig.words X86_64.abi.ptrBits).length = 5 from rfl,
    X86_64.argRegs, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), hrdi, hrsi, hrdx, hrcx, hr8]

theorem callee_bufs (W C D : Addr) {R n : Nat} (hn : n < 2 ^ 64) :
    Sig.bufs Spec.Camellia.ctrSig.params [W, BitVec.ofNat 64 R, C, D, BitVec.ofNat 64 n] =
      [(⟨W, 272⟩, false), (⟨C, 16⟩, true), (⟨D, 16 * n⟩, true)] := by
  simp [Spec.Camellia.ctrSig, Sig.bufs, Elem.size, Nat.mod_eq_of_lt hn, Nat.mul_comm]

theorem callee_pre {s : State} {W C D : Addr} {R n : Nat} (hrdi : s.gpr .rdi = W)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 R) (hrdx : s.gpr .rdx = C) (hrcx : s.gpr .rcx = D)
    (hr8 : s.gpr .r8 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) (hR : R = 18 ∨ R = 24)
    (hsp : 3296 ≤ (s.gpr .rsp).toNat)
    (dWC : (⟨W, 272⟩ : Region).Disjoint ⟨C, 16⟩) (dWD : (⟨W, 272⟩ : Region).Disjoint ⟨D, 16 * n⟩)
    (dCD : (⟨C, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩)
    (hstk : ∀ r ∈ ([⟨W, 272⟩, ⟨C, 16⟩, ⟨D, 16 * n⟩] : List Region), (below (s.gpr .rsp) 3296).Disjoint r)
    (fW : W.toNat + 272 ≤ 2 ^ 64) (fC : C.toNat + 16 ≤ 2 ^ 64) (fD : D.toNat + 16 * n ≤ 2 ^ 64) :
    calleeK.pre (s.callEntry.withRegions [⟨W, 272⟩] [⟨C, 16⟩, ⟨D, 16 * n⟩]) := by
  unfold calleeK Proof.Camellia.ctrContractSk
  rw [pre_regs (by decide) (by decide), callee_args hrdi hrsi hrdx hrcx hr8, callee_bufs W C D hn]
  have hsp8 : (s.gpr .rsp - 8).toNat = (s.gpr .rsp).toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; rfl
  have hret : Region.Sub ⟨s.gpr .rsp - 8, 8⟩ (below (s.gpr .rsp) 3296) :=
    Offset.sub_below _ (by decide) (by decide)
  have hcal : Region.Sub (below (s.gpr .rsp - 8) 3288) (below (s.gpr .rsp) 3296) := below_callee _ 3288
  refine ⟨.inr (by rw [State.withRegions_gpr, State.callEntry_rsp, hsp8]; omega), rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, Bool.true_or, Bool.false_or, forall_const, and_true]
    exact ⟨⟨dWC, dWD⟩, dCD, fun _ h => h.elim⟩
  · simp only [State.withRegions_gpr, State.callEntry_rsp]
    intro r hr a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rw [stackBelow_pos _ (by decide)] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rcases ha with rfl | rfl | rfl
    · exact (hstk _ (by simp)).sub_left hret
    · exact (hstk _ (by simp)).sub_left hret
    · exact (hstk _ (by simp)).sub_left hret
    · exact (hstk _ (by simp)).sub_left hcal
    · exact (hstk _ (by simp)).sub_left hcal
    · exact (hstk _ (by simp)).sub_left hcal
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> with_reducible assumption
  · show (BitVec.ofNat 64 R).toNat = 18 ∨ (BitVec.ofNat 64 R).toNat = 24
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hR

theorem callee_post {s s₂ : State} {W C D : Addr} {R n : Nat} (hrdi : s.gpr .rdi = W)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 R) (hrdx : s.gpr .rdx = C) (hrcx : s.gpr .rcx = D)
    (hr8 : s.gpr .r8 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) (hR : R = 18 ∨ R = 24) {rd wr : List Region}
    (h : calleeK.post (s.callEntry.withRegions rd wr) s₂) :
    Spec.Cbc.blocksAt s₂.mem D n = Spec.Ctr.crypt (Spec.Camellia.cipher (Spec.Camellia.subkeysAt s.callEntry.mem W R))
        (bytesAt s.callEntry.mem C 16) (Spec.Cbc.blocksAt s.callEntry.mem D n) ∧
      bytesAt s₂.mem C 16 = Spec.Ctr.next (bytesAt s.callEntry.mem C 16) n := by
  unfold calleeK Proof.Camellia.ctrContractSk at h
  rw [post_regs (by decide), callee_args hrdi hrsi hrdx hrcx hr8] at h
  change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64]
    (Proof.Camellia.ctrPostSk 64) _ _ _ _ at h
  dsimp only [Curry.apply, Proof.Camellia.ctrPostSk, ArgWord.ofRaw] at h
  have eN : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  simp only [BitVec.setWidth_eq, eN, State.withRegions_mem] at h
  rcases hR with rfl | rfl
  · exact h (.inl rfl)
  · exact h (.inr rfl)

theorem callee_pub {s₁ s₂ : State} {W C D : Addr} {R n : Nat} (h₁ : s₁.gpr .rdi = W)
    (h₂ : s₁.gpr .rsi = BitVec.ofNat 64 R) (h₃ : s₁.gpr .rdx = C) (h₄ : s₁.gpr .rcx = D)
    (h₅ : s₁.gpr .r8 = BitVec.ofNat 64 n) (g₁ : s₂.gpr .rdi = W)
    (g₂ : s₂.gpr .rsi = BitVec.ofNat 64 R) (g₃ : s₂.gpr .rdx = C) (g₄ : s₂.gpr .rcx = D)
    (g₅ : s₂.gpr .r8 = BitVec.ofNat 64 n) (hsp : s₁.gpr .rsp = s₂.gpr .rsp) (rd₁ wr₁ rd₂ wr₂ : List Region) :
    calleeK.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) := by
  unfold calleeK Proof.Camellia.ctrContractSk
  rw [pub_regs (by decide) (by decide), callee_args h₁ h₂ h₃ h₄ h₅, callee_args g₁ g₂ g₃ g₄ g₅]
  refine ⟨?_, fun _ _ => rfl⟩
  simp only [State.withRegions_gpr, State.callEntry_rsp, hsp]

/-! ## The arguments, by name -/

section
variable (s₀ : State)

/-- `save`. -/
abbrev kV : Addr := s₀.gpr .r9
abbrev kSch : Region := ⟨fW s₀, 272⟩
abbrev kIv : Region := ⟨fIv s₀, 16⟩
abbrev kSv : Region := ⟨kV s₀, 64⟩
/-- The block after the registers in `save`. -/
abbrev kBk : Addr := kV s₀ + BitVec.ofNat 64 48
abbrev kBlk : Region := ⟨kBk s₀, 16⟩
/-- The stack the calls use. -/
abbrev kStk : Region := below (fSp s₀) 3296
/-- The registers' values once `save` is in `rax`, and the memory once they
are saved. -/
abbrev kG : Reg → BitVec 64 := (s₀.setReg .rax (kV s₀)).gpr
abbrev kSvMem : Mem := Spill.saveMem s₀.mem (kV s₀) (kG s₀) finalSaved
/-- The cipher, the counter block and the whole blocks on entry. -/
abbrev kCiph : Spec.Cbc.Cipher := Spec.Camellia.cipher (Spec.Camellia.subkeysAt s₀.mem (fW s₀) (fR s₀))
abbrev kT : List Byte := bytesAt s₀.mem (fIv s₀) 16
abbrev kBlks : List (List Byte) := Spec.Cbc.blocksAt s₀.mem (fD s₀) (fN s₀)

/-- What the function writes after saving the registers, with the whole
blocks rather than the data; and with the data. -/
abbrev kW1 : List Region := [kIv s₀, fBlk s₀, kBlk s₀, kStk s₀]
abbrev kW : List Region := [kIv s₀, fData s₀, kBlk s₀, kStk s₀]
/-- What the function writes. -/
abbrev kBig : List Region := [kIv s₀, fData s₀, kSv s₀, kStk s₀]

end

/-- The precondition, by name. -/
structure KPre (s₀ : State) : Prop where
  sp : 3296 ≤ (fSp s₀).toNat
  rd : s₀.rd = [kSch s₀]
  wr : s₀.wr = [kIv s₀, fData s₀, kSv s₀]
  sch_iv : (kSch s₀).Disjoint (kIv s₀)
  sch_data : (kSch s₀).Disjoint (fData s₀)
  sch_sv : (kSch s₀).Disjoint (kSv s₀)
  iv_data : (kIv s₀).Disjoint (fData s₀)
  iv_sv : (kIv s₀).Disjoint (kSv s₀)
  data_sv : (fData s₀).Disjoint (kSv s₀)
  ret_sch : (⟨fSp s₀, 8⟩ : Region).Disjoint (kSch s₀)
  ret_iv : (⟨fSp s₀, 8⟩ : Region).Disjoint (kIv s₀)
  ret_data : (⟨fSp s₀, 8⟩ : Region).Disjoint (fData s₀)
  ret_sv : (⟨fSp s₀, 8⟩ : Region).Disjoint (kSv s₀)
  stk_sch : (kStk s₀).Disjoint (kSch s₀)
  stk_iv : (kStk s₀).Disjoint (kIv s₀)
  stk_data : (kStk s₀).Disjoint (fData s₀)
  stk_sv : (kStk s₀).Disjoint (kSv s₀)
  sch_wrap : (fW s₀).toNat + 272 ≤ 2 ^ 64
  iv_wrap : (fIv s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (fD s₀).toNat + fL s₀ ≤ 2 ^ 64
  sv_wrap : (kV s₀).toNat + 64 ≤ 2 ^ 64
  rounds : fR s₀ = 18 ∨ fR s₀ = 24

theorem KPre.of {s₀ : State} (h : ctrFinalX86_64.pre s₀) : KPre s₀ :=
  let ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22⟩ := h
  ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22⟩

/-! ## Regions and frames -/

theorem blk_sv_sub (s₀ : State) : Region.Sub (kBlk s₀) (kSv s₀) := Offset.sub_base _ (by decide)
theorem blk_sub (s₀ : State) : Region.Sub (fBlk s₀) (fData s₀) := AesCfb.X86_64.blk_sub s₀
theorem tail_sub (s₀ : State) : Region.Sub (fTail s₀) (fData s₀) := AesCfb.X86_64.tail_sub s₀

theorem svMem_frame (s₀ : State) : Frame [kSv s₀] s₀.mem (kSvMem s₀) :=
  Spill.saveMem_frame_base _ _ _ finalSaved (by decide) (by decide)

theorem kW1_kW {s₀ : State} {m : Mem} (hf : Frame (kW1 s₀) (kSvMem s₀) m) : Frame (kW s₀) (kSvMem s₀) m :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨fData s₀, by simp, blk_sub s₀⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem big_of {s₀ : State} {m : Mem} (hf : Frame (kW s₀) (kSvMem s₀) m) : Frame (kBig s₀) s₀.mem m :=
  ((svMem_frame s₀).mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans
    (hf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨kSv s₀, by simp, blk_sv_sub s₀⟩
      · exact ⟨_, by simp, fun _ h => h⟩)

section
variable {s₀ : State} (hp : KPre s₀)
include hp

theorem KPre.blk_wrap : (fD s₀).toNat + 16 * fN s₀ ≤ 2 ^ 64 := by
  have := hp.data_wrap; have := Nat.mul_div_le (fL s₀) 16; rw [AesCfb.X86_64.fN_eq]; omega

theorem KPre.blk_tail : (fBlk s₀).Disjoint (fTail s₀) := by
  have := hp.data_wrap
  have := Nat.div_add_mod (fL s₀) 16
  exact Offset.base_disjoint _ (Nat.le_refl _) (by rw [AesCfb.X86_64.fN_eq, AesCfb.X86_64.fU_eq]; omega)

theorem KPre.sch_big : ∀ r ∈ kBig s₀, (kSch s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.sch_iv
  · exact hp.sch_data
  · exact hp.sch_sv
  · exact hp.stk_sch.symm

theorem KPre.bk_toNat : (kBk s₀).toNat = (kV s₀).toNat + 48 := by
  have := hp.sv_wrap
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 48) (by decide), Nat.mod_eq_of_lt (by omega)]

omit hp in
theorem KPre.rsi : s₀.gpr .rsi = BitVec.ofNat 64 (fR s₀) := by
  apply BitVec.eq_of_toNat_eq; simp

end

/-- The subkeys, from memory that agrees with the entry's on the schedule. -/
theorem subkeys_of {s₀ : State} (hp : KPre s₀) {rs : List Region} {m₀ m : Mem} (hf : Frame rs m₀ m)
    (hd : ∀ r ∈ rs, (kSch s₀).Disjoint r) :
    Spec.Camellia.subkeysAt m (fW s₀) (fR s₀) = Spec.Camellia.subkeysAt m₀ (fW s₀) (fR s₀) :=
  subkeysAt_congr (by rcases hp.rounds with h | h <;> rw [h] <;> decide)
    fun i hi => hf.bytes (R := kSch s₀) hd (by show 272 ≤ 2 ^ 64; decide) hi

/-! ## Saving the registers -/

theorem load0_ok (s : State) : runBlock isa [.mov .rax (.reg .r9)] s = some (s.setReg .rax (s.gpr .r9)) := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc, Option.map_some]

theorem load_ok (s : State) : runBlock isa ctrFinalLoad s = some (s.setReg .rax (s.gpr .r15)) := by
  simp only [ctrFinalLoad, runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc, Option.map_some]

theorem moves_ok (s : State) :
    ∃ s', runBlock isa ctrFinalMoves s = some s' ∧
      s'.gpr .rbx = s.gpr .rdi ∧ s'.gpr .rbp = s.gpr .rsi ∧ s'.gpr .r12 = s.gpr .rdx ∧
      s'.gpr .r15 = s.gpr .rax ∧ s'.gpr .r14 = s.gpr .r8 &&& 15#64 ∧
      s'.gpr .r13 = s.gpr .r8 - (s.gpr .r8 &&& 15#64) + s.gpr .rcx ∧ s'.gpr .r8 = s.gpr .r8 >>> 4 ∧
      s'.gpr .rdi = s.gpr .rdi ∧ s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .rdx = s.gpr .rdx ∧
      s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, ctrFinalMoves, runBlock_cons,
      runStep_some, runBlock_nil, reduceExec, execAlu, execShift, readSrc, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, Nat.reduceLeDiff, and_self, AesCfb.X86_64.signExtend_15]
    rfl, ?_⟩
  simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg,
    rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags, wr_setFlags, reduceCtorEq, ↓reduceIte, and_self]

/-- What saving the registers and setting up the arguments leaves. -/
structure KSetup (s₀ s : State) : Prop where
  rbx : s.gpr .rbx = fW s₀
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r12 : s.gpr .r12 = fIv s₀
  r13 : s.gpr .r13 = fT s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (fU s₀)
  r15 : s.gpr .r15 = kV s₀
  rdi : s.gpr .rdi = fW s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  rdx : s.gpr .rdx = fIv s₀
  rcx : s.gpr .rcx = fD s₀
  r8 : s.gpr .r8 = BitVec.ofNat 64 (fN s₀)
  rsp : s.gpr .rsp = fSp s₀
  mem : s.mem = kSvMem s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem setup_wp {s₀ : State} (hp : KPre s₀) :
    WP isa (.block ctrFinalSetup) (s₀.setReg .rax (kV s₀)) (KSetup s₀) := by
  have hw : ∀ p ∈ finalSaved, InRegions (s₀.setReg .rax (kV s₀)).wr
      (Spill.slot ((s₀.setReg .rax (kV s₀)).gpr .rax) p.2) 8 := by
    intro p hp'
    rw [wr_setReg, gpr_setReg_self, hp.wr]
    have := AesCfb.X86_64.saved_slots p hp'
    exact ⟨kSv s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  show WP isa (.block (Spill.saveCode .rax finalSaved ++ ctrFinalMoves)) _ _
  refine Spill.save_then .rax finalSaved hw ?_
  refine WP.mono (WP.of_runBlock (moves_ok _))
    fun s' ⟨rbx, rbp, r12, r15, r14, r13, r8, rdi, rsi, rdx, rcx, rsp, mem, rd, wr⟩ => ?_
  simp only [gpr_setReg, reduceCtorEq, ↓reduceIte] at rbx rbp r12 r15 r14 r13 r8 rdi rsi rdx rcx rsp
  exact ⟨rbx, rbp, r12, by rw [r13, AesCfb.X86_64.and15, AesCfb.X86_64.tail_addr],
    by rw [r14, AesCfb.X86_64.and15], r15, rdi, rsi, rdx, rcx, by rw [r8, AesCfb.X86_64.shr4], rsp,
    by rw [mem, mem_setReg, gpr_setReg_self], by rw [rd, rd_setReg], by rw [wr, wr_setReg]⟩

/-! ## The whole blocks -/

/-- What the call on the whole blocks leaves. -/
structure KWhole (s₀ s : State) : Prop where
  rbx : s.gpr .rbx = fW s₀
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r12 : s.gpr .r12 = fIv s₀
  r13 : s.gpr .r13 = fT s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (fU s₀)
  r15 : s.gpr .r15 = kV s₀
  rsp : s.gpr .rsp = fSp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (kW1 s₀) (kSvMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) = Spec.Ctr.crypt (kCiph s₀) (kT s₀) (kBlks s₀)
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (kT s₀) (fN s₀)

theorem whole_regions {s₀ : State} (hp : KPre s₀) {s : State} (h : KSetup s₀ s) :
    calleeK.pre (s.callEntry.withRegions [kSch s₀] [kIv s₀, fBlk s₀]) ∧
      Covers ([kSch s₀] ++ [kIv s₀, fBlk s₀]) (s.rd ++ s.wr) ∧ Covers [kIv s₀, fBlk s₀] s.wr := by
  refine ⟨callee_pre h.rdi (h.rsi.trans KPre.rsi) h.rdx h.rcx h.r8 (AesCfb.X86_64.n_lt s₀) hp.rounds
    (by rw [h.rsp]; exact hp.sp) hp.sch_iv (hp.sch_data.sub_right (blk_sub s₀))
    (hp.iv_data.sub_right (blk_sub s₀)) (fun r hr => ?_) hp.sch_wrap hp.iv_wrap hp.blk_wrap, ?_, ?_⟩
  · rw [h.rsp]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.stk_sch
    · exact hp.stk_iv
    · exact hp.stk_data.sub_right (blk_sub s₀)
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨kSch s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨kIv s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨fData s₀, by simp, 0, by simp, by simpa using Nat.mul_div_le (fL s₀) 16⟩
  · rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨kIv s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨fData s₀, by simp, 0, by simp, by simpa using Nat.mul_div_le (fL s₀) 16⟩

/-- The save and a call's return address change only `save` and the stack. -/
theorem entry_frame {s₀ s : State} (h : KSetup s₀ s) : Frame [kSv s₀, kStk s₀] s₀.mem s.callEntry.mem := by
  have f₁ : Frame [kSv s₀, kStk s₀] s₀.mem s.mem := by
    rw [h.mem]; exact (svMem_frame s₀).mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]
  have f₂ : Frame [kSv s₀, kStk s₀] s.mem s.callEntry.mem :=
    (AesCbc.X86_64.callEntry_frame s).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨kStk s₀, by simp, by rw [h.rsp]; exact Offset.sub_below _ (by decide) (by decide)⟩
  exact f₁.trans f₂

theorem whole_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KSetup s₀ s) :
    WP isa (.call "vg_camellia_ctr" ctrFramed) s (KWhole s₀) := by
  have ef := entry_frame h
  have dS : ∀ r ∈ [kSv s₀, kStk s₀], (kSch s₀).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.sch_sv
    · exact hp.stk_sch.symm
  have eT : bytesAt s.callEntry.mem (fIv s₀) 16 = kT s₀ := AesCbc.X86_64.bytesAt_frame ef (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.iv_sv
    · exact hp.stk_iv.symm) (by decide)
  have eB : Spec.Cbc.blocksAt s.callEntry.mem (fD s₀) (fN s₀) = kBlks s₀ :=
    AesCfb.X86_64.blocksAt_frame' ef fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.data_sv.sub_left (blk_sub s₀)
      · exact hp.stk_data.symm.sub_left (blk_sub s₀)
  obtain ⟨hpre, hc, hw⟩ := whole_regions hp h
  refine WP.callF (k := calleeK) ctrFramed_sk.1 ctrFramed_spSafe (by rw [ctrFramed_depth]; decide) hpre hc hw ?_
  intro s' rd' wr' cs' fr' ⟨s₂, mem₂, _, post₂⟩ _
  rw [ctrFramed_depth, h.rsp, h.mem] at fr'
  obtain ⟨pb, pc⟩ := callee_post h.rdi (h.rsi.trans KPre.rsi) h.rdx h.rcx h.r8 (AesCfb.X86_64.n_lt s₀) hp.rounds
    post₂
  rw [mem₂, subkeys_of hp ef dS, eT, eB] at pb
  rw [mem₂, eT] at pc
  refine ⟨by rw [cs' .rbx (by simp [calleeSaved]), h.rbx], by rw [cs' .rbp (by simp [calleeSaved]), h.rbp],
    by rw [cs' .r12 (by simp [calleeSaved]), h.r12], by rw [cs' .r13 (by simp [calleeSaved]), h.r13],
    by rw [cs' .r14 (by simp [calleeSaved]), h.r14], by rw [cs' .r15 (by simp [calleeSaved]), h.r15],
    by rw [cs' .rsp (by simp [calleeSaved]), h.rsp], by rw [rd', h.rd], by rw [wr', h.wr],
    fr'.mono fun r hr => ?_, pb, pc⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with h | h | h <;> simp [h]

theorem test_wp {s₀ s : State} (h : KWhole s₀ s) :
    WP isa (.block [.alu .test .r14 (.reg .r14)]) s fun s' => KWhole s₀ s' ∧ s'.zf = some (decide (fU s₀ = 0)) :=
  WP.of_runBlock ⟨_, AesCfb.X86_64.test_ok s,
    ⟨h.rbx, h.rbp, h.r12, h.r13, h.r14, h.r15, h.rsp, h.rd, h.wr, h.frame, h.blocks, h.ctr⟩, by
    have eU := AesCfb.X86_64.fU_eq s₀
    rw [zf_arithFlags, BitVec.and_self, h.r14,
      AesCfb.X86_64.beq_zero' (by have := Nat.mod_lt (fL s₀) (by decide : 16 > 0); omega)]⟩

/-! ## The partial last block -/

/-- `save` to `rax`, from a state `F` describes. -/
abbrev Loaded (F : State → Prop) (s₀ s : State) : Prop := ∃ w, F w ∧ s = w.setReg .rax (kV s₀)

theorem tailMoves_ok (s : State) :
    ∃ s', runBlock isa ctrFinalTailMoves s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧ s'.gpr .rdx = s.gpr .r12 ∧
      s'.gpr .rcx = s.gpr .rax + BitVec.ofNat 64 48 ∧ s'.gpr .r8 = 1 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.gpr .r13 = s.gpr .r13 ∧ s'.gpr .r14 = s.gpr .r14 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [ctrFinalTailMoves, runBlock_cons, runStep_some, reduceExec, execAlu, readSrc, Option.bind_some,
      Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    try simp [gpr_setReg, State.setReg32, mem_arithFlags, rd_arithFlags, wr_arithFlags, mem_setReg, rd_setReg,
      wr_setReg]
  intro r hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem zero_frame (s₀ : State) (m : Mem) (g : Reg → BitVec 64) :
    Frame [kBlk s₀] m (Spill.saveMem m (kV s₀) g zeroSlots) :=
  Spill.saveMem_frame m _ g zeroSlots fun p hp' => by
    simp only [zeroSlots, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact Offset.contains _ (by decide) (by decide) (by decide)
    · exact Offset.contains _ (by decide) (by decide) (by decide)

/-- What zeroing the block and setting up the arguments leaves. -/
structure KTArgs (s₀ s : State) : Prop where
  rdi : s.gpr .rdi = fW s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  rdx : s.gpr .rdx = fIv s₀
  rcx : s.gpr .rcx = kBk s₀
  r8 : s.gpr .r8 = BitVec.ofNat 64 1
  r13 : s.gpr .r13 = fT s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (fU s₀)
  r15 : s.gpr .r15 = kV s₀
  rsp : s.gpr .rsp = fSp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (kW1 s₀) (kSvMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) = Spec.Ctr.crypt (kCiph s₀) (kT s₀) (kBlks s₀)
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (kT s₀) (fN s₀)
  zero : bytesAt s.mem (kBk s₀) 16 = List.replicate 16 0

theorem tail_load_wp {s₀ s : State} (h : KWhole s₀ s) : WP isa (.block ctrFinalLoad) s (Loaded (KWhole s₀) s₀) :=
  WP.of_runBlock ⟨_, load_ok s, s, h, by rw [h.r15]⟩

theorem tail_args_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KWhole s₀ s) :
    WP isa (.block ctrFinalTailArgs) (s.setReg .rax (kV s₀)) (KTArgs s₀) := by
  obtain ⟨s₂, r₂, z₂, k₂, m₂, rd₂, wr₂⟩ := AesCtr.X86_64.zero_ok (s.setReg .rax (kV s₀))
  show WP isa (.block ([.mov32 .r10 (.imm 0)] ++ (Spill.saveCode .rax zeroSlots ++ ctrFinalTailMoves))) _ _
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₂, r₂, ?_⟩)
  have k₂' : ∀ r, r ≠ .r10 → r ≠ .rax → s₂.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [k₂ r h₁, gpr_setReg_of_ne _ _ h₂]
  have hrax : s₂.gpr .rax = kV s₀ := by rw [k₂ _ (by decide), gpr_setReg_self]
  have hw : ∀ p ∈ zeroSlots, InRegions s₂.wr (Spill.slot (s₂.gpr .rax) p.2) 8 := by
    intro p hp'
    rw [wr₂, wr_setReg, h.wr, hp.wr, hrax]
    simp only [zeroSlots, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact ⟨kSv s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩
    · exact ⟨kSv s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  refine Spill.save_then .rax zeroSlots hw ?_
  refine WP.mono (WP.of_runBlock (tailMoves_ok _))
    fun s' ⟨rdi, rsi, rdx, rcx, r8, cs, r13, r14, mem, rd, wr⟩ => ?_
  have e : ∀ r, ({ s₂ with mem := Spill.saveMem s₂.mem (s₂.gpr .rax) s₂.gpr zeroSlots } : State).gpr r =
    s₂.gpr r := fun _ => rfl
  rw [e] at rdi rsi rdx rcx r13 r14
  have hm : s'.mem = Spill.saveMem s.mem (kV s₀) s₂.gpr zeroSlots := by
    rw [mem]; show Spill.saveMem s₂.mem _ _ _ = _; rw [m₂, mem_setReg, hrax]
  have fz : Frame [kBlk s₀] s.mem s'.mem := by rw [hm]; exact zero_frame s₀ _ _
  have ivZ : ∀ r ∈ [kBlk s₀], (kIv s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_sv.sub_right (blk_sv_sub s₀)
  have blkZ : ∀ r ∈ [kBlk s₀], (fBlk s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (hp.data_sv.sub_left (blk_sub s₀)).sub_right (blk_sv_sub s₀)
  refine ⟨by rw [rdi, k₂' _ (by decide) (by decide), h.rbx], by rw [rsi, k₂' _ (by decide) (by decide), h.rbp],
    by rw [rdx, k₂' _ (by decide) (by decide), h.r12], by rw [rcx, hrax], r8,
    by rw [r13, k₂' _ (by decide) (by decide), h.r13], by rw [r14, k₂' _ (by decide) (by decide), h.r14],
    by rw [cs .r15 (by simp [calleeSaved]), e, k₂' _ (by decide) (by decide), h.r15],
    by rw [cs .rsp (by simp [calleeSaved]), e, k₂' _ (by decide) (by decide), h.rsp],
    by rw [rd, rd₂, rd_setReg, h.rd], by rw [wr, wr₂, wr_setReg, h.wr], ?_, ?_, ?_, ?_⟩
  · exact h.frame.trans (fz.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  · rw [AesCfb.X86_64.blocksAt_frame' fz blkZ]; exact h.blocks
  · rw [AesCbc.X86_64.bytesAt_frame fz ivZ (by decide)]; exact h.ctr
  · rw [hm, show Spill.saveMem s.mem (kV s₀) s₂.gpr zeroSlots =
        ((s.mem.writeW (kBk s₀) (s₂.gpr .r10)).writeW (kBk s₀ + BitVec.ofNat 64 8) (s₂.gpr .r10)) by
      simp only [Spill.saveMem, zeroSlots, Spill.slot, Offset.add_add], z₂]
    exact AesCtr.X86_64.zero_bytes _ _

theorem cipher_length (sk : Spec.Camellia.Subkeys) (b : List Byte) : (Spec.Camellia.cipher sk b).length = 16 := by
  simp [Spec.Camellia.cipher]

/-- What the call on the block leaves. -/
structure KTCall (s₀ s : State) : Prop where
  r13 : s.gpr .r13 = fT s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (fU s₀)
  r15 : s.gpr .r15 = kV s₀
  rsp : s.gpr .rsp = fSp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (kW1 s₀) (kSvMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) = Spec.Ctr.crypt (kCiph s₀) (kT s₀) (kBlks s₀)
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (Spec.Ctr.next (kT s₀) (fN s₀)) 1
  out : bytesAt s.mem (kBk s₀) 16 = kCiph s₀ (Spec.Ctr.next (kT s₀) (fN s₀))

theorem tail_regions {s₀ : State} (hp : KPre s₀) {s : State} (h : KTArgs s₀ s) :
    calleeK.pre (s.callEntry.withRegions [kSch s₀] [kIv s₀, ⟨kBk s₀, 16 * 1⟩]) ∧
      Covers ([kSch s₀] ++ [kIv s₀, ⟨kBk s₀, 16 * 1⟩]) (s.rd ++ s.wr) ∧
      Covers [kIv s₀, ⟨kBk s₀, 16 * 1⟩] s.wr := by
  have bs := blk_sv_sub s₀
  refine ⟨callee_pre h.rdi (h.rsi.trans KPre.rsi) h.rdx h.rcx h.r8 (by decide) hp.rounds
    (by rw [h.rsp]; exact hp.sp) hp.sch_iv (hp.sch_sv.sub_right bs) (hp.iv_sv.sub_right bs) (fun r hr => ?_)
    hp.sch_wrap hp.iv_wrap (by rw [hp.bk_toNat]; have := hp.sv_wrap; omega), ?_, ?_⟩
  · rw [h.rsp]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.stk_sch
    · exact hp.stk_iv
    · exact hp.stk_sv.sub_right bs
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨kSch s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨kIv s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨kSv s₀, by simp, 48, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨kIv s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨kSv s₀, by simp, 48, by simp, by simp⟩

theorem KTArgs.entry {s₀ : State} (hp : KPre s₀) {s : State} (h : KTArgs s₀ s) :
    Spec.Camellia.subkeysAt s.callEntry.mem (fW s₀) (fR s₀) = Spec.Camellia.subkeysAt s₀.mem (fW s₀) (fR s₀) ∧
      bytesAt s.callEntry.mem (fIv s₀) 16 = Spec.Ctr.next (kT s₀) (fN s₀) ∧
      bytesAt s.callEntry.mem (kBk s₀) 16 = List.replicate 16 0 := by
  have ef := AesCbc.X86_64.callEntry_frame s
  have stk : Region.Sub (below (s.gpr .rsp) 8) (kStk s₀) := by
    rw [h.rsp]; exact Offset.sub_below _ (by decide) (by decide)
  have big := big_of (kW1_kW h.frame)
  refine ⟨?_, ?_, ?_⟩
  · rw [subkeys_of hp ef fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.stk_sch.symm.sub_right stk]
    exact subkeys_of hp big hp.sch_big
  · rw [AesCbc.X86_64.bytesAt_frame ef (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.stk_iv.symm.sub_right stk) (by decide)]
    exact h.ctr
  · rw [AesCbc.X86_64.bytesAt_frame ef (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.stk_sv.symm.sub_left (blk_sv_sub s₀)).sub_right stk) (by decide)]
    exact h.zero

theorem tail_call_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KTArgs s₀ s) :
    WP isa (.call "vg_camellia_ctr" ctrFramed) s (KTCall s₀) := by
  obtain ⟨hpre, hc, hw⟩ := tail_regions hp h
  obtain ⟨eK, eT, eZ⟩ := h.entry hp
  refine WP.callF (k := calleeK) ctrFramed_sk.1 ctrFramed_spSafe (by rw [ctrFramed_depth]; decide) hpre hc hw ?_
  intro s' rd' wr' cs' fr' ⟨s₂, mem₂, _, post₂⟩ _
  rw [ctrFramed_depth, h.rsp] at fr'
  obtain ⟨pb, pc⟩ := callee_post h.rdi (h.rsi.trans KPre.rsi) h.rdx h.rcx h.r8 (by decide) hp.rounds post₂
  rw [mem₂, eK, eT] at pb
  rw [mem₂, eT] at pc
  have fc : Frame (kW1 s₀) s.mem s'.mem := fr'.sub fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨kBlk s₀, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  refine ⟨by rw [cs' .r13 (by simp [calleeSaved]), h.r13], by rw [cs' .r14 (by simp [calleeSaved]), h.r14],
    by rw [cs' .r15 (by simp [calleeSaved]), h.r15], by rw [cs' .rsp (by simp [calleeSaved]), h.rsp],
    by rw [rd', h.rd], by rw [wr', h.wr], h.frame.trans fc, ?_, pc, ?_⟩
  · rw [AesCfb.X86_64.blocksAt_frame' fr' fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.iv_data.symm.sub_left (blk_sub s₀)
      · exact (hp.data_sv.sub_left (blk_sub s₀)).sub_right (blk_sv_sub s₀)
      · exact hp.stk_data.symm.sub_left (blk_sub s₀)]
    exact h.blocks
  · exact Modes.CtrFinal.bytesAt_of_blocksAt_one (cipher_length _) eZ pb

theorem key_load_wp {s₀ s : State} (h : KTCall s₀ s) : WP isa (.block ctrFinalLoad) s (Loaded (KTCall s₀) s₀) :=
  WP.of_runBlock ⟨_, load_ok s, s, h, by rw [h.r15]⟩

/-- What the function leaves before restoring the registers. -/
structure KDone (s₀ s : State) : Prop where
  r15 : s.gpr .r15 = kV s₀
  rsp : s.gpr .rsp = fSp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (kW s₀) (kSvMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) = Spec.Ctr.crypt (kCiph s₀) (kT s₀) (kBlks s₀)
  tail : ∀ q < fU s₀, s.mem (fT s₀ + BitVec.ofNat 64 q) = s₀.mem (fT s₀ + BitVec.ofNat 64 q) ^^^
    (kCiph s₀ (Spec.Ctr.next (kT s₀) (fN s₀))).getD q 0
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (kT s₀) (if fU s₀ = 0 then fN s₀ else fN s₀ + 1)

theorem done_of_zero {s₀ s : State} (h : KWhole s₀ s) (hu : fU s₀ = 0) : KDone s₀ s :=
  ⟨h.r15, h.rsp, h.rd, h.wr, kW1_kW h.frame, h.blocks, fun q hq => absurd hq (by omega), by
    rw [ite_eq_left hu]; exact h.ctr⟩

theorem tail_xor_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KTCall s₀ s) (hu : fU s₀ ≠ 0) :
    WP isa (.seq (.block tailKey) (.loop (.block (Impl.Modes.X86_64.xorByte .r13 .r14)) .ne))
      (s.setReg .rax (kV s₀)) (KDone s₀) := by
  obtain ⟨s₁, r₁, rax₁, k₁, m₁, rd₁, wr₁⟩ := AesCtr.X86_64.key_ok (s.setReg .rax (kV s₀))
  rw [gpr_setReg_self] at rax₁
  have k₁' : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r := fun r hr => by rw [k₁ r hr, gpr_setReg_of_ne _ _ hr]
  rw [mem_setReg] at m₁
  rw [rd_setReg] at rd₁
  rw [wr_setReg] at wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, r₁, ?_⟩)
  have hU : fU s₀ < 16 := Nat.mod_lt _ (by decide)
  have hL := Nat.div_add_mod (fL s₀) 16
  have hDw := hp.data_wrap
  have hVw := hp.sv_wrap
  have eN := AesCfb.X86_64.fN_eq s₀
  have eU := AesCfb.X86_64.fU_eq s₀
  have hT : (fT s₀).toNat = (fD s₀).toNat + 16 * fN s₀ := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * fN s₀) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hB := hp.bk_toNat
  have xp : Modes.X86_64.XPre s₁ (kBk s₀) (fT s₀) (fU s₀) .r13 .r14 := {
    pos := by omega
    small := by omega
    fitK := by omega
    fitR := by rw [hT]; omega
    disj := (((hp.data_sv.sub_left (tail_sub s₀)).sub_right (blk_sv_sub s₀)).sub_right
      (Region.sub_prefix (by omega))).symm
    rdK := fun q hq => by
      rw [rd₁, wr₁, h.rd, h.wr, hp.rd, hp.wr]
      refine ⟨kSv s₀, by simp, ?_⟩
      rw [Offset.add_add]
      exact Offset.contains_base _ (by omega) (by omega)
    wrR := fun q hq => by
      rw [wr₁, h.wr, hp.wr]
      refine ⟨fData s₀, by simp, ?_⟩
      rw [show fT s₀ + BitVec.ofNat 64 q = fD s₀ + BitVec.ofNat 64 (16 * fN s₀ + q) from Offset.add_add _ _ _]
      exact Offset.contains_base _ (by omega) (by omega)
    dl := by decide
    dRax := by decide
    dR10 := by decide
    dRcx := by decide }
  have x0 : Modes.X86_64.XInv s₁ (kBk s₀) (fT s₀) (fU s₀) .r13 .r14 0 s₁ := {
    rax := by rw [rax₁]; exact (BitVec.add_zero _).symm
    dat := by rw [k₁' _ (by decide), h.r13]; exact (BitVec.add_zero _).symm
    left := by rw [k₁' _ (by decide), h.r14, Nat.sub_zero]
    lt := by omega
    data := fun q _ => by rw [ite_eq_right (Nat.not_lt_zero q)]
    frame := Frame.refl _ _
    rd := rfl
    wr := rfl
    gpr := fun _ _ _ _ _ _ => rfl }
  refine WP.mono (Modes.X86_64.xorLoop_wp xp x0) fun s' d => ?_
  have tailD : ∀ r ∈ kW1 s₀, (fTail s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hp.iv_data.sub_right (tail_sub s₀)).symm
    · exact hp.blk_tail.symm
    · exact (hp.data_sv.sub_left (tail_sub s₀)).sub_right (blk_sv_sub s₀)
    · exact (hp.stk_data.sub_right (tail_sub s₀)).symm
  have tailS : ∀ r ∈ [kSv s₀], (fTail s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.data_sv.sub_left (tail_sub s₀)
  have hlen : (fTail s₀).len ≤ 2 ^ 64 := by show fU s₀ ≤ 2 ^ 64; omega
  have ivT : ∀ r ∈ [fTail s₀], (kIv s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hp.iv_data.sub_right (tail_sub s₀)
  refine ⟨by rw [d.gpr .r15 (by decide) (by decide) (by decide) (by decide) (by decide), k₁' _ (by decide), h.r15],
    by rw [d.gpr .rsp (by decide) (by decide) (by decide) (by decide) (by decide), k₁' _ (by decide), h.rsp],
    by rw [d.rd, rd₁, h.rd], by rw [d.wr, wr₁, h.wr], ?_, ?_, fun q hq => ?_, ?_⟩
  · refine kW1_kW h.frame |>.trans ?_
    rw [← m₁]
    exact d.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨fData s₀, by simp, tail_sub s₀⟩
  · rw [AesCfb.X86_64.blocksAt_frame' d.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.blk_tail, m₁]
    exact h.blocks
  · rw [d.data q hq, m₁, h.frame.bytes tailD hlen hq, (svMem_frame s₀).bytes tailS hlen hq,
      ← AesCfb.X86_64.bytesAt_getD s.mem (kBk s₀) (show q < 16 by omega), h.out]
  · rw [ite_eq_right hu, AesCbc.X86_64.bytesAt_frame d.frame ivT (by decide), m₁, h.ctr, ← AesCtr.next_add]

theorem mid_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KWhole s₀ s) (hz : s.zf = some (decide (fU s₀ = 0))) :
    WP isa (.ite .e (.block []) ctrFinalTail) s (KDone s₀) := by
  have ev : isa.eval .e s = some (decide (fU s₀ = 0)) := hz
  by_cases hu : fU s₀ = 0
  · exact WP.ite true (by rw [ev, decide_eq_true hu]) (fun _ => WP.block_nil (done_of_zero h hu))
      (fun h => by cases h)
  · refine WP.ite false (by rw [ev, decide_eq_false hu]) (fun h => by cases h) fun _ => ?_
    refine WP.seq (WP.mono (tail_load_wp h) fun _ ⟨w, hw, e⟩ => ?_)
    subst e
    exact WP.seq (WP.mono (tail_args_wp hp hw) fun _ h₁ =>
      WP.seq (WP.mono (tail_call_wp hp h₁) fun _ h₂ =>
        WP.seq (WP.mono (key_load_wp h₂) fun _ ⟨w', hw', e'⟩ => by subst e'; exact tail_xor_wp hp hw' hu)))

/-! ## Restoring the registers -/

theorem end_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KDone s₀ s) :
    WP isa (.seq (.block ctrFinalLoad) (.block finalRestore)) s fun s' => gprPreserved s₀ s' ∧ s'.mem = s.mem := by
  have big := big_of h.frame
  refine WP.seq (WP.of_runBlock ⟨_, load_ok s, ?_⟩)
  rw [h.r15]
  have hs : Spill.Saved (s.setReg .rax (kV s₀)).mem ((s.setReg .rax (kV s₀)).gpr .rax) (kG s₀) finalSaved := by
    rw [mem_setReg, gpr_setReg_self]
    refine (Spill.saveMem_saved _ _ _ _ (by decide)).frame h.frame fun p hp' r hr => ?_
    have := AesCfb.X86_64.saved_slots p hp'
    have hsub : Region.Sub ⟨Spill.slot (kV s₀) p.2, 8⟩ (kSv s₀) := Offset.sub_base _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.iv_sv.symm.sub_left hsub
    · exact hp.data_sv.symm.sub_left hsub
    · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
    · exact hp.stk_sv.symm.sub_left hsub
  show WP isa (.block (Spill.restoreCode .rax finalSaved)) _ _
  refine WP.mono (Spill.restore_ok .rax finalSaved (kG s₀) _ (by decide) (fun p hp' => ?_) hs)
    fun s' ⟨g₁, g₂, mem', _, _⟩ => ?_
  · rw [rd_setReg, wr_setReg, gpr_setReg_self, h.rd, h.wr, hp.rd, hp.wr]
    have := AesCfb.X86_64.saved_slots p hp'
    exact ⟨kSv s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · have cs := Spill.calleeSaved_ok g₁ g₂ (by decide)
      (show _ = (s₀.setReg .rax (kV s₀)).gpr .rsp by
        rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide), h.rsp])
    refine ⟨⟨fun r hr => by rw [cs r hr]; exact gpr_setReg_of_ne _ _ (AesCfb.X86_64.calleeSaved_ne_rax' hr), ?_⟩,
      by rw [mem', mem_setReg]⟩
    rw [mem', mem_setReg]
    refine big.readW (r := ⟨fSp s₀, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.ret_iv
    · exact hp.ret_data
    · exact hp.ret_sv
    · exact Offset.base_disjoint_below _ (by decide)

/-! ## The whole function -/

theorem final_wp {s₀ : State} (hp : KPre s₀) :
    WP isa ctrFinal s₀ fun s' => gprPreserved s₀ s' ∧ ∃ s₁, KDone s₀ s₁ ∧ s'.mem = s₁.mem := by
  refine WP.seq (WP.of_runBlock ⟨_, load0_ok s₀, ?_⟩)
  refine WP.seq (WP.mono (setup_wp hp) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (whole_wp hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (test_wp h₃) fun s₄ ⟨h₄, z₄⟩ => ?_)
  refine WP.seq (WP.mono (mid_wp hp h₄ z₄) fun s₅ h₅ => ?_)
  exact WP.mono (end_wp hp h₅) fun _ ⟨g, m⟩ => ⟨g, s₅, h₅, m⟩

theorem final_post {s₀ s₁ s' : State} (h : KDone s₀ s₁) (hm : s'.mem = s₁.mem) : ctrFinalX86_64.post s₀ s' := by
  show Spec.Ctr.CryptFinal (kCiph s₀) s₀.mem s'.mem (fIv s₀) (fD s₀) (fL s₀)
  exact Modes.CtrFinal.cryptFinal_of (cipher_length _) (by rw [hm]; exact h.blocks)
    (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.ctr)

theorem ctrFinal_mx : ctrFinal.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem final_correct (s : State) (hs : ctrFinalX86_64.pre s) :
    ∃ t s', Exec isa ctrFinal s t s' ∧ abiPreserved s s' ∧ ctrFinalX86_64.post s s' := by
  obtain ⟨t, s', he, hg, s₁, h₁, hm⟩ := final_wp (KPre.of hs)
  exact ⟨t, s', he, abiPreserved_of_exec ctrFinal_mx he hg, final_post h₁ hm⟩

/-! ## Constant time -/

theorem load0_taint : ∃ h, (taint.check (Taint.ofRegs [.r9]) (.block [.mov .rax (.reg .r9)]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem setup_taint : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp, .rax])
    (.block ctrFinalSetup) h).isSome = true := ⟨_, by taint_decide⟩

theorem test_taint : ∃ h, (taint.check (Taint.ofRegs [.r14]) (.block [.alu .test .r14 (.reg .r14)]) h).isSome =
    true := ⟨_, by taint_decide⟩

theorem load_taint : ∃ h, (taint.check (Taint.ofRegs [.r15]) (.block ctrFinalLoad) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tailArgs_taint : ∃ h, (taint.check (Taint.ofRegs [.rax, .rbx, .rbp, .r12, .rsp])
    (.block ctrFinalTailArgs) h).isSome = true := ⟨_, by taint_decide⟩

theorem xor_taint : ∃ h, (taint.check (Taint.ofRegs [.rax, .r13, .r14])
    (.seq (.block tailKey) (.loop (.block (Impl.Modes.X86_64.xorByte .r13 .r14)) .ne)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (taint.check (Taint.ofRegs [.rax]) (.block finalRestore) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem final_rel {s₀ s₀' : State} (h0 : ctrFinalX86_64.pre s₀) (h0' : ctrFinalX86_64.pre s₀')
    (hq : ctrFinalX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') ctrFinal fun _ _ => True := by
  have hp := KPre.of h0
  have hp' := KPre.of h0'
  obtain ⟨qW, qR, qIv, qD, qL, qV, qSp⟩ := hq
  have qU : fU s₀ = fU s₀' := by simp only [fU, fL, qL]
  have qN : fN s₀ = fN s₀' := by simp only [fN, fL, qL]
  have qT : fT s₀ = fT s₀' := by simp only [fT, qD, qN]
  have qRn : fR s₀ = fR s₀' := by simp only [fR, qR]
  have r₁ := AesCtr.X86_64.taint_rel (P := fun a b => a = s₀ ∧ b = s₀') (F₁ := (· = s₀.setReg .rax (kV s₀)))
    (F₂ := (· = s₀'.setReg .rax (kV s₀'))) [.r9] load0_taint
    (fun a b h r hr => by
      obtain ⟨rfl, rfl⟩ := h; simp only [List.mem_singleton] at hr; subst hr; exact qV)
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨WP.of_runBlock ⟨_, load0_ok _, rfl⟩, WP.of_runBlock ⟨_, load0_ok _, rfl⟩⟩
  have r₂ := AesCtr.X86_64.taint_rel
    (P := fun a b => a = s₀.setReg .rax (kV s₀) ∧ b = s₀'.setReg .rax (kV s₀'))
    (F₁ := KSetup s₀) (F₂ := KSetup s₀') [.rdi, .rsi, .rdx, .rcx, .r8, .rsp, .rax] setup_taint
    (fun a b h r hr => by
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, qW, qR, qIv, qD, qL, qSp, kV, qV])
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨setup_wp hp, setup_wp hp'⟩
  have r₃ := (RelCT.callEx (k := calleeK) (n := "vg_camellia_ctr") ctrFramed_sk.1 ctrFramed_sk.2.1
    (P := fun a b => KSetup s₀ a ∧ KSetup s₀' b) fun a b ⟨ha, hb⟩ => by
      obtain ⟨pa, ca, wa⟩ := whole_regions hp ha
      obtain ⟨pb, cb, wb⟩ := whole_regions hp' hb
      refine ⟨_, _, _, _, pa, pb, ?_, ca, wa, cb, wb, by rw [ha.rsp, hb.rsp, fSp, fSp, qSp]⟩
      exact callee_pub ha.rdi (ha.rsi.trans KPre.rsi) ha.rdx ha.rcx ha.r8
        (hb.rdi.trans (by rw [fW, fW, qW])) (hb.rsi.trans (KPre.rsi.trans (by rw [qRn])))
        (hb.rdx.trans (by rw [fIv, fIv, qIv])) (hb.rcx.trans (by rw [fD, fD, qD])) (hb.r8.trans (by rw [qN]))
        (by rw [ha.rsp, hb.rsp, fSp, fSp, qSp]) _ _ _ _).wp
    (F₁ := KWhole s₀) (F₂ := KWhole s₀') fun a b h => ⟨whole_wp hp h.1, whole_wp hp' h.2⟩
  have r₄ := AesCtr.X86_64.taint_rel (P := fun a b => KWhole s₀ a ∧ KWhole s₀' b)
    (F₁ := fun (s : State) => KWhole s₀ s ∧ s.zf = some (decide (fU s₀ = 0)))
    (F₂ := fun (s : State) => KWhole s₀' s ∧ s.zf = some (decide (fU s₀' = 0))) [.r14] test_taint
    (fun a b h r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h.1.r14, h.2.r14, qU])
    fun a b h => ⟨test_wp h.1, test_wp h.2⟩
  have tail (hu : fU s₀ ≠ 0) : RelCT isa (fun a b => KWhole s₀ a ∧ KWhole s₀' b) ctrFinalTail
      fun a b => KDone s₀ a ∧ KDone s₀' b := by
    have hu' : fU s₀' ≠ 0 := qU ▸ hu
    have a₁ := AesCtr.X86_64.taint_rel (P := fun a b => KWhole s₀ a ∧ KWhole s₀' b)
      (F₁ := Loaded (KWhole s₀) s₀) (F₂ := Loaded (KWhole s₀') s₀') [.r15] load_taint
      (fun a b h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.r15, h.2.r15, kV, kV, qV])
      fun a b h => ⟨tail_load_wp h.1, tail_load_wp h.2⟩
    have a₂ := AesCtr.X86_64.taint_rel (P := fun a b => Loaded (KWhole s₀) s₀ a ∧ Loaded (KWhole s₀') s₀' b)
      (F₁ := KTArgs s₀) (F₂ := KTArgs s₀') [.rax, .rbx, .rbp, .r12, .rsp] tailArgs_taint
      (fun a b h r hr => by
        obtain ⟨⟨w, hw, rfl⟩, ⟨w', hw', rfl⟩⟩ := h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [gpr_setReg_self, gpr_setReg_self, kV, kV, qV]
        · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide), hw.rbx, hw'.rbx, fW, fW, qW]
        · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide), hw.rbp, hw'.rbp, qR]
        · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide), hw.r12, hw'.r12, fIv, fIv, qIv]
        · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide), hw.rsp, hw'.rsp, fSp, fSp,
            qSp])
      fun a b h => by
        obtain ⟨⟨w, hw, rfl⟩, ⟨w', hw', rfl⟩⟩ := h
        exact ⟨tail_args_wp hp hw, tail_args_wp hp' hw'⟩
    have a₃ := (RelCT.callEx (k := calleeK) (n := "vg_camellia_ctr") ctrFramed_sk.1 ctrFramed_sk.2.1
      (P := fun a b => KTArgs s₀ a ∧ KTArgs s₀' b) fun a b ⟨ha, hb⟩ => by
        obtain ⟨pa, ca, wa⟩ := tail_regions hp ha
        obtain ⟨pb, cb, wb⟩ := tail_regions hp' hb
        refine ⟨_, _, _, _, pa, pb, ?_, ca, wa, cb, wb, by rw [ha.rsp, hb.rsp, fSp, fSp, qSp]⟩
        exact callee_pub ha.rdi (ha.rsi.trans KPre.rsi) ha.rdx ha.rcx ha.r8
          (hb.rdi.trans (by rw [fW, fW, qW])) (hb.rsi.trans (KPre.rsi.trans (by rw [qRn])))
          (hb.rdx.trans (by rw [fIv, fIv, qIv])) (hb.rcx.trans (by rw [kBk, kBk, kV, kV, qV])) hb.r8
          (by rw [ha.rsp, hb.rsp, fSp, fSp, qSp]) _ _ _ _).wp
      (F₁ := KTCall s₀) (F₂ := KTCall s₀') fun a b h => ⟨tail_call_wp hp h.1, tail_call_wp hp' h.2⟩
    have a₄ := AesCtr.X86_64.taint_rel (P := fun a b => KTCall s₀ a ∧ KTCall s₀' b)
      (F₁ := Loaded (KTCall s₀) s₀) (F₂ := Loaded (KTCall s₀') s₀') [.r15] load_taint
      (fun a b h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.r15, h.2.r15, kV, kV, qV])
      fun a b h => ⟨key_load_wp h.1, key_load_wp h.2⟩
    have a₅ := AesCtr.X86_64.taint_rel (P := fun a b => Loaded (KTCall s₀) s₀ a ∧ Loaded (KTCall s₀') s₀' b)
      (F₁ := KDone s₀) (F₂ := KDone s₀') [.rax, .r13, .r14] xor_taint
      (fun a b h r hr => by
        obtain ⟨⟨w, hw, rfl⟩, ⟨w', hw', rfl⟩⟩ := h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [gpr_setReg_self, gpr_setReg_self, kV, kV, qV]
        · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide), hw.r13, hw'.r13, qT]
        · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide), hw.r14, hw'.r14, qU])
      fun a b h => by
        obtain ⟨⟨w, hw, rfl⟩, ⟨w', hw', rfl⟩⟩ := h
        exact ⟨tail_xor_wp hp hw hu, tail_xor_wp hp' hw' hu'⟩
    exact a₁.seq (a₂.seq ((a₃.mono (fun _ _ h => h) fun _ _ h => h.2).seq (a₄.seq a₅)))
  have r₅ : RelCT isa (fun a b => (KWhole s₀ a ∧ a.zf = some (decide (fU s₀ = 0))) ∧
      (KWhole s₀' b ∧ b.zf = some (decide (fU s₀' = 0)))) (.ite .e (.block []) ctrFinalTail)
      (fun a b => KDone s₀ a ∧ KDone s₀' b) := by
    refine RelCT.ite (fun a b h => ?_) ?_ ?_
    · show a.zf = b.zf; rw [h.1.2, h.2.2, qU]
    · refine RelCT.block_nil fun a b h => ?_
      have h0 : fU s₀ = 0 := by
        have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this; simpa using this
      exact ⟨done_of_zero h.1.1.1 h0, done_of_zero h.1.2.1 (qU ▸ h0)⟩
    · refine (RelCT.exists_ fun (hu : fU s₀ ≠ 0) => tail hu).mono
        (fun a b h => ⟨?_, h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this; simpa using this
  have r₆ := AesCtr.X86_64.taint_rel (P := fun a b => KDone s₀ a ∧ KDone s₀' b)
    (F₁ := fun (s : State) => s.gpr .rax = kV s₀) (F₂ := fun (s : State) => s.gpr .rax = kV s₀') [.r15]
    load_taint
    (fun a b h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.r15, h.2.r15, kV, kV, qV])
    fun a b h => ⟨WP.of_runBlock ⟨_, load_ok _, by rw [gpr_setReg_self, h.1.r15]⟩,
      WP.of_runBlock ⟨_, load_ok _, by rw [gpr_setReg_self, h.2.r15]⟩⟩
  obtain ⟨_, t₇⟩ := restore_taint
  have r₇ := RelCT.taint (A := taint) (P := fun a b => a.gpr .rax = kV s₀ ∧ b.gpr .rax = kV s₀') _
    (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1, h.2, kV, kV, qV]) t₇
  exact r₁.seq (r₂.seq ((r₃.mono (fun _ _ h => h) fun _ _ h => h.2).seq (r₄.seq (r₅.seq (r₆.seq r₇)))))

theorem final_ct : ConstantTime isa ctrFinalX86_64.pre ctrFinalX86_64.pub ctrFinal :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (final_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Verified -/

theorem ctrFinal_spSafe : ctrFinal.all (fun i => !X86_64.isa.writesSp i) = true := Code.all_of_allInstrs (by lit_decide)

theorem ctrFinal_xdepth : ctrFinal.x86_64Depth ≤ 3296 := by lit_decide

theorem ctrFinal_verified : Verified X86_64.target ctrFinal ctrFinalScratchContract :=
  Verified.of_correct final_correct final_ct ctrFinal_implies

/-! ## With `save` on the stack

`vg_camellia_ctr_final` has five argument words, so `save` is passed in `r9`:
it runs its code in a frame of 72 bytes (`withStackScratchWiped`), the
quadword standing for the return address and `save`'s 64 bytes (the
registers, then the block that held the last output block), which it zeroes
before returning. The code's calls use 3296 bytes below it, so 3368 in all. -/

/-- A state satisfying the precondition, without `save`. -/
def ctrFinalFrameSat : State := { ctrFinalSat with wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩] }

theorem ctrFinalFrameSat_pre : ∃ s, (Proof.Camellia.ctrFinalContractSk X86_64.abi 3368).pre s := by
  implies_sat [Proof.Camellia.ctrFinalContractSk, Spec.Camellia.ctrFinalSig, Spec.Camellia.ctrFinalPre,
    Proof.Camellia.ctrFinalPostSk, X86_64.abi, X86_64.argRegs] [ctrFinalFrameSat, ctrFinalSat]
    using ctrFinalFrameSat

theorem ctrFinal_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 72 .r9 8 ctrFinal)
      (Spec.Camellia.ctrFinalContract X86_64.abi 3368) :=
  Proof.Camellia.ctrFinal_of_sk <|
  X86_64.Verified.stackScratchWiped (sig := Spec.Camellia.ctrFinalSig) (nm := "save") (e := .u64)
    (n := 8) (pre := Spec.Camellia.ctrFinalPre X86_64.abi.ptrBits)
    (post := Proof.Camellia.ctrFinalPostSk X86_64.abi.ptrBits) (wa := true) (stack := 3296)
    (bytes := 72) ctrFinal_verified (by decide) (by decide) (by decide) ctrFinal_spSafe ctrFinal_xdepth
    (by decide) (Proof.Camellia.ctrFinalPostOut_local _) ctrFinalFrameSat_pre

end VG.Proof.Camellia.X86_64
