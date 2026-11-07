module

public import VerifiedGarbage.Impl.Sm4.PPC64LE.CtrFinal
public import VerifiedGarbage.Proof.Sm4.CtrFinal
public import VerifiedGarbage.Proof.Sm4.Scratch
public import VerifiedGarbage.Proof.Sm4.PPC64LE.CtrVerified
public import VerifiedGarbage.Proof.AesCfb.PPC64LE.Final
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
import VerifiedGarbage.Proof.AesCtr.PPC64LE.Final
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Sm4.PPC64LE.CtrLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Modes.CtrFinal
import VerifiedGarbage.Proof.Modes.PPC64LE.SeqFinal
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Impl.Sm4.PPC64LE.CtrFinal
meta import VerifiedGarbage.Proof.Sm4.CtrFinal
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.CtrVerified
meta import VerifiedGarbage.Proof.AesCfb.PPC64LE.Final
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
meta import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
meta import VerifiedGarbage.Impl.StackScratch.PPC64LE
meta import VerifiedGarbage.Proof.AesCtr.PPC64LE.Final
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesFrame
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.CtrLit
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Sm4.CtrCipher
meta import VerifiedGarbage.Proof.Modes.CtrFinal
meta import VerifiedGarbage.Proof.Modes.PPC64LE.SeqFinal
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesCbc.Spec
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# SM4-CTR of a message's last piece on PPC64LE

`ctrFinal_framed`: `vg_sm4_ctr_final` (`Impl/Sm4/PPC64LE/CtrFinal.lean`)
meets `Spec.Sm4.ctrFinalContract`.

The code is proven against `ctrFinalPPC64LE`, with the arguments
`(schedule = r3, ctr = r4, data = r5, len = r6, save = r7)`, a fifth argument
`save` (`r7`) of 80 bytes for its return address and its caller's registers
and a block of its own, and 3296 bytes of stack for its calls
(`ctrFinal_implies`: the shared contract with it), as a caller of
`vg_sm4_ctr`, framed by its own working space on the stack (`ctrFramed`),
through a contract of its own, `ctrF`, which the callee's shared contract
implies (`ctrF_implies`), with `WP.callAny` (the callee's frame is the 3296
bytes below the stack pointer, `ctr_sdepth`). It is AES-CTR's final
function's proof (`Proof/AesCtr/PPC64LE/Final.lean`) with SM4's arguments:

* `setup_wp`, `whole_wp`: the return address and the registers saved in
  `save`, whose address is kept in `r20`, and the call on the
  `n = len / 16` whole blocks (`KWhole`);
* `mid_wp`: if `u = len % 16` bytes are left, the block after the registers
  in `save` zeroed and the call on it (`tail_args_wp`, `tail_call_wp`), which
  leaves `CIPH_K(Tₙ₊₁)` there and `Tₙ₊₂` in `ctr`, and its first `u` bytes
  XORed into them (`Modes.PPC64LE.tailLoop_wp`, `tail_xor_wp`); what is left
  before the registers are restored is `KDone`;
* `end_wp`: the registers and the return address restored;
* `final_post`: `KDone` gives `Spec.Ctr.CryptFinal`
  (`Proof.Modes.CtrFinal.cryptFinal_of`), by SM4 with the schedule at
  `schedule`.

Constant time (`final_rel`): the blocks by the taint analysis, the calls by
the callee's constant time (`RelCT.callEx`), whose public arguments agree.

The frame of the registration needs the contract's postcondition to read the
memory on entry only within the function's buffers
(`Proof.Sm4.ctrFinalPost_local`).
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE.CtrFinal

open VG VG.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Impl.Sm4.PPC64LE (ctrFramed ctrCall ctrFinalSave ctrFinalMoves ctrFinalSetup ctrFinalTailMoves
  ctrFinalTailArgs ctrFinalTail ctrFinal)
open VG.Impl.AesCfb.PPC64LE (finalSaved finalRestore)
open VG.Impl.AesCtr.PPC64LE (zeroSlots tailKey)
open VG.Proof.AesCfb.PPC64LE.Final (Kept vars bytesAt_getD blocksAt_frame' saved_slots saved_fits
  shr4 shr4_shl4 sub_shl4 upd_gpr preserved_ne_r0 restore_eq)
open VG.Proof.AesCtr.PPC64LE.Final (zero_bytes one_toNat preserved_ne_args)
open VG.Proof.AesCbc.PPC64LE (callEntry_gpr' taintRegs wp_sp)

/-! ## The callee -/

/-- `vg_sm4_ctr(schedule = r3, ctr = r4, data = r5, n = r6)` with its 3296
bytes of stack. -/
def ctrF : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .r3, 128⟩
    let ctr : Region := ⟨s.gpr .r4, 16⟩
    let data : Region := ⟨s.gpr .r5, 16 * (s.gpr .r6).toNat⟩
    3296 ≤ s.sp.toNat ∧ s.rd = [sched] ∧ s.wr = [ctr, data] ∧ sched.Disjoint ctr ∧ sched.Disjoint data ∧
      ctr.Disjoint data ∧ (below s.sp 3296).Disjoint sched ∧ (below s.sp 3296).Disjoint ctr ∧
      (below s.sp 3296).Disjoint data ∧
      (s.gpr .r3).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + 16 * (s.gpr .r6).toNat ≤ 2 ^ 64
  post s s' :=
    Spec.Cbc.blocksAt s'.mem (s.gpr .r5) (s.gpr .r6).toNat =
        Spec.Ctr.crypt (Spec.Sm4.cipher (Spec.Sm4.scheduleAt s.mem (s.gpr .r3)))
          (bytesAt s.mem (s.gpr .r4) 16) (Spec.Cbc.blocksAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) ∧
      bytesAt s'.mem (s.gpr .r4) 16 = Spec.Ctr.next (bytesAt s.mem (s.gpr .r4) 16) (s.gpr .r6).toNat
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6

theorem ctrF_implies : (Spec.Sm4.ctrContract PPC64LE.abi 3296).Implies ctrF where
  pre s hs := by
    sig_pre [Spec.Sm4.ctrContract, Spec.Sm4.ctrSig, PPC64LE.abi, PPC64LE.argRegs]
    simp only [Nat.mul_comm (s.gpr .r6).toNat 16]
    exact hs
  post s s' _ h := by
    sig_reduce [Spec.Sm4.ctrContract, Spec.Sm4.ctrSig, PPC64LE.abi, PPC64LE.argRegs] at h
    simp only [BitVec.setWidth_eq] at h
    exact h
  pub s₁ s₂ _ _ h := by
    sig_reduce [Spec.Sm4.ctrContract, Spec.Sm4.ctrSig, PPC64LE.abi, PPC64LE.argRegs]
    obtain ⟨hsp, h0, h1, h2, h3⟩ := h
    exact ⟨hsp, fun _ _ => by rw [h0, h1, h2, h3], fun _ hr => absurd hr List.not_mem_nil⟩
  sat := ⟨Sm4.PPC64LE.modeFrameSat, by
    refine ⟨by decide, rfl, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), by decide, by decide, by decide⟩⟩

/-- The callee's frame is the 3296 bytes below the stack pointer. -/
theorem ctr_sdepth : sdepth ctrFramed = 3296 := by lit_decide

theorem ctr_hd : sdepth ctrFramed < 2 ^ 64 := by rw [ctr_sdepth]; decide

theorem ctr_ok : ∀ s, ctrF.pre s → ∃ t s', Exec isa ctrFramed s t s' ∧ abiPreserved s s' ∧ ctrF.post s s' :=
  (Sm4.PPC64LE.Modes.ctr_framed.of_implies ctrF_implies).1

theorem ctr_ct : ConstantTime isa ctrF.pre ctrF.pub ctrFramed :=
  (Sm4.PPC64LE.Modes.ctr_framed.of_implies ctrF_implies).2.1

/-! ## The contract -/

/-- The code's contract, with the arguments `(schedule = r3, ctr = r4,
data = r5, len = r6, save = r7)`, `save` of 80 bytes, and 3296 bytes of stack
for the calls: the data and the counter block as `Spec.Ctr.CryptFinal` says,
by SM4 with the schedule at `schedule`. -/
def ctrFinalPPC64LE : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .r3, 128⟩
    let ctr : Region := ⟨s.gpr .r4, 16⟩
    let data : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let sv : Region := ⟨s.gpr .r7, 80⟩
    let stack := below s.sp 3296
    3296 ≤ s.sp.toNat ∧ s.rd = [sched] ∧ s.wr = [ctr, data, sv] ∧
      sched.Disjoint ctr ∧ sched.Disjoint data ∧ sched.Disjoint sv ∧ ctr.Disjoint data ∧ ctr.Disjoint sv ∧
      data.Disjoint sv ∧
      stack.Disjoint sched ∧ stack.Disjoint ctr ∧ stack.Disjoint data ∧ stack.Disjoint sv ∧
      (s.gpr .r3).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧ (s.gpr .r7).toNat + 80 ≤ 2 ^ 64
  post s s' :=
    Spec.Ctr.CryptFinal (Spec.Sm4.cipher (Spec.Sm4.scheduleAt s.mem (s.gpr .r3)))
      s.mem s'.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6).toNat
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

/-- The contract the frame needs: the shared one, with `save`, 80 bytes, as a
fifth argument, and 3296 bytes of stack (`vg_sm4_ctr`'s frame). -/
abbrev ctrFinalScratchContract : Contract isa :=
  Sig.scratchContract PPC64LE.abi Spec.Sm4.ctrFinalSig "save" .u64 10 (Curry.const (fun _ => True) _)
    (Proof.Sm4.ctrFinalPost PPC64LE.abi.ptrBits) true 3296

/-- A state satisfying the precondition (no data). -/
def ctrFinalSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r7 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 80⟩]

theorem ctrFinal_implies : ctrFinalPPC64LE.Implies ctrFinalScratchContract := by
  sig_implies [ctrFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Sm4.ctrFinalSig, Proof.Sm4.ctrFinalPost, ctrFinalPPC64LE, PPC64LE.abi, PPC64LE.argRegs] [ctrFinalSat]
    using ctrFinalSat

/-! ## The arguments, by name -/

section
variable (s₀ : State)

abbrev fW : Addr := s₀.gpr .r3
abbrev fIv : Addr := s₀.gpr .r4
abbrev fD : Addr := s₀.gpr .r5
abbrev fL : Nat := (s₀.gpr .r6).toNat
/-- The number of whole blocks, and of the bytes after them. -/
abbrev fN : Nat := fL s₀ / 16
abbrev fU : Nat := fL s₀ % 16
/-- The data after the whole blocks. -/
abbrev fT : Addr := fD s₀ + BitVec.ofNat 64 (16 * fN s₀)
abbrev fData : Region := ⟨fD s₀, fL s₀⟩
abbrev fBlk : Region := ⟨fD s₀, 16 * fN s₀⟩
abbrev fTail : Region := ⟨fT s₀, fU s₀⟩
/-- The counter block and the whole blocks on entry. -/
abbrev fIv0 : List Byte := bytesAt s₀.mem (fIv s₀) 16
abbrev fBlks : List (List Byte) := Spec.Cbc.blocksAt s₀.mem (fD s₀) (fN s₀)

/-- `save`. -/
abbrev kV : Addr := s₀.gpr .r7
abbrev kSch : Region := ⟨fW s₀, 128⟩
abbrev kIv : Region := ⟨fIv s₀, 16⟩
abbrev kSv : Region := ⟨kV s₀, 80⟩
abbrev kSv64 : Region := ⟨kV s₀, 64⟩
/-- The block after the registers in `save`. -/
abbrev kBk : Addr := kV s₀ + BitVec.ofNat 64 64
abbrev kBlk : Region := ⟨kBk s₀, 16⟩
/-- The stack the calls use. -/
abbrev kStk : Region := below s₀.sp 3296
/-- The values saved: `r0` holds the return address. -/
abbrev kSaveG : Reg → BitVec 64 := (s₀.write .r0 s₀.lr).gpr
/-- The memory once the return address and the registers are saved. -/
abbrev kSvMem : Mem := Spill.saveMem s₀.mem (kV s₀) (kSaveG s₀) finalSaved
/-- The cipher on entry. -/
abbrev kCiph : Spec.Cbc.Cipher := Spec.Sm4.cipher (Spec.Sm4.scheduleAt s₀.mem (fW s₀))

/-- What the function writes after saving the registers, with the whole
blocks rather than the data; and with the data. -/
abbrev kW1 : List Region := [kIv s₀, fBlk s₀, kBlk s₀, kStk s₀]
abbrev kW : List Region := [kIv s₀, fData s₀, kBlk s₀, kStk s₀]
/-- What the function writes. -/
abbrev kBig : List Region := [kIv s₀, fData s₀, kSv s₀, kStk s₀]

end

/-- The precondition, by name. -/
structure KPre (s₀ : State) : Prop where
  sp : 3296 ≤ s₀.sp.toNat
  rd : s₀.rd = [kSch s₀]
  wr : s₀.wr = [kIv s₀, fData s₀, kSv s₀]
  sch_iv : (kSch s₀).Disjoint (kIv s₀)
  sch_data : (kSch s₀).Disjoint (fData s₀)
  sch_sv : (kSch s₀).Disjoint (kSv s₀)
  iv_data : (kIv s₀).Disjoint (fData s₀)
  iv_sv : (kIv s₀).Disjoint (kSv s₀)
  data_sv : (fData s₀).Disjoint (kSv s₀)
  stk_sch : (kStk s₀).Disjoint (kSch s₀)
  stk_iv : (kStk s₀).Disjoint (kIv s₀)
  stk_data : (kStk s₀).Disjoint (fData s₀)
  stk_sv : (kStk s₀).Disjoint (kSv s₀)
  sch_wrap : (fW s₀).toNat + 128 ≤ 2 ^ 64
  iv_wrap : (fIv s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (fD s₀).toNat + fL s₀ ≤ 2 ^ 64
  sv_wrap : (kV s₀).toNat + 80 ≤ 2 ^ 64

theorem KPre.of {s₀ : State} (h : ctrFinalPPC64LE.pre s₀) : KPre s₀ :=
  let ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := h
  ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩

/-! ## Regions and frames -/

theorem blk_sub (s₀ : State) : Region.Sub (fBlk s₀) (fData s₀) := Region.sub_prefix (Nat.mul_div_le _ _)

theorem tail_sub (s₀ : State) : Region.Sub (fTail s₀) (fData s₀) :=
  Offset.sub_base _ (by rw [Nat.div_add_mod])

theorem fN_eq (s₀ : State) : fN s₀ = fL s₀ / 16 := rfl
theorem fU_eq (s₀ : State) : fU s₀ = fL s₀ % 16 := rfl

theorem n_lt (s₀ : State) : fN s₀ < 2 ^ 64 := by
  have := (s₀.gpr .r6).isLt; have : fL s₀ = (s₀.gpr .r6).toNat := rfl; rw [fN_eq]; omega

theorem u_lt (s₀ : State) : fU s₀ < 16 := Nat.mod_lt _ (by decide)

theorem toNat_n (s₀ : State) : (BitVec.ofNat 64 (fN s₀)).toNat = fN s₀ := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (n_lt s₀)]

theorem sv64_sub (s₀ : State) : Region.Sub (kSv64 s₀) (kSv s₀) := Region.sub_prefix (by decide)
theorem blk_sv_sub (s₀ : State) : Region.Sub (kBlk s₀) (kSv s₀) := Offset.sub_base _ (by decide)

section
variable {s₀ : State} (hp : KPre s₀)
include hp

theorem KPre.blk_tail : (fBlk s₀).Disjoint (fTail s₀) := by
  have := hp.data_wrap
  have := Nat.div_add_mod (fL s₀) 16
  exact Offset.base_disjoint _ (Nat.le_refl _) (by rw [fN_eq, fU_eq]; omega)

theorem KPre.blk_wrap : (fD s₀).toNat + 16 * fN s₀ ≤ 2 ^ 64 := by
  have := hp.data_wrap; have := Nat.mul_div_le (fL s₀) 16; rw [fN_eq]; omega

theorem KPre.bk_toNat : (kBk s₀).toNat = (kV s₀).toNat + 64 := by
  have := hp.sv_wrap
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 64) (by decide), Nat.mod_eq_of_lt (by omega)]

end

theorem svMem_frame (s₀ : State) : Frame [kSv s₀] s₀.mem (kSvMem s₀) :=
  (Spill.saveMem_frame_base (n := 64) (by decide) (by decide) _ _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨kSv s₀, by simp, sv64_sub s₀⟩

/-- The slots of the registers miss the block. -/
theorem slot_blk (s₀ : State) :
    ∀ p ∈ finalSaved, Region.Disjoint ⟨kV s₀ + BitVec.ofNat 64 p.2, 8⟩ (kBlk s₀) := by
  intro p hp'
  have := saved_slots p hp'
  exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)

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

theorem KPre.sch_big {s₀ : State} (hp : KPre s₀) : ∀ r ∈ kBig s₀, (kSch s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.sch_iv
  · exact hp.sch_data
  · exact hp.sch_sv
  · exact hp.stk_sch.symm

/-- The schedule, from memory that agrees with the entry's on it. -/
theorem sched_of {s₀ : State} {rs : List Region} {m₀ m : Mem} (hf : Frame rs m₀ m)
    (hd : ∀ r ∈ rs, (kSch s₀).Disjoint r) : Spec.Sm4.scheduleAt m (fW s₀) = Spec.Sm4.scheduleAt m₀ (fW s₀) :=
  Proof.Sm4.scheduleAt_frame hf hd

/-- A call's frame, within the regions it was given and the stack. -/
theorem call_frame {s₀ s s' : State} (hsp : s.sp = s₀.sp) {wr : List Region}
    (hf : Frame (wr ++ [below s.sp (sdepth ctrFramed)]) s.mem s'.mem) :
    Frame (wr ++ [kStk s₀]) s.mem s'.mem := by
  rw [ctr_sdepth, hsp] at hf; exact hf

/-! ## Saving the registers -/

theorem moves_wp {s : State} {Φ : State → Prop}
    (k : ∀ s', s'.gpr .r14 = s.gpr .r3 → s'.gpr .r16 = s.gpr .r4 → s'.gpr .r20 = s.gpr .r7 →
      s'.gpr .r31 = s.gpr .r5 + (s.gpr .r6 >>> 4 <<< 4) →
      s'.gpr .r30 = s.gpr .r6 - (s.gpr .r6 >>> 4 <<< 4) → s'.gpr .r6 = s.gpr .r6 >>> 4 →
      (∀ r, r ≠ .r14 → r ≠ .r16 → r ≠ .r20 → r ≠ .r10 → r ≠ .r11 →
        r ≠ .r31 → r ≠ .r30 → r ≠ .r6 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → Φ s') :
    WP isa (.block ctrFinalMoves) s Φ := by
  unfold ctrFinalMoves Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ =>
    wp_lsr (by decide) fun s₄ u₄ => wp_lsl (by decide) fun s₅ u₅ => wp_add fun s₆ u₆ =>
    wp_sub fun s₇ u₇ => wp_mr fun s₈ u₈ => wp_nil ?_
  refine k s₈ ?_ ?_ ?_ ?_ ?_ ?_ (fun r h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ => ?_) ?_ ?_ ?_
  all_goals try (simp only [upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅,
    upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte]; done)
  · simp only [upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄,
      upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, ↓reduceIte]
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-- What saving the registers and setting up the arguments leaves. -/
structure KSetup (s₀ s : State) : Prop where
  r14 : s.gpr .r14 = fW s₀
  r16 : s.gpr .r16 = fIv s₀
  r20 : s.gpr .r20 = kV s₀
  r30 : s.gpr .r30 = BitVec.ofNat 64 (fU s₀)
  r31 : s.gpr .r31 = fT s₀
  r3 : s.gpr .r3 = fW s₀
  r4 : s.gpr .r4 = fIv s₀
  r5 : s.gpr .r5 = fD s₀
  r6 : s.gpr .r6 = BitVec.ofNat 64 (fN s₀)
  kept : Kept s₀ s
  mem : s.mem = kSvMem s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem setup_wp {s₀ : State} (hp : KPre s₀) : WP isa (.block ctrFinalSetup) s₀ (KSetup s₀) := by
  show WP isa (.block (.mflr .r0 :: (Spill.saveCode .r7 finalSaved ++ ctrFinalMoves))) _ _
  refine WP.cons exec_mflr (Spill.save_ok (b := .r7) (l := finalSaved) (by decide) saved_fits
    (fun p hp' => ?_) ?_)
  · show InRegions s₀.wr (kV s₀ + BitVec.ofNat 64 p.2) 8
    rw [hp.wr]
    have := saved_slots p hp'
    exact ⟨kSv s₀, by simp, Offset.contains_base _ (by omega) (by have := hp.sv_wrap; omega)⟩
  refine moves_wp fun s' r14 r16 r20 r31 r30 r6 keep mem rd wr => ?_
  have g₀ (r : Reg) (hr : r ≠ .r0) : (s₀.write .r0 s₀.lr).gpr r = s₀.gpr r := by
    simp [State.write, hr]
  have k (r : Reg) (h₁ : r ≠ .r14) (h₃ : r ≠ .r16) (h₅ : r ≠ .r20)
      (h₆ : r ≠ .r10) (h₇ : r ≠ .r11) (h₈ : r ≠ .r31) (h₉ : r ≠ .r30) (h₁₀ : r ≠ .r6) (h₀ : r ≠ .r0) :
      s'.gpr r = s₀.gpr r := (keep r h₁ h₃ h₅ h₆ h₇ h₈ h₉ h₁₀).trans (g₀ r h₀)
  exact {
    r14 := r14.trans (g₀ .r3 (by decide))
    r16 := r16.trans (g₀ .r4 (by decide))
    r20 := r20.trans (g₀ .r7 (by decide))
    r30 := by rw [r30, g₀ .r6 (by decide), shr4_shl4, sub_shl4]
    r31 := by rw [r31, g₀ .r5 (by decide), g₀ .r6 (by decide), shr4_shl4]
    r3 := k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    r4 := k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    r5 := k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    r6 := by rw [r6, g₀ .r6 (by decide), shr4]
    kept := fun r hr hv => by
      obtain ⟨h3, -, -, h6, -, -, -⟩ := preserved_ne_args hr
      obtain ⟨-, -, -, h10, h11, h14, -, h16, -, h20, h30, h31⟩ :=
        Proof.AesCfb.PPC64LE.Final.preserved_ne' hr hv
      exact k r h14 h16 h20 h10 h11 h31 h30 h6 (preserved_ne_r0 r hr)
    mem := mem
    rd := rd
    wr := wr }

/-! ## The whole blocks -/

theorem whole_pre {s₀ : State} (hp : KPre s₀) {s : State} (h : KSetup s₀ s) (hsp : s.sp = s₀.sp) :
    ctrF.pre (s.callEntry.withRegions [kSch s₀] [kIv s₀, fBlk s₀]) ∧
      Covers ([kSch s₀] ++ [kIv s₀, fBlk s₀]) (s.rd ++ s.wr) ∧ Covers [kIv s₀, fBlk s₀] s.wr := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [ctrF, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
      State.callEntry_sp, callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs), h.r3, h.r4, h.r5, h.r6, hsp, toNat_n]
    exact ⟨hp.sp, trivial, trivial, hp.sch_iv, hp.sch_data.sub_right (blk_sub s₀),
      hp.iv_data.sub_right (blk_sub s₀), hp.stk_sch, hp.stk_iv, hp.stk_data.sub_right (blk_sub s₀),
      hp.sch_wrap, hp.iv_wrap, hp.blk_wrap⟩
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

/-- The schedule, the counter block and the whole blocks once the registers
are saved, as on entry. -/
theorem sv_bytes {s₀ : State} (hp : KPre s₀) :
    Spec.Sm4.scheduleAt (kSvMem s₀) (fW s₀) = Spec.Sm4.scheduleAt s₀.mem (fW s₀) ∧
      bytesAt (kSvMem s₀) (fIv s₀) 16 = fIv0 s₀ ∧ Spec.Cbc.blocksAt (kSvMem s₀) (fD s₀) (fN s₀) = fBlks s₀ := by
  have ef := svMem_frame s₀
  exact ⟨sched_of ef (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.sch_sv),
    Proof.Cmac.bytesAt_frame ef (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_sv) (by decide),
    blocksAt_frame' ef (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.data_sv.sub_left (blk_sub s₀))⟩

/-- What the call on the whole blocks leaves. -/
structure KWhole (s₀ s : State) : Prop where
  r14 : s.gpr .r14 = fW s₀
  r16 : s.gpr .r16 = fIv s₀
  r20 : s.gpr .r20 = kV s₀
  r30 : s.gpr .r30 = BitVec.ofNat 64 (fU s₀)
  r31 : s.gpr .r31 = fT s₀
  kept : Kept s₀ s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (kW1 s₀) (kSvMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) = Spec.Ctr.crypt (kCiph s₀) (fIv0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (fIv0 s₀) (fN s₀)

theorem whole_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KSetup s₀ s) (hsp : s.sp = s₀.sp) :
    WP isa ctrCall s (KWhole s₀) := by
  obtain ⟨eK, eIv, eB⟩ := sv_bytes hp
  obtain ⟨hpre, hc, hw⟩ := whole_pre hp h hsp
  refine WP.callAny (k := ctrF) ctr_ok (rd := [kSch s₀]) (wr := [kIv s₀, fBlk s₀]) hpre hc hw ?_ ctr_hd
  intro s' rd' wr' _ fr' cs' post₂
  have fr := call_frame hsp fr'
  rw [h.mem] at fr
  simp only [ctrF, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
    h.r3, h.r4, h.r5, h.r6, toNat_n, h.mem] at post₂
  rw [eK, eIv, eB] at post₂
  exact ⟨by rw [cs' .r14 (by decide), h.r14], by rw [cs' .r16 (by decide), h.r16],
    by rw [cs' .r20 (by decide), h.r20], by rw [cs' .r30 (by decide), h.r30],
    by rw [cs' .r31 (by decide), h.r31],
    fun r hr hv => by rw [cs' r hr, h.kept r hr hv],
    by rw [rd', h.rd], by rw [wr', h.wr],
    fr.mono fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp [h],
    post₂.1, post₂.2⟩

/-! ## The partial last block -/

theorem eval_u {s₀ s : State} (h : KWhole s₀ s) :
    isa.eval (.zero .d .r30) s = some (decide (fU s₀ = 0)) := by
  rw [eval_zero, h.r30, ofNat_beq_zero (by have := u_lt s₀; omega)]

/-- The arguments of `vg_sm4_ctr` on the block. -/
theorem tailMoves_wp {s : State} {Φ : State → Prop}
    (k : ∀ s', s'.gpr .r3 = s.gpr .r14 → s'.gpr .r4 = s.gpr .r16 →
      s'.gpr .r5 = s.gpr .r20 + BitVec.ofNat 64 64 → s'.gpr .r6 = BitVec.ofNat 64 1 →
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → Φ s') :
    WP isa (.block ctrFinalTailMoves) s Φ := by
  unfold ctrFinalTailMoves Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_addi (by decide) (by decide) fun s₃ u₃ =>
    wp_li (by decide) fun s₄ u₄ => wp_nil ?_
  refine k s₄ ?_ ?_ ?_ ?_ (fun r h₃ h₄ h₅ h₆ => ?_) ?_ ?_ ?_
  all_goals try (simp only [upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁,
    reduceCtorEq, ↓reduceIte]; done)
  · simp only [upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, h₃, h₄, h₅, h₆, ↓reduceIte]
  · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-- What zeroing the block and setting up the arguments leaves. -/
structure KArgs (s₀ s : State) : Prop where
  r3 : s.gpr .r3 = fW s₀
  r4 : s.gpr .r4 = fIv s₀
  r5 : s.gpr .r5 = kBk s₀
  r6 : s.gpr .r6 = BitVec.ofNat 64 1
  r20 : s.gpr .r20 = kV s₀
  r30 : s.gpr .r30 = BitVec.ofNat 64 (fU s₀)
  r31 : s.gpr .r31 = fT s₀
  kept : Kept s₀ s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (kW1 s₀) (kSvMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) = Spec.Ctr.crypt (kCiph s₀) (fIv0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (fIv0 s₀) (fN s₀)
  zero : bytesAt s.mem (kBk s₀) 16 = List.replicate 16 0

theorem zero_frame (s₀ : State) (m : Mem) (g : Reg → BitVec 64) :
    Frame [kBlk s₀] m (Spill.saveMem m (kV s₀) g zeroSlots) :=
  Spill.saveMem_frame (lo := 64) (n := 16) (fun p hp' => by
    simp only [zeroSlots, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> decide) (by decide) m _ g

theorem tail_args_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KWhole s₀ s) :
    WP isa (.block ctrFinalTailArgs) s (KArgs s₀) := by
  show WP isa (.block (.li .r9 0 :: (Spill.saveCode .r20 zeroSlots ++ ctrFinalTailMoves))) _ _
  refine wp_li (by decide) fun s₁ u₁ => ?_
  have h20 : s₁.gpr .r20 = kV s₀ := by rw [u₁.other _ (by decide), h.r20]
  have hw : ∀ p ∈ zeroSlots, InRegions s₁.wr (s₁.gpr .r20 + BitVec.ofNat 64 p.2) 8 := by
    intro p hp'
    rw [u₁.wr, h.wr, hp.wr, h20]
    simp only [zeroSlots, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact ⟨kSv s₀, by simp, Offset.contains_base _ (by decide) (by have := hp.sv_wrap; omega)⟩
    · exact ⟨kSv s₀, by simp, Offset.contains_base _ (by decide) (by have := hp.sv_wrap; omega)⟩
  refine Spill.save_ok (by decide) (by decide) hw ?_
  refine tailMoves_wp fun s' r3 r4 r5 r6 o mem rd wr => ?_
  have c (r : Reg) (hr : r ∈ preserved) : s'.gpr r = s.gpr r := by
    obtain ⟨h3, h4, h5, h6, -, -, h9⟩ := preserved_ne_args hr
    rw [o r h3 h4 h5 h6]
    exact u₁.other r h9
  have hm : s'.mem = Spill.saveMem s.mem (kV s₀) s₁.gpr zeroSlots := by
    rw [mem]; show Spill.saveMem s₁.mem _ _ _ = _; rw [u₁.mem, h20]
  have fz : Frame [kBlk s₀] s.mem s'.mem := by rw [hm]; exact zero_frame s₀ _ _
  have ivZ : ∀ r ∈ [kBlk s₀], (kIv s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_sv.sub_right (blk_sv_sub s₀)
  have blkZ : ∀ r ∈ [kBlk s₀], (fBlk s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (hp.data_sv.sub_left (blk_sub s₀)).sub_right (blk_sv_sub s₀)
  have g₁ (r : Reg) (hr : r ≠ .r9) : s₁.gpr r = s.gpr r := u₁.other r hr
  refine ⟨by rw [r3, show ({ s₁ with mem := _ } : State).gpr = s₁.gpr from rfl, g₁ _ (by decide), h.r14],
    by rw [r4, show ({ s₁ with mem := _ } : State).gpr = s₁.gpr from rfl, g₁ _ (by decide), h.r16],
    by rw [r5, show ({ s₁ with mem := _ } : State).gpr = s₁.gpr from rfl, h20],
    r6,
    by rw [c .r20 (by decide), h.r20], by rw [c .r30 (by decide), h.r30], by rw [c .r31 (by decide), h.r31],
    fun r hr hv => by rw [c r hr, h.kept r hr hv],
    by rw [rd, show ({ s₁ with mem := _ } : State).rd = s₁.rd from rfl, u₁.rd, h.rd],
    by rw [wr, show ({ s₁ with mem := _ } : State).wr = s₁.wr from rfl, u₁.wr, h.wr], ?_, ?_, ?_, ?_⟩
  · exact h.frame.trans (fz.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  · rw [blocksAt_frame' fz blkZ]; exact h.blocks
  · rw [Proof.Cmac.bytesAt_frame fz ivZ (by decide), h.ctr]
  · have z₁ : s₁.gpr .r9 = (0 : BitVec 64) := u₁.gpr
    rw [hm, show Spill.saveMem s.mem (kV s₀) s₁.gpr zeroSlots =
        ((s.mem.writeW (kBk s₀) (s₁.gpr .r9)).writeW (kBk s₀ + BitVec.ofNat 64 8) (s₁.gpr .r9)) by
      simp only [Spill.saveMem, zeroSlots, Offset.add_add], z₁]
    exact zero_bytes _ _

theorem tail_pre {s₀ : State} (hp : KPre s₀) {s : State} (h : KArgs s₀ s) (hsp : s.sp = s₀.sp) :
    ctrF.pre (s.callEntry.withRegions [kSch s₀] [kIv s₀, kBlk s₀]) ∧
      Covers ([kSch s₀] ++ [kIv s₀, kBlk s₀]) (s.rd ++ s.wr) ∧ Covers [kIv s₀, kBlk s₀] s.wr := by
  have bs := blk_sv_sub s₀
  refine ⟨?_, ?_, ?_⟩
  · simp only [ctrF, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
      State.callEntry_sp, callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs), h.r3, h.r4, h.r5, h.r6, hsp, one_toNat, Nat.mul_one]
    have := hp.sv_wrap
    exact ⟨hp.sp, trivial, trivial, hp.sch_iv, hp.sch_sv.sub_right bs, hp.iv_sv.sub_right bs, hp.stk_sch,
      hp.stk_iv, hp.stk_sv.sub_right bs, hp.sch_wrap, hp.iv_wrap, by rw [hp.bk_toNat]; omega⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨kSch s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨kIv s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨kSv s₀, by simp, 64, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨kIv s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨kSv s₀, by simp, 64, by simp, by simp⟩

/-- What the call on the block leaves. -/
structure KCall (s₀ s : State) : Prop where
  r20 : s.gpr .r20 = kV s₀
  r30 : s.gpr .r30 = BitVec.ofNat 64 (fU s₀)
  r31 : s.gpr .r31 = fT s₀
  kept : Kept s₀ s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (kW1 s₀) (kSvMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) = Spec.Ctr.crypt (kCiph s₀) (fIv0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (Spec.Ctr.next (fIv0 s₀) (fN s₀)) 1
  out : bytesAt s.mem (kBk s₀) 16 = kCiph s₀ (Spec.Ctr.next (fIv0 s₀) (fN s₀))

theorem cipher_length (k : Spec.Sm4.Schedule) (b : List Byte) : (Spec.Sm4.cipher k b).length = 16 := by
  simp [Spec.Sm4.cipher]

theorem tail_call_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KArgs s₀ s) (hsp : s.sp = s₀.sp) :
    WP isa ctrCall s (KCall s₀) := by
  obtain ⟨hpre, hc, hw⟩ := tail_pre hp h hsp
  have big := big_of (kW1_kW h.frame)
  have eK := sched_of big hp.sch_big
  refine WP.callAny (k := ctrF) ctr_ok (rd := [kSch s₀]) (wr := [kIv s₀, kBlk s₀]) hpre hc hw ?_ ctr_hd
  intro s' rd' wr' _ fr' cs' post₂
  have fr := call_frame hsp fr'
  simp only [ctrF, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
    h.r3, h.r4, h.r5, h.r6, one_toNat, h.ctr] at post₂
  rw [eK] at post₂
  have fc : Frame (kW1 s₀) s.mem s'.mem := fr.sub fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  refine ⟨by rw [cs' .r20 (by decide), h.r20], by rw [cs' .r30 (by decide), h.r30],
    by rw [cs' .r31 (by decide), h.r31], fun r hr hv => by rw [cs' r hr, h.kept r hr hv],
    by rw [rd', h.rd], by rw [wr', h.wr], h.frame.trans fc, ?_, post₂.2, ?_⟩
  · rw [blocksAt_frame' fr fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.iv_data.symm.sub_left (blk_sub s₀)
      · exact (hp.data_sv.sub_left (blk_sub s₀)).sub_right (blk_sv_sub s₀)
      · exact hp.stk_data.symm.sub_left (blk_sub s₀)]
    exact h.blocks
  · exact Modes.CtrFinal.bytesAt_of_blocksAt_one (cipher_length _) h.zero post₂.1

/-- What the function leaves before restoring the registers. -/
structure KDone (s₀ s : State) : Prop where
  r20 : s.gpr .r20 = kV s₀
  kept : Kept s₀ s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (kW s₀) (kSvMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) = Spec.Ctr.crypt (kCiph s₀) (fIv0 s₀) (fBlks s₀)
  tail : ∀ q < fU s₀, s.mem (fT s₀ + BitVec.ofNat 64 q) = s₀.mem (fT s₀ + BitVec.ofNat 64 q) ^^^
    (kCiph s₀ (Spec.Ctr.next (fIv0 s₀) (fN s₀))).getD q 0
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (fIv0 s₀) (if fU s₀ = 0 then fN s₀ else fN s₀ + 1)

theorem done_of_zero {s₀ s : State} (h : KWhole s₀ s) (hu : fU s₀ = 0) : KDone s₀ s :=
  ⟨h.r20, h.kept, h.rd, h.wr, kW1_kW h.frame, h.blocks, fun q hq => absurd hq (by omega), by
    rw [ite_eq_left hu, h.ctr]⟩

theorem toNat_tail {s₀ : State} (hp : KPre s₀) (hu : fU s₀ ≠ 0) : (fT s₀).toNat = (fD s₀).toNat + 16 * fN s₀ := by
  have := hp.data_wrap
  have := Nat.div_add_mod (fL s₀) 16
  have eN := fN_eq s₀
  have eU := fU_eq s₀
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * fN s₀) (by omega),
    Nat.mod_eq_of_lt (by omega)]

/-- The XOR of the partial last block. -/
abbrev xorCode : Prog isa :=
  .seq (.block tailKey) (.loop (.block Impl.Modes.PPC64LE.tailByte) (.nonzero .d .r30))

theorem tail_xor_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KCall s₀ s) (hu : fU s₀ ≠ 0) :
    WP isa xorCode s (KDone s₀) := by
  refine WP.seq (wp_addi (by decide) (by decide) fun s₁ u₁ => wp_nil ?_)
  have hU := u_lt s₀
  have hT := toNat_tail hp hu
  have hL := Nat.div_add_mod (fL s₀) 16
  have hDw := hp.data_wrap
  have hVw := hp.sv_wrap
  have hB := hp.bk_toNat
  have eN := fN_eq s₀
  have eU := fU_eq s₀
  have xp : Proof.Modes.PPC64LE.XPre s₁ (kBk s₀) (fT s₀) (fU s₀) := {
    fitR := by omega
    disj := (((hp.data_sv.sub_left (tail_sub s₀)).sub_right (blk_sv_sub s₀)).sub_right
      (Region.sub_prefix (by omega))).symm
    rdK := fun q hq => by
      rw [u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr]
      refine ⟨kSv s₀, by simp, ?_⟩
      rw [Offset.add_add]
      exact Offset.contains_base _ (by omega) (by omega)
    wrR := fun q hq => by
      rw [u₁.wr, h.wr, hp.wr]
      refine ⟨fData s₀, by simp, ?_⟩
      rw [show fT s₀ + BitVec.ofNat 64 q = fD s₀ + BitVec.ofNat 64 (16 * fN s₀ + q) from Offset.add_add _ _ _]
      exact Offset.contains_base _ (by omega) (by omega) }
  have x0 : Proof.Modes.PPC64LE.XInv s₁ (kBk s₀) (fT s₀) (fU s₀) 0 s₁ := {
    r8 := by rw [u₁.gpr, h.r20]; exact (BitVec.add_zero _).symm
    r31 := by rw [u₁.other _ (by decide), h.r31]; exact (BitVec.add_zero _).symm
    r30 := by rw [u₁.other _ (by decide), h.r30, Nat.sub_zero]
    lt := by omega
    data := fun q _ => by rw [ite_eq_right (Nat.not_lt_zero q)]
    frame := Frame.refl _ _
    rd := rfl
    wr := rfl
    gpr := fun _ _ _ _ _ _ => rfl }
  refine WP.mono (Proof.Modes.PPC64LE.tailLoop_wp xp x0) fun s' d => ?_
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
  have df : Frame [fTail s₀] s.mem s'.mem := by rw [← u₁.mem]; exact d.frame
  have g (r : Reg) (h8 : r ≠ .r8) (h9 : r ≠ .r9) (h10 : r ≠ .r10) (h30 : r ≠ .r30) (h31 : r ≠ .r31) :
      s'.gpr r = s.gpr r := by
    rw [d.gpr r h8 h9 h10 h30 h31, u₁.other r h8]
  refine ⟨by rw [g .r20 (by decide) (by decide) (by decide) (by decide) (by decide), h.r20],
    fun r hr hv => ?_, by rw [d.rd, u₁.rd, h.rd], by rw [d.wr, u₁.wr, h.wr], ?_, ?_, fun q hq => ?_, ?_⟩
  · obtain ⟨-, h8, h9, h10, -, -, -, -, -, -, h30, h31⟩ := Proof.AesCfb.PPC64LE.Final.preserved_ne' hr hv
    rw [g r h8 h9 h10 h30 h31, h.kept r hr hv]
  · exact (kW1_kW h.frame).trans (df.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨fData s₀, by simp, tail_sub s₀⟩)
  · rw [blocksAt_frame' df fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.blk_tail]
    exact h.blocks
  · rw [d.data q hq, u₁.mem, h.frame.bytes tailD hlen hq, (svMem_frame s₀).bytes tailS hlen hq,
      ← bytesAt_getD s.mem (kBk s₀) (show q < 16 by omega), h.out]
  · rw [ite_eq_right hu, Proof.Cmac.bytesAt_frame df ivT (by decide), h.ctr, ← AesCtr.next_add]

theorem mid_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KWhole s₀ s) (hsp : s.sp = s₀.sp) :
    WP isa (.ite (.zero .d .r30) (.block []) ctrFinalTail) s (KDone s₀) := by
  by_cases hu : fU s₀ = 0
  · exact WP.ite true (by rw [eval_u h, decide_eq_true hu]) (fun _ => WP.block_nil (done_of_zero h hu))
      (fun h => by cases h)
  · refine WP.ite false (by rw [eval_u h, decide_eq_false hu]) (fun h => by cases h) fun _ => ?_
    exact WP.seq (WP.mono (wp_sp (tail_args_wp hp h)) fun _ h₁ =>
      WP.seq (WP.mono (tail_call_wp hp h₁.1 (h₁.2.trans hsp)) fun _ h₂ => tail_xor_wp hp h₂ hu))

/-! ## Restoring the registers -/

theorem end_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KDone s₀ s) :
    WP isa (.block finalRestore) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧ s'.mem = s.mem := by
  have hs : Spill.Saved (kV s₀) (kSaveG s₀) finalSaved s.mem :=
    (Spill.saveMem_saved (by decide) s₀.mem (kV s₀) (kSaveG s₀)).frame h.frame fun p hp' r hr => by
      have hsub : Region.Sub ⟨kV s₀ + BitVec.ofNat 64 p.2, 8⟩ (kSv s₀) :=
        Offset.sub_base _ (by have := saved_slots p hp'; omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.iv_sv.symm.sub_left hsub
      · exact hp.data_sv.symm.sub_left hsub
      · exact slot_blk s₀ p hp'
      · exact hp.stk_sv.symm.sub_left hsub
  rw [restore_eq]
  refine Spill.restore_ok (b := .r20) (l := finalSaved) (by decide) h.r20 saved_fits (by decide)
    (fun p hp' => ?_) hs fun s₃ r₃ => ?_
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    have := saved_slots p hp'
    exact ⟨kSv s₀, by simp, Offset.contains_base _ (by omega) (by have := hp.sv_wrap; omega)⟩
  refine WP.cons exec_mtlr (wp_nil ⟨fun r hr => ?_, ?_, r₃.mem⟩)
  · show s₃.gpr r = _
    have h0 : kSaveG s₀ r = s₀.gpr r := by
      show (s₀.write .r0 s₀.lr).gpr r = _
      simp [State.write, preserved_ne_r0 r hr]
    rw [r₃.gpr_of (r := r) ?_, h0]
    by_cases hv : r ∈ vars
    · left
      simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · right; rw [h.kept r hr hv, h0]
  · show s₃.gpr .r0 = _
    rw [r₃.gpr (.r0, 0) (by decide)]; rfl

/-! ## The whole function -/

theorem final_wp {s₀ : State} (hp : KPre s₀) :
    WP isa ctrFinal s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧ ∃ s₁, KDone s₀ s₁ ∧ s'.mem = s₁.mem := by
  refine WP.seq (WP.mono (wp_sp (setup_wp hp)) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (wp_sp (whole_wp hp h₁.1 h₁.2)) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (mid_wp hp h₂.1 (h₂.2.trans h₁.2)) fun s₃ h₃ => ?_)
  exact WP.mono (end_wp hp h₃) fun _ ⟨g, l, m⟩ => ⟨g, l, s₃, h₃, m⟩

/-- `Spec.Ctr.CryptFinal`, from what the function leaves. -/
theorem final_post {s₀ s₁ s' : State} (h : KDone s₀ s₁) (hm : s'.mem = s₁.mem) : ctrFinalPPC64LE.post s₀ s' := by
  show Spec.Ctr.CryptFinal (kCiph s₀) s₀.mem s'.mem (fIv s₀) (fD s₀) (fL s₀)
  exact Modes.CtrFinal.cryptFinal_of (cipher_length _) (by rw [hm]; exact h.blocks)
    (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.ctr)

theorem final_correct (s : State) (hs : ctrFinalPPC64LE.pre s) :
    ∃ t s', Exec isa ctrFinal s t s' ∧ abiPreserved s s' ∧ ctrFinalPPC64LE.post s s' := by
  obtain ⟨t, s', he, hg, hl, s₁, h₁, hm⟩ := final_wp (KPre.of hs)
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hl⟩, final_post h₁ hm⟩

/-! ## Constant time -/

theorem setup_taint : ∃ h, (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (.block ctrFinalSetup) h).isSome = true := ⟨_, by taint_decide⟩

theorem tailArgs_taint : ∃ h, (taint.check (Taint.ofRegs [.r14, .r16, .r20])
    (.block ctrFinalTailArgs) h).isSome = true := ⟨_, by taint_decide⟩

theorem xor_taint : ∃ h, (taint.check (Taint.ofRegs [.r20, .r30, .r31]) xorCode h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (taint.check (Taint.ofRegs [.r20]) (.block finalRestore) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem final_rel {s₀ s₀' : State} (h0 : ctrFinalPPC64LE.pre s₀) (h0' : ctrFinalPPC64LE.pre s₀')
    (hq : ctrFinalPPC64LE.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') ctrFinal fun _ _ => True := by
  have hp := KPre.of h0
  have hp' := KPre.of h0'
  obtain ⟨qW, qIv, qD, qL, qV, qSp⟩ := hq
  have qU : fU s₀ = fU s₀' := by simp only [fU, fL, qL]
  have qN : fN s₀ = fN s₀' := by simp only [fN, fL, qL]
  have qT : fT s₀ = fT s₀' := by simp only [fT, fD, qD, qN]
  -- The registers saved and the arguments set up.
  obtain ⟨_, t₁⟩ := setup_taint
  have r₁ := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨qSp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) t₁).wp
    (F₁ := fun (s : State) => KSetup s₀ s ∧ s.sp = s₀.sp) (F₂ := fun (s : State) => KSetup s₀' s ∧ s.sp = s₀'.sp)
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨wp_sp (setup_wp hp), wp_sp (setup_wp hp')⟩
  -- The whole blocks.
  have r₂ := (RelCT.callEx (k := ctrF) (n := "vg_sm4_ctr") ctr_ok ctr_ct
    (P := fun a b => (KSetup s₀ a ∧ a.sp = s₀.sp) ∧ (KSetup s₀' b ∧ b.sp = s₀'.sp)) fun a b ⟨ha, hb⟩ => by
      obtain ⟨pa, ca, wa⟩ := whole_pre hp ha.1 ha.2
      obtain ⟨pb, cb, wb⟩ := whole_pre hp' hb.1 hb.2
      refine ⟨_, _, _, _, pa, pb, ?_, ca, wa, cb, wb⟩
      simp only [ctrF, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
        callEntry_gpr' _ (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r4 ∉ linkRegs),
        callEntry_gpr' _ (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r6 ∉ linkRegs),
        ha.1.r3, ha.1.r4, ha.1.r5, ha.1.r6, ha.2, hb.1.r3, hb.1.r4, hb.1.r5, hb.1.r6, hb.2]
      rw [fW, fW, fIv, fIv, fD, fD, qW, qIv, qD, qSp, qN]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial).wp
    (F₁ := fun (s : State) => KWhole s₀ s ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => KWhole s₀' s ∧ s.sp = s₀'.sp)
    fun a b h => ⟨WP.mono (wp_sp (whole_wp hp h.1.1 h.1.2)) fun _ x => ⟨x.1, x.2.trans h.1.2⟩,
      WP.mono (wp_sp (whole_wp hp' h.2.1 h.2.2)) fun _ x => ⟨x.1, x.2.trans h.2.2⟩⟩
  -- The partial last block.
  obtain ⟨_, t₃⟩ := tailArgs_taint
  obtain ⟨_, t₄⟩ := xor_taint
  have tail (hu : fU s₀ ≠ 0) : RelCT isa
      (fun a b => (KWhole s₀ a ∧ a.sp = s₀.sp) ∧ (KWhole s₀' b ∧ b.sp = s₀'.sp))
      ctrFinalTail fun a b => (KDone s₀ a ∧ a.sp = s₀.sp) ∧ (KDone s₀' b ∧ b.sp = s₀'.sp) := by
    have hu' : fU s₀' ≠ 0 := qU ▸ hu
    have a₁ := (taintRegs
      (P := fun a b => (KWhole s₀ a ∧ a.sp = s₀.sp) ∧ (KWhole s₀' b ∧ b.sp = s₀'.sp)) _
      (fun a b h => ⟨by rw [h.1.2, h.2.2, qSp], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.1.1.r14, h.2.1.r14, fW, fW, qW]
        · rw [h.1.1.r16, h.2.1.r16, fIv, fIv, qIv]
        · rw [h.1.1.r20, h.2.1.r20, kV, kV, qV]⟩) t₃).wp
      (F₁ := fun (s : State) => KArgs s₀ s ∧ s.sp = s₀.sp) (F₂ := fun (s : State) => KArgs s₀' s ∧ s.sp = s₀'.sp)
      fun a b h => ⟨WP.mono (wp_sp (tail_args_wp hp h.1.1)) fun _ x => ⟨x.1, x.2.trans h.1.2⟩,
        WP.mono (wp_sp (tail_args_wp hp' h.2.1)) fun _ x => ⟨x.1, x.2.trans h.2.2⟩⟩
    have a₂ := (RelCT.callEx (k := ctrF) (n := "vg_sm4_ctr") ctr_ok ctr_ct
      (P := fun a b => (KArgs s₀ a ∧ a.sp = s₀.sp) ∧ (KArgs s₀' b ∧ b.sp = s₀'.sp)) fun a b ⟨ha, hb⟩ => by
        obtain ⟨pa, ca, wa⟩ := tail_pre hp ha.1 ha.2
        obtain ⟨pb, cb, wb⟩ := tail_pre hp' hb.1 hb.2
        refine ⟨_, _, _, _, pa, pb, ?_, ca, wa, cb, wb⟩
        simp only [ctrF, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
          callEntry_gpr' _ (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r4 ∉ linkRegs),
          callEntry_gpr' _ (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r6 ∉ linkRegs),
          ha.1.r3, ha.1.r4, ha.1.r5, ha.1.r6, ha.2, hb.1.r3, hb.1.r4, hb.1.r5, hb.1.r6, hb.2]
        rw [fW, fW, fIv, fIv, kBk, kBk, kV, kV, qW, qIv, qV, qSp]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial).wp
      (F₁ := fun (s : State) => KCall s₀ s ∧ s.sp = s₀.sp) (F₂ := fun (s : State) => KCall s₀' s ∧ s.sp = s₀'.sp)
      fun a b h => ⟨WP.mono (wp_sp (tail_call_wp hp h.1.1 h.1.2)) fun _ x => ⟨x.1, x.2.trans h.1.2⟩,
        WP.mono (wp_sp (tail_call_wp hp' h.2.1 h.2.2)) fun _ x => ⟨x.1, x.2.trans h.2.2⟩⟩
    have a₃ := (taintRegs
      (P := fun a b => (KCall s₀ a ∧ a.sp = s₀.sp) ∧ (KCall s₀' b ∧ b.sp = s₀'.sp)) _
      (fun a b h => ⟨by rw [h.1.2, h.2.2, qSp], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.1.1.r20, h.2.1.r20, kV, kV, qV]
        · rw [h.1.1.r30, h.2.1.r30, qU]
        · rw [h.1.1.r31, h.2.1.r31, qT]⟩) t₄).wp
      (F₁ := fun (s : State) => KDone s₀ s ∧ s.sp = s₀.sp) (F₂ := fun (s : State) => KDone s₀' s ∧ s.sp = s₀'.sp)
      fun a b h => ⟨WP.mono (wp_sp (tail_xor_wp hp h.1.1 hu)) fun _ x => ⟨x.1, x.2.trans h.1.2⟩,
        WP.mono (wp_sp (tail_xor_wp hp' h.2.1 hu')) fun _ x => ⟨x.1, x.2.trans h.2.2⟩⟩
    exact (a₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
      ((a₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq (a₃.mono (fun _ _ h => h) fun _ _ h => h.2))
  have r₃ : RelCT isa
      (fun a b => (KWhole s₀ a ∧ a.sp = s₀.sp) ∧ (KWhole s₀' b ∧ b.sp = s₀'.sp))
      (.ite (.zero .d .r30) (.block []) ctrFinalTail)
      (fun a b => (KDone s₀ a ∧ a.sp = s₀.sp) ∧ (KDone s₀' b ∧ b.sp = s₀'.sp)) := by
    refine RelCT.ite (fun a b h => by rw [eval_u h.1.1, eval_u h.2.1, qU]) ?_ ?_
    · refine RelCT.block_nil fun a b h => ?_
      have h0 : fU s₀ = 0 := by
        have := h.2; rw [eval_u h.1.1.1] at this; simpa using this
      exact ⟨⟨done_of_zero h.1.1.1 h0, h.1.1.2⟩, ⟨done_of_zero h.1.2.1 (qU ▸ h0), h.1.2.2⟩⟩
    · refine (RelCT.exists_ fun (hu : fU s₀ ≠ 0) => tail hu).mono
        (fun a b h => ⟨?_, h.1⟩) fun _ _ h => h
      have := h.2; rw [eval_u h.1.1.1] at this; simpa using this
  -- The registers restored.
  obtain ⟨_, t₅⟩ := restore_taint
  have r₄ := taintRegs
    (P := fun a b => (KDone s₀ a ∧ a.sp = s₀.sp) ∧ (KDone s₀' b ∧ b.sp = s₀'.sp)) _
    (fun a b h => ⟨by rw [h.1.2, h.2.2, qSp], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.r20, h.2.1.r20, kV, kV, qV]⟩) t₅
  exact (r₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((r₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    (r₃.seq r₄))

theorem final_ct : ConstantTime isa ctrFinalPPC64LE.pre ctrFinalPPC64LE.pub ctrFinal :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (final_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Verified -/

theorem ctrFinal_verified : Verified PPC64LE.target ctrFinal ctrFinalScratchContract :=
  Verified.of_correct final_correct final_ct ctrFinal_implies

/-! ## With `save` on the stack

The final function has four argument words, so `save` is its fifth, in `r7`:
it runs its code in a frame of 112 bytes on the stack
(`withStackScratchWiped`), its 32-byte header and `save`'s 80 bytes (the
registers, then the block that held the last output block), which it zeroes
before returning. Its calls use 3296 bytes below it, so 3408 in all. -/

/-- A state satisfying the shared contract's precondition. -/
def ctrFinalFrameSat : State := { ctrFinalSat with wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩] }

theorem ctrFinalFrameSat_pre : ∃ s, (Spec.Sm4.ctrFinalContract PPC64LE.abi (3296 + 112)).pre s := by
  implies_sat [Spec.Sm4.ctrFinalContract, Spec.Sm4.ctrFinalSig, PPC64LE.abi, PPC64LE.argRegs]
    [ctrFinalFrameSat, ctrFinalSat] using ctrFinalFrameSat

theorem ctrFinal_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 112 .r7 10 ctrFinal)
      (Spec.Sm4.ctrFinalContract PPC64LE.abi 3408) := by
  rw [Proof.Sm4.ctrFinalContract_eq]
  exact PPC64LE.Verified.stackScratchWiped (sig := Spec.Sm4.ctrFinalSig) (nm := "save") (e := .u64) (n := 10)
    (post := Proof.Sm4.ctrFinalPost PPC64LE.abi.ptrBits) (wa := true) (stack := 3296) (bytes := 112)
    (words := 10) ctrFinal_verified (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (ctrFinalPost_local _)
    (Proof.Sm4.ctrFinalPostOut_local _) ctrFinalFrameSat_pre

end VG.Proof.Sm4.PPC64LE.CtrFinal
