module

public import VerifiedGarbage.Impl.Sm4.AArch64.CtrFinal
public import VerifiedGarbage.Proof.Sm4.CtrFinal
public import VerifiedGarbage.Proof.Sm4.Scratch
public import VerifiedGarbage.Proof.Sm4.AArch64.CtrVerified
public import VerifiedGarbage.Proof.AesCfb.AArch64.Final
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.AesCtr.AArch64.Final
import VerifiedGarbage.Proof.AesCtr.AArch64.CT
import VerifiedGarbage.Proof.Sm4.AArch64.Lit
import VerifiedGarbage.Proof.Modes.CtrFinal
import VerifiedGarbage.Proof.Modes.AArch64.FbFinal
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCbc.AArch64.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Impl.Sm4.AArch64.CtrFinal
meta import VerifiedGarbage.Proof.Sm4.CtrFinal
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Sm4.AArch64.CtrVerified
meta import VerifiedGarbage.Proof.AesCfb.AArch64.Final
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.AArch64.Spill
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.AesCtr.AArch64.Final
meta import VerifiedGarbage.Proof.AesCtr.AArch64.CT
meta import VerifiedGarbage.Proof.Sm4.AArch64.Lit
meta import VerifiedGarbage.Proof.Modes.CtrFinal
meta import VerifiedGarbage.Proof.Modes.AArch64.FbFinal
meta import VerifiedGarbage.Proof.Modes.AArch64.Steps
meta import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Proof.Modes.AArch64.Xor
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesCbc.Spec
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Block
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# SM4-CTR of a message's last piece on AArch64

`ctrFinal_framed`: `vg_sm4_ctr_final` (`Impl/Sm4/AArch64/CtrFinal.lean`) meets
`Spec.Sm4.ctrFinalContract`.

The code is proven against `ctrFinalAArch64`, with the arguments
`(schedule = x0, ctr = x1, data = x2, len = x3, save = x4)`, a fifth argument `save` (`x4`) of 80 bytes for its caller's registers and
return address and a block of its own, and 3264 bytes of stack for its
calls (`ctrFinal_implies`: the shared contract with it), as a caller of
`vg_sm4_ctr`, framed by its own working space on the stack (`ctrFramed`),
through a contract of its own, `ctrF`, which the callee's shared contract
implies (`ctrF_implies`), with `WP.callF` (the callee's frames lie within the
stack, `ctr_depth`). It is AES-CTR's final function's proof
(`Proof/AesCtr/AArch64/Final.lean`) with SM4's arguments:

* `setup_wp`, `whole_wp`: the registers saved in `save`, whose address is
  kept in `x25`, and the call on the `n = len / 16` whole blocks (`KWhole`);
* `mid_wp`: if `u = len % 16` bytes are left, the block after the registers
  in `save` zeroed and the call on it (`tail_args_wp`, `tail_call_wp`), which
  leaves `CIPH_K(Tₙ₊₁)` there and `Tₙ₊₂` in `ctr`, and its first `u` bytes
  XORed into them (`Modes.AArch64.xorLoop_wp`, `tail_xor_wp`); what is left
  before the registers are restored is `KDone`;
* `end_wp`: the registers restored;
* `final_post`: `KDone` gives `Spec.Ctr.CryptFinal`
  (`Proof.Modes.CtrFinal.cryptFinal_of`), by SM4 with the schedule at `schedule`.

Constant time (`final_rel`): the blocks by the taint analysis, the calls by
the callee's constant time (`RelCT.callEx`), whose public arguments agree.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.CtrFinal

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.AArch64.RegUpd
open VG.Impl.Sm4.AArch64 (ctrFramed ctrFinalSave ctrFinalMoves ctrFinalSetup ctrFinalTailMoves
  ctrFinalTailArgs ctrFinalTail ctrFinal)
open VG.Impl.AesCfb.AArch64 (finalSaved finalRestore)
open VG.Impl.AesCtr.AArch64 (zeroSlots tailKey)

/-! ## The callee -/

/-- `vg_sm4_ctr(schedule = x0, ctr = x1, data = x2, n = x3)` with its 3264
bytes of stack. -/
def ctrF : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 128⟩
    let ctr : Region := ⟨s.gpr .x1, 16⟩
    let data : Region := ⟨s.gpr .x2, 16 * (s.gpr .x3).toNat⟩
    3264 ≤ s.sp.toNat ∧ s.rd = [sched] ∧ s.wr = [ctr, data] ∧ sched.Disjoint ctr ∧ sched.Disjoint data ∧
      ctr.Disjoint data ∧ (below s.sp 3264).Disjoint sched ∧ (below s.sp 3264).Disjoint ctr ∧
      (below s.sp 3264).Disjoint data ∧
      (s.gpr .x0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 16 * (s.gpr .x3).toNat ≤ 2 ^ 64
  post s s' :=
    Spec.Cbc.blocksAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
        Spec.Ctr.crypt (Spec.Sm4.cipher (Spec.Sm4.scheduleAt s.mem (s.gpr .x0)))
          (bytesAt s.mem (s.gpr .x1) 16) (Spec.Cbc.blocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) ∧
      bytesAt s'.mem (s.gpr .x1) 16 = Spec.Ctr.next (bytesAt s.mem (s.gpr .x1) 16) (s.gpr .x3).toNat
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3

theorem ctrF_implies : (Spec.Sm4.ctrContract AArch64.abi 3264).Implies ctrF where
  pre s hs := by
    sig_pre [Spec.Sm4.ctrContract, Spec.Sm4.ctrSig, AArch64.abi, AArch64.argRegs]
    simp only [Nat.mul_comm (s.gpr .x3).toNat 16]
    exact hs
  post s s' _ h := by
    sig_reduce [Spec.Sm4.ctrContract, Spec.Sm4.ctrSig, AArch64.abi, AArch64.argRegs] at h
    simp only [BitVec.setWidth_eq] at h
    exact h
  pub s₁ s₂ _ _ h := by
    sig_reduce [Spec.Sm4.ctrContract, Spec.Sm4.ctrSig, AArch64.abi, AArch64.argRegs]
    obtain ⟨hsp, h0, h1, h2, h3⟩ := h
    exact ⟨hsp, fun _ _ => by rw [h0, h1, h2, h3], fun _ hr => absurd hr List.not_mem_nil⟩
  sat := ⟨Sm4.AArch64.ctrFrameSat, by
    refine ⟨by decide, rfl, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), by decide, by decide, by decide⟩⟩

theorem ctr_depth : 16 * ctrFramed.aarch64Depth ≤ 3264 := by lit_decide

theorem ctr_ok : ∀ s, ctrF.pre s → ∃ t s', Exec isa ctrFramed s t s' ∧ abiPreserved s s' ∧ ctrF.post s s' :=
  (Sm4.AArch64.ctr_framed.of_implies ctrF_implies).1

theorem ctr_ct : ConstantTime isa ctrF.pre ctrF.pub ctrFramed :=
  (Sm4.AArch64.ctr_framed.of_implies ctrF_implies).2.1

/-! ## The contract -/

/-- The code's contract, with the arguments `(schedule = x0, ctr = x1,
data = x2, len = x3, save = x4)`, `save` of 80 bytes, and 3264 bytes of stack
for the calls: the data and the counter block as `Spec.Ctr.CryptFinal` says,
by SM4 with the schedule at `schedule`. -/
def ctrFinalAArch64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 128⟩
    let ctr : Region := ⟨s.gpr .x1, 16⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let sv : Region := ⟨s.gpr .x4, 80⟩
    let stack := below s.sp 3264
    3264 ≤ s.sp.toNat ∧ s.rd = [sched] ∧ s.wr = [ctr, data, sv] ∧
      sched.Disjoint ctr ∧ sched.Disjoint data ∧ sched.Disjoint sv ∧ ctr.Disjoint data ∧ ctr.Disjoint sv ∧
      data.Disjoint sv ∧
      stack.Disjoint sched ∧ stack.Disjoint ctr ∧ stack.Disjoint data ∧ stack.Disjoint sv ∧
      (s.gpr .x0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 80 ≤ 2 ^ 64
  post s s' :=
    Spec.Ctr.CryptFinal (Spec.Sm4.cipher (Spec.Sm4.scheduleAt s.mem (s.gpr .x0)))
      s.mem s'.mem (s.gpr .x1) (s.gpr .x2) (s.gpr .x3).toNat
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- The contract the frame needs: the shared one, with `save`, 80 bytes, as a
fifth argument, and 3264 bytes of stack (`vg_sm4_ctr`'s frame). -/
abbrev ctrFinalScratchContract : Contract isa :=
  Sig.scratchContract AArch64.abi Spec.Sm4.ctrFinalSig "save" .u64 10 (Curry.const (fun _ => True) _)
    (Proof.Sm4.ctrFinalPost AArch64.abi.ptrBits) true 3264

/-- A state satisfying the precondition (no data). -/
def ctrFinalSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 80⟩]

theorem ctrFinal_implies : ctrFinalAArch64.Implies ctrFinalScratchContract := by
  sig_implies [ctrFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Sm4.ctrFinalSig, Proof.Sm4.ctrFinalPost, ctrFinalAArch64, AArch64.abi, AArch64.argRegs] [ctrFinalSat]
    using ctrFinalSat

/-! ## The arguments, by name -/

open VG.Proof.AesCfb.AArch64.Final (Kept cs_of bytesAt_getD blocksAt_frame' saved_slots saved_fits
  WP.sp_eq shr4 shr4_shl4 sub_shl4)
open VG.Proof.AesCtr.AArch64.Final (zero_bytes zero_ok one_toNat lo32_next_of)

section
variable (s₀ : State)

abbrev fW : Addr := s₀.gpr .x0
abbrev fIv : Addr := s₀.gpr .x1
abbrev fD : Addr := s₀.gpr .x2
abbrev fL : Nat := (s₀.gpr .x3).toNat
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
abbrev kV : Addr := s₀.gpr .x4
abbrev kSch : Region := ⟨fW s₀, 128⟩
abbrev kIv : Region := ⟨fIv s₀, 16⟩
abbrev kSv : Region := ⟨kV s₀, 80⟩
abbrev kSv64 : Region := ⟨kV s₀, 64⟩
/-- The block after the registers in `save`. -/
abbrev kBk : Addr := kV s₀ + BitVec.ofNat 64 64
abbrev kBlk : Region := ⟨kBk s₀, 16⟩
/-- The stack the calls use. -/
abbrev kStk : Region := below s₀.sp 3264
/-- The memory once the registers are saved. -/
abbrev kSvMem : Mem := Spill.saveMem s₀.mem (kV s₀) s₀.gpr finalSaved
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
  sp : 3264 ≤ s₀.sp.toNat
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

theorem KPre.of {s₀ : State} (h : ctrFinalAArch64.pre s₀) : KPre s₀ :=
  let ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := h
  ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩

/-! ## Regions and frames -/

theorem blk_sub (s₀ : State) : Region.Sub (fBlk s₀) (fData s₀) := Region.sub_prefix (Nat.mul_div_le _ _)

theorem tail_sub (s₀ : State) : Region.Sub (fTail s₀) (fData s₀) :=
  Offset.sub_base _ (by rw [Nat.div_add_mod])

theorem fN_eq (s₀ : State) : fN s₀ = fL s₀ / 16 := rfl
theorem fU_eq (s₀ : State) : fU s₀ = fL s₀ % 16 := rfl

theorem n_lt (s₀ : State) : fN s₀ < 2 ^ 64 := by
  have := (s₀.gpr .x3).isLt; have : fL s₀ = (s₀.gpr .x3).toNat := rfl; rw [fN_eq]; omega

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

/-- The stack a call of `vg_sm4_ctr` uses lies within the stack. -/
theorem stk_sub (s₀ : State) : Region.Sub (below s₀.sp (16 * ctrFramed.aarch64Depth)) (kStk s₀) :=
  fun x hx => Offset.below_mono s₀.sp ctr_depth (by decide) x hx

/-! ## Saving the registers -/

theorem moves_ok (s : State) :
    ∃ s', runBlock isa ctrFinalMoves s = some s' ∧
      s'.gpr .x19 = s.gpr .x0 ∧ s'.gpr .x21 = s.gpr .x1 ∧ s'.gpr .x25 = s.gpr .x4 ∧
      s'.gpr .x22 = s.gpr .x2 + (s.gpr .x3 >>> 4 <<< 4) ∧ s'.gpr .x23 = s.gpr .x3 - (s.gpr .x3 >>> 4 <<< 4) ∧
      s'.gpr .x3 = s.gpr .x3 >>> 4 ∧
      (∀ r, r ≠ .x19 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x25 → r ≠ .x3 →
        r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [ctrFinalMoves, Impl.AesCbc.AArch64.mov], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    by simp [gpr_write], by simp [gpr_write], fun r h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ => ?_, rfl, rfl, rfl, rfl⟩
  simp [gpr_write, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]

/-- What saving the registers and setting up the arguments leaves. -/
structure KSetup (s₀ s : State) : Prop where
  x19 : s.gpr .x19 = fW s₀
  x21 : s.gpr .x21 = fIv s₀
  x22 : s.gpr .x22 = fT s₀
  x23 : s.gpr .x23 = BitVec.ofNat 64 (fU s₀)
  x25 : s.gpr .x25 = kV s₀
  x0 : s.gpr .x0 = fW s₀
  x1 : s.gpr .x1 = fIv s₀
  x2 : s.gpr .x2 = fD s₀
  x3 : s.gpr .x3 = BitVec.ofNat 64 (fN s₀)
  kept : Kept s₀ s
  sp : s.sp = s₀.sp
  mem : s.mem = kSvMem s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem setup_wp {s₀ : State} (hp : KPre s₀) : WP isa (.block ctrFinalSetup) s₀ (KSetup s₀) := by
  have hw : ∀ p ∈ finalSaved, InRegions s₀.wr (s₀.gpr .x4 + BitVec.ofNat 64 p.2) 8 := by
    intro p hp'
    rw [hp.wr]
    have := saved_slots p hp'
    exact ⟨kSv s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  show WP isa (.block (Spill.saveCode .x4 finalSaved ++ ctrFinalMoves)) _ _
  refine Spill.save_ok saved_fits hw ?_
  refine WP.mono (WP.of_runBlock (moves_ok _))
    fun s' ⟨x19, x21, x25, x22, x23, x3, keep, sp, mem, rd, wr⟩ => ?_
  have k (r : Reg) (h₁ : r ≠ .x19) (h₂ : r ≠ .x21) (h₃ : r ≠ .x22) (h₄ : r ≠ .x23) (h₅ : r ≠ .x25)
      (h₆ : r ≠ .x3) (h₇ : r ≠ .x9) (h₈ : r ≠ .x10) :
      s'.gpr r = s₀.gpr r := keep r h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  exact ⟨x19, x21, by rw [x22, shr4_shl4], by rw [x23, shr4_shl4, sub_shl4], x25,
    k .x0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    k .x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    k .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    by rw [x3, shr4],
    fun r hr => by
      rcases hr with rfl | rfl | rfl <;>
        exact k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide),
    sp, mem, rd, wr⟩

/-! ## The whole blocks -/

theorem whole_pre {s₀ : State} (hp : KPre s₀) {s : State} (h : KSetup s₀ s) :
    ctrF.pre (s.callEntry.withRegions [kSch s₀] [kIv s₀, fBlk s₀]) ∧
      Covers ([kSch s₀] ++ [kIv s₀, fBlk s₀]) (s.rd ++ s.wr) ∧ Covers [kIv s₀, fBlk s₀] s.wr := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [ctrF, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
      State.callEntry_sp, AesCbc.AArch64.callEntry_x0, AesCbc.AArch64.callEntry_x1, AesCbc.AArch64.callEntry_x2,
      AesCbc.AArch64.callEntry_x3, h.x0, h.x1, h.x2, h.x3, h.sp, toNat_n]
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
  x19 : s.gpr .x19 = fW s₀
  x21 : s.gpr .x21 = fIv s₀
  x22 : s.gpr .x22 = fT s₀
  x23 : s.gpr .x23 = BitVec.ofNat 64 (fU s₀)
  x25 : s.gpr .x25 = kV s₀
  kept : Kept s₀ s
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (kW1 s₀) (kSvMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) = Spec.Ctr.crypt (kCiph s₀) (fIv0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (fIv0 s₀) (fN s₀)

/-- A call's frame, within the regions it was given and the stack. -/
theorem call_frame {s₀ s s' : State} (hsp : s.sp = s₀.sp) {wr : List Region}
    (hf : Frame (wr ++ [below s.sp (16 * ctrFramed.aarch64Depth)]) s.mem s'.mem) :
    Frame (wr ++ [kStk s₀]) s.mem s'.mem :=
  hf.sub fun r hr => by
    rcases List.mem_append.mp hr with h | h
    · exact ⟨r, List.mem_append_left _ h, fun _ h => h⟩
    · simp only [List.mem_singleton] at h; subst h
      exact ⟨kStk s₀, by simp, by rw [hsp]; exact stk_sub s₀⟩

theorem whole_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KSetup s₀ s) :
    WP isa (.call "vg_sm4_ctr" ctrFramed) s (KWhole s₀) := by
  obtain ⟨eK, eIv, eB⟩ := sv_bytes hp
  obtain ⟨hpre, hc, hw⟩ := whole_pre hp h
  refine WP.callF (k := ctrF) ctr_ok (rd := [kSch s₀]) (wr := [kIv s₀, fBlk s₀]) hpre hc hw ?_
    (by have := ctr_depth; omega)
  intro s' rd' wr' sp' fr' cs' post₂
  have fr := call_frame h.sp fr'
  rw [h.mem] at fr
  simp only [ctrF, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    AesCbc.AArch64.callEntry_x0, AesCbc.AArch64.callEntry_x1, AesCbc.AArch64.callEntry_x2,
    AesCbc.AArch64.callEntry_x3, h.x0, h.x1, h.x2, h.x3, toNat_n, h.mem] at post₂
  rw [eK, eIv, eB] at post₂
  exact ⟨by rw [cs_of cs' .x19 (by simp), h.x19], by rw [cs_of cs' .x21 (by simp), h.x21], by rw [cs_of cs' .x22 (by simp), h.x22],
    by rw [cs_of cs' .x23 (by simp), h.x23], by rw [cs_of cs' .x25 (by simp), h.x25],
    fun r hr => by rw [cs_of cs' r (by rcases hr with rfl | rfl | rfl <;> simp), h.kept r hr],
    by rw [sp', h.sp], by rw [rd', h.rd], by rw [wr', h.wr],
    fr.mono fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp [h],
    post₂.1, post₂.2⟩

/-! ## The partial last block -/

theorem eval_u {s₀ s : State} (h : KWhole s₀ s) :
    isa.eval (.zero .x .x23) s = some (decide (fU s₀ = 0)) := by
  rw [Proof.Modes.AArch64.eval_zero, h.x23, Proof.Modes.AArch64.ofNat_beq_zero (by have := u_lt s₀; omega)]

theorem tailMoves_ok (s : State) :
    ∃ s', runBlock isa ctrFinalTailMoves s = some s' ∧
      s'.gpr .x0 = s.gpr .x19 ∧ s'.gpr .x1 = s.gpr .x21 ∧ s'.gpr .x2 = s.gpr .x25 + BitVec.ofNat 64 64 ∧
      s'.gpr .x3 = 1 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [ctrFinalTailMoves], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]

/-- What zeroing the block and setting up the arguments leaves. -/
structure KArgs (s₀ s : State) : Prop where
  x0 : s.gpr .x0 = fW s₀
  x1 : s.gpr .x1 = fIv s₀
  x2 : s.gpr .x2 = kBk s₀
  x3 : s.gpr .x3 = 1
  x22 : s.gpr .x22 = fT s₀
  x23 : s.gpr .x23 = BitVec.ofNat 64 (fU s₀)
  x25 : s.gpr .x25 = kV s₀
  kept : Kept s₀ s
  sp : s.sp = s₀.sp
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
  obtain ⟨s₁, r₁, z₁, k₁, sp₁, m₁, rd₁, wr₁⟩ := zero_ok s
  show WP isa (.block ([.movz .x .x9 0 0] ++ (Spill.saveCode .x25 zeroSlots ++ ctrFinalTailMoves))) _ _
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₁, r₁, ?_⟩)
  have h25 : s₁.gpr .x25 = kV s₀ := by rw [k₁ _ (by decide), h.x25]
  have hw : ∀ p ∈ zeroSlots, InRegions s₁.wr (s₁.gpr .x25 + BitVec.ofNat 64 p.2) 8 := by
    intro p hp'
    rw [wr₁, h.wr, hp.wr, h25]
    simp only [zeroSlots, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact ⟨kSv s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩
    · exact ⟨kSv s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  refine Spill.save_ok (by decide) hw ?_
  refine WP.mono (WP.of_runBlock (tailMoves_ok _))
    fun s' ⟨x0, x1, x2, x3, cs, sp, mem, rd, wr⟩ => ?_
  have c (r : Reg) (hr : r = .x19 ∨ r = .x20 ∨ r = .x21 ∨ r = .x22 ∨ r = .x23 ∨ r = .x24 ∨ r = .x25 ∨
      r = .x26 ∨ r = .x27 ∨ r = .x28) : s'.gpr r = s.gpr r := by
    rw [cs r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    exact k₁ r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hm : s'.mem = Spill.saveMem s.mem (kV s₀) s₁.gpr zeroSlots := by
    rw [mem]; show Spill.saveMem s₁.mem _ _ _ = _; rw [m₁, h25]
  have fz : Frame [kBlk s₀] s.mem s'.mem := by rw [hm]; exact zero_frame s₀ _ _
  have ivZ : ∀ r ∈ [kBlk s₀], (kIv s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_sv.sub_right (blk_sv_sub s₀)
  have blkZ : ∀ r ∈ [kBlk s₀], (fBlk s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (hp.data_sv.sub_left (blk_sub s₀)).sub_right (blk_sv_sub s₀)
  refine ⟨by rw [x0]; exact (k₁ _ (by decide)).trans h.x19, by rw [x1]; exact (k₁ _ (by decide)).trans h.x21,
    by rw [x2, h25], x3,
    by rw [c .x22 (by simp), h.x22], by rw [c .x23 (by simp), h.x23], by rw [c .x25 (by simp), h.x25],
    fun r hr => by rw [c r (by rcases hr with rfl | rfl | rfl <;> simp), h.kept r hr],
    by rw [sp, show ({ s₁ with mem := _ } : State).sp = s₁.sp from rfl, sp₁, h.sp],
    by rw [rd, show ({ s₁ with mem := _ } : State).rd = s₁.rd from rfl, rd₁, h.rd],
    by rw [wr, show ({ s₁ with mem := _ } : State).wr = s₁.wr from rfl, wr₁, h.wr], ?_, ?_, ?_, ?_⟩
  · exact h.frame.trans (fz.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  · rw [blocksAt_frame' fz blkZ]; exact h.blocks
  · rw [Proof.Cmac.bytesAt_frame fz ivZ (by decide), h.ctr]
  · rw [hm, show Spill.saveMem s.mem (kV s₀) s₁.gpr zeroSlots =
        ((s.mem.writeW (kBk s₀) (s₁.gpr .x9)).writeW (kBk s₀ + BitVec.ofNat 64 8) (s₁.gpr .x9)) by
      simp only [Spill.saveMem, zeroSlots, Offset.add_add], z₁]
    exact zero_bytes _ _

theorem tail_pre {s₀ : State} (hp : KPre s₀) {s : State} (h : KArgs s₀ s) :
    ctrF.pre (s.callEntry.withRegions [kSch s₀] [kIv s₀, kBlk s₀]) ∧
      Covers ([kSch s₀] ++ [kIv s₀, kBlk s₀]) (s.rd ++ s.wr) ∧ Covers [kIv s₀, kBlk s₀] s.wr := by
  have bs := blk_sv_sub s₀
  refine ⟨?_, ?_, ?_⟩
  · simp only [ctrF, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
      State.callEntry_sp, AesCbc.AArch64.callEntry_x0, AesCbc.AArch64.callEntry_x1, AesCbc.AArch64.callEntry_x2,
      AesCbc.AArch64.callEntry_x3, h.x0, h.x1, h.x2, h.x3, h.sp, one_toNat, Nat.mul_one]
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
  x22 : s.gpr .x22 = fT s₀
  x23 : s.gpr .x23 = BitVec.ofNat 64 (fU s₀)
  x25 : s.gpr .x25 = kV s₀
  kept : Kept s₀ s
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (kW1 s₀) (kSvMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) = Spec.Ctr.crypt (kCiph s₀) (fIv0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (Spec.Ctr.next (fIv0 s₀) (fN s₀)) 1
  out : bytesAt s.mem (kBk s₀) 16 = kCiph s₀ (Spec.Ctr.next (fIv0 s₀) (fN s₀))

theorem cipher_length (k : Spec.Sm4.Schedule) (b : List Byte) : (Spec.Sm4.cipher k b).length = 16 := by
  simp [Spec.Sm4.cipher]

theorem tail_call_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KArgs s₀ s) :
    WP isa (.call "vg_sm4_ctr" ctrFramed) s (KCall s₀) := by
  obtain ⟨hpre, hc, hw⟩ := tail_pre hp h
  have big := big_of (kW1_kW h.frame)
  have eK := sched_of big hp.sch_big
  refine WP.callF (k := ctrF) ctr_ok (rd := [kSch s₀]) (wr := [kIv s₀, kBlk s₀]) hpre hc hw ?_
    (by have := ctr_depth; omega)
  intro s' rd' wr' sp' fr' cs' post₂
  have fr := call_frame h.sp fr'
  simp only [ctrF, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    AesCbc.AArch64.callEntry_x0, AesCbc.AArch64.callEntry_x1, AesCbc.AArch64.callEntry_x2,
    AesCbc.AArch64.callEntry_x3, h.x0, h.x1, h.x2, h.x3, one_toNat, h.ctr] at post₂
  rw [eK] at post₂
  have fc : Frame (kW1 s₀) s.mem s'.mem := fr.sub fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  refine ⟨by rw [cs_of cs' .x22 (by simp), h.x22], by rw [cs_of cs' .x23 (by simp), h.x23],
    by rw [cs_of cs' .x25 (by simp), h.x25],
    fun r hr => by rw [cs_of cs' r (by rcases hr with rfl | rfl | rfl <;> simp), h.kept r hr],
    by rw [sp', h.sp], by rw [rd', h.rd], by rw [wr', h.wr], h.frame.trans fc, ?_, post₂.2, ?_⟩
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
  x25 : s.gpr .x25 = kV s₀
  kept : Kept s₀ s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (kW s₀) (kSvMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) = Spec.Ctr.crypt (kCiph s₀) (fIv0 s₀) (fBlks s₀)
  tail : ∀ q < fU s₀, s.mem (fT s₀ + BitVec.ofNat 64 q) = s₀.mem (fT s₀ + BitVec.ofNat 64 q) ^^^
    (kCiph s₀ (Spec.Ctr.next (fIv0 s₀) (fN s₀))).getD q 0
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (fIv0 s₀) (if fU s₀ = 0 then fN s₀ else fN s₀ + 1)

theorem done_of_zero {s₀ s : State} (h : KWhole s₀ s) (hu : fU s₀ = 0) : KDone s₀ s :=
  ⟨h.x25, h.kept, h.rd, h.wr, kW1_kW h.frame, h.blocks, fun q hq => absurd hq (by omega), by
    rw [ite_eq_left hu, h.ctr]⟩

theorem toNat_tail {s₀ : State} (hp : KPre s₀) (hu : fU s₀ ≠ 0) : (fT s₀).toNat = (fD s₀).toNat + 16 * fN s₀ := by
  have := hp.data_wrap
  have := Nat.div_add_mod (fL s₀) 16
  have eN := fN_eq s₀
  have eU := fU_eq s₀
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * fN s₀) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem tail_xor_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KCall s₀ s) (hu : fU s₀ ≠ 0) :
    WP isa (.seq (.block tailKey) (.loop (.block (Impl.Modes.AArch64.xorByte .x22 .x23)) (.nonzero .x .x23))) s
      (KDone s₀) := by
  obtain ⟨s₁, run₁, x9₁, o₁, mem₁, rd₁, wr₁⟩ := Proof.Modes.AArch64.addImm_ok s .x9 .x25 (v := 64) (by decide)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hU := u_lt s₀
  have hT := toNat_tail hp hu
  have hL := Nat.div_add_mod (fL s₀) 16
  have hDw := hp.data_wrap
  have hVw := hp.sv_wrap
  have eN := fN_eq s₀
  have eU := fU_eq s₀
  have xp : Proof.Modes.AArch64.XPre s₁ (kBk s₀) (fT s₀) (fU s₀) .x22 .x23 := {
    small := by omega
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
    d9 := by decide
    d6 := by decide
    d7 := by decide }
  have x0 : Proof.Modes.AArch64.XInv s₁ (kBk s₀) (fT s₀) (fU s₀) .x22 .x23 0 s₁ := {
    x9 := by rw [x9₁, h.x25]; exact (BitVec.add_zero _).symm
    dat := by rw [o₁ _ (by decide), h.x22]; exact (BitVec.add_zero _).symm
    left := by rw [o₁ _ (by decide), h.x23, Nat.sub_zero]
    lt := by omega
    data := fun q _ => by rw [ite_eq_right (Nat.not_lt_zero q)]
    frame := Frame.refl _ _
    rd := rfl
    wr := rfl
    gpr := fun _ _ _ _ _ _ => rfl }
  refine WP.mono (Proof.Modes.AArch64.xorLoop_wp xp x0) fun s' d => ?_
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
  have g (r : Reg) (hr : r = .x25 ∨ r = .x26 ∨ r = .x27 ∨ r = .x28) : s'.gpr r = s.gpr r := by
    rw [d.gpr r (by rcases hr with rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
      o₁ _ (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
  refine ⟨by rw [g .x25 (by simp), h.x25], fun r hr => by rw [g r (by rcases hr with rfl | rfl | rfl <;> simp),
      h.kept r hr], by rw [d.rd, rd₁, h.rd], by rw [d.wr, wr₁, h.wr], ?_, ?_, fun q hq => ?_, ?_⟩
  · refine kW1_kW h.frame |>.trans ?_
    rw [← mem₁]
    exact d.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨fData s₀, by simp, tail_sub s₀⟩
  · rw [blocksAt_frame' d.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.blk_tail, mem₁]
    exact h.blocks
  · rw [d.data q hq, mem₁, h.frame.bytes tailD hlen hq, (svMem_frame s₀).bytes tailS hlen hq,
      ← bytesAt_getD s.mem (kBk s₀) (show q < 16 by omega), h.out]
  · rw [ite_eq_right hu, Proof.Cmac.bytesAt_frame d.frame ivT (by decide), mem₁, h.ctr, ← AesCtr.next_add]

theorem mid_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KWhole s₀ s) :
    WP isa (.ite (.zero .x .x23) (.block []) ctrFinalTail) s (KDone s₀) := by
  by_cases hu : fU s₀ = 0
  · exact WP.ite true (by rw [eval_u h, decide_eq_true hu]) (fun _ => WP.block_nil (done_of_zero h hu))
      (fun h => by cases h)
  · refine WP.ite false (by rw [eval_u h, decide_eq_false hu]) (fun h => by cases h) fun _ => ?_
    exact WP.seq (WP.mono (tail_args_wp hp h) fun _ h₁ =>
      WP.seq (WP.mono (tail_call_wp hp h₁) fun _ h₂ => tail_xor_wp hp h₂ hu))

/-! ## Restoring the registers -/

theorem end_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KDone s₀ s) :
    WP isa (.block finalRestore) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem := by
  have hs : Spill.Saved (kV s₀) s₀.gpr finalSaved s.mem :=
    (Spill.saveMem_saved (by decide) s₀.mem (kV s₀) s₀.gpr).frame h.frame fun p hp' r hr => by
      have hsub : Region.Sub ⟨kV s₀ + BitVec.ofNat 64 p.2, 8⟩ (kSv s₀) :=
        Offset.sub_base _ (by have := saved_slots p hp'; omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.iv_sv.symm.sub_left hsub
      · exact hp.data_sv.symm.sub_left hsub
      · exact slot_blk s₀ p hp'
      · exact hp.stk_sv.symm.sub_left hsub
  show WP isa (.block (Spill.restoreCode .x25 finalSaved)) _ _
  refine WP.mono (Spill.restore_wp h.x25 saved_fits (by decide) (fun p hp' => ?_) hs)
    fun s' r => ⟨fun q hq => r.gpr_of ?_, r.mem⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    have := saved_slots p hp'
    exact ⟨kSv s₀, by simp, Offset.contains_base _ (by omega) (by have := hp.sv_wrap; omega)⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact .inl (by decide)
      | exact .inr (h.kept _ (by simp))

/-! ## The whole function -/

theorem final_wp {s₀ : State} (hp : KPre s₀) :
    WP isa ctrFinal s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ ∃ s₁, KDone s₀ s₁ ∧ s'.mem = s₁.mem := by
  refine WP.seq (WP.mono (setup_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (whole_wp hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (mid_wp hp h₂) fun s₃ h₃ => ?_)
  exact WP.mono (end_wp hp h₃) fun _ ⟨g, m⟩ => ⟨g, s₃, h₃, m⟩

/-- `Spec.Ctr.CryptFinal`, from what the function leaves. -/
theorem final_post {s₀ s₁ s' : State} (h : KDone s₀ s₁) (hm : s'.mem = s₁.mem) : ctrFinalAArch64.post s₀ s' := by
  show Spec.Ctr.CryptFinal (kCiph s₀) s₀.mem s'.mem (fIv s₀) (fD s₀) (fL s₀)
  exact Modes.CtrFinal.cryptFinal_of (cipher_length _) (by rw [hm]; exact h.blocks)
    (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.ctr)

theorem ctrFinal_keepsV : ctrFinal.allInstrs keepsV = true := by lit_decide

theorem final_correct (s : State) (hs : ctrFinalAArch64.pre s) :
    ∃ t s', Exec isa ctrFinal s t s' ∧ abiPreserved s s' ∧ ctrFinalAArch64.post s s' := by
  obtain ⟨t, s', he, hg, s₁, h₁, hm⟩ := final_wp (KPre.of hs)
  exact ⟨t, s', he, ⟨hg, AArch64.Exec.sp he, Exec.preservedV he ctrFinal_keepsV⟩, final_post h₁ hm⟩

/-! ## Constant time -/

theorem setup_taint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (.block ctrFinalSetup) h).isSome = true := ⟨_, by taint_decide⟩

theorem tailArgs_taint : ∃ h, (taint.check (Taint.ofRegs [.x19, .x21, .x25])
    (.block ctrFinalTailArgs) h).isSome = true := ⟨_, by taint_decide⟩

theorem xor_taint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x22, .x23])
    (.seq (.block tailKey) (.loop (.block (Impl.Modes.AArch64.xorByte .x22 .x23)) (.nonzero .x .x23))) h).isSome =
    true := ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (taint.check (Taint.ofRegs [.x25]) (.block finalRestore) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem final_rel {s₀ s₀' : State} (h0 : ctrFinalAArch64.pre s₀) (h0' : ctrFinalAArch64.pre s₀')
    (hq : ctrFinalAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') ctrFinal fun _ _ => True := by
  have hp := KPre.of h0
  have hp' := KPre.of h0'
  obtain ⟨qW, qIv, qD, qL, qV, qSp⟩ := hq
  have qU : fU s₀ = fU s₀' := by simp only [fU, fL, qL]
  have qN : fN s₀ = fN s₀' := by simp only [fN, fL, qL]
  have qT : fT s₀ = fT s₀' := by simp only [fT, fD, qD, qN]
  -- The registers saved and the arguments set up.
  have r₁ := AesCtr.AArch64.taint_rel (P := fun a b => a = s₀ ∧ b = s₀') (F₁ := KSetup s₀) (F₂ := KSetup s₀')
    [.x0, .x1, .x2, .x3, .x4] setup_taint
    (fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact qSp)
    (fun a b h r hr => by
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption)
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨setup_wp hp, setup_wp hp'⟩
  -- The whole blocks.
  have r₂ := (RelCT.callEx (k := ctrF) (n := "vg_sm4_ctr") ctr_ok ctr_ct
    (P := fun a b => KSetup s₀ a ∧ KSetup s₀' b) fun a b ⟨ha, hb⟩ => by
      obtain ⟨pa, ca, wa⟩ := whole_pre hp ha
      obtain ⟨pb, cb, wb⟩ := whole_pre hp' hb
      refine ⟨_, _, _, _, pa, pb, ?_, ca, wa, cb, wb⟩
      simp only [ctrF, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
        AesCbc.AArch64.callEntry_x0, AesCbc.AArch64.callEntry_x1, AesCbc.AArch64.callEntry_x2,
        AesCbc.AArch64.callEntry_x3, ha.x0, ha.x1, ha.x2, ha.x3, ha.sp, hb.x0, hb.x1, hb.x2, hb.x3, hb.sp]
      rw [fW, fW, fIv, fIv, fD, fD, qW, qIv, qD, qSp, qN]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial).wp
    (F₁ := KWhole s₀) (F₂ := KWhole s₀') fun a b h => ⟨whole_wp hp h.1, whole_wp hp' h.2⟩
  -- The partial last block.
  have tail (hu : fU s₀ ≠ 0) : RelCT isa (fun a b => KWhole s₀ a ∧ KWhole s₀' b) ctrFinalTail
      fun a b => KDone s₀ a ∧ KDone s₀' b := by
    have hu' : fU s₀' ≠ 0 := qU ▸ hu
    have a₁ := AesCtr.AArch64.taint_rel (P := fun a b => KWhole s₀ a ∧ KWhole s₀' b)
      (F₁ := KArgs s₀) (F₂ := KArgs s₀') [.x19, .x21, .x25] tailArgs_taint
      (fun a b h => by rw [h.1.sp, h.2.sp, qSp])
      (fun a b h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.1.x19, h.2.x19, fW, fW, qW]
        · rw [h.1.x21, h.2.x21, fIv, fIv, qIv]
        · rw [h.1.x25, h.2.x25, kV, kV, qV])
      fun a b h => ⟨tail_args_wp hp h.1, tail_args_wp hp' h.2⟩
    have a₂ := (RelCT.callEx (k := ctrF) (n := "vg_sm4_ctr") ctr_ok ctr_ct
      (P := fun a b => KArgs s₀ a ∧ KArgs s₀' b) fun a b ⟨ha, hb⟩ => by
        obtain ⟨pa, ca, wa⟩ := tail_pre hp ha
        obtain ⟨pb, cb, wb⟩ := tail_pre hp' hb
        refine ⟨_, _, _, _, pa, pb, ?_, ca, wa, cb, wb⟩
        simp only [ctrF, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
          AesCbc.AArch64.callEntry_x0, AesCbc.AArch64.callEntry_x1, AesCbc.AArch64.callEntry_x2,
          AesCbc.AArch64.callEntry_x3, ha.x0, ha.x1, ha.x2, ha.x3, ha.sp, hb.x0, hb.x1, hb.x2, hb.x3, hb.sp]
        rw [fW, fW, fIv, fIv, kBk, kBk, kV, kV, qW, qIv, qV, qSp]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial).wp
      (F₁ := KCall s₀) (F₂ := KCall s₀') fun a b h => ⟨tail_call_wp hp h.1, tail_call_wp hp' h.2⟩
    have a₃ := AesCtr.AArch64.taint_rel (P := fun a b => KCall s₀ a ∧ KCall s₀' b)
      (F₁ := KDone s₀) (F₂ := KDone s₀') [.x25, .x22, .x23] xor_taint
      (fun a b h => by rw [h.1.sp, h.2.sp, qSp])
      (fun a b h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.1.x25, h.2.x25, kV, kV, qV]
        · rw [h.1.x22, h.2.x22, qT]
        · rw [h.1.x23, h.2.x23, qU])
      fun a b h => ⟨tail_xor_wp hp h.1 hu, tail_xor_wp hp' h.2 hu'⟩
    exact a₁.seq ((a₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq a₃)
  have r₃ : RelCT isa (fun a b => KWhole s₀ a ∧ KWhole s₀' b) (.ite (.zero .x .x23) (.block []) ctrFinalTail)
      (fun a b => KDone s₀ a ∧ KDone s₀' b) := by
    refine RelCT.ite (fun a b h => by rw [eval_u h.1, eval_u h.2, qU]) ?_ ?_
    · refine RelCT.block_nil fun a b h => ?_
      have h0 : fU s₀ = 0 := by
        have := h.2; rw [eval_u h.1.1] at this; simpa using this
      exact ⟨done_of_zero h.1.1 h0, done_of_zero h.1.2 (qU ▸ h0)⟩
    · refine (RelCT.exists_ fun (hu : fU s₀ ≠ 0) => tail hu).mono
        (fun a b h => ⟨?_, h.1.1, h.1.2⟩) fun _ _ h => h
      have := h.2; rw [eval_u h.1.1] at this; simpa using this
  have r₃' := r₃.wp (F₁ := fun (s : State) => s.sp = s₀.sp) (F₂ := fun (s : State) => s.sp = s₀'.sp)
    fun a b h =>
      ⟨WP.mono (WP.sp_eq (mid_wp hp h.1)) fun _ x => x.2.trans h.1.sp,
        WP.mono (WP.sp_eq (mid_wp hp' h.2)) fun _ x => x.2.trans h.2.sp⟩
  -- The registers restored.
  obtain ⟨_, t₅⟩ := restore_taint
  have r₄ := RelCT.taint (A := taint) (P := fun a b => (KDone s₀ a ∧ KDone s₀' b) ∧
      a.sp = s₀.sp ∧ b.sp = s₀'.sp) _
    (fun a b h => AesCfb.AArch64.Final.agree_of (by rw [h.2.1, h.2.2, qSp]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.x25, h.1.2.x25, kV, kV, qV]) t₅
  exact r₁.seq ((r₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq (r₃'.seq r₄))

theorem final_ct : ConstantTime isa ctrFinalAArch64.pre ctrFinalAArch64.pub ctrFinal :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (final_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Verified -/

theorem ctrFinal_verified : Verified AArch64.target ctrFinal ctrFinalScratchContract :=
  Verified.of_correct final_correct final_ct ctrFinal_implies

/-! ## With `save` on the stack

The final function has four argument words, so `save` is its fifth, in `x4`:
it runs its code in a frame of 80 bytes on the stack (`withStackScratchWiped`),
`save`'s 80 bytes (the registers, then the block that held the last output
block), which it zeroes before returning. Its calls use 3264 bytes below it,
so 3344 in all. -/

/-- A state satisfying the shared contract's precondition. -/
def ctrFinalFrameSat : State := { ctrFinalSat with wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩] }

theorem ctrFinalFrameSat_pre : ∃ s, (Spec.Sm4.ctrFinalContract AArch64.abi 3344).pre s := by
  implies_sat [Spec.Sm4.ctrFinalContract, Spec.Sm4.ctrFinalSig, AArch64.abi, AArch64.argRegs]
    [ctrFinalFrameSat, ctrFinalSat] using ctrFinalFrameSat

theorem ctrFinal_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 80 .x4 10 ctrFinal)
      (Spec.Sm4.ctrFinalContract AArch64.abi 3344) := by
  rw [Proof.Sm4.ctrFinalContract_eq]
  exact AArch64.Verified.stackScratchWiped (sig := Spec.Sm4.ctrFinalSig) (nm := "save") (e := .u64) (n := 10)
    (post := Proof.Sm4.ctrFinalPost AArch64.abi.ptrBits) (wa := true) (stack := 3264) (bytes := 80) (words := 10)
    ctrFinal_verified (by decide) (by decide) (by decide) (Proof.Sm4.ctrFinalPostOut_local _) ctrFinalFrameSat_pre

end VG.Proof.Sm4.AArch64.CtrFinal
