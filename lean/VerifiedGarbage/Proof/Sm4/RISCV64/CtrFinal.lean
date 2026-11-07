module

public import VerifiedGarbage.Impl.Sm4.RISCV64.CtrFinal
public import VerifiedGarbage.Proof.Sm4.CtrFinal
public import VerifiedGarbage.Proof.Sm4.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.AesCfb.RISCV64.Final
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Impl.StackScratch.RISCV64
import VerifiedGarbage.Proof.AesCtr.RISCV64.Final
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesConstantTime
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Modes.CtrFinal
import VerifiedGarbage.Proof.Modes.Words
import VerifiedGarbage.Proof.Modes.RISCV64.SeqFinal
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Impl.Sm4.RISCV64.CtrFinal
meta import VerifiedGarbage.Proof.Sm4.CtrFinal
meta import VerifiedGarbage.Proof.Sm4.RISCV64.ModesVerified
meta import VerifiedGarbage.Proof.AesCfb.RISCV64.Final
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
meta import VerifiedGarbage.Impl.StackScratch.RISCV64
meta import VerifiedGarbage.Proof.AesCtr.RISCV64.Final
meta import VerifiedGarbage.Proof.Sm4.RISCV64.ModesConstantTime
meta import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Modes.CtrFinal
meta import VerifiedGarbage.Proof.Modes.Words
meta import VerifiedGarbage.Proof.Modes.RISCV64.SeqFinal
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesCbc.Spec
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# SM4-CTR of a message's last piece on RISC-V

`ctrFinal_framed`: `vg_sm4_ctr_final` (`Impl/Sm4/RISCV64/CtrFinal.lean`) meets
`Spec.Sm4.ctrFinalContract`.

The code is proven against `ctrFinalRISCV64`, with the arguments
`(schedule = a0, ctr = a1, data = a2, len = a3, save = a4)`, a fifth argument
`save` (`a4`) of 80 bytes for its return address and its caller's registers
and a block of its own, and 3232 bytes of stack for its calls
(`ctrFinal_implies`: the shared contract with it), as a caller of
`vg_sm4_ctr`, which keeps its own working space in a frame on the
stack, through the register-form contract its proofs give it
(`Modes.modeContract Modes.ctrPost`, `Modes.ctr_correct`,
`ctr_constantTime`), with `WP.callAny` (the callee's frames lie within the
stack, `ctr_depth`). It is AES-CTR's final function's proof
(`Proof/AesCtr/RISCV64/Final.lean`) with SM4's arguments:

* `setup_wp`, `whole_wp`: the registers saved in `save`, whose address is
  kept in `s7`, and the call on the `n = len / 16` whole blocks (`KWhole`);
* `mid_wp`: if `u = len % 16` bytes are left, the block after the registers
  in `save` zeroed and the call on it (`tail_args_wp`, `tail_call_wp`), which
  leaves `CIPH_K(Tₙ₊₁)` there and `Tₙ₊₂` in `ctr`, and its first `u` bytes
  XORed into them (`Modes.RISCV64.xorLoop_wp`, `tail_xor_wp`); what is left
  before the registers are restored is `KDone`;
* `end_wp`: the registers restored;
* `final_post`: `KDone` gives `Spec.Ctr.CryptFinal`
  (`Proof.Modes.CtrFinal.cryptFinal_of`), by SM4 with the schedule at
  `schedule`.

Constant time (`final_rel`): the blocks by the taint analysis, the calls by
the callee's constant time (`RelCT.callEx`), whose public arguments agree.
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64.CtrFinal

open VG VG.RISCV64
open VG.RISCV64.Steps
open VG.Spec.Aes (bytesAt)
open VG.Impl.Sm4.RISCV64 (ctr ctrFinalSave ctrFinalMoves ctrFinalSetup ctrFinalTailMoves
  ctrFinalTailArgs ctrFinalTail ctrFinal)
open VG.Impl.AesCfb.RISCV64 (finalSaved finalRestore)
open VG.Impl.AesCtr.RISCV64 (zeroSlots tailKey)

/-! ## The callee -/

/-- `vg_sm4_ctr`'s contract, as its proofs state it: the arguments
`(schedule = a0, ctr = a1, data = a2, n = a3)` and a frame of 3232 bytes
below the stack pointer. -/
abbrev ctrK : Contract isa := Modes.modeContract Modes.ctrPost

theorem ctr_depth : sdepth ctr ≤ 3232 := by lit_decide

theorem ctr_ok : ∀ s, ctrK.pre s → ∃ t s', Exec isa ctr s t s' ∧ abiPreserved s s' ∧ ctrK.post s s' :=
  Modes.ctr_correct

theorem ctr_ct : ConstantTime isa ctrK.pre ctrK.pub ctr := ctr_constantTime _

/-! ## The contract -/

/-- The code's contract, with the arguments `(schedule = a0, ctr = a1,
data = a2, len = a3, save = a4)`, `save` of 80 bytes, and 3232 bytes of stack
for the calls: the data and the counter block as `Spec.Ctr.CryptFinal` says,
by SM4 with the schedule at `schedule`. -/
def ctrFinalRISCV64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 128⟩
    let ctr : Region := ⟨s.gpr .a1, 16⟩
    let data : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let sv : Region := ⟨s.gpr .a4, 80⟩
    let stack := below s.sp 3232
    s.sp.toNat % 16 = 0 ∧ 3232 ≤ s.sp.toNat ∧ s.rd = [sched] ∧ s.wr = [ctr, data, sv] ∧
      sched.Disjoint ctr ∧ sched.Disjoint data ∧ sched.Disjoint sv ∧ ctr.Disjoint data ∧ ctr.Disjoint sv ∧
      data.Disjoint sv ∧
      stack.Disjoint sched ∧ stack.Disjoint ctr ∧ stack.Disjoint data ∧ stack.Disjoint sv ∧
      (s.gpr .a0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat + 80 ≤ 2 ^ 64 ∧
      (s.gpr .a4).toNat % 8 = 0
  post s s' :=
    Spec.Ctr.CryptFinal (Spec.Sm4.cipher (Spec.Sm4.scheduleAt s.mem (s.gpr .a0)))
      s.mem s'.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3).toNat
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

/-- The contract the frame needs: the shared one, with `save`, 80 bytes, as a
fifth argument, and 3232 bytes of stack (`vg_sm4_ctr`'s frame). -/
abbrev ctrFinalScratchContract : Contract isa :=
  Sig.scratchContract RISCV64.abi Spec.Sm4.ctrFinalSig "save" .u64 10 (Curry.const (fun _ => True) _)
    (Proof.Sm4.ctrFinalPost RISCV64.abi.ptrBits) true 3232

/-- A state satisfying the precondition (no data). -/
def ctrFinalSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 80⟩]

theorem ctrFinal_implies : ctrFinalRISCV64.Implies ctrFinalScratchContract := by
  sig_implies [ctrFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Sm4.ctrFinalSig, Proof.Sm4.ctrFinalPost, ctrFinalRISCV64, RISCV64.abi, RISCV64.argRegs] [ctrFinalSat]
    using ctrFinalSat

/-! ## The arguments, by name -/

open VG.Proof.AesCfb.RISCV64.Final (Kept cs_of callEntry bytesAt_getD blocksAt_frame' saved_slots saved_fits
  shr4 shr4_shl4 sub_shl4 upd_gpr)
open VG.Proof.AesCtr.RISCV64.Final (zero_bytes)
open VG.Proof.AesCbc.RISCV64 (one_toNat)

section
variable (s₀ : State)

abbrev fW : Addr := s₀.gpr .a0
abbrev fIv : Addr := s₀.gpr .a1
abbrev fD : Addr := s₀.gpr .a2
abbrev fL : Nat := (s₀.gpr .a3).toNat
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
abbrev kV : Addr := s₀.gpr .a4
abbrev kSch : Region := ⟨fW s₀, 128⟩
abbrev kIv : Region := ⟨fIv s₀, 16⟩
abbrev kSv : Region := ⟨kV s₀, 80⟩
abbrev kSv64 : Region := ⟨kV s₀, 64⟩
/-- The block after the registers in `save`. -/
abbrev kBk : Addr := kV s₀ + BitVec.ofNat 64 64
abbrev kBlk : Region := ⟨kBk s₀, 16⟩
/-- The stack the calls use. -/
abbrev kStk : Region := below s₀.sp 3232
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
  al : s₀.sp.toNat % 16 = 0
  sp : 3232 ≤ s₀.sp.toNat
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
  sv_al : (kV s₀).toNat % 8 = 0

theorem KPre.of {s₀ : State} (h : ctrFinalRISCV64.pre s₀) : KPre s₀ :=
  let ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩ := h
  ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩

/-! ## Regions and frames -/

theorem blk_sub (s₀ : State) : Region.Sub (fBlk s₀) (fData s₀) := Region.sub_prefix (Nat.mul_div_le _ _)

theorem tail_sub (s₀ : State) : Region.Sub (fTail s₀) (fData s₀) :=
  Offset.sub_base _ (by rw [Nat.div_add_mod])

theorem fN_eq (s₀ : State) : fN s₀ = fL s₀ / 16 := rfl
theorem fU_eq (s₀ : State) : fU s₀ = fL s₀ % 16 := rfl

theorem n_lt (s₀ : State) : fN s₀ < 2 ^ 64 := by
  have := (s₀.gpr .a3).isLt; have : fL s₀ = (s₀.gpr .a3).toNat := rfl; rw [fN_eq]; omega

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
    (hf : Frame (wr ++ [below s.sp (sdepth ctr)]) s.mem s'.mem) :
    Frame (wr ++ [kStk s₀]) s.mem s'.mem :=
  hf.sub fun r hr => by
    rcases List.mem_append.mp hr with h | h
    · exact ⟨r, List.mem_append_left _ h, fun _ h => h⟩
    · simp only [List.mem_singleton] at h; subst h
      exact ⟨kStk s₀, by simp, fun x hx => by rw [hsp] at hx; exact Offset.below_mono s₀.sp ctr_depth (by decide) x hx⟩

/-! ## Saving the registers -/

/-- What saving the registers and setting up the arguments leaves. -/
structure KSetup (s₀ s : State) : Prop where
  s1 : s.gpr .s1 = fW s₀
  s5 : s.gpr .s5 = fIv s₀
  s2 : s.gpr .s2 = fT s₀
  s3 : s.gpr .s3 = BitVec.ofNat 64 (fU s₀)
  s7 : s.gpr .s7 = kV s₀
  a0 : s.gpr .a0 = fW s₀
  a1 : s.gpr .a1 = fIv s₀
  a2 : s.gpr .a2 = fD s₀
  a3 : s.gpr .a3 = BitVec.ofNat 64 (fN s₀)
  kept : Kept s₀ s
  sp : s.sp = s₀.sp
  mem : s.mem = kSvMem s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

set_option linter.unusedSimpArgs false in
theorem setup_wp {s₀ : State} (hp : KPre s₀) : WP isa (.block ctrFinalSetup) s₀ (KSetup s₀) := by
  have hw : ∀ p ∈ finalSaved, InRegions s₀.wr (s₀.gpr .a4 + BitVec.ofNat 64 p.2) 8 := by
    intro p hp'
    rw [hp.wr]
    have := saved_slots p hp'
    exact ⟨kSv s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  show WP isa (.block (Spill.saveCode .a4 finalSaved ++ ctrFinalMoves)) _ _
  refine Spill.save_ok hp.sv_al saved_fits hw ?_
  unfold ctrFinalMoves Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ =>
    wp_srl (by decide) fun s₄ u₄ => wp_sll (by decide) fun s₅ u₅ => wp_add fun s₆ u₆ =>
    wp_sub fun s₇ u₇ => wp_mv fun s₈ u₈ => WP.block_nil ?_
  exact {
    s1 := by simp only [upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    s5 := by simp only [upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    s2 := by simp only [upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte]; rw [shr4_shl4]
    s3 := by simp only [upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte]; rw [shr4_shl4, sub_shl4]
    s7 := by simp only [upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    a0 := by simp only [upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    a1 := by simp only [upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    a2 := by simp only [upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    a3 := by simp only [upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] ; rw [shr4]
    kept := fun r hr => by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    sp := by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
    mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
    wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr] }

/-! ## The whole blocks -/

theorem whole_pre {s₀ : State} (hp : KPre s₀) {s : State} (h : KSetup s₀ s) :
    ctrK.pre (s.callEntry.withRegions [kSch s₀] [kIv s₀, fBlk s₀]) ∧
      Covers ([kSch s₀] ++ [kIv s₀, fBlk s₀]) (s.rd ++ s.wr) ∧ Covers [kIv s₀, fBlk s₀] s.wr := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Modes.modeContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp,
      callEntry s (by decide : Reg.a0 ∉ linkRegs), callEntry s (by decide : Reg.a1 ∉ linkRegs),
      callEntry s (by decide : Reg.a2 ∉ linkRegs), callEntry s (by decide : Reg.a3 ∉ linkRegs),
      h.a0, h.a1, h.a2, h.a3, h.sp, toNat_n]
    exact ⟨trivial, trivial, hp.sch_iv, hp.sch_data.sub_right (blk_sub s₀),
      hp.iv_data.sub_right (blk_sub s₀), hp.sch_wrap, hp.iv_wrap, hp.blk_wrap, hp.al, hp.sp, hp.stk_sch,
      hp.stk_iv, hp.stk_data.sub_right (blk_sub s₀)⟩
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
  s1 : s.gpr .s1 = fW s₀
  s5 : s.gpr .s5 = fIv s₀
  s2 : s.gpr .s2 = fT s₀
  s3 : s.gpr .s3 = BitVec.ofNat 64 (fU s₀)
  s7 : s.gpr .s7 = kV s₀
  kept : Kept s₀ s
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (kW1 s₀) (kSvMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) = Spec.Ctr.crypt (kCiph s₀) (fIv0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (fIv0 s₀) (fN s₀)

theorem whole_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KSetup s₀ s) :
    WP isa (.call "vg_sm4_ctr" ctr) s (KWhole s₀) := by
  obtain ⟨eK, eIv, eB⟩ := sv_bytes hp
  obtain ⟨hpre, hc, hw⟩ := whole_pre hp h
  refine WP.callAny (k := ctrK) ctr_ok (rd := [kSch s₀]) (wr := [kIv s₀, fBlk s₀]) hpre hc hw ?_
    (by have := ctr_depth; omega)
  intro s' rd' wr' sp' fr' cs' post₂
  have fr := call_frame h.sp fr'
  rw [h.mem] at fr
  simp only [Modes.modeContract, Modes.ctrPost, Modes.dataAt, Modes.ivAt, Modes.ciph,
    State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry s (by decide : Reg.a0 ∉ linkRegs), callEntry s (by decide : Reg.a1 ∉ linkRegs),
    callEntry s (by decide : Reg.a2 ∉ linkRegs), callEntry s (by decide : Reg.a3 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3, toNat_n, h.mem] at post₂
  have post₃ := post₂
  rw [eK, eIv, eB] at post₃
  exact ⟨by rw [cs_of cs' .s1 (by simp), h.s1], by rw [cs_of cs' .s5 (by simp), h.s5], by rw [cs_of cs' .s2 (by simp), h.s2],
    by rw [cs_of cs' .s3 (by simp), h.s3], by rw [cs_of cs' .s7 (by simp), h.s7],
    fun r hr => by rw [cs_of cs' r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp), h.kept r hr],
    by rw [sp', h.sp], by rw [rd', h.rd], by rw [wr', h.wr],
    fr.mono fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp [h],
    post₃.1, post₃.2⟩

/-! ## The partial last block -/

theorem eval_u {s₀ s : State} (h : KWhole s₀ s) :
    isa.eval (.zero .s3) s = some (decide (fU s₀ = 0)) :=
  eval_zero_ofNat s .s3 (by have := u_lt s₀; omega) h.s3

/-- What zeroing the block and setting up the arguments leaves. -/
structure KArgs (s₀ s : State) : Prop where
  a0 : s.gpr .a0 = fW s₀
  a1 : s.gpr .a1 = fIv s₀
  a2 : s.gpr .a2 = kBk s₀
  a3 : s.gpr .a3 = BitVec.ofNat 64 1
  s2 : s.gpr .s2 = fT s₀
  s3 : s.gpr .s3 = BitVec.ofNat 64 (fU s₀)
  s7 : s.gpr .s7 = kV s₀
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

set_option linter.unusedSimpArgs false in
theorem tail_args_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KWhole s₀ s) :
    WP isa (.block ctrFinalTailArgs) s (KArgs s₀) := by
  show WP isa (.block (.li .t0 0 :: (Spill.saveCode .s7 zeroSlots ++ ctrFinalTailMoves))) _ _
  refine wp_li (imm := 0) (by decide) fun s₁ z => ?_
  have h7 : s₁.gpr .s7 = kV s₀ := by rw [z.other _ (by decide), h.s7]
  have hw : ∀ p ∈ zeroSlots, InRegions s₁.wr (s₁.gpr .s7 + BitVec.ofNat 64 p.2) 8 := by
    intro p hp'
    rw [z.wr, h.wr, hp.wr, h7]
    simp only [zeroSlots, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact ⟨kSv s₀, by simp, Offset.contains_base _ (by decide) (by have := hp.sv_wrap; omega)⟩
    · exact ⟨kSv s₀, by simp, Offset.contains_base _ (by decide) (by have := hp.sv_wrap; omega)⟩
  refine Spill.save_ok (by rw [h7]; exact hp.sv_al) (by decide) hw ?_
  unfold ctrFinalTailMoves Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_addi (imm := 64) (by decide) fun s₄ u₄ =>
    wp_li (imm := 1) (by decide) fun s₅ u₅ => WP.block_nil ?_
  have c (r : Reg) (hr : r = .s0 ∨ r = .s1 ∨ r = .s2 ∨ r = .s3 ∨ r = .s4 ∨ r = .s5 ∨ r = .s6 ∨ r = .s7 ∨
      r = .s8 ∨ r = .s9 ∨ r = .s10 ∨ r = .s11) : s₅.gpr r = s.gpr r := by
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, reduceCtorEq,
        ↓reduceIte] <;> exact z.other _ (by decide)
  have sp : s₅.sp = s.sp := by
    rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, show ({ s₁ with mem := _ } : State).sp = s₁.sp from rfl, z.sp]
  have rd : s₅.rd = s.rd := by
    rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, show ({ s₁ with mem := _ } : State).rd = s₁.rd from rfl, z.rd]
  have wr : s₅.wr = s.wr := by
    rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, show ({ s₁ with mem := _ } : State).wr = s₁.wr from rfl, z.wr]
  have hm : s₅.mem = Spill.saveMem s.mem (kV s₀) s₁.gpr zeroSlots := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, h7]
    show Spill.saveMem s₁.mem _ _ _ = _
    rw [z.mem]
  have fz : Frame [kBlk s₀] s.mem s₅.mem := by rw [hm]; exact zero_frame s₀ _ _
  have ivZ : ∀ r ∈ [kBlk s₀], (kIv s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_sv.sub_right (blk_sv_sub s₀)
  have blkZ : ∀ r ∈ [kBlk s₀], (fBlk s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (hp.data_sv.sub_left (blk_sub s₀)).sub_right (blk_sv_sub s₀)
  have g7 : ({ s₁ with mem := Spill.saveMem s₁.mem (s₁.gpr .s7) s₁.gpr zeroSlots } : State).gpr = s₁.gpr := rfl
  refine ⟨?_, ?_, ?_, ?_, by rw [c .s2 (by simp), h.s2], by rw [c .s3 (by simp), h.s3],
    by rw [c .s7 (by simp), h.s7],
    fun r hr => by rw [c r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp), h.kept r hr],
    by rw [sp, h.sp], by rw [rd, h.rd], by rw [wr, h.wr], ?_, ?_, ?_, ?_⟩
  · simp only [upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, reduceCtorEq, ↓reduceIte, g7]
    rw [z.other _ (by decide), h.s1]
  · simp only [upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, reduceCtorEq, ↓reduceIte, g7]
    rw [z.other _ (by decide), h.s5]
  · simp only [upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, reduceCtorEq, ↓reduceIte, g7]
    rw [h7]
  · simp only [upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, reduceCtorEq, ↓reduceIte]
  · exact h.frame.trans (fz.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  · rw [blocksAt_frame' fz blkZ]; exact h.blocks
  · rw [Proof.Cmac.bytesAt_frame fz ivZ (by decide), h.ctr]
  · rw [hm, show Spill.saveMem s.mem (kV s₀) s₁.gpr zeroSlots =
        ((s.mem.writeW (kBk s₀) (s₁.gpr .t0)).writeW (kBk s₀ + BitVec.ofNat 64 8) (s₁.gpr .t0)) by
      simp only [Spill.saveMem, zeroSlots, Offset.add_add], z.gpr]
    exact zero_bytes _ _

theorem tail_pre {s₀ : State} (hp : KPre s₀) {s : State} (h : KArgs s₀ s) :
    ctrK.pre (s.callEntry.withRegions [kSch s₀] [kIv s₀, kBlk s₀]) ∧
      Covers ([kSch s₀] ++ [kIv s₀, kBlk s₀]) (s.rd ++ s.wr) ∧ Covers [kIv s₀, kBlk s₀] s.wr := by
  have bs := blk_sv_sub s₀
  refine ⟨?_, ?_, ?_⟩
  · simp only [Modes.modeContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp,
      callEntry s (by decide : Reg.a0 ∉ linkRegs), callEntry s (by decide : Reg.a1 ∉ linkRegs),
      callEntry s (by decide : Reg.a2 ∉ linkRegs), callEntry s (by decide : Reg.a3 ∉ linkRegs),
      h.a0, h.a1, h.a2, h.a3, h.sp, one_toNat, Nat.mul_one]
    have := hp.sv_wrap
    exact ⟨trivial, trivial, hp.sch_iv, hp.sch_sv.sub_right bs, hp.iv_sv.sub_right bs, hp.sch_wrap,
      hp.iv_wrap, by rw [hp.bk_toNat]; omega, hp.al, hp.sp, hp.stk_sch, hp.stk_iv, hp.stk_sv.sub_right bs⟩
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
  s2 : s.gpr .s2 = fT s₀
  s3 : s.gpr .s3 = BitVec.ofNat 64 (fU s₀)
  s7 : s.gpr .s7 = kV s₀
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
    WP isa (.call "vg_sm4_ctr" ctr) s (KCall s₀) := by
  obtain ⟨hpre, hc, hw⟩ := tail_pre hp h
  have big := big_of (kW1_kW h.frame)
  have eK := sched_of big hp.sch_big
  refine WP.callAny (k := ctrK) ctr_ok (rd := [kSch s₀]) (wr := [kIv s₀, kBlk s₀]) hpre hc hw ?_
    (by have := ctr_depth; omega)
  intro s' rd' wr' sp' fr' cs' post₂
  have fr := call_frame h.sp fr'
  simp only [Modes.modeContract, Modes.ctrPost, Modes.dataAt, Modes.ivAt, Modes.ciph,
    State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry s (by decide : Reg.a0 ∉ linkRegs), callEntry s (by decide : Reg.a1 ∉ linkRegs),
    callEntry s (by decide : Reg.a2 ∉ linkRegs), callEntry s (by decide : Reg.a3 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3, one_toNat, h.ctr] at post₂
  have post₃ := post₂
  rw [eK] at post₃
  have fc : Frame (kW1 s₀) s.mem s'.mem := fr.sub fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  refine ⟨by rw [cs_of cs' .s2 (by simp), h.s2], by rw [cs_of cs' .s3 (by simp), h.s3],
    by rw [cs_of cs' .s7 (by simp), h.s7],
    fun r hr => by rw [cs_of cs' r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp), h.kept r hr],
    by rw [sp', h.sp], by rw [rd', h.rd], by rw [wr', h.wr], h.frame.trans fc, ?_, post₃.2, ?_⟩
  · rw [blocksAt_frame' fr fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.iv_data.symm.sub_left (blk_sub s₀)
      · exact (hp.data_sv.sub_left (blk_sub s₀)).sub_right (blk_sv_sub s₀)
      · exact hp.stk_data.symm.sub_left (blk_sub s₀)]
    exact h.blocks
  · exact Modes.CtrFinal.bytesAt_of_blocksAt_one (cipher_length _) h.zero post₃.1

/-- What the function leaves before restoring the registers. -/
structure KDone (s₀ s : State) : Prop where
  s7 : s.gpr .s7 = kV s₀
  kept : Kept s₀ s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (kW s₀) (kSvMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) = Spec.Ctr.crypt (kCiph s₀) (fIv0 s₀) (fBlks s₀)
  tail : ∀ q < fU s₀, s.mem (fT s₀ + BitVec.ofNat 64 q) = s₀.mem (fT s₀ + BitVec.ofNat 64 q) ^^^
    (kCiph s₀ (Spec.Ctr.next (fIv0 s₀) (fN s₀))).getD q 0
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (fIv0 s₀) (if fU s₀ = 0 then fN s₀ else fN s₀ + 1)

theorem done_of_zero {s₀ s : State} (h : KWhole s₀ s) (hu : fU s₀ = 0) : KDone s₀ s :=
  ⟨h.s7, h.kept, h.rd, h.wr, kW1_kW h.frame, h.blocks, fun q hq => absurd hq (by omega), by
    rw [ite_eq_left hu, h.ctr]⟩

theorem toNat_tail {s₀ : State} (hp : KPre s₀) (hu : fU s₀ ≠ 0) : (fT s₀).toNat = (fD s₀).toNat + 16 * fN s₀ := by
  have := hp.data_wrap
  have := Nat.div_add_mod (fL s₀) 16
  have eN := fN_eq s₀
  have eU := fU_eq s₀
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * fN s₀) (by omega),
    Nat.mod_eq_of_lt (by omega)]

open VG.Proof.Modes.RISCV64 (XPre XInv xorLoop_wp xf)

theorem tail_xor_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KCall s₀ s) (hu : fU s₀ ≠ 0) :
    WP isa (.seq (.block tailKey) (.loop (.block Impl.Modes.RISCV64.xorStep) (.nonzero .s3))) s (KDone s₀) := by
  refine WP.seq (wp_addi (imm := 64) (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have hU := u_lt s₀
  have hT := toNat_tail hp hu
  have hL := Nat.div_add_mod (fL s₀) 16
  have hDw := hp.data_wrap
  have hVw := hp.sv_wrap
  have hB := hp.bk_toNat
  have eN := fN_eq s₀
  have eU := fU_eq s₀
  have xp : XPre s₁ (kBk s₀) (fT s₀) (fU s₀) := {
    pos := by omega
    fK := by omega
    fR := by omega
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
  have x0 : XInv s₁ (kBk s₀) (fT s₀) (fU s₀) 0 s₁ := {
    t2 := by rw [u₁.gpr, h.s7]; exact (BitVec.add_zero _).symm
    s2 := by rw [u₁.other _ (by decide), h.s2]; exact (BitVec.add_zero _).symm
    s3 := by rw [u₁.other _ (by decide), h.s3, Nat.sub_zero]
    lt := by omega
    mem := (Proof.Modes.over_zero _ _ _).symm
    rd := rfl
    wr := rfl
    gpr := fun _ _ _ _ _ _ => rfl }
  refine WP.mono (xorLoop_wp xp x0) fun s' d => ?_
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
  have g (r : Reg) (hr : r = .s7 ∨ r = .s0 ∨ r = .s8 ∨ r = .s9 ∨ r = .s10 ∨ r = .s11) : s'.gpr r = s.gpr r := by
    rw [d.gpr r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      u₁.other _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  have fr : Frame [fTail s₀] s.mem s'.mem := by
    rw [d.mem, u₁.mem]; exact Proof.Modes.over_frame _ _ _ _
  refine ⟨by rw [g .s7 (by simp), h.s7], fun r hr => by
      rw [g r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp), h.kept r hr],
    by rw [d.rd, u₁.rd, h.rd], by rw [d.wr, u₁.wr, h.wr], ?_, ?_, fun q hq => ?_, ?_⟩
  · exact (kW1_kW h.frame).trans (fr.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨fData s₀, by simp, tail_sub s₀⟩)
  · rw [blocksAt_frame' fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.blk_tail]
    exact h.blocks
  · rw [d.mem, Proof.Modes.over_at hq (by omega), xf, u₁.mem, h.frame.bytes tailD hlen hq,
      (svMem_frame s₀).bytes tailS hlen hq, ← bytesAt_getD s.mem (kBk s₀) (show q < 16 by omega), h.out]
  · rw [ite_eq_right hu, Proof.Cmac.bytesAt_frame fr ivT (by decide), h.ctr, ← AesCtr.next_add]

theorem mid_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KWhole s₀ s) :
    WP isa (.ite (.zero .s3) (.block []) ctrFinalTail) s (KDone s₀) := by
  by_cases hu : fU s₀ = 0
  · exact WP.ite true (by rw [eval_u h, decide_eq_true hu]) (fun _ => WP.block_nil (done_of_zero h hu))
      (fun h => by cases h)
  · refine WP.ite false (by rw [eval_u h, decide_eq_false hu]) (fun h => by cases h) fun _ => ?_
    exact WP.seq (WP.mono (tail_args_wp hp h) fun _ h₁ =>
      WP.seq (WP.mono (tail_call_wp hp h₁) fun _ h₂ => tail_xor_wp hp h₂ hu))

/-! ## Restoring the registers -/

theorem end_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : KDone s₀ s) :
    WP isa (.block finalRestore) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧ s'.mem = s.mem := by
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
  show WP isa (.block (Spill.restoreCode .s7 finalSaved)) _ _
  refine WP.mono (Spill.restore_wp hp.sv_al h.s7 saved_fits (by decide) (fun p hp' => ?_) hs)
    fun s' r => ⟨fun q hq => r.gpr_of ?_, r.gpr (.ra, 0) (by decide), r.mem⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    have := saved_slots p hp'
    exact ⟨kSv s₀, by simp, Offset.contains_base _ (by omega) (by have := hp.sv_wrap; omega)⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact .inl (by decide)
      | exact .inr (h.kept _ (by simp))

/-! ## The whole function -/

theorem final_wp {s₀ : State} (hp : KPre s₀) :
    WP isa ctrFinal s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        ∃ s₁, KDone s₀ s₁ ∧ s'.mem = s₁.mem := by
  refine WP.seq (WP.mono (setup_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (whole_wp hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (mid_wp hp h₂) fun s₃ h₃ => ?_)
  exact WP.mono (end_wp hp h₃) fun _ ⟨g, ra, m⟩ => ⟨g, ra, s₃, h₃, m⟩

/-- `Spec.Ctr.CryptFinal`, from what the function leaves. -/
theorem final_post {s₀ s₁ s' : State} (h : KDone s₀ s₁) (hm : s'.mem = s₁.mem) : ctrFinalRISCV64.post s₀ s' := by
  show Spec.Ctr.CryptFinal (kCiph s₀) s₀.mem s'.mem (fIv s₀) (fD s₀) (fL s₀)
  exact Modes.CtrFinal.cryptFinal_of (cipher_length _) (by rw [hm]; exact h.blocks)
    (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.ctr)

theorem final_correct (s : State) (hs : ctrFinalRISCV64.pre s) :
    ∃ t s', Exec isa ctrFinal s t s' ∧ abiPreserved s s' ∧ ctrFinalRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, s₁, h₁, hm⟩ := final_wp (KPre.of hs)
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hra⟩, final_post h₁ hm⟩

/-! ## Constant time -/

theorem setup_taint : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (.block ctrFinalSetup) h).isSome = true := ⟨_, by taint_decide⟩

theorem tailArgs_taint : ∃ h, (taint.check (Taint.ofRegs [.s1, .s5, .s7])
    (.block ctrFinalTailArgs) h).isSome = true := ⟨_, by taint_decide⟩

theorem xor_taint : ∃ h, (taint.check (Taint.ofRegs [.s7, .s2, .s3])
    (.seq (.block tailKey) (.loop (.block Impl.Modes.RISCV64.xorStep) (.nonzero .s3))) h).isSome =
    true := ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (taint.check (Taint.ofRegs [.s7]) (.block finalRestore) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The callee's public arguments, from the registers. -/
theorem ctr_pub {a b : State} (hsp : a.sp = b.sp) (h0 : a.gpr .a0 = b.gpr .a0) (h1 : a.gpr .a1 = b.gpr .a1)
    (h2 : a.gpr .a2 = b.gpr .a2) (h3 : a.gpr .a3 = b.gpr .a3) : ctrK.pub a b := by
  show modePub a b
  rw [Modes.modePub_iff]
  exact ⟨hsp, h0, h1, h2, h3⟩

theorem final_rel {s₀ s₀' : State} (h0 : ctrFinalRISCV64.pre s₀) (h0' : ctrFinalRISCV64.pre s₀')
    (hq : ctrFinalRISCV64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') ctrFinal fun _ _ => True := by
  have hp := KPre.of h0
  have hp' := KPre.of h0'
  obtain ⟨qW, qIv, qD, qL, qV, qSp⟩ := hq
  have qU : fU s₀ = fU s₀' := by simp only [fU, fL, qL]
  have qN : fN s₀ = fN s₀' := by simp only [fN, fL, qL]
  have qT : fT s₀ = fT s₀' := by simp only [fT, fD, qD, qN]
  -- The registers saved and the arguments set up.
  obtain ⟨_, t₁⟩ := setup_taint
  have r₁ := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine AesCfb.RISCV64.Final.agree_of qSp fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) t₁).wp
    (F₁ := KSetup s₀) (F₂ := KSetup s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨setup_wp hp, setup_wp hp'⟩
  -- The whole blocks.
  have r₂ := (RelCT.callEx (k := ctrK) (n := "vg_sm4_ctr") ctr_ok ctr_ct
    (P := fun a b => KSetup s₀ a ∧ KSetup s₀' b) fun a b ⟨ha, hb⟩ => by
      obtain ⟨pa, ca, wa⟩ := whole_pre hp ha
      obtain ⟨pb, cb, wb⟩ := whole_pre hp' hb
      refine ⟨_, _, _, _, pa, pb, ctr_pub ?_ ?_ ?_ ?_ ?_, ca, wa, cb, wb⟩ <;>
        simp only [State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
          callEntry a (by decide : Reg.a0 ∉ linkRegs), callEntry a (by decide : Reg.a1 ∉ linkRegs),
          callEntry a (by decide : Reg.a2 ∉ linkRegs), callEntry a (by decide : Reg.a3 ∉ linkRegs),
          callEntry b (by decide : Reg.a0 ∉ linkRegs), callEntry b (by decide : Reg.a1 ∉ linkRegs),
          callEntry b (by decide : Reg.a2 ∉ linkRegs), callEntry b (by decide : Reg.a3 ∉ linkRegs),
          ha.a0, ha.a1, ha.a2, ha.a3, ha.sp, hb.a0, hb.a1, hb.a2, hb.a3, hb.sp]
      · exact qSp
      · rw [fW, fW, qW]
      · rw [fIv, fIv, qIv]
      · rw [fD, fD, qD]
      · rw [qN]).wp
    (F₁ := KWhole s₀) (F₂ := KWhole s₀') fun a b h => ⟨whole_wp hp h.1, whole_wp hp' h.2⟩
  -- The partial last block.
  have tail (hu : fU s₀ ≠ 0) : RelCT isa (fun a b => KWhole s₀ a ∧ KWhole s₀' b) ctrFinalTail
      fun a b => KDone s₀ a ∧ KDone s₀' b := by
    have hu' : fU s₀' ≠ 0 := qU ▸ hu
    obtain ⟨_, t₃⟩ := tailArgs_taint
    have a₁ := (RelCT.taint (A := taint) (P := fun a b => KWhole s₀ a ∧ KWhole s₀' b) _
      (fun a b h => AesCfb.RISCV64.Final.agree_of (by rw [h.1.sp, h.2.sp, qSp]) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.1.s1, h.2.s1, fW, fW, qW]
        · rw [h.1.s5, h.2.s5, fIv, fIv, qIv]
        · rw [h.1.s7, h.2.s7, kV, kV, qV]) t₃).wp
      (F₁ := KArgs s₀) (F₂ := KArgs s₀') fun a b h => ⟨tail_args_wp hp h.1, tail_args_wp hp' h.2⟩
    have a₂ := (RelCT.callEx (k := ctrK) (n := "vg_sm4_ctr") ctr_ok ctr_ct
      (P := fun a b => KArgs s₀ a ∧ KArgs s₀' b) fun a b ⟨ha, hb⟩ => by
        obtain ⟨pa, ca, wa⟩ := tail_pre hp ha
        obtain ⟨pb, cb, wb⟩ := tail_pre hp' hb
        refine ⟨_, _, _, _, pa, pb, ctr_pub ?_ ?_ ?_ ?_ ?_, ca, wa, cb, wb⟩ <;>
          simp only [State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
            callEntry a (by decide : Reg.a0 ∉ linkRegs), callEntry a (by decide : Reg.a1 ∉ linkRegs),
            callEntry a (by decide : Reg.a2 ∉ linkRegs), callEntry a (by decide : Reg.a3 ∉ linkRegs),
            callEntry b (by decide : Reg.a0 ∉ linkRegs), callEntry b (by decide : Reg.a1 ∉ linkRegs),
            callEntry b (by decide : Reg.a2 ∉ linkRegs), callEntry b (by decide : Reg.a3 ∉ linkRegs),
            ha.a0, ha.a1, ha.a2, ha.a3, ha.sp, hb.a0, hb.a1, hb.a2, hb.a3, hb.sp]
        · exact qSp
        · rw [fW, fW, qW]
        · rw [fIv, fIv, qIv]
        · rw [kBk, kBk, kV, kV, qV]).wp
      (F₁ := KCall s₀) (F₂ := KCall s₀') fun a b h => ⟨tail_call_wp hp h.1, tail_call_wp hp' h.2⟩
    obtain ⟨_, t₄⟩ := xor_taint
    have a₃ := (RelCT.taint (A := taint) (P := fun a b => KCall s₀ a ∧ KCall s₀' b) _
      (fun a b h => AesCfb.RISCV64.Final.agree_of (by rw [h.1.sp, h.2.sp, qSp]) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.1.s7, h.2.s7, kV, kV, qV]
        · rw [h.1.s2, h.2.s2, qT]
        · rw [h.1.s3, h.2.s3, qU]) t₄).wp
      (F₁ := KDone s₀) (F₂ := KDone s₀') fun a b h => ⟨tail_xor_wp hp h.1 hu, tail_xor_wp hp' h.2 hu'⟩
    exact (a₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
      ((a₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq (a₃.mono (fun _ _ h => h) fun _ _ h => h.2))
  have r₃ : RelCT isa (fun a b => KWhole s₀ a ∧ KWhole s₀' b) (.ite (.zero .s3) (.block []) ctrFinalTail)
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
      ⟨WP.mono (AesCbc.RISCV64.wp_sp (mid_wp hp h.1)) fun _ x => x.2.trans h.1.sp,
        WP.mono (AesCbc.RISCV64.wp_sp (mid_wp hp' h.2)) fun _ x => x.2.trans h.2.sp⟩
  -- The registers restored.
  obtain ⟨_, t₅⟩ := restore_taint
  have r₄ := RelCT.taint (A := taint) (P := fun a b => (KDone s₀ a ∧ KDone s₀' b) ∧
      a.sp = s₀.sp ∧ b.sp = s₀'.sp) _
    (fun a b h => AesCfb.RISCV64.Final.agree_of (by rw [h.2.1, h.2.2, qSp]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.s7, h.1.2.s7, kV, kV, qV]) t₅
  exact (r₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((r₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    (r₃'.seq r₄))

theorem final_ct : ConstantTime isa ctrFinalRISCV64.pre ctrFinalRISCV64.pub ctrFinal :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (final_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Verified -/

theorem ctrFinal_verified : Verified RISCV64.target ctrFinal ctrFinalScratchContract :=
  Verified.of_correct final_correct final_ct ctrFinal_implies

/-! ## With `save` on the stack

The final function has four argument words, so `save` is its fifth, in `a4`:
it runs its code in a frame of 80 bytes on the stack (`withStackScratchWiped`),
`save`'s 80 bytes (the registers, then the block that held the last output
block), which it zeroes before returning. Its calls use 3232 bytes below it,
so 3312 in all. -/

/-- A state satisfying the shared contract's precondition. -/
def ctrFinalFrameSat : State := { ctrFinalSat with wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩] }

theorem ctrFinalFrameSat_pre : ∃ s, (Spec.Sm4.ctrFinalContract RISCV64.abi 3312).pre s := by
  implies_sat [Spec.Sm4.ctrFinalContract, Spec.Sm4.ctrFinalSig, RISCV64.abi, RISCV64.argRegs]
    [ctrFinalFrameSat, ctrFinalSat] using ctrFinalFrameSat

theorem ctrFinal_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchWiped 80 .a4 10 ctrFinal)
      (Spec.Sm4.ctrFinalContract RISCV64.abi 3312) := by
  rw [Proof.Sm4.ctrFinalContract_eq]
  exact RISCV64.Verified.stackScratchWiped (sig := Spec.Sm4.ctrFinalSig) (nm := "save") (e := .u64) (n := 10)
    (post := Proof.Sm4.ctrFinalPost RISCV64.abi.ptrBits) (wa := true) (stack := 3232) (bytes := 80) (words := 10)
    ctrFinal_verified (by decide) (by decide) (by decide) (Proof.Sm4.ctrFinalPostOut_local _) ctrFinalFrameSat_pre

end VG.Proof.Sm4.RISCV64.CtrFinal
