module

public import VerifiedGarbage.Proof.Aes.X86_64.BlocksVariant
public import VerifiedGarbage.Proof.AesCfb8.Rounds
public import VerifiedGarbage.Spec.Cfb8.Contract
import VerifiedGarbage.Proof.AesCbc.X86_64.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
public import VerifiedGarbage.Proof.AesCbc.X86_64.Body
import VerifiedGarbage.Proof.AesCbc.X86_64.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.AesCbc.X86_64.Body
meta import VerifiedGarbage.Proof.AesCbc.X86_64.Block
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.AesCfb8.Mem
public import VerifiedGarbage.Proof.AesCbc.X86_64.Loop
public import VerifiedGarbage.Impl.AesCfb8.X86_64
public import VerifiedGarbage.Proof.AesCfb8.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.AesCfb8.Mem
meta import VerifiedGarbage.Proof.AesCbc.X86_64.Loop
meta import VerifiedGarbage.Impl.AesCfb8.X86_64
meta import VerifiedGarbage.Proof.AesCfb8.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-! ### `AesCfb8.X86_64.CT`, which only this module used -/

section

/-! ### `AesCfb8.X86_64.Body`, which this module and modules that import it used -/

section

/-! ### `AesCfb8.X86_64.Steps`, which this module and modules that import it used -/

section

/-!
# AES-CFB8 on x86-64: the code between the calls

The straight-line pieces of a byte, run once each: the arguments of the
call on the copy of the input block (`args`), the data byte XORed with the
first byte of the enciphered block (`encByte`, `decByte`), and the input
block shifted (`shift`), with their memories as explicit writes
(`shiftMem64`, `Proof/AesCfb8/Mem.lean`).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCbc.X86_64 VG.Impl.AesCfb8.X86_64
open VG.Proof.AesCbc.X86_64 (offset_nat)

/-- The arguments of the call on the copy of the input block. -/
def args : List Instr :=
  [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (.imm cOff),
   .mov32 .rcx (.imm 1), .mov .r8 (.reg .r15)]

theorem pre_eq : pre = copy .r15 cOff .r12 0 ++ args := rfl

theorem args_ok (s : State) :
    ∃ s', runBlock isa args s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧
      s'.gpr .rdx = s.gpr .r15 + BitVec.ofNat 64 2048 ∧
      s'.gpr .rcx = 1 ∧ s'.gpr .r8 = s.gpr .r15 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [args, cOff, runBlock_cons, runStep_some, exec, execAlu, readSrc, Option.map_some,
      Option.bind_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, State.setReg32]

/-- The first four instructions of `encPost`. -/
def encByte : List Instr :=
  [.movzx8 .rax (at_ .r13 0), .movzx8 .rcx (at_ .r15 cOff), .alu .xor .rax (.reg .rcx),
   .store8 (at_ .r13 0) .rax]

/-- The first four instructions of `decPost`. -/
def decByte : List Instr :=
  [.movzx8 .rax (at_ .r13 0), .movzx8 .rcx (at_ .r15 cOff), .alu .xor .rcx (.reg .rax),
   .store8 (at_ .r13 0) .rcx]

theorem encPost_eq : encPost = encByte ++ (shift ++ Impl.AesCfb8.X86_64.advance) := rfl

theorem decPost_eq : decPost = decByte ++ (shift ++ Impl.AesCfb8.X86_64.advance) := rfl

theorem low_xor (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64).setWidth 8 = a ^^^ b := by
  ext i hi; simp

theorem encByte_ok (s : State) {P T : Addr} (hp : s.gpr .r13 = P) (ht : s.gpr .r15 + BitVec.ofNat 64 2048 = T)
    (rP : InRegions (s.rd ++ s.wr) P 1) (rT : InRegions (s.rd ++ s.wr) T 1) (wP : InRegions s.wr P 1) :
    ∃ s', runBlock isa encByte s = some s' ∧ (s'.gpr .rax).setWidth 8 = s.mem P ^^^ s.mem T ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW P (s.mem P ^^^ s.mem T) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, encByte, cOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, State.load8, State.store8, State.ea, offset_nat, execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, hp, BitVec.add_zero, ht, rP, rT, wP]
    rfl, ?_⟩
  refine ⟨?_, fun r h₁ h₂ => ?_, ?_, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg, h₁, h₂]
  · simp only [low_xor]

theorem decByte_ok (s : State) {P T : Addr} (hp : s.gpr .r13 = P) (ht : s.gpr .r15 + BitVec.ofNat 64 2048 = T)
    (rP : InRegions (s.rd ++ s.wr) P 1) (rT : InRegions (s.rd ++ s.wr) T 1) (wP : InRegions s.wr P 1) :
    ∃ s', runBlock isa decByte s = some s' ∧ (s'.gpr .rax).setWidth 8 = s.mem P ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW P (s.mem T ^^^ s.mem P) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, decByte, cOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, State.load8, State.store8, State.ea, offset_nat, execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, hp, BitVec.add_zero, ht, rP, rT, wP]
    rfl, ?_⟩
  refine ⟨?_, fun r h₁ h₂ => ?_, ?_, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg, h₁, h₂]
  · simp only [low_xor]

theorem shift_ok (s : State) {Q : Addr} (hq : s.gpr .r12 = Q)
    (r1 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 1) 8) (r8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (w0 : InRegions s.wr Q 8) (w7 : InRegions s.wr (Q + BitVec.ofNat 64 7) 8)
    (w15 : InRegions s.wr (Q + BitVec.ofNat 64 15) 1) :
    ∃ s', runBlock isa shift s = some s' ∧
      (∀ r, r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = AesCfb8.shiftMem64 s.mem Q ((s.gpr .rax).setWidth 8) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, shift, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.store64, State.store8, State.ea, offset_nat, Option.map_some,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, hq, BitVec.add_zero, r1, r8, w0, w7, w15]
    rfl, ?_⟩
  refine ⟨fun r h₁ h₂ => ?_, rfl, rfl, rfl⟩
  simp [gpr_setReg, h₁, h₂]

end VG.Proof.AesCfb8.X86_64

end

end

/-! ### `AesCfb8.X86_64.Loop`, which this module and modules that import it used -/

section

/-!
# AES-CFB8 on x86-64: the contracts, and the loop

The artifacts' contracts are the shared ones of `Spec/Cfb8/Contract.lean`,
which imply these (`Verified.lean`): `cfb8X86_64 enc`, for encryption
(`enc = true`) and decryption. The functions have AES-CBC's arguments, with
`len` counting bytes, and its prologue and epilogue
(`Proof/AesCbc/X86_64/Loop.lean`), whose stride-free lemmas this reuses.

The invariant after `k` bytes (`LInv`): the registers hold the arguments
(`r13` the next byte, `r14` the bytes left), only the input block, the
data, the first 2064 bytes of the scratch buffer and the stack below the
return address have changed since the registers were saved, the first `k`
bytes are CFB8's of the first `k` bytes on entry and the rest are
unchanged, and the input block is the one after them.

`whole_wp`: if one run of `body` takes the invariant from `k` to `k + 1`
bytes and sets ZF when none are left (`BodyOk`), `whole body` meets the
contract.
-/

@[expose] public section

namespace VG.Proof.AesCfb8.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCbc.X86_64
open VG.Proof.AesCbc.X86_64 (wK W R Iv Dp N S schR ivR scrR stkR iv0 savedMem in_rw savedMem_frame
  saved_bound slot_contains prologue_ok rsi_ofNat r8_ofNat beq_zero)
open VG.Spec.Aes (bytesAt)

/-- `vg_aes_cfb8_encrypt` (`enc`) or `vg_aes_cfb8_decrypt`, with the
arguments `(schedule = rdi, rounds = rsi, iv = rdx, data = rcx, len = r8, scratch = r9)`. -/
def cfb8X86_64 (enc : Bool) : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let iv : Region := ⟨s.gpr .rdx, 16⟩
    let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 2176⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 8
    s.rd = [sched] ∧ s.wr = [iv, data, scr] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ iv.Disjoint data ∧
      iv.Disjoint scr ∧ data.Disjoint scr ∧ ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧
      stack.Disjoint sched ∧ stack.Disjoint iv ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧
      (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    let ciph := Spec.Cbc.aesWith (s.gpr .rsi).toNat (bytesAt s.mem (s.gpr .rdi) (16 * ((s.gpr .rsi).toNat + 1)))
    let iv := bytesAt s.mem (s.gpr .rdx) 16
    let xs := bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat
    bytesAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat = cfb8 enc ciph iv xs ∧
      bytesAt s'.mem (s.gpr .rdx) 16 = inK enc ciph iv xs
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .rsp = s₂.gpr .rsp

section
variable (s₀ : State)

abbrev dataR : Region := ⟨Dp s₀, N s₀⟩

/-- The cipher. -/
abbrev ciph : Spec.Cbc.Cipher := Spec.Cbc.aesWith (R s₀) (wK s₀)

/-- The bytes on entry. -/
abbrev bs : List Byte := bytesAt s₀.mem (Dp s₀) (N s₀)

/-- The address of byte `k`. -/
abbrev byt (k : Nat) : Addr := Dp s₀ + BitVec.ofNat 64 k

/-- The first `k` bytes after CFB8. -/
abbrev outK (enc : Bool) (k : Nat) : List Byte := cfb8 enc (ciph s₀) (iv0 s₀) ((bs s₀).take k)

/-- The input block after the first `k` bytes. -/
abbrev inKk (enc : Bool) (k : Nat) : List Byte := inK enc (ciph s₀) (iv0 s₀) ((bs s₀).take k)

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀]
  wr : s₀.wr = [ivR s₀, dataR s₀, scrR s₀]
  sch_iv : (schR s₀).Disjoint (ivR s₀)
  sch_data : (schR s₀).Disjoint (dataR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  iv_data : (ivR s₀).Disjoint (dataR s₀)
  iv_scr : (ivR s₀).Disjoint (scrR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  ret_iv : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (ivR s₀)
  ret_data : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (dataR s₀)
  ret_scr : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (scrR s₀)
  stk_sch : (stkR s₀).Disjoint (schR s₀)
  stk_iv : (stkR s₀).Disjoint (ivR s₀)
  stk_data : (stkR s₀).Disjoint (dataR s₀)
  stk_scr : (stkR s₀).Disjoint (scrR s₀)
  iv_wrap : (Iv s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (Dp s₀).toNat + N s₀ ≤ 2 ^ 64
  scr_wrap : (S s₀).toNat + 2176 ≤ 2 ^ 64
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {enc : Bool} {s₀ : State} (h : (cfb8X86_64 enc).pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t⟩

/-- The loop invariant, after `k` bytes. -/
structure LInv (enc : Bool) (s₀ : State) (k : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = W s₀
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r12 : s.gpr .r12 = Iv s₀
  r13 : s.gpr .r13 = byt s₀ k
  r14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)
  r15 : s.gpr .r15 = S s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, stkR s₀] (savedMem s₀) s.mem
  data : bytesAt s.mem (Dp s₀) (N s₀) = outK s₀ enc k ++ (bs s₀).drop k
  iv : bytesAt s.mem (Iv s₀) 16 = inKk s₀ enc k

/-! ## Regions -/

section
variable {s₀ : State}

theorem UPre.scr_sub {d n : Nat} (h : d + n ≤ 2176) : Region.Sub ⟨S s₀ + BitVec.ofNat 64 d, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {k : Nat} (hk : k < N s₀) : Region.Sub ⟨byt s₀ k, 1⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega_using [hk])

theorem UPre.byt_disjoint (hp : UPre s₀) {j k : Nat} (hj : j < N s₀) (hk : k < N s₀) (hjk : j ≠ k) :
    (⟨byt s₀ j, 1⟩ : Region).Disjoint ⟨byt s₀ k, 1⟩ := by
  have := hp.data_wrap
  exact Offset.disjoint _ (by omega_using [hjk]) (by omega_using [hj, this]) (by omega_using [hk, this])

end

/-- The regions the function writes. -/
abbrev Big (s₀ : State) : List Region := [ivR s₀, dataR s₀, scrR s₀, stkR s₀]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    bytesAt m (W s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  refine AesCbc.X86_64.bytesAt_frame hf (fun r hr => ?_) (by omega_using [hR])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.sch_iv.sub_left (Region.sub_prefix hR)
  · exact hp.sch_data.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.stk_sch.symm.sub_left (Region.sub_prefix hR)

omit hp in
theorem UPre.big_of {m : Mem} (hf : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, stkR s₀] (savedMem s₀) m) :
    Frame (Big s₀) s₀.mem m := by
  have f₀ : Frame (Big s₀) s₀.mem (savedMem s₀) :=
    (savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩
  exact f₀.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)

/-- The bytes after a step that changed only byte `k`, the input block, the
first 2064 bytes of the scratch buffer and the stack. -/
theorem UPre.bytes_step {m m' : Mem} {k : Nat} (hk : k < N s₀)
    (hf : Frame [⟨byt s₀ k, 1⟩, ivR s₀, ⟨S s₀, 2064⟩, stkR s₀] m m') :
    bytesAt m' (Dp s₀) (N s₀) = (bytesAt m (Dp s₀) (N s₀)).set k (m' (byt s₀ k)) := by
  refine bytesAt_set fun j hj hjk => ?_
  have e := AesCbc.X86_64.bytesAt_frame (p := byt s₀ j) (n := 1) hf (fun r hr => ?_) (by decide)
  · simpa [bytesAt] using e
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.byt_disjoint hj hk hjk
  · exact hp.iv_data.symm.sub_left (UPre.data_sub hj)
  · exact (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right (Region.sub_prefix (by decide))
  · exact hp.stk_data.symm.sub_left (UPre.data_sub hj)

end

theorem length_bs (s₀ : State) : (bs s₀).length = N s₀ := by simp [bytesAt]

/-- Byte `k` before the step, from the invariant. -/
theorem LInv.byte {enc : Bool} {s₀ : State} {k : Nat} {s : State} (h : LInv enc s₀ k s) (hk : k < N s₀) :
    s.mem (byt s₀ k) = (bs s₀)[k]'(by rw [length_bs]; exact hk) := by
  have hl : (outK s₀ enc k).length = k := by
    rw [outK, length_cfb8, List.length_take, length_bs]; omega_using [hk]
  have := congrArg (·[k]?) h.data
  simp only [List.getElem?_append_right (show (outK s₀ enc k).length ≤ k by omega_using [hl]), hl, Nat.sub_self,
    List.getElem?_drop, Nat.add_zero] at this
  rw [List.getElem?_eq_getElem (by simp [bytesAt]; exact hk),
    List.getElem?_eq_getElem (by rw [length_bs]; exact hk)] at this
  simpa [bytesAt] using Option.some.inj this

theorem take_succ_bs (s₀ : State) {k : Nat} (hk : k < N s₀) :
    (bs s₀).take (k + 1) = (bs s₀).take k ++ [(bs s₀)[k]'(by rw [length_bs]; exact hk)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [length_bs]; exact hk)]
  rfl

theorem advance_ok (s : State) :
    ∃ s', runBlock isa Impl.AesCfb8.X86_64.advance s = some s' ∧
      s'.gpr .r13 = s.gpr .r13 + BitVec.ofNat 64 1 ∧ s'.gpr .r14 = s.gpr .r14 - 1 ∧
      s'.zf = some ((s.gpr .r14 - 1) == 0) ∧ (∀ r, r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, Impl.AesCfb8.X86_64.advance,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some, gpr_setReg,
      gpr_arithFlags]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · exact gpr_setReg_self _ _ _
  · rw [zf_setReg, zf_arithFlags]; simp
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]

/-- What `advance` leaves after byte `k`: the registers of byte `k + 1`, and
ZF set if it was the last. -/
theorem advance_regs {s₀ : State} {k : Nat} (hk : k < N s₀) {s : State}
    (h13 : s.gpr .r13 = byt s₀ k) (h14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)) :
    ∃ s', runBlock isa Impl.AesCfb8.X86_64.advance s = some s' ∧ s'.gpr .r13 = byt s₀ (k + 1) ∧
      s'.gpr .r14 = BitVec.ofNat 64 (N s₀ - (k + 1)) ∧ s'.zf = some (decide (N s₀ - (k + 1) = 0)) ∧
      (∀ r, r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', run, r13', r14', zf', keep, mem', rd', wr'⟩ := advance_ok s
  have hN := (s₀.gpr .r8).isLt
  have dec : BitVec.ofNat 64 (N s₀ - k) - 1 = BitVec.ofNat 64 (N s₀ - (k + 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega_using [hk])]; rfl
  refine ⟨s', run, ?_, ?_, ?_, keep, mem', rd', wr'⟩
  · rw [r13', h13, Offset.add_add_eq _ (c := k + 1) (by omega_using [])]
  · rw [r14', h14, dec]
  · rw [zf', h14, dec, beq_zero (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN)]

/-! ## The loop -/

/-- One run of `body` takes the invariant from `k` bytes to `k + 1`, and sets
ZF if no bytes are left. -/
def BodyOk (enc : Bool) (body : Prog isa) : Prop :=
  ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv enc s₀ k s →
    WP isa body s fun s' => LInv enc s₀ (k + 1) s' ∧ s'.zf = some (decide (N s₀ - (k + 1) = 0))

theorem loop_ok {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (hp : UPre s₀) {k : Nat}
    (hk : k < N s₀) {s : State} (h : LInv enc s₀ k s) : WP isa (.loop body .ne) s (LInv enc s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body) (c := .ne) (Q := LInv enc s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv enc s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (hb hp hk h) fun s' ⟨h', zf'⟩ => ?_
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by simp [eval, zf', hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega_using [hk, hz]]
  · right
    refine ⟨by simp [eval, zf', hz], N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hz], h'⟩

/-! ## Saving and restoring the registers -/

theorem prologue_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (save ++ setup)) s₀ fun s₁ => LInv enc s₀ 0 s₁ ∧ s₁.zf = some (decide (N s₀ = 0)) := by
  have hN := (s₀.gpr .r8).isLt
  obtain ⟨s₁, run₁, rbx₁, rbp₁, r12₁, r13₁, r14₁, r15₁, rsp₁, zf₁, mem₁, rd₁, wr₁⟩ :=
    prologue_ok s₀ fun d _ h₂ => by
      rw [hp.wr]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega_using [h₂]) (by omega_using [h₂]))
  have f₀ := savedMem_frame s₀
  have disj : ∀ (r : Region), r ∈ [ivR s₀, dataR s₀] → ∀ r' ∈ [⟨s₀.gpr .r9 + BitVec.ofNat 64 2064, 48⟩],
      r.Disjoint r' := by
    intro r hr r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hr'
    subst hr'
    rcases hr with rfl | rfl
    · exact hp.iv_scr.sub_right (UPre.scr_sub (by decide))
    · exact hp.data_scr.sub_right (UPre.scr_sub (by decide))
  have ivS : bytesAt (savedMem s₀) (Iv s₀) 16 = iv0 s₀ :=
    AesCbc.X86_64.bytesAt_frame f₀ (disj _ (by simp)) (by decide)
  have dataS : bytesAt (savedMem s₀) (Dp s₀) (N s₀) = bs s₀ :=
    AesCbc.X86_64.bytesAt_frame f₀ (disj _ (by simp)) (by simp only [N]; omega_using [])
  have dat : outK s₀ enc 0 ++ (bs s₀).drop 0 = bs s₀ := by
    simp only [outK, List.take_zero, cfb8_nil, List.drop_zero, List.nil_append]
  have ivv : inKk s₀ enc 0 = iv0 s₀ := by
    simp only [inKk, List.take_zero, inK_nil]
  refine WP.of_runBlock ⟨s₁, run₁, ?_, ?_⟩
  · exact { rbx := rbx₁, rbp := rbp₁, r12 := r12₁
            r13 := by rw [r13₁]; simp
            r14 := by rw [r14₁, r8_ofNat]; rfl
            r15 := r15₁, rsp := rsp₁, rd := rd₁, wr := wr₁
            frame := by rw [mem₁]; exact Frame.refl _ _
            data := by rw [mem₁, dataS, dat]
            iv := by rw [mem₁, ivS, ivv] }
  · rw [zf₁, r8_ofNat, beq_zero hN]

theorem mid_wp {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (hp : UPre s₀) {s₁ : State}
    (h : LInv enc s₀ 0 s₁) (hz : s₁.zf = some (decide (N s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop body .ne)) s₁ (LInv enc s₀ (N s₀)) := by
  have ev : isa.eval .e s₁ = some (decide (N s₀ = 0)) := hz
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hb hp (by omega_using [hn]) h

theorem slots_disj {s₀ : State} (hp : UPre s₀) :
    ∀ r ∈ [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, stkR s₀], (⟨S s₀ + BitVec.ofNat 64 2064, 48⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.iv_scr.symm.sub_left (UPre.scr_sub (by decide))
  · exact hp.data_scr.symm.sub_left (UPre.scr_sub (by decide))
  · exact Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega_using [])
  · exact hp.stk_scr.symm.sub_left (UPre.scr_sub (by decide))

theorem slot_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, stkR s₀] (savedMem s₀) m) {d : Nat} (h₁ : 2064 ≤ d)
    (h₂ : d + 8 ≤ 2112) :
    m.readW (S s₀ + BitVec.ofNat 64 d) 64 = (savedMem s₀).readW (S s₀ + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨S s₀ + BitVec.ofNat 64 2064, 48⟩) (slot_contains _ h₁ h₂) (slots_disj hp) (by decide)

theorem epilogue_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {s₂ : State} (h₂ : LInv enc s₀ (N s₀) s₂) :
    WP isa (.block restore) s₂ fun s' => gprPreserved s₀ s' ∧ (cfb8X86_64 enc).post s₀ s' := by
  have rdwr : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr]
  have hsv : Spill.Saved s₂.mem (s₂.gpr .r15) s₀.gpr saved := fun p hp' => by
    have := saved_bound p hp'
    rw [h₂.r15, slot_read hp h₂.frame this.1 this.2]
    exact Spill.saveMem_saved _ _ _ _ (by decide) p hp'
  have hall : (bs s₀).take (N s₀) = bs s₀ := List.take_of_length_le (by rw [length_bs])
  have hnil : (bs s₀).drop (N s₀) = [] := List.drop_of_length_le (by rw [length_bs])
  refine WP.mono (Spill.restore_ok .r15 saved s₀.gpr s₂ (by decide) (fun p hp' => ?_) hsv)
    fun s₃ ⟨g₁, g₂, mem₃, _⟩ => ⟨⟨Spill.calleeSaved_ok g₁ g₂ (by decide) h₂.rsp, ?_⟩, ?_, ?_⟩
  · have := saved_bound p hp'
    rw [rdwr, hp.rd, hp.wr, h₂.r15]
    exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega_using [this]) (by have := hp.scr_wrap; omega_arith))
  · rw [mem₃]
    refine (UPre.big_of h₂.frame).readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.ret_iv
    · exact hp.ret_data
    · exact hp.ret_scr
    · exact Offset.base_disjoint_below _ (by decide)
  · show bytesAt s₃.mem (Dp s₀) (N s₀) = _
    rw [mem₃, h₂.data]; simp only [outK, hall, hnil, List.append_nil]
  · show bytesAt s₃.mem (Iv s₀) 16 = _
    rw [mem₃, h₂.iv]; simp only [inKk, hall]

theorem whole_wp {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (h0 : (cfb8X86_64 enc).pre s₀) :
    WP isa (whole body) s₀ fun s' => gprPreserved s₀ s' ∧ (cfb8X86_64 enc).post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, z₁⟩ =>
    WP.seq (WP.mono (mid_wp hb hp h₁ z₁) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.AesCfb8.X86_64

end

end

/-!
# AES-CFB8 on x86-64: one byte

`encBody_ok` and `decBody_ok`: one run of `body` takes the loop invariant
(`Loop.lean`) from `k` bytes to `k + 1` (`BodyOk`), for any implementation
of the block functions (`BlocksImpl`). The input block is copied to the
scratch buffer and enciphered there (`call_ok`), the data byte is replaced,
and the input block is shifted (`finish_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCbc.X86_64 VG.Impl.AesCfb8.X86_64
open VG.Proof.AesCbc (copyMem copyMem_frame copyMem_bytes aesWith_state set_prefix)
open VG.Proof.AesCbc.X86_64 (wK W R Iv Dp N S schR ivR scrR stkR iv0 in_rw Sv cIv0 cIv8 cSv0 cSv8 sv8
  copy_ok CallPre CallPost blk_call calleeSaved_ne_rax rsi_ofNat)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)

theorem headD_bytesAt (m : Mem) (p : Addr) : (bytesAt m p 16).headD 0 = m p := by
  simp [bytesAt, List.range_succ_eq_map]

/-- A byte outside a frame is unchanged. -/
theorem byte_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 1⟩ : Region).Disjoint r) : m' p = m p := by
  have := AesCbc.X86_64.bytesAt_frame hf hd (by decide)
  simpa [bytesAt] using this

theorem writeW8_self (m : Mem) (p : Addr) (v : Byte) : m.writeW p v p = v := by
  rw [writeW8_apply, BitVec.sub_self]; simp

theorem frame_write8 (m : Mem) (p : Addr) (v : Byte) : Frame [⟨p, 1⟩] m (m.writeW p v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem LInv.regs {enc : Bool} {k : Nat} {s : State} (h : LInv enc s₀ k s) :
    s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
  rw [h.rd, h.wr, hp.rd, hp.wr]; rfl

theorem LInv.wrs {enc : Bool} {k : Nat} {s : State} (h : LInv enc s₀ k s) :
    s.wr = [ivR s₀, dataR s₀, scrR s₀] := by
  rw [h.wr, hp.wr]

theorem UPre.cByt {k : Nat} (hk : k < N s₀) : (dataR s₀).Contains (byt s₀ k) 1 := by
  have := hp.data_wrap
  exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk, this])

theorem UPre.byt_iv {k : Nat} (hk : k < N s₀) : (⟨byt s₀ k, 1⟩ : Region).Disjoint (ivR s₀) :=
  hp.iv_data.symm.sub_left (UPre.data_sub hk)

theorem UPre.byt_sv {k : Nat} (hk : k < N s₀) : (⟨byt s₀ k, 1⟩ : Region).Disjoint ⟨S s₀, 2064⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))

theorem UPre.byt_stk {k : Nat} (hk : k < N s₀) : (⟨byt s₀ k, 1⟩ : Region).Disjoint (stkR s₀) :=
  (hp.stk_data.sub_right (UPre.data_sub hk)).symm

theorem UPre.iv_sv : (ivR s₀).Disjoint ⟨Sv s₀, 16⟩ :=
  hp.iv_scr.sub_right (UPre.scr_sub (by decide))

theorem UPre.sv_scr : (⟨Sv s₀, 16⟩ : Region).Disjoint ⟨S s₀, 2048⟩ :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega_using [])

theorem UPre.sv_wrap : (Sv s₀).toNat + 16 ≤ 2 ^ 64 := by
  have := hp.scr_wrap
  rw [Sv, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
    Nat.mod_eq_of_lt (by omega_using [this])]
  omega_using [this]

/-- The arguments of a call on the copy of the input block, with the
working space at the start of the scratch buffer. -/
theorem UPre.callPre {s : State}
    (rdi : s.gpr .rdi = W s₀) (rsi : s.gpr .rsi = s₀.gpr .rsi) (rdx : s.gpr .rdx = Sv s₀)
    (rcx : s.gpr .rcx = 1) (r8 : s.gpr .r8 = S s₀) (rsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre s (W s₀) (Sv s₀) (S s₀) (R s₀) where
  rdi := rdi
  rsi := by rw [rsi, rsi_ofNat]
  rdx := rdx
  rcx := rcx
  r8 := r8
  rounds := hp.rounds
  wd := hp.sch_scr.sub_right (UPre.scr_sub (by decide))
  ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  ds := hp.sv_scr
  stkW := by rw [rsp]; exact hp.stk_sch
  stkD := by rw [rsp]; exact hp.stk_scr.sub_right (UPre.scr_sub (by decide))
  stkS := by rw [rsp]; exact hp.stk_scr.sub_right (Region.sub_prefix (by decide))
  wrap := hp.sv_wrap
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

end

/-- What the code before the call and the call leave, for either
direction. -/
structure AfterCall (enc : Bool) (s₀ : State) (k : Nat) (s s₂ : State) : Prop where
  g : ∀ r ∈ calleeSaved, s₂.gpr r = s.gpr r
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  frame : Frame [⟨S s₀, 2064⟩, stkR s₀] s.mem s₂.mem
  out : s₂.mem (Sv s₀) = (ciph s₀ (inKk s₀ enc k)).headD 0

theorem call_ok {enc : Bool} (v : BlocksImpl) {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State}
    (h : LInv enc s₀ k s) (post : List Instr) {Q : State → Prop}
    (hq : ∀ s₂, AfterCall enc s₀ k s s₂ → WP isa (.block post) s₂ Q) :
    WP isa (body v.enc post) s Q := by
  have hR := h.regs hp
  have hW := h.wrs hp
  obtain ⟨s₁, run₁, g₁, mem₁, rd₁, wr₁⟩ :=
    copy_ok s (dst := .r15) (src := .r12) (d := cOff) (e := 0) (P := Sv s₀) (Q := Iv s₀)
      (by rw [h.r15]; rfl) (by rw [h.r15]; exact sv8 _)
      (by rw [h.r12]; simp) (by rw [h.r12])
      (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
      (by rw [hW]; exact in_rw (by simp) cSv0) (by rw [hW]; exact in_rw (by simp) cSv8)
      (by decide) (by decide)
  obtain ⟨s₂, run₂, rdi₂, rsi₂, rdx₂, rcx₂, r8₂, cs₂, mem₂, rd₂, wr₂⟩ := args_ok s₁
  have keep (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s.gpr r := by
    rw [cs₂ r hr, g₁ r (calleeSaved_ne_rax hr)]
  have pre₂ : CallPre s₂ (W s₀) (Sv s₀) (S s₀) (R s₀) :=
    hp.callPre (by rw [rdi₂, g₁ _ (by decide), h.rbx]) (by rw [rsi₂, g₁ _ (by decide), h.rbp])
      (by rw [rdx₂, g₁ _ (by decide), h.r15]) rcx₂ (by rw [r8₂, g₁ _ (by decide), h.r15])
      (by rw [keep .rsp (by simp [calleeSaved]), h.rsp]) (by rw [rd₂, rd₁, h.rd]) (by rw [wr₂, wr₁, h.wr])
  refine WP.seq ?_
  rw [pre_eq, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  refine WP.seq (WP.mono (blk_call v.encOk v.encNosp v.encDepth pre₂) fun s₃ c => hq s₃ ?_)
  have rsp₂ : s₂.gpr .rsp = s₀.gpr .rsp := by rw [keep .rsp (by simp [calleeSaved]), h.rsp]
  have svSub : Region.Sub ⟨Sv s₀, 16⟩ ⟨S s₀, 2064⟩ := Offset.sub_base _ (by decide)
  have f₁ : Frame [⟨Sv s₀, 16⟩] s.mem s₂.mem := by rw [mem₂, mem₁]; exact copyMem_frame _ _ _
  have big₂ : Frame (Big s₀) s₀.mem s₂.mem :=
    (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩)
  refine ⟨fun r hr => by rw [c.saved r hr, keep r hr], by rw [c.rd, rd₂, rd₁], by rw [c.wr, wr₂, wr₁],
    (f₁.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_), ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨S s₀, 2064⟩, by simp, svSub⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨S s₀, 2064⟩, by simp, svSub⟩
    · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, by rw [rsp₂]; exact fun _ h => h⟩
  · rw [← headD_bytesAt s₃.mem (Sv s₀), c.out, UPre.sched_bytes hp big₂, ← aesWith_state, mem₂, mem₁,
      copyMem_bytes _ hp.iv_sv.symm, h.iv]

/-- After the byte operation (`v` the new data byte, `c` the byte to shift
in, in `al`), the shift and `advance` take the invariant to `k + 1`. -/
theorem finish_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ s₃ : State}
    (h : LInv enc s₀ k s) (a : AfterCall enc s₀ k s s₂) {v : Byte}
    (g₃ : ∀ r, r ≠ .rax → r ≠ .rcx → s₃.gpr r = s₂.gpr r) (mem₃ : s₃.mem = s₂.mem.writeW (byt s₀ k) v)
    (rd₃ : s₃.rd = s₂.rd) (wr₃ : s₃.wr = s₂.wr)
    (hv : v = (bs s₀)[k]'(by rw [length_bs]; exact hk) ^^^ (ciph s₀ (inKk s₀ enc k)).headD 0)
    (hc : (s₃.gpr .rax).setWidth 8 = if enc then v else (bs s₀)[k]'(by rw [length_bs]; exact hk)) :
    WP isa (.block (shift ++ Impl.AesCfb8.X86_64.advance)) s₃
      fun s' => LInv enc s₀ (k + 1) s' ∧ s'.zf = some (decide (N s₀ - (k + 1) = 0)) := by
  have g₃' (r : Reg) (hr : r ∈ calleeSaved) : s₃.gpr r = s.gpr r := by
    rw [g₃ r (calleeSaved_ne_rax hr) (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), a.g r hr]
  have hW₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₃, a.wr, h.wrs hp]
  have cIv (d n : Nat) (hd : d + n ≤ 16) : InRegions s₃.wr (Iv s₀ + BitVec.ofNat 64 d) n := by
    rw [hW₃]; exact in_rw (by simp) (Offset.contains_base _ hd (by omega_using [hd]))
  have cIvR (d n : Nat) (hd : d + n ≤ 16) : InRegions (s₃.rd ++ s₃.wr) (Iv s₀ + BitVec.ofNat 64 d) n := by
    rw [rd₃, a.rd, hW₃, h.rd, hp.rd]; exact in_rw (by simp) (Offset.contains_base _ hd (by omega_using [hd]))
  obtain ⟨s₄, run₄, g₄, mem₄, rd₄, wr₄⟩ :=
    shift_ok s₃ (Q := Iv s₀) (by rw [g₃' .r12 (by simp [calleeSaved]), h.r12]) (cIvR 1 8 (by decide))
      (cIvR 8 8 (by decide)) (by simpa using cIv 0 8 (by decide)) (cIv 7 8 (by decide)) (cIv 15 1 (by decide))
  obtain ⟨s₅, run₅, r13₅, r14₅, zf₅, keep₅, mem₅, rd₅, wr₅⟩ := advance_regs (s := s₄) hk
    (by rw [g₄ _ (by decide) (by decide), g₃' .r13 (by simp [calleeSaved]), h.r13])
    (by rw [g₄ _ (by decide) (by decide), g₃' .r14 (by simp [calleeSaved]), h.r14])
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, run₄, WP.of_runBlock ⟨s₅, run₅, ?_⟩⟩
  have g (r : Reg) (hr : r ∈ calleeSaved) (h13 : r ≠ .r13) (h14 : r ≠ .r14) : s₅.gpr r = s.gpr r := by
    rw [keep₅ r h13 h14, g₄ r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), g₃' r hr]
  -- Memory.
  have fStep : Frame [⟨byt s₀ k, 1⟩, ivR s₀, ⟨S s₀, 2064⟩, stkR s₀] s.mem s₅.mem := by
    rw [mem₅, mem₄, mem₃]
    refine (a.frame.sub fun r hr => ?_).trans
      (((frame_write8 _ _ _).sub fun r hr => ?_).trans ((AesCfb8.shiftMem64_frame _ _ _).sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have one (r : Region) (P : Addr) (n : Nat) (hd : (⟨P, n⟩ : Region).Disjoint r) :
      ∀ r' ∈ [r], (⟨P, n⟩ : Region).Disjoint r' := fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hd
  have newByte : s₅.mem (byt s₀ k) = v := by
    rw [mem₅, mem₄, byte_frame (AesCfb8.shiftMem64_frame _ _ _) (one _ _ _ (hp.byt_iv hk)), mem₃, writeW8_self]
  have ivIn : bytesAt s₃.mem (Iv s₀) 16 = inKk s₀ enc k := by
    rw [mem₃, AesCbc.X86_64.bytesAt_frame (frame_write8 _ _ _) (one _ _ _ (hp.byt_iv hk).symm) (by decide),
      AesCbc.X86_64.bytesAt_frame a.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
        · exact hp.stk_iv.symm) (by decide), h.iv]
  have hl : (outK s₀ enc k).length = k := by
    rw [outK, length_cfb8, List.length_take, length_bs]; omega_using [hk]
  have iv_ne : iv0 s₀ ≠ [] := by simp [iv0, bytesAt]
  refine ⟨⟨?_, ?_, ?_, r13₅, r14₅, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, zf₅⟩
  · rw [g .rbx (by simp [calleeSaved]) (by decide) (by decide), h.rbx]
  · rw [g .rbp (by simp [calleeSaved]) (by decide) (by decide), h.rbp]
  · rw [g .r12 (by simp [calleeSaved]) (by decide) (by decide), h.r12]
  · rw [g .r15 (by simp [calleeSaved]) (by decide) (by decide), h.r15]
  · rw [g .rsp (by simp [calleeSaved]) (by decide) (by decide), h.rsp]
  · rw [rd₅, rd₄, rd₃, a.rd, h.rd]
  · rw [wr₅, wr₄, wr₃, a.wr, h.wr]
  · exact h.frame.trans (fStep.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  · rw [hp.bytes_step hk fStep, h.data, newByte, set_prefix _ _ _ hl (by rw [length_bs]; exact hk), hv]
    simp only [outK, take_succ_bs s₀ hk, cfb8_snoc enc _ iv_ne, inKk]
  · rw [mem₅, mem₄, AesCfb8.shiftMem64_bytes, ivIn, hc]
    simp only [inKk, take_succ_bs s₀ hk, inK_snoc enc _ iv_ne, ← hv]

theorem encBody_ok (v : BlocksImpl) : BodyOk true (body v.enc encPost) := by
  intro s₀ hp k hk s h
  refine call_ok v hp h encPost fun s₂ a => ?_
  have hR₂ : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [a.rd, a.wr, h.regs hp]
  have hW₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [a.wr, h.wrs hp]
  have cSv₁ : InRegions [schR s₀, ivR s₀, dataR s₀, scrR s₀] (Sv s₀) 1 :=
    in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by decide) (by decide))
  obtain ⟨s₃, run₃, rax₃, g₃, mem₃, rd₃, wr₃⟩ :=
    encByte_ok s₂ (P := byt s₀ k) (T := Sv s₀) (by rw [a.g .r13 (by simp [calleeSaved]), h.r13])
      (by rw [a.g .r15 (by simp [calleeSaved]), h.r15])
      (by rw [hR₂]; exact in_rw (by simp) (hp.cByt hk)) (by rw [hR₂]; exact cSv₁)
      (by rw [hW₂]; exact in_rw (by simp) (hp.cByt hk))
  have p₂ : s₂.mem (byt s₀ k) = (bs s₀)[k]'(by rw [length_bs]; exact hk) := by
    rw [byte_frame a.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.byt_sv hk
      · exact hp.byt_stk hk), h.byte hk]
  rw [encPost_eq, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, finish_wp hp hk h a g₃ mem₃ rd₃ wr₃ (by rw [p₂, a.out]) ?_⟩
  rw [rax₃]; simp only [↓reduceIte, p₂, a.out]

theorem decBody_ok (v : BlocksImpl) : BodyOk false (body v.enc decPost) := by
  intro s₀ hp k hk s h
  refine call_ok v hp h decPost fun s₂ a => ?_
  have hR₂ : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [a.rd, a.wr, h.regs hp]
  have hW₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [a.wr, h.wrs hp]
  have cSv₁ : InRegions [schR s₀, ivR s₀, dataR s₀, scrR s₀] (Sv s₀) 1 :=
    in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by decide) (by decide))
  obtain ⟨s₃, run₃, rax₃, g₃, mem₃, rd₃, wr₃⟩ :=
    decByte_ok s₂ (P := byt s₀ k) (T := Sv s₀) (by rw [a.g .r13 (by simp [calleeSaved]), h.r13])
      (by rw [a.g .r15 (by simp [calleeSaved]), h.r15])
      (by rw [hR₂]; exact in_rw (by simp) (hp.cByt hk)) (by rw [hR₂]; exact cSv₁)
      (by rw [hW₂]; exact in_rw (by simp) (hp.cByt hk))
  have p₂ : s₂.mem (byt s₀ k) = (bs s₀)[k]'(by rw [length_bs]; exact hk) := by
    rw [byte_frame a.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.byt_sv hk
      · exact hp.byt_stk hk), h.byte hk]
  rw [decPost_eq, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, finish_wp hp hk h a g₃ mem₃ rd₃ wr₃ (by rw [p₂, a.out, BitVec.xor_comm]) ?_⟩
  rw [rax₃]; simp only [Bool.false_eq_true, ↓reduceIte, p₂]

end VG.Proof.AesCfb8.X86_64

end

end

/-!
# AES-CFB8 on x86-64: constant time

AES-CBC's argument (`Proof/AesCbc/X86_64/CT.lean`) for the CFB8 loop: two
runs from states that agree on the public arguments are related piece by
piece (`RelCT`): the taint analysis covers the code between the calls, from
the registers the correctness proof pins to the public arguments (`LInv`),
and each call of a block function is constant time by its own proof
(`blk_rel`). `whole_ct`: if one run of `body` is (`BodyCt`), `whole body` is.
-/

@[expose] public section

namespace VG.Proof.AesCfb8.X86_64

open VG VG.X86_64 VG.Impl.AesCbc.X86_64 VG.Impl.AesCfb8.X86_64
open VG.Proof.AesCbc.X86_64 (W R Iv Dp N S iv0 Sv CallPre CallPost blk_call blk_rel)
open VG.Proof.Aes.X86_64 (BlocksImpl)

section
variable {enc : Bool} {s₀ s₀' : State} (hq : (cfb8X86_64 enc).pub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.1
theorem pub_rsi : s₀.gpr .rsi = s₀'.gpr .rsi := hq.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_rsi hq]
theorem pub_Iv : Iv s₀ = Iv s₀' := hq.2.2.1
theorem pub_Dp : Dp s₀ = Dp s₀' := hq.2.2.2.1
theorem pub_N : N s₀ = N s₀' := by rw [N, N, hq.2.2.2.2.1]
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.1
theorem pub_rsp : s₀.gpr .rsp = s₀'.gpr .rsp := hq.2.2.2.2.2.2
theorem pub_byt (k : Nat) : byt s₀ k = byt s₀' k := by rw [byt, byt, pub_Dp hq]

/-- The registers the invariant pins agree in both runs. -/
theorem LInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : LInv enc s₀ k s₁) (h₂ : LInv enc s₀' k s₂) :
    ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.rbx, h₂.rbx, pub_W hq]
  · rw [h₁.rbp, h₂.rbp, pub_rsi hq]
  · rw [h₁.r12, h₂.r12, pub_Iv hq]
  · rw [h₁.r13, h₂.r13, pub_byt hq]
  · rw [h₁.r14, h₂.r14, pub_N hq]
  · rw [h₁.r15, h₂.r15, pub_S hq]
  · rw [h₁.rsp, h₂.rsp, pub_rsp hq]

end

/-- One run of `body` from `k` bytes is constant time. -/
def BodyCt (enc : Bool) (body : Prog isa) : Prop :=
  ∀ {s₀ s₀' : State}, UPre s₀ → UPre s₀' → (cfb8X86_64 enc).pub s₀ s₀' → ∀ k : Nat,
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ LInv enc s₀ k s₁ ∧ LInv enc s₀' k s₂) body fun _ _ => True

/-! ## One byte -/

/-- What is known between the code before the call and the call, on the
block at `D`. -/
structure Mid (s₀ : State) (k : Nat) (D : Addr) (s : State) : Prop where
  pre : CallPre s (W s₀) D (S s₀) (R s₀)
  r12 : s.gpr .r12 = Iv s₀
  r13 : s.gpr .r13 = byt s₀ k
  r14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)
  r15 : s.gpr .r15 = S s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp

/-- What is known after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  r12 : s.gpr .r12 = Iv s₀
  r13 : s.gpr .r13 = byt s₀ k
  r14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)
  r15 : s.gpr .r15 = S s₀

theorem Mid.of {s₀ : State} {k : Nat} {D : Addr} {s s₁ : State} {enc : Bool} (h : LInv enc s₀ k s)
    (pre : CallPre s₁ (W s₀) D (S s₀) (R s₀)) (saved : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r) :
    Mid s₀ k D s₁ :=
  ⟨pre, by rw [saved .r12 (by simp [calleeSaved]), h.r12], by rw [saved .r13 (by simp [calleeSaved]), h.r13],
    by rw [saved .r14 (by simp [calleeSaved]), h.r14], by rw [saved .r15 (by simp [calleeSaved]), h.r15],
    by rw [saved .rsp (by simp [calleeSaved]), h.rsp]⟩

theorem After.of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ : State} {k : Nat} {D : Addr}
    {s s' : State} (h : Mid s₀ k D s) (hc : CallPost f s (W s₀) D (S s₀) (R s₀) s') : After s₀ k s' :=
  ⟨by rw [hc.saved .r12 (by simp [calleeSaved]), h.r12], by rw [hc.saved .r13 (by simp [calleeSaved]), h.r13],
    by rw [hc.saved .r14 (by simp [calleeSaved]), h.r14], by rw [hc.saved .r15 (by simp [calleeSaved]), h.r15]⟩

/-- A body: code before the call (`pre`), the call of `b` on the block at
`D s₀ k` (public), and code after it (`post`), constant time when `pre`'s
addresses and branches depend only on the registers the invariant pins and
`post`'s on `r12` to `r15`. -/
theorem body_ct {enc : Bool} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {D : State → Nat → Addr}
    (pubD : ∀ {s₀ s₀' : State}, (cfb8X86_64 enc).pub s₀ s₀' → ∀ k, D s₀ k = D s₀' k)
    {b : Impl.Aes.X86_64.Blocks} {pre post : List Instr}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86_64 f).pre (Proof.Aes.blocksX86_64 f).pub b.code)
    (nosp : NoSp b.code) (depth : b.code.depth = 0)
    (hA : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]) (.block pre) h).isSome = true)
    (hB : ∃ h, (taint.check (Taint.ofRegs [.r12, .r13, .r14, .r15]) (.block post) h).isSome = true)
    (wpA : ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv enc s₀ k s →
      WP isa (.block pre) s (Mid s₀ k (D s₀ k)))
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (cfb8X86_64 enc).pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ LInv enc s₀ k s₁ ∧ LInv enc s₀' k s₂)
      (.seq (.block pre) (.seq (.call b.name b.code) (.block post))) fun _ _ => True := by
  obtain ⟨_, hA⟩ := hA
  obtain ⟨_, hB⟩ := hB
  have a := (RelCT.taint (A := taint)
    (P := fun s₁ s₂ => k < N s₀ ∧ LInv enc s₀ k s₁ ∧ LInv enc s₀' k s₂) _
    (fun _ _ h => Taint.agree_ofRegs (LInv.agree hq h.2.1 h.2.2)) hA).wp
    (F₁ := Mid s₀ k (D s₀ k)) (F₂ := Mid s₀' k (D s₀' k)) fun _ _ h =>
      ⟨wpA hp h.1 h.2.1, wpA hp' (by rw [← pub_N hq]; exact h.1) h.2.2⟩
  have c := (blk_rel ok ct (P := fun s₁ s₂ => Mid s₀ k (D s₀ k) s₁ ∧ Mid s₀' k (D s₀' k) s₂) fun s₁ s₂ h =>
      ⟨_, _, _, _, h.1.pre, by
        rw [pub_W hq, pub_S hq, pubD hq k, pub_R hq]; exact h.2.pre,
        by rw [h.1.rsp, h.2.rsp, pub_rsp hq]⟩).wp
    (F₁ := After s₀ k) (F₂ := After s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (blk_call ok nosp depth h.1.pre) fun _ hc => After.of h.1 hc,
       WP.mono (blk_call ok nosp depth h.2.pre) fun _ hc => After.of h.2 hc⟩
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂) _
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.r12, h.2.r12, pub_Iv hq]
      · rw [h.1.r13, h.2.r13, pub_byt hq]
      · rw [h.1.r14, h.2.r14, pub_N hq]
      · rw [h.1.r15, h.2.r15, pub_S hq]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
    (.block pre) h).isSome = true := ⟨_, by taint_decide⟩

theorem encPost_taint : ∃ h, (taint.check (Taint.ofRegs [.r12, .r13, .r14, .r15])
    (.block encPost) h).isSome = true := ⟨_, by taint_decide⟩

theorem decPost_taint : ∃ h, (taint.check (Taint.ofRegs [.r12, .r13, .r14, .r15])
    (.block decPost) h).isSome = true := ⟨_, by taint_decide⟩

/-- What the code before the call leaves. -/
theorem pre_mid {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv enc s₀ k s) :
    WP isa (.block pre) s (Mid s₀ k (Sv s₀)) := by
  have hR := h.regs hp
  have hW := h.wrs hp
  obtain ⟨s₁, run₁, g₁, mem₁, rd₁, wr₁⟩ :=
    AesCbc.X86_64.copy_ok s (dst := .r15) (src := .r12) (d := cOff) (e := 0) (P := Sv s₀) (Q := Iv s₀)
      (by rw [h.r15]; rfl) (by rw [h.r15]; exact AesCbc.X86_64.sv8 _)
      (by rw [h.r12]; simp) (by rw [h.r12])
      (by rw [hR]; exact AesCbc.X86_64.in_rw (by simp) AesCbc.X86_64.cIv0)
      (by rw [hR]; exact AesCbc.X86_64.in_rw (by simp) AesCbc.X86_64.cIv8)
      (by rw [hW]; exact AesCbc.X86_64.in_rw (by simp) AesCbc.X86_64.cSv0)
      (by rw [hW]; exact AesCbc.X86_64.in_rw (by simp) AesCbc.X86_64.cSv8)
      (by decide) (by decide)
  obtain ⟨s₂, run₂, rdi₂, rsi₂, rdx₂, rcx₂, r8₂, cs₂, mem₂, rd₂, wr₂⟩ := args_ok s₁
  have keep (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s.gpr r := by
    rw [cs₂ r hr, g₁ r (AesCbc.X86_64.calleeSaved_ne_rax hr)]
  rw [pre_eq, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, Mid.of h ?_ keep⟩⟩
  exact hp.callPre (by rw [rdi₂, g₁ _ (by decide), h.rbx]) (by rw [rsi₂, g₁ _ (by decide), h.rbp])
    (by rw [rdx₂, g₁ _ (by decide), h.r15]) rcx₂ (by rw [r8₂, g₁ _ (by decide), h.r15])
    (by rw [keep .rsp (by simp [calleeSaved]), h.rsp]) (by rw [rd₂, rd₁, h.rd]) (by rw [wr₂, wr₁, h.wr])

theorem pub_Sv {enc : Bool} {s₀ s₀' : State} (hq : (cfb8X86_64 enc).pub s₀ s₀') : Sv s₀ = Sv s₀' := by
  rw [Sv, Sv, pub_S hq]

theorem encBody_ct (v : BlocksImpl) : BodyCt true (body v.enc encPost) :=
  fun hp hp' hq k => body_ct (D := fun s₀ _ => Sv s₀) (fun hq _ => pub_Sv hq) v.encOk v.encCt v.encNosp
    v.encDepth pre_taint encPost_taint (@fun _ hp _ _ _ h => pre_mid hp h) hp hp' hq k

theorem decBody_ct (v : BlocksImpl) : BodyCt false (body v.enc decPost) :=
  fun hp hp' hq k => body_ct (D := fun s₀ _ => Sv s₀) (fun hq _ => pub_Sv hq) v.encOk v.encCt v.encNosp
    v.encDepth pre_taint decPost_taint (@fun _ hp _ _ _ h => pre_mid hp h) hp hp' hq k

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (enc : Bool) (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ LInv enc s₀ k s₁ ∧ LInv enc s₀' k s₂

theorem loop_ct {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) (hc : BodyCt enc body)
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (cfb8X86_64 enc).pub s₀ s₀') (n : Nat) :
    RelCT isa (LRel enc s₀ s₀' n) (.loop body .ne)
      fun s₁ s₂ => LInv enc s₀ (N s₀) s₁ ∧ LInv enc s₀' (N s₀') s₂ := by
  refine RelCT.loop (M := isa) (LRel enc s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel enc s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have ct := (hc hp hp' hq k).wp
    (F₁ := fun (s' : State) => LInv enc s₀ (k + 1) s' ∧ s'.zf = some (decide (N s₀ - (k + 1) = 0)))
    (F₂ := fun (s' : State) => LInv enc s₀' (k + 1) s' ∧ s'.zf = some (decide (N s₀' - (k + 1) = 0)))
    fun _ _ h => ⟨hb hp h.1 h.2.1, hb hp' (by rw [← hN]; exact h.1) h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, ⟨l₁, z₁⟩, ⟨l₂, z₂⟩⟩ => ?_
  rw [← hN] at z₂
  have e₁ : isa.eval .ne s₁ = some (!decide (N s₀ - (k + 1) = 0)) := by
    show s₁.zf.map _ = _; rw [z₁]; rfl
  have e₂ : isa.eval .ne s₂ = some (!decide (N s₀ - (k + 1) = 0)) := by
    show s₂.zf.map _ = _; rw [z₂]; rfl
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : N s₀ = k + 1 := by
      have : N s₀ - (k + 1) = 0 := by simpa using hf
      omega_using [hk, this]
    exact ⟨h0 ▸ l₁, by rw [← hN, h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N s₀ - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [h0], l₁, l₂⟩

/-! ## The whole function -/

theorem whole_rel {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) (hc : BodyCt enc body)
    {s₀ s₀' : State} (h0 : (cfb8X86_64 enc).pre s₀) (h0' : (cfb8X86_64 enc).pre s₀')
    (hq : (cfb8X86_64 enc).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (whole body) fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  have hN := pub_N hq
  obtain ⟨_, hpro⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
      (.block (save ++ setup)) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hepi⟩ : ∃ h, (taint.check (Taint.ofRegs [.r15]) (.block restore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hnil⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have pro := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hpro).wp
    (F₁ := fun (s : State) => LInv enc s₀ 0 s ∧ s.zf = some (decide (N s₀ = 0)))
    (F₂ := fun (s : State) => LInv enc s₀' 0 s ∧ s.zf = some (decide (N s₀' = 0)))
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨prologue_wp hp, prologue_wp hp'⟩
  have nil := RelCT.taint (A := taint)
    (P := fun a b => ((LInv enc s₀ 0 a ∧ a.zf = some (decide (N s₀ = 0))) ∧
      (LInv enc s₀' 0 b ∧ b.zf = some (decide (N s₀' = 0)))) ∧ isa.eval .e a = some true) _
    (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) hnil
  have mid : RelCT isa (fun a b => (LInv enc s₀ 0 a ∧ a.zf = some (decide (N s₀ = 0))) ∧
      (LInv enc s₀' 0 b ∧ b.zf = some (decide (N s₀' = 0))))
      (.ite .e (.block []) (.loop body .ne))
      (fun a b => LInv enc s₀ (N s₀) a ∧ LInv enc s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => ?_) ?_ ?_
    · show a.zf = b.zf; rw [h.1.2, h.2.2, hN]
    · refine (nil.wp (F₁ := LInv enc s₀ (N s₀)) (F₂ := LInv enc s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2.1)⟩
    · refine (loop_ct hb hc hp hp' hq (N s₀ - 0)).mono (fun a b h => ⟨0, rfl, ?_, h.1.1.1, h.1.2.1⟩)
        fun _ _ h => h
      have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this
      have : N s₀ ≠ 0 := by simpa using this
      omega_using [this]
  have epi := RelCT.taint (A := taint) (P := fun a b => LInv enc s₀ (N s₀) a ∧ LInv enc s₀' (N s₀') b) _
    (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.r15, h.2.r15, pub_S hq]) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h.2).seq (mid.seq epi)

theorem whole_ct {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) (hc : BodyCt enc body) :
    ConstantTime isa (cfb8X86_64 enc).pre (cfb8X86_64 enc).pub (whole body) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (whole_rel hb hc h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCfb8.X86_64

end

end

/-!
# AES-CFB8 on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), AES-CBC's state satisfying the precondition, and the shared
contracts of `Spec/Cfb8/Contract.lean` (with 8 bytes of stack, for the
return address of the call of the block function).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.X86_64

open VG VG.X86_64 VG.Impl.AesCfb8.X86_64
open VG.Impl.AesCbc.X86_64 (whole)
open VG.Proof.AesCbc.X86_64 (sat)
open VG.Proof.Aes.X86_64 (BlocksImpl)

theorem encrypt_mx (v : BlocksImpl) : (encrypt v.enc).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [encrypt, whole, body, Code.allInstrs, v.encMxcsr]; decide +kernel

theorem decrypt_mx (v : BlocksImpl) : (decrypt v.enc).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [decrypt, whole, body, Code.allInstrs, v.encMxcsr]; decide +kernel

theorem encrypt_spSafe (v : BlocksImpl) : (encrypt v.enc).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [encrypt, whole, body, Code.all, v.encSpSafe]; decide +kernel

theorem decrypt_spSafe (v : BlocksImpl) : (decrypt v.enc).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [decrypt, whole, body, Code.all, v.encSpSafe]; decide +kernel

theorem encrypt_correct (v : BlocksImpl) (s : State) (hs : (cfb8X86_64 true).pre s) :
    ∃ t s', Exec isa (encrypt v.enc) s t s' ∧ abiPreserved s s' ∧ (cfb8X86_64 true).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := whole_wp (encBody_ok v) hs
  exact ⟨t, s', he, abiPreserved_of_exec (encrypt_mx v) he hg, hp⟩

theorem decrypt_correct (v : BlocksImpl) (s : State) (hs : (cfb8X86_64 false).pre s) :
    ∃ t s', Exec isa (decrypt v.enc) s t s' ∧ abiPreserved s s' ∧ (cfb8X86_64 false).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := whole_wp (decBody_ok v) hs
  exact ⟨t, s', he, abiPreserved_of_exec (decrypt_mx v) he hg, hp⟩

theorem encrypt_verified (v : BlocksImpl) :
    Verified X86_64.target (encrypt v.enc) (Proof.AesCfb8.encryptRoundsContract X86_64.abi 8) :=
  Verified.of_correct (encrypt_correct v) (whole_ct (encBody_ok v) (encBody_ct v)) (by
    sig_implies [Proof.AesCfb8.encryptRoundsContract, Spec.Cfb8.aesSig, cfb8X86_64, cfb8, cts, inK, X86_64.abi,
      X86_64.argRegs] [sat] using sat)

theorem decrypt_verified (v : BlocksImpl) :
    Verified X86_64.target (decrypt v.enc) (Proof.AesCfb8.decryptRoundsContract X86_64.abi 8) :=
  Verified.of_correct (decrypt_correct v) (whole_ct (decBody_ok v) (decBody_ct v)) (by
    sig_implies [Proof.AesCfb8.decryptRoundsContract, Spec.Cfb8.aesSig, cfb8X86_64, cfb8, cts, inK, X86_64.abi,
      X86_64.argRegs] [sat] using sat)

end VG.Proof.AesCfb8.X86_64
