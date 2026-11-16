module

public import VerifiedGarbage.Impl.AesCfb8.Arm
public import VerifiedGarbage.Proof.AesCfb8.Mem
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.AesCbc.Arm.Body
public import VerifiedGarbage.Proof.AesCbc.Arm.Loop
public import VerifiedGarbage.Proof.AesCfb8.Spec
import VerifiedGarbage.Proof.CmacAes.Arm.UpdateCorrect
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `AesCfb8.Arm.Steps`, which only this module used -/

section

/-!
# AES-CFB8 on ARMv7: the code after the call

The straight-line pieces after a call, run once each: the data byte XORed
with the first byte of the enciphered block (`encByte`, `decByte`), and the
input block shifted (`shift`), with their memories as explicit writes
(`shiftMem32`, `Proof/AesCfb8/Mem.lean`).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCfb8.Arm
open VG.Impl.AesCbc.Arm (cOff)

/-- The byte instructions of `encPost`. -/
def encByte : List Instr :=
  [.ldrb .r12 .r7 0, .ldrb .lr .r10 cOff, .dp .eor .r12 .r12 (.reg .lr), .strb .r12 .r7 0]

/-- The byte instructions of `decPost`. -/
def decByte : List Instr :=
  [.ldrb .r12 .r7 0, .ldrb .lr .r10 cOff, .dp .eor .lr .lr (.reg .r12), .strb .lr .r7 0]

theorem encPost_eq : encPost = encByte ++ (shift ++ Impl.AesCfb8.Arm.advance) := rfl

theorem decPost_eq : decPost = decByte ++ (shift ++ Impl.AesCfb8.Arm.advance) := rfl

theorem low_xor (a b : Byte) : (a.setWidth 32 ^^^ b.setWidth 32).setWidth 8 = a ^^^ b := by
  ext i hi; simp

theorem encByte_ok (s : State) {P T : Addr} (hp : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = P)
    (ht : State.addr (s.gpr .r10 + BitVec.ofNat 32 2048) = T)
    (rP : InRegions (s.rd ++ s.wr) P 1) (rT : InRegions (s.rd ++ s.wr) T 1) (wP : InRegions s.wr P 1) :
    ∃ s', runBlock isa encByte s = some s' ∧ s'.gpr .r12 = (s.mem P ^^^ s.mem T).setWidth 32 ∧
      (∀ r, r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW P (s.mem P ^^^ s.mem T) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, encByte, cOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      Op2.eval, State.load8, State.store8, Option.map_some, Nat.reduceLT,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, hp, ht, rP, rT, wP]
    rfl, ?_⟩
  refine ⟨by simp [gpr_setReg], fun r h₁ h₂ => by simp [gpr_setReg, h₁, h₂], rfl, ?_, rfl, rfl⟩
  simp only [low_xor]

theorem decByte_ok (s : State) {P T : Addr} (hp : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = P)
    (ht : State.addr (s.gpr .r10 + BitVec.ofNat 32 2048) = T)
    (rP : InRegions (s.rd ++ s.wr) P 1) (rT : InRegions (s.rd ++ s.wr) T 1) (wP : InRegions s.wr P 1) :
    ∃ s', runBlock isa decByte s = some s' ∧ s'.gpr .r12 = (s.mem P).setWidth 32 ∧
      (∀ r, r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW P (s.mem T ^^^ s.mem P) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, decByte, cOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      Op2.eval, State.load8, State.store8, Option.map_some, Nat.reduceLT,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, hp, ht, rP, rT, wP]
    rfl, ?_⟩
  refine ⟨by simp [gpr_setReg], fun r h₁ h₂ => by simp [gpr_setReg, h₁, h₂], rfl, ?_, rfl, rfl⟩
  simp only [low_xor]

theorem shift_ok (s : State) {Q : Addr} {c : Byte} (hq : State.addr (s.gpr .r6) = Q)
    (hfit : (s.gpr .r6).toNat + 16 ≤ 2 ^ 32) (hc : s.gpr .r12 = c.setWidth 32)
    (hr : ∀ d n, d + n ≤ 16 → InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 d) n)
    (hw : ∀ d n, d + n ≤ 16 → InRegions s.wr (Q + BitVec.ofNat 64 d) n) :
    ∃ s', runBlock isa shift s = some s' ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = AesCfb8.shiftMem32 s.mem Q c ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a (d : Nat) (hd : d < 16) : State.addr (s.gpr .r6 + BitVec.ofNat 32 d) = Q + BitVec.ofNat 64 d := by
    rw [addr_add (by omega_using [hfit, hd]), hq]
  obtain a0 : State.addr (s.gpr .r6 + BitVec.ofNat 32 0) = Q := by rw [a 0 (by decide)]; simp
  obtain w0 : InRegions s.wr Q 4 := by simpa using hw 0 4 (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, shift, runBlock_cons, runStep_some, runBlock_nil, exec,
      State.load32, State.store32, State.store8, Option.map_some, Nat.reduceLT,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, a0, a 1 (by decide), a 5 (by decide),
      a 9 (by decide), a 12 (by decide), a 4 (by decide), a 8 (by decide), a 11 (by decide), a 15 (by decide),
      hr 1 4 (by decide), hr 5 4 (by decide), hr 9 4 (by decide), hr 12 4 (by decide), w0,
      hw 4 4 (by decide), hw 8 4 (by decide), hw 11 4 (by decide), hw 15 1 (by decide)]
    rfl, ?_⟩
  refine ⟨fun r h₁ h₂ h₃ h₄ => by simp [gpr_setReg, h₁, h₂, h₃, h₄], rfl, ?_, rfl, rfl⟩
  simp only [hc, AesCfb8.shiftMem32]
  congr 1
  ext i hi; simp

end VG.Proof.AesCfb8.Arm

end

end

/-! ### `AesCfb8.Arm.Loop`, which only this module used -/

section

/-!
# AES-CFB8 on ARMv7: the contracts, and the loop

The artifacts' contracts are the shared ones of `Spec/Cfb8/Contract.lean`,
which imply these (`Verified.lean`): `cfb8Arm enc`, for encryption
(`enc = true`) and decryption. The functions have AES-CBC's arguments, with
`len` counting bytes, and its prologue and epilogue
(`Proof/AesCbc/Arm/Loop.lean`), whose stride-free definitions this reuses.

The invariant after `k` bytes (`LInv`): the registers hold the arguments
(`r7` the next byte, `r8` the bytes left), `r11` and the stack pointer are
unchanged, only the input block, the data, the first 2064 bytes of the
scratch buffer and the 8 bytes below the stack pointer have changed since
the registers were saved, the first `k` bytes are CFB8's of the first `k`
bytes on entry and the rest are unchanged, and the input block is the one
after them.

`whole_wp`: if one run of `body` takes the invariant from `k` to `k + 1`
bytes and sets Z when none are left (`BodyOk`), `whole body` meets the
contract.
-/

@[expose] public section

namespace VG.Proof.AesCfb8.Arm

open VG VG.Arm VG.Impl.AesCbc.Arm
open VG.Impl.CmacAes.Arm (save setup restore saved mov)
open VG.Proof.CmacAes.Arm (W R Dp N S schR scrR argsR belowR savedMem savedMem_frame savedMem_slot
  saved_bound saved_ne_r12 saved_eq add0)
open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg wp_mov wp_cmp wp_ldrSp cmp0 eval_eq eval_ne)
open VG.Proof.AesCbc.Arm (Iv ivR iv0 wK)
open VG.Spec.Aes (bytesAt)

/-- `vg_aes_cfb8_encrypt` (`enc`) or `vg_aes_cfb8_decrypt`
`(schedule = r0, rounds = r1, iv = r2, data = r3, len = [sp], scratch = [sp + 4])`. -/
def cfb8Arm (enc : Bool) : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 240⟩
    let iv : Region := ⟨State.addr (s.gpr .r2), 16⟩
    let data : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 1), 2176⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let below : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩
    s.rd = [sched, args] ∧ s.wr = [iv, data, scr] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ iv.Disjoint data ∧ iv.Disjoint scr ∧
      data.Disjoint scr ∧ iv.Disjoint args ∧ data.Disjoint args ∧ scr.Disjoint args ∧
      below.Disjoint sched ∧ below.Disjoint iv ∧ below.Disjoint data ∧ below.Disjoint scr ∧
      (s.gpr .r0).toNat + 240 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 16 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 2176 ≤ 2 ^ 32 ∧
      8 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    let ciph := Spec.Cbc.aesWith (s.gpr .r1).toNat
      (bytesAt s.mem (State.addr (s.gpr .r0)) (16 * ((s.gpr .r1).toNat + 1)))
    let iv := bytesAt s.mem (State.addr (s.gpr .r2)) 16
    let xs := bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat
    bytesAt s'.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat = cfb8 enc ciph iv xs ∧
      bytesAt s'.mem (State.addr (s.gpr .r2)) 16 = inK enc ciph iv xs
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

section
variable (s₀ : State)

abbrev dataR : Region := ⟨State.addr (Dp s₀), N s₀⟩

/-- The cipher. -/
abbrev ciph : Spec.Cbc.Cipher := Spec.Cbc.aesWith (R s₀) (wK s₀)

/-- The bytes on entry. -/
abbrev bs : List Byte := bytesAt s₀.mem (State.addr (Dp s₀)) (N s₀)

/-- The address of byte `k`. -/
abbrev byt (k : Nat) : Addr := State.addr (Dp s₀) + BitVec.ofNat 64 k

/-- The byte `r7` points at, as a 32-bit address. -/
abbrev D32 (k : Nat) : BitVec 32 := Dp s₀ + BitVec.ofNat 32 k

/-- The first `k` bytes after CFB8. -/
abbrev outK (enc : Bool) (k : Nat) : List Byte := cfb8 enc (ciph s₀) (iv0 s₀) ((bs s₀).take k)

/-- The input block after the first `k` bytes. -/
abbrev inKk (enc : Bool) (k : Nat) : List Byte := inK enc (ciph s₀) (iv0 s₀) ((bs s₀).take k)

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀, argsR s₀]
  wr : s₀.wr = [ivR s₀, dataR s₀, scrR s₀]
  sch_iv : (schR s₀).Disjoint (ivR s₀)
  sch_data : (schR s₀).Disjoint (dataR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  iv_data : (ivR s₀).Disjoint (dataR s₀)
  iv_scr : (ivR s₀).Disjoint (scrR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  iv_args : (ivR s₀).Disjoint (argsR s₀)
  data_args : (dataR s₀).Disjoint (argsR s₀)
  scr_args : (scrR s₀).Disjoint (argsR s₀)
  b_sch : (belowR s₀).Disjoint (schR s₀)
  b_iv : (belowR s₀).Disjoint (ivR s₀)
  b_data : (belowR s₀).Disjoint (dataR s₀)
  b_scr : (belowR s₀).Disjoint (scrR s₀)
  sch_fit : (W s₀).toNat + 240 ≤ 2 ^ 32
  iv_fit : (Iv s₀).toNat + 16 ≤ 2 ^ 32
  data_fit : (Dp s₀).toNat + N s₀ ≤ 2 ^ 32
  scr_fit : (S s₀).toNat + 2176 ≤ 2 ^ 32
  sp8 : 8 ≤ s₀.sp.toNat
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {enc : Bool} {s₀ : State} (h : (cfb8Arm enc).pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w⟩

/-- The loop invariant, after `k` bytes. -/
structure LInv (enc : Bool) (s₀ : State) (k : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = W s₀
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = Iv s₀
  r7 : s.gpr .r7 = D32 s₀ k
  r8 : s.gpr .r8 = BitVec.ofNat 32 (N s₀ - k)
  r10 : s.gpr .r10 = S s₀
  r11 : s.gpr .r11 = s₀.gpr .r11
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) s.mem
  data : bytesAt s.mem (State.addr (Dp s₀)) (N s₀) = outK s₀ enc k ++ (bs s₀).drop k
  iv : bytesAt s.mem (State.addr (Iv s₀)) 16 = inKk s₀ enc k

/-! ## Addresses and regions -/

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.scrA {d : Nat} (hd : d < 2176) :
    State.addr (S s₀ + BitVec.ofNat 32 d) = State.addr (S s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := hp.scr_fit; have := (S s₀).isLt; omega_arith)

theorem UPre.dataA {k : Nat} (hk : k < N s₀) : State.addr (D32 s₀ k) = byt s₀ k :=
  addr_add (by have := hp.data_fit; have := (Dp s₀).isLt; omega_arith)

theorem UPre.arg1 : stackArgAddr s₀ 1 = stackArgAddr s₀ 0 + BitVec.ofNat 64 4 := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_add (by omega_using [this]), addr_add (by omega_using [])]
  simp

theorem UPre.arg_in {k : Nat} (hk : k < 2) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 := by
  refine ⟨argsR s₀, by simp [hp.rd], ?_⟩
  rcases (by omega_using [hk] : k = 0 ∨ k = 1) with rfl | rfl
  · simpa using Offset.contains_base (stackArgAddr s₀ 0) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  · rw [hp.arg1]; exact Offset.contains_base _ (by decide) (by decide)

theorem UPre.byt_disjoint {j k : Nat} (hj : j < N s₀) (hk : k < N s₀) (hjk : j ≠ k) :
    (⟨byt s₀ j, 1⟩ : Region).Disjoint ⟨byt s₀ k, 1⟩ := by
  have := hp.data_fit
  exact Offset.disjoint _ (by omega_using [hjk]) (by omega_using [hj, this]) (by omega_using [hk, this])

end

theorem UPre.scr_sub {s₀ : State} {d n : Nat} (h : d + n ≤ 2176) :
    Region.Sub ⟨State.addr (S s₀) + BitVec.ofNat 64 d, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {s₀ : State} {k : Nat} (hk : k < N s₀) : Region.Sub ⟨byt s₀ k, 1⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega_using [hk])

theorem UPre.arg_sub {s₀ : State} : Region.Sub ⟨stackArgAddr s₀ 0, 4⟩ (argsR s₀) :=
  Region.sub_prefix (by decide)

/-- The regions the function writes, with the stack below it. -/
abbrev Big (s₀ : State) : List Region := [ivR s₀, dataR s₀, scrR s₀, belowR s₀]

theorem UPre.big_of {s₀ : State} {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) m) :
    Frame (Big s₀) s₀.mem m := by
  obtain f₀ : Frame (Big s₀) s₀.mem (savedMem s₀) :=
    (savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
  exact f₀.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨belowR s₀, by simp, fun _ h => h⟩)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    bytesAt m (State.addr (W s₀)) (16 * (R s₀ + 1)) = bytesAt s₀.mem (State.addr (W s₀)) (16 * (R s₀ + 1)) := by
  obtain hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega_using [hR])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.sch_iv.sub_left (Region.sub_prefix hR)
  · exact hp.sch_data.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.b_sch.symm.sub_left (Region.sub_prefix hR)

/-- The bytes after a step that changed only byte `k`, the input block, the
first 2064 bytes of the scratch buffer and the stack. -/
theorem UPre.bytes_step {m m' : Mem} {k : Nat} (hk : k < N s₀)
    (hf : Frame [⟨byt s₀ k, 1⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] m m') :
    bytesAt m' (State.addr (Dp s₀)) (N s₀) = (bytesAt m (State.addr (Dp s₀)) (N s₀)).set k (m' (byt s₀ k)) := by
  refine bytesAt_set fun j hj hjk => ?_
  have e := Proof.Cmac.bytesAt_frame (p := byt s₀ j) (n := 1) hf (fun r hr => ?_) (by decide)
  · simpa [bytesAt] using e
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.byt_disjoint hj hk hjk
  · exact hp.iv_data.symm.sub_left (UPre.data_sub hj)
  · exact (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right (Region.sub_prefix (by decide))
  · exact hp.b_data.symm.sub_left (UPre.data_sub hj)

end

theorem length_bs (s₀ : State) : (bs s₀).length = N s₀ := by simp [bytesAt]

/-- Byte `k` before the step, from the invariant. -/
theorem LInv.byte {enc : Bool} {s₀ : State} {k : Nat} {s : State} (h : LInv enc s₀ k s) (hk : k < N s₀) :
    s.mem (byt s₀ k) = (bs s₀)[k]'(by rw [length_bs]; exact hk) := by
  obtain hl : (outK s₀ enc k).length = k := by
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

/-! ## The prologue -/

theorem prologue_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (save ++ setup)) s₀ fun s => LInv enc s₀ 0 s ∧ s.z = decide (N s₀ = 0) := by
  have hsc := hp.scr_fit
  rw [show save ++ setup = .ldrSp .r12 4 :: (saved.map (fun p => Instr.str p.1 .r12 p.2) ++ setup) from rfl]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (hp.arg_in (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = S s₀ := u₁.gpr
  refine Spill.saveList_ok saved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have hb := saved_bound p hp'
    rw [h12, u₁.wr, hp.wr]
    exact ⟨by omega_using [hb], by omega_using [hsc, hb], ⟨scrR s₀, by simp, Offset.contains_base _ (by omega_using [hb]) (by omega_using [hb])⟩⟩
  obtain hm₂ : s₂.mem = savedMem s₀ := by
    rw [m₂, u₁.mem, h12, savedMem]
    exact Spill.saveMem_congr _ _ _ fun p hp' => u₁.other _ (saved_ne_r12 p hp')
  obtain harg : s₂.mem.readW (stackArgAddr s₀ 0) 32 = stackArg s₀ 0 := by
    rw [hm₂]
    exact (savedMem_frame s₀).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.scr_args.symm.sub_left UPre.arg_sub).sub_right (Region.sub_prefix (by decide))) (by decide)
  simp only [setup, mov]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]
        exact hp.arg_in (by decide)) fun s₇ u₇ => ?_
  refine wp_mov (op2_reg _ _) fun s₈ u₈ => wp_cmp (op2_imm (by decide)) fun s₉ f₉ z₉ => WP.block_nil ?_
  obtain r8 : s₉.gpr .r8 = stackArg s₀ 0 := by
    rw [f₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.mem, u₅.mem, u₄.mem, u₃.mem, harg]
  obtain mm : s₉.mem = savedMem s₀ := by
    rw [f₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂]
  obtain a0 : stackArg s₀ 0 = BitVec.ofNat 32 (N s₀) := by simp [N]
  obtain f₀ := savedMem_frame s₀
  obtain ivS : bytesAt (savedMem s₀) (State.addr (Iv s₀)) 16 = iv0 s₀ :=
    Proof.Cmac.bytesAt_frame f₀ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))) (by decide)
  obtain dataS : bytesAt (savedMem s₀) (State.addr (Dp s₀)) (N s₀) = bs s₀ :=
    Proof.Cmac.bytesAt_frame f₀ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.data_scr.sub_right (Region.sub_prefix (by decide))) (by have := hp.data_fit; omega_using [this])
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, g₂, u₁.other]
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g₂, u₁.other]
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, g₂, u₁.other]
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, g₂, u₁.other]
    exact (BitVec.add_zero _).symm
  · rw [r8, a0]; rfl
  · simp (disch := decide) only [f₉.gpr, u₈.gpr, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂, h12]
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂,
      u₁.other]
  · rw [f₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  · rw [f₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  · rw [f₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  · rw [mm]; exact Frame.refl _ _
  · rw [mm, dataS]
    simp only [outK, List.take_zero, cfb8_nil, List.drop_zero, List.nil_append]
  · rw [mm, ivS]
    simp only [inKk, List.take_zero, inK_nil]
  · rw [z₉, show s₈.gpr .r8 = s₉.gpr .r8 from (congrFun f₉.gpr _).symm, r8, a0]
    exact cmp0 (stackArg s₀ 0).isLt

/-! ## The loop -/

/-- One run of `body` takes the invariant from `k` bytes to `k + 1`, and sets
Z if no bytes are left. -/
def BodyOk (enc : Bool) (body : Prog isa) : Prop :=
  ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv enc s₀ k s →
    WP isa body s fun s' => LInv enc s₀ (k + 1) s' ∧ s'.z = decide (N s₀ - (k + 1) = 0)

theorem loop_ok {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (hp : UPre s₀) {k : Nat}
    (hk : k < N s₀) {s : State} (h : LInv enc s₀ k s) : WP isa (.loop body .ne) s (LInv enc s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body) (c := .ne) (Q := LInv enc s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv enc s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (hb hp hk h) fun s' ⟨h', hz⟩ => ?_
  obtain ev : isa.eval .ne s' = some !decide (N s₀ - (k + 1) = 0) := by
    show VG.Arm.eval .ne s' = _; rw [eval_ne, hz]
  by_cases hz' : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [show N s₀ = k + 1 by omega_using [hk, hz']]
  · right
    refine ⟨by rw [ev]; simp [hz'], N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hz'], h'⟩

theorem mid_wp {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (hp : UPre s₀) {s₁ : State}
    (h : LInv enc s₀ 0 s₁) (hz : s₁.z = decide (N s₀ = 0)) :
    WP isa (.ite .eq (.block []) (.loop body .ne)) s₁ (LInv enc s₀ (N s₀)) := by
  obtain ev : isa.eval .eq s₁ = some (decide (N s₀ = 0)) := by
    show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz]
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hb hp (by omega_using [hn]) h

/-! ## The epilogue -/

theorem slot_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) m) {d : Nat}
    (h₁ : 2064 ≤ d) (h₂ : d + 4 ≤ 2096) :
    m.readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 =
      (savedMem s₀).readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 :=
  hf.readW (r := ⟨State.addr (S s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.iv_scr.symm.sub_left (UPre.scr_sub (by omega_using [h₂]))
    · exact hp.data_scr.symm.sub_left (UPre.scr_sub (by omega_using [h₂]))
    · exact Offset.disjoint_base _ h₁ (by have := hp.scr_fit; omega_using [h₂])
    · exact hp.b_scr.symm.sub_left (UPre.scr_sub (by omega_using [h₂]))) (by decide)

theorem epilogue_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {s : State} (h : LInv enc s₀ (N s₀) s) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ (cfb8Arm enc).post s₀ s' := by
  have hsc := hp.scr_fit
  obtain rdwr : s.rd ++ s.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  obtain inS : ∀ d, d + 4 ≤ 2176 → InRegions (s.rd ++ s.wr) (State.addr (S s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr]; exact ⟨scrR s₀, by simp, Offset.contains_base _ hd (by omega_using [hd])⟩
  obtain sl : ∀ r d, (r, d) ∈ saved → s.mem.readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
    fun r d hrd => by
      obtain hb := saved_bound _ hrd
      rw [slot_read hp h.frame hb.1 hb.2, savedMem_slot s₀ hrd]
  obtain hall : (bs s₀).take (N s₀) = bs s₀ := List.take_of_length_le (by rw [length_bs])
  obtain hnil : (bs s₀).drop (N s₀) = [] := List.drop_of_length_le (by rw [length_bs])
  rw [restore, saved_eq, ← List.append_nil (List.map _ _)]
  refine Spill.restoreBase_ok (by decide) (fun p hp' => ?_) fun s₂ ld ho m₁ _ _ sp₁ =>
    WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · have hb := saved_bound p (by rw [saved_eq]; exact hp')
    exact ⟨by omega_using [hb], by rw [h.r10]; omega_using [hsc, hb], by rw [h.r10]; exact inS _ (by omega_using [hb])⟩
  · by_cases hs : r ∈ saved.map Prod.fst
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hs
      rw [ld p (by rw [← saved_eq]; exact hp'), h.r10, sl _ _ hp']
    · have hk : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → r = .r11 := by decide
      rw [hk r hr hs, ho _ (by decide), h.r11]
  · rw [sp₁, h.sp]
  · show bytesAt s₂.mem (State.addr (Dp s₀)) (N s₀) = _
    rw [m₁, h.data]; simp only [outK, hall, hnil, List.append_nil]
  · show bytesAt s₂.mem (State.addr (Iv s₀)) 16 = _
    rw [m₁, h.iv]; simp only [inKk, hall]

theorem whole_wp {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (h0 : (cfb8Arm enc).pre s₀) :
    WP isa (whole body) s₀ fun s' => abiPreserved s₀ s' ∧ (cfb8Arm enc).post s₀ s' := by
  obtain hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, hz⟩ =>
    WP.seq (WP.mono (mid_wp hb hp h₁ hz) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.AesCfb8.Arm

end

end


/-!
# AES-CFB8 on ARMv7: one byte

`encBody_ok` and `decBody_ok`: one run of `body` takes the loop invariant
(`Loop.lean`) from `k` bytes to `k + 1` (`BodyOk`). The input block is
copied to the scratch buffer and enciphered there (`call_ok`), as AES-CBC
calls the block function (`Proof/AesCbc/Arm/Body.lean`), the data byte is
replaced, and the input block is shifted (`finish_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.Arm

open VG VG.Arm VG.Impl.AesCfb8.Arm
open VG.Impl.AesCbc.Arm (cOff encFrame zero4)
open VG.Impl.CmacAes.Arm (xor4 mov)
open VG.Proof.CmacAes.Arm (W R Dp N S schR scrR argsR belowR savedMem add0)
open VG.Proof.AesOcb.Arm (BlkCall BlkPost blk_call encF)
open VG.Proof.AesGcm.Arm (below)
open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg wp_mov wp_add wp_subs ofNat_beq_zero sub_ofNat)
open VG.Proof.AesCbc (copy4Mem copy4Mem_frame copy4Mem_bytes aesWith_state set_prefix bytesAt_of_statesAt)
open VG.Proof.AesCbc.Arm (Iv ivR iv0 wK Sv covIv covSv copy_wp Moved encFrame_eq)
open VG.Spec.Aes (bytesAt)

/-- The copy of the input block, as a 32-bit address. -/
abbrev Sv32 (s₀ : State) : BitVec 32 := S s₀ + BitVec.ofNat 32 2048

theorem headD_bytesAt (m : Mem) (p : Addr) : (bytesAt m p 16).headD 0 = m p := by
  simp [bytesAt, List.range_succ_eq_map]

/-- A byte outside a frame is unchanged. -/
theorem byte_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 1⟩ : Region).Disjoint r) : m' p = m p := by
  have := Proof.Cmac.bytesAt_frame hf hd (by decide)
  simpa [bytesAt] using this

theorem writeW8_self (m : Mem) (p : Addr) (v : Byte) : m.writeW p v p = v := by
  rw [writeW8_apply, BitVec.sub_self]; simp

theorem frame_write8 (m : Mem) (p : Addr) (v : Byte) : Frame [⟨p, 1⟩] m (m.writeW p v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sv : State.addr (Sv32 s₀) = Sv s₀ := hp.scrA (by decide)

theorem UPre.cByt {k : Nat} (hk : k < N s₀) : (dataR s₀).Contains (byt s₀ k) 1 := by
  have := hp.data_fit
  exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk, this])

theorem UPre.byt_iv {k : Nat} (hk : k < N s₀) : (⟨byt s₀ k, 1⟩ : Region).Disjoint (ivR s₀) :=
  hp.iv_data.symm.sub_left (UPre.data_sub hk)

theorem UPre.byt_sv {k : Nat} (hk : k < N s₀) :
    (⟨byt s₀ k, 1⟩ : Region).Disjoint ⟨State.addr (S s₀), 2064⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))

theorem UPre.byt_b {k : Nat} (hk : k < N s₀) : (⟨byt s₀ k, 1⟩ : Region).Disjoint (belowR s₀) :=
  (hp.b_data.sub_right (UPre.data_sub hk)).symm

theorem UPre.iv_sv : (ivR s₀).Disjoint ⟨Sv s₀, 16⟩ := hp.iv_scr.sub_right (UPre.scr_sub (by decide))

theorem UPre.sv_scr : (⟨Sv s₀, 16⟩ : Region).Disjoint ⟨State.addr (S s₀), 2048⟩ :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_fit; omega_using [])

/-- The arguments of a call on the copy of the input block, with the working
space at the start of the scratch buffer. -/
theorem UPre.blkCall {s : State}
    (r0 : s.gpr .r0 = W s₀) (r1 : s.gpr .r1 = s₀.gpr .r1) (r2 : s.gpr .r2 = Sv32 s₀) (r3 : s.gpr .r3 = 1)
    (r12 : s.gpr .r12 = S s₀) (sp : s.sp = s₀.sp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    BlkCall s (W s₀) (Sv32 s₀) (S s₀) (R s₀) 1 := by
  obtain hb : below s.sp = belowR s₀ := by rw [sp]; rfl
  have hd := hp.sv
  have hsc := hp.scr_fit
  obtain qN : (Sv32 s₀).toNat = (S s₀).toNat + 2048 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
      Nat.mod_eq_of_lt (by omega_using [hsc])]
  refine ⟨r0, by rw [r1]; simp [R], r2, by rw [r3]; rfl, r12, hp.rounds, by rw [sp]; exact hp.sp8, hp.sch_fit,
    by rw [qN]; omega_using [hsc], by omega_using [hsc], ?_, hp.sch_scr.sub_right (Region.sub_prefix (by decide)), ?_,
    by rw [hb]; exact hp.b_sch, ?_, by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩
  · rw [hd]; exact hp.sch_scr.sub_right (UPre.scr_sub (by decide))
  · rw [hd]; exact hp.sv_scr
  · rw [hb, hd]; exact hp.b_scr.sub_right (UPre.scr_sub (by decide))
  · rw [hrd, hwr, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [hwr, hp.wr, hd]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

end

/-! ## The code before the call -/

/-- What the code before the call leaves. -/
structure PreA (s₀ : State) (s s₁ : State) : Prop where
  pre : BlkCall s₁ (W s₀) (Sv32 s₀) (S s₀) (R s₀) 1
  keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₁.gpr r = s.gpr r
  sp : s₁.sp = s.sp
  mem : s₁.mem = copy4Mem s.mem (Sv s₀) (State.addr (Iv s₀))
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem pre_eq : pre = zero4 .r10 2048 ++ (xor4 .r10 .r6 .r10 2048 0 2048 ++
    ([.mov .r0 (.reg .r4), .mov .r1 (.reg .r5), .dp .add .r2 .r10 (.imm 2048), .mov .r3 (.imm 1),
      .mov .r12 (.reg .r10)] : List Instr)) := rfl

theorem pre_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv enc s₀ k s) :
    WP isa (.block pre) s (PreA s₀ s) := by
  have hsc := hp.scr_fit
  have hiv := hp.iv_fit
  obtain rw₀ : s.rd ++ s.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  obtain w₀ : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  rw [pre_eq]
  refine copy_wp (by decide) (by decide) (by decide) (by decide) (by rw [h.r6]; omega_using [hiv])
    (by rw [h.r10]; omega_using [hsc]) (by rw [h.r6, add0, rw₀]; exact covIv (by simp))
    (by rw [h.r10, w₀]; exact covSv (by simp)) fun s₁ g₁ => ?_
  obtain m₁ : s₁.mem = copy4Mem s.mem (Sv s₀) (State.addr (Iv s₀)) := by rw [g₁.mem, h.r10, h.r6, add0]
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_mov (op2_imm (by decide)) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_
  obtain keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₆.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h12 hlr => by
      rw [u₆.other _ h12, u₅.other _ h3, u₄.other _ h2, u₃.other _ h1, u₂.other _ h0, g₁.gpr _ h12 hlr]
  obtain sp₆ : s₆.sp = s.sp := by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, g₁.sp]
  obtain rd₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, g₁.rd]
  obtain wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, g₁.wr]
  obtain g10 : s₁.gpr .r10 = S s₀ := by rw [g₁.gpr _ (by decide) (by decide), h.r10]
  refine ⟨hp.blkCall ?_ ?_ ?_ ?_ ?_ (by rw [sp₆, h.sp]) (by rw [rd₆, h.rd]) (by rw [wr₆, h.wr]), keep, sp₆,
    by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁], rd₆, wr₆⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      g₁.gpr _ (by decide) (by decide), h.r4]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g₁.gpr _ (by decide) (by decide), h.r5]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      g10]; rfl
  · rw [u₆.other _ (by decide), u₅.gpr]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g10]

/-! ## The call -/

/-- What the code before the call and the call leave, for either
direction. -/
structure AfterCall (enc : Bool) (s₀ : State) (k : Nat) (s s₂ : State) : Prop where
  g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → r ≠ .r12 → r ≠ .lr → s₂.gpr r = s.gpr r
  sp : s₂.sp = s.sp
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  frame : Frame [⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem s₂.mem
  out : s₂.mem (Sv s₀) = (ciph s₀ (inKk s₀ enc k)).headD 0

theorem call_ok {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State}
    (h : LInv enc s₀ k s) (post : List Instr) {Q : State → Prop}
    (hq : ∀ s₂, AfterCall enc s₀ k s s₂ → WP isa (.block post) s₂ Q) :
    WP isa (body post) s Q := by
  refine WP.seq (WP.mono (pre_wp hp h) fun s₁ a => ?_)
  rw [encFrame_eq]
  refine WP.seq (WP.mono (blk_call encF a.pre) fun s₂ c => hq s₂ ?_)
  obtain hb : below s₁.sp = belowR s₀ := by rw [a.sp, h.sp]; rfl
  obtain svSub : Region.Sub ⟨Sv s₀, 16⟩ ⟨State.addr (S s₀), 2064⟩ := Offset.sub_base _ (by decide)
  obtain f₁ : Frame [⟨Sv s₀, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact copy4Mem_frame _ _ _
  obtain big₁ : Frame (Big s₀) s₀.mem s₁.mem := (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩)
  refine ⟨fun r h0 h1 h2 h3 h9 h12 hlr => ?_, by rw [c.sp, a.sp], by rw [c.rd, a.rd], by rw [c.wr, a.wr],
    (f₁.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_), ?_⟩
  · have : r ∈ preserved ∨ r = .r0 ∨ r = .r1 ∨ r = .r2 ∨ r = .r3 ∨ r = .r9 ∨ r = .r12 ∨ r = .lr := by
      cases r <;> simp [preserved]
    rcases this with hr | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c.saved r hr hlr, a.keep r h0 h1 h2 h3 h12 hlr]
    all_goals contradiction
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, svSub⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hp.sv]; exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, svSub⟩
    · exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, Region.sub_prefix (by decide)⟩
    · rw [hb]; exact ⟨belowR s₀, by simp, fun _ h => h⟩
  · have o := bytesAt_of_statesAt c.out
    rw [hp.sv] at o
    rw [← headD_bytesAt s₂.mem (Sv s₀), o, show encF.f = Spec.Aes.cipher from rfl, UPre.sched_bytes hp big₁,
      ← aesWith_state, a.mem, copy4Mem_bytes _ hp.iv_sv.symm, h.iv]

/-! ## After the call -/

/-- After the byte operation (`v` the new data byte, `c` the byte to shift
in, in `r12`), the shift and `advance` take the invariant to `k + 1`. -/
theorem finish_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ s₃ : State}
    (h : LInv enc s₀ k s) (a : AfterCall enc s₀ k s s₂) {v : Byte}
    (g₃ : ∀ r, r ≠ .r12 → r ≠ .lr → s₃.gpr r = s₂.gpr r) (sp₃ : s₃.sp = s₂.sp)
    (mem₃ : s₃.mem = s₂.mem.writeW (byt s₀ k) v) (rd₃ : s₃.rd = s₂.rd) (wr₃ : s₃.wr = s₂.wr)
    (hv : v = (bs s₀)[k]'(by rw [length_bs]; exact hk) ^^^ (ciph s₀ (inKk s₀ enc k)).headD 0)
    (hc : s₃.gpr .r12 = (if enc then v else (bs s₀)[k]'(by rw [length_bs]; exact hk)).setWidth 32) :
    WP isa (.block (shift ++ Impl.AesCfb8.Arm.advance)) s₃
      fun s' => LInv enc s₀ (k + 1) s' ∧ s'.z = decide (N s₀ - (k + 1) = 0) := by
  have hiv := hp.iv_fit
  have hdf := hp.data_fit
  obtain hN := (stackArg s₀ 0).isLt
  have g₃' (r : Reg) (h0 : r ≠ .r0) (h1 : r ≠ .r1) (h2 : r ≠ .r2) (h3 : r ≠ .r3) (h9 : r ≠ .r9) (h12 : r ≠ .r12)
      (hlr : r ≠ .lr) : s₃.gpr r = s.gpr r := by
    rw [g₃ r h12 hlr, a.g r h0 h1 h2 h3 h9 h12 hlr]
  obtain rl : s₃.rd ++ s₃.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rd₃, wr₃, a.rd, a.wr, h.rd, h.wr, hp.rd, hp.wr]; rfl
  obtain wl : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₃, a.wr, h.wr, hp.wr]
  obtain r6 : s₃.gpr .r6 = Iv s₀ := by
    rw [g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r6]
  obtain ⟨s₄, run₄, g₄, sp₄, mem₄, rd₄, wr₄⟩ :=
    shift_ok s₃ (Q := State.addr (Iv s₀)) (by rw [r6]) (by rw [r6]; omega_using [hiv]) hc
      (fun d n hd => by rw [rl]; exact ⟨ivR s₀, by simp, Offset.contains_base _ hd (by omega_using [hd])⟩)
      (fun d n hd => by rw [wl]; exact ⟨ivR s₀, by simp, Offset.contains_base _ hd (by omega_using [hd])⟩)
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  refine wp_add (op2_imm (by decide)) fun s₅ u₅ => wp_subs (op2_imm (by decide)) fun s₆ u₆ z₆ => WP.block_nil ?_
  have g (r : Reg) (h0 : r ≠ .r0) (h1 : r ≠ .r1) (h2 : r ≠ .r2) (h3 : r ≠ .r3) (h7 : r ≠ .r7) (h8 : r ≠ .r8)
      (h9 : r ≠ .r9) (h12 : r ≠ .r12) (hlr : r ≠ .lr) : s₆.gpr r = s.gpr r := by
    rw [u₆.other _ h8, u₅.other _ h7, g₄ r h0 h1 h2 h3, g₃' r h0 h1 h2 h3 h9 h12 hlr]
  obtain r8₅ : s₅.gpr .r8 = BitVec.ofNat 32 (N s₀ - k) := by
    rw [u₅.other _ (by decide), g₄ _ (by decide) (by decide) (by decide) (by decide),
      g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r8]
  obtain dec : BitVec.ofNat 32 (N s₀ - k) - 1 = BitVec.ofNat 32 (N s₀ - (k + 1)) := by
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_using [hk])]; rfl
  obtain mem₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  -- Memory.
  obtain fStep : Frame [⟨byt s₀ k, 1⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem s₆.mem := by
    rw [mem₆, mem₄, mem₃]
    refine (a.frame.sub fun r hr => ?_).trans
      (((frame_write8 _ _ _).sub fun r hr => ?_).trans ((AesCfb8.shiftMem32_frame _ _ _).sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨belowR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have one (r : Region) (P : Addr) (n : Nat) (hd : (⟨P, n⟩ : Region).Disjoint r) :
      ∀ r' ∈ [r], (⟨P, n⟩ : Region).Disjoint r' := fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hd
  obtain newByte : s₆.mem (byt s₀ k) = v := by
    rw [mem₆, mem₄, byte_frame (AesCfb8.shiftMem32_frame _ _ _) (one _ _ _ (hp.byt_iv hk)), mem₃, writeW8_self]
  obtain ivIn : bytesAt s₃.mem (State.addr (Iv s₀)) 16 = inKk s₀ enc k := by
    rw [mem₃, Proof.Cmac.bytesAt_frame (frame_write8 _ _ _) (one _ _ _ (hp.byt_iv hk).symm) (by decide),
      Proof.Cmac.bytesAt_frame a.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
        · exact hp.b_iv.symm) (by decide), h.iv]
  obtain hl : (outK s₀ enc k).length = k := by
    rw [outK, length_cfb8, List.length_take, length_bs]; omega_using [hk]
  obtain iv_ne : iv0 s₀ ≠ [] := by simp [iv0, bytesAt]
  refine ⟨⟨?_, ?_, ?_, ?_, by rw [u₆.gpr, r8₅, dec], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r4]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r5]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r6]
  · rw [u₆.other _ (by decide), u₅.gpr, g₄ _ (by decide) (by decide) (by decide) (by decide),
      g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r7,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add_eq _ (c := k + 1) (by omega_using [])]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r10]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r11]
  · rw [u₆.sp, u₅.sp, sp₄, sp₃, a.sp, h.sp]
  · rw [u₆.rd, u₅.rd, rd₄, rd₃, a.rd, h.rd]
  · rw [u₆.wr, u₅.wr, wr₄, wr₃, a.wr, h.wr]
  · exact h.frame.trans (fStep.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, fun _ h => h⟩
      · exact ⟨belowR s₀, by simp, fun _ h => h⟩)
  · rw [hp.bytes_step hk fStep, h.data, newByte, set_prefix _ _ _ hl (by rw [length_bs]; exact hk), hv]
    simp only [outK, take_succ_bs s₀ hk, cfb8_snoc enc _ iv_ne, inKk]
  · rw [mem₆, mem₄, AesCfb8.shiftMem32_bytes, ivIn]
    simp only [inKk, take_succ_bs s₀ hk, inK_snoc enc _ iv_ne, ← hv]
  · rw [z₆, r8₅, dec]; exact ofNat_beq_zero (by omega_using [hdf])

/-! ## One byte -/

/-- The data byte after the call. -/
theorem AfterCall.byte {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ : State}
    (h : LInv enc s₀ k s) (a : AfterCall enc s₀ k s s₂) :
    s₂.mem (byt s₀ k) = (bs s₀)[k]'(by rw [length_bs]; exact hk) := by
  rw [byte_frame a.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.byt_sv hk
    · exact hp.byt_b hk), h.byte hk]

/-- The registers and regions the byte operation needs. -/
theorem AfterCall.args {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ : State}
    (h : LInv enc s₀ k s) (a : AfterCall enc s₀ k s s₂) :
    State.addr (s₂.gpr .r7 + BitVec.ofNat 32 0) = byt s₀ k ∧
      State.addr (s₂.gpr .r10 + BitVec.ofNat 32 2048) = Sv s₀ ∧
      InRegions (s₂.rd ++ s₂.wr) (byt s₀ k) 1 ∧ InRegions (s₂.rd ++ s₂.wr) (Sv s₀) 1 ∧
      InRegions s₂.wr (byt s₀ k) 1 := by
  obtain rl : s₂.rd ++ s₂.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [a.rd, a.wr, h.rd, h.wr, hp.rd, hp.wr]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [a.g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r7]; simp only [BitVec.add_zero]
    exact hp.dataA hk
  · rw [a.g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r10]
    exact hp.sv
  · rw [rl]; exact ⟨dataR s₀, by simp, hp.cByt hk⟩
  · rw [rl]; exact ⟨scrR s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  · rw [a.wr, h.wr, hp.wr]; exact ⟨dataR s₀, by simp, hp.cByt hk⟩

theorem encBody_ok : BodyOk true (body encPost) := by
  intro s₀ hp k hk s h
  refine call_ok hp h encPost fun s₂ a => ?_
  obtain ⟨eP, eT, rP, rT, wP⟩ := a.args hp hk h
  obtain ⟨s₃, run₃, r12₃, g₃, sp₃, mem₃, rd₃, wr₃⟩ := encByte_ok s₂ eP eT rP rT wP
  rw [encPost_eq, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, finish_wp hp hk h a g₃ sp₃ mem₃ rd₃ wr₃
    (by rw [a.byte hp hk h, a.out]) ?_⟩
  rw [r12₃]; rfl

theorem decBody_ok : BodyOk false (body decPost) := by
  intro s₀ hp k hk s h
  refine call_ok hp h decPost fun s₂ a => ?_
  obtain ⟨eP, eT, rP, rT, wP⟩ := a.args hp hk h
  obtain ⟨s₃, run₃, r12₃, g₃, sp₃, mem₃, rd₃, wr₃⟩ := decByte_ok s₂ eP eT rP rT wP
  rw [decPost_eq, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, finish_wp hp hk h a g₃ sp₃ mem₃ rd₃ wr₃
    (by rw [a.byte hp hk h, a.out, BitVec.xor_comm]) ?_⟩
  rw [r12₃, a.byte hp hk h]; rfl

end VG.Proof.AesCfb8.Arm
