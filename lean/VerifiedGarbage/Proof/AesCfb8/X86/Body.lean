module

public import VerifiedGarbage.Impl.AesCfb8.X86
public import VerifiedGarbage.Proof.AesCfb8.Mem
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.CmacAes.X86.Save
public import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesCbc.X86.Body
public import VerifiedGarbage.Proof.AesCfb8.Spec
import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.MdStream.X86.Common

/-! ### `AesCfb8.X86.Steps`, which only this module used -/

section

/-!
# AES-CFB8 on x86: the code after the call

The straight-line pieces after a call, run once each: the data byte XORed
with the first byte of the enciphered block (`encByte`, `decByte`), and the
input block shifted (`shift`), with their memories as explicit writes
(`shiftMem32`, `Proof/AesCfb8/Mem.lean`).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCfb8.X86
open VG.Impl.AesCbc.X86 (cOff)
open VG.Impl.CmacAes.X86 (argOp at_)
open VG.Proof.CmacAes.X86 (ea_at')

/-- The byte instructions of `encPost`. -/
def encByte : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .movzx8 .ecx (at_ .ebp cOff), .alu .xor .eax (.reg .ecx), .store8 (at_ .esi 0) .al]

/-- The byte instructions of `decPost`. -/
def decByte : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .movzx8 .ecx (at_ .ebp cOff), .alu .xor .ecx (.reg .eax), .store8 (at_ .esi 0) .cl]

theorem encPost_eq : encPost = .mov .ebp (argOp 5) :: (encByte ++ (.mov .ebx (argOp 2) ::
    (shift ++ Impl.AesCfb8.X86.advance))) := rfl

theorem decPost_eq : decPost = .mov .ebp (argOp 5) :: (decByte ++ (.mov .ebx (argOp 2) ::
    (shift ++ Impl.AesCfb8.X86.advance))) := rfl

theorem low_xor (a b : Byte) : (a.setWidth 32 ^^^ b.setWidth 32).setWidth 8 = a ^^^ b := by
  ext i hi; simp

theorem encByte_ok (s : State) {P T : Addr} (hp : addr (s.gpr .esi) 0 = P) (ht : addr (s.gpr .ebp) 2048 = T)
    (rP : InRegions (s.rd ++ s.wr) P 1) (rT : InRegions (s.rd ++ s.wr) T 1) (wP : InRegions s.wr P 1) :
    ∃ s', runBlock isa encByte s = some s' ∧ (s'.gpr .eax).setWidth 8 = s.mem P ^^^ s.mem T ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW P (s.mem P ^^^ s.mem T) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, encByte, cOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      readSrc, State.load8, State.store8, ea_at', execAlu, Option.bind_some, Option.map_some, Reg8.reg,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, hp, ht, rP, rT, wP]
    rfl, ?_⟩
  refine ⟨?_, fun r h₁ h₂ => ?_, ?_, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg, h₁, h₂]
  · simp only [low_xor]

theorem decByte_ok (s : State) {P T : Addr} (hp : addr (s.gpr .esi) 0 = P) (ht : addr (s.gpr .ebp) 2048 = T)
    (rP : InRegions (s.rd ++ s.wr) P 1) (rT : InRegions (s.rd ++ s.wr) T 1) (wP : InRegions s.wr P 1) :
    ∃ s', runBlock isa decByte s = some s' ∧ (s'.gpr .eax).setWidth 8 = s.mem P ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW P (s.mem T ^^^ s.mem P) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, decByte, cOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      readSrc, State.load8, State.store8, ea_at', execAlu, Option.bind_some, Option.map_some, Reg8.reg,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, hp, ht, rP, rT, wP]
    rfl, ?_⟩
  refine ⟨?_, fun r h₁ h₂ => ?_, ?_, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg, h₁, h₂]
  · simp only [low_xor]

theorem shift_ok (s : State) {Q : Addr} (hq : (s.gpr .ebx).setWidth 64 = Q) (hfit : (s.gpr .ebx).toNat + 16 ≤ 2 ^ 32)
    (hr : ∀ d n, d + n ≤ 16 → InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 d) n)
    (hw : ∀ d n, d + n ≤ 16 → InRegions s.wr (Q + BitVec.ofNat 64 d) n) :
    ∃ s', runBlock isa shift s = some s' ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .edi → r ≠ .ebp → s'.gpr r = s.gpr r) ∧
      s'.mem = AesCfb8.shiftMem32 s.mem Q ((s.gpr .eax).setWidth 8) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a (d : Nat) (hd : d < 16) : addr (s.gpr .ebx) d = Q + BitVec.ofNat 64 d := by
    rw [addr_eq (by omega_using [hfit, hd]), hq]
  obtain a0 : addr (s.gpr .ebx) 0 = Q := by rw [a 0 (by decide)]; simp
  obtain w0 : InRegions s.wr Q 4 := by simpa using hw 0 4 (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, shift, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load32, State.store32, State.store8, ea_at', Option.map_some, Reg8.reg,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, a0, a 1 (by decide), a 4 (by decide), a 5 (by decide),
      a 8 (by decide), a 9 (by decide), a 11 (by decide), a 12 (by decide), a 15 (by decide),
      hr 1 4 (by decide), hr 5 4 (by decide), hr 9 4 (by decide), hr 12 4 (by decide), w0,
      hw 4 4 (by decide), hw 8 4 (by decide), hw 11 4 (by decide), hw 15 1 (by decide)]
    rfl, ?_⟩
  refine ⟨fun r h₁ h₂ h₃ h₄ => ?_, rfl, rfl, rfl⟩
  simp [gpr_setReg, h₁, h₂, h₃, h₄]

end VG.Proof.AesCfb8.X86

end

end

/-! ### `AesCfb8.X86.Loop`, which only this module used -/

section

/-!
# AES-CFB8 on x86: the contracts, and the loop

The artifacts' contracts are the shared ones of `Spec/Cfb8/Contract.lean`,
which imply these (`Verified.lean`): `cfb8X86 enc`, for encryption
(`enc = true`) and decryption. The functions have AES-CBC's arguments, with
`len` counting bytes, and its prologue and epilogue
(`Proof/AesCbc/X86/Body.lean`), whose stride-free definitions this reuses.

The invariant after `k` bytes (`LInv`): `esi` points at the next byte,
`esp` is unchanged, only the input block, the data, the first 2064 bytes of
the scratch buffer and the 24 bytes below `esp` have changed since the
registers were saved, the first `k` bytes are CFB8's of the first `k` bytes
on entry and the rest are unchanged, and the input block is the one after
them. Everything else is reloaded from the stack arguments, which nothing
writes.

`whole_wp`: if one run of `body` takes the invariant from `k` to `k + 1`
bytes and sets ZF when none are left (`BodyOk`), `whole body` meets the
contract.
-/

@[expose] public section

namespace VG.Proof.AesCfb8.X86

open VG VG.X86 VG.Impl.AesCbc.X86
open VG.Impl.CmacAes.X86 (argOp setup restore saved)
open VG.Proof.CmacAes.X86 (wp_arg wp_addArg saved_fits saved_bound saved_ne_eax restore_eq
  setup_eq ofNat_and_self_beq arg_ofNat add0 add0')
open VG.Proof.MdStream.X86 (Upd wp_addi wp_add wp_cmp wp_test eval_e eval_ne)
open VG.Proof.AesCbc.X86 (E W R Iv Dp N S schR ivR scrR argsR retR stkR iv0 wK savedMem savedMem_frame
  savedMem_slot savedMem_big)
open VG.Spec.Aes (bytesAt)

/-- `vg_aes_cfb8_encrypt` (`enc`) or `vg_aes_cfb8_decrypt` `(schedule, rounds, iv, data, len, scratch)`. -/
def cfb8X86 (enc : Bool) : Contract isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 240⟩
    let iv : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scr : Region := ⟨(arg s 5).setWidth 64, 2176⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 24, 24⟩
    s.rd = [sched, args] ∧ s.wr = [iv, data, scr] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ iv.Disjoint data ∧ iv.Disjoint scr ∧
      data.Disjoint scr ∧ args.Disjoint iv ∧ args.Disjoint data ∧ args.Disjoint scr ∧
      ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧
      stack.Disjoint sched ∧ stack.Disjoint iv ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧
      (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 2176 ≤ 2 ^ 32 ∧
      24 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
      ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14)
  post s s' :=
    let ciph := Spec.Cbc.aesWith (arg s 1).toNat
      (bytesAt s.mem ((arg s 0).setWidth 64) (16 * ((arg s 1).toNat + 1)))
    let iv := bytesAt s.mem ((arg s 2).setWidth 64) 16
    let xs := bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat
    bytesAt s'.mem ((arg s 3).setWidth 64) (arg s 4).toNat = cfb8 enc ciph iv xs ∧
      bytesAt s'.mem ((arg s 2).setWidth 64) 16 = inK enc ciph iv xs
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

section
variable (s₀ : State)

abbrev dataR : Region := ⟨(Dp s₀).setWidth 64, N s₀⟩

/-- The cipher. -/
abbrev ciph : Spec.Cbc.Cipher := Spec.Cbc.aesWith (R s₀) (wK s₀)

/-- The bytes on entry. -/
abbrev bs : List Byte := bytesAt s₀.mem ((Dp s₀).setWidth 64) (N s₀)

/-- The address of byte `k`. -/
abbrev byt (k : Nat) : Addr := (Dp s₀).setWidth 64 + BitVec.ofNat 64 k

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
  args_iv : (argsR s₀).Disjoint (ivR s₀)
  args_data : (argsR s₀).Disjoint (dataR s₀)
  args_scr : (argsR s₀).Disjoint (scrR s₀)
  ret_iv : (retR s₀).Disjoint (ivR s₀)
  ret_data : (retR s₀).Disjoint (dataR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)
  b_sch : (stkR s₀).Disjoint (schR s₀)
  b_iv : (stkR s₀).Disjoint (ivR s₀)
  b_data : (stkR s₀).Disjoint (dataR s₀)
  b_scr : (stkR s₀).Disjoint (scrR s₀)
  sch_fit : (W s₀).toNat + 240 ≤ 2 ^ 32
  iv_fit : (Iv s₀).toNat + 16 ≤ 2 ^ 32
  data_fit : (Dp s₀).toNat + N s₀ ≤ 2 ^ 32
  scr_fit : (S s₀).toNat + 2176 ≤ 2 ^ 32
  esp24 : 24 ≤ (E s₀).toNat
  esp_fit : (E s₀).toNat + 28 ≤ 2 ^ 32
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {enc : Bool} {s₀ : State} (h : (cfb8X86 enc).pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x, y, z⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x, y, z⟩

/-- The loop invariant, after `k` bytes. -/
structure LInv (enc : Bool) (s₀ : State) (k : Nat) (s : State) : Prop where
  esi : s.gpr .esi = Dp s₀ + BitVec.ofNat 32 k
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) s.mem
  data : bytesAt s.mem ((Dp s₀).setWidth 64) (N s₀) = outK s₀ enc k ++ (bs s₀).drop k
  iv : bytesAt s.mem ((Iv s₀).setWidth 64) 16 = inKk s₀ enc k

/-! ## Addresses and regions -/

/-- The regions the function writes, with the stack below it. -/
abbrev Big (s₀ : State) : List Region := [ivR s₀, dataR s₀, scrR s₀, stkR s₀]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.below_eq : below (E s₀) 24 = stkR s₀ := by
  simp only [below]; rw [Taint.sub_setWidth hp.esp24]

theorem UPre.argA {i : Nat} (hi : i < 6) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  simp only [argAddr]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * i) from rfl,
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * 0) from rfl,
    addr_eq (by omega_using [hi, this]), addr_eq (by omega_using [this]), Offset.add_add]

theorem UPre.arg_sub {i : Nat} (hi : i < 6) : Region.Sub ⟨argAddr s₀ i, 4⟩ (argsR s₀) := by
  rw [hp.argA hi]; exact Offset.sub_base _ (by omega_using [hi])

theorem UPre.arg_in {i : Nat} (hi : i < 6) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 := by
  refine ⟨argsR s₀, by simp [hp.rd], ?_⟩
  rw [hp.argA hi]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])

theorem UPre.args_stk : (argsR s₀).Disjoint (stkR s₀) := by
  have : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  obtain e : argAddr s₀ 0 = (E s₀).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega_using [this])
  show Region.Disjoint ⟨argAddr s₀ 0, 24⟩ _
  rw [e]; exact (Offset.disjoint_below_above _ (by decide)).symm

/-- The stack arguments are unchanged where only `Big` changes. -/
theorem UPre.arg_keep {m : Mem} (hf : Frame (Big s₀) s₀.mem m) {i : Nat} (hi : i < 6) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.args_iv.sub_left (hp.arg_sub hi)
    · exact hp.args_data.sub_left (hp.arg_sub hi)
    · exact hp.args_scr.sub_left (hp.arg_sub hi)
    · exact hp.args_stk.sub_left (hp.arg_sub hi)) (by decide)

theorem UPre.dataA {k : Nat} (hk : k < N s₀) : addr (Dp s₀) k = byt s₀ k :=
  addr_eq (by have := hp.data_fit; omega_using [hk, this])

theorem UPre.byt_disjoint {j k : Nat} (hj : j < N s₀) (hk : k < N s₀) (hjk : j ≠ k) :
    (⟨byt s₀ j, 1⟩ : Region).Disjoint ⟨byt s₀ k, 1⟩ := by
  have := hp.data_fit
  exact Offset.disjoint _ (by omega_using [hjk]) (by omega_using [hj, this]) (by omega_using [hk, this])

end

theorem UPre.scr_sub {s₀ : State} {d n : Nat} (h : d + n ≤ 2176) :
    Region.Sub ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {s₀ : State} {k : Nat} (hk : k < N s₀) : Region.Sub ⟨byt s₀ k, 1⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega_using [hk])

theorem UPre.big_of {s₀ : State} {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m) :
    Frame (Big s₀) s₀.mem m :=
  ((savedMem_frame s₀).mono (by simp)).trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    bytesAt m ((W s₀).setWidth 64) (16 * (R s₀ + 1)) = bytesAt s₀.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)) := by
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
    (hf : Frame [⟨byt s₀ k, 1⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] m m') :
    bytesAt m' ((Dp s₀).setWidth 64) (N s₀) =
      (bytesAt m ((Dp s₀).setWidth 64) (N s₀)).set k (m' (byt s₀ k)) := by
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
    WP isa (.block setup) s₀ fun s => LInv enc s₀ 0 s ∧ s.zf = some (decide (N s₀ = 0)) := by
  have hsc := hp.scr_fit
  rw [setup_eq]
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  have h₁ : s₁.gpr .eax = S s₀ := u₁.gpr
  refine Spill.save_ofNat_ok saved saved_fits (by rw [h₁]; omega_using [hsc]) (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb := saved_bound p hp'
    rw [h₁, u₁.wr, hp.wr]
    exact ⟨scrR s₀, by simp, Offset.contains_base _ (by omega_using [hb]) (by omega_using [hb])⟩
  obtain hm₂ : s₂.mem = savedMem s₀ := by
    rw [u₂.mem, u₁.mem, h₁, savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  obtain esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [u₂.gpr, u₁.other _ (by decide)]
  obtain rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
  obtain sb : Frame (Big s₀) s₀.mem (savedMem s₀) := (savedMem_frame s₀).mono (by simp)
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rw₂]; exact hp.arg_in (by decide))
    (by rw [hm₂]; exact hp.arg_keep sb (by decide)) fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rw₂]; exact hp.arg_in (by decide))
    (by rw [u₃.mem, hm₂]; exact hp.arg_keep sb (by decide)) fun s₄ u₄ => ?_
  obtain f₀ := savedMem_frame s₀
  obtain ivS : bytesAt (savedMem s₀) ((Iv s₀).setWidth 64) 16 = iv0 s₀ :=
    Proof.Cmac.bytesAt_frame f₀ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_scr) (by decide)
  obtain dataS : bytesAt (savedMem s₀) ((Dp s₀).setWidth 64) (N s₀) = bs s₀ :=
    Proof.Cmac.bytesAt_frame f₀ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.data_scr) (by have := hp.data_fit; omega_using [this])
  refine wp_test fun s₅ f₅ z₅ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, add0']
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), esp₂]
  · rw [f₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [f₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂]; exact Frame.refl _ _
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂, dataS]
    simp only [outK, List.take_zero, cfb8_nil, List.drop_zero, List.nil_append]
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂, ivS]
    simp only [inKk, List.take_zero, inK_nil]
  · rw [z₅, u₄.gpr, arg_ofNat s₀ 4, ofNat_and_self_beq (arg s₀ 4).isLt]

/-! ## The end of a byte -/

theorem advance_eq : Impl.AesCfb8.X86.advance = .alu .add .esi (.imm 1) :: .mov .eax (argOp 4) ::
    .alu .add .eax (argOp 3) :: .alu .cmp .esi (.reg .eax) :: [] := rfl

theorem adv_zf {D n : BitVec 32} {k : Nat} (hk : k < n.toNat) (_hfit : D.toNat + n.toNat ≤ 2 ^ 32) :
    (D + BitVec.ofNat 32 k + 1 - (n + D) == 0) = decide (k + 1 = n.toNat) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
  have := D.isLt
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  have h0 : (0 : BitVec 32).toNat = 0 := rfl
  omega

theorem advance_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (hesi : s.gpr .esi = Dp s₀ + BitVec.ofNat 32 k) (hesp : s.gpr .esp = E s₀)
    (hargs : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i) (hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr) :
    WP isa (.block Impl.AesCfb8.X86.advance) s fun s' => s'.gpr .esi = Dp s₀ + BitVec.ofNat 32 (k + 1) ∧
      s'.gpr .esp = E s₀ ∧ (∀ r, r ≠ .eax → r ≠ .esi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = some (decide (k + 1 = N s₀)) := by
  rw [advance_eq]
  refine wp_addi fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), hesp]) (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₁.mem]; exact hargs 4 (by decide)) fun s₂ u₂ => ?_
  refine wp_addArg (s₀ := s₀) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hesp])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₂.mem, u₁.mem]; exact hargs 3 (by decide)) fun s₃ u₃ => ?_
  refine wp_cmp fun s₄ f₄ _ z₄ => WP.block_nil ⟨?_, ?_, fun r h₁ h₂ => ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hesi,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add_eq _ (c := k + 1) (by omega_using [])]
  · rw [f₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hesp]
  · rw [f₄.gpr, u₃.other _ h₁, u₂.other _ h₁, u₁.other _ h₂]
  · rw [f₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [f₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [f₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [z₄, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₂.other _ (by decide), u₁.gpr, hesi]
    exact congrArg some (adv_zf hk hp.data_fit)

/-! ## The loop -/

/-- One run of `body` takes the invariant from `k` bytes to `k + 1`, and sets
ZF if no bytes are left. -/
def BodyOk (enc : Bool) (body : Prog isa) : Prop :=
  ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv enc s₀ k s →
    WP isa body s fun s' => LInv enc s₀ (k + 1) s' ∧ s'.zf = some (decide (k + 1 = N s₀))

theorem loop_ok {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (hp : UPre s₀) {k : Nat}
    (hk : k < N s₀) {s : State} (h : LInv enc s₀ k s) : WP isa (.loop body .ne) s (LInv enc s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body) (c := .ne) (Q := LInv enc s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv enc s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (hb hp hk h) fun s' ⟨h', hz⟩ => ?_
  obtain ev : isa.eval .ne s' = some !decide (k + 1 = N s₀) := by
    show VG.X86.eval .ne s' = _; rw [eval_ne, hz]; rfl
  by_cases hz' : k + 1 = N s₀
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [← hz']
  · right
    refine ⟨by rw [ev]; simp [hz'], N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, hz'], h'⟩

theorem mid_wp {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (hp : UPre s₀) {s₁ : State}
    (h : LInv enc s₀ 0 s₁) (hz : s₁.zf = some (decide (N s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop body .ne)) s₁ (LInv enc s₀ (N s₀)) := by
  obtain ev : isa.eval .e s₁ = some (decide (N s₀ = 0)) := by
    show VG.X86.eval .e s₁ = _; rw [eval_e, hz]
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hb hp (by omega_using [hn]) h

/-! ## The epilogue -/

theorem slot_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m) {d : Nat}
    (h₁ : 2064 ≤ d) (h₂ : d + 4 ≤ 2080) :
    m.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 =
      (savedMem s₀).readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 :=
  hf.readW (r := ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.iv_scr.symm.sub_left (UPre.scr_sub (by omega_using [h₂]))
    · exact hp.data_scr.symm.sub_left (UPre.scr_sub (by omega_using [h₂]))
    · exact Offset.disjoint_base _ h₁ (by omega_using [h₂])
    · exact hp.b_scr.symm.sub_left (UPre.scr_sub (by omega_using [h₂]))) (by decide)

theorem UPre.ret_stk {s₀ : State} (_hp : UPre s₀) : (retR s₀).Disjoint (stkR s₀) := by
  have := Offset.disjoint_below_above ((E s₀).setWidth 64) (m := 24) (a := 0) (l := 4) (by decide)
  rw [add0] at this
  exact this.symm

/-- The return address, which nothing writes. -/
theorem ret_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m) :
    m.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  (UPre.big_of hf).readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.ret_iv
    · exact hp.ret_data
    · exact hp.ret_scr
    · exact hp.ret_stk) (by decide)

theorem epilogue_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {s : State} (h : LInv enc s₀ (N s₀) s) :
    WP isa (.block (restore 5)) s fun s' => abiPreserved s₀ s' ∧ (cfb8X86 enc).post s₀ s' := by
  have hsc : (arg s₀ 5).toNat + 2176 ≤ 2 ^ 32 := hp.scr_fit
  obtain rdwr : s.rd ++ s.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain sl : ∀ r d, (r, d) ∈ saved → s.mem.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
    fun r d hrd => by
      obtain hb := saved_bound _ hrd
      rw [slot_read hp h.frame hb.1 hb.2, savedMem_slot s₀ hrd]
  obtain hall : (bs s₀).take (N s₀) = bs s₀ := List.take_of_length_le (by rw [length_bs])
  obtain hnil : (bs s₀).drop (N s₀) = [] := List.drop_of_length_le (by rw [length_bs])
  rw [restore_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide))
    (hp.arg_keep (UPre.big_of h.frame) (by decide)) fun s₁ u₁ => ?_
  refine Spill.restore_ofNat_ok saved saved_fits (by rw [u₁.gpr]; omega_using [hsc]) saved_ne_eax (fun p hp' => ?_)
    (fun p hp' => by rw [u₁.gpr, u₁.mem]; exact sl p.1 p.2 hp') fun s₂ r₂ => WP.block_nil ?_
  · have hb := saved_bound p hp'
    rw [u₁.gpr, u₁.rd, u₁.wr, rdwr]
    exact ⟨scrR s₀, by simp, Offset.contains_base _ (by omega_using [hb]) (by omega_using [hb])⟩
  refine ⟨⟨r₂.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), h.esp]), ?_⟩, ?_, ?_⟩
  · rw [r₂.mem, u₁.mem]; exact ret_read hp h.frame
  · show bytesAt s₂.mem ((Dp s₀).setWidth 64) (N s₀) = _
    rw [r₂.mem, u₁.mem, h.data]; simp only [outK, hall, hnil, List.append_nil]
  · show bytesAt s₂.mem ((Iv s₀).setWidth 64) 16 = _
    rw [r₂.mem, u₁.mem, h.iv]; simp only [inKk, hall]

theorem whole_wp {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (h0 : (cfb8X86 enc).pre s₀) :
    WP isa (whole body) s₀ fun s' => abiPreserved s₀ s' ∧ (cfb8X86 enc).post s₀ s' := by
  obtain hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, hz⟩ =>
    WP.seq (WP.mono (mid_wp hb hp h₁ hz) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.AesCfb8.X86

end

end


/-!
# AES-CFB8 on x86: one byte

`encBody_ok` and `decBody_ok`: one run of `body` takes the loop invariant
(`Loop.lean`) from `k` bytes to `k + 1` (`BodyOk`), for any implementation
of the block functions (`BlocksImpl`). The input block is copied to the
scratch buffer and enciphered there (`call_ok`), the data byte is replaced,
and the input block is shifted (`finish_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.X86

open VG VG.X86 VG.Impl.AesCfb8.X86
open VG.Impl.AesCbc.X86 (cOff blkCall)
open VG.Impl.CmacAes.X86 (argOp at_ xor4 zero4)
open VG.Proof.CmacAes.X86 (wp_arg xor4_ok zero4_ok add0 add0' arg_ofNat)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movi wp_addi)
open VG.Proof.AesCbc (copy4Mem copy4Mem_frame copy4Mem_bytes aesWith_state set_prefix)
open VG.Proof.AesCbc.X86 (E W R Iv Dp N S schR ivR scrR argsR stkR iv0 wK savedMem BlkPre BlkPost blk_call
  covIv covSv Sv)
open VG.Proof.Aes.X86 (BlocksImpl)
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

theorem UPre.scrN {d : Nat} (hd : d < 2176) : (S s₀ + BitVec.ofNat 32 d).toNat = (S s₀).toNat + d := by
  have := hp.scr_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [hd]), Nat.mod_eq_of_lt (by omega_using [hd, this])]

theorem UPre.sv : (Sv32 s₀).setWidth 64 = Sv s₀ := addr_eq (by have := hp.scr_fit; omega_using [this])

theorem UPre.cByt {k : Nat} (hk : k < N s₀) : (dataR s₀).Contains (byt s₀ k) 1 := by
  have := hp.data_fit
  exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk, this])

theorem UPre.byt_iv {k : Nat} (hk : k < N s₀) : (⟨byt s₀ k, 1⟩ : Region).Disjoint (ivR s₀) :=
  hp.iv_data.symm.sub_left (UPre.data_sub hk)

theorem UPre.byt_sv {k : Nat} (hk : k < N s₀) :
    (⟨byt s₀ k, 1⟩ : Region).Disjoint ⟨(S s₀).setWidth 64, 2064⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))

theorem UPre.byt_stk {k : Nat} (hk : k < N s₀) : (⟨byt s₀ k, 1⟩ : Region).Disjoint (stkR s₀) :=
  (hp.b_data.sub_right (UPre.data_sub hk)).symm

theorem UPre.iv_sv : (ivR s₀).Disjoint ⟨Sv s₀, 16⟩ := hp.iv_scr.sub_right (UPre.scr_sub (by decide))

theorem UPre.sv_scr : (⟨Sv s₀, 16⟩ : Region).Disjoint ⟨(S s₀).setWidth 64, 2048⟩ :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_fit; omega_using [])

/-- The stack arguments, in a state whose memory differs only within `Big`. -/
theorem UPre.args_of {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    ∀ i < 6, m.readW (argAddr s₀ i) 32 = arg s₀ i := fun _ hi => hp.arg_keep hf hi

/-- The arguments of a call on the copy of the input block, with the working
space at the start of the scratch buffer. -/
theorem UPre.blkPre {s : State}
    (eax : s.gpr .eax = W s₀) (ecx : s.gpr .ecx = arg s₀ 1) (ebx : s.gpr .ebx = Sv32 s₀)
    (edi : s.gpr .edi = 1) (ebp : s.gpr .ebp = S s₀) (esp : s.gpr .esp = E s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    BlkPre s (W s₀) (Sv32 s₀) (S s₀) (R s₀) := by
  obtain hb : below (s.gpr .esp) 24 = stkR s₀ := by rw [esp]; exact hp.below_eq
  have hd := hp.sv
  refine ⟨eax, by rw [ecx]; exact arg_ofNat s₀ 1, ebx, edi, ebp, hp.rounds, by rw [esp]; exact hp.esp24,
    ?_, hp.sch_scr.sub_right (Region.sub_prefix (by decide)), ?_, by rw [hb]; exact hp.b_sch, ?_,
    by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), hp.sch_fit, ?_,
    by have := hp.scr_fit; omega_using [this], ?_, ?_⟩
  · rw [hd]; exact hp.sch_scr.sub_right (UPre.scr_sub (by decide))
  · rw [hd]; exact hp.sv_scr
  · rw [hb, hd]; exact hp.b_scr.sub_right (UPre.scr_sub (by decide))
  · rw [hp.scrN (by decide)]; have := hp.scr_fit; omega_using [this]
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
structure PreA (s₀ : State) (s : State) (s₁ : State) : Prop where
  pre : BlkPre s₁ (W s₀) (Sv32 s₀) (S s₀) (R s₀)
  esi : s₁.gpr .esi = s.gpr .esi
  esp : s₁.gpr .esp = s.gpr .esp
  mem : s₁.mem = copy4Mem s.mem (Sv s₀) ((Iv s₀).setWidth 64)
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem pre_eq : pre = .mov .ebp (argOp 5) :: .mov .ebx (argOp 2) :: (zero4 .ebp cOff ++
    (xor4 .ebp .ebx .ebp cOff 0 cOff ++ (.mov .eax (argOp 0) :: .mov .ecx (argOp 1) :: .mov .ebx (.reg .ebp) ::
      .alu .add .ebx (.imm 2048) :: .mov .edi (.imm 1) :: []))) := rfl

theorem pre_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv enc s₀ k s) :
    WP isa (.block pre) s (PreA s₀ s) := by
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain big := UPre.big_of h.frame
  obtain hargs := hp.args_of big
  have hsc := hp.scr_fit
  have hiv := hp.iv_fit
  rw [pre_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hargs 5 (by decide)) fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), h.esp])
    (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide)) (by rw [u₁.mem]; exact hargs 2 (by decide))
    fun s₂ u₂ => ?_
  obtain p₂ : s₂.gpr .ebp = S s₀ := by rw [u₂.other _ (by decide), u₁.gpr]
  have b₂ : s₂.gpr .ebx = Iv s₀ := u₂.gpr
  obtain w₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [u₂.wr, u₁.wr, h.wr, hp.wr]
  refine zero4_ok (by decide) (by rw [p₂]; unfold cOff; omega_using [hsc]) (by rw [p₂, w₂]; exact covSv (by simp))
    fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  obtain p₃ : s₃.gpr .ebp = S s₀ := by rw [g₃ _ (by decide), p₂]
  obtain b₃ : s₃.gpr .ebx = Iv s₀ := by rw [g₃ _ (by decide), b₂]
  obtain rw₃ : s₃.rd ++ s₃.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rd₃, wr₃, u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr]; rfl
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [p₃]; unfold cOff; omega_using [hsc]) (by rw [b₃]; omega_using [hiv]) (by rw [p₃]; unfold cOff; omega_using [hsc])
    (by rw [p₃, rw₃]; exact covSv (by simp))
    (by rw [b₃, add0, rw₃]; exact covIv (by simp))
    (by rw [p₃, wr₃, w₂]; exact covSv (by simp)) fun s₄ g₄ => ?_
  obtain m₄ : s₄.mem = copy4Mem s.mem (Sv s₀) ((Iv s₀).setWidth 64) := by
    rw [g₄.mem, p₃, b₃, add0, m₃, p₂, u₂.mem, u₁.mem]; rfl
  obtain f₄ : Frame [⟨Sv s₀, 16⟩] s.mem s₄.mem := by rw [m₄]; exact copy4Mem_frame _ _ _
  obtain big₄ : Frame (Big s₀) s₀.mem s₄.mem := big.trans (f₄.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩)
  obtain esp₄ : s₄.gpr .esp = E s₀ := by
    rw [g₄.gpr _ (by decide) (by decide), g₃ _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
  obtain rw₄ : s₄.rd ++ s₄.wr = s₀.rd ++ s₀.wr := by rw [g₄.rd, g₄.wr, rd₃, wr₃, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]
  refine wp_arg (s₀ := s₀) esp₄ (by rw [rw₄]; exact hp.arg_in (by decide)) (hp.args_of big₄ 0 (by decide))
    fun s₅ u₅ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₅.other _ (by decide), esp₄])
    (by rw [u₅.rd, u₅.wr, rw₄]; exact hp.arg_in (by decide)) (by rw [u₅.mem]; exact hp.args_of big₄ 1 (by decide))
    fun s₆ u₆ => ?_
  refine wp_mov fun s₇ u₇ => wp_addi fun s₈ u₈ => wp_movi fun s₉ u₉ => WP.block_nil ?_
  obtain keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .ebx → r ≠ .edi → s₉.gpr r = s₄.gpr r :=
    fun r ha hc hb hd => by
      rw [u₉.other _ hd, u₈.other _ hb, u₇.other _ hb, u₆.other _ hc, u₅.other _ ha]
  obtain g₄' : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .ebx → r ≠ .ebp → s₄.gpr r = s.gpr r :=
    fun r ha hc hb hp' => by
      rw [g₄.gpr _ ha hc, g₃ _ ha, u₂.other _ hb, u₁.other _ hp']
  obtain rd₉ : s₉.rd = s.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, g₄.rd, rd₃, u₂.rd, u₁.rd]
  obtain wr₉ : s₉.wr = s.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, g₄.wr, wr₃, u₂.wr, u₁.wr]
  obtain esp₉ : s₉.gpr .esp = E s₀ := by rw [keep _ (by decide) (by decide) (by decide) (by decide), esp₄]
  obtain ebp₉ : s₉.gpr .ebp = S s₀ := by
    rw [keep _ (by decide) (by decide) (by decide) (by decide), g₄.gpr _ (by decide) (by decide), p₃]
  refine ⟨hp.blkPre ?_ ?_ ?_ u₉.gpr ebp₉ esp₉ (by rw [rd₉, h.rd]) (by rw [wr₉, h.wr]),
    by rw [keep _ (by decide) (by decide) (by decide) (by decide), g₄' _ (by decide) (by decide) (by decide)
      (by decide)],
    by rw [esp₉, h.esp],
    by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄], rd₉, wr₉⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      g₄.gpr _ (by decide) (by decide), p₃]
    rfl

/-! ## The call -/

/-- What the code before the call and the call leave, for either
direction. -/
structure AfterCall (enc : Bool) (s₀ : State) (k : Nat) (s s₂ : State) : Prop where
  esi : s₂.gpr .esi = Dp s₀ + BitVec.ofNat 32 k
  esp : s₂.gpr .esp = E s₀
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  frame : Frame [⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₂.mem
  out : s₂.mem (Sv s₀) = (ciph s₀ (inKk s₀ enc k)).headD 0

theorem call_ok {enc : Bool} (v : BlocksImpl) {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State}
    (h : LInv enc s₀ k s) (post : List Instr) {Q : State → Prop}
    (hq : ∀ s₂, AfterCall enc s₀ k s s₂ → WP isa (.block post) s₂ Q) :
    WP isa (body v.enc post) s Q := by
  refine WP.seq (WP.mono (pre_wp hp h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call v.encOk v.encNosp v.encStack a.pre) fun s₂ c => hq s₂ ?_)
  obtain esp₁ : s₁.gpr .esp = E s₀ := by rw [a.esp, h.esp]
  obtain hb : below (s₁.gpr .esp) 24 = stkR s₀ := by rw [esp₁]; exact hp.below_eq
  obtain svSub : Region.Sub ⟨Sv s₀, 16⟩ ⟨(S s₀).setWidth 64, 2064⟩ := Offset.sub_base _ (by decide)
  obtain f₁ : Frame [⟨Sv s₀, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact copy4Mem_frame _ _ _
  obtain big₁ : Frame (Big s₀) s₀.mem s₁.mem := (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩)
  refine ⟨by rw [c.saved .esi (by simp [calleeSaved]), a.esi, h.esi],
    by rw [c.saved .esp (by simp [calleeSaved]), esp₁], by rw [c.rd, a.rd], by rw [c.wr, a.wr],
    (f₁.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_), ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, svSub⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hp.sv]; exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, svSub⟩
    · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
    · rw [hb]; exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · have o := c.out
    rw [hp.sv] at o
    rw [← headD_bytesAt s₂.mem (Sv s₀), o, UPre.sched_bytes hp big₁, ← aesWith_state, a.mem,
      copy4Mem_bytes _ hp.iv_sv.symm, h.iv]

/-! ## After the call -/

/-- After the byte operation (`v` the new data byte, `c` the byte to shift
in, in `al`), the input block reloaded, the shift and `advance` take the
invariant to `k + 1`. -/
theorem finish_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ s₃ : State}
    (h : LInv enc s₀ k s) (a : AfterCall enc s₀ k s s₂) {v : Byte}
    (esi₃ : s₃.gpr .esi = s₂.gpr .esi) (esp₃ : s₃.gpr .esp = s₂.gpr .esp)
    (mem₃ : s₃.mem = s₂.mem.writeW (byt s₀ k) v) (rd₃ : s₃.rd = s₂.rd) (wr₃ : s₃.wr = s₂.wr)
    (hv : v = (bs s₀)[k]'(by rw [length_bs]; exact hk) ^^^ (ciph s₀ (inKk s₀ enc k)).headD 0)
    (hc : (s₃.gpr .eax).setWidth 8 = if enc then v else (bs s₀)[k]'(by rw [length_bs]; exact hk)) :
    WP isa (.block (.mov .ebx (argOp 2) :: (shift ++ Impl.AesCfb8.X86.advance))) s₃
      fun s' => LInv enc s₀ (k + 1) s' ∧ s'.zf = some (decide (k + 1 = N s₀)) := by
  have hiv := hp.iv_fit
  have one (r : Region) (P : Addr) (n : Nat) (hd : (⟨P, n⟩ : Region).Disjoint r) :
      ∀ r' ∈ [r], (⟨P, n⟩ : Region).Disjoint r' := fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hd
  -- Memory after the byte.
  obtain fByte : Frame [⟨byt s₀ k, 1⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₃.mem := by
    rw [mem₃]
    refine (a.frame.sub fun r hr => ?_).trans ((frame_write8 _ _ _).sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  obtain stepOf : ∀ {m : Mem}, Frame [⟨byt s₀ k, 1⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem m →
      Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem m := fun hf => hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  obtain big₃ : Frame (Big s₀) s₀.mem s₃.mem := (UPre.big_of h.frame).trans ((stepOf fByte).sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  obtain esp₃' : s₃.gpr .esp = E s₀ := by rw [esp₃, a.esp]
  obtain rw₃ : s₃.rd ++ s₃.wr = s₀.rd ++ s₀.wr := by rw [rd₃, wr₃, a.rd, a.wr, h.rd, h.wr]
  refine wp_arg (s₀ := s₀) esp₃' (by rw [rw₃]; exact hp.arg_in (by decide)) (hp.args_of big₃ 2 (by decide))
    fun s₄ u₄ => ?_
  obtain rl : s₄.rd ++ s₄.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [u₄.rd, u₄.wr, rw₃, hp.rd, hp.wr]; rfl
  obtain wl : s₄.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [u₄.wr, wr₃, a.wr, h.wr, hp.wr]
  obtain ⟨s₅, run₅, g₅, mem₅, rd₅, wr₅⟩ :=
    shift_ok s₄ (Q := (Iv s₀).setWidth 64) (by rw [u₄.gpr]) (by rw [u₄.gpr]; omega)
      (fun d n hd => by rw [rl]; exact ⟨ivR s₀, by simp, Offset.contains_base _ hd (by omega_using [hd])⟩)
      (fun d n hd => by rw [wl]; exact ⟨ivR s₀, by simp, Offset.contains_base _ hd (by omega_using [hd])⟩)
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  obtain fStep : Frame [⟨byt s₀ k, 1⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₅.mem := by
    rw [mem₅, u₄.mem]
    exact fByte.trans ((AesCfb8.shiftMem32_frame _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  obtain big₅ : Frame (Big s₀) s₀.mem s₅.mem := (UPre.big_of h.frame).trans ((stepOf fStep).sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  refine WP.mono (advance_wp hp hk
    (by rw [g₅ _ (by decide) (by decide) (by decide) (by decide), u₄.other _ (by decide), esi₃, a.esi])
    (by rw [g₅ _ (by decide) (by decide) (by decide) (by decide), u₄.other _ (by decide), esp₃'])
    (hp.args_of big₅) (by rw [rd₅, wr₅, u₄.rd, u₄.wr, rw₃]))
    fun s₆ ⟨esi₆, esp₆, _, mem₆, rd₆, wr₆, zf₆⟩ => ⟨?_, zf₆⟩
  obtain newByte : s₆.mem (byt s₀ k) = v := by
    rw [mem₆, mem₅, byte_frame (AesCfb8.shiftMem32_frame _ _ _) (one _ _ _ (hp.byt_iv hk)), u₄.mem, mem₃,
      writeW8_self]
  obtain ivIn : bytesAt s₄.mem ((Iv s₀).setWidth 64) 16 = inKk s₀ enc k := by
    rw [u₄.mem, mem₃, Proof.Cmac.bytesAt_frame (frame_write8 _ _ _) (one _ _ _ (hp.byt_iv hk).symm) (by decide),
      Proof.Cmac.bytesAt_frame a.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
        · exact hp.b_iv.symm) (by decide), h.iv]
  obtain hl : (outK s₀ enc k).length = k := by
    rw [outK, length_cfb8, List.length_take, length_bs]; omega_using [hk]
  obtain iv_ne : iv0 s₀ ≠ [] := by simp [iv0, bytesAt]
  obtain eax₄ : (s₄.gpr .eax).setWidth 8 = if enc then v else (bs s₀)[k]'(by rw [length_bs]; exact hk) := by
    rw [u₄.other _ (by decide), hc]
  refine ⟨esi₆, esp₆, by rw [rd₆, rd₅, u₄.rd, rd₃, a.rd, h.rd], by rw [wr₆, wr₅, u₄.wr, wr₃, a.wr, h.wr],
    by rw [mem₆]; exact h.frame.trans (stepOf fStep), ?_, ?_⟩
  · rw [mem₆, hp.bytes_step hk fStep, h.data, ← mem₆, newByte, set_prefix _ _ _ hl (by rw [length_bs]; exact hk),
      hv]
    simp only [outK, take_succ_bs s₀ hk, cfb8_snoc enc _ iv_ne, inKk]
  · rw [mem₆, mem₅, AesCfb8.shiftMem32_bytes, ivIn, eax₄]
    simp only [inKk, take_succ_bs s₀ hk, inK_snoc enc _ iv_ne, ← hv]

/-! ## One byte -/

/-- The data byte before the byte operation. -/
theorem AfterCall.byte {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ : State}
    (h : LInv enc s₀ k s) (a : AfterCall enc s₀ k s s₂) :
    s₂.mem (byt s₀ k) = (bs s₀)[k]'(by rw [length_bs]; exact hk) := by
  rw [byte_frame a.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.byt_sv hk
    · exact hp.byt_stk hk), h.byte hk]

/-- The registers and regions the byte operation needs. -/
theorem AfterCall.regs {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ s₃ : State}
    (h : LInv enc s₀ k s) (a : AfterCall enc s₀ k s s₂) (u : Upd s₂ s₃ .ebp (arg s₀ 5)) :
    addr (s₃.gpr .esi) 0 = byt s₀ k ∧ addr (s₃.gpr .ebp) 2048 = Sv s₀ ∧
      InRegions (s₃.rd ++ s₃.wr) (byt s₀ k) 1 ∧ InRegions (s₃.rd ++ s₃.wr) (Sv s₀) 1 ∧
      InRegions s₃.wr (byt s₀ k) 1 := by
  obtain rl : s₃.rd ++ s₃.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [u.rd, u.wr, a.rd, a.wr, h.rd, h.wr, hp.rd, hp.wr]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [u.other _ (by decide), a.esi]; simp only [addr, add0']; exact hp.dataA hk
  · rw [u.gpr]; exact hp.sv
  · rw [rl]; exact ⟨dataR s₀, by simp, hp.cByt hk⟩
  · rw [rl]; exact ⟨scrR s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  · rw [u.wr, a.wr, h.wr, hp.wr]; exact ⟨dataR s₀, by simp, hp.cByt hk⟩

theorem encBody_ok (v : BlocksImpl) : BodyOk true (body v.enc encPost) := by
  intro s₀ hp k hk s h
  refine call_ok v hp h encPost fun s₂ a => ?_
  obtain big₂ : Frame (Big s₀) s₀.mem s₂.mem := (UPre.big_of h.frame).trans (a.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  rw [encPost_eq]
  refine wp_arg (s₀ := s₀) a.esp (by rw [a.rd, a.wr, h.rd, h.wr]; exact hp.arg_in (by decide))
    (hp.args_of big₂ 5 (by decide)) fun s₃ u₃ => ?_
  obtain ⟨eP, eT, rP, rT, wP⟩ := a.regs hp hk h u₃
  obtain ⟨s₄, run₄, rax₄, g₄, mem₄, rd₄, wr₄⟩ := encByte_ok s₃ eP eT rP rT wP
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, run₄, finish_wp hp hk h a (by rw [g₄ _ (by decide) (by decide), u₃.other _ (by decide)])
    (by rw [g₄ _ (by decide) (by decide), u₃.other _ (by decide)]) (by rw [mem₄, u₃.mem])
    (by rw [rd₄, u₃.rd]) (by rw [wr₄, u₃.wr]) (by rw [a.byte hp hk h, a.out]) ?_⟩
  rw [rax₄, u₃.mem, a.byte hp hk h, a.out]; rfl

theorem decBody_ok (v : BlocksImpl) : BodyOk false (body v.enc decPost) := by
  intro s₀ hp k hk s h
  refine call_ok v hp h decPost fun s₂ a => ?_
  obtain big₂ : Frame (Big s₀) s₀.mem s₂.mem := (UPre.big_of h.frame).trans (a.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  rw [decPost_eq]
  refine wp_arg (s₀ := s₀) a.esp (by rw [a.rd, a.wr, h.rd, h.wr]; exact hp.arg_in (by decide))
    (hp.args_of big₂ 5 (by decide)) fun s₃ u₃ => ?_
  obtain ⟨eP, eT, rP, rT, wP⟩ := a.regs hp hk h u₃
  obtain ⟨s₄, run₄, rax₄, g₄, mem₄, rd₄, wr₄⟩ := decByte_ok s₃ eP eT rP rT wP
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, run₄, finish_wp hp hk h a (by rw [g₄ _ (by decide) (by decide), u₃.other _ (by decide)])
    (by rw [g₄ _ (by decide) (by decide), u₃.other _ (by decide)]) (by rw [mem₄, u₃.mem])
    (by rw [rd₄, u₃.rd]) (by rw [wr₄, u₃.wr]) (by rw [a.byte hp hk h, a.out, BitVec.xor_comm]) ?_⟩
  rw [rax₄, u₃.mem, a.byte hp hk h]; rfl

end VG.Proof.AesCfb8.X86
