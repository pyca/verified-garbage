module

public import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesCbc.X86_64.Body
import VerifiedGarbage.Proof.AesCbc.X86_64.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesXts.X86_64Unit
public import VerifiedGarbage.Proof.AesXts.Unit
public import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
public import VerifiedGarbage.Proof.Aes.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesXts.X86_64.Steps
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Call
public import VerifiedGarbage.Spec.Xts.Contract

/-! ### `AesXts.X86_64.Unit.Contract`, which this module and modules that import it used -/

section

/-!
# XTS-AES of data units on x86-64: the contract the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Xts/Contract.lean`, which imply `unitX86_64`
(`Verified.lean`): `(schedule = rdi, tweak_schedule = rsi, rounds = rdx,
i = rcx, data = r8, len = r9, scratch = [rsp + 8])`. The functions call a
whole-block function, which calls a block function: the return addresses
are in the 16 bytes below the stack pointer (`stk`), which no buffer
overlaps, nor the return address (`retR`).

`UPre` names the facts of the precondition; the regions of the scratch
buffer (`tR`, `zR`, `wkR`, the slots of the saved registers) are apart from
each other and from everything else.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Unit

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)

section
variable (s : State)

abbrev W : Addr := s.gpr .rdi
abbrev K : Addr := s.gpr .rsi
abbrev R : Nat := (s.gpr .rdx).toNat
abbrev I : Addr := s.gpr .rcx
abbrev D : Addr := s.gpr .r8
abbrev Len : Nat := (s.gpr .r9).toNat
/-- The scratch buffer, the stack argument. -/
abbrev S : Addr := stackArg s 0

abbrev schR : Region := ⟨W s, 240⟩
abbrev tschR : Region := ⟨K s, 240⟩
abbrev iR : Region := ⟨I s, 16⟩
abbrev dataR : Region := ⟨D s, Len s⟩
abbrev scrR : Region := ⟨S s, 2432⟩
abbrev argR : Region := ⟨stackArgAddr s 0, 8⟩
abbrev retR : Region := ⟨s.gpr .rsp, 8⟩

/-- The tweak, the second tweak, and the working space of the calls, in the
scratch buffer. -/
abbrev tR : Region := ⟨S s + BitVec.ofNat 64 Impl.AesXts.X86_64Unit.tO, 16⟩
abbrev zR : Region := ⟨S s + BitVec.ofNat 64 Impl.AesXts.X86_64Unit.zO, 16⟩
abbrev wkR : Region := ⟨S s, 2176⟩

/-- The number of whole blocks, the bytes after them, and the last whole block. -/
abbrev M : Nat := Len s / 16
abbrev B : Nat := Len s % 16
abbrev L : Addr := D s + BitVec.ofNat 64 (16 * (M s - 1))

end

/-- What the functions need: the permissions, the buffers apart, the stack
the calls use apart from them, `rounds` of 10, 12 or 14, and a data unit of
16 bytes to 2²⁰ blocks. -/
def unitPre (s : State) : Prop :=
  s.rd = [schR s, tschR s, iR s, argR s] ∧ s.wr = [dataR s, scrR s] ∧
    (schR s).Disjoint (dataR s) ∧ (schR s).Disjoint (scrR s) ∧ (tschR s).Disjoint (dataR s) ∧
    (tschR s).Disjoint (scrR s) ∧ (iR s).Disjoint (dataR s) ∧ (iR s).Disjoint (scrR s) ∧
    (dataR s).Disjoint (scrR s) ∧ (dataR s).Disjoint (argR s) ∧ (scrR s).Disjoint (argR s) ∧
    (retR s).Disjoint (dataR s) ∧ (retR s).Disjoint (scrR s) ∧
    (stk s).Disjoint (schR s) ∧ (stk s).Disjoint (tschR s) ∧ (stk s).Disjoint (iR s) ∧
    (stk s).Disjoint (dataR s) ∧ (stk s).Disjoint (scrR s) ∧
    (I s).toNat + 16 ≤ 2 ^ 64 ∧ (D s).toNat + Len s ≤ 2 ^ 64 ∧ (S s).toNat + 2432 ≤ 2 ^ 64 ∧
    16 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64 ∧
    (R s = 10 ∨ R s = 12 ∨ R s = 14) ∧ 16 ≤ Len s ∧ Len s ≤ 16 * Spec.Xts.maxBlocks

/-- XTS-AES of the data unit in a direction. -/
def xtsOf : Bool → List Byte → List Byte → List Byte → Option (List Byte)
  | true => Spec.Xts.aesXtsEncrypt
  | false => Spec.Xts.aesXtsDecrypt

def unitPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ stackArg s₁ 0 = stackArg s₂ 0

/-- `vg_aes_xts_encrypt_unit` (`enc`) or `vg_aes_xts_decrypt_unit`. -/
def unitX86_64 (enc : Bool) : Contract isa where
  pre := unitPre
  post s s' := ∀ key, Spec.Xts.KeySchedules s.mem (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx).toNat key →
    xtsOf enc key (bytesAt s.mem (s.gpr .rcx) 16) (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) =
      some (bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat)
  pub := unitPub

/-- The precondition, by name. -/
structure UPre (s : State) : Prop where
  rd : s.rd = [schR s, tschR s, iR s, argR s]
  wr : s.wr = [dataR s, scrR s]
  sch_data : (schR s).Disjoint (dataR s)
  sch_scr : (schR s).Disjoint (scrR s)
  tsch_data : (tschR s).Disjoint (dataR s)
  tsch_scr : (tschR s).Disjoint (scrR s)
  i_data : (iR s).Disjoint (dataR s)
  i_scr : (iR s).Disjoint (scrR s)
  data_scr : (dataR s).Disjoint (scrR s)
  data_arg : (dataR s).Disjoint (argR s)
  scr_arg : (scrR s).Disjoint (argR s)
  ret_data : (retR s).Disjoint (dataR s)
  ret_scr : (retR s).Disjoint (scrR s)
  stk_sch : (stk s).Disjoint (schR s)
  stk_tsch : (stk s).Disjoint (tschR s)
  stk_i : (stk s).Disjoint (iR s)
  stk_data : (stk s).Disjoint (dataR s)
  stk_scr : (stk s).Disjoint (scrR s)
  i_wrap : (I s).toNat + 16 ≤ 2 ^ 64
  data_wrap : (D s).toNat + Len s ≤ 2 ^ 64
  scr_wrap : (S s).toNat + 2432 ≤ 2 ^ 64
  rsp_lo : 16 ≤ (s.gpr .rsp).toNat
  rsp_hi : (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64
  rounds : R s = 10 ∨ R s = 12 ∨ R s = 14
  len_lo : 16 ≤ Len s
  len_hi : Len s ≤ 16 * Spec.Xts.maxBlocks

theorem UPre.of {s : State} (h : unitPre s) : UPre s :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x, y, z, a'⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x, y, z, a'⟩

/-! ## Regions -/

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x h => h₂ x (h₁ x h)

section
variable {s : State} (hp : UPre s)
include hp

theorem UPre.m_pos : 1 ≤ M s := by have := hp.len_lo; simp only [M]; omega_using [this]

theorem UPre.m_lt : M s < 2 ^ 60 := by
  have := hp.len_hi; simp only [M, Spec.Xts.maxBlocks] at *; omega_using [this]

omit hp in
theorem len_eq (s : State) : Len s = 16 * M s + B s := by simp only [M, B]; omega_using []

omit hp in
theorem scr_sub {d n : Nat} (h : d + n ≤ 2432) : Region.Sub ⟨S s + BitVec.ofNat 64 d, n⟩ (scrR s) :=
  Offset.sub_base _ h

omit hp in
theorem data_sub {d n : Nat} (h : d + n ≤ Len s) : Region.Sub ⟨D s + BitVec.ofNat 64 d, n⟩ (dataR s) :=
  Offset.sub_base _ h

omit hp in
theorem wk_sub : Region.Sub (wkR s) (scrR s) := Region.sub_prefix (by decide)

theorem UPre.t_wk : (tR s).Disjoint (wkR s) :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; simp only [Impl.AesXts.X86_64Unit.tO]; omega_using [])

theorem UPre.z_wk : (zR s).Disjoint (wkR s) :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; simp only [Impl.AesXts.X86_64Unit.zO]; omega_using [])

theorem UPre.t_z : (tR s).Disjoint (zR s) :=
  Offset.disjoint _ (by simp only [Impl.AesXts.X86_64Unit.tO, Impl.AesXts.X86_64Unit.zO]; omega_using [])
    (by have := hp.scr_wrap; simp only [Impl.AesXts.X86_64Unit.tO]; omega_using [])
    (by have := hp.scr_wrap; simp only [Impl.AesXts.X86_64Unit.zO]; omega_using [])

omit hp in
/-- The slots of the saved registers. -/
theorem slot_sub (d : Nat) (h₁ : 2208 ≤ d) (h₂ : d + 8 ≤ 2256) :
    Region.Sub ⟨S s + BitVec.ofNat 64 d, 8⟩ ⟨S s + BitVec.ofNat 64 2208, 48⟩ :=
  Offset.sub _ h₁ (by omega_using [h₂])

/-- Everything the code writes but the slots lies within the data, the first
2208 bytes of the scratch buffer, or the stack below. -/
theorem UPre.slots_disj {r : Region} (hr : Region.Sub r (dataR s) ∨ Region.Sub r ⟨S s, 2208⟩ ∨ r = stk s) :
    (⟨S s + BitVec.ofNat 64 2208, 48⟩ : Region).Disjoint r := by
  have slot : Region.Sub ⟨S s + BitVec.ofNat 64 2208, 48⟩ (scrR s) := scr_sub (by decide)
  rcases hr with h | h | rfl
  · exact (hp.data_scr.symm.sub_left slot).sub_right h
  · exact (Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega_using [])).sub_right h
  · exact (hp.stk_scr.symm.sub_left slot)

omit hp in
theorem t_sub : Region.Sub (tR s) ⟨S s, 2208⟩ := Offset.sub_base _ (by decide)
omit hp in
theorem z_sub : Region.Sub (zR s) ⟨S s, 2208⟩ := Offset.sub_base _ (by decide)
omit hp in
theorem s_sub : Region.Sub ⟨S s, 2208⟩ (scrR s) := Region.sub_prefix (by decide)

theorem UPre.l_sub : Region.Sub ⟨L s, 16⟩ (dataR s) := data_sub (by have := len_eq s; have := hp.m_pos; omega_arith)

theorem UPre.l_wrap : (L s).toNat + 16 ≤ 2 ^ 64 := by
  have := hp.data_wrap; have := len_eq s; have := hp.m_pos
  rw [L, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * (M s - 1)) (by omega),
    Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

end

/-! ## The parts of the data unit -/

section
variable {s : State} (hp : UPre s)
include hp

theorem UPre.wrapD : (D s).toNat + 16 * M s + B s ≤ 2 ^ 64 := by
  have := hp.data_wrap; have := len_eq s; omega_arith

omit hp in
theorem blocks_sub {N : Nat} (h : N ≤ M s) : Region.Sub ⟨D s, 16 * N⟩ (dataR s) :=
  Region.sub_prefix (by have := len_eq s; omega_using [h, this])

theorem UPre.lb_sub : Region.Sub ⟨L s, 16 + B s⟩ (dataR s) :=
  data_sub (by have := len_eq s; have := hp.m_pos; omega_arith)

theorem UPre.tl_eq : L s + 16 = D s + BitVec.ofNat 64 (16 * M s) := by
  rw [L, Proof.AesXts.Unit.add16, show 16 * (M s - 1) + 16 = 16 * M s by have := hp.m_pos; omega_using [this]]

theorem UPre.tl_sub : Region.Sub ⟨L s + 16, B s⟩ (dataR s) := by
  rw [hp.tl_eq]; exact data_sub (by have := len_eq s; omega_using [this])

theorem UPre.hd_lb : (⟨D s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s, 16 + B s⟩ :=
  Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.wrapD; have := hp.m_pos; omega_arith)

theorem UPre.hd_l : (⟨D s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s, 16⟩ :=
  hp.hd_lb.sub_right (Region.sub_prefix (by omega_using []))

theorem UPre.hd_tl : (⟨D s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s + 16, B s⟩ := by
  rw [hp.tl_eq]
  exact Offset.base_disjoint _ (by omega_using []) (by have := hp.wrapD; omega_using [this])

omit hp in
theorem tl_l : (⟨L s + 16, B s⟩ : Region).Disjoint ⟨L s, 16⟩ :=
  Offset.disjoint_base (L s) (d := 16) (n := B s) (k := 16) (Nat.le_refl _) (by simp only [B]; omega_using [])

theorem UPre.tl_blocks : (⟨L s + 16, B s⟩ : Region).Disjoint ⟨D s, 16 * M s⟩ := by
  rw [hp.tl_eq]
  exact Offset.disjoint_base _ (Nat.le_refl _) (by have := hp.wrapD; omega_using [this])

theorem UPre.l_hd : (⟨L s, 16⟩ : Region).Disjoint ⟨D s, 16 * (M s - 1)⟩ := hp.hd_l.symm

end

end VG.Proof.AesXts.X86_64.Unit

end

end

/-! ### `AesXts.X86_64.Unit.Steps`, which this module and modules that import it used -/

section

/-!
# XTS-AES of data units on x86-64: the code between the calls

Each straight-line piece of `encrypt` and `decrypt`, run once, with the
registers and memory it leaves, and the swap loop (`swap_ok`), which leaves
`swapMem` (`Proof/AesXts/Unit.lean`).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Unit

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesXts.X86_64Unit
open VG.Proof.AesCbc.X86_64 (offset_nat)
open VG.Proof.AesXts.Unit (swapMem swapMem_step swapMem_lo swapMem_hi)
open VG.Spec.Aes (bytesAt)

theorem save_eq : save = Spill.saveCode .rax saved := rfl

theorem restore_eq : restore = Spill.restoreCode .r15 saved := rfl

theorem ldS_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8) :
    runBlock isa ldS s =
      some (s.setReg .rax (s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64)) := by
  simp only [ldS, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea,
    offset_nat, hr, ite_true, Option.map_some]

theorem setup_ok (s : State) :
    ∃ s', runBlock isa setup s = some s' ∧
      s'.gpr .r15 = s.gpr .rax ∧ s'.gpr .rbx = s.gpr .rdi ∧ s'.gpr .rbp = s.gpr .rdx ∧
      s'.gpr .r12 = s.gpr .r8 ∧ s'.gpr .r13 = s.gpr .r9 ∧
      (∀ r, r ≠ .r15 → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [setup, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · intro r h₁ h₂ h₃ h₄ h₅; simp [gpr_setReg, h₁, h₂, h₃, h₄, h₅]

/-- The memory after zeroing the block at `c`. -/
def zero2 (m : Mem) (c : Addr) : Mem :=
  (m.writeW c (BitVec.setWidth 64 (0 : BitVec 32))).writeW (c + BitVec.ofNat 64 8) (BitVec.setWidth 64 (0 : BitVec 32))

theorem zero2_frame (m : Mem) (c : Addr) : Frame [⟨c, 16⟩] m (zero2 m c) := AesCbc.frame_store2 _ _ _

theorem zero2_bytes (m : Mem) (c : Addr) : bytesAt (zero2 m c) c 16 = List.replicate 16 0 := by
  rw [zero2, Proof.Cmac.bytesAt_store2]; decide

theorem zeroZ_ok (s : State) {Z : Addr} (hz : s.gpr .r15 + BitVec.ofNat 64 zO = Z)
    (hz8 : s.gpr .r15 + BitVec.ofNat 64 (zO + 8) = Z + BitVec.ofNat 64 8)
    (w0 : InRegions s.wr Z 8) (w8 : InRegions s.wr (Z + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa zeroZ s = some s' ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = zero2 s.mem Z ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, zeroZ, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc32, State.store64, State.ea, State.setReg32, offset_nat, Option.map_some, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, hz, hz8, w0, w8]
    rfl, ?_⟩
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp [gpr_setReg, hr]

theorem tArgs_ok (s : State) :
    ∃ s', runBlock isa tArgs s = some s' ∧
      s'.gpr .rdi = s.gpr .rsi ∧ s'.gpr .rsi = s.gpr .rbp ∧
      s'.gpr .rdx = s.gpr .r15 + BitVec.ofNat 64 zO ∧ s'.gpr .rcx = s.gpr .r15 + BitVec.ofNat 64 tO ∧
      s'.gpr .r8 = 1 ∧ s'.gpr .r9 = s.gpr .r15 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [tArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]; rfl
  · simp [gpr_setReg, State.setReg32]; rfl
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [gpr_setReg, State.setReg32]

theorem shr4 (x : BitVec 64) : x >>> 4 = BitVec.ofNat 64 (x.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := x.isLt; omega_using [])]

theorem shr4_shl4 (x : BitVec 64) : (x >>> 4) <<< 4 = BitVec.ofNat 64 (16 * (x.toNat / 16)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])]
  simp only [Nat.reducePow]
  omega_using []

theorem argsAll_ok (s : State) :
    ∃ s', runBlock isa argsAll s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧
      s'.gpr .rdx = s.gpr .r15 + BitVec.ofNat 64 tO ∧ s'.gpr .rcx = s.gpr .r12 ∧
      s'.gpr .r8 = BitVec.ofNat 64 ((s.gpr .r13).toNat / 16) ∧ s'.gpr .r9 = s.gpr .r15 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [argsAll, runBlock_cons, runStep_some, exec, readSrc, execAlu, execShift,
      Option.bind_some, Option.map_some, show 1 ≤ 4 ∧ 4 ≤ 63 from by decide]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, gpr_setFlags]
  · simp [gpr_setReg, gpr_setFlags]
  · simp [gpr_setReg, gpr_setFlags]; rfl
  · simp [gpr_setReg, gpr_setFlags]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ↓reduceIte, shr4]
  · simp [gpr_setReg, gpr_setFlags]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [gpr_setReg, gpr_setFlags]

theorem argsHead_ok (s : State) (hm : 1 ≤ (s.gpr .r13).toNat / 16) :
    ∃ s', runBlock isa argsHead s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧
      s'.gpr .rdx = s.gpr .r15 + BitVec.ofNat 64 tO ∧ s'.gpr .rcx = s.gpr .r12 ∧
      s'.gpr .r8 = BitVec.ofNat 64 ((s.gpr .r13).toNat / 16 - 1) ∧ s'.gpr .r9 = s.gpr .r15 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, cs₁, mem₁, rd₁, wr₁⟩ := argsAll_ok s
  refine ⟨_, by
    rw [argsHead, runBlock_append, run₁, Option.bind_some]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, mem₁, rd₁, wr₁⟩
  · simp [gpr_setReg, rdi₁]
  · simp [gpr_setReg, rsi₁]
  · simp [gpr_setReg, rdx₁]
  · simp [gpr_setReg, rcx₁]
  · simp only [gpr_setReg, ite_true, r8₁]
    rw [show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat hm]
  · simp [gpr_setReg, r9₁]
  · intro r hr
    have := cs₁ r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [gpr_setReg] using this

theorem beq_zero64 {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
    simpa using this
  · intro he; rw [he]; rfl

theorem split_ok (s : State) :
    ∃ s', runBlock isa split s = some s' ∧
      s'.gpr .rax = BitVec.ofNat 64 (16 * ((s.gpr .r13).toNat / 16)) ∧
      s'.gpr .r8 = BitVec.ofNat 64 ((s.gpr .r13).toNat % 16) ∧
      s'.zf = some (decide ((s.gpr .r13).toNat % 16 = 0)) ∧
      (∀ r, r ≠ .rax → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e : s.gpr .r13 - BitVec.ofNat 64 (16 * ((s.gpr .r13).toNat / 16)) =
      BitVec.ofNat 64 ((s.gpr .r13).toNat % 16) := by
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .r13).isLt
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * _) (by omega_using []),
      Nat.mod_eq_of_lt (a := _ % 16) (by omega_using [])]
    omega_using []
  refine ⟨_, by
    simp only [split, runBlock_cons, runStep_some, exec, readSrc, execShift,
      Option.map_some, show 1 ≤ 4 ∧ 4 ≤ 63 from by decide]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, reduceCtorEq, ↓reduceIte, shr4_shl4]
  · simp only [gpr_setReg, gpr_setFlags, reduceCtorEq, ↓reduceIte, shr4_shl4, e]
  · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_setFlags, reduceCtorEq, ↓reduceIte,
      shr4_shl4, e]
    rw [beq_zero64 (by omega_using [])]
  · intro r h₁ h₂; simp [gpr_setReg, gpr_setFlags, h₁, h₂]

theorem lastAddr_ok (s : State) :
    ∃ s', runBlock isa lastAddr s = some s' ∧ s'.gpr .rdx = s.gpr .r12 + s.gpr .rax - 16 ∧
      (∀ r, r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [lastAddr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · intro r h; simp [gpr_setReg, h]

/-- The last whole block, from the bytes of the whole blocks. -/
theorem last_eq (p : Addr) {m : Nat} (hm : 1 ≤ m) (h : 16 * m < 2 ^ 64) :
    p + BitVec.ofNat 64 (16 * m) - 16 = p + BitVec.ofNat 64 (16 * (m - 1)) := by
  rw [show 16 * m = 16 * (m - 1) + 16 by omega, ← Offset.add_add]
  exact BitVec.add_sub_cancel _ _

theorem argsL_ok (s : State) {o : Nat} (ho : BitVec.signExtend 64 (BitVec.ofNat 32 o) = BitVec.ofNat 64 o) :
    ∃ s', runBlock isa (argsL o) s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧
      s'.gpr .rdx = s.gpr .r15 + BitVec.ofNat 64 o ∧ s'.gpr .rcx = s.gpr .rdx ∧
      s'.gpr .r8 = 1 ∧ s'.gpr .r9 = s.gpr .r15 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [argsL, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32, ho]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [gpr_setReg, State.setReg32]

/-! ## The swap -/

theorem swapStep_ok (s : State) {L : Addr} {k b : Nat} (hd : s.gpr .rdx = L)
    (hc : s.gpr .rcx = BitVec.ofNat 64 k) (h8 : s.gpr .r8 = BitVec.ofNat 64 b)
    (w₀ : InRegions s.wr (L + BitVec.ofNat 64 k) 1) (w₁ : InRegions s.wr (L + BitVec.ofNat 64 (16 + k)) 1) :
    ∃ s', runBlock isa swapBody s = some s' ∧
      s'.mem = (s.mem.writeW (L + BitVec.ofNat 64 k) (s.mem (L + BitVec.ofNat 64 (16 + k)))).writeW
        (L + BitVec.ofNat 64 (16 + k)) (s.mem (L + BitVec.ofNat 64 k)) ∧
      s'.gpr .rcx = BitVec.ofNat 64 k + 1 ∧
      s'.zf = some (BitVec.ofNat 64 k + 1 - BitVec.ofNat 64 b == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r9 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ : InRegions (s.rd ++ s.wr) (L + BitVec.ofNat 64 k) 1 :=
    let ⟨r, hr, c⟩ := w₀; ⟨r, List.mem_append_right _ hr, c⟩
  have r₁ : InRegions (s.rd ++ s.wr) (L + BitVec.ofNat 64 (16 + k)) 1 :=
    let ⟨r, hr, c⟩ := w₁; ⟨r, List.mem_append_right _ hr, c⟩
  have ea₀ : s.gpr .rdx + s.gpr .rcx * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = L + BitVec.ofNat 64 k := by
    rw [hd, hc, BitVec.mul_one]; simp
  have ea₁ : s.gpr .rdx + s.gpr .rcx * BitVec.ofNat 64 1 + BitVec.ofInt 64 16 = L + BitVec.ofNat 64 (16 + k) := by
    rw [hd, hc, BitVec.mul_one, BitVec.add_assoc, Nat.add_comm, BitVec.ofNat_add]; rfl
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, swapBody, lo, hi, runBlock_cons, runStep_some, runBlock_nil, exec,
      readSrc, execAlu, State.load8, State.store8, State.ea, Option.bind_some, Option.map_some, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, ea₀, ea₁, r₀, r₁, w₀, w₁]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide),
      BitVec.setWidth_eq]
  · simp [gpr_setReg, hc]
  · simp [gpr_setReg, hc, h8]
  · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]

theorem swap_ok (s : State) {L : Addr} {b : Nat} (hb₀ : 0 < b) (hb : b < 16) (hd : s.gpr .rdx = L)
    (hc : s.gpr .rcx = 0) (h8 : s.gpr .r8 = BitVec.ofNat 64 b)
    (hw : ∀ i < 16 + b, InRegions s.wr (L + BitVec.ofNat 64 i) 1) :
    WP isa swap s fun s' => s'.mem = swapMem s.mem L b ∧
      (∀ r, r ≠ .rax → r ≠ .r9 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block swapBody) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ k, n = b - k ∧ k < b ∧ t.gpr .rcx = BitVec.ofNat 64 k ∧
      t.mem = swapMem s.mem L k ∧
      (∀ r, r ≠ .rax → r ≠ .r9 → r ≠ .rcx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (b - 0) _
    ⟨0, rfl, hb₀, hc, (Proof.AesXts.Unit.swapMem_zero _ _).symm, fun _ _ _ _ => rfl, rfl, rfl⟩
  rintro n t ⟨k, rfl, hk, rcx, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', rcx', zf', g', rd', wr'⟩ := swapStep_ok t (k := k) (b := b)
    (by rw [g _ (by decide) (by decide) (by decide), hd]) rcx (by rw [g _ (by decide) (by decide) (by decide), h8])
    (by rw [wr]; exact hw k (by omega_using [hk])) (by rw [wr]; exact hw (16 + k) (by omega_using [hk]))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hmem : t'.mem = swapMem s.mem L (k + 1) := by
    rw [mem', mem, swapMem_lo _ _ (Nat.le_refl k) (by omega_using [hb, hk]), swapMem_hi _ _ (Nat.le_refl k) (by omega_using [hb, hk]),
      swapMem_step _ _ (by omega_using [hb, hk])]
  have hz : t'.zf = some (decide (k + 1 = b)) := by
    rw [zf', Offset.add_one_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hb, hk]),
      Offset.ofNat_sub_ofNat_beq (by omega_using [hb, hk]) (by omega_using [hb])]
  have gg : ∀ r, r ≠ .rax → r ≠ .r9 → r ≠ .rcx → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₁ h₂ h₃, g r h₁ h₂ h₃]
  by_cases he : k + 1 = b
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], b - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, he], ?_, hmem, gg,
      by rw [rd', rd], by rw [wr', wr]⟩
    rw [rcx', Offset.add_one_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hb, hk])]

/-! ## The next tweak -/

theorem nextT_ok (s : State) {T Z : Addr} (ht : s.gpr .r15 + BitVec.ofNat 64 tO = T)
    (ht8 : s.gpr .r15 + BitVec.ofNat 64 (tO + 8) = T + BitVec.ofNat 64 8)
    (hz : s.gpr .r15 + BitVec.ofNat 64 zO = Z) (hz8 : s.gpr .r15 + BitVec.ofNat 64 (zO + 8) = Z + BitVec.ofNat 64 8)
    (r0 : InRegions (s.rd ++ s.wr) T 8) (r8 : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 8) 8)
    (w0 : InRegions s.wr Z 8) (w8 : InRegions s.wr (Z + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa nextT s = some s' ∧ (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      Frame [⟨Z, 16⟩] s.mem s'.mem ∧ bytesAt s'.mem Z 16 = Spec.Xts.mulAlpha (bytesAt s.mem T 16) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, g₁, rax₁, rcx₁, mem₁, rd₁, wr₁⟩ : ∃ s₁,
      runBlock isa [.mov .rax (.mem (at_ .r15 tO)), .mov .rcx (.mem (at_ .r15 (tO + 8)))] s = some s₁ ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.gpr .rax = s.mem.readW T 64 ∧
      s₁.gpr .rcx = s.mem.readW (T + BitVec.ofNat 64 8) 64 ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
        State.load64, State.ea, offset_nat, Option.map_some, gpr_setReg, mem_setReg, rd_setReg,
        wr_setReg, ht, ht8, r0, r8]
      rfl, ?_⟩
    refine ⟨fun r h₁ h₂ => ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp [gpr_setReg, h₁, h₂]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
  obtain ⟨s₂, run₂, g₂, rax₂, rcx₂, mem₂, rd₂, wr₂⟩ := Proof.AesXts.X86_64.mulA_ok s₁
  have z₂ : s₂.gpr .r15 + BitVec.ofNat 64 zO = Z := by rw [g₂ _ (by decide) (by decide) (by decide),
    g₁ _ (by decide) (by decide), hz]
  have z₂8 : s₂.gpr .r15 + BitVec.ofNat 64 (zO + 8) = Z + BitVec.ofNat 64 8 := by
    rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide), hz8]
  have w₂0 : InRegions s₂.wr Z 8 := by rw [wr₂, wr₁]; exact w0
  have w₂8 : InRegions s₂.wr (Z + BitVec.ofNat 64 8) 8 := by rw [wr₂, wr₁]; exact w8
  refine ⟨_, by
    rw [nextT, runBlock_append, runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some]
    simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, at_, exec, State.store64, State.ea,
      offset_nat, z₂, z₂8, w₂0, w₂8]
    rfl, ?_⟩
  refine ⟨fun r h₁ h₂ h₃ => ?_, ?_, ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · show s₂.gpr r = s.gpr r
    rw [g₂ r h₁ h₂ h₃, g₁ r h₁ h₂]
  · show Frame [⟨Z, 16⟩] s.mem ((s₂.mem.writeW Z (s₂.gpr .rax)).writeW (Z + BitVec.ofNat 64 8) (s₂.gpr .rcx))
    rw [mem₂, mem₁]; exact AesCbc.frame_store2 _ _ _
  · show bytesAt ((s₂.mem.writeW Z (s₂.gpr .rax)).writeW (Z + BitVec.ofNat 64 8) (s₂.gpr .rcx)) Z 16 = _
    rw [Proof.Cmac.bytesAt_store2, rax₂, rcx₂, rax₁, rcx₁, ← Proof.AesXts.X86_64.tw_readW s.mem T,
      ← Proof.AesXts.X86_64.mulAlpha_le8]

end VG.Proof.AesXts.X86_64.Unit

end

end

/-! ### `AesXts.X86_64.Unit.Pre`, which this module and modules that import it used -/

section

/-!
# XTS-AES of data units on x86-64: the arguments of each call

The five calls of a whole-block function the functions make, each with
`XPre` from the precondition (`UPre`), for a state with the permissions
and stack pointer of the entry state and the call's arguments in its
registers:

* `xpre_tweak`: the tweak value `i`, copied to the tweak (`tR`), enciphered
  with `tweak_schedule` from the zero second tweak (`zR`);
* `xpre_blocks`: the first `N` whole blocks of the data, from the tweak;
* `xpre_last`: the last whole block (`L`), from the tweak (`o = tO`) or from
  the second tweak (`o = zO`).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Unit

open VG VG.X86_64
open VG.Impl.AesXts.X86_64Unit (tO zO)

theorem wrap_off (p : Addr) {d n k : Nat} (h : p.toNat + k ≤ 2 ^ 64) (hd : d + n ≤ k) (hn : 0 < n := by decide) :
    (p + BitVec.ofNat 64 d).toNat + n ≤ 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [h, hd, hn]), Nat.mod_eq_of_lt (by omega_using [h, hd, hn])]
  omega_using [h, hd]

section
variable {s₀ s : State} (hp : UPre s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
  (hsp : s.gpr .rsp = s₀.gpr .rsp)
include hp hrd hwr hsp

theorem xpre_tweak (rdi : s.gpr .rdi = K s₀) (rsi : s.gpr .rsi = BitVec.ofNat 64 (R s₀))
    (rdx : s.gpr .rdx = S s₀ + BitVec.ofNat 64 zO) (rcx : s.gpr .rcx = S s₀ + BitVec.ofNat 64 tO)
    (r8 : s.gpr .r8 = BitVec.ofNat 64 1) (r9 : s.gpr .r9 = S s₀) :
    XPre s (K s₀) (S s₀ + BitVec.ofNat 64 zO) (S s₀ + BitVec.ofNat 64 tO) (S s₀) 1 (R s₀) where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := hp.rounds
  n := by decide
  wt := hp.tsch_scr.sub_right (sub_trans z_sub s_sub)
  wd := hp.tsch_scr.sub_right (sub_trans t_sub s_sub)
  ws := hp.tsch_scr.sub_right wk_sub
  td := hp.t_z.symm
  ts := hp.z_wk
  ds := hp.t_wk
  stkW := by rw [stk, hsp]; exact hp.stk_tsch
  stkT := by rw [stk, hsp]; exact hp.stk_scr.sub_right (sub_trans z_sub s_sub)
  stkD := by rw [stk, hsp]; exact hp.stk_scr.sub_right (sub_trans t_sub s_sub)
  stkS := by rw [stk, hsp]; exact hp.stk_scr.sub_right wk_sub
  wrapT := wrap_off _ hp.scr_wrap (by decide)
  wrapD := wrap_off _ hp.scr_wrap (by decide)
  wrapS := by have := hp.scr_wrap; omega_using [this]
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨tschR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, zO, rfl, by simp [zO]⟩
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scrR s₀, by simp, zO, rfl, by simp [zO]⟩
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

theorem xpre_blocks {N : Nat} (hN : 16 * N ≤ Len s₀) (rdi : s.gpr .rdi = W s₀)
    (rsi : s.gpr .rsi = BitVec.ofNat 64 (R s₀)) (rdx : s.gpr .rdx = S s₀ + BitVec.ofNat 64 tO)
    (rcx : s.gpr .rcx = D s₀) (r8 : s.gpr .r8 = BitVec.ofNat 64 N) (r9 : s.gpr .r9 = S s₀) :
    XPre s (W s₀) (S s₀ + BitVec.ofNat 64 tO) (D s₀) (S s₀) N (R s₀) where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := hp.rounds
  n := by have := hp.len_hi; simp only [Spec.Xts.maxBlocks] at this; omega_using [hN, this]
  wt := hp.sch_scr.sub_right (sub_trans t_sub s_sub)
  wd := hp.sch_data.sub_right (Region.sub_prefix hN)
  ws := hp.sch_scr.sub_right wk_sub
  td := (hp.data_scr.symm.sub_left (sub_trans t_sub s_sub)).sub_right (Region.sub_prefix hN)
  ts := hp.t_wk
  ds := (hp.data_scr.sub_left (Region.sub_prefix hN)).sub_right wk_sub
  stkW := by rw [stk, hsp]; exact hp.stk_sch
  stkT := by rw [stk, hsp]; exact hp.stk_scr.sub_right (sub_trans t_sub s_sub)
  stkD := by rw [stk, hsp]; exact hp.stk_data.sub_right (Region.sub_prefix hN)
  stkS := by rw [stk, hsp]; exact hp.stk_scr.sub_right wk_sub
  wrapT := wrap_off _ hp.scr_wrap (by decide)
  wrapD := by have := hp.data_wrap; omega_using [hN, this]
  wrapS := by have := hp.scr_wrap; omega_using [this]
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨dataR s₀, by simp, 0, by simp, by simpa using hN⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨dataR s₀, by simp, 0, by simp, by simpa using hN⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

theorem xpre_last {o : Nat} (ho : o = tO ∨ o = zO) (rdi : s.gpr .rdi = W s₀)
    (rsi : s.gpr .rsi = BitVec.ofNat 64 (R s₀)) (rdx : s.gpr .rdx = S s₀ + BitVec.ofNat 64 o)
    (rcx : s.gpr .rcx = L s₀) (r8 : s.gpr .r8 = BitVec.ofNat 64 1) (r9 : s.gpr .r9 = S s₀) :
    XPre s (W s₀) (S s₀ + BitVec.ofNat 64 o) (L s₀) (S s₀) 1 (R s₀) := by
  have oS : Region.Sub ⟨S s₀ + BitVec.ofNat 64 o, 16⟩ ⟨S s₀, 2208⟩ := by
    rcases ho with rfl | rfl
    · exact t_sub
    · exact z_sub
  have oW : (⟨S s₀ + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint (wkR s₀) := by
    rcases ho with rfl | rfl
    · exact hp.t_wk
    · exact hp.z_wk
  have ol : o + 16 ≤ 2432 := by rcases ho with rfl | rfl <;> decide
  have lS : Region.Sub ⟨L s₀, 16 * 1⟩ (dataR s₀) := hp.l_sub
  exact {
    rdi := rdi
    rsi := rsi
    rdx := rdx
    rcx := rcx
    r8 := r8
    r9 := r9
    rounds := hp.rounds
    n := by decide
    wt := hp.sch_scr.sub_right (sub_trans oS s_sub)
    wd := hp.sch_data.sub_right lS
    ws := hp.sch_scr.sub_right wk_sub
    td := (hp.data_scr.symm.sub_left (sub_trans oS s_sub)).sub_right lS
    ts := oW
    ds := (hp.data_scr.sub_left lS).sub_right wk_sub
    stkW := by rw [stk, hsp]; exact hp.stk_sch
    stkT := by rw [stk, hsp]; exact hp.stk_scr.sub_right (sub_trans oS s_sub)
    stkD := by rw [stk, hsp]; exact hp.stk_data.sub_right lS
    stkS := by rw [stk, hsp]; exact hp.stk_scr.sub_right wk_sub
    wrapT := wrap_off _ hp.scr_wrap ol
    wrapD := hp.l_wrap
    wrapS := by have := hp.scr_wrap; omega_using [this]
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨scrR s₀, by simp, o, rfl, by simpa using ol⟩
      · exact ⟨dataR s₀, by simp, 16 * (M s₀ - 1), rfl, by
          have := len_eq s₀; have := hp.m_pos; simp only [M, B] at *; omega_using [this]⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, o, rfl, by simpa using ol⟩
      · exact ⟨dataR s₀, by simp, 16 * (M s₀ - 1), rfl, by
          have := len_eq s₀; have := hp.m_pos; simp only [M, B] at *; omega_using [this]⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩ }

end

end VG.Proof.AesXts.X86_64.Unit

end

end

/-!
# XTS-AES of data units on x86-64: the tweak, and what every piece keeps

`Inv`: between the calls the code keeps its arguments in `rbx`, `rbp`,
`r12`, `r13` and `r15`, its caller's callee-saved registers in their slots,
and changes memory only in the data, the scratch buffer and the stack below
(`Inv.step`, for any code whose frame is in those). `tweak_wp`: the prologue
and the call enciphering the tweak value leave `T = AES-enc(Key2, i)` in the
tweak (`TwPost`). `fin_wp`: the epilogue restores the registers.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Unit

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesXts.X86_64Unit
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86_64 (modeX86_64 in_rw)
open VG.Spec.Aes (bytesAt)

section
variable (s₀ : State)

/-- The tweak and the second tweak. -/
abbrev Tp : Addr := S s₀ + BitVec.ofNat 64 tO
abbrev Zp : Addr := S s₀ + BitVec.ofNat 64 zO

/-- `T = AES-enc(Key2, i)`. -/
abbrev t0 : List Byte :=
  Spec.Cbc.aesWith (R s₀) (bytesAt s₀.mem (K s₀) (16 * (R s₀ + 1))) (bytesAt s₀.mem (I s₀) 16)

/-- `AES-enc(Key1, ·)` (`enc`) or `AES-dec(Key1, ·)`. -/
abbrev ciph (enc : Bool) : Spec.Cbc.Cipher := ciphOf enc (R s₀) (bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)))

end

/-- What the code keeps between the calls. -/
structure Inv (s₀ s : State) : Prop where
  rbx : s.gpr .rbx = W s₀
  rbp : s.gpr .rbp = s₀.gpr .rdx
  r12 : s.gpr .r12 = D s₀
  r13 : s.gpr .r13 = s₀.gpr .r9
  r15 : s.gpr .r15 = S s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR s₀, scrR s₀, stk s₀] s₀.mem s.mem
  saved : Spill.Saved s.mem (S s₀) s₀.gpr saved

theorem saved_bound : ∀ p ∈ saved, 2208 ≤ p.2 ∧ p.2 + 8 ≤ 2256 := by decide

/-- The registers `Inv` pins. -/
abbrev pinned : List Reg := [.rbx, .rbp, .r12, .r13, .r15, .rsp]

theorem pinned_cs : ∀ r ∈ pinned, r ∈ calleeSaved := by decide

theorem pinned_ne {r : Reg} (h : r ∈ pinned) :
    r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .r8 ∧ r ≠ .r9 := by
  simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem rsi_ofNat (s₀ : State) : BitVec.ofNat 64 (R s₀) = s₀.gpr .rdx := by
  rw [R, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The save, then `rest`, from the state it leaves. -/
theorem save_wp (s : State) {rest : List Instr} {Q : State → Prop}
    (hw : ∀ p ∈ saved, InRegions s.wr (Spill.slot (s.gpr .rax) p.2) 8)
    (h : ∀ s' : State, s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = Spill.saveMem s.mem (s.gpr .rax) s.gpr saved → WP isa (.block rest) s' Q) :
    WP isa (.block (save ++ rest)) s Q := by
  rw [save_eq]
  exact Spill.save_then .rax saved hw (h _ rfl rfl rfl rfl)

theorem cS (s₀ : State) (d n : Nat) (h : d + n ≤ 2432) : (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by omega_using [h])

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- `Inv` across code that keeps the registers and writes only within
`rs`, each in the data, the first 2208 bytes of the scratch buffer or the
stack. -/
theorem Inv.step {s s' : State} (h : Inv s₀ s) {rs : List Region}
    (hrs : ∀ r ∈ rs, Region.Sub r (dataR s₀) ∨ Region.Sub r ⟨S s₀, 2208⟩ ∨ r = stk s₀)
    (hf : Frame rs s.mem s'.mem)
    (hg : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r15, .rsp], s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ s' where
  rbx := by rw [hg _ (by simp), h.rbx]
  rbp := by rw [hg _ (by simp), h.rbp]
  r12 := by rw [hg _ (by simp), h.r12]
  r13 := by rw [hg _ (by simp), h.r13]
  r15 := by rw [hg _ (by simp), h.r15]
  rsp := by rw [hg _ (by simp), h.rsp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  frame := h.frame.trans (hf.sub fun r hr => by
    rcases hrs r hr with h | h | rfl
    · exact ⟨dataR s₀, by simp, h⟩
    · exact ⟨scrR s₀, by simp, sub_trans h s_sub⟩
    · exact ⟨stk s₀, by simp, fun _ h => h⟩)
  saved := h.saved.frame hf fun p hp' r hr =>
    (hp.slots_disj (hrs r hr)).sub_left (slot_sub p.2 (saved_bound p hp').1 (saved_bound p hp').2)

/-- `Inv` across a call of a whole-block function. -/
theorem Inv.call {enc : Bool} {s s' : State} (h : Inv s₀ s) {Wk T Dd : Addr} {N Rr : Nat}
    (hT : Region.Sub ⟨T, 16⟩ ⟨S s₀, 2208⟩)
    (hD : Region.Sub ⟨Dd, 16 * N⟩ (dataR s₀) ∨ Region.Sub ⟨Dd, 16 * N⟩ ⟨S s₀, 2208⟩)
    (hc : XPost enc s Wk T Dd (S s₀) N Rr s') : Inv s₀ s' :=
  Inv.step hp h (rs := [⟨T, 16⟩, ⟨Dd, 16 * N⟩, ⟨S s₀, 2176⟩, stk s]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact .inr (.inl hT)
      · exact hD.elim .inl fun h => .inr (.inl h)
      · exact .inr (.inl (Region.sub_prefix (by decide)))
      · exact .inr (.inr (by rw [stk, stk, h.rsp])))
    hc.frame (fun r hr => hc.saved r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])) hc.rd hc.wr

/-! ## The prologue -/

/-- Before the call enciphering the tweak value. -/
structure ProPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (K s₀) (Zp s₀) (Tp s₀) (S s₀) 1 (R s₀)
  frame : Frame [scrR s₀] s₀.mem s.mem
  ti : bytesAt s.mem (Tp s₀) 16 = bytesAt s₀.mem (I s₀) 16
  z : bytesAt s.mem (Zp s₀) 16 = List.replicate 16 0

theorem ldS_wp : WP isa (.block ldS) s₀ fun s => s = s₀.setReg .rax (S s₀) :=
  WP.of_runBlock ⟨_, ldS_ok s₀ (by
    rw [hp.rd]; exact in_rw (r := argR s₀) (by simp) (Region.contains_self _ _)), rfl⟩

theorem pro_wp : WP isa (.block pro) (s₀.setReg .rax (S s₀)) (ProPost s₀) := by
  have g₁ : ∀ r, r ≠ .rax → (s₀.setReg .rax (S s₀)).gpr r = s₀.gpr r := fun r h => gpr_setReg_of_ne _ _ h
  rw [pro, List.append_assoc]
  refine save_wp _ (fun p hp' => ?_) fun s₂ gpr₂ rd₂ wr₂ mem₂ => ?_
  · have := saved_bound p hp'
    rw [wr_setReg, hp.wr, gpr_setReg_self]
    exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by omega_using [this]))
  rw [WP.block_append_iff]
  obtain ⟨s₃, run₃, r15₃, rbx₃, rbp₃, r12₃, r13₃, g₃, mem₃', rd₃', wr₃'⟩ := setup_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  rw [gpr₂, gpr_setReg_self] at r15₃
  rw [gpr₂] at rbx₃ rbp₃ r12₃ r13₃
  have mem₃ : s₃.mem = Spill.saveMem s₀.mem (S s₀) (s₀.setReg .rax (S s₀)).gpr saved := by
    rw [mem₃', mem₂, mem_setReg, gpr_setReg_self]
  have rd₃ : s₃.rd = s₀.rd := by rw [rd₃', rd₂, rd_setReg]
  have wr₃ : s₃.wr = s₀.wr := by rw [wr₃', wr₂, wr_setReg]
  have rbx₃' : s₃.gpr .rbx = W s₀ := by rw [rbx₃]; exact g₁ _ (by decide)
  have rbp₃' : s₃.gpr .rbp = s₀.gpr .rdx := by rw [rbp₃]; exact g₁ _ (by decide)
  have r12₃' : s₃.gpr .r12 = D s₀ := by rw [r12₃]; exact g₁ _ (by decide)
  have r13₃' : s₃.gpr .r13 = s₀.gpr .r9 := by rw [r13₃]; exact g₁ _ (by decide)
  have k₃ : ∀ r, r ≠ .rax → r ≠ .r15 → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → s₃.gpr r = s₀.gpr r :=
    fun r h₀ h₁ h₂ h₃ h₄ h₅ => by rw [g₃ r h₁ h₂ h₃ h₄ h₅, gpr₂]; exact g₁ r h₀
  have rdwr₃ : s₃.rd ++ s₃.wr = [schR s₀, tschR s₀, iR s₀, argR s₀, dataR s₀, scrR s₀] := by
    rw [rd₃, wr₃, hp.rd, hp.wr]; rfl
  have wr₃'' : s₃.wr = [dataR s₀, scrR s₀] := by rw [wr₃]; exact hp.wr
  have cI0 : (iR s₀).Contains (I s₀) 8 := by
    simpa using Offset.contains_base (I s₀) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
  rw [tweakIn, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₄, run₄, g₄, mem₄, rd₄, wr₄⟩ := AesCbc.X86_64.copy_ok s₃ (dst := .r15) (src := .rcx) (d := tO) (e := 0)
    (P := Tp s₀) (Q := I s₀) (by rw [r15₃]) (by rw [r15₃, ← Offset.add_add])
    (by rw [k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp)
    (by rw [k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by rw [rdwr₃]; exact in_rw (r := iR s₀) (by simp) cI0)
    (by rw [rdwr₃]; exact in_rw (r := iR s₀) (by simp) (Offset.contains_base _ (by decide) (by decide)))
    (by rw [wr₃'']; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [tO])))
    (by rw [wr₃'', Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [tO])))
    (by decide) (by decide)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  rw [WP.block_append_iff]
  have wr₄' : s₄.wr = [dataR s₀, scrR s₀] := by rw [wr₄, wr₃'']
  obtain ⟨s₅, run₅, g₅, mem₅, rd₅, wr₅⟩ := zeroZ_ok s₄ (Z := Zp s₀)
    (by rw [g₄ _ (by decide), r15₃]) (by rw [g₄ _ (by decide), r15₃, ← Offset.add_add])
    (by rw [wr₄']; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [zO])))
    (by rw [wr₄', Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [zO])))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  obtain ⟨s₆, run₆, rdi₆, rsi₆, rdx₆, rcx₆, r8₆, r9₆, cs₆, mem₆, rd₆, wr₆⟩ := tArgs_ok s₅
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  -- The registers.
  have k₅ : ∀ r, r ≠ .rax → s₅.gpr r = s₃.gpr r := fun r h => by rw [g₅ r h, g₄ r h]
  have r15₅ : s₅.gpr .r15 = S s₀ := by rw [k₅ _ (by decide), r15₃]
  have cs (r : Reg) (hr : r ∈ calleeSaved) : s₆.gpr r = s₃.gpr r := by
    rw [cs₆ r hr, k₅ r (AesCbc.X86_64.calleeSaved_ne_rax hr)]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅, rd₄, rd₃]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅, wr₄, wr₃]
  have rsp₆ : s₆.gpr .rsp = s₀.gpr .rsp := by
    rw [cs _ (by simp [calleeSaved]), k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  -- The memory.
  have f₃ : Frame [scrR s₀] s₀.mem s₃.mem := by
    rw [mem₃]
    exact (Spill.saveMem_frame_base s₀.mem (S s₀) _ (L := 2256) saved (fun p hp' => (saved_bound p hp').2)
      (by decide)).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
  have f₄ : Frame [⟨Tp s₀, 16⟩] s₃.mem s₄.mem := by rw [mem₄]; exact AesCbc.copyMem_frame _ _ _
  have f₅ : Frame [⟨Zp s₀, 16⟩] s₄.mem s₅.mem := by rw [mem₅]; exact zero2_frame _ _
  have frame : Frame [scrR s₀] s₀.mem s₆.mem := by
    rw [mem₆]
    refine f₃.trans ((f₄.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, scr_sub (by simp [tO])⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, scr_sub (by simp [zO])⟩
  have sv₃ : Spill.Saved s₃.mem (S s₀) s₀.gpr saved := by
    intro p hp'
    rw [mem₃, Spill.saveMem_saved _ _ _ _ (by decide) p hp']
    refine g₁ _ ?_
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have sdisj : ∀ (r : Region), Region.Sub r ⟨S s₀, 2208⟩ → ∀ p ∈ saved, ∀ r' ∈ [r],
      Region.Disjoint ⟨Spill.slot (S s₀) p.2, 8⟩ r' := fun r hr p hp' r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.slots_disj (.inr (.inl hr))).sub_left (slot_sub p.2 (saved_bound p hp').1 (saved_bound p hp').2)
  have sv₆ : Spill.Saved s₆.mem (S s₀) s₀.gpr saved := by
    rw [mem₆]; exact (sv₃.frame f₄ (sdisj _ t_sub)).frame f₅ (sdisj _ z_sub)
  refine ⟨⟨by rw [cs _ (by simp [calleeSaved]), rbx₃'], by rw [cs _ (by simp [calleeSaved]), rbp₃'],
    by rw [cs _ (by simp [calleeSaved]), r12₃'], by rw [cs _ (by simp [calleeSaved]), r13₃'],
    by rw [cs _ (by simp [calleeSaved]), r15₃], rsp₆, rd₆', wr₆',
    frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩, sv₆⟩, ?_, frame, ?_, ?_⟩
  · refine xpre_tweak hp rd₆' wr₆' rsp₆ ?_ ?_ (by rw [rdx₆, r15₅]) (by rw [rcx₆, r15₅]) r8₆ (by rw [r9₆, r15₅])
    · rw [rdi₆, k₅ _ (by decide), k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [rsi₆, k₅ _ (by decide), rbp₃', rsi_ofNat]
  · rw [mem₆, mem₅, Proof.Cmac.bytesAt_frame (zero2_frame _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.t_z) (by decide), mem₄,
      AesCbc.copyMem_bytes _ (hp.i_scr.symm.sub_left (scr_sub (by simp [tO]))),
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.i_scr) (by decide)]
  · rw [mem₆, mem₅, zero2_bytes]

/-! ## The tweak -/

/-- After the call enciphering the tweak value. -/
structure TwPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  frame : Frame [scrR s₀, stk s₀] s₀.mem s.mem
  t : bytesAt s.mem (Tp s₀) 16 = t0 s₀

theorem UPre.sched_frame {s : State} {rs : List Region} (hf : Frame rs s₀.mem s.mem)
    (hd : ∀ r ∈ rs, r = dataR s₀ ∨ r = scrR s₀ ∨ r = stk s₀ ∨ Region.Sub r (dataR s₀)) :
    bytesAt s.mem (W s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) := by
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega_using [hRb])
  rcases hd r hr with rfl | rfl | rfl | h
  · exact hp.sch_data.sub_left (Region.sub_prefix hRb)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hRb)
  · exact hp.stk_sch.symm.sub_left (Region.sub_prefix hRb)
  · exact (hp.sch_data.sub_left (Region.sub_prefix hRb)).sub_right h

/-- The call enciphering the tweak value. -/
theorem tcall_wp {n : String} {c : Prog isa}
    (ok : ∀ s, (modeX86_64 (AesXts.xtsMode true)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode true)).post s s')
    (nosp : NoSp c) (depth : c.depth ≤ 1) {s₂ : State} (h₂ : ProPost s₀ s₂) :
    WP isa (.call n c) s₂ (TwPost s₀) := by
  refine WP.mono (xts_call true ok nosp depth h₂.pre) fun s₃ c => ?_
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  have eK : bytesAt s₂.mem (K s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (K s₀) (16 * (R s₀ + 1)) :=
    Proof.Cmac.bytesAt_frame h₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.tsch_scr.sub_left (Region.sub_prefix hRb)) (by omega_using [hRb])
  refine ⟨Inv.call hp h₂.inv z_sub (.inr t_sub) c, ?_, ?_⟩
  · refine (h₂.frame.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, sub_trans z_sub s_sub⟩
      · exact ⟨scrR s₀, by simp, sub_trans t_sub s_sub⟩
      · exact ⟨scrR s₀, by simp, wk_sub⟩
      · exact ⟨stk s₀, by simp, by rw [stk, stk, h₂.inv.rsp]; exact fun _ h => h⟩
  · have := Proof.AesXts.Unit.tweak_of (R := R s₀) (w := bytesAt s₂.mem (K s₀) (16 * (R s₀ + 1))) c.out h₂.z
    rw [this, h₂.ti, eK]

theorem tweak_wp {f : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (modeX86_64 (AesXts.xtsMode true)).pre s →
      ∃ t s', Exec isa f.code s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode true)).post s s')
    (nosp : NoSp f.code) (depth : f.code.depth ≤ 1) :
    WP isa (tweak f) s₀ (TwPost s₀) := by
  refine WP.seq (WP.mono (ldS_wp hp) fun s₁ h₁ => ?_)
  subst h₁
  exact WP.seq (WP.mono (pro_wp hp) fun s₂ h₂ => tcall_wp hp ok nosp depth h₂)

/-! ## A call on whole blocks from the tweak -/

/-- After the call on the first `N` whole blocks from the tweak `T`. -/
structure AllPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  out : Spec.Cbc.blocksAt s.mem (D s₀) N =
    Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (D s₀) N)
  tw : bytesAt s.mem (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N
  frame : Frame [⟨D s₀, 16 * N⟩, scrR s₀, stk s₀] s₀.mem s.mem

/-- The memory of `AllPost`. -/
def AllMem (enc : Bool) (s₀ : State) (N : Nat) (m : Mem) : Prop :=
  Spec.Cbc.blocksAt m (D s₀) N = Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (D s₀) N) ∧
    bytesAt m (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N ∧ Frame [⟨D s₀, 16 * N⟩, scrR s₀, stk s₀] s₀.mem m

omit hp in
theorem AllPost.mem {enc : Bool} {N : Nat} {s : State} (h : AllPost enc s₀ N s) : AllMem enc s₀ N s.mem :=
  ⟨h.out, h.tw, h.frame⟩

/-- Before a call on the first `N` whole blocks from the tweak. -/
structure BlocksReady (s₀ : State) (N : Nat) (s : State) : Prop where
  tw : TwPost s₀ s
  pre : XPre s (W s₀) (Tp s₀) (D s₀) (S s₀) N (R s₀)

theorem blocks_call (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (modeX86_64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s s')
    (nosp : NoSp c) (depth : c.depth ≤ 1) {N : Nat} (hN : 16 * N ≤ Len s₀) {s : State} (h : TwPost s₀ s)
    (hpre : XPre s (W s₀) (Tp s₀) (D s₀) (S s₀) N (R s₀)) :
    WP isa (.call n c) s (AllPost enc s₀ N) := by
  refine WP.mono (xts_call enc ok nosp depth hpre) fun s' x => ?_
  have dS : Region.Sub ⟨D s₀, 16 * N⟩ (dataR s₀) := Region.sub_prefix hN
  have eW := hp.sched_frame (h.inv.frame) (fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)
  have eD : Spec.Cbc.blocksAt s.mem (D s₀) N = Spec.Cbc.blocksAt s₀.mem (D s₀) N :=
    blocksAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.data_scr.sub_left dS
      · exact hp.stk_data.symm.sub_left dS) (by have := hp.data_wrap; omega_using [hN, this])
  refine ⟨Inv.call hp h.inv t_sub (.inl dS) x, ?_, ?_, ?_⟩
  · rw [x.out, eW, h.t, eD]
  · rw [x.tw, h.t]
  · refine (h.frame.sub fun r hr => ?_).trans (x.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scrR s₀, by simp, fun _ h => h⟩
      · exact ⟨stk s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, sub_trans t_sub s_sub⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, wk_sub⟩
      · exact ⟨stk s₀, by simp, by rw [stk, stk, h.inv.rsp]; exact fun _ h => h⟩

/-- `TwPost` across code that keeps the callee-saved registers and memory. -/
theorem TwPost.keep {s s' : State} (h : TwPost s₀ s) (hg : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : TwPost s₀ s' where
  inv := Inv.step hp h.inv (rs := []) (fun _ h => by simp at h) (by rw [hm]; exact Frame.refl _ _)
    (fun r hr => hg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])) hrd hwr
  frame := by rw [hm]; exact h.frame
  t := by rw [hm]; exact h.t

/-! ## The epilogue -/

theorem fin_wp {s : State} (h : Inv s₀ s) :
    WP isa (.block restore) s fun s' => gprPreserved s₀ s' ∧ s'.mem = s.mem := by
  rw [restore_eq]
  refine WP.mono (Spill.restore_ok .r15 saved s₀.gpr s (by decide) (fun p hp' => ?_)
    (by rw [h.r15]; exact h.saved)) fun s' ⟨g₁, g₂, mem', _⟩ =>
      ⟨⟨Spill.calleeSaved_ok g₁ g₂ (by decide) h.rsp, ?_⟩, mem'⟩
  · have := saved_bound p hp'
    rw [h.rd, h.wr, hp.rd, hp.wr, h.r15]
    exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by omega_using [this]))
  · rw [mem']
    refine h.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_data
    · exact hp.ret_scr
    · exact Offset.base_disjoint_below _ (by decide)

/-! ## Bytes of the data a call keeps -/

/-- The bytes of a part `X` of the data that a call on other blocks keeps. -/
theorem call_keeps {enc : Bool} {s s' : State} {Wk T Dd : Addr} {N Rr : Nat} {X : Region}
    (hX : Region.Sub X (dataR s₀)) (hXD : X.Disjoint ⟨Dd, 16 * N⟩) (hT : Region.Sub ⟨T, 16⟩ (scrR s₀))
    (hrsp : s.gpr .rsp = s₀.gpr .rsp) (c : XPost enc s Wk T Dd (S s₀) N Rr s') (hn : X.len ≤ 2 ^ 64) :
    bytesAt s'.mem X.base X.len = bytesAt s.mem X.base X.len :=
  Proof.Cmac.bytesAt_frame c.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hp.data_scr.sub_left hX).sub_right hT
    · exact hXD
    · exact (hp.data_scr.sub_left hX).sub_right wk_sub
    · rw [stk, hrsp]; exact hp.stk_data.symm.sub_left hX) hn

end

end VG.Proof.AesXts.X86_64.Unit
