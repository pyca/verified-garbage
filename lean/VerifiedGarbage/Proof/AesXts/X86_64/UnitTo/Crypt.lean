module

public import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Contract
public import VerifiedGarbage.Proof.AesXts.X86_64.To.Contract
public import VerifiedGarbage.Impl.AesXts.X86_64UnitTo
public import VerifiedGarbage.Spec.Xts.OutOfPlace
public import VerifiedGarbage.Proof.AesXts.Unit
public import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Call
public import VerifiedGarbage.Proof.Framework.X86_64.Spill
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.AesXts.X86_64.Variant
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Steps
import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Run
import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Pre
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesCbc.X86_64.Body
import VerifiedGarbage.Proof.AesCbc.X86_64.Block
import VerifiedGarbage.Proof.AesCbc.X86_64.Loop
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Copy
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesXts.X86_64.Steps
import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# XTS-AES of data units on x86-64, out of place: correctness

The contract of the out-of-place data-unit functions on x86-64, the runs of
their parts, and `encrypt_wp` and `decrypt_wp`: section by section below.
-/

@[expose] public section

/-! ## XTS-AES of data units out of place on x86-64: the contract the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Xts/OutOfPlace.lean`, which imply `unitToX86_64`
(`Verified.lean`): `(schedule = rdi, tweak_schedule = rsi, rounds = rdx,
i = rcx, src = r8, len = r9, dst = [rsp + 8], dst_len = [rsp + 16],
scratch = [rsp + 24])`. The deepest call, of an out-of-place whole-block
function that copies and then calls an in-place one, which calls a block
function, uses the 24 bytes below the stack pointer (`stk3`), which no
buffer overlaps, nor the return address (`retR`).

`UPre` names the facts of the precondition; the regions of the scratch
buffer are those of the in-place functions.
-/

namespace VG.Proof.AesXts.X86_64.UnitTo

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesXts.X86_64.To (stk3)

section
variable (s : State)

abbrev W : Addr := s.gpr .rdi
abbrev K : Addr := s.gpr .rsi
abbrev R : Nat := (s.gpr .rdx).toNat
abbrev I : Addr := s.gpr .rcx
abbrev Sr : Addr := s.gpr .r8
abbrev Len : Nat := (s.gpr .r9).toNat
/-- `dst`, the first stack argument. -/
abbrev D : Addr := stackArg s 0
/-- `dst_len`, the second. -/
abbrev DLen : Nat := (stackArg s 1).toNat
/-- The scratch buffer, the third. -/
abbrev S : Addr := stackArg s 2

abbrev schR : Region := ⟨W s, 240⟩
abbrev tschR : Region := ⟨K s, 240⟩
abbrev iR : Region := ⟨I s, 16⟩
abbrev srcR : Region := ⟨Sr s, Len s⟩
abbrev dstR : Region := ⟨D s, DLen s⟩
abbrev scrR : Region := ⟨S s, 2432⟩
abbrev argR : Region := ⟨stackArgAddr s 0, 24⟩
abbrev retR : Region := ⟨s.gpr .rsp, 8⟩

/-- The tweak, the second tweak, and the working space of the calls, in the
scratch buffer. -/
abbrev tR : Region := ⟨S s + BitVec.ofNat 64 Impl.AesXts.X86_64Unit.tO, 16⟩
abbrev zR : Region := ⟨S s + BitVec.ofNat 64 Impl.AesXts.X86_64Unit.zO, 16⟩
abbrev wkR : Region := ⟨S s, 2176⟩

/-- The number of whole blocks, the bytes after them, and the last whole
block of `dst`. -/
abbrev M : Nat := Len s / 16
abbrev B : Nat := Len s % 16
abbrev L : Addr := D s + BitVec.ofNat 64 (16 * (M s - 1))

end

/-- What the functions need: the permissions, the buffers apart, the stack
the calls use apart from them, `rounds` of 10, 12 or 14, a data unit of 16
bytes to 2²⁰ blocks, and an output as long. -/
def unitPre (s : State) : Prop :=
  s.rd = [schR s, tschR s, iR s, srcR s, argR s] ∧ s.wr = [dstR s, scrR s] ∧
    (schR s).Disjoint (dstR s) ∧ (schR s).Disjoint (scrR s) ∧ (tschR s).Disjoint (dstR s) ∧
    (tschR s).Disjoint (scrR s) ∧ (iR s).Disjoint (dstR s) ∧ (iR s).Disjoint (scrR s) ∧
    (srcR s).Disjoint (dstR s) ∧ (srcR s).Disjoint (scrR s) ∧
    (dstR s).Disjoint (scrR s) ∧ (dstR s).Disjoint (argR s) ∧ (scrR s).Disjoint (argR s) ∧
    (retR s).Disjoint (dstR s) ∧ (retR s).Disjoint (scrR s) ∧
    (stk3 s).Disjoint (schR s) ∧ (stk3 s).Disjoint (tschR s) ∧ (stk3 s).Disjoint (iR s) ∧
    (stk3 s).Disjoint (srcR s) ∧ (stk3 s).Disjoint (dstR s) ∧ (stk3 s).Disjoint (scrR s) ∧
    (I s).toNat + 16 ≤ 2 ^ 64 ∧ (Sr s).toNat + Len s ≤ 2 ^ 64 ∧ (D s).toNat + DLen s ≤ 2 ^ 64 ∧
    (S s).toNat + 2432 ≤ 2 ^ 64 ∧
    24 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64 ∧
    (R s = 10 ∨ R s = 12 ∨ R s = 14) ∧ 16 ≤ Len s ∧ Len s ≤ 16 * Spec.Xts.maxBlocks ∧ DLen s = Len s

def unitPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    stackArg s₁ 2 = stackArg s₂ 2

/-- `vg_aes_xts_encrypt_unit_to` (`enc`) or `vg_aes_xts_decrypt_unit_to`. -/
def unitToX86_64 (enc : Bool) : Contract isa where
  pre := unitPre
  post s s' := ∀ key, Spec.Xts.KeySchedules s.mem (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx).toNat key →
    Unit.xtsOf enc key (bytesAt s.mem (s.gpr .rcx) 16) (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) =
      some (bytesAt s'.mem (stackArg s 0) (s.gpr .r9).toNat)
  pub := unitPub

/-- The precondition, by name. -/
structure UPre (s : State) : Prop where
  rd : s.rd = [schR s, tschR s, iR s, srcR s, argR s]
  wr : s.wr = [dstR s, scrR s]
  sch_dst : (schR s).Disjoint (dstR s)
  sch_scr : (schR s).Disjoint (scrR s)
  tsch_dst : (tschR s).Disjoint (dstR s)
  tsch_scr : (tschR s).Disjoint (scrR s)
  i_dst : (iR s).Disjoint (dstR s)
  i_scr : (iR s).Disjoint (scrR s)
  src_dst : (srcR s).Disjoint (dstR s)
  src_scr : (srcR s).Disjoint (scrR s)
  dst_scr : (dstR s).Disjoint (scrR s)
  dst_arg : (dstR s).Disjoint (argR s)
  scr_arg : (scrR s).Disjoint (argR s)
  ret_dst : (retR s).Disjoint (dstR s)
  ret_scr : (retR s).Disjoint (scrR s)
  stk_sch : (stk3 s).Disjoint (schR s)
  stk_tsch : (stk3 s).Disjoint (tschR s)
  stk_i : (stk3 s).Disjoint (iR s)
  stk_src : (stk3 s).Disjoint (srcR s)
  stk_dst : (stk3 s).Disjoint (dstR s)
  stk_scr : (stk3 s).Disjoint (scrR s)
  i_wrap : (I s).toNat + 16 ≤ 2 ^ 64
  src_wrap : (Sr s).toNat + Len s ≤ 2 ^ 64
  dst_wrap : (D s).toNat + DLen s ≤ 2 ^ 64
  scr_wrap : (S s).toNat + 2432 ≤ 2 ^ 64
  rsp_lo : 24 ≤ (s.gpr .rsp).toNat
  rsp_hi : (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64
  rounds : R s = 10 ∨ R s = 12 ∨ R s = 14
  len_lo : 16 ≤ Len s
  len_hi : Len s ≤ 16 * Spec.Xts.maxBlocks
  dlen : DLen s = Len s

theorem UPre.of {s : State} (h : unitPre s) : UPre s :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x, y, z, a', b', c', d', e', f'⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x, y, z, a', b', c', d', e', f'⟩

/-! ## Regions -/

section
variable {s : State} (hp : UPre s)
include hp

theorem UPre.m_pos : 1 ≤ M s := by have := hp.len_lo; simp only [M]; omega

theorem UPre.m_lt : M s < 2 ^ 21 := by
  have := hp.len_hi; simp only [M, Spec.Xts.maxBlocks] at *; omega

omit hp in
theorem len_eq (s : State) : Len s = 16 * M s + B s := by simp only [M, B]; omega

/-- `dst`, as long as `src`. -/
theorem UPre.dstR_eq : dstR s = ⟨D s, Len s⟩ := by rw [dstR, hp.dlen]

theorem UPre.dst_wrap' : (D s).toNat + Len s ≤ 2 ^ 64 := by rw [← hp.dlen]; exact hp.dst_wrap

omit hp in
theorem scr_sub {d n : Nat} (h : d + n ≤ 2432) : Region.Sub ⟨S s + BitVec.ofNat 64 d, n⟩ (scrR s) :=
  Offset.sub_base _ h

theorem UPre.dst_sub {d n : Nat} (h : d + n ≤ Len s) : Region.Sub ⟨D s + BitVec.ofNat 64 d, n⟩ (dstR s) := by
  rw [hp.dstR_eq]; exact Offset.sub_base _ h

omit hp in
theorem src_sub {d n : Nat} (h : d + n ≤ Len s) : Region.Sub ⟨Sr s + BitVec.ofNat 64 d, n⟩ (srcR s) :=
  Offset.sub_base _ h

omit hp in
theorem wk_sub : Region.Sub (wkR s) (scrR s) := Region.sub_prefix (by decide)

theorem UPre.t_wk : (tR s).Disjoint (wkR s) :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; simp only [Impl.AesXts.X86_64Unit.tO]; omega)

theorem UPre.z_wk : (zR s).Disjoint (wkR s) :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; simp only [Impl.AesXts.X86_64Unit.zO]; omega)

theorem UPre.t_z : (tR s).Disjoint (zR s) :=
  Offset.disjoint _ (by simp only [Impl.AesXts.X86_64Unit.tO, Impl.AesXts.X86_64Unit.zO]; omega)
    (by have := hp.scr_wrap; simp only [Impl.AesXts.X86_64Unit.tO]; omega)
    (by have := hp.scr_wrap; simp only [Impl.AesXts.X86_64Unit.zO]; omega)

omit hp in
/-- The slots of the saved registers. -/
theorem slot_sub (d : Nat) (h₁ : 2208 ≤ d) (h₂ : d + 8 ≤ 2256) :
    Region.Sub ⟨S s + BitVec.ofNat 64 d, 8⟩ ⟨S s + BitVec.ofNat 64 2208, 48⟩ :=
  Offset.sub _ h₁ (by omega)

/-- Everything the code writes but the slots lies within `dst`, the first
2208 bytes of the scratch buffer, or the stack below. -/
theorem UPre.slots_disj {r : Region}
    (hr : Region.Sub r (dstR s) ∨ Region.Sub r ⟨S s, 2208⟩ ∨ Region.Sub r (stk3 s)) :
    (⟨S s + BitVec.ofNat 64 2208, 48⟩ : Region).Disjoint r := by
  have slot : Region.Sub ⟨S s + BitVec.ofNat 64 2208, 48⟩ (scrR s) := scr_sub (by decide)
  rcases hr with h | h | h
  · exact (hp.dst_scr.symm.sub_left slot).sub_right h
  · exact (Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)).sub_right h
  · exact (hp.stk_scr.symm.sub_left slot).sub_right h

omit hp in
theorem t_sub : Region.Sub (tR s) ⟨S s, 2208⟩ := Offset.sub_base _ (by decide)
omit hp in
theorem z_sub : Region.Sub (zR s) ⟨S s, 2208⟩ := Offset.sub_base _ (by decide)
omit hp in
theorem wk_sub' : Region.Sub (wkR s) ⟨S s, 2208⟩ := Region.sub_prefix (by decide)
omit hp in
theorem s_sub : Region.Sub ⟨S s, 2208⟩ (scrR s) := Region.sub_prefix (by decide)

theorem UPre.wrapD : (D s).toNat + 16 * M s + B s ≤ 2 ^ 64 := by
  have := hp.dst_wrap'; have := len_eq s; omega

theorem UPre.l_sub : Region.Sub ⟨L s, 16⟩ (dstR s) :=
  hp.dst_sub (by have := len_eq s; have := hp.m_pos; omega)

theorem UPre.l_wrap : (L s).toNat + 16 ≤ 2 ^ 64 := by
  have := hp.dst_wrap'; have := len_eq s; have := hp.m_pos
  rw [L, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * (M s - 1)) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem UPre.blocks_sub {N : Nat} (h : N ≤ M s) : Region.Sub ⟨D s, 16 * N⟩ (dstR s) :=
  by rw [hp.dstR_eq]; exact Region.sub_prefix (by have := len_eq s; omega)

theorem UPre.lb_sub : Region.Sub ⟨L s, 16 + B s⟩ (dstR s) :=
  hp.dst_sub (by have := len_eq s; have := hp.m_pos; omega)

theorem UPre.tl_eq : L s + 16 = D s + BitVec.ofNat 64 (16 * M s) := by
  rw [L, Proof.AesXts.Unit.add16, show 16 * (M s - 1) + 16 = 16 * M s by have := hp.m_pos; omega]

theorem UPre.tl_sub : Region.Sub ⟨L s + 16, B s⟩ (dstR s) := by
  rw [hp.tl_eq]; exact hp.dst_sub (by have := len_eq s; omega)

theorem UPre.hd_lb : (⟨D s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s, 16 + B s⟩ :=
  Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.wrapD; have := hp.m_pos; omega)

theorem UPre.hd_l : (⟨D s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s, 16⟩ :=
  hp.hd_lb.sub_right (Region.sub_prefix (by omega))

omit hp in
theorem tl_l : (⟨L s + 16, B s⟩ : Region).Disjoint ⟨L s, 16⟩ :=
  Offset.disjoint_base (L s) (d := 16) (n := B s) (k := 16) (Nat.le_refl _) (by simp only [B]; omega)

theorem UPre.tl_blocks : (⟨L s + 16, B s⟩ : Region).Disjoint ⟨D s, 16 * M s⟩ := by
  rw [hp.tl_eq]
  exact Offset.disjoint_base _ (Nat.le_refl _) (by have := hp.wrapD; omega)

end

end VG.Proof.AesXts.X86_64.UnitTo

/-! ## XTS-AES of data units out of place on x86-64: the tweak, the calls, and what every piece keeps

`Inv`: between the calls the code keeps its arguments in `rbx`, `rbp`,
`r12` (`dst`), `r13`, `r14` (`src`) and `r15`, its caller's callee-saved
registers in their slots, and changes memory only in `dst`, the scratch
buffer and the stack below (`Inv.step`). `tweak_wp`: the prologue and the
call enciphering the tweak value leave `T = AES-enc(Key2, i)` in the tweak
(`TwPost`). `blocks_call`: the out-of-place call on the first `N` whole
blocks leaves their XTS at `dst` (`AllPost`); `copyRest_wp`: the copy of the
bytes after the first `h` whole blocks from `src` to `dst`. `vmem`: the
memory with `dst` holding the data unit at `src`, which the in-place lemmas
of ciphertext stealing (`Proof/AesXts/Unit.lean`) take as the memory on
entry. `fin_wp`: the epilogue restores the registers.
-/

namespace VG.Proof.AesXts.X86_64.UnitTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesXts.X86_64Unit
open VG.Impl.AesXts.X86_64UnitTo renaming ldS → ldSTo, setup → setupTo, pro → proTo, tweak → tweakTo,
  argsAll → argsAllTo, argsHead → argsHeadTo, encrypt → encryptTo, decrypt → decryptTo
open VG.Impl.AesXts.X86_64UnitTo (copyRest wholeBytes headBytes decStealTail XtsTo)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86_64 (modeX86_64 in_rw offset_nat)
open VG.Proof.AesXts.X86_64.To (stk3 XtPre XtPost xtsToX86_64 xtsTo_call)
open VG.Proof.AesXts.X86_64.Unit (XPre XPost xts_call)
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

/-- The memory with the data unit at `src` copied to `dst`: what the
in-place functions would start from. -/
def vmem : Mem := WriteBytes.writeBytes s₀.mem (D s₀) (bytesAt s₀.mem (Sr s₀) (Len s₀))

end

/-- What the code keeps between the calls. -/
structure Inv (s₀ s : State) : Prop where
  rbx : s.gpr .rbx = W s₀
  rbp : s.gpr .rbp = s₀.gpr .rdx
  r12 : s.gpr .r12 = D s₀
  r13 : s.gpr .r13 = s₀.gpr .r9
  r14 : s.gpr .r14 = Sr s₀
  r15 : s.gpr .r15 = S s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dstR s₀, scrR s₀, stk3 s₀] s₀.mem s.mem
  saved : Spill.Saved s.mem (S s₀) s₀.gpr saved

/-- The registers `Inv` pins. -/
abbrev pinned : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]

theorem saved_bound : ∀ p ∈ saved, 2208 ≤ p.2 ∧ p.2 + 8 ≤ 2256 := by decide

theorem pinned_cs : ∀ r ∈ pinned, r ∈ calleeSaved := by decide

theorem pinned_ne {r : Reg} (h : r ∈ pinned) :
    r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .rsi ∧ r ≠ .rdi ∧ r ≠ .r10 := by
  simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem rsi_ofNat (s₀ : State) : BitVec.ofNat 64 (R s₀) = s₀.gpr .rdx := by
  rw [R, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem cS (s₀ : State) (d n : Nat) (h : d + n ≤ 2432) : (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by omega)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.cS' {d n : Nat} (h : d + n ≤ 2432) : (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by have := hp.scr_wrap; omega)

/-- `Inv` across code that keeps the pinned registers and writes only
within `rs`, each in `dst`, the first 2208 bytes of the scratch buffer or
the stack. -/
theorem Inv.step {s s' : State} (h : Inv s₀ s) {rs : List Region}
    (hrs : ∀ r ∈ rs, Region.Sub r (dstR s₀) ∨ Region.Sub r ⟨S s₀, 2208⟩ ∨ Region.Sub r (stk3 s₀))
    (hf : Frame rs s.mem s'.mem) (hg : ∀ r ∈ pinned, s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ s' where
  rbx := by rw [hg _ (by simp), h.rbx]
  rbp := by rw [hg _ (by simp), h.rbp]
  r12 := by rw [hg _ (by simp), h.r12]
  r13 := by rw [hg _ (by simp), h.r13]
  r14 := by rw [hg _ (by simp), h.r14]
  r15 := by rw [hg _ (by simp), h.r15]
  rsp := by rw [hg _ (by simp), h.rsp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  frame := h.frame.trans (hf.sub fun r hr => by
    rcases hrs r hr with h | h | h
    · exact ⟨dstR s₀, by simp, h⟩
    · exact ⟨scrR s₀, by simp, Unit.sub_trans h s_sub⟩
    · exact ⟨stk3 s₀, by simp, h⟩)
  saved := h.saved.frame hf fun p hp' r hr =>
    (hp.slots_disj (hrs r hr)).sub_left (slot_sub p.2 (saved_bound p hp').1 (saved_bound p hp').2)

omit hp in
theorem stk_sub3 {s : State} (h : s.gpr .rsp = s₀.gpr .rsp) : Region.Sub (Unit.stk s) (stk3 s₀) := by
  rw [Unit.stk, stk3, h]; exact below_sub (by decide) (by decide)

/-- `Inv` across a call of an in-place whole-block function. -/
theorem Inv.call {enc : Bool} {s s' : State} (h : Inv s₀ s) {Wk T Dd : Addr} {N Rr : Nat}
    (hT : Region.Sub ⟨T, 16⟩ ⟨S s₀, 2208⟩)
    (hD : Region.Sub ⟨Dd, 16 * N⟩ (dstR s₀) ∨ Region.Sub ⟨Dd, 16 * N⟩ ⟨S s₀, 2208⟩)
    (hc : XPost enc s Wk T Dd (S s₀) N Rr s') : Inv s₀ s' :=
  Inv.step hp h (rs := [⟨T, 16⟩, ⟨Dd, 16 * N⟩, ⟨S s₀, 2176⟩, Unit.stk s]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact .inr (.inl hT)
      · exact hD.elim .inl fun h => .inr (.inl h)
      · exact .inr (.inl (Region.sub_prefix (by decide)))
      · exact .inr (.inr (stk_sub3 h.rsp)))
    hc.frame (fun r hr => hc.saved r (pinned_cs r hr)) hc.rd hc.wr

/-- `Inv` across a call of an out-of-place whole-block function. -/
theorem Inv.callTo {enc : Bool} {s s' : State} (h : Inv s₀ s) {Wk T Sr' : Addr} {N Rr : Nat}
    (hT : Region.Sub ⟨T, 16⟩ ⟨S s₀, 2208⟩) (hD : Region.Sub ⟨D s₀, 16 * N⟩ (dstR s₀))
    (hc : XtPost enc s Wk T Sr' (D s₀) (S s₀) N Rr s') : Inv s₀ s' :=
  Inv.step hp h (rs := [⟨T, 16⟩, ⟨D s₀, 16 * N⟩, ⟨S s₀, 2176⟩, stk3 s]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact .inr (.inl hT)
      · exact .inl hD
      · exact .inr (.inl (Region.sub_prefix (by decide)))
      · exact .inr (.inr (by rw [stk3, stk3, h.rsp]; exact fun _ h => h)))
    hc.frame (fun r hr => hc.saved r (pinned_cs r hr)) hc.rd hc.wr

theorem UPre.rdwr {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    s.rd ++ s.wr = [schR s₀, tschR s₀, iR s₀, srcR s₀, argR s₀, dstR s₀, scrR s₀] := by
  rw [hrd, hwr, hp.rd, hp.wr]; rfl

theorem UPre.wr' {s : State} (hwr : s.wr = s₀.wr) : s.wr = [dstR s₀, scrR s₀] := by rw [hwr, hp.wr]

/-- The stack arguments are readable. -/
theorem UPre.argAddr_toNat : (stackArgAddr s₀ 0).toNat = (s₀.gpr .rsp).toNat + 8 := by
  have := hp.rsp_hi
  unfold stackArgAddr
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * (0 + 1)) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem UPre.inArg {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 8 ≤ 24) :
    InRegions (s.rd ++ s.wr) (stackArgAddr s₀ 0 + BitVec.ofNat 64 d) 8 := by
  rw [hp.rdwr hrd hwr]
  exact in_rw (r := argR s₀) (by simp) (Offset.contains_base _ hd (by
    omega))

omit hp in
theorem arg_add (s : State) (d : Nat) :
    stackArgAddr s 0 + BitVec.ofNat 64 d = s.gpr .rsp + BitVec.ofNat 64 (8 + d) := by
  rw [stackArgAddr, BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## The prologue -/

omit hp in
theorem ldS_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 24) 8) :
    runBlock isa ldSTo s = some (s.setReg .rax (s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 24) 64)) := by
  simp only [ldSTo, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea,
    offset_nat, hr, ite_true, Option.map_some]

theorem ldS_wp : WP isa (.block ldSTo) s₀ fun s => s = s₀.setReg .rax (S s₀) :=
  WP.of_runBlock ⟨_, ldS_ok s₀ (by
    have := hp.inArg (s := s₀) rfl rfl (d := 16) (by decide)
    rwa [arg_add] at this), rfl⟩

omit hp in
theorem setup_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa setupTo s = some s' ∧
      s'.gpr .r15 = s.gpr .rax ∧ s'.gpr .rbx = s.gpr .rdi ∧ s'.gpr .rbp = s.gpr .rdx ∧
      s'.gpr .r12 = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 ∧ s'.gpr .r13 = s.gpr .r9 ∧
      s'.gpr .r14 = s.gpr .r8 ∧
      (∀ r, r ≠ .r15 → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [setupTo, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea,
      offset_nat, gpr_setReg, rd_setReg, wr_setReg, mem_setReg, reduceCtorEq, ↓reduceIte, hr, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · intro r h₁ h₂ h₃ h₄ h₅ h₆; simp [gpr_setReg, h₁, h₂, h₃, h₄, h₅, h₆]

/-- Before the call enciphering the tweak value. -/
structure ProPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (K s₀) (Zp s₀) (Tp s₀) (S s₀) 1 (R s₀)
  frame : Frame [scrR s₀] s₀.mem s.mem
  ti : bytesAt s.mem (Tp s₀) 16 = bytesAt s₀.mem (I s₀) 16
  z : bytesAt s.mem (Zp s₀) 16 = List.replicate 16 0

theorem xpre_tweak {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hsp : s.gpr .rsp = s₀.gpr .rsp)
    (rdi : s.gpr .rdi = K s₀) (rsi : s.gpr .rsi = BitVec.ofNat 64 (R s₀))
    (rdx : s.gpr .rdx = S s₀ + BitVec.ofNat 64 zO) (rcx : s.gpr .rcx = S s₀ + BitVec.ofNat 64 tO)
    (r8 : s.gpr .r8 = BitVec.ofNat 64 1) (r9 : s.gpr .r9 = S s₀) :
    XPre s (K s₀) (Zp s₀) (Tp s₀) (S s₀) 1 (R s₀) where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := hp.rounds
  n := by decide
  wt := hp.tsch_scr.sub_right (Unit.sub_trans z_sub s_sub)
  wd := hp.tsch_scr.sub_right (Unit.sub_trans t_sub s_sub)
  ws := hp.tsch_scr.sub_right wk_sub
  td := hp.t_z.symm
  ts := hp.z_wk
  ds := hp.t_wk
  stkW := hp.stk_tsch.sub_left (stk_sub3 hsp)
  stkT := (hp.stk_scr.sub_right (Unit.sub_trans z_sub s_sub)).sub_left (stk_sub3 hsp)
  stkD := (hp.stk_scr.sub_right (Unit.sub_trans t_sub s_sub)).sub_left (stk_sub3 hsp)
  stkS := (hp.stk_scr.sub_right wk_sub).sub_left (stk_sub3 hsp)
  wrapT := Unit.wrap_off _ hp.scr_wrap (by decide)
  wrapD := Unit.wrap_off _ hp.scr_wrap (by decide)
  wrapS := by have := hp.scr_wrap; omega
  reads := by
    rw [hp.rdwr hrd hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨tschR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, zO, rfl, by simp [zO]⟩
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hp.wr' hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scrR s₀, by simp, zO, rfl, by simp [zO]⟩
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

theorem pro_wp : WP isa (.block proTo) (s₀.setReg .rax (S s₀)) (ProPost s₀) := by
  have g₁ : ∀ r, r ≠ .rax → (s₀.setReg .rax (S s₀)).gpr r = s₀.gpr r := fun r h => gpr_setReg_of_ne _ _ h
  rw [proTo, List.append_assoc]
  refine Unit.save_wp _ (fun p hp' => ?_) fun s₂ gpr₂ rd₂ wr₂ mem₂ => ?_
  · have := saved_bound p hp'
    rw [wr_setReg, hp.wr, gpr_setReg_self]
    exact in_rw (r := scrR s₀) (by simp) (hp.cS' (by omega))
  rw [WP.block_append_iff]
  have rsp₂ : s₂.gpr .rsp = s₀.gpr .rsp := by rw [gpr₂]; exact g₁ _ (by decide)
  obtain ⟨s₃, run₃, r15₃, rbx₃, rbp₃, r12₃, r13₃, r14₃, g₃, mem₃', rd₃', wr₃'⟩ := setup_ok s₂ (by
    rw [rsp₂, rd₂, wr₂, rd_setReg, wr_setReg]
    have := hp.inArg (s := s₀) rfl rfl (d := 0) (by decide)
    rwa [arg_add] at this)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  rw [gpr₂, gpr_setReg_self] at r15₃
  rw [gpr₂] at rbx₃ rbp₃ r13₃ r14₃
  rw [rsp₂] at r12₃
  have mem₃ : s₃.mem = Spill.saveMem s₀.mem (S s₀) (s₀.setReg .rax (S s₀)).gpr saved := by
    rw [mem₃', mem₂, mem_setReg, gpr_setReg_self]
  have rd₃ : s₃.rd = s₀.rd := by rw [rd₃', rd₂, rd_setReg]
  have wr₃ : s₃.wr = s₀.wr := by rw [wr₃', wr₂, wr_setReg]
  have fs : Frame [scrR s₀] s₀.mem (Spill.saveMem s₀.mem (S s₀) (s₀.setReg .rax (S s₀)).gpr saved) :=
    (Spill.saveMem_frame_base s₀.mem (S s₀) _ (L := 2256) saved (fun p hp' => (saved_bound p hp').2)
      (by decide)).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
  have f₃ : Frame [scrR s₀] s₀.mem s₃.mem := by rw [mem₃]; exact fs
  have rbx₃' : s₃.gpr .rbx = W s₀ := by rw [rbx₃]; exact g₁ _ (by decide)
  have rbp₃' : s₃.gpr .rbp = s₀.gpr .rdx := by rw [rbp₃]; exact g₁ _ (by decide)
  have r12₃' : s₃.gpr .r12 = D s₀ := by
    have hc : (argR s₀).Contains (s₀.gpr .rsp + BitVec.ofNat 64 8) (64 / 8) := by
      have := Offset.contains_base (stackArgAddr s₀ 0) (d := 0) (n := 8) (k := 24) (by decide) (by decide)
      rwa [BitVec.add_zero] at this
    rw [r12₃, mem₂, mem_setReg, gpr_setReg_self, fs.readW (r := argR s₀) hc (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.scr_arg.symm) (by decide)]
    rfl
  have r13₃' : s₃.gpr .r13 = s₀.gpr .r9 := by rw [r13₃]; exact g₁ _ (by decide)
  have r14₃' : s₃.gpr .r14 = Sr s₀ := by rw [r14₃]; exact g₁ _ (by decide)
  have k₃ : ∀ r, r ≠ .rax → r ≠ .r15 → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 →
      s₃.gpr r = s₀.gpr r :=
    fun r h₀ h₁ h₂ h₃ h₄ h₅ h₆ => by rw [g₃ r h₁ h₂ h₃ h₄ h₅ h₆, gpr₂]; exact g₁ r h₀
  have rdwr₃ := hp.rdwr rd₃ wr₃
  have wr₃'' : s₃.wr = [dstR s₀, scrR s₀] := hp.wr' wr₃
  have iw := hp.i_wrap
  have cI0 : (iR s₀).Contains (I s₀) 8 := by
    have := Offset.contains_base (I s₀) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  rw [tweakIn, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₄, run₄, g₄, mem₄, rd₄, wr₄⟩ := AesCbc.X86_64.copy_ok s₃ (dst := .r15) (src := .rcx) (d := tO) (e := 0)
    (P := Tp s₀) (Q := I s₀) (by rw [r15₃]) (by rw [r15₃, ← Offset.add_add])
    (by rw [k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp)
    (by rw [k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by rw [rdwr₃]; exact in_rw (r := iR s₀) (by simp) cI0)
    (by rw [rdwr₃]; exact in_rw (r := iR s₀) (by simp) (Offset.contains_base _ (by decide) (by decide)))
    (by rw [wr₃'']; exact in_rw (r := scrR s₀) (by simp) (hp.cS' (by simp [tO])))
    (by rw [wr₃'', Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (hp.cS' (by simp [tO])))
    (by decide) (by decide)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  rw [WP.block_append_iff]
  have wr₄' : s₄.wr = [dstR s₀, scrR s₀] := by rw [wr₄, wr₃'']
  obtain ⟨s₅, run₅, g₅, mem₅, rd₅, wr₅⟩ := Unit.zeroZ_ok s₄ (Z := Zp s₀)
    (by rw [g₄ _ (by decide), r15₃]) (by rw [g₄ _ (by decide), r15₃, ← Offset.add_add])
    (by rw [wr₄']; exact in_rw (r := scrR s₀) (by simp) (hp.cS' (by simp [zO])))
    (by rw [wr₄', Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (hp.cS' (by simp [zO])))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  obtain ⟨s₆, run₆, rdi₆, rsi₆, rdx₆, rcx₆, r8₆, r9₆, cs₆, mem₆, rd₆, wr₆⟩ := Unit.tArgs_ok s₅
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  have k₅ : ∀ r, r ≠ .rax → s₅.gpr r = s₃.gpr r := fun r h => by rw [g₅ r h, g₄ r h]
  have r15₅ : s₅.gpr .r15 = S s₀ := by rw [k₅ _ (by decide), r15₃]
  have cs (r : Reg) (hr : r ∈ calleeSaved) : s₆.gpr r = s₃.gpr r := by
    rw [cs₆ r hr, k₅ r (AesCbc.X86_64.calleeSaved_ne_rax hr)]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅, rd₄, rd₃]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅, wr₄, wr₃]
  have rsp₆ : s₆.gpr .rsp = s₀.gpr .rsp := by
    rw [cs _ (by simp [calleeSaved]),
      k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  have f₄ : Frame [⟨Tp s₀, 16⟩] s₃.mem s₄.mem := by rw [mem₄]; exact AesCbc.copyMem_frame _ _ _
  have f₅ : Frame [⟨Zp s₀, 16⟩] s₄.mem s₅.mem := by rw [mem₅]; exact Unit.zero2_frame _ _
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
    by rw [cs _ (by simp [calleeSaved]), r14₃'],
    by rw [cs _ (by simp [calleeSaved]), r15₃], rsp₆, rd₆', wr₆',
    frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩, sv₆⟩, ?_, frame, ?_, ?_⟩
  · refine xpre_tweak hp rd₆' wr₆' rsp₆ ?_ ?_ (by rw [rdx₆, r15₅]) (by rw [rcx₆, r15₅]) r8₆ (by rw [r9₆, r15₅])
    · rw [rdi₆, k₅ _ (by decide),
        k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [rsi₆, k₅ _ (by decide), rbp₃', rsi_ofNat]
  · rw [mem₆, mem₅, Proof.Cmac.bytesAt_frame (Unit.zero2_frame _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.t_z) (by decide), mem₄,
      AesCbc.copyMem_bytes _ (hp.i_scr.symm.sub_left (scr_sub (by simp [tO]))),
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.i_scr) (by decide)]
  · rw [mem₆, mem₅, Unit.zero2_bytes]

/-! ## The tweak -/

/-- After the call enciphering the tweak value. -/
structure TwPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  frame : Frame [scrR s₀, stk3 s₀] s₀.mem s.mem
  t : bytesAt s.mem (Tp s₀) 16 = t0 s₀

theorem UPre.sched_frame {s : State} {rs : List Region} (hf : Frame rs s₀.mem s.mem)
    (hd : ∀ r ∈ rs, Region.Sub r (dstR s₀) ∨ r = scrR s₀ ∨ Region.Sub r (stk3 s₀)) :
    bytesAt s.mem (W s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) := by
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega)
  rcases hd r hr with h | rfl | h
  · exact (hp.sch_dst.sub_left (Region.sub_prefix hRb)).sub_right h
  · exact hp.sch_scr.sub_left (Region.sub_prefix hRb)
  · exact (hp.stk_sch.symm.sub_left (Region.sub_prefix hRb)).sub_right h

theorem tcall_wp {n : String} {c : Prog isa}
    (ok : ∀ s, (modeX86_64 (AesXts.xtsMode true)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode true)).post s s')
    (nosp : NoSp c) (depth : c.depth ≤ 1) {s₂ : State} (h₂ : ProPost s₀ s₂) :
    WP isa (.call n c) s₂ (TwPost s₀) := by
  refine WP.mono (xts_call true ok nosp depth h₂.pre) fun s₃ c => ?_
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  have eK : bytesAt s₂.mem (K s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (K s₀) (16 * (R s₀ + 1)) :=
    Proof.Cmac.bytesAt_frame h₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.tsch_scr.sub_left (Region.sub_prefix hRb)) (by omega)
  refine ⟨Inv.call hp h₂.inv z_sub (.inr t_sub) c, ?_, ?_⟩
  · refine ((h₂.frame.mono (by simp)).trans (c.frame.sub fun r hr => ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨scrR s₀, by simp, Unit.sub_trans z_sub s_sub⟩
    · exact ⟨scrR s₀, by simp, Unit.sub_trans t_sub s_sub⟩
    · exact ⟨scrR s₀, by simp, wk_sub⟩
    · exact ⟨stk3 s₀, by simp, stk_sub3 h₂.inv.rsp⟩
  · have := Proof.AesXts.Unit.tweak_of (R := R s₀) (w := bytesAt s₂.mem (K s₀) (16 * (R s₀ + 1))) c.out h₂.z
    rw [this, h₂.ti, eK]

theorem tweak_wp {f : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (modeX86_64 (AesXts.xtsMode true)).pre s →
      ∃ t s', Exec isa f.code s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode true)).post s s')
    (nosp : NoSp f.code) (depth : f.code.depth ≤ 1) :
    WP isa (tweakTo f) s₀ (TwPost s₀) := by
  refine WP.seq (WP.mono (ldS_wp hp) fun s₁ h₁ => ?_)
  subst h₁
  exact WP.seq (WP.mono (pro_wp hp) fun s₂ h₂ => tcall_wp hp ok nosp depth h₂)

/-- `TwPost` across code that keeps the pinned registers and memory. -/
theorem TwPost.keep {s s' : State} (h : TwPost s₀ s) (hg : ∀ r ∈ pinned, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : TwPost s₀ s' where
  inv := Inv.step hp h.inv (rs := []) (fun _ h => by simp at h) (by rw [hm]; exact Frame.refl _ _) hg hrd hwr
  frame := by rw [hm]; exact h.frame
  t := by rw [hm]; exact h.t

/-! ## The out-of-place call on whole blocks -/

/-- After the out-of-place call on the first `N` whole blocks from `T`. -/
structure AllPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  out : Spec.Cbc.blocksAt s.mem (D s₀) N =
    Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (Sr s₀) N)
  tw : bytesAt s.mem (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N
  frame : Frame [⟨D s₀, 16 * N⟩, scrR s₀, stk3 s₀] s₀.mem s.mem

/-- The arguments of the out-of-place call on the first `N` whole blocks. -/
theorem xtpre_blocks {N : Nat} (hN : 16 * N ≤ Len s₀) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hsp : s.gpr .rsp = s₀.gpr .rsp) (rdi : s.gpr .rdi = W s₀)
    (rsi : s.gpr .rsi = BitVec.ofNat 64 (R s₀)) (rdx : s.gpr .rdx = Tp s₀)
    (rcx : s.gpr .rcx = Sr s₀) (r8 : s.gpr .r8 = BitVec.ofNat 64 N) (r9 : s.gpr .r9 = S s₀)
    (r10 : s.gpr .r10 = D s₀) :
    XtPre s (W s₀) (Tp s₀) (Sr s₀) (D s₀) (S s₀) N (R s₀) := by
  have dS : Region.Sub ⟨D s₀, 16 * N⟩ (dstR s₀) := by rw [hp.dstR_eq]; exact Region.sub_prefix hN
  have sS : Region.Sub ⟨Sr s₀, 16 * N⟩ (srcR s₀) := Region.sub_prefix hN
  have tS : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := Unit.sub_trans t_sub s_sub
  have stk : stk3 s = stk3 s₀ := by rw [stk3, stk3, hsp]
  exact {
    rdi := rdi
    rsi := rsi
    rdx := rdx
    rcx := rcx
    r8 := r8
    r9 := r9
    r10 := r10
    rounds := hp.rounds
    n := by have := hp.len_hi; simp only [Spec.Xts.maxBlocks] at this; omega
    wt := hp.sch_scr.sub_right tS
    wd := hp.sch_dst.sub_right dS
    ws := hp.sch_scr.sub_right wk_sub
    rt := (hp.src_scr.sub_left sS).sub_right tS
    rd' := (hp.src_dst.sub_left sS).sub_right dS
    rs := (hp.src_scr.sub_left sS).sub_right wk_sub
    td := (hp.dst_scr.symm.sub_left tS).sub_right dS
    ts := hp.t_wk
    ds := (hp.dst_scr.sub_left dS).sub_right wk_sub
    stkW := by rw [stk]; exact hp.stk_sch
    stkR := by rw [stk]; exact hp.stk_src.sub_right sS
    stkT := by rw [stk]; exact hp.stk_scr.sub_right tS
    stkD := by rw [stk]; exact hp.stk_dst.sub_right dS
    stkS := by rw [stk]; exact hp.stk_scr.sub_right wk_sub
    wrapT := Unit.wrap_off _ hp.scr_wrap (by decide)
    wrapR := by have := hp.src_wrap; omega
    wrapD := by have := hp.dst_wrap'; omega
    wrapS := by have := hp.scr_wrap; omega
    rsp_lo := by rw [hsp]; exact hp.rsp_lo
    rsp_hi := by rw [hsp]; have := hp.rsp_hi; omega
    reads := by
      rw [hp.rdwr hrd hwr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨srcR s₀, by simp, 0, by simp, by simpa using hN⟩
      · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
      · exact ⟨dstR s₀, by simp, 0, by simp, by simpa [hp.dlen] using hN⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hp.wr' hwr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
      · exact ⟨dstR s₀, by simp, 0, by simp, by simpa [hp.dlen] using hN⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩ }

theorem blocks_call (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (xtsToX86_64 enc).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (xtsToX86_64 enc).post s s')
    (nosp : NoSp c) (depth : c.depth ≤ 2) {N : Nat} (hN : 16 * N ≤ Len s₀) {s : State} (h : TwPost s₀ s)
    (hpre : XtPre s (W s₀) (Tp s₀) (Sr s₀) (D s₀) (S s₀) N (R s₀)) :
    WP isa (.call n c) s (AllPost enc s₀ N) := by
  refine WP.mono (xtsTo_call enc ok nosp depth hpre) fun s' x => ?_
  have dS : Region.Sub ⟨D s₀, 16 * N⟩ (dstR s₀) := by rw [hp.dstR_eq]; exact Region.sub_prefix hN
  have sS : Region.Sub ⟨Sr s₀, 16 * N⟩ (srcR s₀) := Region.sub_prefix hN
  have eW := hp.sched_frame (h.inv.frame) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (fun _ h => h)
    · exact .inr (.inl rfl)
    · exact .inr (.inr (fun _ h => h)))
  have eS : Spec.Cbc.blocksAt s.mem (Sr s₀) N = Spec.Cbc.blocksAt s₀.mem (Sr s₀) N :=
    Unit.blocksAt_frame h.inv.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.src_dst.sub_left sS
      · exact hp.src_scr.sub_left sS
      · exact hp.stk_src.symm.sub_left sS) (by have := hp.src_wrap; omega)
  refine ⟨Inv.callTo hp h.inv t_sub dS x, ?_, ?_, ?_⟩
  · rw [x.out, eW, h.t, eS]
  · rw [x.tw, h.t]
  · refine ((h.frame.mono (by simp)).trans (x.frame.sub fun r hr => ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨scrR s₀, by simp, Unit.sub_trans t_sub s_sub⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, wk_sub⟩
    · exact ⟨stk3 s₀, by simp, by rw [stk3, stk3, h.inv.rsp]; exact fun _ h => h⟩

/-! ## The epilogue -/

theorem fin_wp {s : State} (h : Inv s₀ s) :
    WP isa (.block restore) s fun s' => gprPreserved s₀ s' ∧ s'.mem = s.mem := by
  rw [Unit.restore_eq]
  refine WP.mono (Spill.restore_ok .r15 saved s₀.gpr s (by decide) (fun p hp' => ?_)
    (by rw [h.r15]; exact h.saved)) fun s' ⟨g₁, g₂, mem', _⟩ =>
      ⟨⟨Spill.calleeSaved_ok g₁ g₂ (by decide) h.rsp, ?_⟩, mem'⟩
  · have := saved_bound p hp'
    rw [hp.rdwr h.rd h.wr, h.r15]
    exact in_rw (r := scrR s₀) (by simp) (hp.cS' (by omega))
  · rw [mem']
    refine h.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_dst
    · exact hp.ret_scr
    · exact Offset.base_disjoint_below _ (by decide)

/-! ## The bytes after the first whole blocks -/

/-- After the copy of the bytes after the first `hh` whole blocks. -/
theorem copyRest_wp {hh : Nat} (hh16 : 16 * hh ≤ Len s₀) {s : State} (hi : Inv s₀ s)
    (hrax : s.gpr .rax = BitVec.ofNat 64 (16 * hh)) :
    WP isa copyRest s fun s' => Inv s₀ s' ∧
      s'.mem = WriteBytes.writeBytes s.mem (D s₀ + BitVec.ofNat 64 (16 * hh))
        (bytesAt s₀.mem (Sr s₀ + BitVec.ofNat 64 (16 * hh)) (Len s₀ - 16 * hh)) := by
  have hl := hp.len_hi
  simp only [Spec.Xts.maxBlocks] at hl
  have sS : Region.Sub ⟨Sr s₀ + BitVec.ofNat 64 (16 * hh), Len s₀ - 16 * hh⟩ (srcR s₀) := src_sub (by omega)
  have dS : Region.Sub ⟨D s₀ + BitVec.ofNat 64 (16 * hh), Len s₀ - 16 * hh⟩ (dstR s₀) := hp.dst_sub (by omega)
  refine WP.seq (WP.of_runBlock ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩)
  refine WP.mono (Proof.ChaCha20Poly1305.X86_64.Gather.copyBytes_ok (S := Sr s₀ + BitVec.ofNat 64 (16 * hh))
    (D := D s₀ + BitVec.ofNat 64 (16 * hh)) (n := Len s₀ - 16 * hh) ?_ .x16) fun s' ⟨m', g', rd', wr'⟩ => ?_
  · refine ⟨?_, ?_, ?_, by omega, ?_, ?_, (hp.src_dst.sub_left sS).sub_right dS⟩
    · simp [gpr_setReg, hi.r14, hrax]
    · simp [gpr_setReg, hi.r12, hrax]
    · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ↓reduceIte, hi.r13, hrax]
      rw [show s₀.gpr .r9 = BitVec.ofNat 64 (Len s₀) by rw [Len, BitVec.ofNat_toNat, BitVec.setWidth_eq],
        Offset.ofNat_sub_ofNat hh16]
    · simp only [rd_setReg, wr_setReg, arithFlags, State.setFlags]
      rw [hp.rdwr hi.rd hi.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨srcR s₀, by simp, 16 * hh, rfl, by simp; omega⟩
    · simp only [wr_setReg, arithFlags, State.setFlags]
      rw [hp.wr' hi.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dstR s₀, by simp, 16 * hh, rfl, by simp [hp.dlen]; omega⟩
  · have mS : bytesAt s.mem (Sr s₀ + BitVec.ofNat 64 (16 * hh)) (Len s₀ - 16 * hh) =
        bytesAt s₀.mem (Sr s₀ + BitVec.ofNat 64 (16 * hh)) (Len s₀ - 16 * hh) :=
      Proof.Cmac.bytesAt_frame hi.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.src_dst.sub_left sS
        · exact hp.src_scr.sub_left sS
        · exact hp.stk_src.symm.sub_left sS) (by omega)
    simp only [mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags] at m' rd' wr'
    rw [mS] at m'
    refine ⟨Inv.step hp hi (rs := [⟨D s₀ + BitVec.ofNat 64 (16 * hh), Len s₀ - 16 * hh⟩])
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inl dS)
      (by rw [m']; exact Proof.AesGcm.X86_64.writeBytes_frame' _ (Proof.AesXts.Unit.length_bytesAt _ _ _))
      (fun r hr => ?_) rd' wr', m'⟩
    have n := pinned_ne hr
    rw [g' r n.1 n.2.2.2.1 n.2.2.2.2.2.2.2]
    simp [gpr_setReg, n.2.1, n.2.2.2.2.2.1, n.2.2.2.2.2.2.1]

/-! ## The data unit at `src`, as if at `dst` -/

theorem vmem_bytes0 {n : Nat} (hn : n ≤ Len s₀) : bytesAt (vmem s₀) (D s₀) n = bytesAt s₀.mem (Sr s₀) n := by
  have hl := hp.len_hi
  simp only [Spec.Xts.maxBlocks] at hl
  have hL : bytesAt (vmem s₀) (D s₀) (Len s₀) = bytesAt s₀.mem (Sr s₀) (Len s₀) := by
    rw [vmem, Proof.AesCcm.bytesAt_writeBytes_base _ _ _ (by rw [Proof.AesXts.Unit.length_bytesAt]) (by omega),
      Proof.AesXts.Unit.length_bytesAt, List.drop_eq_nil_of_le (by rw [Proof.AesXts.Unit.length_bytesAt]),
      List.append_nil]
  rw [← Proof.AesXts.Unit.bytesAt_take _ _ hn, hL, Proof.AesXts.Unit.bytesAt_take _ _ hn]

theorem vmem_bytes {a n : Nat} (h : a + n ≤ Len s₀) :
    bytesAt (vmem s₀) (D s₀ + BitVec.ofNat 64 a) n = bytesAt s₀.mem (Sr s₀ + BitVec.ofNat 64 a) n := by
  have e₁ := Proof.AesXts.Unit.bytesAt_drop (vmem s₀) (D s₀) (show a ≤ Len s₀ by omega)
  have e₂ := Proof.AesXts.Unit.bytesAt_drop s₀.mem (Sr s₀) (show a ≤ Len s₀ by omega)
  rw [vmem_bytes0 hp (Nat.le_refl _)] at e₁
  rw [← Proof.AesXts.Unit.bytesAt_take (vmem s₀) _ (show n ≤ Len s₀ - a by omega), ← e₁, e₂,
    Proof.AesXts.Unit.bytesAt_take _ _ (show n ≤ Len s₀ - a by omega)]

theorem vmem_blocks {N : Nat} (hN : 16 * N ≤ Len s₀) :
    Spec.Cbc.blocksAt (vmem s₀) (D s₀) N = Spec.Cbc.blocksAt s₀.mem (Sr s₀) N := by
  rw [← Proof.AesXts.Unit.blocks_bytesAt, ← Proof.AesXts.Unit.blocks_bytesAt, vmem_bytes0 hp hN]

end

end VG.Proof.AesXts.X86_64.UnitTo

/-! ## XTS-AES of data units out of place on x86-64: encryption and decryption

`encrypt_wp`, `decrypt_wp`: the tweak; the out-of-place call on the first
`h` whole blocks (`m` for encryption, or decryption without a partial
block; `m - 1` otherwise), from `src` to `dst`; the copy of the bytes after
them from `src` to `dst`; then ciphertext stealing on `dst` as in place,
and the epilogue. After the copy, `dst` holds what the in-place functions
would hold at the same point, from the memory `vmem` in which `dst` holds
the data unit at `src` (`AllMem`): the in-place lemmas of ciphertext
stealing (`enc_steal`, `dec_steal`) take `vmem` as the memory on entry, and
give the data unit's encryption or decryption at `dst` (`unit_post`).
-/

namespace VG.Proof.AesXts.X86_64.UnitTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesXts.X86_64Unit
open VG.Impl.AesXts.X86_64UnitTo renaming ldS → ldSTo, setup → setupTo, pro → proTo, tweak → tweakTo,
  argsAll → argsAllTo, argsHead → argsHeadTo, encrypt → encryptTo, decrypt → decryptTo
open VG.Impl.AesXts.X86_64UnitTo (copyRest wholeBytes headBytes decStealTail)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86_64 (modeX86_64 in_rw)
open VG.Proof.AesXts.X86_64.To (stk3 XtPre XtPost xtsToX86_64)
open VG.Proof.AesXts.X86_64.Unit (XPre XPost xts_call split_ok lastAddr_ok argsL_ok swap_ok nextT_ok shr4
  shr4_shl4 last_eq xtsOf)
open VG.Proof.AesXts.Unit (swapMem encWith decWith)
open VG.Spec.Aes (bytesAt)

/-- An implementation of the in-place and out-of-place whole-block functions
on x86-64, as the out-of-place data-unit functions call them. -/
structure UnitImpl where
  x : Proof.AesXts.X86_64.XtsImpl
  encTo : Impl.Aes.X86_64.Blocks
  encToDepth : encTo.code.depth ≤ 2
  encToOk : ∀ s, (xtsToX86_64 true).pre s →
    ∃ t s', Exec isa encTo.code s t s' ∧ abiPreserved s s' ∧ (xtsToX86_64 true).post s s'
  encToCt : ConstantTime isa (xtsToX86_64 true).pre (xtsToX86_64 true).pub encTo.code
  encToNosp : NoSp encTo.code
  encToMxcsr : encTo.code.allInstrs (fun i => !loadsMxcsr i) = true
  encToSpSafe : encTo.code.all (fun i => !isa.writesSp i) = true
  decTo : Impl.Aes.X86_64.Blocks
  decToDepth : decTo.code.depth ≤ 2
  decToOk : ∀ s, (xtsToX86_64 false).pre s →
    ∃ t s', Exec isa decTo.code s t s' ∧ abiPreserved s s' ∧ (xtsToX86_64 false).post s s'
  decToCt : ConstantTime isa (xtsToX86_64 false).pre (xtsToX86_64 false).pub decTo.code
  decToNosp : NoSp decTo.code
  decToMxcsr : decTo.code.allInstrs (fun i => !loadsMxcsr i) = true
  decToSpSafe : decTo.code.all (fun i => !isa.writesSp i) = true

namespace UnitImpl

abbrev xt (v : UnitImpl) : Impl.AesXts.X86_64UnitTo.XtsTo := ⟨v.encTo, v.decTo⟩

end UnitImpl

/-- The data unit's result in a direction. -/
def withOf : Bool → Spec.Cbc.Cipher → List Byte → List Byte → List Byte
  | true => encWith
  | false => decWith

/-- What each branch leaves before the epilogue. -/
structure Fin (enc : Bool) (s₀ s : State) : Prop where
  inv : Inv s₀ s
  data : bytesAt s.mem (D s₀) (Len s₀) = withOf enc (ciph s₀ enc) (t0 s₀) (bytesAt (vmem s₀) (D s₀) (Len s₀))

/-- The bytes at `p + a` from those at `p`. -/
theorem bytesAt_sub {m m' : Mem} {p : Addr} {k a n : Nat} (h : bytesAt m p k = bytesAt m' p k)
    (ha : a + n ≤ k) : bytesAt m (p + BitVec.ofNat 64 a) n = bytesAt m' (p + BitVec.ofNat 64 a) n := by
  rw [← Proof.AesXts.Unit.bytesAt_take m _ (show n ≤ k - a by omega), ← Proof.AesXts.Unit.bytesAt_drop m p
    (show a ≤ k by omega), h, Proof.AesXts.Unit.bytesAt_drop m' p (show a ≤ k by omega),
    Proof.AesXts.Unit.bytesAt_take _ _ (show n ≤ k - a by omega)]

/-- The memory after the first `N` whole blocks and the bytes after them:
the blocks XTS's, the tweak the one after them, and the rest of `dst` that
of `vmem`. -/
def AllMem (enc : Bool) (s₀ : State) (N : Nat) (m : Mem) : Prop :=
  Spec.Cbc.blocksAt m (D s₀) N = Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt (vmem s₀) (D s₀) N) ∧
    bytesAt m (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N ∧
    bytesAt m (D s₀ + BitVec.ofNat 64 (16 * N)) (Len s₀ - 16 * N) =
      bytesAt (vmem s₀) (D s₀ + BitVec.ofNat 64 (16 * N)) (Len s₀ - 16 * N)

/-- After the first `N` whole blocks and the bytes after them. -/
structure Copied (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  mem : AllMem enc s₀ N s.mem

section
variable {s₀ : State} (hp : UPre s₀)
include hp

omit hp in
theorem AllMem.rest {enc : Bool} {N : Nat} {m : Mem} (h : AllMem enc s₀ N m) {a n : Nat} (ha : 16 * N ≤ a)
    (hn : a + n ≤ Len s₀) :
    bytesAt m (D s₀ + BitVec.ofNat 64 a) n = bytesAt (vmem s₀) (D s₀ + BitVec.ofNat 64 a) n := by
  have e := bytesAt_sub (a := a - 16 * N) (n := n) h.2.2 (by omega)
  rwa [Offset.add_add, show 16 * N + (a - 16 * N) = a by omega] at e

omit hp in
/-- The arguments of the out-of-place call on all the whole blocks. -/
theorem argsAllTo_ok (s : State) :
    ∃ s', runBlock isa argsAllTo s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧
      s'.gpr .rdx = s.gpr .r15 + BitVec.ofNat 64 tO ∧ s'.gpr .rcx = s.gpr .r14 ∧
      s'.gpr .r8 = BitVec.ofNat 64 ((s.gpr .r13).toNat / 16) ∧ s'.gpr .r9 = s.gpr .r15 ∧
      s'.gpr .r10 = s.gpr .r12 ∧
      (∀ r ∈ pinned, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [argsAllTo, runBlock_cons, runStep_some, exec, readSrc, execAlu, execShift,
      Option.bind_some, Option.map_some, show 1 ≤ 4 ∧ 4 ≤ 63 from by decide]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, gpr_setFlags]
  · simp [gpr_setReg, gpr_setFlags]
  · simp [gpr_setReg, gpr_setFlags]; rfl
  · simp [gpr_setReg, gpr_setFlags]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ↓reduceIte, shr4]
  · simp [gpr_setReg, gpr_setFlags]
  · simp [gpr_setReg, gpr_setFlags]
  · intro r hr
    simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_setFlags]

omit hp in
theorem argsHeadTo_ok (s : State) (hm : 1 ≤ (s.gpr .r13).toNat / 16) :
    ∃ s', runBlock isa argsHeadTo s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧
      s'.gpr .rdx = s.gpr .r15 + BitVec.ofNat 64 tO ∧ s'.gpr .rcx = s.gpr .r14 ∧
      s'.gpr .r8 = BitVec.ofNat 64 ((s.gpr .r13).toNat / 16 - 1) ∧ s'.gpr .r9 = s.gpr .r15 ∧
      s'.gpr .r10 = s.gpr .r12 ∧
      (∀ r ∈ pinned, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, r10₁, cs₁, mem₁, rd₁, wr₁⟩ := argsAllTo_ok s
  refine ⟨_, by
    rw [argsHeadTo, runBlock_append, run₁, Option.bind_some]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, mem₁, rd₁, wr₁⟩
  · simp [gpr_setReg, rdi₁]
  · simp [gpr_setReg, rsi₁]
  · simp [gpr_setReg, rdx₁]
  · simp [gpr_setReg, rcx₁]
  · simp only [gpr_setReg, ite_true, r8₁]
    rw [show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat hm]
  · simp [gpr_setReg, r9₁]
  · simp [gpr_setReg, r10₁]
  · intro r hr
    have := cs₁ r hr
    simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [gpr_setReg] using this

/-- Before the out-of-place call on the first `N` whole blocks. -/
structure BlocksReady (s₀ : State) (N : Nat) (s : State) : Prop where
  tw : TwPost s₀ s
  pre : XtPre s (W s₀) (Tp s₀) (Sr s₀) (D s₀) (S s₀) N (R s₀)

theorem argsAll_wp {s : State} (h : TwPost s₀ s) : WP isa (.block argsAllTo) s (BlocksReady s₀ (M s₀)) := by
  obtain ⟨s₂, run₂, rdi₂, rsi₂, rdx₂, rcx₂, r8₂, r9₂, r10₂, cs₂, mem₂, rd₂, wr₂⟩ := argsAllTo_ok s
  have h₂ := TwPost.keep hp h cs₂ mem₂ rd₂ wr₂
  exact WP.of_runBlock ⟨s₂, run₂, h₂, xtpre_blocks hp (N := M s₀) (by rw [len_eq s₀]; omega) h₂.inv.rd h₂.inv.wr
    h₂.inv.rsp (by rw [rdi₂, h.inv.rbx]) (by rw [rsi₂, h.inv.rbp, rsi_ofNat]) (by rw [rdx₂, h.inv.r15])
    (by rw [rcx₂, h.inv.r14]) (by rw [r8₂, h.inv.r13]) (by rw [r9₂, h.inv.r15]) (by rw [r10₂, h.inv.r12])⟩

theorem argsHead_wp {s : State} (h : TwPost s₀ s) : WP isa (.block argsHeadTo) s (BlocksReady s₀ (M s₀ - 1)) := by
  have hm := hp.m_pos
  obtain ⟨s₂, run₂, rdi₂, rsi₂, rdx₂, rcx₂, r8₂, r9₂, r10₂, cs₂, mem₂, rd₂, wr₂⟩ :=
    argsHeadTo_ok s (by rw [h.inv.r13]; exact hm)
  have h₂ := TwPost.keep hp h cs₂ mem₂ rd₂ wr₂
  exact WP.of_runBlock ⟨s₂, run₂, h₂, xtpre_blocks hp (N := M s₀ - 1) (by rw [len_eq s₀]; omega) h₂.inv.rd
    h₂.inv.wr h₂.inv.rsp (by rw [rdi₂, h.inv.rbx]) (by rw [rsi₂, h.inv.rbp, rsi_ofNat]) (by rw [rdx₂, h.inv.r15])
    (by rw [rcx₂, h.inv.r14]) (by rw [r8₂, h.inv.r13]) (by rw [r9₂, h.inv.r15]) (by rw [r10₂, h.inv.r12])⟩

/-- The bytes after the first `N` whole blocks copied, from `16 N` in `rax`. -/
theorem copied_wp {enc : Bool} {N : Nat} (hN : 16 * N ≤ Len s₀) {s : State} (h : AllPost enc s₀ N s)
    (hrax : s.gpr .rax = BitVec.ofNat 64 (16 * N)) : WP isa copyRest s (Copied enc s₀ N) := by
  have hl := hp.len_hi
  simp only [Spec.Xts.maxBlocks] at hl
  refine WP.mono (copyRest_wp hp hN h.inv hrax) fun s' ⟨inv', m'⟩ => ⟨inv', ?_, ?_, ?_⟩
  · have dS : Region.Sub ⟨D s₀, 16 * N⟩ (dstR s₀) := hp.blocks_sub (by simp only [M]; omega)
    rw [m', Unit.blocksAt_frame (Proof.AesGcm.X86_64.writeBytes_frame' _ (Proof.AesXts.Unit.length_bytesAt _ _ _))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.dst_wrap'; omega)) (by omega),
      h.out, vmem_blocks hp hN]
  · rw [m', Proof.Cmac.bytesAt_frame (Proof.AesGcm.X86_64.writeBytes_frame' _
      (Proof.AesXts.Unit.length_bytesAt _ _ _)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.dst_scr.symm.sub_left (Unit.sub_trans t_sub s_sub)).sub_right (hp.dst_sub (by omega)))
      (by decide), h.tw]
  · rw [m', Proof.AesCcm.bytesAt_writeBytes_base _ _ _ (by rw [Proof.AesXts.Unit.length_bytesAt]) (by omega),
      Proof.AesXts.Unit.length_bytesAt, List.drop_eq_nil_of_le (by rw [Proof.AesXts.Unit.length_bytesAt]),
      List.append_nil, vmem_bytes hp (by omega)]

omit hp in
theorem wholeBytes_ok (s : State) :
    ∃ s', runBlock isa wholeBytes s = some s' ∧
      s'.gpr .rax = BitVec.ofNat 64 (16 * ((s.gpr .r13).toNat / 16)) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [wholeBytes, runBlock_cons, runStep_some, exec, readSrc, execShift,
      Option.map_some, show 1 ≤ 4 ∧ 4 ≤ 63 from by decide]
    rfl, ?_⟩
  refine ⟨?_, fun r h => ?_, rfl, rfl, rfl⟩
  · simp only [gpr_setReg, ↓reduceIte, shr4_shl4]
  · simp [gpr_setReg, gpr_setFlags, h]

/-- `wholeBytes`, then the copy. -/
theorem copiedAll_wp {enc : Bool} {s : State} (h : AllPost enc s₀ (M s₀) s) :
    WP isa (.seq (.block wholeBytes) copyRest) s (Copied enc s₀ (M s₀)) := by
  obtain ⟨s₁, run₁, rax₁, g₁, m₁, rd₁, wr₁⟩ := wholeBytes_ok s
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine copied_wp hp (by rw [len_eq s₀]; omega)
    ⟨Inv.step hp h.inv (rs := []) (fun _ h => by simp at h) (by rw [m₁]; exact Frame.refl _ _)
      (fun r hr => g₁ r (pinned_ne hr).1) rd₁ wr₁, by rw [m₁]; exact h.out, by rw [m₁]; exact h.tw,
      by rw [m₁]; exact h.frame⟩ (by rw [rax₁, h.inv.r13])

omit hp in
theorem headBytes_ok (s : State) (hm : 1 ≤ (s.gpr .r13).toNat / 16) :
    ∃ s', runBlock isa headBytes s = some s' ∧
      s'.gpr .rax = BitVec.ofNat 64 (16 * ((s.gpr .r13).toNat / 16 - 1)) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, rax₁, g₁, mem₁, rd₁, wr₁⟩ := wholeBytes_ok s
  refine ⟨_, by
    rw [headBytes, runBlock_append, run₁, Option.bind_some]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
    rfl, ?_⟩
  refine ⟨?_, fun r h => ?_, mem₁, rd₁, wr₁⟩
  · simp only [gpr_setReg, ite_true, rax₁]
    rw [show BitVec.signExtend 64 (16 : BitVec 32) = BitVec.ofNat 64 16 from rfl, Offset.ofNat_sub_ofNat (by omega),
      Nat.mul_sub_one]
  · simp [gpr_setReg, h, g₁ r h]

/-- `headBytes`, then the copy. -/
theorem copiedHead_wp {enc : Bool} {s : State} (h : AllPost enc s₀ (M s₀ - 1) s) :
    WP isa (.seq (.block headBytes) copyRest) s (Copied enc s₀ (M s₀ - 1)) := by
  have hm := hp.m_pos
  obtain ⟨s₁, run₁, rax₁, g₁, m₁, rd₁, wr₁⟩ := headBytes_ok s (by rw [h.inv.r13]; exact hm)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine copied_wp hp (by rw [len_eq s₀]; omega)
    ⟨Inv.step hp h.inv (rs := []) (fun _ h => by simp at h) (by rw [m₁]; exact Frame.refl _ _)
      (fun r hr => g₁ r (pinned_ne hr).1) rd₁ wr₁, by rw [m₁]; exact h.out, by rw [m₁]; exact h.tw,
      by rw [m₁]; exact h.frame⟩ (by rw [rax₁, h.inv.r13])

/-- The bytes of a part `X` of `dst` that an in-place call on other blocks keeps. -/
theorem call_keeps {enc : Bool} {s s' : State} {Wk T Dd : Addr} {N Rr : Nat} {X : Region}
    (hX : Region.Sub X (dstR s₀)) (hXD : X.Disjoint ⟨Dd, 16 * N⟩) (hT : Region.Sub ⟨T, 16⟩ (scrR s₀))
    (hrsp : s.gpr .rsp = s₀.gpr .rsp) (c : XPost enc s Wk T Dd (S s₀) N Rr s') (hn : X.len ≤ 2 ^ 64) :
    bytesAt s'.mem X.base X.len = bytesAt s.mem X.base X.len :=
  Proof.Cmac.bytesAt_frame c.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hp.dst_scr.sub_left hX).sub_right hT
    · exact hXD
    · exact (hp.dst_scr.sub_left hX).sub_right wk_sub
    · exact (hp.stk_dst.symm.sub_left hX).sub_right (stk_sub3 hrsp)) hn

/-- The steal's prologue: the last whole block in `rdx`, and the index in `rcx`. -/
theorem stealPre_wp {s : State} (hr12 : s.gpr .r12 = D s₀) (hrax : s.gpr .rax = BitVec.ofNat 64 (16 * M s₀))
    {Q : State → Prop}
    (h : ∀ s', s'.gpr .rdx = L s₀ → s'.gpr .rcx = 0 → (∀ r, r ≠ .rdx → r ≠ .rcx → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (.block stealPre) s Q := by
  rw [stealPre, WP.block_append_iff]
  obtain ⟨s₁, run₁, rdx₁, g₁, mem₁, rd₁, wr₁⟩ := lastAddr_ok s
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₁.setReg .rcx (BitVec.setWidth 64 (0 : BitVec 32)), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some, State.setReg32], ?_⟩⟩
  refine h _ ?_ (by simp [gpr_setReg]) (fun r h₁ h₂ => ?_) (by rw [mem_setReg, mem₁]) (by rw [rd_setReg, rd₁])
    (by rw [wr_setReg, wr₁])
  · rw [gpr_setReg_of_ne _ _ (by decide), rdx₁, hr12, hrax, last_eq _ hp.m_pos (by have := hp.m_lt; omega)]
  · rw [gpr_setReg_of_ne _ _ h₂, g₁ r h₁]

/-- After `split`, following the copy. -/
structure SplitPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  cp : Copied enc s₀ N s
  rax : s.gpr .rax = BitVec.ofNat 64 (16 * M s₀)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (B s₀)
  zf : s.zf = some (decide (B s₀ = 0))

omit hp in
theorem split_wp {s : State} (h : Inv s₀ s) {Q : State → Prop}
    (hq : ∀ s', s'.gpr .rax = BitVec.ofNat 64 (16 * M s₀) → s'.gpr .r8 = BitVec.ofNat 64 (B s₀) →
      s'.zf = some (decide (B s₀ = 0)) → (∀ r, r ≠ .rax → r ≠ .r8 → s'.gpr r = s.gpr r) → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (.block split) s Q := by
  obtain ⟨s', run', rax', r8', zf', g', mem', rd', wr'⟩ := split_ok s
  rw [h.r13] at rax' r8' zf'
  exact WP.of_runBlock ⟨s', run', hq s' rax' r8' zf' g' mem' rd' wr'⟩

theorem splitCopied_wp {enc : Bool} {N : Nat} {s : State} (h : Copied enc s₀ N s) :
    WP isa (.block split) s (SplitPost enc s₀ N) :=
  split_wp h.inv fun _ rax₄ r8₄ zf₄ g₄ mem₄ rd₄ wr₄ =>
    ⟨⟨Inv.step hp h.inv (rs := []) (fun _ h => by simp at h) (by rw [mem₄]; exact Frame.refl _ _)
      (fun r hr => g₄ r (pinned_ne hr).1 (pinned_ne hr).2.2.2.1) rd₄ wr₄, by rw [mem₄]; exact h.mem⟩,
      rax₄, r8₄, zf₄⟩

/-- Before the call on the last whole block, from the tweak of block `M`:
`Cₘ` and `PP` swapped into place. -/
structure EncLast (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (Tp s₀) (L s₀) (S s₀) 1 (R s₀)
  mem : ∃ m, AllMem true s₀ (M s₀) m ∧ s.mem = swapMem m (L s₀) (B s₀)

/-- The arguments of a call on the last whole block, from the tweak at `o`. -/
theorem xpre_last {o : Nat} (ho : o = tO ∨ o = zO) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hsp : s.gpr .rsp = s₀.gpr .rsp) (rdi : s.gpr .rdi = W s₀)
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
  have lS : Region.Sub ⟨L s₀, 16 * 1⟩ (dstR s₀) := hp.l_sub
  have stk := stk_sub3 hsp
  have hL : 16 * (M s₀ - 1) + 16 ≤ DLen s₀ := by
    rw [hp.dlen]; have := len_eq s₀; have := hp.m_pos; simp only [M, B] at *; omega
  exact {
    rdi := rdi
    rsi := rsi
    rdx := rdx
    rcx := rcx
    r8 := r8
    r9 := r9
    rounds := hp.rounds
    n := by decide
    wt := hp.sch_scr.sub_right (Unit.sub_trans oS s_sub)
    wd := hp.sch_dst.sub_right lS
    ws := hp.sch_scr.sub_right wk_sub
    td := (hp.dst_scr.symm.sub_left (Unit.sub_trans oS s_sub)).sub_right lS
    ts := oW
    ds := (hp.dst_scr.sub_left lS).sub_right wk_sub
    stkW := hp.stk_sch.sub_left stk
    stkT := (hp.stk_scr.sub_right (Unit.sub_trans oS s_sub)).sub_left stk
    stkD := (hp.stk_dst.sub_right lS).sub_left stk
    stkS := (hp.stk_scr.sub_right wk_sub).sub_left stk
    wrapT := Unit.wrap_off _ hp.scr_wrap ol
    wrapD := hp.l_wrap
    wrapS := by have := hp.scr_wrap; omega
    reads := by
      rw [hp.rdwr hrd hwr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨scrR s₀, by simp, o, rfl, by simpa using ol⟩
      · exact ⟨dstR s₀, by simp, 16 * (M s₀ - 1), rfl, by simpa using hL⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hp.wr' hwr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, o, rfl, by simpa using ol⟩
      · exact ⟨dstR s₀, by simp, 16 * (M s₀ - 1), rfl, by simpa using hL⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩ }

/-- The call on the last whole block, and the data unit's ciphertext. -/
theorem encLastCall_wp (v : UnitImpl) {s : State} (h : EncLast s₀ s) (hB : B s₀ ≠ 0) :
    WP isa (.call v.x.enc.name v.x.enc.code) s (Fin true s₀) := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨m, ⟨hout, htw, hrest⟩, m₂⟩ := h.mem
  refine WP.mono (xts_call true v.x.encOk v.x.encNosp v.x.encDepth h.pre) fun s₄ c => ?_
  have sw := Proof.AesXts.Unit.swapMem_frame m (L s₀) (B s₀)
  have tS : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := Unit.sub_trans t_sub s_sub
  refine ⟨Inv.call hp h.inv t_sub (.inl hp.l_sub) c, ?_⟩
  rw [len_eq s₀]
  refine Proof.AesXts.Unit.enc_steal (m₀ := vmem s₀) hp.m_pos (Nat.pos_of_ne_zero hB) hb hout ?_ ⟨?_, ?_, ?_⟩
  · rw [hp.tl_eq]
    exact AllMem.rest (enc := true) ⟨hout, htw, hrest⟩ (Nat.le_refl _) (by rw [len_eq s₀])
  · rw [Proof.AesXts.Unit.crypt_one_of c.out,
      hp.sched_frame h.inv.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact .inl (fun _ h => h)
        · exact .inr (.inl rfl)
        · exact .inr (.inr (fun _ h => h))), m₂,
      Proof.Cmac.bytesAt_frame sw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.dst_scr.symm.sub_left tS).sub_right hp.lb_sub) (by decide), htw]
  · rw [call_keeps hp (X := ⟨D s₀, 16 * (M s₀ - 1)⟩) (hp.blocks_sub (by omega)) hp.hd_l tS h.inv.rsp c
      (by dsimp only; have := hp.wrapD; omega), m₂]
    exact Proof.Cmac.bytesAt_frame sw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.hd_lb) (by dsimp only; have := hp.wrapD; omega)
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub tl_l tS h.inv.rsp c (by dsimp only; omega), m₂]

theorem encLast_wp {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa (.seq (.seq (.block stealPre) swap) (.block (argsL tO))) s (EncLast s₀) := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  refine WP.seq (WP.seq (stealPre_wp hp (by rw [h.cp.inv.r12]) h.rax fun s₁ rdx₁ rcx₁ g₁ mem₁ rd₁ wr₁ => ?_))
  have wr₁' : s₁.wr = [dstR s₀, scrR s₀] := by rw [wr₁, hp.wr' h.cp.inv.wr]
  refine WP.mono (swap_ok s₁ (Nat.pos_of_ne_zero hB) hb rdx₁ rcx₁
    (by rw [g₁ _ (by decide) (by decide), h.r8]) (fun i hi => by
      rw [wr₁']
      exact in_rw (r := dstR s₀) (by simp)
        (hp.lb_sub _ (Offset.contains_base (L s₀) (d := i) (n := 1) (k := 16 + B s₀) (by omega) (by omega)))))
    fun s₂ ⟨mem₂, g₂, rd₂, wr₂⟩ => ?_
  obtain ⟨s₃, run₃, rdi₃, rsi₃, rdx₃, rcx₃, r8₃, r9₃, cs₃, mem₃, rd₃, wr₃⟩ := argsL_ok s₂ (o := tO) rfl
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have k₂ (r : Reg) (hr : r ∈ pinned) : s₂.gpr r = s.gpr r := by
    have n := pinned_ne hr
    rw [g₂ r n.1 n.2.2.2.2.1 n.2.1, g₁ r n.2.2.1 n.2.1]
  have k₃ (r : Reg) (hr : r ∈ pinned) : s₃.gpr r = s.gpr r := by
    rw [cs₃ r (pinned_cs r hr), k₂ r hr]
  have inv₂ : Inv s₀ s₂ := Inv.step hp h.cp.inv (rs := [⟨L s₀, 16 + B s₀⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl hp.lb_sub)
    (by rw [mem₂, mem₁]; exact Proof.AesXts.Unit.swapMem_frame _ _ _) k₂ (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  have inv₃ : Inv s₀ s₃ := Inv.step hp inv₂ (rs := []) (fun _ h => by simp at h)
    (by rw [mem₃]; exact Frame.refl _ _) (fun r hr => by rw [k₃ r hr, k₂ r hr]) rd₃ wr₃
  exact ⟨inv₃, xpre_last hp (.inl rfl) inv₃.rd inv₃.wr inv₃.rsp (by rw [rdi₃, inv₂.rbx])
    (by rw [rsi₃, inv₂.rbp, rsi_ofNat]) (by rw [rdx₃, inv₂.r15]) (by rw [rcx₃, g₂ _ (by decide) (by decide)
      (by decide), rdx₁]) r8₃ (by rw [r9₃, inv₂.r15]),
    ⟨s.mem, h.cp.mem, by rw [mem₃, mem₂, mem₁]⟩⟩

/-- The steal of encryption: `Cₘ` and `PP` swapped into place, and `PP`
enciphered with the tweak of block `M`. -/
theorem encSteal_wp (v : UnitImpl) {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa (encSteal v.x.enc) s (Fin true s₀) :=
  WP.assoc (WP.assoc (WP.seq (WP.mono (encLast_wp hp h hB) fun _ h' => encLastCall_wp hp v h' hB)))

omit hp in
/-- The data unit of whole blocks, after the call on all of them. -/
theorem whole_fin {enc : Bool} {s : State} (h : Copied enc s₀ (M s₀) s) (hb : B s₀ = 0) : Fin enc s₀ s := by
  refine ⟨h.inv, ?_⟩
  rw [show Len s₀ = 16 * M s₀ by rw [len_eq s₀, hb, Nat.add_zero]]
  cases enc
  · exact Proof.AesXts.Unit.dec_whole h.mem.1
  · exact Proof.AesXts.Unit.enc_whole h.mem.1

/-- The postcondition, from the bytes of the data unit. -/
theorem unit_post {enc : Bool} {s' : State}
    (hd : bytesAt s'.mem (D s₀) (Len s₀) =
      withOf enc (ciph s₀ enc) (t0 s₀) (bytesAt (vmem s₀) (D s₀) (Len s₀))) :
    (unitToX86_64 enc).post s₀ s' := by
  intro key hk
  have hk' := Proof.AesXts.Unit.keys_of (bytesAt s₀.mem (I s₀) 16) hk
  have hl : 16 ≤ (bytesAt s₀.mem (Sr s₀) (Len s₀)).length := by
    rw [Proof.AesXts.Unit.length_bytesAt]; exact hp.len_lo
  rw [vmem_bytes0 hp (Nat.le_refl _)] at hd
  cases enc
  · rw [Unit.xtsOf, Proof.AesXts.Unit.aesXtsDecrypt_eq hk' hl, hd]; rfl
  · rw [Unit.xtsOf, Proof.AesXts.Unit.aesXtsEncrypt_eq hk' hl, hd]; rfl

theorem encrypt_wp (v : UnitImpl) :
    WP isa (encryptTo v.x.xts v.xt) s₀ fun s' => gprPreserved s₀ s' ∧ (unitToX86_64 true).post s₀ s' := by
  refine WP.seq (WP.mono (tweak_wp hp v.x.encOk v.x.encNosp v.x.encDepth) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (argsAll_wp hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (blocks_call hp true v.encToOk v.encToNosp v.encToDepth (by rw [len_eq s₀]; omega)
    h₂.tw h₂.pre) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (copiedAll_wp hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (splitCopied_wp hp h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (WP.ite (decide (B s₀ = 0)) h₅.zf
    (fun hb => WP.block_nil (whole_fin h₅.cp (by simpa using hb)))
    (fun hb => encSteal_wp hp v h₅ (by simpa using hb))) fun s₆ h₆ => ?_)
  exact WP.mono (fin_wp hp h₆.inv) fun s' ⟨g, m⟩ => ⟨g, unit_post hp (by rw [m]; exact h₆.data)⟩

/-! ## Decryption -/

/-- Before the call on the last whole block from the tweak of block `M`,
which is at `zO`. -/
structure DecL1 (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (Zp s₀) (L s₀) (S s₀) 1 (R s₀)
  mem : ∃ m, AllMem false s₀ (M s₀ - 1) m ∧ Frame [⟨Zp s₀, 16⟩] m s.mem ∧
    bytesAt s.mem (Zp s₀) 16 = Spec.Xts.mulAlpha (bytesAt m (Tp s₀) 16)

/-- The memory after the call on the last whole block from the tweak of
block `M`: `PP` there, from the memory `m` after the first `M - 1` blocks
and the bytes after them. -/
def DecMem (s₀ : State) (m₅ : Mem) : Prop :=
  ∃ m, AllMem false s₀ (M s₀ - 1) m ∧
    bytesAt m₅ (L s₀) 16 = Spec.Xts.block (ciph s₀ false) (Spec.Xts.next (t0 s₀) (M s₀)) (bytesAt m (L s₀) 16) ∧
    bytesAt m₅ (D s₀) (16 * (M s₀ - 1)) = bytesAt m (D s₀) (16 * (M s₀ - 1)) ∧
    bytesAt m₅ (L s₀ + 16) (B s₀) = bytesAt m (L s₀ + 16) (B s₀) ∧
    bytesAt m₅ (Tp s₀) 16 = Spec.Xts.next (t0 s₀) (M s₀ - 1)

/-- After the call on the last whole block from the tweak of block `M`. -/
structure DecL2 (s₀ s : State) : Prop where
  inv : Inv s₀ s
  mem : DecMem s₀ s.mem

/-- Before the call on the last whole block from the tweak of block `M - 1`:
`Pₘ` and `CC` swapped into place. -/
structure DecL3 (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (Tp s₀) (L s₀) (S s₀) 1 (R s₀)
  mem : ∃ m₅, DecMem s₀ m₅ ∧ s.mem = swapMem m₅ (L s₀) (B s₀)

/-- The tweak of block `M`, at `zO`, and the arguments of the call on the
last whole block from it. -/
theorem decL1_wp {s₂ : State} (h₂ : Copied false s₀ (M s₀ - 1) s₂) :
    WP isa (.block (nextT ++ split ++ lastAddr ++ argsL zO)) s₂ (DecL1 s₀) := by
  have hm := hp.m_pos
  have wr₂ : s₂.wr = [dstR s₀, scrR s₀] := hp.wr' h₂.inv.wr
  have rdwr₂ := hp.rdwr h₂.inv.rd h₂.inv.wr
  obtain ⟨s₃, run₃, g₃, f₃, z₃, rd₃, wr₃⟩ := nextT_ok s₂ (T := Tp s₀) (Z := Zp s₀) (by rw [h₂.inv.r15])
    (by rw [h₂.inv.r15, ← Offset.add_add]) (by rw [h₂.inv.r15]) (by rw [h₂.inv.r15, ← Offset.add_add])
    (by rw [rdwr₂]; exact in_rw (r := scrR s₀) (by simp) (hp.cS' (by simp [tO])))
    (by rw [rdwr₂, Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (hp.cS' (by simp [tO])))
    (by rw [wr₂]; exact in_rw (r := scrR s₀) (by simp) (hp.cS' (by simp [zO])))
    (by rw [wr₂, Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (hp.cS' (by simp [zO])))
  have inv₃ : Inv s₀ s₃ := Inv.step hp h₂.inv (rs := [⟨Zp s₀, 16⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl z_sub)) f₃
    (fun r hr => g₃ r (pinned_ne hr).1 (pinned_ne hr).2.1 (pinned_ne hr).2.2.1) rd₃ wr₃
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  rw [WP.block_append_iff]
  refine split_wp inv₃ fun s₄ rax₄ _ _ g₄ mem₄ rd₄ wr₄ => ?_
  rw [WP.block_append_iff]
  obtain ⟨s₅, run₅, rdx₅, g₅, mem₅, rd₅, wr₅⟩ := lastAddr_ok s₄
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  obtain ⟨s₆, run₆, rdi₆, rsi₆, rdx₆, rcx₆, r8₆, r9₆, cs₆, mem₆, rd₆, wr₆⟩ := argsL_ok s₅ (o := zO) rfl
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  have k₆ (r : Reg) (hr : r ∈ pinned) : s₆.gpr r = s₃.gpr r := by
    have n := pinned_ne hr
    rw [cs₆ r (pinned_cs r hr), g₅ r n.2.2.1, g₄ r n.1 n.2.2.2.1]
  have m₆ : s₆.mem = s₃.mem := by rw [mem₆, mem₅, mem₄]
  have inv₆ : Inv s₀ s₆ := Inv.step hp inv₃ (rs := []) (fun _ h => by simp at h)
    (by rw [m₆]; exact Frame.refl _ _) k₆ (by rw [rd₆, rd₅, rd₄]) (by rw [wr₆, wr₅, wr₄])
  refine ⟨inv₆, xpre_last hp (.inr rfl) inv₆.rd inv₆.wr inv₆.rsp (by rw [rdi₆, g₅ _ (by decide),
      g₄ _ (by decide) (by decide), inv₃.rbx])
    (by rw [rsi₆, g₅ _ (by decide), g₄ _ (by decide) (by decide), inv₃.rbp, rsi_ofNat])
    (by rw [rdx₆, g₅ _ (by decide), g₄ _ (by decide) (by decide), inv₃.r15])
    (by rw [rcx₆, rdx₅, g₄ _ (by decide) (by decide), rax₄, inv₃.r12,
      last_eq _ hm (by have := hp.m_lt; omega)]) r8₆
    (by rw [r9₆, g₅ _ (by decide), g₄ _ (by decide) (by decide), inv₃.r15]),
    ⟨s₂.mem, h₂.mem, by rw [m₆]; exact f₃, by rw [m₆]; exact z₃⟩⟩

/-- The call on the last whole block from the tweak of block `M`. -/
theorem decL2_wp (v : UnitImpl) {s : State} (h : DecL1 s₀ s) :
    WP isa (.call v.x.dec.name v.x.dec.code) s (DecL2 s₀) := by
  have hm := hp.m_pos
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨m, ⟨hout, htw, hrest⟩, f₃, z₃⟩ := h.mem
  refine WP.mono (xts_call false v.x.decOk v.x.decNosp v.x.decDepth h.pre) fun s₇ c₇ => ?_
  have tL : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := Unit.sub_trans t_sub s_sub
  have zL : Region.Sub ⟨Zp s₀, 16⟩ (scrR s₀) := Unit.sub_trans z_sub s_sub
  have eW := hp.sched_frame h.inv.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (fun _ h => h)
    · exact .inr (.inl rfl)
    · exact .inr (.inr (fun _ h => h)))
  refine ⟨Inv.call hp h.inv z_sub (.inl hp.l_sub) c₇, m, ⟨hout, htw, hrest⟩, ?_, ?_, ?_, ?_⟩
  · rw [Proof.AesXts.Unit.crypt_one_of c₇.out, eW, z₃, htw, ← Proof.AesXts.next_succ,
      Nat.sub_add_cancel hm,
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.dst_scr.sub_left hp.l_sub).sub_right zL) (by decide)]
  · rw [call_keeps hp (X := ⟨D s₀, 16 * (M s₀ - 1)⟩) (hp.blocks_sub (by omega)) hp.hd_l zL h.inv.rsp c₇
      (by dsimp only; have := hp.wrapD; omega)]
    exact Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.dst_scr.sub_left (hp.blocks_sub (by omega))).sub_right zL) (by dsimp only; have := hp.wrapD; omega)
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub tl_l zL h.inv.rsp c₇ (by dsimp only; omega)]
    exact Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.dst_scr.sub_left hp.tl_sub).sub_right zL) (by dsimp only; omega)
  · rw [Proof.Cmac.bytesAt_frame c₇.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hp.t_z
        · exact (hp.dst_scr.symm.sub_left tL).sub_right hp.l_sub
        · exact hp.t_wk
        · exact ((hp.stk_scr.sub_right tL).sub_left (stk_sub3 h.inv.rsp)).symm) (by decide),
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.t_z) (by decide), htw]

/-- The call on the last whole block from the tweak of block `M - 1`, and
the data unit's plaintext. -/
theorem decLast_wp (v : UnitImpl) {s : State} (h : DecL3 s₀ s) (hB : B s₀ ≠ 0) :
    WP isa (.call v.x.dec.name v.x.dec.code) s (Fin false s₀) := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  have hm := hp.m_pos
  obtain ⟨m₅, ⟨m, ⟨hout, htw, hrest⟩, h5L, h5H, h5T, tw₅⟩, m₁₀⟩ := h.mem
  refine WP.mono (xts_call false v.x.decOk v.x.decNosp v.x.decDepth h.pre) fun s₁₂ c₁₂ => ?_
  refine ⟨Inv.call hp h.inv t_sub (.inl hp.l_sub) c₁₂, ?_⟩
  have sw := Proof.AesXts.Unit.swapMem_frame m₅ (L s₀) (B s₀)
  have tL : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := Unit.sub_trans t_sub s_sub
  have eW' := hp.sched_frame h.inv.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (fun _ h => h)
    · exact .inr (.inl rfl)
    · exact .inr (.inr (fun _ h => h)))
  have am : AllMem false s₀ (M s₀ - 1) m := ⟨hout, htw, hrest⟩
  rw [len_eq s₀]
  refine Proof.AesXts.Unit.dec_steal (m₀ := vmem s₀) (m₃ := m) (m₅ := m₅) hm (Nat.pos_of_ne_zero hB) hb hout
    ⟨?_, ?_⟩ ⟨h5L, h5H, h5T⟩ ⟨?_, ?_, ?_⟩
  · exact am.rest (a := 16 * (M s₀ - 1)) (n := 16) (Nat.le_refl _) (by simp only [M] at *; omega)
  · rw [hp.tl_eq]; exact am.rest (a := 16 * M s₀) (n := B s₀) (by omega) (by rw [len_eq s₀])
  · rw [Proof.AesXts.Unit.crypt_one_of c₁₂.out, eW', m₁₀,
      Proof.Cmac.bytesAt_frame sw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.dst_scr.symm.sub_left tL).sub_right hp.lb_sub) (by decide), tw₅]
  · rw [call_keeps hp (X := ⟨D s₀, 16 * (M s₀ - 1)⟩) (hp.blocks_sub (by omega)) hp.hd_l tL h.inv.rsp c₁₂
      (by dsimp only; have := hp.wrapD; omega), m₁₀]
    exact Proof.Cmac.bytesAt_frame sw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.hd_lb) (by dsimp only; have := hp.wrapD; omega)
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub tl_l tL h.inv.rsp c₁₂ (by dsimp only; omega), m₁₀]

/-- `Pₘ` and `CC` swapped into place, and the arguments of the call on the
last whole block from the tweak of block `M - 1`. -/
theorem decL3_wp {s : State} (h : DecL2 s₀ s) (hB : B s₀ ≠ 0) :
    WP isa (.seq (.seq (.block (split ++ stealPre)) swap) (.block (argsL tO))) s (DecL3 s₀) := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  refine WP.seq (WP.seq ?_)
  rw [WP.block_append_iff]
  refine split_wp h.inv fun s₈ rax₈ r8₈ _ g₈ mem₈ rd₈ wr₈ => ?_
  refine stealPre_wp hp (by rw [g₈ _ (by decide) (by decide), h.inv.r12]) rax₈
    fun s₉ rdx₉ rcx₉ g₉ mem₉ rd₉ wr₉ => ?_
  have wr₉' : s₉.wr = [dstR s₀, scrR s₀] := by rw [wr₉, wr₈, hp.wr' h.inv.wr]
  refine WP.mono (swap_ok s₉ (Nat.pos_of_ne_zero hB) hb rdx₉ rcx₉
    (by rw [g₉ _ (by decide) (by decide), r8₈]) (fun i hi => by
      rw [wr₉']
      exact in_rw (r := dstR s₀) (by simp)
        (hp.lb_sub _ (Offset.contains_base (L s₀) (d := i) (n := 1) (k := 16 + B s₀) (by omega) (by omega)))))
    fun s₁₀ ⟨mem₁₀, g₁₀, rd₁₀, wr₁₀⟩ => ?_
  obtain ⟨s₁₁, run₁₁, rdi₁₁, rsi₁₁, rdx₁₁, rcx₁₁, r8₁₁, r9₁₁, cs₁₁, mem₁₁, rd₁₁, wr₁₁⟩ := argsL_ok s₁₀ (o := tO) rfl
  refine WP.of_runBlock ⟨s₁₁, run₁₁, ?_⟩
  have k₁₀ (r : Reg) (hr : r ∈ pinned) : s₁₀.gpr r = s.gpr r := by
    have n := pinned_ne hr
    rw [g₁₀ r n.1 n.2.2.2.2.1 n.2.1, g₉ r n.2.2.1 n.2.1, g₈ r n.1 n.2.2.2.1]
  have m₁₀ : s₁₀.mem = swapMem s.mem (L s₀) (B s₀) := by rw [mem₁₀, mem₉, mem₈]
  have inv₁₀ : Inv s₀ s₁₀ := Inv.step hp h.inv (rs := [⟨L s₀, 16 + B s₀⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl hp.lb_sub)
    (by rw [m₁₀]; exact Proof.AesXts.Unit.swapMem_frame _ _ _) k₁₀ (by rw [rd₁₀, rd₉, rd₈])
    (by rw [wr₁₀, wr₉, wr₈])
  have inv₁₁ : Inv s₀ s₁₁ := Inv.step hp inv₁₀ (rs := []) (fun _ h => by simp at h)
    (by rw [mem₁₁]; exact Frame.refl _ _) (fun r hr => cs₁₁ r (pinned_cs r hr)) rd₁₁ wr₁₁
  exact ⟨inv₁₁, xpre_last hp (.inl rfl) inv₁₁.rd inv₁₁.wr inv₁₁.rsp (by rw [rdi₁₁, inv₁₀.rbx])
    (by rw [rsi₁₁, inv₁₀.rbp, rsi_ofNat]) (by rw [rdx₁₁, inv₁₀.r15])
    (by rw [rcx₁₁, g₁₀ _ (by decide) (by decide) (by decide), rdx₉]) r8₁₁ (by rw [r9₁₁, inv₁₀.r15]),
    s.mem, h.mem, by rw [mem₁₁, m₁₀]⟩

/-- The steal of decryption, after the first `M - 1` blocks and the bytes after them. -/
theorem decStealTail_wp (v : UnitImpl) {s : State} (h : Copied false s₀ (M s₀ - 1) s) (hB : B s₀ ≠ 0) :
    WP isa (decStealTail v.x.dec) s (Fin false s₀) :=
  WP.seq (WP.mono (decL1_wp hp h) fun _ h₁ =>
    WP.seq (WP.mono (decL2_wp hp v h₁) fun _ h₂ =>
      WP.assoc (WP.assoc (WP.seq (WP.mono (decL3_wp hp h₂ hB) fun _ h₃ => decLast_wp hp v h₃ hB)))))

theorem split_tw_wp {s : State} (h : TwPost s₀ s) :
    WP isa (.block split) s fun s' => TwPost s₀ s' ∧ s'.zf = some (decide (B s₀ = 0)) :=
  split_wp h.inv fun _ _ _ zf₂ g₂ mem₂ rd₂ wr₂ =>
    ⟨TwPost.keep hp h (fun r hr => g₂ r (pinned_ne hr).1 (pinned_ne hr).2.2.2.1) mem₂ rd₂ wr₂, zf₂⟩

/-- The data unit of whole blocks, after the out-of-place call on all of them. -/
theorem allPost_fin {enc : Bool} {s : State} (h : AllPost enc s₀ (M s₀) s) (hb : B s₀ = 0) : Fin enc s₀ s :=
  whole_fin ⟨h.inv, by rw [vmem_blocks hp (by rw [len_eq s₀]; omega)]; exact h.out, h.tw, by
    rw [show Len s₀ - 16 * M s₀ = 0 by rw [len_eq s₀, hb]; omega]; rfl⟩ hb

theorem decrypt_wp (v : UnitImpl) :
    WP isa (decryptTo v.x.xts v.xt) s₀ fun s' => gprPreserved s₀ s' ∧ (unitToX86_64 false).post s₀ s' := by
  refine WP.seq (WP.mono (tweak_wp hp v.x.encOk v.x.encNosp v.x.encDepth) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (split_tw_wp hp h₁) fun s₂ ⟨h₂, zf₂⟩ => ?_)
  refine WP.seq (WP.mono (WP.ite (Q := Fin false s₀) (decide (B s₀ = 0)) zf₂ (fun hb => ?_) (fun hb => ?_))
    fun s₅ h₅ => ?_)
  · refine WP.seq (WP.mono (argsAll_wp hp h₂) fun s₃ h₃ => ?_)
    exact WP.mono (blocks_call hp false v.decToOk v.decToNosp v.decToDepth (by rw [len_eq s₀]; omega) h₃.tw h₃.pre)
      fun s₄ h₄ => allPost_fin hp h₄ (by simpa using hb)
  · refine WP.seq (WP.mono (argsHead_wp hp h₂) fun s₃ h₃ => ?_)
    refine WP.seq (WP.mono (blocks_call hp false v.decToOk v.decToNosp v.decToDepth (by rw [len_eq s₀]; omega)
      h₃.tw h₃.pre) fun s₄ h₄ => ?_)
    exact WP.seq (WP.mono (copiedHead_wp hp h₄) fun s₆ h₆ => decStealTail_wp hp v h₆ (by simpa using hb))
  · exact WP.mono (fin_wp hp h₅.inv) fun s' ⟨g, m⟩ => ⟨g, unit_post hp (by rw [m]; exact h₅.data)⟩

end

end VG.Proof.AesXts.X86_64.UnitTo
