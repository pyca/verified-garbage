module
public import Batteries.Logic
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace

import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.Bignum.Arm.Sub
import VerifiedGarbage.Impl.Bignum.Arm.Shift
import VerifiedGarbage.Impl.Bignum.Arm.Zero

/-! # What holds throughout an ARMv7 Montgomery square

The square works in `4 * (2 * n + 8)` bytes at offset `M` of the workspace (arrays 2
and 3): six words of metadata, then `T`'s `2n + 2` words at `M + 24`. Every
other byte keeps its value from the entry memory `m0`, which holds the
workspace pointer at `sp` and the header's pointers. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure SqEnv (m0 : Mem) (base : BitVec 32) (size out a mod M n : Nat) (inv : BitVec 32)
    (s : State) : Prop where
  workspace : Workspace s base size
  count : 4 ≤ n
  header : 256 ≤ M
  fits : M + 4 * (2 * n + 8) ≤ size
  aFits : a + 4 * n ≤ size
  mFits : mod + 4 * n ≤ size
  outFits : out + 4 * n ≤ size
  sepA : M + 4 * (2 * n + 8) ≤ a ∨ a + 4 * n ≤ M
  sepM : M + 4 * (2 * n + 8) ≤ mod ∨ mod + 4 * n ≤ M
  sepO : M + 4 * (2 * n + 8) ≤ out ∨ out + 4 * n ≤ M
  frame : Outs (State.addr base) [(M, 4 * (2 * n + 8))] m0 s.mem
  stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4
  stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, size⟩
  saved : m0.readW (State.addr s.sp) 32 = base
  metaPtr : m0.readW (off (State.addr base) 80) 32 = base + BitVec.ofNat 32 M
  modPtr : m0.readW (off (State.addr base) 64) 32 = base + BitVec.ofNat 32 mod
  inverse : m0.readW (off (State.addr base) 56) 32 = inv
  operand : val32 m0 (State.addr base) a n < val32 m0 (State.addr base) mod n
  invOk : (val32 m0 (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0

section
variable {m0 : Mem} {base : BitVec 32} {size out a mod M n : Nat} {inv : BitVec 32} {s t : State}

theorem SqEnv.next (h : SqEnv m0 base size out a mod M n inv s)
    (outs : Outs (State.addr base) [(M, 4 * (2 * n + 8))] s.mem t.mem) {rs : List Reg} (rest : Rest rs s t) :
    SqEnv m0 base size out a mod M n inv t :=
  { h with
    workspace := h.workspace.congr rest.wr
    frame := h.frame.trans outs
    stackRead := by rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead
    stackSep := by rw [rest.sp]; exact h.stackSep
    saved := by rw [rest.sp]; exact h.saved }

theorem SqEnv.of_mem (h : SqEnv m0 base size out a mod M n inv s) (mem : t.mem = s.mem)
    {rs : List Reg} (rest : Rest rs s t) : SqEnv m0 base size out a mod M n inv t :=
  h.next (by rw [mem]; exact Outs.refl _ _ _) rest

theorem SqEnv.nowrap (h : SqEnv m0 base size out a mod M n inv s) : base.toNat + size ≤ 2 ^ 32 :=
  h.workspace.nowrap

/-- Memory outside the square's bytes, in the whole workspace. -/
theorem SqEnv.wsFrame (h : SqEnv m0 base size out a mod M n inv s) :
    Frame [⟨State.addr base, size⟩] m0 s.mem := by
  have fits := h.fits
  intro x hx
  have hb := hx ⟨State.addr base, size⟩ (by simp)
  change ¬ ((x - State.addr base).toNat + 1 ≤ size) at hb
  apply h.frame
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [ofs]
  omega

/-- The workspace pointer at `sp`. -/
theorem SqEnv.savedNow (h : SqEnv m0 base size out a mod M n inv s) :
    s.mem.readW (State.addr s.sp) 32 = base := by
  have e := h.wsFrame.read (r := ⟨State.addr s.sp, 4⟩) (a := State.addr s.sp) (n := 4)
    (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.stackSep)
    (by decide)
  change (s.mem.read (State.addr s.sp) 4).setWidth 32 = base
  rw [e]
  exact h.saved

/-- A word outside the square's bytes. -/
theorem SqEnv.word (h : SqEnv m0 base size out a mod M n inv s) {d : Nat}
    (hd : d + 4 ≤ M ∨ M + 4 * (2 * n + 8) ≤ d) (fit : d + 4 ≤ size) :
    s.mem.readW (off (State.addr base) d) 32 = m0.readW (off (State.addr base) d) 32 := by
  have nowrap := h.nowrap
  apply BitVec.eq_of_toNat_eq
  exact outs_word32 h.frame (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp only; omega) (by omega)

theorem SqEnv.metaNow (h : SqEnv m0 base size out a mod M n inv s) :
    s.mem.readW (off (State.addr base) 80) 32 = base + BitVec.ofNat 32 M := by
  have := h.header; have := h.fits
  rw [h.word (by omega) (by omega)]; exact h.metaPtr

theorem SqEnv.modNow (h : SqEnv m0 base size out a mod M n inv s) :
    s.mem.readW (off (State.addr base) 64) 32 = base + BitVec.ofNat 32 mod := by
  have := h.header; have := h.fits
  rw [h.word (by omega) (by omega)]; exact h.modPtr

theorem SqEnv.invNow (h : SqEnv m0 base size out a mod M n inv s) :
    s.mem.readW (off (State.addr base) 56) 32 = inv := by
  have := h.header; have := h.fits
  rw [h.word (by omega) (by omega)]; exact h.inverse

/-- The operand's words. -/
theorem SqEnv.aWord (h : SqEnv m0 base size out a mod M n inv s) {j : Nat} (hj : j < n) :
    w32 s.mem (State.addr base) (a + 4 * j) = w32 m0 (State.addr base) (a + 4 * j) := by
  have := h.sepA; have := h.aFits
  exact congrArg BitVec.toNat (h.word (by omega) (by omega))

theorem SqEnv.aVal (h : SqEnv m0 base size out a mod M n inv s) {d k : Nat}
    (hd : a ≤ d) (hk : d + 4 * k ≤ a + 4 * n) :
    val32 s.mem (State.addr base) d k = val32 m0 (State.addr base) d k := by
  have := h.sepA; have := h.aFits; have := h.nowrap
  exact h.frame.val32 (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp only; omega) (by omega)

theorem SqEnv.modVal (h : SqEnv m0 base size out a mod M n inv s) :
    val32 s.mem (State.addr base) mod n = val32 m0 (State.addr base) mod n := by
  have := h.sepM; have := h.mFits; have := h.nowrap
  exact h.frame.val32 (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp only; omega) (by omega)

/-- An address in the workspace. -/
theorem SqEnv.ea (h : SqEnv m0 base size out a mod M n inv s) {d imm : Nat} {r : Reg}
    (hp : s.gpr r = base + BitVec.ofNat 32 d) (hd : d + imm < size) :
    State.addr (s.gpr r + BitVec.ofNat 32 imm) = off (State.addr base) (d + imm) :=
  h.workspace.ea hp hd

theorem SqEnv.read (h : SqEnv m0 base size out a mod M n inv s) {d : Nat} (hd : d + 4 ≤ size) :
    InRegions (s.rd ++ s.wr) (off (State.addr base) d) 4 :=
  h.workspace.read hd

theorem SqEnv.write (h : SqEnv m0 base size out a mod M n inv s) {d : Nat} (hd : d + 4 ≤ size) :
    InRegions s.wr (off (State.addr base) d) 4 :=
  h.workspace.write hd

end

/-! ## Memory facts -/

/-- The address `[x, #imm]` for `x` at offset `d` of the workspace. -/
theorem sq_ea {base : BitVec 32} {size : Nat} (nowrap : base.toNat + size ≤ 2 ^ 32) {x : BitVec 32}
    {d imm : Nat} (hp : x = base + BitVec.ofNat 32 d) (hd : d + imm < size) :
    State.addr (x + BitVec.ofNat 32 imm) = off (State.addr base) (d + imm) := by
  rw [hp, Offset.add_add]
  exact VG.Arm.addr_add (by omega)

/-- The address `[x, #imm]` for `x` the workspace's base. -/
theorem sq_ea0 {base : BitVec 32} {size : Nat} (nowrap : base.toNat + size ≤ 2 ^ 32) {x : BitVec 32}
    {imm : Nat} (hp : x = base) (hd : imm < size) :
    State.addr (x + BitVec.ofNat 32 imm) = off (State.addr base) imm := by
  rw [hp]
  exact VG.Arm.addr_add (by omega)

/-- A left shift of a small number. -/
theorem ofNat_shl {n k : Nat} (h : n * 2 ^ k < 2 ^ 32) :
    BitVec.ofNat 32 n <<< k = BitVec.ofNat 32 (n * 2 ^ k) := by
  have hn : n < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right n (Nat.two_pow_pos k)) h
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.X25519.Arm.toNat_shl, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-- The tail of a zero number. -/
theorem val32_zero_tail {m : Mem} {b : Addr} {d i j : Nat} (h : val32 m b d (i + j) = 0) :
    val32 m b (d + 4 * i) j = 0 := by
  rw [val32_append] at h
  have hp : 0 < 2 ^ (32 * i) := Nat.two_pow_pos _
  rcases Nat.eq_zero_or_pos (val32 m b (d + 4 * i) j) with e | e
  · exact e
  · have : 2 ^ (32 * i) * 1 ≤ 2 ^ (32 * i) * val32 m b (d + 4 * i) j := Nat.mul_le_mul_left _ e
    omega

/-- A store's word read back. -/
theorem rd_self (m : Mem) (b : Addr) (d : Nat) (v : BitVec 32) :
    (m.writeW (off b d) v).readW (off b d) 32 = v :=
  Mem.readW_writeW_self32 _ _ _

/-- A word apart from a store. -/
theorem rd_other {m : Mem} {b : Addr} {d e : Nat} (v : BitVec 32) (hn : e + 4 ≤ 2 ^ 64)
    (hn' : d + 4 ≤ 2 ^ 64) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (off b d) v).readW (off b e) 32 = m.readW (off b e) 32 :=
  Mem.readW_writeW_sep (Offset.sep b (by omega) hn hn') (by decide)

/-- The metadata every phase keeps: `n`, the output and the operand. -/
structure SqMeta (mem : Mem) (base : BitVec 32) (out a M n : Nat) : Prop where
  count : mem.readW (off (State.addr base) M) 32 = BitVec.ofNat 32 n
  outPtr : mem.readW (off (State.addr base) (M + 4)) 32 = base + BitVec.ofNat 32 out
  aPtr : mem.readW (off (State.addr base) (M + 8)) 32 = base + BitVec.ofNat 32 a

theorem SqMeta.congr {mem mem' : Mem} {base : BitVec 32} {out a M n : Nat}
    (h : SqMeta mem base out a M n)
    (eq : ∀ d, d + 4 ≤ 12 → mem'.readW (off (State.addr base) (M + d)) 32 =
      mem.readW (off (State.addr base) (M + d)) 32) : SqMeta mem' base out a M n :=
  ⟨(eq 0 (by decide)).trans h.count, (eq 4 (by decide)).trans h.outPtr,
    (eq 8 (by decide)).trans h.aPtr⟩

theorem SqMeta.of_outs {mem mem' : Mem} {base : BitVec 32} {out a M n : Nat} {rs : List (Nat × Nat)}
    (h : SqMeta mem base out a M n) (outs : Outs (State.addr base) rs mem mem')
    (sep : ∀ r ∈ rs, M + 12 ≤ r.1 ∨ r.1 + r.2 ≤ M) (fit : M + 12 ≤ 2 ^ 64) :
    SqMeta mem' base out a M n :=
  h.congr fun d hd => BitVec.eq_of_toNat_eq (outs_word32 outs (by
    intro r hr; have := sep r hr; omega) (by omega))

end VG.Proof.Bignum.Arm
