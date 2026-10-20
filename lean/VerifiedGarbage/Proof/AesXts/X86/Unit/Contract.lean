module

import VerifiedGarbage.Proof.AesXts.Unit
public import VerifiedGarbage.Impl.AesXts.X86Unit
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Spec.Xts.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# XTS-AES of data units on x86 (32-bit): the contract the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Xts/Contract.lean` with 52 bytes of stack, which
imply `unitX86` (`Verified.lean`): every argument on the stack, from
`[esp + 4]` (cdecl).

`UPre` names the facts of the precondition; the regions of the scratch
buffer (`tR`, `zR`, `wkR`, the slots of the saved registers) are apart from
each other and from everything else.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86.Unit

open VG VG.X86
open VG.Spec.Aes (bytesAt)

section
variable (s : State)

abbrev E : BitVec 32 := s.gpr .esp
abbrev W : BitVec 32 := arg s 0
abbrev K : BitVec 32 := arg s 1
abbrev R : Nat := (arg s 2).toNat
abbrev I : BitVec 32 := arg s 3
abbrev D : BitVec 32 := arg s 4
abbrev Len : Nat := (arg s 5).toNat
abbrev S : BitVec 32 := arg s 6

/-- The scratch buffer and the data, as addresses. -/
abbrev Sa : Addr := (S s).setWidth 64
abbrev Da : Addr := (D s).setWidth 64

abbrev schR : Region := ⟨(W s).setWidth 64, 240⟩
abbrev tschR : Region := ⟨(K s).setWidth 64, 240⟩
abbrev iR : Region := ⟨(I s).setWidth 64, 16⟩
abbrev dataR : Region := ⟨Da s, Len s⟩
abbrev scrR : Region := ⟨Sa s, 2432⟩
abbrev argsR : Region := ⟨argAddr s 0, 28⟩
abbrev retR : Region := ⟨(E s).setWidth 64, 4⟩
/-- The 52 bytes of stack below `esp` the calls use. -/
abbrev stkR : Region := ⟨(E s).setWidth 64 - BitVec.ofNat 64 52, 52⟩

/-- The tweak, the second tweak, and the working space of the calls, in the
scratch buffer. -/
abbrev tR : Region := ⟨Sa s + BitVec.ofNat 64 Impl.AesXts.X86Unit.tO, 16⟩
abbrev zR : Region := ⟨Sa s + BitVec.ofNat 64 Impl.AesXts.X86Unit.zO, 16⟩
abbrev wkR : Region := ⟨Sa s, 2176⟩

/-- The number of whole blocks, the bytes after them, and the last whole block. -/
abbrev M : Nat := Len s / 16
abbrev B : Nat := Len s % 16
abbrev L : Addr := Da s + BitVec.ofNat 64 (16 * (M s - 1))

end

/-- What the functions need: the permissions, the buffers apart, from the
arguments on the stack, the return address and the 52 bytes below it,
`rounds` of 10, 12 or 14, and a data unit of 16 bytes to 2²⁰ blocks. -/
def unitPre (s : State) : Prop :=
  (52 ≤ (E s).toNat ∧ (E s).toNat + 4 + 28 ≤ 2 ^ 32) ∧
    s.rd = [schR s, tschR s, iR s, argsR s] ∧ s.wr = [dataR s, scrR s] ∧
    (schR s).Disjoint (dataR s) ∧ (schR s).Disjoint (scrR s) ∧ (tschR s).Disjoint (dataR s) ∧
    (tschR s).Disjoint (scrR s) ∧ (iR s).Disjoint (dataR s) ∧ (iR s).Disjoint (scrR s) ∧
    (dataR s).Disjoint (scrR s) ∧ (dataR s).Disjoint (argsR s) ∧ (scrR s).Disjoint (argsR s) ∧
    (retR s).Disjoint (schR s) ∧ (retR s).Disjoint (tschR s) ∧ (retR s).Disjoint (iR s) ∧
    (retR s).Disjoint (dataR s) ∧ (retR s).Disjoint (scrR s) ∧ (retR s).Disjoint (argsR s) ∧
    (stkR s).Disjoint (schR s) ∧ (stkR s).Disjoint (tschR s) ∧ (stkR s).Disjoint (iR s) ∧
    (stkR s).Disjoint (dataR s) ∧ (stkR s).Disjoint (scrR s) ∧ (stkR s).Disjoint (argsR s) ∧
    (W s).toNat + 240 ≤ 2 ^ 32 ∧ (K s).toNat + 240 ≤ 2 ^ 32 ∧ (I s).toNat + 16 ≤ 2 ^ 32 ∧
    (D s).toNat + Len s ≤ 2 ^ 32 ∧ (S s).toNat + 2432 ≤ 2 ^ 32 ∧
    (R s = 10 ∨ R s = 12 ∨ R s = 14) ∧ 16 ≤ Len s ∧ Len s ≤ 16 * Spec.Xts.maxBlocks

/-- XTS-AES of the data unit in a direction. -/
def xtsOf : Bool → List Byte → List Byte → List Byte → Option (List Byte)
  | true => Spec.Xts.aesXtsEncrypt
  | false => Spec.Xts.aesXtsDecrypt

def unitPub (s₁ s₂ : State) : Prop := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 7, arg s₁ i = arg s₂ i

/-- `vg_aes_xts_encrypt_unit` (`enc`) or `vg_aes_xts_decrypt_unit`. -/
def unitX86 (enc : Bool) : Contract isa where
  pre := unitPre
  post s s' := ∀ key, Spec.Xts.KeySchedules s.mem ((arg s 0).setWidth 64) ((arg s 1).setWidth 64)
      (arg s 2).toNat key →
    xtsOf enc key (bytesAt s.mem ((arg s 3).setWidth 64) 16)
        (bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat) =
      some (bytesAt s'.mem ((arg s 4).setWidth 64) (arg s 5).toNat)
  pub := unitPub

/-- The precondition, by name. -/
structure UPre (s : State) : Prop where
  esp52 : 52 ≤ (E s).toNat
  esp_fit : (E s).toNat + 4 + 28 ≤ 2 ^ 32
  rd : s.rd = [schR s, tschR s, iR s, argsR s]
  wr : s.wr = [dataR s, scrR s]
  sch_data : (schR s).Disjoint (dataR s)
  sch_scr : (schR s).Disjoint (scrR s)
  tsch_data : (tschR s).Disjoint (dataR s)
  tsch_scr : (tschR s).Disjoint (scrR s)
  i_data : (iR s).Disjoint (dataR s)
  i_scr : (iR s).Disjoint (scrR s)
  data_scr : (dataR s).Disjoint (scrR s)
  data_args : (dataR s).Disjoint (argsR s)
  scr_args : (scrR s).Disjoint (argsR s)
  ret_sch : (retR s).Disjoint (schR s)
  ret_tsch : (retR s).Disjoint (tschR s)
  ret_i : (retR s).Disjoint (iR s)
  ret_data : (retR s).Disjoint (dataR s)
  ret_scr : (retR s).Disjoint (scrR s)
  ret_args : (retR s).Disjoint (argsR s)
  stk_sch : (stkR s).Disjoint (schR s)
  stk_tsch : (stkR s).Disjoint (tschR s)
  stk_i : (stkR s).Disjoint (iR s)
  stk_data : (stkR s).Disjoint (dataR s)
  stk_scr : (stkR s).Disjoint (scrR s)
  stk_args : (stkR s).Disjoint (argsR s)
  sch_fit : (W s).toNat + 240 ≤ 2 ^ 32
  tsch_fit : (K s).toNat + 240 ≤ 2 ^ 32
  i_fit : (I s).toNat + 16 ≤ 2 ^ 32
  data_fit : (D s).toNat + Len s ≤ 2 ^ 32
  scr_fit : (S s).toNat + 2432 ≤ 2 ^ 32
  rounds : R s = 10 ∨ R s = 12 ∨ R s = 14
  len_lo : 16 ≤ Len s
  len_hi : Len s ≤ 16 * Spec.Xts.maxBlocks

theorem UPre.of {s : State} (h : unitPre s) : UPre s :=
  let ⟨⟨a, b⟩, c, d, e, f, g, h, i, j, k, l, m, r₁, r₂, r₃, r₄, r₅, r₆, n, o, p, q, r, t, u, v, w, x, y, z, a',
    b'⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, r₁, r₂, r₃, r₄, r₅, r₆, n, o, p, q, r, t, u, v, w, x, y, z, a', b'⟩

/-! ## Regions -/

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x h => h₂ x (h₁ x h)

theorem addr_toNat (a : BitVec 32) : (a.setWidth 64).toNat = a.toNat := by
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

section
variable {s : State} (hp : UPre s)
include hp

theorem UPre.m_pos : 1 ≤ M s := by have := hp.len_lo; simp only [M]; omega

theorem UPre.m_lt : M s < 2 ^ 28 := by
  have := hp.len_hi; simp only [M, Spec.Xts.maxBlocks] at *; omega

omit hp in
theorem len_eq (s : State) : Len s = 16 * M s + B s := by simp only [M, B]; omega

/-- An offset of the scratch buffer, as an address. -/
theorem UPre.scrA {d : Nat} (hd : d < 2432) : addr (S s) d = Sa s + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.scr_fit; omega)

/-- An offset of the data, as an address. -/
theorem UPre.dataA {d : Nat} (hd : d < Len s) : addr (D s) d = Da s + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.data_fit; omega)

theorem UPre.scr_wrap : (Sa s).toNat + 2432 ≤ 2 ^ 32 := by rw [addr_toNat]; exact hp.scr_fit

theorem UPre.data_wrap : (Da s).toNat + Len s ≤ 2 ^ 32 := by rw [addr_toNat]; exact hp.data_fit

omit hp in
theorem scr_sub {d n : Nat} (h : d + n ≤ 2432) : Region.Sub ⟨Sa s + BitVec.ofNat 64 d, n⟩ (scrR s) :=
  Offset.sub_base _ h

omit hp in
theorem data_sub {d n : Nat} (h : d + n ≤ Len s) : Region.Sub ⟨Da s + BitVec.ofNat 64 d, n⟩ (dataR s) :=
  Offset.sub_base _ h

omit hp in
theorem wk_sub : Region.Sub (wkR s) (scrR s) := Region.sub_prefix (by decide)

theorem UPre.t_wk : (tR s).Disjoint (wkR s) :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; simp only [Impl.AesXts.X86Unit.tO]; omega)

theorem UPre.z_wk : (zR s).Disjoint (wkR s) :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; simp only [Impl.AesXts.X86Unit.zO]; omega)

theorem UPre.t_z : (tR s).Disjoint (zR s) :=
  Offset.disjoint _ (by simp only [Impl.AesXts.X86Unit.tO, Impl.AesXts.X86Unit.zO]; omega)
    (by have := hp.scr_wrap; simp only [Impl.AesXts.X86Unit.tO]; omega)
    (by have := hp.scr_wrap; simp only [Impl.AesXts.X86Unit.zO]; omega)

omit hp in
/-- The slots of the saved registers. -/
theorem slot_sub (d : Nat) (h₁ : 2208 ≤ d) (h₂ : d + 4 ≤ 2224) :
    Region.Sub ⟨Sa s + BitVec.ofNat 64 d, 4⟩ ⟨Sa s + BitVec.ofNat 64 2208, 16⟩ :=
  Offset.sub _ h₁ (by omega)

/-- Everything the code writes but the slots lies within the data, the
first 2208 bytes of the scratch buffer or the stack below `esp`. -/
theorem UPre.slots_disj {r : Region}
    (hr : Region.Sub r (dataR s) ∨ Region.Sub r ⟨Sa s, 2208⟩ ∨ Region.Sub r (stkR s)) :
    (⟨Sa s + BitVec.ofNat 64 2208, 16⟩ : Region).Disjoint r := by
  have slot : Region.Sub ⟨Sa s + BitVec.ofNat 64 2208, 16⟩ (scrR s) := scr_sub (by decide)
  rcases hr with h | h | h
  · exact (hp.data_scr.symm.sub_left slot).sub_right h
  · exact (Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)).sub_right h
  · exact (hp.stk_scr.symm.sub_left slot).sub_right h

omit hp in
theorem t_sub : Region.Sub (tR s) ⟨Sa s, 2208⟩ := Offset.sub_base _ (by decide)
omit hp in
theorem z_sub : Region.Sub (zR s) ⟨Sa s, 2208⟩ := Offset.sub_base _ (by decide)
omit hp in
theorem s_sub : Region.Sub ⟨Sa s, 2208⟩ (scrR s) := Region.sub_prefix (by decide)

theorem UPre.l_sub : Region.Sub ⟨L s, 16⟩ (dataR s) := data_sub (by have := len_eq s; have := hp.m_pos; omega)

theorem UPre.l_wrap : (L s).toNat + 16 ≤ 2 ^ 32 := by
  have := hp.data_wrap; have := len_eq s; have := hp.m_pos
  rw [L, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * (M s - 1)) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

end

/-! ## The parts of the data unit -/

section
variable {s : State} (hp : UPre s)
include hp

theorem UPre.wrapD : (Da s).toNat + 16 * M s + B s ≤ 2 ^ 32 := by
  have := hp.data_wrap; have := len_eq s; omega

omit hp in
theorem blocks_sub {N : Nat} (h : N ≤ M s) : Region.Sub ⟨Da s, 16 * N⟩ (dataR s) :=
  Region.sub_prefix (by have := len_eq s; omega)

theorem UPre.lb_sub : Region.Sub ⟨L s, 16 + B s⟩ (dataR s) :=
  data_sub (by have := len_eq s; have := hp.m_pos; omega)

theorem UPre.tl_eq : L s + 16 = Da s + BitVec.ofNat 64 (16 * M s) := by
  rw [L, Proof.AesXts.Unit.add16, show 16 * (M s - 1) + 16 = 16 * M s by have := hp.m_pos; omega]

theorem UPre.tl_sub : Region.Sub ⟨L s + 16, B s⟩ (dataR s) := by
  rw [hp.tl_eq]; exact data_sub (by have := len_eq s; omega)

theorem UPre.hd_lb : (⟨Da s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s, 16 + B s⟩ :=
  Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.wrapD; have := hp.m_pos; omega)

theorem UPre.hd_l : (⟨Da s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s, 16⟩ :=
  hp.hd_lb.sub_right (Region.sub_prefix (by omega))

theorem UPre.hd_tl : (⟨Da s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s + 16, B s⟩ := by
  rw [hp.tl_eq]
  exact Offset.base_disjoint _ (by omega) (by have := hp.wrapD; omega)

omit hp in
theorem tl_l : (⟨L s + 16, B s⟩ : Region).Disjoint ⟨L s, 16⟩ :=
  Offset.disjoint_base (L s) (d := 16) (n := B s) (k := 16) (Nat.le_refl _) (by simp only [B]; omega)

theorem UPre.tl_blocks : (⟨L s + 16, B s⟩ : Region).Disjoint ⟨Da s, 16 * M s⟩ := by
  rw [hp.tl_eq]
  exact Offset.disjoint_base _ (Nat.le_refl _) (by have := hp.wrapD; omega)

theorem UPre.l_hd : (⟨L s, 16⟩ : Region).Disjoint ⟨Da s, 16 * (M s - 1)⟩ := hp.hd_l.symm

end

end VG.Proof.AesXts.X86.Unit
