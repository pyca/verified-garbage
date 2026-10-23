module

public import VerifiedGarbage.Impl.AesXts.PPC64LEUnit
public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.Framework.Offset

/-!
# XTS-AES of data units on PPC64LE: the contract the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Xts/Contract.lean`, which imply `unitPPC64LE`
(`Verified.lean`): `(schedule = r3, tweak_schedule = r4, rounds = r5,
i = r6, data = r7, len = r8, scratch = r9)`. A call (`bl`) stores nothing in
memory, so no stack is used.

`UPre` names the facts of the precondition; the regions of the scratch
buffer (`tR`, `zR`, `wkR`, the slots of the saved registers) are apart from
each other and from everything else, as on AArch64
(`Proof/AesXts/AArch64/Unit/Contract.lean`).
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE.Unit

open VG VG.PPC64LE
open VG.Spec.Aes (bytesAt)

section
variable (s : State)

abbrev W : Addr := s.gpr .r3
abbrev K : Addr := s.gpr .r4
abbrev R : Nat := (s.gpr .r5).toNat
abbrev I : Addr := s.gpr .r6
abbrev D : Addr := s.gpr .r7
abbrev Len : Nat := (s.gpr .r8).toNat
abbrev S : Addr := s.gpr .r9

abbrev schR : Region := ⟨W s, 240⟩
abbrev tschR : Region := ⟨K s, 240⟩
abbrev iR : Region := ⟨I s, 16⟩
abbrev dataR : Region := ⟨D s, Len s⟩
abbrev scrR : Region := ⟨S s, 2432⟩

/-- The tweak, the second tweak, and the working space of the calls, in the
scratch buffer. -/
abbrev tR : Region := ⟨S s + BitVec.ofNat 64 Impl.AesXts.PPC64LEUnit.tO, 16⟩
abbrev zR : Region := ⟨S s + BitVec.ofNat 64 Impl.AesXts.PPC64LEUnit.zO, 16⟩
abbrev wkR : Region := ⟨S s, 2176⟩

/-- The number of whole blocks, the bytes after them, and the last whole block. -/
abbrev M : Nat := Len s / 16
abbrev B : Nat := Len s % 16
abbrev L : Addr := D s + BitVec.ofNat 64 (16 * (M s - 1))

end

/-- What the functions need: the permissions, the buffers apart, `rounds`
of 10, 12 or 14, and a data unit of 16 bytes to 2²⁰ blocks. -/
def unitPre (s : State) : Prop :=
  s.rd = [schR s, tschR s, iR s] ∧ s.wr = [dataR s, scrR s] ∧
    (schR s).Disjoint (dataR s) ∧ (schR s).Disjoint (scrR s) ∧ (tschR s).Disjoint (dataR s) ∧
    (tschR s).Disjoint (scrR s) ∧ (iR s).Disjoint (dataR s) ∧ (iR s).Disjoint (scrR s) ∧
    (dataR s).Disjoint (scrR s) ∧
    (I s).toNat + 16 ≤ 2 ^ 64 ∧ (D s).toNat + Len s ≤ 2 ^ 64 ∧ (S s).toNat + 2432 ≤ 2 ^ 64 ∧
    (R s = 10 ∨ R s = 12 ∨ R s = 14) ∧ 16 ≤ Len s ∧ Len s ≤ 16 * Spec.Xts.maxBlocks

/-- XTS-AES of the data unit in a direction. -/
def xtsOf : Bool → List Byte → List Byte → List Byte → Option (List Byte)
  | true => Spec.Xts.aesXtsEncrypt
  | false => Spec.Xts.aesXtsDecrypt

def unitPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.sp = s₂.sp

/-- `vg_aes_xts_encrypt_unit` (`enc`) or `vg_aes_xts_decrypt_unit`. -/
def unitPPC64LE (enc : Bool) : Contract isa where
  pre := unitPre
  post s s' := ∀ key, Spec.Xts.KeySchedules s.mem (s.gpr .r3) (s.gpr .r4) (s.gpr .r5).toNat key →
    xtsOf enc key (bytesAt s.mem (s.gpr .r6) 16) (bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) =
      some (bytesAt s'.mem (s.gpr .r7) (s.gpr .r8).toNat)
  pub := unitPub

/-- The precondition, by name. -/
structure UPre (s : State) : Prop where
  rd : s.rd = [schR s, tschR s, iR s]
  wr : s.wr = [dataR s, scrR s]
  sch_data : (schR s).Disjoint (dataR s)
  sch_scr : (schR s).Disjoint (scrR s)
  tsch_data : (tschR s).Disjoint (dataR s)
  tsch_scr : (tschR s).Disjoint (scrR s)
  i_data : (iR s).Disjoint (dataR s)
  i_scr : (iR s).Disjoint (scrR s)
  data_scr : (dataR s).Disjoint (scrR s)
  i_wrap : (I s).toNat + 16 ≤ 2 ^ 64
  data_wrap : (D s).toNat + Len s ≤ 2 ^ 64
  scr_wrap : (S s).toNat + 2432 ≤ 2 ^ 64
  rounds : R s = 10 ∨ R s = 12 ∨ R s = 14
  len_lo : 16 ≤ Len s
  len_hi : Len s ≤ 16 * Spec.Xts.maxBlocks

theorem UPre.of {s : State} (h : unitPre s) : UPre s :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩

/-! ## Regions -/

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x h => h₂ x (h₁ x h)

section
variable {s : State} (hp : UPre s)
include hp

theorem UPre.m_pos : 1 ≤ M s := by have := hp.len_lo; simp only [M]; omega

theorem UPre.m_lt : M s < 2 ^ 60 := by
  have := hp.len_hi; simp only [M, Spec.Xts.maxBlocks] at *; omega

omit hp in
theorem len_eq (s : State) : Len s = 16 * M s + B s := by simp only [M, B]; omega

omit hp in
theorem scr_sub {d n : Nat} (h : d + n ≤ 2432) : Region.Sub ⟨S s + BitVec.ofNat 64 d, n⟩ (scrR s) :=
  Offset.sub_base _ h

omit hp in
theorem data_sub {d n : Nat} (h : d + n ≤ Len s) : Region.Sub ⟨D s + BitVec.ofNat 64 d, n⟩ (dataR s) :=
  Offset.sub_base _ h

omit hp in
theorem wk_sub : Region.Sub (wkR s) (scrR s) := Region.sub_prefix (by decide)

theorem UPre.t_wk : (tR s).Disjoint (wkR s) :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; simp only [Impl.AesXts.PPC64LEUnit.tO]; omega)

theorem UPre.z_wk : (zR s).Disjoint (wkR s) :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; simp only [Impl.AesXts.PPC64LEUnit.zO]; omega)

theorem UPre.t_z : (tR s).Disjoint (zR s) :=
  Offset.disjoint _ (by simp only [Impl.AesXts.PPC64LEUnit.tO, Impl.AesXts.PPC64LEUnit.zO]; omega)
    (by have := hp.scr_wrap; simp only [Impl.AesXts.PPC64LEUnit.tO]; omega)
    (by have := hp.scr_wrap; simp only [Impl.AesXts.PPC64LEUnit.zO]; omega)

omit hp in
/-- The slots of the saved registers. -/
theorem slot_sub (d : Nat) (h₁ : 2208 ≤ d) (h₂ : d + 8 ≤ 2264) :
    Region.Sub ⟨S s + BitVec.ofNat 64 d, 8⟩ ⟨S s + BitVec.ofNat 64 2208, 56⟩ :=
  Offset.sub _ h₁ (by omega)

/-- Everything the code writes but the slots lies within the data or the
first 2208 bytes of the scratch buffer. -/
theorem UPre.slots_disj {r : Region} (hr : Region.Sub r (dataR s) ∨ Region.Sub r ⟨S s, 2208⟩) :
    (⟨S s + BitVec.ofNat 64 2208, 56⟩ : Region).Disjoint r := by
  have slot : Region.Sub ⟨S s + BitVec.ofNat 64 2208, 56⟩ (scrR s) := scr_sub (by decide)
  rcases hr with h | h
  · exact (hp.data_scr.symm.sub_left slot).sub_right h
  · exact (Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)).sub_right h

omit hp in
theorem t_sub : Region.Sub (tR s) ⟨S s, 2208⟩ := Offset.sub_base _ (by decide)
omit hp in
theorem z_sub : Region.Sub (zR s) ⟨S s, 2208⟩ := Offset.sub_base _ (by decide)
omit hp in
theorem wk_sub' : Region.Sub (wkR s) ⟨S s, 2208⟩ := Region.sub_prefix (by decide)
omit hp in
theorem s_sub : Region.Sub ⟨S s, 2208⟩ (scrR s) := Region.sub_prefix (by decide)

theorem UPre.l_sub : Region.Sub ⟨L s, 16⟩ (dataR s) := data_sub (by have := len_eq s; have := hp.m_pos; omega)

theorem UPre.l_wrap : (L s).toNat + 16 ≤ 2 ^ 64 := by
  have := hp.data_wrap; have := len_eq s; have := hp.m_pos
  rw [L, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * (M s - 1)) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

end

/-! ## The parts of the data unit -/

section
variable {s : State} (hp : UPre s)
include hp

theorem UPre.wrapD : (D s).toNat + 16 * M s + B s ≤ 2 ^ 64 := by
  have := hp.data_wrap; have := len_eq s; omega

omit hp in
theorem blocks_sub {N : Nat} (h : N ≤ M s) : Region.Sub ⟨D s, 16 * N⟩ (dataR s) :=
  Region.sub_prefix (by have := len_eq s; omega)

theorem UPre.lb_sub : Region.Sub ⟨L s, 16 + B s⟩ (dataR s) :=
  data_sub (by have := len_eq s; have := hp.m_pos; omega)

theorem UPre.tl_eq : L s + 16 = D s + BitVec.ofNat 64 (16 * M s) := by
  rw [L, Proof.AesXts.Unit.add16, show 16 * (M s - 1) + 16 = 16 * M s by have := hp.m_pos; omega]

theorem UPre.tl_sub : Region.Sub ⟨L s + 16, B s⟩ (dataR s) := by
  rw [hp.tl_eq]; exact data_sub (by have := len_eq s; omega)

theorem UPre.hd_lb : (⟨D s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s, 16 + B s⟩ :=
  Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.wrapD; have := hp.m_pos; omega)

theorem UPre.hd_l : (⟨D s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s, 16⟩ :=
  hp.hd_lb.sub_right (Region.sub_prefix (by omega))

theorem UPre.hd_tl : (⟨D s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s + 16, B s⟩ := by
  rw [hp.tl_eq]
  exact Offset.base_disjoint _ (by omega) (by have := hp.wrapD; omega)

omit hp in
theorem tl_l : (⟨L s + 16, B s⟩ : Region).Disjoint ⟨L s, 16⟩ :=
  Offset.disjoint_base (L s) (d := 16) (n := B s) (k := 16) (Nat.le_refl _) (by simp only [B]; omega)

theorem UPre.tl_blocks : (⟨L s + 16, B s⟩ : Region).Disjoint ⟨D s, 16 * M s⟩ := by
  rw [hp.tl_eq]
  exact Offset.disjoint_base _ (Nat.le_refl _) (by have := hp.wrapD; omega)

theorem UPre.l_hd : (⟨L s, 16⟩ : Region).Disjoint ⟨D s, 16 * (M s - 1)⟩ := hp.hd_l.symm

end

end VG.Proof.AesXts.PPC64LE.Unit
