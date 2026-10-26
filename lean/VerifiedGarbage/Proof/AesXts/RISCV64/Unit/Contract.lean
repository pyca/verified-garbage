module

public import VerifiedGarbage.Impl.AesXts.RISCV64Unit
public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.Framework.Offset

/-!
# XTS-AES of data units on RISC-V: the contract the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Xts/Contract.lean`, which imply `unitRISCV64`
(`Verified.lean`): `(schedule = a0, tweak_schedule = a1, rounds = a2,
i = a3, data = a4, len = a5, scratch = a6)`. A call (`jal`) stores nothing
in memory, and the return address is saved in the scratch buffer, so no
stack is used.

`UPre` names the facts of the precondition; the regions of the scratch
buffer (the tweaks `tzR`, the slots `slotR` of the saved registers, the
working space `wkR`) are apart from each other and from everything else, as
on PPC64LE (`Proof/AesXts/PPC64LE/Unit/Contract.lean`).
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64.Unit

open VG VG.RISCV64 VG.RISCV64.Align
open VG.Impl.AesXts.RISCV64Unit (tO zO wO)
open VG.Spec.Aes (bytesAt)

section
variable (s : State)

abbrev W : Addr := s.gpr .a0
abbrev K : Addr := s.gpr .a1
abbrev R : Nat := (s.gpr .a2).toNat
abbrev I : Addr := s.gpr .a3
abbrev D : Addr := s.gpr .a4
abbrev Len : Nat := (s.gpr .a5).toNat
abbrev S : Addr := s.gpr .a6

abbrev schR : Region := ⟨W s, 240⟩
abbrev tschR : Region := ⟨K s, 240⟩
abbrev iR : Region := ⟨I s, 16⟩
abbrev dataR : Region := ⟨D s, Len s⟩
abbrev scrR : Region := ⟨S s, 2432⟩

/-- The tweak, the second tweak, both of them, the working space of the
calls, and where the slots of the saved registers are, in the scratch
buffer. -/
abbrev tR : Region := ⟨S s + BitVec.ofNat 64 tO, 16⟩
abbrev zR : Region := ⟨S s + BitVec.ofNat 64 zO, 16⟩
abbrev tzR : Region := ⟨S s, 32⟩
abbrev Wk : Addr := S s + BitVec.ofNat 64 wO
abbrev wkR : Region := ⟨Wk s, 2176⟩
abbrev slotR : Region := ⟨S s + BitVec.ofNat 64 32, 64⟩

/-- The slots: `scratch + 32`, rounded up. -/
abbrev sv : Addr := S s + BitVec.ofNat 64 32 + BitVec.ofNat 64 (pad (S s + BitVec.ofNat 64 32))

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
  s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.sp = s₂.sp

/-- `vg_aes_xts_encrypt_unit` (`enc`) or `vg_aes_xts_decrypt_unit`. -/
def unitRISCV64 (enc : Bool) : Contract isa where
  pre := unitPre
  post s s' := ∀ key, Spec.Xts.KeySchedules s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2).toNat key →
    xtsOf enc key (bytesAt s.mem (s.gpr .a3) 16) (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) =
      some (bytesAt s'.mem (s.gpr .a4) (s.gpr .a5).toNat)
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

/-- The regions the code writes, but the slots. -/
abbrev Wr (s : State) : List Region := [dataR s, tzR s, wkR s]

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
theorem wk_sub : Region.Sub (wkR s) (scrR s) := scr_sub (by simp [wO])

omit hp in
theorem tz_sub : Region.Sub (tzR s) (scrR s) := Region.sub_prefix (by decide)

omit hp in
theorem slot_scr : Region.Sub (slotR s) (scrR s) := scr_sub (by decide)

omit hp in
theorem t_sub : Region.Sub (tR s) (tzR s) := by
  show Region.Sub ⟨S s + BitVec.ofNat 64 0, 16⟩ ⟨S s, 32⟩
  rw [show S s + BitVec.ofNat 64 0 = S s by simp]; exact Region.sub_prefix (by decide)

omit hp in
theorem z_sub : Region.Sub (zR s) (tzR s) := Offset.sub_base _ (by simp [zO])

theorem UPre.t_wk : (tR s).Disjoint (wkR s) :=
  Offset.disjoint _ (by simp [tO, wO]) (by have := hp.scr_wrap; simp only [tO]; omega)
    (by have := hp.scr_wrap; simp only [wO]; omega)

theorem UPre.z_wk : (zR s).Disjoint (wkR s) :=
  Offset.disjoint _ (by simp [zO, wO]) (by have := hp.scr_wrap; simp only [zO]; omega)
    (by have := hp.scr_wrap; simp only [wO]; omega)

theorem UPre.t_z : (tR s).Disjoint (zR s) :=
  Offset.disjoint _ (by simp [tO, zO]) (by have := hp.scr_wrap; simp only [tO]; omega)
    (by have := hp.scr_wrap; simp only [zO]; omega)

theorem UPre.slot_tz : (slotR s).Disjoint (tzR s) :=
  Offset.disjoint_base (S s) (d := 32) (n := 64) (k := 32) (Nat.le_refl _) (by have := hp.scr_wrap; omega)

theorem UPre.slot_wk : (slotR s).Disjoint (wkR s) :=
  Offset.disjoint _ (by simp [wO]) (by have := hp.scr_wrap; omega) (by have := hp.scr_wrap; simp only [wO]; omega)

theorem UPre.slot_data : (slotR s).Disjoint (dataR s) := hp.data_scr.symm.sub_left slot_scr

omit hp in
/-- The slots of the saved registers. -/
theorem sv_slot (d : Nat) (h : d + 8 ≤ 56) : Region.Sub ⟨sv s + BitVec.ofNat 64 d, 8⟩ (slotR s) := by
  have := pad_lt (S s + BitVec.ofNat 64 32)
  rw [align_add]
  exact Offset.sub _ (by omega) (by omega)

/-- Everything the code writes but the slots lies within the data, the
tweaks or the working space. -/
theorem UPre.slots_disj {r : Region} (hr : ∃ r' ∈ Wr s, Region.Sub r r') : (slotR s).Disjoint r := by
  obtain ⟨r', hr', hs⟩ := hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl
  · exact hp.slot_data.sub_right hs
  · exact hp.slot_tz.sub_right hs
  · exact hp.slot_wk.sub_right hs

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

end VG.Proof.AesXts.RISCV64.Unit
