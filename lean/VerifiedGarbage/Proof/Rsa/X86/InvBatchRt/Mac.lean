module

public import VerifiedGarbage.Impl.Rsa.X86.InvBatchRt
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! # One multiply-accumulate step through pointers

`macWord_ok`: `[ebp + d] += ecx · [edi + d] + ebx`, the carry into `ebx`
(`Mont.mulStep`'s arithmetic, `step_regs`); `macSet_ok`: the same without the
word's old value, for the first row of a product.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

variable {is : List Instr} {Q : State → Prop}

theorem macWord_ok {s : State} {W : Addr} {Z x y d : Nat} (hw : Ws s W Z)
    (px : PtrAt s W .edi x) (py : PtrAt s W .ebp y) (hx : x + d + 4 ≤ Z) (hy : y + d + 4 ≤ Z)
    (k : ∀ u, u.mem = s.mem.writeW (off W (y + d)) (BitVec.ofNat 32
        ((s.gpr .ecx).toNat * w32 s.mem W (x + d) + (s.gpr .ebx).toNat + w32 s.mem W (y + d))) →
      (u.gpr .ebx).toNat = ((s.gpr .ecx).toNat * w32 s.mem W (x + d) + (s.gpr .ebx).toNat +
        w32 s.mem W (y + d)) / 2 ^ 32 →
      Keeps [.eax, .ebx, .edx] s u → WP isa (.block is) u Q) :
    WP isa (.block (macWord d ++ is)) s Q := by
  simp only [macWord, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_ptr hw px (d := d) hx) fun s₁ u₁ _ => ?_
  refine wp_mul fun s₂ m₂ => ?_
  refine wp_addS rfl fun s₃ u₃ c₃ => ?_
  refine wp_adcS rfl c₃ fun s₄ u₄ c₄ => ?_
  have Km : Keeps [.eax, .edx] s₁ s₂ :=
    ⟨fun q hq => m₂.other q (by intro e; exact hq (by simp [e])) (by intro e; exact hq (by simp [e])), m₂.rd, m₂.wr⟩
  have K₄ : Keeps [.eax, .edx] s s₄ :=
    (((u₁.keeps.mono (by decide)).trans Km).trans (u₃.keeps.mono (by decide))).trans (u₄.keeps.mono (by decide))
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, m₂.mem, u₁.mem]
  have py₄ : PtrAt s₄ W .ebp y := by rw [PtrAt, K₄.1 _ (by decide)]; exact py
  refine wp_addS (readSrc_ptr (hw.of_keeps K₄) py₄ (d := d) hy) fun s₅ u₅ c₅ => ?_
  refine wp_adcS rfl c₅ fun s₆ u₆ c₆ => ?_
  have K₆ : Keeps [.eax, .edx] s s₆ := (K₄.trans (u₅.keeps.mono (by decide))).trans (u₆.keeps.mono (by decide))
  have py₆ : PtrAt s₆ W .ebp y := by rw [PtrAt, K₆.1 _ (by decide)]; exact py
  have hw₆ := hw.of_keeps K₆
  refine wp_storeS (by simpa using ea_ptr hw₆ py₆ (d := d) (by omega)) (ws_write hw₆ hy) fun s₇ m₇ => ?_
  refine wp_movS rfl fun s₈ u₈ _ => ?_
  -- The registers along the way.
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, m₄]
  have ecx₂ : s₁.gpr .ecx = s.gpr .ecx := u₁.other _ (by decide)
  have eax₂ := m₂.eax
  have edx₂ := m₂.edx
  rw [u₁.gpr, ecx₂] at eax₂ edx₂
  have ebx₂ : s₂.gpr .ebx = s.gpr .ebx := by rw [m₂.other _ (by decide) (by decide), u₁.other _ (by decide)]
  have eax₃ : s₃.gpr .eax = s₂.gpr .eax + s₂.gpr .ebx := u₃.gpr
  have edx₄ : s₄.gpr .edx = s₃.gpr .edx + 0 + (BitVec.ofBool _).setWidth 32 := u₄.gpr
  have eax₄ : s₄.gpr .eax = s₃.gpr .eax := u₄.other _ (by decide)
  have edx₃ : s₃.gpr .edx = s₂.gpr .edx := u₃.other _ (by decide)
  have eax₅ : s₅.gpr .eax = s₄.gpr .eax + s.mem.readW (off W (y + d)) 32 := by rw [u₅.gpr, m₄]
  have edx₆ : s₆.gpr .edx = s₅.gpr .edx + 0 + (BitVec.ofBool _).setWidth 32 := u₆.gpr
  have eax₆ : s₆.gpr .eax = s₅.gpr .eax := u₆.other _ (by decide)
  have edx₅ : s₅.gpr .edx = s₄.gpr .edx := u₅.other _ (by decide)
  have hpost := step_regs (s.mem.readW (off W (x + d)) 32) (s.gpr .ecx) (s.gpr .ebx)
    (s.mem.readW (off W (y + d)) 32) _ _ rfl rfl
  have ex₆ : s₆.gpr .eax = BitVec.ofNat 32 ((s.mem.readW (off W (x + d)) 32).toNat * (s.gpr .ecx).toNat) +
      s.gpr .ebx + s.mem.readW (off W (y + d)) 32 := by
    rw [eax₆, eax₅, eax₄, eax₃, eax₂, ebx₂]
  have dx₆ := edx₆
  rw [edx₅, edx₄, edx₃, edx₂, eax₄, eax₃, eax₂, ebx₂, m₄] at dx₆
  have hx' : s₆.gpr .eax = BitVec.ofNat 32 ((s.gpr .ecx).toNat * w32 s.mem W (x + d) +
      (s.gpr .ebx).toNat + w32 s.mem W (y + d)) := by
    apply BitVec.eq_of_toNat_eq
    rw [ex₆, hpost.1, BitVec.toNat_ofNat]
  refine k s₈ (by rw [u₈.mem, m₇.mem, m₆, hx']) (by rw [u₈.gpr, m₇.gpr, dx₆, hpost.2]) ?_
  exact ((K₆.trans (m₇.keeps _)).mono (by decide)).trans (u₈.keeps.mono (by decide))

theorem macSet_ok {s : State} {W : Addr} {Z x y d : Nat} (hw : Ws s W Z)
    (px : PtrAt s W .edi x) (py : PtrAt s W .ebp y) (hx : x + d + 4 ≤ Z) (hy : y + d + 4 ≤ Z)
    (k : ∀ u, u.mem = s.mem.writeW (off W (y + d)) (BitVec.ofNat 32
        ((s.gpr .ecx).toNat * w32 s.mem W (x + d) + (s.gpr .ebx).toNat)) →
      (u.gpr .ebx).toNat = ((s.gpr .ecx).toNat * w32 s.mem W (x + d) + (s.gpr .ebx).toNat) / 2 ^ 32 →
      Keeps [.eax, .ebx, .edx] s u → WP isa (.block is) u Q) :
    WP isa (.block (macSet d ++ is)) s Q := by
  simp only [macSet, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_ptr hw px (d := d) hx) fun s₁ u₁ _ => ?_
  refine wp_mul fun s₂ m₂ => ?_
  refine wp_addS rfl fun s₃ u₃ c₃ => ?_
  refine wp_adcS rfl c₃ fun s₄ u₄ c₄ => ?_
  have Km : Keeps [.eax, .edx] s₁ s₂ :=
    ⟨fun q hq => m₂.other q (by intro e; exact hq (by simp [e])) (by intro e; exact hq (by simp [e])), m₂.rd, m₂.wr⟩
  have K₄ : Keeps [.eax, .edx] s s₄ :=
    (((u₁.keeps.mono (by decide)).trans Km).trans (u₃.keeps.mono (by decide))).trans (u₄.keeps.mono (by decide))
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, m₂.mem, u₁.mem]
  have py₄ : PtrAt s₄ W .ebp y := by rw [PtrAt, K₄.1 _ (by decide)]; exact py
  have hw₄ := hw.of_keeps K₄
  refine wp_storeS (by simpa using ea_ptr hw₄ py₄ (d := d) (by omega)) (ws_write hw₄ hy) fun s₇ m₇ => ?_
  refine wp_movS rfl fun s₈ u₈ _ => ?_
  have ecx₂ : s₁.gpr .ecx = s.gpr .ecx := u₁.other _ (by decide)
  have eax₂ := m₂.eax
  have edx₂ := m₂.edx
  rw [u₁.gpr, ecx₂] at eax₂ edx₂
  have ebx₂ : s₂.gpr .ebx = s.gpr .ebx := by rw [m₂.other _ (by decide) (by decide), u₁.other _ (by decide)]
  have eax₃ : s₃.gpr .eax = s₂.gpr .eax + s₂.gpr .ebx := u₃.gpr
  have edx₄ : s₄.gpr .edx = s₃.gpr .edx + 0 + (BitVec.ofBool _).setWidth 32 := u₄.gpr
  have eax₄ : s₄.gpr .eax = s₃.gpr .eax := u₄.other _ (by decide)
  have edx₃ : s₃.gpr .edx = s₂.gpr .edx := u₃.other _ (by decide)
  have h5 : false = decide (2 ^ 32 ≤ (BitVec.ofNat 32 ((s.mem.readW (off W (x + d)) 32).toNat *
      (s.gpr .ecx).toNat) + s.gpr .ebx).toNat + (0 : BitVec 32).toNat) := by
    rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero]
    exact (decide_eq_false (Nat.not_le.mpr (BitVec.isLt _))).symm
  have h0 : ∀ v : BitVec 32, v + 0 = v := BitVec.add_zero
  have hpost := step_regs (s.mem.readW (off W (x + d)) 32) (s.gpr .ecx) (s.gpr .ebx) 0 _ false rfl h5
  rw [h0, show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero] at hpost
  have hx' : s₄.gpr .eax = BitVec.ofNat 32 ((s.gpr .ecx).toNat * w32 s.mem W (x + d) + (s.gpr .ebx).toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [eax₄, eax₃, eax₂, ebx₂, hpost.1, BitVec.toNat_ofNat]
  have dx₄ : (s₄.gpr .edx).toNat = ((s.gpr .ecx).toNat * w32 s.mem W (x + d) + (s.gpr .ebx).toNat) / 2 ^ 32 := by
    rw [edx₄, edx₃, edx₂, ← hpost.2]
    simp only [eax₂, ebx₂, h0, show (BitVec.ofBool false).setWidth 32 = (0 : BitVec 32) from rfl]
  refine k s₈ (by rw [u₈.mem, m₇.mem, m₄, hx']) (by rw [u₈.gpr, m₇.gpr, dx₄]) ?_
  exact ((K₄.trans (m₇.keeps _)).mono (by decide)).trans (u₈.keeps.mono (by decide))

end VG.Proof.Rsa.X86.InvBatchRt
