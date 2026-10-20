module

public import VerifiedGarbage.Impl.Rsa.X86.KeyRt
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Rt.Step

/-! # The selection of one of two arrays into a third

`select3Loop_ok`: the `N` words at `edi` set to those at `ebx` where the mask
`ecx` is all ones, else to those at `ebp`, a word at a time with one
temporary (`a ^ ((a ^ b) & m)`), counted down in `edx`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt (countLoop ptr4)

theorem select3Loop_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L) {x y d N : Nat} (k : Bool)
    (hN : 0 < N) (hx : x + 4 * N ≤ L) (hy : y + 4 * N ≤ L) (hd : d + 4 * N ≤ L)
    (hdx : d + 4 * N ≤ x ∨ x + 4 * N ≤ d) (hdy : d + 4 * N ≤ y ∨ y + 4 * N ≤ d)
    (hebp : PtrAt t₀ W .ebp x) (hebx : PtrAt t₀ W .ebx y) (hedi : PtrAt t₀ W .edi d)
    (hedx : (t₀.gpr .edx).toNat = 4 * N) (hecx : t₀.gpr .ecx = cmask k) :
    WP isa select3Loop t₀ fun u => Outside W d (4 * N) t₀.mem u.mem ∧
      val32 u.mem W d N = (if k then val32 t₀.mem W y N else val32 t₀.mem W x N) ∧
      Keeps [.eax, .ebx, .edx, .ebp, .edi] t₀ u := by
  have hn := hw.nowrap
  unfold select3Loop
  refine WP.mono (countLoop hN (fun j t => Keeps [.eax, .ebx, .edx, .ebp, .edi] t₀ t ∧
      PtrAt t W .ebp (x + 4 * j) ∧ PtrAt t W .ebx (y + 4 * j) ∧ PtrAt t W .edi (d + 4 * j) ∧
      (t.gpr .edx).toNat = 4 * (N - j) ∧ Outside W d (4 * j) t₀.mem t.mem ∧
      val32 t.mem W d j = (if k then val32 t₀.mem W y j else val32 t₀.mem W x j)) ?_
    ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hebx, by simpa using hedi, by simpa using hedx,
      Outside.refl _ _ _ _, by cases k <;> rfl⟩) fun u ⟨K, _, _, _, _, O, V⟩ => ⟨O, V, K⟩
  rintro j t hj ⟨Kt, ebp, ebx, edi, edx, O, V⟩
  have ht := hw.of_keeps Kt
  have ecx : t.gpr .ecx = cmask k := by rw [Kt.1 _ (by decide)]; exact hecx
  have xw : w32 t.mem W (x + 4 * j) = w32 t₀.mem W (x + 4 * j) :=
    O.w32 (by omega_using [hdx, hj]) (by omega_using [hx, hj, hn])
  have yw : w32 t.mem W (y + 4 * j) = w32 t₀.mem W (y + 4 * j) :=
    O.w32 (by omega_using [hdy, hj]) (by omega_using [hy, hj, hn])
  refine wp_movS (readSrc_ptr ht ebp (d := 0) (by omega_using [hx, hj])) fun s₁ u₁ _ => ?_
  have ht₁ := ht.of_keeps u₁.keeps
  have ebx₁ : PtrAt s₁ W .ebx (y + 4 * j) := by rw [PtrAt, u₁.other _ (by decide)]; exact ebx
  refine wp_logicS (.inr rfl) (readSrc_ptr ht₁ ebx₁ (d := 0) (by omega_using [hy, hj])) fun s₂ u₂ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₃ u₃ => ?_
  have K₃ : Keeps [.eax] t s₃ := (u₁.keeps.trans u₂.keeps).trans u₃.keeps
  have ht₃ := ht.of_keeps K₃
  have ebp₃ : PtrAt s₃ W .ebp (x + 4 * j) := by rw [PtrAt, K₃.1 _ (by decide)]; exact ebp
  refine wp_logicS (.inr rfl) (readSrc_ptr ht₃ ebp₃ (d := 0) (by omega_using [hx, hj])) fun s₄ u₄ => ?_
  have K₄ : Keeps [.eax] t s₄ := K₃.trans u₄.keeps
  have ht₄ := ht.of_keeps K₄
  have edi₄ : PtrAt s₄ W .edi (d + 4 * j) := by rw [PtrAt, K₄.1 _ (by decide)]; exact edi
  refine wp_storeS (ea_ptr ht₄ edi₄ (d := 0) (by omega_using [hd, hj]))
    (ws_write ht₄ (y := d + 4 * j + 0) (n := 4) (by omega_using [hd, hj])) fun s₅ m₅ => ?_
  refine wp_addS rfl fun s₆ u₆ _ => wp_addS rfl fun s₇ u₇ _ => wp_addS rfl fun s₈ u₈ _ =>
    wp_subZ rfl fun s₉ u₉ z₉ => WP.block_nil ?_
  obtain ⟨c₁, c₂⟩ := count_zf edx hj
  have r₅ : ∀ r, r ≠ .eax → s₅.gpr r = t.gpr r := by
    intro r hr; rw [m₅.gpr]; exact K₄.1 _ (by simp [hr])
  have mem₄ : s₄.mem = t.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have eax₄ : s₄.gpr .eax = t.mem.readW (off W (x + 4 * j)) 32 ^^^
      ((t.mem.readW (off W (y + 4 * j)) 32 ^^^ t.mem.readW (off W (x + 4 * j)) 32) &&&
        (if k then BitVec.allOnes 32 else 0)) := by
    rw [u₄.gpr, ite_eq_right (by decide), u₃.gpr, ite_eq_left rfl, u₂.other .ecx (by decide),
      u₁.other .ecx (by decide), ecx, u₂.gpr, ite_eq_right (by decide), u₁.gpr, u₃.mem, u₂.mem, u₁.mem,
      Nat.add_zero, Nat.add_zero]
    change _ = _ ^^^ ((_ ^^^ _) &&& cmask k)
    ac_rfl
  rw [select_val] at eax₄
  refine ⟨⟨Kt.trans ((((K₄.mono (by decide)).widen (m₅.keeps [])).widen u₆.keeps |>.widen u₇.keeps |>.widen
      u₈.keeps).widen u₉.keeps), ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [PtrAt, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, r₅ _ (by decide)]
    exact ptr4 ebp
  · rw [PtrAt, u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), r₅ _ (by decide)]
    exact ptr4 ebx
  · rw [PtrAt, u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), r₅ _ (by decide)]
    exact ptr4 edi
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), r₅ _ (by decide)]
    exact c₁
  · rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅.mem, mem₄, Nat.add_zero]
    exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [hd, hj, hn])).mono (by omega_using []) (by omega_using []))
  · rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅.mem, mem₄, Nat.add_zero, val32_store hn (by omega_using [hd, hj]), V,
      eax₄, val32_succ t₀.mem W x, val32_succ t₀.mem W y]
    have xw' : (t.mem.readW (off W (x + 4 * j)) 32).toNat = w32 t₀.mem W (x + 4 * j) := xw
    have yw' : (t.mem.readW (off W (y + 4 * j)) 32).toNat = w32 t₀.mem W (y + 4 * j) := yw
    cases k
    · simp only [Bool.false_eq_true, ite_false, xw']
    · simp only [ite_true, yw']
  · rw [z₉, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), r₅ _ (by decide), c₂]

end VG.Proof.Rsa.X86.KeyRt
