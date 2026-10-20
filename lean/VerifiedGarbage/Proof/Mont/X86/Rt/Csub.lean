module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Sub
public import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Framework.Omega

/-! # The mask and the selection of the run-time width multiplication

`mask`: all ones when the high half with its top word is at least `M`, from
the subtraction's borrow (`mask_ok`); `select`'s loop: the result at `esi`,
the temporary (at `ebx`) where the mask is all ones, else the high half (at
`ebp`), with `edi` counting down (`selLoop_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Rt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt VG.Proof.Mont VG.Proof.Mont.X86

/-- The mask, from the top word at `ebp` and the borrow `c`. -/
theorem mask_ok {s : State} {W : Addr} {L : Nat} (hw : Ws s W L) {y : Nat} {c : Bool}
    (hebp : PtrAt s W .ebp y) (hy : y + 4 ≤ L) (hc : s.gpr .ecx = cmask c) :
    WP isa (.block Rt.mask) s fun u =>
      u.gpr .ecx = (if !(decide (w32 s.mem W y < c.toNat)) then BitVec.allOnes 32 else 0) ∧
      u.mem = s.mem ∧ Keeps [.eax, .ecx, .edx] s u := by
  have hn := hw.nowrap
  simp only [Rt.mask, List.singleton_append, restore_eq]
  refine wp_movS (readSrc_ptr hw hebp (d := 0) (by omega_using [hy])) fun s₂ u₂ _ => ?_
  refine wp_restore (by rw [u₂.other _ (by decide), hc]) fun s₃ u₃ c₃ => ?_
  refine wp_sbbS rfl c₃ fun s₄ u₄ c₄ => ?_
  refine wp_sbbS rfl c₄ fun s₅ u₅ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₆ u₆ => ?_
  refine wp_movS rfl fun s₇ u₇ _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · have mask := u₆.gpr
    simp only [reduceCtorEq, ite_false] at mask
    rw [u₅.gpr, mask_val] at mask
    rw [u₇.gpr, mask]
    have z : (0 : BitVec 32).toNat = 0 := rfl
    have eax₃ : (s₃.gpr .eax).toNat = w32 s.mem W y := by
      rw [u₃.other _ (by decide), u₂.gpr, Nat.add_zero]
    rw [eax₃, z, Nat.zero_add]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  · exact ((((u₂.keeps.mono (by decide)).widen u₃.keeps |>.widen u₄.keeps).widen u₅.keeps).widen
      u₆.keeps).widen u₇.keeps

/-- The body of `select`'s loop. -/
def selBody : List Instr :=
  [.mov .eax (.mem (at_ .ebp 0)), .mov .edx (.mem (at_ .ebx 0)),
   .alu .xor .edx (.reg .eax), .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx),
   .store (at_ .esi 0) .eax, .alu .add .ebp (.imm 4), .alu .add .ebx (.imm 4), .alu .add .esi (.imm 4),
   .alu .sub .edi (.imm 4)]

/-- One word of the selection. -/
theorem selStep_ok {t : State} {W : Addr} {L : Nat} (hw : Ws t W L) {src tmp o j N : Nat} (k : Bool)
    (hebp : PtrAt t W .ebp (src + 4 * j)) (hebx : PtrAt t W .ebx (tmp + 4 * j)) (hesi : PtrAt t W .esi (o + 4 * j))
    (hedi : (t.gpr .edi).toNat = 4 * (N - j)) (hj : j < N)
    (hm : t.gpr .ecx = if k then BitVec.allOnes 32 else 0)
    (hs : src + 4 * j + 4 ≤ L) (ht : tmp + 4 * j + 4 ≤ L) (ho : o + 4 * j + 4 ≤ L) :
    WP isa (.block selBody) t fun u =>
      u.mem = t.mem.writeW (off W (o + 4 * j))
        (if k then t.mem.readW (off W (tmp + 4 * j)) 32 else t.mem.readW (off W (src + 4 * j)) 32) ∧
      PtrAt u W .ebp (src + 4 * (j + 1)) ∧ PtrAt u W .ebx (tmp + 4 * (j + 1)) ∧
      PtrAt u W .esi (o + 4 * (j + 1)) ∧ (u.gpr .edi).toNat = 4 * (N - (j + 1)) ∧
      u.zf = some (decide (j + 1 = N)) ∧ Keeps [.eax, .ebx, .edx, .ebp, .esi, .edi] t u := by
  have hn := hw.nowrap
  simp only [selBody]
  refine wp_movS (readSrc_ptr hw hebp (d := 0) (by omega_using [hs])) fun s₂ u₂ _ => ?_
  have hw₂ := hw.of_keeps u₂.keeps
  have ebx₂ : PtrAt s₂ W .ebx (tmp + 4 * j) := by rw [PtrAt, u₂.other _ (by decide)]; exact hebx
  refine wp_movS (readSrc_ptr hw₂ ebx₂ (d := 0) (by omega_using [ht])) fun s₃ u₃ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₄ u₄ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₅ u₅ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₆ u₆ => ?_
  have k₆ : Keeps [.eax, .edx] t s₆ := (((u₂.keeps.mono (by decide)).widen u₃.keeps).widen u₄.keeps |>.widen
    u₅.keeps).widen u₆.keeps
  have hw₆ := hw.of_keeps k₆
  have esi₆ : PtrAt s₆ W .esi (o + 4 * j) := by rw [PtrAt, k₆.1 _ (by decide)]; exact hesi
  refine wp_storeS (ea_ptr hw₆ esi₆ (d := 0) (by omega_using [ho]))
    (ws_write hw₆ (y := o + 4 * j + 0) (n := 4) (by omega_using [ho])) fun s₇ m₇ => ?_
  refine wp_addS rfl fun s₈ u₈ _ => ?_
  refine wp_addS rfl fun s₉ u₉ _ => ?_
  refine wp_addS rfl fun s₁₀ u₁₀ _ => ?_
  refine wp_subZ rfl fun s₁₁ u₁₁ z₁₁ => WP.block_nil ?_
  have r₇ : ∀ r, r = .ebp ∨ r = .esi ∨ r = .ebx ∨ r = .edi → s₇.gpr r = t.gpr r := by
    intro r hr; rw [m₇.gpr]; apply k₆.1; rcases hr with rfl | rfl | rfl | rfl <;> decide
  obtain ⟨c₁, c₂⟩ := count_zf hedi hj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have mem₆ : s₆.mem = t.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    have ecx₄ : s₄.gpr .ecx = t.gpr .ecx := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide)]
    have eax₆ : s₆.gpr .eax = t.mem.readW (off W (src + 4 * j)) 32 ^^^
        ((t.mem.readW (off W (tmp + 4 * j)) 32 ^^^ t.mem.readW (off W (src + 4 * j)) 32) &&&
          (if k then BitVec.allOnes 32 else 0)) := by
      rw [u₆.gpr, u₅.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₄.gpr, ecx₄, hm,
        u₃.other _ (by decide), u₃.gpr, u₂.gpr, u₂.mem, Nat.add_zero, Nat.add_zero]
      rfl
    rw [select_val] at eax₆
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, m₇.mem, mem₆, eax₆, Nat.add_zero]
  · rw [PtrAt, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr,
      r₇ _ (.inl rfl), ptr_add hebp]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega_using []
  · rw [PtrAt, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide),
      r₇ _ (.inr (.inr (.inl rfl))), ptr_add hebx]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega_using []
  · rw [PtrAt, u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide),
      r₇ _ (.inr (.inl rfl)), ptr_add hesi]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega_using []
  · rw [u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      r₇ _ (.inr (.inr (.inr rfl)))]; exact c₁
  · rw [z₁₁, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      r₇ _ (.inr (.inr (.inr rfl))), c₂]
  · exact (((((k₆.mono (by decide)).widen (m₇.keeps [])).widen u₈.keeps).widen u₉.keeps).widen u₁₀.keeps).widen
      u₁₁.keeps

/-- The selection: `[o] = [tmp]` if `k`, else `[src]`, `N` words. -/
theorem selLoop_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L) {src tmp o N : Nat} (k : Bool) (hN : 0 < N)
    (hs : src + 4 * N ≤ L) (ht : tmp + 4 * N ≤ L) (ho : o + 4 * N ≤ L)
    (hos : o + 4 * N ≤ src ∨ src + 4 * N ≤ o) (hot : o + 4 * N ≤ tmp ∨ tmp + 4 * N ≤ o)
    (hebp : PtrAt t₀ W .ebp src) (hebx : PtrAt t₀ W .ebx tmp) (hesi : PtrAt t₀ W .esi o)
    (hedi : (t₀.gpr .edi).toNat = 4 * N) (hm : t₀.gpr .ecx = if k then BitVec.allOnes 32 else 0) :
    WP isa (.loop (.block selBody) .ne) t₀ fun u =>
      Outside W o (4 * N) t₀.mem u.mem ∧
      val32 u.mem W o N = val32 t₀.mem W (if k then tmp else src) N ∧
      Keeps [.eax, .ebx, .edx, .ebp, .esi, .edi] t₀ u := by
  have hn := hw.nowrap
  let I : Nat → State → Prop := fun j t =>
    Keeps [.eax, .ebx, .edx, .ebp, .esi, .edi] t₀ t ∧ PtrAt t W .ebp (src + 4 * j) ∧
    PtrAt t W .ebx (tmp + 4 * j) ∧ PtrAt t W .esi (o + 4 * j) ∧ (t.gpr .edi).toNat = 4 * (N - j) ∧
    Outside W o (4 * j) t₀.mem t.mem ∧ val32 t.mem W o j = val32 t₀.mem W (if k then tmp else src) j
  have I₀ : I 0 t₀ := ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hebx, by simpa using hesi,
    by simpa using hedi, Outside.refl _ _ _ _, rfl⟩
  refine WP.mono (WP.loop (M := isa) (Q := I N) (fun m t => ∃ j, m = N - j ∧ j < N ∧ I j t) ?_ N t₀
    ⟨0, by omega_using [hN], hN, I₀⟩) fun u ⟨K, _, _, _, _, O, V⟩ => ⟨O, V, K⟩
  rintro m t ⟨j, rfl, hj, K, ebp, ebx, esi, edi, O, V⟩
  have ht' := hw.of_keeps K
  have hm' : t.gpr .ecx = if k then BitVec.allOnes 32 else 0 := by rw [K.1 _ (by decide)]; exact hm
  refine WP.mono (selStep_ok ht' k ebp ebx esi edi hj hm' (by omega_using [hs, hj]) (by omega_using [ht, hj])
    (by omega_using [ho, hj])) fun u ⟨mu, pu, bu, su, du, zu, Ku⟩ => ?_
  have I' : I (j + 1) u := by
    refine ⟨K.trans Ku, pu, bu, su, du, ?_, ?_⟩
    · rw [mu]
      exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
        ((writeW32_outside _ _ _ (by omega_using [ho, hj, hn])).mono (by omega_using []) (by omega_using []))
    · rw [mu, val32_store hn (by omega_using [ho, hj]), V, val32_succ]
      congr 1
      cases k
      · exact congrArg (2 ^ (32 * j) * ·) (O.w32 (d := src + 4 * j) (by omega_using [hos, hj])
          (by omega_using [hs, hj, hn]))
      · exact congrArg (2 ^ (32 * j) * ·) (O.w32 (d := tmp + 4 * j) (by omega_using [hot, hj])
          (by omega_using [ht, hj, hn]))
  by_cases hjN : j + 1 = N
  · exact .inl ⟨by simp only [eval, zu, hjN, decide_true, Option.map_some, Bool.not_true], hjN ▸ I'⟩
  · exact .inr ⟨by simp only [eval, zu, decide_eq_false hjN, Option.map_some, Bool.not_false],
      N - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, hjN], I'⟩

end VG.Proof.Mont.X86.Rt
