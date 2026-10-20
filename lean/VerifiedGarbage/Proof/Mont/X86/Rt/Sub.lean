module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Rows
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Framework.Omega

/-! # The subtraction of the modulus, in the run-time width multiplication

`subM`'s loop: `[tmp] = [src] - [mo]`, `N` words, the borrow as a mask in
`ecx`, with `ebp`, `esi` and `ebx` at the three numbers and `edi` counting
`4 N` bytes down (`subLoop_ok`), as `chainSubW_ok` at fixed offsets.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Rt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt VG.Proof.Mont VG.Proof.Mont.X86

theorem restore_eq : Rt.restore = VG.Impl.Mont.X86.Dynamic.restore := rfl

/-- What the subtraction's loop changes. -/
abbrev clob7 : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi]

/-- The body of `subM`'s loop. -/
def subBody : List Instr :=
  [.mov .eax (.mem (at_ .ebp 0))] ++ Rt.restore ++
    [.alu .sbb .eax (.mem (at_ .esi 0)), .store (at_ .ebx 0) .eax, .alu .sbb .ecx (.reg .ecx),
     .alu .add .ebp (.imm 4), .alu .add .esi (.imm 4), .alu .add .ebx (.imm 4), .alu .sub .edi (.imm 4)]

/-- One word: `[tmp + 4j] = [src + 4j] - [mo + 4j] - c`, and the borrow. -/
theorem subStep_ok {t : State} {W : Addr} {L : Nat} (hw : Ws t W L) {src mo tmp j N : Nat} {c : Bool}
    (hebp : PtrAt t W .ebp (src + 4 * j)) (hesi : PtrAt t W .esi (mo + 4 * j)) (hebx : PtrAt t W .ebx (tmp + 4 * j))
    (hedi : (t.gpr .edi).toNat = 4 * (N - j)) (hj : j < N) (hc : t.gpr .ecx = cmask c)
    (hs : src + 4 * j + 4 ≤ L) (hm : mo + 4 * j + 4 ≤ L) (ht : tmp + 4 * j + 4 ≤ L) :
    WP isa (.block subBody) t fun u =>
      u.mem = t.mem.writeW (off W (tmp + 4 * j)) (t.mem.readW (off W (src + 4 * j)) 32 -
        t.mem.readW (off W (mo + 4 * j)) 32 - (BitVec.ofBool c).setWidth 32) ∧
      u.gpr .ecx = cmask (decide (w32 t.mem W (src + 4 * j) < w32 t.mem W (mo + 4 * j) + c.toNat)) ∧
      PtrAt u W .ebp (src + 4 * (j + 1)) ∧ PtrAt u W .esi (mo + 4 * (j + 1)) ∧
      PtrAt u W .ebx (tmp + 4 * (j + 1)) ∧ (u.gpr .edi).toNat = 4 * (N - (j + 1)) ∧
      u.zf = some (decide (j + 1 = N)) ∧ Keeps clob7 t u := by
  have hn := hw.nowrap
  simp only [subBody, List.singleton_append, restore_eq]
  refine wp_movS (readSrc_ptr hw hebp (d := 0) (by omega)) fun s₁ u₁ _ => ?_
  refine wp_restore (by rw [u₁.other _ (by decide), hc]) fun s₂ u₂ c₂ => ?_
  have K₂ : Keeps [.eax, .edx] t s₂ := (u₁.keeps.mono (by decide)).widen u₂.keeps
  have hw₂ := hw.of_keeps K₂
  have esi₂ : PtrAt s₂ W .esi (mo + 4 * j) := by rw [PtrAt, K₂.1 _ (by decide)]; exact hesi
  refine wp_sbbS (readSrc_ptr hw₂ esi₂ (d := 0) (by omega)) c₂ fun s₃ u₃ c₃ => ?_
  have hw₃ := hw₂.of_keeps u₃.keeps
  have ebx₃ : PtrAt s₃ W .ebx (tmp + 4 * j) := by rw [PtrAt, u₃.other _ (by decide), K₂.1 _ (by decide)]; exact hebx
  refine wp_storeS (ea_ptr hw₃ ebx₃ (d := 0) (by omega)) (ws_write hw₃ (y := tmp + 4 * j + 0) (n := 4) (by omega))
    fun s₄ m₄ => wp_sbb_self (by rw [m₄.cf]; exact c₃) fun s₅ u₅ => ?_
  refine wp_addS rfl fun s₆ u₆ _ => ?_
  refine wp_addS rfl fun s₇ u₇ _ => ?_
  refine wp_addS rfl fun s₈ u₈ _ => ?_
  refine wp_subZ rfl fun s₉ u₉ z₉ => WP.block_nil ?_
  have m₂ : s₂.mem = t.mem := by rw [u₂.mem, u₁.mem]
  have eax₂ : s₂.gpr .eax = t.mem.readW (off W (src + 4 * j)) 32 := by
    rw [u₂.other _ (by decide), u₁.gpr, Nat.add_zero]
  have K₅ : Keeps [.eax, .ecx, .edx] t s₅ := ((K₂.mono (by decide)).widen u₃.keeps |>.widen (m₄.keeps [])).widen u₅.keeps
  have r₅ : ∀ r, r = .ebp ∨ r = .esi ∨ r = .ebx ∨ r = .edi → s₅.gpr r = t.gpr r := by
    intro r hr; apply K₅.1; rcases hr with rfl | rfl | rfl | rfl <;> decide
  obtain ⟨c₁, c₂'⟩ := count_zf hedi hj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄.mem, u₃.gpr, eax₂, u₃.mem, m₂, Nat.add_zero, Nat.add_zero]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      eax₂, m₂, Nat.add_zero]
  · rw [PtrAt, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
      r₅ _ (.inl rfl), ptr_add hebp]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega
  · rw [PtrAt, u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
      r₅ _ (.inr (.inl rfl)), ptr_add hesi]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega
  · rw [PtrAt, u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
      r₅ _ (.inr (.inr (.inl rfl))), ptr_add hebx]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      r₅ _ (.inr (.inr (.inr rfl)))]; exact c₁
  · rw [z₉, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      r₅ _ (.inr (.inr (.inr rfl))), c₂']
  · exact ((((K₅.mono (by decide)).widen u₆.keeps).widen u₇.keeps).widen u₈.keeps).widen u₉.keeps

/-- The loop: `[tmp] = [src] - [mo]`, `N` words, and the borrow. -/
theorem subLoop_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L) {src mo tmp N : Nat} (hN : 0 < N)
    (hs : src + 4 * N ≤ L) (hm : mo + 4 * N ≤ L) (ht : tmp + 4 * N ≤ L)
    (hts : tmp + 4 * N ≤ src ∨ src + 4 * N ≤ tmp) (htm : tmp + 4 * N ≤ mo ∨ mo + 4 * N ≤ tmp)
    (hebp : PtrAt t₀ W .ebp src) (hesi : PtrAt t₀ W .esi mo) (hebx : PtrAt t₀ W .ebx tmp)
    (hedi : (t₀.gpr .edi).toNat = 4 * N) (hc : t₀.gpr .ecx = cmask false) :
    WP isa (.loop (.block subBody) .ne) t₀ fun u =>
      Outside W tmp (4 * N) t₀.mem u.mem ∧
      (∃ c : Bool, u.gpr .ecx = cmask c ∧
        val32 u.mem W tmp N + val32 t₀.mem W mo N = val32 t₀.mem W src N + 2 ^ (32 * N) * c.toNat) ∧
      PtrAt u W .ebp (src + 4 * N) ∧ Keeps clob7 t₀ u := by
  have hn := hw.nowrap
  let I : Nat → State → Prop := fun j t =>
    Keeps clob7 t₀ t ∧ PtrAt t W .ebp (src + 4 * j) ∧ PtrAt t W .esi (mo + 4 * j) ∧
    PtrAt t W .ebx (tmp + 4 * j) ∧ (t.gpr .edi).toNat = 4 * (N - j) ∧ Outside W tmp (4 * j) t₀.mem t.mem ∧
    ∃ c : Bool, t.gpr .ecx = cmask c ∧
      val32 t.mem W tmp j + val32 t₀.mem W mo j = val32 t₀.mem W src j + 2 ^ (32 * j) * c.toNat
  have I₀ : I 0 t₀ := ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hesi, by simpa using hebx,
    by simpa using hedi, Outside.refl _ _ _ _, false, hc, by simp [val32]⟩
  refine WP.mono (WP.loop (M := isa) (Q := I N) (fun m t => ∃ j, m = N - j ∧ j < N ∧ I j t) ?_ N t₀
    ⟨0, by omega, hN, I₀⟩) fun u ⟨K, ebp, _, _, _, O, V⟩ => ⟨O, V, ebp, K⟩
  rintro m t ⟨j, rfl, hj, K, ebp, esi, ebx, edi, O, c, ec, V⟩
  have ht' := hw.of_keeps K
  refine WP.mono (subStep_ok ht' ebp esi ebx edi hj ec (by omega_using [hs, hj]) (by omega_using [hm, hj])
    (by omega_using [ht, hj]))
    fun u ⟨mu, eu, pu, su, bu, du, zu, Ku⟩ => ?_
  have ea : w32 t.mem W (src + 4 * j) = w32 t₀.mem W (src + 4 * j) :=
    O.w32 (by omega_using [hts, hj]) (by omega_using [hs, hj, hn])
  have eb : w32 t.mem W (mo + 4 * j) = w32 t₀.mem W (mo + 4 * j) :=
    O.w32 (by omega_using [htm, hj]) (by omega_using [hm, hj, hn])
  have I' : I (j + 1) u := by
    refine ⟨K.trans Ku, pu, su, bu, du, ?_, _, eu, ?_⟩
    · rw [mu]
      exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
        ((writeW32_outside _ _ _ (by omega_using [ht, hj, hn])).mono (by omega_using []) (by omega_using []))
    · rw [mu, val32_store hn (by omega_using [ht, hj]), val32_succ t₀.mem W src, val32_succ t₀.mem W mo, pow32_succ]
      have h := sbb_rel (t.mem.readW (off W (src + 4 * j)) 32) (t.mem.readW (off W (mo + 4 * j)) 32) c
      have ea' : (t.mem.readW (off W (src + 4 * j)) 32).toNat = w32 t₀.mem W (src + 4 * j) := ea
      have eb' : (t.mem.readW (off W (mo + 4 * j)) 32).toNat = w32 t₀.mem W (mo + 4 * j) := eb
      rw [ea', eb'] at h
      rw [ea, eb]
      exact chain_sub_step V h
  by_cases hjN : j + 1 = N
  · exact .inl ⟨by simp only [eval, zu, hjN, decide_true, Option.map_some, Bool.not_true], hjN ▸ I'⟩
  · exact .inr ⟨by simp only [eval, zu, decide_eq_false hjN, Option.map_some, Bool.not_false],
      N - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, hjN], I'⟩

end VG.Proof.Mont.X86.Rt
