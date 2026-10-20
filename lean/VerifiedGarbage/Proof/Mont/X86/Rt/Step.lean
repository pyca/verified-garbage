module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.Framework.Omega

/-! # One step of a row of the run-time width multiplication

`mulStep`: `[ebp] += [edi + multOff] · [ecx]` with the carry in `ebx`, both
pointers up a word and the count `esi` down by 4, ZF when it reaches zero.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Rt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt VG.Proof.Mont VG.Proof.Mont.X86

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `sub d, src`, and ZF. -/
theorem wp_subZ {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d (s.gpr d - v) → t.zf = some (s.gpr d - v == 0) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .sub d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl)

end

/-- The count down by 4: ZF when it reaches zero. -/
theorem count_zf {x : BitVec 32} {N j : Nat} (hx : x.toNat = 4 * (N - j)) (hj : j < N) :
    (x - 4).toNat = 4 * (N - (j + 1)) ∧ (x - 4 == 0) = decide (j + 1 = N) := by
  have h4 : (x - 4).toNat = 4 * (N - (j + 1)) := by
    rw [BitVec.toNat_sub, hx]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]
    omega
  refine ⟨h4, ?_⟩
  by_cases h : j + 1 = N
  · simp only [h, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [h4]; simp; omega
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro hz
    have := congrArg BitVec.toNat hz
    rw [h4] at this
    simp at this
    omega

/-- One step of a row, the multiplier at `[edi + mo]`. -/
theorem mulStepAt_ok {mo : Nat} {t : State} {W : Addr} {L : Nat} (hw : Ws t W L) {S bx w j N : Nat}
    (hedi : PtrAt t W .edi S) (hecx : PtrAt t W .ecx (bx + 4 * j)) (hebp : PtrAt t W .ebp (w + 4 * j))
    (hesi : (t.gpr .esi).toNat = 4 * (N - j)) (hj : j < N)
    (hm : S + mo + 4 ≤ L) (hb : bx + 4 * j + 4 ≤ L) (ht : w + 4 * j + 4 ≤ L) :
    WP isa (.block (Rt.mulStepAt mo)) t fun u =>
      u.mem = t.mem.writeW (off W (w + 4 * j)) (BitVec.ofNat 32
        (w32 t.mem W (S + mo) * w32 t.mem W (bx + 4 * j) + (t.gpr .ebx).toNat + w32 t.mem W (w + 4 * j))) ∧
      (u.gpr .ebx).toNat = (w32 t.mem W (S + mo) * w32 t.mem W (bx + 4 * j) + (t.gpr .ebx).toNat +
          w32 t.mem W (w + 4 * j)) / 2 ^ 32 ∧
      PtrAt u W .ecx (bx + 4 * (j + 1)) ∧ PtrAt u W .ebp (w + 4 * (j + 1)) ∧
      (u.gpr .esi).toNat = 4 * (N - (j + 1)) ∧
      u.zf = some (decide (j + 1 = N)) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] t u := by
  have hn := hw.nowrap
  simp only [Rt.mulStepAt]
  refine wp_movS (readSrc_ptr hw hedi (d := mo) (by omega)) fun s₀ u₀ _ => ?_
  have hw₀ := hw.of_keeps u₀.keeps
  have hecx₀ : PtrAt s₀ W .ecx (bx + 4 * j) := by rw [PtrAt, u₀.other _ (by decide)]; exact hecx
  refine wp_movS (readSrc_ptr hw₀ hecx₀ (d := 0) (by omega)) fun s₁ u₁ _ => ?_
  refine wp_mul fun s₂ m₂ => ?_
  have K₂ : Keeps [.eax, .edx] t s₂ := ((u₀.keeps.mono (by decide)).widen u₁.keeps).widen m₂.keeps
  have hw₂ := hw.of_keeps K₂
  have hp₂ : PtrAt s₂ W .ebp (w + 4 * j) := by rw [PtrAt, K₂.1 _ (by decide)]; exact hebp
  refine wp_addS (readSrc_ptr hw₂ hp₂ (d := 0) (by omega)) fun s₃ u₃ c₃ => ?_
  refine wp_adcS rfl c₃ fun s₄ u₄ c₄ => ?_
  refine wp_addS rfl fun s₅ u₅ c₅ => ?_
  refine wp_adcS rfl c₅ fun s₆ u₆ c₆ => ?_
  have K₄ : Keeps [.eax, .edx] t s₄ := (K₂.widen u₃.keeps).widen u₄.keeps
  have K₆ : Keeps [.eax, .edx] t s₆ := (K₄.widen u₅.keeps).widen u₆.keeps
  have hw₆ := hw.of_keeps K₆
  have hp₆ : PtrAt s₆ W .ebp (w + 4 * j) := by rw [PtrAt, K₆.1 _ (by decide)]; exact hebp
  refine wp_storeS (ea_ptr hw₆ hp₆ (d := 0) (by omega)) (ws_write hw₆ (y := w + 4 * j + 0) (n := 4) (by omega))
    fun s₇ m₇ => ?_
  refine wp_movS rfl fun s₈ u₈ _ => ?_
  refine wp_addS rfl fun s₉ u₉ _ => ?_
  refine wp_addS rfl fun s₁₀ u₁₀ _ => ?_
  refine wp_subZ rfl fun s₁₁ u₁₁ z₁₁ => WP.block_nil ?_
  -- The registers and memory along the way.
  have m₂' : s₂.mem = t.mem := by rw [m₂.mem, u₁.mem, u₀.mem]
  have m₄ : s₄.mem = t.mem := by rw [u₄.mem, u₃.mem, m₂']
  have m₆ : s₆.mem = t.mem := by rw [u₆.mem, u₅.mem, m₄]
  have eax₁ : s₁.gpr .eax = t.mem.readW (off W (S + mo)) 32 := by rw [u₁.other _ (by decide), u₀.gpr]
  have eax₂ := m₂.eax
  have edx₂ := m₂.edx
  rw [eax₁, u₁.gpr, u₀.mem, Nat.add_zero] at eax₂ edx₂
  have ebx₂ : s₂.gpr .ebx = t.gpr .ebx := by
    rw [m₂.other _ (by decide) (by decide), u₁.other _ (by decide), u₀.other _ (by decide)]
  have eax₃ : s₃.gpr .eax = s₂.gpr .eax + t.mem.readW (off W (w + 4 * j)) 32 := by
    rw [u₃.gpr, m₂', Nat.add_zero]
  have edx₄ : s₄.gpr .edx = s₃.gpr .edx + 0 + (BitVec.ofBool _).setWidth 32 := u₄.gpr
  have eax₄ : s₄.gpr .eax = s₃.gpr .eax := u₄.other _ (by decide)
  have edx₃ : s₃.gpr .edx = s₂.gpr .edx := u₃.other _ (by decide)
  have ebx₄ : s₄.gpr .ebx = t.gpr .ebx := by rw [u₄.other _ (by decide), u₃.other _ (by decide), ebx₂]
  have eax₅ : s₅.gpr .eax = s₄.gpr .eax + s₄.gpr .ebx := u₅.gpr
  have edx₆ : s₆.gpr .edx = s₅.gpr .edx + 0 + (BitVec.ofBool _).setWidth 32 := u₆.gpr
  have eax₆ : s₆.gpr .eax = s₅.gpr .eax := u₆.other _ (by decide)
  have edx₅ : s₅.gpr .edx = s₄.gpr .edx := u₅.other _ (by decide)
  have hpost := step_regs (t.mem.readW (off W (bx + 4 * j)) 32) (t.mem.readW (off W (S + mo)) 32)
    (t.mem.readW (off W (w + 4 * j)) 32) (t.gpr .ebx) _ _ rfl rfl
  rw [Nat.mul_comm (t.mem.readW (off W (bx + 4 * j)) 32).toNat] at hpost
  have ex₆ : s₆.gpr .eax = BitVec.ofNat 32 ((t.mem.readW (off W (S + mo)) 32).toNat *
      (t.mem.readW (off W (bx + 4 * j)) 32).toNat) + t.mem.readW (off W (w + 4 * j)) 32 + t.gpr .ebx := by
    rw [eax₆, eax₅, ebx₄, eax₄, eax₃, eax₂]
  have dx₆ := edx₆
  rw [edx₅, edx₄, edx₃, edx₂, ebx₄, eax₄, eax₃, eax₂, m₂'] at dx₆
  simp only [Nat.add_zero] at dx₆
  have hx : s₆.gpr .eax = BitVec.ofNat 32 (w32 t.mem W (S + mo) * w32 t.mem W (bx + 4 * j) +
      (t.gpr .ebx).toNat + w32 t.mem W (w + 4 * j)) := by
    apply BitVec.eq_of_toNat_eq
    rw [ex₆, hpost.1, BitVec.toNat_ofNat, Nat.add_right_comm]
  have K₇ : Keeps [.eax, .ebx, .edx] t s₇ := (K₆.mono (by decide)).widen (m₇.keeps [])
  have K₁₁ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] t s₁₁ :=
    ((((K₇.mono (by decide)).widen u₈.keeps).widen u₉.keeps).widen u₁₀.keeps).widen u₁₁.keeps
  have ecx₁₀ : s₁₀.gpr .ecx = t.gpr .ecx + 4 := by
    rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), m₇.gpr, K₆.1 _ (by decide)]
  have ebp₁₀ : s₁₀.gpr .ebp = t.gpr .ebp + 4 := by
    rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), m₇.gpr, K₆.1 _ (by decide)]
  have esi₁₀ : s₁₀.gpr .esi = t.gpr .esi := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), m₇.gpr, K₆.1 _ (by decide)]
  obtain ⟨c₁, c₂⟩ := count_zf hesi hj
  refine ⟨by rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, m₇.mem, m₆, hx, Nat.add_zero],
    ?_, ?_, ?_, by rw [u₁₁.gpr, esi₁₀]; exact c₁, by rw [z₁₁, esi₁₀, c₂], K₁₁⟩
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.gpr, m₇.gpr, dx₆, hpost.2, Nat.add_right_comm]
  · rw [PtrAt, u₁₁.other _ (by decide), ecx₁₀, ptr_add hecx 4]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega
  · rw [PtrAt, u₁₁.other _ (by decide), ebp₁₀, ptr_add hebp 4]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega


/-- One step of a row. -/
theorem mulStep_ok {t : State} {W : Addr} {L : Nat} (hw : Ws t W L) {S bx w j N : Nat}
    (hedi : PtrAt t W .edi S) (hecx : PtrAt t W .ecx (bx + 4 * j)) (hebp : PtrAt t W .ebp (w + 4 * j))
    (hesi : (t.gpr .esi).toNat = 4 * (N - j)) (hj : j < N)
    (hm : S + multOff + 4 ≤ L) (hb : bx + 4 * j + 4 ≤ L) (ht : w + 4 * j + 4 ≤ L) :
    WP isa (.block Rt.mulStep) t fun u =>
      u.mem = t.mem.writeW (off W (w + 4 * j)) (BitVec.ofNat 32
        (w32 t.mem W (S + multOff) * w32 t.mem W (bx + 4 * j) + (t.gpr .ebx).toNat + w32 t.mem W (w + 4 * j))) ∧
      (u.gpr .ebx).toNat = (w32 t.mem W (S + multOff) * w32 t.mem W (bx + 4 * j) + (t.gpr .ebx).toNat +
          w32 t.mem W (w + 4 * j)) / 2 ^ 32 ∧
      PtrAt u W .ecx (bx + 4 * (j + 1)) ∧ PtrAt u W .ebp (w + 4 * (j + 1)) ∧
      (u.gpr .esi).toNat = 4 * (N - (j + 1)) ∧
      u.zf = some (decide (j + 1 = N)) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] t u :=
  mulStepAt_ok hw hedi hecx hebp hesi hj hm hb ht

end VG.Proof.Mont.X86.Rt
