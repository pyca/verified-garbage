module

public import VerifiedGarbage.Impl.Mont.X86.Dynamic
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Mont.X86.Loop
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# A multiply-accumulate row as a loop (x86, 32-bit)

`mulRowW acc b N` adds `ecx · [b]` to the window at `[ebp + acc]`, as
`mulRow` does (`mulRow_ok`), in a loop whose step (`mulStepW_ok`) reads
`[esi + b]` and writes `[ebp + acc]` and moves both pointers up a word;
`ebp` is moved back before the carry word is added (`carryUp_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Mont VG.Proof.Mont

/-- `[r + d]`, with `r` at `4i` bytes into the working space. -/
theorem Scr.ea_regAt {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {r : Reg} {i d : Nat}
    (hp : s.gpr r = s.gpr .edi + BitVec.ofNat 32 (4 * i)) (hd : 4 * i + d < size) :
    s.ea (at_ r d) = off base (4 * i + d) := by
  change ((s.gpr r + BitVec.ofNat 32 d).setWidth 64) = _
  rw [hp, Offset.add_add]
  exact hs.ea hd

theorem readSrc_regAt {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {r : Reg} {i d : Nat}
    (hp : s.gpr r = s.gpr .edi + BitVec.ofNat 32 (4 * i)) (hd : 4 * i + d + 4 ≤ size) :
    readSrc s (.mem (at_ r d)) = some (s.mem.readW (off base (4 * i + d)) 32) := by
  show s.load32 (s.ea (at_ r d)) = _
  rw [hs.ea_regAt hp (by omega), State.load32, ite_eq_left_iff.mpr fun h => absurd (hs.read hd) h]

/-- One step of the row's loop. -/
theorem mulStepW_ok {t : State} {base : Addr} {size : Nat} (hs : Scr t base size) {acc b i j N w mult : Nat}
    (hecx : t.gpr .ecx = t.gpr .edi + BitVec.ofNat 32 (4 * j))
    (hp : t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * (i + j))) (hw : 4 * i + acc = w)
    (hj : j < N) (hN32 : 4 * N < 2 ^ 32) (hb : b + 4 * j + 4 ≤ size) (ht : w + 4 * j + 4 ≤ size)
    (hm : mult + 4 ≤ size) :
    WP isa (.block (mulStepW N acc b mult)) t fun u =>
      u.mem = t.mem.writeW (off base (w + 4 * j)) (BitVec.ofNat 32
        (w32 t.mem base mult * w32 t.mem base (b + 4 * j) + (t.gpr .ebx).toNat + w32 t.mem base (w + 4 * j))) ∧
      (u.gpr .ebx).toNat = (w32 t.mem base mult * w32 t.mem base (b + 4 * j) + (t.gpr .ebx).toNat +
          w32 t.mem base (w + 4 * j)) / 2 ^ 32 ∧
      u.gpr .ecx = u.gpr .edi + BitVec.ofNat 32 (4 * (j + 1)) ∧
      u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * (i + (j + 1))) ∧
      u.zf = some (decide (j + 1 = N)) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] t u := by
  have hn := hs.nowrap
  have eb : 4 * j + b = b + 4 * j := by omega
  have ew : 4 * (i + j) + acc = w + 4 * j := by omega
  simp only [mulStepW]
  refine wp_movS (readSrc_sc hs hm) fun s₀ u₀ _ => ?_
  have hs₀ := hs.of_keeps u₀.keeps (by decide)
  have hecx₀ : s₀.gpr .ecx = s₀.gpr .edi + BitVec.ofNat 32 (4 * j) := by
    rw [u₀.other _ (by decide), u₀.other _ (by decide)]; exact hecx
  refine wp_movS (readSrc_regAt hs₀ hecx₀ (d := b) (by omega)) fun s₁ u₁ _ => ?_
  refine wp_mul fun s₂ m₂ => ?_
  have K₂ : Keeps [.eax, .edx] t s₂ := ((u₀.keeps.mono (by decide)).widen u₁.keeps).widen m₂.keeps
  have hs₂ := hs.of_keeps K₂ (by decide)
  have hp₂ : s₂.gpr .ebp = s₂.gpr .edi + BitVec.ofNat 32 (4 * (i + j)) := by
    rw [K₂.1 _ (by decide), K₂.1 _ (by decide)]; exact hp
  refine wp_addS (readSrc_regAt hs₂ hp₂ (d := acc) (by omega)) fun s₃ u₃ c₃ => ?_
  refine wp_adcS rfl c₃ fun s₄ u₄ c₄ => ?_
  refine wp_addS rfl fun s₅ u₅ c₅ => ?_
  refine wp_adcS rfl c₅ fun s₆ u₆ c₆ => ?_
  have K₄ : Keeps [.eax, .edx] t s₄ := (K₂.widen u₃.keeps).widen u₄.keeps
  have K₆ : Keeps [.eax, .edx] t s₆ := (K₄.widen u₅.keeps).widen u₆.keeps
  have hs₆ := hs.of_keeps K₆ (by decide)
  have hp₆ : s₆.gpr .ebp = s₆.gpr .edi + BitVec.ofNat 32 (4 * (i + j)) := by
    rw [K₆.1 _ (by decide), K₆.1 _ (by decide)]; exact hp
  refine wp_storeS (hs₆.ea_regAt hp₆ (d := acc) (by omega)) (hs₆.write (d := 4 * (i + j) + acc) (n := 4) (by omega))
    fun s₇ m₇ => ?_
  refine wp_movS rfl fun s₈ u₈ _ => ?_
  refine wp_addS rfl fun s₉ u₉ _ => ?_
  refine wp_addS rfl fun s₁₀ u₁₀ _ => ?_
  refine wp_movS rfl fun s₁₁ u₁₁ _ => ?_
  refine wp_addS rfl fun s₁₂ u₁₂ _ => ?_
  refine wp_cmpS rfl fun s₁₃ f₁₃ z₁₃ => WP.block_nil ?_
  -- The registers and memory along the way.
  have m₂' : s₂.mem = t.mem := by rw [m₂.mem, u₁.mem, u₀.mem]
  have m₄ : s₄.mem = t.mem := by rw [u₄.mem, u₃.mem, m₂']
  have m₆ : s₆.mem = t.mem := by rw [u₆.mem, u₅.mem, m₄]
  have eax₁ : s₁.gpr .eax = t.mem.readW (off base mult) 32 := by rw [u₁.other _ (by decide), u₀.gpr]
  have eax₂ := m₂.eax
  have edx₂ := m₂.edx
  rw [eax₁, u₁.gpr, u₀.mem, eb] at eax₂ edx₂
  have ebx₂ : s₂.gpr .ebx = t.gpr .ebx := by
    rw [m₂.other _ (by decide) (by decide), u₁.other _ (by decide), u₀.other _ (by decide)]
  have eax₃ : s₃.gpr .eax = s₂.gpr .eax + t.mem.readW (off base (w + 4 * j)) 32 := by
    rw [u₃.gpr, m₂', ew]
  have edx₄ : s₄.gpr .edx = s₃.gpr .edx + 0 + (BitVec.ofBool _).setWidth 32 := u₄.gpr
  have eax₄ : s₄.gpr .eax = s₃.gpr .eax := u₄.other _ (by decide)
  have edx₃ : s₃.gpr .edx = s₂.gpr .edx := u₃.other _ (by decide)
  have ebx₄ : s₄.gpr .ebx = t.gpr .ebx := by rw [u₄.other _ (by decide), u₃.other _ (by decide), ebx₂]
  have eax₅ : s₅.gpr .eax = s₄.gpr .eax + s₄.gpr .ebx := u₅.gpr
  have edx₆ : s₆.gpr .edx = s₅.gpr .edx + 0 + (BitVec.ofBool _).setWidth 32 := u₆.gpr
  have eax₆ : s₆.gpr .eax = s₅.gpr .eax := u₆.other _ (by decide)
  have edx₅ : s₅.gpr .edx = s₄.gpr .edx := u₅.other _ (by decide)
  have hpost := step_regs (t.mem.readW (off base (b + 4 * j)) 32) (t.mem.readW (off base mult) 32)
    (t.mem.readW (off base (w + 4 * j)) 32) (t.gpr .ebx) _ _ rfl rfl
  rw [Nat.mul_comm (t.mem.readW (off base (b + 4 * j)) 32).toNat] at hpost
  have ex₆ : s₆.gpr .eax = BitVec.ofNat 32 ((t.mem.readW (off base mult) 32).toNat *
      (t.mem.readW (off base (b + 4 * j)) 32).toNat) + t.mem.readW (off base (w + 4 * j)) 32 + t.gpr .ebx := by
    rw [eax₆, eax₅, ebx₄, eax₄, eax₃, eax₂]
  have dx₆ := edx₆
  rw [edx₅, edx₄, edx₃, edx₂, ebx₄, eax₄, eax₃, eax₂, m₂', ew] at dx₆
  have hx : s₆.gpr .eax = BitVec.ofNat 32 (w32 t.mem base mult * w32 t.mem base (b + 4 * j) +
      (t.gpr .ebx).toNat + w32 t.mem base (w + 4 * j)) := by
    apply BitVec.eq_of_toNat_eq
    rw [ex₆, hpost.1, BitVec.toNat_ofNat, Nat.add_right_comm]
  have K₇ : Keeps [.eax, .ebx, .edx] t s₇ := (K₆.mono (by decide)).widen (m₇.keeps [])
  have K₁₃ : Keeps [.eax, .ebx, .ecx, .edx, .ebp] t s₁₃ :=
    (((((K₇.mono (by decide)).widen u₈.keeps).widen u₉.keeps).widen u₁₀.keeps).widen u₁₁.keeps |>.widen
      u₁₂.keeps).widen (f₁₃.keeps [])
  have edi₁₃ : s₁₃.gpr .edi = t.gpr .edi := K₁₃.1 _ (by decide)
  have ecx₁₂ : s₁₂.gpr .ecx = t.gpr .edi + BitVec.ofNat 32 (4 * j) + 4 := by
    rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide),
      m₇.gpr, K₆.1 _ (by decide), hecx]
  have ebp₁₂ : s₁₂.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * (i + j)) + 4 := by
    rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide),
      m₇.gpr, hp₆, K₆.1 _ (by decide)]
  have eax₁₂ : s₁₂.gpr .eax = t.gpr .edi + BitVec.ofNat 32 (4 * N) := by
    rw [u₁₂.gpr, u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), m₇.gpr,
      K₆.1 _ (by decide)]
  refine ⟨by rw [f₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, m₇.mem, m₆, hx, ew],
    ?_, by rw [edi₁₃, f₁₃.gpr, ecx₁₂, row_ebp], by rw [edi₁₃, f₁₃.gpr, ebp₁₂, row_ebp, Nat.add_assoc],
    by rw [z₁₃, ecx₁₂, eax₁₂, row_zf _ hj hN32], K₁₃⟩
  rw [f₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
    u₈.gpr, m₇.gpr, dx₆, hpost.2, Nat.add_right_comm]

/-- The window `+= [mult] · [b]` (`N` words), when the sum fits its `N + 2`
words; `ecx` is used and `ebp` restored. -/
theorem mulRowW_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc b i w N : Nat}
    (hN : 0 < N) (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)) (hw : 4 * i + acc = w)
    (hb : b + 4 * N ≤ size) (hwN : w + 4 * N + 8 ≤ size) (hsep : b + 4 * N ≤ w ∨ w + 4 * N + 8 ≤ b)
    {mult : Nat} (hm : mult + 4 ≤ size) (hsm : mult + 4 ≤ w ∨ w + 4 * N + 8 ≤ mult)
    (hlt : val32 s.mem base w (N + 2) + w32 s.mem base mult * val32 s.mem base b N < 2 ^ (32 * (N + 2))) :
    WP isa (mulRowW acc b N mult) s fun u =>
      Outside base w (4 * N + 8) s.mem u.mem ∧
      val32 u.mem base w (N + 2) = val32 s.mem base w (N + 2) + w32 s.mem base mult * val32 s.mem base b N ∧
      Keeps [.eax, .ebx, .ecx, .edx] s u := by
  have hn := hs.nowrap
  have hN32 : 4 * N < 2 ^ 32 := by have := hs.size_lt; omega
  unfold mulRowW
  refine WP.seq (wp_movS rfl fun s₀ u₀ _ => wp_movS rfl fun s₁ u₁ _ => WP.block_nil ?_)
  have k₁ : Keeps [.ebx, .ecx] s s₁ := (u₀.keeps.mono (by decide)).widen u₁.keeps
  -- The loop: `j` steps done.
  let I : Nat → State → Prop := fun j t =>
    Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
    t.gpr .ecx = t.gpr .edi + BitVec.ofNat 32 (4 * j) ∧
    t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * (i + j)) ∧
    Outside base w (4 * j) s.mem t.mem ∧
    val32 t.mem base w j + 2 ^ (32 * j) * (t.gpr .ebx).toNat =
      val32 s.mem base w j + w32 s.mem base mult * val32 s.mem base b j
  have I₀ : I 0 s₁ := by
    refine ⟨k₁.mono (by decide), ?_, ?_,
      by rw [u₁.mem, u₀.mem]; exact VG.Proof.Mont.Outside.refl _ _ _ _, ?_⟩
    · rw [u₁.gpr, u₁.other _ (by decide)]; exact (BitVec.add_zero _).symm
    · rw [k₁.1 _ (by decide), k₁.1 _ (by decide), hp, Nat.add_zero]
    · rw [u₁.other _ (by decide), u₀.gpr]; simp [val32]
  refine WP.seq (WP.mono (WP.loop (M := isa) (Q := I N) (fun m t => ∃ j, m = N - j ∧ j < N ∧ I j t) ?_ N s₁
    ⟨0, by omega, hN, I₀⟩) ?_)
  · rintro m t ⟨j, rfl, hj, K, ecx, ebp, O, V⟩
    have ht := hs.of_keeps K (by decide)
    refine WP.mono (mulStepW_ok ht ecx ebp hw hj hN32 (by omega) (by omega) hm)
      fun u ⟨mu, bu, su, pu, zu, Ku⟩ => ?_
    have mk : w32 t.mem base mult = w32 s.mem base mult := O.w32 (by omega) (by omega)
    have bk : w32 t.mem base (b + 4 * j) = w32 s.mem base (b + 4 * j) := O.w32 (by omega) (by omega)
    have tk : w32 t.mem base (w + 4 * j) = w32 s.mem base (w + 4 * j) := O.w32 (by omega) (by omega)
    rw [mk, bk, tk] at mu bu
    have W := writeW32_outside t.mem base (d := w + 4 * j)
      (BitVec.ofNat 32 (w32 s.mem base mult * w32 s.mem base (b + 4 * j) + (t.gpr .ebx).toNat +
        w32 s.mem base (w + 4 * j))) (by omega)
    rw [← mu] at W
    have I' : I (j + 1) u := by
      refine ⟨K.trans Ku, su, pu,
        (O.mono (Nat.le_refl _) (by omega)).trans (W.mono (by omega) (by omega)), ?_⟩
      have hlow : val32 u.mem base w j = val32 t.mem base w j := W.val32 (by omega) (by omega)
      have htop : w32 u.mem base (w + 4 * j) = (w32 s.mem base mult * w32 s.mem base (b + 4 * j) +
          (t.gpr .ebx).toNat + w32 s.mem base (w + 4 * j)) % 2 ^ 32 := by
        rw [mu, w32_write_self, BitVec.toNat_ofNat]
      rw [val32_succ, val32_succ, val32_succ, hlow, htop, bu, pow32_succ]
      generalize hxd : w32 s.mem base mult * w32 s.mem base (b + 4 * j) + (t.gpr .ebx).toNat +
        w32 s.mem base (w + 4 * j) = x at *
      have hx := Nat.div_add_mod x (2 ^ 32)
      generalize 2 ^ (32 * j) = P at *
      grind
    by_cases hjN : j + 1 = N
    · exact .inl ⟨by simp only [eval, zu, hjN, decide_true, Option.map_some, Bool.not_true], hjN ▸ I'⟩
    · exact .inr ⟨by simp only [eval, zu, decide_eq_false hjN, Option.map_some, Bool.not_false],
        N - (j + 1), by omega, j + 1, rfl, by omega, I'⟩
  · intro t ⟨K, _, ebp, O, V⟩
    -- `ebp` moves back, and the carry word goes up.
    refine wp_subS rfl fun s₂ u₂ _ => ?_
    have K₂ : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s s₂ := K.widen u₂.keeps
    have hs₂ := hs.of_keeps K₂ (by decide)
    have hp₂ : s₂.gpr .ebp = s₂.gpr .edi + BitVec.ofNat 32 (4 * i) := by
      rw [u₂.gpr, ebp, u₂.other _ (by decide)]
      refine (BitVec.eq_sub_iff_add_eq.mpr ?_).symm
      rw [BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have k₂ : Keeps [.eax, .ebx, .ecx, .edx] s s₂ :=
      ⟨fun r hr => by
        by_cases hr' : r = .ebp
        · subst hr'; rw [hp₂, hp, K₂.1 _ (by decide)]
        · exact K₂.1 r (by simp_all), K₂.2⟩
    have mem₂ : s₂.mem = t.mem := u₂.mem
    have ebx₂ : s₂.gpr .ebx = t.gpr .ebx := u₂.other _ (by decide)
    have hhi : val32 s₂.mem base (w + 4 * N) 2 = val32 s.mem base (w + 4 * N) 2 := by
      rw [mem₂]; exact O.val32 (by omega) (by omega)
    have hsplit : val32 s.mem base w (N + 2) =
        val32 s.mem base w N + 2 ^ (32 * N) * val32 s.mem base (w + 4 * N) 2 := val32_append _ _ _ _ _
    rw [pow32_add, show 32 * 2 = 64 by rfl] at hlt
    have hP : 0 < 2 ^ (32 * N) := Nat.two_pow_pos _
    have hlt₁ : val32 s₂.mem base (w + 4 * N) 2 + (s₂.gpr .ebx).toNat < 2 ^ 64 := by
      rw [hhi, ebx₂]
      rw [hsplit] at hlt
      refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (32 * N)) ?_
      rw [Nat.mul_add]
      have := val32_lt t.mem base w N
      omega
    refine WP.mono (carryUp_ok hs₂ hp₂ hw hwN hlt₁) fun u ⟨O₂, V₂, K₃⟩ =>
      ⟨?_, ?_, k₂.trans (K₃.mono (by simp))⟩
    · rw [mem₂] at O₂
      exact (O.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))
    · rw [val32_append, V₂, O₂.val32 (d := w) (k := N) (by omega) (by omega), hhi, hsplit, Nat.mul_add, mem₂,
        ebx₂]
      omega

end VG.Proof.Mont.X86
