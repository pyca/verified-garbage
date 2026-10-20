module

public import VerifiedGarbage.Impl.Mont.X86.Dynamic
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Mont.X86.Loop
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# A multiply-accumulate row as a loop (x86, 32-bit)

`mulRowW acc b N` adds `[mult] · [b]` to the window at `[ebp + acc]`, as
`mulRow` does (`mulRow_ok`), in a loop over two words at a time: each word
(`macW_ok`) reads `[ecx + b + d]` and writes `[ebp + acc + d]`, and is a
step of the row's invariant (`macW_inv`); then both pointers move up two
words (`stepCtl_ok`). `ebp` is moved back before the carry word is added
(`carryUp_ok`).
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

/-- One word of the row: `[ebp + acc + d] += [mult] · [ecx + b + d] + ebx`,
the carry word to `ebx`, at the byte `o` of the row. -/
theorem macW_ok {t : State} {base : Addr} {size : Nat} (hs : Scr t base size) {acc b i j d o w mult : Nat}
    (hecx : t.gpr .ecx = t.gpr .edi + BitVec.ofNat 32 (4 * j))
    (hp : t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * (i + j))) (hw : 4 * i + acc = w)
    (ho : 4 * j + d = o) (hb : b + o + 4 ≤ size) (ht : w + o + 4 ≤ size) (hm : mult + 4 ≤ size) :
    WP isa (.block (macW acc b mult d)) t fun u =>
      u.mem = t.mem.writeW (off base (w + o)) (BitVec.ofNat 32
        (w32 t.mem base mult * w32 t.mem base (b + o) + (t.gpr .ebx).toNat + w32 t.mem base (w + o))) ∧
      (u.gpr .ebx).toNat = (w32 t.mem base mult * w32 t.mem base (b + o) + (t.gpr .ebx).toNat +
          w32 t.mem base (w + o)) / 2 ^ 32 ∧
      Keeps [.eax, .ebx, .edx] t u := by
  have hn := hs.nowrap
  have eb : 4 * j + (b + d) = b + o := by omega
  have ew : 4 * (i + j) + (acc + d) = w + o := by omega
  simp only [macW]
  refine wp_movS (readSrc_sc hs hm) fun s₀ u₀ _ => ?_
  have hs₀ := hs.of_keeps u₀.keeps (by decide)
  have hecx₀ : s₀.gpr .ecx = s₀.gpr .edi + BitVec.ofNat 32 (4 * j) := by
    rw [u₀.other _ (by decide), u₀.other _ (by decide)]; exact hecx
  refine wp_movS (readSrc_regAt hs₀ hecx₀ (d := b + d) (by omega)) fun s₁ u₁ _ => ?_
  refine wp_mul fun s₂ m₂ => ?_
  have K₂ : Keeps [.eax, .edx] t s₂ := ((u₀.keeps.mono (by decide)).widen u₁.keeps).widen m₂.keeps
  have hs₂ := hs.of_keeps K₂ (by decide)
  have hp₂ : s₂.gpr .ebp = s₂.gpr .edi + BitVec.ofNat 32 (4 * (i + j)) := by
    rw [K₂.1 _ (by decide), K₂.1 _ (by decide)]; exact hp
  refine wp_addS (readSrc_regAt hs₂ hp₂ (d := acc + d) (by omega)) fun s₃ u₃ c₃ => ?_
  refine wp_adcS rfl c₃ fun s₄ u₄ c₄ => ?_
  refine wp_addS rfl fun s₅ u₅ c₅ => ?_
  refine wp_adcS rfl c₅ fun s₆ u₆ c₆ => ?_
  have K₄ : Keeps [.eax, .edx] t s₄ := (K₂.widen u₃.keeps).widen u₄.keeps
  have K₆ : Keeps [.eax, .edx] t s₆ := (K₄.widen u₅.keeps).widen u₆.keeps
  have hs₆ := hs.of_keeps K₆ (by decide)
  have hp₆ : s₆.gpr .ebp = s₆.gpr .edi + BitVec.ofNat 32 (4 * (i + j)) := by
    rw [K₆.1 _ (by decide), K₆.1 _ (by decide)]; exact hp
  refine wp_storeS (hs₆.ea_regAt hp₆ (d := acc + d) (by omega))
    (hs₆.write (d := 4 * (i + j) + (acc + d)) (n := 4) (by omega)) fun s₇ m₇ => ?_
  refine wp_movS rfl fun s₈ u₈ _ => WP.block_nil ?_
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
  have eax₃ : s₃.gpr .eax = s₂.gpr .eax + t.mem.readW (off base (w + o)) 32 := by
    rw [u₃.gpr, m₂', ew]
  have edx₄ : s₄.gpr .edx = s₃.gpr .edx + 0 + (BitVec.ofBool _).setWidth 32 := u₄.gpr
  have eax₄ : s₄.gpr .eax = s₃.gpr .eax := u₄.other _ (by decide)
  have edx₃ : s₃.gpr .edx = s₂.gpr .edx := u₃.other _ (by decide)
  have ebx₄ : s₄.gpr .ebx = t.gpr .ebx := by rw [u₄.other _ (by decide), u₃.other _ (by decide), ebx₂]
  have eax₅ : s₅.gpr .eax = s₄.gpr .eax + s₄.gpr .ebx := u₅.gpr
  have edx₆ : s₆.gpr .edx = s₅.gpr .edx + 0 + (BitVec.ofBool _).setWidth 32 := u₆.gpr
  have eax₆ : s₆.gpr .eax = s₅.gpr .eax := u₆.other _ (by decide)
  have edx₅ : s₅.gpr .edx = s₄.gpr .edx := u₅.other _ (by decide)
  have hpost := step_regs (t.mem.readW (off base (b + o)) 32) (t.mem.readW (off base mult) 32)
    (t.mem.readW (off base (w + o)) 32) (t.gpr .ebx) _ _ rfl rfl
  rw [Nat.mul_comm (t.mem.readW (off base (b + o)) 32).toNat] at hpost
  have ex₆ : s₆.gpr .eax = BitVec.ofNat 32 ((t.mem.readW (off base mult) 32).toNat *
      (t.mem.readW (off base (b + o)) 32).toNat) + t.mem.readW (off base (w + o)) 32 + t.gpr .ebx := by
    rw [eax₆, eax₅, ebx₄, eax₄, eax₃, eax₂]
  have dx₆ := edx₆
  rw [edx₅, edx₄, edx₃, edx₂, ebx₄, eax₄, eax₃, eax₂, m₂', ew] at dx₆
  have hx : s₆.gpr .eax = BitVec.ofNat 32 (w32 t.mem base mult * w32 t.mem base (b + o) +
      (t.gpr .ebx).toNat + w32 t.mem base (w + o)) := by
    apply BitVec.eq_of_toNat_eq
    rw [ex₆, hpost.1, BitVec.toNat_ofNat, Nat.add_right_comm]
  have K₇ : Keeps [.eax, .edx] t s₇ := K₆.widen (m₇.keeps [])
  refine ⟨by rw [u₈.mem, m₇.mem, m₆, hx, ew], ?_, (K₇.mono (by decide)).widen u₈.keeps⟩
  rw [u₈.gpr, m₇.gpr, dx₆, hpost.2, Nat.add_right_comm]

/-- One word of the row, as a step of the row's invariant: the window's low
`j` words and the carry word hold the window's start plus `[mult] · [b]`'s
low `j` words. -/
theorem macW_inv {s t : State} {base : Addr} {size : Nat} (hs : Scr t base size)
    {acc b i jc d j w N mult : Nat}
    (hecx : t.gpr .ecx = t.gpr .edi + BitVec.ofNat 32 (4 * jc))
    (hp : t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * (i + jc))) (hw : 4 * i + acc = w)
    (hd : 4 * jc + d = 4 * j) (hj : j < N) (hb : b + 4 * N ≤ size) (hwN : w + 4 * N + 8 ≤ size)
    (hsep : b + 4 * N ≤ w ∨ w + 4 * N + 8 ≤ b) (hm : mult + 4 ≤ size)
    (hsm : mult + 4 ≤ w ∨ w + 4 * N + 8 ≤ mult)
    (O : Outside base w (4 * j) s.mem t.mem)
    (V : val32 t.mem base w j + 2 ^ (32 * j) * (t.gpr .ebx).toNat =
      val32 s.mem base w j + w32 s.mem base mult * val32 s.mem base b j) :
    WP isa (.block (macW acc b mult d)) t fun u =>
      Outside base w (4 * (j + 1)) s.mem u.mem ∧
      val32 u.mem base w (j + 1) + 2 ^ (32 * (j + 1)) * (u.gpr .ebx).toNat =
        val32 s.mem base w (j + 1) + w32 s.mem base mult * val32 s.mem base b (j + 1) ∧
      Keeps [.eax, .ebx, .edx] t u := by
  have hn := hs.nowrap
  refine WP.mono (macW_ok hs hecx hp hw hd (by omega) (by omega) hm) fun u ⟨mu, bu, Ku⟩ => ?_
  have mk : w32 t.mem base mult = w32 s.mem base mult := O.w32 (by omega) (by omega)
  have bk : w32 t.mem base (b + 4 * j) = w32 s.mem base (b + 4 * j) := O.w32 (by omega) (by omega)
  have tk : w32 t.mem base (w + 4 * j) = w32 s.mem base (w + 4 * j) := O.w32 (by omega) (by omega)
  rw [mk, bk, tk] at mu bu
  have W := writeW32_outside t.mem base (d := w + 4 * j)
    (BitVec.ofNat 32 (w32 s.mem base mult * w32 s.mem base (b + 4 * j) + (t.gpr .ebx).toNat +
      w32 s.mem base (w + 4 * j))) (by omega)
  rw [← mu] at W
  refine ⟨(O.mono (Nat.le_refl _) (by omega)).trans (W.mono (by omega) (by omega)), ?_, Ku⟩
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

/-- `ZF` after the loop's comparison: whether `ecx` reached `edi + 4N`. -/
theorem row2_zf (e : BitVec 32) {j N : Nat} (hj : j + 2 ≤ N) (hN : 4 * N < 2 ^ 32) :
    (e + BitVec.ofNat 32 (4 * j) + 8 - (e + BitVec.ofNat 32 (4 * N)) == 0) = decide (j + 2 = N) := by
  by_cases h : j + 2 = N
  · subst h; simp only [decide_true, beq_iff_eq]; bv_omega
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]; bv_omega

theorem row2_ptr (e : BitVec 32) (j : Nat) :
    e + BitVec.ofNat 32 (4 * j) + 8 = e + BitVec.ofNat 32 (4 * (j + 2)) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have : (8 : BitVec 32).toNat = 8 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, this]
  omega_using []

/-- The loop's own instructions, after two words: both pointers move up two
words, and `ZF` says whether the row is done. -/
theorem stepCtl_ok {t : State} {i j N : Nat}
    (hecx : t.gpr .ecx = t.gpr .edi + BitVec.ofNat 32 (4 * j))
    (hp : t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * (i + j))) (hj : j + 2 ≤ N) (hN32 : 4 * N < 2 ^ 32) :
    WP isa (.block [.alu .add .ecx (.imm 8), .alu .add .ebp (.imm 8), .mov .eax (.reg .edi),
        .alu .add .eax (.imm (BitVec.ofNat 32 (4 * N))), .alu .cmp .ecx (.reg .eax)]) t fun u =>
      u.mem = t.mem ∧ u.gpr .ecx = u.gpr .edi + BitVec.ofNat 32 (4 * (j + 2)) ∧
      u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * (i + (j + 2))) ∧
      u.zf = some (decide (j + 2 = N)) ∧ Keeps [.eax, .ecx, .ebp] t u := by
  refine wp_addS rfl fun s₁ u₁ _ => ?_
  refine wp_addS rfl fun s₂ u₂ _ => ?_
  refine wp_movS rfl fun s₃ u₃ _ => ?_
  refine wp_addS rfl fun s₄ u₄ _ => ?_
  refine wp_cmpS rfl fun s₅ f₅ z₅ => WP.block_nil ?_
  have K₅ : Keeps [.eax, .ecx, .ebp] t s₅ :=
    (((((u₁.keeps.mono (rs' := [.eax, .ecx, .ebp]) (by decide)).widen u₂.keeps).widen u₃.keeps).widen
      u₄.keeps).widen (f₅.keeps []))
  have edi₅ : s₅.gpr .edi = t.gpr .edi := K₅.1 _ (by decide)
  have ecx₄ : s₄.gpr .ecx = t.gpr .edi + BitVec.ofNat 32 (4 * j) + 8 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hecx]
  have ebp₄ : s₄.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * (i + j)) + 8 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hp]
  have eax₄ : s₄.gpr .eax = t.gpr .edi + BitVec.ofNat 32 (4 * N) := by
    rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  refine ⟨by rw [f₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [edi₅, f₅.gpr, ecx₄, row2_ptr],
    by rw [edi₅, f₅.gpr, ebp₄, row2_ptr, Nat.add_assoc], by rw [z₅, ecx₄, eax₄, row2_zf _ hj hN32], K₅⟩

/-- The window `+= [mult] · [b]` (`N` words), when the sum fits its `N + 2`
words; `ecx` is used and `ebp` restored. -/
theorem mulRowW_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc b i w N : Nat}
    (hN : 0 < N) (hE : N % 2 = 0) (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (hw : 4 * i + acc = w) (hb : b + 4 * N ≤ size) (hwN : w + 4 * N + 8 ≤ size)
    (hsep : b + 4 * N ≤ w ∨ w + 4 * N + 8 ≤ b)
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
  refine WP.seq (WP.mono (WP.loop (M := isa) (Q := I N)
    (fun m t => ∃ j, m = N - j ∧ j < N ∧ j % 2 = 0 ∧ I j t) ?_ N s₁ ⟨0, by omega, hN, rfl, I₀⟩) ?_)
  · rintro m t ⟨j, rfl, hj, hj2, K, ecx, ebp, O, V⟩
    have hj' : j + 2 ≤ N := by omega
    have ht := hs.of_keeps K (by decide)
    simp only [mulStepW, List.append_assoc]
    refine WP.block_append (WP.mono (macW_inv ht ecx ebp hw (Nat.add_zero _) hj hb hwN hsep hm hsm O V)
      fun t₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have ht₁ := ht.of_keeps K₁ (by decide)
    have ecx₁ : t₁.gpr .ecx = t₁.gpr .edi + BitVec.ofNat 32 (4 * j) := by
      rw [K₁.1 _ (by decide), K₁.1 _ (by decide)]; exact ecx
    have ebp₁ : t₁.gpr .ebp = t₁.gpr .edi + BitVec.ofNat 32 (4 * (i + j)) := by
      rw [K₁.1 _ (by decide), K₁.1 _ (by decide)]; exact ebp
    refine WP.block_append (WP.mono (macW_inv ht₁ ecx₁ ebp₁ hw (j := j + 1) (by omega) (by omega) hb hwN hsep
      hm hsm O₁ V₁) fun t₂ ⟨O₂, V₂, K₂⟩ => ?_)
    have ecx₂ : t₂.gpr .ecx = t₂.gpr .edi + BitVec.ofNat 32 (4 * j) := by
      rw [K₂.1 _ (by decide), K₂.1 _ (by decide)]; exact ecx₁
    have ebp₂ : t₂.gpr .ebp = t₂.gpr .edi + BitVec.ofNat 32 (4 * (i + j)) := by
      rw [K₂.1 _ (by decide), K₂.1 _ (by decide)]; exact ebp₁
    refine WP.mono (stepCtl_ok ecx₂ ebp₂ hj' hN32) fun u ⟨mu, su, pu, zu, Ku⟩ => ?_
    have ebx₂ : u.gpr .ebx = t₂.gpr .ebx := Ku.1 _ (by decide)
    have I' : I (j + 2) u := by
      refine ⟨K.trans ((K₁.trans K₂).mono (by decide) |>.widen Ku), su, pu, by rw [mu]; exact O₂, ?_⟩
      rw [mu, ebx₂]; exact V₂
    by_cases hjN : j + 2 = N
    · exact .inl ⟨by simp only [eval, zu, hjN, decide_true, Option.map_some, Bool.not_true], hjN ▸ I'⟩
    · exact .inr ⟨by simp only [eval, zu, decide_eq_false hjN, Option.map_some, Bool.not_false],
        N - (j + 2), by omega, j + 2, rfl, by omega, by omega, I'⟩
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
