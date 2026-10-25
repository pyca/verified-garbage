module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Calls
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Common
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# PBKDF2 over any streaming hash function on RISC-V, the whole derivation: the setup

From the start of the inner frame's body, the prologue saves our caller's
`ra` and `s1`–`s7` at the start of the frame and moves the arguments into
`s1`–`s6` (`prologue_ok`); HMAC's `init` makes the key's inner and outer
states (`States`, of `K₀`, the password made a key, `K0`; `hi_ok`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_mv wp_addi wp_li wp_addSp)
open VG.Impl.Pbkdf2.Whole.RISCV64 (Fns)
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open Spec.Hmac (xorPad ipad opad blockKey)
open Spec.Sha256 (bytesAt)

variable {F : Fns}

/-- Reads registers through register writes (`Upd`), deciding which register
each writes. -/
macro "upd_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (set_option linter.unusedSimpArgs false in simp (disch := decide) only [$ls,*]))

/-- After the prologue: `KR`, the output in `s4` and `s5`, and HMAC's
`init`'s arguments. -/
structure Pro (F : Fns) (s₀ s : State) : Prop where
  kr : KR F s₀ s
  s4 : s.gpr .s4 = out s₀
  s5 : s.gpr .s5 = s₀.gpr .a6
  a0 : s.gpr .a0 = sA s₀ Fns.st0O
  a1 : s.gpr .a1 = sA s₀ F.st1O
  a2 : s.gpr .a2 = pw s₀
  a3 : s.gpr .a3 = s₀.gpr .a1

theorem prologue_eq : F.prologue = .addSp .t0 0 :: (Spill.saveCode .t0 Fns.saved ++
    [mov .s1 .t0, mov .s2 .a3, mov .s3 .a4, mov .s4 .a5, mov .s5 .a6, mov .s6 .a2, mov .a2 .a0, mov .a3 .a1,
      .addi .a0 .s1 Fns.st0O, .addi .a1 .s1 F.st1O]) := rfl

section
variable (hF : FnsOK F) {s₀ : State} (hp : Pre F s₀)
include hF hp

theorem prologue_ok : WP isa (.block F.prologue) s₀ (Pro F s₀) := by
  have hz := sizes hF
  have hl := layout (F := F)
  have hfr := hz.frB
  rw [prologue_eq]
  refine wp_addSp (imm := 0) (by decide) fun s₁ u₁ => ?_
  have t0 : s₁.gpr .t0 = s₀.sp := by rw [u₁.gpr, BitVec.add_zero]
  have e₁ : ∀ r, r ≠ .t0 → s₁.gpr r = s₀.gpr r := fun r h => u₁.other r h
  refine Spill.save_ok (b := .t0) (by rw [t0]; omega_using [hp.al])
    (fun q hq => by
      simp only [Fns.saved, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun q hq => by
      rw [t0, u₁.wr]
      exact in_fr hp rfl (by have := saved_in q hq; omega) (by omega)) ?_
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ =>
    wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => wp_mv fun s₉ u₉ =>
    wp_addi (by simp only [Fns.st0O]; omega) fun s₁₀ u₁₀ => wp_addi (by omega) fun s₁₁ u₁₁ => WP.block_nil ?_
  have mm : s₁₁.mem = Spill.saveMem s₁.mem s₀.sp s₁.gpr Fns.saved := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    show Spill.saveMem s₁.mem (s₁.gpr .t0) s₁.gpr Fns.saved = _
    rw [t0]
  have gg : ∀ r, r ∉ [Reg.s1, .s2, .s3, .s4, .s5, .s6, .a2, .a3, .a0, .a1] → s₁₁.gpr r = s₁.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, f, g, h, i, j, k⟩ := hr
    exact (u₁₁.other r k).trans ((u₁₀.other r j).trans ((u₉.other r i).trans ((u₈.other r h).trans
      ((u₇.other r g).trans ((u₆.other r f).trans ((u₅.other r d).trans ((u₄.other r c).trans
      ((u₃.other r b).trans (u₂.other r a)))))))))
  have sv : Spill.Saved s₀.sp s₀.gpr Fns.saved s₁₁.mem := by
    rw [mm]
    intro q hq
    rw [Spill.saveMem_saved saved_fits s₁.mem s₀.sp s₁.gpr q hq]
    simp only [Fns.saved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact e₁ _ (by decide)
  have q1 : s₁₁.gpr .s1 = s₀.sp := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other,
      u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact t0
  have r : ∀ q, q ≠ .t0 → s₁.gpr q = s₀.gpr q := e₁
  refine ⟨⟨by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd]; exact u₁.rd,
    by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]; exact u₁.wr,
    by rw [u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp]; exact u₁.sp,
    q1, ?_, ?_, ?_, fun q hq => ?_, sv, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other,
      u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact r _ (by decide)
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other,
      u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact r _ (by decide)
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other,
      u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact r _ (by decide)
  · rw [gg q (by revert q; decide), r q (by revert q hq; decide)]
  · rw [mm, u₁.mem]
    refine ((Spill.saveMem_frame_base (n := 64) (fun p hp' => (saved_in p hp').2) (by omega) _ _ _).sub
      fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨frR F s₀, by simp, Region.sub_prefix (by omega)⟩
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other,
      u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact r _ (by decide)
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other,
      u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact r _ (by decide)
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other,
      u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    rw [t0]
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other,
      u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    rw [t0]
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other,
      u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact r _ (by decide)
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other,
      u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact r _ (by decide)

end

/-! ## HMAC's states for the key -/

/-- The key `K₀`: the password, or its digest, padded to a block. -/
abbrev K0 (hF : FnsOK F) (s₀ : State) : List Byte := blockKey hF.hH.SH.H (bytesAt s₀.mem (pw s₀) (pwl s₀))

/-- The key's inner and outer states. -/
def States (hF : FnsOK F) (s₀ : State) (m : Mem) : Prop :=
  hF.hH.SH.Repr m (sA s₀ Fns.st0O) (xorPad (K0 hF s₀) ipad) ∧
    hF.hH.SH.Repr m (sA s₀ F.st1O) (xorPad (K0 hF s₀) opad)

theorem sA_add (s₀ : State) (a b : Nat) : sA s₀ a + BitVec.ofNat 64 b = sA s₀ (a + b) := by
  show s₀.sp + BitVec.ofNat 64 a + BitVec.ofNat 64 b = s₀.sp + BitVec.ofNat 64 (a + b)
  rw [BitVec.ofNat_add, BitVec.add_assoc]

section
variable {hF : FnsOK F} {s₀ : State}

/-- The key's states survive writes apart from them. -/
theorem States.keep {m m' : Mem} (h : States hF s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (sR s₀ Fns.st0O (2 * F.H.S)) r) : States hF s₀ m' := by
  have hz := sizes hF
  have hS : F.H.S ≤ 256 := by have := hz.N; have := hz.B; rw [hz.S]; omega
  refine ⟨hF.hH.congr m m' _ _ (fun i hi => ?_) h.1, hF.hH.congr m m' _ _ (fun i hi => ?_) h.2⟩
  · exact hf.bytes (R := sR s₀ Fns.st0O F.H.S) (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by omega)))
      (by show F.H.S ≤ 2 ^ 64; omega) hi
  · have := hf.bytes (R := sR s₀ Fns.st0O (2 * F.H.S)) (hd · ·) (by show 2 * F.H.S ≤ 2 ^ 64; omega)
      (i := F.H.S + i) (by show F.H.S + i < 2 * F.H.S; omega)
    have e : sA s₀ Fns.st0O + BitVec.ofNat 64 (F.H.S + i) = sA s₀ F.st1O + BitVec.ofNat 64 i := by
      rw [sA_add, sA_add, show Fns.st0O + (F.H.S + i) = F.st1O + i by simp only [Fns.st1O]; omega]
    rwa [e] at this

end

/-- After HMAC's `init`. -/
structure Keyed (hF : FnsOK F) (s₀ s : State) : Prop where
  kr : KR F s₀ s
  s4 : s.gpr .s4 = out s₀
  s5 : s.gpr .s5 = s₀.gpr .a6
  st : States hF s₀ s.mem

section
variable (hF : FnsOK F) {s₀ : State} (hp : Pre F s₀)
include hF hp

/-- HMAC's `init`'s arguments, after the prologue. -/
theorem hi_args {s : State} (h : Pro F s₀ s) :
    HiArgs F s (sA s₀ Fns.st0O) (sA s₀ F.st1O) (pw s₀) (pwl s₀) := by
  have hz := sizes hF; have hl := layout (F := F)
  have hX := hz.X; have hfr := hz.frB
  have bsub : Region.Sub (below s.sp (F.H.ibytes + F.H.F)) (stk F s₀) := by
    rw [h.kr.sp]; exact below_stk hp (by omega)
  have p0 : Region.Sub (sR s₀ Fns.st0O F.H.S) (frR F s₀) := part_sub (by omega)
  have p1 : Region.Sub (sR s₀ F.st1O F.H.S) (frR F s₀) := part_sub (by omega)
  refine ⟨h.a0, h.a1, h.a2, by rw [h.a3], by rw [h.kr.sp]; exact hp.al, by rw [h.kr.sp]; have := hp.spX; omega,
    part_disj (.inl (by omega)) (by omega) (by omega), (hp.f_pw.sub_left p0).symm,
    (hp.f_pw.sub_left p1).symm, (f_s hp).sub_left p0 |>.symm.sub_left bsub,
    (f_s hp).sub_left p1 |>.symm.sub_left bsub, hp.b_pw.sub_left bsub, ?_, ?_⟩
  · rw [h.kr.rd, h.kr.wr, hp.rd, hp.wr]
    refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨pwR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨frR F s₀, by simp, Fns.st0O, rfl, by show Fns.st0O + F.H.S ≤ F.frB; omega⟩
    · exact ⟨frR F s₀, by simp, F.st1O, rfl, by show F.st1O + F.H.S ≤ F.frB; omega⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨frR F s₀, fr_wr hp h.kr.wr, Fns.st0O, rfl, by show Fns.st0O + F.H.S ≤ F.frB; omega⟩
    · exact ⟨frR F s₀, fr_wr hp h.kr.wr, F.st1O, rfl, by show F.st1O + F.H.S ≤ F.frB; omega⟩

theorem hi_ok' {s : State} (h : Pro F s₀ s) : WP isa F.callHi s (Keyed hF s₀) := by
  have hz := sizes hF; have hl := layout (F := F)
  have hX := hz.X; have hfr := hz.frB
  refine hi_call hF (hi_args hF hp h) fun s' a hI hO => ?_
  have kr' := h.kr.call hp hz a.rd a.wr a.sp a.cs a.frame fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl ⟨_, _, rfl, by simp only [Fns.st0O]; omega, by omega⟩
    · exact .inl ⟨_, _, rfl, by omega, by omega⟩
    · exact .inr (.inr ⟨_, by rw [h.kr.sp], by omega⟩)
  rw [h.kr.pwBytes hp] at hI hO
  exact ⟨kr', by rw [a.cs _ (by decide), h.s4], by rw [a.cs _ (by decide), h.s5], hI, hO⟩

end

end VG.Proof.Pbkdf2.Whole.RISCV64
