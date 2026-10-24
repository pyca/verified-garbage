module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Calls
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Copy

/-!
# PBKDF2 over any streaming hash function on PPC64LE, the whole derivation: the setup

From the start of the frame (`framed`, the link register in `r0` pushed),
the prologue saves our caller's `r20`–`r25` and moves the arguments into
them (`prologue_ok`); HMAC's `init` makes the key's inner and outer states
(`States`, of `K₀`, the password made a key, `K0`); and `INT (1)` is stored
(`setup_ok`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.PPC64LE

open VG.PPC64LE
open VG.Impl.Pbkdf2.Whole.PPC64LE (Fns)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK Saved saveMem saveMem_saved saveMem_frame save_ok untouched)
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_mov wp_addi wp_li wp_stwbrx)
open Spec.Hmac (xorPad ipad opad blockKey)
open Spec.Sha256 (bytesAt)

variable {F : Fns}

/-- Reads registers through register writes (`Upd`), deciding which register
each writes. -/
macro "upd_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (set_option linter.unusedSimpArgs false in simp (disch := decide) only [$ls,*]))

/-- The frame's push writes only the 48 bytes below the stack pointer. -/
theorem framed_frame {s : State} (r : Reg) : Frame [below s.sp 48] s.mem (framed r s).mem := by
  have c : ∀ off, off + 8 ≤ 48 → (below s.sp 48).Contains (s.sp - 48 + BitVec.ofNat 64 off) 8 := fun off ho => by
    simp only [Region.Contains]
    rw [show s.sp - 48 + BitVec.ofNat 64 off - (s.sp - BitVec.ofNat 64 48) = BitVec.ofNat 64 off by
      bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  exact Frame.write (Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ (by simpa using c 0 (by omega)))
    (List.mem_singleton_self _) _ (c 32 (by omega))

/-- The state the frame's body starts in. -/
abbrev entry (s₀ : State) : State := framed .r0 (s₀.write .r0 s₀.lr)

theorem entry_gpr (s₀ : State) {r : Reg} (h : r ≠ .r0) : (entry s₀).gpr r = s₀.gpr r := by
  simp [framed, State.write, h]

/-- After the prologue: `KR`, the output in `r23` and `r24`, and HMAC's
`init`'s arguments. -/
structure Pro (F : Fns) (X : Nat) (s₀ s : State) : Prop where
  kr : KR F X s₀ s
  r23 : s.gpr .r23 = out s₀
  r24 : s.gpr .r24 = s₀.gpr .r9
  r3 : s.gpr .r3 = sA s₀ F.st0O
  r4 : s.gpr .r4 = sA s₀ F.st1O
  r5 : s.gpr .r5 = pw s₀
  r6 : s.gpr .r6 = s₀.gpr .r4

section
variable (hF : FnsOK F) {s₀ : State} (hp : Pre F hF.X s₀)
include hF hp

theorem prologue_ok : WP isa (.block F.prologue) (entry s₀) (Pro F hF.X s₀) := by
  have hz := sizes hF
  have hl := layout (F := F)
  have hb := hz.reach
  have hsp : 48 ≤ s₀.sp.toNat := by have := hp.sp; omega
  unfold Fns.prologue
  refine save_ok (so := 0) ⟨rfl, by decide⟩ (b := .r10) (by decide)
    (fun d _ hd => by rw [entry_gpr s₀ (by decide)]; exact in_sc hp hz.reach rfl (by omega))
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ => wp_mov fun s₆ u₆ =>
    wp_mov fun s₇ u₇ => wp_mov fun s₈ u₈ => wp_mov fun s₉ u₉ =>
    wp_addi (by omega) fun s₁₀ u₁₀ => wp_addi (by omega) fun s₁₁ u₁₁ => WP.block_nil ?_
  have e : ∀ r, r ≠ .r0 → s₁.gpr r = s₀.gpr r := fun r h => by rw [g₁]; exact entry_gpr s₀ h
  have mm : s₁₁.mem = s₁.mem := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have gg : ∀ r, r ∉ [Reg.r21, .r20, .r22, .r23, .r24, .r25, .r5, .r6, .r3, .r4] → s₁₁.gpr r = s₁.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, f, g, h, i, j, k⟩ := hr
    rw [u₁₁.other r k, u₁₀.other r j, u₉.other r i, u₈.other r h, u₇.other r g, u₆.other r f, u₅.other r d,
      u₄.other r c, u₃.other r b, u₂.other r a]
  have sv : Saved 0 (scr s₀) s₀.gpr s₁₁.mem := by
    rw [mm, m₁, show (entry s₀).gpr .r10 = scr s₀ from entry_gpr s₀ (by decide)]
    intro p hp'
    have h0 : p.1 ≠ .r0 := by
      simp only [Hash.savedAt, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [saveMem_saved (so := 0) ⟨rfl, by decide⟩ (entry s₀).mem (scr s₀) (entry s₀).gpr p hp', entry_gpr s₀ h0]
  have q20 : s₁₁.gpr .r20 = s₀.gpr .r6 := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
      u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e _ (by decide)
  have q21 : s₁₁.gpr .r21 = scr s₀ := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
      u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e _ (by decide)
  have q22 : s₁₁.gpr .r22 = s₀.gpr .r7 := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
      u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e _ (by decide)
  have q23 : s₁₁.gpr .r23 = out s₀ := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
      u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e _ (by decide)
  have q24 : s₁₁.gpr .r24 = s₀.gpr .r9 := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
      u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e _ (by decide)
  have q25 : s₁₁.gpr .r25 = salt s₀ := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
      u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e _ (by decide)
  have q3 : s₁₁.gpr .r3 = sA s₀ F.st0O := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
      u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    rw [e _ (by decide)]
  have q4 : s₁₁.gpr .r4 = sA s₀ F.st1O := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
      u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    rw [e _ (by decide)]
  have q5 : s₁₁.gpr .r5 = pw s₀ := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
      u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e _ (by decide)
  have q6 : s₁₁.gpr .r6 = s₀.gpr .r4 := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
      u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e _ (by decide)
  refine ⟨⟨by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]; rfl,
    by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]; rfl,
    by rw [u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]; rfl,
    q20, q21, q22, q25, fun r hr => ?_, sv, ?_⟩, q23, q24, q3, q4, q5, q6⟩
  · rw [gg r (by revert r hr; decide), e r (by revert r hr; decide)]
  · rw [mm, m₁]
    have f1 : Frame [below s₀.sp 48] s₀.mem (entry s₀).mem := framed_frame (s := s₀.write .r0 s₀.lr) .r0
    refine (f1.sub fun r hr => ?_).trans ((saveMem_frame (so := 0) ⟨rfl, by decide⟩ _ _ _).sub
      fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stk hF.X s₀, by simp, below_sub (by omega) (by have := hp.sp; have := s₀.sp.isLt; omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨scR F s₀, by simp, ?_⟩
      rw [entry_gpr s₀ (by decide)]
      exact Region.sub_prefix (by omega)

end

/-! ## HMAC's states for the key -/

/-- The key `K₀`: the password, or its digest, padded to a block. -/
abbrev K0 (hF : FnsOK F) (s₀ : State) : List Byte := blockKey hF.hH.SH.H (bytesAt s₀.mem (pw s₀) (pwl s₀))

/-- The key's inner and outer states. -/
def States (hF : FnsOK F) (s₀ : State) (m : Mem) : Prop :=
  hF.hH.SH.Repr m (sA s₀ F.st0O) (xorPad (K0 hF s₀) ipad) ∧ hF.hH.SH.Repr m (sA s₀ F.st1O) (xorPad (K0 hF s₀) opad)

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F hF.X s₀)
include hp

theorem sp_toNat : (s₀.sp - 48).toNat = s₀.sp.toNat - 48 := by
  have := hp.sp
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 (by simp; omega))]; rfl

theorem sA_toNat {o : Nat} (h : o < F.bytes) : (sA s₀ o).toNat = (scr s₀).toNat + o := by
  have := hp.nsc
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]

omit hp in
/-- The key's states survive writes apart from them. -/
theorem States.keep {m m' : Mem} (h : States hF s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (sR s₀ F.st0O (2 * F.H.S)) r) : States hF s₀ m' := by
  have hz := sizes hF
  have hS : F.H.S ≤ 256 := by have := hz.N; have := hz.B; rw [hz.S]; omega
  refine ⟨hF.hH.congr m m' _ _ (fun i hi => ?_) h.1, hF.hH.congr m m' _ _ (fun i hi => ?_) h.2⟩
  · exact hf.bytes (R := sR s₀ F.st0O F.H.S) (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by omega)))
      (by show F.H.S ≤ 2 ^ 64; omega) hi
  · have := hf.bytes (R := sR s₀ F.st0O (2 * F.H.S)) (hd · ·) (by show 2 * F.H.S ≤ 2 ^ 64; omega)
      (i := F.H.S + i) (by show F.H.S + i < 2 * F.H.S; omega)
    rwa [VG.Proof.Hmac.Stream.PPC64LE.add_off, show sA s₀ F.st0O + BitVec.ofNat 64 F.H.S = sA s₀ F.st1O by
      rw [← VG.Proof.Hmac.Stream.PPC64LE.add_off]; rfl] at this

end

/-- After HMAC's `init`. -/
structure Keyed (hF : FnsOK F) (s₀ s : State) : Prop where
  kr : KR F hF.X s₀ s
  r23 : s.gpr .r23 = out s₀
  r24 : s.gpr .r24 = s₀.gpr .r9
  st : States hF s₀ s.mem

section
variable (hF : FnsOK F) {s₀ : State} (hp : Pre F hF.X s₀)
include hF hp

/-- HMAC's `init`'s arguments, after the prologue. -/
theorem hi_args {s : State} (h : Pro F hF.X s₀ s) :
    HiArgs hF s (sA s₀ F.st0O) (sA s₀ F.st1O) (pw s₀) (pwl s₀) := by
  have hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  have hsp := sp_toNat hp
  have hX := hF.hX
  have bsub : Region.Sub (below s.sp (hF.X + 96)) (stk hF.X s₀) := by
    rw [h.kr.sp]; exact below_stk hp (by omega)
  have p0 : Region.Sub (sR s₀ F.st0O F.H.S) (scR F s₀) := part_sub (by omega)
  have p1 : Region.Sub (sR s₀ F.st1O F.H.S) (scR F s₀) := part_sub (by omega)
  refine ⟨h.r3, h.r4, h.r5, by rw [h.r6], by rw [h.kr.sp, hsp]; have := hp.sp; omega,
    part_disj hb (.inl (by omega)) (by omega) (by omega), (hp.pw_s.sub_right p0).symm,
    (hp.pw_s.sub_right p1).symm, hp.b_s.sub_left bsub |>.sub_right p0, hp.b_s.sub_left bsub |>.sub_right p1,
    hp.b_pw.sub_left bsub, by rw [sA_toNat hp (by omega)]; have := hp.nsc; omega,
    by rw [sA_toNat hp (by omega)]; have := hp.nsc; omega, hp.npw, ?_, ?_⟩
  · rw [h.kr.rd, h.kr.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨pwR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR F s₀, by simp, F.st0O, rfl, by show F.st0O + F.H.S ≤ F.bytes; omega⟩
    · exact ⟨scR F s₀, by simp, F.st1O, rfl, by show F.st1O + F.H.S ≤ F.bytes; omega⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scR F s₀, sc_wr hp h.kr.wr, F.st0O, rfl, by show F.st0O + F.H.S ≤ F.bytes; omega⟩
    · exact ⟨scR F s₀, sc_wr hp h.kr.wr, F.st1O, rfl, by show F.st1O + F.H.S ≤ F.bytes; omega⟩

theorem hi_ok {s : State} (h : Pro F hF.X s₀ s) : WP isa F.callHi s (Keyed hF s₀) := by
  have hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  have hX := hF.hX
  refine hi_call hF (hi_args hF hp h) fun s' a hI hO => ?_
  have kr' := h.kr.call hp hb a.rd a.wr a.sp a.cs a.frame fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl ⟨_, _, rfl, by omega, by omega⟩
    · exact .inl ⟨_, _, rfl, by omega, by omega⟩
    · exact .inr ⟨_, by rw [h.kr.sp], by omega⟩
  rw [h.kr.pwBytes hp] at hI hO
  exact ⟨kr', by rw [a.cs _ (by decide), h.r23], by rw [a.cs _ (by decide), h.r24], hI, hO⟩

end

end VG.Proof.Pbkdf2.Whole.PPC64LE
