module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Copy
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# PBKDF2 over any streaming hash function on PPC64LE, the whole derivation: the rest of a block, and the loop

`T` starts as `U₁` and `iterate` runs the other `c - 1` steps (`t_ok`):
`T = T_{k+1}`. As much of it as the output still needs is copied to `out`
(`outLen_ok`, `outLoop_ok`), and the pointers and `INT (i)` advance
(`tail_ok`): `Inv` holds after `k + 1` blocks (`block_ok`), and after all of
them (`loop_ok`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.PPC64LE

open VG.PPC64LE
open VG.Impl.Pbkdf2.Whole.PPC64LE (Fns)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK Saved)
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_mov wp_addi wp_subi wp_li wp_add wp_sub wp_lsr wp_lbz wp_stb
  wp_stwbrx)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.WriteBytes (writeBytes)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

variable {F : Fns}

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F hF.X s₀)
include hp

/-- `T ← U₁`, and `iterate`'s arguments. -/
theorem b7_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block (F.copyT ++ F.iterArgs)) s fun t => Inv hF s₀ k t ∧
      bytesAt t.mem (sA s₀ F.uO) F.H.D = bytesAt s.mem (sA s₀ F.uO) F.H.D ∧
      bytesAt t.mem (sA s₀ F.tO) F.H.D = bytesAt s.mem (sA s₀ F.uO) F.H.D ∧
      t.gpr .r3 = sA s₀ F.st0O ∧ t.gpr .r4 = sA s₀ F.uO ∧ t.gpr .r5 = s₀.gpr .r7 - 1 ∧
      t.gpr .r6 = sA s₀ F.tO ∧ t.gpr .r7 = sA s₀ 48 := by
  have hz := sizes hF; have hl := layout (F := F); have hb := hz.reach; have hD := hz.D
  have hD4 : 4 * (F.H.D / 4) = F.H.D := by have := hz.D4; omega
  unfold Fns.copyT Fns.iterArgs
  refine copy_ok hp h (a := F.uO) (b := F.tO) (n := F.H.D / 4) (by omega) (by omega)
    (.inr (.inl ⟨_, _, rfl, by omega, by omega⟩)) (by omega) fun t ht g m => ?_
  rw [hD4] at m
  refine wp_addi (by omega) fun s₁ u₁ => wp_addi (by omega) fun s₂ u₂ => wp_subi (by decide) fun s₃ u₃ =>
    wp_addi (by omega) fun s₄ u₄ => wp_addi (by decide) fun s₅ u₅ => WP.block_nil ?_
  have mm : s₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hn : F.H.D < 2 ^ 64 := by omega
  refine ⟨ht.keep hp (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (fun r hr => by
      rw [u₅.other r (by revert r; decide), u₄.other r (by revert r; decide), u₃.other r (by revert r; decide),
        u₂.other r (by revert r; decide), u₁.other r (by revert r; decide)]) (rs := [])
    (by rw [mm]; exact Frame.refl _ _) (by simp), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have fr : Frame [sR s₀ F.tO F.H.D] s.mem t.mem := by
      rw [m]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
    rw [mm]
    exact VG.Proof.Sha256.Stream.bytesAt_congr fun _ hi => fr.bytes (R := sR s₀ F.uO F.H.D)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact part_disj hb (.inl (by omega)) (by omega) (by omega)) (by show F.H.D ≤ 2 ^ 64; omega) hi
  · rw [mm, m]
    have := VG.Proof.Hmac.Common.bytesAt_writeBytes_self s.mem (sA s₀ F.tO) (bytesAt s.mem (sA s₀ F.uO) F.H.D)
      (by rw [bytesAt_length]; exact hn)
    rwa [bytesAt_length] at this
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.r21]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.r21]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.r22]; rfl
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.r21]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.r21]; rfl

end

theorem iterBytes (H : Hash) : Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes H = H.W + 48 + H.S + H.FD + H.FD := by
  simp only [Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes, Impl.Pbkdf2.Stream.PPC64LE.Iter.ub,
    Impl.Pbkdf2.Stream.PPC64LE.Iter.dig, Impl.Pbkdf2.Stream.PPC64LE.Iter.st]

/-- The low word of `c - 1`. -/
theorem lo_pred (x : BitVec 64) (h : 0 < (x.setWidth 32).toNat) :
    ((x - 1).setWidth 32).toNat = (x.setWidth 32).toNat - 1 := by
  rw [lo32_sub, show (1 : BitVec 64).setWidth 32 = 1 from rfl,
    BitVec.toNat_sub_of_le (BitVec.le_def.2 (by simp only [BitVec.toNat_setWidth] at h ⊢; simp; omega))]
  rfl

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F hF.X s₀)
include hp

/-- The other `c - 1` steps, with `iterate`: `T = T_{k+1}`. -/
theorem b8_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) {u : List Byte}
    (hu : bytesAt s.mem (sA s₀ F.uO) F.H.D = u) (ht : bytesAt s.mem (sA s₀ F.tO) F.H.D = u)
    (h3 : s.gpr .r3 = sA s₀ F.st0O) (h4 : s.gpr .r4 = sA s₀ F.uO) (h5 : s.gpr .r5 = s₀.gpr .r7 - 1)
    (h6 : s.gpr .r6 = sA s₀ F.tO) (h7 : s.gpr .r7 = sA s₀ 48) :
    WP isa F.callIt s fun t => Inv hF s₀ k t ∧
      bytesAt t.mem (sA s₀ F.tO) F.H.D = Spec.Pbkdf2.iterate (prf hF s₀) (cc s₀ - 1) u u := by
  have hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  have hWc := hz.Wc; have hSS := hz.S; have hD := hz.D; have hN := hz.N; have hB := hz.B
  have hbH := iterBytes F.H
  have hsp := sp_toNat hp
  have hK := blockKey_length hF.hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  have bs := below48 hp h.kr (n := 96) (by omega)
  have pd : ∀ {a m b n : Nat}, a + m ≤ b ∨ b + n ≤ a → a + m ≤ F.bytes → b + n ≤ F.bytes →
      Region.Disjoint (sR s₀ a m) (sR s₀ b n) := fun h₁ h₂ h₃ => part_disj hb h₁ h₂ h₃
  have bp : ∀ {o n : Nat}, o + n ≤ F.bytes → (below s.sp 96).Disjoint (sR s₀ o n) := fun h' =>
    hp.b_s.sub_left bs |>.sub_right (part_sub h')
  have cv : ∀ o n, o + n ≤ F.bytes → ∃ r' ∈ s.wr, ∃ off,
      (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len :=
    fun o n h' => ⟨scR F s₀, sc_wr hp h.kr.wr, o, rfl, h'⟩
  have cv' : ∀ o n, o + n ≤ F.bytes → ∃ r' ∈ s.rd ++ s.wr, ∃ off,
      (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len := fun o n h' => by
    obtain ⟨r', hr', off, e, l⟩ := cv o n h'; exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
  refine it_call hF h3 h4 h6 h7 (by rw [h.kr.sp, hsp]; have := hp.sp; omega)
    (pd (.inl (by omega)) (by omega) (by omega)) (pd (.inr (by rw [hbH]; omega)) (by omega) (by rw [hbH]; omega))
    (pd (.inl (by omega)) (by omega) (by omega)) (pd (.inr (by rw [hbH]; omega)) (by omega) (by rw [hbH]; omega))
    (pd (.inr (by rw [hbH]; omega)) (by omega) (by rw [hbH]; omega))
    (bp (by omega)) (bp (by omega)) (bp (by omega)) (bp (by rw [hbH]; omega)) ?_ ?_ fun t a hi => ?_
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact cv' F.st0O (2 * F.H.S) (by omega)
    · exact cv' F.uO F.H.D (by omega)
    · exact cv' F.tO F.H.D (by omega)
    · exact cv' 48 _ (by rw [hbH]; omega)
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cv F.tO F.H.D (by omega)
    · exact cv 48 _ (by rw [hbH]; omega)
  · refine ⟨h.keep hp a.rd a.wr a.sp (fun r hr => a.cs r (by revert r; decide)) a.frame fun r hr => ?_, ?_⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr (.inl ⟨_, _, rfl, by omega, by omega⟩)
      · exact .inl ⟨_, _, rfl, Nat.le_refl _, by rw [hbH]; omega⟩
      · exact .inr (.inr ⟨96, by rw [h.kr.sp], by omega⟩)
    · have e1 : sA s₀ F.st0O + BitVec.ofNat 64 F.H.S = sA s₀ F.st1O := by
        rw [← VG.Proof.Hmac.Stream.PPC64LE.add_off]; rfl
      rw [hi (K0 hF s₀) hK h.st.1 (by rw [e1]; exact h.st.2), hu, ht, h5, lo_pred _ hp.c0]

end

end VG.Proof.Pbkdf2.Whole.PPC64LE
