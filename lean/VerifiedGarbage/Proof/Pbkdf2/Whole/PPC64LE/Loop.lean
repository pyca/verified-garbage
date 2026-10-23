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

/-! ## Copying `T` out -/

/-- The sign bit of `a - b`, for `a, b < 2⁶³`: whether `a < b`. -/
theorem sub_sign {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    ((BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 != 0) = decide (a < b) := by
  have e : ((BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63).toNat = if a < b then 1 else 0 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    split <;> omega
  by_cases hab : a < b
  · simp only [hab, ↓reduceIte] at e
    have : (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 ≠ 0 := fun h0 => by rw [h0] at e; simp at e
    simp only [bne_iff_ne, ne_eq, this, not_false_eq_true, hab, decide_true]
  · simp only [hab, ↓reduceIte] at e
    have : (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = 0 := BitVec.eq_of_toNat_eq (by rw [e]; rfl)
    rw [this]
    simp [hab]

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F hF.X s₀)
include hp

theorem ol_lt : ol s₀ < 2 ^ 38 := by
  have := hp.olD; have := (sizes hF).D; omega

omit hp in
/-- Before block `k + 1`, some output is left. -/
theorem dn_lt (hD : 0 < F.H.D) {k : Nat} (hk : k < nbk s₀ (F := F)) :
    dn s₀ (F := F) k = k * F.H.D ∧ k * F.H.D < ol s₀ := by
  have := (Whole.lt_nb hD).1 hk
  exact ⟨by show min _ _ = _; omega, this⟩

/-- The bytes of `T` the output still needs, `min (ol - k D, D)`, in `r9`. -/
theorem outLen_ok {k : Nat} (hk : k < nbk s₀ (F := F)) {s : State} (h : Inv hF s₀ k s) :
    WP isa F.outLen s fun t => Inv hF s₀ k t ∧ t.mem = s.mem ∧
      t.gpr .r9 = BitVec.ofNat 64 (min (ol s₀ - k * F.H.D) F.H.D) := by
  have hD := (sizes hF).D
  have hol := ol_lt hp
  obtain ⟨hdn, hkD⟩ := dn_lt hD.1 hk
  unfold Fns.outLen
  refine WP.seq (wp_subi (by omega) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ => wp_mov fun s₃ u₃ =>
    WP.block_nil ?_)
  have i₃ : Inv hF s₀ k s₃ := h.keep hp (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₃.sp, u₂.sp, u₁.sp]) (fun r hr => by
      rw [u₃.other r (by revert r; decide), u₂.other r (by revert r; decide), u₁.other r (by revert r; decide)])
    (rs := []) (by rw [u₃.mem, u₂.mem, u₁.mem]; exact Frame.refl _ _) (by simp)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have e24 : s.gpr .r24 = BitVec.ofNat 64 (ol s₀ - k * F.H.D) := by rw [h.r24, hdn]
  have e9 : s₃.gpr .r9 = BitVec.ofNat 64 (ol s₀ - k * F.H.D) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), e24]
  have e12 : s₃.gpr .r12 = (BitVec.ofNat 64 (ol s₀ - k * F.H.D) - BitVec.ofNat 64 F.H.D) >>> 63 := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, e24]
  refine WP.ite (decide (ol s₀ - k * F.H.D < F.H.D)) (by
      show VG.PPC64LE.eval (.nonzero .d .r12) s₃ = _
      rw [VG.Proof.MdStream.PPC64LE.eval_nonzero, e12, sub_sign (by omega) (by omega)])
    (fun hT => WP.block_nil ⟨i₃, m₃, ?_⟩) fun hE => wp_li (by omega) fun s₄ u₄ => WP.block_nil
      ⟨i₃.keep hp u₄.rd u₄.wr u₄.sp (fun r hr => u₄.other r (by revert r; decide)) (rs := [])
        (by rw [u₄.mem]; exact Frame.refl _ _) (by simp), by rw [u₄.mem, m₃], ?_⟩
  · rw [e9, Nat.min_eq_left (Nat.le_of_lt (of_decide_eq_true hT))]
  · have := of_decide_eq_false hE
    rw [u₄.gpr, Nat.min_eq_right (by omega)]

end

/-- The output loop after `j` of its `n` bytes, copying from `A` to `B`. -/
structure CI (s : State) (A B : Addr) (n j : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r11 → r ≠ .r12 → t.gpr r = s.gpr r
  r8 : t.gpr .r8 = BitVec.ofNat 64 j
  r9 : t.gpr .r9 = BitVec.ofNat 64 (n - j)
  mem : t.mem = writeBytes s.mem B (bytesAt s.mem A j)

/-- The loop copying `n` bytes from `scratch + tO` to `r23`. -/
theorem copyLoop_ok {s : State} {n : Nat} {A B : Addr} {tO : Nat} (hn : 0 < n) (hn' : n < 2 ^ 32)
    (ho : tO < 2 ^ 15) (hA : s.gpr .r21 + BitVec.ofNat 64 tO = A) (hB : s.gpr .r23 = B)
    (hin : ∀ j < n, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 j) 1)
    (hout : ∀ j < n, InRegions s.wr (B + BitVec.ofNat 64 j) 1)
    (hd : Region.Disjoint ⟨A, n⟩ ⟨B, n⟩) {t : State} (h : CI s A B n 0 t) :
    WP isa (.loop (.block [.add .r11 .r21 .r8, .lbz .r12 .r11 tO, .add .r11 .r23 .r8, .stb .r12 .r11 0,
      .addi .r8 .r8 1, .subi .r9 .r9 1]) (.nonzero .d .r9)) t (CI s A B n n) := by
  refine WP.loop (M := isa) (fun m t => ∃ j, m = n - j ∧ j < n ∧ CI s A B n j t) ?_ n t ⟨0, rfl, hn, h⟩
  rintro m t ⟨j, rfl, hj, c⟩
  refine wp_add fun t₁ u₁ => wp_lbz (a := A + BitVec.ofNat 64 j) ho
    (by rw [u₁.gpr, c.other _ (by decide) (by decide) (by decide) (by decide), c.r8, ← hA]; ac_rfl)
    (by rw [u₁.rd, u₁.wr, c.rd, c.wr]; exact hin j hj) fun t₂ u₂ => wp_add fun t₃ u₃ => ?_
  refine wp_stb (a := B + BitVec.ofNat 64 j) (by decide)
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), c.other _ (by decide) (by decide) (by decide) (by decide), c.r8, hB]; simp)
    (by rw [u₃.wr, u₂.wr, u₁.wr, c.wr]; exact hout j hj) fun t₄ m₄ => wp_addi (by decide) fun t₅ u₅ =>
    wp_subi (by decide) fun t₆ u₆ => WP.block_nil ?_
  have hl : (bytesAt s.mem A j).length = j := bytesAt_length _ _ _
  have byte : (t₃.gpr .r12).setWidth 8 = s.mem (A + BitVec.ofNat 64 j) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, c.mem, VG.Proof.Hmac.Common.writeBytes_other _ _ _
      (by rw [hl]; exact VG.Proof.Hmac.Generic.Common.not_mem_of_disjoint hd hj (Nat.le_of_lt hj) (by omega))]
    ext i hi; simp
  have c' : CI s A B n (j + 1) t₆ := by
    refine ⟨by rw [u₆.rd, u₅.rd, m₄.rd, u₃.rd, u₂.rd, u₁.rd, c.rd], by rw [u₆.wr, u₅.wr, m₄.wr, u₃.wr, u₂.wr,
      u₁.wr, c.wr], by rw [u₆.sp, u₅.sp, m₄.sp, u₃.sp, u₂.sp, u₁.sp, c.sp], fun r a b d e => ?_, ?_, ?_, ?_⟩
    · rw [u₆.other r b, u₅.other r a, m₄.gpr, u₃.other r d, u₂.other r e, u₁.other r d, c.other r a b d e]
    · rw [u₆.other _ (by decide), u₅.gpr, m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), c.r8]
      exact (BitVec.ofNat_add _ _).symm
    · rw [u₆.gpr, u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), c.r9]
      exact (VG.Proof.MdStream.PPC64LE.ofNat_pred (k := n - j) (by omega)).trans (by rw [Nat.sub_sub])
    · rw [u₆.mem, u₅.mem, m₄.mem, byte, u₃.mem, u₂.mem, u₁.mem, c.mem,
        VG.Proof.Hmac.Generic.Common.bytesAt_snoc', ← VG.Proof.Hmac.Generic.Common.writeBytes_snoc _ _ _ _
          (by rw [hl]; omega), hl]
  have hz : isa.eval (.nonzero .d .r9) t₆ = some (decide (n - (j + 1) ≠ 0)) := by
    show VG.PPC64LE.eval (.nonzero .d .r9) t₆ = _
    rw [VG.Proof.MdStream.PPC64LE.eval_nonzero, c'.r9, bne, VG.Proof.MdStream.PPC64LE.ofNat_beq_zero (by omega)]
    simp
  by_cases hl' : n - (j + 1) = 0
  · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl'], ?_⟩
    have e : n = j + 1 := by omega
    rw [e]; rw [e] at c'; exact c'
  · exact .inr ⟨by rw [hz, decide_eq_true hl'], _, by omega, j + 1, rfl, by omega, c'⟩

end VG.Proof.Pbkdf2.Whole.PPC64LE
