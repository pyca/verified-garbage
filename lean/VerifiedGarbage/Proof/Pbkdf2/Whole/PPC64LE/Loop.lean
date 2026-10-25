module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Block
import VerifiedGarbage.Proof.Framework.Offset
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
  have hD4 : 4 * (F.H.D / 4) = F.H.D := by have := hz.D4; omega_arith
  unfold Fns.copyT Fns.iterArgs
  refine copy_ok hp h (a := F.uO) (b := F.tO) (n := F.H.D / 4) (by omega_arith) (by omega_arith)
    (.inr (.inl ⟨_, _, rfl, by omega_arith, by omega_arith⟩)) (by omega_arith) fun t ht g m => ?_
  rw [hD4] at m
  refine wp_addi (by omega_arith) fun s₁ u₁ => wp_addi (by omega_arith) fun s₂ u₂ => wp_subi (by decide) fun s₃ u₃ =>
    wp_addi (by omega_arith) fun s₄ u₄ => wp_addi (by decide) fun s₅ u₅ => WP.block_nil ?_
  have mm : s₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hn : F.H.D < 2 ^ 64 := by omega_arith
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
        exact part_disj hb (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by show F.H.D ≤ 2 ^ 64; omega_arith) hi
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
    BitVec.toNat_sub_of_le (BitVec.le_def.2 (by simp only [BitVec.toNat_setWidth] at h ⊢; simp; omega_arith))]
  rfl

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F hF.X s₀)
include hp

/-- `iterate`'s arguments. -/
theorem b8_args {k : Nat} {s : State} (h : Inv hF s₀ k s)
    (h3 : s.gpr .r3 = sA s₀ F.st0O) (h4 : s.gpr .r4 = sA s₀ F.uO) (h6 : s.gpr .r6 = sA s₀ F.tO)
    (h7 : s.gpr .r7 = sA s₀ 48) : ItArgs F s (sA s₀ F.st0O) (sA s₀ F.uO) (sA s₀ F.tO) (sA s₀ 48) := by
  have hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  have hWc := hz.Wc; have hSS := hz.S; have hD := hz.D; have hN := hz.N; have hB := hz.B
  have hbH := iterBytes F.H
  have hsp := sp_toNat hp
  have bs := below48 hp h.kr (n := 96) (by omega_arith)
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
  refine ⟨h3, h4, h6, h7, by rw [h.kr.sp, hsp]; have := hp.sp; omega_arith,
    pd (.inl (by omega_arith)) (by omega_arith) (by omega_arith), pd (.inr (by rw [hbH]; omega_arith)) (by omega_arith) (by rw [hbH]; omega_arith),
    pd (.inl (by omega_arith)) (by omega_arith) (by omega_arith), pd (.inr (by rw [hbH]; omega_arith)) (by omega_arith) (by rw [hbH]; omega_arith),
    pd (.inr (by rw [hbH]; omega_arith)) (by omega_arith) (by rw [hbH]; omega_arith),
    bp (by omega_arith), bp (by omega_arith), bp (by omega_arith), bp (by rw [hbH]; omega_arith), ?_, ?_⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact cv' F.st0O (2 * F.H.S) (by omega_arith)
    · exact cv' F.uO F.H.D (by omega_arith)
    · exact cv' F.tO F.H.D (by omega_arith)
    · exact cv' 48 _ (by rw [hbH]; omega_arith)
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cv F.tO F.H.D (by omega_arith)
    · exact cv 48 _ (by rw [hbH]; omega_arith)

/-- The other `c - 1` steps, with `iterate`: `T = T_{k+1}`. -/
theorem b8_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) {u : List Byte}
    (hu : bytesAt s.mem (sA s₀ F.uO) F.H.D = u) (ht : bytesAt s.mem (sA s₀ F.tO) F.H.D = u)
    (h3 : s.gpr .r3 = sA s₀ F.st0O) (h4 : s.gpr .r4 = sA s₀ F.uO) (h5 : s.gpr .r5 = s₀.gpr .r7 - 1)
    (h6 : s.gpr .r6 = sA s₀ F.tO) (h7 : s.gpr .r7 = sA s₀ 48) :
    WP isa F.callIt s fun t => Inv hF s₀ k t ∧
      bytesAt t.mem (sA s₀ F.tO) F.H.D = Spec.Pbkdf2.iterate (prf hF s₀) (cc s₀ - 1) u u := by
  have hz := sizes hF; have hl := layout (F := F)
  have hWc := hz.Wc; have hSS := hz.S; have hD := hz.D
  have hbH := iterBytes F.H
  have hK := blockKey_length hF.hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  refine it_call hF (b8_args hp h h3 h4 h6 h7) fun t a hi => ?_
  refine ⟨h.keep hp a.rd a.wr a.sp (fun r hr => a.cs r (by revert r; decide)) a.frame fun r hr => ?_, ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inl ⟨_, _, rfl, by omega_arith, by omega_arith⟩)
    · exact .inl ⟨_, _, rfl, Nat.le_refl _, by rw [hbH]; omega_arith⟩
    · exact .inr (.inr ⟨96, by rw [h.kr.sp], by omega_arith⟩)
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
    split <;> omega_arith
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
  have := hp.olD; have := (sizes hF).D; omega_arith

omit hp in
/-- Before block `k + 1`, some output is left. -/
theorem dn_lt (hD : 0 < F.H.D) {k : Nat} (hk : k < nbk s₀ (F := F)) :
    dn s₀ (F := F) k = k * F.H.D ∧ k * F.H.D < ol s₀ := by
  have := (Whole.lt_nb hD).1 hk
  exact ⟨by show min _ _ = _; omega_arith, this⟩

/-- The bytes of `T` the output still needs, `min (ol - k D, D)`, in `r9`. -/
theorem outLen_ok {k : Nat} (hk : k < nbk s₀ (F := F)) {s : State} (h : Inv hF s₀ k s) :
    WP isa F.outLen s fun t => Inv hF s₀ k t ∧ t.mem = s.mem ∧
      t.gpr .r9 = BitVec.ofNat 64 (min (ol s₀ - k * F.H.D) F.H.D) := by
  have hD := (sizes hF).D
  have hol := ol_lt hp
  obtain ⟨hdn, hkD⟩ := dn_lt hD.1 hk
  unfold Fns.outLen
  refine WP.seq (wp_subi (by omega_arith) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ => wp_mov fun s₃ u₃ =>
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
      rw [VG.Proof.MdStream.PPC64LE.eval_nonzero, e12, sub_sign (by omega_arith) (by omega_arith)])
    (fun hT => WP.block_nil ⟨i₃, m₃, ?_⟩) fun hE => wp_li (by omega_arith) fun s₄ u₄ => WP.block_nil
      ⟨i₃.keep hp u₄.rd u₄.wr u₄.sp (fun r hr => u₄.other r (by revert r; decide)) (rs := [])
        (by rw [u₄.mem]; exact Frame.refl _ _) (by simp), by rw [u₄.mem, m₃], ?_⟩
  · rw [e9, Nat.min_eq_left (Nat.le_of_lt (of_decide_eq_true hT))]
  · have := of_decide_eq_false hE
    rw [u₄.gpr, Nat.min_eq_right (by omega_arith)]

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
      (by rw [hl]; exact VG.Proof.Hmac.Generic.Common.not_mem_of_disjoint hd hj (Nat.le_of_lt hj) (by omega_arith))]
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
      exact (VG.Proof.MdStream.PPC64LE.ofNat_pred (k := n - j) (by omega_arith)).trans (by rw [Nat.sub_sub])
    · rw [u₆.mem, u₅.mem, m₄.mem, byte, u₃.mem, u₂.mem, u₁.mem, c.mem,
        VG.Proof.Hmac.Generic.Common.bytesAt_snoc', ← VG.Proof.Hmac.Generic.Common.writeBytes_snoc _ _ _ _
          (by rw [hl]; omega_arith), hl]
  have hz : isa.eval (.nonzero .d .r9) t₆ = some (decide (n - (j + 1) ≠ 0)) := by
    show VG.PPC64LE.eval (.nonzero .d .r9) t₆ = _
    rw [VG.Proof.MdStream.PPC64LE.eval_nonzero, c'.r9, bne, VG.Proof.MdStream.PPC64LE.ofNat_beq_zero (by omega_arith)]
    simp
  by_cases hl' : n - (j + 1) = 0
  · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl'], ?_⟩
    have e : n = j + 1 := by omega_arith
    rw [e]; rw [e] at c'; exact c'
  · exact .inr ⟨by rw [hz, decide_eq_true hl'], _, by omega_arith, j + 1, rfl, by omega_arith, c'⟩

/-- `lwbrx t, n, m`. -/
theorem wp_lwbrx {is : List Instr} {s : State} {Q : State → Prop} {t n m : Reg} {a : Addr}
    (ha : s.gpr n + s.gpr m = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t ((rev32 (s.mem.readW a 32)).setWidth 64) → WP isa (.block is) s' Q)
    (hn : n ≠ .r0 := by decide) :
    WP isa (.block (.loadRev .w t n m :: is)) s Q :=
  VG.Proof.MdStream.PPC64LE.WP.cons (by rw [exec_loadRev_w hn (by rw [ha]; exact hin), ha]) (k _ (Upd.write _ _ _))

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F hF.X s₀)
include hp

/-- The rest of a block: as much of `T` as the output needs, copied out, the
pointers advanced, and `INT (k + 2)`. -/
theorem tail_ok {k : Nat} (hk : k < nbk s₀ (F := F)) {s : State} (h : Inv hF s₀ k s)
    (ht : bytesAt s.mem (sA s₀ F.tO) F.H.D = Tk hF s₀ (k + 1)) :
    WP isa (.seq F.outLen (.seq F.outLoop (.block F.advance))) s (Inv hF s₀ (k + 1)) := by
  have hz := sizes hF; have hl := layout (F := F); have hb := hz.reach; have hD := hz.D
  have hol := ol_lt hp
  have hno := hp.no
  obtain ⟨hdn, hkD⟩ := dn_lt hD.1 hk
  generalize en : min (ol s₀ - k * F.H.D) F.H.D = n
  have hn : 0 < n := by omega_arith
  have hkn : k * F.H.D + n ≤ ol s₀ := by omega_arith
  have hnD : n ≤ F.H.D := by omega_arith
  have hdn' : dn s₀ (F := F) (k + 1) = k * F.H.D + n := by show min _ _ = _; rw [Nat.succ_mul]; omega_arith
  have osub : Region.Sub ⟨out s₀ + BitVec.ofNat 64 (k * F.H.D), n⟩ (outR s₀) := Offset.sub_base _ hkn
  refine WP.seq (WP.mono (outLen_ok hp hk h) fun s₁ ⟨i₁, m₁, c₁⟩ => ?_)
  rw [en] at c₁
  unfold Fns.outLoop
  refine WP.seq (WP.seq (wp_li (by decide) fun s₂ u₂ => WP.block_nil ?_))
  have i₂ : Inv hF s₀ k s₂ := i₁.keep hp u₂.rd u₂.wr u₂.sp (fun r hr => u₂.other r (by revert r; decide))
    (rs := []) (by rw [u₂.mem]; exact Frame.refl _ _) (by simp)
  have eA : s₂.gpr .r21 + BitVec.ofNat 64 F.tO = sA s₀ F.tO := by rw [i₂.kr.r21]
  have eB : s₂.gpr .r23 = out s₀ + BitVec.ofNat 64 (k * F.H.D) := by rw [i₂.r23, hdn]
  have tsub : Region.Sub ⟨sA s₀ F.tO, n⟩ (scR F s₀) := part_sub (by omega_arith)
  refine WP.mono (copyLoop_ok (s := s₂) (n := n) hn (by omega_arith) (by omega_arith) eA eB
    (fun j hj => by rw [← VG.Proof.Hmac.Stream.PPC64LE.add_off]; exact in_sc' hp hb i₂.kr.wr (by omega_arith))
    (fun j hj => ⟨outR s₀, out_wr hp i₂.kr.wr, by
      rw [← VG.Proof.Hmac.Stream.PPC64LE.add_off]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    ((hp.o_s.sub_left osub).sub_right tsub).symm
    ⟨rfl, rfl, rfl, fun _ _ _ _ _ => rfl, by rw [u₂.gpr], by rw [u₂.other _ (by decide), c₁, Nat.sub_zero],
      by rw [bytesAt, List.range_zero, List.map_nil, VG.WriteBytes.writeBytes_nil]⟩) fun s₃ c₃ => ?_
  unfold Fns.advance
  refine wp_add fun s₄ u₄ => wp_sub fun s₅ u₅ => wp_li (by omega_arith) fun s₆ u₆ => ?_
  refine wp_lwbrx (a := sA s₀ F.intO) (by
      upd_simp [u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, c₃.other]
      rw [i₂.kr.r21])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, c₃.rd, c₃.wr]; exact in_sc' hp hb i₂.kr.wr (by omega_arith))
    fun s₇ u₇ => wp_addi (by decide) fun s₈ u₈ => ?_
  refine wp_stwbrx (a := sA s₀ F.intO) (by
      upd_simp [u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other,
        c₃.other]
      rw [i₂.kr.r21])
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, c₃.wr]; exact in_sc hp hb i₂.kr.wr (by omega_arith))
    fun s₉ m₉ => WP.block_nil ?_
  -- Memory.
  have fr₃ : Frame [⟨out s₀ + BitVec.ofNat 64 (k * F.H.D), n⟩] s₂.mem s₃.mem := by
    rw [c₃.mem]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have m₈ : s₈.mem = s₃.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have fr₉ : Frame [sR s₀ F.intO 4] s₃.mem s₉.mem := by
    rw [m₉.mem, m₈]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have dI : (sR s₀ F.intO 4).Disjoint ⟨out s₀ + BitVec.ofNat 64 (k * F.H.D), n⟩ :=
    ((hp.o_s.sub_left osub).sub_right (part_sub (by omega_arith))).symm
  have r₃ : s₃.mem.readW (sA s₀ F.intO) 32 = rev32 (BitVec.ofNat 32 (k + 1)) := by
    rw [← i₂.intW]
    exact fr₃.readW (r := sR s₀ F.intO 4) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dI) (by decide)
  have e8 : s₈.gpr .r12 = (BitVec.ofNat 32 (k + 1)).setWidth 64 + 1 := by
    rw [u₈.gpr, u₇.gpr, u₆.mem, u₅.mem, u₄.mem, r₃, show rev32 = byteRev32 from rfl, Whole.byteRev32_byteRev32]
    rfl
  have eW : (s₈.gpr .r12).setWidth 32 = BitVec.ofNat 32 (k + 1 + 1) := by
    rw [e8, lo32_add, lo32_ext, show (1 : BitVec 64).setWidth 32 = BitVec.ofNat 32 1 from rfl,
      ← BitVec.ofNat_add]
  have hg : Gk hF s₀ (k + 1) = Gk hF s₀ k ++ Tk hF s₀ (k + 1) := Whole.G_succ _ _ _ _
  have tl : (Tk hF s₀ (k + 1)).length = F.H.D := by rw [← ht, bytesAt_length]
  have rs : ∀ r ∈ [(⟨out s₀ + BitVec.ofNat 64 (k * F.H.D), n⟩ : Region), sR s₀ F.intO 4],
      Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 0, 48⟩ r ∧ ∃ r' ∈ wrs F hF.X s₀, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨(hp.o_s.sub_left osub).symm.sub_left (part_sub (o := 0) (n := 48) (by omega_arith)), outR s₀, by simp, osub⟩
    · exact ⟨part_disj hb (.inl (by omega_arith)) (by omega_arith) (by omega_arith), scR F s₀, by simp, part_sub (by omega_arith)⟩
  have fr : Frame [(⟨out s₀ + BitVec.ofNat 64 (k * F.H.D), n⟩ : Region), sR s₀ F.intO 4] s₂.mem s₉.mem :=
    (fr₃.mono (by simp)).trans (fr₉.mono (by simp))
  have g9 : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r11 → r ≠ .r12 → r ≠ .r23 → r ≠ .r24 → s₉.gpr r = s₂.gpr r := by
    intro r a b c d e f
    rw [m₉.gpr, u₈.other r d, u₇.other r d, u₆.other r c, u₅.other r f, u₄.other r e, c₃.other r a b c d]
  refine ⟨i₂.kr.keep (by rw [m₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, c₃.rd])
      (by rw [m₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, c₃.wr])
      (by rw [m₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, c₃.sp])
      (fun r hr => g9 r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide) (by revert r; decide)) fr (fun r hr => (rs r hr).1) (fun r hr => (rs r hr).2),
    i₂.st.keep fr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ((hp.o_s.sub_left osub).sub_right (part_sub (by omega_arith))).symm
      · exact part_disj hb (.inl (by omega_arith)) (by omega_arith) (by omega_arith)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [m₉.gpr]
    upd_simp [u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other,
      c₃.other]
    rw [c₃.r8, eB, hdn', BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [m₉.gpr]
    upd_simp [u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other,
      c₃.other]
    rw [c₃.r8, i₂.r24, hdn, hdn', VG.Proof.MdStream.PPC64LE.sub_ofNat (by omega_arith), Nat.sub_sub]
  · rw [m₉.mem, Mem.readW_writeW_self32, eW]
  · rw [hg, List.length_append, i₂.glen, tl, Nat.succ_mul]
  · have osub' : Region.Sub ⟨out s₀, k * F.H.D + n⟩ (outR s₀) := Region.sub_prefix hkn
    rw [hdn', VG.Proof.Hmac.Generic.Common.bytes_keep fr₉ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.o_s.sub_left osub').sub_right (part_sub (by omega_arith))) (by omega_arith), c₃.mem]
    have bw := VG.Proof.Sha256.Stream.bytesAt_writeBytes s₂.mem (out s₀) (k * F.H.D)
      (bytesAt s₂.mem (sA s₀ F.tO) n) (by rw [bytesAt_length]; omega_arith)
    rw [bytesAt_length] at bw
    have ob := i₂.outB
    rw [hdn] at ob
    rw [bw, ob, VG.Proof.Hmac.Generic.Common.bytesAt_take _ _ hnD, u₂.mem, m₁, ht, hg, List.take_append,
      i₂.glen, Nat.add_sub_cancel_left, List.take_of_length_le (l := Gk hF s₀ k) (i := k * F.H.D) (by rw [i₂.glen]),
      List.take_of_length_le (l := Gk hF s₀ k) (i := k * F.H.D + n) (by rw [i₂.glen]; omega_arith)]

end

/-! ## The loop -/

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F hF.X s₀)
include hp

/-- A block of the output. -/
theorem block_ok {k : Nat} (hk : k < nbk s₀ (F := F)) {s : State} (h : Inv hF s₀ k s) :
    WP isa F.block s (Inv hF s₀ (k + 1)) := by
  unfold Fns.block
  refine WP.seq (WP.mono (b1_ok hp h) fun s₁ ⟨i₁, r₁, a3, a4, a5, a6, a7⟩ => ?_)
  refine WP.seq (WP.mono (b2_ok hp i₁ r₁ a3 a4 a5 a6 a7) fun s₂ ⟨i₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (b3_ok hp i₂) fun s₃ ⟨i₃, m₃, c3, c4, c5, c6, c7⟩ => ?_)
  refine WP.seq (WP.mono (b4_ok hp i₃ (by rw [m₃]; exact r₂) c3 c4 c5 c6 c7) fun s₄ ⟨i₄, r₄⟩ => ?_)
  refine WP.seq (WP.mono (b5_ok hp i₄) fun s₅ ⟨i₅, m₅, d3, d4, d5, d6, d7⟩ => ?_)
  refine WP.seq (WP.mono (b6_ok hp i₅ (by rw [m₅]; exact r₄) d3 d4 d5 d6 d7) fun s₆ ⟨i₆, u₆⟩ => ?_)
  refine WP.seq (WP.mono (b7_ok hp i₆) fun s₇ ⟨i₇, hu, ht, e3, e4, e5, e6, e7⟩ => ?_)
  refine WP.seq (WP.mono (b8_ok hp i₇ (hu.trans u₆) (ht.trans u₆) e3 e4 e5 e6 e7) fun s₈ ⟨i₈, t₈⟩ => ?_)
  exact tail_ok hp hk i₈ (by rw [t₈]; rfl)

/-- The bytes of output left, while some are. -/
theorem left_ne {k : Nat} (hk : k ≤ nbk s₀ (F := F)) :
    (BitVec.ofNat 64 (ol s₀ - dn s₀ (F := F) k) != 0) = decide (k < nbk s₀ (F := F)) := by
  have hD := (sizes hF).D
  have hol := ol_lt hp
  rw [bne, VG.Proof.MdStream.PPC64LE.ofNat_beq_zero (by omega_arith)]
  have e := Whole.lt_nb (D := F.H.D) (ol := ol s₀) hD.1 (k := k)
  by_cases h : k < nbk s₀ (F := F)
  · have h1 : k * F.H.D < ol s₀ := e.1 h
    have h2 : dn s₀ (F := F) k = k * F.H.D := Nat.min_eq_left (Nat.le_of_lt h1)
    rw [h2]; simp only [h, decide_true]
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    omega_arith
  · have hk' : k = nbk s₀ (F := F) := by omega_arith
    have dn' : dn s₀ (F := F) k = ol s₀ := by rw [hk']; exact Whole.done_nb hD.1
    rw [dn', Nat.sub_self]; simp [h]

/-- The blocks of the output, from `Inv 0`: `Inv` after all of them. -/
theorem loop_ok {s : State} (h : Inv hF s₀ 0 s) :
    WP isa (.ite (.zero .d .r24) (.block []) (.loop F.block (.nonzero .d .r24))) s (Inv hF s₀ (nbk s₀ (F := F))) := by
  have hD := (sizes hF).D
  have hol := ol_lt hp
  have e24 : s.gpr .r24 = BitVec.ofNat 64 (ol s₀) := by
    rw [h.r24]; congr 1; show _ - min (0 * F.H.D) _ = _; simp
  refine WP.ite (decide (ol s₀ = 0)) (by
      show VG.PPC64LE.eval (.zero .d .r24) s = _
      rw [VG.Proof.MdStream.PPC64LE.eval_zero, e24, VG.Proof.MdStream.PPC64LE.ofNat_beq_zero (by omega_arith)])
    (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : nbk s₀ (F := F) = 0 := (Whole.nb_zero hD.1).2 (of_decide_eq_true h0)
    rw [this]; exact h
  · have hn : 0 < nbk s₀ (F := F) := by
      have : nbk s₀ (F := F) ≠ 0 := fun h' => of_decide_eq_false h0 ((Whole.nb_zero hD.1).1 h')
      omega_arith
    refine WP.loop (M := isa) (fun m t => ∃ k, m = nbk s₀ (F := F) - k ∧ k < nbk s₀ (F := F) ∧ Inv hF s₀ k t) ?_
      _ s ⟨0, rfl, hn, h⟩
    rintro m t ⟨k, rfl, hk, i⟩
    refine WP.mono (block_ok hp hk i) fun t' i' => ?_
    have hz : isa.eval (.nonzero .d .r24) t' = some (decide (k + 1 < nbk s₀ (F := F))) := by
      show VG.PPC64LE.eval (.nonzero .d .r24) t' = _
      rw [VG.Proof.MdStream.PPC64LE.eval_nonzero, i'.r24, left_ne hp (by omega_arith)]
    by_cases hl : k + 1 < nbk s₀ (F := F)
    · exact .inr ⟨by rw [hz, decide_eq_true hl], _, by omega_arith, k + 1, rfl, hl, i'⟩
    · refine .inl ⟨by rw [hz, decide_eq_false hl], ?_⟩
      have e : k + 1 = nbk s₀ (F := F) := by omega_arith
      rw [← e]; exact i'

end

end VG.Proof.Pbkdf2.Whole.PPC64LE
