module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# PBKDF2 over any streaming hash function on RISC-V, the whole derivation: the rest of a block, and the loop

`T` starts as `U₁` and `iterate` runs the other `c - 1` steps (`b8_ok`):
`T = T_{k+1}`. As much of it as the output still needs is copied to `out`
(`outLen_ok`, `copyLoop_ok`), and the pointers and `i` advance (`tail_ok`):
`Inv` holds after `k + 1` blocks (`block_ok`), and after all of them
(`loop_ok`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_mv wp_addi wp_subi wp_li wp_add wp_sub wp_srl wp_lbu wp_sb eval_zero
  eval_nonzero ofNat_beq_zero)
open VG.Impl.Pbkdf2.Whole.RISCV64 (Fns)
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.WriteBytes (writeBytes writeBytes_frame)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

variable {F : Fns}

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀)
include hp

/-- `T ← U₁`, and `iterate`'s arguments. -/
theorem b7_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block F.iterArgs) s fun t => Inv hF s₀ k t ∧
      bytesAt t.mem (sA s₀ F.uO) F.H.D = bytesAt s.mem (sA s₀ F.uO) F.H.D ∧
      bytesAt t.mem (sA s₀ F.tO) F.H.D = bytesAt s.mem (sA s₀ F.uO) F.H.D ∧
      t.gpr .a0 = sA s₀ Fns.st0O ∧ t.gpr .a1 = sA s₀ F.uO ∧ t.gpr .a2 = s₀.gpr .a4 - BitVec.ofNat 64 1 ∧
      t.gpr .a3 = sA s₀ F.tO ∧ t.gpr .a4 = sA s₀ F.frB := by
  have hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB; have hD := hz.D
  unfold Fns.iterArgs
  refine copy_ok hp h (a := F.uO) (b := F.tO) (n := F.H.D) (by omega) (by omega) (by omega) (by omega)
    fun t ht g m => ?_
  refine wp_addi (by simp only [Fns.st0O]; omega) fun s₁ u₁ => wp_addi (by omega) fun s₂ u₂ =>
    wp_subi (imm := 1) (by decide) fun s₃ u₃ => wp_addi (by omega) fun s₄ u₄ => wp_addi hfr fun s₅ u₅ =>
    WP.block_nil ?_
  have mm : s₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hn : F.H.D < 2 ^ 64 := by omega
  refine ⟨ht.keep hp (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (fun r hr => by
      rw [u₅.other r (by revert r; decide), u₄.other r (by revert r; decide), u₃.other r (by revert r; decide),
        u₂.other r (by revert r; decide), u₁.other r (by revert r; decide)]) (rs := [])
    (by rw [mm]; exact Frame.refl _ _) (by simp), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have fr : Frame [sR s₀ F.tO F.H.D] s.mem t.mem := by
      rw [m]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
    rw [mm]
    exact VG.Proof.Sha256.Stream.bytesAt_congr fun _ hi => fr.bytes (R := sR s₀ F.uO F.H.D)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact part_disj (.inl (by omega)) (by omega) (by omega)) (by show F.H.D ≤ 2 ^ 64; omega) hi
  · rw [mm, m]
    have := VG.Proof.Hmac.Common.bytesAt_writeBytes_self s.mem (sA s₀ F.tO) (bytesAt s.mem (sA s₀ F.uO) F.H.D)
      (by rw [bytesAt_length]; exact hn)
    rwa [bytesAt_length] at this
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.s1]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.s1]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.s3]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.s1]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.s1]

end

/-- The low word of `c - 1`. -/
theorem lo_pred (x : BitVec 64) (h : 0 < (x.setWidth 32).toNat) :
    ((x - BitVec.ofNat 64 1).setWidth 32).toNat = (x.setWidth 32).toNat - 1 := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat] at h ⊢
  have := x.isLt
  omega

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀)
include hp

/-- `iterate`'s arguments. -/
theorem b8_args {k : Nat} {s : State} (h : Inv hF s₀ k s)
    (h0 : s.gpr .a0 = sA s₀ Fns.st0O) (h1 : s.gpr .a1 = sA s₀ F.uO) (h3 : s.gpr .a3 = sA s₀ F.tO)
    (h4 : s.gpr .a4 = sA s₀ F.frB) : ItArgs F s (sA s₀ Fns.st0O) (sA s₀ F.uO) (sA s₀ F.tO) (sA s₀ F.frB) := by
  have hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB; have hib := hz.itB
  have pd : ∀ {a m b n : Nat}, a + m ≤ b ∨ b + n ≤ a → a + m ≤ 4096 → b + n ≤ 4096 →
      Region.Disjoint (sR s₀ a m) (sR s₀ b n) := fun h₁ h₂ h₃ => part_disj h₁ h₂ h₃
  have cv : ∀ o n, o + n ≤ F.frB → ∃ r' ∈ s.wr, ∃ off,
      (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len :=
    fun o n h' => ⟨frR F s₀, fr_wr hp h.kr.wr, o, rfl, h'⟩
  have cv' : ∀ o n, o + n ≤ F.frB → ∃ r' ∈ s.rd ++ s.wr, ∃ off,
      (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len := fun o n h' => by
    obtain ⟨r', hr', off, e, l⟩ := cv o n h'; exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
  have ci : ∃ r' ∈ s.wr, ∃ off, (sR s₀ F.frB F.itW).base = r'.base + BitVec.ofNat 64 off ∧ off + F.itW ≤ r'.len :=
    ⟨itR F s₀, it_wr hp h.kr.wr, 0, by simp, by show 0 + F.itW ≤ F.itB; omega⟩
  refine ⟨h0, h1, h3, h4, pd (.inl (by simp only [Fns.st0O]; omega)) (by omega) (by omega),
    pd (.inl (by simp only [Fns.st0O]; omega)) (by omega) (by omega), pd (.inl (by omega)) (by omega) (by omega),
    pd (.inl (by omega)) (by omega) (by omega), pd (.inl (by omega)) (by omega) (by omega), ?_, ?_⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact cv' Fns.st0O (2 * F.H.S) (by simp only [Fns.st0O]; omega)
    · exact cv' F.uO F.H.D (by omega)
    · exact cv' F.tO F.H.D (by omega)
    · obtain ⟨r', hr', off, e, l⟩ := ci; exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cv F.tO F.H.D (by omega)
    · exact ci

/-- The other `c - 1` steps, with `iterate`: `T = T_{k+1}`. -/
theorem b8_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) {u : List Byte}
    (hu : bytesAt s.mem (sA s₀ F.uO) F.H.D = u) (ht : bytesAt s.mem (sA s₀ F.tO) F.H.D = u)
    (h0 : s.gpr .a0 = sA s₀ Fns.st0O) (h1 : s.gpr .a1 = sA s₀ F.uO) (h2 : s.gpr .a2 = s₀.gpr .a4 - BitVec.ofNat 64 1)
    (h3 : s.gpr .a3 = sA s₀ F.tO) (h4 : s.gpr .a4 = sA s₀ F.frB) :
    WP isa F.callIt s fun t => Inv hF s₀ k t ∧
      bytesAt t.mem (sA s₀ F.tO) F.H.D = Spec.Pbkdf2.iterate (prf hF s₀) (cc s₀ - 1) u u := by
  have hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB
  have hK := blockKey_length hF.hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  refine it_call hF (b8_args hp h h0 h1 h3 h4) fun t a hi => ?_
  refine ⟨h.keep hp a.rd a.wr a.sp (fun r hr => a.cs r (by revert r; decide)) a.frame fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl ⟨_, _, rfl, by omega, by omega⟩
    · exact .inr (.inl (Region.sub_prefix (by omega)))
  · have e1 : sA s₀ Fns.st0O + BitVec.ofNat 64 F.H.S = sA s₀ F.st1O := by rw [sA_add]; rfl
    rw [hi (K0 hF s₀) hK h.st.1 (by rw [e1]; exact h.st.2), hu, ht, h2, lo_pred _ hp.c0]

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
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀)
include hp

include hF in
theorem ol_lt : ol s₀ < 2 ^ 38 := by
  have := hp.olD; have := (sizes hF).D; omega

omit hp in
/-- Before block `k + 1`, some output is left. -/
theorem dn_lt (hD : 0 < F.H.D) {k : Nat} (hk : k < nbk s₀ (F := F)) :
    dn s₀ (F := F) k = k * F.H.D ∧ k * F.H.D < ol s₀ := by
  have := (Whole.lt_nb hD).1 hk
  exact ⟨by show min _ _ = _; omega, this⟩

/-- The bytes of `T` the output still needs, `min (ol - k D, D)`, in `t2`. -/
theorem outLen_ok {k : Nat} (hk : k < nbk s₀ (F := F)) {s : State} (h : Inv hF s₀ k s) :
    WP isa F.outLen s fun t => Inv hF s₀ k t ∧ t.mem = s.mem ∧
      t.gpr .t2 = BitVec.ofNat 64 (min (ol s₀ - k * F.H.D) F.H.D) := by
  have hD := (sizes hF).D
  have hol := ol_lt (hF := hF) hp
  obtain ⟨hdn, hkD⟩ := dn_lt hD.1 hk
  unfold Fns.outLen
  refine WP.seq (wp_subi (imm := F.H.D) (by omega) fun s₁ u₁ => wp_srl (by decide) fun s₂ u₂ => wp_mv fun s₃ u₃ =>
    WP.block_nil ?_)
  have i₃ : Inv hF s₀ k s₃ := h.keep hp (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₃.sp, u₂.sp, u₁.sp]) (fun r hr => by
      rw [u₃.other r (by revert r; decide), u₂.other r (by revert r; decide), u₁.other r (by revert r; decide)])
    (rs := []) (by rw [u₃.mem, u₂.mem, u₁.mem]; exact Frame.refl _ _) (by simp)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have e5 : s.gpr .s5 = BitVec.ofNat 64 (ol s₀ - k * F.H.D) := by rw [h.s5, hdn]
  have e2 : s₃.gpr .t2 = BitVec.ofNat 64 (ol s₀ - k * F.H.D) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), e5]
  have e1 : s₃.gpr .t1 = (BitVec.ofNat 64 (ol s₀ - k * F.H.D) - BitVec.ofNat 64 F.H.D) >>> 63 := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, e5]
  refine WP.ite (decide (ol s₀ - k * F.H.D < F.H.D)) (by
      rw [eval_nonzero, e1, sub_sign (by omega) (by omega)])
    (fun hT => WP.block_nil ⟨i₃, m₃, ?_⟩) fun hE => wp_li (by omega) fun s₄ u₄ => WP.block_nil
      ⟨i₃.keep hp u₄.rd u₄.wr u₄.sp (fun r hr => u₄.other r (by revert r; decide)) (rs := [])
        (by rw [u₄.mem]; exact Frame.refl _ _) (by simp), by rw [u₄.mem, m₃], ?_⟩
  · rw [e2, Nat.min_eq_left (Nat.le_of_lt (of_decide_eq_true hT))]
  · have := of_decide_eq_false hE
    rw [u₄.gpr, Nat.min_eq_right (by omega)]

end

/-- The output loop after `j` of its `n` bytes, copying from `A` to `B`. -/
structure CI (s : State) (A B : Addr) (n j : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → t.gpr r = s.gpr r
  t3 : t.gpr .t3 = BitVec.ofNat 64 j
  t2 : t.gpr .t2 = BitVec.ofNat 64 (n - j)
  mem : t.mem = writeBytes s.mem B (bytesAt s.mem A j)

/-- The loop copying `n` bytes from `s1 + tO` to `s4`. -/
theorem copyLoop_ok {s : State} {n : Nat} {A B : Addr} {tO : Nat} (hn : 0 < n) (hn' : n < 2 ^ 32)
    (ho : tO < 2048) (hA : s.gpr .s1 + BitVec.ofNat 64 tO = A) (hB : s.gpr .s4 = B)
    (hin : ∀ j < n, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 j) 1)
    (hout : ∀ j < n, InRegions s.wr (B + BitVec.ofNat 64 j) 1)
    (hd : Region.Disjoint ⟨A, n⟩ ⟨B, n⟩) {t : State} (h : CI s A B n 0 t) :
    WP isa (.loop (.block [.add .t4 .s1 .t3, .load .b .t1 .t4 tO, .add .t4 .s4 .t3, .store .b .t1 .t4 0,
      .addi .t3 .t3 1, .addi .t2 .t2 (-1)]) (.nonzero .t2)) t (CI s A B n n) := by
  refine WP.loop (M := isa) (fun m t => ∃ j, m = n - j ∧ j < n ∧ CI s A B n j t) ?_ n t ⟨0, rfl, hn, h⟩
  rintro m t ⟨j, rfl, hj, c⟩
  refine wp_add fun t₁ u₁ => wp_lbu (a := A + BitVec.ofNat 64 j) ho
    (by rw [u₁.gpr, c.other _ (by decide) (by decide) (by decide) (by decide), c.t3, ← hA]; ac_rfl)
    (by rw [u₁.rd, u₁.wr, c.rd, c.wr]; exact hin j hj) fun t₂ u₂ => wp_add fun t₃ u₃ => ?_
  refine wp_sb (a := B + BitVec.ofNat 64 j) (by decide)
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), c.other _ (by decide) (by decide) (by decide) (by decide), c.t3, hB]; simp)
    (by rw [u₃.wr, u₂.wr, u₁.wr, c.wr]; exact hout j hj) fun t₄ m₄ => wp_addi (by decide) fun t₅ u₅ =>
    wp_subi (imm := 1) (by decide) fun t₆ u₆ => WP.block_nil ?_
  have hl : (bytesAt s.mem A j).length = j := bytesAt_length _ _ _
  have byte : (t₃.gpr .t1).setWidth 8 = s.mem (A + BitVec.ofNat 64 j) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, c.mem, VG.Proof.Hmac.Common.writeBytes_other _ _ _
      (by rw [hl]; exact VG.Proof.Hmac.Generic.Common.not_mem_of_disjoint hd hj (Nat.le_of_lt hj) (by omega))]
    ext i hi; simp
  have c' : CI s A B n (j + 1) t₆ := by
    refine ⟨by rw [u₆.rd, u₅.rd, m₄.rd, u₃.rd, u₂.rd, u₁.rd, c.rd], by rw [u₆.wr, u₅.wr, m₄.wr, u₃.wr, u₂.wr,
      u₁.wr, c.wr], by rw [u₆.sp, u₅.sp, m₄.sp, u₃.sp, u₂.sp, u₁.sp, c.sp], fun r a b d e => ?_, ?_, ?_, ?_⟩
    · rw [u₆.other r b, u₅.other r d, m₄.gpr, u₃.other r e, u₂.other r a, u₁.other r e, c.other r a b d e]
    · rw [u₆.other _ (by decide), u₅.gpr, m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), c.t3]
      exact (BitVec.ofNat_add _ _).symm
    · rw [u₆.gpr, u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), c.t2, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
    · rw [u₆.mem, u₅.mem, m₄.mem, byte, u₃.mem, u₂.mem, u₁.mem, c.mem,
        VG.Proof.Hmac.Generic.Common.bytesAt_snoc', ← VG.Proof.Hmac.Generic.Common.writeBytes_snoc _ _ _ _
          (by rw [hl]; omega), hl]
  have hz : isa.eval (.nonzero .t2) t₆ = some (decide (n - (j + 1) ≠ 0)) := by
    rw [eval_nonzero, c'.t2, bne, ofNat_beq_zero (by omega)]
    simp
  by_cases hl' : n - (j + 1) = 0
  · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl'], ?_⟩
    have e : n = j + 1 := by omega
    rw [e]; rw [e] at c'; exact c'
  · exact .inr ⟨by rw [hz, decide_eq_true hl'], _, by omega, j + 1, rfl, by omega, c'⟩

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀)
include hp

/-- The rest of a block: as much of `T` as the output needs, copied out, and
the pointers and `i` advanced. -/
theorem tail_ok {k : Nat} (hk : k < nbk s₀ (F := F)) {s : State} (h : Inv hF s₀ k s)
    (ht : bytesAt s.mem (sA s₀ F.tO) F.H.D = Tk hF s₀ (k + 1)) :
    WP isa (.seq F.outLen (.seq F.outLoop (.block Fns.advance))) s (Inv hF s₀ (k + 1)) := by
  have hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB; have hD := hz.D
  have hol := ol_lt (hF := hF) hp
  have hno := hp.no
  obtain ⟨hdn, hkD⟩ := dn_lt hD.1 hk
  generalize en : min (ol s₀ - k * F.H.D) F.H.D = n
  have hn : 0 < n := by omega
  have hkn : k * F.H.D + n ≤ ol s₀ := by omega
  have hnD : n ≤ F.H.D := by omega
  have hdn' : dn s₀ (F := F) (k + 1) = k * F.H.D + n := by show min _ _ = _; rw [Nat.succ_mul]; omega
  have osub : Region.Sub ⟨out s₀ + BitVec.ofNat 64 (k * F.H.D), n⟩ (outR s₀) := Offset.sub_base _ hkn
  refine WP.seq (WP.mono (outLen_ok hp hk h) fun s₁ ⟨i₁, m₁, c₁⟩ => ?_)
  rw [en] at c₁
  unfold Fns.outLoop
  refine WP.seq (WP.seq (wp_li (by decide) fun s₂ u₂ => WP.block_nil ?_))
  have i₂ : Inv hF s₀ k s₂ := i₁.keep hp u₂.rd u₂.wr u₂.sp (fun r hr => u₂.other r (by revert r; decide))
    (rs := []) (by rw [u₂.mem]; exact Frame.refl _ _) (by simp)
  have eA : s₂.gpr .s1 + BitVec.ofNat 64 F.tO = sA s₀ F.tO := by rw [i₂.kr.s1]
  have eB : s₂.gpr .s4 = out s₀ + BitVec.ofNat 64 (k * F.H.D) := by rw [i₂.s4, hdn]
  have tsub : Region.Sub ⟨sA s₀ F.tO, n⟩ (frR F s₀) := part_sub (by omega)
  refine WP.mono (copyLoop_ok (s := s₂) (n := n) hn (by omega) (by omega) eA eB
    (fun j hj => by rw [sA_add]; exact in_fr' hp i₂.kr.wr (by omega) (by omega))
    (fun j hj => ⟨outR s₀, out_wr hp i₂.kr.wr, by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩)
    ((hp.f_o.sub_right osub).sub_left tsub)
    ⟨rfl, rfl, rfl, fun _ _ _ _ _ => rfl, by rw [u₂.gpr], by rw [u₂.other _ (by decide), c₁, Nat.sub_zero],
      by rw [bytesAt, List.range_zero, List.map_nil, VG.WriteBytes.writeBytes_nil]⟩) fun s₃ c₃ => ?_
  unfold Fns.advance
  refine wp_add fun s₄ u₄ => wp_sub fun s₅ u₅ => wp_addi (by decide) fun s₆ u₆ => WP.block_nil ?_
  -- Memory.
  have fr₃ : Frame [⟨out s₀ + BitVec.ofNat 64 (k * F.H.D), n⟩] s₂.mem s₃.mem := by
    rw [c₃.mem]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have m₆ : s₆.mem = s₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  have hg : Gk hF s₀ (k + 1) = Gk hF s₀ k ++ Tk hF s₀ (k + 1) := Whole.G_succ _ _ _ _
  have tl : (Tk hF s₀ (k + 1)).length = F.H.D := by rw [← ht, bytesAt_length]
  have g6 : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .s4 → r ≠ .s5 → r ≠ .s7 → s₆.gpr r = s₂.gpr r := by
    intro r a b c d e f g
    rw [u₆.other r g, u₅.other r f, u₄.other r e, c₃.other r a b c d]
  refine ⟨i₂.kr.keep (by rw [u₆.rd, u₅.rd, u₄.rd, c₃.rd]) (by rw [u₆.wr, u₅.wr, u₄.wr, c₃.wr])
      (by rw [u₆.sp, u₅.sp, u₄.sp, c₃.sp])
      (fun r hr => g6 r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide) (by revert r; decide) (by revert r; decide)) (by rw [m₆]; exact fr₃)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.f_o.sub_right osub).sub_left (part_sub (o := 0) (n := 64) (by omega)))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨outR s₀, by simp, osub⟩),
    i₂.st.keep (by rw [m₆]; exact fr₃) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.f_o.sub_right osub).sub_left (part_sub (by omega))), ?_, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, c₃.other]
    rw [c₃.t3, eB, hdn', BitVec.add_assoc, ← BitVec.ofNat_add]
  · upd_simp [u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, c₃.other]
    rw [c₃.t3, i₂.s5, hdn, hdn', Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · upd_simp [u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, c₃.other]
    rw [i₂.s7, ← BitVec.ofNat_add]
  · rw [hg, List.length_append, i₂.glen, tl, Nat.succ_mul]
  · rw [hdn', m₆, c₃.mem]
    have bw := VG.Proof.Sha256.Stream.bytesAt_writeBytes s₂.mem (out s₀) (k * F.H.D)
      (bytesAt s₂.mem (sA s₀ F.tO) n) (by rw [bytesAt_length]; omega)
    rw [bytesAt_length] at bw
    have ob := i₂.outB
    rw [hdn] at ob
    rw [bw, ob, VG.Proof.Hmac.Generic.Common.bytesAt_take _ _ hnD, u₂.mem, m₁, ht, hg, List.take_append,
      i₂.glen, Nat.add_sub_cancel_left, List.take_of_length_le (l := Gk hF s₀ k) (i := k * F.H.D) (by rw [i₂.glen]),
      List.take_of_length_le (l := Gk hF s₀ k) (i := k * F.H.D + n) (by rw [i₂.glen]; omega)]

end

/-! ## The loop -/

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀)
include hp

include hF in
theorem nbk_lt : nbk s₀ (F := F) < 2 ^ 32 := by
  have hD := (sizes hF).D
  exact Whole.nb_lt hD.1 hp.olD

/-- A block of the output. -/
theorem block_ok {k : Nat} (hk : k < nbk s₀ (F := F)) {s : State} (h : Inv hF s₀ k s) :
    WP isa F.block s (Inv hF s₀ (k + 1)) := by
  have hk32 : k + 1 < 2 ^ 32 := by have := nbk_lt (hF := hF) hp; omega
  unfold Fns.block
  refine WP.seq (WP.mono (b1_ok hp h) fun s₁ ⟨i₁, r₁, a0, a1, a2, a3⟩ => ?_)
  refine WP.seq (WP.mono (b2_ok hp i₁ r₁ a0 a1 a2 a3) fun s₂ ⟨i₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (b3_ok hp hk32 i₂ r₂) fun s₃ ⟨i₃, r₃, n₃, c0, c1, c2, c3⟩ => ?_)
  refine WP.seq (WP.mono (b4_ok hp i₃ r₃ n₃ c0 c1 c2 c3) fun s₄ ⟨i₄, r₄⟩ => ?_)
  refine WP.seq (WP.mono (b5_ok hp i₄) fun s₅ ⟨i₅, m₅, d0, d1, d2, d3⟩ => ?_)
  refine WP.seq (WP.mono (b6_ok hp i₅ (by rw [m₅]; exact r₄) d0 d1 d2 d3) fun s₆ ⟨i₆, u₆⟩ => ?_)
  refine WP.seq (WP.mono (b7_ok hp i₆) fun s₇ ⟨i₇, hu, ht, e0, e1, e2, e3, e4⟩ => ?_)
  refine WP.seq (WP.mono (b8_ok hp i₇ (hu.trans u₆) (ht.trans u₆) e0 e1 e2 e3 e4) fun s₈ ⟨i₈, t₈⟩ => ?_)
  exact tail_ok hp hk i₈ (by rw [t₈]; rfl)

include hF in
/-- The bytes of output left, while some are. -/
theorem left_ne {k : Nat} (hk : k ≤ nbk s₀ (F := F)) :
    (BitVec.ofNat 64 (ol s₀ - dn s₀ (F := F) k) != 0) = decide (k < nbk s₀ (F := F)) := by
  have hD := (sizes hF).D
  have hol := ol_lt (hF := hF) hp
  rw [bne, ofNat_beq_zero (by omega)]
  have e := Whole.lt_nb (D := F.H.D) (ol := ol s₀) hD.1 (k := k)
  by_cases h : k < nbk s₀ (F := F)
  · have h1 : k * F.H.D < ol s₀ := e.1 h
    have h2 : dn s₀ (F := F) k = k * F.H.D := Nat.min_eq_left (Nat.le_of_lt h1)
    rw [h2]; simp only [h, decide_true]
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    omega
  · have hk' : k = nbk s₀ (F := F) := by omega
    have dn' : dn s₀ (F := F) k = ol s₀ := by rw [hk']; exact Whole.done_nb hD.1
    rw [dn', Nat.sub_self]; simp [h]

/-- The blocks of the output, from `Inv 0`: `Inv` after all of them. -/
theorem loop_ok {s : State} (h : Inv hF s₀ 0 s) :
    WP isa (.ite (.zero .s5) (.block []) (.loop F.block (.nonzero .s5))) s (Inv hF s₀ (nbk s₀ (F := F))) := by
  have hD := (sizes hF).D
  have hol := ol_lt (hF := hF) hp
  have e5 : s.gpr .s5 = BitVec.ofNat 64 (ol s₀) := by
    rw [h.s5]; congr 1; show _ - min (0 * F.H.D) _ = _; simp
  refine WP.ite (decide (ol s₀ = 0)) (by rw [eval_zero, e5, ofNat_beq_zero (by omega)])
    (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : nbk s₀ (F := F) = 0 := (Whole.nb_zero hD.1).2 (of_decide_eq_true h0)
    rw [this]; exact h
  · have hn : 0 < nbk s₀ (F := F) := by
      have : nbk s₀ (F := F) ≠ 0 := fun h' => of_decide_eq_false h0 ((Whole.nb_zero hD.1).1 h')
      omega
    refine WP.loop (M := isa) (fun m t => ∃ k, m = nbk s₀ (F := F) - k ∧ k < nbk s₀ (F := F) ∧ Inv hF s₀ k t) ?_
      _ s ⟨0, rfl, hn, h⟩
    rintro m t ⟨k, rfl, hk, i⟩
    refine WP.mono (block_ok hp hk i) fun t' i' => ?_
    have hz : isa.eval (.nonzero .s5) t' = some (decide (k + 1 < nbk s₀ (F := F))) := by
      rw [eval_nonzero, i'.s5, left_ne (hF := hF) hp (by omega)]
    by_cases hl : k + 1 < nbk s₀ (F := F)
    · exact .inr ⟨by rw [hz, decide_eq_true hl], _, by omega, k + 1, rfl, hl, i'⟩
    · refine .inl ⟨by rw [hz, decide_eq_false hl], ?_⟩
      have e : k + 1 = nbk s₀ (F := F) := by omega
      rw [← e]; exact i'

end

end VG.Proof.Pbkdf2.Whole.RISCV64
