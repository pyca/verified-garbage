import VerifiedGarbage.Proof.AesOcb.AArch64.HashFill

/-!
# AES-OCB on AArch64: a chunk of `HASH` (`hashChunk`)

Untrusted: everything here is checked by Lean. After `j` of the `m` whole
blocks of the associated data `a`, `HInv` holds: the sum and the offset of
`HASH` are `Sum_j` and `Offset_j` (`Proof.Ocb.hsum`, `Proof.Ocb.offAt`),
`x23` points at block `j`, `x25` is `j + 1` and `x26` is `m − j`.
`hashChunk` takes `c = min(8, m − j)` blocks (`chunkHead_ok`): fills the
buffer with each block XORed with its offset (`fill_ok`), enciphers the
buffer, adds it to the sum (`hashSum_ok`), and leaves `HInv` at `j + c`
(`hashChunk_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz ctxCiph ctxLstar)
open VG.Proof.Ocb (offAt hsum blockAtMem_frame)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (in_left in_off eval_zero eval_nonzero toNat_ofNat_of_lt)

/-- What `HASH` writes: the sum, `[96, 160)` (`L_{ntz(i)}`, the blocks of
one call and the offset), and the buffer and the working space of the
functions called. -/
abbrev hashR (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 48, 16⟩, ⟨W + BitVec.ofNat 64 96, 64⟩, ⟨W + BitVec.ofNat 64 384, 2176⟩]

theorem hashR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (hashR W) m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact in_mutA (by decide)
  · exact in_mutA (by decide)
  · exact in_mutB (by decide) (by decide)

/-- What holds of `HASH` of `a` (at `A`) after `j` of its whole blocks, from
the state `s₀` at its start. -/
structure HInv (K W D : Addr) (R n : Nat) (SP : Addr) (ciph : Cipher) (l : Block) (A : Addr) (a : List Byte)
    (s₀ s : State) (j : Nat) : Prop where
  env : Env K W D R n SP s
  frame : Frame (hashR W) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  le : j ≤ a.length / 16
  sum : blockAtMem s.mem (W + BitVec.ofNat 64 sumO) = hsum ciph l a j
  oh : blockAtMem s.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l j
  x23 : s.gpr .x23 = A + BitVec.ofNat 64 (16 * j)
  x25 : s.gpr .x25 = BitVec.ofNat 64 (j + 1)
  x26 : s.gpr .x26 = BitVec.ofNat 64 (a.length / 16 - j)
  l0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0

/-- What a chunk of `HASH` needs of its start, `s₀`: the key context's
cipher and `L_*`, the associated data (apart from `W` and the data at `D`). -/
structure HCtx (K W D : Addr) (n R : Nat) (ciph : Cipher) (l : Block) (A : Addr) (a : List Byte)
    (s₀ : State) : Prop where
  lay : Lay K W
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  ciph : ctxCiph s₀.mem K R = ciph
  lstar : ctxLstar s₀.mem K = l
  buf : Buf W s₀ A a.length
  aad : bytesAt s₀.mem A a.length = a
  ad : (⟨A, a.length⟩ : Region).Disjoint ⟨D, n⟩
  kd : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩
  dw : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩

namespace HCtx

variable {K W D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr} {a : List Byte} {s₀ : State}
  (C : HCtx K W D n R ciph l A a s₀)
include C

theorem short : a.length < 2 ^ 64 := C.buf.lt

/-- The associated data misses the parts the pieces write. -/
theorem a_mut : ∀ r ∈ mutR W D n, (⟨A, a.length⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact C.buf.w.sub_right (Region.sub_prefix (by decide))
  · exact C.buf.w.sub_right (Lay.wSub (by decide))
  · exact C.ad

/-- Block `i` of the associated data, in a state after `s₀`. -/
theorem blk {m : Mem} (h : Frame (mutR W D n) s₀.mem m) {i : Nat} (hi : i < a.length / 16) :
    blockAtMem m (A + BitVec.ofNat 64 (16 * i)) = blockAt a i := by
  rw [← C.aad, Proof.Ocb.blockAt_bytesAt _ _ (by omega), blockAtMem_frame h fun r hr =>
    (C.a_mut r hr).sub_left (Offset.sub_base A (by omega))]

theorem ciph' {m : Mem} (h : Frame (mutR W D n) s₀.mem m) : ctxCiph m K R = ciph := by
  rw [ctxCiph_mut C.lay C.kd h C.rounds, C.ciph]

theorem lstar' {m : Mem} (h : Frame (mutR W D n) s₀.mem m) : ctxLstar m K = l := by
  rw [ctxLstar_mut C.lay C.kd h, C.lstar]

end HCtx

/-! ## Filling the buffer -/

/-- The fill loop after `i` of the `c` blocks of a chunk from block `j`. -/
structure FillInv (K W D : Addr) (R n : Nat) (SP : Addr) (ciph : Cipher) (l : Block) (A : Addr) (a : List Byte)
    (s₀ : State) (j c : Nat) (t : State) (i : Nat) : Prop where
  env : Env K W D R n SP t
  frame : Frame (hashR W) s₀.mem t.mem
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  x23 : t.gpr .x23 = A + BitVec.ofNat 64 (16 * (j + i))
  x25 : t.gpr .x25 = BitVec.ofNat 64 (j + i + 1)
  x27 : t.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * i)
  x15 : t.gpr .x15 = BitVec.ofNat 64 (c - i)
  x24 : t.gpr .x24 = BitVec.ofNat 64 c
  x26 : t.gpr .x26 = BitVec.ofNat 64 (a.length / 16 - j)
  oh : blockAtMem t.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i)
  buf : ∀ k < i, blockAtMem t.mem (W + BitVec.ofNat 64 (384 + 16 * k)) = blockAt a (j + k) ^^^ offAt 0 l (j + k + 1)
  sum : blockAtMem t.mem (W + BitVec.ofNat 64 sumO) = hsum ciph l a j
  l0 : blockAtMem t.mem (W + BitVec.ofNat 64 l0O) = lAt l 0

theorem fill_step {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block} {A : Addr} {a : List Byte}
    {s₀ : State} (C : HCtx K W D n R ciph l A a s₀) {j c : Nat} (hc : c ≤ 8) (hjc : j + c ≤ a.length / 16)
    {t : State} {i : Nat} (hi : i < c) (F : FillInv K W D R n SP ciph l A a s₀ j c t i) :
    WP isa hashFill t fun t' => FillInv K W D R n SP ciph l A a s₀ j c t' (i + 1) := by
  have L := C.lay
  have hs := C.short
  have hA : Covers [⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩] (t.rd ++ t.wr) := by
    rw [F.rd, F.wr]; exact (C.buf.slice (a := 16 * (j + i)) (k := 16) (by omega)).rd
  have hAW : (⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Disjoint ⟨W, 2560⟩ :=
    (C.buf.slice (a := 16 * (j + i)) (k := 16) (by omega)).w
  refine WP.mono (hashFill_ok L F.env.x19 F.env.perm.w hi hc (by omega) F.x25 F.x23 F.x27 F.x15 F.l0 F.oh hA hAW)
    fun t' P => ?_
  have hfr : ∀ r ∈ [(⟨W + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ohO, 16⟩,
      ⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩], ∃ r' ∈ hashR W, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
        Offset.sub W (by omega) (by omega)⟩
  have keepB : ∀ {d : Nat}, (d + 16 ≤ 96 ∨ (112 ≤ d ∧ d + 16 ≤ 144) ∨ (160 ≤ d ∧ d + 16 ≤ 384 + 16 * i) ∨
      384 + 16 * (i + 1) ≤ d) → d + 16 ≤ 2560 →
      blockAtMem t'.mem (W + BitVec.ofNat 64 d) = blockAtMem t.mem (W + BitVec.ofNat 64 d) := fun h₁ h₂ =>
    blockAtMem_frame P.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (a := _) (d := 96) (k := 16) (by omega) h₂ (by decide)
      · exact L.w_w (a := _) (d := 144) (k := 16) (by omega) h₂ (by decide)
      · exact L.w_w (a := _) (d := 384 + 16 * i) (k := 16) (by omega) h₂ (by omega)
  have hg : ∀ r ∈ envRegs, t'.gpr r = t.gpr r := fun r hr => P.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  refine
    { env := F.env.keep hg P.sp P.rd P.wr
      frame := F.frame.trans (P.frame.sub hfr)
      rd := by rw [P.rd, F.rd]
      wr := by rw [P.wr, F.wr]
      x23 := by rw [P.x23, show j + i + 1 = j + (i + 1) by omega]
      x25 := by rw [P.x25, show j + i + 2 = j + (i + 1) + 1 by omega]
      x27 := P.x27
      x15 := P.x15
      x24 := by rw [P.gpr _ (by decide), F.x24]
      x26 := by rw [P.gpr _ (by decide), F.x26]
      oh := by rw [P.oh]; rfl
      buf := fun k hk => ?_
      sum := by rw [keepB (by simp only [sumO]; omega) (by decide), F.sum]
      l0 := by rw [keepB (by simp only [l0O]; omega) (by decide), F.l0] }
  rcases Nat.lt_or_ge k i with hk' | hk'
  · rw [keepB (by omega) (by omega), F.buf k hk']
  · obtain rfl : k = i := by omega
    rw [P.buf, C.blk (hashR_mut F.frame) (by omega)]

theorem fill_ok {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block} {A : Addr} {a : List Byte}
    {s₀ : State} (C : HCtx K W D n R ciph l A a s₀) {j c : Nat} (hc0 : 0 < c) (hc : c ≤ 8)
    (hjc : j + c ≤ a.length / 16) {t : State} (F : FillInv K W D R n SP ciph l A a s₀ j c t 0) :
    WP isa (.loop hashFill (.nonzero .x .x15)) t fun t' => FillInv K W D R n SP ciph l A a s₀ j c t' c := by
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ i, k = c - i ∧ i < c ∧ FillInv K W D R n SP ciph l A a s₀ j c u i) ?_ (c - 0) _
    ⟨0, rfl, hc0, F⟩
  rintro k u ⟨i, rfl, hi, F⟩
  refine WP.mono (fill_step C hc hjc hi F) fun u' F' => ?_
  have ev := eval_nonzero F'.x15 (by omega)
  by_cases he : i + 1 = c
  · left; exact ⟨ev.trans (by simp; omega), he ▸ F'⟩
  · right; exact ⟨ev.trans (by simp; omega), c - (i + 1), by omega, i + 1, rfl, by omega, F'⟩

/-! ## Adding the buffer to the sum -/

theorem bufStart_ok {W : Addr} {t : State} (h19 : t.gpr .x19 = W) {c : Nat} (h24 : t.gpr .x24 = BitVec.ofNat 64 c) :
    ∃ t', runBlock isa bufStart t = some t' ∧ t'.gpr .x15 = BitVec.ofNat 64 (c - 0) ∧
      t'.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * 0) ∧
      (∀ r, r ≠ .x15 → r ≠ .x27 → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧
      t'.wr = t.wr := by
  refine ⟨_, by orun [bufStart, h19], ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, h24]
  · simp [gpr_write, h19]
  · simp [gpr_write, h1, h2]
  all_goals rfl

/-- `x` XORed with `g 0`, …, `g (k − 1)`. -/
def sumOf (x : Block) (g : Nat → Block) : Nat → Block
  | 0 => x
  | k + 1 => sumOf x g k ^^^ g k

theorem hsum_add (ciph : Cipher) (l : Block) (a : List Byte) (j : Nat) :
    ∀ c, hsum ciph l a (j + c) =
      sumOf (hsum ciph l a j) (fun k => ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1))) c
  | 0 => rfl
  | c + 1 => by rw [← Nat.add_assoc, hsum, hsum_add ciph l a j c]; rfl

/-- The sum loop after `k` of the `c` blocks of the buffer. -/
theorem sumStep_ok {W : Addr} {t : State} (h19 : t.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] t.wr) {k c : Nat}
    (hk : k < c) (hc : c ≤ 8) (h27 : t.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * k))
    (h15 : t.gpr .x15 = BitVec.ofNat 64 (c - k)) :
    ∃ t', runBlock isa (xor16 .x27 0 sumO ++ [Impl.AesGcm.AArch64.ptr .x27 .x27 16, .subImm .x .x15 .x15 1]) t =
        some t' ∧
      BlkStep W sumO (blockAtMem t.mem (W + BitVec.ofNat 64 sumO) ^^^
        blockAtMem t.mem (W + BitVec.ofNat 64 (384 + 16 * k))) [.x9, .x10, .x11, .x12, .x15, .x27] t t' ∧
      t'.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * (k + 1)) ∧ t'.gpr .x15 = BitVec.ofNat 64 (c - (k + 1)) := by
  have e0 : W + BitVec.ofNat 64 (384 + 16 * k) + BitVec.ofNat 64 0 = W + BitVec.ofNat 64 (384 + 16 * k) :=
    BitVec.add_zero _
  obtain ⟨t₁, run₁, B₁⟩ := xor16_ok (s := t) (b := .x27) (a := 0) (d := sumO) (by decide) (by decide) h19 h27
    (by decide) (by decide) (by decide) (by rw [e0]; exact in_left (in_off hw (by omega) (by decide)))
    (by rw [Offset.add_add]; exact in_left (in_off hw (by omega) (by decide)))
    (in_off hw (by decide) (by decide)) (in_off hw (by decide) (by decide))
  rw [e0] at B₁
  have h27₁ : t₁.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * k) := by rw [B₁.gpr _ (by decide), h27]
  have h15₁ : t₁.gpr .x15 = BitVec.ofNat 64 (c - k) := by rw [B₁.gpr _ (by decide), h15]
  refine ⟨_, by rw [runBlock_append, run₁, Option.bind_some]; orun [h27₁, h15₁], ?_, ?_, ?_⟩
  · refine ⟨B₁.frame, B₁.val, fun r hr => ?_, B₁.sp, B₁.rd, B₁.wr⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]
    exact B₁.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1])
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h27₁, Offset.add_add]
    rw [show 384 + 16 * k + 16 = 384 + 16 * (k + 1) by omega]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h15₁]
    rw [Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]

theorem hashSum_ok {K W : Addr} (L : Lay K W) {t : State} (h19 : t.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] t.wr)
    {c : Nat} (hc0 : 0 < c) (hc : c ≤ 8) (h24 : t.gpr .x24 = BitVec.ofNat 64 c) {g : Nat → Block}
    (hg : ∀ k < c, blockAtMem t.mem (W + BitVec.ofNat 64 (384 + 16 * k)) = g k) :
    WP isa hashSum t fun t' => Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩] t.mem t'.mem ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = sumOf (blockAtMem t.mem (W + BitVec.ofNat 64 sumO)) g c ∧
      (∀ r, r ∉ [.x9, .x10, .x11, .x12, .x15, .x27] → t'.gpr r = t.gpr r) ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧
      t'.wr = t.wr := by
  obtain ⟨t₁, run₁, x15₁, x27₁, g₁, m₁, sp₁, rd₁, wr₁⟩ := bufStart_ok h19 h24
  unfold hashSum
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ i, k = c - i ∧ i < c ∧
      u.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * i) ∧ u.gpr .x15 = BitVec.ofNat 64 (c - i) ∧
      Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩] t.mem u.mem ∧
      blockAtMem u.mem (W + BitVec.ofNat 64 sumO) = sumOf (blockAtMem t.mem (W + BitVec.ofNat 64 sumO)) g i ∧
      (∀ r, r ∉ [.x9, .x10, .x11, .x12, .x15, .x27] → u.gpr r = t.gpr r) ∧ u.sp = t.sp ∧ u.rd = t.rd ∧
      u.wr = t.wr) ?_ (c - 0) _
    ⟨0, rfl, hc0, x27₁, x15₁, by rw [m₁]; exact Frame.refl _ _, by rw [m₁]; rfl, fun r hr => g₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr.2.2.2.2.1)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr.2.2.2.2.2), sp₁, rd₁,
      wr₁⟩
  rintro k u ⟨i, rfl, hi, x27, x15, fr, sum, gu, sp, rd, wr⟩
  obtain ⟨u', run', B, x27', x15'⟩ := sumStep_ok (by rw [gu _ (by decide), h19]) (by rw [wr]; exact hw) hi hc x27 x15
  refine WP.of_runBlock ⟨u', run', ?_⟩
  have hbuf : blockAtMem u.mem (W + BitVec.ofNat 64 (384 + 16 * i)) = g i := by
    rw [blockAtMem_frame fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (a := 384 + 16 * i) (n := 16) (d := 48) (k := 16) (.inr (by omega)) (by omega) (by decide),
      hg i hi]
  have fr' : Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩] t.mem u'.mem := fr.trans B.frame
  have sum' : blockAtMem u'.mem (W + BitVec.ofNat 64 sumO) = sumOf (blockAtMem t.mem (W + BitVec.ofNat 64 sumO)) g (i + 1) := by
    rw [B.val, sum, hbuf]; rfl
  have gu' : ∀ r, r ∉ [.x9, .x10, .x11, .x12, .x15, .x27] → u'.gpr r = t.gpr r := fun r hr => by
    rw [B.gpr r hr, gu r hr]
  have ev := eval_nonzero x15' (by omega)
  by_cases he : i + 1 = c
  · left
    exact ⟨ev.trans (by simp; omega), fr', he ▸ sum', gu', by rw [B.sp, sp], by rw [B.rd, rd], by rw [B.wr, wr]⟩
  · right
    exact ⟨ev.trans (by simp; omega), c - (i + 1), by omega, i + 1, rfl, by omega, x27', x15', fr',
      sum', gu', by rw [B.sp, sp], by rw [B.rd, rd], by rw [B.wr, wr]⟩

/-! ## A chunk -/

/-- `x9 ← (x26 − 8) ⋙ 63`: 1 if fewer than 8 blocks are left. -/
theorem lt8 {L : Nat} (hL : L < 2 ^ 63) :
    (BitVec.ofNat 64 L - 8#64) >>> 63 = BitVec.ofNat 64 (if L < 8 then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, toNat_ofNat_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

/-- The number of blocks of a chunk: `x24 ← min(8, x26)`. -/
theorem chunkHead_ok {t : State} {L : Nat} (hL : L < 2 ^ 63) (h26 : t.gpr .x26 = BitVec.ofNat 64 L) :
    WP isa (.seq (.block [.subImm .x .x9 .x26 8, .lsr .x .x9 .x9 63, Impl.AesGcm.AArch64.mov .x24 .x26])
      (.ite (.zero .x .x9) (.block [Impl.AesGcm.AArch64.imm .x24 8]) (.block []))) t fun t' =>
      t'.gpr .x24 = BitVec.ofNat 64 (min 8 L) ∧ (∀ r, r ≠ .x9 → r ≠ .x24 → t'.gpr r = t.gpr r) ∧
      t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain ⟨t₁, run₁, x9₁, x24₁, g₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa
      [.subImm .x .x9 .x26 8, .lsr .x .x9 .x9 63, Impl.AesGcm.AArch64.mov .x24 .x26] t = some t₁ ∧
      t₁.gpr .x9 = BitVec.ofNat 64 (if L < 8 then 1 else 0) ∧ t₁.gpr .x24 = BitVec.ofNat 64 L ∧
      (∀ r, r ≠ .x9 → r ≠ .x24 → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧
      t₁.wr = t.wr := by
    refine ⟨_, by orun [h26], ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, h26, lt8 hL]
    · simp [gpr_write, h26]
    · simp [gpr_write, h1, h2]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  by_cases h8 : L < 8
  · simp only [h8, ↓reduceIte] at x9₁
    refine WP.ite false (by rw [eval_zero x9₁ (by decide)]; rfl) (fun h => by cases h) (fun _ => ?_)
    exact WP.block_nil ⟨by rw [x24₁, Nat.min_eq_right (by omega)], g₁, m₁, sp₁, rd₁, wr₁⟩
  · simp only [h8, ↓reduceIte] at x9₁
    refine WP.ite true (by rw [eval_zero x9₁ (by decide)]; rfl) (fun _ => ?_) (fun h => by cases h)
    refine Proof.AesGcm.AArch64.WP.run (Q := fun t' => t' = t₁.write .x .x24 (BitVec.ofNat 64 8)) ⟨_, by orun [], rfl⟩ fun t' ht' => ?_
    subst ht'
    refine ⟨by simp [gpr_write, Nat.min_eq_left (show 8 ≤ L by omega)], fun r h1 h2 => ?_, m₁, sp₁, rd₁, wr₁⟩
    simp only [gpr_write, h2, ite_false]; exact g₁ r h1 h2

/-- The `c` blocks of the buffer. -/
theorem bufArgs_ok {W : Addr} {t : State} (h19 : t.gpr .x19 = W) {c : Nat} (h24 : t.gpr .x24 = BitVec.ofNat 64 c) :
    ArgsOk [Impl.AesGcm.AArch64.ptr .x2 .x19 bufO, Impl.AesGcm.AArch64.mov .x3 .x24] t (W + BitVec.ofNat 64 384) c := by
  refine ⟨_, by orun [h19, h24], ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, h19]
  · simp [gpr_write, h24]
  · simp [gpr_write, h1, h2]
  all_goals rfl

/-- `bufStart`: the fill loop before its first block. -/
theorem bufStart_inv {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} {t : State} {j c : Nat}
    (H : HInv K W D R n SP ciph l A a s₀ t j) (h24 : t.gpr .x24 = BitVec.ofNat 64 c) :
    ∃ t₁, runBlock isa bufStart t = some t₁ ∧ FillInv K W D R n SP ciph l A a s₀ j c t₁ 0 := by
  obtain ⟨t₁, run₁, x15₁, x27₁, g₁, m₁, sp₁, rd₁, wr₁⟩ := bufStart_ok H.env.x19 h24
  exact ⟨t₁, run₁,
    { env := H.env.others (rs := [.x15, .x27]) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact g₁ r hr.1 hr.2) sp₁ rd₁ wr₁
      frame := by rw [m₁]; exact H.frame
      rd := by rw [rd₁, H.rd]
      wr := by rw [wr₁, H.wr]
      x23 := by rw [g₁ _ (by decide) (by decide), H.x23]; rfl
      x25 := by rw [g₁ _ (by decide) (by decide), H.x25]
      x27 := x27₁
      x15 := x15₁
      x24 := by rw [g₁ _ (by decide) (by decide), h24]
      x26 := by rw [g₁ _ (by decide) (by decide), H.x26]
      oh := by rw [m₁, H.oh]; rfl
      buf := fun k hk => absurd hk (Nat.not_lt_zero _)
      sum := by rw [m₁, H.sum]
      l0 := by rw [m₁, H.l0] }⟩

/-- A chunk from `bufStart` on, with its `c` blocks in `x24`. -/
theorem chunkRest_ok (v : BlocksImpl) {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx K W D n R ciph l A a s₀) {t : State} {j c : Nat}
    (H : HInv K W D R n SP ciph l A a s₀ t j) (hc0 : 0 < c) (hc : c ≤ 8) (hjc : j + c ≤ a.length / 16)
    (h24 : t.gpr .x24 = BitVec.ofNat 64 c) :
    WP isa (.seq (.block bufStart) (.seq (.loop hashFill (.nonzero .x .x15))
        (.seq (callBlocks (callees v).enc [Impl.AesGcm.AArch64.ptr .x2 .x19 bufO, Impl.AesGcm.AArch64.mov .x3 .x24])
          (.seq hashSum (.block [.sub .x .x26 .x26 .x24]))))) t
      fun t' => HInv K W D R n SP ciph l A a s₀ t' (j + c) := by
  have L := C.lay
  have hs := C.short
  obtain ⟨t₁, run₁, F₀⟩ := bufStart_inv H h24
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (fill_ok C hc0 hc hjc F₀) fun t₂ F => ?_)
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOk v.encNoFrames L F.env
    C.rounds (bufArgs_ok F.env.x19 F.x24) (dstW L F.env.perm (d := 384) (n := c) (by omega)))
    fun t₃ P₃ => ?_)
  have E₃ := F.env.of_saved P₃.saved P₃.sp P₃.rd P₃.wr
  have F₃ : Frame (hashR W) t₂.mem t₃.mem := P₃.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, Offset.sub W (e := 384) (k := 2176) (by decide) (by omega)⟩
    · exact ⟨_, by simp, Offset.sub W (e := 384) (k := 2176) (by decide) (by decide)⟩
  have k₃ : ∀ {d : Nat}, d + 16 ≤ 384 → blockAtMem t₃.mem (W + BitVec.ofNat 64 d) = blockAtMem t₂.mem (W + BitVec.ofNat 64 d) :=
    fun hd => blockAtMem_frame P₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by omega)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  have hg : ∀ k < c, blockAtMem t₃.mem (W + BitVec.ofNat 64 (384 + 16 * k)) =
      ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1)) := fun k hk => by
    have := P₃.enc hk
    rw [Offset.add_add] at this
    rw [this, F.buf k hk]
    exact congrFun (C.ciph' (hashR_mut F.frame)) _
  have h24₃ : t₃.gpr .x24 = BitVec.ofNat 64 c := by rw [P₃.saved _ (by decide) (by decide), F.x24]
  refine WP.seq (WP.mono (hashSum_ok L E₃.x19 E₃.perm.w hc0 hc h24₃ hg) fun t₄ ⟨fr₄, sum₄, g₄, sp₄, rd₄, wr₄⟩ => ?_)
  have E₄ := E₃.others g₄ sp₄ rd₄ wr₄
  have k₄ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ 64 ≤ d) → d + 16 ≤ 2560 →
      blockAtMem t₄.mem (W + BitVec.ofNat 64 d) = blockAtMem t₃.mem (W + BitVec.ofNat 64 d) := fun h₁ h₂ =>
    blockAtMem_frame fr₄ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (a := _) (d := 48) (k := 16) (by omega) h₂ (by decide)
  have h24₄ : t₄.gpr .x24 = BitVec.ofNat 64 c := by rw [g₄ _ (by decide), h24₃]
  have h26₄ : t₄.gpr .x26 = BitVec.ofNat 64 (a.length / 16 - j) := by
    rw [g₄ _ (by decide), P₃.saved _ (by decide) (by decide), F.x26]
  refine Proof.AesGcm.AArch64.WP.run (Q := fun t' => t' = t₄.write .x .x26 (t₄.gpr .x26 - t₄.gpr .x24)) ⟨_, by orun [], rfl⟩ fun t' ht' => ?_
  subst ht'
  refine
    { env := E₄.others (rs := [.x26]) (fun r hr => by simp at hr; simp [gpr_write, hr]) rfl rfl rfl
      frame := F.frame.trans (F₃.trans (fr₄.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., fun _ h => h⟩))
      rd := by rw [rd_write, rd₄, P₃.rd, F.rd]
      wr := by rw [wr_write, wr₄, P₃.wr, F.wr]
      le := by omega
      sum := by rw [mem_write, sum₄, k₃ (by decide), F.sum, hsum_add]
      oh := by rw [mem_write, k₄ (by simp only [ohO]; omega) (by decide), k₃ (by decide), F.oh]
      x23 := by
        rw [gpr_write_of_ne _ _ _ (by decide), g₄ _ (by decide), P₃.saved _ (by decide) (by decide), F.x23]
      x25 := by
        rw [gpr_write_of_ne _ _ _ (by decide), g₄ _ (by decide), P₃.saved _ (by decide) (by decide), F.x25]
      x26 := by
        rw [gpr_write_self, h26₄, h24₄, BitVec.setWidth_eq, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
      l0 := by rw [mem_write, k₄ (by simp only [l0O]; omega) (by decide), k₃ (by decide), F.l0] }

/-- `HInv` after `chunkHead`, which writes only `x9` and `x24`. -/
theorem HInv.head {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} {t t₁ : State} {j : Nat}
    (H : HInv K W D R n SP ciph l A a s₀ t j) (g₁ : ∀ r, r ≠ .x9 → r ≠ .x24 → t₁.gpr r = t.gpr r)
    (m₁ : t₁.mem = t.mem) (sp₁ : t₁.sp = t.sp) (rd₁ : t₁.rd = t.rd) (wr₁ : t₁.wr = t.wr) :
    HInv K W D R n SP ciph l A a s₀ t₁ j :=
  { H with
    env := H.env.others (rs := [.x9, .x24]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact g₁ r hr.1 hr.2) sp₁ rd₁ wr₁
    frame := by rw [m₁]; exact H.frame
    rd := by rw [rd₁, H.rd]
    wr := by rw [wr₁, H.wr]
    sum := by rw [m₁, H.sum]
    oh := by rw [m₁, H.oh]
    x23 := by rw [g₁ _ (by decide) (by decide), H.x23]
    x25 := by rw [g₁ _ (by decide) (by decide), H.x25]
    x26 := by rw [g₁ _ (by decide) (by decide), H.x26]
    l0 := by rw [m₁, H.l0] }

theorem hashChunk_ok (v : BlocksImpl) {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx K W D n R ciph l A a s₀) {t : State} {j : Nat}
    (H : HInv K W D R n SP ciph l A a s₀ t j) (hj : j < a.length / 16) :
    WP isa (hashChunk (callees v)) t fun t' =>
      HInv K W D R n SP ciph l A a s₀ t' (j + min 8 (a.length / 16 - j)) := by
  have hs := C.short
  unfold hashChunk
  refine WP.assoc (WP.seq (WP.mono (chunkHead_ok (L := a.length / 16 - j) (by omega) H.x26)
    fun t₁ ⟨h24, g₁, m₁, sp₁, rd₁, wr₁⟩ => ?_))
  exact chunkRest_ok v C (H.head g₁ m₁ sp₁ rd₁ wr₁) (by omega) (by omega) (by omega) h24

end VG.Proof.AesOcb.AArch64
