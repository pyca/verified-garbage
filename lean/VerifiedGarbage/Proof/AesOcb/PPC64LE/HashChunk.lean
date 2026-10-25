module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Words
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Args
public import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.AesOcb.PPC64LE.HashFill
import VerifiedGarbage.Proof.AesOcb.PPC64LE.Nonce
import VerifiedGarbage.Proof.AesOcb.PPC64LE.PadTo
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-OCB on PPC64LE: a chunk of `HASH` (`hashChunk`)

Untrusted: everything here is checked by Lean. After `j` of the `m` whole
blocks of the associated data `a`, `HInv` holds: the sum and the offset of
`HASH` are `Sum_j` and `Offset_j` (`Proof.Ocb.hsum`, `Proof.Ocb.offAt`),
`r24` points at block `j`, `r26` is `j + 1`, and `m − j` is in `r3` and at
`W + hlO`. `hashChunk` takes `c = min(8, m − j)` blocks (`chunkHead_ok`):
fills the buffer with each block XORed with its offset (`fill_ok`),
enciphers the buffer, adds it to the sum (`hashSum_ok`), and leaves `HInv`
at `j + c` (`hashChunk_ok`). As on AArch64
(`Proof/AesOcb/AArch64/HashChunk.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Impl.AesOcb.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz ctxCiph ctxLstar)
open VG.Proof.Ocb (offAt hsum blockAtMem_frame)
open VG.Proof.AesGcm.PPC64LE (in_left in_off eval_zero Keeps)
open VG.Proof.ChaCha20Poly1305.PPC64LE renaming wp_or → cwp_or, wp_subi → cwp_subi, wp_lsr → cwp_lsr,
  wp_addi → cwp_addi, wp_ld → cwp_ld, wp_std → cwp_std, wp_sub → cwp_sub, wp_li → cwp_li

/-- What `HASH` writes: the sum, `L_{ntz(i)}`, its offset, the counts of
blocks at `[296, 312)`, and the buffer and the working space of the
functions called. -/
abbrev hashR (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 48, 16⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 272, 16⟩,
    ⟨W + BitVec.ofNat 64 296, 16⟩, ⟨W + BitVec.ofNat 64 384, 2176⟩]

theorem hashR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (hashR W) m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact in_mutA (by decide)
  · exact in_mutA (by decide)
  · exact in_mutB (by decide) (by decide)
  · exact in_mutB (by decide) (by decide)
  · exact in_mutB (by decide) (by decide)

/-- A part of `W` that `HASH` writes, within its part at `W + e`. -/
theorem in_hashR {W : Addr} {d k e n : Nat} (he : (⟨W + BitVec.ofNat 64 e, n⟩ : Region) ∈ hashR W)
    (h₁ : e ≤ d) (h₂ : d + k ≤ e + n) : ∃ r' ∈ hashR W, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨_, he, Offset.sub W h₁ h₂⟩

/-- A doubleword of `W` that a frame within `HASH`'s parts keeps. -/
theorem readW_hashR {K W : Addr} (L : Lay K W) {rs : List Region} {m m' : Mem} (f : Frame rs m m')
    (hsub : ∀ r ∈ rs, ∃ r' ∈ hashR W, Region.Sub r r') {d : Nat}
    (hd : (64 ≤ d ∧ d + 8 ≤ 96) ∨ (112 ≤ d ∧ d + 8 ≤ 272) ∨ (288 ≤ d ∧ d + 8 ≤ 296) ∨ (312 ≤ d ∧ d + 8 ≤ 384)) :
    m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
  (f.sub hsub).readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact L.w_w (by omega_arith) (by omega_arith) (by decide)) (by decide)

/-- What holds of `HASH` of `a` (at `A`) after `j` of its whole blocks, from
the state `s₀` at its start. -/
structure HInv (V : Reg → BitVec 64) (sp : Addr) (ciph : Cipher) (l : Block) (A : Addr) (a : List Byte)
    (s₀ s : State) (j : Nat) : Prop where
  env : Env V sp s
  frame : Frame (hashR (V .r31)) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  le : j ≤ a.length / 16
  sum : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 sumO) = hsum ciph l a j
  oh : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 ohO) = offAt 0 l j
  r24 : s.gpr .r24 = A + BitVec.ofNat 64 (16 * j)
  r26 : s.gpr .r26 = BitVec.ofNat 64 (j + 1)
  r3 : s.gpr .r3 = BitVec.ofNat 64 (a.length / 16 - j)
  hl : s.mem.readW (V .r31 + BitVec.ofNat 64 hlO) 64 = BitVec.ofNat 64 (a.length / 16 - j)
  l0 : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 l0O) = lAt l 0

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
  rw [← C.aad, Proof.Ocb.blockAt_bytesAt _ _ (by omega_arith), blockAtMem_frame h fun r hr =>
    (C.a_mut r hr).sub_left (Offset.sub_base A (by omega_arith))]

theorem ciph' {m : Mem} (h : Frame (mutR W D n) s₀.mem m) : ctxCiph m K R = ciph := by
  rw [ctxCiph_mut C.lay C.kd h C.rounds, C.ciph]

theorem lstar' {m : Mem} (h : Frame (mutR W D n) s₀.mem m) : ctxLstar m K = l := by
  rw [ctxLstar_mut C.lay C.kd h, C.lstar]

end HCtx

/-! ## Filling the buffer -/

/-- The fill loop after `i` of the `c` blocks of a chunk from block `j`. -/
structure FillInv (V : Reg → BitVec 64) (sp : Addr) (ciph : Cipher) (l : Block) (A : Addr) (a : List Byte)
    (s₀ : State) (j c : Nat) (t : State) (i : Nat) : Prop where
  env : Env V sp t
  frame : Frame (hashR (V .r31)) s₀.mem t.mem
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  r24 : t.gpr .r24 = A + BitVec.ofNat 64 (16 * (j + i))
  r26 : t.gpr .r26 = BitVec.ofNat 64 (j + i + 1)
  r11 : t.gpr .r11 = V .r31 + BitVec.ofNat 64 (384 + 16 * i)
  r25 : t.gpr .r25 = BitVec.ofNat 64 (c - i)
  cn : t.mem.readW (V .r31 + BitVec.ofNat 64 cnO) 64 = BitVec.ofNat 64 c
  hl : t.mem.readW (V .r31 + BitVec.ofNat 64 hlO) 64 = BitVec.ofNat 64 (a.length / 16 - (j + c))
  oh : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ohO) = offAt 0 l (j + i)
  buf : ∀ k < i, blockAtMem t.mem (V .r31 + BitVec.ofNat 64 (384 + 16 * k)) =
    blockAt a (j + k) ^^^ offAt 0 l (j + k + 1)
  sum : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 sumO) = hsum ciph l a j
  l0 : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 l0O) = lAt l 0

theorem fill_step {V : Reg → BitVec 64} {sp : Addr} {D : Addr} {n R : Nat} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx (V .r29) (V .r31) D n R ciph l A a s₀) {j c : Nat}
    (hc : c ≤ 8) (hjc : j + c ≤ a.length / 16) {t : State} {i : Nat} (hi : i < c)
    (F : FillInv V sp ciph l A a s₀ j c t i) :
    WP isa hashFill t fun t' => FillInv V sp ciph l A a s₀ j c t' (i + 1) := by
  have L := C.lay
  have hs := C.short
  have hA : Covers [⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩] (t.rd ++ t.wr) := by
    rw [F.rd, F.wr]; exact (C.buf.slice (a := 16 * (j + i)) (k := 16) (by omega_arith)).rd
  have hAW : (⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Disjoint ⟨V .r31, 2560⟩ :=
    (C.buf.slice (a := 16 * (j + i)) (k := 16) (by omega_arith)).w
  refine WP.mono (hashFill_ok L F.env.r31 F.env.perm.w hi hc (by omega_arith) F.r26 F.r24 F.r11 F.r25 F.l0 F.oh hA hAW)
    fun t' P => ?_
  have hfr : ∀ r ∈ [(⟨V .r31 + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨V .r31 + BitVec.ofNat 64 ohO, 16⟩,
      ⟨V .r31 + BitVec.ofNat 64 (384 + 16 * i), 16⟩], ∃ r' ∈ hashR (V .r31), Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact in_hashR (e := 96) (n := 16) (by simp) (by decide) (by decide)
    · exact in_hashR (e := 272) (n := 16) (by simp) (by decide) (by decide)
    · exact in_hashR (e := 384) (n := 2176) (by simp) (by omega_arith) (by omega_arith)
  have keepB : ∀ {d : Nat}, (d + 16 ≤ 96 ∨ (112 ≤ d ∧ d + 16 ≤ 272) ∨ (288 ≤ d ∧ d + 16 ≤ 384 + 16 * i) ∨
      384 + 16 * (i + 1) ≤ d) → d + 16 ≤ 2560 →
      blockAtMem t'.mem (V .r31 + BitVec.ofNat 64 d) = blockAtMem t.mem (V .r31 + BitVec.ofNat 64 d) :=
    fun h₁ h₂ => blockAtMem_frame P.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (a := _) (d := 96) (k := 16) (by omega_arith) h₂ (by decide)
      · exact L.w_w (a := _) (d := 272) (k := 16) (by omega_arith) h₂ (by decide)
      · exact L.w_w (a := _) (d := 384 + 16 * i) (k := 16) (by omega_arith) h₂ (by omega_arith)
  have keepW : ∀ {d : Nat}, (288 ≤ d ∧ d + 8 ≤ 384) →
      t'.mem.readW (V .r31 + BitVec.ofNat 64 d) 64 = t.mem.readW (V .r31 + BitVec.ofNat 64 d) 64 := fun h =>
    P.frame.readW (r := ⟨V .r31 + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (d := 96) (k := 16) (by omega_arith) (by omega_arith) (by decide)
      · exact L.w_w (d := 272) (k := 16) (by omega_arith) (by omega_arith) (by decide)
      · exact L.w_w (d := 384 + 16 * i) (k := 16) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)
  refine
    { env := F.env.others P.gpr P.sp P.rd P.wr
      frame := F.frame.trans (P.frame.sub hfr)
      rd := by rw [P.rd, F.rd]
      wr := by rw [P.wr, F.wr]
      r24 := by rw [P.r24, show j + i + 1 = j + (i + 1) by omega_arith]
      r26 := by rw [P.r26, show j + i + 2 = j + (i + 1) + 1 by omega_arith]
      r11 := P.r11
      r25 := P.r25
      cn := by rw [keepW (by simp only [cnO]; omega_arith), F.cn]
      hl := by rw [keepW (by simp only [hlO]; omega_arith), F.hl]
      oh := by rw [P.oh]; rfl
      buf := fun k hk => ?_
      sum := by rw [keepB (by simp only [sumO]; omega_arith) (by decide), F.sum]
      l0 := by rw [keepB (by simp only [l0O]; omega_arith) (by decide), F.l0] }
  rcases Nat.lt_or_ge k i with hk' | hk'
  · rw [keepB (by omega_arith) (by omega_arith), F.buf k hk']
  · obtain rfl : k = i := by omega_arith
    rw [P.buf, C.blk (hashR_mut F.frame) (by omega_arith)]

theorem fill_ok {V : Reg → BitVec 64} {sp : Addr} {D : Addr} {n R : Nat} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx (V .r29) (V .r31) D n R ciph l A a s₀) {j c : Nat}
    (hc0 : 0 < c) (hc : c ≤ 8) (hjc : j + c ≤ a.length / 16) {t : State}
    (F : FillInv V sp ciph l A a s₀ j c t 0) :
    WP isa (.loop hashFill (.nonzero .d .r25)) t fun t' => FillInv V sp ciph l A a s₀ j c t' c := by
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ i, k = c - i ∧ i < c ∧ FillInv V sp ciph l A a s₀ j c u i) ?_ (c - 0) _
    ⟨0, rfl, hc0, F⟩
  rintro k u ⟨i, rfl, hi, F⟩
  refine WP.mono (fill_step C hc hjc hi F) fun u' F' => ?_
  have ev := eval_nonzero F'.r25 (by omega_arith)
  by_cases he : i + 1 = c
  · left; exact ⟨ev.trans (by simp; omega_arith), he ▸ F'⟩
  · right; exact ⟨ev.trans (by simp; omega_arith), c - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, F'⟩

/-! ## Adding the buffer to the sum -/

/-- `x` XORed with `g 0`, …, `g (k − 1)`. -/
def sumOf (x : Block) (g : Nat → Block) : Nat → Block
  | 0 => x
  | k + 1 => sumOf x g k ^^^ g k

theorem hsum_add (ciph : Cipher) (l : Block) (a : List Byte) (j : Nat) :
    ∀ c, hsum ciph l a (j + c) =
      sumOf (hsum ciph l a j) (fun k => ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1))) c
  | 0 => rfl
  | c + 1 => by rw [← Nat.add_assoc, hsum, hsum_add ciph l a j c]; rfl

/-- The registers the sum loop writes. -/
abbrev sumRegs : List Reg := [.r3, .r4, .r11, .r25]

/-- The sum loop after `k` of the `c` blocks of the buffer. -/
theorem sumStep_ok {W : Addr} {t : State} (h31 : t.gpr .r31 = W) (hw : Covers [⟨W, 2560⟩] t.wr) {k c : Nat}
    (hk : k < c) (hc : c ≤ 8) (h11 : t.gpr .r11 = W + BitVec.ofNat 64 (384 + 16 * k))
    (h25 : t.gpr .r25 = BitVec.ofNat 64 (c - k)) :
    WP isa (.block (xorB .r31 .r11 .r31 sumO 0 sumO ++ ([.addi .r11 .r11 16, .subi .r25 .r25 1] : List Instr))) t fun t' =>
      BlkStep W sumO (blockAtMem t.mem (W + BitVec.ofNat 64 sumO) ^^^
        blockAtMem t.mem (W + BitVec.ofNat 64 (384 + 16 * k))) sumRegs t t' ∧
      t'.gpr .r11 = W + BitVec.ofNat 64 (384 + 16 * (k + 1)) ∧ t'.gpr .r25 = BitVec.ofNat 64 (c - (k + 1)) := by
  have e0 : W + BitVec.ofNat 64 (384 + 16 * k) + BitVec.ofNat 64 0 = W + BitVec.ofNat 64 (384 + 16 * k) :=
    BitVec.add_zero _
  have e8 : W + BitVec.ofNat 64 (384 + 16 * k) + BitVec.ofNat 64 (0 + 8) = W + BitVec.ofNat 64 (384 + 16 * k + 8) :=
    Offset.add_add _ _ _
  refine WP.block_append (WP.mono (xorB_ok (s := t) (pd := sumO) (qd := 0) (cd := sumO) (by decide) (by decide)
    (by decide) h31 h11 h31 (by decide) (by decide) (by decide) (in_left (in_off hw (by decide) (by decide)))
    (in_left (in_off hw (by decide) (by decide))) (by rw [e0]; exact in_left (in_off hw (by omega_arith) (by decide)))
    (by rw [e8]; exact in_left (in_off hw (by omega_arith) (by decide))) (in_off hw (by decide) (by decide))
    (in_off hw (by decide) (by decide)) (Offset.sep W (by decide) (by decide) (by decide))
    (by rw [e8]; exact Offset.sep W (.inr (by simp only [sumO]; omega_arith)) (by omega_arith) (by decide))) fun t₁ B₁ => ?_)
  rw [e0] at B₁
  refine cwp_addi (by decide) (by decide) fun t₂ u₂ => cwp_subi (by decide) (by decide) fun t₃ u₃ => WP.block_nil ?_
  refine ⟨⟨by rw [u₃.mem, u₂.mem]; exact B₁.frame, by rw [u₃.mem, u₂.mem]; exact B₁.val, fun r hr => ?_,
    by rw [u₃.sp, u₂.sp, B₁.sp], by rw [u₃.lr, u₂.lr, B₁.lr], by rw [u₃.rd, u₂.rd, B₁.rd],
    by rw [u₃.wr, u₂.wr, B₁.wr]⟩, ?_, ?_⟩
  · simp only [sumRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₃.other _ hr.2.2.2, u₂.other _ hr.2.2.1, B₁.gpr r (by simp [hr.1, hr.2.1])]
  · rw [u₃.other _ (by decide), u₂.gpr, B₁.gpr _ (by decide), h11, Offset.add_add,
      show 384 + 16 * k + 16 = 384 + 16 * (k + 1) by omega_arith]
  · rw [u₃.gpr, u₂.other _ (by decide), B₁.gpr _ (by decide), h25, Offset.ofNat_sub_ofNat (by omega_arith), Nat.sub_sub]

theorem hashSum_ok {K W : Addr} (L : Lay K W) {t : State} (h31 : t.gpr .r31 = W) (hw : Covers [⟨W, 2560⟩] t.wr)
    {c : Nat} (hc0 : 0 < c) (hc : c ≤ 8) (h11 : t.gpr .r11 = W + BitVec.ofNat 64 384)
    (h25 : t.gpr .r25 = BitVec.ofNat 64 c) {g : Nat → Block}
    (hg : ∀ k < c, blockAtMem t.mem (W + BitVec.ofNat 64 (384 + 16 * k)) = g k) :
    WP isa hashSum t fun t' => Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩] t.mem t'.mem ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = sumOf (blockAtMem t.mem (W + BitVec.ofNat 64 sumO)) g c ∧
      (∀ r, r ∉ sumRegs → t'.gpr r = t.gpr r) ∧ t'.sp = t.sp ∧ t'.lr = t.lr ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  unfold hashSum
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ i, k = c - i ∧ i < c ∧
      u.gpr .r11 = W + BitVec.ofNat 64 (384 + 16 * i) ∧ u.gpr .r25 = BitVec.ofNat 64 (c - i) ∧
      Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩] t.mem u.mem ∧
      blockAtMem u.mem (W + BitVec.ofNat 64 sumO) = sumOf (blockAtMem t.mem (W + BitVec.ofNat 64 sumO)) g i ∧
      (∀ r, r ∉ sumRegs → u.gpr r = t.gpr r) ∧ u.sp = t.sp ∧ u.lr = t.lr ∧ u.rd = t.rd ∧ u.wr = t.wr) ?_
    (c - 0) _ ⟨0, rfl, hc0, h11, h25, Frame.refl _ _, rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  rintro k u ⟨i, rfl, hi, r11, r25, fr, sum, gu, sp, lr, rd, wr⟩
  refine WP.mono (sumStep_ok (by rw [gu _ (by decide), h31]) (by rw [wr]; exact hw) hi hc r11 r25)
    fun u' ⟨B, r11', r25'⟩ => ?_
  have hbuf : blockAtMem u.mem (W + BitVec.ofNat 64 (384 + 16 * i)) = g i := by
    rw [blockAtMem_frame fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (a := 384 + 16 * i) (n := 16) (d := 48) (k := 16) (.inr (by omega_arith)) (by omega_arith) (by decide),
      hg i hi]
  have fr' : Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩] t.mem u'.mem := fr.trans B.frame
  have sum' : blockAtMem u'.mem (W + BitVec.ofNat 64 sumO) =
      sumOf (blockAtMem t.mem (W + BitVec.ofNat 64 sumO)) g (i + 1) := by
    rw [B.val, sum, hbuf]; rfl
  have gu' : ∀ r, r ∉ sumRegs → u'.gpr r = t.gpr r := fun r hr => by rw [B.gpr r hr, gu r hr]
  have ev := eval_nonzero r25' (by omega_arith)
  by_cases he : i + 1 = c
  · left
    exact ⟨ev.trans (by simp; omega_arith), fr', he ▸ sum', gu', by rw [B.sp, sp], by rw [B.lr, lr], by rw [B.rd, rd],
      by rw [B.wr, wr]⟩
  · right
    exact ⟨ev.trans (by simp; omega_arith), c - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, r11', r25', fr',
      sum', gu', by rw [B.sp, sp], by rw [B.lr, lr], by rw [B.rd, rd], by rw [B.wr, wr]⟩

/-! ## A chunk -/

theorem shr3 {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 3 = BitVec.ofNat 64 (n / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_arith)]

/-- The blocks left `L` (at `W + hlO`) to `r3`, and `L / 8` to `r4`. -/
theorem chunkLd_ok {W : Addr} {t : State} (h31 : t.gpr .r31 = W) (hw : Covers [⟨W, 2560⟩] t.wr) {L : Nat}
    (hL : L < 2 ^ 63) (hl : t.mem.readW (W + BitVec.ofNat 64 hlO) 64 = BitVec.ofNat 64 L) :
    WP isa (.block [.load .d .r3 .r31 hlO, .lsr .d .r4 .r3 3]) t fun t₂ =>
      t₂.gpr .r3 = BitVec.ofNat 64 L ∧ t₂.gpr .r4 = BitVec.ofNat 64 (L / 8) ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → t₂.gpr r = t.gpr r) ∧ Keeps t t₂ :=
  cwp_ld (a := W + BitVec.ofNat 64 hlO) (by decide) (by decide) (by rw [h31])
    (in_left (in_off hw (by decide) (by decide))) fun t₁ u₁ => cwp_lsr (by decide) fun t₂ u₂ => WP.block_nil
    ⟨by rw [u₂.other _ (by decide), u₁.gpr, hl], by rw [u₂.gpr, u₁.gpr, hl, shr3 (by omega_arith)],
      fun r a b => by rw [u₂.other _ b, u₁.other _ a],
      ⟨by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp],
        by rw [u₂.lr, u₁.lr]⟩⟩

/-- The number of blocks of a chunk: `r25 ← min(8, L)`, `L` the blocks left (at `W + hlO`). -/
theorem chunkHead_ok {W : Addr} {t : State} (h31 : t.gpr .r31 = W) (hw : Covers [⟨W, 2560⟩] t.wr) {L : Nat}
    (hL : L < 2 ^ 63) (hl : t.mem.readW (W + BitVec.ofNat 64 hlO) 64 = BitVec.ofNat 64 L) :
    WP isa (.seq (.block [.load .d .r3 .r31 hlO, .lsr .d .r4 .r3 3])
      (.ite (.zero .d .r4) (.block [Impl.AesGcm.PPC64LE.mov .r25 .r3]) (.block [.li .r25 8]))) t fun t' =>
      t'.gpr .r25 = BitVec.ofNat 64 (min 8 L) ∧ (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r25 → t'.gpr r = t.gpr r) ∧
      Keeps t t' := by
  refine WP.seq (WP.mono (chunkLd_ok h31 hw hL hl) fun t₂ ⟨r3₂, r4₂, g₂, k₂⟩ => ?_)
  by_cases h8 : L < 8
  · refine WP.ite true (by rw [eval_zero r4₂ (by omega_arith)]; simp; omega_arith) (fun _ => ?_) (fun h => by cases h)
    refine cwp_or fun t₃ u₃ => WP.block_nil ⟨by rw [u₃.gpr, BitVec.or_self, r3₂, Nat.min_eq_right (by omega_arith)],
      fun r a b c => by rw [u₃.other _ c, g₂ r a b], k₂.trans ⟨u₃.mem, u₃.rd, u₃.wr, u₃.sp, u₃.lr⟩⟩
  · refine WP.ite false (by rw [eval_zero r4₂ (by omega_arith)]; simp; omega_arith) (fun h => by cases h) (fun _ => ?_)
    refine cwp_li (by decide) fun t₃ u₃ => WP.block_nil ⟨by rw [u₃.gpr, Nat.min_eq_left (by omega_arith)],
      fun r a b c => by rw [u₃.other _ c, g₂ r a b], k₂.trans ⟨u₃.mem, u₃.rd, u₃.wr, u₃.sp, u₃.lr⟩⟩

/-- The `c` blocks of the buffer, their number at `W + cnO`. -/
theorem bufArgs_ok {W : Addr} {s : State} (h31 : s.gpr .r31 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {c : Nat}
    (hcn : s.mem.readW (W + BitVec.ofNat 64 cnO) 64 = BitVec.ofNat 64 c) :
    ArgsOk [.addi .r5 .r31 bufO, .load .d .r6 .r31 cnO] s (W + BitVec.ofNat 64 384) c := by
  have r := in_left (rd := s.rd) (in_off hw (d := cnO) (n := 8) (by decide) (by decide))
  simp only [cnO] at r
  refine ⟨(s.write .r5 (s.gpr .r31 + BitVec.ofNat 64 bufO)).write .r6
      (s.mem.readW (s.gpr .r31 + BitVec.ofNat 64 cnO) 64), ?_,
    by rw [gpr_write_of_ne _ _ (by decide), gpr_write_self, h31]; rfl,
    by rw [gpr_write_self, h31, hcn], fun r h5 h6 => by rw [gpr_write_of_ne _ _ h6, gpr_write_of_ne _ _ h5],
    ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  simp only [bufO, cnO, runBlock_cons, runStep_some, runBlock_nil, exec_addi (show Reg.r31 ≠ .r0 by decide)
    (show 384 < 2 ^ 15 by decide), exec_load_d, gpr_write, rd_write, wr_write, mem_write, reduceCtorEq,
    ↓reduceIte, h31, r, ne_eq, not_false_eq_true, Nat.reduceLT, Nat.reducePow, Nat.reduceMod, and_self,
    Option.bind_some]

/-- The frame of the counts at `W + cnO` and `W + hlO`. -/
theorem frame_counts (m : Mem) (W : Addr) (v w : BitVec 64) :
    Frame [⟨W + BitVec.ofNat 64 296, 16⟩] m ((m.writeW (W + BitVec.ofNat 64 296) v).writeW (W + BitVec.ofNat 64 304) w) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_pre _ (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains W (e := 296) (k := 16) (d := 304) (n := 8) (by decide) (by decide)
      (by decide))

/-- After the number `c` of blocks of a chunk in `r25`: the counts stored, the
buffer's start in `r11`, and the fill loop before its first block. -/
theorem chunkMid_ok {V : Reg → BitVec 64} {sp : Addr} {D : Addr} {n R : Nat} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx (V .r29) (V .r31) D n R ciph l A a s₀) {t t₁ : State}
    {j c : Nat} (H : HInv V sp ciph l A a s₀ t j) (hc : c ≤ a.length / 16 - j)
    (g₁ : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r25 → t₁.gpr r = t.gpr r) (k₁ : Keeps t t₁)
    (h25 : t₁.gpr .r25 = BitVec.ofNat 64 c) :
    WP isa (.block [.store .d .r25 .r31 cnO, .load .d .r3 .r31 hlO, .sub .r3 .r3 .r25, .store .d .r3 .r31 hlO,
      .addi .r11 .r31 bufO]) t₁ fun t₂ => FillInv V sp ciph l A a s₀ j c t₂ 0 := by
  have L := C.lay
  have hs := C.short
  have h31 : t₁.gpr .r31 = V .r31 := by rw [g₁ _ (by decide) (by decide) (by decide), H.env.r31]
  have hw : Covers [⟨V .r31, 2560⟩] t₁.wr := by rw [k₁.wr]; exact H.env.perm.w
  have hl₁ : t₁.mem.readW (V .r31 + BitVec.ofNat 64 hlO) 64 = BitVec.ofNat 64 (a.length / 16 - j) := by
    rw [k₁.mem, H.hl]
  refine cwp_std (a := V .r31 + BitVec.ofNat 64 cnO) (by decide) (by decide) (by rw [h31])
    (in_off hw (by decide) (by decide)) fun t₂ u₂ => ?_
  refine cwp_ld (a := V .r31 + BitVec.ofNat 64 hlO) (by decide) (by decide) (by rw [u₂.gpr, h31])
    (by rw [u₂.rd, u₂.wr]; exact in_left (in_off hw (by decide) (by decide))) fun t₃ u₃ => cwp_sub fun t₄ u₄ => ?_
  have sep : Mem.Sep (V .r31 + BitVec.ofNat 64 hlO) (64 / 8) (V .r31 + BitVec.ofNat 64 cnO) (64 / 8) :=
    Offset.sep _ (by decide) (by decide) (by decide)
  have r3₄ : t₄.gpr .r3 = BitVec.ofNat 64 (a.length / 16 - j - c) := by
    rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.mem, u₂.gpr, h25, Mem.readW_writeW_sep sep (by decide), hl₁,
      Offset.ofNat_sub_ofNat hc]
  refine cwp_std (a := V .r31 + BitVec.ofNat 64 hlO) (by decide) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, h31])
    (by rw [u₄.wr, u₃.wr, u₂.wr]; exact in_off hw (by decide) (by decide)) fun t₅ u₅ => ?_
  refine cwp_addi (by decide) (by decide) fun t₆ u₆ => WP.block_nil ?_
  have m₆ : t₆.mem = (t.mem.writeW (V .r31 + BitVec.ofNat 64 296) (BitVec.ofNat 64 c)).writeW
      (V .r31 + BitVec.ofNat 64 304) (BitVec.ofNat 64 (a.length / 16 - j - c)) := by
    rw [u₆.mem, u₅.mem, r3₄, u₄.mem, u₃.mem, u₂.mem, h25, k₁.mem]; rfl
  have f₆ : Frame [⟨V .r31 + BitVec.ofNat 64 296, 16⟩] t.mem t₆.mem := by rw [m₆]; exact frame_counts _ _ _ _
  have kb : ∀ {d : Nat}, (d + 16 ≤ 296 ∨ 312 ≤ d) → d + 16 ≤ 2560 →
      blockAtMem t₆.mem (V .r31 + BitVec.ofNat 64 d) = blockAtMem t.mem (V .r31 + BitVec.ofNat 64 d) :=
    fun h₁ h₂ => blockAtMem_frame f₆ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega_arith) h₂ (by decide)
  have g₆ : ∀ r, r ∉ [.r3, .r4, .r11, .r25] → t₆.gpr r = t.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.2.1, u₅.gpr, u₄.other _ hr.1, u₃.other _ hr.1, u₂.gpr, g₁ r hr.1 hr.2.1 hr.2.2.2]
  have sep' : Mem.Sep (V .r31 + BitVec.ofNat 64 cnO) (64 / 8) (V .r31 + BitVec.ofNat 64 304) (64 / 8) :=
    Offset.sep _ (by decide) (by decide) (by decide)
  refine
    { env := H.env.others g₆ (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, k₁.sp])
        (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, k₁.rd]) (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, k₁.wr])
      frame := H.frame.trans (f₆.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact in_hashR (e := 296) (n := 16) (by simp) (by decide) (by decide))
      rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, k₁.rd, H.rd]
      wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, k₁.wr, H.wr]
      r24 := by rw [g₆ _ (by decide), H.r24]; rfl
      r26 := by rw [g₆ _ (by decide), H.r26]
      r11 := by rw [u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, h31]; rfl
      r25 := by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, h25]; rfl
      cn := by rw [m₆, Mem.readW_writeW_sep sep' (by decide)]; exact Mem.readW_writeW_self64 _ _ _
      hl := by rw [m₆, show V .r31 + BitVec.ofNat 64 hlO = V .r31 + BitVec.ofNat 64 304 from rfl,
        Mem.readW_writeW_self64, Nat.sub_sub]
      oh := by rw [kb (by simp only [ohO]; omega_arith) (by decide), H.oh]; rfl
      buf := fun k hk => absurd hk (Nat.not_lt_zero _)
      sum := by rw [kb (by simp only [sumO]; omega_arith) (by decide), H.sum]
      l0 := by rw [kb (by simp only [l0O]; omega_arith) (by decide), H.l0] }

/-- A doubleword of `W` below the buffer, after the call on the buffer's `c ≤ 8` blocks. -/
theorem bufCall_readW {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {K W : Addr} (L : Lay K W)
    {t t' : State} {K' : Addr} {R c : Nat} (P : BPost f t K' (W + BitVec.ofNat 64 384) (W + BitVec.ofNat 64 512) R c t')
    (hc : c ≤ 8) {d : Nat} (hd : d + 8 ≤ 384) :
    t'.mem.readW (W + BitVec.ofNat 64 d) 64 = t.mem.readW (W + BitVec.ofNat 64 d) 64 :=
  P.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)) (by decide)

/-- The buffer's start to `r11` and its `c` blocks (at `W + cnO`) to `r25`. -/
theorem sumArgs_ok {W : Addr} {t : State} (h31 : t.gpr .r31 = W) (hw : Covers [⟨W, 2560⟩] t.wr) {c : Nat}
    (hcn : t.mem.readW (W + BitVec.ofNat 64 cnO) 64 = BitVec.ofNat 64 c) :
    WP isa (.block [.addi .r11 .r31 bufO, .load .d .r25 .r31 cnO]) t fun t₅ =>
      t₅.gpr .r11 = W + BitVec.ofNat 64 384 ∧ t₅.gpr .r25 = BitVec.ofNat 64 c ∧
      (∀ r, r ≠ .r11 → r ≠ .r25 → t₅.gpr r = t.gpr r) ∧ Keeps t t₅ :=
  cwp_addi (by decide) (by decide) fun t₄ u₄ => cwp_ld (a := W + BitVec.ofNat 64 cnO)
    (by decide) (by decide) (by rw [u₄.other _ (by decide), h31])
    (by rw [u₄.rd, u₄.wr]; exact in_left (in_off hw (by decide) (by decide))) fun t₅ u₅ => WP.block_nil
    ⟨by rw [u₅.other _ (by decide), u₄.gpr, h31]; rfl, by rw [u₅.gpr, u₄.mem, hcn],
      fun r a b => by rw [u₅.other _ b, u₄.other _ a],
      ⟨by rw [u₅.mem, u₄.mem], by rw [u₅.rd, u₄.rd], by rw [u₅.wr, u₄.wr], by rw [u₅.sp, u₄.sp],
        by rw [u₅.lr, u₄.lr]⟩⟩

/-- A chunk from the fill loop on, with its `c` blocks at `W + cnO`. -/
theorem chunkRest_ok {V : Reg → BitVec 64} {sp : Addr} {D : Addr} {n R : Nat} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx (V .r29) (V .r31) D n R ciph l A a s₀)
    (h28 : V .r28 = BitVec.ofNat 64 R) {t : State} {j c : Nat} (F₀ : FillInv V sp ciph l A a s₀ j c t 0)
    (hc0 : 0 < c) (hc : c ≤ 8) (hjc : j + c ≤ a.length / 16) :
    WP isa (.seq (.loop hashFill (.nonzero .d .r25))
      (.seq (.block (callArgs ++ ([.addi .r5 .r31 bufO, .load .d .r6 .r31 cnO] : List Instr)))
      (.seq encCall
      (.seq (.block [.addi .r11 .r31 bufO, .load .d .r25 .r31 cnO])
      (.seq hashSum (.block [.load .d .r3 .r31 hlO])))))) t
      fun t' => HInv V sp ciph l A a s₀ t' (j + c) := by
  have L := C.lay
  have hs := C.short
  refine WP.seq (WP.mono (fill_ok C hc0 hc hjc F₀) fun t₂ F => ?_)
  refine WP.assoc (WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) L
    Proof.Aes.PPC64LE.encryptBlocks_correct encryptBlocks_noFrames C.rounds h28 F.env
    (fun s₁ g₁ k₁ => bufArgs_ok (by rw [g₁ _ (by decide) (by decide) (by decide), F.env.r31])
      (by rw [k₁.wr]; exact F.env.perm.w) (by rw [k₁.mem, F.cn]))
    (dstW L F.env.perm (d := 384) (n := c) (by omega_arith))) fun t₃ P₃ => ?_))
  have E₃ := P₃.env F.env
  have F₃ : Frame (hashR (V .r31)) t₂.mem t₃.mem := P₃.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact in_hashR (e := 384) (n := 2176) (by simp) (by decide) (by omega_arith)
    · exact in_hashR (e := 384) (n := 2176) (by simp) (by decide) (by decide)
  have k₃ : ∀ {d : Nat}, d + 16 ≤ 384 →
      blockAtMem t₃.mem (V .r31 + BitVec.ofNat 64 d) = blockAtMem t₂.mem (V .r31 + BitVec.ofNat 64 d) :=
    fun hd => blockAtMem_frame P₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  have kw₃ : ∀ {d : Nat}, d + 8 ≤ 384 →
      t₃.mem.readW (V .r31 + BitVec.ofNat 64 d) 64 = t₂.mem.readW (V .r31 + BitVec.ofNat 64 d) 64 := fun hd =>
    bufCall_readW L P₃ hc hd
  have hg : ∀ k < c, blockAtMem t₃.mem (V .r31 + BitVec.ofNat 64 (384 + 16 * k)) =
      ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1)) := fun k hk => by
    have := P₃.enc hk
    rw [Offset.add_add] at this
    rw [this, F.buf k hk]
    exact congrFun (C.ciph' (hashR_mut F.frame)) _
  have h31₃ := E₃.r31
  have hw₃ : Covers [⟨V .r31, 2560⟩] t₃.wr := E₃.perm.w
  have cn₃ : t₃.mem.readW (V .r31 + BitVec.ofNat 64 cnO) 64 = BitVec.ofNat 64 c := by
    rw [kw₃ (by decide), F.cn]
  have hB := sumArgs_ok h31₃ hw₃ cn₃
  refine WP.seq (WP.mono hB ?_)
  rintro t₅ ⟨r11₅, r25₅, g₅, k₅⟩
  have hg₅ : ∀ k < c, blockAtMem t₅.mem (V .r31 + BitVec.ofNat 64 (384 + 16 * k)) =
      ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1)) := fun k hk => by rw [k₅.mem, hg k hk]
  refine WP.seq (WP.mono (hashSum_ok L (by rw [g₅ _ (by decide) (by decide), h31₃]) (by rw [k₅.wr]; exact hw₃)
    hc0 hc r11₅ r25₅ hg₅) fun t₆ ⟨fr₆, sum₆, g₆, sp₆, lr₆, rd₆, wr₆⟩ => ?_)
  have h31₆ : t₆.gpr .r31 = V .r31 := by rw [g₆ _ (by decide), g₅ _ (by decide) (by decide), h31₃]
  have kb₆ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ 64 ≤ d) → d + 16 ≤ 2560 →
      blockAtMem t₆.mem (V .r31 + BitVec.ofNat 64 d) = blockAtMem t₃.mem (V .r31 + BitVec.ofNat 64 d) :=
    fun h₁ h₂ => by
      rw [blockAtMem_frame fr₆ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (a := _) (d := 48) (k := 16) (by omega_arith) h₂
          (by decide), k₅.mem]
  have hl₆ : t₆.mem.readW (V .r31 + BitVec.ofNat 64 hlO) 64 = BitVec.ofNat 64 (a.length / 16 - (j + c)) := by
    rw [fr₆.readW (r := ⟨V .r31 + BitVec.ofNat 64 hlO, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide), k₅.mem, kw₃ (by decide), F.hl]
  refine cwp_ld (a := V .r31 + BitVec.ofNat 64 hlO) (by decide) (by decide) (by rw [h31₆])
    (by rw [rd₆, wr₆, k₅.rd, k₅.wr]; exact in_left (in_off hw₃ (by decide) (by decide))) fun t₇ u₇ =>
    WP.block_nil ?_
  have g₇ : ∀ r, r ∉ [.r3, .r4, .r11, .r25] → t₇.gpr r = t₃.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₇.other _ hr.1, g₆ r (by simp [sumRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]), g₅ r hr.2.2.1 hr.2.2.2]
  refine
    { env := E₃.others g₇ (by rw [u₇.sp, sp₆, k₅.sp]) (by rw [u₇.rd, rd₆, k₅.rd]) (by rw [u₇.wr, wr₆, k₅.wr])
      frame := F.frame.trans (F₃.trans ((by rw [k₅.mem]; exact Frame.refl _ _ : Frame [] t₃.mem t₅.mem).mono
        (by simp) |>.trans ((fr₆.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact in_hashR (e := 48) (n := 16) (by simp) (by decide) (by decide)).trans
          ((by rw [u₇.mem]; exact Frame.refl _ _ : Frame [] t₆.mem t₇.mem).mono (by simp)))))
      rd := by rw [u₇.rd, rd₆, k₅.rd, P₃.rd, F.rd]
      wr := by rw [u₇.wr, wr₆, k₅.wr, P₃.wr, F.wr]
      le := by omega_arith
      sum := by rw [u₇.mem, sum₆, k₅.mem, k₃ (by decide), F.sum, hsum_add]
      oh := by rw [u₇.mem, kb₆ (by simp only [ohO]; omega_arith) (by decide), k₃ (by decide), F.oh]
      r24 := by rw [g₇ _ (by decide), P₃.saved _ (by decide), F.r24]
      r26 := by rw [g₇ _ (by decide), P₃.saved _ (by decide), F.r26]
      r3 := by rw [u₇.gpr, hl₆]
      hl := by rw [u₇.mem, hl₆]
      l0 := by rw [u₇.mem, kb₆ (by simp only [l0O]; omega_arith) (by decide), k₃ (by decide), F.l0] }

theorem hashChunk_ok {V : Reg → BitVec 64} {sp : Addr} {D : Addr} {n R : Nat} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx (V .r29) (V .r31) D n R ciph l A a s₀)
    (h28 : V .r28 = BitVec.ofNat 64 R) {t : State} {j : Nat} (H : HInv V sp ciph l A a s₀ t j)
    (hj : j < a.length / 16) :
    WP isa hashChunk t fun t' => HInv V sp ciph l A a s₀ t' (j + min 8 (a.length / 16 - j)) := by
  have hs := C.short
  unfold hashChunk
  refine WP.assoc (WP.seq (WP.mono (chunkHead_ok (L := a.length / 16 - j) H.env.r31 H.env.perm.w (by omega_arith) H.hl)
    fun t₁ ⟨h25, g₁, k₁⟩ => ?_))
  refine WP.seq (WP.mono (chunkMid_ok C H (by omega_arith) g₁ k₁ h25) fun t₂ F₀ => ?_)
  exact chunkRest_ok C h28 F₀ (by omega_arith) (by omega_arith) (by omega_arith)

end VG.Proof.AesOcb.PPC64LE
