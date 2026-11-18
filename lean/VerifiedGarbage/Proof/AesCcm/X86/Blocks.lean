module

public import VerifiedGarbage.Proof.AesCcm.X86.Run
public import VerifiedGarbage.Proof.Cmac.Block32
public import VerifiedGarbage.Spec.Ccm
import VerifiedGarbage.Proof.AesCcm.X86.Callee
import VerifiedGarbage.Proof.AesGcm.X86.Cmp
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesGcm.X86.Flush
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.AesCcm.X86.Run
meta import VerifiedGarbage.Proof.Cmac.Block32
meta import VerifiedGarbage.Spec.Ccm
meta import VerifiedGarbage.Proof.AesCcm.X86.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86.Cmp
meta import VerifiedGarbage.Proof.AesCcm.BytesAt
meta import VerifiedGarbage.Proof.AesGcm.X86.Flush
meta import VerifiedGarbage.Proof.AesGcm.X86.Loops
meta import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.AesCcm.Words
import VerifiedGarbage.Proof.AesCcm.Bytes
public import VerifiedGarbage.Proof.Cmac.Mem32
public import VerifiedGarbage.Proof.AesCcm.Mac
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Proof.AesCcm.Words
meta import VerifiedGarbage.Proof.AesCcm.Bytes
meta import VerifiedGarbage.Proof.Cmac.Mem32
meta import VerifiedGarbage.Proof.AesCcm.Mac
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `AesCcm.Words32`, which this module and modules that import it used -/

section

/-!
# AES-CCM: blocks built of 32-bit words

Untrusted: everything here is checked by Lean. Target-independent facts for
code that builds AES-CCM's blocks from 32-bit words, as the x86 code does: a
word written into a buffer replaces four of its bytes
(`bytesAt_writeW32_at`); a byte-reversed number is its big-endian bytes
(`le4_byteRev32_ofNat`); the last word of `Ctrᵢ` (A.3) is that of `Ctr₀`
ORed with `[i]₃₂` (`ctr_or32`); and the encodings of the lengths of the
associated data less than 2³² (A.2.2), and the flags of `B₀` (A.2.1), as
the 32-bit code computes them.
-/

@[expose] public section

namespace VG.Proof.AesCcm

open VG VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4)

/-- The bytes of a buffer after a write that misses it. -/
theorem bytesAt_writeW_sep (m : Mem) {q a : Addr} {w n : Nat} (v : BitVec w)
    (h : (⟨q, n⟩ : Region).Disjoint ⟨a, w / 8⟩) (hn : n ≤ 2 ^ 64) : bytesAt (m.writeW a v) q n = bytesAt m q n :=
  Proof.Cmac.bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) v (Region.contains_self _ _))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h) hn

/-- The four bytes of a word just written. -/
theorem bytesAt_writeW32_self (m : Mem) (p : Addr) (v : BitVec 32) : bytesAt (m.writeW p v) p 4 = le4 v := by
  rw [bytesAt_writeW32_base _ _ _ (by decide) (by decide), List.drop_eq_nil_of_le (by rw [length_bytesAt]),
    List.append_nil]

/-- `B₀` as the x86 code builds it: the first three words of `Ctr₀`, the
flags over its first byte, then the last word. -/
theorem b0_bytes (m : Mem) (p : Addr) (w₀ w₁ w₂ x : BitVec 32) (f : Byte) :
    bytesAt (((((m.writeW p w₀).writeW (p + BitVec.ofNat 64 4) w₁).writeW (p + BitVec.ofNat 64 8) w₂).writeW p f).writeW
      (p + BitVec.ofNat 64 12) x) p 16 = (f :: (le4 w₀).drop 1) ++ le4 w₁ ++ le4 w₂ ++ le4 x := by
  have dj : ∀ a n d k, a + n ≤ d ∨ d + k ≤ a → a + n ≤ 16 → d + k ≤ 16 →
      (⟨p + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 d, k⟩ :=
    fun a n d k h ha hd => Offset.disjoint p h (by omega_using [ha]) (by omega_using [hd])
  have d0 : ∀ d k, 4 ≤ d → d + k ≤ 16 → (⟨p, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 d, k⟩ := fun d k h hd => by
    simpa using dj 0 4 d k (.inl h) (by decide) hd
  have d0' : ∀ a n, 1 ≤ a → a + n ≤ 16 → (⟨p + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨p, 8 / 8⟩ := fun a n h ha => by
    simpa using dj a n 0 1 (.inr h) ha (by decide)
  rw [Cmac.bytesAt_split4]
  rw [bytesAt_writeW_sep _ _ (d0 12 4 (by decide) (by decide)) (by decide), bytesAt_writeW8_base _ _ _ (by decide)
      (by decide), bytesAt_writeW_sep _ _ (d0 8 4 (by decide) (by decide)) (by decide),
    bytesAt_writeW_sep _ _ (d0 4 4 (by decide) (by decide)) (by decide), bytesAt_writeW32_self,
    bytesAt_writeW_sep _ _ (dj 4 4 12 4 (.inl (by decide)) (by decide) (by decide)) (by decide),
    bytesAt_writeW_sep _ _ (d0' 4 4 (by decide) (by decide)) (by decide),
    bytesAt_writeW_sep _ _ (dj 4 4 8 4 (.inl (by decide)) (by decide) (by decide)) (by decide), bytesAt_writeW32_self,
    bytesAt_writeW_sep _ _ (dj 8 4 12 4 (.inl (by decide)) (by decide) (by decide)) (by decide),
    bytesAt_writeW_sep _ _ (d0' 8 4 (by decide) (by decide)) (by decide), bytesAt_writeW32_self, bytesAt_writeW32_self]

/-- The bytes of `[v]₃₂`, the most significant first. -/
theorem le4_byteRev32_ofNat {v : Nat} (hv : v < 2 ^ 32) : le4 (byteRev32 (BitVec.ofNat 32 v)) = Spec.Ccm.be 4 v := by
  rw [le4, byteRev32_extract, Spec.Ccm.be, show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hv]

/-- The last 4 bytes of `Ctrᵢ`, for `i < 2³²`: `[i]₃₂`, ORed with those of
`Ctr₀` (the nonce's last bytes, when `q < 4`). -/
theorem ctrBlock_drop12_or {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13) {i : Nat}
    (hi : i < 256 ^ (15 - nonce.length)) (hi32 : i < 2 ^ 32) :
    (Spec.Ccm.ctrBlock nonce i).drop 12 =
      List.zipWith (· ||| ·) (Spec.Ccm.be 4 i) ((Spec.Ccm.ctrBlock nonce 0).drop 12) := by
  simp only [Spec.Ccm.ctrBlock, List.cons_append, List.drop_succ_cons]
  rcases Nat.lt_or_ge nonce.length 11 with h | h
  · -- `q > 4`: the last 4 bytes are those of `[i]₈q`.
    simp only [List.drop_append, List.drop_eq_nil_of_le (show nonce.length ≤ 11 by omega),
      List.nil_append, be_zero]
    rw [be_split (q := 4) (k := 15 - nonce.length) (by omega_using [h]) (by omega_using [hi32]), Spec.Ccm.zeros, Spec.Ccm.zeros,
      List.drop_append, List.drop_replicate, List.length_replicate, List.drop_replicate,
      show 15 - nonce.length - 4 - (11 - nonce.length) = 0 by omega_using [], List.replicate_zero, List.nil_append,
      show 11 - nonce.length - (15 - nonce.length - 4) = 0 by omega_using [], List.drop_zero,
      show 15 - nonce.length - (11 - nonce.length) = 4 by omega_using [h]]
    exact (zipWith_or_zeros_right _ (length_be 4 i)).symm
  · -- `q ≤ 4`: the nonce's last bytes, then `[i]₈q`.
    rw [List.drop_append_of_le_length h, List.drop_append_of_le_length h, be_zero,
      be_split (q := 15 - nonce.length) (k := 4) (by omega_using [h]) hi]
    have hd : (nonce.drop 11).length = 4 - (15 - nonce.length) := by rw [List.length_drop]; omega_using [h13]
    rw [List.zipWith_append (by rw [hd]; simp [Spec.Ccm.zeros]), zipWith_or_zeros_left _ hd,
      zipWith_or_zeros_right _ (length_be _ _)]

/-- The first 12 bytes of `Ctrᵢ`, for `i < 2³²`, are those of `Ctr₀`. -/
theorem ctrBlock_take12 {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13) {i : Nat}
    (hi32 : i < 2 ^ 32) : (Spec.Ccm.ctrBlock nonce i).take 12 = (Spec.Ccm.ctrBlock nonce 0).take 12 := by
  simp only [Spec.Ccm.ctrBlock, List.cons_append, List.take_succ_cons, List.cons.injEq, true_and]
  rcases Nat.lt_or_ge nonce.length 11 with h | h
  · simp only [List.take_append, List.take_of_length_le (show nonce.length ≤ 11 by omega)]
    congr 1
    rw [be_zero, be_split (q := 4) (k := 15 - nonce.length) (by omega_using [h]) (by omega_using [hi32]), Spec.Ccm.zeros, Spec.Ccm.zeros,
      List.take_append, List.take_replicate, List.take_replicate, List.length_replicate,
      show 11 - nonce.length - (15 - nonce.length - 4) = 0 by omega_using [], List.take_zero, List.append_nil,
      Nat.min_eq_left (show 11 - nonce.length ≤ 15 - nonce.length - 4 by omega_using []),
      Nat.min_eq_left (show 11 - nonce.length ≤ 15 - nonce.length by omega_using [])]
  · rw [List.take_append_of_le_length h, List.take_append_of_le_length h]

/-- `Ctrᵢ`'s last word, from `Ctr₀`'s and `[i]₃₂`. -/
theorem ctr_or32 {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13) {w : BitVec 32}
    (hw : le4 w = (Spec.Ccm.ctrBlock nonce 0).drop 12) {i : Nat} (hi : i < 256 ^ (15 - nonce.length))
    (hi32 : i < 2 ^ 32) :
    le4 (byteRev32 (BitVec.ofNat 32 i) ||| w) = (Spec.Ccm.ctrBlock nonce i).drop 12 := by
  rw [le4_or, le4_byteRev32_ofNat hi32, hw, ctrBlock_drop12_or h7 h13 hi hi32]

/-! ## The encoding of the length of the associated data (A.2.2) -/

theorem le4_feff : le4 (BitVec.ofNat 32 0xfeff) = [0xff, 0xfe] ++ Spec.Ccm.zeros 2 := by decide

/-- A right shift by whole bytes drops the low bytes. -/
theorem le4_ushiftRight (x : BitVec 32) {k : Nat} (hk : k ≤ 4) :
    le4 (x >>> (8 * k)) = (le4 x).drop k ++ Spec.Ccm.zeros k := by
  have hl : ((le4 x).drop k).length = 4 - k := by rw [List.length_drop, Proof.Cmac.length_le4]
  have hlen : (le4 (x >>> (8 * k))).length = ((le4 x).drop k ++ Spec.Ccm.zeros k).length := by
    rw [Proof.Cmac.length_le4, List.length_append, hl, Spec.Ccm.zeros, List.length_replicate]
    omega_using [hk]
  apply List.ext_getElem hlen
  intro i h₁ h₂
  have hi : i < 4 := by rwa [Proof.Cmac.length_le4] at h₁
  by_cases h : i < 4 - k
  · rw [List.getElem_append_left (by rw [hl]; exact h), List.getElem_drop]
    simp only [le4, List.getElem_map, List.getElem_range]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      ← Nat.pow_add]
    rw [show 8 * k + 8 * i = 8 * (k + i) by omega_using []]
  · rw [List.getElem_append_right (by rw [hl]; omega_using [h])]
    simp only [Spec.Ccm.zeros, List.getElem_replicate, le4, List.getElem_map, List.getElem_range]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      ← Nat.pow_add]
    rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega_using [h])))]
    rfl

/-- `[a]₁₆`, from `[a]₃₂` shifted right by 16, followed by zeros. -/
theorem enc_lo32 {a : Nat} (h : a < 2 ^ 16 - 2 ^ 8) :
    le4 (byteRev32 (BitVec.ofNat 32 a) >>> 16) ++ Spec.Ccm.zeros 12 =
      Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - hdrLen a) := by
  rw [show byteRev32 (BitVec.ofNat 32 a) >>> 16 = byteRev32 (BitVec.ofNat 32 a) >>> (8 * 2) from rfl,
    le4_ushiftRight _ (by decide), le4_byteRev32_ofNat (by omega_using [h]), be_split (q := 2) (by decide) (by omega_using [h]),
    encodeLen_lo h, hdrLen_lo h]
  simp [Spec.Ccm.zeros]

/-- `0xff ‖ 0xfe ‖ [a]₃₂`, written over zeros. -/
theorem enc_mid32 {a : Nat} (h₁ : ¬ a < 2 ^ 16 - 2 ^ 8) (h₂ : a < 2 ^ 32) :
    (le4 (BitVec.ofNat 32 0xfeff) ++ Spec.Ccm.zeros 12).take 2 ++ le4 (byteRev32 (BitVec.ofNat 32 a)) ++
        (le4 (BitVec.ofNat 32 0xfeff) ++ Spec.Ccm.zeros 12).drop (2 + 4) =
      Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - hdrLen a) := by
  rw [le4_feff, le4_byteRev32_ofNat h₂, encodeLen_mid h₁ h₂, hdrLen_mid h₁ h₂]
  simp [Spec.Ccm.zeros, List.replicate]

/-! ## The flags of `B₀` (A.2.1) -/

theorem flags_val32 {tl nl al : Nat} (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) :
    ((BitVec.ofNat 32 (4 * (tl - 2) + (14 - nl) + if al = 0 then 0 else 64)).setWidth 8 : Byte) =
      Spec.Ccm.flags tl (15 - nl) al := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Spec.Ccm.flags]
  by_cases h : al = 0
  · subst h; simp only [ite_true, Nat.add_zero, show ¬ (0 > 0) by omega, ite_false, Nat.zero_add]; omega
  · simp only [h, ite_false, show al > 0 by omega, ite_true]; omega

/-- The first byte of `Ctr₀`, `q − 1 = 14 − n`. -/
theorem sub_low_byte32 {nl : Nat} (h : nl ≤ 14) :
    ((BitVec.ofNat 32 14 - BitVec.ofNat 32 nl).setWidth 8 : Byte) = BitVec.ofNat 8 (15 - nl - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_using [h]

end VG.Proof.AesCcm

end

end

/-!
# AES-CCM on x86: `Ctr₀`, counter blocks and chaining a block

Untrusted: everything here is checked by Lean. `ctrs` zeroes the block at
`W + 48`, writes `q − 1 = 14 − n` to its first byte and copies the nonce
after it: `Ctr₀` (`ctrs_ok`). `ctrAt` makes `Ctrᵢ` at `W + 64` from `Ctr₀`
(`ctrAt_ok`); `updBlock y` chains the block `B` at `W + 32` into the MAC
state at `W + y` (`updBlock_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop zero4)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 slotv LoopPre CopyPost copyLoop_ok zero4_fold zero4_bytes'
  length_bytesAt CT)

/-! ## `Ctr₀` -/

/-- `ctrs`'s block: `Ctr₀`'s first byte, and the copy's arguments. -/
theorem ctrsBlk_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {N : BitVec 32} {nl : Nat}
    (hNp : slotv s.mem W nonceO = N) (hnl : slotv s.mem W nlenO = BitVec.ofNat 32 nl) (h13 : nl ≤ 13) :
    ∃ s₁, runBlock isa
      (zero4 c0O ++ ([.mov .eax (imm 14), .alu .sub .eax (slot nlenO), .store8 (at_ .ebp c0O) .al,
        .mov .edi (slot nonceO), .mov .edx (.reg .ebp), .alu .add .edx (imm (c0O + 1)), .mov .ecx (slot nlenO)] : List Instr)) s =
        some s₁ ∧
      s₁.mem = (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 48)).writeW (w64 W + BitVec.ofNat 64 48)
        (BitVec.ofNat 8 (15 - nl - 1)) ∧
      s₁.gpr .edi = N ∧ s₁.gpr .edx = W + BitVec.ofNat 32 49 ∧ s₁.gpr .ecx = BitVec.ofNat 32 nl ∧
      s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have hz := zero4_fold s.mem W 48
  simp only [Nat.reduceAdd] at hz
  have hb := sub_low_byte32 (show nl ≤ 14 by omega_using [h13])
  refine ⟨_, by crun [zero4, E.ebp, L.aW, E.perm.wW, E.perm.wR, hnl, hNp], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hz, hb]
  · cregs [hNp]
  · cregs [E.ebp]
  · cregs [hnl]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals rfl

/-- `Ctr₀`, from the nonce `N` of `nl` bytes. -/
theorem ctrs_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {N : BitVec 32} {nl : Nat}
    (hNp : slotv s.mem W nonceO = N) (hnl : slotv s.mem W nlenO = BitVec.ofNat 32 nl) (hN : Buf W SP s N nl)
    (h7 : 7 ≤ nl) (h13 : nl ≤ 13) :
    WP isa ctrs s fun s' => Env K W SP s' ∧ Frame [⟨w64 W + BitVec.ofNat 64 48, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, hm₁, hdi, hdx, hcx, hbp, hsp, hrd₁, hwr₁⟩ := ctrsBlk_ok L E hNp hnl h13
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : Env K W SP s₁ := E.keep (by rw [hbp, E.ebp]) (by rw [hsp, E.esp]) hrd₁ hwr₁
  have a49 : w64 (W + BitVec.ofNat 32 49) = w64 W + BitVec.ofNat 64 49 := L.aW (by decide)
  have dNW : (⟨w64 N, nl⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 49, nl⟩ :=
    hN.w.sub_right (Lay.wSub (by omega_using [h13]))
  have lp : LoopPre s₁ N (W + BitVec.ofNat 32 49) nl :=
    ⟨hdi, hdx, hcx, by omega_using [h7], by omega_using [h13], hN.wrap, by rw [L.nW (by decide)]; have := L.fw; omega_using [h13, this],
      by rw [hrd₁, hwr₁]; exact hN.rd, by rw [a49]; exact E₁.perm.wC (by omega_using [h13]), by rw [a49]; exact dNW⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s₂ P => ?_
  have hfz : Frame [⟨w64 W + BitVec.ofNat 64 48, 16⟩] s.mem s₁.mem := by
    rw [hm₁]
    exact (Cmac.frame_store4 _ _ _ _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 48) (n := 1) (e := 48) (k := 16) (by decide) (by decide) (by decide))
  have hNs : bytesAt s₁.mem (w64 N) nl = bytesAt s.mem (w64 N) nl :=
    Proof.AesGcm.X86.bytesAt_frame hfz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hN.w.sub_right (Lay.wSub (by decide))) (by have := hN.lt; omega_using [h13])
  refine ⟨E₁.keep (by rw [P.other _ (by decide) (by decide) (by decide) (by decide)])
      (by rw [P.other _ (by decide) (by decide) (by decide) (by decide)]) P.rd P.wr, ?_, ?_,
    by rw [P.rd, hrd₁], by rw [P.wr, hwr₁]⟩
  · refine hfz.trans ?_
    rw [P.mem, a49]
    exact writeBytes_frame _ _ _ (by
      rw [length_bytesAt]
      exact Offset.contains (w64 W) (d := 49) (n := nl) (e := 48) (k := 16) (by decide) (by omega_using [h13]) (by decide))
  · -- The bytes of the block.
    have hz' : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 48) 16 = BitVec.ofNat 8 (15 - nl - 1) :: Spec.Ccm.zeros 15 := by
      rw [hm₁, bytesAt_writeW8_base _ _ _ (by decide) (by decide), zero4_bytes']
      rfl
    have hl := length_bytesAt s.mem (w64 N) nl
    rw [P.mem, a49, show w64 W + BitVec.ofNat 64 49 = w64 W + BitVec.ofNat 64 48 + BitVec.ofNat 64 1 by
        rw [add_ofNat_assoc],
      bytesAt_writeBytes_at _ _ _ (by rw [length_bytesAt]; omega_using [h13]) (by decide), length_bytesAt, hz', hNs,
      Spec.Ccm.ctrBlock, hl, be_zero, show 1 + nl = nl + 1 by omega_using []]
    simp only [Spec.Ccm.zeros, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_replicate,
      List.cons_append, List.nil_append]

/-! ## `ctrAt` -/

/-- Four words stored at `p + 64` (`Cmac.store4`), as the code stores them. -/
theorem store4_fold (m : Mem) (p : Addr) (d : Nat) (a b c e : BitVec 32) :
    (((m.writeW (p + BitVec.ofNat 64 d) a).writeW (p + BitVec.ofNat 64 (d + 4)) b).writeW
      (p + BitVec.ofNat 64 (d + 8)) c).writeW (p + BitVec.ofNat 64 (d + 12)) e =
      Cmac.store4 m (p + BitVec.ofNat 64 d) a b c e := by
  simp only [Cmac.store4, add_ofNat_assoc]

/-- A block as its four words. -/
theorem bytesAt_words (m : Mem) (p : Addr) (d : Nat) :
    bytesAt m (p + BitVec.ofNat 64 d) 16 = le4 (m.readW (p + BitVec.ofNat 64 d) 32) ++
      le4 (m.readW (p + BitVec.ofNat 64 (d + 4)) 32) ++ le4 (m.readW (p + BitVec.ofNat 64 (d + 8)) 32) ++
      le4 (m.readW (p + BitVec.ofNat 64 (d + 12)) 32) := by
  rw [Cmac.bytesAt_split4, add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW]

/-- `Ctrᵢ` at `W + 64`, for `i` in `eax`. -/
theorem ctrAt_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {nonce : List Byte}
    (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {i : Nat}
    (hi : i < 256 ^ (15 - nonce.length)) (hi32 : i < 2 ^ 32) (hax : s.gpr .eax = BitVec.ofNat 32 i) :
    ∃ s', runBlock isa ctrAt s = some s' ∧ Frame [⟨w64 W + BitVec.ofNat 64 64, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce i ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hf := store4_fold s.mem (w64 W) 64 (s.mem.readW (w64 W + BitVec.ofNat 64 48) 32)
    (s.mem.readW (w64 W + BitVec.ofNat 64 52) 32) (s.mem.readW (w64 W + BitVec.ofNat 64 56) 32)
    (bswap (BitVec.ofNat 32 i) ||| s.mem.readW (w64 W + BitVec.ofNat 64 60) 32)
  simp only [Nat.reduceAdd] at hf
  obtain ⟨s', run, hm, hg, hrd, hwr⟩ : ∃ s', runBlock isa ctrAt s = some s' ∧
      s'.mem = Cmac.store4 s.mem (w64 W + BitVec.ofNat 64 64) (s.mem.readW (w64 W + BitVec.ofNat 64 48) 32)
        (s.mem.readW (w64 W + BitVec.ofNat 64 52) 32) (s.mem.readW (w64 W + BitVec.ofNat 64 56) 32)
        (bswap (BitVec.ofNat 32 i) ||| s.mem.readW (w64 W + BitVec.ofNat 64 60) 32) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine ⟨_, by crun [ctrAt, E.ebp, L.aW, E.perm.wW, E.perm.wR], ?_, ?_, ?_, ?_⟩
    · cmems [hax, hf]
    · intro r a b; cregs [a, b]
    all_goals rfl
  refine ⟨s', run, by rw [hm]; exact Cmac.frame_store4 _ _ _ _ _, ?_, hg, hrd, hwr⟩
  have e := bytesAt_words s.mem (w64 W) 48
  simp only [Nat.reduceAdd] at e
  rw [hc0] at e
  have l12 : (le4 (s.mem.readW (w64 W + BitVec.ofNat 64 48) 32) ++ le4 (s.mem.readW (w64 W + BitVec.ofNat 64 52) 32) ++
      le4 (s.mem.readW (w64 W + BitVec.ofNat 64 56) 32)).length = 12 := by
    simp only [List.length_append, Proof.Cmac.length_le4]
  have hw : le4 (s.mem.readW (w64 W + BitVec.ofNat 64 60) 32) = (Spec.Ccm.ctrBlock nonce 0).drop 12 := by
    rw [e, List.drop_left' l12]
  rw [hm, Cmac.bytesAt_store4, show bswap (BitVec.ofNat 32 i) = byteRev32 (BitVec.ofNat 32 i) from rfl,
    ctr_or32 h7 h13 hw hi hi32]
  conv => rhs; rw [← List.take_append_drop 12 (Spec.Ccm.ctrBlock nonce i)]
  rw [ctrBlock_take12 h7 h13 hi32, e, List.take_left' l12]

/-! ## Chaining `B` -/

/-- The arguments of `updBlock y`'s call. -/
theorem updBlockArgs_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hK : slotv s.mem W ctxO = K) (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R) (y : Nat) :
    ∃ s₁, runBlock isa (keyArgs y ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm blkO), .mov .esi (imm 1)] : List Instr) ++ updScr) s =
      some s₁ ∧ s₁.mem = s.mem ∧ s₁.gpr .eax = K ∧ s₁.gpr .ecx = BitVec.ofNat 32 R ∧
      s₁.gpr .edx = W + BitVec.ofNat 32 y ∧ s₁.gpr .ebx = W + BitVec.ofNat 32 32 ∧ s₁.gpr .esi = BitVec.ofNat 32 1 ∧
      s₁.gpr .edi = W + BitVec.ofNat 32 384 ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  refine ⟨_, by crun [keyArgs, updScr, E.ebp, L.aW, E.perm.wR, hK, hRo], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · cregs [hK]
  · cregs [hRo]
  · cregs [E.ebp]
  · cregs [E.ebp]
  · cregs []
  · cregs [E.ebp]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals rfl

/-- `B` (at `W + 32`) chained into the MAC state at `W + y`. -/
theorem updBlock_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hK : slotv s.mem W ctxO = K) (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (updBlock v.callee v.suffix y) s fun s' => Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨w64 W + BitVec.ofNat 64 y, 16⟩, ⟨w64 W + BitVec.ofNat 64 384, 2176⟩, below SP 60] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16)
          [bytesAt s.mem (w64 W + BitVec.ofNat 64 32) 16] := by
  obtain ⟨s₁, run₁, hm₁, hax, hcx, hdx, hbx, hsi, hdi, hbp, hsp, hrd₁, hwr₁⟩ := updBlockArgs_ok L E hK hRo y
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : Env K W SP s₁ := E.keep (by rw [hbp, E.ebp]) (by rw [hsp, E.esp]) hrd₁ hwr₁
  have hq := srcW (s := s₁) L E₁.perm (t := 32) (k := 16 * 1) (by decide)
  have hqy : (⟨w64 (W + BitVec.ofNat 32 32), 16 * 1⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩ := by
    rw [L.aW (o := 32) (by decide)]
    rcases hy with rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  refine WP.mono (updCall_ok v L E₁ hR (by omega_using [hy]) hq hqy (by decide) hax hcx hdx hbx hsi hdi)
    fun s₂ ⟨E₂, rd₂, wr₂, _, f₂, o₂⟩ => ⟨E₂, by rw [rd₂, hrd₁], by rw [wr₂, hwr₁], by rw [← hm₁]; exact f₂, ?_⟩
  rw [o₂, Proof.Cmac.Stream.blocksAt_eq, Nat.mul_one, Proof.Cmac.Stream.blocks_single
    (Proof.Cmac.bytesAt_length _ _ _), hm₁, L.aW (o := 32) (by decide)]

/-- `updBlock y` is constant time. -/
theorem updBlock_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) {I : State → Prop}
    (hI : ∀ s, I s → Env K W SP s ∧ slotv s.mem W ctxO = K ∧ slotv s.mem W roundsO = BitVec.ofNat 32 R) :
    CT I (updBlock v.callee v.suffix y) := by
  have hqy : (⟨w64 (W + BitVec.ofNat 32 32), 16 * 1⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩ := by
    rw [L.aW (o := 32) (by decide)]
    rcases hy with rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  refine CT.seq (J := fun s₁ => ∃ s, I s ∧ s₁.mem = s.mem ∧ s₁.gpr .eax = K ∧ s₁.gpr .ecx = BitVec.ofNat 32 R ∧
      s₁.gpr .edx = W + BitVec.ofNat 32 y ∧ s₁.gpr .ebx = W + BitVec.ofNat 32 32 ∧ s₁.gpr .esi = BitVec.ofNat 32 1 ∧
      s₁.gpr .edi = W + BitVec.ofNat 32 384 ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr)
    (by
      have hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.ebp], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [(hI _ h₁).1.ebp, (hI _ h₂).1.ebp]
      rcases hy with rfl | rfl
      · exact CT.taint [.ebp] hr (by taint_decide)
      · exact CT.taint [.ebp] hr (by taint_decide))
    (fun s hs => by
      obtain ⟨E, hK, hRo⟩ := hI s hs
      obtain ⟨s₁, run₁, h⟩ := updBlockArgs_ok L E hK hRo y
      exact WP.of_runBlock ⟨s₁, run₁, s, hs, h⟩) ?_
  refine updCall_ct v L hR (y := y) (Q := W + BitVec.ofNat 32 32) (n := 1)
    (by rcases hy with rfl | rfl <;> decide) (by decide) fun s₁ ⟨s, hs, _, ax, cx, dx, bx, si, di, bp, sp, rd, wr⟩ => ?_
  have E₁ : Env K W SP s₁ := ⟨bp, sp, (hI s hs).1.perm.of_eq rd wr⟩
  exact ⟨E₁, srcW L E₁.perm (by decide), hqy, ax, cx, dx, bx, si, di⟩

/-- `ctrs` is constant time. -/
theorem ctrs_ct {K W SP : BitVec 32} (L : Lay K W SP) {N : BitVec 32} {nl : Nat} (h13 : nl ≤ 13) {I : State → Prop}
    (hI : ∀ s, I s → Env K W SP s ∧ slotv s.mem W nonceO = N ∧ slotv s.mem W nlenO = BitVec.ofNat 32 nl) :
    CT I ctrs :=
  CT.block_seq [.ebp] (pin_ebp fun s h => (hI s h).1.ebp) (by taint_decide)
    (fun s hs => ctrsBlk_ok L (hI s hs).1 (hI s hs).2.1 (hI s hs).2.2 h13)
    (Proof.AesGcm.X86.copyLoop_ct (pin3 fun _ ⟨_, _, _, hdi, hdx, hcx, _⟩ => ⟨hdi, hdx, hcx⟩))

end VG.Proof.AesCcm.X86
