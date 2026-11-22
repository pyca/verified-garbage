module

public import VerifiedGarbage.Proof.Seed.X86.AesNiWideMaps
public import VerifiedGarbage.Proof.Seed.X86.AesNiCore
public import VerifiedGarbage.Proof.Seed.Rounds
public import VerifiedGarbage.Spec.Seed.Cbc
public import VerifiedGarbage.Proof.Modes.X86.Core
public import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Seed.ModeBytes

/-!
# SEED's core by the AES S-box, four blocks at a time, on x86 (32-bit)

`coreSpec d`: `Impl.Seed.X86.AesNiWide.core d` meets what the modes need of
a core (`Proof.Modes.X86.CoreSpec`), with the key a schedule, read through
the first stack argument (the one-block core's `KeyArgs`), and its cipher
`Spec.Seed.cipher` for encryption and `Spec.Seed.invCipher` for decryption.

The proof is the one-block core's (`AesNiCore.lean`), a lane at a time: a
register holds a word of four blocks, block `l`'s in lane `l` (`Hw`,
`WordAt`). G's output at a byte is of the four bytes of its lane
(`AesNiWideMaps.g_all`), which `gsum_ok` shows is G of the lane's word, so
F and a round of the code are `Spec.Seed.f` and a round in every lane
(`fX_wp`, `round_ok`). `crypt_wp`: the four blocks at byte 608 of the
scratch buffer are replaced with `Spec.Seed.crypt` of them, under the round
keys in their places, in the order the rounds read them. `prepare_wp`:
`prepare d` leaves the schedule's round keys there in `d`'s order (`pos d`),
the rounds' in reverse for decryption, which is the specification's
decryption (RFC 4269 §2.4).
-/

@[expose] public section

namespace VG.Proof.Seed.X86.AesNiWide

open VG VG.X86 VG.X86.ByteMap VG.Impl.Seed.X86.AesNiWide
open VG.Impl.Seed.X86.AesNi (tbr kr m0)
open VG.Proof.Seed (byteOf maskOf sOf getLsbD_byteOf)
open VG.Spec.Seed (Word Direction)
open VG.Proof.Modes.X86 (ScrIn)
open VG.Proof.Seed.X86.AesNi (var kv maskOk keeps regs₀ byte_ofNat bv128_ext byteOf_eq byteOf_xor word_ext
  byteOf_g kb env_var keeps_ok mask_ok same_mem same_gpr same_zf same_rd same_wr same_syms wp_subi_x wp_addi_x
  wp_ldx wp_stx wp_xb sAt frame_sAt KeyAt)

/-! ## The byte maps -/

theorem and_xor (a b c : Byte) : (a ^^^ b) &&& c = (a &&& c) ^^^ (b &&& c) := Fn.lin_xor (g := .and c) rfl a b

/-- `sbox_all`, of a byte. -/
theorem sbox_ok (b : Byte) : am oP0 (aesSbox (pre b)) = sOf 0 b ∧
    am oP0 (aesSbox (pre b)) ^^^ am oD (aesSbox (pre b)) = sOf 1 b := by
  have h := List.all_eq_true.mp sbox_all b.toNat (List.mem_range.mpr b.isLt)
  rw [byte_ofNat, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  exact ⟨h.1.trans (Proof.Seed.sTable_getD false _).symm, h.2.trans (Proof.Seed.sTable_getD true _).symm⟩

/-! ## Words in registers -/

/-- The register `v` holds the words `X`: block `l`'s in lane `l`. -/
def Hw (v : BitVec 128) (X : Nat → Word) : Prop := ∀ q < 16, byte v q = byteOf (X (q / 4)) (q % 4)

theorem Hw.dw {v : BitVec 128} {X : Nat → Word} (h : Hw v X) {c : Nat} (hc : c < 4) : X86.dword v c = X c :=
  word_ext fun k hk => by
    have e := h (4 * c + k) (by omega_using [hc, hk])
    rw [byte_eq_dword, show (4 * c + k) / 4 = c by omega_arith, show (4 * c + k) % 4 = k by omega_arith] at e
    rw [byteOf_eq, e]

theorem Hw.of_dw {v : BitVec 128} {X : Nat → Word} (h : ∀ c < 4, X86.dword v c = X c) : Hw v X := fun q hq => by
  rw [byte_eq_dword, h _ (by omega_arith), byteOf_eq]

theorem Hw.paddd {a b : BitVec 128} {X Y : Nat → Word} (ha : Hw a X) (hb : Hw b Y) :
    Hw (XBinOp.eval .paddd a b) (fun l => X l + Y l) :=
  Hw.of_dw fun c hc => by rw [dword_paddd _ _ hc, ha.dw hc, hb.dw hc]

theorem Hw.pxor {a b : BitVec 128} {X Y : Nat → Word} (ha : Hw a X) (hb : Hw b Y) :
    Hw (a ^^^ b) (fun l => X l ^^^ Y l) :=
  fun q hq => by rw [byte_xor, ha q hq, hb q hq, byteOf_xor]

theorem Hw.congr {v : BitVec 128} {X Y : Nat → Word} (h : Hw v X) (he : ∀ l < 4, X l = Y l) : Hw v Y :=
  fun q hq => by rw [h q hq, he _ (by omega_arith)]

/-! ## G -/

/-- The S-box of byte `k` of the lane of `p`, of `aesenclast`'s input bytes
`w`, under its mask for the output byte `p`. -/
def kterm (w : Nat → Byte) (p k : Nat) : Byte :=
  (am oP0 (aesSbox (w (4 * (p / 4) + k))) &&& maskOf ((k + p % 4) % 4)) ^^^
    ((am oD (aesSbox (w (4 * (p / 4) + k))) &&& e1 k) &&& maskOf ((k + p % 4) % 4))

/-- G's output byte `p`: of the four bytes of its lane. -/
def gsum (w : Nat → Byte) (p : Nat) : Byte := kterm w p 0 ^^^ kterm w p 1 ^^^ kterm w p 2 ^^^ kterm w p 3

/-- A byte's term, when `aesenclast`'s input is the map before the S-box of
the bytes of the words `X`: the S-box of its place of the byte of the
lane's word, under its mask for the output byte. -/
theorem kterm_ok (X : Nat → Word) {w : Nat → Byte} (hw : ∀ p < 16, w p = pre (byteOf (X (p / 4)) (p % 4)))
    {p k : Nat} (hp : p < 16) (hk : k < 4) :
    kterm w p k = sOf k (byteOf (X (p / 4)) k) &&& maskOf ((k + p % 4) % 4) := by
  have e₁ : (4 * (p / 4) + k) / 4 = p / 4 := by omega_arith
  have e₂ : (4 * (p / 4) + k) % 4 = k := by omega_arith
  rw [kterm, hw _ (by omega_using [hp, hk]), e₁, e₂]
  obtain ⟨h0, h1⟩ := sbox_ok (byteOf (X (p / 4)) k)
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl
  · rw [show e1 0 = 0#8 from rfl, BitVec.and_zero, BitVec.zero_and, BitVec.xor_zero, h0]
  · rw [show e1 1 = BitVec.allOnes 8 from rfl, BitVec.and_allOnes, ← and_xor, h1]
  · rw [show e1 2 = 0#8 from rfl, BitVec.and_zero, BitVec.zero_and, BitVec.xor_zero, h0]; rfl
  · rw [show e1 3 = BitVec.allOnes 8 from rfl, BitVec.and_allOnes, ← and_xor, h1]; rfl

/-- The four terms are `G`'s byte. -/
theorem gsum_ok (X : Nat → Word) {w : Nat → Byte} (hw : ∀ p < 16, w p = pre (byteOf (X (p / 4)) (p % 4)))
    {p : Nat} (hp : p < 16) : gsum w p = byteOf (Spec.Seed.g (X (p / 4))) (p % 4) := by
  have hi : p % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [gsum, kterm_ok X hw hp (by decide), kterm_ok X hw hp (by decide), kterm_ok X hw hp (by decide),
    kterm_ok X hw hp (by decide), byteOf_g _ hi]

/-! ## What the parts of the code compute -/

/-- What a round needs of the state: the table's address in its register,
the scratch buffer's first 96 bytes, which end with the five places,
readable, and the mask. -/
structure Env (s : State) : Prop where
  tb : s.gpr tbr = s.syms tableName
  fit : (s.gpr Impl.Modes.X86.sb).toNat + 96 ≤ 2 ^ 32
  acc : ∀ o, o + 16 ≤ 96 → InRegions (s.rd ++ s.wr) (addr (s.gpr Impl.Modes.X86.sb) o) 16
  msk : ∀ i < 16, byte (s.xmm m0) i = 0x0f#8

section
variable {s s' : State} {ρ : Regs}

theorem Env.rel (h : Env s) : Rel params (envOf params s) regs₀ s :=
  (rel_init (p := params) h.tb h.fit h.acc).const m0 h.msk

theorem Env.same (h : Env s) (hs : Same s s') (hm : ∀ i < 16, byte (s'.xmm m0) i = 0x0f#8) : Env s' := by
  obtain ⟨f, rfl⟩ := hs
  exact ⟨h.tb, h.fit, h.acc, hm⟩

theorem env_key {o : Nat} (ho : o < 96) : mask (envOf params s) (kv o) nvars = kb s o := by
  rw [kv, mask_bit _ (by show 128 + o < 1024; omega_using [ho]), envOf_key]; rfl

/-- The two look-ups of the map before the S-box are the map. -/
theorem cterms_sum (env : Nat → BitVec 8) (v : Nat) : sum env (cterms v) = pre (mask env v nvars) := by
  simp only [cterms, sum, BitVec.xor_zero]; rfl

theorem aT_sum (env : Nat → BitVec 8) (t : Nat) (c : Byte) (q : Nat) :
    sum env (aT t c q) = am t (aesSbox (mask env (var .xmm1 q) nvars)) &&& c := by
  simp only [aT, sum, BitVec.xor_zero]
  exact (Fn.lin_xor (g := .and c) rfl _ _).symm

theorem dT_sum (env : Nat → BitVec 8) (c e : Byte) (q : Nat) :
    sum env (dT c e q) = (am oD (aesSbox (mask env (var .xmm1 q) nvars)) &&& e) &&& c := by
  simp only [dT, sum, BitVec.xor_zero]
  exact ((congrArg (· &&& c) (and_xor _ _ e)).trans (and_xor _ _ c)).symm

theorem gT_sum {p : Nat} (hp : p < 16) :
    sum (envOf params s) (gT p) = gsum (fun q => byte (s.xmm .xmm1) q) p := by
  have b : ∀ k < 4, 4 * (p / 4) + k < 16 := fun k hk => by omega_using [hp, hk]
  simp only [gT, kT, sum_append, aT_sum, dT_sum, gsum, kterm, env_var params .xmm1 (b 0 (by decide)),
    env_var params .xmm1 (b 1 (by decide)), env_var params .xmm1 (b 2 (by decide)),
    env_var params .xmm1 (b 3 (by decide))]

/-- `G`: the words in `xmm0` to `G` of each; `xmm5` is kept. -/
theorem g_wp (he : Env s) {X : Nat → Word} (hx : Hw (s.xmm .xmm0) X) :
    WP isa (.block g) s fun s' =>
      Same s s' ∧ Hw (s'.xmm .xmm0) (fun l => Spec.Seed.g (X l)) ∧ s'.xmm .xmm5 = s.xmm .xmm5 ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  have hpre := g_all.1
  unfold gPreOk at hpre
  split at hpre <;> [cases hpre; rename_i ρ₁ hrun₁]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hpre
  obtain ⟨⟨⟨p1, c1⟩, k5⟩, km⟩ := hpre
  have hpost := g_all.2
  unfold gPostOk at hpost
  split at hpost <;> [cases hpost; rename_i ρ₂ hrun₂]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hpost
  obtain ⟨⟨⟨p0, c0⟩, l5⟩, lm⟩ := hpost
  refine WP.block_append_iff.mpr (run_wp he.rel hrun₁ fun s₁ hr₁ same₁ => ?_)
  have m₁ := mask_ok hr₁ km
  have he₁ := he.same same₁ m₁
  have w₁ : ∀ p < 16, byte (s₁.xmm .xmm1) p = pre (byteOf (X (p / 4)) (p % 4)) := fun p hp => by
    rw [hr₁.bytes p1 p hp, BV.same_eval _ (List.all_eq_true.mp c1 p (List.mem_range.mpr hp)), BV.eval, mask_zero,
      cterms_sum, BitVec.zero_xor, BitVec.xor_zero, env_var params .xmm0 hp, hx p hp]
  refine run_wp he₁.rel hrun₂ fun s₂ hr₂ same₂ => ?_
  refine ⟨same₁.trans same₂, fun q hq => ?_, (keeps_ok hr₂ l5).trans (keeps_ok hr₁ k5), mask_ok hr₂ lm⟩
  rw [hr₂.bytes p0 q hq, BV.same_eval _ (List.all_eq_true.mp c0 q (List.mem_range.mpr hq)), BV.eval, mask_zero,
    gT_sum hq, BitVec.zero_xor, BitVec.xor_zero]
  exact gsum_ok X w₁ hq

end

end VG.Proof.Seed.X86.AesNiWide
