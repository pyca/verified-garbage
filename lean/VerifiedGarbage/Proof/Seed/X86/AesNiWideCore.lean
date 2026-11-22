module

public import VerifiedGarbage.Proof.Seed.X86.AesNiWideMaps
public import VerifiedGarbage.Proof.Seed.X86.AesNiCore
public import VerifiedGarbage.Proof.Seed.Rounds
public import VerifiedGarbage.Spec.Seed.Cbc
public import VerifiedGarbage.Proof.Modes.X86.Core
public import VerifiedGarbage.Proof.Framework.X86.SymFrame
public import VerifiedGarbage.Proof.Seed.ModeBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Seed.Memory

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
  wp_ldx wp_stx wp_xb sAt frame_sAt KeyAt byteOf_wordAt blockAt_getD rkAt byteOf_rkAt Sch)

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

/-! ## Single instructions -/

section
variable {is : List Instr} {Q : State → Prop} {s : State}

/-- `movdqu [b + o], r`, to writable bytes: only the memory changes. -/
theorem wp_stx' {b : Reg} {o : Nat} {r : XReg} (hin : InRegions s.wr (addr (s.gpr b) o) 16)
    (k : ∀ s', s'.gpr = s.gpr → s'.xmm = s.xmm → s'.zf = s.zf → s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms →
      s'.mem = s.mem.writeW (addr (s.gpr b) o) (s.xmm r) → WP isa (.block is) s' Q) :
    WP isa (.block (.movdquStore ⟨b, o⟩ r :: is)) s Q :=
  wp_stx hin (k _ rfl rfl rfl rfl rfl rfl rfl)

/-- `movdqu d, [b + o]`, of readable bytes: only `d` changes. -/
theorem wp_ldx' {d : XReg} {b : Reg} {o : Nat} (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr b) o) 16)
    (k : ∀ s', Same s s' → s'.xmm d = s.mem.readW (addr (s.gpr b) o) 128 → (∀ r, ¬r = d → s'.xmm r = s.xmm r) →
      WP isa (.block is) s' Q) : WP isa (.block (.movdquLoad d ⟨b, o⟩ :: is)) s Q :=
  wp_ldx hin (k _ ⟨_, rfl⟩ (RegUpd.xmm_setXmm_self s d _) fun _ hr => RegUpd.xmm_setXmm_of_ne s _ hr)

end

/-! ## F -/

section
variable {s : State} {B : BitVec 32}

/-- F (§2.1) of `A` in `xmm5` and `B` in `xmm0`, in every lane:
`C = G(A ⊕ B)`, `D = G(C + A)`, `E = G(D + C)`; `E + D` to `xmm5` and `E`
to `xmm0`. `C` waits in its place, at byte 80 of the scratch buffer. -/
theorem fX_wp (he : Env s) (hB : s.gpr Impl.Modes.X86.sb = B) (hf : B.toNat + 96 ≤ 2 ^ 32)
    (hwr : InRegions s.wr (addr B 80) 16) {A Bw : Nat → Word} (ha : Hw (s.xmm .xmm5) A)
    (hb : Hw (s.xmm .xmm0) Bw) :
    WP isa (.block fX) s fun s' =>
      s'.gpr = s.gpr ∧ s'.zf = s.zf ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 80, 16⟩] s.mem s'.mem ∧
      Hw (s'.xmm .xmm5) (fun l => Spec.Seed.g (Spec.Seed.g (Spec.Seed.g (A l ^^^ Bw l) + A l) +
        Spec.Seed.g (A l ^^^ Bw l)) + Spec.Seed.g (Spec.Seed.g (A l ^^^ Bw l) + A l)) ∧
      Hw (s'.xmm .xmm0) (fun l => Spec.Seed.g (Spec.Seed.g (Spec.Seed.g (A l ^^^ Bw l) + A l) +
        Spec.Seed.g (A l ^^^ Bw l))) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  obtain ⟨c, hc⟩ : ∃ c : Nat → Word, c = fun l => Spec.Seed.g (A l ^^^ Bw l) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : Nat → Word, d = fun l => Spec.Seed.g (c l + A l) := ⟨_, rfl⟩
  obtain ⟨e, he'⟩ : ∃ e : Nat → Word, e = fun l => Spec.Seed.g (d l + c l) := ⟨_, rfl⟩
  have ha80 : addr B 80 = B.setWidth 64 + BitVec.ofNat 64 80 := addr_eq (by omega_using [hf])
  show WP isa (.block (.xop (.bin .pxor .xmm0 .xmm5) :: (g ++ (.movdquStore ⟨Impl.Modes.X86.sb, 80⟩ .xmm0 ::
    .xop (.bin .paddd .xmm0 .xmm5) :: (g ++ (.xop (.bin .movdqa .xmm5 .xmm0) ::
      .movdquLoad .xmm1 ⟨Impl.Modes.X86.sb, 80⟩ :: .xop (.bin .paddd .xmm0 .xmm1) ::
        (g ++ [.xop (.bin .paddd .xmm5 .xmm0)]))))))) s _
  -- `A ⊕ B`
  refine wp_xb fun s₁ sm₁ v₁ o₁ => ?_
  have h0₁ : Hw (s₁.xmm .xmm0) (fun l => A l ^^^ Bw l) := by
    rw [v₁]; exact (hb.pxor ha).congr fun l _ => BitVec.xor_comm _ _
  have h5₁ : s₁.xmm .xmm5 = s.xmm .xmm5 := o₁ _ (by decide)
  have m₁ : ∀ q < 16, byte (s₁.xmm m0) q = 0x0f#8 := by rw [o₁ m0 (by decide)]; exact he.msk
  refine WP.block_append_iff.mpr (WP.mono (g_wp (he.same sm₁ m₁) h0₁) fun s₂ ⟨sm₂, g₂, k5₂, m₂⟩ => ?_)
  have g₂' : Hw (s₂.xmm .xmm0) c := by rw [hc]; exact g₂
  have sm₁₂ : Same s s₂ := sm₁.trans sm₂
  have he₂ : Env s₂ := he.same sm₁₂ m₂
  -- `C` to its place, and `C + A`
  refine wp_stx' (by rw [same_wr sm₁₂, same_gpr sm₁₂, hB]; exact hwr) fun s₃ g₃ x₃ z₃ rd₃ wr₃ sy₃ mem₃ => ?_
  have he₃ : Env s₃ := ⟨by rw [g₃, sy₃]; exact he₂.tb, by rw [g₃]; exact he₂.fit,
    fun o ho => by rw [rd₃, wr₃, g₃]; exact he₂.acc o ho, by rw [x₃]; exact m₂⟩
  refine wp_xb fun s₄ sm₄ v₄ o₄ => ?_
  have h0₄ : Hw (s₄.xmm .xmm0) (fun l => c l + A l) := by
    rw [v₄, x₃, k5₂, h5₁]; exact g₂'.paddd ha
  have m₄ : ∀ q < 16, byte (s₄.xmm m0) q = 0x0f#8 := by rw [o₄ m0 (by decide), x₃]; exact m₂
  refine WP.block_append_iff.mpr (WP.mono (g_wp (he₃.same sm₄ m₄) h0₄) fun s₅ ⟨sm₅, g₅, _, m₅⟩ => ?_)
  have g₅' : Hw (s₅.xmm .xmm0) d := by rw [hd]; exact g₅
  have he₅ : Env s₅ := he₃.same (sm₄.trans sm₅) m₅
  -- `D`, `C` back, and `D + C`
  refine wp_xb fun s₆ sm₆ v₆ o₆ => ?_
  have sm₃₆ : Same s₃ s₆ := (sm₄.trans sm₅).trans sm₆
  have g₆ : s₆.gpr Impl.Modes.X86.sb = B := by rw [same_gpr sm₃₆, g₃, same_gpr sm₁₂, hB]
  have hin₆ : InRegions (s₆.rd ++ s₆.wr) (addr (s₆.gpr Impl.Modes.X86.sb) 80) 16 := by
    have := he₅.acc 80 (by decide)
    rwa [← same_rd sm₆, ← same_wr sm₆, ← same_gpr sm₆] at this
  refine wp_ldx' hin₆ fun s₇ sm₇ v₇ o₇ => ?_
  have c₇ : Hw (s₇.xmm .xmm1) c := by
    rw [v₇, g₆, same_mem sm₃₆, mem₃, same_gpr sm₁₂, hB, Mem.readW_writeW_self _ _ 16 _ (by decide)]
    exact g₂'
  refine wp_xb fun s₈ sm₈ v₈ o₈ => ?_
  have h5₈ : Hw (s₈.xmm .xmm5) d := by
    rw [o₈ _ (by decide), o₇ _ (by decide), v₆]; exact g₅'
  have h0₈ : Hw (s₈.xmm .xmm0) (fun l => d l + c l) := by
    rw [v₈, o₇ .xmm0 (by decide), o₆ .xmm0 (by decide)]; exact g₅'.paddd c₇
  have m₈ : ∀ q < 16, byte (s₈.xmm m0) q = 0x0f#8 := by
    rw [o₈ m0 (by decide), o₇ m0 (by decide), o₆ m0 (by decide)]; exact m₅
  have sm₃₈ : Same s₃ s₈ := (sm₃₆.trans sm₇).trans sm₈
  refine WP.block_append_iff.mpr (WP.mono (g_wp (he₃.same sm₃₈ m₈) h0₈) fun s₉ ⟨sm₉, g₉, k5₉, m₉⟩ => ?_)
  have g₉' : Hw (s₉.xmm .xmm0) e := by rw [he']; exact g₉
  -- `E + D`
  refine wp_xb fun s₁₀ sm₁₀ v₁₀ o₁₀ => WP.block_nil ?_
  have sm' : Same s₃ s₁₀ := (sm₃₈.trans sm₉).trans sm₁₀
  have hfin5 : Hw (s₁₀.xmm .xmm5) (fun l => e l + d l) := by
    rw [v₁₀, k5₉]; exact (h5₈.paddd g₉').congr fun l _ => BitVec.add_comm _ _
  have hfin0 : Hw (s₁₀.xmm .xmm0) e := by rw [o₁₀ _ (by decide)]; exact g₉'
  subst he' hd hc
  refine ⟨by rw [same_gpr sm', g₃, same_gpr sm₁₂], by rw [same_zf sm', z₃, same_zf sm₁₂],
    by rw [same_rd sm', rd₃, same_rd sm₁₂], by rw [same_wr sm', wr₃, same_wr sm₁₂],
    by rw [same_syms sm', sy₃, same_syms sm₁₂], ?_, hfin5, hfin0, by rw [o₁₀ m0 (by decide)]; exact m₉⟩
  rw [same_mem sm', mem₃, same_mem sm₁₂, same_gpr sm₁₂, hB, ha80]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 16)

end

/-! ## The state's halves in the scratch buffer -/

/-- The place `j` of the state's halves holds the words `X`: block `l`'s in
lane `l`. -/
def WordAt (m : Mem) (B : BitVec 32) (j : Nat) (X : Nat → Word) : Prop :=
  ∀ q < 16, sAt m B (16 + 16 * j + q) = byteOf (X (q / 4)) (q % 4)

theorem WordAt.frame {m m' : Mem} {B : BitVec 32} {j lo n : Nat} {X : Nat → Word} (h : WordAt m B j X)
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 lo, n⟩] m m') (hj : j < 4)
    (hne : 16 + 16 * j + 16 ≤ lo ∨ lo + n ≤ 16 + 16 * j) (hl : lo + n ≤ 96) : WordAt m' B j X := fun q hq => by
  rw [frame_sAt hf (by omega_using [hq, hne]) (by omega_using [hj, hq]) (by omega_using [hl])]; exact h q hq

/-- A state of `crypt` after `n` turns, from the state `s₀` it starts in:
the scratch buffer's address, the round keys' pointer, and the table's
address. -/
structure At (s₀ : State) (B : BitVec 32) (n : Nat) (s : State) : Prop where
  base : s.gpr Impl.Modes.X86.sb = B
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  syms : s.syms = s₀.syms
  tb : s.gpr tbr = s₀.syms tableName
  kp : s.gpr kr = B + BitVec.ofNat 32 (96 + 64 * n)

section
variable {s₀ s : State} {B : BitVec 32} {n : Nat}

theorem At.of_gpr {s' : State} (h : At s₀ B n s) (hg : s'.gpr = s.gpr) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsy : s'.syms = s.syms) : At s₀ B n s' :=
  ⟨by rw [hg]; exact h.base, by rw [hg]; exact h.esp, hrd.trans h.rd, hwr.trans h.wr, hsy.trans h.syms,
    by rw [hg]; exact h.tb, by rw [hg]; exact h.kp⟩

theorem At.same {s' : State} (h : At s₀ B n s) (hs : Same s s') : At s₀ B n s' :=
  h.of_gpr (same_gpr hs) (same_rd hs) (same_wr hs) (same_syms hs)

theorem At.kr64 (h : At s₀ B n s) (hf : B.toNat + 712 ≤ 2 ^ 32) (hn : n ≤ 8) :
    (s.gpr kr).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 (96 + 64 * n) := by
  rw [h.kp]; exact addr_eq (by omega_using [hf, hn])

theorem At.krNat (h : At s₀ B n s) (hf : B.toNat + 712 ≤ 2 ^ 32) (hn : n ≤ 8) :
    (s.gpr kr).toNat = B.toNat + (96 + 64 * n) := by
  rw [h.kp, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 96 + 64 * n) (by omega_using [hn]),
    Nat.mod_eq_of_lt (by omega_using [hf, hn])]

theorem At.scr (h : At s₀ B n s) (o : Nat) : kb s o = sAt s.mem B o := by
  rw [kb, h.base]; rfl

theorem At.env (h : At s₀ B n s) (hs : ScrIn s₀ B 178) (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) : Env s := by
  have hf : B.toNat + 712 ≤ 2 ^ 32 := hs.fit
  refine ⟨by rw [h.tb, h.syms], by rw [h.base]; omega_using [hf],
    fun o ho => ⟨_, List.mem_append_right _ (by rw [h.wr]; exact hs.wr), ?_⟩, hm⟩
  rw [h.base, addr_eq (by omega_using [hf, ho])]
  exact Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])

/-- Round `h` of turn `n`, round `2 n + h` of the four blocks: from the
right half in `xmm5` and `xmm0`, the left half in the places `2 h` and
`2 h + 1` and the round's keys, to the next round's right half in the
registers and its left half in the places `2 - 2 h` and `3 - 2 h`. -/
theorem round_ok {h : Nat} (hh : h < 2) (hs : ScrIn s₀ B 178) (hn : n < 8) (a : At s₀ B n s)
    (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) {l0 l1 r0 r1 : Nat → Word} {k0 k1 : Word}
    (h5 : Hw (s.xmm .xmm5) r0) (h0 : Hw (s.xmm .xmm0) r1)
    (wl0 : WordAt s.mem B (2 * h) l0) (wl1 : WordAt s.mem B (2 * h + 1) l1)
    (hk0 : KeyAt s.mem B (4 * n + 2 * h) k0) (hk1 : KeyAt s.mem B (4 * n + 2 * h + 1) k1) :
    WP isa (.block (round h)) s fun s' =>
      At s₀ B n s' ∧ (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) ∧ s'.gpr = s.gpr ∧ s'.zf = s.zf ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 16, 80⟩] s.mem s'.mem ∧
      WordAt s'.mem B (2 - 2 * h) r0 ∧ WordAt s'.mem B (3 - 2 * h) r1 ∧
      Hw (s'.xmm .xmm5) (fun l => l0 l ^^^ (Spec.Seed.f k0 k1 (r0 l) (r1 l)).1) ∧
      Hw (s'.xmm .xmm0) (fun l => l1 l ^^^ (Spec.Seed.f k0 k1 (r0 l) (r1 l)).2) := by
  have hf : B.toNat + 712 ≤ 2 ^ 32 := hs.fit
  have hle := Nat.le_of_lt hn
  have hkn := a.krNat hf hle
  have hk64 := a.kr64 hf hle
  obtain ⟨hkey, hleft⟩ := round_all h hh
  show WP isa (.block (keyX h ++ (fX ++ leftX h))) s _
  -- the right half to its places, and the keys
  have rel : Rel kparams (envOf kparams s) regs₀ s :=
    (rel_init (p := kparams) (by show s.gpr tbr = s.syms tableName; rw [a.tb, a.syms])
      (by show (s.gpr kr).toNat + 64 ≤ _; omega_using [hkn, hf, hn])
      fun o ho => ⟨_, List.mem_append_right _ (by rw [a.wr]; exact hs.wr), by
        show Region.Contains _ (addr (s.gpr kr) o) 16
        have ho' : o + 16 ≤ 64 := ho
        rw [addr_eq (by omega_using [hkn, hf, hn, ho']), hk64, Offset.add_ofNat_add_ofNat]
        exact Offset.contains_base _ (by omega_using [hn, ho']) (by omega_using [hn, ho'])⟩).const m0 hm
  have ok : OutOk kparams koparams s := by
    refine ⟨by show (s.gpr Impl.Modes.X86.sb).toNat + 96 ≤ _; rw [a.base]; omega_using [hf],
      fun o ho => ⟨_, by rw [a.wr]; exact hs.wr, ?_⟩, ?_, by show (s.gpr kr).toNat + 64 ≤ _; omega_using [hkn, hf, hn]⟩
    · show Region.Contains _ (addr (s.gpr Impl.Modes.X86.sb) o) 16
      have ho' : o + 16 ≤ 96 := ho
      rw [a.base, addr_eq (by omega_using [hf, ho'])]
      exact Offset.contains_base _ (by omega_using [ho']) (by omega_using [ho'])
    · show Region.Disjoint ⟨(s.gpr kr).setWidth 64, 64⟩ ⟨(s.gpr Impl.Modes.X86.sb).setWidth 64, 96⟩
      rw [hk64, a.base]
      exact Offset.disjoint_base _ (by omega_arith) (by omega_using [hn])
  unfold keyOk at hkey
  split at hkey <;> [cases hkey; rename_i σ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hkey
  obtain ⟨⟨⟨⟨⟨⟨o5, o0⟩, ol⟩, p5⟩, p0⟩, cx⟩, cm⟩ := hkey
  refine WP.block_append_iff.mpr (runS_wp ok (RelS.init rel rfl) hrun fun s₁ hr => ?_)
  have a₁ : At s₀ B n s₁ := a.of_gpr hr.gpr hr.rd hr.wr hr.syms
  have m₁ := mask_ok hr.rel cm
  have f₁ : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (16 + 16 * (2 - 2 * h)), 32⟩] s.mem s₁.mem := by
    refine hr.frame.sub fun r hr' => ?_
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr'
    have he' : e.1 ∈ σ.2.map fun e => e.1 := List.mem_map.mpr ⟨e, he, rfl⟩
    rw [ol] at he'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he'
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rw [show (s.gpr koparams.oreg) = s.gpr Impl.Modes.X86.sb from rfl, a.base]
    rcases he' with e | e <;> rw [e] <;> exact Offset.sub _ (by show _ ≤ 16 + _; omega_using [hh])
      (by show 16 + _ + 16 ≤ _; omega_using [hh])
  have wr0 : WordAt s₁.mem B (2 - 2 * h) r0 := fun q hq => by
    have := hr.out o5 hq
    rw [show (s.gpr koparams.oreg) = s.gpr Impl.Modes.X86.sb from rfl, a.base] at this
    rw [sAt, show 16 + 16 * (2 - 2 * h) + q = oR + 16 * (2 - 2 * h) + q from rfl, this]
    simp only [BV.eval, sum, BitVec.xor_zero, env_var kparams .xmm5 hq]
    exact h5 q hq
  have wr1 : WordAt s₁.mem B (3 - 2 * h) r1 := fun q hq => by
    have := hr.out o0 hq
    rw [show (s.gpr koparams.oreg) = s.gpr Impl.Modes.X86.sb from rfl, a.base] at this
    rw [sAt, show 16 + 16 * (3 - 2 * h) + q = oR + 16 * (3 - 2 * h) + q from rfl, this]
    simp only [BV.eval, sum, BitVec.xor_zero, env_var kparams .xmm0 hq]
    exact h0 q hq
  have key : ∀ {i : Nat} {k : Word}, KeyAt s.mem B (4 * n + i) k → i < 4 → ∀ q < 16,
      mask (envOf kparams s) (kv (16 * i + q)) nvars = byteOf k (q % 4) := fun {i k} hk hi q hq => by
    rw [kv, mask_bit _ (by show 128 + (16 * i + q) < 1024; omega_using [hi, hq]), envOf_key,
      show (s.gpr kparams.kreg) = s.gpr kr from rfl, hk64, Offset.add_ofNat_add_ofNat, ← hk q hq, sAt]
    exact congrArg (fun o => s.mem (B.setWidth 64 + BitVec.ofNat 64 o)) (by omega_arith)
  have x5₁ : Hw (s₁.xmm .xmm5) (fun l => r0 l ^^^ k0) := fun q hq => by
    have c := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp cx q (List.mem_range.mpr hq))
    rw [hr.rel.bytes p5 q hq, BV.same_eval _ c.1]
    simp only [BV.eval, sum, BitVec.xor_zero, mask_xor, env_var kparams .xmm5 hq]
    rw [show 32 * h + q = 16 * (2 * h) + q by omega_arith, key (i := 2 * h) hk0 (by omega_using [hh]) q hq, h5 q hq,
      byteOf_xor]
  have x0₁ : Hw (s₁.xmm .xmm0) (fun l => r1 l ^^^ k1) := fun q hq => by
    have c := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp cx q (List.mem_range.mpr hq))
    rw [hr.rel.bytes p0 q hq, BV.same_eval _ c.2]
    simp only [BV.eval, sum, BitVec.xor_zero, mask_xor, env_var kparams .xmm0 hq]
    rw [show 32 * h + 16 + q = 16 * (2 * h + 1) + q by omega_arith, key (i := 2 * h + 1) hk1 (by omega_using [hh]) q hq,
      h0 q hq, byteOf_xor]
  have wl0₁ : WordAt s₁.mem B (2 * h) l0 := wl0.frame f₁ (by omega_using [hh]) (by omega_using [hh]) (by omega_using [hh])
  have wl1₁ : WordAt s₁.mem B (2 * h + 1) l1 :=
    wl1.frame f₁ (by omega_using [hh]) (by omega_using [hh]) (by omega_using [hh])
  -- F
  have hw80 : InRegions s₁.wr (addr B 80) 16 := ⟨_, by rw [a₁.wr]; exact hs.wr, by
    rw [addr_eq (by omega_using [hf])]; exact Offset.contains_base _ (by decide) (by decide)⟩
  refine WP.block_append_iff.mpr (WP.mono (fX_wp (a₁.env hs m₁) a₁.base (by omega_using [hf]) hw80 x5₁ x0₁)
    fun s₂ ⟨g₂, z₂, rd₂, wr₂, sy₂, f₂, f5, f0, m₂⟩ => ?_)
  have a₂ : At s₀ B n s₂ := a₁.of_gpr g₂ rd₂ wr₂ sy₂
  have fr : ∀ {j : Nat} {X : Nat → Word}, WordAt s₁.mem B j X → j < 4 → WordAt s₂.mem B j X :=
    fun hw hj => hw.frame f₂ hj (.inl (by omega_using [hj])) (by decide)
  -- the left half
  unfold leftOk at hleft
  split at hleft <;> [cases hleft; rename_i ρ hrun']
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hleft
  obtain ⟨⟨⟨q5, q0⟩, cy⟩, cn⟩ := hleft
  refine run_wp (a₂.env hs m₂).rel hrun' fun s₃ hr₃ sm₃ => ?_
  have lft : ∀ {j : Nat} {X : Nat → Word}, WordAt s₂.mem B j X → j < 4 → ∀ q < 16,
      mask (envOf params s₂) (kv (oR + 16 * j + q)) nvars = byteOf (X (q / 4)) (q % 4) := fun {j X} hw hj q hq => by
    rw [env_key (by show 16 + 16 * j + q < 96; omega_using [hj, hq]), a₂.scr]
    exact hw q hq
  have e₃ : s₃.mem = s₂.mem := same_mem sm₃
  refine ⟨a₂.same sm₃, mask_ok hr₃ cn, by rw [same_gpr sm₃, g₂, hr.gpr],
    by rw [same_zf sm₃, z₂, hr.zf], ?_, by rw [e₃]; exact fr wr0 (by omega_using [hh]),
    by rw [e₃]; exact fr wr1 (by omega_using [hh]), fun q hq => ?_, fun q hq => ?_⟩
  · rw [e₃]
    exact (f₁.sub fun r hr' => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr']; exact Offset.sub _ (by omega_arith) (by omega_using [hh])⟩).trans
      (f₂.sub fun r hr' => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr']; exact Offset.sub _ (by decide) (by decide)⟩)
  · have c := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp cy q (List.mem_range.mpr hq))
    rw [hr₃.bytes q5 q hq, BV.same_eval _ c.1]
    simp only [BV.eval, sum, BitVec.xor_zero, mask_xor, env_var params .xmm5 hq]
    rw [show oR + 32 * h + q = oR + 16 * (2 * h) + q by omega_arith,
      lft (j := 2 * h) (fr wl0₁ (by omega_using [hh])) (by omega_using [hh]) q hq, f5 q hq, byteOf_xor, BitVec.xor_comm]
    rfl
  · have c := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp cy q (List.mem_range.mpr hq))
    rw [hr₃.bytes q0 q hq, BV.same_eval _ c.2]
    simp only [BV.eval, sum, BitVec.xor_zero, mask_xor, env_var params .xmm0 hq]
    rw [show oR + 32 * h + 16 + q = oR + 16 * (2 * h + 1) + q by omega_arith,
      lft (j := 2 * h + 1) (fr wl1₁ (by omega_using [hh])) (by omega_using [hh]) q hq, f0 q hq, byteOf_xor,
      BitVec.xor_comm]
    rfl

end

/-! ## The four blocks -/

/-- Word `w` of block `l` of the scratch buffer's four. -/
def bwd (m : Mem) (B : BitVec 32) (w l : Nat) : Word :=
  Spec.Seed.wordAt (Spec.Seed.blockAt m (B.setWidth 64 + BitVec.ofNat 64 (608 + 16 * l))) (4 * w)

/-- The blocks' words are big-endian. -/
theorem byteOf_bwd (m : Mem) (B : BitVec 32) {w l k : Nat} (hw : w < 4) (hk : k < 4) :
    byteOf (bwd m B w l) k = sAt m B (608 + 16 * l + (4 * w + (3 - k))) := by
  rw [bwd, byteOf_wordAt _ _ hk, blockAt_getD _ _ (by omega_using [hw, hk]), Offset.add_ofNat_add_ofNat]; rfl

section
variable {s : State} {B : BitVec 32}

/-- The mask, and the four blocks to their four words, in `xmm0`, `xmm3`,
`xmm4` and `xmm1`. -/
theorem head_wp (htb : s.gpr tbr = s.syms tableName) (hB : s.gpr Impl.Modes.X86.sb = B)
    (hwr : (⟨B.setWidth 64, 4 * 178⟩ : Region) ∈ s.wr) (hf : B.toNat + 712 ≤ 2 ^ 32) :
    WP isa (.block headX) s fun s' =>
      Same s s' ∧ Hw (s'.xmm .xmm0) (bwd s.mem B 0) ∧ Hw (s'.xmm .xmm3) (bwd s.mem B 1) ∧
      Hw (s'.xmm .xmm4) (bwd s.mem B 2) ∧ Hw (s'.xmm .xmm1) (bwd s.mem B 3) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  have rel : Rel hparams (envOf hparams s) Regs.init s :=
    rel_init (p := hparams) htb (by show (s.gpr Impl.Modes.X86.sb).toNat + 672 ≤ _; rw [hB]; omega_using [hf])
      (fun o ho => ⟨_, List.mem_append_right _ hwr, by
        show Region.Contains _ (addr (s.gpr Impl.Modes.X86.sb) o) 16
        have ho' : o + 16 ≤ 672 := ho
        rw [hB, addr_eq (by omega_using [hf, ho'])]
        exact Offset.contains_base _ (by omega_using [ho']) (by omega_using [ho'])⟩)
  have hok := ends_all.1
  unfold headOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨h0, h3⟩, h4⟩, h1⟩, cx⟩, cm⟩ := hok
  refine run_wp rel hrun fun s' hr hsame => ?_
  have ev : ∀ w < 4, ∀ q < 16, (hw w q).eval (envOf hparams s) = byteOf (bwd s.mem B w (q / 4)) (q % 4) :=
    fun w hw4 q hq => by
    rw [hw, BV.eval, sum, BitVec.xor_zero, BitVec.xor_zero, kv,
      mask_bit _ (by show 128 + (608 + 16 * (q / 4) + 4 * w + (3 - q % 4)) < 1024; omega_using [hw4, hq]), envOf_key,
      show (s.gpr hparams.kreg) = s.gpr Impl.Modes.X86.sb from rfl, hB,
      byteOf_bwd _ _ hw4 (Nat.mod_lt _ (by decide)), sAt]
    exact congrArg (fun o => s.mem (B.setWidth 64 + BitVec.ofNat 64 o)) (by show 608 + _ + _ + _ = _; omega_arith)
  have cq := fun q (hq : q < 16) => List.all_eq_true.mp cx q (List.mem_range.mpr hq)
  simp only [Bool.and_eq_true] at cq
  refine ⟨hsame, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, mask_ok hr cm⟩
  · rw [hr.bytes h0 q hq, BV.same_eval _ (cq q hq).1.1.1, ev 0 (by decide) q hq]
  · rw [hr.bytes h3 q hq, BV.same_eval _ (cq q hq).1.1.2, ev 1 (by decide) q hq]
  · rw [hr.bytes h4 q hq, BV.same_eval _ (cq q hq).1.2, ev 2 (by decide) q hq]
  · rw [hr.bytes h1 q hq, BV.same_eval _ (cq q hq).2, ev 3 (by decide) q hq]

/-- A register stored at byte `o` of the scratch buffer: its bytes there,
and nothing else changed. -/
theorem store_sAt (m : Mem) {B : BitVec 32} {o : Nat} (hf : B.toNat + o + 16 ≤ 2 ^ 32) (v : BitVec 128) :
    (∀ q < 16, sAt (m.writeW (addr B o) v) B (o + q) = byte v q) ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 o, 16⟩] m (m.writeW (addr B o) v) := by
  have ha : addr B o = B.setWidth 64 + BitVec.ofNat 64 o := addr_eq (by omega_using [hf])
  refine ⟨fun q hq => ?_, ?_⟩
  · show (m.writeW (addr B o) v) (B.setWidth 64 + BitVec.ofNat 64 (o + q)) = _
    rw [← Offset.add_ofNat_add_ofNat, ← ha,
      ← byte_readW (m.writeW (addr B o) v) (addr B o) (w := 128) (k := q) (by omega_using [hq]),
      Mem.readW_writeW_self _ _ 16 _ (by decide)]
    rfl
  · rw [ha]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 16)

/-- Four registers to four places of the scratch buffer (`stores`): their
bytes there, and nothing else changed. -/
theorem stores_wp {o : Nat} {r0 r1 r2 r3 : XReg} (hB : s.gpr Impl.Modes.X86.sb = B)
    (hwr : (⟨B.setWidth 64, 4 * 178⟩ : Region) ∈ s.wr) (hf : B.toNat + 712 ≤ 2 ^ 32) (ho : o + 64 ≤ 712) :
    WP isa (.block (stores o r0 r1 r2 r3)) s fun s' =>
      s'.gpr = s.gpr ∧ s'.xmm = s.xmm ∧ s'.zf = s.zf ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 o, 64⟩] s.mem s'.mem ∧
      (∀ q < 16, sAt s'.mem B (o + q) = byte (s.xmm r0) q) ∧
      (∀ q < 16, sAt s'.mem B (o + 16 + q) = byte (s.xmm r1) q) ∧
      (∀ q < 16, sAt s'.mem B (o + 32 + q) = byte (s.xmm r2) q) ∧
      (∀ q < 16, sAt s'.mem B (o + 48 + q) = byte (s.xmm r3) q) := by
  have hin : ∀ d, d + 16 ≤ 712 → InRegions s.wr (addr B d) 16 := fun d hd => ⟨_, hwr, by
    rw [addr_eq (by omega_using [hf, hd])]; exact Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])⟩
  obtain ⟨v0, f0⟩ := store_sAt s.mem (B := B) (o := o) (by omega_using [hf, ho]) (s.xmm r0)
  obtain ⟨v1, f1⟩ := store_sAt (s.mem.writeW (addr B o) (s.xmm r0)) (B := B) (o := o + 16)
    (by omega_using [hf, ho]) (s.xmm r1)
  obtain ⟨v2, f2⟩ := store_sAt ((s.mem.writeW (addr B o) (s.xmm r0)).writeW (addr B (o + 16)) (s.xmm r1)) (B := B)
    (o := o + 32) (by omega_using [hf, ho]) (s.xmm r2)
  obtain ⟨v3, f3⟩ := store_sAt (((s.mem.writeW (addr B o) (s.xmm r0)).writeW (addr B (o + 16)) (s.xmm r1)).writeW
    (addr B (o + 32)) (s.xmm r2)) (B := B) (o := o + 48) (by omega_using [hf, ho]) (s.xmm r3)
  have hb : ∀ d, d < 712 → d < 2 ^ 32 := fun d hd => by omega_using [hd]
  unfold stores
  refine wp_stx (by rw [hB]; exact hin _ (by omega_using [ho])) ?_
  refine wp_stx (s := { s with mem := _ })
    (by show InRegions s.wr (addr (s.gpr _) _) 16; rw [hB]; exact hin _ (by omega_using [ho])) ?_
  refine wp_stx (s := { s with mem := _ })
    (by show InRegions s.wr (addr (s.gpr _) _) 16; rw [hB]; exact hin _ (by omega_using [ho])) ?_
  refine wp_stx (s := { s with mem := _ })
    (by show InRegions s.wr (addr (s.gpr _) _) 16; rw [hB]; exact hin _ (by omega_using [ho])) (WP.block_nil ?_)
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · show Frame _ s.mem ((((s.mem.writeW (addr (s.gpr _) o) (s.xmm r0)).writeW (addr (s.gpr _) (o + 16)) (s.xmm r1)).writeW
      (addr (s.gpr _) (o + 32)) (s.xmm r2)).writeW (addr (s.gpr _) (o + 48)) (s.xmm r3))
    rw [hB]
    have sub : ∀ d, d + 16 ≤ 64 → ∀ r ∈ [(⟨B.setWidth 64 + BitVec.ofNat 64 (o + d), 16⟩ : Region)],
        ∃ r' ∈ [(⟨B.setWidth 64 + BitVec.ofNat 64 o, 64⟩ : Region)], Region.Sub r r' := fun d hd r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega_arith) (by omega_using [hd])⟩
    exact (((f0.sub (sub 0 (by decide))).trans (f1.sub (sub 16 (by decide)))).trans
      (f2.sub (sub 32 (by decide)))).trans (f3.sub (sub 48 (by decide)))
  · show sAt ((((s.mem.writeW (addr (s.gpr _) o) (s.xmm r0)).writeW (addr (s.gpr _) (o + 16)) (s.xmm r1)).writeW
      (addr (s.gpr _) (o + 32)) (s.xmm r2)).writeW (addr (s.gpr _) (o + 48)) (s.xmm r3)) B (o + q) = _
    rw [hB, frame_sAt f3 (by omega_using [hq]) (hb _ (by omega_using [ho, hq])) (hb _ (by omega_using [ho])),
      frame_sAt f2 (by omega_using [hq]) (hb _ (by omega_using [ho, hq])) (hb _ (by omega_using [ho])),
      frame_sAt f1 (by omega_using [hq]) (hb _ (by omega_using [ho, hq])) (hb _ (by omega_using [ho]))]
    exact v0 q hq
  · show sAt ((((s.mem.writeW (addr (s.gpr _) o) (s.xmm r0)).writeW (addr (s.gpr _) (o + 16)) (s.xmm r1)).writeW
      (addr (s.gpr _) (o + 32)) (s.xmm r2)).writeW (addr (s.gpr _) (o + 48)) (s.xmm r3)) B (o + 16 + q) = _
    rw [hB, frame_sAt f3 (by omega_using [hq]) (hb _ (by omega_using [ho, hq])) (hb _ (by omega_using [ho])),
      frame_sAt f2 (by omega_using [hq]) (hb _ (by omega_using [ho, hq])) (hb _ (by omega_using [ho]))]
    exact v1 q hq
  · show sAt ((((s.mem.writeW (addr (s.gpr _) o) (s.xmm r0)).writeW (addr (s.gpr _) (o + 16)) (s.xmm r1)).writeW
      (addr (s.gpr _) (o + 32)) (s.xmm r2)).writeW (addr (s.gpr _) (o + 48)) (s.xmm r3)) B (o + 32 + q) = _
    rw [hB, frame_sAt f3 (by omega_using [hq]) (hb _ (by omega_using [ho, hq])) (hb _ (by omega_using [ho]))]
    exact v2 q hq
  · show sAt ((((s.mem.writeW (addr (s.gpr _) o) (s.xmm r0)).writeW (addr (s.gpr _) (o + 16)) (s.xmm r1)).writeW
      (addr (s.gpr _) (o + 32)) (s.xmm r2)).writeW (addr (s.gpr _) (o + 48)) (s.xmm r3)) B (o + 48 + q) = _
    rw [hB]
    exact v3 q hq

end

section
variable {s₀ s : State} {B : BitVec 32} {rk : Nat → Word}

/-- The scratch buffer's four blocks to their words, and the registers of
the loop: the first two words in their places, the third in `xmm5` and the
last in `xmm0`. -/
theorem cryptHead_wp (hB : s.gpr Impl.Modes.X86.sb = B) (hs : ScrIn s B 178)
    (htab : s.mem.readW (B.setWidth 64) 32 = s.syms tableName) (hk : ∀ i < 32, KeyAt s.mem B i (rk i)) :
    WP isa (.block cryptHead) s fun s' =>
      At s B 0 s' ∧ (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) ∧ s'.gpr .eax = BitVec.ofNat 32 8 ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 16, 80⟩] s.mem s'.mem ∧
      (∀ i < 32, KeyAt s'.mem B i (rk i)) ∧
      WordAt s'.mem B 0 (bwd s.mem B 0) ∧ WordAt s'.mem B 1 (bwd s.mem B 1) ∧
      Hw (s'.xmm .xmm5) (bwd s.mem B 2) ∧ Hw (s'.xmm .xmm0) (bwd s.mem B 3) := by
  have hf : B.toNat + 712 ≤ 2 ^ 32 := hs.fit
  have hw : InRegions (s.rd ++ s.wr) (addr B 0) 4 := ⟨_, List.mem_append_right _ hs.wr, by
    rw [addr_eq (by omega_using [hf])]; exact Offset.contains_base _ (by decide) (by decide)⟩
  show WP isa (.block (.mov tbr (.mem ⟨Impl.Modes.X86.sb, 0⟩) :: .mov kr (.reg Impl.Modes.X86.sb) ::
    .alu .add kr (.imm 96) :: .mov .eax (.imm 8) :: (headX ++ headS))) s _
  refine Wp.wp_ldm hB hw fun s₁ u₁ => ?_
  refine Wp.wp_mov fun s₂ u₂ => ?_
  refine Wp.wp_addi fun s₃ u₃ => ?_
  refine Wp.wp_movi fun s₄ u₄ => ?_
  have e₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have w₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have y₄ : s₄.syms = s.syms := by rw [u₄.syms, u₃.syms, u₂.syms, u₁.syms]
  have b₄ : s₄.gpr Impl.Modes.X86.sb = B := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hB]
  have a₄ : At s B 0 s₄ := by
    refine ⟨b₄, ?_, r₄, w₄, y₄, ?_, ?_⟩
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
        addr_eq (by omega_using [hf]), BitVec.add_zero]
      exact htab
    · rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), hB]
      rfl
  have c₄ : s₄.gpr .eax = BitVec.ofNat 32 8 := by rw [u₄.gpr]; rfl
  refine WP.block_append_iff.mpr (WP.mono (head_wp (B := B) (by rw [a₄.tb, a₄.syms]) a₄.base
    (by rw [a₄.wr]; exact hs.wr) hf) fun s₅ ⟨hsame, x0₅, x3₅, x4₅, x1₅, m₅⟩ => ?_)
  obtain ⟨f, rfl⟩ := hsame
  rw [e₄] at x0₅ x3₅ x4₅ x1₅
  have hin : ∀ d, d + 16 ≤ 712 → InRegions s₄.wr (addr (s₄.gpr Impl.Modes.X86.sb) d) 16 := fun d hd =>
    ⟨_, by rw [w₄]; exact hs.wr, by
      rw [b₄, addr_eq (by omega_using [hf, hd])]
      exact Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])⟩
  obtain ⟨v0, f0⟩ := store_sAt s.mem (B := B) (o := 16) (by omega_using [hf]) (f .xmm0)
  obtain ⟨v1, f1⟩ := store_sAt (s.mem.writeW (addr B 16) (f .xmm0)) (B := B) (o := 32) (by omega_using [hf])
    (f .xmm3)
  show WP isa (.block [.movdquStore ⟨Impl.Modes.X86.sb, 16⟩ .xmm0, .movdquStore ⟨Impl.Modes.X86.sb, 32⟩ .xmm3,
    .xop (.bin .movdqa .xmm5 .xmm4), .xop (.bin .movdqa .xmm0 .xmm1)]) { s₄ with xmm := f } _
  refine wp_stx' (s := { s₄ with xmm := f }) (hin 16 (by decide)) fun s₆ g₆ x₆ z₆ rd₆ wr₆ sy₆ mem₆ => ?_
  refine wp_stx' (by rw [wr₆, g₆]; exact hin 32 (by decide)) fun s₇ g₇ x₇ z₇ rd₇ wr₇ sy₇ mem₇ => ?_
  refine wp_xb fun s₈ sm₈ v₈ o₈ => wp_xb fun s₉ sm₉ v₉ o₉ => WP.block_nil ?_
  have e₉ : s₉.mem = (s.mem.writeW (addr B 16) (f .xmm0)).writeW (addr B 32) (f .xmm3) := by
    rw [same_mem sm₉, same_mem sm₈, mem₇, g₆, x₆, mem₆]
    show (s₄.mem.writeW (addr (s₄.gpr Impl.Modes.X86.sb) 16) (f .xmm0)).writeW
      (addr (s₄.gpr Impl.Modes.X86.sb) 32) (f .xmm3) = _
    rw [b₄, e₄]
  have g₉ : s₉.gpr = s₄.gpr := (same_gpr sm₉).trans ((same_gpr sm₈).trans (g₇.trans g₆))
  have F : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 16, 80⟩] s.mem s₉.mem := by
    rw [e₉]
    exact (f0.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩).trans
      (f1.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩)
  refine ⟨a₄.of_gpr g₉ ((same_rd sm₉).trans ((same_rd sm₈).trans (rd₇.trans rd₆)))
    ((same_wr sm₉).trans ((same_wr sm₈).trans (wr₇.trans wr₆)))
    ((same_syms sm₉).trans ((same_syms sm₈).trans (sy₇.trans sy₆))), ?_, by rw [g₉]; exact c₄, F,
    fun i hi => (hk i hi).frame F hi (by decide), fun q hq => ?_, fun q hq => ?_, ?_, ?_⟩
  · rw [o₉ m0 (by decide), o₈ m0 (by decide), x₇, x₆]; exact m₅
  · rw [e₉, frame_sAt f1 (.inl (by omega_using [hq])) (by omega_using [hq]) (by decide)]
    exact (v0 q hq).trans (x0₅ q hq)
  · rw [e₉]
    exact (v1 q hq).trans (x3₅ q hq)
  · rw [o₉ _ (by decide), v₈, x₇, x₆]; exact x4₅
  · rw [v₉, o₈ .xmm1 (by decide), x₇, x₆]; exact x1₅

/-- Round `j + 1`'s key, of the round keys `rk`. -/
abbrev keyOf (rk : Nat → Word) : Nat → Word × Word := fun j => (rk (2 * j), rk (2 * j + 1))

/-- The state with `n` turns left: the keys' pointer after `8 - n` turns,
the turns left in `eax`, the round keys, and the four blocks' state after
`2 (8 - n)` rounds: its left half in the first two places, its right half
in `xmm5` and `xmm0`. -/
def Inv (s₀ : State) (B : BitVec 32) (rk : Nat → Word) (b : Nat → Spec.Seed.Block) (n : Nat) (s : State) : Prop :=
  n ≤ 8 ∧ At s₀ B (8 - n) s ∧ (∀ q < 16, byte (s.xmm m0) q = 0x0f#8) ∧ s.gpr .eax = BitVec.ofNat 32 n ∧
    Frame [⟨B.setWidth 64 + BitVec.ofNat 64 16, 80⟩] s₀.mem s.mem ∧ (∀ i < 32, KeyAt s.mem B i (rk i)) ∧
    ∃ l0 l1 r0 r1 : Nat → Word,
      (∀ l, Proof.Seed.roundsN (keyOf rk) (2 * (8 - n)) (Proof.Seed.decodeQ (b l)) = (l0 l, l1 l, r0 l, r1 l)) ∧
      WordAt s.mem B 0 l0 ∧ WordAt s.mem B 1 l1 ∧ Hw (s.xmm .xmm5) r0 ∧ Hw (s.xmm .xmm0) r1

/-- A turn of the loop: two rounds of the four blocks. -/
theorem turn_wp (hs : ScrIn s₀ B 178) {b : Nat → Spec.Seed.Block} {n : Nat} (hn : 1 ≤ n) (hI : Inv s₀ B rk b n s) :
    WP isa (.block turn) s fun s' => s'.zf = some (decide (n = 1)) ∧ Inv s₀ B rk b (n - 1) s' := by
  obtain ⟨hn8, a, hm, hc, hfr, hk, l0, l1, r0, r1, hst, w0, w1, h5, h0⟩ := hI
  obtain ⟨m, hm'⟩ : ∃ m, m = 8 - n := ⟨_, rfl⟩
  rw [← hm'] at a hst
  have hm8 : m < 8 := by omega_using [hn, hm']
  show WP isa (.block (round 0 ++ (round 1 ++ Impl.Seed.X86.AesNiWide.step))) s _
  -- round `2 m`
  have ka0 : KeyAt s.mem B (4 * m + 2 * 0) (rk (2 * (2 * m))) := by
    rw [show 4 * m + 2 * 0 = 2 * (2 * m) by omega_arith]; exact hk _ (by omega_using [hm8])
  have ka1 : KeyAt s.mem B (4 * m + 2 * 0 + 1) (rk (2 * (2 * m) + 1)) := by
    rw [show 4 * m + 2 * 0 + 1 = 2 * (2 * m) + 1 by omega_arith]; exact hk _ (by omega_using [hm8])
  refine WP.block_append_iff.mpr (WP.mono (round_ok (h := 0) (by decide) hs hm8 a hm h5 h0 w0 w1 ka0 ka1)
    fun s₁ ⟨a₁, m₁, g₁, z₁, f₁, wa₁, wb₁, x5₁, x0₁⟩ => ?_)
  obtain ⟨R0, hR0⟩ : ∃ R0 : Nat → Word,
    R0 = fun l => l0 l ^^^ (Spec.Seed.f (rk (2 * (2 * m))) (rk (2 * (2 * m) + 1)) (r0 l) (r1 l)).1 := ⟨_, rfl⟩
  obtain ⟨R1, hR1⟩ : ∃ R1 : Nat → Word,
    R1 = fun l => l1 l ^^^ (Spec.Seed.f (rk (2 * (2 * m))) (rk (2 * (2 * m) + 1)) (r0 l) (r1 l)).2 := ⟨_, rfl⟩
  rw [← hR0] at x5₁
  rw [← hR1] at x0₁
  have k₁ : ∀ i < 32, KeyAt s₁.mem B i (rk i) := fun i hi => (hk i hi).frame f₁ hi (by decide)
  -- round `2 m + 1`
  have kb0 : KeyAt s₁.mem B (4 * m + 2 * 1) (rk (2 * (2 * m + 1))) := by
    rw [show 4 * m + 2 * 1 = 2 * (2 * m + 1) by omega_arith]; exact k₁ _ (by omega_using [hm8])
  have kb1 : KeyAt s₁.mem B (4 * m + 2 * 1 + 1) (rk (2 * (2 * m + 1) + 1)) := by
    rw [show 4 * m + 2 * 1 + 1 = 2 * (2 * m + 1) + 1 by omega_arith]; exact k₁ _ (by omega_using [hm8])
  refine WP.block_append_iff.mpr (WP.mono (round_ok (h := 1) (by decide) hs hm8 a₁ m₁ x5₁ x0₁ wa₁ wb₁ kb0 kb1)
    fun s₂ ⟨a₂, m₂, g₂, z₂, f₂, wa₂, wb₂, x5₂, x0₂⟩ => ?_)
  have k₂ : ∀ i < 32, KeyAt s₂.mem B i (rk i) := fun i hi => (k₁ i hi).frame f₂ hi (by decide)
  have c₀ : s₂.gpr .eax = BitVec.ofNat 32 n := by rw [g₂, g₁, hc]
  show WP isa (.block [.alu .add kr (.imm 64), .alu .sub .eax (.imm 1)]) s₂ _
  refine wp_addi_x fun s₅ u₅ x₅ => wp_subi_x fun s₆ u₆ x₆ z₆ => WP.block_nil ?_
  have e₆ : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem]
  have xe : s₆.xmm = s₂.xmm := by rw [x₆, x₅]
  have c₅ : s₅.gpr .eax = BitVec.ofNat 32 n := by rw [u₅.other _ (by decide), c₀]
  refine ⟨?_, by omega_using [hn8], ?_, by rw [xe]; exact m₂, ?_, ?_, by rw [e₆]; exact k₂, R0, R1,
    fun l => r0 l ^^^ (Spec.Seed.f (rk (2 * (2 * m + 1))) (rk (2 * (2 * m + 1) + 1)) (R0 l) (R1 l)).1,
    fun l => r1 l ^^^ (Spec.Seed.f (rk (2 * (2 * m + 1))) (rk (2 * (2 * m + 1) + 1)) (R0 l) (R1 l)).2, fun l => ?_,
    by rw [e₆]; exact wa₂, by rw [e₆]; exact wb₂, by rw [xe]; exact x5₂, by rw [xe]; exact x0₂⟩
  · rw [z₆, c₅, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_beq (by omega_using [hn8]) (by decide)]
  · rw [show 8 - (n - 1) = m + 1 by omega_using [hn, hm', hn8]]
    refine ⟨?_, ?_, by rw [u₆.rd, u₅.rd]; exact a₂.rd, by rw [u₆.wr, u₅.wr]; exact a₂.wr,
      by rw [u₆.syms, u₅.syms]; exact a₂.syms, ?_, ?_⟩
    · rw [u₆.other _ (by decide), u₅.other _ (by decide)]; exact a₂.base
    · rw [u₆.other _ (by decide), u₅.other _ (by decide)]; exact a₂.esp
    · rw [u₆.other _ (by decide), u₅.other _ (by decide)]; exact a₂.tb
    · rw [u₆.other _ (by decide), u₅.gpr, a₂.kp, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl,
        Offset.add_ofNat_add_ofNat]
      congr 2
  · rw [u₆.gpr, c₅]; exact Wp.ofNat_pred hn
  · rw [e₆]
    exact (hfr.trans f₁).trans f₂
  · rw [show 2 * (8 - (n - 1)) = 2 * m + 1 + 1 by omega_using [hn, hm', hn8], Proof.Seed.roundsN_succ,
      Proof.Seed.roundsN_succ, hst l, hR0, hR1]
    rfl

/-- The eight turns: the state after the 16 rounds. -/
theorem loop_wp (hs : ScrIn s₀ B 178) {b : Nat → Spec.Seed.Block} {n : Nat} (hn : 1 ≤ n) (hI : Inv s₀ B rk b n s) :
    WP isa (.loop (.block turn) .ne) s (Inv s₀ B rk b 0) := by
  refine WP.loop (M := isa) (fun n s => 1 ≤ n ∧ Inv s₀ B rk b n s) ?_ n s ⟨hn, hI⟩
  rintro n s ⟨hn, hI⟩
  refine WP.mono (turn_wp hs hn hI) fun s₁ ⟨z₁, i₁⟩ => ?_
  by_cases h1 : n = 1
  · subst h1
    exact .inl ⟨by show s₁.zf.map _ = _; rw [z₁]; rfl, i₁⟩
  · exact .inr ⟨by show s₁.zf.map _ = _; rw [z₁, decide_eq_false h1]; rfl, n - 1, by omega_using [hn],
      by omega_using [hn, h1], i₁⟩

/-- The last right half, then the last left half, of each block to its
bytes, at byte 608 of the scratch buffer. -/
theorem cryptTail_wp {n : Nat} (hs : ScrIn s₀ B 178) (h : At s₀ B n s) (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8)
    {l0 l1 r0 r1 : Nat → Word} (w0 : WordAt s.mem B 0 l0) (w1 : WordAt s.mem B 1 l1) (h5 : Hw (s.xmm .xmm5) r0)
    (h0 : Hw (s.xmm .xmm0) r1) :
    WP isa (.block cryptTail) s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s₀.gpr .esp ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.syms = s₀.syms ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 608, 64⟩] s.mem s'.mem ∧
      ∀ l < 4, ∀ q < 16, sAt s'.mem B (608 + 16 * l + q) =
        byteOf ((#v[r0 l, r1 l, l0 l, l1 l] : Vector Word 4).getD (q / 4) 0) (3 - q % 4) := by
  have hf : B.toNat + 712 ≤ 2 ^ 32 := hs.fit
  have he := h.env hs hm
  have hok := ends_all.2
  unfold tailOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨h0', h3⟩, h4⟩, h1⟩, c2⟩ := hok
  refine WP.block_append_iff.mpr (run_wp he.rel hrun fun s₁ hr hsame => ?_)
  have ev : ∀ l < 4, ∀ q < 16, mask (envOf params s) (tw l q) nvars =
      byteOf ((#v[r0 l, r1 l, l0 l, l1 l] : Vector Word 4).getD (q / 4) 0) (3 - q % 4) := fun l hl q hq => by
    have h3 : (4 * l + (3 - q % 4)) % 4 = 3 - q % 4 := by omega_arith
    have hd : (4 * l + (3 - q % 4)) / 4 = l := by omega_arith
    have hlt : 4 * l + (3 - q % 4) < 16 := by omega_using [hl]
    rcases (show q / 4 = 0 ∨ q / 4 = 1 ∨ q / 4 = 2 ∨ q / 4 = 3 by omega_using [hq]) with e | e | e | e
    · rw [tw, ite_eq_left e, env_var params .xmm5 hlt, h5 _ hlt, h3, hd, e]; rfl
    · rw [tw, ite_eq_right (by omega_using [e]), ite_eq_left e, env_var params .xmm0 hlt, h0 _ hlt, h3, hd, e]; rfl
    · rw [tw, ite_eq_right (by omega_using [e]), ite_eq_right (by omega_using [e]), e,
        env_key (by show 16 + 16 * (2 - 2) + 4 * l + (3 - q % 4) < 96; omega_using [hl]), h.scr]
      have := w0 (4 * l + (3 - q % 4)) hlt
      rw [h3, hd] at this
      exact (congrArg (sAt s.mem B) (by show 16 + 16 * (2 - 2) + 4 * l + (3 - q % 4) = _; omega_arith)).trans this
    · rw [tw, ite_eq_right (by omega_using [e]), ite_eq_right (by omega_using [e]), e,
        env_key (by show 16 + 16 * (3 - 2) + 4 * l + (3 - q % 4) < 96; omega_using [hl]), h.scr]
      have := w1 (4 * l + (3 - q % 4)) hlt
      rw [h3, hd] at this
      exact (congrArg (sAt s.mem B) (by show 16 + 16 * (3 - 2) + 4 * l + (3 - q % 4) = _; omega_arith)).trans this
  have cq := fun q (hq : q < 16) => List.all_eq_true.mp c2 q (List.mem_range.mpr hq)
  simp only [Bool.and_eq_true] at cq
  have b0 : ∀ q < 16, byte (s₁.xmm .xmm0) q =
      byteOf ((#v[r0 0, r1 0, l0 0, l1 0] : Vector Word 4).getD (q / 4) 0) (3 - q % 4) := fun q hq => by
    rw [hr.bytes h0' q hq, BV.same_eval _ (cq q hq).1.1.1]
    simp only [BV.eval, sum, BitVec.xor_zero]
    exact ev 0 (by decide) q hq
  have b1 : ∀ q < 16, byte (s₁.xmm .xmm3) q =
      byteOf ((#v[r0 1, r1 1, l0 1, l1 1] : Vector Word 4).getD (q / 4) 0) (3 - q % 4) := fun q hq => by
    rw [hr.bytes h3 q hq, BV.same_eval _ (cq q hq).1.1.2]
    simp only [BV.eval, sum, BitVec.xor_zero]
    exact ev 1 (by decide) q hq
  have b2 : ∀ q < 16, byte (s₁.xmm .xmm4) q =
      byteOf ((#v[r0 2, r1 2, l0 2, l1 2] : Vector Word 4).getD (q / 4) 0) (3 - q % 4) := fun q hq => by
    rw [hr.bytes h4 q hq, BV.same_eval _ (cq q hq).1.2]
    simp only [BV.eval, sum, BitVec.xor_zero]
    exact ev 2 (by decide) q hq
  have b3 : ∀ q < 16, byte (s₁.xmm .xmm1) q =
      byteOf ((#v[r0 3, r1 3, l0 3, l1 3] : Vector Word 4).getD (q / 4) 0) (3 - q % 4) := fun q hq => by
    rw [hr.bytes h1 q hq, BV.same_eval _ (cq q hq).2]
    simp only [BV.eval, sum, BitVec.xor_zero]
    exact ev 3 (by decide) q hq
  obtain ⟨f, rfl⟩ := hsame
  refine WP.mono (stores_wp (s := { s with xmm := f }) (B := B) (o := oB) h.base
    (by show _ ∈ s.wr; rw [h.wr]; exact hs.wr) hf (by decide))
    fun s₂ ⟨g₂, _, _, rd₂, wr₂, sy₂, f₂, v0, v1, v2, v3⟩ => ?_
  refine ⟨by rw [g₂]; exact h.base, by rw [g₂]; exact h.esp, rd₂.trans h.rd, wr₂.trans h.wr, sy₂.trans h.syms,
    f₂, fun l hl q hq => ?_⟩
  rcases (show l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 by omega_using [hl]) with rfl | rfl | rfl | rfl
  · exact (v0 q hq).trans (b0 q hq)
  · exact (v1 q hq).trans (b1 q hq)
  · exact (v2 q hq).trans (b2 q hq)
  · exact (v3 q hq).trans (b3 q hq)

/-- Block `l` of the scratch buffer's four. -/
abbrev blkAt (m : Mem) (B : BitVec 32) (l : Nat) : Spec.Seed.Block :=
  Spec.Seed.blockAt m (B.setWidth 64 + BitVec.ofNat 64 (608 + 16 * l))

/-- `crypt` enciphers the four blocks at byte 608 of the scratch buffer,
under the round keys in their places, and changes nothing else but the
five places. -/
theorem crypt_wp (hB : s.gpr Impl.Modes.X86.sb = B) (hs : ScrIn s B 178)
    (htab : s.mem.readW (B.setWidth 64) 32 = s.syms tableName) (hk : ∀ i < 32, KeyAt s.mem B i (rk i)) :
    WP isa crypt s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 608, 64⟩, ⟨B.setWidth 64 + BitVec.ofNat 64 16, 80⟩] s.mem s'.mem ∧
      (∀ i < 32, KeyAt s'.mem B i (rk i)) ∧
      ∀ l < 4, Spec.Aes.bytesAt s'.mem (B.setWidth 64 + BitVec.ofNat 64 (608 + 16 * l)) 16 =
        (Spec.Seed.crypt (keyOf rk) (blkAt s.mem B l)).toList := by
  show WP isa (.seq (.block cryptHead) (.seq (.loop (.block turn) .ne) (.block cryptTail))) s _
  refine WP.seq (WP.mono (cryptHead_wp hB hs htab hk) fun s₁ ⟨a₁, m₁, c₁, f₁, k₁, w0₁, w1₁, x5₁, x0₁⟩ => ?_)
  have hI : Inv s B rk (blkAt s.mem B) 8 s₁ :=
    ⟨Nat.le_refl _, a₁, m₁, c₁, f₁, k₁, bwd s.mem B 0, bwd s.mem B 1, bwd s.mem B 2, bwd s.mem B 3, fun _ => rfl,
      w0₁, w1₁, x5₁, x0₁⟩
  refine WP.seq (WP.mono (loop_wp hs (by decide) hI)
    fun s₂ ⟨_, a₂, m₂, _, f₂, k₂, l0, l1, r0, r1, h16, v0, v1, v5, vx⟩ => ?_)
  refine WP.mono (cryptTail_wp hs a₂ m₂ v0 v1 v5 vx) fun s₃ ⟨b₃, e₃, r₃, w₃, y₃, f₃, v₃⟩ => ⟨b₃, e₃, r₃, w₃, y₃, ?_, ?_, ?_⟩
  · exact (f₂.mono fun r hr => List.mem_cons_of_mem _ hr).trans (f₃.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_self)
  · intro i hi q hq
    rw [frame_sAt f₃ (.inl (by omega_using [hi, hq])) (by omega_using [hi, hq]) (by decide)]
    exact k₂ i hi q hq
  · intro l hl
    rw [Proof.Seed.crypt_eq, show Proof.Seed.roundsN (keyOf rk) 16 (Proof.Seed.decodeQ (blkAt s.mem B l)) =
        (l0 l, l1 l, r0 l, r1 l) from h16 l,
      show Proof.Seed.encodeSwapped (l0 l, l1 l, r0 l, r1 l) = Vector.ofFn fun i : Fin 16 =>
        byteOf ((#v[r0 l, r1 l, l0 l, l1 l] : Vector Word 4).getD (i.val / 4) 0) (3 - i.val % 4) from rfl]
    refine List.ext_getElem (by simp [Spec.Aes.bytesAt]) fun q h₁ _ => ?_
    have hq : q < 16 := by simpa [Spec.Aes.bytesAt] using h₁
    rw [Vector.getElem_toList, Vector.getElem_ofFn]
    simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range]
    have := v₃ l hl q hq
    rw [sAt, ← Offset.add_ofNat_add_ofNat] at this
    exact this

end

/-! ## The round keys `prepare` leaves -/

section

open VG.Impl.Modes.X86 (at_ argOp)

/-- The place of the schedule's round key `j`: its own, or, for decryption,
its round's in the reverse order of the rounds. -/
def pos : Direction → Nat → Nat
  | .encrypt, j => j
  | .decrypt, j => 4 * (7 - j / 4) + (j % 4 + 2) % 4

/-- The keys' pointer after `i` groups, from the scratch buffer's address. -/
def kpo : Direction → Nat → Nat
  | .encrypt, i => 96 + 64 * i
  | .decrypt, i => 544 - 64 * i

theorem pos_pos (d : Direction) {i : Nat} (hi : i < 32) : pos d (pos d i) = i := by
  cases d <;> simp only [pos] <;> omega_using [hi]

theorem pos_lt (d : Direction) {i : Nat} (hi : i < 32) : pos d i < 32 := by
  cases d <;> simp only [pos] <;> omega_using [hi]

/-- For decryption, the places of round `j`'s keys hold round `15 - j`'s. -/
theorem pos_decrypt {j : Nat} (hj : j < 16) :
    pos .decrypt (2 * j) = 2 * (15 - j) ∧ pos .decrypt (2 * j + 1) = 2 * (15 - j) + 1 := by
  simp only [pos]; omega_using [hj]

theorem kpo_zero (d : Direction) : kpo d 0 = keyBase d := by cases d <;> rfl

theorem kpo_bounds (d : Direction) {i : Nat} (hi : i < 8) : 96 ≤ kpo d i ∧ kpo d i + 64 ≤ 608 := by
  cases d <;> simp only [kpo] <;> omega_using [hi]

/-- The place of the key that goes to `kr + 16 w` in group `i`. -/
theorem place_eq (d : Direction) {i w : Nat} (hi : i < 8) (hw : w < 4) :
    96 + 16 * pos d (4 * i + keyIdx d w) = kpo d i + 16 * w := by
  cases d <;> simp only [pos, keyIdx, kpo] <;> omega_using [hi, hw]

theorem keyIdx_lt (d : Direction) {w : Nat} (hw : w < 4) : keyIdx d w < 4 := by
  cases d <;> simp only [keyIdx] <;> omega_using [hw]

theorem keyIdx_keyIdx (d : Direction) {w : Nat} (hw : w < 4) : keyIdx d (keyIdx d w) = w := by
  cases d <;> simp only [keyIdx] <;> omega_using [hw]

/-- The places of the keys of the groups before group `m` are outside its
four. -/
theorem place_out (d : Direction) {m j q : Nat} (hm : m < 8) (hj : j < 4 * m) (hq : q < 16) :
    96 + 16 * pos d j + q < kpo d m ∨ kpo d m + 64 ≤ 96 + 16 * pos d j + q := by
  cases d <;> simp only [pos, kpo] <;> omega_using [hm, hj, hq]

/-- What `prepare` needs of the state it starts in: the scratch buffer, and
the schedule, apart from it. -/
structure PEnv (s₀ : State) (B p : BitVec 32) : Prop where
  scr : ScrIn s₀ B 178
  sch : (⟨p.setWidth 64, 128⟩ : Region) ∈ s₀.rd ++ s₀.wr
  pfit : p.toNat + 128 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨p.setWidth 64, 128⟩ ⟨B.setWidth 64, 712⟩

/-- A state of `prepare d` after `i` groups of four round keys: the
schedule's pointer, the round keys' pointer, and the table's address. -/
structure PAt (d : Direction) (s₀ : State) (B p : BitVec 32) (i : Nat) (s : State) : Prop where
  base : s.gpr Impl.Modes.X86.sb = B
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  syms : s.syms = s₀.syms
  tb : s.gpr tbr = s₀.syms tableName
  sp : s.gpr .eax = p + BitVec.ofNat 32 (16 * i)
  kp : s.gpr kr = B + BitVec.ofNat 32 (kpo d i)

variable {d : Direction} {s₀ s : State} {B p : BitVec 32} {i : Nat} {M : Mem}

theorem PAt.kr64 (h : PAt d s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 8) :
    (s.gpr kr).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 (kpo d i) := by
  have hf := he.scr.fit
  have hb := kpo_bounds d hi
  rw [h.kp]; exact addr_eq (by omega_arith)

theorem PAt.krNat (h : PAt d s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 8) :
    (s.gpr kr).toNat = B.toNat + kpo d i := by
  have hf := he.scr.fit
  have hb := kpo_bounds d hi
  rw [h.kp, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := kpo d i) (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

theorem PAt.ax64 (h : PAt d s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 8) :
    (s.gpr .eax).setWidth 64 = p.setWidth 64 + BitVec.ofNat 64 (16 * i) := by
  have hf := he.pfit
  rw [h.sp]; exact addr_eq (by omega_arith)

theorem PAt.axNat (h : PAt d s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 8) :
    (s.gpr .eax).toNat = p.toNat + 16 * i := by
  have hf := he.pfit
  rw [h.sp, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 16 * i) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

theorem prepGroupOk_all (d : Direction) : prepGroupOk d = true := by
  cases d
  · exact prep_all.1
  · exact prep_all.2

/-- Four round keys of the schedule to their places (`prepGroupX d`). -/
theorem prepGroupX_wp (he : PEnv s₀ B p) (hi : i < 8) (h : PAt d s₀ B p i s) (hS : Sch M s.mem p) :
    WP isa (.block (prepGroupX d)) s fun s' => PAt d s₀ B p i s' ∧ s'.gpr .ecx = s.gpr .ecx ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (kpo d i), 64⟩] s.mem s'.mem ∧
      ∀ u < 4, KeyAt s'.mem B (pos d (4 * i + u)) (rkAt M p (4 * i + u)) := by
  have hf := he.scr.fit
  have hpf := he.pfit
  have hk := h.krNat he hi
  have ha := h.axNat he hi
  have hb := kpo_bounds d hi
  have rel : Rel pparams (envOf pparams s) Regs.init s :=
    rel_init (p := pparams) (by show s.gpr tbr = s.syms tableName; rw [h.tb, h.syms])
      (by show (s.gpr .eax).toNat + 16 ≤ _; omega_arith)
      fun o ho => ⟨_, by rw [h.rd, h.wr]; exact he.sch, by
        show Region.Contains _ (addr (s.gpr .eax) o) 16
        have ho' : o + 16 ≤ 16 := ho
        rw [addr_eq (by omega_arith), h.ax64 he hi, Offset.add_ofNat_add_ofNat]
        exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have ok : OutOk pparams poparams s := by
    refine ⟨by show (s.gpr kr).toNat + 64 ≤ _; omega_arith, fun o ho => ⟨_, by rw [h.wr]; exact he.scr.wr, ?_⟩, ?_,
      by show (s.gpr .eax).toNat + 16 ≤ _; omega_arith⟩
    · show Region.Contains _ (addr (s.gpr kr) o) 16
      have ho' : o + 16 ≤ 64 := ho
      rw [addr_eq (by omega_arith), h.kr64 he hi, Offset.add_ofNat_add_ofNat]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    · show Region.Disjoint ⟨(s.gpr .eax).setWidth 64, 16⟩ ⟨(s.gpr kr).setWidth 64, 64⟩
      rw [h.ax64 he hi, h.kr64 he hi]
      exact (he.sep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
  have hok := prepGroupOk_all d
  unfold prepGroupOk at hok
  split at hok <;> [cases hok; rename_i σ hrun]
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨o0, o1⟩, o2⟩, o3⟩, oin⟩ := hok
  refine runS_wp ok (RelS.init rel rfl) hrun fun s' hr => ?_
  have st : ∀ {w : Nat}, outOk σ.2 (16 * w) (pw d w) = true → w < 4 →
      KeyAt s'.mem B (pos d (4 * i + keyIdx d w)) (rkAt M p (4 * i + keyIdx d w)) := fun {w} ho hw4 q hq => by
    have h4 : q % 4 < 4 := Nat.mod_lt _ (by decide)
    have hu := keyIdx_lt d hw4
    have := hr.out ho hq
    rw [show (s.gpr poparams.oreg) = s.gpr kr from rfl, h.kr64 he hi, Offset.add_ofNat_add_ofNat] at this
    rw [sAt, show 96 + 16 * pos d (4 * i + keyIdx d w) + q = kpo d i + (16 * w + q) by
        rw [place_eq d hi hw4, Nat.add_assoc], this, pw, BV.eval, sum, BitVec.xor_zero, BitVec.xor_zero, kv,
      mask_bit _ (by show 128 + (4 * keyIdx d w + q % 4) < 1024; omega_using [hu]), envOf_key,
      show (s.gpr pparams.kreg) = s.gpr .eax from rfl, h.ax64 he hi, Offset.add_ofNat_add_ofNat,
      hS _ (by omega_using [hi, hu]), byteOf_rkAt _ _ (by omega_using [hi, hu]) h4]
    exact congrArg (fun o => M (p.setWidth 64 + BitVec.ofNat 64 o)) (by omega_arith)
  refine ⟨⟨by rw [hr.gpr]; exact h.base, by rw [hr.gpr]; exact h.esp, hr.rd.trans h.rd, hr.wr.trans h.wr,
    hr.syms.trans h.syms, by rw [hr.gpr]; exact h.tb, by rw [hr.gpr]; exact h.sp, by rw [hr.gpr]; exact h.kp⟩,
    by rw [hr.gpr], ?_, fun u hu => ?_⟩
  · have := hr.frameIn oin
    rw [show (s.gpr poparams.oreg) = s.gpr kr from rfl, h.kr64 he hi, Offset.add_ofNat_add_ofNat, Nat.add_zero,
      Nat.sub_zero] at this
    exact this
  · have hw := keyIdx_lt d hu
    have e := keyIdx_keyIdx d hu
    rcases (show keyIdx d u = 0 ∨ keyIdx d u = 1 ∨ keyIdx d u = 2 ∨ keyIdx d u = 3 by omega_using [hw]) with
      h0 | h0 | h0 | h0
    · have := st (w := 0) o0 (by decide); rwa [← h0, e] at this
    · have := st (w := 1) o1 (by decide); rwa [← h0, e] at this
    · have := st (w := 2) o2 (by decide); rwa [← h0, e] at this
    · have := st (w := 3) o3 (by decide); rwa [← h0, e] at this

/-- The schedule is outside what `prepare` writes. -/
theorem sch_frame {m m' : Mem} {a n : Nat} (h : Sch M m p) (he : PEnv s₀ B p)
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 a, n⟩] m m') (han : a + n ≤ 712) : Sch M m' p := fun o ho => by
  rw [← h o ho]
  refine hf.bytes (R := ⟨p.setWidth 64, 128⟩) (fun r hr => ?_) (by show (128 : Nat) ≤ 2 ^ 64; decide) ho
  rw [List.mem_singleton] at hr; subst hr
  exact he.sep.sub_right (Offset.sub_base _ han)

/-- `keyStep d`, the keys' pointer on by four places in `d`'s order. -/
theorem keyStep_wp {is : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ kr → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.syms = s.syms → (i < 8 → s.gpr kr = B + BitVec.ofNat 32 (kpo d i) →
      s'.gpr kr = B + BitVec.ofNat 32 (kpo d (i + 1))) → WP isa (.block is) s' Q) :
    WP isa (.block (keyStep d :: is)) s Q := by
  cases d
  · refine wp_addi_x fun s' u x => k s' u.other u.mem u.rd u.wr u.syms fun _ hk => ?_
    rw [u.gpr, hk, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, Offset.add_ofNat_add_ofNat]
    rfl
  · refine wp_subi_x fun s' u x _ => k s' u.other u.mem u.rd u.wr u.syms fun hi hk => ?_
    rw [u.gpr, hk, show kpo .decrypt i = kpo .decrypt (i + 1) + 64 by
        show 544 - 64 * i = 544 - 64 * (i + 1) + 64; omega_using [hi],
      BitVec.ofNat_add, ← BitVec.add_assoc]
    exact BitVec.add_sub_cancel _ _

/-- The loop's invariant, with `n` groups left, from the memory `m₁`. -/
def PInv (d : Direction) (s₀ : State) (M m₁ : Mem) (B p : BitVec 32) (n : Nat) (s : State) : Prop :=
  n ≤ 8 ∧ PAt d s₀ B p (8 - n) s ∧ s.gpr .ecx = BitVec.ofNat 32 n ∧ Sch M s.mem p ∧
    Frame [⟨B.setWidth 64 + BitVec.ofNat 64 96, 512⟩] m₁ s.mem ∧
    ∀ j < 4 * (8 - n), KeyAt s.mem B (pos d j) (rkAt M p j)

theorem pturn_wp {m₁ : Mem} (he : PEnv s₀ B p) {n : Nat} (hn : 1 ≤ n) (hI : PInv d s₀ M m₁ B p n s) :
    WP isa (.block (prepGroup d)) s fun s' => s'.zf = some (decide (n = 1)) ∧ PInv d s₀ M m₁ B p (n - 1) s' := by
  obtain ⟨hn8, a, hc, hS, hF, K⟩ := hI
  obtain ⟨m, hm'⟩ : ∃ m, m = 8 - n := ⟨_, rfl⟩
  rw [← hm'] at a K
  have hm8 : m < 8 := by omega_using [hn, hm']
  have hf := he.scr.fit
  have hb := kpo_bounds d hm8
  refine WP.block_append_iff.mpr (WP.mono (prepGroupX_wp he hm8 a hS) fun s₁ ⟨a₁, c₁, f₁, k₁⟩ => ?_)
  show WP isa (.block [.alu .add .eax (.imm 16), keyStep d, .alu .sub .ecx (.imm 1)]) s₁ _
  refine wp_addi_x fun s₂ u₂ x₂ => keyStep_wp (i := m) (B := B) fun s₃ o₃ m₃ rd₃ wr₃ sy₃ kp₃ =>
    wp_subi_x fun s₄ u₄ x₄ z₄ => WP.block_nil ?_
  have e₄ : s₄.mem = s₁.mem := by rw [u₄.mem, m₃, u₂.mem]
  have c₃ : s₃.gpr .ecx = BitVec.ofNat 32 n := by rw [o₃ _ (by decide), u₂.other _ (by decide), c₁, hc]
  refine ⟨?_, by omega_using [hn8], ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [z₄, c₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_beq (by omega_using [hn8]) (by decide)]
  · rw [show 8 - (n - 1) = m + 1 by omega_using [hn, hm', hn8]]
    refine ⟨?_, ?_, by rw [u₄.rd, rd₃, u₂.rd]; exact a₁.rd, by rw [u₄.wr, wr₃, u₂.wr]; exact a₁.wr,
      by rw [u₄.syms, sy₃, u₂.syms]; exact a₁.syms, ?_, ?_, ?_⟩
    · rw [u₄.other _ (by decide), o₃ _ (by decide), u₂.other _ (by decide)]; exact a₁.base
    · rw [u₄.other _ (by decide), o₃ _ (by decide), u₂.other _ (by decide)]; exact a₁.esp
    · rw [u₄.other _ (by decide), o₃ _ (by decide), u₂.other _ (by decide)]; exact a₁.tb
    · rw [u₄.other _ (by decide), o₃ _ (by decide), u₂.gpr, a₁.sp,
        show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, Offset.add_ofNat_add_ofNat]
      congr 2
    · rw [u₄.other _ (by decide)]
      exact kp₃ hm8 (by rw [u₂.other _ (by decide)]; exact a₁.kp)
  · rw [u₄.gpr, c₃]; exact Wp.ofNat_pred hn
  · rw [e₄]
    exact sch_frame hS he f₁ (by omega_arith)
  · rw [e₄]
    refine hF.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    rw [List.mem_singleton.mp hr]
    exact Offset.sub _ (by omega_arith) (by omega_arith)
  · rw [e₄]
    by_cases hj' : j < 4 * m
    · intro q hq
      have ho := place_out d hm8 hj' hq
      have hp := pos_lt d (show j < 32 by omega_using [hj', hm8])
      rw [frame_sAt f₁ (by omega_arith) (by omega_arith) (by omega_arith)]
      exact K j hj' q hq
    · have := k₁ (j - 4 * m) (by omega_using [hj, hj', hn, hm', hn8])
      rwa [show 4 * m + (j - 4 * m) = j by omega_using [hj']] at this

/-- The eight groups: the 32 round keys in their places. -/
theorem ploop_wp {m₁ : Mem} (he : PEnv s₀ B p) {n : Nat} (hn : 1 ≤ n) (hI : PInv d s₀ M m₁ B p n s) :
    WP isa (.loop (.block (prepGroup d)) .ne) s (PInv d s₀ M m₁ B p 0) := by
  refine WP.loop (M := isa) (fun n s => 1 ≤ n ∧ PInv d s₀ M m₁ B p n s) ?_ n s ⟨hn, hI⟩
  rintro n s ⟨hn, hI⟩
  refine WP.mono (pturn_wp he hn hI) fun s₁ ⟨z₁, i₁⟩ => ?_
  by_cases h1 : n = 1
  · subst h1
    exact .inl ⟨by show s₁.zf.map _ = _; rw [z₁]; rfl, i₁⟩
  · exact .inr ⟨by show s₁.zf.map _ = _; rw [z₁, decide_eq_false h1]; rfl, n - 1, by omega_using [hn],
      by omega_using [hn, h1], i₁⟩

/-- The table's address to the scratch buffer's first slot, and the
registers of the loop (`prepHead d`), with the table's address in `eax`. -/
theorem prepHead_wp (hB : s.gpr Impl.Modes.X86.sb = B) (he : PEnv s B p) (hax : s.gpr .eax = s.syms tableName)
    (hS : Sch M s.mem p) (hin0 : InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4)
    (hp : s.mem.readW (s.ea (argOp 0)) 32 = p)
    (h0B : Region.Disjoint ⟨s.ea (argOp 0), 4⟩ ⟨B.setWidth 64, 712⟩) :
    WP isa (.block (prepHead d)) s fun s' => PAt d s B p 0 s' ∧ s'.gpr .ecx = BitVec.ofNat 32 8 ∧ Sch M s'.mem p ∧
      Frame [⟨B.setWidth 64, 4⟩] s.mem s'.mem ∧ s'.mem.readW (B.setWidth 64) 32 = s.syms tableName := by
  have hf := he.scr.fit
  have hpf := he.pfit
  have ha0 : addr B 0 = B.setWidth 64 := by rw [addr_eq (by omega_arith), BitVec.add_zero]
  have hw : InRegions s.wr (addr B 0) 4 := ⟨_, he.scr.wr, by
    rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  show WP isa (.block (.store ⟨Impl.Modes.X86.sb, 0⟩ .eax :: .mov tbr (.reg .eax) ::
    .mov .eax (.mem ⟨.esp, 4 + 4 * 0⟩) :: .mov kr (.reg Impl.Modes.X86.sb) ::
    .alu .add kr (.imm (BitVec.ofNat 32 (keyBase d))) :: [.mov .ecx (.imm 8)])) s _
  refine Wp.wp_stm hB hw fun s₂ u₂ => ?_
  have f₂ : Frame [⟨B.setWidth 64, 4⟩] s.mem s₂.mem := by
    rw [u₂.mem, ha0]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 4)
  have sub4 : Region.Sub ⟨B.setWidth 64, 4⟩ ⟨B.setWidth 64, 712⟩ := Region.sub_prefix (by decide)
  have e0 : s₂.mem.readW (s.ea (argOp 0)) 32 = p := by
    rw [f₂.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h0B.sub_right sub4) (by decide), hp]
  refine Wp.wp_mov fun s₃ u₃ => ?_
  refine Wp.wp_ldm (B := s.gpr .esp) (by rw [u₃.other _ (by decide), u₂.gpr]) (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact hin0)
    fun s₄ u₄ => ?_
  refine Wp.wp_mov fun s₅ u₅ => ?_
  refine Wp.wp_addi fun s₆ u₆ => ?_
  refine Wp.wp_movi fun s₇ u₇ => WP.block_nil ?_
  have m₇ : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have r₇ : s₇.rd = s.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd]
  have w₇ : s₇.wr = s.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]
  have y₇ : s₇.syms = s.syms := by rw [u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms]
  have b₇ : s₇.gpr Impl.Modes.X86.sb = B := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, hB]
  have sp₇ : s₇.gpr .esp = s.gpr .esp := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr]
  have t₇ : s₇.gpr tbr = s.syms tableName := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.gpr, hax]
  have a₇ : s₇.gpr .eax = p := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem]
    exact e0
  have c₇ : s₇.gpr .ecx = BitVec.ofNat 32 8 := by rw [u₇.gpr]; rfl
  have k₇ : s₇.gpr kr = B + BitVec.ofNat 32 (kpo d 0) := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hB, kpo_zero]
  have hS₇ : Sch M s₇.mem p := by
    rw [m₇]
    exact sch_frame (a := 0) hS he (by rw [BitVec.add_zero]; exact f₂) (by decide)
  refine ⟨⟨b₇, sp₇, r₇, w₇, y₇, t₇, by rw [a₇]; simp, k₇⟩, c₇, hS₇, by rw [m₇]; exact f₂, ?_⟩
  rw [m₇, u₂.mem, ha0, Mem.readW_writeW_self32, hax]

/-- `prepare d` leaves the round keys of the schedule in their places, in
`d`'s order, and the table's address in the scratch buffer's first slot; it
writes only the core's slots before the four blocks, and the four bytes
below `esp` of the frame that gets the table's address. -/
theorem prepare_wp (d : Direction) (hB : s.gpr Impl.Modes.X86.sb = B) (he : PEnv s B p)
    (hesp : 4 ≤ (s.gpr .esp).toNat) (hin0 : InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4)
    (hp : s.mem.readW (s.ea (argOp 0)) 32 = p)
    (h0B : Region.Disjoint ⟨s.ea (argOp 0), 4⟩ ⟨B.setWidth 64, 712⟩)
    (hkS : Region.Disjoint (below (s.gpr .esp) 4) ⟨p.setWidth 64, 128⟩)
    (h0S : Region.Disjoint (below (s.gpr .esp) 4) ⟨s.ea (argOp 0), 4⟩) :
    WP isa (prepare d) s fun s' => (∀ i < 32, KeyAt s'.mem B (pos d i) (rkAt s.mem p i)) ∧
      s'.mem.readW (B.setWidth 64) 32 = s.syms tableName ∧ s'.gpr Impl.Modes.X86.sb = B ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64, 608⟩, below (s.gpr .esp) 4] s.mem s'.mem := by
  have hf := he.scr.fit
  show WP isa (.seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1)) (.seq (.block (prepHead d))
    (.loop (.block (prepGroup d)) .ne))) s _
  refine WP.seq (WP.mono (symFrame_ok tableName s hesp) fun s₁ a₁ => ?_)
  have esp₁ : s₁.gpr .esp = s.gpr .esp := a₁.gpr .esp (by decide)
  have ea₁ : ∀ k, s₁.ea (argOp k) = s.ea (argOp k) := fun k => by
    show addr (s₁.gpr .esp) _ = addr (s.gpr .esp) _
    rw [esp₁]
  have he₁ : PEnv s₁ B p :=
    ⟨⟨by rw [a₁.wr]; exact he.scr.wr, he.scr.fit⟩, by rw [a₁.rd, a₁.wr]; exact he.sch, he.pfit, he.sep⟩
  have hS₁ : Sch s.mem s₁.mem p := fun o ho =>
    a₁.frame.bytes (R := ⟨p.setWidth 64, 128⟩) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hkS.symm) (by show (128 : Nat) ≤ 2 ^ 64; decide) ho
  have p₁ : s₁.mem.readW (s.ea (argOp 0)) 32 = p := by
    rw [a₁.frame.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h0S.symm) (by decide), hp]
  refine WP.seq (WP.mono (prepHead_wp (d := d) (M := s.mem) (by rw [a₁.gpr _ (by decide)]; exact hB) he₁
    (by rw [a₁.addr, a₁.syms]) hS₁ (by rw [ea₁, a₁.rd, a₁.wr]; exact hin0) (by rw [ea₁]; exact p₁)
    (by rw [ea₁]; exact h0B)) fun s₂ ⟨a₂, c₂, hS₂, f₂, t₂⟩ => ?_)
  have hI : PInv d s₁ s.mem s₂.mem B p 8 s₂ :=
    ⟨Nat.le_refl _, a₂, c₂, hS₂, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  refine WP.mono (ploop_wp he₁ (by decide) hI) fun s₃ ⟨_, a₃, _, _, F₃, K₃⟩ => ?_
  refine ⟨K₃, ?_, a₃.base, a₃.esp.trans esp₁, a₃.rd.trans a₁.rd, a₃.wr.trans a₁.wr, a₃.syms.trans a₁.syms, ?_⟩
  · rw [F₃.readW (r := ⟨B.setWidth 64, 4⟩) (Region.contains_self _ 4) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by decide) (by decide)) (by decide), t₂, a₁.syms]
  · refine ((a₁.frame.mono fun r hr => ?_).trans (f₂.sub fun r hr => ?_)).trans (F₃.sub fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩

end

/-! ## The core -/

section

open VG.Impl.Modes.X86 (at_ argOp)
open VG.Proof.Modes.X86 (coreRegion blkRegion blkAddr stkRegion slotA CoreSpec Layout)
open VG.Proof.Seed.X86.AesNi (KeyArgs keyArgs_congr)
open VG.Proof.Seed (dirCipher)

/-- The key `k` is ready in the scratch buffer at `B`, for the direction
`d`: its round keys in their places, in `d`'s order, and the table's
address in the first slot. -/
def Ready (d : Direction) (s : State) (B : BitVec 32) (k : Spec.Seed.Schedule) : Prop :=
  (∀ i < 32, KeyAt s.mem B i (k.getD (pos d i) 0)) ∧ s.mem.readW (B.setWidth 64) 32 = s.syms tableName ∧
    B.toNat + 712 ≤ 2 ^ 32

theorem core_slots (d : Direction) : (core d).slots = 168 := rfl

/-- The key stays ready through what a mode writes outside the core's slots
or within its four blocks. -/
theorem ready_frame {d : Direction} {s s' : State} {B : BitVec 32} {k : Spec.Seed.Schedule} {rs : List Region}
    (h : Ready d s B k) (hsy : s'.syms = s.syms) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (core d) B) r ∨ Region.Sub r (blkRegion (core d) B)) :
    Ready d s' B k := by
  obtain ⟨hk, ht, hfit⟩ := h
  have keep : ∀ {a n : Nat}, a + n ≤ 608 → ∀ r ∈ rs,
      Region.Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 a, n⟩ r := fun {a n} h₁ r hr => by
    rcases hd r hr with h | h
    · exact h.sub_left (Offset.sub_base _ (by rw [core_slots]; omega_arith))
    · exact (Offset.disjoint (B.setWidth 64) (d := a) (n := n) (e := 4 * (core d).buf)
        (k := 4 * (core d).bw * (core d).G) (by show a + n ≤ 608 ∨ 608 + 64 ≤ a; omega_arith) (by omega_arith)
        (by show 4 * 152 + 4 * 4 * 4 ≤ 2 ^ 64; decide)).sub_right h
  refine ⟨fun i hi q hq => ?_, ?_, hfit⟩
  · have := hf.bytes (R := ⟨B.setWidth 64 + BitVec.ofNat 64 (96 + 16 * i + q), 1⟩)
      (keep (by omega_arith)) (by show (1 : Nat) ≤ 2 ^ 64; decide) (i := 0) (show (0 : Nat) < 1 by decide)
    rw [BitVec.add_zero] at this
    rw [sAt, this]
    exact hk i hi q hq
  · have e := hf.readW (r := ⟨B.setWidth 64 + BitVec.ofNat 64 0, 4⟩) (a := B.setWidth 64 + BitVec.ofNat 64 0)
      (w := 32) (Region.contains_self _ 4) (keep (by decide)) (by decide)
    rw [BitVec.add_zero] at e
    rw [e, hsy]; exact ht

theorem prepare_ok {d : Direction} {s : State} {B : BitVec 32} {rs : List Region} {k : Spec.Seed.Schedule}
    (hB : s.gpr Impl.Modes.X86.sb = B) (hs : ScrIn s B (core d).total)
    (hR : (⟨B.setWidth 64, 4 * (core d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k)
    (hsp : (core d).stack ≤ (s.gpr .esp).toNat) :
    WP isa (core d).prepare s fun s' => Ready d s' B k ∧ s'.gpr Impl.Modes.X86.sb = B ∧
      s'.gpr .esp = s.gpr .esp ∧
      Frame [coreRegion (core d) B, stkRegion (s.gpr .esp) (core d).stack] s.mem s'.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨p, hin0, hp, hk, hsch, hfit, hdis, hd0, hkS, h0S⟩ := hk
  have he : PEnv s B p := ⟨hs, hsch, hfit, hdis _ hR⟩
  refine WP.mono (prepare_wp d hB he hsp hin0 hp (hd0 _ hR) hkS h0S) fun s' ⟨K, t, b, e, rd, wr, sy, f⟩ => ?_
  refine ⟨⟨fun i hi => ?_, by rw [t, sy], hs.fit⟩, b, e, f.sub fun r hr => ?_, rd, wr⟩
  · have := K (pos d i) (pos_lt d hi)
    rw [pos_pos d hi] at this
    rw [hk]
    exact this
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by show 608 ≤ 4 * 168; decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

private theorem ofFn_toList (v : Spec.Seed.Block) : (Vector.ofFn fun i : Fin 16 => v.toList.getD i.val 0) = v := by
  apply Vector.ext; intro i hi
  simp

/-- The cipher of `d` on the 16 bytes at `p`: the rounds under the round
keys in `d`'s order (RFC 4269 §2.4 for decryption). -/
theorem dirCipher_bytes (d : Direction) (k : Spec.Seed.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (Spec.Aes.bytesAt m p 16) =
      (Spec.Seed.crypt (keyOf fun i => k.getD (pos d i) 0) (Spec.Seed.blockAt m p)).toList := by
  cases d
  · rw [dirCipher, Spec.Seed.cipher, Proof.Seed.bytesAt_eq, ofFn_toList]; rfl
  · rw [dirCipher, Spec.Seed.invCipher, Proof.Seed.bytesAt_eq, ofFn_toList, Spec.Seed.decryptBlock]
    refine congrArg Vector.toList (Proof.Seed.crypt_congr (fun j hj => ?_) _)
    show Spec.Seed.roundKey k (15 - j) = (k.getD (pos .decrypt (2 * j)) 0, k.getD (pos .decrypt (2 * j + 1)) 0)
    rw [(pos_decrypt hj).1, (pos_decrypt hj).2]
    rfl

theorem crypt_ok {d : Direction} {s : State} {B : BitVec 32} {k : Spec.Seed.Schedule}
    (hB : s.gpr Impl.Modes.X86.sb = B) (hs : ScrIn s B (core d).total) (hr : Ready d s B k) :
    WP isa (core d).crypt s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ Ready d s' B k ∧
      Frame [coreRegion (core d) B, stkRegion (s.gpr .esp) (core d).stack] s.mem s'.mem ∧
      (∀ j < (core d).G, Spec.Aes.bytesAt s'.mem (blkAddr (core d) B j) (4 * (core d).bw) =
        dirCipher d k (Spec.Aes.bytesAt s.mem (blkAddr (core d) B j) (4 * (core d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hk, ht, hfit⟩ := hr
  refine WP.mono (crypt_wp hB hs ht hk) fun s' ⟨b, e, rd, wr, sy, f, k', v⟩ => ?_
  have hblk : ∀ j, blkAddr (core d) B j = B.setWidth 64 + BitVec.ofNat 64 (608 + 16 * j) := fun j => by
    show B.setWidth 64 + BitVec.ofNat 64 (4 * 152) + BitVec.ofNat 64 (4 * 4 * j) = _
    rw [Offset.add_ofNat_add_ofNat]
  refine ⟨b, e, ⟨k', ?_, hfit⟩, f.sub fun r hr => ?_, fun j hj => ?_, rd, wr⟩
  · rw [f.readW (r := ⟨B.setWidth 64, 4⟩) (Region.contains_self _ 4) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.base_disjoint _ (by decide) (by decide)
      · exact Offset.base_disjoint _ (by decide) (by decide)) (by decide), sy]
    exact ht
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by show 608 + 64 ≤ 4 * 168; decide)⟩
    · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by show 16 + 80 ≤ 4 * 168; decide)⟩
  · rw [hblk, show 4 * (core d).bw = 16 from rfl, dirCipher_bytes]
    exact v j hj

/-- SEED's core by the AES S-box for four blocks, in the direction `d`,
meets what the modes need. -/
def coreSpec (d : Direction) : CoreSpec (core d) where
  Key := Spec.Seed.Schedule
  cipher k := dirCipher d k
  KeyArgs := KeyArgs
  Ready := Ready d
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher, core]
  layout := ⟨by show 0 < 4; decide, .inr rfl, by show 152 + 4 * 4 ≤ 168; decide,
    by show 168 + 10 ≤ 168 + 10; decide⟩
  keyArgs_congr h e r w _ f := keyArgs_congr h e r w f
  ready_frame h _ _ _ sy f _ hd := ready_frame h sy f hd
  prepare_wp hB hs hR hk hsp := prepare_ok hB hs hR hk hsp
  crypt_wp hB hs hr _ := crypt_ok hB hs hr

end

end VG.Proof.Seed.X86.AesNiWide
