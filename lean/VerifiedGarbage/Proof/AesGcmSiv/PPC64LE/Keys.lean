module

import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Derive
public import VerifiedGarbage.Proof.GcmSiv.Words
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesGcmSiv.PPC64LE
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Callee
public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Env
public import VerifiedGarbage.Proof.Cmac.Block
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Spec.GcmSiv

/-!
# AES-GCM-SIV on PPC64LE: the keys (`keys`)

Untrusted: everything here is checked by Lean. After `derive`
(`Proof/AesGcmSiv/PPC64LE/Derive.lean`), `expand` expands the encryption key
at `W + 32` to its schedule at `W + 256` by a call of
`vg_aes_expand_key_scratch` (`expand_wp`), and `hkey` computes GHASH's key
`H · x` at `W + 64`, in GHASH's order (`stdbrx`), from the authentication key
`H` at `W + 16` as a little-endian number, and zeroes the accumulator at
`W + 80` (`hkey_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.PPC64LE

open VG VG.Impl.AesGcmSiv.PPC64LE
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_addi wp_li wp_ld wp_std wp_lsl wp_lsr wp_sub wp_subi wp_and
  wp_or wp_xor wp_lis)
open VG.Proof.AesCcm.PPC64LE (wp_stdbrx)
open VG.Proof.AesGcm.PPC64LE (KeyCall KeyPost key_call)
open VG.Proof.GcmSiv.Words (hkeyOf)
open VG.Spec.Aes (bytesAt)

/-! ## `expand` -/

/-- What `expand` leaves: the schedule of the encryption key at `W + 256`. -/
structure ExpPost (c : Cx) (t t' : State) : Prop where
  pk : PK t t'
  frame : Frame [⟨c.W + BitVec.ofNat 64 256, 240⟩, ⟨c.W + BitVec.ofNat 64 1776, 512⟩] t.mem t'.mem
  ciph : Spec.GcmSiv.ctxCiph t'.mem (c.W + BitVec.ofNat 64 256) c.R =
    Spec.GcmSiv.aes (bytesAt t.mem (c.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen c.R))

theorem keyLen_lsl {R : Nat} (hR : R = 10 ∨ R = 14) :
    (BitVec.ofNat 64 R - BitVec.ofNat 64 6) <<< 2 = BitVec.ofNat 64 (Spec.GcmSiv.keyLen R) := by
  rw [ofNat_sub (by omega) (by omega), ofNat_shl]
  unfold Spec.GcmSiv.keyLen; rcases hR with h | h <;> subst h <;> rfl

/-- The arguments of `expand`'s call. -/
theorem expArgs_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) :
    WP isa (.block expandArgs) t fun t₅ => PK t t₅ ∧ t₅.mem = t.mem ∧
      KeyCall t₅ (c.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen c.R) (c.W + BitVec.ofNat 64 256)
        (c.W + BitVec.ofNat 64 1776) := by
  have hR := L.rounds
  have hl : Spec.GcmSiv.keyLen c.R = 16 ∨ Spec.GcmSiv.keyLen c.R = 32 := by
    unfold Spec.GcmSiv.keyLen; rcases hR with h | h <;> rw [h] <;> decide
  unfold expandArgs
  refine wp_addi (by decide) (by decide) fun t₁ u₁ => wp_subi (by decide) (by decide) fun t₂ u₂ =>
    wp_lsl (by decide) fun t₃ u₃ => wp_addi (by decide) (by decide) fun t₄ u₄ =>
    wp_addi (by decide) (by decide) fun t₅ u₅ => WP.block_nil ?_
  have pk₅ : PK t t₅ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    (PK.ofUpd u₅))))
  have E₅ := E.of_pk pk₅
  refine ⟨pk₅, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], ?_⟩
  exact
    { r3 := by
        rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
          E.r14] <;> rfl
      r4 := by
        rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), E.r17,
          keyLen_lsl hR]
      r5 := by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), E.r14] <;> rfl
      r6 := by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), E.r14] <;> rfl
      kl_ok := by omega
      kc := L.w_w (.inl (by omega)) (by omega) (by decide)
      ks := L.w_w (.inl (by omega)) (by omega) (by decide)
      cs := L.w_w (.inl (by decide)) (by decide) (by decide)
      reads := Covers.append_left (Covers.cons (E₅.perm.wCR (by omega)) Covers.nil)
        (Covers.cons (E₅.perm.wCR (by decide)) (Covers.cons (E₅.perm.wCR (by decide)) Covers.nil))
      writes := Covers.cons (E₅.perm.wC (by decide)) (Covers.cons (E₅.perm.wC (by decide)) Covers.nil) }

theorem expand_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) : WP isa expand t (ExpPost c t) := by
  have hR := L.rounds
  unfold expand
  refine WP.seq (WP.mono (expArgs_wp L E) fun t₅ ⟨pk₅, hm₅, kc⟩ => ?_)
  refine WP.mono (key_call kc) fun t₆ P => ⟨pk₅.trans (PK.ofSaved P.rd P.wr P.sp P.saved), by rw [← hm₅]; exact P.frame, ?_⟩
  have hr : Spec.Aes.rounds (Spec.GcmSiv.keyLen c.R / 4) = c.R := by
    unfold Spec.Aes.rounds Spec.GcmSiv.keyLen; rcases hR with h | h <;> rw [h]
  have out := P.out
  rw [hr] at out
  rw [Spec.GcmSiv.ctxCiph, out, Spec.GcmSiv.aes, Proof.Cmac.bytesAt_length, hr, hm₅]

/-! ## `hkey` -/

/-- GHASH's key from the halves `hi` and `lo` of the authentication key (as
a little-endian number), as `hkey` computes it: its high half and its low
half. -/
abbrev hkHi (hi lo : BitVec 64) : BitVec 64 := (hi >>> 1) ^^^ (0xE100000000000000#64 &&& (0#64 - (lo &&& 1#64)))
abbrev hkLo (hi lo : BitVec 64) : BitVec 64 := (lo >>> 1) ||| (hi &&& 1#64).rotateRight 1

/-- The memory `hkey` leaves. -/
def hkeyMem (m : Mem) (W : Addr) : Mem :=
  let lo := m.readW (W + BitVec.ofNat 64 16) 64
  let hi := m.readW (W + BitVec.ofNat 64 24) 64
  Proof.Cmac.zero2 ((m.writeW (W + BitVec.ofNat 64 64) (rev64 (hkHi hi lo))).writeW (W + BitVec.ofNat 64 64 + BitVec.ofNat 64 8)
    (rev64 (hkLo hi lo))) (W + BitVec.ofNat 64 80)

theorem shl63 (x : BitVec 64) : x <<< 63 = (x &&& 1#64).rotateRight 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_rotateRight, BitVec.getLsbD_and]
  by_cases h63 : i < 63
  · simp [h63, BitVec.getLsbD_one]
  · have : i = 63 := by omega
    subst this; simp

theorem lis_e100 : (((0xe100 : BitVec 16) ++ (0 : BitVec 16)).signExtend 64) <<< 32 = 0xE100000000000000#64 := by
  decide

theorem hkeyMem_frame (m : Mem) (W : Addr) : Frame [⟨W + BitVec.ofNat 64 64, 32⟩] m (hkeyMem m W) := by
  unfold hkeyMem Proof.Cmac.zero2
  exact ((Proof.Cmac.frame_store2 (W + BitVec.ofNat 64 64) _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub W (d := 64) (e := 64) (by decide) (by decide)⟩).trans
    ((Proof.Cmac.frame_store2 (W + BitVec.ofNat 64 80) _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub W (d := 80) (e := 64) (by decide) (by decide)⟩)

theorem hkeyMem_key (m : Mem) (W : Addr) :
    Spec.Gcm.blockAt (hkeyMem m W) (W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt m (W + BitVec.ofNat 64 16) 16)) := by
  have hs : Mem.Sep (W + BitVec.ofNat 64 64) (64 / 8) (W + BitVec.ofNat 64 64 + BitVec.ofNat 64 8) (64 / 8) := by
    simpa using Offset.sep (W + BitVec.ofNat 64 64) (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide)
      (by decide)
  unfold hkeyMem Proof.Cmac.zero2
  dsimp only
  rw [blockAt_frame (Proof.Cmac.frame_store2 _ _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)),
    ← Proof.Gcm.PPC64LE.blockAt_rev, BitVec.add_zero,
    Mem.readW_writeW_sep hs (by decide),
    Mem.readW_writeW_self64, Mem.readW_writeW_self64, Proof.Gcm.PPC64LE.rev64_rev64,
    Proof.Gcm.PPC64LE.rev64_rev64, GcmSiv.Words.hkeyOf_words, GcmSiv.ofBytes_bytesAt, Offset.add_add]

theorem hkeyMem_acc (m : Mem) (W : Addr) : Spec.Gcm.blockAt (hkeyMem m W) (W + BitVec.ofNat 64 80) = 0 := by
  unfold hkeyMem
  rw [Spec.Gcm.blockAt, Proof.Cmac.zero2_bytes]
  decide

/-- `hkey`: GHASH's key at `W + 64` and its accumulator zeroed at `W + 80`. -/
theorem hkey_wp {c : Cx} {t : State} (E : Env c t) :
    WP isa (.block hkey) t fun t' => PK t t' ∧ t'.mem = hkeyMem t.mem c.W := by
  unfold hkey zero16
  simp only [List.cons_append, List.nil_append]
  refine wp_ld (a := c.W + BitVec.ofNat 64 16) (by decide) (by decide) (by rw [E.r14] <;> rfl)
    (E.perm.wR (by decide)) fun t₁ u₁ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 24) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), E.r14] <;> rfl) (by rw [u₁.rd, u₁.wr]; exact E.perm.wR (by decide))
    fun t₂ u₂ => ?_
  refine wp_li (by decide) fun t₃ u₃ => wp_and fun t₄ u₄ => wp_li (by decide) fun t₅ u₅ => wp_sub fun t₆ u₆ =>
    wp_lsr (by decide) fun t₇ u₇ => wp_lsl (by decide) fun t₈ u₈ => wp_or fun t₉ u₉ =>
    wp_lsr (by decide) fun t₁₀ u₁₀ => wp_lis fun t₁₁ u₁₁ => wp_lsl (by decide) fun t₁₂ u₁₂ =>
    wp_and fun t₁₃ u₁₃ => wp_xor fun t₁₄ u₁₄ => wp_li (by decide) fun t₁₅ u₁₅ => ?_
  have g₁₅ : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → t₁₅.gpr r = t.gpr r :=
    fun r h3 h4 h5 h6 h7 => by
      rw [u₁₅.other _ h7, u₁₄.other _ h4, u₁₃.other _ h5, u₁₂.other _ h6, u₁₁.other _ h6, u₁₀.other _ h4,
        u₉.other _ h3, u₈.other _ h6, u₇.other _ h3, u₆.other _ h5, u₅.other _ h6, u₄.other _ h5, u₃.other _ h5,
        u₂.other _ h4, u₁.other _ h3]
  have w14 : t₁₅.gpr .r14 = c.W := by rw [g₁₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), E.r14]
  have rw₁₅ : t₁₅.wr = t.wr := by
    rw [u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine wp_stdbrx (ea := c.W + BitVec.ofNat 64 64) (by decide) (by rw [w14, u₁₅.gpr]; rfl)
    (by rw [rw₁₅]; exact E.perm.wW (by decide)) fun t₁₆ u₁₆ => ?_
  refine wp_li (by decide) fun t₁₇ u₁₇ => ?_
  refine wp_stdbrx (ea := c.W + BitVec.ofNat 64 64 + BitVec.ofNat 64 8) (by decide)
    (by rw [u₁₇.other _ (by decide), u₁₆.gpr, w14, u₁₇.gpr, Offset.add_add] <;> rfl)
    (by rw [u₁₇.wr, u₁₆.wr, rw₁₅, Offset.add_add]; exact E.perm.wW (by decide)) fun t₁₈ u₁₈ => ?_
  refine wp_li (by decide) fun t₁₉ u₁₉ => ?_
  have w14' : t₁₉.gpr .r14 = c.W := by
    rw [u₁₉.other _ (by decide), u₁₈.gpr, u₁₇.other _ (by decide), u₁₆.gpr, w14]
  refine wp_std (a := c.W + BitVec.ofNat 64 80) (by decide) (by decide) (by rw [w14'] <;> rfl)
    (by rw [u₁₉.wr, u₁₈.wr, u₁₇.wr, u₁₆.wr, rw₁₅]; exact E.perm.wW (by decide)) fun t₂₀ u₂₀ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 80 + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₂₀.gpr, w14', Offset.add_add] <;> rfl)
    (by rw [u₂₀.wr, u₁₉.wr, u₁₈.wr, u₁₇.wr, u₁₆.wr, rw₁₅, Offset.add_add]; exact E.perm.wW (by decide))
    fun t₂₁ u₂₁ => WP.block_nil ?_
  refine ⟨(PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans ((PK.ofUpd u₅).trans
    ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans ((PK.ofUpd u₉).trans ((PK.ofUpd u₁₀).trans
    ((PK.ofUpd u₁₁).trans ((PK.ofUpd u₁₂).trans ((PK.ofUpd u₁₃).trans ((PK.ofUpd u₁₄).trans ((PK.ofUpd u₁₅).trans
    ((PK.ofMupd u₁₆).trans ((PK.ofUpd u₁₇).trans ((PK.ofMupd u₁₈).trans ((PK.ofUpd u₁₉).trans ((PK.ofMupd u₂₀).trans
    (PK.ofMupd u₂₁)))))))))))))))))))), ?_⟩
  -- The two words computed.
  have e3 : t₁₄.gpr .r3 = hkLo (t.mem.readW (c.W + BitVec.ofNat 64 24) 64) (t.mem.readW (c.W + BitVec.ofNat 64 16) 64) := by
    rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₈.gpr, u₇.gpr, u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₁.mem, shl63]
  have e4 : t₁₄.gpr .r4 = hkHi (t.mem.readW (c.W + BitVec.ofNat 64 24) 64) (t.mem.readW (c.W + BitVec.ofNat 64 16) 64) := by
    rw [u₁₄.gpr, u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr,
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem,
      u₁₃.gpr, u₁₂.gpr, u₁₁.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.gpr,
      u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, lis_e100,
      BitVec.and_comm]
  rw [u₂₁.mem, u₂₀.gpr, u₂₀.mem, u₁₉.gpr, u₁₉.mem, u₁₈.mem, u₁₇.other .r3 (by decide), u₁₇.mem, u₁₆.gpr,
    u₁₆.mem, u₁₅.other .r3 (by decide), u₁₅.other .r4 (by decide), e3, e4, u₁₅.mem, u₁₄.mem, u₁₃.mem,
    u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  rfl

/-! ## `keys` -/

/-- What `keys` writes: the keys, GHASH's key and accumulator, the blocks
the calls use, the encryption key's schedule and the working spaces. -/
abbrev keyR (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 112⟩, ⟨W + BitVec.ofNat 64 240, 16⟩, ⟨W + BitVec.ofNat 64 256, 3568⟩]

/-- What `keys` leaves, from `σ`. -/
structure KeysPost (c : Cx) (σ t : State) : Prop where
  env : Env c t
  pk : PK σ t
  frame : Frame (keyR c.W) σ.mem t.mem
  auth : (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem c.K c.R) (Spec.GcmSiv.keyLen c.R)
    (bytesAt σ.mem c.N 12)).1 = bytesAt t.mem (c.W + BitVec.ofNat 64 16) 16
  ciph : Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R = Spec.GcmSiv.aes
    (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem c.K c.R) (Spec.GcmSiv.keyLen c.R)
      (bytesAt σ.mem c.N 12)).2
  hkey : Spec.Gcm.blockAt t.mem (c.W + BitVec.ofNat 64 64) =
    hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (c.W + BitVec.ofNat 64 16) 16))
  acc : Spec.Gcm.blockAt t.mem (c.W + BitVec.ofNat 64 80) = 0

theorem keys_wp {c : Cx} (L : Lay c) {σ : State} (E : Env c σ) : WP isa keys σ (KeysPost c σ) := by
  have hR := L.rounds
  unfold keys
  refine WP.seq (WP.mono (derive_wp L E) fun t₂ I => ?_)
  have k0 : (⟨c.W + BitVec.ofNat 64 16, 112⟩ : Region) ∈ keyR c.W := List.mem_cons_self
  have k1 : (⟨c.W + BitVec.ofNat 64 240, 16⟩ : Region) ∈ keyR c.W := List.mem_cons_of_mem _ List.mem_cons_self
  have k2 : (⟨c.W + BitVec.ofNat 64 256, 3568⟩ : Region) ∈ keyR c.W :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have f₂ : Frame (keyR c.W) σ.mem t₂.mem := I.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, k0, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k0, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k1, fun _ h => h⟩
    · exact ⟨_, k2, Offset.sub _ (by decide) (by decide)⟩
  refine WP.seq (WP.mono (expand_wp L I.env) fun t₃ X => ?_)
  have E₃ := I.env.of_pk X.pk
  refine WP.mono (hkey_wp E₃) fun t₄ ⟨pk₄, hm₄⟩ => ?_
  have dK : ∀ {d k : Nat}, d + k ≤ 64 → 16 ≤ d → ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 256, 240⟩ : Region),
      ⟨c.W + BitVec.ofNat 64 1776, 512⟩], (⟨c.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact L.w_w (.inl (by omega)) (by omega) (by decide)
  have f₃ : Frame (keyR c.W) t₂.mem t₃.mem := X.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨_, k2, Offset.sub _ (by decide) (by decide)⟩
  have f₄ : Frame (keyR c.W) t₃.mem t₄.mem := by
    rw [hm₄]; exact (hkeyMem_frame _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, k0, Offset.sub _ (by decide) (by decide)⟩
  have dH : ∀ {d k : Nat}, d + k ≤ 64 → ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 32⟩ : Region)],
      (⟨c.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl h) (by omega) (by decide)
  have dH' : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 32⟩ : Region)],
      (⟨c.W + BitVec.ofNat 64 256, 240⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)
  have keys := I.keys L
  have a₃ : bytesAt t₃.mem (c.W + BitVec.ofNat 64 16) 16 = bytesAt t₂.mem (c.W + BitVec.ofNat 64 16) 16 :=
    Proof.Cmac.bytesAt_frame X.frame (dK (by decide) (by decide)) (by decide)
  have a₄ : bytesAt t₄.mem (c.W + BitVec.ofNat 64 16) 16 = bytesAt t₃.mem (c.W + BitVec.ofNat 64 16) 16 := by
    rw [hm₄]; exact Proof.Cmac.bytesAt_frame (hkeyMem_frame _ _) (dH (by decide)) (by decide)
  refine ⟨E₃.of_pk pk₄, I.pk.trans (X.pk.trans pk₄), (f₂.trans f₃).trans f₄, ?_, ?_, ?_, ?_⟩
  · rw [keys, a₄, a₃]
  · have hk := keys
    rw [Prod.ext_iff] at hk
    rw [hk.2, ← X.ciph]
    unfold Spec.GcmSiv.ctxCiph
    rw [hm₄, Proof.Cmac.bytesAt_frame (hkeyMem_frame _ _) (fun r hr =>
      (dH' r hr).sub_left (Region.sub_prefix L.rb)) (by have := L.rb; omega)]
  · rw [hm₄, hkeyMem_key, ← hm₄, a₄]
  · rw [hm₄]; exact hkeyMem_acc _ _

end VG.Proof.AesGcmSiv.PPC64LE
