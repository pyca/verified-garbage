module

public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Derive
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.GcmSiv.Words
import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Run
public import VerifiedGarbage.Impl.AesGcmSiv.RISCV64
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Callee
public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Env
public import VerifiedGarbage.Proof.Cmac.Block
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Spec.GcmSiv
import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Wp

/-!
# AES-GCM-SIV on RISC-V: the keys (`keys`)

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcmSiv/PPC64LE/Keys.lean`): after `derive`, `expand` expands
the encryption key at `W + 32` to its schedule at `W + 256` by a call of
`vg_aes_expand_key_scratch` (`expand_wp`), and `hkey` computes GHASH's key
`H · x` at `W + 64`, in GHASH's order (each half stored big-endian, a byte at
a time), from the authentication key `H` at `W + 16` as a little-endian
number, and zeroes the accumulator at `W + 80` (`hkey_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.RISCV64

open VG VG.Impl.AesGcmSiv.RISCV64 VG.RISCV64 VG.WriteBytes
open VG.RISCV64.Steps (Upd Mupd wp_addi wp_li wp_ld wp_sd wp_sll wp_srl wp_sub wp_subi)
open VG.Proof.AesGcm.RISCV64 (KeyCall KeyPost key_call)
open VG.Impl.Words.RISCV64 (storeBE)
open VG.Proof.GcmSiv.Words (hkeyOf)
open VG.Spec.Aes (bytesAt)

/-! ## `expand` -/

/-- What `expand` leaves: the schedule of the encryption key at `W + 256`. -/
structure ExpPost (c : Cx) (t t' : State) : Prop where
  pk : PK t t'
  frame : Frame [⟨c.W + BitVec.ofNat 64 256, 240⟩, ⟨c.W + BitVec.ofNat 64 1792, 512⟩] t.mem t'.mem
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
        (c.W + BitVec.ofNat 64 1792) := by
  have hR := L.rounds
  have hl : Spec.GcmSiv.keyLen c.R = 16 ∨ Spec.GcmSiv.keyLen c.R = 32 := by
    unfold Spec.GcmSiv.keyLen; rcases hR with h | h <;> rw [h] <;> decide
  unfold expandArgs ekO skO scrO
  refine wp_addi (by decide) fun t₁ u₁ => wp_subi (imm := 6) (by decide) fun t₂ u₂ =>
    wp_sll (by decide) fun t₃ u₃ => wp_addi (by decide) fun t₄ u₄ =>
    wp_addi (by decide) fun t₅ u₅ => WP.block_nil ?_
  have pk₅ : PK t t₅ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    (PK.ofUpd u₅))))
  have E₅ := E.of_pk pk₅
  refine ⟨pk₅, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], ?_⟩
  exact
    { a0 := by
        rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
          E.s0]
      a1 := by
        rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), E.s3,
          keyLen_lsl hR]
      a2 := by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), E.s0]
      a3 := by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), E.s0]
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

/-- The memory `hkey` leaves: the halves stored big-endian, the high one
first. -/
def hkeyMem (m : Mem) (W : Addr) : Mem :=
  let lo := m.readW (W + BitVec.ofNat 64 16) 64
  let hi := m.readW (W + BitVec.ofNat 64 24) 64
  Proof.Cmac.zero2 (writeBytes (writeBytes m (W + BitVec.ofNat 64 64 + BitVec.ofNat 64 0)
    (ByteLoad.beBytes 8 (hkHi hi lo))) (W + BitVec.ofNat 64 64 + BitVec.ofNat 64 8) (ByteLoad.beBytes 8 (hkLo hi lo)))
    (W + BitVec.ofNat 64 80)

theorem shl63 (x : BitVec 64) : x <<< 63 = (x &&& 1#64).rotateRight 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_rotateRight, BitVec.getLsbD_and]
  by_cases h63 : i < 63
  · simp [h63, BitVec.getLsbD_one]
  · have : i = 63 := by omega
    subst this; simp

theorem hkeyMem_frame (m : Mem) (W : Addr) : Frame [⟨W + BitVec.ofNat 64 64, 32⟩] m (hkeyMem m W) := by
  unfold hkeyMem Proof.Cmac.zero2
  refine (((writeBytes_frame _ _ _ ?_).trans (writeBytes_frame _ _ _ ?_)).trans
    (Proof.Cmac.frame_store2 (W + BitVec.ofNat 64 80) _ _ |>.sub fun r hr => ?_))
  · rw [ByteLoad.beBytes_length]
    exact Offset.contains_base (W + BitVec.ofNat 64 64) (d := 0) (n := 8) (k := 32) (by decide) (by decide)
  · rw [ByteLoad.beBytes_length]
    exact Offset.contains_base (W + BitVec.ofNat 64 64) (d := 8) (n := 8) (k := 32) (by decide) (by decide)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub W (d := 80) (e := 64) (by decide) (by decide)⟩

theorem hkeyMem_key (m : Mem) (W : Addr) :
    Spec.Gcm.blockAt (hkeyMem m W) (W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt m (W + BitVec.ofNat 64 16) 16)) := by
  unfold hkeyMem Proof.Cmac.zero2
  dsimp only
  rw [blockAt_frame (Proof.Cmac.frame_store2 _ _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)),
    Proof.Gcm.RISCV64.blockAt_store, Proof.Gcm.RISCV64.w2, GcmSiv.Words.hkeyOf_words, GcmSiv.ofBytes_bytesAt,
    Offset.add_add]

theorem hkeyMem_acc (m : Mem) (W : Addr) : Spec.Gcm.blockAt (hkeyMem m W) (W + BitVec.ofNat 64 80) = 0 := by
  unfold hkeyMem
  rw [Spec.Gcm.blockAt, Proof.Cmac.zero2_bytes]
  decide

/-- The arithmetic of `hkey`: the halves of GHASH's key in `a1` and `a0`. -/
abbrev hkeyAlu : List Instr :=
  [.load .d .a0 .s0 16, .load .d .a1 .s0 24, .logicImm .and .a2 .a0 1, .li .a3 0,
    .sub .a2 .a3 .a2, .shift .srl .d .a0 .a0 1, .shift .sll .d .a3 .a1 63, .logic .or .a0 .a0 .a3,
    .shift .srl .d .a1 .a1 1, .li .a3 0xe1, .shift .sll .d .a3 .a3 56, .logic .and .a2 .a2 .a3,
    .logic .xor .a1 .a1 .a2]

theorem e1_56 : (BitVec.ofNat 64 0xe1 : BitVec 64) <<< 56 = 0xE100000000000000#64 := by decide

theorem hkeyAlu_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) :
    WP isa (.block hkeyAlu) t fun t' => PK t t' ∧ t'.mem = t.mem ∧ t'.gpr .s0 = c.W ∧
      t'.gpr .a1 = hkHi (t.mem.readW (c.W + BitVec.ofNat 64 24) 64) (t.mem.readW (c.W + BitVec.ofNat 64 16) 64) ∧
      t'.gpr .a0 = hkLo (t.mem.readW (c.W + BitVec.ofNat 64 24) 64) (t.mem.readW (c.W + BitVec.ofNat 64 16) 64) := by
  refine wp_ld (a := c.W + BitVec.ofNat 64 16) (by decide) (by rw [E.s0]) (L.wal8 (by decide) (by decide))
    (E.perm.wR (by decide)) fun t₁ u₁ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 24) (by decide) (by rw [u₁.other _ (by decide), E.s0])
    (L.wal8 (by decide) (by decide)) (by rw [u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun t₂ u₂ => ?_
  refine Steps.wp_andi (by decide) fun t₃ u₃ => wp_li (by decide) fun t₄ u₄ => wp_sub fun t₅ u₅ =>
    wp_srl (by decide) fun t₆ u₆ => wp_sll (by decide) fun t₇ u₇ => Steps.wp_or fun t₈ u₈ =>
    wp_srl (by decide) fun t₉ u₉ => wp_li (by decide) fun t₁₀ u₁₀ => wp_sll (by decide) fun t₁₁ u₁₁ =>
    wp_and fun t₁₂ u₁₂ => Steps.wp_xor fun t₁₃ u₁₃ => WP.block_nil ?_
  have pk : PK t t₁₃ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans ((PK.ofUpd u₉).trans
    ((PK.ofUpd u₁₀).trans ((PK.ofUpd u₁₁).trans ((PK.ofUpd u₁₂).trans (PK.ofUpd u₁₃))))))))))))
  refine ⟨pk, by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem,
    u₃.mem, u₂.mem, u₁.mem], by rw [pk.gpr _ (by decide), E.s0], ?_, ?_⟩
  · simp (disch := decide) only [u₁₃.gpr, u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr,
      u₁₀.other, u₉.gpr, u₉.other, u₈.other, u₇.other, u₆.other, u₅.gpr, u₅.other,
      u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.mem, e1_56]
    rw [BitVec.and_comm (0#64 - _)]
    rfl
  · simp (disch := decide) only [u₁₃.other, u₁₂.other, u₁₁.other,
      u₁₀.other, u₉.other, u₈.gpr, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.other,
      u₄.other, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.mem, shl63]

/-- `hkey`: GHASH's key at `W + 64` and its accumulator zeroed at `W + 80`. -/
theorem hkey_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) :
    WP isa (.block hkey) t fun t' => PK t t' ∧ t'.mem = hkeyMem t.mem c.W := by
  have e : hkey = hkeyAlu ++ (storeBE 8 .a1 .t0 .s0 64 ++ (storeBE 8 .a0 .t0 .s0 72 ++ zero16 80)) := rfl
  rw [e]
  refine WP.block_append (WP.mono (hkeyAlu_wp L E) fun t₁ ⟨pk₁, hm₁, w₁, h₁, l₁⟩ => ?_)
  have E₁ := E.of_pk pk₁
  refine WP.block_append (WP.mono (ByteLoad.storeBE_ok (s := t₁) (v := .a1) (tmp := .t0) (n := .s0) (off := 64)
    (w := 8) (by decide) (by decide) (by decide) (by decide) (by decide) fun j hj => by
      rw [w₁]; exact E₁.perm.wW (by omega)) fun t₂ e₂ => ?_)
  have m₂ : t₂.mem = writeBytes t₁.mem (c.W + BitVec.ofNat 64 64) (ByteLoad.beBytes 8 (t₁.gpr .a1)) := by
    rw [e₂, w₁]; rfl
  have g₂ : ∀ r, r ≠ .t0 → t₂.gpr r = t₁.gpr r := fun r h => by
    rw [e₂]; exact RegUpd.gpr_write_of_ne _ _ h
  have k₂ : t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr ∧ t₂.sp = t₁.sp := by rw [e₂]; exact ⟨rfl, rfl, rfl⟩
  have w₂ : t₂.gpr .s0 = c.W := by rw [g₂ _ (by decide), w₁]
  refine WP.block_append (WP.mono (ByteLoad.storeBE_ok (s := t₂) (v := .a0) (tmp := .t0) (n := .s0) (off := 72)
    (w := 8) (by decide) (by decide) (by decide) (by decide) (by decide) fun j hj => by
      rw [w₂, k₂.2.1]; exact E₁.perm.wW (by omega)) fun t₃ e₃ => ?_)
  have m₃ : t₃.mem = writeBytes t₂.mem (c.W + BitVec.ofNat 64 72) (ByteLoad.beBytes 8 (t₂.gpr .a0)) := by
    rw [e₃, w₂]; rfl
  have g₃ : ∀ r, r ≠ .t0 → t₃.gpr r = t₂.gpr r := fun r h => by
    rw [e₃]; exact RegUpd.gpr_write_of_ne _ _ h
  have k₃ : t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr ∧ t₃.sp = t₂.sp := by rw [e₃]; exact ⟨rfl, rfl, rfl⟩
  have w₃ : t₃.gpr .s0 = c.W := by rw [g₃ _ (by decide), w₂]
  unfold zero16
  refine Steps.wp_li (by decide) fun t₄ u₄ => ?_
  have w₄ : t₄.gpr .s0 = c.W := by rw [u₄.other _ (by decide), w₃]
  have wr₄ : t₄.wr = t₁.wr := by rw [u₄.wr, k₃.2.1, k₂.2.1]
  refine Steps.wp_sd (a := c.W + BitVec.ofNat 64 80) (by decide) (by rw [w₄])
    (L.wal8 (by decide) (by decide)) (by rw [wr₄]; exact E₁.perm.wW (by decide))
    fun t₅ u₅ => ?_
  refine Steps.wp_sd (a := c.W + BitVec.ofNat 64 80 + BitVec.ofNat 64 8) (by decide)
    (by rw [u₅.gpr, w₄, Offset.add_add]) (by rw [Offset.add_add]; exact L.wal8 (by decide) (by decide))
    (by rw [u₅.wr, wr₄, Offset.add_add]; exact E₁.perm.wW (by decide))
    fun t₆ u₆ => WP.block_nil ?_
  have pk₆ : PK t₁ t₆ := ⟨by rw [u₆.rd, u₅.rd, u₄.rd, k₃.1, k₂.1], by rw [u₆.wr, u₅.wr, wr₄],
    by rw [u₆.sp, u₅.sp, u₄.sp, k₃.2.2, k₂.2.2], fun r hr => by
      have h0 : r ≠ .t0 := by revert hr; revert r; decide
      rw [u₆.gpr, u₅.gpr, u₄.other _ h0, g₃ _ h0, g₂ _ h0]⟩
  refine ⟨pk₁.trans pk₆, ?_⟩
  have a1 : t₁.gpr .a1 = hkHi (t.mem.readW (c.W + BitVec.ofNat 64 24) 64) (t.mem.readW (c.W + BitVec.ofNat 64 16) 64) := h₁
  have a0 : t₂.gpr .a0 = hkLo (t.mem.readW (c.W + BitVec.ofNat 64 24) 64) (t.mem.readW (c.W + BitVec.ofNat 64 16) 64) := by
    rw [g₂ _ (by decide), l₁]
  have z : t₅.gpr .t0 = 0 := by rw [u₅.gpr, u₄.gpr]; rfl
  rw [u₆.mem, u₅.gpr, u₅.mem, u₄.gpr, u₄.mem, m₃, m₂, a0, a1, hm₁]
  unfold hkeyMem Proof.Cmac.zero2
  simp only [BitVec.add_zero, Offset.add_add, Nat.reduceAdd]
  rfl

/-! ## `keys` -/

/-- What `keys` writes: the keys, GHASH's key and accumulator, the blocks
the calls use, the encryption key's schedule and the working spaces. -/
abbrev keyR (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 112⟩, ⟨W + BitVec.ofNat 64 240, 16⟩, ⟨W + BitVec.ofNat 64 256, 240⟩,
    ⟨W + BitVec.ofNat 64 1792, 2048⟩]

/-- What `keys` leaves, from `σ`. -/
structure KeysPost (c : Cx) (σ t : State) : Prop where
  env : Env c t
  pk : PK σ t
  frame : Frame (keyR c.W) σ.mem t.mem
  auth : (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem c.K c.R) (Spec.GcmSiv.keyLen c.R)
    (bytesAt σ.mem (nP c.W) 12)).1 = bytesAt t.mem (c.W + BitVec.ofNat 64 16) 16
  ciph : Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R = Spec.GcmSiv.aes
    (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem c.K c.R) (Spec.GcmSiv.keyLen c.R)
      (bytesAt σ.mem (nP c.W) 12)).2
  hkey : Spec.Gcm.blockAt t.mem (c.W + BitVec.ofNat 64 64) =
    hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (c.W + BitVec.ofNat 64 16) 16))
  acc : Spec.Gcm.blockAt t.mem (c.W + BitVec.ofNat 64 80) = 0

theorem keys_wp {c : Cx} (L : Lay c) {σ : State} (E : Env c σ) : WP isa keys σ (KeysPost c σ) := by
  have hR := L.rounds
  unfold keys
  refine WP.seq (WP.mono (derive_wp L E) fun t₂ I => ?_)
  have k0 : (⟨c.W + BitVec.ofNat 64 16, 112⟩ : Region) ∈ keyR c.W := List.mem_cons_self
  have k1 : (⟨c.W + BitVec.ofNat 64 240, 16⟩ : Region) ∈ keyR c.W := List.mem_cons_of_mem _ List.mem_cons_self
  have k2 : (⟨c.W + BitVec.ofNat 64 256, 240⟩ : Region) ∈ keyR c.W := by simp
  have k3 : (⟨c.W + BitVec.ofNat 64 1792, 2048⟩ : Region) ∈ keyR c.W := by simp
  have f₂ : Frame (keyR c.W) σ.mem t₂.mem := I.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, k0, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k0, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k1, fun _ h => h⟩
    · exact ⟨_, k3, fun _ h => h⟩
  refine WP.seq (WP.mono (expand_wp L I.env) fun t₃ X => ?_)
  have E₃ := I.env.of_pk X.pk
  refine WP.mono (hkey_wp L E₃) fun t₄ ⟨pk₄, hm₄⟩ => ?_
  have dK : ∀ {d k : Nat}, d + k ≤ 64 → 16 ≤ d → ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 256, 240⟩ : Region),
      ⟨c.W + BitVec.ofNat 64 1792, 512⟩], (⟨c.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact L.w_w (.inl (by omega)) (by omega) (by decide)
  have f₃ : Frame (keyR c.W) t₂.mem t₃.mem := X.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, k2, fun _ h => h⟩
    · exact ⟨_, k3, Offset.sub _ (by decide) (by decide)⟩
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

end VG.Proof.AesGcmSiv.RISCV64
