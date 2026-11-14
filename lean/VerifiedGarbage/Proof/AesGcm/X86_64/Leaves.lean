module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Instances
public import VerifiedGarbage.Proof.Variants.AesGcm.X86_64.VaesVpclmul
public import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Leaves
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.Ok
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesGcm.X86_64.SealLeaves

/-!
# AES-GCM on x86-64: what the VAES functions leave in their working space

Untrusted: everything here is checked by Lean. The two
`vg_aes_gcm_encrypt_blocks` that `vg_aes_gcm_seal_prepared_vaes_vpclmul`
calls, for the key context of `vg_aes_gcm_init` (`GcmImpl.blkB`) and for one
of `vg_aes_gcm_prepare16` (`blkR16`), leave in their `scratch` a function of
their arguments (`BlkLeaves`): the arguments kept in its first 48 bytes
(`keptW`), zeros where their loops wrote, and elsewhere what was there. So
the two codes of `vg_aes_gcm_seal_prepared_vaes_vpclmul` (`sealCodeF16`)
leave in `work` from byte 96 on a function of their argument registers and
stack arguments (`sealP16_vaes_leaves`, `seal_vaes_leaves`, from
`seal_leaves`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64

/-- Word `j` of the arguments the blocks functions keep in `scratch`, for
what is left after `q` blocks. -/
def keptW (rdi rsi rdx rcx r8 r9 : BitVec 64) (q : Nat) : Nat → BitVec 64
  | 0 => rdi
  | 1 => rsi
  | 2 => rdx
  | 3 => rcx
  | 4 => r8 + BitVec.ofNat 64 (16 * q)
  | _ => BitVec.ofNat 64 (r9.toNat - q)

/-- What a blocks function leaves at `x` in `scratch` at `S`: in its first 48
bytes the arguments kept for what is left after `q n` of the `n` blocks;
after them zero where `Z n S` says of the offset, and elsewhere nothing
written. -/
def leavesL (q : Nat → Nat) (Z : Nat → Addr → Nat → Bool) (rdi rsi rdx rcx r8 r9 : BitVec 64) (S x : Addr) :
    Option (BitVec 8) :=
  if (x - S).toNat < 48 then
    some ((keptW rdi rsi rdx rcx r8 r9 (q r9.toNat) ((x - S).toNat / 8)).extractLsb' (8 * ((x - S).toNat % 8)) 8)
  else if Z r9.toNat S (x - S).toNat then some 0 else none

theorem kept_words {s : State} {q : Nat} {m : Mem} (hk : Blocks.Kept s q m) :
    ∀ j < 6, m.readW (Blocks.S s + BitVec.ofNat 64 (8 * j)) 64 =
      keptW (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8) (s.gpr .r9) q j := by
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show Blocks.S s + BitVec.ofNat 64 (8 * 0) = Blocks.S s from BitVec.add_zero _]; exact hk.ctx
  · exact hk.rounds
  · exact hk.ctr
  · exact hk.y
  · exact hk.data
  · exact hk.n

/-- `BlkLeaves` from what the encryption leaves in `scratch` (`Blocks.Scr`). -/
theorem blkLeaves_of {M : Gcm.X86_64.Stitch.CtxMode} {B : BlkFn M} (q : Nat → Nat) (Z : Nat → Addr → Nat → Bool)
    (h : ∀ s, (Proof.AesGcm.encryptBlocksX86_64M M).pre s → WP isa B.enc.code s fun s' =>
      Blocks.Scr s (q (Blocks.n s)) (Z (Blocks.n s) (Blocks.S s)) s'.mem) :
    BlkLeaves B := by
  refine ⟨leavesL q Z, fun s t s' hpre he x hx => ?_⟩
  obtain ⟨_, s'', he', hS⟩ := h s hpre
  obtain ⟨_, rfl⟩ := Exec.det he he'
  obtain ⟨d, hd, rfl⟩ : ∃ d, d < 2112 ∧ x = stackArg s 0 + BitVec.ofNat 64 d :=
    ⟨(x - stackArg s 0).toNat, hx, by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]⟩
  simp only [leavesL, Mem.sub_ofNat_toNat _ (show d < 2 ^ 64 by omega)]
  by_cases h48 : d < 48
  · simp only [h48, ↓reduceIte, Option.getD_some]
    rw [← kept_words hS.kept (d / 8) (by omega), ← Blocks.byte_readW64 _ _ (by omega),
      Offset.add_add_eq _ (by omega : 8 * (d / 8) + d % 8 = d)]
  · simp only [h48, ↓reduceIte]
    rw [hS.rest d (by omega) hd]
    cases Z (Blocks.n s) (Blocks.S s) d <;> rfl

/-! ## For the key context of `vg_aes_gcm_init` -/

/-- `Stitch.enc` leaves `PieceL`: it clears the copy of the powers, the 256
bytes it writes. -/
theorem stitch_pieceL {s₃ : State} (hp : Gcm.X86_64.Stitch.SPreM Gcm.X86_64.Stitch.CtxMode.base s₃)
    (hm : Gcm.X86_64.Stitch.nb s₃ % 16 = 0) :
    WP isa Impl.Gcm.X86_64.Stitch.enc s₃ fun s₄ =>
      Gcm.X86_64.Stitch.EPost s₃ s₄ ∧ Gcm.X86_64.Stitch.PieceL 256 (fun _ _ => true) s₃ s₄ :=
  Gcm.X86_64.Stitch.enc_okL hp.base hm

/-- The key-context `vg_aes_gcm_encrypt_blocks_vaes_vpclmul` leaves in
`scratch` the arguments kept, the 256 bytes of its loops' copy of the powers
at `scratch + 64` cleared if it had at least 16 blocks, and nothing else
written. -/
theorem blkB_vaes_leaves : BlkLeaves VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.blkB :=
  blkLeaves_of (fun n => n - n % 16) (fun n _ d => decide (16 ≤ n) && decide (64 ≤ d) && decide (d < 320))
    fun s hpre => by
      change WP isa (Impl.AesGcm.X86_64.Blocks.encrypt
        ⟨VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.ctr.callee.name,
          VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.ctr.callee.code⟩
        VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.gh.fn (some Impl.Gcm.X86_64.Stitch.enc) false false)
        s _
      exact Blocks.encryptB_leaves (Blocks.BP.ofM hpre) _
        (VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.ctr.free.get rfl) _
        (VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.gh.free.get rfl) fun s₃ h₃ hm => stitch_pieceL h₃ hm

/-! ## For a key context of `vg_aes_gcm_prepare16` -/

/-- `StitchR.encR` leaves `PieceL`: it clears the copy of the powers and the
keystream it writes (`StitchR.zeroR`). -/
theorem stitchR_pieceL {s₃ : State} (hp : Gcm.X86_64.Stitch.SPreM Gcm.X86_64.Stitch.CtxMode.prepared16 s₃ 1) :
    WP isa Impl.Gcm.X86_64.StitchR.encR s₃ fun s₄ =>
      Gcm.X86_64.Stitch.EPost s₃ s₄ ∧ Gcm.X86_64.Stitch.PieceL 512 Gcm.X86_64.StitchR.zeroR s₃ s₄ :=
  Gcm.X86_64.StitchR.encR_okL hp.toPrepared (by decide)

/-- The prepared-16 `vg_aes_gcm_encrypt_blocks_prepared16_vaes_vpclmul`
leaves in `scratch` the arguments kept, and, with at least 2 blocks, in the
working space at `scratch + o` (`o = AlignedScratch.offset true scratch`,
rounded up to 64 bytes) the bytes `StitchR.zeroR` names cleared: the copy of
the powers (256 bytes at `o`) with at least 16 blocks, and the keystream of
the blocks after the last group (128 bytes at `o + 256`, and the next 128 if
more than 8); nothing else written. -/
theorem blkR16_vaes_leaves : BlkLeaves (blkR16 VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant) :=
  blkLeaves_of (fun _ => 0) (fun n S d => decide (2 ≤ n) && (decide (AlignedScratch.offset true S ≤ d) &&
      decide (d < AlignedScratch.offset true S + 512) && Gcm.X86_64.StitchR.zeroR n (d - AlignedScratch.offset true S)))
    fun s hpre => by
      change WP isa (Impl.AesGcm.X86_64.Blocks.encrypt
        ⟨VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.ctr.callee.name,
          VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.ctr.callee.code⟩
        VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.gh.fn (some Impl.Gcm.X86_64.StitchR.encR) true true
        true false (some Impl.Gcm.X86_64.StitchR.encR)) s _
      exact Blocks.encryptR_leaves (Blocks.BP.ofM hpre) _
        (VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.ctr.free.get rfl) _
        (VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.gh.free.get rfl) (ℓ := 512) (by decide)
        fun s₃ h₃ => stitchR_pieceL h₃

/-! ## `vg_aes_gcm_seal_prepared_vaes_vpclmul` -/

open VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul (variant) in
/-- The code of `vg_aes_gcm_seal_prepared_vaes_vpclmul` for a key context of
`vg_aes_gcm_prepare16` (inside `withStackArgScratch 2600 3` in
`sealCodeF16`): what it leaves in `work` (`[rsp + 32]`) from byte 96 on is a
function of its argument registers and stack arguments (`sealL`). -/
theorem sealP16_vaes_leaves :
    ∃ L : (Reg → BitVec 64) → (Nat → BitVec 64) → Addr → Option (BitVec 8),
      ∀ s t s', (Proof.AesGcm.sealX86_64M Gcm.X86_64.Stitch.CtxMode.prepared16).pre s →
        Exec isa (variant.impl.sealCodeP (variant.impl.withBlk (blkR16 variant))) s t s' →
        ∀ x, (⟨stackArg s 3 + BitVec.ofNat 64 96, 2464⟩ : Region).Contains x 1 →
          s'.mem x = (L s.gpr (fun i => stackArg s i) x).getD (s.mem x) := by
  have hs : variant.impl.short = false := rfl
  have hf : variant.impl.fin = false := rfl
  unfold GcmImpl.sealCodeP
  simp only [hs, hf, Bool.false_eq_true, ↓reduceIte]
  exact seal_leaves _ (blkR16 variant) blkR16_vaes_leaves (variant.impl.gh.free.get rfl)
    (variant.impl.ctr.free.get rfl)

open VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul (variant) in
/-- The code of `vg_aes_gcm_seal_prepared_vaes_vpclmul` for the key context of
`vg_aes_gcm_init` (inside `withStackArgScratch 2600 3` in `sealCodeF16`):
what it leaves in `work` (`[rsp + 32]`) from byte 96 on is a function of its
argument registers and stack arguments (`sealL`). -/
theorem seal_vaes_leaves :
    ∃ L : (Reg → BitVec 64) → (Nat → BitVec 64) → Addr → Option (BitVec 8),
      ∀ s t s', (Proof.AesGcm.sealX86_64M Gcm.X86_64.Stitch.CtxMode.base).pre s →
        Exec isa (variant.impl.sealCode variant.impl.callees) s t s' →
        ∀ x, (⟨stackArg s 3 + BitVec.ofNat 64 96, 2464⟩ : Region).Contains x 1 →
          s'.mem x = (L s.gpr (fun i => stackArg s i) x).getD (s.mem x) := by
  have hs : variant.impl.short = false := rfl
  have hf : variant.impl.fin = false := rfl
  unfold GcmImpl.sealCode
  simp only [hs, hf, Bool.false_eq_true, ↓reduceIte]
  exact seal_leaves _ variant.impl.blkB blkB_vaes_leaves (variant.impl.gh.free.get rfl)
    (variant.impl.ctr.free.get rfl)

end VG.Proof.AesGcm.X86_64
