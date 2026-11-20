module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Instances
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.X86_64.Leaves
public import VerifiedGarbage.Proof.Framework.X86_64.WidenArray
public import VerifiedGarbage.Proof.Framework.X86_64.FlagBranch
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.AesGcm.X86_64.Flag
import VerifiedGarbage.Proof.AesGcm.X86_64.Scrub
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Frame
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared16
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
public import VerifiedGarbage.Proof.Variants.AesGcm.X86_64.VaesVpclmul
public import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Leaves
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.Ok
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Inline
import VerifiedGarbage.Proof.Framework.X86_64.ResidueTaintSound
public import VerifiedGarbage.Proof.AesGcm.X86_64.SealLeaves
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenLeaves
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamLeaves
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubPart
public import VerifiedGarbage.Proof.Variants.AesGcm.X86_64.AesNiPclmulAvx
public import VerifiedGarbage.Proof.Variants.AesGcm.X86_64.VaesVpclmulAvx512
public import VerifiedGarbage.Impl.AesGcm.X86_64.StreamClr
public import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Base
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.AesGcm.X86_64.ScrubStub
public import VerifiedGarbage.Impl.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.Framework.Lit

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

In the frame of `withStackArgScratch 2600 3`, on either side of the count
(`sealP16_branch`, `seal_branch`), that is a function of the entry's
registers but `rax` and its stack arguments, which two runs with the same
public data agree on, the count included, which the contract leaks. So two
runs leave the same bytes in the 2624 bytes below the stack pointer but the
160 at their bottom (`sealF16_resOk`): the 24 the calls use below the frame,
the frame's copies of the stack arguments and `work`'s address, and the
first 96 bytes of `work`, which hold the tag, `J₀` and the keystream. Five
32-byte stores clear those (`sealKs`), and the function returns without
secret residue (`sealF16Vaes`, which `sealF16Reg` chooses for it).
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
    ∃ Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
        Option (BitVec 8),
      ∀ s t s', (Proof.AesGcm.sealX86_64M Gcm.X86_64.Stitch.CtxMode.prepared16).pre s →
        Exec isa (variant.impl.sealCodeP (variant.impl.withBlk (blkR16 variant))) s t s' →
        ∀ x, (⟨stackArg s 3 + BitVec.ofNat 64 96, 2464⟩ : Region).Contains x 1 →
          s'.mem x = (sealL Lb s.gpr (fun i => stackArg s i) x).getD (s.mem x) := by
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
    ∃ Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
        Option (BitVec 8),
      ∀ s t s', (Proof.AesGcm.sealX86_64M Gcm.X86_64.Stitch.CtxMode.base).pre s →
        Exec isa (variant.impl.sealCode variant.impl.callees) s t s' →
        ∀ x, (⟨stackArg s 3 + BitVec.ofNat 64 96, 2464⟩ : Region).Contains x 1 →
          s'.mem x = (sealL Lb s.gpr (fun i => stackArg s i) x).getD (s.mem x) := by
  have hs : variant.impl.short = false := rfl
  have hf : variant.impl.fin = false := rfl
  unfold GcmImpl.sealCode
  simp only [hs, hf, Bool.false_eq_true, ↓reduceIte]
  exact seal_leaves _ variant.impl.blkB blkB_vaes_leaves (variant.impl.gh.free.get rfl)
    (variant.impl.ctr.free.get rfl)

/-! ## In the frame of `withStackArgScratch`, by the count -/

section
open VG.Impl.StackScratch.X86_64 (withStackArgScratch)

/-- The state `pre_narrowFirstArray` gives: the key context narrowed to its
first 32 words. -/
abbrev narrow32 (s : State) : State := s.withRegions (narrowHead (32 * 8) s.rd) s.wr

/-- The state `pre_narrowFirstArray` gives on 16 prepared powers: the key
context narrowed to its first 128 words. -/
abbrev narrow128 (s : State) : State := s.withRegions (narrowHead (128 * 8) s.rd) s.wr

/-- What `L₁` and `L₂` say alike they say alike through the same release. -/
theorem loseL_getD_congr {B : Addr} {n : Nat} {U : Nat → BitVec 64} {L₁ L₂ : Addr → Option (BitVec 8)}
    {o₁ o₂ : BitVec 8} {x : Addr} (h : (L₁ x).getD o₁ = (L₂ x).getD o₂) :
    (loseL B n U L₁ x).getD o₁ = (loseL B n U L₂ x).getD o₂ := by
  rcases loseL_cases B n U x with hc | ⟨w, hc⟩
  · rw [hc, hc]; exact h
  · rw [hc, hc]; rfl

/-- A run of code verified against `k` from `s`, where `k` holds of `s` with
fewer regions permitted, ends in the memory of a run from that state. -/
theorem exec_narrow {c : Prog isa} {k : Contract isa} (hv : Verified X86_64.target c k) {s : State}
    {rd wr : List Region} (hk : k.pre (s.withRegions rd wr)) (hc : Covers (rd ++ wr) (s.rd ++ s.wr))
    (hw : Covers wr s.wr) {t : List Leak} {u : State} (he : Exec isa c s t u) :
    ∃ t' u', Exec isa c (s.withRegions rd wr) t' u' ∧ u.mem = u'.mem := by
  obtain ⟨t', u', he', -, -⟩ := hv.1 _ hk
  have hw' := Exec.widen he' (rd := s.rd) (wr := s.wr) hc hw
  rw [State.withRegions_withRegions, State.withRegions_self] at hw'
  obtain ⟨-, rfl⟩ := Exec.det he hw'
  exact ⟨t', u', he', rfl⟩

/-- What code leaves in its frame of `withStackArgScratch` (`L`, at the
state `narrowS` it runs from), where `Q` says, from what it leaves run by
run from the states its contract's precondition implies `P` of. -/
theorem framed_leavesQ {sig : Sig} {nm : String} {e : Elem} {n bytes stack : Nat}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {c : Prog isa} {P : State → Prop}
    {Q : State → Addr → Prop} {L : State → Addr → Option (BitVec 8)}
    (hv : Verified X86_64.target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hP : ∀ s, (Sig.scratchContract abi sig nm e n pre post wa stack leak).pre s → P s)
    (hl : ∀ s t s', P s → Exec isa c s t s' → ∀ x, Q s x → s'.mem x = (L s x).getD (s.mem x))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 8 ≤ 2 ^ 64) (hsp : c.all (fun i => !isa.writesSp i) = true)
    (hd : c.x86_64Depth ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) {t : List Leak} {u : State}
    (he : Exec isa (withStackArgScratch bytes (nStack sig) c) s t u) :
    ∀ x, Q (narrowS sig e n bytes s) x →
      u.mem x = (loseL (s.gpr .rsp - BitVec.ofNat 64 bytes) bytes (innerU c (narrowS sig e n bytes s))
        (L (narrowS sig e n bytes s)) x).getD ((narrowS sig e n bytes s).mem x) := by
  have hn := narrowS_pre (nm := nm) hk hb.1 hb.2.1 (fun vs m₁ m₂ hl hb _ => hpre vs m₁ m₂ hl hb) hs
  obtain ⟨t₃, s₃, he₃, ha, -⟩ := hv.1 _ hn
  obtain ⟨hex, -, hm, -⟩ := withStackArgScratch_runMem hk hb hst (SpSafe.of_all hsp) hd hs he₃ ha
  obtain ⟨-, rfl⟩ := Exec.det he hex
  intro x hx
  rw [hm, innerU_eq he₃]
  exact lose_loseL _ _ _ (hl _ _ _ (hP _ hn) he₃ x hx)

/-- The stack arguments of `vg_aes_gcm_seal`'s code in the frame of
`withStackArgScratch 2600 3` from `s`: those of `s`, then `work`. -/
def sealArgs (s : State) (i : Nat) : BitVec 64 :=
  if i < 3 then stackArg s i else s.gpr .rsp - BitVec.ofNat 64 2600 + BitVec.ofNat 64 40

/-- What `sealL` says of the state `narrowS` runs `vg_aes_gcm_seal`'s code
from, in the frame of `withStackArgScratch 2600 3` from `s`, it says of `s`,
in `work` from byte 96 on. -/
theorem narrowS_sealL {sig : Sig} {e : Elem} {n : Nat}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    (h3 : nStack sig = 3) (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 16 + 8 * nStack sig + n * e.size ≤ 2600)
    {s : State} (hs : (sig.contract abi pre post wa (24 + 2600) leak).pre s)
    (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8))
    {x : Addr} (hx : (⟨s.gpr .rsp - BitVec.ofNat 64 2600 + BitVec.ofNat 64 40 + BitVec.ofNat 64 96, 2464⟩ : Region).Contains x 1) :
    (⟨stackArg (narrowS sig e n 2600 s) 3 + BitVec.ofNat 64 96, 2464⟩ : Region).Contains x 1 ∧
      (sealL Lb (narrowS sig e n 2600 s).gpr (fun i => stackArg (narrowS sig e n 2600 s) i) x).getD
          ((narrowS sig e n 2600 s).mem x) =
        (sealL Lb s.gpr (sealArgs s) x).getD (s.mem x) := by
  obtain ⟨hg, ha, hl, hf⟩ := narrowS_args hk hb (by decide) hs
  rw [h3] at ha hl hf
  have hW : stackArg (narrowS sig e n 2600 s) 3 = s.gpr .rsp - BitVec.ofNat 64 2600 + BitVec.ofNat 64 40 := hl
  refine ⟨by rw [hW]; exact hx, ?_⟩
  rw [sealL_congr Lb (g' := s.gpr) (a' := sealArgs s) hg (fun i hi => ?_)]
  · refine congrArg _ (hf x fun r hr => ?_)
    simp only [List.mem_singleton] at hr
    subst hr
    intro hc
    simp only [Region.Contains] at hx hc
    rw [Offset.add_add_eq _ (show 40 + 96 = 136 from rfl)] at hx
    have h₁ := (Offset.lt_iff x (s.gpr .rsp - BitVec.ofNat 64 2600) (d := 136) (n := 2464) (by decide)).1
      (by omega_using [hx])
    have h₂ := (Offset.lt_iff x (s.gpr .rsp - BitVec.ofNat 64 2600) (d := 8) (n := 32) (by decide)).1
      (by rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl] at hc; omega_using [hc])
    omega_using [h₁, h₂]
  · by_cases h : i < 3
    · simp only [sealArgs, h, ↓reduceIte]; exact ha i h
    · have : i = 3 := by omega_using [h, hi]
      subst this
      simp only [sealArgs, Nat.lt_irrefl, ↓reduceIte]; exact hW

open VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul (variant) in
/-- `vg_aes_gcm_seal_prepared_vaes_vpclmul` on a key context with 16
prepared powers: its code in its frame leaves in `work` from byte 96 on
what `sealL` says of its entry. -/
theorem sealP16_branch :
    ∃ Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
        Option (BitVec 8),
      ∀ s t u, (Spec.Gcm.sealPreparedContract X86_64.abi 2624).pre s → 16 ≤ flagCount s →
        Exec isa (withStackArgScratch 2600 3 (variant.impl.sealCodeP (variant.impl.withBlk (blkR16 variant))))
          s t u →
        ∀ x, (⟨s.gpr .rsp - BitVec.ofNat 64 2600 + BitVec.ofNat 64 40 + BitVec.ofNat 64 96, 2464⟩ : Region).Contains x 1 →
          u.mem x = (loseL (s.gpr .rsp - BitVec.ofNat 64 2600) 2600
            (innerU (Impl.AesGcm.X86_64.«seal» (variant.impl.withBlk (blkR16 variant))) (narrowS Proof.Gcm.sealPrecomputedSig .u64 320 2600 (narrow128 s)))
            (sealL Lb s.gpr (sealArgs s)) x).getD (s.mem x) := by
  have hc : variant.impl.sealCodeP (variant.impl.withBlk (blkR16 variant)) =
      Impl.AesGcm.X86_64.«seal» (variant.impl.withBlk (blkR16 variant)) := by
    have hs : variant.impl.short = false := rfl
    have hf : variant.impl.fin = false := rfl
    unfold GcmImpl.sealCodeP
    simp only [hs, hf, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨Lb, hL⟩ := sealP16_vaes_leaves
  rw [hc] at hL
  refine ⟨Lb, fun s t u hs hf he x hx => ?_⟩
  rw [hc] at he
  unfold Spec.Gcm.sealPreparedContract at hs
  have h₁ := pre_of_rel (N := 129) (C := fun m ctx => 16 ≤ (m.readW (ctx + 1024) 64).toNat) (leakB := none)
    (pre := Spec.Gcm.sealPreparedPre 64) (pre' := Proof.Gcm.sealPrepared16Pre 64) (fun _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1 hf⟩) hs hf
  have h₂ := pre_narrowFirstArray (n := 128) (n' := 129) (by decide) (pre := Proof.Gcm.sealPrepared16Pre 64)
    (fun _ _ _ _ _ _ _ _ _ _ h => h) h₁
  obtain ⟨t₁, u₁, he₁, hm⟩ := exec_narrow (sealPrepared16_framed variant.impl (blkR16 variant)) h₂
    (fun _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)) (Covers.refl _) he
  obtain ⟨hx', hv⟩ := narrowS_sealL (sig := Proof.Gcm.sealPrecomputedSig) (e := .u64) (n := 320) (by decide)
    (by decide) (by decide) h₂ Lb hx
  rw [hm, framed_leaves (sig := Proof.Gcm.sealPrecomputedSig) (nm := "work") (e := .u64) (n := 320)
    (bytes := 2600) (stack := 24) (pre := Proof.Gcm.sealPrepared16Pre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.sealRoundsPost X86_64.abi.ptrBits) (wa := true) (leak := none)
    (sealPrepared16_verified variant.impl (blkR16 variant)) (fun s h => sealPrepared16_implies.pre s h) hL
    (by decide) (by decide) (by decide) (sealM_spSafe _ _) (sealM_xdepth _ _)
    (Proof.AesGcm.sealPrepared16Pre_local _) h₂ he₁ x hx']
  exact loseL_getD_congr hv

/-- The code of `vg_aes_gcm_seal` of the variant `v` for the key context of
`vg_aes_gcm_init`, in the frame of `withStackArgScratch 2600 3`, from a state
meeting `vg_aes_gcm_seal_prepared`'s precondition and `C` (which takes it to
`vg_aes_gcm_seal`'s): what `sealL` says the code leaves in `work` from byte
96 on, it says of the entry. -/
theorem seal_branchOf (v : GcmVariant) (hc : v.impl.sealCode v.impl.callees = Impl.AesGcm.X86_64.«seal» v.impl.callees)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : ∀ s t s', (Proof.AesGcm.sealX86_64M Gcm.X86_64.Stitch.CtxMode.base).pre s →
      Exec isa (v.impl.sealCode v.impl.callees) s t s' →
      ∀ x, (⟨stackArg s 3 + BitVec.ofNat 64 96, 2464⟩ : Region).Contains x 1 →
        s'.mem x = (sealL Lb s.gpr (fun i => stackArg s i) x).getD (s.mem x))
    {C : Mem → Addr → Prop} :
    ∀ s t u, (Spec.Gcm.sealPreparedContract X86_64.abi 2624).pre s → C s.mem (s.gpr .rdi) →
      Exec isa (withStackArgScratch 2600 3 (v.impl.sealCode v.impl.callees)) s t u →
      ∀ x, (⟨s.gpr .rsp - BitVec.ofNat 64 2600 + BitVec.ofNat 64 40 + BitVec.ofNat 64 96, 2464⟩ : Region).Contains x 1 →
        u.mem x = (loseL (s.gpr .rsp - BitVec.ofNat 64 2600) 2600
            (innerU (Impl.AesGcm.X86_64.«seal» v.impl.callees) (narrowS Spec.Gcm.sealSig .u64 320 2600 (narrow32 s)))
            (sealL Lb s.gpr (sealArgs s)) x).getD (s.mem x) := by
  rw [hc] at hL
  intro s t u hs hf he x hx
  rw [hc] at he
  unfold Spec.Gcm.sealPreparedContract at hs
  have h₁ := pre_of_rel (N := 129) (C := C) (leakB := none)
    (pre := Spec.Gcm.sealPreparedPre 64) (pre' := Spec.Gcm.sealPre 64) (fun _ _ _ _ _ _ _ _ _ _ h _ => h.1) hs hf
  have h₂ := pre_narrowFirstArray (n := 32) (n' := 129) (by decide) (pre := Spec.Gcm.sealPre 64)
    (fun _ _ _ _ _ _ _ _ _ _ h => h) h₁
  obtain ⟨t₁, u₁, he₁, hm⟩ := exec_narrow (seal_framed v.impl) h₂
    (fun _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)) (Covers.refl _) he
  obtain ⟨hx', hv⟩ := narrowS_sealL (sig := Spec.Gcm.sealSig) (e := .u64) (n := 320) (by decide)
    (by decide) (by decide) h₂ Lb hx
  rw [hm, framed_leaves (sig := Spec.Gcm.sealSig) (nm := "work") (e := .u64) (n := 320)
    (bytes := 2600) (stack := 24) (pre := Spec.Gcm.sealPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.sealRoundsPost X86_64.abi.ptrBits) (wa := true) (leak := none)
    (seal_verified v.impl) (fun s h => ⟨sealCode_implies.pre s h, trivial⟩) hL
    (by decide) (by decide) (by decide) (seal_spSafe _) (seal_xdepth _)
    (sealPre_local _) h₂ he₁ x hx']
  exact loseL_getD_congr hv

open VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul (variant) in
/-- `vg_aes_gcm_seal_prepared_vaes_vpclmul` on a key context without 16
prepared powers: its code in its frame leaves in `work` from byte 96 on
what `sealL` says of its entry. -/
theorem seal_branch :
    ∃ Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
        Option (BitVec 8),
      ∀ s t u, (Spec.Gcm.sealPreparedContract X86_64.abi 2624).pre s → ¬ 16 ≤ flagCount s →
        Exec isa (withStackArgScratch 2600 3 (variant.impl.sealCode variant.impl.callees)) s t u →
        ∀ x, (⟨s.gpr .rsp - BitVec.ofNat 64 2600 + BitVec.ofNat 64 40 + BitVec.ofNat 64 96, 2464⟩ : Region).Contains x 1 →
          u.mem x = (loseL (s.gpr .rsp - BitVec.ofNat 64 2600) 2600
            (innerU (Impl.AesGcm.X86_64.«seal» variant.impl.callees) (narrowS Spec.Gcm.sealSig .u64 320 2600 (narrow32 s)))
            (sealL Lb s.gpr (sealArgs s)) x).getD (s.mem x) := by
  have hc : variant.impl.sealCode variant.impl.callees = Impl.AesGcm.X86_64.«seal» variant.impl.callees := by
    have hs : variant.impl.short = false := rfl
    have hf : variant.impl.fin = false := rfl
    unfold GcmImpl.sealCode
    simp only [hs, hf, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨Lb, hL⟩ := seal_vaes_leaves
  exact ⟨Lb, seal_branchOf variant hc hL (C := fun m ctx => ¬ 16 ≤ (m.readW (ctx + 1024) 64).toNat)⟩

open VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul (variant) in
/-- The unknowns `vg_aes_gcm_seal`'s code on 16 prepared powers ends with in
its frame: the same in two runs. -/
theorem sealP16_innerU {s₁ s₂ : State} (h₁ : (Spec.Gcm.sealPreparedContract X86_64.abi 2624).pre s₁)
    (h₂ : (Spec.Gcm.sealPreparedContract X86_64.abi 2624).pre s₂) (hf₁ : 16 ≤ flagCount s₁)
    (hf₂ : 16 ≤ flagCount s₂) (hp : (Spec.Gcm.sealPreparedContract X86_64.abi 2624).pub s₁ s₂)
    (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (Impl.AesGcm.X86_64.«seal» (variant.impl.withBlk (blkR16 variant))),
      s₁.syms n = s₂.syms n) :
    innerU (Impl.AesGcm.X86_64.«seal» (variant.impl.withBlk (blkR16 variant)))
        (narrowS Proof.Gcm.sealPrecomputedSig .u64 320 2600 (narrow128 s₁)) =
      innerU (Impl.AesGcm.X86_64.«seal» (variant.impl.withBlk (blkR16 variant)))
        (narrowS Proof.Gcm.sealPrecomputedSig .u64 320 2600 (narrow128 s₂)) := by
  unfold Spec.Gcm.sealPreparedContract at h₁ h₂ hp
  have q (s : State) (hs : (Spec.Gcm.sealPreparedSig.contract abi (Spec.Gcm.sealPreparedPre abi.ptrBits)
      (Spec.Gcm.sealPost abi.ptrBits) true 2624 (some (Spec.Gcm.sealPreparedLeak abi.ptrBits))).pre s)
      (hf : 16 ≤ flagCount s) := pre_narrowFirstArray (n := 128) (n' := 129) (by decide)
    (pre := Proof.Gcm.sealPrepared16Pre 64) (fun _ _ _ _ _ _ _ _ _ _ h => h)
    (pre_of_rel (N := 129) (C := fun m ctx => 16 ≤ (m.readW (ctx + 1024) 64).toNat) (leakB := none)
      (pre := Spec.Gcm.sealPreparedPre 64) (pre' := Proof.Gcm.sealPrepared16Pre 64)
      (fun _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1 hf⟩) hs hf)
  obtain ⟨⟨hs, -⟩, hpubs, hdescs⟩ := (pubL_args (sig := Spec.Gcm.sealPreparedSig) (by decide)).mp hp
  exact framed_innerU_agree (sig := Proof.Gcm.sealPrecomputedSig) (nm := "work") (e := .u64) (n := 320)
    (stack := 24) (bytes := 2600) (pre := Proof.Gcm.sealPrepared16Pre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.sealRoundsPost X86_64.abi.ptrBits) (wa := true) (leak := none)
    (sealPrepared16_verified variant.impl (blkR16 variant)) (by decide) (by decide) (by decide)
    (Proof.AesGcm.sealPrepared16Pre_local _) (q s₁ h₁ hf₁) (q s₂ h₂ hf₂)
    ((pubL_args (sig := Proof.Gcm.sealPrecomputedSig) (by decide)).mpr ⟨⟨hs, trivial⟩, hpubs,
      fun r hr i hi => hdescs r (by
        rw [show Spec.Gcm.sealPreparedSig.params = ("ctx", .array false .u64 129) ::
          Proof.Gcm.sealPrecomputedSig.params.tail from rfl, descs_array .u64 128 129]
        exact hr) i hi⟩) hu hsy

/-- The unknowns `vg_aes_gcm_seal`'s code of `v` ends with in its frame: the
same in two runs. -/
theorem seal32_innerU (v : GcmVariant) {C : Mem → Addr → Prop} {s₁ s₂ : State}
    (h₁ : (Spec.Gcm.sealPreparedContract X86_64.abi 2624).pre s₁)
    (h₂ : (Spec.Gcm.sealPreparedContract X86_64.abi 2624).pre s₂) (hf₁ : C s₁.mem (s₁.gpr .rdi))
    (hf₂ : C s₂.mem (s₂.gpr .rdi)) (hp : (Spec.Gcm.sealPreparedContract X86_64.abi 2624).pub s₁ s₂)
    (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (Impl.AesGcm.X86_64.«seal» v.impl.callees), s₁.syms n = s₂.syms n) :
    innerU (Impl.AesGcm.X86_64.«seal» v.impl.callees) (narrowS Spec.Gcm.sealSig .u64 320 2600 (narrow32 s₁)) =
      innerU (Impl.AesGcm.X86_64.«seal» v.impl.callees) (narrowS Spec.Gcm.sealSig .u64 320 2600 (narrow32 s₂)) := by
  unfold Spec.Gcm.sealPreparedContract at h₁ h₂ hp
  have q (s : State) (hs : (Spec.Gcm.sealPreparedSig.contract abi (Spec.Gcm.sealPreparedPre abi.ptrBits)
      (Spec.Gcm.sealPost abi.ptrBits) true 2624 (some (Spec.Gcm.sealPreparedLeak abi.ptrBits))).pre s)
      (hf : C s.mem (s.gpr .rdi)) := pre_narrowFirstArray (n := 32) (n' := 129) (by decide)
    (pre := Spec.Gcm.sealPre 64) (fun _ _ _ _ _ _ _ _ _ _ h => h)
    (pre_of_rel (N := 129) (C := C) (leakB := none)
      (pre := Spec.Gcm.sealPreparedPre 64) (pre' := Spec.Gcm.sealPre 64)
      (fun _ _ _ _ _ _ _ _ _ _ h _ => h.1) hs hf)
  obtain ⟨⟨hs, -⟩, hpubs, hdescs⟩ := (pubL_args (sig := Spec.Gcm.sealPreparedSig) (by decide)).mp hp
  exact framed_innerU_agree (sig := Spec.Gcm.sealSig) (nm := "work") (e := .u64) (n := 320)
    (stack := 24) (bytes := 2600) (pre := Spec.Gcm.sealPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.sealRoundsPost X86_64.abi.ptrBits) (wa := true) (leak := none)
    (seal_verified v.impl) (by decide) (by decide) (by decide)
    (sealPre_local _) (q s₁ h₁ hf₁) (q s₂ h₂ hf₂)
    ((pubL_args (sig := Spec.Gcm.sealSig) (by decide)).mpr ⟨⟨hs, trivial⟩, hpubs,
      fun r hr i hi => hdescs r (by
        rw [show Spec.Gcm.sealPreparedSig.params = ("ctx", .array false .u64 129) ::
          Spec.Gcm.sealSig.params.tail from rfl, descs_array .u64 32 129]
        exact hr) i hi⟩) hu hsy

/-! ## `vg_aes_gcm_seal_prepared_vaes_vpclmul` without secret residue -/

open VG.X86_64.Scrub VG.Impl.Scrub.X86_64

/-- The state after the test of `onFlag t`, from `s`. -/
def afterFlag (t : Nat) (s : State) : State :=
  match execBlock isa (Impl.Gcm.X86_64.Flag.testFlag t) s with
  | some p => p.1
  | none => s

/-- The state after the test is `s` but for `rax` and the flags, with its
unknowns and the addresses of its statics. -/
theorem afterFlag_facts {t : Nat} (htv : t = 16 ∨ t = 48) {s : State}
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + 1024) 8) :
    Same s (afterFlag t s) ∧ (afterFlag t s).unknowns = s.unknowns ∧ (afterFlag t s).syms = s.syms := by
  obtain ⟨s₀, e₀, hS, -⟩ := testFlag_run htv s hin
  have hA : afterFlag t s = s₀ := by unfold afterFlag; rw [e₀]
  rw [hA]
  exact ⟨hS, execBlock_keep (M := isa) (fun s : State => s.unknowns) (ok := fun _ => True)
    (fun _ he => RTaint.exec_unknowns he) (fun _ _ => trivial) e₀, execBlock_syms e₀⟩

/-- `onFlag t c₁ c₂` from `s` runs `c₁` from the state after the test if the
count is at least `t`, and `c₂` if not. -/
theorem onFlag_inv {t : Nat} (htv : t = 16 ∨ t = 48) {c₁ c₂ : Prog isa} {s u : State} {tr : List Leak}
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + 1024) 8)
    (he : Exec isa (Impl.Gcm.X86_64.Flag.onFlag t c₁ c₂) s tr u) :
    ∃ s₀ t₀, Same s s₀ ∧ s₀.unknowns = s.unknowns ∧ afterFlag t s = s₀ ∧
      ((t ≤ flagCount s ∧ Exec isa c₁ s₀ t₀ u) ∨ (¬ t ≤ flagCount s ∧ Exec isa c₂ s₀ t₀ u)) := by
  obtain ⟨s₀, e₀, hS, ev⟩ := testFlag_run htv s hin
  have hA : afterFlag t s = s₀ := by unfold afterFlag; rw [e₀]
  have hk : s₀.unknowns = s.unknowns := execBlock_keep (M := isa) (fun s : State => s.unknowns) (ok := fun _ => True)
    (fun _ he => RTaint.exec_unknowns he) (fun _ _ => trivial) e₀
  unfold Impl.Gcm.X86_64.Flag.onFlag Code.iteCold at he
  cases he with
  | seq h₁ h₂ =>
    cases h₁ with
    | block h =>
      rw [e₀] at h
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
      have hnil : ∀ {a : State} {tr : List Leak} {b : State}, Exec isa (.block []) a tr b → b = a := by
        intro a tr b hb
        cases hb with
        | block h => exact (Prod.mk.inj (Option.some.inj h)).1.symm
      cases h₂ with
      | iteT hc hth =>
        have hc' : eval .ae s₀ = some true := hc
        rw [ev] at hc'
        cases hth with
        | seq hb hc₁ =>
          cases hb with
          | seq b₁ b₂ =>
            obtain rfl := hnil b₁
            obtain rfl := hnil b₂
            exact ⟨_, _, hS, hk, hA, .inl ⟨of_decide_eq_true (Option.some.inj hc'), hc₁⟩⟩
      | iteF hc hel =>
        have hc' : eval .ae s₀ = some false := hc
        rw [ev] at hc'
        exact ⟨_, _, hS, hk, hA, .inr ⟨of_decide_eq_false (Option.some.inj hc'), hel⟩⟩

/-- The granules `vg_aes_gcm_seal_prepared_vaes_vpclmul` wipes: the 160
bytes at the bottom of its 2624 bytes of stack, the 24 below its frame
(return addresses and a saved register of its calls), the bottom of its
frame (the copies of the stack arguments and `work`'s address) and the
first 96 bytes of `work` (the tag, `J₀`, `Y`, the counter and the
keystream of a partial block). -/
def sealKs : List Nat := (List.range 10).map (16 * ·)

theorem sealKs_cov : ∀ i < 160, cov sealKs [2624] i = true := by
  intro i hi
  have hm : 16 * (i / 16) ∈ sealKs := List.mem_map.mpr ⟨i / 16, List.mem_range.mpr (by omega_using [hi]), rfl⟩
  simp only [cov, covC, List.sum_nil, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, Nat.zero_add,
    show 2624 % 16 = 0 from rfl, Bool.and_eq_true, List.contains_iff_mem]
  exact ⟨decide_eq_true (by omega_using [hi]), hm⟩

theorem chunks_2624 : chunks 2624 = [2624] := by decide

/-- A byte of the 2624 below `R` that `wipe sealKs` does not zero is in
`work` from byte 96 on. -/
theorem sealWindow {R x : Addr} (hx : (⟨R - BitVec.ofNat 64 2624, 2624⟩ : Region).Contains x 1)
    (hw : ¬ WCov sealKs (chunks 2624) R x) :
    (⟨R - BitVec.ofNat 64 2600 + BitVec.ofNat 64 40 + BitVec.ofNat 64 96, 2464⟩ : Region).Contains x 1 := by
  rw [chunks_2624] at hw
  simp only [WCov, List.sum_cons, List.sum_nil, Nat.add_zero] at hw
  have h160 : 160 ≤ (x - (R - BitVec.ofNat 64 2624)).toNat := by
    refine Nat.le_of_not_lt fun h => hw ⟨hx, sealKs_cov _ h⟩
  simp only [Region.Contains] at hx ⊢
  rw [Offset.sub_ofNat_eq R (show 2600 ≤ 2624 by decide), Offset.add_add, Offset.add_add,
    show 2624 - 2600 + 40 + 96 = 160 from rfl]
  have := (Offset.lt_iff x (R - BitVec.ofNat 64 2624) (d := 160) (n := 2464) (by decide)).2
    ⟨h160, by omega_using [hx]⟩
  omega_using [this]

theorem sealArgs_same {s u : State} (h : Same s u) : sealArgs u = sealArgs s := by
  funext i
  simp only [sealArgs, h.stackArg_eq, h.gpr .rsp (by decide)]

/-- Two runs of `vg_aes_gcm_seal_prepared` with the same public data, from
states that agree outside the buffers, agree on the stack arguments of
`vg_aes_gcm_seal`'s code in the frame of `withStackArgScratch 2600 3`. -/
theorem sealArgs_pub {stack : Nat} {s₁ s₂ : State} (hp : (Spec.Gcm.sealPreparedContract X86_64.abi stack).pub s₁ s₂)
    (ho : Outside 0 s₁ s₂) : sealArgs s₁ = sealArgs s₂ := by
  unfold Spec.Gcm.sealPreparedContract at hp
  obtain ⟨-, hpubs, -⟩ := (pubL_args (sig := Spec.Gcm.sealPreparedSig) (by decide)).mp hp
  have harg (j : Nat) (hj : (Spec.Gcm.sealPreparedSig.params.flatMap (·.2.pubs)).getD (6 + j) false = true)
      (hj3 : j < 3) : stackArg s₁ j = stackArg s₂ j := by
    have := hpubs (6 + j) hj
    have e : ∀ s : State, (allArgs Spec.Gcm.sealPreparedSig s).getD (6 + j) 0 = stackArg s j := by
      intro s
      rcases (by omega_using [hj3] : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> rfl
    rw [e, e] at this
    have hw : ((Spec.Gcm.sealPreparedSig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD (6 + j) 64 = 64 := by
      rcases (by omega_using [hj3] : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> rfl
    rw [hw, BitVec.setWidth_eq, BitVec.setWidth_eq] at this
    exact this
  funext i
  simp only [sealArgs]
  by_cases hi : i < 3
  · simp only [hi, ↓reduceIte]
    exact harg i (by rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl) hi
  · simp only [hi, ↓reduceIte, ho.2.2.1 .rsp (by decide)]

open VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul (variant) in
open VG.X86_64.Scrub in
/-- Two runs of `vg_aes_gcm_seal_prepared_vaes_vpclmul`'s code with the same
public data leave the same bytes in its stack but the granules `sealKs`:
there each run leaves what `sealL` says of its entry, by the count (which it
leaks), and that depends on no secret. -/
theorem sealF16_resOk :
    ResOk (sealCodeF16 variant) (Spec.Gcm.sealPreparedContract X86_64.abi 2624) 2624 sealKs (chunks 2624) := by
  obtain ⟨Lb₁, h₁⟩ := sealP16_branch
  obtain ⟨Lb₂, h₂⟩ := seal_branch
  have hc₁ : variant.impl.sealCodeP (variant.impl.withBlk (blkR16 variant)) =
      Impl.AesGcm.X86_64.«seal» (variant.impl.withBlk (blkR16 variant)) := by
    have hs : variant.impl.short = false := rfl
    have hf : variant.impl.fin = false := rfl
    unfold GcmImpl.sealCodeP
    simp only [hs, hf, Bool.false_eq_true, ↓reduceIte]
  have hc₂ : variant.impl.sealCode variant.impl.callees = Impl.AesGcm.X86_64.«seal» variant.impl.callees := by
    have hs : variant.impl.short = false := rfl
    have hf : variant.impl.fin = false := rfl
    unfold GcmImpl.sealCode
    simp only [hs, hf, Bool.false_eq_true, ↓reduceIte]
  have hn : UpperLock.inames (sealCodeF16 variant) =
      UpperLock.inames (Impl.AesGcm.X86_64.«seal» (variant.impl.withBlk (blkR16 variant))) ++
        UpperLock.inames (Impl.AesGcm.X86_64.«seal» variant.impl.callees) := by
    rw [← hc₁, ← hc₂]; rfl
  refine resOk_of_leaves (V := fun s x => if 16 ≤ flagCount s then
      loseL (s.gpr .rsp - BitVec.ofNat 64 2600) 2600
        (innerU (Impl.AesGcm.X86_64.«seal» (variant.impl.withBlk (blkR16 variant)))
          (narrowS Proof.Gcm.sealPrecomputedSig .u64 320 2600 (narrow128 (afterFlag 16 s))))
        (sealL Lb₁ s.gpr (sealArgs s)) x
    else loseL (s.gpr .rsp - BitVec.ofNat 64 2600) 2600
        (innerU (Impl.AesGcm.X86_64.«seal» variant.impl.callees)
          (narrowS Spec.Gcm.sealSig .u64 320 2600 (narrow32 (afterFlag 16 s))))
        (sealL Lb₂ s.gpr (sealArgs s)) x) ScrubAbi.plain ?_ ?_
  · intro s t u hs he x hx hw
    have hW := sealWindow hx hw
    obtain ⟨s₀, t₀, hS, -, hA, hb⟩ := onFlag_inv (Or.inl rfl) (flag_inRegions (N := 129) (by decide) hs) he
    have hs₀ := (pre_same hS).mpr hs
    have hf : flagCount s₀ = flagCount s := by simp only [flagCount, hS.mem, hS.gpr .rdi (by decide)]
    have hg : sealL Lb₁ s₀.gpr (sealArgs s₀) = sealL Lb₁ s.gpr (sealArgs s) ∧
        sealL Lb₂ s₀.gpr (sealArgs s₀) = sealL Lb₂ s.gpr (sealArgs s) := by
      rw [sealArgs_same hS]
      exact ⟨sealL_congr Lb₁ (fun r hr _ => hS.gpr r hr) (fun _ _ => rfl),
        sealL_congr Lb₂ (fun r hr _ => hS.gpr r hr) (fun _ _ => rfl)⟩
    have hsp := hS.gpr .rsp (by decide)
    rw [← hsp] at hW
    rcases hb with ⟨hb, he₀⟩ | ⟨hb, he₀⟩
    · rw [h₁ s₀ t₀ u hs₀ (hf ▸ hb) he₀ x hW, hg.1, hS.mem, hsp]
      simp only [hb, ↓reduceIte, hA]
    · rw [h₂ s₀ t₀ u hs₀ (hf ▸ hb) he₀ x hW, hg.2, hS.mem, hsp]
      simp only [hb, ↓reduceIte, hA]
  · intro s₁ s₂ hs₁ hs₂ hp ho hu hsy
    obtain ⟨⟨-, hl⟩, -, -⟩ := (pubL_args (sig := Spec.Gcm.sealPreparedSig) (by decide)).mp hp
    have hg : ∀ r, r ≠ .rax → s₁.gpr r = s₂.gpr r := ho.2.2.1
    have hflag : 16 ≤ flagCount s₁ ↔ 16 ≤ flagCount s₂ := by
      have hl' : flagLeak s₁.mem (s₁.gpr .rdi) = flagLeak s₂.mem (s₂.gpr .rdi) :=
        List.head_eq_of_cons_eq hl
      exact flagLeak_iff (Or.inl rfl) hl'
    have ha := sealArgs_pub hp ho
    obtain ⟨S₁, U₁, Y₁⟩ := afterFlag_facts (t := 16) (Or.inl rfl) (flag_inRegions (N := 129) (by decide) hs₁)
    obtain ⟨S₂, U₂, Y₂⟩ := afterFlag_facts (t := 16) (Or.inl rfl) (flag_inRegions (N := 129) (by decide) hs₂)
    have a₁ := (pre_same S₁).mpr hs₁
    have a₂ := (pre_same S₂).mpr hs₂
    have ap := (pub_same S₁ S₂).mpr hp
    have au : (afterFlag 16 s₁).unknowns = (afterFlag 16 s₂).unknowns := by rw [U₁, U₂, hu]
    have hf₁ : flagCount (afterFlag 16 s₁) = flagCount s₁ := by
      simp only [flagCount, S₁.mem, S₁.gpr .rdi (by decide)]
    have hf₂ : flagCount (afterFlag 16 s₂) = flagCount s₂ := by
      simp only [flagCount, S₂.mem, S₂.gpr .rdi (by decide)]
    have hsy' : ∀ n ∈ UpperLock.inames (sealCodeF16 variant),
        (afterFlag 16 s₁).syms n = (afterFlag 16 s₂).syms n := fun n h => by rw [Y₁, Y₂]; exact hsy n h
    rw [hn] at hsy'
    funext x
    dsimp only
    rw [ha, sealL_congr Lb₁ (g' := s₂.gpr) (fun r hr _ => hg r hr) (fun _ _ => rfl),
      sealL_congr Lb₂ (g' := s₂.gpr) (fun r hr _ => hg r hr) (fun _ _ => rfl), hg .rsp (by decide)]
    by_cases h : 16 ≤ flagCount s₁
    · simp only [h, hflag.mp h, ↓reduceIte]
      rw [sealP16_innerU a₁ a₂ (hf₁ ▸ h) (hf₂ ▸ hflag.mp h) ap au
        (fun n hn' => hsy' n (List.mem_append_left _ hn'))]
    · simp only [h, mt hflag.mpr h, ↓reduceIte]
      rw [seal32_innerU variant (C := fun m ctx => ¬ 16 ≤ (m.readW (ctx + 1024) 64).toNat) a₁ a₂
        (show ¬ 16 ≤ flagCount (afterFlag 16 s₁) by rw [hf₁]; exact h)
        (show ¬ 16 ≤ flagCount (afterFlag 16 s₂) by rw [hf₂]; exact mt hflag.mpr h) ap au
        (fun n hn' => hsy' n (List.mem_append_right _ hn'))]

/-- `vg_aes_gcm_seal_prepared`'s postcondition reads the memory on return
only within the buffers: the data and the tag. -/
theorem sealPreparedOut (stack : Nat) :
    PostOut (Spec.Gcm.sealPreparedContract X86_64.abi stack) (Spec.Gcm.sealPreparedSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, data, len, tag], _ =>
      simp only [Spec.Gcm.sealPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      intro key hk
      show _ = (Spec.Aes.bytesAt m₂ data len.toNat, Spec.Aes.bytesAt m₂ tag 16)
      rw [Scrub.bytesAt_of0 hb.2.2.2.1 (by omega_arith), Scrub.bytesAt_of0 hb.2.2.2.2 (by decide)]
      exact h key hk

/-- The variant reads only the first 16 prepared powers. -/
theorem r16_vaes : R16 VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant :=
  ⟨rfl, fun n h => by
    obtain rfl : OnePassName.r = n := Option.some.inj (show some OnePassName.r = some n from h)
    decide⟩

/-- `vg_aes_gcm_seal_prepared` of a variant whose loops read 16 powers: by
the count, its code on them or its code on the key context
(`sealCodeF16`). -/
def sealF16Plain (v : GcmVariant) (r : R16 v) : Unscrubbed Spec.Gcm.sealPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := sealCodeF16 v
  stack := 2624
  verified := VG.Proof.AesGcm.Flag.seal_keyed (Flag.seal_ofB (Or.inl rfl) (sealCodeF16_verified v r))
  spSafe := sealCodeF16_spAll v

open VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul (variant) in
/-- `vg_aes_gcm_seal_prepared_vaes_vpclmul`, followed by the clearing of the
160 bytes at the bottom of its stack (`sealKs`): it returns without secret
residue (`sealF16_resOk`). -/
def sealF16Vaes : Registration Spec.Gcm.sealPreparedApi X86_64.target :=
  RScrub.withScrubRes (sealF16Plain variant r16_vaes) (sealPreparedOut _) sealKs sealF16_resOk

open VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul (variant) in
/-- `vg_aes_gcm_seal_prepared` of a variant whose loops read 16 powers:
`sealF16Vaes` for the function of the VAES variant's name, which returns
without secret residue (`vg_aes_gcm_seal_gather_prepared` calls its code as
it was, `vg_aes_gcm_seal_prepared_vaes_vpclmul_core`: `sealFnF16`), and
for the others `sealF16Plain` followed by the clearing of its whole frame of
2624 bytes, in chunks whose 16-byte stores are aligned. -/
def sealF16Reg (v : GcmVariant) (r : R16 v) : Registration Spec.Gcm.sealPreparedApi X86_64.target :=
  if v.impl.suffix = variant.impl.suffix then sealF16Vaes
  else RScrub.withScrubAllRC (sealF16Plain v r) (sealPreparedOut _) [8, 2616]

/-- What `seal` needs of where its tag is, as a contract (`sealScratch_tagArgs`). -/
def sealTagArgs : Contract isa :=
  { Proof.AesGcm.sealX86_64 with
    pre := fun s => (⟨Proof.AesGcm.arg s 2, 16⟩ : Region).Disjoint ⟨s.gpr .rsp + BitVec.ofNat 64 8, 24⟩ }

/-- `seal`'s tag is apart from its stack arguments. -/
theorem sealScratch_tagArgs :
    ∀ s, (Proof.AesGcm.sealScratchContract X86_64.abi 24).pre s → sealTagArgs.pre s := by
  intro s h
  sig_pre [Proof.AesGcm.sealScratchContract, Proof.AesGcm.sealScratchSig, Spec.Gcm.sealPre, Proof.AesGcm.sealRoundsPost,
    X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
    X86_64.argRegs] at h
  sig_split h
  show Region.Disjoint ⟨Proof.AesGcm.arg s 2, 16⟩ ⟨s.gpr .rsp + BitVec.ofNat 64 8, 24⟩
  refine Region.Disjoint.sub_right ?_ (Region.sub_prefix (show 24 ≤ 32 by decide))
  first
    | with_reducible assumption
    | sig_disjoint_symm
    | (simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at *
       first | with_reducible assumption | sig_disjoint_symm)

/-! ## `vg_aes_gcm_seal_prepared_aesni_pclmul` -/

/-- The variant on AES-NI and PCLMULQDQ, without interleaved loops
(`VG.Proof.Variants.AesGcm.X86_64.aesNiPclmul`). -/
def aesNiPclmulV : GcmVariant := ⟨.aesni, .aesni, .pclmul, none⟩

/-- Its `vg_aes_gcm_encrypt_blocks_aesni_pclmul` leaves in `scratch` the
arguments kept, and nothing else written: it has no loops of its own, and
its calls need no working space. -/
theorem blkB_aesniPclmul_leaves : BlkLeaves aesNiPclmulV.impl.blkB :=
  blkLeaves_of (fun _ => 0) (fun _ _ _ => false) fun s hpre => by
    change WP isa (Impl.AesGcm.X86_64.Blocks.encrypt
      ⟨aesNiPclmulV.impl.ctr.callee.name, aesNiPclmulV.impl.ctr.callee.code⟩ aesNiPclmulV.impl.gh.fn none) s _
    exact Blocks.encryptN_leaves (Blocks.BP.ofM hpre) _ (aesNiPclmulV.impl.ctr.free.get rfl) _
      (aesNiPclmulV.impl.gh.free.get rfl)

theorem sealCode_aesniPclmul :
    aesNiPclmulV.impl.sealCode aesNiPclmulV.impl.callees = Impl.AesGcm.X86_64.«seal» aesNiPclmulV.impl.callees := by
  have hs : aesNiPclmulV.impl.short = false := rfl
  have hf : aesNiPclmulV.impl.fin = false := rfl
  unfold GcmImpl.sealCode
  simp only [hs, hf, Bool.false_eq_true, ↓reduceIte]

/-- The bytes `vg_aes_gcm_seal`'s leaves function (`sealV`) covers: the 32
bytes at `A` (the stack pointer: its return address and its three stack
arguments) and `work` (`W`) from byte 104 on. -/
def sealQ (A W x : Addr) : Prop :=
  (⟨A, 32⟩ : Region).Contains x 1 ∨ (⟨W + BitVec.ofNat 64 104, 2456⟩ : Region).Contains x 1

/-- What `vg_aes_gcm_seal` leaves at `x` there: at `A` what `hdr` says, and in
`work` what `sealL` says. -/
def sealV (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)) (hdr : Addr → Option (BitVec 8)) (g : Reg → BitVec 64) (a : Nat → BitVec 64)
    (A x : Addr) : Option (BitVec 8) :=
  if (⟨A, 32⟩ : Region).Contains x 1 then hdr x else sealL Lb g a x

/-- The code of `vg_aes_gcm_seal_prepared_aesni_pclmul` (inside
`withStackArgScratch 2600 3`), from a state whose tag is apart from its
stack arguments: it leaves its return address and stack arguments as they
were, and `work` from byte 104 on as `sealL` says (`sealV`). -/
theorem seal_aesniPclmul_leaves :
    ∃ Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
        Option (BitVec 8),
      ∀ s t s', (Proof.AesGcm.sealX86_64M Gcm.X86_64.Stitch.CtxMode.base).pre s ∧ sealTagArgs.pre s →
        Exec isa (aesNiPclmulV.impl.sealCode aesNiPclmulV.impl.callees) s t s' →
        ∀ x, sealQ (s.gpr .rsp) (stackArg s 3) x →
          s'.mem x = (sealV Lb (fun _ => none) s.gpr (fun i => stackArg s i) (s.gpr .rsp) x).getD (s.mem x) := by
  rw [sealCode_aesniPclmul]
  obtain ⟨Lb, hL⟩ := seal_leavesF _ aesNiPclmulV.impl.blkB blkB_aesniPclmul_leaves (aesNiPclmulV.impl.gh.free.get rfl)
    (aesNiPclmulV.impl.ctr.free.get rfl)
  refine ⟨Lb, fun s t s' ⟨hp, hta⟩ he x hx => ?_⟩
  obtain ⟨hw, hf⟩ := hL s t s' hp he
  obtain ⟨C, -, -, -, r_t⟩ := OneCtx.ofSeal hp.1 (Gcm.X86_64.Stitch.CtxMode.base.ge)
  have hta' : (⟨stackArg s 2, 16⟩ : Region).Disjoint ⟨s.gpr .rsp + BitVec.ofNat 64 8, 24⟩ := hta
  have hsW : ∀ {y : Addr}, (⟨s.gpr .rsp, 32⟩ : Region).Contains y 1 →
      ¬ (⟨stackArg s 3, 2560⟩ : Region).Contains y 1 := fun {y} hy hW => by
    by_cases h8 : (y - s.gpr .rsp).toNat < 8
    · exact C.rW y (by simp only [Region.Contains] at hy ⊢; omega_using [h8]) hW
    · have : (⟨s.gpr .rsp + BitVec.ofNat 64 8, 8 * 4⟩ : Region).Contains y 1 := by
        have := (Offset.lt_iff y (s.gpr .rsp) (d := 8) (n := 32) (by decide)).2
          ⟨by omega_arith, by simp only [Region.Contains] at hy; omega_using [hy]⟩
        simp only [Region.Contains]; omega_using [this]
      exact C.dA y this hW
  rcases hx with hx | hx
  · simp only [sealV, hx, ↓reduceIte, Option.getD_none]
    have hsplit : (⟨s.gpr .rsp, 8⟩ : Region).Contains x 1 ∨
        (⟨s.gpr .rsp + BitVec.ofNat 64 8, 24⟩ : Region).Contains x 1 := by
      by_cases h8 : (x - s.gpr .rsp).toNat < 8
      · exact .inl (by simp only [Region.Contains] at hx ⊢; omega_using [h8])
      · refine .inr ?_
        have := (Offset.lt_iff x (s.gpr .rsp) (d := 8) (n := 24) (by decide)).2
          ⟨by omega_arith, by simp only [Region.Contains] at hx; omega_using [hx]⟩
        simp only [Region.Contains]; omega_using [this]
    have hA4 : (⟨s.gpr .rsp + BitVec.ofNat 64 8, 24⟩ : Region).Sub ⟨s.gpr .rsp + BitVec.ofNat 64 8, 8 * 4⟩ :=
      Region.sub_prefix (by decide)
    refine hf x fun r hr hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hsW hx hc
    · rcases hsplit with h | h
      · exact C.rD x h hc
      · exact C.dAD x (hA4 x h) hc
    · rcases hsplit with h | h
      · exact r_t x h hc
      · exact hta' x hc h
    · rcases hsplit with h | h
      · exact Offset.base_disjoint_below _ (n := 24) (k := 8) (by decide) x h hc
      · exact Offset.disjoint_below _ (n := 24) (d := 8) (k := 24) (by decide) x h hc
  · have hx' : (⟨stackArg s 3 + BitVec.ofNat 64 96, 2464⟩ : Region).Contains x 1 :=
      Offset.sub _ (by decide) (by decide) x hx
    have hnA : ¬ (⟨s.gpr .rsp, 32⟩ : Region).Contains x 1 := fun h =>
      hsW h (Lay.wSub (N := 2560) (by decide) x hx')
    simp only [sealV, hnA, ↓reduceIte]
    exact hw x hx'

/-- Where `vg_aes_gcm_seal`'s code in the frame of `withStackArgScratch 2600 3`
from `s` has its stack pointer, and `work`. -/
abbrev sealA (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 2600
abbrev sealW (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 2600 + BitVec.ofNat 64 40

/-- What is left at the stack pointer of `vg_aes_gcm_seal`'s code in the
frame from `s`: what was there in its first 8 bytes (`none`), then the
copies of the stack arguments (`sealArgs`). -/
def sealHdr (s : State) (x : Addr) : Option (BitVec 8) :=
  if (x - sealA s).toNat < 8 then none
  else some ((sealArgs s ((x - sealA s).toNat / 8 - 1)).extractLsb' (8 * ((x - sealA s).toNat % 8)) 8)

/-- What `vg_aes_gcm_seal_prepared`'s code leaves at its frame's stack pointer
and in `work`, of its entry `s`. -/
def sealVs (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
    Option (BitVec 8)) (s : State) (x : Addr) : Option (BitVec 8) :=
  sealV Lb (sealHdr s) s.gpr (sealArgs s) (sealA s) x

/-- What `sealV` says of the state `narrowS` runs `vg_aes_gcm_seal`'s code
from, in the frame of `withStackArgScratch 2600 3` from `s`, `sealVs` says of
`s`. -/
theorem narrowS_sealV {sig : Sig} {e : Elem} {n : Nat}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    (h3 : nStack sig = 3) (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 16 + 8 * nStack sig + n * e.size ≤ 2600)
    {s : State} (hs : (sig.contract abi pre post wa (24 + 2600) leak).pre s)
    (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8))
    {x : Addr} (hx : sealQ (sealA s) (sealW s) x) :
    sealQ ((narrowS sig e n 2600 s).gpr .rsp) (stackArg (narrowS sig e n 2600 s) 3) x ∧
      (sealV Lb (fun _ => none) (narrowS sig e n 2600 s).gpr (fun i => stackArg (narrowS sig e n 2600 s) i)
          ((narrowS sig e n 2600 s).gpr .rsp) x).getD ((narrowS sig e n 2600 s).mem x) =
        (sealVs Lb s x).getD (s.mem x) := by
  obtain ⟨hg, ha, hl, hf⟩ := narrowS_args hk hb (by decide) hs
  obtain ⟨hrsp, -⟩ := narrowS_facts (nm := "") hk hb (by decide) hs
  rw [h3] at ha hl hf
  have hW : stackArg (narrowS sig e n 2600 s) 3 = sealW s := hl
  have hA : (narrowS sig e n 2600 s).gpr .rsp = sealA s := hrsp
  refine ⟨by rw [hW, hA]; exact hx, ?_⟩
  rw [hA]
  unfold sealVs sealV
  by_cases hh : (⟨sealA s, 32⟩ : Region).Contains x 1
  · simp only [hh, ↓reduceIte, Option.getD_none, sealHdr]
    have hlt : (x - sealA s).toNat < 32 := by simp only [Region.Contains] at hh; omega_using [hh]
    generalize hd : (x - sealA s).toNat = d at hlt ⊢
    have ex : x = sealA s + BitVec.ofNat 64 d := by
      rw [← hd, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    by_cases h8 : d < 8
    · simp only [h8, ↓reduceIte, Option.getD_none]
      refine hf x fun r hr hc => ?_
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains] at hc
      rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl] at hc
      have hc' : (x - (sealA s + BitVec.ofNat 64 8)).toNat < 8 * (3 + 1) := by
        have h' : (x - (sealA s + BitVec.ofNat 64 8)).toNat + 1 ≤ 8 * (3 + 1) := hc
        omega_using [h']
      have := (Offset.lt_iff x (sealA s) (d := 8) (n := 8 * (3 + 1)) (by decide)).1 hc'
      omega_using [this, h8, hd]
    · simp only [h8, ↓reduceIte, Option.getD_some]
      have ex' : x = sealA s + BitVec.ofNat 64 (8 * (d / 8)) + BitVec.ofNat 64 (d % 8) := by
        rw [Offset.add_add_eq _ (show 8 * (d / 8) + d % 8 = d by omega_arith), ex]
      have hrd : (narrowS sig e n 2600 s).mem.readW (sealA s + BitVec.ofNat 64 (8 * (d / 8))) 64 =
          stackArg (narrowS sig e n 2600 s) (d / 8 - 1) := by
        unfold stackArg stackArgAddr
        rw [hA, show 8 * (d / 8 - 1 + 1) = 8 * (d / 8) by omega_arith]
      have hj : d / 8 - 1 < 3 := by omega_arith
      rw [ex', Blocks.byte_readW64 (narrowS sig e n 2600 s).mem (sealA s + BitVec.ofNat 64 (8 * (d / 8)))
        (j := d % 8) (by omega_arith), hrd, ha _ hj]
      simp only [sealArgs, hj, ↓reduceIte]
  · simp only [hh, ↓reduceIte]
    have hx' : (⟨s.gpr .rsp - BitVec.ofNat 64 2600 + BitVec.ofNat 64 40 + BitVec.ofNat 64 96, 2464⟩ : Region).Contains x 1 := by
      rcases hx with hx | hx
      · exact absurd hx hh
      · exact Offset.sub _ (by decide) (by decide) x hx
    exact (narrowS_sealL (sig := sig) (e := e) (n := n) h3 hk hb hs Lb hx').2

/-- The code of `vg_aes_gcm_seal` of the variant `v` for the key context of
`vg_aes_gcm_init`, in the frame of `withStackArgScratch 2600 3`, from a state
meeting `vg_aes_gcm_seal_prepared`'s precondition and `C`: what `sealVs` says
the code leaves where `sealQ` says. -/
theorem seal_branchQ (v : GcmVariant) (hc : v.impl.sealCode v.impl.callees = Impl.AesGcm.X86_64.«seal» v.impl.callees)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : ∀ s t s', (Proof.AesGcm.sealX86_64M Gcm.X86_64.Stitch.CtxMode.base).pre s ∧ sealTagArgs.pre s →
      Exec isa (v.impl.sealCode v.impl.callees) s t s' →
      ∀ x, sealQ (s.gpr .rsp) (stackArg s 3) x →
        s'.mem x = (sealV Lb (fun _ => none) s.gpr (fun i => stackArg s i) (s.gpr .rsp) x).getD (s.mem x))
    {C : Mem → Addr → Prop} :
    ∀ s t u, (Spec.Gcm.sealPreparedContract X86_64.abi 2624).pre s → C s.mem (s.gpr .rdi) →
      Exec isa (withStackArgScratch 2600 3 (v.impl.sealCode v.impl.callees)) s t u →
      ∀ x, sealQ (sealA s) (sealW s) x → u.mem x = (loseL (sealA s) 2600
        (innerU (Impl.AesGcm.X86_64.«seal» v.impl.callees) (narrowS Spec.Gcm.sealSig .u64 320 2600 (narrow32 s)))
        (sealVs Lb s) x).getD (s.mem x) := by
  rw [hc] at hL
  intro s t u hs hf he x hx
  rw [hc] at he
  unfold Spec.Gcm.sealPreparedContract at hs
  have h₁ := pre_of_rel (N := 129) (C := C) (leakB := none)
    (pre := Spec.Gcm.sealPreparedPre 64) (pre' := Spec.Gcm.sealPre 64) (fun _ _ _ _ _ _ _ _ _ _ h _ => h.1) hs hf
  have h₂ := pre_narrowFirstArray (n := 32) (n' := 129) (by decide) (pre := Spec.Gcm.sealPre 64)
    (fun _ _ _ _ _ _ _ _ _ _ h => h) h₁
  obtain ⟨t₁, u₁, he₁, hm⟩ := exec_narrow (seal_framed v.impl) h₂
    (fun _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)) (Covers.refl _) he
  obtain ⟨hx', hv⟩ := narrowS_sealV (sig := Spec.Gcm.sealSig) (e := .u64) (n := 320) (by decide)
    (by decide) (by decide) h₂ Lb hx
  rw [hm, framed_leavesQ (sig := Spec.Gcm.sealSig) (nm := "work") (e := .u64) (n := 320)
    (bytes := 2600) (stack := 24) (pre := Spec.Gcm.sealPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.sealRoundsPost X86_64.abi.ptrBits) (wa := true) (leak := none)
    (seal_verified v.impl) (fun s h => ⟨⟨sealCode_implies.pre s h, trivial⟩, sealScratch_tagArgs s h⟩) hL
    (by decide) (by decide) (by decide) (seal_spSafe _) (seal_xdepth _)
    (sealPre_local _) h₂ he₁ x hx']
  exact loseL_getD_congr hv

/-- The granules `vg_aes_gcm_seal_prepared_aesni_pclmul` wipes, of its 2624
bytes of stack in chunks of 8 (at the top) and 2616, whose 16-byte granules
are then aligned: the 24 bytes below its frame (an 8-byte granule and a
16-byte one), and `work`'s address with the first 104 bytes of `work`: the
tag, `J₀`, `Y`, the counter and the keystream (seven). -/
def sealKsA : List Nat := [0, 8, 56, 72, 88, 104, 120, 136, 152]

/-- A byte of the 2624 below `R` that `wipe sealKsA` does not zero is where
`sealQ` says. -/
theorem sealWindowA {R x : Addr} (hx : (⟨R - BitVec.ofNat 64 2624, 2624⟩ : Region).Contains x 1)
    (hw : ¬ WCov sealKsA [8, 2616] R x) :
    sealQ (R - BitVec.ofNat 64 2600) (R - BitVec.ofNat 64 2600 + BitVec.ofNat 64 40) x := by
  simp only [WCov, List.sum_cons, List.sum_nil, Nat.add_zero, show 8 + 2616 = 2624 from rfl] at hw
  have hlt : (x - (R - BitVec.ofNat 64 2624)).toNat < 2624 := by simp only [Region.Contains] at hx; omega_using [hx]
  generalize hi : (x - (R - BitVec.ofNat 64 2624)).toNat = i at hlt hw
  have hc : ¬ cov sealKsA [8, 2616] i = true := fun h => hw ⟨hx, h⟩
  have hi' : ¬ i < 24 ∧ ¬ (56 ≤ i ∧ i < 168) := by
    refine ⟨fun h => hc ?_, fun h => hc ?_⟩ <;>
      simp only [cov, covC, List.sum_cons, List.sum_nil, show i < 2616 by omega_arith, ↓reduceIte, Nat.add_zero,
        show 2616 % 16 = 8 from rfl, Nat.sub_zero, Nat.zero_add]
    · by_cases h8 : i < 8
      · simp [h8, sealKsA]
      · simp only [h8, ↓reduceIte]
        rw [show (i - 8) / 16 = 0 by omega_arith]; simp [sealKsA]
    · simp only [show ¬ i < 8 by omega_arith, ↓reduceIte]
      rcases (by omega_arith : (i - 8) / 16 = 3 ∨ (i - 8) / 16 = 4 ∨ (i - 8) / 16 = 5 ∨ (i - 8) / 16 = 6 ∨
        (i - 8) / 16 = 7 ∨ (i - 8) / 16 = 8 ∨ (i - 8) / 16 = 9) with e | e | e | e | e | e | e <;> rw [e] <;>
        simp [sealKsA]
  have eA : R - BitVec.ofNat 64 2600 = R - BitVec.ofNat 64 2624 + BitVec.ofNat 64 24 :=
    Offset.sub_ofNat_eq R (show 2600 ≤ 2624 by decide)
  have mk : ∀ {d k : Nat}, d ≤ i → i < d + k → d + k ≤ 2624 →
      (⟨R - BitVec.ofNat 64 2624 + BitVec.ofNat 64 d, k⟩ : Region).Contains x 1 := fun {d k} h₁ h₂ h₃ => by
    have := (Offset.lt_iff x (R - BitVec.ofNat 64 2624) (d := d) (n := k) (by omega_arith)).2
      ⟨by omega_arith, by omega_arith⟩
    simp only [Region.Contains]; omega_using [this]
  unfold sealQ
  rw [eA, Offset.add_add, Offset.add_add]
  by_cases h₁ : i < 56
  · exact .inl (mk (by omega_arith) (by omega_arith) (by decide))
  · exact .inr (mk (by omega_arith) (by omega_arith) (by decide))

theorem sealV_congr (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)) {hdr hdr' : Addr → Option (BitVec 8)} {g g' : Reg → BitVec 64} {a a' : Nat → BitVec 64}
    {A x : Addr} (hh : (⟨A, 32⟩ : Region).Contains x 1 → hdr x = hdr' x)
    (hg : ∀ r, r ≠ .rax → r ≠ .rsp → g r = g' r) (ha : ∀ i < 4, a i = a' i) :
    sealV Lb hdr g a A x = sealV Lb hdr' g' a' A x := by
  unfold sealV
  by_cases h : (⟨A, 32⟩ : Region).Contains x 1
  · simp only [h, ↓reduceIte]; exact hh h
  · simp only [h, ↓reduceIte, sealL_congr Lb hg ha]

open VG.X86_64.Scrub in
/-- Two runs of the code of `vg_aes_gcm_seal_prepared` of a variant whose
loops read only the key context, where its `vg_aes_gcm_seal` leaves what
`sealV` says (`hL`), with the same public data leave the same bytes in its
stack but the granules `sealKsA`. -/
theorem sealW_resOk (v : GcmVariant)
    (hc : v.impl.sealCode v.impl.callees = Impl.AesGcm.X86_64.«seal» v.impl.callees)
    (hL : ∃ Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
        Option (BitVec 8),
      ∀ s t s', (Proof.AesGcm.sealX86_64M Gcm.X86_64.Stitch.CtxMode.base).pre s ∧ sealTagArgs.pre s →
        Exec isa (v.impl.sealCode v.impl.callees) s t s' →
        ∀ x, sealQ (s.gpr .rsp) (stackArg s 3) x →
          s'.mem x = (sealV Lb (fun _ => none) s.gpr (fun i => stackArg s i) (s.gpr .rsp) x).getD (s.mem x)) :
    ResOk (withStackArgScratch 2600 3 (v.impl.sealCode v.impl.callees))
      (Spec.Gcm.sealPreparedContract X86_64.abi 2624) 2624 sealKsA [8, 2616] := by
  obtain ⟨Lb, hL⟩ := hL
  unfold Spec.Gcm.sealPreparedContract
  refine resOk_of_leaves (V := fun s x => loseL (sealA s) 2600
      (innerU (Impl.AesGcm.X86_64.«seal» v.impl.callees) (narrowS Spec.Gcm.sealSig .u64 320 2600 (narrow32 s)))
      (sealVs Lb s) x) ScrubAbi.plain ?_ ?_
  · intro s t u hs he x hx hw
    exact seal_branchQ v hc hL (C := fun _ _ => True) s t u hs trivial he x (sealWindowA hx hw)
  · intro s₁ s₂ h₁ h₂ hp ho hu hsy
    have ha := sealArgs_pub hp ho
    have hsp : s₁.gpr .rsp = s₂.gpr .rsp := ho.2.2.1 .rsp (by decide)
    have hA : sealA s₁ = sealA s₂ := by simp only [sealA, hsp]
    have hV : sealVs Lb s₁ = sealVs Lb s₂ := by
      funext x
      unfold sealVs
      rw [ha, hA]
      exact sealV_congr Lb (fun _ => by simp only [sealHdr, ha, hA]) (fun r hr _ => ho.2.2.1 r hr) (fun _ _ => rfl)
    have hsy' : ∀ n ∈ UpperLock.inames (Impl.AesGcm.X86_64.«seal» v.impl.callees), s₁.syms n = s₂.syms n := by
      rw [← hc]; exact hsy
    have hU := seal32_innerU v (C := fun _ _ => True) h₁ h₂ trivial trivial hp hu hsy'
    funext x
    dsimp only
    rw [hA, hU, hV]

/-- `vg_aes_gcm_seal_prepared` of a variant whose loops read only the key
context. -/
def sealWPlain (v : GcmVariant) : Unscrubbed Spec.Gcm.sealPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := withStackArgScratch 2600 3 (v.impl.sealCode v.impl.callees)
  stack := 2624
  verified := VG.Proof.AesGcm.Flag.seal_keyed (Flag.seal_of_base (sealSel_framed v.impl Short.shortFacts))
  spSafe := X86_64.withStackArgScratch_spSafe (sealCode_spSafe v.impl v.impl.blkB)

/-- `vg_aes_gcm_seal_prepared_aesni_pclmul`, followed by the clearing of the
granules `sealKsA` (an 8-byte and eight 16-byte aligned stores): it returns
without secret residue (`sealW_resOk`). -/
def sealWAesniPclmul : Registration Spec.Gcm.sealPreparedApi X86_64.target :=
  RScrub.withScrubResC (sealWPlain aesNiPclmulV) (sealPreparedOut _) sealKsA [8, 2616]
    (sealW_resOk aesNiPclmulV sealCode_aesniPclmul seal_aesniPclmul_leaves)

/-! ## `vg_aes_gcm_stream_encrypt_prepared` and `_decrypt_prepared`, clearing by path -/

/-- `BlkLeavesD` from what the decryption leaves in `scratch` (`Blocks.Scr`). -/
theorem blkLeavesD_of {M : Gcm.X86_64.Stitch.CtxMode} {B : BlkFn M} (q : Nat → Nat) (Z : Nat → Addr → Nat → Bool)
    (h : ∀ s, (Proof.AesGcm.decryptBlocksX86_64M M).pre s → WP isa B.dec.code s fun s' =>
      Blocks.Scr s (q (Blocks.n s)) (Z (Blocks.n s) (Blocks.S s)) s'.mem) :
    BlkLeavesD B := by
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

/-- Its `vg_aes_gcm_decrypt_blocks_aesni_pclmul` leaves in `scratch` the
arguments kept, and nothing else written. -/
theorem blkBD_aesniPclmul_leaves : BlkLeavesD aesNiPclmulV.impl.blkB :=
  blkLeavesD_of (fun _ => 0) (fun _ _ _ => false) fun s hpre => by
    change WP isa (Impl.AesGcm.X86_64.Blocks.decrypt
      ⟨aesNiPclmulV.impl.ctr.callee.name, aesNiPclmulV.impl.ctr.callee.code⟩ aesNiPclmulV.impl.gh.fn none) s _
    exact Blocks.decryptN_leaves (Blocks.BP.ofM hpre) _ (aesNiPclmulV.impl.ctr.free.get rfl) _
      (aesNiPclmulV.impl.gh.free.get rfl)

/-- The key-context `vg_aes_gcm_decrypt_blocks_vaes_vpclmul` leaves in
`scratch` what `blkB_vaes_leaves` says of the encryption: the arguments kept,
the 256 bytes of its loops' copy of the powers cleared if it had at least 16
blocks (`Stitch.dec_okL`), and nothing else written. -/
theorem blkBD_vaes_leaves : BlkLeavesD VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.blkB :=
  blkLeavesD_of (fun n => n - n % 16) (fun n _ d => decide (16 ≤ n) && decide (64 ≤ d) && decide (d < 320))
    fun s hpre => by
      change WP isa (Impl.AesGcm.X86_64.Blocks.decrypt
        ⟨VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.ctr.callee.name,
          VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.ctr.callee.code⟩
        VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.gh.fn (some Impl.Gcm.X86_64.Stitch.dec) false false)
        s _
      exact Blocks.decryptB_leaves (Blocks.BP.ofM hpre) _
        (VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.ctr.free.get rfl) _
        (VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.gh.free.get rfl)
        fun s₃ h₃ hm => Gcm.X86_64.Stitch.dec_okL h₃.base hm

/-- The prepared-16 `vg_aes_gcm_decrypt_blocks_prepared16_vaes_vpclmul`
leaves in `scratch` what `blkR16_vaes_leaves` says of the encryption
(`StitchR.decR_okL`). -/
theorem blkR16D_vaes_leaves : BlkLeavesD (blkR16 VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant) :=
  blkLeavesD_of (fun _ => 0) (fun n S d => decide (2 ≤ n) && (decide (AlignedScratch.offset true S ≤ d) &&
      decide (d < AlignedScratch.offset true S + 512) && Gcm.X86_64.StitchR.zeroR n (d - AlignedScratch.offset true S)))
    fun s hpre => by
      change WP isa (Impl.AesGcm.X86_64.Blocks.decrypt
        ⟨VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.ctr.callee.name,
          VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.ctr.callee.code⟩
        VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.gh.fn (some Impl.Gcm.X86_64.StitchR.decR) true true
        true false (some Impl.Gcm.X86_64.StitchR.decR)) s _
      exact Blocks.decryptR_leaves (Blocks.BP.ofM hpre) _
        (VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.ctr.free.get rfl) _
        (VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.gh.free.get rfl) (ℓ := 512) (by decide)
        fun s₃ h₃ => Gcm.X86_64.StitchR.decR_okL h₃.toPrepared (by decide)

/-! ## `vg_aes_gcm_stream_{en,de}crypt_prepared_aesni_pclmul`, without secret residue -/

section
open VG.X86_64.Scrub
open VG.Impl.StackScratch.X86_64 (withStackArgScratch)
open Gcm.X86_64.Stitch (CtxMode)


theorem streamEnc_narrowPre {s : State} (hs : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pre s) :
    (Proof.AesGcm.streamEncryptRoundsContract X86_64.abi 2608).pre (narrow32 s) :=
  pre_narrowFirstArray (n := 32) (n' := 129) (by decide) (pre := Spec.Gcm.streamTextPre 64)
    (pre' := Spec.Gcm.streamCryptPreparedPre 64) (post := Proof.AesGcm.streamEncryptRoundsPost 64) (leak := none)
    (fun _ _ _ _ _ _ _ _ h => h.1) hs

theorem streamDec_narrowPre {s : State} (hs : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pre s) :
    (Proof.AesGcm.streamDecryptRoundsContract X86_64.abi 2608).pre (narrow32 s) :=
  pre_narrowFirstArray (n := 32) (n' := 129) (by decide) (pre := Spec.Gcm.streamTextPre 64)
    (pre' := Spec.Gcm.streamCryptPreparedPre 64) (post := Proof.AesGcm.streamDecryptRoundsPost 64) (leak := none)
    (fun _ _ _ _ _ _ _ _ h => h.1) hs

/-- The public data of the prepared contract, of the narrowed states. -/
theorem streamEnc_narrowPub {s₁ s₂ : State}
    (hp : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pub s₁ s₂) :
    (Proof.AesGcm.streamEncryptRoundsContract X86_64.abi 2608).pub (narrow32 s₁) (narrow32 s₂) := by
  unfold Spec.Gcm.streamEncryptPreparedContract at hp
  obtain ⟨⟨hs, -⟩, hpubs, hdescs⟩ := (pubL_args (sig := Spec.Gcm.streamCryptPreparedSig) (by decide)).mp hp
  unfold Proof.AesGcm.streamEncryptRoundsContract
  exact (pubL_args (sig := Spec.Gcm.streamCryptSig) (by decide)).mpr ⟨⟨hs, trivial⟩, hpubs,
    fun r hr i hi => hdescs r (by rw [show Spec.Gcm.streamCryptPreparedSig.params =
      ("ctx", .array false .u64 129) :: Spec.Gcm.streamCryptSig.params.tail from rfl, descs_array .u64 32 129]; exact hr) i hi⟩

theorem streamDec_narrowPub {s₁ s₂ : State}
    (hp : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pub s₁ s₂) :
    (Proof.AesGcm.streamDecryptRoundsContract X86_64.abi 2608).pub (narrow32 s₁) (narrow32 s₂) := by
  unfold Spec.Gcm.streamDecryptPreparedContract at hp
  obtain ⟨⟨hs, -⟩, hpubs, hdescs⟩ := (pubL_args (sig := Spec.Gcm.streamCryptPreparedSig) (by decide)).mp hp
  unfold Proof.AesGcm.streamDecryptRoundsContract
  exact (pubL_args (sig := Spec.Gcm.streamCryptSig) (by decide)).mpr ⟨⟨hs, trivial⟩, hpubs,
    fun r hr i hi => hdescs r (by rw [show Spec.Gcm.streamCryptPreparedSig.params =
      ("ctx", .array false .u64 129) :: Spec.Gcm.streamCryptSig.params.tail from rfl, descs_array .u64 32 129]; exact hr) i hi⟩

/-- Two runs with the same public data have the same length. -/
theorem streamLen_pub {s₁ s₂ : State} {pre : Curry (Spec.Gcm.streamCryptPreparedSig.words abi.ptrBits) (Mem → Prop)}
    {post : Spec.Gcm.streamCryptPreparedSig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (Spec.Gcm.streamCryptPreparedSig.words abi.ptrBits) (Mem → List Nat))}
    (hp : (Spec.Gcm.streamCryptPreparedSig.contract abi pre post wa stack leak).pub s₁ s₂) :
    stackArg s₁ 0 = stackArg s₂ 0 := by
  obtain ⟨-, hpubs, -⟩ := (pubL_args (sig := Spec.Gcm.streamCryptPreparedSig) (by decide)).mp hp
  have := hpubs 6 rfl
  have hw : ((Spec.Gcm.streamCryptPreparedSig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD 6 64 = 64 := rfl
  rw [hw, BitVec.setWidth_eq, BitVec.setWidth_eq] at this
  exact this

/-- The bytes below the stack pointer on entry, outside every buffer, are
the same in two runs `NoResidue` relates. -/
theorem below_same {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
    {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s₁ s₂ : State}
    (h₁ : (sig.contract abi pre post wa stack leak).pre s₁) (ho : Outside 0 s₁ s₂) (hs : stack ≠ 0) :
    ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 → s₁.mem x = s₂.mem x :=
  fun x hx => ho.2.2.2.2.2.2.2.2.2.2.2.2.2.2 x fun r hr =>
    ((contract_pre_scrub ScrubAbi.plain h₁).2 r hr).2 hs x hx

theorem frame_or_below {R x : Addr} (hx : (⟨R - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1)
    (hb : ¬ (below (R - BitVec.ofNat 64 2584) 24).Contains x 1) :
    (⟨R - BitVec.ofNat 64 2584, 2584⟩ : Region).Contains x 1 := by
  have e : R - BitVec.ofNat 64 2584 - BitVec.ofNat 64 24 = R - BitVec.ofNat 64 2608 := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  simp only [Region.Contains, e] at hx hb ⊢
  have e' : R - BitVec.ofNat 64 2584 = R - BitVec.ofNat 64 2608 + BitVec.ofNat 64 24 :=
    Offset.sub_ofNat_eq R (show 2584 ≤ 2608 by decide)
  rw [e']
  have := (Offset.lt_iff x (R - BitVec.ofNat 64 2608) (d := 24) (n := 2584) (by decide)).2
    ⟨by omega_arith, by omega_arith⟩
  omega_using [this]

open StackLock in
/-- Two runs of `vg_aes_gcm_stream_encrypt_prepared` clearing the registers
after each call (at the level `lv`), on the key context, with callees that
never touch their working space, with the same public data, from states
that agree on the registers but `rax` and on the stack below them, leave
the same bytes in all 2608 of their stack: below the frame the same return
addresses and stack argument (`streamEncryptClrB_below`), and in it what
`streamFV` says of their entry (`streamEncryptClrB_leaves`), which depends
on no secret. -/
theorem streamEncB_agree (lv : Impl.Scrub.X86_64.VecLevel) (v : GcmImpl) (B : BlkFn CtxMode.base)
    (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) (hB : BlkLeaves B)
    (hct : Plain v.callees.ctr.code) (hgh : Plain v.callees.gh.code) (hn : UpperLock.inames B.enc.code = [])
    {s₁ s₂ : State}
    (h₁ : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pre s₁)
    (h₂ : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pre s₂)
    (hp : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pub s₁ s₂)
    (hg : ∀ r, r ≠ .rax → s₁.gpr r = s₂.gpr r)
    (hbm : ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 → s₁.mem x = s₂.mem x)
    (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (Impl.AesGcm.X86_64.streamEncryptClr (v.withBlk B) lv), s₁.syms n = s₂.syms n) {t₁ t₂ : List Leak} {u₁ u₂ : State}
    (e₁ : Exec isa (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr (v.withBlk B) lv)) s₁ t₁ u₁)
    (e₂ : Exec isa (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr (v.withBlk B) lv)) s₂ t₂ u₂) :
    ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 → u₁.mem x = u₂.mem x := by
  obtain ⟨Lb, hL⟩ := hB
  intro x hx
  have hn₁ := streamEnc_narrowPre h₁
  have hn₂ := streamEnc_narrowPre h₂
  have hv := streamEncryptClrB_framed lv v B
  obtain ⟨t₁', u₁', e₁', hm₁⟩ := exec_narrow hv hn₁
    (fun _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)) (Covers.refl _) e₁
  obtain ⟨t₂', u₂', e₂', hm₂⟩ := exec_narrow hv hn₂
    (fun _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)) (Covers.refl _) e₂
  have hrsp : s₁.gpr .rsp = s₂.gpr .rsp := hg .rsp (by decide)
  unfold Spec.Gcm.streamEncryptPreparedContract at hp
  rw [hm₁, hm₂]
  by_cases hb : (below (s₁.gpr .rsp - BitVec.ofNat 64 2584) 24).Contains x 1
  · exact streamEncryptClrB_below lv v B hct hgh hn hn₁ hn₂ (streamEnc_narrowPub hp) hrsp hbm hu e₁' e₂' x hb
  · have hx' := frame_or_below hx hb
    rw [streamEncryptClrB_leaves lv v gf cf B hL hn₁ e₁' x hx',
      streamEncryptClrB_leaves lv v gf cf B hL hn₂ e₂' x (by have h := hx'; rw [hrsp] at h; exact h),
      streamFV_congr Lb (s₁ := narrow32 s₁) (s₂ := narrow32 s₂) hg (streamLen_pub (s₁ := s₁) (s₂ := s₂) hp)]
    have hb' : (narrow32 s₁).gpr .rsp = (narrow32 s₂).gpr .rsp := hrsp
    rw [streamEncryptClrB_leaves_innerU lv v B hn₁ hn₂ (streamEnc_narrowPub hp) hu hsy, hb']
    exact congrArg (Option.getD _) (hbm x hx)

open StackLock in
/-- `streamEncB_agree` for `vg_aes_gcm_stream_decrypt_prepared`. -/
theorem streamDecB_agree (lv : Impl.Scrub.X86_64.VecLevel) (v : GcmImpl) (B : BlkFn CtxMode.base)
    (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) (hB : BlkLeavesD B)
    (hct : Plain v.callees.ctr.code) (hgh : Plain v.callees.gh.code) (hn : UpperLock.inames B.dec.code = [])
    {s₁ s₂ : State}
    (h₁ : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pre s₁)
    (h₂ : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pre s₂)
    (hp : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pub s₁ s₂)
    (hg : ∀ r, r ≠ .rax → s₁.gpr r = s₂.gpr r)
    (hbm : ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 → s₁.mem x = s₂.mem x)
    (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (Impl.AesGcm.X86_64.streamDecryptClr (v.withBlk B) lv), s₁.syms n = s₂.syms n) {t₁ t₂ : List Leak} {u₁ u₂ : State}
    (e₁ : Exec isa (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecryptClr (v.withBlk B) lv)) s₁ t₁ u₁)
    (e₂ : Exec isa (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecryptClr (v.withBlk B) lv)) s₂ t₂ u₂) :
    ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 → u₁.mem x = u₂.mem x := by
  obtain ⟨Lb, hL⟩ := hB
  intro x hx
  have hn₁ := streamDec_narrowPre h₁
  have hn₂ := streamDec_narrowPre h₂
  have hv := streamDecryptClrB_framed lv v B
  obtain ⟨t₁', u₁', e₁', hm₁⟩ := exec_narrow hv hn₁
    (fun _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)) (Covers.refl _) e₁
  obtain ⟨t₂', u₂', e₂', hm₂⟩ := exec_narrow hv hn₂
    (fun _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)) (Covers.refl _) e₂
  have hrsp : s₁.gpr .rsp = s₂.gpr .rsp := hg .rsp (by decide)
  unfold Spec.Gcm.streamDecryptPreparedContract at hp
  rw [hm₁, hm₂]
  by_cases hb : (below (s₁.gpr .rsp - BitVec.ofNat 64 2584) 24).Contains x 1
  · exact streamDecryptClrB_below lv v B hct hgh hn hn₁ hn₂ (streamDec_narrowPub hp) hrsp hbm hu e₁' e₂' x hb
  · have hx' := frame_or_below hx hb
    rw [streamDecryptClrB_leaves lv v gf cf B hL hn₁ e₁' x hx',
      streamDecryptClrB_leaves lv v gf cf B hL hn₂ e₂' x (by have h := hx'; rw [hrsp] at h; exact h),
      streamFV_congr Lb (s₁ := narrow32 s₁) (s₂ := narrow32 s₂) hg (streamLen_pub (s₁ := s₁) (s₂ := s₂) hp)]
    have hb' : (narrow32 s₁).gpr .rsp = (narrow32 s₂).gpr .rsp := hrsp
    rw [streamDecryptClrB_leaves_innerU lv v B hn₁ hn₂ (streamDec_narrowPub hp) hu hsy, hb']
    exact congrArg (Option.getD _) (hbm x hx)


theorem streamEnc16_narrowPre {s : State} (hs : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pre s)
    (hf : 16 ≤ flagCount s) :
    (Proof.AesGcm.streamEncryptPrepared16RoundsContract X86_64.abi 2608).pre (narrow128 s) := by
  unfold Spec.Gcm.streamEncryptPreparedContract at hs
  have h₁ := pre_of_rel (N := 129) (C := fun m ctx => 16 ≤ (m.readW (ctx + 1024) 64).toNat) (leakB := none)
    (pre := Spec.Gcm.streamCryptPreparedPre 64) (pre' := Proof.Gcm.streamCryptPrepared16Pre 64)
    (fun _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1 hf⟩) hs hf
  exact pre_narrowFirstArray (n := 128) (n' := 129) (by decide) (pre := Proof.Gcm.streamCryptPrepared16Pre 64)
    (fun _ _ _ _ _ _ _ _ h => h) h₁

theorem streamEnc16_narrowPub {s₁ s₂ : State}
    (hp : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pub s₁ s₂) :
    (Proof.AesGcm.streamEncryptPrepared16RoundsContract X86_64.abi 2608).pub (narrow128 s₁) (narrow128 s₂) := by
  unfold Spec.Gcm.streamEncryptPreparedContract at hp
  obtain ⟨⟨hs, -⟩, hpubs, hdescs⟩ := (pubL_args (sig := Spec.Gcm.streamCryptPreparedSig) (by decide)).mp hp
  unfold Proof.AesGcm.streamEncryptPrepared16RoundsContract
  exact (pubL_args (sig := Proof.Gcm.streamCryptPrecomputedSig) (by decide)).mpr ⟨⟨hs, trivial⟩, hpubs,
    fun r hr i hi => hdescs r (by
      rw [show Spec.Gcm.streamCryptPreparedSig.params = ("ctx", .array false .u64 129) ::
        Proof.Gcm.streamCryptPrecomputedSig.params.tail from rfl, descs_array .u64 128 129]
      exact hr) i hi⟩

open StackLock in
/-- `streamEncB_agree`, over a `vg_aes_ctr32` that zeroes its working space
(`CrCallZ`), what `streamFVZ` says in the frame. As there: two runs of `vg_aes_gcm_stream_encrypt_prepared` clearing the registers
after each call (at the level `lv`), on the key context, with callees that
never touch their working space, with the same public data, from states
that agree on the registers but `rax` and on the stack below them, leave
the same bytes in all 2608 of their stack: below the frame the same return
addresses and stack argument (`streamEncryptClrB_below`), and in it what
`streamFV` says of their entry (`streamEncryptClrB_leaves`), which depends
on no secret. -/
theorem streamEncBZ_agree (lv : Impl.Scrub.X86_64.VecLevel) (v : GcmImpl) (B : BlkFn CtxMode.base)
    {zg : Nat → Bool} (GZ : GhCallZ (v.wrapC lv) zg) {sc : Nat} {z : Nat → Bool} (hsc : sc ≤ 2048)
    (CZ : CrCallZ (v.wrapC lv) sc z) (hB : BlkLeaves B)
    (hct : Plain v.callees.ctr.code) (hgh : Plain v.callees.gh.code) (hn : UpperLock.inames B.enc.code = [])
    {s₁ s₂ : State}
    (h₁ : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pre s₁)
    (h₂ : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pre s₂)
    (hp : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pub s₁ s₂)
    (hg : ∀ r, r ≠ .rax → s₁.gpr r = s₂.gpr r)
    (hbm : ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 → s₁.mem x = s₂.mem x)
    (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (Impl.AesGcm.X86_64.streamEncryptClr (v.withBlk B) lv), s₁.syms n = s₂.syms n) {t₁ t₂ : List Leak} {u₁ u₂ : State}
    (e₁ : Exec isa (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr (v.withBlk B) lv)) s₁ t₁ u₁)
    (e₂ : Exec isa (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr (v.withBlk B) lv)) s₂ t₂ u₂) :
    ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 → u₁.mem x = u₂.mem x := by
  obtain ⟨Lb, hL⟩ := hB
  intro x hx
  have hn₁ := streamEnc_narrowPre h₁
  have hn₂ := streamEnc_narrowPre h₂
  have hv := streamEncryptClrB_framed lv v B
  obtain ⟨t₁', u₁', e₁', hm₁⟩ := exec_narrow hv hn₁
    (fun _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)) (Covers.refl _) e₁
  obtain ⟨t₂', u₂', e₂', hm₂⟩ := exec_narrow hv hn₂
    (fun _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)) (Covers.refl _) e₂
  have hrsp : s₁.gpr .rsp = s₂.gpr .rsp := hg .rsp (by decide)
  unfold Spec.Gcm.streamEncryptPreparedContract at hp
  rw [hm₁, hm₂]
  by_cases hb : (below (s₁.gpr .rsp - BitVec.ofNat 64 2584) 24).Contains x 1
  · exact streamEncryptClrB_below lv v B hct hgh hn hn₁ hn₂ (streamEnc_narrowPub hp) hrsp hbm hu e₁' e₂' x hb
  · have hx' := frame_or_below hx hb
    rw [streamEncryptClrB_leavesZ lv v B GZ hsc CZ hL hn₁ e₁' x hx',
      streamEncryptClrB_leavesZ lv v B GZ hsc CZ hL hn₂ e₂' x (by have h := hx'; rw [hrsp] at h; exact h),
      streamFVZ_congr z zg Lb (s₁ := narrow32 s₁) (s₂ := narrow32 s₂) hg (streamLen_pub (s₁ := s₁) (s₂ := s₂) hp)]
    have hb' : (narrow32 s₁).gpr .rsp = (narrow32 s₂).gpr .rsp := hrsp
    rw [streamEncryptClrB_leaves_innerU lv v B hn₁ hn₂ (streamEnc_narrowPub hp) hu hsy, hb']
    exact congrArg (Option.getD _) (hbm x hx)

open StackLock in
/-- `streamEncBZ_agree` for `vg_aes_gcm_stream_decrypt_prepared`. -/
theorem streamDecBZ_agree (lv : Impl.Scrub.X86_64.VecLevel) (v : GcmImpl) (B : BlkFn CtxMode.base)
    {zg : Nat → Bool} (GZ : GhCallZ (v.wrapC lv) zg) {sc : Nat} {z : Nat → Bool} (hsc : sc ≤ 2048)
    (CZ : CrCallZ (v.wrapC lv) sc z) (hB : BlkLeavesD B)
    (hct : Plain v.callees.ctr.code) (hgh : Plain v.callees.gh.code) (hn : UpperLock.inames B.dec.code = [])
    {s₁ s₂ : State}
    (h₁ : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pre s₁)
    (h₂ : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pre s₂)
    (hp : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pub s₁ s₂)
    (hg : ∀ r, r ≠ .rax → s₁.gpr r = s₂.gpr r)
    (hbm : ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 → s₁.mem x = s₂.mem x)
    (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (Impl.AesGcm.X86_64.streamDecryptClr (v.withBlk B) lv), s₁.syms n = s₂.syms n) {t₁ t₂ : List Leak} {u₁ u₂ : State}
    (e₁ : Exec isa (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecryptClr (v.withBlk B) lv)) s₁ t₁ u₁)
    (e₂ : Exec isa (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecryptClr (v.withBlk B) lv)) s₂ t₂ u₂) :
    ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 → u₁.mem x = u₂.mem x := by
  obtain ⟨Lb, hL⟩ := hB
  intro x hx
  have hn₁ := streamDec_narrowPre h₁
  have hn₂ := streamDec_narrowPre h₂
  have hv := streamDecryptClrB_framed lv v B
  obtain ⟨t₁', u₁', e₁', hm₁⟩ := exec_narrow hv hn₁
    (fun _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)) (Covers.refl _) e₁
  obtain ⟨t₂', u₂', e₂', hm₂⟩ := exec_narrow hv hn₂
    (fun _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)) (Covers.refl _) e₂
  have hrsp : s₁.gpr .rsp = s₂.gpr .rsp := hg .rsp (by decide)
  unfold Spec.Gcm.streamDecryptPreparedContract at hp
  rw [hm₁, hm₂]
  by_cases hb : (below (s₁.gpr .rsp - BitVec.ofNat 64 2584) 24).Contains x 1
  · exact streamDecryptClrB_below lv v B hct hgh hn hn₁ hn₂ (streamDec_narrowPub hp) hrsp hbm hu e₁' e₂' x hb
  · have hx' := frame_or_below hx hb
    rw [streamDecryptClrB_leavesZ lv v B GZ hsc CZ hL hn₁ e₁' x hx',
      streamDecryptClrB_leavesZ lv v B GZ hsc CZ hL hn₂ e₂' x (by have h := hx'; rw [hrsp] at h; exact h),
      streamFVZ_congr z zg Lb (s₁ := narrow32 s₁) (s₂ := narrow32 s₂) hg (streamLen_pub (s₁ := s₁) (s₂ := s₂) hp)]
    have hb' : (narrow32 s₁).gpr .rsp = (narrow32 s₂).gpr .rsp := hrsp
    rw [streamDecryptClrB_leaves_innerU lv v B hn₁ hn₂ (streamDec_narrowPub hp) hu hsy, hb']
    exact congrArg (Option.getD _) (hbm x hx)

open StackLock in
/-- `streamEncB_agree`, on 16 prepared powers (whose count both runs read). -/
theorem streamEnc16_agree (lv : Impl.Scrub.X86_64.VecLevel) (v : GcmImpl) (B : BlkFn CtxMode.prepared16)
    (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) (hB : BlkLeaves B)
    (hct : Plain v.callees.ctr.code) (hgh : Plain v.callees.gh.code) (hn : UpperLock.inames B.enc.code = [])
    {s₁ s₂ : State}
    (h₁ : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pre s₁)
    (h₂ : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pre s₂)
    (hf₁ : 16 ≤ flagCount s₁) (hf₂ : 16 ≤ flagCount s₂)
    (hp : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pub s₁ s₂)
    (hg : ∀ r, r ≠ .rax → s₁.gpr r = s₂.gpr r)
    (hbm : ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 → s₁.mem x = s₂.mem x)
    (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (Impl.AesGcm.X86_64.streamEncryptClr (v.withBlk B) lv), s₁.syms n = s₂.syms n) {t₁ t₂ : List Leak} {u₁ u₂ : State}
    (e₁ : Exec isa (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr (v.withBlk B) lv)) s₁ t₁ u₁)
    (e₂ : Exec isa (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr (v.withBlk B) lv)) s₂ t₂ u₂) :
    ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 → u₁.mem x = u₂.mem x := by
  obtain ⟨Lb, hL⟩ := hB
  intro x hx
  have hn₁ := streamEnc16_narrowPre h₁ hf₁
  have hn₂ := streamEnc16_narrowPre h₂ hf₂
  have hv := streamEncryptClr16_framed lv v B
  obtain ⟨t₁', u₁', e₁', hm₁⟩ := exec_narrow hv hn₁
    (fun _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)) (Covers.refl _) e₁
  obtain ⟨t₂', u₂', e₂', hm₂⟩ := exec_narrow hv hn₂
    (fun _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)) (Covers.refl _) e₂
  have hrsp : s₁.gpr .rsp = s₂.gpr .rsp := hg .rsp (by decide)
  have hpn := streamEnc16_narrowPub hp
  unfold Spec.Gcm.streamEncryptPreparedContract at hp
  rw [hm₁, hm₂]
  by_cases hb : (below (s₁.gpr .rsp - BitVec.ofNat 64 2584) 24).Contains x 1
  · exact streamEncryptClr16_below lv v B hct hgh hn hn₁ hn₂ hpn hrsp hbm hu e₁' e₂' x hb
  · have hx' := frame_or_below hx hb
    rw [streamEncryptClr16_leaves lv v gf cf B hL hn₁ e₁' x hx',
      streamEncryptClr16_leaves lv v gf cf B hL hn₂ e₂' x (by have h := hx'; rw [hrsp] at h; exact h),
      streamFV_congr Lb (s₁ := narrow128 s₁) (s₂ := narrow128 s₂) hg (streamLen_pub (s₁ := s₁) (s₂ := s₂) hp)]
    have hb' : (narrow128 s₁).gpr .rsp = (narrow128 s₂).gpr .rsp := hrsp
    rw [streamEncryptClr16_leaves_innerU lv v B hn₁ hn₂ hpn hu hsy, hb']
    exact congrArg (Option.getD _) (hbm x hx)

theorem streamDec16_narrowPre {s : State} (hs : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pre s)
    (hf : 16 ≤ flagCount s) :
    (Proof.AesGcm.streamDecryptPrepared16RoundsContract X86_64.abi 2608).pre (narrow128 s) := by
  unfold Spec.Gcm.streamDecryptPreparedContract at hs
  have h₁ := pre_of_rel (N := 129) (C := fun m ctx => 16 ≤ (m.readW (ctx + 1024) 64).toNat) (leakB := none)
    (pre := Spec.Gcm.streamCryptPreparedPre 64) (pre' := Proof.Gcm.streamCryptPrepared16Pre 64)
    (fun _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1 hf⟩) hs hf
  exact pre_narrowFirstArray (n := 128) (n' := 129) (by decide) (pre := Proof.Gcm.streamCryptPrepared16Pre 64)
    (fun _ _ _ _ _ _ _ _ h => h) h₁

theorem streamDec16_narrowPub {s₁ s₂ : State}
    (hp : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pub s₁ s₂) :
    (Proof.AesGcm.streamDecryptPrepared16RoundsContract X86_64.abi 2608).pub (narrow128 s₁) (narrow128 s₂) := by
  unfold Spec.Gcm.streamDecryptPreparedContract at hp
  obtain ⟨⟨hs, -⟩, hpubs, hdescs⟩ := (pubL_args (sig := Spec.Gcm.streamCryptPreparedSig) (by decide)).mp hp
  unfold Proof.AesGcm.streamDecryptPrepared16RoundsContract
  exact (pubL_args (sig := Proof.Gcm.streamCryptPrecomputedSig) (by decide)).mpr ⟨⟨hs, trivial⟩, hpubs,
    fun r hr i hi => hdescs r (by
      rw [show Spec.Gcm.streamCryptPreparedSig.params = ("ctx", .array false .u64 129) ::
        Proof.Gcm.streamCryptPrecomputedSig.params.tail from rfl, descs_array .u64 128 129]
      exact hr) i hi⟩

open StackLock in
/-- `streamDecB_agree`, on 16 prepared powers (whose count both runs read). -/
theorem streamDec16_agree (lv : Impl.Scrub.X86_64.VecLevel) (v : GcmImpl) (B : BlkFn CtxMode.prepared16)
    (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) (hB : BlkLeavesD B)
    (hct : Plain v.callees.ctr.code) (hgh : Plain v.callees.gh.code) (hn : UpperLock.inames B.dec.code = [])
    {s₁ s₂ : State}
    (h₁ : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pre s₁)
    (h₂ : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pre s₂)
    (hf₁ : 16 ≤ flagCount s₁) (hf₂ : 16 ≤ flagCount s₂)
    (hp : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pub s₁ s₂)
    (hg : ∀ r, r ≠ .rax → s₁.gpr r = s₂.gpr r)
    (hbm : ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 → s₁.mem x = s₂.mem x)
    (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (Impl.AesGcm.X86_64.streamDecryptClr (v.withBlk B) lv), s₁.syms n = s₂.syms n) {t₁ t₂ : List Leak} {u₁ u₂ : State}
    (e₁ : Exec isa (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecryptClr (v.withBlk B) lv)) s₁ t₁ u₁)
    (e₂ : Exec isa (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecryptClr (v.withBlk B) lv)) s₂ t₂ u₂) :
    ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 → u₁.mem x = u₂.mem x := by
  obtain ⟨Lb, hL⟩ := hB
  intro x hx
  have hn₁ := streamDec16_narrowPre h₁ hf₁
  have hn₂ := streamDec16_narrowPre h₂ hf₂
  have hv := streamDecryptClr16_framed lv v B
  obtain ⟨t₁', u₁', e₁', hm₁⟩ := exec_narrow hv hn₁
    (fun _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)) (Covers.refl _) e₁
  obtain ⟨t₂', u₂', e₂', hm₂⟩ := exec_narrow hv hn₂
    (fun _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)) (Covers.refl _) e₂
  have hrsp : s₁.gpr .rsp = s₂.gpr .rsp := hg .rsp (by decide)
  have hpn := streamDec16_narrowPub hp
  unfold Spec.Gcm.streamDecryptPreparedContract at hp
  rw [hm₁, hm₂]
  by_cases hb : (below (s₁.gpr .rsp - BitVec.ofNat 64 2584) 24).Contains x 1
  · exact streamDecryptClr16_below lv v B hct hgh hn hn₁ hn₂ hpn hrsp hbm hu e₁' e₂' x hb
  · have hx' := frame_or_below hx hb
    rw [streamDecryptClr16_leaves lv v gf cf B hL hn₁ e₁' x hx',
      streamDecryptClr16_leaves lv v gf cf B hL hn₂ e₂' x (by have h := hx'; rw [hrsp] at h; exact h),
      streamFV_congr Lb (s₁ := narrow128 s₁) (s₂ := narrow128 s₂) hg (streamLen_pub (s₁ := s₁) (s₂ := s₂) hp)]
    have hb' : (narrow128 s₁).gpr .rsp = (narrow128 s₂).gpr .rsp := hrsp
    rw [streamDecryptClr16_leaves_innerU lv v B hn₁ hn₂ hpn hu hsy, hb']
    exact congrArg (Option.getD _) (hbm x hx)

open StackLock in
/-- `streamEncB_agree` at the level of SSE, as `ResOk`. -/
theorem streamEncryptW_resOk (v : GcmImpl) (gf : GhashFree v.gh.fn.code)
    (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) (hB : BlkLeaves v.blkB) (hct : Plain v.callees.ctr.code)
    (hgh : Plain v.callees.gh.code) (hn : UpperLock.inames v.blkB.enc.code = []) :
    ResOk (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr (v.withBlk v.blkB) .sse))
      (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608) 2608 [] [2608] := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho hu hsy e₁ e₂ x hx _
  have h₁' := h₁
  unfold Spec.Gcm.streamEncryptPreparedContract at h₁'
  exact streamEncB_agree .sse v v.blkB gf cf hB hct hgh hn h₁ h₂ hp (fun r h => ho.2.2.1 r h)
    (below_same h₁' ho (by decide)) hu hsy e₁ e₂ x hx

open StackLock in
/-- `streamEncryptW_resOk` for `vg_aes_gcm_stream_decrypt_prepared`. -/
theorem streamDecryptW_resOk (v : GcmImpl) (gf : GhashFree v.gh.fn.code)
    (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) (hB : BlkLeavesD v.blkB) (hct : Plain v.callees.ctr.code)
    (hgh : Plain v.callees.gh.code) (hn : UpperLock.inames v.blkB.dec.code = []) :
    ResOk (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecryptClr (v.withBlk v.blkB) .sse))
      (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608) 2608 [] [2608] := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho hu hsy e₁ e₂ x hx _
  have h₁' := h₁
  unfold Spec.Gcm.streamDecryptPreparedContract at h₁'
  exact streamDecB_agree .sse v v.blkB gf cf hB hct hgh hn h₁ h₂ hp (fun r h => ho.2.2.1 r h)
    (below_same h₁' ho (by decide)) hu hsy e₁ e₂ x hx

/-- `vg_aes_gcm_stream_encrypt_prepared`'s postcondition reads the memory on
return only within the buffers: the state and the data. -/
theorem streamEncryptPreparedOut (stack : Nat) :
    PostOut (Spec.Gcm.streamEncryptPreparedContract X86_64.abi stack) (Spec.Gcm.streamCryptPreparedSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, data, len], _ =>
      simp only [Spec.Gcm.streamCryptPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      intro key hk
      dsimp only
      intro iv a p hr hA hT
      obtain ⟨h1, h2⟩ := h key hk iv a p hr hA hT
      refine ⟨Proof.AesGcm.streamRepr_congr (Proof.AesGcm.agree_of hb.2.1) h1, ?_⟩
      show Spec.Aes.bytesAt m₂ data len.toNat = _
      rw [Scrub.bytesAt_of0 hb.2.2 (by omega_arith)]
      exact h2

/-- `streamEncryptPreparedOut` for `vg_aes_gcm_stream_decrypt_prepared`. -/
theorem streamDecryptPreparedOut (stack : Nat) :
    PostOut (Spec.Gcm.streamDecryptPreparedContract X86_64.abi stack) (Spec.Gcm.streamCryptPreparedSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, data, len], _ =>
      simp only [Spec.Gcm.streamCryptPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      intro key hk
      dsimp only
      intro iv a c hr hA hT
      obtain ⟨h1, h2⟩ := h key hk iv a c hr hA hT
      refine ⟨Proof.AesGcm.streamRepr_congr (Proof.AesGcm.agree_of hb.2.1) h1, ?_⟩
      show Spec.Aes.bytesAt m₂ data len.toNat = _
      rw [Scrub.bytesAt_of0 hb.2.2 (by omega_arith)]
      exact h2

end

/-- `vg_aes_gcm_stream_encrypt_prepared_aesni_pclmul`, clearing the registers
after each call, before the clearing on return. -/
def streamEncryptWPlainA : Unscrubbed Spec.Gcm.streamEncryptPreparedApi X86_64.target where
  suffix := aesNiPclmulV.impl.suffix
  code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
    (Impl.AesGcm.X86_64.streamEncryptClr aesNiPclmulV.impl.callees .sse)
  stack := 2608
  verified := VG.Proof.AesGcm.Flag.streamEncrypt_keyed
    (Flag.streamEncrypt_of_base (streamEncryptClrB_framed .sse aesNiPclmulV.impl aesNiPclmulV.impl.blkB))
  spSafe := streamEncryptClr_spSafe .sse aesNiPclmulV.impl aesNiPclmulV.impl.blkB

/-- `vg_aes_gcm_stream_decrypt_prepared_aesni_pclmul`, as `streamEncryptWPlainA`. -/
def streamDecryptWPlainA : Unscrubbed Spec.Gcm.streamDecryptPreparedApi X86_64.target where
  suffix := aesNiPclmulV.impl.suffix
  code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
    (Impl.AesGcm.X86_64.streamDecryptClr aesNiPclmulV.impl.callees .sse)
  stack := 2608
  verified := VG.Proof.AesGcm.Flag.streamDecrypt_keyed
    (Flag.streamDecrypt_of_base (streamDecryptClrB_framed .sse aesNiPclmulV.impl aesNiPclmulV.impl.blkB))
  spSafe := streamDecryptClr_spSafe .sse aesNiPclmulV.impl aesNiPclmulV.impl.blkB

/-- What the clearing of only the general-purpose registers needs of the code
of `vg_aes_gcm_stream_{en,de}crypt_prepared_aesni_pclmul`, checked by the
emitter: no function called indirectly, in it and in its callees, and the
vector registers agreeing in two runs along the same path
(`VecLock.step`). -/
def StreamChk (c : Prog isa) (b : Prog isa) : Prop :=
  UpperLock.inames aesNiPclmulV.impl.callees.ctr.code = [] ∧ UpperLock.inames aesNiPclmulV.impl.callees.gh.code = [] ∧
    UpperLock.inames b = [] ∧ UpperLock.inames c = [] ∧ VecLock.step .sse c (true, true) = (true, true)

instance (c b : Prog isa) : Decidable (StreamChk c b) := by unfold StreamChk; infer_instance

open VG.X86_64.Scrub StackLock in
/-- `vg_aes_gcm_stream_encrypt_prepared_aesni_pclmul`, followed by the clearing
of the scratch registers only (`withScrubResCR`), no stack and no vector
register: it leaves the same stack in two runs (`streamEncryptW_resOk`), and
the vector registers it leaves agree (`VecLock.regsOk_of_vec`). `streamEncryptWPlainA`
if the emitter's check (`StreamChk`) fails. -/
def streamEncryptWAesniPclmul : Registration Spec.Gcm.streamEncryptPreparedApi X86_64.target :=
  if h : StreamChk streamEncryptWPlainA.code aesNiPclmulV.impl.blkB.enc.code then
    RScrub.withScrubResCR streamEncryptWPlainA (streamEncryptPreparedOut _) [] [2608]
      (streamEncryptW_resOk aesNiPclmulV.impl (aesNiPclmulV.impl.gh.free.get rfl) (aesNiPclmulV.impl.ctr.free.get rfl)
        blkB_aesniPclmul_leaves ⟨aesNiPclmulV.impl.ctr.nosp, h.1⟩ ⟨aesNiPclmulV.impl.gh.nosp, h.2.1⟩ h.2.2.1)
      [] scratchRegs (VecLock.regsOk_of_vec streamEncryptWPlainA.verified.2.1 h.2.2.2.1 h.2.2.2.2)
  else streamEncryptWPlainA.registration

open VG.X86_64.Scrub StackLock in
/-- `streamEncryptWAesniPclmul` for `vg_aes_gcm_stream_decrypt_prepared_aesni_pclmul`. -/
def streamDecryptWAesniPclmul : Registration Spec.Gcm.streamDecryptPreparedApi X86_64.target :=
  if h : StreamChk streamDecryptWPlainA.code aesNiPclmulV.impl.blkB.dec.code then
    RScrub.withScrubResCR streamDecryptWPlainA (streamDecryptPreparedOut _) [] [2608]
      (streamDecryptW_resOk aesNiPclmulV.impl (aesNiPclmulV.impl.gh.free.get rfl) (aesNiPclmulV.impl.ctr.free.get rfl)
        blkBD_aesniPclmul_leaves ⟨aesNiPclmulV.impl.ctr.nosp, h.1⟩ ⟨aesNiPclmulV.impl.gh.nosp, h.2.1⟩ h.2.2.1)
      [] scratchRegs (VecLock.regsOk_of_vec streamDecryptWPlainA.verified.2.1 h.2.2.2.1 h.2.2.2.2)
  else streamDecryptWPlainA.registration


/-! ## Whole-blocks functions that zero their loops' working space before they return

`BlkFn.wipeW z add k B` runs `B`'s code and then `wipeWin z add k`, which
zeroes `wbytes z * k` bytes of the stack argument `scratch` from
`winOff add` (`scratch + add` rounded down to 64 bytes) with stores of
`ymm0`, or of `zmm0` if `z`. Where those cover the loops' working space
(`winCov_aligned`, `winCov_base`), whatever the loops left there, `B.wipeW`
leaves zeros, and elsewhere in `scratch` what `B`'s calls and slots leave
(`Blocks.ScrW`): a function of its arguments (`BlkFn.wipeW_leaves`). Its code
that never writes `rsp` keeps the stack pointer and the stack argument
(`blk_mid`), and the stores touch only `scratch` (`wipeW_frame`), which holds
none of what the contract reads. -/

section Wipe
open Gcm.X86_64.Stitch (CtxMode)
open VG.Impl.AesGcm.X86_64 (wbytes zeroAt zeroWs at_)
open VG.X86_64.Scrub (writeW_zero256 off_lt ite_t ite_f)

/-- The trace of `zeroWs z k` from `r11 = p`. -/
def zeroWsTr (z : Bool) (p : Addr) : Nat → List Leak
  | 0 => []
  | k + 1 => .addr (p + BitVec.ofNat 64 (wbytes z * k)) :: zeroWsTr z p k

theorem ea_at (u : State) (r : Reg) (n : Nat) : u.ea (at_ r n) = u.gpr r + BitVec.ofNat 64 n := by
  simp [at_, State.ea, BitVec.ofInt_natCast]

theorem writeW_zero512 (m : Mem) (a x : Addr) :
    m.writeW a (0 : BitVec 512) x = if (x - a).toNat < 64 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

theorem wbytes_le (z : Bool) : wbytes z ≤ 64 := by cases z <;> decide

/-- One store of `zeroAt z`, within a region it may write, from `ymm0` and
`zmm0` zero. -/
theorem zeroAt_exec (z : Bool) (u : State) (d : Nat)
    (hin : InRegions u.wr (u.gpr .r11 + BitVec.ofNat 64 d) (wbytes z))
    (hy : u.ymm .xmm0 = 0) (hh : u.zmmHi .xmm0 = 0) :
    ∃ m₁ : Mem, isa.exec (zeroAt z d) u = some { u with mem := m₁ } ∧
      addrs (zeroAt z d) u = [u.gpr .r11 + BitVec.ofNat 64 d] ∧
      ∀ x, m₁ x = if (x - (u.gpr .r11 + BitVec.ofNat 64 d)).toNat < wbytes z then 0 else u.mem x := by
  cases z
  · refine ⟨_, ?_, ?_, fun x => writeW_zero256 u.mem _ x⟩
    · simp only [zeroAt, wbytes] at hin ⊢
      simp only [reduceExec, ea_at, State.store256, hin, hy, ↓reduceIte]
    · simp [zeroAt, addrs, ea_at]
  · have hz : u.zmm .xmm0 = 0 := by rw [State.zmm, hy, hh]; exact BitVec.zero_append_zero
    refine ⟨_, ?_, ?_, fun x => writeW_zero512 u.mem _ x⟩
    · simp only [zeroAt, wbytes] at hin ⊢
      simp only [reduceExec, ea_at, State.store512, hin, hz, ↓reduceIte]
    · simp [zeroAt, addrs, ea_at]

/-- `zeroWs z k` zeroes the `wbytes z * k` bytes at `r11`, within a region it
may write. -/
theorem zeroWs_run (z : Bool) {p : Addr} {b c : Nat} (hb : b < 2 ^ 64) : ∀ (k : Nat) (u : State),
    (⟨p, b⟩ : Region) ∈ u.wr → u.gpr .r11 = p + BitVec.ofNat 64 c → u.ymm .xmm0 = 0 → u.zmmHi .xmm0 = 0 →
    c + wbytes z * k ≤ b →
    ∃ m', execBlock isa (zeroWs z k) u = some ({ u with mem := m' }, zeroWsTr z (u.gpr .r11) k) ∧
      ∀ x, m' x = if (x - u.gpr .r11).toNat < wbytes z * k then 0 else u.mem x
  | 0, u, _, _, _, _, _ => ⟨u.mem, rfl, fun x => by simp⟩
  | k + 1, u, hR, h11, hy, hh, hk => by
    obtain hk' : c + wbytes z * k + wbytes z ≤ b := by rw [Nat.add_assoc, ← Nat.mul_succ]; exact hk
    have hin : InRegions u.wr (u.gpr .r11 + BitVec.ofNat 64 (wbytes z * k)) (wbytes z) := by
      refine ⟨_, hR, ?_⟩
      rw [h11, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains_base _ (by omega) (by omega)
    obtain ⟨m₁, ex, ea, hm₁⟩ := zeroAt_exec z u (wbytes z * k) hin hy hh
    obtain ⟨m', he, hm⟩ := zeroWs_run z hb k { u with mem := m₁ } hR h11 hy hh (by omega)
    refine ⟨m', ?_, fun x => ?_⟩
    · show execBlock isa (zeroAt z (wbytes z * k) :: zeroWs z k) u = _
      rw [execBlock, ex]
      dsimp only
      rw [he, ea]
      rfl
    · rw [hm x]
      show (if (x - u.gpr .r11).toNat < wbytes z * k then 0 else m₁ x) = _
      rw [hm₁ x, Nat.mul_succ]
      simp only [off_lt _ _ _ _ (show wbytes z * k + wbytes z < 2 ^ 64 by omega)]
      generalize (x - u.gpr .r11).toNat = d
      by_cases h1 : d < wbytes z * k
      · rw [ite_t h1, ite_t (by omega)]
      · rw [ite_f h1]
        by_cases h2 : d < wbytes z * k + wbytes z
        · rw [ite_t ⟨by omega, by omega⟩, ite_t h2]
        · rw [ite_f (by omega), ite_f h2]

/-- Code that never writes `rsp`, with calls one deep, run from the entry of
a whole-blocks function: the stack pointer, the permissions and the stack
argument kept. -/
theorem blk_mid {M : CtxMode} {c : Prog isa} (hc : NoSp c) (hd : c.depth = 1) {s v : State} {t : List Leak}
    (hp : Blocks.BP M s) (e : Exec isa c s t v) :
    v.gpr .rsp = s.gpr .rsp ∧ v.rd = s.rd ∧ v.wr = s.wr ∧
      v.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s 0 := by
  obtain ⟨hrd, hwr⟩ := Exec.rdwr e
  have hf := Exec.frameSp e hc (by rw [hd]; decide)
  rw [hd] at hf
  refine ⟨Exec.gpr hc e, hrd, hwr, hf.readW (r := Blocks.aR s) (Region.contains_self _ _) (fun r hr => ?_) (by decide)⟩
  rcases List.mem_append.mp hr with hr | hr
  · rw [hp.wr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.c_a.symm
    · exact hp.y_a.symm
    · exact hp.d_a.symm
    · exact hp.s_a.symm
  · simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_below _ (by decide)

theorem encPost_wipe {M : CtxMode} {s s₁ u : State} (hp : Blocks.BP M s) (hf : Frame [Blocks.sR s] s₁.mem u.mem)
    (h : Proof.AesGcm.encryptBlocksX86_64.post s s₁) : Proof.AesGcm.encryptBlocksX86_64.post s u := by
  simp only [Proof.AesGcm.encryptBlocksX86_64] at h ⊢
  rw [blocksAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [Nat.mul_comm]; exact hp.d_s)
      (by have h := hp.w_d; dsimp only [Blocks.n, Blocks.D] at h; omega),
    blockAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.c_s),
    blockAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.y_s)]
  exact h

theorem decPost_wipe {M : CtxMode} {s s₁ u : State} (hp : Blocks.BP M s) (hf : Frame [Blocks.sR s] s₁.mem u.mem)
    (h : Proof.AesGcm.decryptBlocksX86_64.post s s₁) : Proof.AesGcm.decryptBlocksX86_64.post s u := by
  simp only [Proof.AesGcm.decryptBlocksX86_64] at h ⊢
  rw [blocksAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [Nat.mul_comm]; exact hp.d_s)
      (by have h := hp.w_d; dsimp only [Blocks.n, Blocks.D] at h; omega),
    blockAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.c_s),
    blockAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.y_s)]
  exact h

/-! ### Zeroing only the loops' working space -/

open VG.Impl.AesGcm.X86_64 (wipeWin Fn.wipeW imm)

/-- Where `wipeWin _ add` starts zeroing, from `scratch = p`: `p + add`
rounded down to 64 bytes. -/
def winOff (add : Nat) (p : Addr) : Nat := (p.toNat + add) / 64 * 64 - p.toNat

theorem alignW_eq {add : Nat} (h1 : 63 ≤ add) (h2 : add ≤ 127) (p : Addr) (hp : p.toNat + 2112 ≤ 2 ^ 64) :
    (p + BitVec.ofNat 64 add) &&& (-64) = p + BitVec.ofNat 64 (winOff add p) := by
  apply BitVec.eq_of_toNat_eq
  rw [AlignedScratch.mask_nat]
  simp only [winOff, BitVec.toNat_add, BitVec.toNat_ofNat]
  have hm := Nat.mod_lt (p.toNat + add) (by decide : 0 < 64)
  have hd := Nat.mod_add_div (p.toNat + add) 64
  rw [Nat.mod_eq_of_lt (a := add) (by omega), Nat.mod_eq_of_lt (a := p.toNat + add) (by omega),
    Nat.mod_eq_of_lt (a := (p.toNat + add) / 64 * 64 - p.toNat) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem winOff_le {add : Nat} (h1 : 63 ≤ add) (p : Addr) : winOff add p ≤ add ∧ add ≤ winOff add p + 63 := by
  have hm := Nat.mod_lt (p.toNat + add) (by decide : 0 < 64)
  have hd := Nat.mod_add_div (p.toNat + add) 64
  simp only [winOff]; omega

/-- The setup of `wipeWin`: `r11` at `[rsp + 8] + add`, rounded down to 64
bytes; nothing else changed but the flags. -/
theorem winSetup_exec (u : State) (add : Nat) (ha : add < 2 ^ 31)
    (hin : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 8) 8) :
    ∃ u₁, execBlock isa [.mov .r11 (.mem (at_ .rsp 8)), .alu .add .r11 (imm add), .alu .and .r11 (.imm (-64)),
        .vop (.vbin .vpxor .l128 .xmm0 .xmm0 .xmm0)] u = some (u₁, [.addr (u.gpr .rsp + BitVec.ofNat 64 8)]) ∧
      (∀ r, u₁.gpr r = if r = .r11 then
        (u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64 + BitVec.ofNat 64 add) &&& (-64) else u.gpr r) ∧
      u₁.mem = u.mem ∧ u₁.rd = u.rd ∧ u₁.wr = u.wr ∧ u₁.mxcsr = u.mxcsr ∧ u₁.ymm .xmm0 = 0 ∧
      u₁.zmmHi .xmm0 = 0 := by
  have e1 : (BitVec.ofNat 32 add).signExtend 64 = BitVec.ofNat 64 add := imm_eq ha
  have e2 : (-64 : BitVec 32).signExtend 64 = -64 := by decide
  let S := u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64
  let i₁ := (BitVec.ofNat 32 add).signExtend 64
  let a₁ := S + i₁
  let u₂ := (arithFlags (u.setReg .r11 S) a₁ (decide (2 ^ 64 ≤ S.toNat + i₁.toNat)) (addOverflow S i₁ a₁)).setReg .r11 a₁
  let a₂ := a₁ &&& (-64 : BitVec 32).signExtend 64
  let u₃ := (arithFlags u₂ a₂ false false).setReg .r11 a₂
  let u₄ := u₃.setV .l128 .xmm0 (VBinOp.vpxor.sse.eval (u₃.lane .xmm0 0) (u₃.lane .xmm0 0))
    (VBinOp.vpxor.sse.eval (u₃.lane .xmm0 1) (u₃.lane .xmm0 1))
  refine ⟨u₄, ?_, fun r => ?_, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [execBlock, isa, reduceExec, readSrc, State.load64, ea_at, hin, ↓reduceIte, Option.map_some, VOp.exec,
      addrs, srcAddrs, List.map_nil, List.append_nil, List.map_cons, execAlu, imm, Option.bind_some]
    rfl
  · simp only [u₄, u₃, u₂, a₂, a₁, i₁, RegUpd.gpr_setV, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, e1, e2]
    split <;> rfl
  · simp only [State.ymm, u₄, RegUpd.ymmHi_setV_128, RegUpd.xmm_setV, ↓reduceIte, VBinOp.sse, XBinOp.eval,
      BitVec.xor_self]
    rfl
  · simp only [u₄, State.setV, ↓reduceIte]

/-- `wipeWin z add k` zeroes the `wbytes z * k` bytes from `winOff add` of
the scratch at `[rsp + 8]`, a region it may write, and changes no register
`B`'s caller reads but `r11`. -/
theorem wipeWin_run (z : Bool) {add k : Nat} (h1 : 63 ≤ add) (h2 : add ≤ 127) (hk : add + wbytes z * k ≤ 2112)
    (u : State) (hin : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 8) 8)
    (hR : (⟨u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64, 2112⟩ : Region) ∈ u.wr)
    (hS : (u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64).toNat + 2112 ≤ 2 ^ 64) :
    ∃ u', execBlock isa (wipeWin z add k) u =
        some (u', .addr (u.gpr .rsp + BitVec.ofNat 64 8) :: zeroWsTr z
          (u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64 +
            BitVec.ofNat 64 (winOff add (u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64))) k) ∧
      (∀ x, u'.mem x =
        if winOff add (u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64) ≤
            (x - u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64).toNat ∧
          (x - u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64).toNat <
            winOff add (u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64) + wbytes z * k then 0 else u.mem x) ∧
      (∀ r, r ≠ .r11 → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.mxcsr = u.mxcsr := by
  generalize hSd : u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64 = S at hR hS ⊢
  obtain ⟨u₁, e₁, g₁, m₁, rd₁, wr₁, mx₁, y₁, h₁⟩ := winSetup_exec u add (by omega) hin
  rw [hSd] at g₁
  obtain ho := winOff_le h1 S
  obtain h11 : u₁.gpr .r11 = S + BitVec.ofNat 64 (winOff add S) := by
    rw [g₁, ite_t rfl]; exact alignW_eq h1 h2 S hS
  obtain ⟨m', he, hm⟩ := zeroWs_run z (p := S) (b := 2112) (c := winOff add S) (by decide) k u₁
    (by rw [wr₁]; exact hR) h11 y₁ h₁ (by omega)
  let v : State := { ({ u₁ with mem := m' } : State) with ymmHi := fun _ => 0, zmmHi := fun _ => 0 }
  let w : State := if z then
      { v with
        ymmH := (fun r => if r ∈ VG.Impl.Scrub.X86_64.hregs then 0 else v.ymmH r)
        zmmHiH := (fun r => if r ∈ VG.Impl.Scrub.X86_64.hregs then 0 else v.zmmHiH r) }
    else v
  have ew : execBlock isa (if z then VG.Impl.Scrub.X86_64.hregs.map VG.Impl.Scrub.X86_64.zeroH else []) v =
      some (w, []) := by
    cases z
    · rfl
    · exact Scrub.execBlock_zeroH _ _
  have hw : w.mem = m' ∧ w.gpr = u₁.gpr ∧ w.rd = u₁.rd ∧ w.wr = u₁.wr ∧ w.mxcsr = u₁.mxcsr := by
    cases z <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨w, ?_, fun x => ?_, fun r hr => ?_, hw.2.2.1.trans rd₁, hw.2.2.2.1.trans wr₁, hw.2.2.2.2.trans mx₁⟩
  · have ev : execBlock isa [.vop .vzeroupper] { u₁ with mem := m' } = some (v, []) := by
      simp only [execBlock, isa, reduceExec, VOp.exec, addrs, Option.map_some, List.map_nil, List.append_nil]
      rfl
    rw [VG.Impl.AesGcm.X86_64.wipeWin, execBlock_append, execBlock_append, execBlock_append, e₁]
    simp only [Option.bind_some, he, ev, ew, Option.map_some]
    simp only [h11, List.cons_append, List.nil_append, List.append_nil]
  · rw [hw.1, hm x, h11, m₁]
    simp only [off_lt _ _ _ _ (show winOff add S + wbytes z * k < 2 ^ 64 by omega)]
  · rw [hw.2.1, g₁, ite_f hr]

section WipeW
variable (z : Bool) {add k : Nat} (h1 : 63 ≤ add) (h2 : add ≤ 127) (hk : add + wbytes z * k ≤ 2112)
include h1 h2 hk

/-- `wipeWin` after code that kept what `blk_mid` says. -/
theorem wipeW_after {M : CtxMode} {s v : State} (hp : Blocks.BP M s)
    (h : v.gpr .rsp = s.gpr .rsp ∧ v.rd = s.rd ∧ v.wr = s.wr ∧
      v.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s 0) :
    ∃ u, execBlock isa (wipeWin z add k) v = some (u, .addr (s.gpr .rsp + BitVec.ofNat 64 8) ::
        zeroWsTr z (stackArg s 0 + BitVec.ofNat 64 (winOff add (stackArg s 0))) k) ∧
      (∀ x, u.mem x = if winOff add (stackArg s 0) ≤ (x - stackArg s 0).toNat ∧
        (x - stackArg s 0).toNat < winOff add (stackArg s 0) + wbytes z * k then 0 else v.mem x) ∧
      (∀ r, r ≠ .r11 → u.gpr r = v.gpr r) ∧ u.rd = v.rd ∧ u.wr = v.wr ∧ u.mxcsr = v.mxcsr := by
  obtain ⟨hsp, hrd, hwr, hS⟩ := h
  have := wipeWin_run z h1 h2 hk v (by rw [hsp, hrd, hwr]; exact Blocks.a_in hp)
    (by rw [hsp, hS, hwr, hp.wr]; simp [Blocks.wR]) (by rw [hsp, hS]; exact hp.w_s)
  rwa [hsp, hS] at this

omit h1 h2 in
theorem wipeW_frame {S : Addr} {m m' : Mem}
    (h : ∀ x, m' x = if winOff add S ≤ (x - S).toNat ∧ (x - S).toNat < winOff add S + wbytes z * k then 0 else m x)
    (ho : winOff add S ≤ add) : Frame [⟨S, 2112⟩] m m' := fun x hx => by
  rw [h x, ite_f]
  intro hl
  exact hx _ (List.mem_singleton_self _) (show (x - S).toNat + 1 ≤ 2112 by omega)

theorem wipeW_ok {M : CtxMode} {c : Prog isa} (hc : NoSp c) (hd : c.depth = 1) {post : State → State → Prop}
    (hpost : ∀ s s₁ u, Blocks.BP M s → Frame [Blocks.sR s] s₁.mem u.mem → post s s₁ → post s u)
    (h : ∀ s, Proof.AesGcm.blocksPreM M s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ post s s') :
    ∀ s, Proof.AesGcm.blocksPreM M s →
      ∃ t s', Exec isa (.seq c (.block (wipeWin z add k))) s t s' ∧ abiPreserved s s' ∧ post s s' := by
  intro s hs
  obtain hp := Blocks.BP.ofM hs
  obtain ⟨t, v, e, ha, hq⟩ := h s hs
  obtain ⟨u, ew, hm, hg, -, -, hmx⟩ := wipeW_after z h1 h2 hk hp (blk_mid hc hd hp e)
  obtain hf := wipeW_frame z hk hm (winOff_le h1 _).1
  refine ⟨_, u, .seq e (.block ew), ⟨fun r hr => ?_, ?_, ?_⟩, hpost s v u hp hf hq⟩
  · rw [hg r (fun h => by subst h; exact absurd hr (by decide))]; exact ha.1 r hr
  · rw [hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.r_s) (by decide)]
    exact ha.2.1
  · rw [hmx]; exact ha.2.2

theorem wipeW_ct {M : CtxMode} {c : Prog isa} (hc : NoSp c) (hd : c.depth = 1) {pre : State → Prop}
    (hpre : ∀ s, pre s → Proof.AesGcm.blocksPreM M s) (h : ConstantTime isa pre Proof.AesGcm.blocksPub c) :
    ConstantTime isa pre Proof.AesGcm.blocksPub (.seq c (.block (wipeWin z add k))) := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁' h₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
      cases b₁ with
      | block w₁ =>
        cases b₂ with
        | block w₂ =>
          obtain p₁ := Blocks.BP.ofM (hpre _ h₁')
          obtain p₂ := Blocks.BP.ofM (hpre _ h₂')
          obtain ⟨_, ew₁, -⟩ := wipeW_after z h1 h2 hk p₁ (blk_mid hc hd p₁ a₁)
          obtain ⟨_, ew₂, -⟩ := wipeW_after z h1 h2 hk p₂ (blk_mid hc hd p₂ a₂)
          rw [ew₁] at w₁
          rw [ew₂] at w₂
          obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj w₁)
          obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj w₂)
          rw [h s₁ s₂ _ _ _ _ h₁' h₂' hp a₁ a₂, hp.2.2.2.2.2.2.1, show stackArg s₁ 0 = stackArg s₂ 0 from hp.2.2.2.2.2.2.2]

end WipeW

theorem wipeWin_nosp (z : Bool) (add k : Nat) : ∀ i ∈ wipeWin z add k, Taint.clobbers i .rsp = false := by
  intro i hi
  simp only [VG.Impl.AesGcm.X86_64.wipeWin, List.mem_append] at hi
  rcases hi with ((hi | hi) | hi) | hi
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> rfl
  · induction k with
    | zero => exact absurd hi (by simp [zeroWs])
    | succ k ih =>
      simp only [zeroWs, List.mem_cons] at hi
      rcases hi with rfl | hi
      · cases z <;> rfl
      · exact ih hi
  · simp only [List.mem_singleton] at hi; subst hi; rfl
  · cases z
    · exact absurd hi (by simp)
    · simp only [↓reduceIte, List.mem_map] at hi
      obtain ⟨h, -, rfl⟩ := hi
      cases h <;> rfl

/-- `B`, its functions renamed (`Fn.wipeW`) and zeroing their loops' working
space before they return (`wipeWin z add k`). -/
def BlkFn.wipeW (z : Bool) (add k : Nat) (h1 : 63 ≤ add) (h2 : add ≤ 127) (hk : add + wbytes z * k ≤ 2112)
    (hmx : (Code.block (wipeWin z add k) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsp : (Code.block (wipeWin z add k) : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true)
    {M : CtxMode} (B : BlkFn M) : BlkFn M where
  enc := B.enc.wipeW z add k
  dec := B.dec.wipeW z add k
  encOk := wipeW_ok z h1 h2 hk B.encNosp B.encDepth (fun _ _ _ hp hf h => encPost_wipe hp hf h) B.encOk
  decOk := wipeW_ok z h1 h2 hk B.decNosp B.decDepth (fun _ _ _ hp hf h => decPost_wipe hp hf h) B.decOk
  encCt := wipeW_ct z h1 h2 hk B.encNosp B.encDepth (fun _ h => h) B.encCt
  decCt := wipeW_ct z h1 h2 hk B.decNosp B.decDepth (fun _ h => h) B.decCt
  encNosp := fun i hi => by
    rcases List.mem_append.mp hi with hi | hi
    · exact B.encNosp i hi
    · exact wipeWin_nosp z add k i hi
  decNosp := fun i hi => by
    rcases List.mem_append.mp hi with hi | hi
    · exact B.decNosp i hi
    · exact wipeWin_nosp z add k i hi
  encDepth := by simp only [Fn.wipeW, Code.depth, B.encDepth]; rfl
  decDepth := by simp only [Fn.wipeW, Code.depth, B.decDepth]; rfl
  encMx := by simp only [Fn.wipeW, Code.allInstrs, B.encMx, Bool.true_and]; exact hmx
  decMx := by simp only [Fn.wipeW, Code.allInstrs, B.decMx, Bool.true_and]; exact hmx
  encSp := by simp only [Fn.wipeW, Code.all, B.encSp, Bool.true_and]; exact hsp
  decSp := by simp only [Fn.wipeW, Code.all, B.decSp, Bool.true_and]; exact hsp
  encXd := by simp only [Fn.wipeW, Code.x86_64Depth, Nat.max_le]; exact ⟨B.encXd, Nat.zero_le _⟩
  decXd := by simp only [Fn.wipeW, Code.x86_64Depth, Nat.max_le]; exact ⟨B.decXd, Nat.zero_le _⟩


/-! ### Zeroing the working space of the callees, with 16-byte stores -/

open VG.Impl.AesGcm.X86_64 (wipeX Fn.wipeS) in
/-- The load of `scratch` from the stack argument, then `wipeX .r11 64 n`:
the `n` bytes from byte 64 of `scratch`, a region it may write, zeroed; no
register changed but `r11` and `xmm0`. -/
theorem wipeS_run {n : Nat} (hn : 64 + n ≤ 2112) (h16 : n % 16 = 0 ∨ 16 ≤ n) (u : State)
    (hin : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 8) 8)
    (hR : (⟨u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64, 2112⟩ : Region) ∈ u.wr) :
    ∃ u', execBlock isa (.mov .r11 (.mem (at_ .rsp 8)) :: wipeX .r11 64 n) u =
        some (u', .addr (u.gpr .rsp + BitVec.ofNat 64 8) ::
          wipeXTr (u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64) 64 n) ∧
      (∀ x, u'.mem x = if 64 ≤ (x - u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64).toNat ∧
        (x - u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64).toNat < 64 + n then 0 else u.mem x) ∧
      (∀ r, r ≠ .r11 → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.mxcsr = u.mxcsr := by
  generalize hSd : u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64 = S at hR ⊢
  let u₁ := u.setReg .r11 S
  have e₁ : isa.exec (.mov .r11 (.mem (at_ .rsp 8))) u = some u₁ ∧
      addrs (.mov .r11 (.mem (at_ .rsp 8))) u = [u.gpr .rsp + BitVec.ofNat 64 8] := by
    refine ⟨?_, ?_⟩
    · simp only [reduceExec, readSrc, State.load64, ea_at, hin, ↓reduceIte, Option.map_some, hSd, u₁]
    · simp [addrs, srcAddrs, ea_at]
  obtain ⟨m', he, hm⟩ := wipeX_run (r := .r11) (o := 64) (n := n) (p := S) (b := 2112) (by decide) u₁ (covers_of_mem hR)
    (RegUpd.gpr_setReg_self ..) hn h16
  refine ⟨{ u₁.setXmm .xmm0 0 with mem := m' }, ?_, fun x => hm x, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [execBlock, e₁.1]
    dsimp only
    rw [he, e₁.2]
    rfl
  · show (u₁.setXmm .xmm0 0).gpr r = u.gpr r
    simp [u₁, State.setXmm, RegUpd.gpr_setReg, hr]

open VG.Impl.AesGcm.X86_64 (wipeX Fn.wipeS)

section WipeS
variable {n : Nat} (hn : 64 + n ≤ 2112) (h16 : n % 16 = 0 ∨ 16 ≤ n)
include hn h16

/-- `wipeS_run` after code that kept what `blk_mid` says. -/
theorem wipeS_after {M : CtxMode} {s v : State} (hp : Blocks.BP M s)
    (h : v.gpr .rsp = s.gpr .rsp ∧ v.rd = s.rd ∧ v.wr = s.wr ∧
      v.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s 0) :
    ∃ u, execBlock isa (.mov .r11 (.mem (at_ .rsp 8)) :: wipeX .r11 64 n) v =
        some (u, .addr (s.gpr .rsp + BitVec.ofNat 64 8) :: wipeXTr (stackArg s 0) 64 n) ∧
      (∀ x, u.mem x = if 64 ≤ (x - stackArg s 0).toNat ∧ (x - stackArg s 0).toNat < 64 + n then 0 else v.mem x) ∧
      (∀ r, r ≠ .r11 → u.gpr r = v.gpr r) ∧ u.rd = v.rd ∧ u.wr = v.wr ∧ u.mxcsr = v.mxcsr := by
  obtain ⟨hsp, hrd, hwr, hS⟩ := h
  have := wipeS_run hn h16 v (by rw [hsp, hrd, hwr]; exact Blocks.a_in hp)
    (by rw [hsp, hS, hwr, hp.wr]; simp [Blocks.wR])
  rwa [hsp, hS] at this

omit h16 in
theorem wipeS_frame {S : Addr} {m m' : Mem}
    (h : ∀ x, m' x = if 64 ≤ (x - S).toNat ∧ (x - S).toNat < 64 + n then 0 else m x) :
    Frame [⟨S, 2112⟩] m m' := fun x hx => by
  rw [h x, ite_f]
  intro hl
  exact hx _ (List.mem_singleton_self _) (show (x - S).toNat + 1 ≤ 2112 by omega)

theorem wipeS_ok {M : CtxMode} {c : Prog isa} (hc : NoSp c) (hd : c.depth = 1) {post : State → State → Prop}
    (hpost : ∀ s s₁ u, Blocks.BP M s → Frame [Blocks.sR s] s₁.mem u.mem → post s s₁ → post s u)
    (h : ∀ s, Proof.AesGcm.blocksPreM M s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ post s s') :
    ∀ s, Proof.AesGcm.blocksPreM M s →
      ∃ t s', Exec isa (.seq c (.block (.mov .r11 (.mem (at_ .rsp 8)) :: wipeX .r11 64 n))) s t s' ∧
        abiPreserved s s' ∧ post s s' := by
  intro s hs
  obtain hp := Blocks.BP.ofM hs
  obtain ⟨t, v, e, ha, hq⟩ := h s hs
  obtain ⟨u, ew, hm, hg, -, -, hmx⟩ := wipeS_after hn h16 hp (blk_mid hc hd hp e)
  obtain hf := wipeS_frame hn hm
  refine ⟨_, u, .seq e (.block ew), ⟨fun r hr => ?_, ?_, ?_⟩, hpost s v u hp hf hq⟩
  · rw [hg r (fun h => by subst h; exact absurd hr (by decide))]; exact ha.1 r hr
  · rw [hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.r_s) (by decide)]
    exact ha.2.1
  · rw [hmx]; exact ha.2.2

theorem wipeS_ct {M : CtxMode} {c : Prog isa} (hc : NoSp c) (hd : c.depth = 1) {pre : State → Prop}
    (hpre : ∀ s, pre s → Proof.AesGcm.blocksPreM M s) (h : ConstantTime isa pre Proof.AesGcm.blocksPub c) :
    ConstantTime isa pre Proof.AesGcm.blocksPub (.seq c (.block (.mov .r11 (.mem (at_ .rsp 8)) :: wipeX .r11 64 n))) := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁' h₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
      cases b₁ with
      | block w₁ =>
        cases b₂ with
        | block w₂ =>
          obtain p₁ := Blocks.BP.ofM (hpre _ h₁')
          obtain p₂ := Blocks.BP.ofM (hpre _ h₂')
          obtain ⟨_, ew₁, -⟩ := wipeS_after hn h16 p₁ (blk_mid hc hd p₁ a₁)
          obtain ⟨_, ew₂, -⟩ := wipeS_after hn h16 p₂ (blk_mid hc hd p₂ a₂)
          rw [ew₁] at w₁
          rw [ew₂] at w₂
          obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj w₁)
          obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj w₂)
          rw [h s₁ s₂ _ _ _ _ h₁' h₂' hp a₁ a₂, hp.2.2.2.2.2.2.1, show stackArg s₁ 0 = stackArg s₂ 0 from hp.2.2.2.2.2.2.2]

end WipeS

theorem wipeS_nosp (n : Nat) : ∀ i ∈ (.mov .r11 (.mem (at_ .rsp 8)) :: wipeX .r11 64 n : List Instr),
    Taint.clobbers i .rsp = false := by
  intro i hi
  rcases List.mem_cons.mp hi with rfl | hi
  · rfl
  · exact X86_64.wipeX_nosp .r11 64 n i hi

theorem wipeS_mx (n : Nat) :
    (Code.block (.mov .r11 (.mem (at_ .rsp 8)) :: wipeX .r11 64 n) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  have h := X86_64.wipeX_mx .r11 64 n
  rw [Code.allInstrs_eq] at h ⊢
  simp only [instrs, List.all_cons] at h ⊢
  rw [h]; rfl

theorem wipeS_sp (n : Nat) :
    (.mov .r11 (.mem (at_ .rsp 8)) :: wipeX .r11 64 n : List Instr).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [List.all_cons, X86_64.wipeX_sp .r11 64 n]; rfl

/-- `B`, its functions renamed (`Fn.wipeS`) and zeroing the `n` bytes of the
working space of their callees, from byte 64 of `scratch`, before they
return. -/
def BlkFn.wipeS (n : Nat) (hn : 64 + n ≤ 2112) (h16 : n % 16 = 0 ∨ 16 ≤ n) {M : CtxMode} (B : BlkFn M) : BlkFn M where
  enc := B.enc.wipeS n
  dec := B.dec.wipeS n
  encOk := wipeS_ok hn h16 B.encNosp B.encDepth (fun _ _ _ hp hf h => encPost_wipe hp hf h) B.encOk
  decOk := wipeS_ok hn h16 B.decNosp B.decDepth (fun _ _ _ hp hf h => decPost_wipe hp hf h) B.decOk
  encCt := wipeS_ct hn h16 B.encNosp B.encDepth (fun _ h => h) B.encCt
  decCt := wipeS_ct hn h16 B.decNosp B.decDepth (fun _ h => h) B.decCt
  encNosp := fun i hi => by
    rcases List.mem_append.mp hi with hi | hi
    · exact B.encNosp i hi
    · exact wipeS_nosp n i hi
  decNosp := fun i hi => by
    rcases List.mem_append.mp hi with hi | hi
    · exact B.decNosp i hi
    · exact wipeS_nosp n i hi
  encDepth := by simp only [Fn.wipeS, Code.depth, B.encDepth]; rfl
  decDepth := by simp only [Fn.wipeS, Code.depth, B.decDepth]; rfl
  encMx := by simp only [Fn.wipeS, Code.allInstrs, B.encMx, Bool.true_and]; exact wipeS_mx n
  decMx := by simp only [Fn.wipeS, Code.allInstrs, B.decMx, Bool.true_and]; exact wipeS_mx n
  encSp := by simp only [Fn.wipeS, Code.all, B.encSp, Bool.true_and]; exact wipeS_sp n
  decSp := by simp only [Fn.wipeS, Code.all, B.decSp, Bool.true_and]; exact wipeS_sp n
  encXd := by simp only [Fn.wipeS, Code.x86_64Depth, Nat.max_le]; exact ⟨B.encXd, Nat.zero_le _⟩
  decXd := by simp only [Fn.wipeS, Code.x86_64Depth, Nat.max_le]; exact ⟨B.decXd, Nat.zero_le _⟩


/-- What `B.wipeS n` leaves at `x` in `scratch` at `S`: zero in the `n` bytes
from byte 64, and elsewhere the arguments kept, or what it found. -/
def leavesS (n : Nat) (rdi rsi rdx rcx r8 r9 : BitVec 64) (S x : Addr) : Option (BitVec 8) :=
  if 64 ≤ (x - S).toNat ∧ (x - S).toNat < 64 + n then some 0
  else leavesL (fun _ => 0) (fun _ _ _ => false) rdi rsi rdx rcx r8 r9 S x

/-- After code leaving `ScrW` (outside `Wn`), what `wipeS` leaves, if it zeroes
`Wn` (`hcov`). -/
theorem wipeS_leaves_of {M : CtxMode} {c : Prog isa} (hc : NoSp c) (hd : c.depth = 1) {n : Nat}
    (hn : 64 + n ≤ 2112) (h16 : n % 16 = 0 ∨ 16 ≤ n) {Wn : Nat → Bool}
    (hcov : ∀ d, Wn d = true → 64 ≤ d ∧ d < 64 + n)
    {s s' : State} {t : List Leak} (hpre : Proof.AesGcm.blocksPreM M s)
    (hW : WP isa c s fun s' => Blocks.ScrW s 0 Wn s'.mem)
    (he : Exec isa (.seq c (.block (.mov .r11 (.mem (at_ .rsp 8)) :: wipeX .r11 64 n))) s t s') :
    ∀ x, (⟨stackArg s 0, 2112⟩ : Region).Contains x 1 →
      s'.mem x = (leavesS n (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8)
        (s.gpr .r9) (stackArg s 0) x).getD (s.mem x) := by
  intro x hx
  cases he with
  | seq a b =>
    cases b with
    | block w =>
      obtain hp := Blocks.BP.ofM hpre
      obtain ⟨_, v', ea, hS⟩ := hW
      obtain ⟨_, rfl⟩ := Exec.det a ea
      obtain ⟨u, ew, hm, -⟩ := wipeS_after hn h16 hp (blk_mid hc hd hp a)
      rw [ew] at w
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj w)
      obtain ⟨d, hd, rfl⟩ : ∃ d, d < 2112 ∧ x = stackArg s 0 + BitVec.ofNat 64 d :=
        ⟨(x - stackArg s 0).toNat, hx, by
          rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]⟩
      rw [hm]
      simp only [leavesS, leavesL, Mem.sub_ofNat_toNat _ (show d < 2 ^ 64 by omega)]
      by_cases hw : 64 ≤ d ∧ d < 64 + n
      · simp only [hw, and_self, ↓reduceIte, Option.getD_some]
      · simp only [hw, ↓reduceIte]
        by_cases h48 : d < 48
        · simp only [h48, ↓reduceIte, Option.getD_some]
          rw [← kept_words hS.kept (d / 8) (by omega), ← Blocks.byte_readW64 _ _ (by omega),
            Offset.add_add_eq _ (by omega : 8 * (d / 8) + d % 8 = d)]
        · simp only [h48, ↓reduceIte, Bool.false_eq_true, Option.getD_none]
          exact hS.rest d (by omega) hd (by
            cases h' : Wn d
            · rfl
            · exact absurd (hcov d h') hw)

theorem BlkFn.wipeS_leaves (n : Nat) (hn : 64 + n ≤ 2112) (h16 : n % 16 = 0 ∨ 16 ≤ n) {M : CtxMode} (B : BlkFn M)
    {Wn : Nat → Bool} (hcov : ∀ d, Wn d = true → 64 ≤ d ∧ d < 64 + n)
    (hW : ∀ s, (Proof.AesGcm.encryptBlocksX86_64M M).pre s → WP isa B.enc.code s fun s' => Blocks.ScrW s 0 Wn s'.mem) :
    BlkLeaves (B.wipeS n hn h16) :=
  ⟨leavesS n, fun _ _ _ hpre he => wipeS_leaves_of B.encNosp B.encDepth hn h16 hcov hpre (hW _ hpre) he⟩

theorem BlkFn.wipeS_leavesD (n : Nat) (hn : 64 + n ≤ 2112) (h16 : n % 16 = 0 ∨ 16 ≤ n) {M : CtxMode} (B : BlkFn M)
    {Wn : Nat → Bool} (hcov : ∀ d, Wn d = true → 64 ≤ d ∧ d < 64 + n)
    (hW : ∀ s, (Proof.AesGcm.decryptBlocksX86_64M M).pre s → WP isa B.dec.code s fun s' => Blocks.ScrW s 0 Wn s'.mem) :
    BlkLeavesD (B.wipeS n hn h16) :=
  ⟨leavesS n, fun _ _ _ hpre he => wipeS_leaves_of B.decNosp B.decDepth hn h16 hcov hpre (hW _ hpre) he⟩

/-- `vg_aes_ctr32` through its contract with 1480 bytes, as a whole-blocks
function calls it. -/
theorem CtrW.small (ctr : VG.Proof.Aes.X86_64.Ctr32Impl) (f : VG.Proof.Aes.X86_64.Ctr32Small ctr.callee) :
    Blocks.CtrW ⟨ctr.callee.name, ctr.callee.code⟩ 1480 :=
  fun h => WP.mono (ctr_callS ctr f h) fun _ ⟨g, fr⟩ => ⟨g.saved, g.rd, g.wr, fr⟩

/-- What `B.wipeW` leaves at `x` in `scratch` at `S`: zero in the bytes
`wipeWin` zeroes (`len` from `winOff add`), and elsewhere what `leavesL`
says of loops that write only their working space. -/
def leavesW (q : Nat → Nat) (add len : Nat) (rdi rsi rdx rcx r8 r9 : BitVec 64) (S x : Addr) :
    Option (BitVec 8) :=
  if winOff add S ≤ (x - S).toNat ∧ (x - S).toNat < winOff add S + len then some 0
  else leavesL q (fun _ _ _ => false) rdi rsi rdx rcx r8 r9 S x

/-- After code leaving `ScrW` (in the working space `winW aligned`), what
`wipeWin` leaves, if it zeroes that space (`hcov`). -/
theorem wipeW_leaves_of {M : CtxMode} {c : Prog isa} (hc : NoSp c) (hd : c.depth = 1) (z : Bool) {add k : Nat}
    (h1 : 63 ≤ add) (h2 : add ≤ 127) (hk : add + wbytes z * k ≤ 2112) {aligned : Bool} (q : Nat → Nat)
    (hcov : ∀ p : Addr, ∀ d, Blocks.winW aligned p d = true →
      winOff add p ≤ d ∧ d < winOff add p + wbytes z * k)
    {s s' : State} {t : List Leak} (hpre : Proof.AesGcm.blocksPreM M s)
    (hW : WP isa c s fun s' => Blocks.ScrW s (q (Blocks.n s)) (Blocks.winW aligned (Blocks.S s)) s'.mem)
    (he : Exec isa (.seq c (.block (wipeWin z add k))) s t s') :
    ∀ x, (⟨stackArg s 0, 2112⟩ : Region).Contains x 1 →
      s'.mem x = (leavesW q add (wbytes z * k) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8)
        (s.gpr .r9) (stackArg s 0) x).getD (s.mem x) := by
  intro x hx
  cases he with
  | seq a b =>
    cases b with
    | block w =>
      obtain hp := Blocks.BP.ofM hpre
      obtain ⟨_, v', ea, hS⟩ := hW
      obtain ⟨_, rfl⟩ := Exec.det a ea
      obtain ⟨u, ew, hm, -⟩ := wipeW_after z h1 h2 hk hp (blk_mid hc hd hp a)
      rw [ew] at w
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj w)
      obtain ⟨d, hd, rfl⟩ : ∃ d, d < 2112 ∧ x = stackArg s 0 + BitVec.ofNat 64 d :=
        ⟨(x - stackArg s 0).toNat, hx, by
          rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]⟩
      rw [hm]
      simp only [leavesW, leavesL, Mem.sub_ofNat_toNat _ (show d < 2 ^ 64 by omega)]
      by_cases hw : winOff add (stackArg s 0) ≤ d ∧ d < winOff add (stackArg s 0) + wbytes z * k
      · simp only [hw, and_self, ↓reduceIte, Option.getD_some]
      · simp only [hw, ↓reduceIte]
        by_cases h48 : d < 48
        · simp only [h48, ↓reduceIte, Option.getD_some]
          rw [← kept_words hS.kept (d / 8) (by omega), ← Blocks.byte_readW64 _ _ (by omega),
            Offset.add_add_eq _ (by omega : 8 * (d / 8) + d % 8 = d)]
        · simp only [h48, ↓reduceIte, Bool.false_eq_true, Option.getD_none]
          exact hS.rest d (by omega) hd (by
            cases h' : Blocks.winW aligned (Blocks.S s) d
            · rfl
            · exact absurd (hcov _ d h') hw)

theorem BlkFn.wipeW_leaves (z : Bool) (add k : Nat) (h1 : 63 ≤ add) (h2 : add ≤ 127)
    (hk : add + wbytes z * k ≤ 2112)
    (hmx : (Code.block (wipeWin z add k) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsp : (Code.block (wipeWin z add k) : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true)
    {M : CtxMode} (B : BlkFn M) {aligned : Bool} (q : Nat → Nat)
    (hcov : ∀ p : Addr, ∀ d, Blocks.winW aligned p d = true →
      winOff add p ≤ d ∧ d < winOff add p + wbytes z * k)
    (hW : ∀ s, (Proof.AesGcm.encryptBlocksX86_64M M).pre s → WP isa B.enc.code s fun s' =>
      Blocks.ScrW s (q (Blocks.n s)) (Blocks.winW aligned (Blocks.S s)) s'.mem) :
    BlkLeaves (B.wipeW z add k h1 h2 hk hmx hsp) :=
  ⟨leavesW q add (wbytes z * k), fun _ _ _ hpre he =>
    wipeW_leaves_of B.encNosp B.encDepth z h1 h2 hk q hcov hpre (hW _ hpre) he⟩

theorem BlkFn.wipeW_leavesD (z : Bool) (add k : Nat) (h1 : 63 ≤ add) (h2 : add ≤ 127)
    (hk : add + wbytes z * k ≤ 2112)
    (hmx : (Code.block (wipeWin z add k) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsp : (Code.block (wipeWin z add k) : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true)
    {M : CtxMode} (B : BlkFn M) {aligned : Bool} (q : Nat → Nat)
    (hcov : ∀ p : Addr, ∀ d, Blocks.winW aligned p d = true →
      winOff add p ≤ d ∧ d < winOff add p + wbytes z * k)
    (hW : ∀ s, (Proof.AesGcm.decryptBlocksX86_64M M).pre s → WP isa B.dec.code s fun s' =>
      Blocks.ScrW s (q (Blocks.n s)) (Blocks.winW aligned (Blocks.S s)) s'.mem) :
    BlkLeavesD (B.wipeW z add k h1 h2 hk hmx hsp) :=
  ⟨leavesW q add (wbytes z * k), fun _ _ _ hpre he =>
    wipeW_leaves_of B.decNosp B.decDepth z h1 h2 hk q hcov hpre (hW _ hpre) he⟩

/-- The working space of loops on 64-byte aligned scratch (`winW true`) is
what `wipeWin _ 127` zeroes with 1024 bytes. -/
theorem winCov_aligned (z : Bool) (k : Nat) (hk : 1024 ≤ wbytes z * k) :
    ∀ p : Addr, ∀ d, Blocks.winW true p d = true → winOff 127 p ≤ d ∧ d < winOff 127 p + wbytes z * k := by
  intro p d h
  simp only [Blocks.winW, AlignedScratch.offset, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
  have hm := Nat.mod_lt (p.toNat + 127) (by decide : 0 < 64)
  have hd := Nat.mod_add_div (p.toNat + 127) 64
  simp only [winOff]; omega

/-- The working space at `scratch + 64` (`winW false`) is within what
`wipeWin _ 63` zeroes with 1088 bytes. -/
theorem winCov_base (z : Bool) (k : Nat) (hk : 1088 ≤ wbytes z * k) :
    ∀ p : Addr, ∀ d, Blocks.winW false p d = true → winOff 63 p ≤ d ∧ d < winOff 63 p + wbytes z * k := by
  intro p d h
  simp only [Blocks.winW, AlignedScratch.offset, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
    decide_eq_true_eq] at h
  have hm := Nat.mod_lt (p.toNat + 63) (by decide : 0 < 64)
  have hd := Nat.mod_add_div (p.toNat + 63) 64
  simp only [winOff]; omega

end Wipe

/-! ## `vg_aes_gcm_stream_encrypt_prepared_vaes_vpclmul`, without secret residue -/

section
open VG.X86_64.Scrub StackLock
open VG.Impl.StackScratch.X86_64 (withStackArgScratch)
open Gcm.X86_64.Stitch (CtxMode)

/-- `vg_aes_gcm_stream_encrypt_prepared` of a variant whose loops read 16
powers, clearing the registers after each call (`streamEncryptClr`, at the
level of 256-bit registers), with the whole-blocks functions `B16` on 16
prepared powers and `B` on the key context. -/
def streamEncryptCodeF16W (v : GcmImpl) (B16 : BlkFn CtxMode.prepared16) (B : BlkFn CtxMode.base) : Prog isa :=
  Impl.Gcm.X86_64.Flag.onFlag 16
    (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr (v.withBlk B16) .avx))
    (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr (v.withBlk B) .avx))

/-- `streamDecryptCodeF16C` with the whole-blocks functions `B16` and `B`. -/
def streamDecryptCodeF16W (v : GcmImpl) (B16 : BlkFn CtxMode.prepared16) (B : BlkFn CtxMode.base) : Prog isa :=
  Impl.Gcm.X86_64.Flag.onFlag 16
    (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecryptClr (v.withBlk B16) .avx))
    (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecryptClr (v.withBlk B) .avx))

/-- Two runs of `streamEncryptCodeF16W` with the same public data leave the
same bytes in all 2608 of their stack: both read the same count (which the
contract leaks) and take the same branch, after the test of the count, which
changes only the flags (`onFlag_inv`); then `streamEnc16_agree` or
`streamEncB_agree` at the level of 256-bit registers. -/
theorem streamEncryptF16W_resOk (v : GcmImpl) (B16 : BlkFn CtxMode.prepared16) (B : BlkFn CtxMode.base)
    (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) (hB : BlkLeaves B)
    (hB16 : BlkLeaves B16) (hct : Plain v.callees.ctr.code) (hgh : Plain v.callees.gh.code)
    (hn : UpperLock.inames B.enc.code = []) (hn16 : UpperLock.inames B16.enc.code = []) :
    ResOk (streamEncryptCodeF16W v B16 B) (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608) 2608 [] [2608] := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho hu hsy e₁ e₂ x hx _
  have h₁' := h₁
  have h₂' := h₂
  have hp' := hp
  unfold Spec.Gcm.streamEncryptPreparedContract at h₁' h₂' hp'
  obtain ⟨s₀₁, t₀₁, hS₁, hk₁, hA₁, hb₁⟩ := onFlag_inv (Or.inl rfl) (flag_inRegions (N := 129) (by decide) h₁') e₁
  obtain ⟨s₀₂, t₀₂, hS₂, hk₂, hA₂, hb₂⟩ := onFlag_inv (Or.inl rfl) (flag_inRegions (N := 129) (by decide) h₂') e₂
  obtain ⟨⟨-, hl⟩, -, -⟩ := (pubL_args (sig := Spec.Gcm.streamCryptPreparedSig) (by decide)).mp hp'
  have hflag : 16 ≤ flagCount s₁ ↔ 16 ≤ flagCount s₂ :=
    flagLeak_iff (Or.inl rfl) (List.head_eq_of_cons_eq hl)
  have q₁ : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pre s₀₁ := by
    unfold Spec.Gcm.streamEncryptPreparedContract; exact (pre_same hS₁).mpr h₁'
  have q₂ : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pre s₀₂ := by
    unfold Spec.Gcm.streamEncryptPreparedContract; exact (pre_same hS₂).mpr h₂'
  have qp : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pub s₀₁ s₀₂ := by
    unfold Spec.Gcm.streamEncryptPreparedContract; exact (pub_same hS₁ hS₂).mpr hp'
  have qg : ∀ r, r ≠ .rax → s₀₁.gpr r = s₀₂.gpr r := fun r h =>
    (hS₁.gpr r h).trans ((ho.2.2.1 r h).trans (hS₂.gpr r h).symm)
  have hsp : s₀₁.gpr .rsp = s₁.gpr .rsp := hS₁.gpr .rsp (by decide)
  have qbm : ∀ x, (⟨s₀₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 →
      s₀₁.mem x = s₀₂.mem x := fun x hx => by
    rw [hS₁.mem, hS₂.mem]; rw [hsp] at hx; exact below_same h₁' ho (by decide) x hx
  have qu : s₀₁.unknowns = s₀₂.unknowns := hk₁.trans (hu.trans hk₂.symm)
  have hf₁ : flagCount s₀₁ = flagCount s₁ := by simp only [flagCount, hS₁.mem, hS₁.gpr .rdi (by decide)]
  have hf₂ : flagCount s₀₂ = flagCount s₂ := by simp only [flagCount, hS₂.mem, hS₂.gpr .rdi (by decide)]
  have hx' : (⟨s₀₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 := by rw [hsp]; exact hx
  have y₁ : s₀₁.syms = s₁.syms := by
    rw [← hA₁]; exact (afterFlag_facts (Or.inl rfl) (flag_inRegions (N := 129) (by decide) h₁')).2.2
  have y₂ : s₀₂.syms = s₂.syms := by
    rw [← hA₂]; exact (afterFlag_facts (Or.inl rfl) (flag_inRegions (N := 129) (by decide) h₂')).2.2
  rcases hb₁ with ⟨c₁, x₁⟩ | ⟨c₁, x₁⟩ <;> rcases hb₂ with ⟨c₂, x₂⟩ | ⟨c₂, x₂⟩
  · exact streamEnc16_agree .avx v B16 gf cf hB16 hct hgh hn16 q₁ q₂ (Nat.le_trans c₁ (Nat.le_of_eq hf₁.symm)) (Nat.le_trans c₂ (Nat.le_of_eq hf₂.symm)) qp qg qbm qu
      (fun n h => by rw [y₁, y₂]; exact hsy n (List.mem_append_right _ (List.mem_append_left _ h))) x₁ x₂ x hx'
  · exact absurd (hflag.mp c₁) c₂
  · exact absurd (hflag.mpr c₂) c₁
  · exact streamEncB_agree .avx v B gf cf hB hct hgh hn q₁ q₂ qp qg qbm qu
      (fun n h => by rw [y₁, y₂]; exact hsy n (List.mem_append_right _ (List.mem_append_right _ h))) x₁ x₂ x hx'

/-- `streamEncryptF16W_resOk` for the blocks functions of `streamEncryptCodeF16C`. -/
theorem streamEncryptF16_resOk (v : GcmVariant) (gf : GhashFree v.impl.gh.fn.code)
    (cf : Proof.Aes.X86_64.Ctr32Free v.impl.ctr.callee) (hB : BlkLeaves v.impl.blkB) (hB16 : BlkLeaves (blkR16 v))
    (hct : Plain v.impl.callees.ctr.code) (hgh : Plain v.impl.callees.gh.code)
    (hn : UpperLock.inames v.impl.blkB.enc.code = []) (hn16 : UpperLock.inames (blkR16 v).enc.code = []) :
    ResOk (streamEncryptCodeF16C v) (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608) 2608 [] [2608] :=
  streamEncryptF16W_resOk v.impl (blkR16 v) v.impl.blkB gf cf hB hB16 hct hgh hn hn16


/-- `vg_aes_gcm_stream_decrypt_prepared` of a variant whose loops read 16
powers, clearing the registers after each call (`streamDecryptClr`, at the
level of 256-bit registers): by the count, its code on them or its code on
the key context. -/
def streamDecryptCodeF16C (v : GcmVariant) : Prog isa :=
  Impl.Gcm.X86_64.Flag.onFlag 16
    (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecryptClr (v.impl.withBlk (blkR16 v)) .avx))
    (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecryptClr v.impl.callees .avx))

/-- `streamEncryptF16W_resOk` for `vg_aes_gcm_stream_decrypt_prepared`. -/
theorem streamDecryptF16W_resOk (v : GcmImpl) (B16 : BlkFn CtxMode.prepared16) (B : BlkFn CtxMode.base)
    (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) (hB : BlkLeavesD B)
    (hB16 : BlkLeavesD B16) (hct : Plain v.callees.ctr.code) (hgh : Plain v.callees.gh.code)
    (hn : UpperLock.inames B.dec.code = []) (hn16 : UpperLock.inames B16.dec.code = []) :
    ResOk (streamDecryptCodeF16W v B16 B) (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608) 2608 [] [2608] := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho hu hsy e₁ e₂ x hx _
  have h₁' := h₁
  have h₂' := h₂
  have hp' := hp
  unfold Spec.Gcm.streamDecryptPreparedContract at h₁' h₂' hp'
  obtain ⟨s₀₁, t₀₁, hS₁, hk₁, hA₁, hb₁⟩ := onFlag_inv (Or.inl rfl) (flag_inRegions (N := 129) (by decide) h₁') e₁
  obtain ⟨s₀₂, t₀₂, hS₂, hk₂, hA₂, hb₂⟩ := onFlag_inv (Or.inl rfl) (flag_inRegions (N := 129) (by decide) h₂') e₂
  obtain ⟨⟨-, hl⟩, -, -⟩ := (pubL_args (sig := Spec.Gcm.streamCryptPreparedSig) (by decide)).mp hp'
  have hflag : 16 ≤ flagCount s₁ ↔ 16 ≤ flagCount s₂ :=
    flagLeak_iff (Or.inl rfl) (List.head_eq_of_cons_eq hl)
  have q₁ : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pre s₀₁ := by
    unfold Spec.Gcm.streamDecryptPreparedContract; exact (pre_same hS₁).mpr h₁'
  have q₂ : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pre s₀₂ := by
    unfold Spec.Gcm.streamDecryptPreparedContract; exact (pre_same hS₂).mpr h₂'
  have qp : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pub s₀₁ s₀₂ := by
    unfold Spec.Gcm.streamDecryptPreparedContract; exact (pub_same hS₁ hS₂).mpr hp'
  have qg : ∀ r, r ≠ .rax → s₀₁.gpr r = s₀₂.gpr r := fun r h =>
    (hS₁.gpr r h).trans ((ho.2.2.1 r h).trans (hS₂.gpr r h).symm)
  have hsp : s₀₁.gpr .rsp = s₁.gpr .rsp := hS₁.gpr .rsp (by decide)
  have qbm : ∀ x, (⟨s₀₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 →
      s₀₁.mem x = s₀₂.mem x := fun x hx => by
    rw [hS₁.mem, hS₂.mem]; rw [hsp] at hx; exact below_same h₁' ho (by decide) x hx
  have qu : s₀₁.unknowns = s₀₂.unknowns := hk₁.trans (hu.trans hk₂.symm)
  have hf₁ : flagCount s₀₁ = flagCount s₁ := by simp only [flagCount, hS₁.mem, hS₁.gpr .rdi (by decide)]
  have hf₂ : flagCount s₀₂ = flagCount s₂ := by simp only [flagCount, hS₂.mem, hS₂.gpr .rdi (by decide)]
  have hx' : (⟨s₀₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 := by rw [hsp]; exact hx
  have y₁ : s₀₁.syms = s₁.syms := by
    rw [← hA₁]; exact (afterFlag_facts (Or.inl rfl) (flag_inRegions (N := 129) (by decide) h₁')).2.2
  have y₂ : s₀₂.syms = s₂.syms := by
    rw [← hA₂]; exact (afterFlag_facts (Or.inl rfl) (flag_inRegions (N := 129) (by decide) h₂')).2.2
  rcases hb₁ with ⟨c₁, x₁⟩ | ⟨c₁, x₁⟩ <;> rcases hb₂ with ⟨c₂, x₂⟩ | ⟨c₂, x₂⟩
  · exact streamDec16_agree .avx v B16 gf cf hB16 hct hgh hn16 q₁ q₂ (Nat.le_trans c₁ (Nat.le_of_eq hf₁.symm)) (Nat.le_trans c₂ (Nat.le_of_eq hf₂.symm)) qp qg qbm qu
      (fun n h => by rw [y₁, y₂]; exact hsy n (List.mem_append_right _ (List.mem_append_left _ h))) x₁ x₂ x hx'
  · exact absurd (hflag.mp c₁) c₂
  · exact absurd (hflag.mpr c₂) c₁
  · exact streamDecB_agree .avx v B gf cf hB hct hgh hn q₁ q₂ qp qg qbm qu
      (fun n h => by rw [y₁, y₂]; exact hsy n (List.mem_append_right _ (List.mem_append_right _ h))) x₁ x₂ x hx'

/-- `streamDecryptF16W_resOk` for the blocks functions of `streamDecryptCodeF16C`. -/
theorem streamDecryptF16_resOk (v : GcmVariant) (gf : GhashFree v.impl.gh.fn.code)
    (cf : Proof.Aes.X86_64.Ctr32Free v.impl.ctr.callee) (hB : BlkLeavesD v.impl.blkB) (hB16 : BlkLeavesD (blkR16 v))
    (hct : Plain v.impl.callees.ctr.code) (hgh : Plain v.impl.callees.gh.code)
    (hn : UpperLock.inames v.impl.blkB.dec.code = []) (hn16 : UpperLock.inames (blkR16 v).dec.code = []) :
    ResOk (streamDecryptCodeF16C v) (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608) 2608 [] [2608] :=
  streamDecryptF16W_resOk v.impl (blkR16 v) v.impl.blkB gf cf hB hB16 hct hgh hn hn16

end

/-- `vg_aes_gcm_stream_encrypt_prepared` of a variant whose loops read 16
powers, before any clearing on return. -/
def streamEncryptF16Plain (v : GcmVariant) : Unscrubbed Spec.Gcm.streamEncryptPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := streamEncryptCodeF16S v
  stack := 2608
  verified := VG.Proof.AesGcm.Flag.streamEncrypt_keyed
    (Flag.streamEncrypt_ofB (Or.inl rfl) (streamEncryptCodeF16S_verified v))
  spSafe := streamEncryptCodeF16S_spAll v

open VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul (variant) in
/-- What the clearing of only the general-purpose registers needs of
`vg_aes_gcm_stream_encrypt_prepared_vaes_vpclmul`, checked by the emitter
(as `StreamChk`). -/
def StreamChkF16 : Prop :=
  variant.streamF16Clr = true ∧ UpperLock.inames variant.impl.callees.ctr.code = [] ∧
    UpperLock.inames variant.impl.callees.gh.code = [] ∧ UpperLock.inames variant.impl.blkB.enc.code = [] ∧
    UpperLock.inames (blkR16 variant).enc.code = [] ∧ UpperLock.inames (streamEncryptCodeF16C variant) = [] ∧
    VecLock.step .avx (streamEncryptCodeF16C variant) (true, true) = (true, true)

instance : Decidable StreamChkF16 := by unfold StreamChkF16; infer_instance

open VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul (variant) in
open VG.X86_64.Scrub StackLock in
/-- `vg_aes_gcm_stream_encrypt_prepared_vaes_vpclmul`, followed by the
clearing of the scratch registers only (`withScrubResCR`): it leaves the
same stack in two runs (`streamEncryptF16_resOk`), and the vector registers
it leaves agree (`VecLock.regsOk_of_vec`). `vg_aes_gcm_seal_gather_prepared`
calls its code as it was, `vg_aes_gcm_stream_encrypt_prepared_vaes_vpclmul_core`
(`encFnF16`). `streamEncryptF16Plain` if the emitter's check fails. -/
def streamEncryptF16Vaes : Registration Spec.Gcm.streamEncryptPreparedApi X86_64.target :=
  if h : StreamChkF16 then
    have hc : (streamEncryptF16Plain variant).code = streamEncryptCodeF16C variant := by
      simp only [streamEncryptF16Plain, streamEncryptCodeF16S, h.1, ↓reduceIte]
    RScrub.withScrubResCR (streamEncryptF16Plain variant) (streamEncryptPreparedOut _) [] [2608]
      (hc ▸ streamEncryptF16_resOk variant (variant.impl.gh.free.get rfl) (variant.impl.ctr.free.get rfl)
        blkB_vaes_leaves blkR16_vaes_leaves ⟨variant.impl.ctr.nosp, h.2.1⟩ ⟨variant.impl.gh.nosp, h.2.2.1⟩
        h.2.2.2.1 h.2.2.2.2.1)
      [] scratchRegs (VecLock.regsOk_of_vec (streamEncryptF16Plain variant).verified.2.1 (hc ▸ h.2.2.2.2.2.1)
        (hc ▸ h.2.2.2.2.2.2))
  else (streamEncryptF16Plain variant).registration

section AvxW
open VG.Proof.Variants.AesGcm.X86_64.AesNiPclmulAvx (variant)
open Gcm.X86_64.Stitch (CtxMode)
open VG.Impl.AesGcm.X86_64 (wipeWin)

theorem wipeAB_mx : (Code.block (wipeWin false 63 34) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  decide
theorem wipeAB_sp : (Code.block (wipeWin false 63 34) : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by
  decide
theorem wipeAR_mx : (Code.block (wipeWin false 127 32) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  decide
theorem wipeAR_sp : (Code.block (wipeWin false 127 32) : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by
  decide

/-- The key-context whole-blocks functions of the AVX variant, zeroing the
1088 bytes from `scratch + 63` rounded down to 64 (34 ymm stores). -/
def blkBA : BlkFn CtxMode.base :=
  variant.impl.blkB.wipeW false 63 34 (by decide) (by decide) (by decide) wipeAB_mx wipeAB_sp

/-- The whole-blocks functions of the AVX variant on 16 prepared powers,
zeroing the 1024 bytes of their 64-byte aligned working space (32 ymm
stores). -/
def blkRA : BlkFn CtxMode.prepared16 :=
  (blkR16 variant).wipeW false 127 32 (by decide) (by decide) (by decide) wipeAR_mx wipeAR_sp

theorem blkBA_leaves : BlkLeaves blkBA :=
  BlkFn.wipeW_leaves false 63 34 _ _ _ _ _ variant.impl.blkB (aligned := false) (fun _ => 0)
    (winCov_base false 34 (by decide)) fun s hpre => by
      change WP isa (Impl.AesGcm.X86_64.Blocks.encrypt
        ⟨variant.impl.ctr.callee.name, variant.impl.ctr.callee.code⟩
        variant.impl.gh.fn (some Impl.Gcm.X86_64.StitchAvx8.enc) false true false false
        (some Impl.Gcm.X86_64.StitchAvx8.enc)) s _
      exact Blocks.encryptRW_leaves (Blocks.BP.ofM hpre) _ (variant.impl.ctr.free.get rfl) _
        (variant.impl.gh.free.get rfl) (fun s₃ h₃ => StitchName.okFull .aesniAvx rfl s₃ h₃.base)
        (fun s₃ h₃ _ => StitchName.okFull .aesniAvx rfl s₃ h₃.base)

theorem blkBA_leavesD : BlkLeavesD blkBA :=
  BlkFn.wipeW_leavesD false 63 34 _ _ _ _ _ variant.impl.blkB (aligned := false) (fun n => n - n % 16)
    (winCov_base false 34 (by decide)) fun s hpre => by
      change WP isa (Impl.AesGcm.X86_64.Blocks.decrypt
        ⟨variant.impl.ctr.callee.name, variant.impl.ctr.callee.code⟩
        variant.impl.gh.fn (some Impl.Gcm.X86_64.StitchAvx8.dec) false false) s _
      exact Blocks.decryptBW_leaves (Blocks.BP.ofM hpre) _ (variant.impl.ctr.free.get rfl) _
        (variant.impl.gh.free.get rfl) fun s₃ h₃ hm => (StitchName.ok .aesniAvx).2 s₃ h₃.base hm

theorem blkRA_leaves : BlkLeaves blkRA :=
  BlkFn.wipeW_leaves false 127 32 _ _ _ _ _ (blkR16 variant) (aligned := true) (fun _ => 0)
    (winCov_aligned false 32 (by decide)) fun s hpre => by
      change WP isa (Impl.AesGcm.X86_64.Blocks.encrypt
        ⟨variant.impl.ctr.callee.name, variant.impl.ctr.callee.code⟩
        variant.impl.gh.fn (some Impl.Gcm.X86_64.StitchAvx8.encR) true true true true
        (some Impl.Gcm.X86_64.StitchAvx8.encRS)) s _
      exact Blocks.encryptRW_leaves (Blocks.BP.ofM hpre) _ (variant.impl.ctr.free.get rfl) _
        (variant.impl.gh.free.get rfl) (fun s₃ h₃ => (StitchName.okR16 .aesniAvx rfl).1 s₃ h₃ (Nat.mod_one _))
        (StitchName.okRS16 .aesniAvx rfl).1

theorem blkRA_leavesD : BlkLeavesD blkRA :=
  BlkFn.wipeW_leavesD false 127 32 _ _ _ _ _ (blkR16 variant) (aligned := true) (fun _ => 0)
    (winCov_aligned false 32 (by decide)) fun s hpre => by
      change WP isa (Impl.AesGcm.X86_64.Blocks.decrypt
        ⟨variant.impl.ctr.callee.name, variant.impl.ctr.callee.code⟩
        variant.impl.gh.fn (some Impl.Gcm.X86_64.StitchAvx8.decR) true true true true
        (some Impl.Gcm.X86_64.StitchAvx8.decRS)) s _
      exact Blocks.decryptRW_leaves (Blocks.BP.ofM hpre) _ (variant.impl.ctr.free.get rfl) _
        (variant.impl.gh.free.get rfl) (fun s₃ h₃ => (StitchName.okR16 .aesniAvx rfl).2 s₃ h₃ (Nat.mod_one _))
        (StitchName.okRS16 .aesniAvx rfl).2

end AvxW

section Avx
open VG.Proof.Variants.AesGcm.X86_64.AesNiPclmulAvx (variant)
open VG.X86_64.Scrub StackLock

/-- `vg_aes_gcm_stream_encrypt_prepared_aesni_pclmul_avx`, clearing the
registers after each call (`streamEncryptClr`, at the level of 256-bit
registers) and calling whole-blocks functions that zero their loops' working
space before they return (`blkRA`, `blkBA`), before any clearing on return. -/
def streamEncryptF16AvxPlain : Unscrubbed Spec.Gcm.streamEncryptPreparedApi X86_64.target where
  suffix := variant.impl.suffix
  code := streamEncryptCodeF16W variant.impl blkRA blkBA
  stack := 2608
  verified := VG.Proof.AesGcm.Flag.streamEncrypt_keyed (Flag.streamEncrypt_ofB (Or.inl rfl)
    (Flag.streamEncrypt_onFlag16B (streamEncryptClr16_framed .avx variant.impl blkRA)
      (streamEncryptClrB_framed .avx variant.impl blkBA)))
  spSafe := VG.X86_64.onFlag_spSafe (streamEncryptClr_spSafe .avx variant.impl blkRA)
    (streamEncryptClr_spSafe .avx variant.impl blkBA)

/-- What the clearing of only the general-purpose registers needs of
`vg_aes_gcm_stream_encrypt_prepared_aesni_pclmul_avx`, checked by the
emitter (as `StreamChk`). -/
def StreamChkF16A : Prop :=
  UpperLock.inames variant.impl.callees.ctr.code = [] ∧ UpperLock.inames variant.impl.callees.gh.code = [] ∧
    UpperLock.inames blkBA.enc.code = [] ∧ UpperLock.inames blkRA.enc.code = [] ∧
    UpperLock.inames streamEncryptF16AvxPlain.code = [] ∧
    VecLock.step .avx streamEncryptF16AvxPlain.code (true, true) = (true, true)

instance : Decidable StreamChkF16A := by unfold StreamChkF16A; infer_instance

/-- `vg_aes_gcm_stream_encrypt_prepared_aesni_pclmul_avx`, followed by the
clearing of the scratch registers only (`withScrubResCR`): its whole-blocks
functions zero their loops' working space (`blkBA_leaves`, `blkRA_leaves`), so it leaves
the same stack in two runs (`streamEncryptF16W_resOk`), and the vector
registers it leaves agree (`VecLock.regsOk_of_vec`).
`vg_aes_gcm_seal_gather_prepared` calls its code as it was,
`vg_aes_gcm_stream_encrypt_prepared_aesni_pclmul_avx_core` (`encFnF16`).
`streamEncryptF16AvxPlain` if the emitter's check fails. -/
def streamEncryptF16Avx : Registration Spec.Gcm.streamEncryptPreparedApi X86_64.target :=
  if h : StreamChkF16A then
    RScrub.withScrubResCR streamEncryptF16AvxPlain (streamEncryptPreparedOut _) [] [2608]
      (streamEncryptF16W_resOk variant.impl blkRA blkBA
        (variant.impl.gh.free.get rfl) (variant.impl.ctr.free.get rfl) blkBA_leaves blkRA_leaves
        ⟨variant.impl.ctr.nosp, h.1⟩ ⟨variant.impl.gh.nosp, h.2.1⟩ h.2.2.1 h.2.2.2.1)
      [] scratchRegs (VecLock.regsOk_of_vec streamEncryptF16AvxPlain.verified.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
  else streamEncryptF16AvxPlain.registration

/-- `streamEncryptF16AvxPlain` for `vg_aes_gcm_stream_decrypt_prepared`. -/
def streamDecryptF16AvxPlain : Unscrubbed Spec.Gcm.streamDecryptPreparedApi X86_64.target where
  suffix := variant.impl.suffix
  code := streamDecryptCodeF16W variant.impl blkRA blkBA
  stack := 2608
  verified := VG.Proof.AesGcm.Flag.streamDecrypt_keyed (Flag.streamDecrypt_onFlag16
    (streamDecryptClr16_framed .avx variant.impl blkRA)
    (streamDecryptClrB_framed .avx variant.impl blkBA))
  spSafe := VG.X86_64.onFlag_spSafe (streamDecryptClr_spSafe .avx variant.impl blkRA)
    (streamDecryptClr_spSafe .avx variant.impl blkBA)

/-- `StreamChkF16A` for `vg_aes_gcm_stream_decrypt_prepared_aesni_pclmul_avx`. -/
def StreamChkF16AD : Prop :=
  UpperLock.inames variant.impl.callees.ctr.code = [] ∧ UpperLock.inames variant.impl.callees.gh.code = [] ∧
    UpperLock.inames blkBA.dec.code = [] ∧ UpperLock.inames blkRA.dec.code = [] ∧
    UpperLock.inames streamDecryptF16AvxPlain.code = [] ∧
    VecLock.step .avx streamDecryptF16AvxPlain.code (true, true) = (true, true)

instance : Decidable StreamChkF16AD := by unfold StreamChkF16AD; infer_instance

/-- `streamEncryptF16Avx` for `vg_aes_gcm_stream_decrypt_prepared`. -/
def streamDecryptF16Avx : Registration Spec.Gcm.streamDecryptPreparedApi X86_64.target :=
  if h : StreamChkF16AD then
    RScrub.withScrubResCR streamDecryptF16AvxPlain (streamDecryptPreparedOut _) [] [2608]
      (streamDecryptF16W_resOk variant.impl blkRA blkBA
        (variant.impl.gh.free.get rfl) (variant.impl.ctr.free.get rfl) blkBA_leavesD blkRA_leavesD
        ⟨variant.impl.ctr.nosp, h.1⟩ ⟨variant.impl.gh.nosp, h.2.1⟩ h.2.2.1 h.2.2.2.1)
      [] scratchRegs (VecLock.regsOk_of_vec streamDecryptF16AvxPlain.verified.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
  else streamDecryptF16AvxPlain.registration

end Avx

/-! ## `vg_aes_gcm_stream_encrypt_prepared_vaes_vpclmul_avx512` and `_decrypt_prepared`, without secret residue

The flag-48 route P: the whole-blocks functions zero their loops' working
space before they return (`BlkFn.wipeW`: 16 aligned zmm stores on the 48
powers, 17 at `scratch + 64` on the key context), so what they leave in
`scratch` is a function of their arguments (`blkBZ_leaves`, `blkRZ_leaves`,
from `Blocks.encryptBW_leaves` and `Blocks.encryptRW_leaves`, which use only
the loops' frame). -/

section Avx512
open VG.Proof.Variants.AesGcm.X86_64.VaesVpclmulAvx512 (variant)
open VG.X86_64.Scrub StackLock
open VG.Impl.StackScratch.X86_64 (withStackArgScratch)
open Gcm.X86_64.Stitch (CtxMode)
open VG.Impl.AesGcm.X86_64 (wipeWin)

theorem wipeZB_mx : (Code.block (wipeWin true 63 17) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  decide
theorem wipeZB_sp : (Code.block (wipeWin true 63 17) : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by
  decide
theorem wipeZR_mx : (Code.block (wipeWin true 127 16) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  decide
theorem wipeZR_sp : (Code.block (wipeWin true 127 16) : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by
  decide

/-- The key-context whole-blocks functions of the AVX-512 variant, zeroing
the 1088 bytes from `scratch + 63` rounded down to 64 (17 zmm stores). -/
def blkBZ : BlkFn CtxMode.base :=
  variant.impl.blkB.wipeW true 63 17 (by decide) (by decide) (by decide) wipeZB_mx wipeZB_sp

/-- The whole-blocks functions of the AVX-512 variant on the 48 prepared
powers, zeroing the 1024 bytes of their 64-byte aligned working space (16
zmm stores). -/
def blkRZ : BlkFn CtxMode.prepared :=
  (blkR variant).wipeW true 127 16 (by decide) (by decide) (by decide) wipeZR_mx wipeZR_sp

theorem blkBZ_leaves : BlkLeaves blkBZ :=
  BlkFn.wipeW_leaves true 63 17 _ _ _ _ _ variant.impl.blkB (aligned := false) (fun n => n - n % 16)
    (winCov_base true 17 (by decide)) fun s hpre => by
      change WP isa (Impl.AesGcm.X86_64.Blocks.encrypt
        ⟨variant.impl.ctr.callee.name, variant.impl.ctr.callee.code⟩
        variant.impl.gh.fn (some Impl.Gcm.X86_64.StitchZ.enc) false false) s _
      exact Blocks.encryptBW_leaves (Blocks.BP.ofM hpre) _ (variant.impl.ctr.free.get rfl) _
        (variant.impl.gh.free.get rfl) fun s₃ h₃ hm => (StitchName.ok .vaesAvx512).1 s₃ h₃.base hm

theorem blkBZ_leavesD : BlkLeavesD blkBZ :=
  BlkFn.wipeW_leavesD true 63 17 _ _ _ _ _ variant.impl.blkB (aligned := false) (fun n => n - n % 16)
    (winCov_base true 17 (by decide)) fun s hpre => by
      change WP isa (Impl.AesGcm.X86_64.Blocks.decrypt
        ⟨variant.impl.ctr.callee.name, variant.impl.ctr.callee.code⟩
        variant.impl.gh.fn (some Impl.Gcm.X86_64.StitchZ.dec) false false) s _
      exact Blocks.decryptBW_leaves (Blocks.BP.ofM hpre) _ (variant.impl.ctr.free.get rfl) _
        (variant.impl.gh.free.get rfl) fun s₃ h₃ hm => (StitchName.ok .vaesAvx512).2 s₃ h₃.base hm

theorem blkRZ_leaves : BlkLeaves blkRZ :=
  BlkFn.wipeW_leaves true 127 16 _ _ _ _ _ (blkR variant) (aligned := true) (fun _ => 0)
    (winCov_aligned true 16 (by decide)) fun s hpre => by
      change WP isa (Impl.AesGcm.X86_64.Blocks.encrypt
        ⟨variant.impl.ctr.callee.name, variant.impl.ctr.callee.code⟩
        variant.impl.gh.fn (some Impl.Gcm.X86_64.StitchZH.encR) true true false false
        (some Impl.Gcm.X86_64.StitchZH.encR)) s _
      exact Blocks.encryptRW_leaves (Blocks.BP.ofM hpre) _ (variant.impl.ctr.free.get rfl) _
        (variant.impl.gh.free.get rfl) (fun s₃ h₃ => (StitchName.okR .vaesAvx512).1 s₃ h₃ (Nat.mod_one _))
        (StitchName.okRS .vaesAvx512).1

theorem blkRZ_leavesD : BlkLeavesD blkRZ :=
  BlkFn.wipeW_leavesD true 127 16 _ _ _ _ _ (blkR variant) (aligned := true) (fun _ => 0)
    (winCov_aligned true 16 (by decide)) fun s hpre => by
      change WP isa (Impl.AesGcm.X86_64.Blocks.decrypt
        ⟨variant.impl.ctr.callee.name, variant.impl.ctr.callee.code⟩
        variant.impl.gh.fn (some Impl.Gcm.X86_64.StitchZH.decR) true true false false
        (some Impl.Gcm.X86_64.StitchZH.decR)) s _
      exact Blocks.decryptRW_leaves (Blocks.BP.ofM hpre) _ (variant.impl.ctr.free.get rfl) _
        (variant.impl.gh.free.get rfl) (fun s₃ h₃ => (StitchName.okR .vaesAvx512).2 s₃ h₃ (Nat.mod_one _))
        (StitchName.okRS .vaesAvx512).2

end Avx512

section F48
open VG.X86_64.Scrub StackLock
open VG.Impl.StackScratch.X86_64 (withStackArgScratch)
open Gcm.X86_64.Stitch (CtxMode)

/-- `streamEncryptCodeF16W` on the 48 prepared powers. -/
def streamEncryptCodeF48W (v : GcmImpl) (B48 : BlkFn CtxMode.prepared) (B : BlkFn CtxMode.base) : Prog isa :=
  Impl.Gcm.X86_64.Flag.onFlag 48
    (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr (v.withBlk B48) .avx))
    (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr (v.withBlk B) .avx))

/-- `streamDecryptCodeF16W` on the 48 prepared powers. -/
def streamDecryptCodeF48W (v : GcmImpl) (B48 : BlkFn CtxMode.prepared) (B : BlkFn CtxMode.base) : Prog isa :=
  Impl.Gcm.X86_64.Flag.onFlag 48
    (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecryptClr (v.withBlk B48) .avx))
    (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecryptClr (v.withBlk B) .avx))

theorem streamEnc48_narrowPre {s : State} (hs : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pre s)
    (hf : 48 ≤ flagCount s) :
    (Proof.AesGcm.streamEncryptPreparedRoundsContract X86_64.abi 2608).pre (narrow128 s) := by
  unfold Spec.Gcm.streamEncryptPreparedContract at hs
  have h₁ := pre_of_rel (N := 129) (C := fun m ctx => 48 ≤ (m.readW (ctx + 1024) 64).toNat) (leakB := none)
    (pre := Spec.Gcm.streamCryptPreparedPre 64) (pre' := Proof.Gcm.streamCryptPowersPre 64)
    (fun _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.2 hf⟩) hs hf
  exact pre_narrowFirstArray (n := 128) (n' := 129) (by decide) (pre := Proof.Gcm.streamCryptPowersPre 64)
    (fun _ _ _ _ _ _ _ _ h => h) h₁

theorem streamEnc48_narrowPub {s₁ s₂ : State}
    (hp : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pub s₁ s₂) :
    (Proof.AesGcm.streamEncryptPreparedRoundsContract X86_64.abi 2608).pub (narrow128 s₁) (narrow128 s₂) := by
  unfold Spec.Gcm.streamEncryptPreparedContract at hp
  obtain ⟨⟨hs, -⟩, hpubs, hdescs⟩ := (pubL_args (sig := Spec.Gcm.streamCryptPreparedSig) (by decide)).mp hp
  unfold Proof.AesGcm.streamEncryptPreparedRoundsContract
  exact (pubL_args (sig := Proof.Gcm.streamCryptPrecomputedSig) (by decide)).mpr ⟨⟨hs, trivial⟩, hpubs,
    fun r hr i hi => hdescs r (by
      rw [show Spec.Gcm.streamCryptPreparedSig.params = ("ctx", .array false .u64 129) ::
        Proof.Gcm.streamCryptPrecomputedSig.params.tail from rfl, descs_array .u64 128 129]
      exact hr) i hi⟩

open StackLock in
/-- `streamEncB_agree`, on 48 prepared powers (whose count both runs read). -/
theorem streamEnc48_agree (lv : Impl.Scrub.X86_64.VecLevel) (v : GcmImpl) (B : BlkFn CtxMode.prepared)
    (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) (hB : BlkLeaves B)
    (hct : Plain v.callees.ctr.code) (hgh : Plain v.callees.gh.code) (hn : UpperLock.inames B.enc.code = [])
    {s₁ s₂ : State}
    (h₁ : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pre s₁)
    (h₂ : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pre s₂)
    (hf₁ : 48 ≤ flagCount s₁) (hf₂ : 48 ≤ flagCount s₂)
    (hp : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pub s₁ s₂)
    (hg : ∀ r, r ≠ .rax → s₁.gpr r = s₂.gpr r)
    (hbm : ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 → s₁.mem x = s₂.mem x)
    (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (Impl.AesGcm.X86_64.streamEncryptClr (v.withBlk B) lv), s₁.syms n = s₂.syms n) {t₁ t₂ : List Leak} {u₁ u₂ : State}
    (e₁ : Exec isa (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr (v.withBlk B) lv)) s₁ t₁ u₁)
    (e₂ : Exec isa (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr (v.withBlk B) lv)) s₂ t₂ u₂) :
    ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 → u₁.mem x = u₂.mem x := by
  obtain ⟨Lb, hL⟩ := hB
  intro x hx
  have hn₁ := streamEnc48_narrowPre h₁ hf₁
  have hn₂ := streamEnc48_narrowPre h₂ hf₂
  have hv := streamEncryptClr48_framed lv v B
  obtain ⟨t₁', u₁', e₁', hm₁⟩ := exec_narrow hv hn₁
    (fun _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)) (Covers.refl _) e₁
  obtain ⟨t₂', u₂', e₂', hm₂⟩ := exec_narrow hv hn₂
    (fun _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)) (Covers.refl _) e₂
  have hrsp : s₁.gpr .rsp = s₂.gpr .rsp := hg .rsp (by decide)
  have hpn := streamEnc48_narrowPub hp
  unfold Spec.Gcm.streamEncryptPreparedContract at hp
  rw [hm₁, hm₂]
  by_cases hb : (below (s₁.gpr .rsp - BitVec.ofNat 64 2584) 24).Contains x 1
  · exact streamEncryptClr48_below lv v B hct hgh hn hn₁ hn₂ hpn hrsp hbm hu e₁' e₂' x hb
  · have hx' := frame_or_below hx hb
    rw [streamEncryptClr48_leaves lv v gf cf B hL hn₁ e₁' x hx',
      streamEncryptClr48_leaves lv v gf cf B hL hn₂ e₂' x (by have h := hx'; rw [hrsp] at h; exact h),
      streamFV_congr Lb (s₁ := narrow128 s₁) (s₂ := narrow128 s₂) hg (streamLen_pub (s₁ := s₁) (s₂ := s₂) hp)]
    have hb' : (narrow128 s₁).gpr .rsp = (narrow128 s₂).gpr .rsp := hrsp
    rw [streamEncryptClr48_leaves_innerU lv v B hn₁ hn₂ hpn hu hsy, hb']
    exact congrArg (Option.getD _) (hbm x hx)

theorem streamDec48_narrowPre {s : State} (hs : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pre s)
    (hf : 48 ≤ flagCount s) :
    (Proof.AesGcm.streamDecryptPreparedRoundsContract X86_64.abi 2608).pre (narrow128 s) := by
  unfold Spec.Gcm.streamDecryptPreparedContract at hs
  have h₁ := pre_of_rel (N := 129) (C := fun m ctx => 48 ≤ (m.readW (ctx + 1024) 64).toNat) (leakB := none)
    (pre := Spec.Gcm.streamCryptPreparedPre 64) (pre' := Proof.Gcm.streamCryptPowersPre 64)
    (fun _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.2 hf⟩) hs hf
  exact pre_narrowFirstArray (n := 128) (n' := 129) (by decide) (pre := Proof.Gcm.streamCryptPowersPre 64)
    (fun _ _ _ _ _ _ _ _ h => h) h₁

theorem streamDec48_narrowPub {s₁ s₂ : State}
    (hp : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pub s₁ s₂) :
    (Proof.AesGcm.streamDecryptPreparedRoundsContract X86_64.abi 2608).pub (narrow128 s₁) (narrow128 s₂) := by
  unfold Spec.Gcm.streamDecryptPreparedContract at hp
  obtain ⟨⟨hs, -⟩, hpubs, hdescs⟩ := (pubL_args (sig := Spec.Gcm.streamCryptPreparedSig) (by decide)).mp hp
  unfold Proof.AesGcm.streamDecryptPreparedRoundsContract
  exact (pubL_args (sig := Proof.Gcm.streamCryptPrecomputedSig) (by decide)).mpr ⟨⟨hs, trivial⟩, hpubs,
    fun r hr i hi => hdescs r (by
      rw [show Spec.Gcm.streamCryptPreparedSig.params = ("ctx", .array false .u64 129) ::
        Proof.Gcm.streamCryptPrecomputedSig.params.tail from rfl, descs_array .u64 128 129]
      exact hr) i hi⟩

open StackLock in
/-- `streamDecB_agree`, on 48 prepared powers (whose count both runs read). -/
theorem streamDec48_agree (lv : Impl.Scrub.X86_64.VecLevel) (v : GcmImpl) (B : BlkFn CtxMode.prepared)
    (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) (hB : BlkLeavesD B)
    (hct : Plain v.callees.ctr.code) (hgh : Plain v.callees.gh.code) (hn : UpperLock.inames B.dec.code = [])
    {s₁ s₂ : State}
    (h₁ : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pre s₁)
    (h₂ : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pre s₂)
    (hf₁ : 48 ≤ flagCount s₁) (hf₂ : 48 ≤ flagCount s₂)
    (hp : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pub s₁ s₂)
    (hg : ∀ r, r ≠ .rax → s₁.gpr r = s₂.gpr r)
    (hbm : ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 → s₁.mem x = s₂.mem x)
    (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (Impl.AesGcm.X86_64.streamDecryptClr (v.withBlk B) lv), s₁.syms n = s₂.syms n) {t₁ t₂ : List Leak} {u₁ u₂ : State}
    (e₁ : Exec isa (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecryptClr (v.withBlk B) lv)) s₁ t₁ u₁)
    (e₂ : Exec isa (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecryptClr (v.withBlk B) lv)) s₂ t₂ u₂) :
    ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 → u₁.mem x = u₂.mem x := by
  obtain ⟨Lb, hL⟩ := hB
  intro x hx
  have hn₁ := streamDec48_narrowPre h₁ hf₁
  have hn₂ := streamDec48_narrowPre h₂ hf₂
  have hv := streamDecryptClr48_framed lv v B
  obtain ⟨t₁', u₁', e₁', hm₁⟩ := exec_narrow hv hn₁
    (fun _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)) (Covers.refl _) e₁
  obtain ⟨t₂', u₂', e₂', hm₂⟩ := exec_narrow hv hn₂
    (fun _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)) (Covers.refl _) e₂
  have hrsp : s₁.gpr .rsp = s₂.gpr .rsp := hg .rsp (by decide)
  have hpn := streamDec48_narrowPub hp
  unfold Spec.Gcm.streamDecryptPreparedContract at hp
  rw [hm₁, hm₂]
  by_cases hb : (below (s₁.gpr .rsp - BitVec.ofNat 64 2584) 24).Contains x 1
  · exact streamDecryptClr48_below lv v B hct hgh hn hn₁ hn₂ hpn hrsp hbm hu e₁' e₂' x hb
  · have hx' := frame_or_below hx hb
    rw [streamDecryptClr48_leaves lv v gf cf B hL hn₁ e₁' x hx',
      streamDecryptClr48_leaves lv v gf cf B hL hn₂ e₂' x (by have h := hx'; rw [hrsp] at h; exact h),
      streamFV_congr Lb (s₁ := narrow128 s₁) (s₂ := narrow128 s₂) hg (streamLen_pub (s₁ := s₁) (s₂ := s₂) hp)]
    have hb' : (narrow128 s₁).gpr .rsp = (narrow128 s₂).gpr .rsp := hrsp
    rw [streamDecryptClr48_leaves_innerU lv v B hn₁ hn₂ hpn hu hsy, hb']
    exact congrArg (Option.getD _) (hbm x hx)

/-- Two runs of `streamEncryptCodeF48W` with the same public data leave the
same bytes in all 2608 of their stack: both read the same count (which the
contract leaks) and take the same branch, after the test of the count, which
changes only the flags (`onFlag_inv`); then `streamEnc48_agree` or
`streamEncB_agree` at the level of 256-bit registers. -/
theorem streamEncryptF48W_resOk (v : GcmImpl) (B48 : BlkFn CtxMode.prepared) (B : BlkFn CtxMode.base)
    (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) (hB : BlkLeaves B)
    (hB48 : BlkLeaves B48) (hct : Plain v.callees.ctr.code) (hgh : Plain v.callees.gh.code)
    (hn : UpperLock.inames B.enc.code = []) (hn48 : UpperLock.inames B48.enc.code = []) :
    ResOk (streamEncryptCodeF48W v B48 B) (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608) 2608 [] [2608] := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho hu hsy e₁ e₂ x hx _
  have h₁' := h₁
  have h₂' := h₂
  have hp' := hp
  unfold Spec.Gcm.streamEncryptPreparedContract at h₁' h₂' hp'
  obtain ⟨s₀₁, t₀₁, hS₁, hk₁, hA₁, hb₁⟩ := onFlag_inv (Or.inr rfl) (flag_inRegions (N := 129) (by decide) h₁') e₁
  obtain ⟨s₀₂, t₀₂, hS₂, hk₂, hA₂, hb₂⟩ := onFlag_inv (Or.inr rfl) (flag_inRegions (N := 129) (by decide) h₂') e₂
  obtain ⟨⟨-, hl⟩, -, -⟩ := (pubL_args (sig := Spec.Gcm.streamCryptPreparedSig) (by decide)).mp hp'
  have hflag : 48 ≤ flagCount s₁ ↔ 48 ≤ flagCount s₂ :=
    flagLeak_iff (Or.inr rfl) (List.head_eq_of_cons_eq hl)
  have q₁ : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pre s₀₁ := by
    unfold Spec.Gcm.streamEncryptPreparedContract; exact (pre_same hS₁).mpr h₁'
  have q₂ : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pre s₀₂ := by
    unfold Spec.Gcm.streamEncryptPreparedContract; exact (pre_same hS₂).mpr h₂'
  have qp : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pub s₀₁ s₀₂ := by
    unfold Spec.Gcm.streamEncryptPreparedContract; exact (pub_same hS₁ hS₂).mpr hp'
  have qg : ∀ r, r ≠ .rax → s₀₁.gpr r = s₀₂.gpr r := fun r h =>
    (hS₁.gpr r h).trans ((ho.2.2.1 r h).trans (hS₂.gpr r h).symm)
  have hsp : s₀₁.gpr .rsp = s₁.gpr .rsp := hS₁.gpr .rsp (by decide)
  have qbm : ∀ x, (⟨s₀₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 →
      s₀₁.mem x = s₀₂.mem x := fun x hx => by
    rw [hS₁.mem, hS₂.mem]; rw [hsp] at hx; exact below_same h₁' ho (by decide) x hx
  have qu : s₀₁.unknowns = s₀₂.unknowns := hk₁.trans (hu.trans hk₂.symm)
  have hf₁ : flagCount s₀₁ = flagCount s₁ := by simp only [flagCount, hS₁.mem, hS₁.gpr .rdi (by decide)]
  have hf₂ : flagCount s₀₂ = flagCount s₂ := by simp only [flagCount, hS₂.mem, hS₂.gpr .rdi (by decide)]
  have hx' : (⟨s₀₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 := by rw [hsp]; exact hx
  have y₁ : s₀₁.syms = s₁.syms := by
    rw [← hA₁]; exact (afterFlag_facts (Or.inr rfl) (flag_inRegions (N := 129) (by decide) h₁')).2.2
  have y₂ : s₀₂.syms = s₂.syms := by
    rw [← hA₂]; exact (afterFlag_facts (Or.inr rfl) (flag_inRegions (N := 129) (by decide) h₂')).2.2
  rcases hb₁ with ⟨c₁, x₁⟩ | ⟨c₁, x₁⟩ <;> rcases hb₂ with ⟨c₂, x₂⟩ | ⟨c₂, x₂⟩
  · exact streamEnc48_agree .avx v B48 gf cf hB48 hct hgh hn48 q₁ q₂ (Nat.le_trans c₁ (Nat.le_of_eq hf₁.symm)) (Nat.le_trans c₂ (Nat.le_of_eq hf₂.symm)) qp qg qbm qu
      (fun n h => by rw [y₁, y₂]; exact hsy n (List.mem_append_right _ (List.mem_append_left _ h))) x₁ x₂ x hx'
  · exact absurd (hflag.mp c₁) c₂
  · exact absurd (hflag.mpr c₂) c₁
  · exact streamEncB_agree .avx v B gf cf hB hct hgh hn q₁ q₂ qp qg qbm qu
      (fun n h => by rw [y₁, y₂]; exact hsy n (List.mem_append_right _ (List.mem_append_right _ h))) x₁ x₂ x hx'

/-- `streamEncryptF48W_resOk` for `vg_aes_gcm_stream_decrypt_prepared`. -/
theorem streamDecryptF48W_resOk (v : GcmImpl) (B48 : BlkFn CtxMode.prepared) (B : BlkFn CtxMode.base)
    (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) (hB : BlkLeavesD B)
    (hB48 : BlkLeavesD B48) (hct : Plain v.callees.ctr.code) (hgh : Plain v.callees.gh.code)
    (hn : UpperLock.inames B.dec.code = []) (hn48 : UpperLock.inames B48.dec.code = []) :
    ResOk (streamDecryptCodeF48W v B48 B) (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608) 2608 [] [2608] := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho hu hsy e₁ e₂ x hx _
  have h₁' := h₁
  have h₂' := h₂
  have hp' := hp
  unfold Spec.Gcm.streamDecryptPreparedContract at h₁' h₂' hp'
  obtain ⟨s₀₁, t₀₁, hS₁, hk₁, hA₁, hb₁⟩ := onFlag_inv (Or.inr rfl) (flag_inRegions (N := 129) (by decide) h₁') e₁
  obtain ⟨s₀₂, t₀₂, hS₂, hk₂, hA₂, hb₂⟩ := onFlag_inv (Or.inr rfl) (flag_inRegions (N := 129) (by decide) h₂') e₂
  obtain ⟨⟨-, hl⟩, -, -⟩ := (pubL_args (sig := Spec.Gcm.streamCryptPreparedSig) (by decide)).mp hp'
  have hflag : 48 ≤ flagCount s₁ ↔ 48 ≤ flagCount s₂ :=
    flagLeak_iff (Or.inr rfl) (List.head_eq_of_cons_eq hl)
  have q₁ : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pre s₀₁ := by
    unfold Spec.Gcm.streamDecryptPreparedContract; exact (pre_same hS₁).mpr h₁'
  have q₂ : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pre s₀₂ := by
    unfold Spec.Gcm.streamDecryptPreparedContract; exact (pre_same hS₂).mpr h₂'
  have qp : (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pub s₀₁ s₀₂ := by
    unfold Spec.Gcm.streamDecryptPreparedContract; exact (pub_same hS₁ hS₂).mpr hp'
  have qg : ∀ r, r ≠ .rax → s₀₁.gpr r = s₀₂.gpr r := fun r h =>
    (hS₁.gpr r h).trans ((ho.2.2.1 r h).trans (hS₂.gpr r h).symm)
  have hsp : s₀₁.gpr .rsp = s₁.gpr .rsp := hS₁.gpr .rsp (by decide)
  have qbm : ∀ x, (⟨s₀₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 →
      s₀₁.mem x = s₀₂.mem x := fun x hx => by
    rw [hS₁.mem, hS₂.mem]; rw [hsp] at hx; exact below_same h₁' ho (by decide) x hx
  have qu : s₀₁.unknowns = s₀₂.unknowns := hk₁.trans (hu.trans hk₂.symm)
  have hf₁ : flagCount s₀₁ = flagCount s₁ := by simp only [flagCount, hS₁.mem, hS₁.gpr .rdi (by decide)]
  have hf₂ : flagCount s₀₂ = flagCount s₂ := by simp only [flagCount, hS₂.mem, hS₂.gpr .rdi (by decide)]
  have hx' : (⟨s₀₁.gpr .rsp - BitVec.ofNat 64 2608, 2608⟩ : Region).Contains x 1 := by rw [hsp]; exact hx
  have y₁ : s₀₁.syms = s₁.syms := by
    rw [← hA₁]; exact (afterFlag_facts (Or.inr rfl) (flag_inRegions (N := 129) (by decide) h₁')).2.2
  have y₂ : s₀₂.syms = s₂.syms := by
    rw [← hA₂]; exact (afterFlag_facts (Or.inr rfl) (flag_inRegions (N := 129) (by decide) h₂')).2.2
  rcases hb₁ with ⟨c₁, x₁⟩ | ⟨c₁, x₁⟩ <;> rcases hb₂ with ⟨c₂, x₂⟩ | ⟨c₂, x₂⟩
  · exact streamDec48_agree .avx v B48 gf cf hB48 hct hgh hn48 q₁ q₂ (Nat.le_trans c₁ (Nat.le_of_eq hf₁.symm)) (Nat.le_trans c₂ (Nat.le_of_eq hf₂.symm)) qp qg qbm qu
      (fun n h => by rw [y₁, y₂]; exact hsy n (List.mem_append_right _ (List.mem_append_left _ h))) x₁ x₂ x hx'
  · exact absurd (hflag.mp c₁) c₂
  · exact absurd (hflag.mpr c₂) c₁
  · exact streamDecB_agree .avx v B gf cf hB hct hgh hn q₁ q₂ qp qg qbm qu
      (fun n h => by rw [y₁, y₂]; exact hsy n (List.mem_append_right _ (List.mem_append_right _ h))) x₁ x₂ x hx'

end F48

section Avx512R
open VG.Proof.Variants.AesGcm.X86_64.VaesVpclmulAvx512 (variant)
open VG.X86_64.Scrub StackLock

/-- `vg_aes_gcm_stream_encrypt_prepared_vaes_vpclmul_avx512`, clearing the
registers after each call (`streamEncryptClr`, at the level of 256-bit
registers: `vpxor` zeroes `zmm0`–`zmm15` whole) and calling whole-blocks
functions that zero their loops' working space before they return
(`blkRZ`, `blkBZ`), before any clearing on return. -/
def streamEncryptF48ZPlain : Unscrubbed Spec.Gcm.streamEncryptPreparedApi X86_64.target where
  suffix := variant.impl.suffix
  code := streamEncryptCodeF48W variant.impl blkRZ blkBZ
  stack := 2608
  verified := VG.Proof.AesGcm.Flag.streamEncrypt_keyed (Flag.streamEncrypt_ofB (Or.inr rfl)
    (Flag.streamEncrypt_onFlagB (streamEncryptClr48_framed .avx variant.impl blkRZ)
      (streamEncryptClrB_framed .avx variant.impl blkBZ)))
  spSafe := VG.X86_64.onFlag_spSafe (streamEncryptClr_spSafe .avx variant.impl blkRZ)
    (streamEncryptClr_spSafe .avx variant.impl blkBZ)

/-- What the clearing of only the general-purpose registers needs of
`vg_aes_gcm_stream_encrypt_prepared_vaes_vpclmul_avx512`, checked by the
emitter (as `StreamChkF16A`). -/
def StreamChkF48Z : Prop :=
  UpperLock.inames variant.impl.callees.ctr.code = [] ∧ UpperLock.inames variant.impl.callees.gh.code = [] ∧
    UpperLock.inames blkBZ.enc.code = [] ∧ UpperLock.inames blkRZ.enc.code = [] ∧
    UpperLock.inames streamEncryptF48ZPlain.code = [] ∧
    VecLock.step .avx streamEncryptF48ZPlain.code (true, true) = (true, true) ∧
    HLock.step streamEncryptF48ZPlain.code true = true

instance : Decidable StreamChkF48Z := by unfold StreamChkF48Z; infer_instance

/-- `vg_aes_gcm_stream_encrypt_prepared_vaes_vpclmul_avx512`, followed by the
clearing of the scratch registers only (`withScrubResCRH`): its
whole-blocks functions zero `zmm16`–`zmm31` before they return, so two runs
leave the same there (`HLock.step`), and they leave in their scratch a
function of their arguments (`blkBZ_leaves`, `blkRZ_leaves`), so it leaves
the same stack in two runs (`streamEncryptF48W_resOk`), and `zmm0`–`zmm15`
agree (`VecLock.regsOk_of_vec`). `vg_aes_gcm_seal_gather_prepared` calls its
code as it was, `vg_aes_gcm_stream_encrypt_prepared_vaes_vpclmul_avx512_core`
(`encFnF`). `streamEncryptF48ZPlain` if the emitter's check fails. -/
def streamEncryptF48Z : Registration Spec.Gcm.streamEncryptPreparedApi X86_64.target :=
  if h : StreamChkF48Z then
    RScrub.withScrubResCRH streamEncryptF48ZPlain (streamEncryptPreparedOut _) [] [2608]
      (streamEncryptF48W_resOk variant.impl blkRZ blkBZ (variant.impl.gh.free.get rfl) (variant.impl.ctr.free.get rfl)
        blkBZ_leaves blkRZ_leaves ⟨variant.impl.ctr.nosp, h.1⟩ ⟨variant.impl.gh.nosp, h.2.1⟩ h.2.2.1 h.2.2.2.1)
      [] scratchRegs (VecLock.regsOk_of_vec streamEncryptF48ZPlain.verified.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1)
      (hregsOk_of_step streamEncryptF48ZPlain.verified.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2)
  else streamEncryptF48ZPlain.registration

/-- `streamEncryptF48ZPlain` for `vg_aes_gcm_stream_decrypt_prepared`. -/
def streamDecryptF48ZPlain : Unscrubbed Spec.Gcm.streamDecryptPreparedApi X86_64.target where
  suffix := variant.impl.suffix
  code := streamDecryptCodeF48W variant.impl blkRZ blkBZ
  stack := 2608
  verified := VG.Proof.AesGcm.Flag.streamDecrypt_keyed (Flag.streamDecrypt_onFlag
    (streamDecryptClr48_framed .avx variant.impl blkRZ)
    (streamDecryptClrB_framed .avx variant.impl blkBZ))
  spSafe := VG.X86_64.onFlag_spSafe (streamDecryptClr_spSafe .avx variant.impl blkRZ)
    (streamDecryptClr_spSafe .avx variant.impl blkBZ)

/-- `StreamChkF48Z` for `vg_aes_gcm_stream_decrypt_prepared_vaes_vpclmul_avx512`. -/
def StreamChkF48ZD : Prop :=
  UpperLock.inames variant.impl.callees.ctr.code = [] ∧ UpperLock.inames variant.impl.callees.gh.code = [] ∧
    UpperLock.inames blkBZ.dec.code = [] ∧ UpperLock.inames blkRZ.dec.code = [] ∧
    UpperLock.inames streamDecryptF48ZPlain.code = [] ∧
    VecLock.step .avx streamDecryptF48ZPlain.code (true, true) = (true, true) ∧
    HLock.step streamDecryptF48ZPlain.code true = true

instance : Decidable StreamChkF48ZD := by unfold StreamChkF48ZD; infer_instance

/-- `streamEncryptF48Z` for `vg_aes_gcm_stream_decrypt_prepared`. -/
def streamDecryptF48Z : Registration Spec.Gcm.streamDecryptPreparedApi X86_64.target :=
  if h : StreamChkF48ZD then
    RScrub.withScrubResCRH streamDecryptF48ZPlain (streamDecryptPreparedOut _) [] [2608]
      (streamDecryptF48W_resOk variant.impl blkRZ blkBZ (variant.impl.gh.free.get rfl) (variant.impl.ctr.free.get rfl)
        blkBZ_leavesD blkRZ_leavesD ⟨variant.impl.ctr.nosp, h.1⟩ ⟨variant.impl.gh.nosp, h.2.1⟩ h.2.2.1 h.2.2.2.1)
      [] scratchRegs (VecLock.regsOk_of_vec streamDecryptF48ZPlain.verified.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1)
      (hregsOk_of_step streamDecryptF48ZPlain.verified.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2)
  else streamDecryptF48ZPlain.registration

end Avx512R

/-- `vg_aes_gcm_stream_encrypt_prepared` of a variant whose loops read the 48
prepared powers: `streamEncryptF48Z` for the function of the AVX-512
variant's name, and otherwise by the flag, its code on the powers or on the
key context. -/
def streamEncryptF48Reg (v : GcmVariant) : Registration Spec.Gcm.streamEncryptPreparedApi X86_64.target :=
  if v.impl.suffix = VG.Proof.Variants.AesGcm.X86_64.VaesVpclmulAvx512.variant.impl.suffix then streamEncryptF48Z
  else {
    suffix := v.impl.suffix
    code := streamEncryptCodeF v
    verified := .unscrubbed (VG.Proof.AesGcm.Flag.streamEncrypt_keyed
      (Flag.streamEncrypt_ofB (Or.inr rfl) (streamEncryptCodeF_verified v)))
    spSafe := streamEncryptCodeF_spAll v }

/-- `streamEncryptF48Reg` for `vg_aes_gcm_stream_decrypt_prepared`. -/
def streamDecryptR48Reg (v : GcmVariant) : Registration Spec.Gcm.streamDecryptPreparedApi X86_64.target :=
  if v.impl.suffix = VG.Proof.Variants.AesGcm.X86_64.VaesVpclmulAvx512.variant.impl.suffix then streamDecryptF48Z
  else {
    suffix := v.impl.suffix
    code := Impl.Gcm.X86_64.Flag.onFlag 48
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamDecrypt (v.impl.withBlk (blkR v))))
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt v.impl.callees))
    verified := .unscrubbed (VG.Proof.AesGcm.Flag.streamDecrypt_keyed (Flag.streamDecrypt_onFlag
      (streamDecryptPrepared_framed v.impl (blkR v))
      (streamDecrypt_framed v.impl)))
    spSafe := VG.X86_64.onFlag_spSafe
      (X86_64.withStackArgScratch_spSafe (streamDecryptM_spSafe v.impl (blkR v)))
      (X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl)) }


/-! ## The streaming functions over callees that need working space

`vg_ghash` and `vg_aes_ctr32` of the baseline implementations write secrets
in their working space, at `W + 512`. The streaming functions of the variants
that call them call `vg_ghash_w` and `vg_aes_ctr32_w` instead, which zero it
before they return (`GhashImpl.wipe`, `Ctr32Impl.wipe`), and whole-blocks
functions that zero the working space they give those callees before they
return (`BlkFn.wipeS`). -/

open Gcm.X86_64.Stitch (CtxMode)

/-- `c`, as `vg_aes_ctr32_w` (`Ctr32Impl.wipe`), if it needs working space and
never writes `r9`, which the emitter checks. -/
def ctrS (c : VG.Proof.Aes.X86_64.Ctr32Impl) : VG.Proof.Aes.X86_64.Ctr32Impl :=
  match c.free, c.small with
  | none, some f => if h : ∀ i ∈ instrs c.callee.code, Taint.clobbers i .r9 = false then c.wipe h f else c
  | _, _ => c

/-- `g`, as `vg_ghash_w` (`GhashImpl.wipe`), if it needs working space and
never writes `r8`, which the emitter checks. -/
def ghS (g : GhashImpl) : GhashImpl :=
  match g.free with
  | none => if h : ∀ i ∈ instrs g.fn.code, Taint.clobbers i .r8 = false then g.wipe h else g
  | some _ => g

/-- `i`, its callees that need working space zeroing it (`ctrS`, `ghS`). -/
def GcmImpl.wipeS (i : GcmImpl) : GcmImpl := { i with ctr := ctrS i.ctr, gh := ghS i.gh }

/-- The bytes of the callees' working space the whole blocks of `i` zero:
1480 with `vg_aes_ctr32`'s, the more, else 256. -/
def blkWipeN (i : GcmImpl) : Nat := if i.ctr.free.isNone then 1480 else 256

theorem blkWipeN_le (i : GcmImpl) : 64 + blkWipeN i ≤ 2112 := by unfold blkWipeN; split <;> decide

theorem blkWipeN_16 (i : GcmImpl) : blkWipeN i % 16 = 0 ∨ 16 ≤ blkWipeN i := by
  unfold blkWipeN; split <;> decide

/-- `i`'s whole blocks, zeroing their callees' working space (`BlkFn.wipeS`). -/
def blkS (i : GcmImpl) : BlkFn CtxMode.base := i.blkB.wipeS (blkWipeN i) (blkWipeN_le i) (blkWipeN_16 i)

/-- `vg_aes_gcm_stream_encrypt_prepared` of a variant whose callees need working
space: over `GcmImpl.wipeS` and `blkS`, clearing the registers after each
call (`streamEncryptClr`, at the level of SSE). -/
def streamEncryptWSPlain (v : GcmVariant) : Registration Spec.Gcm.streamEncryptPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
    (Impl.AesGcm.X86_64.streamEncryptClr (v.impl.wipeS.withBlk (blkS v.impl)) .sse)
  stack := 2608
  verified := .unscrubbed (VG.Proof.AesGcm.Flag.streamEncrypt_keyed
    (Flag.streamEncrypt_of_base (streamEncryptClrB_framed .sse v.impl.wipeS (blkS v.impl))))
  spSafe := streamEncryptClr_spSafe .sse v.impl.wipeS (blkS v.impl)

/-- `streamEncryptWSPlain` for `vg_aes_gcm_stream_decrypt_prepared`. -/
def streamDecryptWSPlain (v : GcmVariant) : Registration Spec.Gcm.streamDecryptPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
    (Impl.AesGcm.X86_64.streamDecryptClr (v.impl.wipeS.withBlk (blkS v.impl)) .sse)
  stack := 2608
  verified := .unscrubbed (VG.Proof.AesGcm.Flag.streamDecrypt_keyed
    (Flag.streamDecrypt_of_base (streamDecryptClrB_framed .sse v.impl.wipeS (blkS v.impl))))
  spSafe := streamDecryptClr_spSafe .sse v.impl.wipeS (blkS v.impl)


/-! ## `vg_aes_gcm_stream_{en,de}crypt_prepared_pclmul`, without secret residue

Over `vg_aes_ctr32_w`, which zeroes the 1480 bytes of its working space at
`W + 512` before it returns, and whole blocks that zero those bytes of
theirs: the frame is what `streamFVZ` says, zero there on the paths that
called it, as on entry on the others. -/

/-- The variant on PCLMULQDQ alone. -/
def pclmulV : GcmVariant := ⟨.scalar, .scalar, .pclmul, none⟩

theorem blkWipeN_pclmul : blkWipeN pclmulV.impl = 1480 := rfl

theorem blkS_pclmul_leaves (f : VG.Proof.Aes.X86_64.Ctr32Small pclmulV.impl.ctr.callee)
    (gf : GhashFree pclmulV.impl.gh.fn.code) : BlkLeaves (blkS pclmulV.impl) :=
  BlkFn.wipeS_leaves (blkWipeN pclmulV.impl) _ _ pclmulV.impl.blkB (Wn := zw 64 1544)
    (fun d h => by rw [blkWipeN_pclmul]; simp [zw] at h; omega) fun s hpre => by
    change WP isa (Impl.AesGcm.X86_64.Blocks.encrypt
      ⟨pclmulV.impl.ctr.callee.name, pclmulV.impl.ctr.callee.code⟩ pclmulV.impl.gh.fn none) s _
    exact Blocks.encryptS_leaves (Blocks.BP.ofM hpre) _ _ (by decide) (by decide) (CtrW.small pclmulV.impl.ctr f)
      (Blocks.GhW.free pclmulV.impl.gh gf) fun d h1 h2 => by simp [zw]; omega

theorem blkS_pclmul_leavesD (f : VG.Proof.Aes.X86_64.Ctr32Small pclmulV.impl.ctr.callee)
    (gf : GhashFree pclmulV.impl.gh.fn.code) : BlkLeavesD (blkS pclmulV.impl) :=
  BlkFn.wipeS_leavesD (blkWipeN pclmulV.impl) _ _ pclmulV.impl.blkB (Wn := zw 64 1544)
    (fun d h => by rw [blkWipeN_pclmul]; simp [zw] at h; omega) fun s hpre => by
    change WP isa (Impl.AesGcm.X86_64.Blocks.decrypt
      ⟨pclmulV.impl.ctr.callee.name, pclmulV.impl.ctr.callee.code⟩ pclmulV.impl.gh.fn none) s _
    exact Blocks.decryptS_leaves (Blocks.BP.ofM hpre) _ _ (by decide) (by decide) (CtrW.small pclmulV.impl.ctr f)
      (Blocks.GhW.free pclmulV.impl.gh gf) fun d h1 h2 => by simp [zw]; omega

/-- `pclmulV`'s implementation over `vg_aes_ctr32_w`. -/
def pclmulW (f : VG.Proof.Aes.X86_64.Ctr32Small pclmulV.impl.ctr.callee)
    (h9 : ∀ i ∈ instrs pclmulV.impl.ctr.callee.code, Taint.clobbers i .r9 = false) : GcmImpl :=
  { pclmulV.impl with ctr := pclmulV.impl.ctr.wipe h9 f }

theorem pclmulW_crCallZ (f : VG.Proof.Aes.X86_64.Ctr32Small pclmulV.impl.ctr.callee)
    (h9 : ∀ i ∈ instrs pclmulV.impl.ctr.callee.code, Taint.clobbers i .r9 = false) :
    CrCallZ ((pclmulW f h9).wrapC .sse) 1480 (zw 512 1992) :=
  crCallZ_wipeC .sse _ (c₀ := pclmulV.impl.ctr.callee.code) rfl h9 ((f.wipe h9).wrapC .sse)

open StackLock in
theorem streamEncryptWZ_resOk (v : GcmImpl) (B : BlkFn CtxMode.base) {zg : Nat → Bool} (GZ : GhCallZ (v.wrapC .sse) zg)
    {sc : Nat}
    {z : Nat → Bool} (hsc : sc ≤ 2048) (CZ : CrCallZ (v.wrapC .sse) sc z) (hB : BlkLeaves B)
    (hct : Plain v.callees.ctr.code) (hgh : Plain v.callees.gh.code) (hn : UpperLock.inames B.enc.code = []) :
    ResOk (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr (v.withBlk B) .sse))
      (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608) 2608 [] [2608] := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho hu hsy e₁ e₂ x hx _
  have h₁' := h₁
  unfold Spec.Gcm.streamEncryptPreparedContract at h₁'
  exact streamEncBZ_agree .sse v B GZ hsc CZ hB hct hgh hn h₁ h₂ hp (fun r h => ho.2.2.1 r h)
    (below_same h₁' ho (by decide)) hu hsy e₁ e₂ x hx

open StackLock in
theorem streamDecryptWZ_resOk (v : GcmImpl) (B : BlkFn CtxMode.base) {zg : Nat → Bool} (GZ : GhCallZ (v.wrapC .sse) zg)
    {sc : Nat}
    {z : Nat → Bool} (hsc : sc ≤ 2048) (CZ : CrCallZ (v.wrapC .sse) sc z) (hB : BlkLeavesD B)
    (hct : Plain v.callees.ctr.code) (hgh : Plain v.callees.gh.code) (hn : UpperLock.inames B.dec.code = []) :
    ResOk (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecryptClr (v.withBlk B) .sse))
      (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608) 2608 [] [2608] := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho hu hsy e₁ e₂ x hx _
  have h₁' := h₁
  unfold Spec.Gcm.streamDecryptPreparedContract at h₁'
  exact streamDecBZ_agree .sse v B GZ hsc CZ hB hct hgh hn h₁ h₂ hp (fun r h => ho.2.2.1 r h)
    (below_same h₁' ho (by decide)) hu hsy e₁ e₂ x hx

/-- `StreamChk` over the callees of `v`. -/
def StreamChkV (v : GcmImpl) (c : Prog isa) (b : Prog isa) : Prop :=
  UpperLock.inames v.callees.ctr.code = [] ∧ UpperLock.inames v.callees.gh.code = [] ∧
    UpperLock.inames b = [] ∧ UpperLock.inames c = [] ∧ VecLock.step .sse c (true, true) = (true, true)

instance (v : GcmImpl) (c b : Prog isa) : Decidable (StreamChkV v c b) := by unfold StreamChkV; infer_instance

/-- `vg_aes_gcm_stream_encrypt_prepared_pclmul` over `pclmulW`, before any
clearing on return. -/
def streamEncryptPclmulPlain (f : VG.Proof.Aes.X86_64.Ctr32Small pclmulV.impl.ctr.callee)
    (h9 : ∀ i ∈ instrs pclmulV.impl.ctr.callee.code, Taint.clobbers i .r9 = false) :
    Unscrubbed Spec.Gcm.streamEncryptPreparedApi X86_64.target where
  suffix := pclmulV.impl.suffix
  code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
    (Impl.AesGcm.X86_64.streamEncryptClr ((pclmulW f h9).withBlk (blkS pclmulV.impl)) .sse)
  stack := 2608
  verified := VG.Proof.AesGcm.Flag.streamEncrypt_keyed
    (Flag.streamEncrypt_of_base (streamEncryptClrB_framed .sse (pclmulW f h9) (blkS pclmulV.impl)))
  spSafe := streamEncryptClr_spSafe .sse (pclmulW f h9) (blkS pclmulV.impl)

/-- `streamEncryptPclmulPlain` for `vg_aes_gcm_stream_decrypt_prepared_pclmul`. -/
def streamDecryptPclmulPlain (f : VG.Proof.Aes.X86_64.Ctr32Small pclmulV.impl.ctr.callee)
    (h9 : ∀ i ∈ instrs pclmulV.impl.ctr.callee.code, Taint.clobbers i .r9 = false) :
    Unscrubbed Spec.Gcm.streamDecryptPreparedApi X86_64.target where
  suffix := pclmulV.impl.suffix
  code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
    (Impl.AesGcm.X86_64.streamDecryptClr ((pclmulW f h9).withBlk (blkS pclmulV.impl)) .sse)
  stack := 2608
  verified := VG.Proof.AesGcm.Flag.streamDecrypt_keyed
    (Flag.streamDecrypt_of_base (streamDecryptClrB_framed .sse (pclmulW f h9) (blkS pclmulV.impl)))
  spSafe := streamDecryptClr_spSafe .sse (pclmulW f h9) (blkS pclmulV.impl)

open VG.X86_64.Scrub StackLock in
/-- `vg_aes_gcm_stream_encrypt_prepared_pclmul`, followed by the clearing of
the scratch registers only (`withScrubResCR`): it leaves the same stack in two
runs (`streamEncryptWZ_resOk`), and the vector registers agree
(`VecLock.regsOk_of_vec`). `streamEncryptWSPlain` if the emitter's checks fail. -/
def streamEncryptWPclmul : Registration Spec.Gcm.streamEncryptPreparedApi X86_64.target :=
  match pclmulV.impl.ctr.small, pclmulV.impl.gh.free with
  | some f, some gf =>
    if h9 : ∀ i ∈ instrs pclmulV.impl.ctr.callee.code, Taint.clobbers i .r9 = false then
      if h : StreamChkV (pclmulW f h9) (streamEncryptPclmulPlain f h9).code (blkS pclmulV.impl).enc.code then
        RScrub.withScrubResCR (streamEncryptPclmulPlain f h9) (streamEncryptPreparedOut _) [] [2608]
          (streamEncryptWZ_resOk (pclmulW f h9) (blkS pclmulV.impl)
            (ghCallZ_free _ (gf.wrapC .sse)) (by decide) (pclmulW_crCallZ f h9)
            (blkS_pclmul_leaves f gf) ⟨(pclmulW f h9).ctr.nosp, h.1⟩ ⟨(pclmulW f h9).gh.nosp, h.2.1⟩ h.2.2.1)
          [] scratchRegs (VecLock.regsOk_of_vec (streamEncryptPclmulPlain f h9).verified.2.1 h.2.2.2.1 h.2.2.2.2)
      else (streamEncryptPclmulPlain f h9).registration
    else streamEncryptWSPlain pclmulV
  | _, _ => streamEncryptWSPlain pclmulV

open VG.X86_64.Scrub StackLock in
/-- `streamEncryptWPclmul` for `vg_aes_gcm_stream_decrypt_prepared_pclmul`. -/
def streamDecryptWPclmul : Registration Spec.Gcm.streamDecryptPreparedApi X86_64.target :=
  match pclmulV.impl.ctr.small, pclmulV.impl.gh.free with
  | some f, some gf =>
    if h9 : ∀ i ∈ instrs pclmulV.impl.ctr.callee.code, Taint.clobbers i .r9 = false then
      if h : StreamChkV (pclmulW f h9) (streamDecryptPclmulPlain f h9).code (blkS pclmulV.impl).dec.code then
        RScrub.withScrubResCR (streamDecryptPclmulPlain f h9) (streamDecryptPreparedOut _) [] [2608]
          (streamDecryptWZ_resOk (pclmulW f h9) (blkS pclmulV.impl)
            (ghCallZ_free _ (gf.wrapC .sse)) (by decide) (pclmulW_crCallZ f h9)
            (blkS_pclmul_leavesD f gf) ⟨(pclmulW f h9).ctr.nosp, h.1⟩ ⟨(pclmulW f h9).gh.nosp, h.2.1⟩ h.2.2.1)
          [] scratchRegs (VecLock.regsOk_of_vec (streamDecryptPclmulPlain f h9).verified.2.1 h.2.2.2.1 h.2.2.2.2)
      else (streamDecryptPclmulPlain f h9).registration
    else streamDecryptWSPlain pclmulV
  | _, _ => streamDecryptWSPlain pclmulV

/-! ## `vg_aes_gcm_stream_{en,de}crypt_prepared_aesni` and `vg_aes_gcm_stream_{en,de}crypt_prepared`, without secret residue

As the `_pclmul` functions, over `vg_ghash_w` too, which zeroes the 256 bytes
of its working space at `W + 512` before it returns, and whole blocks that
zero those of theirs. -/

/-- The variant on AES-NI alone. -/
def aesNiV : GcmVariant := ⟨.aesni, .aesni, .scalar, none⟩

/-- The variant on the baseline instruction set. -/
def scalarV : GcmVariant := ⟨.scalar, .scalar, .scalar, none⟩

theorem blkWipeN_aesNi : blkWipeN aesNiV.impl = 256 := rfl

theorem blkWipeN_scalar : blkWipeN scalarV.impl = 1480 := rfl

theorem blkS_aesNi_leaves (cf : VG.Proof.Aes.X86_64.Ctr32Free aesNiV.impl.ctr.callee) :
    BlkLeaves (blkS aesNiV.impl) :=
  BlkFn.wipeS_leaves (blkWipeN aesNiV.impl) _ _ aesNiV.impl.blkB (Wn := zw 64 320)
    (fun d h => by rw [blkWipeN_aesNi]; simp [zw] at h; omega) fun s hpre => by
    change WP isa (Impl.AesGcm.X86_64.Blocks.encrypt
      ⟨aesNiV.impl.ctr.callee.name, aesNiV.impl.ctr.callee.code⟩ aesNiV.impl.gh.fn none) s _
    exact Blocks.encryptS_leaves (Blocks.BP.ofM hpre) _ _ (by decide) (by decide) (Blocks.CtrW.free aesNiV.impl.ctr cf)
      (Blocks.GhW.base aesNiV.impl.gh) fun d h1 h2 => by simp [zw]; omega

theorem blkS_aesNi_leavesD (cf : VG.Proof.Aes.X86_64.Ctr32Free aesNiV.impl.ctr.callee) :
    BlkLeavesD (blkS aesNiV.impl) :=
  BlkFn.wipeS_leavesD (blkWipeN aesNiV.impl) _ _ aesNiV.impl.blkB (Wn := zw 64 320)
    (fun d h => by rw [blkWipeN_aesNi]; simp [zw] at h; omega) fun s hpre => by
    change WP isa (Impl.AesGcm.X86_64.Blocks.decrypt
      ⟨aesNiV.impl.ctr.callee.name, aesNiV.impl.ctr.callee.code⟩ aesNiV.impl.gh.fn none) s _
    exact Blocks.decryptS_leaves (Blocks.BP.ofM hpre) _ _ (by decide) (by decide) (Blocks.CtrW.free aesNiV.impl.ctr cf)
      (Blocks.GhW.base aesNiV.impl.gh) fun d h1 h2 => by simp [zw]; omega

theorem blkS_scalar_leaves (f : VG.Proof.Aes.X86_64.Ctr32Small scalarV.impl.ctr.callee) :
    BlkLeaves (blkS scalarV.impl) :=
  BlkFn.wipeS_leaves (blkWipeN scalarV.impl) _ _ scalarV.impl.blkB (Wn := zw 64 1544)
    (fun d h => by rw [blkWipeN_scalar]; simp [zw] at h; omega) fun s hpre => by
    change WP isa (Impl.AesGcm.X86_64.Blocks.encrypt
      ⟨scalarV.impl.ctr.callee.name, scalarV.impl.ctr.callee.code⟩ scalarV.impl.gh.fn none) s _
    exact Blocks.encryptS_leaves (Blocks.BP.ofM hpre) _ _ (by decide) (by decide) (CtrW.small scalarV.impl.ctr f)
      (Blocks.GhW.base scalarV.impl.gh) fun d h1 h2 => by simp [zw]; omega

theorem blkS_scalar_leavesD (f : VG.Proof.Aes.X86_64.Ctr32Small scalarV.impl.ctr.callee) :
    BlkLeavesD (blkS scalarV.impl) :=
  BlkFn.wipeS_leavesD (blkWipeN scalarV.impl) _ _ scalarV.impl.blkB (Wn := zw 64 1544)
    (fun d h => by rw [blkWipeN_scalar]; simp [zw] at h; omega) fun s hpre => by
    change WP isa (Impl.AesGcm.X86_64.Blocks.decrypt
      ⟨scalarV.impl.ctr.callee.name, scalarV.impl.ctr.callee.code⟩ scalarV.impl.gh.fn none) s _
    exact Blocks.decryptS_leaves (Blocks.BP.ofM hpre) _ _ (by decide) (by decide) (CtrW.small scalarV.impl.ctr f)
      (Blocks.GhW.base scalarV.impl.gh) fun d h1 h2 => by simp [zw]; omega

/-- `aesNiV`'s implementation over `vg_ghash_w`. -/
def aesNiW (h8 : ∀ i ∈ instrs aesNiV.impl.gh.fn.code, Taint.clobbers i .r8 = false) : GcmImpl :=
  { aesNiV.impl with gh := aesNiV.impl.gh.wipe h8 }

/-- `scalarV`'s implementation over `vg_aes_ctr32_w` and `vg_ghash_w`. -/
def scalarW (f : VG.Proof.Aes.X86_64.Ctr32Small scalarV.impl.ctr.callee)
    (h9 : ∀ i ∈ instrs scalarV.impl.ctr.callee.code, Taint.clobbers i .r9 = false)
    (h8 : ∀ i ∈ instrs scalarV.impl.gh.fn.code, Taint.clobbers i .r8 = false) : GcmImpl :=
  { scalarV.impl with ctr := scalarV.impl.ctr.wipe h9 f, gh := scalarV.impl.gh.wipe h8 }

/-- `vg_aes_gcm_stream_encrypt_prepared_aesni` over `aesNiW`, before any
clearing on return. -/
def streamEncryptAesNiPlain (h8 : ∀ i ∈ instrs aesNiV.impl.gh.fn.code, Taint.clobbers i .r8 = false) :
    Unscrubbed Spec.Gcm.streamEncryptPreparedApi X86_64.target where
  suffix := aesNiV.impl.suffix
  code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
    (Impl.AesGcm.X86_64.streamEncryptClr ((aesNiW h8).withBlk (blkS aesNiV.impl)) .sse)
  stack := 2608
  verified := VG.Proof.AesGcm.Flag.streamEncrypt_keyed
    (Flag.streamEncrypt_of_base (streamEncryptClrB_framed .sse (aesNiW h8) (blkS aesNiV.impl)))
  spSafe := streamEncryptClr_spSafe .sse (aesNiW h8) (blkS aesNiV.impl)

/-- `streamEncryptAesNiPlain` for `vg_aes_gcm_stream_decrypt_prepared_aesni`. -/
def streamDecryptAesNiPlain (h8 : ∀ i ∈ instrs aesNiV.impl.gh.fn.code, Taint.clobbers i .r8 = false) :
    Unscrubbed Spec.Gcm.streamDecryptPreparedApi X86_64.target where
  suffix := aesNiV.impl.suffix
  code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
    (Impl.AesGcm.X86_64.streamDecryptClr ((aesNiW h8).withBlk (blkS aesNiV.impl)) .sse)
  stack := 2608
  verified := VG.Proof.AesGcm.Flag.streamDecrypt_keyed
    (Flag.streamDecrypt_of_base (streamDecryptClrB_framed .sse (aesNiW h8) (blkS aesNiV.impl)))
  spSafe := streamDecryptClr_spSafe .sse (aesNiW h8) (blkS aesNiV.impl)

/-- `vg_aes_gcm_stream_encrypt_prepared` over `scalarW`, before any clearing
on return. -/
def streamEncryptScalarPlain (f : VG.Proof.Aes.X86_64.Ctr32Small scalarV.impl.ctr.callee)
    (h9 : ∀ i ∈ instrs scalarV.impl.ctr.callee.code, Taint.clobbers i .r9 = false)
    (h8 : ∀ i ∈ instrs scalarV.impl.gh.fn.code, Taint.clobbers i .r8 = false) :
    Unscrubbed Spec.Gcm.streamEncryptPreparedApi X86_64.target where
  suffix := scalarV.impl.suffix
  code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
    (Impl.AesGcm.X86_64.streamEncryptClr ((scalarW f h9 h8).withBlk (blkS scalarV.impl)) .sse)
  stack := 2608
  verified := VG.Proof.AesGcm.Flag.streamEncrypt_keyed
    (Flag.streamEncrypt_of_base (streamEncryptClrB_framed .sse (scalarW f h9 h8) (blkS scalarV.impl)))
  spSafe := streamEncryptClr_spSafe .sse (scalarW f h9 h8) (blkS scalarV.impl)

/-- `streamEncryptScalarPlain` for `vg_aes_gcm_stream_decrypt_prepared`. -/
def streamDecryptScalarPlain (f : VG.Proof.Aes.X86_64.Ctr32Small scalarV.impl.ctr.callee)
    (h9 : ∀ i ∈ instrs scalarV.impl.ctr.callee.code, Taint.clobbers i .r9 = false)
    (h8 : ∀ i ∈ instrs scalarV.impl.gh.fn.code, Taint.clobbers i .r8 = false) :
    Unscrubbed Spec.Gcm.streamDecryptPreparedApi X86_64.target where
  suffix := scalarV.impl.suffix
  code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
    (Impl.AesGcm.X86_64.streamDecryptClr ((scalarW f h9 h8).withBlk (blkS scalarV.impl)) .sse)
  stack := 2608
  verified := VG.Proof.AesGcm.Flag.streamDecrypt_keyed
    (Flag.streamDecrypt_of_base (streamDecryptClrB_framed .sse (scalarW f h9 h8) (blkS scalarV.impl)))
  spSafe := streamDecryptClr_spSafe .sse (scalarW f h9 h8) (blkS scalarV.impl)

open VG.X86_64.Scrub StackLock in
/-- `vg_aes_gcm_stream_encrypt_prepared_aesni`, followed by the clearing of
the scratch registers only, as `streamEncryptWPclmul`. `streamEncryptWSPlain`
if the emitter's checks fail. -/
def streamEncryptWAesNi : Registration Spec.Gcm.streamEncryptPreparedApi X86_64.target :=
  match aesNiV.impl.ctr.free with
  | some cf =>
    if h8 : ∀ i ∈ instrs aesNiV.impl.gh.fn.code, Taint.clobbers i .r8 = false then
      if h : StreamChkV (aesNiW h8) (streamEncryptAesNiPlain h8).code (blkS aesNiV.impl).enc.code then
        RScrub.withScrubResCR (streamEncryptAesNiPlain h8) (streamEncryptPreparedOut _) [] [2608]
          (streamEncryptWZ_resOk (aesNiW h8) (blkS aesNiV.impl)
            (ghCallZ_wipeC .sse _ (c₀ := aesNiV.impl.gh.fn.code) rfl h8) (by decide)
            (crCallZ_free _ (cf.wrapC .sse)) (blkS_aesNi_leaves cf)
            ⟨(aesNiW h8).ctr.nosp, h.1⟩ ⟨(aesNiW h8).gh.nosp, h.2.1⟩ h.2.2.1)
          [] scratchRegs (VecLock.regsOk_of_vec (streamEncryptAesNiPlain h8).verified.2.1 h.2.2.2.1 h.2.2.2.2)
      else (streamEncryptAesNiPlain h8).registration
    else streamEncryptWSPlain aesNiV
  | none => streamEncryptWSPlain aesNiV

open VG.X86_64.Scrub StackLock in
/-- `streamEncryptWAesNi` for `vg_aes_gcm_stream_decrypt_prepared_aesni`. -/
def streamDecryptWAesNi : Registration Spec.Gcm.streamDecryptPreparedApi X86_64.target :=
  match aesNiV.impl.ctr.free with
  | some cf =>
    if h8 : ∀ i ∈ instrs aesNiV.impl.gh.fn.code, Taint.clobbers i .r8 = false then
      if h : StreamChkV (aesNiW h8) (streamDecryptAesNiPlain h8).code (blkS aesNiV.impl).dec.code then
        RScrub.withScrubResCR (streamDecryptAesNiPlain h8) (streamDecryptPreparedOut _) [] [2608]
          (streamDecryptWZ_resOk (aesNiW h8) (blkS aesNiV.impl)
            (ghCallZ_wipeC .sse _ (c₀ := aesNiV.impl.gh.fn.code) rfl h8) (by decide)
            (crCallZ_free _ (cf.wrapC .sse)) (blkS_aesNi_leavesD cf)
            ⟨(aesNiW h8).ctr.nosp, h.1⟩ ⟨(aesNiW h8).gh.nosp, h.2.1⟩ h.2.2.1)
          [] scratchRegs (VecLock.regsOk_of_vec (streamDecryptAesNiPlain h8).verified.2.1 h.2.2.2.1 h.2.2.2.2)
      else (streamDecryptAesNiPlain h8).registration
    else streamDecryptWSPlain aesNiV
  | none => streamDecryptWSPlain aesNiV

open VG.X86_64.Scrub StackLock in
/-- `vg_aes_gcm_stream_encrypt_prepared`, followed by the clearing of the
scratch registers only, as `streamEncryptWPclmul`. `streamEncryptWSPlain` if
the emitter's checks fail. -/
def streamEncryptWScalar : Registration Spec.Gcm.streamEncryptPreparedApi X86_64.target :=
  match scalarV.impl.ctr.small with
  | some f =>
    if h9 : ∀ i ∈ instrs scalarV.impl.ctr.callee.code, Taint.clobbers i .r9 = false then
      if h8 : ∀ i ∈ instrs scalarV.impl.gh.fn.code, Taint.clobbers i .r8 = false then
        if h : StreamChkV (scalarW f h9 h8) (streamEncryptScalarPlain f h9 h8).code (blkS scalarV.impl).enc.code then
          RScrub.withScrubResCR (streamEncryptScalarPlain f h9 h8) (streamEncryptPreparedOut _) [] [2608]
            (streamEncryptWZ_resOk (scalarW f h9 h8) (blkS scalarV.impl)
              (ghCallZ_wipeC .sse _ (c₀ := scalarV.impl.gh.fn.code) rfl h8) (by decide)
              (crCallZ_wipeC .sse _ (c₀ := scalarV.impl.ctr.callee.code) rfl h9 ((f.wipe h9).wrapC .sse))
              (blkS_scalar_leaves f) ⟨(scalarW f h9 h8).ctr.nosp, h.1⟩ ⟨(scalarW f h9 h8).gh.nosp, h.2.1⟩ h.2.2.1)
            [] scratchRegs
            (VecLock.regsOk_of_vec (streamEncryptScalarPlain f h9 h8).verified.2.1 h.2.2.2.1 h.2.2.2.2)
        else (streamEncryptScalarPlain f h9 h8).registration
      else streamEncryptWSPlain scalarV
    else streamEncryptWSPlain scalarV
  | none => streamEncryptWSPlain scalarV

open VG.X86_64.Scrub StackLock in
/-- `streamEncryptWScalar` for `vg_aes_gcm_stream_decrypt_prepared`. -/
def streamDecryptWScalar : Registration Spec.Gcm.streamDecryptPreparedApi X86_64.target :=
  match scalarV.impl.ctr.small with
  | some f =>
    if h9 : ∀ i ∈ instrs scalarV.impl.ctr.callee.code, Taint.clobbers i .r9 = false then
      if h8 : ∀ i ∈ instrs scalarV.impl.gh.fn.code, Taint.clobbers i .r8 = false then
        if h : StreamChkV (scalarW f h9 h8) (streamDecryptScalarPlain f h9 h8).code (blkS scalarV.impl).dec.code then
          RScrub.withScrubResCR (streamDecryptScalarPlain f h9 h8) (streamDecryptPreparedOut _) [] [2608]
            (streamDecryptWZ_resOk (scalarW f h9 h8) (blkS scalarV.impl)
              (ghCallZ_wipeC .sse _ (c₀ := scalarV.impl.gh.fn.code) rfl h8) (by decide)
              (crCallZ_wipeC .sse _ (c₀ := scalarV.impl.ctr.callee.code) rfl h9 ((f.wipe h9).wrapC .sse))
              (blkS_scalar_leavesD f) ⟨(scalarW f h9 h8).ctr.nosp, h.1⟩ ⟨(scalarW f h9 h8).gh.nosp, h.2.1⟩ h.2.2.1)
            [] scratchRegs
            (VecLock.regsOk_of_vec (streamDecryptScalarPlain f h9 h8).verified.2.1 h.2.2.2.1 h.2.2.2.2)
        else (streamDecryptScalarPlain f h9 h8).registration
      else streamDecryptWSPlain scalarV
    else streamDecryptWSPlain scalarV
  | none => streamDecryptWSPlain scalarV

/-- `vg_aes_gcm_stream_encrypt_prepared` of a variant whose loops read 16
powers: `streamEncryptF16Vaes` for the function of the VAES variant's name,
`streamEncryptF16Avx` for that of the AVX variant, and
`streamEncryptF16Plain` for the others. -/
def streamEncryptF16Reg (v : GcmVariant) : Registration Spec.Gcm.streamEncryptPreparedApi X86_64.target :=
  if v.impl.suffix = VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.suffix then streamEncryptF16Vaes
  else if v.impl.suffix = VG.Proof.Variants.AesGcm.X86_64.AesNiPclmulAvx.variant.impl.suffix then streamEncryptF16Avx
  else (streamEncryptF16Plain v).registration

/-- `vg_aes_gcm_stream_encrypt_prepared` of a variant whose loops read only
the key context: for the variant on AES-NI and PCLMULQDQ, whose callees never
touch the stack, the code that clears the registers after each call
(`streamEncryptClr`, at the level of SSE); for the others, the same code over
callees that zero their working space, with the scratch registers cleared on
return (`streamEncryptWPclmul`, `streamEncryptWAesNi`, `streamEncryptWScalar`,
or `streamEncryptWSPlain` for any other). -/
def streamEncryptWReg (v : GcmVariant) : Registration Spec.Gcm.streamEncryptPreparedApi X86_64.target :=
  if v.impl.suffix = aesNiPclmulV.impl.suffix then streamEncryptWAesniPclmul
  else if v.impl.suffix = pclmulV.impl.suffix then streamEncryptWPclmul
  else if v.impl.suffix = aesNiV.impl.suffix then streamEncryptWAesNi
  else if v.impl.suffix = scalarV.impl.suffix then streamEncryptWScalar
  else streamEncryptWSPlain v

/-- `vg_aes_gcm_stream_decrypt_prepared` of a variant whose loops read only
the key context, as `streamEncryptWReg`. -/
def streamDecryptWReg (v : GcmVariant) : Registration Spec.Gcm.streamDecryptPreparedApi X86_64.target :=
  if v.impl.suffix = aesNiPclmulV.impl.suffix then streamDecryptWAesniPclmul
  else if v.impl.suffix = pclmulV.impl.suffix then streamDecryptWPclmul
  else if v.impl.suffix = aesNiV.impl.suffix then streamDecryptWAesNi
  else if v.impl.suffix = scalarV.impl.suffix then streamDecryptWScalar
  else streamDecryptWSPlain v

/-- `vg_aes_gcm_stream_decrypt_prepared` of a variant whose loops read 16
powers, clearing the registers after each call (`streamDecryptCodeF16C`),
before any clearing on return. -/
def streamDecryptF16Plain (v : GcmVariant) : Unscrubbed Spec.Gcm.streamDecryptPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := streamDecryptCodeF16C v
  stack := 2608
  verified := VG.Proof.AesGcm.Flag.streamDecrypt_keyed (Flag.streamDecrypt_onFlag16
    (streamDecryptClr16_framed .avx v.impl (blkR16 v))
    (streamDecryptClrB_framed .avx v.impl v.impl.blkB))
  spSafe := VG.X86_64.onFlag_spSafe (streamDecryptClr_spSafe .avx v.impl (blkR16 v))
    (streamDecryptClr_spSafe .avx v.impl v.impl.blkB)

open VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul (variant) in
/-- What the clearing of only the general-purpose registers needs of
`vg_aes_gcm_stream_decrypt_prepared_vaes_vpclmul`, checked by the emitter
(as `StreamChkF16`). -/
def StreamChkF16D : Prop :=
  UpperLock.inames variant.impl.callees.ctr.code = [] ∧ UpperLock.inames variant.impl.callees.gh.code = [] ∧
    UpperLock.inames variant.impl.blkB.dec.code = [] ∧ UpperLock.inames (blkR16 variant).dec.code = [] ∧
    UpperLock.inames (streamDecryptCodeF16C variant) = [] ∧
    VecLock.step .avx (streamDecryptCodeF16C variant) (true, true) = (true, true)

instance : Decidable StreamChkF16D := by unfold StreamChkF16D; infer_instance

open VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul (variant) in
open VG.X86_64.Scrub StackLock in
/-- `vg_aes_gcm_stream_decrypt_prepared_vaes_vpclmul`, followed by the
clearing of the scratch registers only (`withScrubResCR`): it leaves the
same stack in two runs (`streamDecryptF16_resOk`), and the vector registers
it leaves agree (`VecLock.regsOk_of_vec`). `streamDecryptF16Plain` if the
emitter's check fails. -/
def streamDecryptF16Vaes : Registration Spec.Gcm.streamDecryptPreparedApi X86_64.target :=
  if h : StreamChkF16D then
    RScrub.withScrubResCR (streamDecryptF16Plain variant) (streamDecryptPreparedOut _) [] [2608]
      (streamDecryptF16_resOk variant (variant.impl.gh.free.get rfl) (variant.impl.ctr.free.get rfl)
        blkBD_vaes_leaves blkR16D_vaes_leaves ⟨variant.impl.ctr.nosp, h.1⟩ ⟨variant.impl.gh.nosp, h.2.1⟩
        h.2.2.1 h.2.2.2.1)
      [] scratchRegs (VecLock.regsOk_of_vec (streamDecryptF16Plain variant).verified.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
  else (streamDecryptF16Plain variant).registration

/-- `vg_aes_gcm_stream_decrypt_prepared` of a variant whose loops read 16
powers: by the count, its code on them or its code on the key context; where
`GcmVariant.streamF16Clr` says so, both clearing the registers after each
call (`streamDecryptCodeF16C`), and for the function of the VAES variant's
name, returning without secret residue (`streamDecryptF16Vaes`); for the
function of the AVX variant's name, `streamDecryptF16Avx`. -/
def streamDecryptR16Reg (v : GcmVariant) : Registration Spec.Gcm.streamDecryptPreparedApi X86_64.target :=
  if v.streamF16Clr then
    if v.impl.suffix = VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant.impl.suffix then streamDecryptF16Vaes
    else (streamDecryptF16Plain v).registration
  else if v.impl.suffix = VG.Proof.Variants.AesGcm.X86_64.AesNiPclmulAvx.variant.impl.suffix then streamDecryptF16Avx
  else {
    suffix := v.impl.suffix
    code := Impl.Gcm.X86_64.Flag.onFlag 16
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamDecrypt (v.impl.withBlk (blkR16 v))))
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt v.impl.callees))
    verified := .unscrubbed (VG.Proof.AesGcm.Flag.streamDecrypt_keyed (Flag.streamDecrypt_onFlag16
      (streamDecryptPrepared16_framed v.impl (blkR16 v))
      (streamDecrypt_framed v.impl)))
    spSafe := VG.X86_64.onFlag_spSafe
      (X86_64.withStackArgScratch_spSafe (streamDecryptM_spSafe v.impl (blkR16 v)))
      (X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl)) }

/-! ## `vg_aes_gcm_open_prepared_aesni_pclmul` -/

theorem openCode_aesniPclmul :
    aesNiPclmulV.impl.openCode aesNiPclmulV.impl.callees = Impl.AesGcm.X86_64.«open» aesNiPclmulV.impl.callees := by
  have hs : aesNiPclmulV.impl.short = false := rfl
  unfold GcmImpl.openCode
  simp only [hs, Bool.false_eq_true, ↓reduceIte]

/-- The code of `vg_aes_gcm_open_prepared_aesni_pclmul` (inside
`withStackArgScratch 2616 4`): what it leaves in its return address, its
stack arguments and `work` (`[rsp + 40]`), byte by byte (`openV`). -/
theorem open_aesniPclmul_leaves :
    ∃ Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
        Option (BitVec 8),
      ∀ s t s', (Proof.AesGcm.openX86_64M Gcm.X86_64.Stitch.CtxMode.base).pre s →
        Exec isa (aesNiPclmulV.impl.openCode aesNiPclmulV.impl.callees) s t s' →
        ∀ x, openQ (s.gpr .rsp) (stackArg s 4) x →
          s'.mem x = (openV Lb (fun _ => none) s.gpr (fun i => stackArg s i) (s.gpr .rsp)
            (stackArg s 4) x).getD (s.mem x) := by
  rw [openCode_aesniPclmul]
  exact open_leavesQ _ aesNiPclmulV.impl.blkB blkBD_aesniPclmul_leaves (aesNiPclmulV.impl.gh.free.get rfl)
    (aesNiPclmulV.impl.ctr.free.get rfl)

/-! ### In a frame of 2616 bytes

In a frame of 2616 bytes, 8 more than the 2608 its stack arguments and
`work` need, `work` is 16-byte aligned (the stack pointer on entry is 8
bytes off 16), so that every slot of 16 bytes it keeps in `work` is. -/

theorem openFrameSatA_pre : ∃ s, (Proof.AesGcm.openRoundsContract X86_64.abi 2640).pre s := by
  implies_sat [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openPre, Proof.AesGcm.openRoundsPost,
    Spec.Gcm.openLeak, X86_64.abi, X86_64.argRegs] [openFrameSat, openSat] using openFrameSat

/-- `vg_aes_gcm_open` in a frame of 2616 bytes, for any code that meets the
contract within it. -/
theorem openCode_framedA {c : Prog isa}
    (hv : Verified X86_64.target c (Proof.AesGcm.openScratchContract X86_64.abi 24))
    (hsp : c.all (fun i => !X86_64.isa.writesSp i) = true) (hxd : c.x86_64Depth ≤ 24) :
    Verified X86_64.target (withStackArgScratch 2616 4 c) (Proof.AesGcm.openRoundsContract X86_64.abi 2640) :=
  X86_64.Verified.stackArgScratch (hpostOut := openPostOut_local _) (sig := Spec.Gcm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.openRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (leak := some (Spec.Gcm.openLeak X86_64.abi.ptrBits)) (bytes := 2616) hv
    (by decide) (by decide) (by decide) hsp hxd (openPre_local _)
    (openPost_local _) openFrameSatA_pre (hleak := openLeak_local _)

theorem open_framedA (v : GcmImpl) :
    Verified X86_64.target (withStackArgScratch 2616 4 (Impl.AesGcm.X86_64.«open» v.callees))
      (Proof.AesGcm.openRoundsContract X86_64.abi 2640) :=
  openCode_framedA (open_verified v) (open_spSafe v) (open_xdepth v)

theorem open_satFA : ∃ s, (Spec.Gcm.openPreparedSig.contract abi (Spec.Gcm.openPreparedPre 64)
    (Proof.AesGcm.openRoundsPost 64) true 2640 none).pre s := by
  refine ⟨Flag.openSatF, ?_⟩
  sig_pre [Spec.Gcm.openPreparedSig, Spec.Gcm.openPreparedPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.openRoundsPost,
    X86_64.abi, X86_64.argRegs, Flag.openSatF, openFrameSat, openSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro _
       exact preparedPowersRepr_of_zero fun _ _ => rfl)
    | (intro _
       refine preparedPowers16Repr_of ?_
       exact preparedPowersRepr_of_zero fun _ _ => rfl)

/-- `Flag.open_of_base`, in a frame of 2616 bytes. -/
theorem open_of_baseA {c : Prog isa}
    (h : Verified X86_64.target c (Proof.AesGcm.openRoundsContract abi 2640)) :
    Verified X86_64.target c (AesGcm.Flag.openRoundsContract abi 2640) :=
  Verified.leak_flag (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h
    (fun _ _ _ _ _ _ _ _ _ _ _ h => h.1) open_satFA) (fun _ _ _ _ _ _ _ _ _ _ _ => rfl)

/-- The stack arguments of `vg_aes_gcm_open`'s code in the frame of
`withStackArgScratch 2616 4` from `s`: those of `s`, then `work`. -/
def openArgs (s : State) (i : Nat) : BitVec 64 :=
  if i < 4 then stackArg s i else s.gpr .rsp - BitVec.ofNat 64 2616 + BitVec.ofNat 64 48

/-- Where `vg_aes_gcm_open`'s code in the frame of `withStackArgScratch 2616 4`
from `s` has its stack pointer, and `work`. -/
abbrev openA (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 2616
abbrev openW (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 2616 + BitVec.ofNat 64 48

/-- What is left at the stack pointer of `vg_aes_gcm_open`'s code in the
frame from `s`: what was there in its first 8 bytes (`none`), then the
copies of the stack arguments (`openArgs`). -/
def openHdr (s : State) (x : Addr) : Option (BitVec 8) :=
  if (x - openA s).toNat < 8 then none
  else some ((openArgs s ((x - openA s).toNat / 8 - 1)).extractLsb' (8 * ((x - openA s).toNat % 8)) 8)

/-- What `vg_aes_gcm_open_prepared`'s code leaves in its frame and in `work`,
of its entry `s`. -/
def openVs (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
    Option (BitVec 8)) (s : State) (x : Addr) : Option (BitVec 8) :=
  openV Lb (openHdr s) s.gpr (openArgs s) (openA s) (openW s) x

theorem openWord_congr {g g' : Reg → BitVec 64} {a a' : Nat → BitVec 64}
    (hg : ∀ r, r ≠ .rax → r ≠ .rsp → g r = g' r) (ha : ∀ i < 5, a i = a' i) (j : Nat) :
    openWord g a j = openWord g' a' j := by
  unfold openWord
  rw [hg .rbx (by decide) (by decide), hg .rbp (by decide) (by decide), hg .r12 (by decide) (by decide),
    hg .r13 (by decide) (by decide), hg .r14 (by decide) (by decide), hg .r15 (by decide) (by decide),
    hg .rsi (by decide) (by decide), hg .r8 (by decide) (by decide), hg .r9 (by decide) (by decide),
    ha 0 (by decide), ha 1 (by decide), ha 3 (by decide)]

theorem openV_congr (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)) {hdr hdr' : Addr → Option (BitVec 8)} {g g' : Reg → BitVec 64} {a a' : Nat → BitVec 64}
    {A W x : Addr} (hh : (⟨A, 48⟩ : Region).Contains x 1 → hdr x = hdr' x)
    (hg : ∀ r, r ≠ .rax → r ≠ .rsp → g r = g' r) (ha : ∀ i < 5, a i = a' i) :
    openV Lb hdr g a A W x = openV Lb hdr' g' a' A W x := by
  unfold openV
  by_cases h : (⟨A, 48⟩ : Region).Contains x 1
  · simp only [h, ↓reduceIte]; exact hh h
  · simp only [h, ↓reduceIte, funext (openWord_congr hg ha), openL_congr Lb hg ha]

/-- What `openV` says of the state `narrowS` runs `vg_aes_gcm_open`'s code
from, in the frame of `withStackArgScratch 2616 4` from `s`, `openVs` says of
`s`. -/
theorem narrowS_openV {sig : Sig} {e : Elem} {n : Nat}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    (h4 : nStack sig = 4) (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 16 + 8 * nStack sig + n * e.size ≤ 2616)
    {s : State} (hs : (sig.contract abi pre post wa (24 + 2616) leak).pre s)
    (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8))
    {x : Addr} (hx : openQ (openA s) (openW s) x) :
    openQ ((narrowS sig e n 2616 s).gpr .rsp) (stackArg (narrowS sig e n 2616 s) 4) x ∧
      (openV Lb (fun _ => none) (narrowS sig e n 2616 s).gpr (fun i => stackArg (narrowS sig e n 2616 s) i)
          ((narrowS sig e n 2616 s).gpr .rsp) (stackArg (narrowS sig e n 2616 s) 4) x).getD
          ((narrowS sig e n 2616 s).mem x) =
        (openVs Lb s x).getD (s.mem x) := by
  obtain ⟨hg, ha, hl, hf⟩ := narrowS_args hk hb (by decide) hs
  obtain ⟨hrsp, -⟩ := narrowS_facts (nm := "") hk hb (by decide) hs
  rw [h4] at ha hl hf
  have hW : stackArg (narrowS sig e n 2616 s) 4 = openW s := hl
  have hA : (narrowS sig e n 2616 s).gpr .rsp = openA s := hrsp
  have hargs : ∀ i < 5, stackArg (narrowS sig e n 2616 s) i = openArgs s i := fun i hi => by
    by_cases h : i < 4
    · simp only [openArgs, h, ↓reduceIte]; exact ha i h
    · have : i = 4 := by omega_using [h, hi]
      subst this
      simp only [openArgs, Nat.lt_irrefl, ↓reduceIte]; exact hW
  refine ⟨by rw [hW, hA]; exact hx, ?_⟩
  rw [hW, hA]
  unfold openVs
  by_cases hh : (⟨openA s, 48⟩ : Region).Contains x 1
  · -- The return address and the copies of the stack arguments.
    simp only [openV, hh, ↓reduceIte, Option.getD_none, openHdr]
    have hlt : (x - openA s).toNat < 48 := by simp only [Region.Contains] at hh; omega_using [hh]
    generalize hd : (x - openA s).toNat = d at hlt ⊢
    have ex : x = openA s + BitVec.ofNat 64 d := by
      rw [← hd, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    by_cases h8 : d < 8
    · simp only [h8, ↓reduceIte, Option.getD_none]
      refine hf x fun r hr hc => ?_
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains] at hc
      rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl] at hc
      have hc' : (x - (openA s + BitVec.ofNat 64 8)).toNat < 8 * (4 + 1) := by
        have h' : (x - (openA s + BitVec.ofNat 64 8)).toNat + 1 ≤ 8 * (4 + 1) := hc
        omega_using [h']
      have := (Offset.lt_iff x (openA s) (d := 8) (n := 8 * (4 + 1)) (by decide)).1 hc'
      omega_using [this, h8, hd]
    · simp only [h8, ↓reduceIte, Option.getD_some]
      have ex' : x = openA s + BitVec.ofNat 64 (8 * (d / 8)) + BitVec.ofNat 64 (d % 8) := by
        rw [Offset.add_add_eq _ (show 8 * (d / 8) + d % 8 = d by omega_arith), ex]
      have hrd : (narrowS sig e n 2616 s).mem.readW (openA s + BitVec.ofNat 64 (8 * (d / 8))) 64 =
          stackArg (narrowS sig e n 2616 s) (d / 8 - 1) := by
        unfold stackArg stackArgAddr
        rw [hA, show 8 * (d / 8 - 1 + 1) = 8 * (d / 8) by omega_arith]
      rw [ex', Blocks.byte_readW64 (narrowS sig e n 2616 s).mem (openA s + BitVec.ofNat 64 (8 * (d / 8)))
        (j := d % 8) (by omega_arith), hrd, hargs _ (by omega_arith)]
  · rw [openV_congr Lb (hdr' := openHdr s) (g' := s.gpr) (a' := openArgs s) (fun h => absurd h hh) hg hargs]
    refine congrArg _ (hf x fun r hr hc => ?_)
    simp only [List.mem_singleton] at hr
    subst hr
    refine hh ?_
    simp only [Region.Contains] at hc
    rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl] at hc
    have hc' : (x - (openA s + BitVec.ofNat 64 8)).toNat + 1 ≤ 8 * (4 + 1) := hc
    have hlt : (x - (openA s + BitVec.ofNat 64 8)).toNat < 40 := by omega_using [hc']
    have := (Offset.lt_iff x (openA s) (d := 8) (n := 40) (by decide)).1 hlt
    simp only [Region.Contains]; omega_using [this]

/-- The unknowns `vg_aes_gcm_open`'s code of `v` ends with in its frame: the
same in two runs. -/
theorem open32_innerU (v : GcmVariant) {C : Mem → Addr → Prop} {s₁ s₂ : State}
    (h₁ : (Spec.Gcm.openPreparedContract X86_64.abi 2640).pre s₁)
    (h₂ : (Spec.Gcm.openPreparedContract X86_64.abi 2640).pre s₂) (hf₁ : C s₁.mem (s₁.gpr .rdi))
    (hf₂ : C s₂.mem (s₂.gpr .rdi)) (hp : (Spec.Gcm.openPreparedContract X86_64.abi 2640).pub s₁ s₂)
    (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (Impl.AesGcm.X86_64.«open» v.impl.callees), s₁.syms n = s₂.syms n) :
    innerU (Impl.AesGcm.X86_64.«open» v.impl.callees) (narrowS Spec.Gcm.openSig .u64 320 2616 (narrow32 s₁)) =
      innerU (Impl.AesGcm.X86_64.«open» v.impl.callees) (narrowS Spec.Gcm.openSig .u64 320 2616 (narrow32 s₂)) := by
  unfold Spec.Gcm.openPreparedContract at h₁ h₂ hp
  have q (s : State) (hs : (Spec.Gcm.openPreparedSig.contract abi (Spec.Gcm.openPreparedPre abi.ptrBits)
      (Spec.Gcm.openPost abi.ptrBits) true 2640 (some (Spec.Gcm.openPreparedLeak abi.ptrBits))).pre s)
      (hf : C s.mem (s.gpr .rdi)) := pre_narrowFirstArray (n := 32) (n' := 129) (by decide)
    (pre := Spec.Gcm.openPre 64) (fun _ _ _ _ _ _ _ _ _ _ _ h => h)
    (pre_of_rel (N := 129) (C := C) (leakB := some (Spec.Gcm.openLeak 64))
      (pre := Spec.Gcm.openPreparedPre 64) (pre' := Spec.Gcm.openPre 64)
      (fun _ _ _ _ _ _ _ _ _ _ _ h _ => h.1) hs hf)
  obtain ⟨⟨hs, hl⟩, hpubs, hdescs⟩ := (pubL_args (sig := Spec.Gcm.openPreparedSig) (by decide)).mp hp
  have e : ∀ s : State, Curry.apply (Spec.Gcm.openPreparedSig.words abi.ptrBits) (Spec.Gcm.openPreparedLeak abi.ptrBits)
      (allArgs Spec.Gcm.openPreparedSig s) s.mem = flagLeak s.mem (s.gpr .rdi) ::
        Curry.apply (Spec.Gcm.openSig.words abi.ptrBits) (Spec.Gcm.openLeak abi.ptrBits)
          (allArgs Spec.Gcm.openSig s) s.mem := fun _ => rfl
  have hl' := (List.cons.inj ((e s₁).symm.trans (hl.trans (e s₂)))).2
  exact framed_innerU_agree (sig := Spec.Gcm.openSig) (nm := "work") (e := .u64) (n := 320)
    (stack := 24) (bytes := 2616) (pre := Spec.Gcm.openPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.openRoundsPost X86_64.abi.ptrBits) (wa := true)
    (leak := some (Spec.Gcm.openLeak X86_64.abi.ptrBits))
    (open_verified v.impl) (by decide) (by decide) (by decide)
    (openPre_local _) (q s₁ h₁ hf₁) (q s₂ h₂ hf₂)
    ((pubL_args (sig := Spec.Gcm.openSig) (by decide)).mpr ⟨⟨hs, hl'⟩, hpubs,
      fun r hr i hi => hdescs r (by
        rw [show Spec.Gcm.openPreparedSig.params = ("ctx", .array false .u64 129) ::
          Spec.Gcm.openSig.params.tail from rfl, descs_array .u64 32 129]
        exact hr) i hi⟩) hu hsy
    (Sig.LeakLocal.toL (sig := Spec.Gcm.openSig) (leak := some (Spec.Gcm.openLeak X86_64.abi.ptrBits))
      (openLeak_local _))

/-- The code of `vg_aes_gcm_open` of the variant `v` for the key context of
`vg_aes_gcm_init`, in the frame of `withStackArgScratch 2616 4`, from a state
meeting `vg_aes_gcm_open_prepared`'s precondition and `C`: what `openVs`
says the code leaves where `openQ` says. -/
theorem open_branchOf (v : GcmVariant) (hc : v.impl.openCode v.impl.callees = Impl.AesGcm.X86_64.«open» v.impl.callees)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : ∀ s t s', (Proof.AesGcm.openX86_64M Gcm.X86_64.Stitch.CtxMode.base).pre s →
      Exec isa (v.impl.openCode v.impl.callees) s t s' →
      ∀ x, openQ (s.gpr .rsp) (stackArg s 4) x →
        s'.mem x = (openV Lb (fun _ => none) s.gpr (fun i => stackArg s i) (s.gpr .rsp)
          (stackArg s 4) x).getD (s.mem x))
    {C : Mem → Addr → Prop} :
    ∀ s t u, (Spec.Gcm.openPreparedContract X86_64.abi 2640).pre s → C s.mem (s.gpr .rdi) →
      Exec isa (withStackArgScratch 2616 4 (v.impl.openCode v.impl.callees)) s t u →
      ∀ x, openQ (openA s) (openW s) x → u.mem x = (loseL (openA s) 2616
        (innerU (Impl.AesGcm.X86_64.«open» v.impl.callees) (narrowS Spec.Gcm.openSig .u64 320 2616 (narrow32 s)))
        (openVs Lb s) x).getD (s.mem x) := by
  rw [hc] at hL
  intro s t u hs hf he x hx
  rw [hc] at he
  unfold Spec.Gcm.openPreparedContract at hs
  have h₁ := pre_of_rel (N := 129) (C := C) (leakB := some (Spec.Gcm.openLeak 64))
    (pre := Spec.Gcm.openPreparedPre 64) (pre' := Spec.Gcm.openPre 64) (fun _ _ _ _ _ _ _ _ _ _ _ h _ => h.1) hs hf
  have h₂ := pre_narrowFirstArray (n := 32) (n' := 129) (by decide) (pre := Spec.Gcm.openPre 64)
    (fun _ _ _ _ _ _ _ _ _ _ _ h => h) h₁
  obtain ⟨t₁, u₁, he₁, hm⟩ := exec_narrow (open_framedA v.impl) h₂
    (fun _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)) (Covers.refl _) he
  obtain ⟨hx', hv⟩ := narrowS_openV (sig := Spec.Gcm.openSig) (e := .u64) (n := 320) (by decide)
    (by decide) (by decide) h₂ Lb hx
  rw [hm, framed_leavesQ (sig := Spec.Gcm.openSig) (nm := "work") (e := .u64) (n := 320)
    (bytes := 2616) (stack := 24) (pre := Spec.Gcm.openPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.openRoundsPost X86_64.abi.ptrBits) (wa := true)
    (leak := some (Spec.Gcm.openLeak X86_64.abi.ptrBits))
    (open_verified v.impl) (fun s h => ⟨openCode_implies.pre s h, trivial⟩) hL
    (by decide) (by decide) (by decide) (open_spSafe _) (open_xdepth _)
    (openPre_local _) h₂ he₁ x hx']
  exact loseL_getD_congr hv

/-- The granules `vg_aes_gcm_open_prepared` wipes, of its 2640 bytes of stack
in chunks of 8 (at the top), 2344, 8 and 280, whose granules are then
aligned: the 24 bytes below its frame (an 8-byte granule and a 16-byte one),
in `work` the state (`J₀`, `Y`, the counter, the keystream: five 16-byte
granules), the tag of the ciphertext (one), the result (an 8-byte granule)
and the computed and received tags padded (two), and the 8 bytes above
`work` (an 8-byte granule): twelve stores. -/
def openKs : List Nat := [0, 8, 88, 104, 120, 136, 152, 184, 288, 312, 328, 2632]

/-- The chunks of the 2640 bytes `vg_aes_gcm_open_prepared` wipes, from the
top. -/
def openCs : List Nat := [8, 2344, 8, 280]

/-- A byte of the 2640 below `R` that `wipe openKs` does not zero is where
`openQ` says. -/
theorem openWindow {R x : Addr} (hx : (⟨R - BitVec.ofNat 64 2640, 2640⟩ : Region).Contains x 1)
    (hw : ¬ WCov openKs openCs R x) :
    openQ (R - BitVec.ofNat 64 2616) (R - BitVec.ofNat 64 2616 + BitVec.ofNat 64 48) x := by
  simp only [WCov, openCs, List.sum_cons, List.sum_nil, Nat.add_zero, show 8 + (2344 + (8 + 280)) = 2640 from rfl]
    at hw
  have hlt : (x - (R - BitVec.ofNat 64 2640)).toNat < 2640 := by simp only [Region.Contains] at hx; omega_using [hx]
  generalize hi : (x - (R - BitVec.ofNat 64 2640)).toNat = i at hlt hw
  have hc : ¬ cov openKs openCs i = true := fun h => hw ⟨hx, h⟩
  have hi' : ¬ i < 24 ∧ ¬ (88 ≤ i ∧ i < 168) ∧ ¬ (184 ≤ i ∧ i < 200) ∧ ¬ (288 ≤ i ∧ i < 296) ∧
      ¬ (312 ≤ i ∧ i < 344) ∧ ¬ 2632 ≤ i := by
    have e : cov openKs openCs i = if i < 280 then covC openKs 0 280 i
        else if i < 288 then decide (i - 280 < 8) && covC openKs 280 8 (i - 280)
        else if i < 2632 then decide (i - 288 < 2344) && covC openKs 288 2344 (i - 288)
        else decide (i - 2632 < 8) && covC openKs 2632 8 (i - 2632) := by
      simp only [cov, openCs, List.sum_cons, List.sum_nil]
      by_cases h₁ : i < 280
      · simp [h₁, show i < 288 by omega_arith, show i < 2632 by omega_arith]
      by_cases h₂ : i < 288
      · simp [h₁, h₂, show i < 2632 by omega_arith]
      by_cases h₃ : i < 2632
      · simp [h₁, h₂, h₃]
      · simp [h₁, h₂, h₃]
    refine ⟨fun h => hc ?_, fun h => hc ?_, fun h => hc ?_, fun h => hc ?_, fun h => hc ?_, fun h => hc ?_⟩ <;>
      rw [e]
    · simp only [show i < 280 by omega_arith, ↓reduceIte, covC, show 280 % 16 = 8 from rfl]
      by_cases h8 : i < 8
      · simp [h8, openKs]
      · simp only [h8, ↓reduceIte]
        rw [show (i - 8) / 16 = 0 by omega_arith]; simp [openKs]
    · simp only [show i < 280 by omega_arith, ↓reduceIte, covC, show 280 % 16 = 8 from rfl,
        show ¬ i < 8 by omega_arith]
      rcases (by omega_arith : (i - 8) / 16 = 5 ∨ (i - 8) / 16 = 6 ∨ (i - 8) / 16 = 7 ∨ (i - 8) / 16 = 8 ∨
        (i - 8) / 16 = 9) with e | e | e | e | e <;> rw [e] <;> simp [openKs]
    · simp only [show i < 280 by omega_arith, ↓reduceIte, covC, show 280 % 16 = 8 from rfl,
        show ¬ i < 8 by omega_arith]
      rw [show (i - 8) / 16 = 11 by omega_arith]; simp [openKs]
    · simp only [show ¬ i < 280 by omega_arith, show ¬ i < 288 by omega_arith, show i < 2632 by omega_arith,
        ↓reduceIte, covC, show 2344 % 16 = 8 from rfl, show i - 288 < 8 by omega_arith,
        show i - 288 < 2344 by omega_arith]
      simp [openKs]
    · simp only [show ¬ i < 280 by omega_arith, show ¬ i < 288 by omega_arith, show i < 2632 by omega_arith,
        ↓reduceIte, covC, show 2344 % 16 = 8 from rfl, show ¬ i - 288 < 8 by omega_arith,
        show i - 288 < 2344 by omega_arith]
      rcases (by omega_arith : (i - 288 - 8) / 16 = 1 ∨ (i - 288 - 8) / 16 = 2) with e | e <;>
        rw [e] <;> simp [openKs]
    · simp only [show ¬ i < 280 by omega_arith, show ¬ i < 288 by omega_arith, show ¬ i < 2632 by omega_arith,
        ↓reduceIte, covC, show 8 % 16 = 8 from rfl, show i - 2632 < 8 by omega_arith]
      simp [openKs]
  have eA : R - BitVec.ofNat 64 2616 = R - BitVec.ofNat 64 2640 + BitVec.ofNat 64 24 :=
    Offset.sub_ofNat_eq R (show 2616 ≤ 2640 by decide)
  have mk : ∀ {d k : Nat}, d ≤ i → i < d + k → d + k ≤ 2640 →
      (⟨R - BitVec.ofNat 64 2640 + BitVec.ofNat 64 d, k⟩ : Region).Contains x 1 := fun {d k} h₁ h₂ h₃ => by
    have := (Offset.lt_iff x (R - BitVec.ofNat 64 2640) (d := d) (n := k) (by omega_arith)).2
      ⟨by omega_arith, by omega_arith⟩
    simp only [Region.Contains]; omega_using [this]
  unfold openQ
  rw [eA]
  simp only [Offset.add_add]
  by_cases h₁ : i < 72
  · exact .inl (mk (by omega_arith) (by omega_arith) (by decide))
  by_cases h₂ : i < 88
  · exact .inr (.inl (by simpa using mk (d := 72) (k := 16) (by omega_arith) (by omega_arith) (by decide)))
  by_cases h₃ : i < 184
  · exact .inr (.inr (.inl (mk (by omega_arith) (by omega_arith) (by decide))))
  by_cases h₄ : i < 288
  · exact .inr (.inr (.inr (.inl (mk (by omega_arith) (by omega_arith) (by decide)))))
  by_cases h₅ : i < 312
  · exact .inr (.inr (.inr (.inr (.inl (mk (by omega_arith) (by omega_arith) (by decide))))))
  · exact .inr (.inr (.inr (.inr (.inr (mk (by omega_arith) (by omega_arith) (by decide))))))

/-- Two runs of `vg_aes_gcm_open_prepared` with the same public data, from
states that agree outside the buffers, agree on the stack arguments of
`vg_aes_gcm_open`'s code in the frame of `withStackArgScratch 2616 4`. -/
theorem openArgs_pub {stack : Nat} {s₁ s₂ : State} (hp : (Spec.Gcm.openPreparedContract X86_64.abi stack).pub s₁ s₂)
    (ho : Outside 0 s₁ s₂) : openArgs s₁ = openArgs s₂ := by
  unfold Spec.Gcm.openPreparedContract at hp
  obtain ⟨-, hpubs, -⟩ := (pubL_args (sig := Spec.Gcm.openPreparedSig) (by decide)).mp hp
  have harg (j : Nat) (hj : (Spec.Gcm.openPreparedSig.params.flatMap (·.2.pubs)).getD (6 + j) false = true)
      (hj4 : j < 4) : stackArg s₁ j = stackArg s₂ j := by
    have := hpubs (6 + j) hj
    have e : ∀ s : State, (allArgs Spec.Gcm.openPreparedSig s).getD (6 + j) 0 = stackArg s j := by
      intro s
      rcases (by omega_using [hj4] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl
    rw [e, e] at this
    have hw : ((Spec.Gcm.openPreparedSig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD (6 + j) 64 = 64 := by
      rcases (by omega_using [hj4] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl
    rw [hw, BitVec.setWidth_eq, BitVec.setWidth_eq] at this
    exact this
  funext i
  simp only [openArgs]
  by_cases hi : i < 4
  · simp only [hi, ↓reduceIte]
    exact harg i (by rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl) hi
  · simp only [hi, ↓reduceIte, ho.2.2.1 .rsp (by decide)]

open VG.X86_64.Scrub in
/-- Two runs of the code of `vg_aes_gcm_open_prepared` of a variant whose
loops read only the key context, where its `vg_aes_gcm_open` leaves what
`openV` says (`hL`), with the same public data leave the same bytes in its
stack but the granules `openKs`. -/
theorem openW_resOk (v : GcmVariant)
    (hc : v.impl.openCode v.impl.callees = Impl.AesGcm.X86_64.«open» v.impl.callees)
    (hL : ∃ Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
        Option (BitVec 8),
      ∀ s t s', (Proof.AesGcm.openX86_64M Gcm.X86_64.Stitch.CtxMode.base).pre s →
        Exec isa (v.impl.openCode v.impl.callees) s t s' →
        ∀ x, openQ (s.gpr .rsp) (stackArg s 4) x →
          s'.mem x = (openV Lb (fun _ => none) s.gpr (fun i => stackArg s i) (s.gpr .rsp)
            (stackArg s 4) x).getD (s.mem x)) :
    ResOk (withStackArgScratch 2616 4 (v.impl.openCode v.impl.callees))
      (Spec.Gcm.openPreparedContract X86_64.abi 2640) 2640 openKs openCs := by
  obtain ⟨Lb, hL⟩ := hL
  unfold Spec.Gcm.openPreparedContract
  refine resOk_of_leaves (V := fun s x => loseL (openA s) 2616
      (innerU (Impl.AesGcm.X86_64.«open» v.impl.callees) (narrowS Spec.Gcm.openSig .u64 320 2616 (narrow32 s)))
      (openVs Lb s) x) ScrubAbi.plain ?_ ?_
  · intro s t u hs he x hx hw
    exact open_branchOf v hc hL (C := fun _ _ => True) s t u hs trivial he x (openWindow hx hw)
  · intro s₁ s₂ h₁ h₂ hp ho hu hsy
    have ha := openArgs_pub hp ho
    have hsp : s₁.gpr .rsp = s₂.gpr .rsp := ho.2.2.1 .rsp (by decide)
    have hA : openA s₁ = openA s₂ := by simp only [openA, hsp]
    have hW : openW s₁ = openW s₂ := by simp only [openW, hsp]
    have hV : openVs Lb s₁ = openVs Lb s₂ := by
      funext x
      unfold openVs
      rw [ha, hA, hW]
      exact openV_congr Lb (fun _ => by simp only [openHdr, ha, hA]) (fun r hr _ => ho.2.2.1 r hr)
        (fun _ _ => rfl)
    have hsy' : ∀ n ∈ UpperLock.inames (Impl.AesGcm.X86_64.«open» v.impl.callees), s₁.syms n = s₂.syms n := by
      rw [← hc]; exact hsy
    have hU := open32_innerU v (C := fun _ _ => True) h₁ h₂ trivial trivial hp hu hsy'
    funext x
    dsimp only
    rw [hA, hU, hV]

/-- `vg_aes_gcm_open_prepared`'s postcondition reads the memory on return
only within the buffers: the data. -/
theorem openPreparedOut (stack : Nat) :
    PostOut (Spec.Gcm.openPreparedContract X86_64.abi stack) (Spec.Gcm.openPreparedSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, data, len, tag, tl], _ =>
      simp only [Spec.Gcm.openPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      intro key hk
      show (match Spec.Gcm.openResult (Spec.Gcm.aes key) (Spec.Gcm.aes key 0) tl.toNat
          (Spec.Aes.bytesAt m nonce nl.toNat) (Spec.Aes.bytesAt m data len.toNat)
          (Spec.Aes.bytesAt m aad al.toNat) (Spec.Aes.bytesAt m tag tl.toNat) with
        | some pt => r = 1 ∧ Spec.Aes.bytesAt m₂ data len.toNat = pt
        | none => r = 0 ∧ Spec.Aes.bytesAt m₂ data len.toNat = Spec.Aes.bytesAt m data len.toNat)
      rw [Scrub.bytesAt_of0 hb.2.2.2.1 (by omega_arith)]
      exact h key hk

/-- `vg_aes_gcm_open_prepared` of a variant whose loops read only the key
context. -/
def openWPlain (v : GcmVariant) : Unscrubbed Spec.Gcm.openPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := withStackArgScratch 2608 4 (v.impl.openCode v.impl.callees)
  stack := 2632
  verified := VG.Proof.AesGcm.Flag.open_keyed (Flag.open_of_base (openSel_framed v.impl Short.shortFacts))
  spSafe := X86_64.withStackArgScratch_spSafe (openCode_spSafe v.impl v.impl.blkB)

theorem openA_verified : Verified X86_64.target
    (withStackArgScratch 2616 4 (aesNiPclmulV.impl.openCode aesNiPclmulV.impl.callees))
    (AesGcm.Flag.openRoundsContract abi 2640) := by
  rw [openCode_aesniPclmul]; exact open_of_baseA (open_framedA aesNiPclmulV.impl)

/-- `vg_aes_gcm_open_prepared` of the variant on AES-NI and PCLMULQDQ, in a
frame of 2616 bytes, whose `work` is 16-byte aligned. -/
def openWPlainA : Unscrubbed Spec.Gcm.openPreparedApi X86_64.target where
  suffix := aesNiPclmulV.impl.suffix
  code := withStackArgScratch 2616 4 (aesNiPclmulV.impl.openCode aesNiPclmulV.impl.callees)
  stack := 2640
  verified := VG.Proof.AesGcm.Flag.open_keyed openA_verified
  spSafe := X86_64.withStackArgScratch_spSafe (openCode_spSafe aesNiPclmulV.impl aesNiPclmulV.impl.blkB)

/-- `vg_aes_gcm_open_prepared_aesni_pclmul`, in a frame of 2616 bytes,
followed by the clearing of the granules `openKs` (three 8-byte stores and
nine 16-byte ones, all aligned): it returns without secret residue
(`openW_resOk`). -/
def openWAesniPclmul : Registration Spec.Gcm.openPreparedApi X86_64.target :=
  RScrub.withScrubResC openWPlainA (openPreparedOut _) openKs openCs
    (openW_resOk aesNiPclmulV openCode_aesniPclmul open_aesniPclmul_leaves)

/-! ## The one-shot functions wiped whole

The one-shot functions for which no proof says what they leave are followed
by the clearing of their whole frame, in chunks whose 16-byte stores are
aligned (an 8-byte chunk at the top, the stack pointer on entry being 8 off
16; `X86_64.RScrub.withScrubAllC`, and `withScrubAllRC` at any level, for
code that writes `zmm16`–`zmm31`), which asks no proof of what the code
leaves: the wipe, 32 bytes a store at every level but SSE's, costs the same
whatever the length of the input. -/

/-- `vg_aes_gcm_seal_prepared` of a variant whose loops read only the key
context: `sealWAesniPclmul` for the function of the variant on AES-NI and
PCLMULQDQ, which returns without secret residue, and for the others
`sealWPlain` followed by the clearing of its whole frame of 2624 bytes. -/
def sealWReg (v : GcmVariant) : Registration Spec.Gcm.sealPreparedApi X86_64.target :=
  if v.impl.suffix = aesNiPclmulV.impl.suffix then sealWAesniPclmul
  else RScrub.withScrubAllC (sealWPlain v) (sealPreparedOut _) [8, 2616]

/-- `vg_aes_gcm_open_prepared` of a variant whose loops read only the key
context: `openWAesniPclmul` for the variant on AES-NI and PCLMULQDQ, which
returns without secret residue, and for the others `openWPlain` followed by
the clearing of its whole frame of 2632 bytes. -/
def openWReg (v : GcmVariant) : Registration Spec.Gcm.openPreparedApi X86_64.target :=
  if v.impl.suffix = aesNiPclmulV.impl.suffix then openWAesniPclmul
  else RScrub.withScrubAllC (openWPlain v) (openPreparedOut _) [8, 2624]

/-- `vg_aes_gcm_open_to_prepared`'s postcondition reads the memory on return
only within the buffers: the output, as long as the input by the
precondition. -/
theorem openToPreparedOut (stack : Nat) :
    PostOut (Spec.Gcm.openToPreparedContract X86_64.abi stack) (Spec.Gcm.openToPreparedSig.retBits 64) :=
  postOut_of_local_pre ScrubAbi.plain fun vs m m₁ m₂ r hlen hpre hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, src, len, dst, dl, tag, tl], _ =>
      simp only [Spec.Gcm.openToPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      have hdl : dl.toNat = len.toNat := hpre.2.1
      intro key hk
      show (match Spec.Gcm.openResult (Spec.Gcm.aes key) (Spec.Gcm.aes key 0) tl.toNat
          (Spec.Aes.bytesAt m nonce nl.toNat) (Spec.Aes.bytesAt m src len.toNat)
          (Spec.Aes.bytesAt m aad al.toNat) (Spec.Aes.bytesAt m tag tl.toNat) with
        | some pt => r = 1 ∧ Spec.Aes.bytesAt m₂ dst len.toNat = pt
        | none => r = 0 ∧ Spec.Aes.bytesAt m₂ dst len.toNat = List.replicate len.toNat 0)
      rw [Scrub.bytesAt_of0 hb.2.2.2.2.1 (by omega_arith)]
      exact h key hk

/-- `vg_aes_gcm_open_to_prepared` of a variant whose loops read only the key
context. -/
def openToWPlain (v : GcmVariant) : Unscrubbed Spec.Gcm.openToPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := openToCode v
  verified := VG.Proof.AesGcm.Flag.openTo_keyed (openToCode_keyed v)
  spSafe := openToCode_spAll v

/-- `vg_aes_gcm_open_to_prepared` of a variant whose loops read only the key
context, followed by the clearing of its whole frame of 2776 bytes. -/
def openToWReg (v : GcmVariant) : Registration Spec.Gcm.openToPreparedApi X86_64.target :=
  RScrub.withScrubAllC (openToWPlain v) (openToPreparedOut _) [8, 2768]

/-- `vg_aes_gcm_seal_gather_prepared`'s postcondition reads the memory on
return only within the buffers: the output and the tag. -/
theorem sealGatherPreparedOut (stack : Nat) :
    PostOut (Spec.Gcm.sealGatherPreparedContract X86_64.abi stack)
      (Spec.Gcm.sealGatherPreparedSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, src, sc, dst, len, tag], _ =>
      simp only [Spec.Gcm.sealGatherPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      intro key hk hg
      show _ = (Spec.Aes.bytesAt m₂ dst len.toNat, Spec.Aes.bytesAt m₂ tag 16)
      rw [Scrub.bytesAt_of0 hb.2.2.2.1 (by omega_arith), Scrub.bytesAt_of0 hb.2.2.2.2 (by decide)]
      exact h key hk hg

/-- `vg_aes_gcm_seal_gather_prepared` of a variant whose loops read only the
key context. -/
def sealGatherWPlain (v : GcmVariant) : Unscrubbed Spec.Gcm.sealGatherPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.StackScratch.X86_64.withStackArgScratch 240 5
      (Impl.AesGcm.X86_64.SealGather.sealGather (shortFn v).quick (shortFn v).fast (shortFn v).test
        (shortFn v).code (initFn v.impl).fn (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn)
  verified := VG.Proof.AesGcm.Flag.sealGather_keyed (Flag.sealGather_of_base
    (Gather.sealGather_framed (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl)))
  spSafe := X86_64.withStackArgScratch_spSafe
      (Gather.sealGather_spAll (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl))

/-- `vg_aes_gcm_seal_gather_prepared` of a variant whose loops read only the
key context, followed by the clearing of its whole frame of 5128 bytes, in
two chunks below the top 8 bytes as each must be under a page. -/
def sealGatherWReg (v : GcmVariant) : Registration Spec.Gcm.sealGatherPreparedApi X86_64.target :=
  RScrub.withScrubAllC (sealGatherWPlain v) (sealGatherPreparedOut _) [8, 2560, 2560]

/-! ## The one-shot functions over the prepared powers, wiped whole

The one-shot functions of the variants whose loops read prepared powers (48
of them, `stitchR`, or 16, `R16`), by the flag or the count on those or on
the key context, that no proof says what they leave: each followed by the
clearing of its whole frame (`RScrub.withScrubAllRC`, which clears
`zmm16`–`zmm31` too for the AVX-512 variant's code, which writes them). -/

/-- `vg_aes_gcm_seal_prepared` of a variant whose loops read the 48 prepared
powers: by the flag, its code on those or on the key context. -/
def sealRPlain (v : GcmVariant) : Unscrubbed Spec.Gcm.sealPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := sealCodeF v
  verified := VG.Proof.AesGcm.Flag.seal_keyed (Flag.seal_ofB (Or.inr rfl) (sealCodeF_verified v))
  spSafe := sealCodeF_spAll v

/-- `sealRPlain`, followed by the clearing of its whole frame of 2624
bytes. -/
def sealRReg (v : GcmVariant) : Registration Spec.Gcm.sealPreparedApi X86_64.target :=
  RScrub.withScrubAllRC (sealRPlain v) (sealPreparedOut _) [8, 2616]

/-- `vg_aes_gcm_open_prepared` of a variant whose loops read the 48 prepared
powers: by the flag, its code on those or on the key context. -/
def openRPlain (v : GcmVariant) : Unscrubbed Spec.Gcm.openPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := openCodeF v
  verified := VG.Proof.AesGcm.Flag.open_keyed (Flag.open_ofB (Or.inr rfl) (openCodeF_verified v))
  spSafe := openCodeF_spAll v

/-- `openRPlain`, followed by the clearing of its whole frame of 2632 bytes. -/
def openRReg (v : GcmVariant) : Registration Spec.Gcm.openPreparedApi X86_64.target :=
  RScrub.withScrubAllRC (openRPlain v) (openPreparedOut _) [8, 2624]

/-- `vg_aes_gcm_open_to_prepared` of a variant whose loops read the 48
prepared powers: by the flag, its code on those or on the key context. -/
def openToRPlain (v : GcmVariant) : Unscrubbed Spec.Gcm.openToPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.Gcm.X86_64.Flag.onFlag 48 (openToCodeF v) (openToCode v)
  verified := VG.Proof.AesGcm.Flag.openTo_keyed (openToCodeR_onFlag v)
  spSafe := openToCodeR_onFlag_spAll v

/-- `openToRPlain`, followed by the clearing of its whole frame of 2776
bytes. -/
def openToRReg (v : GcmVariant) : Registration Spec.Gcm.openToPreparedApi X86_64.target :=
  RScrub.withScrubAllRC (openToRPlain v) (openToPreparedOut _) [8, 2768]

/-- `vg_aes_gcm_seal_gather_prepared` of a variant whose loops read the 48
prepared powers: by the flag, its code on those or on the key context. -/
def sealGatherRPlain (v : GcmVariant) : Unscrubbed Spec.Gcm.sealGatherPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.Gcm.X86_64.Flag.onFlag 48 (sealGatherCodeF v)
    (Impl.StackScratch.X86_64.withStackArgScratch 240 5
      (Impl.AesGcm.X86_64.SealGather.sealGather (shortFn v).quick (shortFn v).fast (shortFn v).test
        (shortFn v).code (initFn v.impl).fn (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn))
  verified := VG.Proof.AesGcm.Flag.sealGather_keyed (sealGatherR_onFlag v)
  spSafe := VG.X86_64.onFlag_spSafe (sealGatherCodeF_spAll v)
    (X86_64.withStackArgScratch_spSafe
      (Gather.sealGather_spAll (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl)))

/-- `sealGatherRPlain`, followed by the clearing of its whole frame of 5128
bytes, in two chunks below the top 8 bytes as each must be under a page. -/
def sealGatherRReg (v : GcmVariant) : Registration Spec.Gcm.sealGatherPreparedApi X86_64.target :=
  RScrub.withScrubAllRC (sealGatherRPlain v) (sealGatherPreparedOut _) [8, 2560, 2560]

/-- `vg_aes_gcm_open_prepared` of a variant whose loops read 16 prepared
powers: by the count, its code on those or on the key context. -/
def openR16Plain (v : GcmVariant) (r : R16 v) : Unscrubbed Spec.Gcm.openPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := openCodeF16 v
  verified := VG.Proof.AesGcm.Flag.open_keyed (Flag.open_ofB (Or.inl rfl) (openCodeF16_verified v r))
  spSafe := openCodeF16_spAll v

/-- `openR16Plain`, followed by the clearing of its whole frame of 2632
bytes. -/
def openR16Reg (v : GcmVariant) (r : R16 v) : Registration Spec.Gcm.openPreparedApi X86_64.target :=
  RScrub.withScrubAllRC (openR16Plain v r) (openPreparedOut _) [8, 2624]

/-- `vg_aes_gcm_open_to_prepared` of a variant whose loops read 16 prepared
powers: by the count, its code on those or on the key context. -/
def openToR16Plain (v : GcmVariant) (r : R16 v) : Unscrubbed Spec.Gcm.openToPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.Gcm.X86_64.Flag.onFlag 16 (openToCodeF16 v r) (openToCode v)
  verified := VG.Proof.AesGcm.Flag.openTo_keyed (openToCodeR16_onFlag v r)
  spSafe := openToCodeR16_onFlag_spAll v r

/-- `openToR16Plain`, followed by the clearing of its whole frame of 2776
bytes. -/
def openToR16Reg (v : GcmVariant) (r : R16 v) : Registration Spec.Gcm.openToPreparedApi X86_64.target :=
  RScrub.withScrubAllRC (openToR16Plain v r) (openToPreparedOut _) [8, 2768]

/-- `vg_aes_gcm_seal_gather_prepared` of a variant whose loops read 16
prepared powers: by the count, its code on those or on the key context. -/
def sealGatherR16Plain (v : GcmVariant) (r : R16 v) :
    Unscrubbed Spec.Gcm.sealGatherPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.Gcm.X86_64.Flag.onFlag 16 (sealGatherCodeF16 v r)
    (Impl.StackScratch.X86_64.withStackArgScratch 240 5
      (Impl.AesGcm.X86_64.SealGather.sealGather (shortFn v).quick (shortFn v).fast (shortFn v).test
        (shortFn v).code (initFn v.impl).fn (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn))
  verified := VG.Proof.AesGcm.Flag.sealGather_keyed (sealGatherR16_onFlag v r)
  spSafe := VG.X86_64.onFlag_spSafe (sealGatherCodeF16_spAll v r)
    (X86_64.withStackArgScratch_spSafe
      (Gather.sealGather_spAll (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl)))

/-- `sealGatherR16Plain`, followed by the clearing of its whole frame of
5128 bytes, in two chunks below the top 8 bytes as each must be under a
page. -/
def sealGatherR16Reg (v : GcmVariant) (r : R16 v) :
    Registration Spec.Gcm.sealGatherPreparedApi X86_64.target :=
  RScrub.withScrubAllRC (sealGatherR16Plain v r) (sealGatherPreparedOut _) [8, 2560, 2560]

end

end VG.Proof.AesGcm.X86_64

/-!
## AES-GCM's functions on a prepared key context, on x86-64, without secret residue

Each function of a variant `v` of AES-GCM on a key context of
`vg_aes_gcm_prepare`, followed by the clearing of every register it may
write and of its whole frame (`Impl.AesGcm.X86_64.Fn`), at the level
`GcmVariant.lv`: the highest of its callees' and of its interleaved loops'
(`GcmVariant.own`). The code over stubs of the callees, and of the
functions it calls that are built from them (the whole-blocks functions,
`blk*_sides`), is evaluated once for each kind of interleaved loops.
-/

namespace VG.Proof.AesGcm.X86_64

open VG.X86_64 VG.X86_64.Scrub
open VG.Impl.Scrub.X86_64 (VecLevel)
open VG.Impl.AesGcm.X86_64 (Callees Fn)

/-- The level of the vector instructions of the loops named `n`. -/
def StitchName.lv : StitchName → VecLevel
  | .vaes => .avx
  | .vaesAvx512 => .evex
  | .aesniAvx => .avx

/-- The level of the vector instructions of `v`'s own code: its loops'. -/
def GcmVariant.own (v : GcmVariant) : VecLevel :=
  match v.stitch with
  | none => .sse
  | some p => p.name.lv

/-- The level of the cleanup of `v`'s functions. -/
def GcmVariant.lv (v : GcmVariant) : VecLevel := v.impl.lv v.own

/-- The level of the cleanup of `v`'s `open` on prepared powers, whose code
past the short path is in VEX (`FastOpen.openFin`). -/
def GcmVariant.lvA (v : GcmVariant) : VecLevel := v.impl.lv (v.own.join .avx)

theorem GcmVariant.lv_le_lvA (v : GcmVariant) : v.lv.level ≤ v.lvA.level := by
  unfold GcmVariant.lv GcmVariant.lvA GcmImpl.lv
  generalize (v.impl.ctr.level.join v.impl.key.level).join v.impl.gh.level = a
  generalize v.own = b
  cases a <;> cases b <;> decide

/-! ## The whole-blocks functions -/

theorem encrypt_fill {k : Nat} {n : String → Nat} (ctr gh : Fn) (hc : calleeSide ctr.code k (n "c") = true)
    (hg : calleeSide gh.code k (n "g") = true) (P PS : Option (Prog isa)) (al F S S4 : Bool) :
    Fill k n (Impl.AesGcm.X86_64.Blocks.encrypt ctrStub ghStub P al F S S4 PS)
      (Impl.AesGcm.X86_64.Blocks.encrypt ctr gh P al F S S4 PS) := by
  unfold Impl.AesGcm.X86_64.Blocks.encrypt Impl.AesGcm.X86_64.Blocks.blocks Impl.AesGcm.X86_64.Blocks.body
  cases P <;> cases F <;> fill_calls_refl

theorem decrypt_fill {k : Nat} {n : String → Nat} (ctr gh : Fn) (hc : calleeSide ctr.code k (n "c") = true)
    (hg : calleeSide gh.code k (n "g") = true) (P PS : Option (Prog isa)) (al F S S4 : Bool) :
    Fill k n (Impl.AesGcm.X86_64.Blocks.decrypt ctrStub ghStub P al F S S4 PS)
      (Impl.AesGcm.X86_64.Blocks.decrypt ctr gh P al F S S4 PS) := by
  unfold Impl.AesGcm.X86_64.Blocks.decrypt Impl.AesGcm.X86_64.Blocks.blocks Impl.AesGcm.X86_64.Blocks.body
  cases P <;> cases F <;> fill_calls_refl

/-- `v`'s `vg_aes_gcm_encrypt_blocks` and `_decrypt_blocks`, for the key
context of `vg_aes_gcm_init`, meet what the cleanup of their callers needs
of them. -/
theorem blkB_sides (v : GcmVariant) :
    calleeSide v.impl.callees.enc.code v.lv.level 8 = true ∧ calleeSide v.impl.callees.dec.code v.lv.level 8 = true := by
  obtain ⟨h1, -, h3⟩ := v.impl.sides v.own
  have hl := (v.impl.lv_le v.own).2.2.2
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact ⟨calleeSide_of_fill (ks := 0) (encrypt_fill (n := fun _ => 0) _ _ h1 h3 none none false false false false) hl
      (by lit_decide),
      calleeSide_of_fill (ks := 0) (decrypt_fill (n := fun _ => 0) _ _ h1 h3 none none false false false false) hl
      (by lit_decide)⟩
  · cases name
    · exact ⟨calleeSide_of_fill (ks := 1)
        (encrypt_fill (n := fun _ => 0) _ _ h1 h3 (some (StitchName.enc .vaes)) none false false false false) hl
        (by lit_decide),
        calleeSide_of_fill (ks := 1)
        (decrypt_fill (n := fun _ => 0) _ _ h1 h3 (some (StitchName.dec .vaes)) none false false false false) hl
        (by lit_decide)⟩
    · exact ⟨calleeSide_of_fill (ks := 2)
        (encrypt_fill (n := fun _ => 0) _ _ h1 h3 (some (StitchName.enc .vaesAvx512)) none false false false false) hl
        (by lit_decide),
        calleeSide_of_fill (ks := 2)
        (decrypt_fill (n := fun _ => 0) _ _ h1 h3 (some (StitchName.dec .vaesAvx512)) none false false false false) hl
        (by lit_decide)⟩
    · exact ⟨calleeSide_of_fill (ks := 1)
        (encrypt_fill (n := fun _ => 0) _ _ h1 h3 (some (StitchName.enc .aesniAvx)) none false true false false) hl
        (by lit_decide),
        calleeSide_of_fill (ks := 1)
        (decrypt_fill (n := fun _ => 0) _ _ h1 h3 (some (StitchName.dec .aesniAvx)) none false false false false) hl
        (by lit_decide)⟩

open Gcm.X86_64.Stitch (CtxMode) in
/-- `i.blkM none`, the whole-blocks functions without loops, meet what the
cleanup of their callers needs of them, at the level `i.lv own`. -/
theorem blkM_none_sides {M : CtxMode} {al : Bool} (i : GcmImpl) (own : VecLevel) (e d : String) :
    calleeSide (i.blkM (M := M) (aligned := al) none e d).enc.code (i.lv own).level 8 = true ∧
      calleeSide (i.blkM (M := M) (aligned := al) none e d).dec.code (i.lv own).level 8 = true := by
  obtain ⟨h1, -, h3⟩ := i.sides own
  cases al
  · exact ⟨calleeSide_of_fill (ks := 0) (encrypt_fill (n := fun _ => 0) _ _ h1 h3 none none false false false false)
        (Nat.zero_le _) (by lit_decide),
      calleeSide_of_fill (ks := 0) (decrypt_fill (n := fun _ => 0) _ _ h1 h3 none none false false false false)
        (Nat.zero_le _) (by lit_decide)⟩
  · exact ⟨calleeSide_of_fill (ks := 0) (encrypt_fill (n := fun _ => 0) _ _ h1 h3 none none true false false false)
        (Nat.zero_le _) (by lit_decide),
      calleeSide_of_fill (ks := 0) (decrypt_fill (n := fun _ => 0) _ _ h1 h3 none none true false false false)
        (Nat.zero_le _) (by lit_decide)⟩

open Gcm.X86_64.Stitch (CtxMode) in
/-- `i.blkM (some st)` for loops `st` on prepared powers, those named `n`,
meet what the cleanup of their callers needs of them, at the level
`i.lv n.lv`, from their code over stubs (`hae`, `had`, by `lit_decide`). -/
theorem blkM_prep_sides {M : CtxMode} (i : GcmImpl) (n : StitchName) (st : StitchCode M true) (e d : String)
    (hst : st.enc = n.encR ∧ st.dec = n.decR ∧ st.full = n.fullR ∧ st.fullD = n.fullDR ∧ st.small = n.smallR ∧
      st.smallD = n.smallR ∧ st.small4 = n.small4R ∧ st.encS = n.encRS ∧ st.decS = n.decRS)
    (hae : stubCallee (Impl.AesGcm.X86_64.Blocks.encrypt ctrStub ghStub (some n.encR) true n.fullR n.smallR
      n.small4R (some n.encRS)) n.lv.level (fun _ => 0) 8 = true)
    (had : stubCallee (Impl.AesGcm.X86_64.Blocks.decrypt ctrStub ghStub (some n.decR) true n.fullDR n.smallR
      n.small4R (some n.decRS)) n.lv.level (fun _ => 0) 8 = true) :
    calleeSide (i.blkM (some st) e d).enc.code (i.lv n.lv).level 8 = true ∧
      calleeSide (i.blkM (some st) e d).dec.code (i.lv n.lv).level 8 = true := by
  obtain ⟨h1, -, h3⟩ := i.sides n.lv
  have hl := (i.lv_le n.lv).2.2.2
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := hst
  refine ⟨?_, ?_⟩
  · show calleeSide (Impl.AesGcm.X86_64.Blocks.encrypt i.callees.ctr i.callees.gh (some st.enc) true st.full st.small
      st.small4 (some st.encS)) _ 8 = true
    rw [e1, e3, e5, e7, e8]
    exact calleeSide_of_fill (encrypt_fill (n := fun _ => 0) _ _ h1 h3 _ _ _ _ _ _) hl hae
  · show calleeSide (Impl.AesGcm.X86_64.Blocks.decrypt i.callees.ctr i.callees.gh (some st.dec) true st.fullD st.smallD
      st.small4 (some st.decS)) _ 8 = true
    rw [e2, e4, e6, e7, e9]
    exact calleeSide_of_fill (decrypt_fill (n := fun _ => 0) _ _ h1 h3 _ _ _ _ _ _) hl had

/-- `v`'s whole-blocks functions on 48 prepared powers (`blkR`) meet what the
cleanup of their callers needs of them. -/
theorem blkR_sides (v : GcmVariant) :
    calleeSide (blkR v).enc.code v.lv.level 8 = true ∧ calleeSide (blkR v).dec.code v.lv.level 8 = true := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, _ | q, tP⟩⟩
  · exact blkM_none_sides _ _ _ _
  · exact blkM_none_sides _ _ _ _
  · cases name
    · exact blkM_prep_sides _ .vaes _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by lit_decide) (by lit_decide)
    · exact blkM_prep_sides _ .vaesAvx512 _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by lit_decide)
        (by lit_decide)
    · exact blkM_prep_sides _ .aesniAvx _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by lit_decide)
        (by lit_decide)

/-- `v`'s whole-blocks functions on 16 prepared powers (`blkR16`), as
`blkR_sides`. -/
theorem blkR16_sides (v : GcmVariant) :
    calleeSide (blkR16 v).enc.code v.lv.level 8 = true ∧ calleeSide (blkR16 v).dec.code v.lv.level 8 = true := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, _ | q, tP⟩⟩
  · exact blkM_none_sides _ _ _ _
  · cases name <;> exact blkM_none_sides _ _ _ _
  · cases name
    · exact blkM_prep_sides _ .vaes _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by lit_decide) (by lit_decide)
    · exact blkM_none_sides _ _ _ _
    · exact blkM_prep_sides _ .aesniAvx _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by lit_decide)
        (by lit_decide)

/-! ## The functions -/

open VG.Impl.StackScratch.X86_64 (withStackArgScratch)

/-- AES-GCM's callees, each a stub: the whole-blocks functions too. -/
def stub5 : Callees := ⟨ctrStub, ⟨"k", .block []⟩, ghStub, ⟨"e", .block []⟩, ⟨"d", .block []⟩⟩

/-- The stack the stubs of `stub5` stand for: the whole-blocks functions'
calls, and at most as much for the others. -/
def blkN : String → Nat := fun _ => 8

/-- What the cleanup needs of AES-GCM's callees `c`, at the level `k`. -/
structure CalleesSide (k : Nat) (c : Callees) : Prop where
  ctr : calleeSide c.ctr.code k 8 = true
  key : calleeSide c.key.code k 8 = true
  gh : calleeSide c.gh.code k 8 = true
  enc : calleeSide c.enc.code k 8 = true
  dec : calleeSide c.dec.code k 8 = true

theorem CalleesSide.mono {k k' : Nat} {c : Callees} (hk : k ≤ k') (h : CalleesSide k c) : CalleesSide k' c :=
  ⟨calleeSide_mono hk (Nat.le_refl _) h.ctr, calleeSide_mono hk (Nat.le_refl _) h.key,
    calleeSide_mono hk (Nat.le_refl _) h.gh, calleeSide_mono hk (Nat.le_refl _) h.enc,
    calleeSide_mono hk (Nat.le_refl _) h.dec⟩

/-- `v`'s callees meet `CalleesSide`. -/
theorem callees_side (v : GcmVariant) : CalleesSide v.lv.level v.impl.callees :=
  have h := v.impl.sides v.own
  ⟨calleeSide_mono (Nat.le_refl _) (Nat.zero_le 8) h.1, calleeSide_mono (Nat.le_refl _) (Nat.zero_le 8) h.2.1,
    calleeSide_mono (Nat.le_refl _) (Nat.zero_le 8) h.2.2, (blkB_sides v).1, (blkB_sides v).2⟩

/-- `v`'s callees with whole-blocks functions `B` meet `CalleesSide`, if `B` does. -/
theorem withBlk_side {M : Gcm.X86_64.Stitch.CtxMode} (v : GcmVariant) (B : BlkFn M)
    (hB : calleeSide B.enc.code v.lv.level 8 = true ∧ calleeSide B.dec.code v.lv.level 8 = true) :
    CalleesSide v.lv.level (v.impl.withBlk B) :=
  have h := callees_side v
  ⟨h.ctr, h.key, h.gh, hB.1, hB.2⟩

theorem sealCode_fill {k : Nat} (c : Callees) (h : CalleesSide k c) (s : Bool) (f : Bool) :
    Fill k blkN (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode s f stub5)) (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode s f c)) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  unfold Impl.AesGcm.X86_64.Fn.sealCode
  cases s <;> cases f <;> fill_calls_wide

theorem openCode_fill {k : Nat} (c : Callees) (h : CalleesSide k c) (s : Bool) :
    Fill k blkN (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode s stub5)) (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode s c)) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  unfold Impl.AesGcm.X86_64.Fn.openCode
  cases s <;> fill_calls_wide

theorem sealCodeP_fill {k : Nat} (c : Callees) (h : CalleesSide k c) (s : Bool) (f : Bool) :
    Fill k blkN (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCodeP s f stub5)) (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCodeP s f c)) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  unfold Impl.AesGcm.X86_64.Fn.sealCodeP
  cases s <;> cases f <;> fill_calls_wide

theorem openCodeP_fill {k : Nat} (c : Callees) (h : CalleesSide k c) (s : Bool) :
    Fill k blkN (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP s stub5)) (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP s c)) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  unfold Impl.AesGcm.X86_64.Fn.openCodeP
  cases s <;> fill_calls_wide

theorem streamEncrypt_fill {k : Nat} (c : Callees) (h : CalleesSide k c) :
    Fill k blkN (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5)) (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt c)) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  fill_calls_wide

theorem streamDecrypt_fill {k : Nat} (c : Callees) (h : CalleesSide k c) :
    Fill k blkN (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5)) (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt c)) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  fill_calls_wide

theorem sealW_of (v : GcmVariant) (s : Bool) (f : Bool) (ks : Nat) (hs : v.impl.short = s) (hf : v.impl.fin = f) (hks : ks ≤ v.lv.level)
    (ha : stubSide (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode s f stub5)) ks blkN 2624 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.sealW v.lv v.impl.short v.impl.fin v.impl.callees)
      (Spec.Gcm.sealPreparedApi.contract X86_64.abi 2624) 0 := by
  rw [← hs, ← hf] at ha
  have hf := sealCode_fill _ (callees_side v) v.impl.short v.impl.fin
  exact verifiedScrubbedAllFill (api := Spec.Gcm.sealPreparedApi) (ks := ks) (n := blkN) (a := withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode v.impl.short v.impl.fin stub5))
    (sealWPlain v) v.lv (sealPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem openW_of (v : GcmVariant) (s : Bool) (ks : Nat) (hs : v.impl.short = s) (hks : ks ≤ v.lv.level)
    (ha : stubSide (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode s stub5)) ks blkN 2632 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.openW v.lv v.impl.short v.impl.callees)
      (Spec.Gcm.openPreparedApi.contract X86_64.abi 2632) 32 := by
  rw [← hs] at ha
  have hf := openCode_fill _ (callees_side v) v.impl.short
  exact verifiedScrubbedAllFill (api := Spec.Gcm.openPreparedApi) (ks := ks) (n := blkN) (a := withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode v.impl.short stub5))
    (openWPlain v) v.lv (openPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem streamEncryptW_of (v : GcmVariant) (ks : Nat) (hks : ks ≤ v.lv.level)
    (ha : stubSide (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5)) ks blkN 2608 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamEncryptW v.lv v.impl.callees)
      (Spec.Gcm.streamEncryptPreparedApi.contract X86_64.abi 2608) 0 := by
  have hf := streamEncrypt_fill _ (callees_side v)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.streamEncryptPreparedApi) (ks := ks) (n := blkN) (a := withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5))
    ({ suffix := v.impl.suffix
       code := withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt v.impl.callees)
       stack := 2608
       verified := VG.Proof.AesGcm.Flag.streamEncrypt_keyed (Flag.streamEncrypt_of_base (streamEncrypt_framed v.impl))
       spSafe := X86_64.withStackArgScratch_spSafe (streamEncrypt_spSafe v.impl) }) v.lv (streamEncryptPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem streamDecryptW_of (v : GcmVariant) (ks : Nat) (hks : ks ≤ v.lv.level)
    (ha : stubSide (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5)) ks blkN 2608 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamDecryptW v.lv v.impl.callees)
      (Spec.Gcm.streamDecryptPreparedApi.contract X86_64.abi 2608) 0 := by
  have hf := streamDecrypt_fill _ (callees_side v)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.streamDecryptPreparedApi) (ks := ks) (n := blkN) (a := withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5))
    ({ suffix := v.impl.suffix
       code := withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt v.impl.callees)
       stack := 2608
       verified := VG.Proof.AesGcm.Flag.streamDecrypt_keyed (Flag.streamDecrypt_of_base (streamDecrypt_framed v.impl))
       spSafe := X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl) }) v.lv (streamDecryptPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem sealR_of (v : GcmVariant) (s : Bool) (f : Bool) (ks : Nat) (hs : v.impl.short = s) (hf : v.impl.fin = f) (hks : ks ≤ v.lv.level)
    (ha : stubSide (Impl.Gcm.X86_64.Flag.onFlag 48 (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCodeP s f stub5)) (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode s f stub5))) ks blkN 2624 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.sealP v.lv 48 v.impl.short v.impl.fin (v.impl.withBlk (blkR v)) v.impl.callees)
      (Spec.Gcm.sealPreparedApi.contract X86_64.abi 2624) 0 := by
  rw [← hs, ← hf] at ha
  have hp := sealCodeP_fill _ (withBlk_side v (blkR v) (blkR_sides v)) v.impl.short v.impl.fin
  have hb := sealCode_fill _ (callees_side v) v.impl.short v.impl.fin
  have hf := Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 48))
    (Fill.ite .ae (Fill.seq (Fill.seq (Fill.block []) (Fill.block [])) hp) hb)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.sealPreparedApi) (ks := ks) (n := blkN) (a := Impl.Gcm.X86_64.Flag.onFlag 48 (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCodeP v.impl.short v.impl.fin stub5)) (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode v.impl.short v.impl.fin stub5)))
    (sealRPlain v) v.lv (sealPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem openR_of (v : GcmVariant) (s : Bool) (ks : Nat) (hs : v.impl.short = s) (hks : ks ≤ v.lvA.level)
    (ha : stubSide (Impl.Gcm.X86_64.Flag.onFlag 48 (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP s stub5)) (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode s stub5))) ks blkN 2632 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.openP v.lvA 48 v.impl.short (v.impl.withBlk (blkR v)) v.impl.callees)
      (Spec.Gcm.openPreparedApi.contract X86_64.abi 2632) 32 := by
  rw [← hs] at ha
  have hp := openCodeP_fill _ (CalleesSide.mono v.lv_le_lvA (withBlk_side v (blkR v) (blkR_sides v))) v.impl.short
  have hb := openCode_fill _ (CalleesSide.mono v.lv_le_lvA (callees_side v)) v.impl.short
  have hf := Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 48))
    (Fill.ite .ae (Fill.seq (Fill.seq (Fill.block []) (Fill.block [])) hp) hb)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.openPreparedApi) (ks := ks) (n := blkN) (a := Impl.Gcm.X86_64.Flag.onFlag 48 (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP v.impl.short stub5)) (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode v.impl.short stub5)))
    (openRPlain v) v.lvA (openPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem streamEncryptR_of (v : GcmVariant) (ks : Nat) (hks : ks ≤ v.lv.level)
    (ha : stubSide (Impl.Gcm.X86_64.Flag.onFlag 48 (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5)) (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5))) ks blkN 2608 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamEncryptP v.lv 48 (v.impl.withBlk (blkR v)) v.impl.callees)
      (Spec.Gcm.streamEncryptPreparedApi.contract X86_64.abi 2608) 0 := by
  have hp := streamEncrypt_fill _ (withBlk_side v (blkR v) (blkR_sides v))
  have hb := streamEncrypt_fill _ (callees_side v)
  have hf := Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 48))
    (Fill.ite .ae (Fill.seq (Fill.seq (Fill.block []) (Fill.block [])) hp) hb)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.streamEncryptPreparedApi) (ks := ks) (n := blkN) (a := Impl.Gcm.X86_64.Flag.onFlag 48 (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5)) (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5)))
    ({ suffix := v.impl.suffix
       code := streamEncryptCodeF v
       stack := 2608
       verified := VG.Proof.AesGcm.Flag.streamEncrypt_keyed
         (Flag.streamEncrypt_ofB (Or.inr rfl) (streamEncryptCodeF_verified v))
       spSafe := streamEncryptCodeF_spAll v }) v.lv (streamEncryptPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem streamDecryptR_of (v : GcmVariant) (ks : Nat) (hks : ks ≤ v.lv.level)
    (ha : stubSide (Impl.Gcm.X86_64.Flag.onFlag 48 (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5)) (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5))) ks blkN 2608 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamDecryptP v.lv 48 (v.impl.withBlk (blkR v)) v.impl.callees)
      (Spec.Gcm.streamDecryptPreparedApi.contract X86_64.abi 2608) 0 := by
  have hp := streamDecrypt_fill _ (withBlk_side v (blkR v) (blkR_sides v))
  have hb := streamDecrypt_fill _ (callees_side v)
  have hf := Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 48))
    (Fill.ite .ae (Fill.seq (Fill.seq (Fill.block []) (Fill.block [])) hp) hb)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.streamDecryptPreparedApi) (ks := ks) (n := blkN) (a := Impl.Gcm.X86_64.Flag.onFlag 48 (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5)) (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5)))
    ({ suffix := v.impl.suffix
       code := Impl.Gcm.X86_64.Flag.onFlag 48
         (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt (v.impl.withBlk (blkR v))))
         (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt v.impl.callees))
       stack := 2608
       verified := VG.Proof.AesGcm.Flag.streamDecrypt_keyed (Flag.streamDecrypt_onFlag
         (streamDecryptPrepared_framed v.impl (blkR v)) (streamDecrypt_framed v.impl))
       spSafe := VG.X86_64.onFlag_spSafe
         (X86_64.withStackArgScratch_spSafe (streamDecryptM_spSafe v.impl (blkR v)))
         (X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl)) }) v.lv (streamDecryptPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem sealR16_of (v : GcmVariant) (r : R16 v) (s : Bool) (f : Bool) (ks : Nat) (hs : v.impl.short = s) (hf : v.impl.fin = f) (hks : ks ≤ v.lv.level)
    (ha : stubSide (Impl.Gcm.X86_64.Flag.onFlag 16 (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCodeP s f stub5)) (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode s f stub5))) ks blkN 2624 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.sealP v.lv 16 v.impl.short v.impl.fin (v.impl.withBlk (blkR16 v)) v.impl.callees)
      (Spec.Gcm.sealPreparedApi.contract X86_64.abi 2624) 0 := by
  rw [← hs, ← hf] at ha
  have hp := sealCodeP_fill _ (withBlk_side v (blkR16 v) (blkR16_sides v)) v.impl.short v.impl.fin
  have hb := sealCode_fill _ (callees_side v) v.impl.short v.impl.fin
  have hf := Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 16))
    (Fill.ite .ae (Fill.seq (Fill.seq (Fill.block []) (Fill.block [])) hp) hb)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.sealPreparedApi) (ks := ks) (n := blkN) (a := Impl.Gcm.X86_64.Flag.onFlag 16 (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCodeP v.impl.short v.impl.fin stub5)) (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode v.impl.short v.impl.fin stub5)))
    (sealF16Plain v r) v.lv (sealPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem openR16_of (v : GcmVariant) (r : R16 v) (s : Bool) (ks : Nat) (hs : v.impl.short = s) (hks : ks ≤ v.lvA.level)
    (ha : stubSide (Impl.Gcm.X86_64.Flag.onFlag 16 (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP s stub5)) (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode s stub5))) ks blkN 2632 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.openP v.lvA 16 v.impl.short (v.impl.withBlk (blkR16 v)) v.impl.callees)
      (Spec.Gcm.openPreparedApi.contract X86_64.abi 2632) 32 := by
  rw [← hs] at ha
  have hp := openCodeP_fill _ (CalleesSide.mono v.lv_le_lvA (withBlk_side v (blkR16 v) (blkR16_sides v))) v.impl.short
  have hb := openCode_fill _ (CalleesSide.mono v.lv_le_lvA (callees_side v)) v.impl.short
  have hf := Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 16))
    (Fill.ite .ae (Fill.seq (Fill.seq (Fill.block []) (Fill.block [])) hp) hb)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.openPreparedApi) (ks := ks) (n := blkN) (a := Impl.Gcm.X86_64.Flag.onFlag 16 (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP v.impl.short stub5)) (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode v.impl.short stub5)))
    (openR16Plain v r) v.lvA (openPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem streamEncryptR16_of (v : GcmVariant) (ks : Nat) (hks : ks ≤ v.lv.level)
    (ha : stubSide (Impl.Gcm.X86_64.Flag.onFlag 16 (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5)) (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5))) ks blkN 2608 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamEncryptP v.lv 16 (v.impl.withBlk (blkR16 v)) v.impl.callees)
      (Spec.Gcm.streamEncryptPreparedApi.contract X86_64.abi 2608) 0 := by
  have hp := streamEncrypt_fill _ (withBlk_side v (blkR16 v) (blkR16_sides v))
  have hb := streamEncrypt_fill _ (callees_side v)
  have hf := Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 16))
    (Fill.ite .ae (Fill.seq (Fill.seq (Fill.block []) (Fill.block [])) hp) hb)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.streamEncryptPreparedApi) (ks := ks) (n := blkN) (a := Impl.Gcm.X86_64.Flag.onFlag 16 (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5)) (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5)))
    ({ suffix := v.impl.suffix
       code := streamEncryptCodeF16 v
       stack := 2608
       verified := VG.Proof.AesGcm.Flag.streamEncrypt_keyed
         (Flag.streamEncrypt_ofB (Or.inl rfl) (streamEncryptCodeF16_verified v))
       spSafe := streamEncryptCodeF16_spAll v }) v.lv (streamEncryptPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem streamDecryptR16_of (v : GcmVariant) (ks : Nat) (hks : ks ≤ v.lv.level)
    (ha : stubSide (Impl.Gcm.X86_64.Flag.onFlag 16 (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5)) (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5))) ks blkN 2608 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamDecryptP v.lv 16 (v.impl.withBlk (blkR16 v)) v.impl.callees)
      (Spec.Gcm.streamDecryptPreparedApi.contract X86_64.abi 2608) 0 := by
  have hp := streamDecrypt_fill _ (withBlk_side v (blkR16 v) (blkR16_sides v))
  have hb := streamDecrypt_fill _ (callees_side v)
  have hf := Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 16))
    (Fill.ite .ae (Fill.seq (Fill.seq (Fill.block []) (Fill.block [])) hp) hb)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.streamDecryptPreparedApi) (ks := ks) (n := blkN) (a := Impl.Gcm.X86_64.Flag.onFlag 16 (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5)) (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5)))
    ({ suffix := v.impl.suffix
       code := Impl.Gcm.X86_64.Flag.onFlag 16
         (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt (v.impl.withBlk (blkR16 v))))
         (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt v.impl.callees))
       stack := 2608
       verified := VG.Proof.AesGcm.Flag.streamDecrypt_keyed (Flag.streamDecrypt_onFlag16
         (streamDecryptPrepared16_framed v.impl (blkR16 v)) (streamDecrypt_framed v.impl))
       spSafe := VG.X86_64.onFlag_spSafe
         (X86_64.withStackArgScratch_spSafe (streamDecryptM_spSafe v.impl (blkR16 v)))
         (X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl)) }) v.lv (streamDecryptPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

/-! ## By the kind of interleaved loops -/

/-- `Spec.Gcm.sealPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `sealW_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem sealW_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.sealW v.lv v.impl.short v.impl.fin v.impl.callees)
      (Spec.Gcm.sealPreparedApi.contract X86_64.abi 2624) 0 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact sealW_of _ false false 0 rfl rfl (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact sealW_of _ false false 1 rfl rfl (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact sealW_of _ true false 2 rfl rfl (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact sealW_of _ false true 1 rfl rfl (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.openPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `openW_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem openW_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.openW v.lv v.impl.short v.impl.callees)
      (Spec.Gcm.openPreparedApi.contract X86_64.abi 2632) 32 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact openW_of _ false 0 rfl (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact openW_of _ false 1 rfl (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact openW_of _ true 2 rfl (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact openW_of _ false 1 rfl (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.streamEncryptPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `streamEncryptW_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem streamEncryptW_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamEncryptW v.lv v.impl.callees)
      (Spec.Gcm.streamEncryptPreparedApi.contract X86_64.abi 2608) 0 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact streamEncryptW_of _ 0 (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact streamEncryptW_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact streamEncryptW_of _ 2 (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact streamEncryptW_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.streamDecryptPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `streamDecryptW_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem streamDecryptW_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamDecryptW v.lv v.impl.callees)
      (Spec.Gcm.streamDecryptPreparedApi.contract X86_64.abi 2608) 0 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact streamDecryptW_of _ 0 (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact streamDecryptW_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact streamDecryptW_of _ 2 (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact streamDecryptW_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.sealPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `sealR_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem sealR_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.sealP v.lv 48 v.impl.short v.impl.fin (v.impl.withBlk (blkR v)) v.impl.callees)
      (Spec.Gcm.sealPreparedApi.contract X86_64.abi 2624) 0 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact sealR_of _ false false 0 rfl rfl (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact sealR_of _ false false 1 rfl rfl (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact sealR_of _ true false 2 rfl rfl (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact sealR_of _ false true 1 rfl rfl (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.openPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `openR_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem openR_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.openP v.lvA 48 v.impl.short (v.impl.withBlk (blkR v)) v.impl.callees)
      (Spec.Gcm.openPreparedApi.contract X86_64.abi 2632) 32 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact openR_of _ false 1 rfl (GcmImpl.lv_le _ ((VecLevel.sse).join .avx)).2.2.2 (by lit_decide)
  · cases name
    · exact openR_of _ false 1 rfl (GcmImpl.lv_le _ ((StitchName.lv .vaes).join .avx)).2.2.2 (by lit_decide)
    · exact openR_of _ true 2 rfl (GcmImpl.lv_le _ ((StitchName.lv .vaesAvx512).join .avx)).2.2.2 (by lit_decide)
    · exact openR_of _ false 1 rfl (GcmImpl.lv_le _ ((StitchName.lv .aesniAvx).join .avx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.streamEncryptPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `streamEncryptR_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem streamEncryptR_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamEncryptP v.lv 48 (v.impl.withBlk (blkR v)) v.impl.callees)
      (Spec.Gcm.streamEncryptPreparedApi.contract X86_64.abi 2608) 0 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact streamEncryptR_of _ 0 (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact streamEncryptR_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact streamEncryptR_of _ 2 (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact streamEncryptR_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.streamDecryptPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `streamDecryptR_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem streamDecryptR_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamDecryptP v.lv 48 (v.impl.withBlk (blkR v)) v.impl.callees)
      (Spec.Gcm.streamDecryptPreparedApi.contract X86_64.abi 2608) 0 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact streamDecryptR_of _ 0 (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact streamDecryptR_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact streamDecryptR_of _ 2 (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact streamDecryptR_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.sealPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `sealR16_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem sealR16_scrubbed (v : GcmVariant) (r : R16 v) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.sealP v.lv 16 v.impl.short v.impl.fin (v.impl.withBlk (blkR16 v)) v.impl.callees)
      (Spec.Gcm.sealPreparedApi.contract X86_64.abi 2624) 0 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact sealR16_of _ r false false 0 rfl rfl (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact sealR16_of _ r false false 1 rfl rfl (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact sealR16_of _ r true false 2 rfl rfl (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact sealR16_of _ r false true 1 rfl rfl (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.openPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `openR16_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem openR16_scrubbed (v : GcmVariant) (r : R16 v) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.openP v.lvA 16 v.impl.short (v.impl.withBlk (blkR16 v)) v.impl.callees)
      (Spec.Gcm.openPreparedApi.contract X86_64.abi 2632) 32 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact openR16_of _ r false 1 rfl (GcmImpl.lv_le _ ((VecLevel.sse).join .avx)).2.2.2 (by lit_decide)
  · cases name
    · exact openR16_of _ r false 1 rfl (GcmImpl.lv_le _ ((StitchName.lv .vaes).join .avx)).2.2.2 (by lit_decide)
    · exact openR16_of _ r true 2 rfl (GcmImpl.lv_le _ ((StitchName.lv .vaesAvx512).join .avx)).2.2.2 (by lit_decide)
    · exact openR16_of _ r false 1 rfl (GcmImpl.lv_le _ ((StitchName.lv .aesniAvx).join .avx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.streamEncryptPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `streamEncryptR16_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem streamEncryptR16_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamEncryptP v.lv 16 (v.impl.withBlk (blkR16 v)) v.impl.callees)
      (Spec.Gcm.streamEncryptPreparedApi.contract X86_64.abi 2608) 0 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact streamEncryptR16_of _ 0 (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact streamEncryptR16_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact streamEncryptR16_of _ 2 (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact streamEncryptR16_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.streamDecryptPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `streamDecryptR16_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem streamDecryptR16_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamDecryptP v.lv 16 (v.impl.withBlk (blkR16 v)) v.impl.callees)
      (Spec.Gcm.streamDecryptPreparedApi.contract X86_64.abi 2608) 0 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact streamDecryptR16_of _ 0 (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact streamDecryptR16_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact streamDecryptR16_of _ 2 (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact streamDecryptR16_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

end VG.Proof.AesGcm.X86_64

/-!
## AES-GCM's `vg_aes_gcm_open_to_prepared` on x86-64, without secret residue

On the key context, `vg_aes_gcm_open_to_prepared` calls `vg_aes_gcm_open_split`
(`openSplitFnB`), which calls the callees and `vg_aes_gcm_decrypt_blocks_to`
(`blkToDecB`), which calls `vg_ghash` and the out-of-place `vg_aes_ctr32_to`
(`GcmVariant.ctrTo`). Each is evaluated once over stubs of what it calls
(`calleeSide_of_fill`), and the function over a stub of the first
(`verifiedScrubbedAllFill`), at the level `GcmVariant.lvTW` (`lvT` on prepared powers).
-/

namespace VG.Proof.AesGcm.X86_64

open VG.X86_64 VG.X86_64.Scrub
open VG.Impl.Scrub.X86_64 (VecLevel)
open VG.Impl.AesGcm.X86_64 (Callees Fn)
open VG.Impl.StackScratch.X86_64 (withStackArgScratch)

/-- The level of the vector instructions of the out-of-place loops named `n`. -/
def StitchToName.lv : StitchToName → VecLevel
  | .vaes => .avx
  | .vaesAvx512 => .evex
  | .aesniAvx => .avx

/-- The level of `v`'s out-of-place loops, if any. -/
def GcmVariant.toLv (v : GcmVariant) : VecLevel :=
  match v.stitch with
  | some p => (p.toPart.map (·.name.lv)).getD .sse
  | none => .sse

/-- The level of the cleanup of `v`'s `open_to`: `lvA`'s, its out-of-place
`vg_aes_ctr32_to`'s and its out-of-place loops'. -/
def GcmVariant.lvT (v : GcmVariant) : VecLevel := (v.lvA.join v.ctrTo.level).join v.toLv

theorem GcmVariant.lvA_le_lvT (v : GcmVariant) : v.lvA.level ≤ v.lvT.level :=
  Nat.le_trans (level_join_left _ _) (level_join_left _ _)

theorem GcmVariant.ctrTo_le_lvT (v : GcmVariant) : v.ctrTo.level.level ≤ v.lvT.level :=
  Nat.le_trans (level_join_right _ _) (level_join_left _ _)

theorem GcmVariant.toLv_le_lvT (v : GcmVariant) : v.toLv.level ≤ v.lvT.level := level_join_right _ _

/-- The level of the cleanup of `v`'s `open_to` on the key context: `lv`'s
and its out-of-place `vg_aes_ctr32_to`'s. -/
def GcmVariant.lvTW (v : GcmVariant) : VecLevel := v.lv.join v.ctrTo.level

theorem join_mono_left {a b : VecLevel} (c : VecLevel) (h : a.level ≤ b.level) :
    (a.join c).level ≤ (b.join c).level := by
  revert h; cases a <;> cases b <;> cases c <;> decide

theorem GcmVariant.lvTW_le_lvT (v : GcmVariant) : v.lvTW.level ≤ v.lvT.level :=
  Nat.le_trans (join_mono_left _ v.lv_le_lvA) (level_join_left _ _)

theorem GcmVariant.one_le_lvT (v : GcmVariant) : 1 ≤ v.lvT.level :=
  Nat.le_trans (Nat.le_trans (level_join_right v.own .avx) (v.impl.lv_le _).2.2.2) v.lvA_le_lvT

/-- The stub of `vg_aes_ctr32_to`. -/
def ctrToStub : Fn := ⟨"t", .block []⟩

/-- The stub of `vg_aes_gcm_decrypt_blocks_to`. -/
def toDecStub : Fn := ⟨"T", .block []⟩

/-- The stub of `vg_aes_gcm_open_split`. -/
def splitStub : Fn := ⟨"S", .block []⟩

theorem decryptTo_fill {k : Nat} {n : String → Nat} (g c : Fn) (hg : calleeSide g.code k (n "g") = true)
    (hc : calleeSide c.code k (n "t") = true) :
    Fill k n (Impl.AesGcm.X86_64.BlocksToDec.decryptTo ghStub ctrToStub)
      (Impl.AesGcm.X86_64.BlocksToDec.decryptTo g c) := by
  fill_calls_wide

theorem openSplit_fill {k : Nat} {n : String → Nat} (c : Callees) (T : Fn)
    (h1 : calleeSide c.ctr.code k (n "c") = true) (h3 : calleeSide c.gh.code k (n "g") = true)
    (hT : calleeSide T.code k (n "T") = true) :
    Fill k n (Impl.AesGcm.X86_64.OpenSplit.openSplit stub5 toDecStub)
      (Impl.AesGcm.X86_64.OpenSplit.openSplit c T) := by
  fill_calls_wide

/-- `openSplit`'s code over stubs, evaluated once. -/
theorem openSplit_stub : stubCallee (Impl.AesGcm.X86_64.OpenSplit.openSplit stub5 toDecStub) 0 (fun _ => 24) 56 = true := by
  lit_decide

theorem openToSplit_fill {k : Nat} {n : String → Nat} (S : Fn) (hS : calleeSide S.code k (n "S") = true) :
    Fill k n (withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit splitStub))
      (withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit S)) := by
  fill_calls_wide

/-- `v`'s callees meet `CalleesSide` at the level `lvTW`. -/
theorem callees_sideTW (v : GcmVariant) : CalleesSide v.lvTW.level v.impl.callees :=
  CalleesSide.mono (level_join_left _ _) (callees_side v)

/-- `v`'s callees meet `CalleesSide` at the level `lvT`. -/
theorem callees_sideT (v : GcmVariant) : CalleesSide v.lvT.level v.impl.callees :=
  CalleesSide.mono v.lvTW_le_lvT (callees_sideTW v)

/-- `v`'s `vg_aes_gcm_decrypt_blocks_to` on the key context. -/
theorem blkToDecB_side (v : GcmVariant) : calleeSide (blkToDecB v v.ctrTo).fn.code v.lvTW.level 24 = true :=
  have hl := Nat.le_trans (v.impl.lv_le v.own).2.2.1 (level_join_left _ _)
  calleeSide_of_fill (ks := 0)
    (decryptTo_fill (n := fun _ => 0) _ _ (calleeSide_mono hl (Nat.le_refl 0) v.impl.gh.side)
      (calleeSide_mono (level_join_right _ _) (Nat.le_refl 0) v.ctrTo.side))
    (Nat.zero_le _) (by lit_decide)

/-- `v`'s `vg_aes_gcm_open_split` on the key context. -/
theorem openSplitFnB_side (v : GcmVariant) : calleeSide (openSplitFnB v v.ctrTo).fn.code v.lvTW.level 56 = true :=
  have h := callees_sideTW v
  have m := fun {c : Prog isa} (hc : calleeSide c v.lvTW.level 8 = true) =>
    calleeSide_mono (Nat.le_refl _) (show 8 ≤ 24 by decide) hc
  calleeSide_of_fill (ks := 0)
    (openSplit_fill (n := fun _ => 24) _ _ (m h.ctr) (m h.gh) (blkToDecB_side v))
    (Nat.zero_le _) openSplit_stub

/-- `Spec.Gcm.openToPreparedApi`'s function on the key context, as emitted
over `v` (`Impl.AesGcm.X86_64.Fn.openToW`), meets its contract in constant
time and returns without secret residue. -/
theorem openToW_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.openToW v.lvTW (openSplitFnB v v.ctrTo).fn)
      (Spec.Gcm.openToPreparedApi.contract X86_64.abi 2776) 32 :=
  verifiedScrubbedAllFill (api := Spec.Gcm.openToPreparedApi) (ks := 0) (n := fun _ => 56)
    (a := withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit splitStub))
    (openToWPlain v) v.lvTW (openToPreparedOut _) (openToSplit_fill _ (openSplitFnB_side v))
    (Nat.zero_le _) (Nat.le_refl _)

/-! ## On prepared powers -/

/-- `open`'s code on 48 prepared powers or on the key context, over stubs. -/
theorem openCodeF_fill (v : GcmVariant) :
    Fill v.lvA.level blkN
      (Impl.Gcm.X86_64.Flag.onFlag 48 (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP v.impl.short stub5))
        (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode v.impl.short stub5)))
      (openCodeF v) :=
  Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 48)) (Fill.ite .ae
    (Fill.seq (Fill.seq (Fill.block []) (Fill.block []))
      (openCodeP_fill _ (CalleesSide.mono v.lv_le_lvA (withBlk_side v (blkR v) (blkR_sides v))) v.impl.short))
    (openCode_fill _ (CalleesSide.mono v.lv_le_lvA (callees_side v)) v.impl.short))

/-- `open`'s code on 16 prepared powers or on the key context, over stubs. -/
theorem openCodeF16_fill (v : GcmVariant) :
    Fill v.lvA.level blkN
      (Impl.Gcm.X86_64.Flag.onFlag 16 (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP v.impl.short stub5))
        (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode v.impl.short stub5)))
      (openCodeF16 v) :=
  Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 16)) (Fill.ite .ae
    (Fill.seq (Fill.seq (Fill.block []) (Fill.block []))
      (openCodeP_fill _ (CalleesSide.mono v.lv_le_lvA (withBlk_side v (blkR16 v) (blkR16_sides v))) v.impl.short))
    (openCode_fill _ (CalleesSide.mono v.lv_le_lvA (callees_side v)) v.impl.short))

theorem openCodeF_side_of (v : GcmVariant) (s : Bool) (hs : v.impl.short = s) (ks : Nat) (hks : ks ≤ v.lvA.level)
    (ha : stubCallee (Impl.Gcm.X86_64.Flag.onFlag 48 (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP s stub5))
        (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode s stub5))) ks blkN 2632 = true) :
    calleeSide (openCodeF v) v.lvA.level 2632 = true := by
  rw [← hs] at ha
  exact calleeSide_of_fill (openCodeF_fill v) hks ha

theorem openCodeF16_side_of (v : GcmVariant) (s : Bool) (hs : v.impl.short = s) (ks : Nat) (hks : ks ≤ v.lvA.level)
    (ha : stubCallee (Impl.Gcm.X86_64.Flag.onFlag 16 (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP s stub5))
        (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode s stub5))) ks blkN 2632 = true) :
    calleeSide (openCodeF16 v) v.lvA.level 2632 = true := by
  rw [← hs] at ha
  exact calleeSide_of_fill (openCodeF16_fill v) hks ha

theorem openP_stub (s : Bool) (t : Nat) (ht : t = 16 ∨ t = 48) :
    stubCallee (Impl.Gcm.X86_64.Flag.onFlag t (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP s stub5))
        (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode s stub5))) (if s then 2 else 1) blkN 2632 = true := by
  rcases ht with rfl | rfl <;> cases s <;> lit_decide

/-- `v`'s `open` on 48 prepared powers meets what the cleanup of its callers
needs of it. -/
theorem openCodeF_side (v : GcmVariant) : calleeSide (openCodeF v) v.lvA.level 2632 = true := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact openCodeF_side_of _ false rfl 1 (GcmImpl.lv_le _ ((VecLevel.sse).join .avx)).2.2.2 (openP_stub false 48 (.inr rfl))
  · cases name
    · exact openCodeF_side_of _ false rfl 1 (GcmImpl.lv_le _ ((StitchName.lv .vaes).join .avx)).2.2.2
        (openP_stub false 48 (.inr rfl))
    · exact openCodeF_side_of _ true rfl 2 (GcmImpl.lv_le _ ((StitchName.lv .vaesAvx512).join .avx)).2.2.2
        (openP_stub true 48 (.inr rfl))
    · exact openCodeF_side_of _ false rfl 1 (GcmImpl.lv_le _ ((StitchName.lv .aesniAvx).join .avx)).2.2.2
        (openP_stub false 48 (.inr rfl))

/-- `v`'s `open` on 16 prepared powers, as `openCodeF_side`. -/
theorem openCodeF16_side (v : GcmVariant) : calleeSide (openCodeF16 v) v.lvA.level 2632 = true := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact openCodeF16_side_of _ false rfl 1 (GcmImpl.lv_le _ ((VecLevel.sse).join .avx)).2.2.2 (openP_stub false 16 (.inl rfl))
  · cases name
    · exact openCodeF16_side_of _ false rfl 1 (GcmImpl.lv_le _ ((StitchName.lv .vaes).join .avx)).2.2.2
        (openP_stub false 16 (.inl rfl))
    · exact openCodeF16_side_of _ true rfl 2 (GcmImpl.lv_le _ ((StitchName.lv .vaesAvx512).join .avx)).2.2.2
        (openP_stub true 16 (.inl rfl))
    · exact openCodeF16_side_of _ false rfl 1 (GcmImpl.lv_le _ ((StitchName.lv .aesniAvx).join .avx)).2.2.2
        (openP_stub false 16 (.inl rfl))

/-- `v`'s whole-blocks functions on the flagged context of 48 powers (`blkF`). -/
theorem blkF_sides (v : GcmVariant) :
    calleeSide (blkF v).enc.code v.lv.level 8 = true ∧ calleeSide (blkF v).dec.code v.lv.level 8 = true := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, _ | q, tP⟩⟩
  · exact blkM_none_sides _ _ _ _
  · exact blkM_none_sides _ _ _ _
  · cases name
    · exact blkM_prep_sides _ .vaes _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by lit_decide) (by lit_decide)
    · exact blkM_prep_sides _ .vaesAvx512 _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by lit_decide)
        (by lit_decide)
    · exact blkM_prep_sides _ .aesniAvx _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by lit_decide)
        (by lit_decide)

/-- `v`'s whole-blocks functions on the flagged context of 16 powers (`blkF16`). -/
theorem blkF16_sides (v : GcmVariant) :
    calleeSide (blkF16 v).enc.code v.lv.level 8 = true ∧ calleeSide (blkF16 v).dec.code v.lv.level 8 = true := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, _ | q, tP⟩⟩
  · exact blkM_none_sides _ _ _ _
  · cases name <;> exact blkM_none_sides _ _ _ _
  · cases name
    · exact blkM_prep_sides _ .vaes _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by lit_decide) (by lit_decide)
    · exact blkM_none_sides _ _ _ _
    · exact blkM_prep_sides _ .aesniAvx _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by lit_decide)
        (by lit_decide)

theorem toDec_fill {k : Nat} {n : String → Nat} (dec : Fn) (hd : calleeSide dec.code k (n "d") = true)
    (P : Option (Prog isa)) (al : Bool) :
    Fill k n (Impl.AesGcm.X86_64.BlocksToDec.decrypt ⟨"d", .block []⟩ P al)
      (Impl.AesGcm.X86_64.BlocksToDec.decrypt dec P al) := by
  cases P <;> fill_calls_wide

/-- `BlocksToDec.decrypt` over stubs, with the out-of-place loops named `n`
if any, evaluated once for each. -/
theorem toDec_stub : (n : Option StitchToName) →
    stubCallee (Impl.AesGcm.X86_64.BlocksToDec.decrypt ⟨"d", .block []⟩ (n.map StitchToName.decToR) true)
      ((n.map StitchToName.lv).getD .sse).level (fun _ => 8) 24 = true
  | none => by lit_decide
  | some .vaes => by lit_decide
  | some .vaesAvx512 => by lit_decide
  | some .aesniAvx => by lit_decide

theorem toDecF_side_of (v : GcmVariant) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
    (hB : calleeSide B.dec.code v.lv.level 8 = true) (st : Option (StitchToDecCode M true)) (n : Option StitchToName)
    (hst : st.map (·.dec) = n.map StitchToName.decToR) (hn : ((n.map StitchToName.lv).getD .sse).level ≤ v.lvT.level) :
    calleeSide (BlkToDecFn.ofBlocks "" B st).fn.code v.lvT.level 24 = true := by
  show calleeSide (Impl.AesGcm.X86_64.BlocksToDec.decrypt B.dec (st.map (·.dec)) true) _ 24 = true
  rw [hst]
  exact calleeSide_of_fill (toDec_fill (n := fun _ => 8) _
    (calleeSide_mono (Nat.le_trans v.lv_le_lvA v.lvA_le_lvT) (Nat.le_refl _) hB) _ true) hn (toDec_stub n)

/-- `v`'s `vg_aes_gcm_decrypt_blocks_to_prepared` meets what the cleanup of
its callers needs of it. -/
theorem blkToDecF_side (v : GcmVariant) : calleeSide (blkToDecF v).fn.code v.lvT.level 24 = true := by
  have hB := (blkF_sides v).2
  have hl := v.toLv_le_lvT
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, _ | ⟨tname, tpiece, tpP, tpR, _ | q⟩⟩⟩
  · exact toDecF_side_of _ _ hB _ none rfl (Nat.zero_le _)
  · exact toDecF_side_of _ _ hB _ none rfl (Nat.zero_le _)
  · exact toDecF_side_of _ _ hB _ none rfl (Nat.zero_le _)
  · cases tname
    · exact toDecF_side_of _ _ hB _ (some .vaes) rfl hl
    · exact toDecF_side_of _ _ hB _ (some .vaesAvx512) rfl hl
    · exact toDecF_side_of _ _ hB _ (some .aesniAvx) rfl hl

/-- `v`'s `vg_aes_gcm_open_split_prepared`, as `openSplitFnB_side`. -/
theorem openSplitFnF_side (v : GcmVariant) : calleeSide (openSplitFnF v).fn.code v.lvT.level 56 = true :=
  have h := callees_sideT v
  have m := fun {c : Prog isa} (hc : calleeSide c v.lvT.level 8 = true) =>
    calleeSide_mono (Nat.le_refl _) (show 8 ≤ 24 by decide) hc
  calleeSide_of_fill (ks := 0)
    (openSplit_fill (n := fun _ => 24) _ _ (m h.ctr) (m h.gh) (blkToDecF_side v))
    (Nat.zero_le _) openSplit_stub

/-- `v`'s `vg_aes_gcm_decrypt_blocks_to_prepared16` meets what the cleanup of
its callers needs of it. -/
theorem blkToDecF16_side (v : GcmVariant) : calleeSide (blkToDecF16 v).fn.code v.lvT.level 24 = true := by
  have hB := (blkF16_sides v).2
  have hl := v.toLv_le_lvT
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, _ | ⟨tname, tpiece, tpP, tpR, _ | q⟩⟩⟩
  · exact toDecF_side_of _ _ hB _ none rfl (Nat.zero_le _)
  · exact toDecF_side_of _ _ hB _ none rfl (Nat.zero_le _)
  · exact toDecF_side_of _ _ hB _ none rfl (Nat.zero_le _)
  · cases tname
    · exact toDecF_side_of _ _ hB _ (some .vaes) rfl hl
    · exact toDecF_side_of _ _ hB _ none rfl (Nat.zero_le _)
    · exact toDecF_side_of _ _ hB _ (some .aesniAvx) rfl hl

/-- `v`'s `vg_aes_gcm_open_split_prepared16`, as `openSplitFnB_side`. -/
theorem openSplitFnF16_side (v : GcmVariant) : calleeSide (openSplitFnF16 v).fn.code v.lvT.level 56 = true :=
  have h := callees_sideT v
  have m := fun {c : Prog isa} (hc : calleeSide c v.lvT.level 8 = true) =>
    calleeSide_mono (Nat.le_refl _) (show 8 ≤ 24 by decide) hc
  calleeSide_of_fill (ks := 0)
    (openSplit_fill (n := fun _ => 24) _ _ (m h.ctr) (m h.gh) (blkToDecF16_side v))
    (Nat.zero_le _) openSplit_stub

theorem openToStackF_eq (v : GcmVariant) : openToStackF v = 2776 := by
  unfold openToStackF openToStackR openToStack; split <;> rfl

theorem openToStackF16_eq (v : GcmVariant) : openToStackF16 v = 2776 := by
  unfold openToStackF16 openToStackR16 openToStack; split <;> rfl

/-- The stub of `vg_aes_gcm_open_prepared<suffix>_core`. -/
def openStubO : Fn := ⟨"O", .block []⟩

/-- The stub of `vg_aes_gcm_open_split_prepared`. -/
def splitStubF : Fn := ⟨"F", .block []⟩

/-- The stack the stubs of `open_to` on prepared powers stand for. -/
def openToN : String → Nat := fun s => if s = "O" then 2632 else 56

theorem openToP_fill {k : Nat} {n : String → Nat} (t : Nat) (sel : Bool)
    (w : Impl.ChaCha20Poly1305.X86_64.SealGather.Width) (fO fS S : Fn)
    (hO : calleeSide fO.code k (n "O") = true) (hF : calleeSide fS.code k (n "F") = true)
    (hS : calleeSide S.code k (n "S") = true) :
    Fill k n (Impl.Gcm.X86_64.Flag.onFlag t (Impl.AesGcm.X86_64.Fn.openToCodeP sel w openStubO splitStubF)
        (withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit splitStub)))
      (Impl.Gcm.X86_64.Flag.onFlag t (Impl.AesGcm.X86_64.Fn.openToCodeP sel w fO fS)
        (withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit S))) := by
  unfold Impl.AesGcm.X86_64.Fn.openToCodeP
  fill_calls_wide

/-- The level of `copyBytes w`: SSE's, VEX's or EVEX's. -/
def widthLv : Impl.ChaCha20Poly1305.X86_64.SealGather.Width → Nat
  | .x16 => 0
  | .y32 => 1
  | .z64 => 2

theorem copyW_cases (i : GcmImpl) : i.copyW = .x16 ∨ i.copyW = .y32 := by
  unfold GcmImpl.copyW; split
  · exact .inr rfl
  · exact .inl rfl

theorem openToP_stub (t : Nat) (ht : t = 16 ∨ t = 48) (sel : Bool) (w : Impl.ChaCha20Poly1305.X86_64.SealGather.Width)
    (hw : w = .x16 ∨ w = .y32) :
    stubSide (Impl.Gcm.X86_64.Flag.onFlag t (Impl.AesGcm.X86_64.Fn.openToCodeP sel w openStubO splitStubF)
        (withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit splitStub)))
      (widthLv w) openToN 2776 [] = true := by
  rcases ht with rfl | rfl <;> rcases hw with rfl | rfl <;> cases sel <;> lit_decide

theorem width_le (v : GcmVariant) (w : Impl.ChaCha20Poly1305.X86_64.SealGather.Width) (hw : w = .x16 ∨ w = .y32) :
    widthLv w ≤ v.lvT.level := by
  rcases hw with rfl | rfl
  · exact Nat.zero_le _
  · exact v.one_le_lvT

/-- `Spec.Gcm.openToPreparedApi`'s function over `v` on 48 prepared powers or
the key context, as emitted (`Impl.AesGcm.X86_64.Fn.openToP`), meets its
contract in constant time and returns without secret residue. -/
theorem openToR_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target
      (Impl.AesGcm.X86_64.Fn.openToP v.lvT 48 v.stitchToDecR.isSome v.impl.copyW (openFnF v).fn (openSplitFnF v).fn
        (openSplitFnB v v.ctrTo).fn)
      (Spec.Gcm.openToPreparedApi.contract X86_64.abi 2776) 32 := by
  have hO := calleeSide_mono v.lvA_le_lvT (show 2632 ≤ openToN "O" by decide) (openCodeF_side v)
  have hF := calleeSide_mono (Nat.le_refl _) (show 56 ≤ openToN "F" by decide) (openSplitFnF_side v)
  have hS := calleeSide_mono v.lvTW_le_lvT (show 56 ≤ openToN "S" by decide) (openSplitFnB_side v)
  have ha := openToP_stub 48 (.inr rfl) v.stitchToDecR.isSome v.impl.copyW (copyW_cases v.impl)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.openToPreparedApi) (n := openToN) (rb := 32) (stack := 2776)
    (a := Impl.Gcm.X86_64.Flag.onFlag 48 (Impl.AesGcm.X86_64.Fn.openToCodeP v.stitchToDecR.isSome v.impl.copyW openStubO splitStubF)
      (withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit splitStub)))
    { suffix := v.impl.suffix
      code := Impl.Gcm.X86_64.Flag.onFlag 48 (openToCodeF v) (openToCode v)
      stack := 2776
      verified := VG.Proof.AesGcm.Flag.openTo_keyed (openToStackF_eq v ▸ openToCodeR_onFlag v)
      spSafe := openToCodeR_onFlag_spAll v } v.lvT (openToPreparedOut _) (openToP_fill 48 _ _ _ _ _ hO hF hS) (width_le v _ (copyW_cases v.impl)) (Nat.le_refl _)
    (ha := ha)

/-- `Spec.Gcm.openToPreparedApi`'s function over `v` on 16 prepared powers or
the key context, as emitted (`Impl.AesGcm.X86_64.Fn.openToP`), meets its
contract in constant time and returns without secret residue. -/
theorem openToR16_scrubbed (v : GcmVariant) (r : R16 v) :
    VerifiedScrubbed target
      (Impl.AesGcm.X86_64.Fn.openToP v.lvT 16 v.stitchToDecR16.isSome v.impl.copyW (openFnF16 v r).fn (openSplitFnF16 v).fn
        (openSplitFnB v v.ctrTo).fn)
      (Spec.Gcm.openToPreparedApi.contract X86_64.abi 2776) 32 := by
  have hO := calleeSide_mono v.lvA_le_lvT (show 2632 ≤ openToN "O" by decide) (openCodeF16_side v)
  have hF := calleeSide_mono (Nat.le_refl _) (show 56 ≤ openToN "F" by decide) (openSplitFnF16_side v)
  have hS := calleeSide_mono v.lvTW_le_lvT (show 56 ≤ openToN "S" by decide) (openSplitFnB_side v)
  have ha := openToP_stub 16 (.inl rfl) v.stitchToDecR16.isSome v.impl.copyW (copyW_cases v.impl)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.openToPreparedApi) (n := openToN) (rb := 32) (stack := 2776)
    (a := Impl.Gcm.X86_64.Flag.onFlag 16 (Impl.AesGcm.X86_64.Fn.openToCodeP v.stitchToDecR16.isSome v.impl.copyW openStubO splitStubF)
      (withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit splitStub)))
    { suffix := v.impl.suffix
      code := Impl.Gcm.X86_64.Flag.onFlag 16 (openToCodeF16 v r) (openToCode v)
      stack := 2776
      verified := VG.Proof.AesGcm.Flag.openTo_keyed (openToStackF16_eq v ▸ openToCodeR16_onFlag v r)
      spSafe := openToCodeR16_onFlag_spAll v r } v.lvT (openToPreparedOut _) (openToP_fill 16 _ _ _ _ _ hO hF hS) (width_le v _ (copyW_cases v.impl)) (Nat.le_refl _)
    (ha := ha)

end VG.Proof.AesGcm.X86_64

/-!
## AES-GCM's `vg_aes_gcm_seal_gather_prepared` on x86-64, without secret residue

`vg_aes_gcm_seal_gather_prepared` calls `vg_aes_gcm_seal` (`sealFn`),
`vg_aes_gcm_seal_split` (`splitFn`) and the streaming functions (`initFn`,
`aadFn`, `toFn`, `finFn`), which call the callees, the whole-blocks
functions and their out-of-place forms (`blkTo`). Each is evaluated once
over stubs of what it calls (`calleeSide_of_fill`), for each kind of
interleaved loops where its code depends on them, and the function over
stubs of the first (`verifiedScrubbedAllFill`), at the level `GcmVariant.lvG`.
-/

namespace VG.Proof.AesGcm.X86_64

open VG.X86_64 VG.X86_64.Scrub
open VG.Impl.Scrub.X86_64 (VecLevel)
open VG.Impl.AesGcm.X86_64 (Callees Fn)
open VG.Impl.StackScratch.X86_64 (withStackScratch withStackArgScratch)

/-- The level of the cleanup of `v`'s `seal_gather` on the key context:
`lv`'s and its out-of-place loops'. -/
def GcmVariant.lvG (v : GcmVariant) : VecLevel := v.lv.join v.toLv

theorem GcmVariant.lv_le_lvG (v : GcmVariant) : v.lv.level ≤ v.lvG.level := level_join_left _ _

theorem GcmVariant.toLv_le_lvG (v : GcmVariant) : v.toLv.level ≤ v.lvG.level := level_join_right _ _

theorem GcmVariant.own_le_lvG (v : GcmVariant) : v.own.level ≤ v.lvG.level :=
  Nat.le_trans (v.impl.lv_le v.own).2.2.2 v.lv_le_lvG

/-- A stub, named `s`. -/
def fnStub (s : String) : Fn := ⟨s, .block []⟩

/-! ## The streaming functions it calls -/

/-- What the cleanup needs of AES-GCM's callees `c`, at the level `k`, each
in the stack `n` says by its stub's name. -/
structure CalleesSideN (k : Nat) (n : String → Nat) (c : Callees) : Prop where
  ctr : calleeSide c.ctr.code k (n "c") = true
  key : calleeSide c.key.code k (n "k") = true
  gh : calleeSide c.gh.code k (n "g") = true
  enc : calleeSide c.enc.code k (n "e") = true
  dec : calleeSide c.dec.code k (n "d") = true

/-- The stack the stubs of `stub5` stand for, each its own: none for
`vg_aes_ctr32`, the key expansion and `vg_ghash`. -/
def blkN0 : String → Nat := fun s => if s = "e" then 8 else if s = "d" then 8 else 0

/-- `v`'s callees meet `CalleesSideN` with the stacks `blkN0`. -/
theorem callees_side0 (v : GcmVariant) : CalleesSideN v.lv.level blkN0 v.impl.callees :=
  have h := v.impl.sides v.own
  ⟨calleeSide_mono (Nat.le_refl _) (Nat.zero_le _) h.1, calleeSide_mono (Nat.le_refl _) (Nat.zero_le _) h.2.1,
    calleeSide_mono (Nat.le_refl _) (Nat.zero_le _) h.2.2,
    calleeSide_mono (Nat.le_refl _) (by simp [blkN0]) (blkB_sides v).1,
    calleeSide_mono (Nat.le_refl _) (by simp [blkN0]) (blkB_sides v).2⟩

theorem streamInitS_fill {k : Nat} {n : String → Nat} (c : Callees) (h : CalleesSideN k n c) :
    Fill k n (withStackScratch 2568 .r8 (Impl.AesGcm.X86_64.streamInit stub5))
      (withStackScratch 2568 .r8 (Impl.AesGcm.X86_64.streamInit c)) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  fill_calls_wide

theorem streamAadS_fill {k : Nat} {n : String → Nat} (c : Callees) (h : CalleesSideN k n c) :
    Fill k n (withStackScratch 2568 .r9 (Impl.AesGcm.X86_64.streamAad stub5))
      (withStackScratch 2568 .r9 (Impl.AesGcm.X86_64.streamAad c)) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  fill_calls_wide

theorem streamFinishS_fill {k : Nat} {n : String → Nat} (c : Callees) (h : CalleesSideN k n c) :
    Fill k n (withStackArgScratch 2576 0 (Impl.AesGcm.X86_64.streamFinish stub5))
      (withStackArgScratch 2576 0 (Impl.AesGcm.X86_64.streamFinish c)) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  fill_calls_wide

theorem initFn_side (v : GcmVariant) : calleeSide (initFn v.impl).fn.code v.lv.level 2576 = true :=
  calleeSide_of_fill (ks := 0) (streamInitS_fill _ (callees_side0 v)) (Nat.zero_le _) (by lit_decide)

theorem aadFn_side (v : GcmVariant) : calleeSide (aadFn v.impl).fn.code v.lv.level 2576 = true :=
  calleeSide_of_fill (ks := 0) (streamAadS_fill _ (callees_side0 v)) (Nat.zero_le _) (by lit_decide)

theorem finFn_side (v : GcmVariant) : calleeSide (finFn v.impl).fn.code v.lv.level 2584 = true :=
  calleeSide_of_fill (ks := 0) (streamFinishS_fill _ (callees_side0 v)) (Nat.zero_le _) (by lit_decide)

theorem encFn_side (v : GcmVariant) : calleeSide (encFn v.impl).fn.code v.lv.level 2608 = true :=
  calleeSide_of_fill (ks := 0) (streamEncrypt_fill _ (callees_side v)) (Nat.zero_le _) (by lit_decide)

/-! ## `vg_aes_gcm_seal` -/

theorem sealFn_side_of (v : GcmVariant) (s f : Bool) (hs : v.impl.short = s) (hf : v.impl.fin = f) (ks : Nat)
    (hks : ks ≤ v.lv.level)
    (ha : stubCallee (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode s f stub5)) ks blkN 2624 = true) :
    calleeSide (sealFn v.impl).fn.code v.lv.level 2624 = true := by
  rw [← hs, ← hf] at ha
  exact calleeSide_of_fill (sealCode_fill _ (callees_side v) v.impl.short v.impl.fin) hks ha

theorem sealFn_side (v : GcmVariant) : calleeSide (sealFn v.impl).fn.code v.lv.level 2624 = true := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact sealFn_side_of _ false false rfl rfl 0 (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact sealFn_side_of _ false false rfl rfl 1 (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact sealFn_side_of _ true false rfl rfl 2 (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact sealFn_side_of _ false true rfl rfl 1 (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

/-! ## The out-of-place whole-blocks functions -/

theorem blocksTo_fill {k : Nat} {n : String → Nat} (enc : Fn) (he : calleeSide enc.code k (n "e") = true)
    (P : Option (Prog isa)) (al F : Bool) :
    Fill k n (Impl.AesGcm.X86_64.BlocksTo.encrypt ⟨"e", .block []⟩ P al F)
      (Impl.AesGcm.X86_64.BlocksTo.encrypt enc P al F) := by
  cases P <;> fill_calls_wide

/-- `BlocksTo.encrypt` over a stub, with the out-of-place loop `P` (of the
level `l`), evaluated once for each. -/
theorem blocksTo_stub : (n : Option StitchToName) →
    stubCallee (Impl.AesGcm.X86_64.BlocksTo.encrypt ⟨"e", .block []⟩ (n.map StitchToName.enc) false
      ((n.map StitchToName.full).getD false)) ((n.map StitchToName.lv).getD .sse).level (fun _ => 8) 24 = true
  | none => by lit_decide
  | some .vaes => by lit_decide
  | some .vaesAvx512 => by lit_decide
  | some .aesniAvx => by lit_decide

theorem blkTo_side_of (v : GcmVariant) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
    (hB : calleeSide B.enc.code v.lv.level 8 = true) (st : Option (StitchToCode M false)) (n : Option StitchToName)
    (hst : st.map (·.enc) = n.map StitchToName.enc ∧ encFullTo st = (n.map StitchToName.full).getD false)
    (hn : ((n.map StitchToName.lv).getD .sse).level ≤ v.lvG.level) :
    calleeSide (StreamTo.BlkToFn.ofBlocks "" B st).fn.code v.lvG.level 24 = true := by
  show calleeSide (Impl.AesGcm.X86_64.BlocksTo.encrypt B.enc (st.map (·.enc)) false (encFullTo st)) _ 24 = true
  rw [hst.1, hst.2]
  exact calleeSide_of_fill (blocksTo_fill (n := fun _ => 8) _
    (calleeSide_mono v.lv_le_lvG (Nat.le_refl _) hB) _ false _) hn (blocksTo_stub n)

/-- `v`'s `vg_aes_gcm_encrypt_blocks_to`. -/
theorem blkTo_side (v : GcmVariant) : calleeSide (blkTo v).fn.code v.lvG.level 24 = true := by
  have hB := (blkB_sides v).1
  have hl := v.toLv_le_lvG
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, _ | ⟨tname, tpiece, tpP, tpR, tpD⟩⟩⟩
  · exact blkTo_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · exact blkTo_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · cases tname
    · exact blkTo_side_of _ _ hB _ (some .vaes) ⟨rfl, rfl⟩ hl
    · exact blkTo_side_of _ _ hB _ (some .vaesAvx512) ⟨rfl, rfl⟩ hl
    · exact blkTo_side_of _ _ hB _ (some .aesniAvx) ⟨rfl, rfl⟩ hl

theorem streamTo_fill {k : Nat} {n : String → Nat} (blk enc : Fn) (hb : calleeSide blk.code k (n "B") = true)
    (he : calleeSide enc.code k (n "E") = true) :
    Fill k n (withStackArgScratch 2232 3 (Impl.AesGcm.X86_64.StreamTo.encrypt (fnStub "B") (fnStub "E")))
      (withStackArgScratch 2232 3 (Impl.AesGcm.X86_64.StreamTo.encrypt blk enc)) := by
  fill_calls_wide

/-- The stack the stubs of `vg_aes_gcm_stream_encrypt_to` stand for. -/
def streamToN : String → Nat := fun s => if s = "B" then 24 else 2608

theorem streamTo_stub :
    stubCallee (withStackArgScratch 2232 3 (Impl.AesGcm.X86_64.StreamTo.encrypt (fnStub "B") (fnStub "E")))
      0 streamToN 4856 = true := by
  lit_decide

/-- `v`'s `vg_aes_gcm_stream_encrypt_to`. -/
theorem toFn_side (v : GcmVariant) : calleeSide (toFn v).fn.code v.lvG.level 4856 = true :=
  calleeSide_of_fill (streamTo_fill _ _ (calleeSide_mono (Nat.le_refl _) (show 24 ≤ streamToN "B" by decide) (blkTo_side v))
    (calleeSide_mono v.lv_le_lvG (show 2608 ≤ streamToN "E" by decide) (encFn_side v))) (Nat.zero_le _) streamTo_stub

/-! ## `vg_aes_gcm_seal_split` -/

/-- The stub of `vg_aes_gcm_encrypt_blocks_to`. -/
def toStub : Fn := fnStub "T"

/-- `GcmImpl.splitFin` over stubs. -/
def stubSplitFin (s f : Bool) : Prog isa :=
  if s then Impl.AesGcm.X86_64.Short.finish
  else if f then Impl.AesGcm.X86_64.Short.finishWith Impl.AesGcm.X86_64.Short.finKsA
  else Impl.AesGcm.X86_64.SealSplit.finCalls stub5

/-- `GcmImpl.splitMid` over stubs. -/
def stubSplitMid (s f : Bool) : Prog isa :=
  if s then Impl.AesGcm.X86_64.SealSplit.runShort stub5 toStub (stubSplitFin s f)
  else Impl.AesGcm.X86_64.SealSplit.run stub5 toStub (stubSplitFin s f)

/-- The stack the stubs of `seal_split` stand for. -/
def splitN : String → Nat := fun s => if s = "T" then 24 else 8

theorem splitMid_fill {k : Nat} {n : String → Nat} (i : GcmImpl) (c : Callees) (fTo : Fn)
    (h : CalleesSideN k n c) (h₀ : CalleesSideN k n i.callees) (hT : calleeSide fTo.code k (n "T") = true) :
    Fill k n (withStackArgScratch 2616 5 (Impl.AesGcm.X86_64.SealSplit.«seal» (stubSplitMid i.short i.fin)))
      (withStackArgScratch 2616 5 (Impl.AesGcm.X86_64.SealSplit.«seal» (i.splitMid c fTo))) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  obtain ⟨g1, g2, g3, ge, gd⟩ := h₀
  unfold GcmImpl.splitMid GcmImpl.splitFin stubSplitMid stubSplitFin
  fill_calls_wide

/-- `v`'s callees meet `CalleesSideN` with the stacks `splitN`. -/
theorem callees_sideS (v : GcmVariant) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) (k : Nat)
    (hk : v.lv.level ≤ k) (hB : calleeSide B.enc.code k 8 = true ∧ calleeSide B.dec.code k 8 = true) :
    CalleesSideN k splitN (v.impl.withBlk B) :=
  have h := callees_side v
  ⟨calleeSide_mono hk (by simp [splitN]) h.ctr, calleeSide_mono hk (by simp [splitN]) h.key,
    calleeSide_mono hk (by simp [splitN]) h.gh, calleeSide_mono (Nat.le_refl _) (by simp [splitN]) hB.1,
    calleeSide_mono (Nat.le_refl _) (by simp [splitN]) hB.2⟩

theorem splitFn_side_of (v : GcmVariant) (s f : Bool) (hs : v.impl.short = s) (hf : v.impl.fin = f) (ks : Nat)
    (hk : v.own.level = ks)
    (ha : stubCallee (withStackArgScratch 2616 5 (Impl.AesGcm.X86_64.SealSplit.«seal» (stubSplitMid s f))) ks splitN
      2672 = true) :
    calleeSide (splitFn v).fn.code v.lvG.level 2672 = true := by
  rw [← hs, ← hf] at ha
  have hks := v.own_le_lvG
  rw [hk] at hks
  have hB := blkB_sides v
  exact calleeSide_of_fill (splitMid_fill v.impl _ _
    (callees_sideS v v.impl.blkB _ v.lv_le_lvG ⟨calleeSide_mono v.lv_le_lvG (Nat.le_refl _) hB.1,
      calleeSide_mono v.lv_le_lvG (Nat.le_refl _) hB.2⟩)
    (callees_sideS v v.impl.blkB _ v.lv_le_lvG ⟨calleeSide_mono v.lv_le_lvG (Nat.le_refl _) hB.1,
      calleeSide_mono v.lv_le_lvG (Nat.le_refl _) hB.2⟩)
    (calleeSide_mono (Nat.le_refl _) (by simp [splitN]) (blkTo_side v))) hks ha

/-- `v`'s `vg_aes_gcm_seal_split`. -/
theorem splitFn_side (v : GcmVariant) : calleeSide (splitFn v).fn.code v.lvG.level 2672 = true := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact splitFn_side_of _ false false rfl rfl 0 rfl (by lit_decide)
  · cases name
    · exact splitFn_side_of _ false false rfl rfl 1
        rfl (by lit_decide)
    · exact splitFn_side_of _ true false rfl rfl 2
        rfl (by lit_decide)
    · exact splitFn_side_of _ false true rfl rfl 1
        rfl (by lit_decide)

/-! ## `vg_aes_gcm_seal_gather_prepared` on the key context -/

/-- The stack the stubs of `seal_gather` stand for. -/
def gatherN : String → Nat := fun s =>
  if s = "Se" ∨ s = "SeF" then 2624 else if s = "Sp" ∨ s = "SpF" then 2672 else if s = "To" ∨ s = "ToF" then 4856
  else if s = "Fi" then 2584 else if s = "I" ∨ s = "A" then 2576 else if s = "e" ∨ s = "d" then 8 else 0

theorem gather_fill {k : Nat} {n : String → Nat} (t ts : Nat) (Se Sp I A To Fi : Fn)
    (hSe : calleeSide Se.code k (n "Se") = true) (hSp : calleeSide Sp.code k (n "Sp") = true)
    (hI : calleeSide I.code k (n "I") = true) (hA : calleeSide A.code k (n "A") = true)
    (hTo : calleeSide To.code k (n "To") = true) (hFi : calleeSide Fi.code k (n "Fi") = true) :
    Fill k n (Impl.AesGcm.X86_64.Fn.sealGatherCode t ts (fnStub "Se") (fnStub "Sp") (fnStub "I") (fnStub "A")
        (fnStub "To") (fnStub "Fi"))
      (Impl.AesGcm.X86_64.Fn.sealGatherCode t ts Se Sp I A To Fi) := by
  fill_calls_wide

/-- `seal_gather` over stubs, copying below `t` bytes and sealing a first
slice of `ts` bytes in place: those of each kind of out-of-place loops. -/
theorem gather_stub : (n : Option StitchToName) →
    stubSide (Impl.AesGcm.X86_64.Fn.sealGatherCode
        (match n with | some .vaesAvx512 => 768 | some .vaes => 16384 | some .aesniAvx => 3072 | none => 2 ^ 31 - 1)
        (match n with | some .vaesAvx512 => 752 | some .vaes => 1024 | some .aesniAvx => 384 | none => 2 ^ 31 - 17)
        (fnStub "Se") (fnStub "Sp") (fnStub "I") (fnStub "A") (fnStub "To") (fnStub "Fi"))
      0 gatherN 5128 [] = true
  | none => by lit_decide
  | some .vaes => by lit_decide
  | some .vaesAvx512 => by lit_decide
  | some .aesniAvx => by lit_decide

theorem copyBelow_eq (v : GcmVariant) : copyBelow v =
    match (v.stitch.bind (·.toPart)).map (·.name) with
    | some .vaesAvx512 => 768 | some .vaes => 16384 | some .aesniAvx => 3072 | none => 2 ^ 31 - 1 := rfl

theorem splitFrom_eq (v : GcmVariant) : splitFrom v =
    match (v.stitch.bind (·.toPart)).map (·.name) with
    | some .vaesAvx512 => 752 | some .vaes => 1024 | some .aesniAvx => 384 | none => 2 ^ 31 - 17 := rfl

/-- `Spec.Gcm.sealGatherPreparedApi`'s function on the key context, as
emitted over `v` (`Impl.AesGcm.X86_64.Fn.sealGatherW`), meets its contract in
constant time and returns without secret residue. -/
theorem sealGatherW_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target
      (Impl.AesGcm.X86_64.Fn.sealGatherW v.lvG (copyBelow v) (splitFrom v) (sealFn v.impl).fn (splitFn v).fn
        (initFn v.impl).fn (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn)
      (Spec.Gcm.sealGatherPreparedApi.contract X86_64.abi 5128) 0 := by
  have hSe := calleeSide_mono v.lv_le_lvG (show 2624 ≤ gatherN "Se" by decide) (sealFn_side v)
  have hSp := calleeSide_mono (Nat.le_refl _) (show 2672 ≤ gatherN "Sp" by decide) (splitFn_side v)
  have hI := calleeSide_mono v.lv_le_lvG (show 2576 ≤ gatherN "I" by decide) (initFn_side v)
  have hA := calleeSide_mono v.lv_le_lvG (show 2576 ≤ gatherN "A" by decide) (aadFn_side v)
  have hTo := calleeSide_mono (Nat.le_refl _) (show 4856 ≤ gatherN "To" by decide) (toFn_side v)
  have hFi := calleeSide_mono v.lv_le_lvG (show 2584 ≤ gatherN "Fi" by decide) (finFn_side v)
  have ha := gather_stub ((v.stitch.bind (·.toPart)).map (·.name))
  rw [← copyBelow_eq, ← splitFrom_eq] at ha
  exact verifiedScrubbedAllFill (api := Spec.Gcm.sealGatherPreparedApi) (ks := 0) (n := gatherN) (rb := 0)
    (stack := 5128)
    (a := Impl.AesGcm.X86_64.Fn.sealGatherCode (copyBelow v) (splitFrom v) (fnStub "Se") (fnStub "Sp")
      (fnStub "I") (fnStub "A") (fnStub "To") (fnStub "Fi"))
    (sealGatherWPlain v) v.lvG (sealGatherPreparedOut _) (gather_fill _ _ _ _ _ _ _ _ hSe hSp hI hA hTo hFi)
    (Nat.zero_le _) (Nat.le_refl _) (ha := ha)

/-! ## On prepared powers: what `seal_gather` calls -/

/-- `seal`'s code on 48 prepared powers or on the key context, over stubs. -/
theorem sealCodeF_fill (v : GcmVariant) :
    Fill v.lv.level blkN
      (Impl.Gcm.X86_64.Flag.onFlag 48
        (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCodeP v.impl.short v.impl.fin stub5))
        (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode v.impl.short v.impl.fin stub5)))
      (sealCodeF v) :=
  Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 48)) (Fill.ite .ae
    (Fill.seq (Fill.seq (Fill.block []) (Fill.block []))
      (sealCodeP_fill _ (withBlk_side v (blkR v) (blkR_sides v)) v.impl.short v.impl.fin))
    (sealCode_fill _ (callees_side v) v.impl.short v.impl.fin))

/-- `seal`'s code on 16 prepared powers or on the key context, over stubs. -/
theorem sealCodeF16_fill (v : GcmVariant) :
    Fill v.lv.level blkN
      (Impl.Gcm.X86_64.Flag.onFlag 16
        (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCodeP v.impl.short v.impl.fin stub5))
        (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode v.impl.short v.impl.fin stub5)))
      (sealCodeF16 v) :=
  Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 16)) (Fill.ite .ae
    (Fill.seq (Fill.seq (Fill.block []) (Fill.block []))
      (sealCodeP_fill _ (withBlk_side v (blkR16 v) (blkR16_sides v)) v.impl.short v.impl.fin))
    (sealCode_fill _ (callees_side v) v.impl.short v.impl.fin))

theorem sealP_stub (t : Nat) (ht : t = 16 ∨ t = 48) (s f : Bool) :
    stubCallee (Impl.Gcm.X86_64.Flag.onFlag t
        (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCodeP s f stub5))
        (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode s f stub5)))
      (if s then 2 else if f then 1 else 0) blkN 2624 = true := by
  rcases ht with rfl | rfl <;> cases s <;> cases f <;> lit_decide

theorem sealCodeF_side_of (v : GcmVariant) (s f : Bool) (hs : v.impl.short = s) (hf : v.impl.fin = f)
    (hks : (if s then 2 else if f then 1 else 0) ≤ v.lv.level) :
    calleeSide (sealCodeF v) v.lv.level 2624 = true ∧ calleeSide (sealCodeF16 v) v.lv.level 2624 = true := by
  have h₁ := sealP_stub 48 (.inr rfl) s f
  have h₂ := sealP_stub 16 (.inl rfl) s f
  rw [← hs, ← hf] at h₁ h₂
  rw [← hs, ← hf] at hks
  exact ⟨calleeSide_of_fill (sealCodeF_fill v) hks h₁, calleeSide_of_fill (sealCodeF16_fill v) hks h₂⟩

/-- `v`'s `seal` on 48 and on 16 prepared powers. -/
theorem sealCodeF_sides (v : GcmVariant) :
    calleeSide (sealCodeF v) v.lv.level 2624 = true ∧ calleeSide (sealCodeF16 v) v.lv.level 2624 = true := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact sealCodeF_side_of _ false false rfl rfl (Nat.zero_le _)
  · cases name
    · exact sealCodeF_side_of _ false false rfl rfl (Nat.zero_le _)
    · exact sealCodeF_side_of _ true false rfl rfl (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2
    · exact sealCodeF_side_of _ false true rfl rfl (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2

/-- `stream_encrypt` on 48 or 16 prepared powers or on the key context, over stubs. -/
theorem streamEncP_stub (t : Nat) (ht : t = 16 ∨ t = 48) :
    stubCallee (Impl.Gcm.X86_64.Flag.onFlag t (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5))
        (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5))) 0 blkN 2608 = true := by
  rcases ht with rfl | rfl <;> lit_decide

/-- `v`'s `stream_encrypt` on 48 prepared powers. -/
theorem streamEncryptCodeF_side (v : GcmVariant) : calleeSide (streamEncryptCodeF v) v.lv.level 2608 = true :=
  calleeSide_of_fill
    (Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 48)) (Fill.ite .ae
      (Fill.seq (Fill.seq (Fill.block []) (Fill.block []))
        (streamEncrypt_fill _ (withBlk_side v (blkR v) (blkR_sides v))))
      (streamEncrypt_fill _ (callees_side v))))
    (Nat.zero_le _) (streamEncP_stub 48 (.inr rfl))

/-- `v`'s `stream_encrypt` on 16 prepared powers. -/
theorem streamEncryptCodeF16_side (v : GcmVariant) : calleeSide (streamEncryptCodeF16 v) v.lv.level 2608 = true :=
  calleeSide_of_fill
    (Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 16)) (Fill.ite .ae
      (Fill.seq (Fill.seq (Fill.block []) (Fill.block []))
        (streamEncrypt_fill _ (withBlk_side v (blkR16 v) (blkR16_sides v))))
      (streamEncrypt_fill _ (callees_side v))))
    (Nat.zero_le _) (streamEncP_stub 16 (.inl rfl))

theorem streamEncryptClr_fill {k : Nat} (c : Callees) (h : CalleesSide k c) :
    Fill k blkN (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr stub5 .avx))
      (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr c .avx)) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  fill_calls_wide

theorem streamEncClr_stub :
    stubCallee (Impl.Gcm.X86_64.Flag.onFlag 16
        (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr stub5 .avx))
        (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr stub5 .avx))) 1 blkN 2608 = true := by
  lit_decide

/-- `v`'s `stream_encrypt` on 16 prepared powers as `seal_gather` calls it
(`streamEncryptCodeF16S`), at the level `lvA`. -/
theorem streamEncryptCodeF16S_side (v : GcmVariant) :
    calleeSide (streamEncryptCodeF16S v) v.lvA.level 2608 = true := by
  unfold streamEncryptCodeF16S
  split
  · exact calleeSide_of_fill
      (Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 16)) (Fill.ite .ae
        (Fill.seq (Fill.seq (Fill.block []) (Fill.block []))
          (streamEncryptClr_fill _ (CalleesSide.mono v.lv_le_lvA (withBlk_side v (blkR16 v) (blkR16_sides v)))))
        (streamEncryptClr_fill _ (CalleesSide.mono v.lv_le_lvA (callees_side v)))))
      (Nat.le_trans (level_join_right v.own .avx) (v.impl.lv_le _).2.2.2) streamEncClr_stub
  · exact calleeSide_mono v.lv_le_lvA (Nat.le_refl _) (streamEncryptCodeF16_side v)

/-- `BlocksTo.encrypt` over a stub on prepared powers, with the out-of-place
loop named `n` if any, evaluated once for each. -/
theorem blocksToP_stub : (n : Option StitchToName) →
    stubCallee (Impl.AesGcm.X86_64.BlocksTo.encrypt ⟨"e", .block []⟩ (n.map StitchToName.encR) true
      ((n.map StitchToName.fullR).getD false)) ((n.map StitchToName.lv).getD .sse).level (fun _ => 8) 24 = true
  | none => by lit_decide
  | some .vaes => by lit_decide
  | some .vaesAvx512 => by lit_decide
  | some .aesniAvx => by lit_decide

theorem blkToP_side_of (v : GcmVariant) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
    (hB : calleeSide B.enc.code v.lv.level 8 = true) (st : Option (StitchToCode M true)) (n : Option StitchToName)
    (hst : st.map (·.enc) = n.map StitchToName.encR ∧ encFullTo st = (n.map StitchToName.fullR).getD false)
    (hn : ((n.map StitchToName.lv).getD .sse).level ≤ v.lvG.level) :
    calleeSide (StreamTo.BlkToFn.ofBlocks "" B st).fn.code v.lvG.level 24 = true := by
  show calleeSide (Impl.AesGcm.X86_64.BlocksTo.encrypt B.enc (st.map (·.enc)) true (encFullTo st)) _ 24 = true
  rw [hst.1, hst.2]
  exact calleeSide_of_fill (blocksTo_fill (n := fun _ => 8) _
    (calleeSide_mono v.lv_le_lvG (Nat.le_refl _) hB) _ true _) hn (blocksToP_stub n)

/-- `v`'s `blkToR`. -/
theorem blkToR_side (v : GcmVariant) : calleeSide (blkToR v).fn.code v.lvG.level 24 = true := by
  have hB := (blkR_sides v).1
  have hl := v.toLv_le_lvG
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, _ | ⟨tname, tpiece, tpP, _ | q, tpD⟩⟩⟩
  · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · cases tname
    · exact blkToP_side_of _ _ hB _ (some .vaes) ⟨rfl, rfl⟩ hl
    · exact blkToP_side_of _ _ hB _ (some .vaesAvx512) ⟨rfl, rfl⟩ hl
    · exact blkToP_side_of _ _ hB _ (some .aesniAvx) ⟨rfl, rfl⟩ hl

/-- `v`'s `blkToF`. -/
theorem blkToF_side (v : GcmVariant) : calleeSide (blkToF v).fn.code v.lvG.level 24 = true := by
  have hB := (blkF_sides v).1
  have hl := v.toLv_le_lvG
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, _ | ⟨tname, tpiece, tpP, _ | q, tpD⟩⟩⟩
  · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · cases tname
    · exact blkToP_side_of _ _ hB _ (some .vaes) ⟨rfl, rfl⟩ hl
    · exact blkToP_side_of _ _ hB _ (some .vaesAvx512) ⟨rfl, rfl⟩ hl
    · exact blkToP_side_of _ _ hB _ (some .aesniAvx) ⟨rfl, rfl⟩ hl

/-- `v`'s `blkToR16`. -/
theorem blkToR16_side (v : GcmVariant) : calleeSide (blkToR16 v).fn.code v.lvG.level 24 = true := by
  have hB := (blkR16_sides v).1
  have hl := v.toLv_le_lvG
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, _ | ⟨tname, tpiece, tpP, _ | q, tpD⟩⟩⟩
  · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · cases tname <;> exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · cases tname
    · exact blkToP_side_of _ _ hB _ (some .vaes) ⟨rfl, rfl⟩ hl
    · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
    · exact blkToP_side_of _ _ hB _ (some .aesniAvx) ⟨rfl, rfl⟩ hl

/-- `v`'s `blkToF16`. -/
theorem blkToF16_side (v : GcmVariant) : calleeSide (blkToF16 v).fn.code v.lvG.level 24 = true := by
  have hB := (blkF16_sides v).1
  have hl := v.toLv_le_lvG
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, _ | ⟨tname, tpiece, tpP, _ | q, tpD⟩⟩⟩
  · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · cases tname <;> exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · cases tname
    · exact blkToP_side_of _ _ hB _ (some .vaes) ⟨rfl, rfl⟩ hl
    · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
    · exact blkToP_side_of _ _ hB _ (some .aesniAvx) ⟨rfl, rfl⟩ hl

/-! ## `vg_aes_gcm_seal_split_prepared` -/

/-- The level of the cleanup of `v`'s `seal_gather` on prepared powers:
`lvG`'s, and VEX's for its path for TLS records (`Fast.sel`). -/
def GcmVariant.lvGA (v : GcmVariant) : VecLevel := v.lvG.join .avx

theorem GcmVariant.lvG_le_lvGA (v : GcmVariant) : v.lvG.level ≤ v.lvGA.level := level_join_left _ _

theorem GcmVariant.one_le_lvGA (v : GcmVariant) : 1 ≤ v.lvGA.level := level_join_right v.lvG .avx

/-- `GcmImpl.splitPre` over stubs. -/
def stubSplitPre : Option OnePassName → Prog isa
  | some .r => Impl.AesGcm.X86_64.SealSplit.prefixS ctrStub toStub OnePassName.r.code
  | some .z => Impl.AesGcm.X86_64.SealSplit.prefixN toStub OnePassName.z.code
  | none => Impl.AesGcm.X86_64.SealSplit.«prefix» toStub

/-- `GcmImpl.splitMidR` over stubs. -/
def stubSplitMidR (s f : Bool) (op : Option OnePassName) : Prog isa :=
  if s then Impl.AesGcm.X86_64.Fast.sel stub5 (stubSplitPre op) Impl.AesGcm.X86_64.Short.finKs (stubSplitFin s f)
    (stubSplitMid s f)
  else Impl.AesGcm.X86_64.Fast.sel stub5 (stubSplitPre op) Impl.AesGcm.X86_64.Short.finKsA (stubSplitFin s f)
    (stubSplitMid s f) true

theorem splitMidR_fill {k : Nat} {n : String → Nat} (i : GcmImpl) (c : Callees) (fTo : Fn)
    (h : CalleesSideN k n c) (h₀ : CalleesSideN k n i.callees) (hT : calleeSide fTo.code k (n "T") = true) :
    Fill k n (withStackArgScratch 2616 5 (Impl.AesGcm.X86_64.SealSplit.«seal» (stubSplitMidR i.short i.fin i.onePass)))
      (withStackArgScratch 2616 5 (Impl.AesGcm.X86_64.SealSplit.«seal» (i.splitMidR c fTo))) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  obtain ⟨g1, g2, g3, ge, gd⟩ := h₀
  unfold GcmImpl.splitMidR GcmImpl.splitPre GcmImpl.splitMid GcmImpl.splitFin stubSplitMidR stubSplitPre stubSplitMid
    stubSplitFin
  generalize i.onePass = op
  rcases op with _ | _ | _ <;> fill_calls_wide

theorem splitFnP_side_of (v : GcmVariant) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) (T : Fn)
    (hB : calleeSide B.enc.code v.lv.level 8 = true ∧ calleeSide B.dec.code v.lv.level 8 = true)
    (hT : calleeSide T.code v.lvG.level 24 = true) (s f : Bool) (op : Option OnePassName)
    (hs : v.impl.short = s) (hf : v.impl.fin = f) (hop : v.impl.onePass = op) (ks : Nat) (hk : ks ≤ v.lvGA.level)
    (ha : stubCallee (withStackArgScratch 2616 5 (Impl.AesGcm.X86_64.SealSplit.«seal» (stubSplitMidR s f op))) ks
      splitN 2672 = true) :
    calleeSide (withStackArgScratch 2616 5 (Impl.AesGcm.X86_64.SealSplit.«seal» (v.impl.splitMidR (v.impl.withBlk B) T)))
      v.lvGA.level 2672 = true := by
  rw [← hs, ← hf, ← hop] at ha
  have hB₀ := blkB_sides v
  have hl := Nat.le_trans v.lv_le_lvG v.lvG_le_lvGA
  exact calleeSide_of_fill (splitMidR_fill v.impl _ _
    (callees_sideS v B _ hl ⟨calleeSide_mono hl (Nat.le_refl _) hB.1, calleeSide_mono hl (Nat.le_refl _) hB.2⟩)
    (callees_sideS v v.impl.blkB _ hl ⟨calleeSide_mono hl (Nat.le_refl _) hB₀.1,
      calleeSide_mono hl (Nat.le_refl _) hB₀.2⟩)
    (calleeSide_mono v.lvG_le_lvGA (by simp [splitN]) hT)) hk ha

/-- `v`'s `vg_aes_gcm_seal_split_prepared`. -/
theorem splitFnF_side (v : GcmVariant) : calleeSide (splitFnF v).fn.code v.lvGA.level 2672 = true := by
  have hB := blkR_sides v
  have hT := blkToR_side v
  have hk := Nat.le_trans v.own_le_lvG v.lvG_le_lvGA
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact splitFnP_side_of _ _ _ hB hT false false none rfl rfl rfl 1 (GcmVariant.one_le_lvGA _) (by lit_decide)
  · cases name
    · exact splitFnP_side_of _ _ _ hB hT false false (some .r) rfl rfl rfl 1 hk (by lit_decide)
    · exact splitFnP_side_of _ _ _ hB hT true false (some .z) rfl rfl rfl 2 hk (by lit_decide)
    · exact splitFnP_side_of _ _ _ hB hT false true none rfl rfl rfl 1 hk (by lit_decide)

/-- `v`'s `vg_aes_gcm_seal_split_prepared16`. -/
theorem splitFnF16_side (v : GcmVariant) (r : R16 v) : calleeSide (splitFnF16 v r).fn.code v.lvGA.level 2672 = true := by
  have hB := blkR16_sides v
  have hT := blkToR16_side v
  have hk := Nat.le_trans v.own_le_lvG v.lvG_le_lvGA
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact splitFnP_side_of _ _ _ hB hT false false none rfl rfl rfl 1 (GcmVariant.one_le_lvGA _) (by lit_decide)
  · cases name
    · exact splitFnP_side_of _ _ _ hB hT false false (some .r) rfl rfl rfl 1 hk (by lit_decide)
    · exact splitFnP_side_of _ _ _ hB hT true false (some .z) rfl rfl rfl 2 hk (by lit_decide)
    · exact splitFnP_side_of _ _ _ hB hT false true none rfl rfl rfl 1 hk (by lit_decide)

/-- `v`'s `vg_aes_gcm_stream_encrypt_to_prepared`. -/
theorem toFnF_side (v : GcmVariant) : calleeSide (toFnF v).fn.code v.lvG.level 4856 = true :=
  calleeSide_of_fill (streamTo_fill _ _ (calleeSide_mono (Nat.le_refl _) (show 24 ≤ streamToN "B" by decide) (blkToF_side v))
    (calleeSide_mono v.lv_le_lvG (show 2608 ≤ streamToN "E" by decide) (streamEncryptCodeF_side v))) (Nat.zero_le _)
    streamTo_stub

theorem GcmVariant.lvA_le_lvGA (v : GcmVariant) : v.lvA.level ≤ v.lvGA.level := by
  unfold GcmVariant.lvA GcmVariant.lvGA GcmVariant.lvG GcmVariant.lv GcmImpl.lv
  generalize (v.impl.ctr.level.join v.impl.key.level).join v.impl.gh.level = a
  generalize v.own = b
  generalize v.toLv = c
  cases a <;> cases b <;> cases c <;> decide

/-- `v`'s `vg_aes_gcm_stream_encrypt_to_prepared16`. -/
theorem toFnF16_side (v : GcmVariant) : calleeSide (toFnF16 v).fn.code v.lvGA.level 4856 = true :=
  calleeSide_of_fill (streamTo_fill _ _
    (calleeSide_mono v.lvG_le_lvGA (show 24 ≤ streamToN "B" by decide) (blkToF16_side v))
    (calleeSide_mono v.lvA_le_lvGA (show 2608 ≤ streamToN "E" by decide) (streamEncryptCodeF16S_side v)))
    (Nat.zero_le _) streamTo_stub

/-! ## `vg_aes_gcm_seal_gather_prepared` on prepared powers -/

theorem gatherP_fill {k : Nat} {n : String → Nat} (c : Nat) (lg : Bool) (t ts : Nat)
    (SeF SpF ToF Se Sp To I A Fi : Fn)
    (hSeF : calleeSide SeF.code k (n "SeF") = true) (hSpF : calleeSide SpF.code k (n "SpF") = true)
    (hToF : calleeSide ToF.code k (n "ToF") = true)
    (hSe : calleeSide Se.code k (n "Se") = true) (hSp : calleeSide Sp.code k (n "Sp") = true)
    (hI : calleeSide I.code k (n "I") = true) (hA : calleeSide A.code k (n "A") = true)
    (hTo : calleeSide To.code k (n "To") = true) (hFi : calleeSide Fi.code k (n "Fi") = true) :
    Fill k n (Impl.Gcm.X86_64.Flag.onFlag c
        (Impl.AesGcm.X86_64.Fn.sealGatherCodeP lg t ts (fnStub "SeF") (fnStub "SpF") (fnStub "I") (fnStub "A")
          (fnStub "ToF") (fnStub "Fi") false)
        (Impl.AesGcm.X86_64.Fn.sealGatherCode t ts (fnStub "Se") (fnStub "Sp") (fnStub "I") (fnStub "A")
          (fnStub "To") (fnStub "Fi")))
      (Impl.Gcm.X86_64.Flag.onFlag c (Impl.AesGcm.X86_64.Fn.sealGatherCodeP lg t ts SeF SpF I A ToF Fi false)
        (Impl.AesGcm.X86_64.Fn.sealGatherCode t ts Se Sp I A To Fi)) := by
  fill_calls_wide

/-- `streamInit`, `streamAad` and `streamFinish` over stubs, as stubs of
their instances, which `seal_gather` on 16 prepared powers inlines. -/
def initStub : Fn := ⟨"I", withStackScratch 2568 .r8 (Impl.AesGcm.X86_64.streamInit stub5)⟩
def aadStub : Fn := ⟨"A", withStackScratch 2568 .r9 (Impl.AesGcm.X86_64.streamAad stub5)⟩
def finStub : Fn := ⟨"Fi", withStackArgScratch 2576 0 (Impl.AesGcm.X86_64.streamFinish stub5)⟩

theorem gatherP16_fill {k : Nat} {n : String → Nat} (c : Nat) (lg : Bool) (t ts : Nat)
    (SeF SpF ToF Se Sp To I A Fi : Fn)
    (hSeF : calleeSide SeF.code k (n "SeF") = true) (hSpF : calleeSide SpF.code k (n "SpF") = true)
    (hToF : calleeSide ToF.code k (n "ToF") = true)
    (hSe : calleeSide Se.code k (n "Se") = true) (hSp : calleeSide Sp.code k (n "Sp") = true)
    (hI : calleeSide I.code k (n "I") = true) (hA : calleeSide A.code k (n "A") = true)
    (hTo : calleeSide To.code k (n "To") = true) (hFi : calleeSide Fi.code k (n "Fi") = true)
    (fI : Fill k n initStub.code I.code) (fA : Fill k n aadStub.code A.code) (fFi : Fill k n finStub.code Fi.code) :
    Fill k n (Impl.Gcm.X86_64.Flag.onFlag c
        (Impl.AesGcm.X86_64.Fn.sealGatherCodeP lg t ts (fnStub "SeF") (fnStub "SpF") initStub aadStub
          (fnStub "ToF") finStub true)
        (Impl.AesGcm.X86_64.Fn.sealGatherCode t ts (fnStub "Se") (fnStub "Sp") (fnStub "I") (fnStub "A")
          (fnStub "To") (fnStub "Fi")))
      (Impl.Gcm.X86_64.Flag.onFlag c (Impl.AesGcm.X86_64.Fn.sealGatherCodeP lg t ts SeF SpF I A ToF Fi true)
        (Impl.AesGcm.X86_64.Fn.sealGatherCode t ts Se Sp I A To Fi)) := by
  fill_calls_wide
  all_goals first | exact fI | exact fA | exact fFi

/-- The shapes of `seal_gather` by the kind of out-of-place loops. -/
def gLong (n : Option StitchToName) : Bool := match n with | some .vaesAvx512 => true | _ => false
def gT (n : Option StitchToName) : Nat :=
  match n with | some .vaesAvx512 => 768 | some .vaes => 16384 | some .aesniAvx => 3072 | none => 2 ^ 31 - 1
def gTs (n : Option StitchToName) : Nat :=
  match n with | some .vaesAvx512 => 752 | some .vaes => 1024 | some .aesniAvx => 384 | none => 2 ^ 31 - 17

theorem gatherP_stub (c : Nat) (hc : c = 16 ∨ c = 48) : (n : Option StitchToName) →
    stubSide (Impl.Gcm.X86_64.Flag.onFlag c
        (Impl.AesGcm.X86_64.Fn.sealGatherCodeP (gLong n) (gT n) (gTs n) (fnStub "SeF") (fnStub "SpF") (fnStub "I")
          (fnStub "A") (fnStub "ToF") (fnStub "Fi") false)
        (Impl.AesGcm.X86_64.Fn.sealGatherCode (gT n) (gTs n) (fnStub "Se") (fnStub "Sp") (fnStub "I") (fnStub "A")
          (fnStub "To") (fnStub "Fi")))
      1 gatherN 5128 [] = true
  | none => by rcases hc with rfl | rfl <;> lit_decide
  | some .vaes => by rcases hc with rfl | rfl <;> lit_decide
  | some .vaesAvx512 => by rcases hc with rfl | rfl <;> lit_decide
  | some .aesniAvx => by rcases hc with rfl | rfl <;> lit_decide

theorem gatherP16_stub : (n : Option StitchToName) →
    stubSide (Impl.Gcm.X86_64.Flag.onFlag 16
        (Impl.AesGcm.X86_64.Fn.sealGatherCodeP (gLong n) (gT n) (gTs n) (fnStub "SeF") (fnStub "SpF") initStub
          aadStub (fnStub "ToF") finStub true)
        (Impl.AesGcm.X86_64.Fn.sealGatherCode (gT n) (gTs n) (fnStub "Se") (fnStub "Sp") (fnStub "I") (fnStub "A")
          (fnStub "To") (fnStub "Fi")))
      1 gatherN 5128 [] = true
  | none => by lit_decide
  | some .vaes => by lit_decide
  | some .vaesAvx512 => by lit_decide
  | some .aesniAvx => by lit_decide

theorem tlsLong_eq (v : GcmVariant) : tlsLong v = gLong ((v.stitch.bind (·.toPart)).map (·.name)) := rfl
theorem copyBelow_eq' (v : GcmVariant) : copyBelow v = gT ((v.stitch.bind (·.toPart)).map (·.name)) := rfl
theorem splitFrom_eq' (v : GcmVariant) : splitFrom v = gTs ((v.stitch.bind (·.toPart)).map (·.name)) := rfl

/-- `v`'s callees meet `CalleesSideN` with the stacks `gatherN`. -/
theorem callees_sideG (v : GcmVariant) : CalleesSideN v.lvGA.level gatherN v.impl.callees :=
  have h := v.impl.sides v.own
  have hl := Nat.le_trans v.lv_le_lvG v.lvG_le_lvGA
  ⟨calleeSide_mono hl (Nat.zero_le _) h.1, calleeSide_mono hl (Nat.zero_le _) h.2.1,
    calleeSide_mono hl (Nat.zero_le _) h.2.2,
    calleeSide_mono hl (by simp [gatherN]) (blkB_sides v).1,
    calleeSide_mono hl (by simp [gatherN]) (blkB_sides v).2⟩

/-- `Spec.Gcm.sealGatherPreparedApi`'s function over `v` on 48 prepared powers
or the key context, as emitted (`Impl.AesGcm.X86_64.Fn.sealGatherP`), meets
its contract in constant time and returns without secret residue. -/
theorem sealGatherR_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target
      (Impl.AesGcm.X86_64.Fn.sealGatherP v.lvGA 48 (tlsLong v) (copyBelow v) (splitFrom v) (sealFnF v).fn
        (splitFnF v).fn (toFnF v).fn (sealFn v.impl).fn (splitFn v).fn (toFn v).fn (initFn v.impl).fn
        (aadFn v.impl).fn (finFn v.impl).fn false)
      (Spec.Gcm.sealGatherPreparedApi.contract X86_64.abi 5128) 0 := by
  have hl := Nat.le_trans v.lv_le_lvG v.lvG_le_lvGA
  have hSeF := calleeSide_mono hl (show 2624 ≤ gatherN "SeF" by decide) (sealCodeF_sides v).1
  have hSpF := calleeSide_mono (Nat.le_refl _) (show 2672 ≤ gatherN "SpF" by decide) (splitFnF_side v)
  have hToF := calleeSide_mono v.lvG_le_lvGA (show 4856 ≤ gatherN "ToF" by decide) (toFnF_side v)
  have hSe := calleeSide_mono hl (show 2624 ≤ gatherN "Se" by decide) (sealFn_side v)
  have hSp := calleeSide_mono v.lvG_le_lvGA (show 2672 ≤ gatherN "Sp" by decide) (splitFn_side v)
  have hI := calleeSide_mono hl (show 2576 ≤ gatherN "I" by decide) (initFn_side v)
  have hA := calleeSide_mono hl (show 2576 ≤ gatherN "A" by decide) (aadFn_side v)
  have hTo := calleeSide_mono v.lvG_le_lvGA (show 4856 ≤ gatherN "To" by decide) (toFn_side v)
  have hFi := calleeSide_mono hl (show 2584 ≤ gatherN "Fi" by decide) (finFn_side v)
  have ha := gatherP_stub 48 (.inr rfl) ((v.stitch.bind (·.toPart)).map (·.name))
  rw [← tlsLong_eq, ← copyBelow_eq', ← splitFrom_eq'] at ha
  exact verifiedScrubbedAllFill (api := Spec.Gcm.sealGatherPreparedApi) (ks := 1) (n := gatherN) (rb := 0)
    (stack := 5128)
    (a := Impl.Gcm.X86_64.Flag.onFlag 48
      (Impl.AesGcm.X86_64.Fn.sealGatherCodeP (tlsLong v) (copyBelow v) (splitFrom v) (fnStub "SeF") (fnStub "SpF")
        (fnStub "I") (fnStub "A") (fnStub "ToF") (fnStub "Fi") false)
      (Impl.AesGcm.X86_64.Fn.sealGatherCode (copyBelow v) (splitFrom v) (fnStub "Se") (fnStub "Sp") (fnStub "I")
        (fnStub "A") (fnStub "To") (fnStub "Fi")))
    (sealGatherRPlain v) v.lvGA (sealGatherPreparedOut _)
    (gatherP_fill 48 _ _ _ _ _ _ _ _ _ _ _ _ hSeF hSpF hToF hSe hSp hI hA hTo hFi)
    v.one_le_lvGA (Nat.le_refl _) (ha := ha)

/-- `Spec.Gcm.sealGatherPreparedApi`'s function over `v` on 16 prepared powers
or the key context, as `sealGatherR_scrubbed`. -/
theorem sealGatherR16_scrubbed (v : GcmVariant) (r : R16 v) :
    VerifiedScrubbed target
      (Impl.AesGcm.X86_64.Fn.sealGatherP v.lvGA 16 (tlsLong v) (copyBelow v) (splitFrom v) (sealFnF16 v r).fn
        (splitFnF16 v r).fn (toFnF16 v).fn (sealFn v.impl).fn (splitFn v).fn (toFn v).fn (initFn v.impl).fn
        (aadFn v.impl).fn (finFn v.impl).fn true)
      (Spec.Gcm.sealGatherPreparedApi.contract X86_64.abi 5128) 0 := by
  have hl := Nat.le_trans v.lv_le_lvG v.lvG_le_lvGA
  have hSeF := calleeSide_mono hl (show 2624 ≤ gatherN "SeF" by decide) (sealCodeF_sides v).2
  have hSpF := calleeSide_mono (Nat.le_refl _) (show 2672 ≤ gatherN "SpF" by decide) (splitFnF16_side v r)
  have hToF := calleeSide_mono (Nat.le_refl _) (show 4856 ≤ gatherN "ToF" by decide) (toFnF16_side v)
  have hSe := calleeSide_mono hl (show 2624 ≤ gatherN "Se" by decide) (sealFn_side v)
  have hSp := calleeSide_mono v.lvG_le_lvGA (show 2672 ≤ gatherN "Sp" by decide) (splitFn_side v)
  have hI := calleeSide_mono hl (show 2576 ≤ gatherN "I" by decide) (initFn_side v)
  have hA := calleeSide_mono hl (show 2576 ≤ gatherN "A" by decide) (aadFn_side v)
  have hTo := calleeSide_mono v.lvG_le_lvGA (show 4856 ≤ gatherN "To" by decide) (toFn_side v)
  have hFi := calleeSide_mono hl (show 2584 ≤ gatherN "Fi" by decide) (finFn_side v)
  have fI := streamInitS_fill _ (callees_sideG v)
  have fA := streamAadS_fill _ (callees_sideG v)
  have fFi := streamFinishS_fill _ (callees_sideG v)
  have ha := gatherP16_stub ((v.stitch.bind (·.toPart)).map (·.name))
  rw [← tlsLong_eq, ← copyBelow_eq', ← splitFrom_eq'] at ha
  exact verifiedScrubbedAllFill (api := Spec.Gcm.sealGatherPreparedApi) (ks := 1) (n := gatherN) (rb := 0)
    (stack := 5128)
    (a := Impl.Gcm.X86_64.Flag.onFlag 16
      (Impl.AesGcm.X86_64.Fn.sealGatherCodeP (tlsLong v) (copyBelow v) (splitFrom v) (fnStub "SeF") (fnStub "SpF")
        initStub aadStub (fnStub "ToF") finStub true)
      (Impl.AesGcm.X86_64.Fn.sealGatherCode (copyBelow v) (splitFrom v) (fnStub "Se") (fnStub "Sp") (fnStub "I")
        (fnStub "A") (fnStub "To") (fnStub "Fi")))
    (sealGatherR16Plain v r) v.lvGA (sealGatherPreparedOut _)
    (gatherP16_fill 16 _ _ _ _ _ _ _ _ _ _ _ _ hSeF hSpF hToF hSe hSp hI hA hTo hFi fI fA fFi)
    v.one_le_lvGA (Nat.le_refl _) (ha := ha)

/-! ## The registrations

Each binds a function as emitted over `v` (`Impl.AesGcm.X86_64.Fn`) and its
theorem: on the key context alone (`…W`), or by the flag on 48 prepared
powers (`…R`), or by the count on 16 (`…R16`, given `R16 v`). -/

/-- `sealPreparedApi`'s function over `v`. -/
def sealPrepW (v : GcmVariant) : Registration Spec.Gcm.sealPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.sealW v.lv v.impl.short v.impl.fin v.impl.callees
  verified := .scrubbed (sealW_scrubbed v)
  spSafe := scrubKs_spSafe ((sealWPlain v).spSafe)

/-- `openPreparedApi`'s function over `v`. -/
def openPrepW (v : GcmVariant) : Registration Spec.Gcm.openPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.openW v.lv v.impl.short v.impl.callees
  verified := .scrubbed (openW_scrubbed v)
  spSafe := scrubKs_spSafe ((openWPlain v).spSafe)

/-- `openToPreparedApi`'s function over `v`. -/
def openToPrepW (v : GcmVariant) : Registration Spec.Gcm.openToPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.openToW v.lvTW (openSplitFnB v v.ctrTo).fn
  verified := .scrubbed (openToW_scrubbed v)
  spSafe := scrubKs_spSafe ((openToWPlain v).spSafe)

/-- `streamEncryptPreparedApi`'s function over `v`. -/
def streamEncryptPrepW (v : GcmVariant) : Registration Spec.Gcm.streamEncryptPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.streamEncryptW v.lv v.impl.callees
  verified := .scrubbed (streamEncryptW_scrubbed v)
  spSafe := scrubKs_spSafe (X86_64.withStackArgScratch_spSafe (streamEncrypt_spSafe v.impl))

/-- `streamDecryptPreparedApi`'s function over `v`. -/
def streamDecryptPrepW (v : GcmVariant) : Registration Spec.Gcm.streamDecryptPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.streamDecryptW v.lv v.impl.callees
  verified := .scrubbed (streamDecryptW_scrubbed v)
  spSafe := scrubKs_spSafe (X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl))

/-- `sealGatherPreparedApi`'s function over `v`. -/
def sealGatherPrepW (v : GcmVariant) : Registration Spec.Gcm.sealGatherPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.sealGatherW v.lvG (copyBelow v) (splitFrom v) (sealFn v.impl).fn (splitFn v).fn
        (initFn v.impl).fn (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn
  verified := .scrubbed (sealGatherW_scrubbed v)
  spSafe := scrubKs_spSafe ((sealGatherWPlain v).spSafe)

/-- `sealPreparedApi`'s function over `v`. -/
def sealPrepR (v : GcmVariant) : Registration Spec.Gcm.sealPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.sealP v.lv 48 v.impl.short v.impl.fin (v.impl.withBlk (blkR v)) v.impl.callees
  verified := .scrubbed (sealR_scrubbed v)
  spSafe := scrubKs_spSafe ((sealRPlain v).spSafe)

/-- `openPreparedApi`'s function over `v`. -/
def openPrepR (v : GcmVariant) : Registration Spec.Gcm.openPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.openP v.lvA 48 v.impl.short (v.impl.withBlk (blkR v)) v.impl.callees
  verified := .scrubbed (openR_scrubbed v)
  spSafe := scrubKs_spSafe ((openRPlain v).spSafe)

/-- `openToPreparedApi`'s function over `v`. -/
def openToPrepR (v : GcmVariant) : Registration Spec.Gcm.openToPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.openToP v.lvT 48 v.stitchToDecR.isSome v.impl.copyW (openFnF v).fn (openSplitFnF v).fn
        (openSplitFnB v v.ctrTo).fn
  verified := .scrubbed (openToR_scrubbed v)
  spSafe := scrubKs_spSafe (openToCodeR_onFlag_spAll v)

/-- `streamEncryptPreparedApi`'s function over `v`. -/
def streamEncryptPrepR (v : GcmVariant) : Registration Spec.Gcm.streamEncryptPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.streamEncryptP v.lv 48 (v.impl.withBlk (blkR v)) v.impl.callees
  verified := .scrubbed (streamEncryptR_scrubbed v)
  spSafe := scrubKs_spSafe (streamEncryptCodeF_spAll v)

/-- `streamDecryptPreparedApi`'s function over `v`. -/
def streamDecryptPrepR (v : GcmVariant) : Registration Spec.Gcm.streamDecryptPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.streamDecryptP v.lv 48 (v.impl.withBlk (blkR v)) v.impl.callees
  verified := .scrubbed (streamDecryptR_scrubbed v)
  spSafe := scrubKs_spSafe (VG.X86_64.onFlag_spSafe
      (X86_64.withStackArgScratch_spSafe (streamDecryptM_spSafe v.impl (blkR v)))
      (X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl)))

/-- `sealGatherPreparedApi`'s function over `v`. -/
def sealGatherPrepR (v : GcmVariant) : Registration Spec.Gcm.sealGatherPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.sealGatherP v.lvGA 48 (tlsLong v) (copyBelow v) (splitFrom v) (sealFnF v).fn
        (splitFnF v).fn (toFnF v).fn (sealFn v.impl).fn (splitFn v).fn (toFn v).fn (initFn v.impl).fn
        (aadFn v.impl).fn (finFn v.impl).fn false
  verified := .scrubbed (sealGatherR_scrubbed v)
  spSafe := scrubKs_spSafe ((sealGatherRPlain v).spSafe)

/-- `sealPreparedApi`'s function over `v`, on 16 prepared powers. -/
def sealPrepR16 (v : GcmVariant) (r : R16 v) : Registration Spec.Gcm.sealPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.sealP v.lv 16 v.impl.short v.impl.fin (v.impl.withBlk (blkR16 v)) v.impl.callees
  verified := .scrubbed (sealR16_scrubbed v r)
  spSafe := scrubKs_spSafe ((sealF16Plain v r).spSafe)

/-- `openPreparedApi`'s function over `v`, on 16 prepared powers. -/
def openPrepR16 (v : GcmVariant) (r : R16 v) : Registration Spec.Gcm.openPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.openP v.lvA 16 v.impl.short (v.impl.withBlk (blkR16 v)) v.impl.callees
  verified := .scrubbed (openR16_scrubbed v r)
  spSafe := scrubKs_spSafe ((openR16Plain v r).spSafe)

/-- `openToPreparedApi`'s function over `v`, on 16 prepared powers. -/
def openToPrepR16 (v : GcmVariant) (r : R16 v) : Registration Spec.Gcm.openToPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.openToP v.lvT 16 v.stitchToDecR16.isSome v.impl.copyW (openFnF16 v r).fn
        (openSplitFnF16 v).fn (openSplitFnB v v.ctrTo).fn
  verified := .scrubbed (openToR16_scrubbed v r)
  spSafe := scrubKs_spSafe (openToCodeR16_onFlag_spAll v r)

/-- `streamEncryptPreparedApi`'s function over `v`, on 16 prepared powers. -/
def streamEncryptPrepR16 (v : GcmVariant) : Registration Spec.Gcm.streamEncryptPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.streamEncryptP v.lv 16 (v.impl.withBlk (blkR16 v)) v.impl.callees
  verified := .scrubbed (streamEncryptR16_scrubbed v)
  spSafe := scrubKs_spSafe (streamEncryptCodeF16_spAll v)

/-- `streamDecryptPreparedApi`'s function over `v`, on 16 prepared powers. -/
def streamDecryptPrepR16 (v : GcmVariant) : Registration Spec.Gcm.streamDecryptPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.streamDecryptP v.lv 16 (v.impl.withBlk (blkR16 v)) v.impl.callees
  verified := .scrubbed (streamDecryptR16_scrubbed v)
  spSafe := scrubKs_spSafe (VG.X86_64.onFlag_spSafe
      (X86_64.withStackArgScratch_spSafe (streamDecryptM_spSafe v.impl (blkR16 v)))
      (X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl)))

/-- `sealGatherPreparedApi`'s function over `v`, on 16 prepared powers. -/
def sealGatherPrepR16 (v : GcmVariant) (r : R16 v) : Registration Spec.Gcm.sealGatherPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.sealGatherP v.lvGA 16 (tlsLong v) (copyBelow v) (splitFrom v) (sealFnF16 v r).fn
        (splitFnF16 v r).fn (toFnF16 v).fn (sealFn v.impl).fn (splitFn v).fn (toFn v).fn (initFn v.impl).fn
        (aadFn v.impl).fn (finFn v.impl).fn true
  verified := .scrubbed (sealGatherR16_scrubbed v r)
  spSafe := scrubKs_spSafe ((sealGatherR16Plain v r).spSafe)

end VG.Proof.AesGcm.X86_64
