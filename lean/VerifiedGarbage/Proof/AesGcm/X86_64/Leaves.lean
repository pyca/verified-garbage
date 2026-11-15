module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Instances
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.X86_64.WidenArray
public import VerifiedGarbage.Proof.Framework.X86_64.FlagBranch
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.AesGcm.X86_64.Flag
import VerifiedGarbage.Proof.AesGcm.X86_64.Scrub
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Frame
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared16
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Variants.AesGcm.X86_64.VaesVpclmul
public import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Leaves
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.Ok
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesGcm.X86_64.SealLeaves

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
state `narrowS` it runs from), from what it leaves run by run from the
states its contract's precondition implies `P` of. -/
theorem framed_leaves {sig : Sig} {nm : String} {e : Elem} {n bytes stack : Nat}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {c : Prog isa} {P : State → Prop}
    {R : State → Region} {L : State → Addr → Option (BitVec 8)}
    (hv : Verified X86_64.target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hP : ∀ s, (Sig.scratchContract abi sig nm e n pre post wa stack leak).pre s → P s)
    (hl : ∀ s t s', P s → Exec isa c s t s' → ∀ x, (R s).Contains x 1 → s'.mem x = (L s x).getD (s.mem x))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 8 ≤ 2 ^ 64) (hsp : c.all (fun i => !isa.writesSp i) = true)
    (hd : c.x86_64Depth ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) {t : List Leak} {u : State}
    (he : Exec isa (withStackArgScratch bytes (nStack sig) c) s t u) :
    ∀ x, (R (narrowS sig e n bytes s)).Contains x 1 →
      u.mem x = (L (narrowS sig e n bytes s) x).getD ((narrowS sig e n bytes s).mem x) := by
  have hn := narrowS_pre (nm := nm) hk hb.1 hb.2.1 (fun vs m₁ m₂ hl hb _ => hpre vs m₁ m₂ hl hb) hs
  obtain ⟨t₃, s₃, he₃, ha, -⟩ := hv.1 _ hn
  obtain ⟨hex, -, hm, -⟩ := withStackArgScratch_run hk hb hst (SpSafe.of_all hsp) hd hs he₃ ha
  obtain ⟨-, rfl⟩ := Exec.det he hex
  intro x hx
  rw [hm]
  exact hl _ _ _ (hP _ hn) he₃ x hx

/-- What `narrowS` keeps of `s`: the registers but `rax` and `rsp`, the
stack arguments, the buffer after them, and the memory outside the copies. -/
theorem narrowS_args {sig : Sig} {e : Elem} {n bytes stack : Nat}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 16 + 8 * nStack sig + n * e.size ≤ bytes)
    (hb1 : bytes < 4096) {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    (∀ q, q ≠ .rax → q ≠ .rsp → (narrowS sig e n bytes s).gpr q = s.gpr q) ∧
      (∀ j < nStack sig, stackArg (narrowS sig e n bytes s) j = stackArg s j) ∧
      stackArg (narrowS sig e n bytes s) (nStack sig) =
        s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig) ∧
      Frame [⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, 8 * (nStack sig + 1)⟩]
        s.mem (narrowS sig e n bytes s).mem := by
  obtain ⟨-, hg, -, -, hf⟩ := narrowS_facts (nm := "") hk hb hb1 hs
  obtain ⟨-, -, -, -, -, -, ha, hl⟩ := argsState_run hs hk hb hb1
  exact ⟨hg, ha, hl, hf⟩

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
          u.mem x = (sealL Lb s.gpr (sealArgs s) x).getD (s.mem x) := by
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
  exact hv

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
          u.mem x = (sealL Lb s.gpr (sealArgs s) x).getD (s.mem x) := by
  have hc : variant.impl.sealCode variant.impl.callees = Impl.AesGcm.X86_64.«seal» variant.impl.callees := by
    have hs : variant.impl.short = false := rfl
    have hf : variant.impl.fin = false := rfl
    unfold GcmImpl.sealCode
    simp only [hs, hf, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨Lb, hL⟩ := seal_vaes_leaves
  rw [hc] at hL
  refine ⟨Lb, fun s t u hs hf he x hx => ?_⟩
  rw [hc] at he
  unfold Spec.Gcm.sealPreparedContract at hs
  have h₁ := pre_of_rel (N := 129) (C := fun m ctx => ¬ 16 ≤ (m.readW (ctx + 1024) 64).toNat) (leakB := none)
    (pre := Spec.Gcm.sealPreparedPre 64) (pre' := Spec.Gcm.sealPre 64) (fun _ _ _ _ _ _ _ _ _ _ h _ => h.1) hs hf
  have h₂ := pre_narrowFirstArray (n := 32) (n' := 129) (by decide) (pre := Spec.Gcm.sealPre 64)
    (fun _ _ _ _ _ _ _ _ _ _ h => h) h₁
  obtain ⟨t₁, u₁, he₁, hm⟩ := exec_narrow (seal_framed variant.impl) h₂
    (fun _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)) (Covers.refl _) he
  obtain ⟨hx', hv⟩ := narrowS_sealL (sig := Spec.Gcm.sealSig) (e := .u64) (n := 320) (by decide)
    (by decide) (by decide) h₂ Lb hx
  rw [hm, framed_leaves (sig := Spec.Gcm.sealSig) (nm := "work") (e := .u64) (n := 320)
    (bytes := 2600) (stack := 24) (pre := Spec.Gcm.sealPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.sealRoundsPost X86_64.abi.ptrBits) (wa := true) (leak := none)
    (seal_verified variant.impl) (fun s h => ⟨sealCode_implies.pre s h, trivial⟩) hL
    (by decide) (by decide) (by decide) (seal_spSafe _) (seal_xdepth _)
    (sealPre_local _) h₂ he₁ x hx']
  exact hv

/-! ## `vg_aes_gcm_seal_prepared_vaes_vpclmul` without secret residue -/

open VG.X86_64.Scrub VG.Impl.Scrub.X86_64

/-- `onFlag t c₁ c₂` from `s` runs `c₁` from the state after the test if the
count is at least `t`, and `c₂` if not. -/
theorem onFlag_inv {t : Nat} (htv : t = 16 ∨ t = 48) {c₁ c₂ : Prog isa} {s u : State} {tr : List Leak}
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + 1024) 8)
    (he : Exec isa (Impl.Gcm.X86_64.Flag.onFlag t c₁ c₂) s tr u) :
    ∃ s₀ t₀, Same s s₀ ∧
      ((t ≤ flagCount s ∧ Exec isa c₁ s₀ t₀ u) ∨ (¬ t ≤ flagCount s ∧ Exec isa c₂ s₀ t₀ u)) := by
  obtain ⟨s₀, e₀, hS, ev⟩ := testFlag_run htv s hin
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
            exact ⟨_, _, hS, .inl ⟨of_decide_eq_true (Option.some.inj hc'), hc₁⟩⟩
      | iteF hc hel =>
        have hc' : eval .ae s₀ = some false := hc
        rw [ev] at hc'
        exact ⟨_, _, hS, .inr ⟨of_decide_eq_false (Option.some.inj hc'), hel⟩⟩

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
  unfold Spec.Gcm.sealPreparedContract
  refine resOk_of_leaves (V := fun s x => if 16 ≤ flagCount s then sealL Lb₁ s.gpr (sealArgs s) x
    else sealL Lb₂ s.gpr (sealArgs s) x) ScrubAbi.plain ?_ ?_
  · intro s t u hs he x hx hw
    have hW := sealWindow hx hw
    obtain ⟨s₀, t₀, hS, hb⟩ := onFlag_inv (Or.inl rfl) (flag_inRegions (N := 129) (by decide) hs) he
    have hs₀ := (pre_same hS).mpr hs
    have hf : flagCount s₀ = flagCount s := by simp only [flagCount, hS.mem, hS.gpr .rdi (by decide)]
    have hg : sealL Lb₁ s₀.gpr (sealArgs s₀) = sealL Lb₁ s.gpr (sealArgs s) ∧
        sealL Lb₂ s₀.gpr (sealArgs s₀) = sealL Lb₂ s.gpr (sealArgs s) := by
      rw [sealArgs_same hS]
      exact ⟨sealL_congr Lb₁ (fun r hr _ => hS.gpr r hr) (fun _ _ => rfl),
        sealL_congr Lb₂ (fun r hr _ => hS.gpr r hr) (fun _ _ => rfl)⟩
    rw [← hS.gpr .rsp (by decide)] at hW
    rcases hb with ⟨hb, he₀⟩ | ⟨hb, he₀⟩
    · rw [h₁ s₀ t₀ u hs₀ (hf ▸ hb) he₀ x hW, hg.1, hS.mem]
      simp only [hb, ↓reduceIte]
    · rw [h₂ s₀ t₀ u hs₀ (hf ▸ hb) he₀ x hW, hg.2, hS.mem]
      simp only [hb, ↓reduceIte]
  · intro s₁ s₂ _ _ hp ho _
    obtain ⟨⟨-, hl⟩, hpubs, -⟩ := (pubL_args (sig := Spec.Gcm.sealPreparedSig) (by decide)).mp hp
    have hg : ∀ r, r ≠ .rax → s₁.gpr r = s₂.gpr r := ho.2.2.1
    have hflag : 16 ≤ flagCount s₁ ↔ 16 ≤ flagCount s₂ := by
      have hl' : flagLeak s₁.mem (s₁.gpr .rdi) = flagLeak s₂.mem (s₂.gpr .rdi) :=
        List.head_eq_of_cons_eq hl
      exact flagLeak_iff (Or.inl rfl) hl'
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
    have ha : sealArgs s₁ = sealArgs s₂ := by
      funext i
      simp only [sealArgs]
      by_cases hi : i < 3
      · simp only [hi, ↓reduceIte]
        exact harg i (by rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl) hi
      · simp only [hi, ↓reduceIte, hg .rsp (by decide)]
    funext x
    dsimp only
    rw [ha, sealL_congr Lb₁ (g' := s₂.gpr) (fun r hr _ => hg r hr) (fun _ _ => rfl),
      sealL_congr Lb₂ (g' := s₂.gpr) (fun r hr _ => hg r hr) (fun _ _ => rfl)]
    by_cases h : 16 ≤ flagCount s₁
    · simp only [h, hflag.mp h, ↓reduceIte]
    · simp only [h, mt hflag.mpr h, ↓reduceIte]

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
def sealF16Plain (v : GcmVariant) (r : R16 v) : Registration Spec.Gcm.sealPreparedApi X86_64.target where
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
`sealF16Plain` for the others. -/
def sealF16Reg (v : GcmVariant) (r : R16 v) : Registration Spec.Gcm.sealPreparedApi X86_64.target :=
  if v.impl.suffix = variant.impl.suffix then sealF16Vaes else sealF16Plain v r

end

end VG.Proof.AesGcm.X86_64
