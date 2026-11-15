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
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenLeaves
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks

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
  have e (j : Nat) : stackArg (narrowS sig e n bytes s) j =
      stackArg (setArgsState bytes (nStack sig) (allocState bytes s)) j := by
    simp only [stackArg, stackArgAddr, narrowS, State.withRegions_mem, State.withRegions_gpr]
  exact ⟨hg, fun j hj => (e j).trans (ha j hj), (e _).trans hl, hf⟩

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
        u.mem x = (sealL Lb s.gpr (sealArgs s) x).getD (s.mem x) := by
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
  exact ⟨Lb, seal_branchOf variant hc hL (C := fun m ctx => ¬ 16 ≤ (m.readW (ctx + 1024) 64).toNat)⟩

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
    obtain ⟨⟨-, hl⟩, -, -⟩ := (pubL_args (sig := Spec.Gcm.sealPreparedSig) (by decide)).mp hp
    have hg : ∀ r, r ≠ .rax → s₁.gpr r = s₂.gpr r := ho.2.2.1
    have hflag : 16 ≤ flagCount s₁ ↔ 16 ≤ flagCount s₂ := by
      have hl' : flagLeak s₁.mem (s₁.gpr .rdi) = flagLeak s₂.mem (s₂.gpr .rdi) :=
        List.head_eq_of_cons_eq hl
      exact flagLeak_iff (Or.inl rfl) hl'
    have ha := sealArgs_pub hp ho
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
      ∀ x, sealQ (sealA s) (sealW s) x → u.mem x = (sealVs Lb s x).getD (s.mem x) := by
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
  exact hv

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
  refine resOk_of_leaves (V := sealVs Lb) ScrubAbi.plain ?_ ?_
  · intro s t u hs he x hx hw
    exact seal_branchQ v hc hL (C := fun _ _ => True) s t u hs trivial he x (sealWindowA hx hw)
  · intro s₁ s₂ _ _ hp ho _
    have ha := sealArgs_pub hp ho
    have hsp : s₁.gpr .rsp = s₂.gpr .rsp := ho.2.2.1 .rsp (by decide)
    have hA : sealA s₁ = sealA s₂ := by simp only [sealA, hsp]
    funext x
    unfold sealVs
    rw [ha, hA]
    exact sealV_congr Lb (fun _ => by simp only [sealHdr, ha, hA]) (fun r hr _ => ho.2.2.1 r hr) (fun _ _ => rfl)

/-- `vg_aes_gcm_seal_prepared` of a variant whose loops read only the key
context. -/
def sealWPlain (v : GcmVariant) : Registration Spec.Gcm.sealPreparedApi X86_64.target where
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

/-- `vg_aes_gcm_seal_prepared` of a variant whose loops read only the key
context: `sealWAesniPclmul` for the function of the variant on AES-NI and
PCLMULQDQ, which returns without secret residue, and `sealWPlain` for the
others. -/
def sealWReg (v : GcmVariant) : Registration Spec.Gcm.sealPreparedApi X86_64.target :=
  if v.impl.suffix = aesNiPclmulV.impl.suffix then sealWAesniPclmul else sealWPlain v

/-! ## `vg_aes_gcm_open_prepared_aesni_pclmul` -/

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
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.openSig) (nm := "work") (e := .u64)
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
      ∀ x, openQ (openA s) (openW s) x → u.mem x = (openVs Lb s x).getD (s.mem x) := by
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
  exact hv

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
  refine resOk_of_leaves (V := openVs Lb) ScrubAbi.plain ?_ ?_
  · intro s t u hs he x hx hw
    exact open_branchOf v hc hL (C := fun _ _ => True) s t u hs trivial he x (openWindow hx hw)
  · intro s₁ s₂ _ _ hp ho _
    have ha := openArgs_pub hp ho
    have hsp : s₁.gpr .rsp = s₂.gpr .rsp := ho.2.2.1 .rsp (by decide)
    have hA : openA s₁ = openA s₂ := by simp only [openA, hsp]
    have hW : openW s₁ = openW s₂ := by simp only [openW, hsp]
    funext x
    unfold openVs
    rw [ha, hA, hW]
    exact openV_congr Lb (fun _ => by simp only [openHdr, ha, hA]) (fun r hr _ => ho.2.2.1 r hr)
      (fun _ _ => rfl)

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
def openWPlain (v : GcmVariant) : Registration Spec.Gcm.openPreparedApi X86_64.target where
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
def openWPlainA : Registration Spec.Gcm.openPreparedApi X86_64.target where
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

/-- `vg_aes_gcm_open_prepared` of a variant whose loops read only the key
context: `openWAesniPclmul` for the variant on AES-NI and PCLMULQDQ, which
returns without secret residue, and `openWPlain` for the others. -/
def openWReg (v : GcmVariant) : Registration Spec.Gcm.openPreparedApi X86_64.target :=
  if v.impl.suffix = aesNiPclmulV.impl.suffix then openWAesniPclmul else openWPlain v

end

end VG.Proof.AesGcm.X86_64
