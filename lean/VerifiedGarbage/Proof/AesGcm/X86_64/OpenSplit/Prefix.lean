module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixOk
public import VerifiedGarbage.Impl.AesGcm.X86_64.OpenSplit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.BlkCall
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Piece
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Piece
meta import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Verified
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Impl.AesGcm.X86_64
meta import VerifiedGarbage.Impl.AesGcm.X86_64.BlocksTo
meta import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksVerified
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Gcm.Be64
meta import VerifiedGarbage.Impl.Gcm.X86_64
meta import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
meta import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Gcm.Be64
meta import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
public import VerifiedGarbage.Impl.AesGcm.X86_64.BlocksToDec
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Stitch
import VerifiedGarbage.Proof.Gcm.Split
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Full
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Contract
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecToDec
meta import VerifiedGarbage.Impl.AesGcm.X86_64.BlocksToDec
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Stitch
meta import VerifiedGarbage.Proof.Gcm.Split
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Full
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Run
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Env
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
meta import VerifiedGarbage.Proof.Gcm.Ctr
meta import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Contract
meta import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecToDec

/-! ### `AesGcm.X86_64.BlocksToDec.Fn`, which this module and modules that import it used -/

section

/-! ### `AesGcm.X86_64.BlocksToDec.Run`, which only this module used -/

section

/-! ### `AesGcm.X86_64.BlocksToDec.Contract`, which this module and modules that import it used -/

section

/-!
# AES-GCM decryption of whole blocks out of place, x86-64: the contract

Untrusted: everything here is checked by Lean. `vg_aes_gcm_decrypt_blocks_to`
takes the arguments of `vg_aes_gcm_encrypt_blocks_to`, under the same
precondition (`blocksToPreM`) and with the same public arguments
(`blocksToPub`); it leaves the decryption of the ciphertext at `src` in the
output, the counter advanced, and `Y` continued over the ciphertext
(`blocksToDecPost`). Only verified code calls it, so its contract is here,
with no `Api`. `StitchToDecCode` is an out-of-place decryption loop with its
proof, which it may run on whole groups of 16 blocks.
-/

@[expose] public section

namespace VG.Proof.AesGcm

open VG VG.X86_64
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-- What `vg_aes_gcm_decrypt_blocks_to` leaves: the decryption of the
ciphertext in the output, the counter advanced, and `Y` continued over the
ciphertext. -/
def blocksToDecPost (s s' : State) : Prop :=
  let n := (s.gpr .r9).toNat
  let c := blocksAt s.mem (s.gpr .r8) n
  blocksAt s'.mem (arg s 0) n = ctr32 (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (blockAt s.mem (s.gpr .rdx)) c ∧
    blockAt s'.mem (s.gpr .rdx) = Nat.repeat inc32 n (blockAt s.mem (s.gpr .rdx)) ∧
    blockAt s'.mem (s.gpr .rcx) = ghashFrom (ctxH s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rcx)) c

/-- `vg_aes_gcm_decrypt_blocks_to`, for a key context of kind `M`. -/
def decryptBlocksToX86_64M (M : CtxMode) : Contract isa where
  pre := blocksToPreM M
  post := blocksToDecPost
  pub := blocksToPub

end VG.Proof.AesGcm

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64

open Gcm.X86_64.Stitch (CtxMode StitchToDecOkM) in
/-- An out-of-place interleaved decryption loop for a key context of kind
`M`, on whole groups of 16 blocks, with its proof. -/
structure StitchToDecCode (M : CtxMode) (aligned : Bool := false) where
  dec : Prog isa
  ok : StitchToDecOkM M dec
  P : PieceTo dec aligned false

end VG.Proof.AesGcm.X86_64

end

end

/-!
# AES-GCM decryption of whole blocks out of place, x86-64: correctness

Untrusted: everything here is checked by Lean. As `BlocksTo` proves of
`vg_aes_gcm_encrypt_blocks_to`, whose code this is, with `Y` continued over
the ciphertext, read from `src` (`pt`), which nothing writes: `MidD s q k`
is `BlocksTo.Mid` with that `Y`, which holds after the entry, after the
out-of-place decryption loop (`mid_of_postToDec`, from `DPostTo`) and after
`rest`; the blocks left are copied to the output, decrypted there by a call
of `vg_aes_gcm_decrypt_blocks`, which hashes them as it reads them
(`blkD_call`), and their GHASH continues that of the first
(`ghashFrom_append`, `blocksAt_add`): `decrypt_wp`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.BlocksToDec

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.BlocksTo VG.WriteBytes
open VG.Proof.AesGcm.X86_64.BlocksTo
open VG.Impl.AesGcm.X86_64.Blocks (argCtx argRounds argCtr argY argN)
open VG.Impl.AesGcm.X86_64.BlocksToDec (ghArgsTo ctrArgsTo tailTo decryptTo)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode SPreTo DPostTo StitchToDecOkM)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32 aesWith)

/-- The ciphertext of the first `q` blocks, at `src`. -/
abbrev pt (s : State) (q : Nat) : List Block := blocksAt s.mem (Src s) q

/-- The first `q` blocks decrypted into the output and their ciphertext
hashed, the arguments kept for what is left after `k` blocks. -/
structure MidD (s : State) (q k : Nat) (st : State) : Prop where
  q_le : q ≤ n s
  rsp : st.gpr .rsp = SP s
  saved : ∀ r ∈ calleeSaved, st.gpr r = s.gpr r
  rd : st.rd = s.rd
  wr : st.wr = s.wr
  kept : Kept s k st.mem
  frame : Frame (wR s) s.mem st.mem
  data : blocksAt st.mem (Dst s) q = ct s q
  ctr : blockAt st.mem (C s) = Nat.repeat inc32 q (cb s)
  y : blockAt st.mem (Y s) = ghashFrom (hk s) (y₀ s) (pt s q)

/-- What the function returns with. -/
def DoneD (s s' : State) : Prop := gprPreserved s s' ∧ Proof.AesGcm.blocksToDecPost s s'

section
variable {aligned : Bool} {M : CtxMode} {s : State} (hp : BT M s)
include hp

theorem mid_entry {s₁ : State} (hsp : s₁.gpr .rsp = s.gpr .rsp)
    (hcs : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r)
    (hk : Kept s 0 s₁.mem) (hf : Frame [kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    MidD s 0 0 s₁ :=
  ⟨Nat.zero_le _, hsp, hcs, hrd, hwr, hk, frame_kR' hf, rfl,
    block_kR' hf (kR'_disj hp _ (by simp)).symm, block_kR' hf (kR'_disj hp _ (by simp)).symm⟩

/-- `MidD` through a frame of `scratch`'s slots that keeps the stack pointer
and the callee-saved registers. -/
theorem MidD.slots {q k k' : Nat} {st st' : State} (h : MidD s q k st)
    (hsp : st'.gpr .rsp = st.gpr .rsp) (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) (hk : Kept s k' st'.mem)
    (hf : Frame [kR' s] st.mem st'.mem) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) : MidD s q k' st' := by
  refine ⟨h.q_le, by rw [hsp, h.rsp], fun r hr => by rw [hcs r hr, h.saved r hr], hrd.trans h.rd,
    hwr.trans h.wr, hk, h.frame.trans (frame_kR' hf), ?_, ?_, ?_⟩
  · rw [← h.data]
    exact blocksAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [Nat.mul_comm]
      exact (kR'_disj hp (dR s) (by simp)).symm.sub_left (Region.sub_prefix (by have := h.q_le; omega_arith)))
      (by have := hp.w_d; have := h.q_le; omega_arith)
  · rw [← h.ctr]; exact block_kR' hf (kR'_disj hp _ (by simp)).symm
  · rw [← h.y]; exact block_kR' hf (kR'_disj hp _ (by simp)).symm

/-- `rest`: the arguments of the `n mod 16` blocks after the first
`16 ⌊n / 16⌋`. -/
theorem rest_ok {q : Nat} (hq : q = n s - n s % 16) {st : State} (h : MidD s q 0 st) :
    WP isa (.block rest) st (MidD s q q) := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have a₂ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 24) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 2) (by decide)
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 24) 64 = S s := by
    rw [h.rsp, show (24 : Nat) = 8 * (2 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  have r₅ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 32) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₇ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 48) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have w₅ : InRegions st.wr (S s + BitVec.ofNat 64 32) 8 := by rw [h.wr]; exact s_in hp (by decide)
  have w₆ : InRegions st.wr (S s + BitVec.ofNat 64 40) 8 := by rw [h.wr]; exact s_in hp (by decide)
  have w₇ : InRegions st.wr (S s + BitVec.ofNat 64 48) 8 := by rw [h.wr]; exact s_in hp (by decide)
  have kr := h.kept.src
  have kn := h.kept.n
  have kd := h.kept.dst
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.sub_zero] at kr kn kd
  have e15 := and15 (BitVec.ofNat 64 (n s))
  rw [toNat_ofNat_of_lt hn, imm_eq (by decide)] at e15
  have esub : BitVec.ofNat 64 (n s) - BitVec.ofNat 64 (n s % 16) = BitVec.ofNat 64 q := by
    rw [hq]; exact ofNat_sub (Nat.mod_le _ _) hn
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2112 → d + 8 ≤ 2112 →
      Mem.Sep (S s + BitVec.ofNat 64 a) (64 / 8) (S s + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep _ h (by omega_arith) (by omega_arith)
  have s₅₇ := sep 32 48 (by decide) (by decide) (by decide)
  have s₅₆ := sep 32 40 (by decide) (by decide) (by decide)
  have s₆₇ := sep 40 48 (by decide) (by decide) (by decide)
  have s₇₅ := sep 48 32 (by decide) (by decide) (by decide)
  have kp : ∀ d, d + 8 ≤ 32 → ∀ u v w : BitVec 64,
      (((st.mem.writeW (S s + BitVec.ofNat 64 32) u).writeW (S s + BitVec.ofNat 64 48) v).writeW
        (S s + BitVec.ofNat 64 40) w).readW (S s + BitVec.ofNat 64 d) 64 =
        st.mem.readW (S s + BitVec.ofNat 64 d) 64 := fun d h₁ u v w => by
    rw [Mem.readW_writeW_sep (sep d 40 (.inl (by omega_arith)) (by omega_arith) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep d 48 (.inl (by omega_arith)) (by omega_arith) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep d 32 (.inl (by omega_arith)) (by omega_arith) (by decide)) (by decide)]
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [rest, argSrc, argN, argDst]
    xrun [a₂, hS, r₅, r₆, r₇, w₅, w₆, w₇, kn, e15, esub, times16_val, kr, kd, s₅₇, s₅₆, s₆₇, s₇₅,
      Mem.readW_writeW_sep, Mem.readW_writeW_self64], ?_⟩
  refine h.slots hp (by simp [gpr_setReg, gpr_arithFlags]) (fun r hr => ?_) ?_ ?_ rfl rfl
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := kp 0 (by decide); simp only [BitVec.add_zero] at this; rw [this]; exact h.kept.ctx
    · rw [kp 8 (by decide)]; exact h.kept.rounds
    · rw [kp 16 (by decide)]; exact h.kept.ctr
    · rw [kp 24 (by decide)]; exact h.kept.y
    · rw [Mem.readW_writeW_sep (sep 32 40 (.inl (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_sep (sep 32 48 (.inl (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64, BitVec.add_comm]
    · rw [Mem.readW_writeW_self64, hq]; congr 1; omega_arith
    · rw [Mem.readW_writeW_sep (sep 48 40 (.inr (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64, BitVec.add_comm]
  · have c : ∀ d, d + 8 ≤ 56 → (kR' s).Contains (S s + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ => Offset.contains_base _ h₁ (by omega_arith)
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 32 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 48 (by decide))).writeW (List.mem_singleton_self _) _ (c 40 (by decide))

/-- `MidD` after the out-of-place loops, from what they leave. -/
theorem mid_of_postToDec {q k : Nat} {s₃ s₄ : State} (hqn : q ≤ n s) (h9 : s₃.gpr .r9 = BitVec.ofNat 64 q)
    (hg : ∀ r ∈ BlocksTo.argRegs, s₃.gpr r = s.gpr r) (hcs : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r)
    (h10 : s₃.gpr .r10 = Dst s) (h11 : s₃.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)))
    (hrd : s₃.rd = s.rd) (hwr : s₃.wr = s.wr) (hkp : Kept s k s₃.mem) (hf₃ : Frame [kR' s] s.mem s₃.mem)
    (P : DPostTo s₃ s₄) : MidD s q k s₄ := by
  obtain hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have data := P.data
  have ctr := P.ctr
  have frame := P.frame
  have y := P.y
  obtain hq9 : (s₃.gpr .r9).toNat = q := by rw [h9, toNat_ofNat_of_lt (by omega_using [hqn, hn])]
  obtain ek : s₃.gpr .rdi = K s := hg _ (by simp [BlocksTo.argRegs])
  obtain er : s₃.gpr .rsi = s.gpr .rsi := hg _ (by simp [BlocksTo.argRegs])
  obtain ec : s₃.gpr .rdx = C s := hg _ (by simp [BlocksTo.argRegs])
  obtain ey : s₃.gpr .rcx = Y s := hg _ (by simp [BlocksTo.argRegs])
  obtain ed : s₃.gpr .r8 = Src s := hg _ (by simp [BlocksTo.argRegs])
  simp only [Gcm.X86_64.Stitch.cR, Gcm.X86_64.Stitch.yR, Gcm.X86_64.Stitch.oR, Gcm.X86_64.Stitch.pR,
    Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.op, Gcm.X86_64.Stitch.pp,
    Gcm.X86_64.Stitch.nb, ec, ey, h10, h11, hq9] at frame
  simp only [Gcm.X86_64.Stitch.op, Gcm.X86_64.Stitch.sp, Gcm.X86_64.Stitch.nb, Gcm.X86_64.Stitch.cb,
    Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.ciph, Gcm.X86_64.Stitch.sch, Gcm.X86_64.Stitch.nr,
    Gcm.X86_64.Stitch.kp, ek, er, ec, ed, h10, hq9] at data
  simp only [Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.cb, Gcm.X86_64.Stitch.nb, ec, hq9] at ctr
  simp only [Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.hk, Gcm.X86_64.Stitch.y₀, Gcm.X86_64.Stitch.kp,
    Gcm.X86_64.Stitch.sp, Gcm.X86_64.Stitch.nb, ey, ek, ed, hq9] at y
  obtain kd : ∀ r ∈ [kR' s], (kR M s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.k_s.sub_right kR'_sub
  obtain hRb : 16 * (R s + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> simp only [R, h] <;> decide
  obtain eK : Spec.Aes.bytesAt s₃.mem (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt s.mem (K s) (16 * (R s + 1)) :=
    bytesAt_frame hf₃ (fun r hr => (kd r hr).sub_left (Region.sub_prefix (Nat.le_trans hRb M.ge)))
      (by have := hp.w_k; have := M.ge; omega_using [hRb])
  obtain eH : blockAt s₃.mem (K s + 240) = hk s :=
    block_kR' hf₃ ((hp.k_s.sub_right kR'_sub).sub_left (Offset.sub_base (d := 240) _ (by have := M.ge; omega_using [this])))
  obtain eC : blockAt s₃.mem (C s) = cb s := block_kR' hf₃ (kR'_disj hp _ (by simp)).symm
  obtain eY : blockAt s₃.mem (Y s) = y₀ s := block_kR' hf₃ (kR'_disj hp _ (by simp)).symm
  obtain pr : Region.Sub ⟨Src s, 16 * q⟩ (srcR s) := Region.sub_prefix (by omega_using [hqn])
  obtain eS : blocksAt s₃.mem (Src s) q = blocksAt s.mem (Src s) q := blocksAt_frame hf₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hp.r_s.sub_left pr).sub_right kR'_sub)
    (by have := hp.w_r; omega_using [hqn, this])
  rw [eK, eC, eS] at data
  rw [eC] at ctr
  rw [eH, eY, eS] at y
  obtain pd : Region.Sub ⟨Dst s, 16 * q⟩ (dR s) := Region.sub_prefix (by omega_using [hqn])
  obtain sk : Region.Disjoint (kR' s) ⟨S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)), 1024⟩ :=
    Offset.base_disjoint _ (by have := AlignedScratch.offset_bounds aligned (S s); omega_using [this]) (by have := hp.w_s; have := AlignedScratch.offset_bounds aligned (S s); omega_using [this])
  obtain fk : ∀ r ∈ [cR s, yR s, (⟨Dst s, 16 * q⟩ : Region), (⟨S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)), 1024⟩ : Region)],
      (kR' s).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact kR'_disj hp _ (by simp)
    · exact kR'_disj hp _ (by simp)
    · exact (kR'_disj hp (dR s) (by simp)).sub_right pd
    · exact sk
  obtain fw : Frame (wR s) s.mem s₄.mem := by
    refine (frame_kR' hf₃).trans (frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨cR s, by simp, fun _ h => h⟩
    · exact ⟨yR s, by simp, fun _ h => h⟩
    · exact ⟨dR s, by simp, pd⟩
    · exact ⟨sR s, by simp, Offset.sub_base _ (by have := AlignedScratch.offset_bounds aligned (S s); omega_using [this])⟩
  refine ⟨hqn, ?_, fun r hr => ?_, P.rd.trans hrd, P.wr.trans hwr, hkp.frame frame fk, fw, data, ctr, y⟩
  · rw [P.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hg _ (by simp [BlocksTo.argRegs])
  · have hr' : r ≠ .rax ∧ r ≠ .rdx ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [P.gpr r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2.1 hr'.2.2.2.2]; exact hcs r hr

/-- The interleaved part, from the state after the entry. -/
theorem stitch_ok {piece : Prog isa} (hpiece : StitchToDecOkM M piece)
    {s₁ : State} (h11 : s₁.gpr .r11 = S s) (h10 : s₁.gpr .r10 = Dst s)
    (hg : ∀ r, r ≠ .r11 → r ≠ .r10 → s₁.gpr r = s.gpr r)
    (hk : Kept s 0 s₁.mem) (hf : Frame [kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    WP isa (stitchPart piece aligned) s₁ (MidD s (n s - n s % 16) 0) := by
  refine WP.seq (WP.mono (BlocksTo.cmp16_ok (hg _ (by decide) (by decide))) fun s₂ ⟨g₂, m₂, rd₂, wr₂, cf₂⟩ => ?_)
  refine WP.ite (decide (n s < 16)) (by simp only [eval, cf₂]) (fun h => ?_) (fun h => ?_)
  · have h0 : n s - n s % 16 = 0 := by simp at h; omega_using [h]
    rw [h0]
    refine WP.block_nil (mid_entry hp (by rw [g₂]; exact hg _ (by decide) (by decide))
      (fun r hr => by rw [g₂]; exact hg r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr))
      (by rw [m₂]; exact hk) (by rw [m₂]; exact hf) (rd₂.trans hrd) (wr₂.trans hwr))
  · have h16 : 16 ≤ n s := by simp at h; omega_using [h]
    refine WP.seq (WP.mono (BlocksTo.split_ok hp (s := s) (s₁ := s₂) (by rw [g₂]; exact hg _ (by decide) (by decide))
      (by rw [g₂, h11])) fun s₃ ⟨h9, h11₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
    obtain h10₃ : s₃.gpr .r10 = Dst s := by rw [g₃ _ (by decide) (by decide) (by decide), g₂, h10]
    obtain keepR : ∀ r, r ≠ .rax → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s₃.gpr r = s.gpr r := fun r a b c d => by
      rw [g₃ r a b d, g₂, hg r d c]
    obtain ga : ∀ r ∈ BlocksTo.argRegs, s₃.gpr r = s.gpr r := fun r hr => by
      simp only [BlocksTo.argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact keepR _ (by decide) (by decide) (by decide) (by decide)
    obtain gc : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r := fun r hr => by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact keepR _ (by decide) (by decide) (by decide) (by decide)
    obtain rd₃' : s₃.rd = s.rd := rd₃.trans (rd₂.trans hrd)
    obtain wr₃' : s₃.wr = s.wr := wr₃.trans (wr₂.trans hwr)
    obtain hk₃ : Kept s 0 s₃.mem := by rw [m₃, m₂]; exact hk
    obtain hf₃ : Frame [kR' s] s.mem s₃.mem := by rw [m₃, m₂]; exact hf
    obtain hm : Gcm.X86_64.Stitch.nb s₃ % 16 = 0 := by
      obtain hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
      simp only [Gcm.X86_64.Stitch.nb, h9, toNat_ofNat_of_lt (show n s - n s % 16 < 2 ^ 64 by omega_using [hn])]; omega_using []
    exact WP.mono (hpiece s₃ (BlocksTo.spreTo_of hp (by omega_using [h16]) (by omega_using []) h9 ga h10₃ h11₃ rd₃' wr₃' hf₃) hm) fun s₄ hP =>
      mid_of_postToDec hp (by omega_using []) h9 ga gc h10₃ h11₃ rd₃' wr₃' hk₃ hf₃ hP

/-- With nothing left, `MidD` is the end. -/
theorem done_of {q : Nat} {st : State} (h : MidD s q q st) (h0 : n s - q = 0) : DoneD s st := by
  obtain hq : q = n s := by have := h.q_le; omega_arith
  subst hq
  exact ⟨⟨h.saved, keep_r hp h.frame⟩, h.data, h.ctr, h.y⟩

/-- The head of `tail`: `rcx` the number of blocks left, `ZF` if none. -/
theorem tailHead_ok {q : Nat} {st : State} (h : MidD s q q st) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 24)), .mov .rcx (.mem (at_ .r11 argN)), .alu .test .rcx (.reg .rcx)])
      st fun st' => MidD s q q st' ∧ st'.zf = some (decide (n s - q = 0)) ∧
        st'.gpr .r11 = S s ∧ st'.gpr .rcx = BitVec.ofNat 64 (n s - q) ∧ st'.mem = st.mem := by
  obtain hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  obtain a₂ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 24) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 2) (by decide)
  obtain hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 24) 64 = S s := by
    rw [h.rsp, show (24 : Nat) = 8 * (2 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  obtain r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  obtain hz := and_self_beq (show n s - q < 2 ^ 64 by omega_arith)
  apply WP.of_runBlock
  refine ⟨_, by simp only [argN]; xrun [a₂, hS, r₆, h.kept.n], ?_, by simp only [zf_arithFlags, hz],
    by simp [gpr_setReg, gpr_arithFlags], by simp [gpr_setReg, gpr_arithFlags], by rfl⟩
  exact h.slots hp (by simp [gpr_setReg, gpr_arithFlags]) (fun r hr => by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags])
    h.kept (Frame.refl _ _) rfl rfl

/-- The pointers of the copy. -/
theorem ptrs_ok {q : Nat} {st : State} (h : MidD s q q st) (h11 : st.gpr .r11 = S s) :
    WP isa (.block [.mov .rsi (.mem (at_ .r11 argSrc)), .mov .rdi (.mem (at_ .r11 argDst))]) st
      fun st' => st'.gpr .rsi = sq s q ∧ st'.gpr .rdi = dq s q ∧
        (∀ r, r ≠ .rsi → r ≠ .rdi → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧
        st'.wr = st.wr := by
  obtain r₅ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 32) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  obtain r₇ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 48) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  apply WP.of_runBlock
  refine ⟨_, by simp only [argSrc, argDst]; xrun [h11, r₅, r₇, h.kept.src, h.kept.dst], ?_, ?_, ?_, by rfl, by rfl,
    by rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]

/-- What the copy leaves: the ciphertext left in the output, nothing else
written. -/
theorem copy_ok {q : Nat} {st : State} (h : MidD s q q st) (hlt : q < n s)
    (hsi : st.gpr .rsi = sq s q) (hdi : st.gpr .rdi = dq s q) (hcx : st.gpr .rcx = BitVec.ofNat 64 (n s - q)) :
    WP isa copyBlocks st fun st' =>
      blocksAt st'.mem (dq s q) (n s - q) = blocksAt s.mem (sq s q) (n s - q) ∧
      Frame [⟨dq s q, 16 * (n s - q)⟩] st.mem st'.mem ∧
      (∀ r, r ≠ .r10 → r ≠ .rcx → st'.gpr r = st.gpr r) ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have hq := h.q_le
  obtain h16 := n16_lt hp
  have hwr := hp.w_r
  have hwd := hp.w_d
  obtain ss : Region.Sub ⟨sq s q, 16 * (n s - q)⟩ (srcR s) := Offset.sub_base _ (by omega_arith)
  obtain ds : Region.Sub ⟨dq s q, 16 * (n s - q)⟩ (dR s) := Offset.sub_base _ (by omega_arith)
  obtain pre : CopyPre st (sq s q) (dq s q) (n s - q) :=
    ⟨hsi, hdi, hcx, by omega_arith, by omega_arith,
      Blocks.covers_off' (covers_of_mem (r := srcR s) (by rw [h.rd, h.wr, hp.rd]; simp)) (by omega_arith) (by omega_arith),
      Blocks.covers_off' (covers_of_mem (r := dR s) (by rw [h.wr, hp.wr]; simp)) (by omega_arith) (by omega_arith),
      (hp.r_d.sub_left ss).sub_right ds⟩
  refine WP.mono (copyBlocks_wp st pre) fun st' ⟨hm, hg, hrd, hwr'⟩ => ⟨?_, ?_, hg, hrd, hwr'⟩
  · have e := bytesAt_writeBytes_self st.mem (dq s q) (Spec.Aes.bytesAt st.mem (sq s q) (16 * (n s - q)))
      (by rw [length_bytesAt]; omega_arith)
    rw [length_bytesAt] at e
    rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq, hm, e,
      bytesAt_frame h.frame (fun r hr => (src_wR hp r hr).sub_left ss) (by omega_arith)]
  · rw [hm]; exact writeBytes_frame' _ (length_bytesAt _ _ _)

/-- `MidD` through the copy, which writes only the output past the first `q`
blocks. -/
theorem MidD.copy {q : Nat} {st st' : State} (h : MidD s q q st)
    (hf : Frame [⟨dq s q, 16 * (n s - q)⟩] st.mem st'.mem) (hsp : st'.gpr .rsp = st.gpr .rsp)
    (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) :
    MidD s q q st' := by
  have hq := h.q_le
  have hwd := hp.w_d
  obtain h16 := n16_lt hp
  obtain ds : Region.Sub ⟨dq s q, 16 * (n s - q)⟩ (dR s) := Offset.sub_base _ (by omega_arith)
  obtain one : ∀ {r : Region}, r.Disjoint ⟨dq s q, 16 * (n s - q)⟩ →
      ∀ r' ∈ [(⟨dq s q, 16 * (n s - q)⟩ : Region)], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  refine ⟨hq, by rw [hsp, h.rsp], fun r hr => by rw [hcs r hr, h.saved r hr], hrd.trans h.rd, hwr.trans h.wr,
    h.kept.frame hf (one ((kR'_disj hp (dR s) (by simp)).sub_right ds)), h.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s, by simp, ds⟩), ?_, ?_, ?_⟩
  · rw [← h.data]
    exact blocksAt_frame hf (one (Offset.base_disjoint (Dst s) (k := 16 * q) (e := 16 * q) (n := 16 * (n s - q))
      (Nat.le_refl _) (by omega_arith))) (by omega_arith)
  · rw [← h.ctr]; exact blockAt_frame hf (one (hp.c_d.sub_right ds))
  · rw [← h.y]; exact blockAt_frame hf (one (hp.y_d.sub_right ds))

/-- The arguments of `vg_aes_gcm_decrypt_blocks` on the output left. -/
theorem args_ok {q : Nat} {st : State} (h : MidD s q q st) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 24)), .mov .rdi (.mem (at_ .r11 argCtx)),
        .mov .rsi (.mem (at_ .r11 argRounds)), .mov .rdx (.mem (at_ .r11 argCtr)),
        .mov .rcx (.mem (at_ .r11 argY)), .mov .r8 (.mem (at_ .r11 argDst)), .mov .r9 (.mem (at_ .r11 argN)),
        .mov .rax (.reg .r11)]) st fun st' =>
      st'.gpr .rdi = K s ∧ st'.gpr .rsi = s.gpr .rsi ∧ st'.gpr .rdx = C s ∧ st'.gpr .rcx = Y s ∧
      st'.gpr .r8 = dq s q ∧ st'.gpr .r9 = BitVec.ofNat 64 (n s - q) ∧ st'.gpr .rax = S s ∧
      st'.gpr .rsp = SP s ∧ (∀ r ∈ calleeSaved, st'.gpr r = s.gpr r) ∧ st'.mem = st.mem ∧
      st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain a₂ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 24) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 2) (by decide)
  obtain hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 24) 64 = S s := by
    rw [h.rsp, show (24 : Nat) = 8 * (2 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  obtain r₁ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 0) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  obtain kc0 : st.mem.readW (S s + BitVec.ofNat 64 0) 64 = K s := by simpa using h.kept.ctx
  obtain r₂ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 8) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  obtain r₃ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 16) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  obtain r₄ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 24) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  obtain r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  obtain r₇ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 48) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [argCtx, argRounds, argCtr, argY, argDst, argN]
    xrun [a₂, hS, r₁, r₂, r₃, r₄, r₆, r₇, kc0, h.kept.rounds, h.kept.ctr, h.kept.y, h.kept.dst, h.kept.n], ?_⟩
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg],
    by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg, h.rsp],
    fun r hr => ?_, by rfl, by rfl, by rfl⟩
  rw [← h.saved r hr]
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]

/-- What the call needs, after the push of `scratch`. -/
theorem blkCall_of {q : Nat} {st : State} (h : MidD s q q st) (hlt : q < n s)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = C s) (h_cx : st.gpr .rcx = Y s)
    (h_8 : st.gpr .r8 = dq s q) (h_9 : st.gpr .r9 = BitVec.ofNat 64 (n s - q)) (h_ax : st.gpr .rax = S s) :
    BlkCall M (pushed [.rax] st) (K s) (C s) (Y s) (dq s q) (S s) (R s) (n s - q) := by
  have hq := h.q_le
  have hwd := hp.w_d
  obtain h16 := n16_lt hp
  have hsp := h.rsp
  have wt := hp.w_t
  obtain hn8 : 8 * [Reg.rax].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.rax] (by decide) hn8
  obtain psp : (pushed [.rax] st).gpr .rsp = SP s - BitVec.ofNat 64 8 := by rw [pushed_rsp, hsp]; rfl
  obtain harg : (pushed [.rax] st).mem.readW ((pushed [.rax] st).gpr .rsp) 64 = S s := by
    have := hpj 0 (by decide); rw [← h_ax]; rw [pushed_rsp]; exact this
  obtain ds : Region.Sub ⟨dq s q, (n s - q) * 16⟩ (dR s) := Offset.sub_base _ (by omega_arith)
  obtain tt := pushed_tR (s := s) hsp
  obtain hdq : (dq s q).toNat = (Dst s).toNat + 16 * q := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * q) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  obtain hR : BitVec.ofNat 64 (R s) = s.gpr .rsi := by simp [R]
  obtain hok : M.ok st.mem (K s) := M.frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hp.k_c, hp.k_y, hp.k_d, hp.k_s]) hp.w_k hp.ok
  refine ⟨by rw [pushed_gpr _ _ (by decide)]; exact h_di, by rw [pushed_gpr _ _ (by decide), h_si, hR],
    by rw [pushed_gpr _ _ (by decide)]; exact h_dx, by rw [pushed_gpr _ _ (by decide)]; exact h_cx,
    by rw [pushed_gpr _ _ (by decide)]; exact h_8, by rw [pushed_gpr _ _ (by decide)]; exact h_9, harg, hp.rounds,
    hp.w_k, hp.w_c, hp.w_y, by rw [hdq]; omega_arith, hp.w_s, ?_,
    hp.k_c, hp.k_y, hp.k_d.sub_right ds, hp.k_s, hp.c_y, hp.c_d.sub_right ds, hp.c_s, hp.y_d.sub_right ds, hp.y_s,
    hp.d_s.sub_left ds, by rw [tt]; exact hp.b_k, by rw [tt]; exact hp.b_c, by rw [tt]; exact hp.b_y,
    by rw [tt]; exact hp.b_d.sub_right ds, by rw [tt]; exact hp.b_s, ?_, ?_, ?_⟩
  · rw [psp, show SP s - BitVec.ofNat 64 8 - 8 = SP s - BitVec.ofNat 64 16 by rw [← Offset.sub_add_eq]; rfl,
      toNat_sub_ofNat (by omega_arith)]
    omega_arith
  · simp only [pushed_rd, pushed_wr, h.rd, h.wr, hp.rd, hp.wr, hsp]
    refine covers_cons (covers_of_mem (by simp)) (covers_cons (covers_of_mem (by rw [pushed_rsp, hsp]; simp))
      (covers_cons (covers_of_mem (by simp)) (covers_cons (covers_of_mem (by simp))
      (covers_cons ?_ (covers_cons (covers_of_mem (by simp)) covers_nil)))))
    exact Blocks.covers_off' (covers_of_mem (r := dR s) (by simp)) (by omega_arith) (by omega_arith)
  · simp only [pushed_wr, h.wr, hp.wr, hsp]
    refine covers_cons (covers_of_mem (by simp)) (covers_cons (covers_of_mem (by simp))
      (covers_cons ?_ (covers_cons (covers_of_mem (by simp)) covers_nil)))
    exact Blocks.covers_off' (covers_of_mem (r := dR s) (by simp)) (by omega_arith) (by omega_arith)
  · exact M.frame hpf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [hsp]
      exact (hp.b_k.sub_left (below_sub (by decide) (by decide))).symm) hp.w_k hok

/-- What the call leaves, after the frame's pop. -/
theorem call_ok (B : BlkFn M) {q : Nat} {st : State} (h : MidD s q q st) (hlt : q < n s)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = C s) (h_cx : st.gpr .rcx = Y s)
    (h_8 : st.gpr .r8 = dq s q) (h_9 : st.gpr .r9 = BitVec.ofNat 64 (n s - q)) (h_ax : st.gpr .rax = S s) :
    WP isa (.frame (.push [.rax]) (.call B.dec.name B.dec.code) (.pop .rax 1)) st fun st' =>
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      Frame [cR s, yR s, ⟨dq s q, (n s - q) * 16⟩, sR s, tR s] st.mem st'.mem ∧
      blocksAt st'.mem (dq s q) (n s - q) = ctr32 (aesWith (R s) (Spec.Aes.bytesAt st.mem (K s) (16 * (R s + 1))))
        (blockAt st.mem (C s)) (blocksAt st.mem (dq s q) (n s - q)) ∧
      blockAt st'.mem (C s) = Nat.repeat inc32 (n s - q) (blockAt st.mem (C s)) ∧
      blockAt st'.mem (Y s) = ghashFrom (blockAt st.mem (K s + 240)) (blockAt st.mem (Y s))
        (blocksAt st.mem (dq s q) (n s - q)) := by
  have hq := h.q_le
  have hwd := hp.w_d
  obtain h16 := n16_lt hp
  have hsp := h.rsp
  have wt := hp.w_t
  obtain hn8 : 8 * [Reg.rax].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, -⟩ := pushRegs_mem st [.rax] (by decide) hn8
  obtain hpf' : Frame [below (SP s) 8] st.mem (pushed [.rax] st).mem := by rw [hsp] at hpf; exact hpf
  obtain b8 : Region.Sub (below (SP s) 8) (tR s) := below_sub (by decide) (by decide)
  obtain one : ∀ {r : Region}, (tR s).Disjoint r → ∀ r' ∈ [below (SP s) 8], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hd.sub_left b8).symm
  obtain hRb : 16 * (R s + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> simp only [R, h] <;> decide
  obtain ds : Region.Sub ⟨dq s q, (n s - q) * 16⟩ (dR s) := Offset.sub_base _ (by omega_arith)
  obtain eK : Spec.Aes.bytesAt (pushed [.rax] st).mem (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt st.mem (K s) (16 * (R s + 1)) :=
    bytesAt_frame hpf' (one (hp.b_k.sub_right (Region.sub_prefix (Nat.le_trans hRb M.ge)))) (by have := hp.w_k; have := M.ge; omega_arith)
  obtain eC : blockAt (pushed [.rax] st).mem (C s) = blockAt st.mem (C s) := blockAt_frame hpf' (one hp.b_c)
  obtain eY : blockAt (pushed [.rax] st).mem (Y s) = blockAt st.mem (Y s) := blockAt_frame hpf' (one hp.b_y)
  obtain eD : blocksAt (pushed [.rax] st).mem (dq s q) (n s - q) = blocksAt st.mem (dq s q) (n s - q) :=
    blocksAt_frame hpf' (one (by rw [Nat.mul_comm]; exact hp.b_d.sub_right ds)) (by omega_arith)
  obtain eH : blockAt (pushed [.rax] st).mem (K s + 240) = blockAt st.mem (K s + 240) :=
    blockAt_frame hpf' (one (hp.b_k.sub_right (Offset.sub_base (d := 240) _ (by have := M.ge; omega_arith))))
  refine WP.frame (by simp) (by decide) (by decide) hn8
    (WP.mono (blkD_call B (blkCall_of hp h hlt h_di h_si h_dx h_cx h_8 h_9 h_ax)) fun s₃ ⟨bp, o₁, o₂, o₃⟩ => ?_)
  obtain psp : (pushed [.rax] st).gpr .rsp = SP s - BitVec.ofNat 64 8 := by rw [pushed_rsp, hsp]; rfl
  obtain r₃ := bp.saved _ (by decide : Reg.rsp ∈ calleeSaved)
  refine ⟨r₃, bp.wr, fun m u fm => ?_⟩
  -- The `pop` loses the frame's 8 bytes below `SP`, apart from the outputs.
  obtain fm' : Frame [below (SP s) 8] s₃.mem m := by have := fm; rw [hsp] at this; exact this
  obtain lD : blocksAt m (dq s q) (n s - q) = blocksAt s₃.mem (dq s q) (n s - q) :=
    blocksAt_frame fm' (one (by rw [Nat.mul_comm]; exact hp.b_d.sub_right ds)) (by omega_arith)
  obtain lC : blockAt m (C s) = blockAt s₃.mem (C s) := blockAt_frame fm' (one hp.b_c)
  obtain lY : blockAt m (Y s) = blockAt s₃.mem (Y s) := blockAt_frame fm' (one hp.b_y)
  dsimp only
  refine ⟨fun r hr => ?_, by rw [popped_rd, bp.rd, pushed_rd], by rw [popped_wr, bp.wr, pushed_wr]; rfl,
    ?_, ?_, ?_, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; rw [popped_rsp, r₃, psp, hsp]; exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ hr' (fun e => by subst e; simp [calleeSaved] at hr), bp.saved r hr, pushed_gpr _ _ hr']
  · refine Frame.trans ?_ (fm'.sub fun r hr => ⟨tR s, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact b8⟩)
    refine (hpf'.sub fun r hr => ⟨tR s, by simp, by simp only [List.mem_singleton] at hr; subst hr; exact b8⟩).trans
      (bp.frame.sub fun r hr => ?_)
    simp only [BlkCall.wr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · refine ⟨tR s, by simp, ?_⟩
      obtain e : SP s - BitVec.ofNat 64 8 - BitVec.ofNat 64 16 = SP s - BitVec.ofNat 64 24 := by
        rw [← Offset.sub_add_eq, ← BitVec.ofNat_add]
      show Region.Sub ⟨(pushed [.rax] st).gpr .rsp - BitVec.ofNat 64 16, 16⟩ _
      rw [psp, e]; exact Region.sub_prefix (by decide)
  · rw [lD]; rw [eK, eC, eD] at o₁; exact o₁
  · rw [lC]; rw [eC] at o₂; exact o₂
  · rw [lY]; rw [eH, eY, eD] at o₃; exact o₃

/-- The blocks left, from `MidD s q q`: copied and decrypted in place. -/
theorem tail_ok (B : BlkFn M) {q : Nat} {st : State} (h : MidD s q q st) : WP isa (tail B.dec) st (DoneD s) := by
  have hq := h.q_le
  have hwd := hp.w_d
  have hwr := hp.w_r
  obtain h16 := n16_lt hp
  refine WP.seq (WP.mono (tailHead_ok hp h) fun st₁ ⟨M₁, hz, h11, hcx, hm₁⟩ => ?_)
  refine WP.ite (decide (n s - q = 0)) (by simp only [eval, hz]) (fun e => ?_) (fun e => ?_)
  · simp only [decide_eq_true_eq] at e
    exact WP.block_nil (done_of hp M₁ e)
  obtain hlt : q < n s := by simp at e; omega_arith
  refine WP.seq (WP.mono (ptrs_ok hp M₁ h11) fun st₂ ⟨hsi, hdi, g₂, m₂, rd₂, wr₂⟩ => ?_)
  obtain M₂ : MidD s q q st₂ := M₁.copy hp (by rw [m₂]; exact Frame.refl _ _) (g₂ _ (by decide) (by decide))
    (fun r hr => g₂ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₂ wr₂
  refine WP.seq (WP.mono (copy_ok hp M₂ hlt hsi hdi (by rw [g₂ _ (by decide) (by decide), hcx]))
    fun st₃ ⟨hb₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  obtain M₃ : MidD s q q st₃ := M₂.copy hp f₃ (g₃ _ (by decide) (by decide))
    (fun r hr => g₃ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₃ wr₃
  refine WP.seq (WP.mono (args_ok hp M₃) fun st₄ ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, sp₄, cs₄, m₄, rd₄, wr₄⟩ => ?_)
  obtain M₄ : MidD s q q st₄ := M₃.slots hp (by rw [sp₄, M₃.rsp]) (fun r hr => by rw [cs₄ r hr, M₃.saved r hr])
    (by rw [m₄]; exact M₃.kept) (by rw [m₄]; exact Frame.refl _ _) rd₄ wr₄
  refine WP.mono (call_ok hp B M₄ hlt a₁ a₂ a₃ a₄ a₅ a₆ a₇) fun st₅ ⟨cs₅, rd₅, wr₅, f₅, o₁, o₂, o₃⟩ => ?_
  -- The values the call read.
  obtain hK : Spec.Aes.bytesAt st₄.mem (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt s.mem (K s) (16 * (R s + 1)) :=
    keep_sch hp M₄.frame
  obtain hH : blockAt st₄.mem (K s + 240) = hk s := keep_h hp M₄.frame
  obtain hD₄ : blocksAt st₄.mem (dq s q) (n s - q) = blocksAt s.mem (sq s q) (n s - q) := by rw [m₄]; exact hb₃
  rw [hK, M₄.ctr, hD₄] at o₁
  rw [M₄.ctr] at o₂
  rw [hH, M₄.y, hD₄] at o₃
  -- What the call wrote is apart from the first `q` blocks and the return address.
  obtain ds : Region.Sub ⟨dq s q, (n s - q) * 16⟩ (dR s) := Offset.sub_base _ (by omega_arith)
  obtain keep : ∀ {r : Region}, r.Disjoint (cR s) → r.Disjoint (yR s) → r.Disjoint ⟨dq s q, (n s - q) * 16⟩ →
      r.Disjoint (sR s) → r.Disjoint (tR s) → ∀ r' ∈ [cR s, yR s, ⟨dq s q, (n s - q) * 16⟩, sR s, tR s],
        r.Disjoint r' := by
    intro r a b c d e r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  obtain pq : Region.Sub ⟨Dst s, 16 * q⟩ (dR s) := Region.sub_prefix (by omega_arith)
  obtain hfirst : blocksAt st₅.mem (Dst s) q = ct s q := by
    rw [← M₄.data]
    exact blocksAt_frame f₅ (keep (hp.c_d.symm.sub_left pq) (hp.y_d.symm.sub_left pq)
      (Offset.base_disjoint (Dst s) (k := 16 * q) (e := 16 * q) (Nat.le_refl _) (by omega_arith))
      (hp.d_s.sub_left pq) (hp.b_d.symm.sub_left pq)) (by omega_arith)
  obtain hall : ct s (n s) = ct s q ++ ctr32 (ciph s) (Nat.repeat inc32 q (cb s)) (blocksAt s.mem (sq s q) (n s - q)) := by
    rw [ct, ← Nat.add_sub_cancel' hq, Proof.Gcm.blocksAt_add, Proof.Gcm.ctr32_append, Blocks.length_blocksAt,
      Nat.add_sub_cancel' hq]
  refine ⟨⟨fun r hr => by rw [cs₅ r hr, M₄.saved r hr], ?_⟩, ?_, ?_, ?_⟩
  · show st₅.mem.readW (SP s) 64 = s.mem.readW (SP s) 64
    rw [f₅.readW (Region.contains_self _ _) (keep hp.t_c hp.t_y (hp.t_d.sub_right ds) hp.t_s
      (Offset.base_disjoint_below (SP s) (by omega_arith))) (by decide), keep_r hp M₄.frame]
  · show blocksAt st₅.mem (Dst s) (n s) = ct s (n s)
    rw [← Nat.add_sub_cancel' hq, Proof.Gcm.blocksAt_add, Nat.add_sub_cancel' hq]
    rw [hfirst]; exact (congrArg (ct s q ++ ·) o₁).trans hall.symm
  · show blockAt st₅.mem (C s) = Nat.repeat inc32 (n s) (cb s)
    rw [o₂, ← Proof.Gcm.repeat_add, Nat.sub_add_cancel hq]
  · show blockAt st₅.mem (Y s) = ghashFrom (hk s) (y₀ s) (pt s (n s))
    rw [o₃, ← Proof.Gcm.ghashFrom_append, pt, pt, ← Proof.Gcm.blocksAt_add, Nat.add_sub_cancel' hq]

end

/-! ## Out of place, with no copy -/

section
variable {M : CtxMode} {s : State} (hp : BT M s)
include hp

/-- The calls' working space, after the arguments kept. -/
abbrev W5 (s : State) : Addr := S s + BitVec.ofNat 64 64

omit hp in
theorem w5_sub {k : Nat} (hk : k ≤ 2048) : Region.Sub ⟨W5 s, k⟩ (sR s) := Offset.sub_base _ (by omega_arith)

omit hp in
/-- A call's return address is in the stack below the arguments. -/
theorem ret_sub : Region.Sub (below (SP s) 8) (tR s) := below_sub (by decide) (by decide)

omit hp in
theorem h_sub : Region.Sub ⟨K s + BitVec.ofNat 64 240, 16⟩ (kR M s) :=
  Offset.sub_base _ (by have := M.ge; omega_arith)

omit hp in
theorem k_sub : Region.Sub ⟨K s, 240⟩ (kR M s) :=
  Region.sub_prefix (by have := M.ge; omega_arith)

omit hp in
theorem src_eq : (⟨Src s, 16 * n s⟩ : Region) = srcR s := by rw [Nat.mul_comm]

omit hp in
theorem dst_eq : (⟨Dst s, 16 * n s⟩ : Region) = dR s := by rw [Nat.mul_comm]

/-- The arguments of `vg_ghash` on the `n` blocks at `src`. -/
theorem ghArgsTo_ok {st : State} (h : MidD s 0 0 st) :
    WP isa (.block ghArgsTo) st fun st' =>
      GhCall st' (K s + BitVec.ofNat 64 240) (Y s) (Src s) (W5 s) (n s) ∧ st'.gpr .rsp = SP s ∧
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain h16 := n16_lt hp
  obtain a₂ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 24) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 2) (by decide)
  obtain hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 24) 64 = S s := by
    rw [h.rsp, show (24 : Nat) = 8 * (2 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  obtain r₁ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 0) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  obtain kc0 : st.mem.readW (S s + BitVec.ofNat 64 0) 64 = K s := by simpa using h.kept.ctx
  obtain r₄ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 24) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  obtain r₅ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 32) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  obtain r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  obtain ks0 : st.mem.readW (S s + BitVec.ofNat 64 32) 64 = Src s := by simpa using h.kept.src
  obtain kn0 : st.mem.readW (S s + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (n s) := by simpa using h.kept.n
  obtain s16 : Region.Sub ⟨W5 s, 256⟩ (sR s) := w5_sub (by decide)
  obtain pH := h_sub (s := s) (M := M)
  obtain rs := ret_sub (s := s)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [ghArgsTo, argCtx, argY, argSrc, argN]
    xrun [a₂, hS, r₁, r₄, r₅, r₆, kc0, h.kept.y, ks0, kn0], ?_⟩
  refine ⟨⟨by simp [gpr_setReg, gpr_arithFlags], by simp [gpr_setReg], by simp [gpr_setReg],
    by simp [gpr_setReg], by simp [gpr_setReg, gpr_arithFlags], by omega_arith,
    hp.k_y.sub_left pH, (hp.k_s.sub_left pH).sub_right s16, by rw [src_eq]; exact hp.y_r,
    hp.y_s.sub_right s16, by rw [src_eq]; exact hp.r_s.sub_right s16, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    by simp [gpr_setReg, gpr_arithFlags, h.rsp], fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals try simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ↓reduceIte, h.rsp]
  · exact (hp.b_k.sub_left rs).sub_right pH
  · exact hp.b_y.sub_left rs
  · rw [src_eq]; exact hp.b_r.sub_left rs
  · exact (hp.b_s.sub_left rs).sub_right s16
  · simp only [rd_setReg, wr_setReg, rd_arithFlags, wr_arithFlags, h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨kR M s, by simp, 240, rfl, by have := M.ge; omega_arith⟩
    · exact ⟨srcR s, by simp, 0, by simp, by simp [Nat.mul_comm]⟩
    · exact ⟨yR s, by simp, 0, by simp, by simp⟩
    · exact ⟨sR s, by simp, 64, rfl, by exact (by decide : 64 + 256 ≤ 2112)⟩
  · simp only [wr_setReg, wr_arithFlags, h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨yR s, by simp, 0, by simp, by simp⟩
    · exact ⟨sR s, by simp, 64, rfl, by exact (by decide : 64 + 256 ≤ 2112)⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]

/-- The arguments of `vg_aes_ctr32_to` on the `n` blocks, from `src` to
`dst`, with the arguments kept in memory `m`. -/
theorem ctrArgsTo_ok {st : State} (hsp : st.gpr .rsp = SP s) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr)
    (hk : Kept s 0 st.mem) (ha : st.mem.readW (SP s + BitVec.ofNat 64 24) 64 = S s) :
    WP isa (.block ctrArgsTo) st fun st' =>
      CtrToCall st' (K s) (C s) (Src s) (Dst s) (W5 s) (R s) (n s) ∧ st'.gpr .rsp = SP s ∧
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain h16 := n16_lt hp
  have hwr' := hp.w_r
  have hwd := hp.w_d
  obtain a₂ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 24) 8 := by
    rw [hrd, hwr, hsp]; exact a_in hp (i := 2) (by decide)
  obtain hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 24) 64 = S s := by rw [hsp, ha]
  obtain r₁ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 0) 8 := by rw [hrd, hwr]; exact s_in' hp (by decide)
  obtain kc0 : st.mem.readW (S s + BitVec.ofNat 64 0) 64 = K s := by simpa using hk.ctx
  obtain r₂ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 8) 8 := by rw [hrd, hwr]; exact s_in' hp (by decide)
  obtain r₃ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 16) 8 := by rw [hrd, hwr]; exact s_in' hp (by decide)
  obtain r₅ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 32) 8 := by rw [hrd, hwr]; exact s_in' hp (by decide)
  obtain r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [hrd, hwr]; exact s_in' hp (by decide)
  obtain r₇ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 48) 8 := by rw [hrd, hwr]; exact s_in' hp (by decide)
  obtain ks0 : st.mem.readW (S s + BitVec.ofNat 64 32) 64 = Src s := by simpa using hk.src
  obtain kn0 : st.mem.readW (S s + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (n s) := by simpa using hk.n
  obtain kd0 : st.mem.readW (S s + BitVec.ofNat 64 48) 64 = Dst s := by simpa using hk.dst
  obtain s48 : Region.Sub ⟨W5 s, 2048⟩ (sR s) := w5_sub (by decide)
  have pK : Region.Sub ⟨K s, 240⟩ (kR M s) := k_sub
  obtain rs := ret_sub (s := s)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [ctrArgsTo, argCtx, argRounds, argCtr, argSrc, argN, argDst]
    xrun [a₂, hS, r₁, r₂, r₃, r₅, r₆, r₇, kc0, hk.rounds, hk.ctr, ks0, kn0, kd0], ?_⟩
  refine ⟨⟨by simp [gpr_setReg], by simp [gpr_setReg, R], by simp [gpr_setReg], by simp [gpr_setReg],
    by simp [gpr_setReg], by simp [gpr_setReg, gpr_arithFlags], by simp [gpr_setReg], hp.rounds,
    by omega_arith, by omega_arith,
    hp.k_c.sub_left pK, by rw [dst_eq]; exact hp.k_d.sub_left pK, (hp.k_s.sub_left pK).sub_right s48,
    by rw [src_eq]; exact hp.c_r, by rw [dst_eq]; exact hp.c_d, hp.c_s.sub_right s48,
    by rw [src_eq, dst_eq]; exact hp.r_d, by rw [src_eq]; exact hp.r_s.sub_right s48,
    by rw [dst_eq]; exact hp.d_s.sub_right s48, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    by simp [gpr_setReg, gpr_arithFlags, hsp], fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals try simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ↓reduceIte, hsp]
  · exact (hp.b_k.sub_left rs).sub_right pK
  · exact hp.b_c.sub_left rs
  · rw [src_eq]; exact hp.b_r.sub_left rs
  · rw [dst_eq]; exact hp.b_d.sub_left rs
  · exact (hp.b_s.sub_left rs).sub_right s48
  · simp only [rd_setReg, wr_setReg, rd_arithFlags, wr_arithFlags, hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨kR M s, by simp, 0, by simp, by show 0 + 240 ≤ M.len; have := M.ge; omega_arith⟩
    · exact ⟨srcR s, by simp, 0, by simp, by simp [Nat.mul_comm]⟩
    · exact ⟨cR s, by simp, 0, by simp, by simp⟩
    · exact ⟨dR s, by simp, 0, by simp, by simp [Nat.mul_comm]⟩
    · exact ⟨sR s, by simp, 64, rfl, by exact (by decide : 64 + 2048 ≤ 2112)⟩
  · simp only [wr_setReg, wr_arithFlags, hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨cR s, by simp, 0, by simp, by simp⟩
    · exact ⟨dR s, by simp, 0, by simp, by simp [Nat.mul_comm]⟩
    · exact ⟨sR s, by simp, 64, rfl, by exact (by decide : 64 + 2048 ≤ 2112)⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]

/-- After the hash of the `n` blocks at `src`: `Y` continued over them, and
what the decryption needs (the arguments kept, the stack argument `scratch`,
the counter and the key context through a frame of the regions written and
the stack below the arguments). -/
structure GD (s st : State) : Prop where
  rsp : st.gpr .rsp = SP s
  saved : ∀ r ∈ calleeSaved, st.gpr r = s.gpr r
  rd : st.rd = s.rd
  wr : st.wr = s.wr
  kept : Kept s 0 st.mem
  arg : st.mem.readW (SP s + BitVec.ofNat 64 24) 64 = S s
  frame : Frame (wR s ++ [tR s]) s.mem st.mem
  ctr : blockAt st.mem (C s) = cb s
  y : blockAt st.mem (Y s) = ghashFrom (hk s) (y₀ s) (pt s (n s))

/-- The blocks at `src` hashed: the arguments of `vg_ghash` and its call. -/
theorem ghStep_ok (g : GhashImpl) {st : State} (h : MidD s 0 0 st) :
    WP isa (.seq (.block ghArgsTo) (.call g.fn.name g.fn.code)) st (GD s) := by
  obtain h16 := n16_lt hp
  have hwd := hp.w_d
  have hwr := hp.w_r
  refine WP.seq (WP.mono (ghArgsTo_ok hp h) fun st₂ ⟨G, sp₂, cs₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.mono (gh_call g G) fun st₃ P₃ => ?_
  obtain rs := ret_sub (s := s)
  obtain s16 : Region.Sub ⟨W5 s, 256⟩ (sR s) := w5_sub (by decide)
  obtain k56 : (kR' s).Disjoint ⟨W5 s, 2048⟩ :=
    Offset.disjoint_of_le (by simp only [kR', W5]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := hp.w_s; omega_arith)
      (by simp only [W5]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := hp.w_s; omega_arith)
  obtain F₃ : Frame (wR s ++ [tR s]) s.mem st₃.mem := by
    refine (show Frame (wR s ++ [tR s]) s.mem st₂.mem by
      rw [m₂]; exact h.frame.mono fun r hr => List.mem_append_left _ hr).trans (P₃.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false, sp₂] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨yR s, by simp, fun _ h => h⟩
    · exact ⟨sR s, by simp, s16⟩
    · exact ⟨tR s, by simp, rs⟩
  obtain kept₃ : Kept s 0 st₃.mem := (m₂ ▸ h.kept).frame P₃.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, sp₂] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.y_s.sub_right kR'_sub).symm
    · exact k56.sub_right (Region.sub_prefix (by decide))
    · exact (hp.b_s.sub_left rs).symm.sub_left kR'_sub
  -- The stack argument `scratch`.
  obtain aS : Region.Disjoint (tR s) ⟨SP s + BitVec.ofNat 64 24, 8⟩ := by
    have := hp.w_t; have := hp.w_sp
    intro a h₁ h₂
    simp only [Region.Contains, tR, below, SP] at h₁ h₂
    bv_omega
  obtain hsA : Region.Sub ⟨SP s + BitVec.ofNat 64 24, 8⟩ (aR s) := by
    rw [show SP s + BitVec.ofNat 64 24 = SP s + BitVec.ofNat 64 8 + BitVec.ofNat 64 16 by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
    exact Offset.sub_base _ (by omega_arith)
  obtain ha₃ : st₃.mem.readW (SP s + BitVec.ofNat 64 24) 64 = S s := by
    rw [F₃.readW (r := ⟨SP s + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact hp.c_a.symm.sub_left hsA
      · exact hp.y_a.symm.sub_left hsA
      · exact hp.d_a.symm.sub_left hsA
      · exact hp.s_a.symm.sub_left hsA
      · exact aS.symm) (by decide)]
    rfl
  obtain hC₃ : blockAt st₃.mem (C s) = cb s := by
    rw [blockAt_frame P₃.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, sp₂] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.c_y
      · exact hp.c_s.sub_right s16
      · exact (hp.b_c.sub_left rs).symm), m₂, h.ctr]
    rfl
  have o₃ := P₃.out
  rw [m₂, keep_h hp h.frame, h.y, blocksAt_frame h.frame (fun r hr => by rw [src_eq]; exact src_wR hp r hr)
    (by omega_arith)] at o₃
  exact ⟨by rw [P₃.saved _ (by decide), sp₂], fun r hr => by rw [P₃.saved r hr, cs₂ r hr, h.saved r hr],
    by rw [P₃.rd, rd₂, h.rd], by rw [P₃.wr, wr₂, h.wr], kept₃, ha₃, F₃, hC₃, by rw [o₃]; rfl⟩

/-- The blocks decrypted from `src` to `dst`: the arguments of
`vg_aes_ctr32_to` and its call. -/
theorem ctrStep_ok (v : Proof.Aes.X86_64.Ctr32ToImpl) {st : State} (G : GD s st) :
    WP isa (.seq (.block ctrArgsTo) (.call v.callee.name v.callee.code)) st (DoneD s) := by
  obtain h16 := n16_lt hp
  have hwd := hp.w_d
  have hwr := hp.w_r
  obtain rs := ret_sub (s := s)
  obtain s48 : Region.Sub ⟨W5 s, 2048⟩ (sR s) := w5_sub (by decide)
  refine WP.seq (WP.mono (ctrArgsTo_ok hp G.rsp G.rd G.wr G.kept G.arg) fun st₄ ⟨T, sp₄, cs₄, m₄, _, _⟩ => ?_)
  refine WP.mono (ctrTo_call v T) fun st₅ P₅ => ?_
  obtain F₅ : Frame (wR s ++ [tR s]) s.mem st₅.mem := G.frame.trans (by
    rw [← m₄]
    exact P₅.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, sp₄] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨cR s, by simp, fun _ h => h⟩
      · exact ⟨dR s, by simp, by rw [dst_eq]; exact fun _ h => h⟩
      · exact ⟨sR s, by simp, s48⟩
      · exact ⟨tR s, by simp, rs⟩)
  -- What the call reads.
  obtain hRb : 16 * (R s + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> simp only [R, h] <;> decide
  obtain hK₄ : Spec.Aes.bytesAt st₄.mem (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt s.mem (K s) (16 * (R s + 1)) := by
    obtain hs : Region.Sub ⟨K s, 16 * (R s + 1)⟩ (kR M s) := Region.sub_prefix (by have := M.ge; omega_arith)
    rw [m₄]
    exact bytesAt_frame G.frame (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact hp.k_c.sub_left hs
      · exact hp.k_y.sub_left hs
      · exact hp.k_d.sub_left hs
      · exact hp.k_s.sub_left hs
      · exact hp.b_k.symm.sub_left hs) (by omega_arith)
  obtain hS : blocksAt st.mem (Src s) (n s) = blocksAt s.mem (Src s) (n s) :=
    blocksAt_frame G.frame (fun r hr => by
      rw [src_eq]
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact src_wR hp r hr
      · exact hp.b_r.symm) (by omega_arith)
  have o₁ := P₅.out
  rw [hK₄, m₄, G.ctr, hS] at o₁
  have o₂ := P₅.ctr
  rw [m₄, G.ctr] at o₂
  obtain hY₅ : blockAt st₅.mem (Y s) = blockAt st.mem (Y s) := by
    rw [← m₄]
    exact blockAt_frame P₅.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, sp₄] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.c_y.symm
      · rw [dst_eq]; exact hp.y_d
      · exact hp.y_s.sub_right s48
      · exact (hp.b_y.sub_left rs).symm)
  refine ⟨⟨fun r hr => by rw [P₅.saved r hr, cs₄ r hr, G.saved r hr], ?_⟩, o₁, o₂, by rw [hY₅, G.y]⟩
  show st₅.mem.readW (SP s) 64 = s.mem.readW (SP s) 64
  exact F₅.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.t_c
    · exact hp.t_y
    · exact hp.t_d
    · exact hp.t_s
    · exact Offset.base_disjoint_below (SP s) (by omega_arith)) (by decide)

/-- The blocks, from `MidD s 0 0`: hashed at `src`, then decrypted from
`src` to `dst`. -/
theorem tailTo_ok (g : GhashImpl) (v : Proof.Aes.X86_64.Ctr32ToImpl) {st : State} (h : MidD s 0 0 st) :
    WP isa (tailTo g.fn ⟨v.callee.name, v.callee.code⟩) st (DoneD s) := by
  refine WP.seq (WP.mono (tailHead_ok hp h) fun st₁ ⟨M₁, hz, _, _, _⟩ => ?_)
  refine WP.ite (decide (n s - 0 = 0)) (by simp only [eval, hz]) (fun e => ?_) (fun _ => ?_)
  · simp only [decide_eq_true_eq] at e
    exact WP.block_nil (done_of hp M₁ e)
  exact WP.seq (WP.mono (ghStep_ok hp g M₁) fun _ G => ctrStep_ok hp v G)

end

theorem decrypt_wp {M : CtxMode} (B : BlkFn M) (aligned : Bool) (st : Option (Prog isa))
    (hst : ∀ p, st = some p → StitchToDecOkM M p) {s : State}
    (hpre : Proof.AesGcm.blocksToPreM M s) :
    WP isa (BlocksToDec.decrypt B.dec st aligned) s (DoneD s) := by
  obtain hp := BT.ofM hpre
  refine WP.seq (WP.mono (entry_ok hp) fun s₁ ⟨h11, h10, hg, hk, hf, hrd, hwr⟩ => ?_)
  cases st with
  | none =>
    exact WP.seq (WP.block_nil (tail_ok hp B (mid_entry hp (hg _ (by decide) (by decide))
      (fun r hr => hg r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr))
      hk hf hrd hwr)))
  | some p =>
    exact WP.seq (WP.seq (WP.mono (stitch_ok hp (hst p rfl) h11 h10 hg hk hf hrd hwr) fun st M =>
      WP.mono (rest_ok hp rfl M) fun st' M' => tail_ok hp B M'))

/-- `decryptTo`: the entry, then the blocks hashed at `src` and decrypted
from `src` to `dst`, with no copy. -/
theorem decryptTo_wp {M : CtxMode} (g : GhashImpl) (v : Proof.Aes.X86_64.Ctr32ToImpl) {s : State}
    (hpre : Proof.AesGcm.blocksToPreM M s) :
    WP isa (decryptTo g.fn ⟨v.callee.name, v.callee.code⟩) s (DoneD s) := by
  obtain hp := BT.ofM hpre
  refine WP.seq (WP.mono (entry_ok hp) fun s₁ ⟨_, _, hg, hk, hf, hrd, hwr⟩ => ?_)
  exact tailTo_ok hp g v (mid_entry hp (hg _ (by decide) (by decide))
    (fun r hr => hg r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr))
    hk hf hrd hwr)

end VG.Proof.AesGcm.X86_64.BlocksToDec

end

end

/-!
# AES-GCM decryption of whole blocks out of place, x86-64: constant time, and the callee

Untrusted: everything here is checked by Lean. `BlkToDecFn M`: an instance of
`vg_aes_gcm_decrypt_blocks_to` for a key context of kind `M`, with what its
callers need: its contract (`decryptBlocksToX86_64M`), constant time, and its
code's static facts (no load of `mxcsr`, `rsp` kept, 24 bytes of stack).
`BlkToDecFn.ofBlocks` builds it from an instance of
`vg_aes_gcm_decrypt_blocks` and, if any, an out-of-place decryption loop.

Constant time (`decrypt_ct`), as `BlocksTo/CT.lean` proves of
`vg_aes_gcm_encrypt_blocks_to`, whose code this is, from `MidD` in place of
`Mid`: the entry and the blocks of `tail` are checked by the taint
analysis (`BlocksTo.entry_rel`, `rel_r11`, the `_check`s), the out-of-place
decryption loop from the arguments in their registers and the output in
`r10` (`PieceTo.ct`), the branch on the blocks left agrees, and the copy and
the call of `vg_aes_gcm_decrypt_blocks` get the same pointers and lengths
(`blkD_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.BlocksToDec

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.BlocksTo
open VG.Proof.AesGcm.X86_64.BlocksTo
open VG.Impl.AesGcm.X86_64.Blocks (argCtx argRounds argCtr argY argN)
open VG.Impl.AesGcm.X86_64.BlocksToDec (ghArgsTo ctrArgsTo tailTo decryptTo)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-- `MidD`, with the arguments of the call in their registers. -/
def AP (s : State) (q : Nat) (st : State) : Prop :=
  MidD s q q st ∧ st.gpr .rdi = K s ∧ st.gpr .rsi = s.gpr .rsi ∧ st.gpr .rdx = C s ∧ st.gpr .rcx = Y s ∧
    st.gpr .r8 = dq s q ∧ st.gpr .r9 = BitVec.ofNat 64 (n s - q) ∧ st.gpr .rax = S s

section
variable {M : CtxMode} {s : State} (hp : BT M s)
include hp


/-- `scratch` on the stack, at `MidD`. -/
theorem mid_S {q k : Nat} {st : State} (h : MidD s q k st) :
    st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 24) 64 = S s ∧
      InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 24) 8 := by
  refine ⟨?_, ?_⟩
  · rw [h.rsp, show (24 : Nat) = 8 * (2 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  · rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 2) (by decide)

/-- `MidD` after the pointers of the copy. -/
theorem ptrsM_ok {q : Nat} {st : State} (h : MidD s q q st) (h11 : st.gpr .r11 = S s)
    (hcx : st.gpr .rcx = BitVec.ofNat 64 (n s - q)) :
    WP isa (.block ptrsB) st fun st' => MidD s q q st' ∧ st'.gpr .rsi = sq s q ∧ st'.gpr .rdi = dq s q ∧
      st'.gpr .rcx = BitVec.ofNat 64 (n s - q) :=
  WP.mono (BlocksToDec.ptrs_ok hp h h11) fun _ ⟨hsi, hdi, g₂, m₂, rd₂, wr₂⟩ =>
    ⟨h.copy hp (by rw [m₂]; exact Frame.refl _ _) (g₂ _ (by decide) (by decide))
      (fun r hr => g₂ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₂ wr₂,
      hsi, hdi, by rw [g₂ _ (by decide) (by decide), hcx]⟩

/-- `MidD` after the copy. -/
theorem copyM_ok {q : Nat} {st : State} (h : MidD s q q st) (hlt : q < n s)
    (hsi : st.gpr .rsi = sq s q) (hdi : st.gpr .rdi = dq s q) (hcx : st.gpr .rcx = BitVec.ofNat 64 (n s - q)) :
    WP isa copyBlocks st (MidD s q q) :=
  WP.mono (BlocksToDec.copy_ok hp h hlt hsi hdi hcx) fun _ ⟨_, f₃, g₃, rd₃, wr₃⟩ =>
    h.copy hp f₃ (g₃ _ (by decide) (by decide))
      (fun r hr => g₃ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₃ wr₃

/-- `MidD` after the arguments of the call. -/
theorem argsM_ok {q : Nat} {st : State} (h : MidD s q q st) : WP isa (.block argsB) st (AP s q) :=
  WP.mono (BlocksToDec.args_ok hp h) fun _ ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, sp₄, cs₄, m₄, rd₄, wr₄⟩ =>
    ⟨h.slots hp (by rw [sp₄, h.rsp]) (fun r hr => by rw [cs₄ r hr, h.saved r hr]) (by rw [m₄]; exact h.kept)
      (by rw [m₄]; exact Frame.refl _ _) rd₄ wr₄, a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩

end

theorem ghArgsTo_check : ∃ hc, ((taint.check (Taint.ofRegs [.r11, .rsp]) (.block ghArgsTo.tail) hc).map fun τ' =>
    (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem ctrArgsTo_check : ∃ hc, ((taint.check (Taint.ofRegs [.r11, .rsp]) (.block ctrArgsTo.tail) hc).map fun τ' =>
    (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

/-- What the head of `tail` leaves. -/
def TH (s : State) (q : Nat) (st : State) : Prop :=
  MidD s q q st ∧ st.zf = some (decide (n s - q = 0)) ∧ st.gpr .r11 = S s ∧
    st.gpr .rcx = BitVec.ofNat 64 (n s - q)

section
variable {M : CtxMode} {s₀ s₀' : State} (hp : BT M s₀) (hp' : BT M s₀') (pb : Pub s₀ s₀')
include hp hp' pb


/-- Loading `scratch` from the stack, in two runs at `MidD`. -/
theorem mid_hS {q k q' k' : Nat} {s₁ s₂ : State} (h₁ : MidD s₀ q k s₁) (h₂ : MidD s₀' q' k' s₂) :
    s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 24) 64 = s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 24) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 24) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 24) 8 :=
  ⟨by rw [(mid_S hp h₁).1, (mid_S hp' h₂).1, pb.sc], (mid_S hp h₁).2, (mid_S hp' h₂).2⟩

omit hp hp' in
theorem mid_rsp {q k q' k' : Nat} {s₁ s₂ : State} (h₁ : MidD s₀ q k s₁) (h₂ : MidD s₀' q' k' s₂) :
    ∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rsp, h₂.rsp, pb.sp]

/-- The interleaved part (or nothing) and `rest`, in two runs. -/
theorem part_rel {aligned : Bool} (st : Option (StitchToDecCode M aligned)) :
    RelCT isa (fun s₁ s₂ => (∀ r ∈ .r11 :: BlocksTo.args, s₁.gpr r = s₂.gpr r) ∧ EntryPost s₀ s₁ ∧ EntryPost s₀' s₂)
      (head (st.map (·.dec)) aligned false)
      fun s₁ s₂ => ∃ q, MidD s₀ q q s₁ ∧ MidD s₀' q q s₂ := by
  have me : ∀ (s s₁ : State), BT M s → EntryPost s s₁ → MidD s 0 0 s₁ := fun s s₁ hp h => by
    obtain ⟨_, _, g₁, k₁, f₁, rd₁, wr₁⟩ := h
    exact BlocksToDec.mid_entry hp (g₁ _ (by decide) (by decide))
      (fun r hr => g₁ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr))
      k₁ f₁ rd₁ wr₁
  cases st with
  | none =>
    refine ((rel_regs (.r11 :: BlocksTo.args) [.rsp] false (fun _ _ h => h.1) nil_check).wp
      (F₁ := MidD s₀ 0 0) (F₂ := MidD s₀' 0 0) fun s₁ s₂ h => ⟨WP.block_nil (me _ _ hp h.2.1),
        WP.block_nil (me _ _ hp' h.2.2)⟩).mono (fun _ _ h => h) fun _ _ h => ⟨0, h.2.1, h.2.2⟩
  | some p =>
    have ag : ∀ s₁ s₂, ((∀ r ∈ .r11 :: BlocksTo.args, s₁.gpr r = s₂.gpr r) ∧ EntryPost s₀ s₁ ∧ EntryPost s₀' s₂) →
        ∀ r ∈ [Reg.r10, .r11, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r := by
      intro s₁ s₂ h r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [h.2.1.2.1, h.2.2.2.1, pb.dst]
      · exact h.1 r hr
    rcases p with ⟨dec, ok, P⟩
    have a := rel_wp (rel_regs _ [.rsp] false ag P.ct) (fun _ _ h => h.2)
      (fun _ h => BlocksToDec.stitch_ok hp ok h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2)
      (fun _ h => BlocksToDec.stitch_ok hp' ok h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2)
    have b := rel_wp (rel_r11 (l₀ := rest) (l := rest.tail) rfl
      (P := fun s₁ s₂ => (∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r) ∧
        MidD s₀ (n s₀ - n s₀ % 16) 0 s₁ ∧ MidD s₀' (n s₀' - n s₀' % 16) 0 s₂) [.rsp] [.rsp] (by simp)
      (fun _ _ h => h.1) (fun _ _ h => mid_hS hp hp' pb h.2.1 h.2.2) rest_check)
      (fun _ _ h => h.2) (fun _ h => BlocksToDec.rest_ok hp rfl h) (fun _ h => BlocksToDec.rest_ok hp' rfl h)
    refine (RelCT.seq (a.mono (fun _ _ h => h) fun _ _ h => ⟨h.1.1, h.2⟩) b).mono (fun _ _ h => h)
      fun _ _ h => ⟨n s₀ - n s₀ % 16, h.2.1, ?_⟩
    rw [← pb.en]; exact h.2.2

/-- The call, in two runs at the same point. -/
theorem frame_rel (B : BlkFn M) {q : Nat} (hlt : q < n s₀) :
    RelCT isa (fun s₁ s₂ => AP s₀ q s₁ ∧ AP s₀' q s₂)
      (.frame (.push [.rax]) (.call B.dec.name B.dec.code) (.pop .rax 1)) fun _ _ => True := by
  have hlt' : q < n s₀' := by rw [pb.en]; exact hlt
  refine RelCT.frame (fun _ _ h => by rw [h.1.1.rsp, h.2.1.rsp, pb.sp]) (blkD_rel B fun _ _ ⟨s₁, s₂, h, ha, hb⟩ => ?_)
  obtain ⟨⟨M₁, a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩, ⟨M₂, b₁, b₂, b₃, b₄, b₅, b₆, b₇⟩⟩ := h
  have c₂ := BlocksToDec.blkCall_of hp' M₂ hlt' b₁ b₂ b₃ b₄ b₅ b₆ b₇
  rw [pb.k, pb.c, pb.y, pb.edq, pb.sc, pb.eR, pb.en] at c₂
  exact ⟨_, _, _, _, _, _, _, ha ▸ BlocksToDec.blkCall_of hp M₁ hlt a₁ a₂ a₃ a₄ a₅ a₆ a₇, hb ▸ c₂,
    by rw [ha, hb, pushed_rsp, pushed_rsp, M₁.rsp, M₂.rsp, pb.sp]⟩

/-- `tail`, from two runs at the same point. -/
theorem tail_rel (B : BlkFn M) {q : Nat} :
    RelCT isa (fun s₁ s₂ => MidD s₀ q q s₁ ∧ MidD s₀' q q s₂) (tail B.dec) fun _ _ => True := by
  have a := rel_wp (rel_r11 (l₀ := headB) (l := headB.tail) rfl
      (P := fun s₁ s₂ => MidD s₀ q q s₁ ∧ MidD s₀' q q s₂) [.rsp] [.rsp] (by simp)
      (fun _ _ h => mid_rsp pb h.1 h.2) (fun _ _ h => mid_hS hp hp' pb h.1 h.2) tailHead_check)
    (fun _ _ h => h) (G₁ := TH s₀ q) (G₂ := TH s₀' q)
    (fun _ h => WP.mono (BlocksToDec.tailHead_ok hp h) fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
    (fun _ h => WP.mono (BlocksToDec.tailHead_ok hp' h) fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
  rw [tail_eq]
  refine RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.2.1.2.1, h.2.2.2.1, pb.en]) ?_ ?_)
  · exact (rel_taint [] (fun _ _ _ r hr => by cases hr) empty_check).mono (fun _ _ h => h) fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨⟨-, ⟨M₁, z₁, r11₁, cx₁⟩, ⟨M₂, z₂, r11₂, cx₂⟩⟩, hz⟩ := hP
  have hlt : q < n s₀ := by
    rw [hz] at z₁; simp only [Option.some.injEq, Bool.false_eq, decide_eq_false_iff_not] at z₁; omega_using [z₁]
  have hlt' : q < n s₀' := by rw [pb.en]; exact hlt
  -- The pointers of the copy.
  have b := rel_wp (rel_taint (P := fun s₁ s₂ =>
      (MidD s₀ q q s₁ ∧ s₁.gpr .r11 = S s₀ ∧ s₁.gpr .rcx = BitVec.ofNat 64 (n s₀ - q)) ∧
      (MidD s₀' q q s₂ ∧ s₂.gpr .r11 = S s₀' ∧ s₂.gpr .rcx = BitVec.ofNat 64 (n s₀' - q))) (c := .block ptrsB)
      [.r11] (fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.1, h.2.2.1, pb.sc]) ptrs_check)
    (fun _ _ h => h) (fun _ h => ptrsM_ok hp h.1 h.2.1 h.2.2) (fun _ h => ptrsM_ok hp' h.1 h.2.1 h.2.2)
  have c := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧
      (MidD s₀ q q s₁ ∧ s₁.gpr .rsi = sq s₀ q ∧ s₁.gpr .rdi = dq s₀ q ∧ s₁.gpr .rcx = BitVec.ofNat 64 (n s₀ - q)) ∧
      (MidD s₀' q q s₂ ∧ s₂.gpr .rsi = sq s₀' q ∧ s₂.gpr .rdi = dq s₀' q ∧
        s₂.gpr .rcx = BitVec.ofNat 64 (n s₀' - q))) (c := copyBlocks)
      [.rsi, .rdi, .rcx] (fun _ _ h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.2.1.2.1, h.2.2.2.1, pb.esq]
        · rw [h.2.1.2.2.1, h.2.2.2.2.1, pb.edq]
        · rw [h.2.1.2.2.2, h.2.2.2.2.2, pb.en]) copy_check)
    (fun _ _ h => h.2) (fun _ h => copyM_ok hp h.1 hlt h.2.1 h.2.2.1 h.2.2.2)
    (fun _ h => copyM_ok hp' h.1 hlt' h.2.1 h.2.2.1 h.2.2.2)
  have d := rel_wp (rel_r11 (l₀ := argsB) (l := argsB.tail) rfl
      (P := fun s₁ s₂ => True ∧ MidD s₀ q q s₁ ∧ MidD s₀' q q s₂) [.rsp] [.rsp] (by simp)
      (fun _ _ h => mid_rsp pb h.2.1 h.2.2) (fun _ _ h => mid_hS hp hp' pb h.2.1 h.2.2) args_check)
    (fun _ _ h => h.2) (G₁ := AP s₀ q) (G₂ := AP s₀' q) (fun _ h => argsM_ok hp h) (fun _ h => argsM_ok hp' h)
  have e := (frame_rel hp hp' pb B hlt).mono (P' := fun (s₁ s₂ : State) => (∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r) ∧
    AP s₀ q s₁ ∧ AP s₀' q s₂) (fun _ _ h => h.2) fun _ _ h => h
  exact (RelCT.seq b (RelCT.seq c (RelCT.seq d e))) _ _ _ _ _ _ ⟨⟨M₁, r11₁, cx₁⟩, ⟨M₂, r11₂, cx₂⟩⟩ e₁ e₂

omit hp hp' in
theorem pub_ew5 : BlocksToDec.W5 s₀' = BlocksToDec.W5 s₀ := by simp only [BlocksToDec.W5, pb.sc]

/-- `tailTo`, from two runs after the entry: the branch on the number of
blocks, public, and the calls, with the same public arguments. -/
theorem tailTo_rel (g : GhashImpl) (v : Proof.Aes.X86_64.Ctr32ToImpl) :
    RelCT isa (fun s₁ s₂ => MidD s₀ 0 0 s₁ ∧ MidD s₀' 0 0 s₂) (tailTo g.fn ⟨v.callee.name, v.callee.code⟩)
      fun _ _ => True := by
  have a := rel_wp (rel_r11 (l₀ := headB) (l := headB.tail) rfl
      (P := fun s₁ s₂ => MidD s₀ 0 0 s₁ ∧ MidD s₀' 0 0 s₂) [.rsp] [.rsp] (by simp)
      (fun _ _ h => mid_rsp pb h.1 h.2) (fun _ _ h => mid_hS hp hp' pb h.1 h.2) tailHead_check)
    (fun _ _ h => h) (G₁ := TH s₀ 0) (G₂ := TH s₀' 0)
    (fun _ h => WP.mono (BlocksToDec.tailHead_ok hp h) fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
    (fun _ h => WP.mono (BlocksToDec.tailHead_ok hp' h) fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
  refine RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.2.1.2.1, h.2.2.2.1, pb.en]) ?_ ?_)
  · exact (rel_taint [] (fun _ _ _ r hr => by cases hr) empty_check).mono (fun _ _ h => h) fun _ _ h => h
  -- The hash.
  have b := rel_wp (rel_r11 (l₀ := ghArgsTo) (l := ghArgsTo.tail) rfl
      (P := fun s₁ s₂ => MidD s₀ 0 0 s₁ ∧ MidD s₀' 0 0 s₂) [.rsp] [.rsp] (by simp)
      (fun _ _ h => mid_rsp pb h.1 h.2) (fun _ _ h => mid_hS hp hp' pb h.1 h.2) ghArgsTo_check)
    (fun _ _ h => h)
    (G₁ := fun st' => GhCall st' (K s₀ + BitVec.ofNat 64 240) (Y s₀) (Src s₀) (BlocksToDec.W5 s₀) (n s₀))
    (G₂ := fun st' => GhCall st' (K s₀' + BitVec.ofNat 64 240) (Y s₀') (Src s₀') (BlocksToDec.W5 s₀') (n s₀'))
    (fun _ h => WP.mono (BlocksToDec.ghArgsTo_ok hp h) fun _ h => h.1)
    (fun _ h => WP.mono (BlocksToDec.ghArgsTo_ok hp' h) fun _ h => h.1)
  have gh := rel_wp (RelCT.seq b (gh_rel g fun s₁ s₂ h => by
      obtain ⟨hr, c₁, c₂⟩ := h
      rw [pb.k, pb.y, pb.src, pub_ew5 pb, pb.en] at c₂
      exact ⟨_, _, _, _, _, c₁, c₂, hr _ (List.mem_singleton_self _)⟩)) (fun _ _ h => h)
    (fun _ h => BlocksToDec.ghStep_ok hp g h) (fun _ h => BlocksToDec.ghStep_ok hp' g h)
  -- The decryption.
  have c := rel_wp (rel_r11 (l₀ := ctrArgsTo) (l := ctrArgsTo.tail) rfl
      (P := fun s₁ s₂ => BlocksToDec.GD s₀ s₁ ∧ BlocksToDec.GD s₀' s₂) [.rsp] [.rsp] (by simp)
      (fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h.1.rsp, h.2.rsp, pb.sp])
      (fun _ _ h => ⟨by rw [h.1.rsp, h.2.rsp, h.1.arg, h.2.arg, pb.sc],
        by rw [h.1.rd, h.1.wr, h.1.rsp]; exact a_in hp (i := 2) (by decide),
        by rw [h.2.rd, h.2.wr, h.2.rsp]; exact a_in hp' (i := 2) (by decide)⟩) ctrArgsTo_check)
    (fun _ _ h => h)
    (G₁ := fun st' => CtrToCall st' (K s₀) (C s₀) (Src s₀) (Dst s₀) (BlocksToDec.W5 s₀) (R s₀) (n s₀))
    (G₂ := fun st' => CtrToCall st' (K s₀') (C s₀') (Src s₀') (Dst s₀') (BlocksToDec.W5 s₀') (R s₀') (n s₀'))
    (fun _ h => WP.mono (BlocksToDec.ctrArgsTo_ok hp h.rsp h.rd h.wr h.kept h.arg) fun _ h => h.1)
    (fun _ h => WP.mono (BlocksToDec.ctrArgsTo_ok hp' h.rsp h.rd h.wr h.kept h.arg) fun _ h => h.1)
  have d := RelCT.seq c (ctrTo_rel v fun s₁ s₂ h => by
    obtain ⟨hr, c₁, c₂⟩ := h
    rw [pb.k, pb.c, pb.src, pb.dst, pub_ew5 pb, pb.eR, pb.en] at c₂
    exact ⟨_, _, _, _, _, _, _, c₁, c₂, hr _ (List.mem_singleton_self _)⟩)
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨⟨-, ⟨M₁, -⟩, ⟨M₂, -⟩⟩, -⟩ := hP
  exact (RelCT.seq gh (d.mono (fun _ _ h => h.2) fun _ _ h => h)) _ _ _ _ _ _ ⟨M₁, M₂⟩ e₁ e₂

end

theorem decryptTo_ct {M : CtxMode} (g : GhashImpl) (v : Proof.Aes.X86_64.Ctr32ToImpl) :
    ConstantTime isa (Proof.AesGcm.decryptBlocksToX86_64M M).pre Proof.AesGcm.blocksToPub
      (decryptTo g.fn ⟨v.callee.name, v.callee.code⟩) := by
  refine ct_of_rel fun s₀ s₀' h h' hq => ?_
  have hp := BT.ofM h
  have hp' := BT.ofM h'
  have pb := Pub.of hq
  have me : ∀ (s s₁ : State), BT M s → EntryPost s s₁ → MidD s 0 0 s₁ := fun s s₁ hp h => by
    obtain ⟨_, _, g₁, k₁, f₁, rd₁, wr₁⟩ := h
    exact BlocksToDec.mid_entry hp (g₁ _ (by decide) (by decide))
      (fun r hr => g₁ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr))
      k₁ f₁ rd₁ wr₁
  unfold decryptTo
  refine RelCT.seq (entry_rel hp hp' pb) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨_, E₁, E₂⟩ e₁ e₂
  exact tailTo_rel hp hp' pb g v _ _ _ _ _ _ ⟨me _ _ hp E₁, me _ _ hp' E₂⟩ e₁ e₂

theorem decrypt_ct {M : CtxMode} (B : BlkFn M) {aligned : Bool} (st : Option (StitchToDecCode M aligned)) :
    ConstantTime isa (Proof.AesGcm.decryptBlocksToX86_64M M).pre Proof.AesGcm.blocksToPub
      (BlocksToDec.decrypt B.dec (st.map (·.dec)) aligned) := by
  refine ct_of_rel fun s₀ s₀' h h' hq => ?_
  have hp := BT.ofM h
  have hp' := BT.ofM h'
  have pb := Pub.of hq
  unfold BlocksToDec.decrypt BlocksTo.encrypt
  refine RelCT.seq (entry_rel hp hp' pb) (RelCT.seq (part_rel hp hp' pb st) ?_)
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, M₁, M₂⟩ e₁ e₂
  exact tail_rel hp hp' pb B _ _ _ _ _ _ ⟨M₁, M₂⟩ e₁ e₂

end VG.Proof.AesGcm.X86_64.BlocksToDec



namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)

/-- An instance of `vg_aes_gcm_decrypt_blocks_to`, with what its callers need. -/
structure BlkToDecFn (M : CtxMode) where
  fn : Fn
  ok : ∀ s, (Proof.AesGcm.decryptBlocksToX86_64M M).pre s →
    ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.AesGcm.decryptBlocksToX86_64M M).post s s'
  ct : ConstantTime isa (Proof.AesGcm.decryptBlocksToX86_64M M).pre Proof.AesGcm.blocksToPub fn.code
  sp : SpSafe fn.code
  xd : fn.code.x86_64Depth ≤ 24
  mx : fn.code.allInstrs (fun i => !loadsMxcsr i) = true
  spAll : fn.code.all (fun i => !X86_64.isa.writesSp i) = true

section
variable {M : CtxMode} {aligned : Bool} (st : Option (StitchToDecCode M aligned)) (B : BlkFn M)

theorem headFrom_mx : (BlocksTo.head (st.map (·.dec)) aligned false).allInstrs (fun i => !loadsMxcsr i) = true := by
  rcases st with _ | ⟨dec, ok, P⟩
  · rfl
  · simp only [Option.map, BlocksTo.head, BlocksTo.stitchPart, Code.allInstrs, P.mxcsr]
    cases aligned <;> rfl

theorem headFrom_spSafe : (BlocksTo.head (st.map (·.dec)) aligned false).all (fun i => !X86_64.isa.writesSp i) = true := by
  rcases st with _ | ⟨dec, ok, P⟩
  · rfl
  · simp only [Option.map, BlocksTo.head, BlocksTo.stitchPart, Code.all, P.spSafe]
    cases aligned <;> rfl

theorem headFrom_xdepth : (BlocksTo.head (st.map (·.dec)) aligned false).x86_64Depth = 0 := by
  rcases st with _ | ⟨dec, ok, P⟩
  · rfl
  · simp only [Option.map, BlocksTo.head, BlocksTo.stitchPart, Code.x86_64Depth, P.xdepth]
    cases aligned <;> rfl

theorem decryptTo_mx : (BlocksToDec.decrypt B.dec (st.map (·.dec)) aligned).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.decMx
  simp only [BlocksToDec.decrypt, BlocksTo.encrypt, BlocksTo.tail, BlocksTo.copyBlocks, Code.allInstrs, headFrom_mx st, e,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem decryptTo_spSafe :
    (BlocksToDec.decrypt B.dec (st.map (·.dec)) aligned).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.decSp
  simp only [BlocksToDec.decrypt, BlocksTo.encrypt, BlocksTo.tail, BlocksTo.copyBlocks, Code.all, headFrom_spSafe st, e,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem decryptTo_xdepth : (BlocksToDec.decrypt B.dec (st.map (·.dec)) aligned).x86_64Depth ≤ 24 := by
  have e := B.decXd
  simp only [BlocksToDec.decrypt, BlocksTo.encrypt, BlocksTo.tail, BlocksTo.copyBlocks, Code.x86_64Depth,
    X86_64.Instr.frameBytes, List.length_cons, List.length_nil, headFrom_xdepth st, Nat.max_le]
  omega_using [e]

theorem decryptToM_correct (s : State) (hs : (Proof.AesGcm.decryptBlocksToX86_64M M).pre s) :
    ∃ t s', Exec isa (BlocksToDec.decrypt B.dec (st.map (·.dec)) aligned) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.blocksToDecPost s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := BlocksToDec.decrypt_wp B aligned (st.map (·.dec))
    (fun p e => by obtain ⟨i, rfl, rfl⟩ := Option.map_eq_some_iff.1 e; exact i.ok) hs
  exact ⟨t, s', he, abiPreserved_of_exec (decryptTo_mx st B) he hg, hp⟩

end

/-- The instance of `vg_aes_gcm_decrypt_blocks_to` named `n`, calling `B`'s
`vg_aes_gcm_decrypt_blocks` and running the out-of-place loop `st`, if any. -/
def BlkToDecFn.ofBlocks {M : CtxMode} (n : String) (B : BlkFn M) {aligned : Bool}
    (st : Option (StitchToDecCode M aligned)) : BlkToDecFn M where
  fn := ⟨n, BlocksToDec.decrypt B.dec (st.map (·.dec)) aligned⟩
  ok := decryptToM_correct st B
  ct := BlocksToDec.decrypt_ct B st
  sp := SpSafe.of_all (decryptTo_spSafe st B)
  xd := decryptTo_xdepth st B
  mx := decryptTo_mx st B
  spAll := decryptTo_spSafe st B

section
variable (g : GhashImpl) (v : Proof.Aes.X86_64.Ctr32ToImpl)

theorem decryptToTo_mx :
    (BlocksToDec.decryptTo g.fn ⟨v.callee.name, v.callee.code⟩).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e₁ := g.mxcsr
  have e₂ := v.mxcsr
  simp only [BlocksToDec.decryptTo, BlocksToDec.tailTo, Code.allInstrs, e₁, e₂, Bool.true_and, Bool.and_true]
  decide +kernel

theorem decryptToTo_spSafe :
    (BlocksToDec.decryptTo g.fn ⟨v.callee.name, v.callee.code⟩).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e₁ := g.spSafe
  have e₂ := v.spSafe
  simp only [BlocksToDec.decryptTo, BlocksToDec.tailTo, Code.all, e₁, e₂, Bool.true_and, Bool.and_true]
  decide +kernel

theorem decryptToTo_xdepth : (BlocksToDec.decryptTo g.fn ⟨v.callee.name, v.callee.code⟩).x86_64Depth ≤ 24 := by
  have e₁ := g.noStack
  have e₂ := v.noStack
  simp only [BlocksToDec.decryptTo, BlocksToDec.tailTo, Code.x86_64Depth, e₁, e₂]
  omega_using []

end

/-- The instance of `vg_aes_gcm_decrypt_blocks_to` named `n` with no
out-of-place loop and no copy, calling `g` (`vg_ghash`) and `v`
(`vg_aes_ctr32_to`). -/
def BlkToDecFn.ofTo {M : CtxMode} (n : String) (g : GhashImpl) (v : Proof.Aes.X86_64.Ctr32ToImpl) :
    BlkToDecFn M where
  fn := ⟨n, BlocksToDec.decryptTo g.fn ⟨v.callee.name, v.callee.code⟩⟩
  ok s hs := by
    obtain ⟨t, s', he, hg, hp⟩ := BlocksToDec.decryptTo_wp g v hs
    exact ⟨t, s', he, abiPreserved_of_exec (decryptToTo_mx g v) he hg, hp⟩
  ct := BlocksToDec.decryptTo_ct g v
  sp := SpSafe.of_all (decryptToTo_spSafe g v)
  xd := decryptToTo_xdepth g v
  mx := decryptToTo_mx g v
  spAll := decryptToTo_spSafe g v

end VG.Proof.AesGcm.X86_64

end

end

/-!
# AES-GCM `open_split` on x86-64: the whole blocks at `src`

Untrusted: everything here is checked by Lean. `Impl.AesGcm.X86_64.OpenSplit.prefix`, `seal_split`'s
`prefix` with a call of `vg_aes_gcm_decrypt_blocks_to` in place of
`vg_aes_gcm_encrypt_blocks_to` and no copy (`prefixD_ok`): from the same
state as `Split.prefix_ok` (`Split.PP`), with `Y` continued over the
ciphertext at `src`, which the call absorbs (`preCallToDec_ok`), rather than
over what it writes (`Mid2D`), and the bytes left at `src` kept as the data
(`restS_ok`, `PPostD`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.OpenSplit

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.AesGcm.X86_64.Split
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (covers_cons' covers_nil' sub_add_ofNat off_bound stackArg_entry)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

/-- After the call (or none, for no whole block): what it did. -/
structure Mid2D (Ctx W SP D S : Addr) (R sl : Nat) (s s₂ : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  frame : Frame (callWr W D (sl / 16) ++ [below SP 56]) s.mem s₂.mem
  blocks : blocksAt s₂.mem D (sl / 16) = ctr32 (ctxCiph s.mem Ctx R) (blockAt s.mem (cbA W)) (blocksAt s.mem S (sl / 16))
  ctr : blockAt s₂.mem (cbA W) = Nat.repeat inc32 (sl / 16) (blockAt s.mem (cbA W))
  y : blockAt s₂.mem (yA W) = ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (yA W)) (blocksAt s.mem S (sl / 16))

/-- What `prefix` leaves. -/
structure PPostD (Ctx W SP D S : Addr) (R sl : Nat) (s s' : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame (callWr W D (sl / 16) ++ [⟨W + BitVec.ofNat 64 200, 16⟩, below SP 56]) s.mem s'.mem
  blocks : blocksAt s'.mem D (sl / 16) = ctr32 (ctxCiph s.mem Ctx R) (blockAt s.mem (cbA W)) (blocksAt s.mem S (sl / 16))
  ctr : blockAt s'.mem (cbA W) = Nat.repeat inc32 (sl / 16) (blockAt s.mem (cbA W))
  y : blockAt s'.mem (yA W) = ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (yA W)) (blocksAt s.mem S (sl / 16))
  dat : s'.mem.readW (W + BitVec.ofNat 64 200) 64 = S + BitVec.ofNat 64 (16 * (sl / 16))
  len : s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (sl % 16)

/-- `Impl.AesGcm.X86_64.OpenSplit.rest`: the bytes after the `16 ⌊sl / 16⌋` at `S` kept as the
data, and their number as its length. -/
theorem restS_ok {Ctx W SP S : Addr} {sl : Nat} (hsl : sl < 2 ^ 64) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hsrc : s.mem.readW (W + BitVec.ofNat 64 224) 64 = S)
    (hslot : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 sl) :
    WP isa (.block Impl.AesGcm.X86_64.OpenSplit.rest) s fun s₄ =>
      s₄.mem.readW (W + BitVec.ofNat 64 200) 64 = S + BitVec.ofNat 64 (16 * (sl / 16)) ∧
      s₄.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (sl % 16) ∧
      Frame [⟨W + BitVec.ofNat 64 200, 16⟩] s.mem s₄.mem ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s₄.gpr r = s.gpr r) ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr := by
  have q₁ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have q₃ := he.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 200 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 208 + 8 ≤ 2560 by decide)
  have e15 := and15 (BitVec.ofNat 64 sl)
  rw [toNat_ofNat_of_lt hsl, imm_eq (by decide)] at e15
  have esub : BitVec.ofNat 64 sl - BitVec.ofNat 64 (sl % 16) = BitVec.ofNat 64 (16 * (sl / 16)) := by
    rw [ofNat_sub (Nat.mod_le _ _) hsl]; congr 1; omega_arith
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2560 → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by have := he.perm; omega_arith) (by omega_arith)
  have hsrc' : (s.mem.writeW (W + BitVec.ofNat 64 208) (BitVec.ofNat 64 (sl % 16))).readW
      (W + BitVec.ofNat 64 224) 64 = S := by
    rw [Mem.readW_writeW_sep (sep 224 208 (by decide) (by decide) (by decide)) (by decide), hsrc]
  have q₃' : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 224) 8 := q₃
  unfold Impl.AesGcm.X86_64.OpenSplit.rest
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, q₃', w₁, w₂, hslot, e15, esub, hsrc'], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [mem_arithFlags, mem_setReg, Mem.readW_writeW_self64, BitVec.add_comm]
  · simp only [mem_arithFlags, mem_setReg]
    rw [Mem.readW_writeW_sep (sep 208 200 (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
  · have c : ∀ d, 200 ≤ d → d + 8 ≤ 216 → (⟨W + BitVec.ofNat 64 200, 16⟩ : Region).Contains
        (W + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => Offset.contains _ h₁ (by omega_arith) (by have := he.perm; omega_arith)
    simp only [mem_arithFlags, mem_setReg]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  all_goals simp [rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

section
variable {M : CtxMode} {Ctx W SP D S : Addr} {R n sl : Nat} {s : State} (h : PP M Ctx W SP D S R n sl s)
include h

/-- The call of `vg_aes_gcm_decrypt_blocks_to` on the `q` whole blocks at
`S`, to `D`, with `D`, `q` and the working space pushed for it. -/
theorem preCallToDec_ok (T : BlkToDecFn M) {q : Nat} (hq : 16 * q ≤ sl) {st : State}
    (hsp : st.gpr .rsp = SP) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) (hm : st.mem = s.mem)
    (h_di : st.gpr .rdi = Ctx) (h_si : st.gpr .rsi = BitVec.ofNat 64 R)
    (h_dx : st.gpr .rdx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)
    (h_cx : st.gpr .rcx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (h_8 : st.gpr .r8 = S)
    (h_9 : st.gpr .r9 = BitVec.ofNat 64 q) (h_10 : st.gpr .r10 = BitVec.ofNat 64 q) (h_11 : st.gpr .r11 = D)
    (h_ax : st.gpr .rax = W + BitVec.ofNat 64 448) :
    WP isa (.frame (.push [.rax, .r10, .r11]) (.call T.fn.name T.fn.code) (.pop .rax 3)) st fun st' =>
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      Frame (callWr W D q ++ [below SP 56]) st.mem st'.mem ∧
      blocksAt st'.mem D q = ctr32 (ctxCiph s.mem Ctx R) (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48))
        (blocksAt s.mem S q) ∧
      blockAt st'.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
        Nat.repeat inc32 q (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)) ∧
      blockAt st'.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) =
        ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16)) (blocksAt s.mem S q) := by
  have L := h.lay
  have sp := h.sp56
  have hn := h.data.ok.lt
  obtain hqs : q * 16 ≤ sl := by omega_arith
  obtain hn8 : 8 * [Reg.rax, .r10, .r11].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.rax, .r10, .r11] (by decide) hn8
  obtain hP : (pushed [.rax, .r10, .r11] st).gpr .rsp = SP - BitVec.ofNat 64 24 := by rw [pushed_rsp, hsp]; rfl
  obtain hpf' : Frame [⟨SP - BitVec.ofNat 64 24, 24⟩] st.mem (pushed [.rax, .r10, .r11] st).mem := by
    rw [hsp] at hpf; exact hpf
  obtain hE : Frame [⟨SP - BitVec.ofNat 64 32, 8⟩] (pushed [.rax, .r10, .r11] st).mem
      (pushed [.rax, .r10, .r11] st).callEntry.mem := by
    have := callEntry_frame (pushed [.rax, .r10, .r11] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  obtain b56 : ∀ {a k : Nat}, a ≤ 56 → k ≤ a → ∃ r ∈ [below SP 56], Region.Sub ⟨SP - BitVec.ofNat 64 a, k⟩ r :=
    fun ha hk => ⟨_, List.mem_singleton_self _, stk56_sub ha hk⟩
  obtain fS : Frame [below SP 56] st.mem (pushed [.rax, .r10, .r11] st).callEntry.mem :=
    (hpf'.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact b56 (by decide) (by decide)).trans
      (hE.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact b56 (by decide) (by decide))
  have kM := h.kM
  obtain ⟨hpre, cr, cw, gU, -, a0, -, -⟩ := callIn h hq hsp hrd hwr hm h_di h_si h_dx h_cx h_8 h_9 h_10 h_11 h_ax
  -- What the push and the return address leave as it was.
  obtain keep : ∀ {p : Addr} {k : Nat}, (⟨p, k⟩ : Region).Disjoint (below SP 56) → k ≤ 2 ^ 64 →
      bytesAt (pushed [.rax, .r10, .r11] st).callEntry.mem p k = bytesAt s.mem p k := fun hd hk => by
    rw [← hm]
    exact bytesAt_frame fS (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hk
  obtain keepB : ∀ {p : Addr}, (⟨p, 16⟩ : Region).Disjoint (below SP 56) →
      blockAt (pushed [.rax, .r10, .r11] st).callEntry.mem p = blockAt s.mem p := fun hd => by
    rw [blockAt, blockAt, keep hd (by decide)]
  obtain cW : Region.Sub (cbR W) ⟨W, 2560⟩ := fun a hc => st_w a (cb_sub a hc)
  obtain yW : Region.Sub (yR W) ⟨W, 2560⟩ := fun a hc => st_w a (y_sub a hc)
  obtain eC := keepB ((h.kw.sub_right cW).symm)
  obtain eY := keepB ((h.kw.sub_right yW).symm)
  obtain eS : blocksAt (pushed [.rax, .r10, .r11] st).callEntry.mem S q = blocksAt s.mem S q := by
    rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq,
      keep ((h.ks.sub_right (Region.sub_prefix (by omega_arith))).symm) (by have := h.sWrap; omega_arith)]
  obtain hRb : 16 * (R + 1) ≤ 256 := by rcases h.rounds.2 with h | h | h <;> subst h <;> decide
  obtain eK : ctxCiph (pushed [.rax, .r10, .r11] st).callEntry.mem Ctx R = ctxCiph s.mem Ctx R := by
    simp only [ctxCiph]
    rw [keep ((kM.sub_right (Region.sub_prefix (Nat.le_trans hRb M.ge))).symm) (Nat.le_trans hRb (by decide))]
  obtain eH : ctxH (pushed [.rax, .r10, .r11] st).callEntry.mem Ctx = ctxH s.mem Ctx := by
    simp only [ctxH]
    exact keepB ((kM.sub_right (Offset.sub_base _ (by have := M.ge; omega_arith))).symm)
  obtain hqn : (BitVec.ofNat 64 q).toNat = q := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.sl_le; omega_arith)
  obtain hRn : (BitVec.ofNat 64 R).toNat = R := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rcases h.rounds.2 with h | h | h <;> subst h <;> decide)
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.call_sp_mx (k := Proof.AesGcm.decryptBlocksToX86_64M M)
    T.ok T.sp (by have := T.xd; omega_arith) hpre cr cw fun s' hrd' hwr' hcs hfr _ ⟨s₂, hm₂, _, hpost⟩ _ => ?_)
  obtain r₃ := hcs _ (by decide : Reg.rsp ∈ calleeSaved)
  simp only [Proof.AesGcm.decryptBlocksToX86_64M, Proof.AesGcm.blocksToDecPost, Proof.AesGcm.arg, a0,
    State.withRegions_mem, gU _ (by decide : Reg.rdi ≠ .rsp), gU _ (by decide : Reg.rsi ≠ .rsp),
    gU _ (by decide : Reg.rdx ≠ .rsp), gU _ (by decide : Reg.rcx ≠ .rsp), gU _ (by decide : Reg.r8 ≠ .rsp),
    gU _ (by decide : Reg.r9 ≠ .rsp), h_di, h_si, h_dx, h_cx, h_8, h_9, h_11, hqn, hRn, hm₂, eK, eH,
    eC, eY, eS] at hpost
  obtain ⟨o₁, o₂, o₃⟩ := hpost
  refine ⟨r₃, hwr', fun m u fm => ?_⟩
  -- The `pop` loses the frame's 24 bytes, in the stack below `SP`, apart from
  -- the outputs.
  obtain fm' : Frame [below SP 56] s'.mem m := by
    rw [hsp] at fm
    exact fm.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact b56 (by decide) (by decide)
  obtain one : ∀ {r : Region}, (below SP 56).Disjoint r → ∀ r' ∈ [below SP 56], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd.symm
  obtain kD : blocksAt m D q = blocksAt s'.mem D q :=
    blocksAt_frame fm' (one (h.kd.sub_right (Region.sub_prefix (by have := h.sl_le; omega_arith))))
      (by have := h.data.ok.wrap; have := h.sl_le; omega_arith)
  obtain kC := blockAt_frame fm' (one (h.kw.sub_right cW))
  obtain kY := blockAt_frame fm' (one (h.kw.sub_right yW))
  dsimp only
  refine ⟨fun r hr => ?_, by rw [popped_rd, hrd', pushed_rd], by rw [popped_wr, hwr', pushed_wr]; rfl,
    ?_, ?_, ?_, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; rw [popped_rsp, r₃, hP, hsp]
      show SP - BitVec.ofNat 64 24 + BitVec.ofNat 64 24 = SP
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ hr' (fun e => by subst e; simp [calleeSaved] at hr), hcs r hr, pushed_gpr _ _ hr']
  · refine Frame.trans ?_ (fm'.sub fun r hr => ⟨below SP 56, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
    obtain bT : Region.Sub (below ((pushed [.rax, .r10, .r11] st).gpr .rsp) (T.fn.code.x86_64Depth + 8)) (below SP 56) := by
      obtain h₁ := below_sub (sp := (pushed [.rax, .r10, .r11] st).gpr .rsp) (a := T.fn.code.x86_64Depth + 8) (b := 32)
        (by have := T.xd; omega_arith) (by decide)
      obtain e : below (SP - BitVec.ofNat 64 24) 32 = ⟨SP - BitVec.ofNat 64 56, 32⟩ := by
        simp only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add]
      rw [hP] at h₁ ⊢
      rw [e] at h₁
      exact fun a h' => stk56_sub (by decide) (by decide) a (h₁ a h')
    refine (hpf'.sub fun r hr => ?_).trans (hfr.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨below SP 56, by simp, stk56_sub (by decide) (by decide)⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨below SP 56, by simp, bT⟩
  · rw [kD]; exact o₁
  · rw [kC]; exact o₂
  · rw [kY]; exact o₃

/-- After the call (or none): `rest`. -/
theorem restD_ok {s₂ : State} (H : Mid2D Ctx W SP D S R sl s s₂) :
    WP isa (.block Impl.AesGcm.X86_64.OpenSplit.rest) s₂ (PPostD Ctx W SP D S R sl s) := by
  have L := h.lay
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  obtain kp : ∀ d, 128 ≤ d → d + 8 ≤ 448 → s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => H.frame.readW (Region.contains_self _ _) (slot_disj h (q := sl / 16) (by omega_arith) h₁ h₂) (by decide)
  refine WP.mono (restS_ok (S := S) (sl := sl) (by omega_arith) H.env (by rw [kp 224 (by decide) (by decide)]; exact h.src)
    (by rw [kp 192 (by decide) (by decide)]; exact h.slen)) fun s₅ ⟨d₅, l₅, f₅, g₅, rd₅, wr₅⟩ => ?_
  obtain cW : ∀ {p : Addr}, (⟨p, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 200, 16⟩ →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 200, 16⟩ : Region)], (⟨p, 16⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  obtain dB : (⟨D, 16 * (sl / 16)⟩ : Region).Disjoint ⟨W, 2560⟩ := h.data.ok.w.sub_left (Region.sub_prefix (by omega_arith))
  obtain eB : blocksAt s₅.mem D (sl / 16) = blocksAt s₂.mem D (sl / 16) :=
    blocksAt_frame f₅ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dB.sub_right (Lay.wSub (by decide))) (by omega_arith)
  obtain eC : blockAt s₅.mem (cbA W) = blockAt s₂.mem (cbA W) :=
    blockAt_frame f₅ (cW (by simp only [cbA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide)))
  obtain eY : blockAt s₅.mem (yA W) = blockAt s₂.mem (yA W) :=
    blockAt_frame f₅ (cW (by simp only [yA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide)))
  refine ⟨H.env.keep g₅ rd₅ wr₅, rd₅.trans H.rd, wr₅.trans H.wr, ?_, by rw [eB, H.blocks], by rw [eC, H.ctr],
    by rw [eY, H.y], d₅, l₅⟩
  refine (H.frame.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp, fun _ h => h⟩

/-- The call of `prefix` for the `sl / 16` whole blocks at `src`, from a
state `s₁` with their number in `rax` and `s`'s memory: what `Mid2D` says. -/
theorem callD_ok (T : BlkToDecFn M) {s₁ : State} (he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁)
    (ax₁ : s₁.gpr .rax = BitVec.ofNat 64 (sl / 16)) (m₁ : s₁.mem = s.mem) (rd₁ : s₁.rd = s.rd)
    (wr₁ : s₁.wr = s.wr) :
    WP isa (.seq (.block SealSplit.preArgs)
      (.frame (.push [.rax, .r10, .r11]) (.call T.fn.name T.fn.code) (.pop .rax 3))) s₁
      (Mid2D Ctx W SP D S R sl s) := by
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  refine WP.seq (WP.mono (pre2_ok (R := R) (D := D) (S := S) he₁ (by rw [m₁]; exact h.rounds) (by rw [m₁]; exact h.dat)
    (by rw [m₁]; exact h.src)) fun s₂ ⟨di₂, si₂, dx₂, cx₂, r8₂, r9₂, r10₂, r11₂, ax₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  obtain he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep g₂ rd₂ wr₂
  exact WP.mono (preCallToDec_ok h T (q := sl / 16) (by omega_arith) he₂.rsp (rd₂.trans rd₁) (wr₂.trans wr₁)
    (m₂.trans m₁) di₂ si₂ dx₂ cx₂ r8₂ (by rw [r9₂, ax₁]) (by rw [r10₂, ax₁]) r11₂ ax₂)
    fun s₃ ⟨cs₃, rd₃, wr₃, fr₃, bl₃, ct₃, y₃⟩ => ⟨he₂.keep (fun r hr => cs₃ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])) rd₃ wr₃,
      rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), by rw [m₂, m₁] at fr₃; exact fr₃, bl₃, ct₃, y₃⟩

/-- `prefix`: the whole blocks at `src` decrypted to `dst` and absorbed by a
call of `vg_aes_gcm_decrypt_blocks_to` (`T`), and the bytes left at `src`
kept as the data. -/
theorem prefixD_ok (T : BlkToDecFn M) :
    WP isa (Impl.AesGcm.X86_64.OpenSplit.prefix T.fn) s (PPostD Ctx W SP D S R sl s) := by
  have L := h.lay
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  have he := h.env
  unfold Impl.AesGcm.X86_64.OpenSplit.prefix
  refine WP.seq (WP.mono (pre1_ok (sl := sl) (by omega_arith) he h.slen) fun s₁ ⟨ax₁, zf₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  obtain he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) rd₁ wr₁
  refine WP.seq (WP.ite (decide (sl / 16 = 0)) (by simp only [eval, zf₁]) (fun h0 => ?_) (fun h0 => ?_))
  · -- No whole block at `src`.
    obtain h0' : sl / 16 = 0 := of_decide_eq_true h0
    refine WP.block_nil (restD_ok h ⟨he₁, rd₁, wr₁, by rw [m₁]; exact Frame.refl _ _, ?_, ?_, ?_⟩)
    · rw [h0']; rfl
    · rw [h0', m₁]; rfl
    · rw [h0', m₁]; rfl
  · exact WP.mono (callD_ok h T he₁ ax₁ m₁ rd₁ wr₁) fun _ H => restD_ok h H

end

end VG.Proof.AesGcm.X86_64.OpenSplit
