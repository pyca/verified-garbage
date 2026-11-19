module

public import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
public import VerifiedGarbage.Impl.AesGcm.PPC64LE.OpenTo
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.Proof.Zeroize.Common
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.Fn
import VerifiedGarbage.Proof.AesGcm.CtxFrame
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Open
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Groups
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Crypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamInit
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Compare
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamVerify
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneShot
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Verified
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Contract
import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneEntry
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealFused
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CryptOk
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.FinTag
import VerifiedGarbage.Proof.Gcm.StreamTo
import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Impl.AesGcm.PPC64LE.OpenTo
meta import VerifiedGarbage.Proof.AesGcm.Rounds
meta import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
meta import VerifiedGarbage.Proof.Zeroize.Common
meta import VerifiedGarbage.Spec.Gcm.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.Fn
meta import VerifiedGarbage.Proof.AesGcm.CtxFrame
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Open
meta import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Groups
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Crypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamInit
meta import VerifiedGarbage.Proof.Gcm.Ctr
meta import VerifiedGarbage.Proof.Gcm.Compose
meta import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Compare
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamVerify
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneShot
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Verified
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Contract
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneEntry
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealFused
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.FinTag
meta import VerifiedGarbage.Proof.Gcm.StreamTo
meta import VerifiedGarbage.Proof.Framework.SigEval

/-! ### `AesGcm.PPC64LE.OpenTo.Fn`, which this module and modules that import it used -/

section

/-! ### `AesGcm.PPC64LE.OpenTo.Split`, which this module and modules that import it used -/

section

/-! ### `AesGcm.PPC64LE.OpenTo.Pass`, which this module and modules that import it used -/

section

/-!
# AES-GCM on PPC64LE: `vg_aes_gcm_open_split`'s data, in one pass

Untrusted: everything here is checked by Lean. `whole` calls
`vg_aes_gcm_decrypt_blocks_to` (`SplitBlocks/Verified.lean`) on the whole
blocks of the data: it decrypts them from the source to the destination and
continues GHASH over them, the ciphertext (`whole_ok`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE.Pass

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE VG.Impl.AesGcm.PPC64LE.OpenTo
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxH ctxCiph ctr32 ghashFrom inc32)

section
variable {V : Reg → BitVec 64} {sp : Addr}

/-- The number of whole blocks of the data. -/
abbrev Q (V : Reg → BitVec 64) : Nat := (V .r23).toNat / 16

/-- What `whole` needs: the data (`r23` bytes at `r27`), only read, and the
destination `D` at `sp + 120`, written, apart from it. -/
structure WholeIn (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (D : Addr) (s : State) : Prop where
  env : Env V sp s
  r28 : V .r28 = BitVec.ofNat 64 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  src : DataOk (V .r30) (V .r31) s (V .r27) (V .r23).toNat
  dst : DataW (V .r29) (V .r30) (V .r31) s D (V .r23).toNat
  sd : (⟨V .r27, (V .r23).toNat⟩ : Region).Disjoint ⟨D, (V .r23).toNat⟩
  hi : InRegions (s.rd ++ s.wr) (sp + BitVec.ofNat 64 120) 8
  hv : s.mem.readW (sp + BitVec.ofNat 64 120) 64 = D

/-- After `whole`, from `s₀`. -/
structure WholeOut (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (D : Addr) (s₀ s : State) : Prop where
  env : Env V sp s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r26 : s.gpr .r26 = D
  out : blocksAt s.mem D (Q V) = ctr32 (ctxCiph s₀.mem (V .r29) R)
    (blockAt s₀.mem (V .r30 + BitVec.ofNat 64 48)) (blocksAt s₀.mem (V .r27) (Q V))
  cb : blockAt s.mem (V .r30 + BitVec.ofNat 64 48) =
    Nat.repeat inc32 (Q V) (blockAt s₀.mem (V .r30 + BitVec.ofNat 64 48))
  hash : blockAt s.mem (V .r30 + BitVec.ofNat 64 16) = ghashFrom (ctxH s₀.mem (V .r29))
    (blockAt s₀.mem (V .r30 + BitVec.ofNat 64 16)) (blocksAt s₀.mem (V .r27) (Q V))
  frame : Frame [⟨V .r30 + BitVec.ofNat 64 16, 48⟩, ⟨D, Q V * 16⟩, ⟨V .r31 + BitVec.ofNat 64 448, 2112⟩]
    s₀.mem s.mem

/-- The registers `wholeArgs` sets. -/
def argRegs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12, .r26]

theorem wholeArgs_ok {R : Nat} {D : Addr} {s : State} (h : WholeIn V sp R D s) :
    WP isa (.block wholeArgs) s fun s' =>
      s'.gpr .r3 = V .r29 ∧ s'.gpr .r4 = BitVec.ofNat 64 R ∧ s'.gpr .r5 = V .r30 + BitVec.ofNat 64 16 ∧
      s'.gpr .r6 = V .r27 ∧ s'.gpr .r7 = BitVec.ofNat 64 (Q V) ∧ s'.gpr .r8 = D ∧
      s'.gpr .r9 = BitVec.ofNat 64 (Q V) ∧ s'.gpr .r10 = V .r31 + BitVec.ofNat 64 448 ∧ s'.gpr .r26 = D ∧
      (∀ r, r ∉ argRegs → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have he := h.env
  obtain h27 := he.fr .r27 (by decide)
  obtain h28 := he.fr .r28 (by decide)
  obtain h29 := he.r29; have h30 := he.r30; have h31 := he.r31
  obtain h23 := he.fr .r23 (by decide)
  obtain hsh : s.gpr .r23 >>> 4 = BitVec.ofNat 64 (Q V) := by
    rw [h23]
    calc
      _ = BitVec.ofNat 64 (V .r23).toNat >>> 4 := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      _ = _ := shr4 (V .r23).isLt
  have hsp := he.sp
  obtain h₀ : WP isa (.block [.addSp .r12 0]) s fun s₀ =>
      s₀.gpr .r12 = s.sp ∧ (∀ r, r ≠ .r12 → s₀.gpr r = s.gpr r) ∧ Keeps s s₀ := by
    crun []
    exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  rw [show wholeArgs = [.addSp .r12 0] ++ ([.load .d .r26 .r12 120] ++ [mov .r3 .r29, mov .r4 .r28,
      .addi .r5 .r30 16, mov .r6 .r27, .lsr .d .r7 .r23 4, mov .r8 .r26, mov .r9 .r7, .addi .r10 .r31 448])
      from rfl]
  refine WP.block_append (WP.mono h₀ fun s₀ ⟨a12, g₀, k₀⟩ => ?_)
  refine WP.block_append (WP.mono (ld_ok (t := .r26) (v := D) (by decide) (by decide) (by decide)
    (by rw [a12, k₀.rd, k₀.wr, hsp]; exact h.hi) (by rw [a12, k₀.mem, hsp]; exact h.hv))
    fun s₁ ⟨h26, g₁, k₁⟩ => ?_)
  obtain e : ∀ r, r ≠ .r12 → r ≠ .r26 → s₁.gpr r = s.gpr r := fun r a b => (g₁ r b).trans (g₀ r a)
  crun [mov, BitVec.or_self, e .r27 (by decide) (by decide), e .r28 (by decide) (by decide),
    e .r29 (by decide) (by decide), e .r30 (by decide) (by decide), e .r31 (by decide) (by decide),
    e .r23 (by decide) (by decide), h27, h28, h29, h30, h31, h.r28, hsh, h26]
  refine ⟨fun r hr => ?_, k₀.trans (k₁.trans ⟨rfl, rfl, rfl, rfl, rfl⟩)⟩
  have hr' := hr
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
  obtain ⟨b3, b4, b5, b6, b7, b8, b9, b10, b12, b26⟩ := hr'
  simp [b3, b4, b5, b6, b7, b8, b9, b10, e r b12 b26]

theorem fitOff (p : Addr) {bound off n : Nat} (hf : p.toNat + bound ≤ 2 ^ 64)
    (hb : bound < 2 ^ 64) (ho : off + n ≤ bound) : (p + BitVec.ofNat 64 off).toNat + n ≤ 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (b := 2 ^ 64) (by omega_using [hb, ho])]
  have := Nat.mod_le (p.toNat + off) (2 ^ 64)
  omega_using [hf, ho]

theorem st48 (p : Addr) : p + BitVec.ofNat 64 16 + 32 = p + BitVec.ofNat 64 48 := by
  rw [BitVec.add_assoc]; rfl

/-- What the call reads and writes. -/
abbrev callRd (V : Reg → BitVec 64) : List Region := [⟨V .r29, 256⟩, ⟨V .r27, Q V * 16⟩]
abbrev callWr (V : Reg → BitVec 64) (D : Addr) : List Region :=
  [⟨V .r30 + BitVec.ofNat 64 16, 48⟩, ⟨D, Q V * 16⟩, ⟨V .r31 + BitVec.ofNat 64 448, 2112⟩]

/-- `wholeArgs`'s registers, from `s`. -/
structure ArgsOut (V : Reg → BitVec 64) (R : Nat) (D : Addr) (s s₁ : State) : Prop where
  r3 : s₁.gpr .r3 = V .r29
  r4 : s₁.gpr .r4 = BitVec.ofNat 64 R
  r5 : s₁.gpr .r5 = V .r30 + BitVec.ofNat 64 16
  r6 : s₁.gpr .r6 = V .r27
  r7 : s₁.gpr .r7 = BitVec.ofNat 64 (Q V)
  r8 : s₁.gpr .r8 = D
  r9 : s₁.gpr .r9 = BitVec.ofNat 64 (Q V)
  r10 : s₁.gpr .r10 = V .r31 + BitVec.ofNat 64 448
  r26 : s₁.gpr .r26 = D
  regs : ∀ r, r ∉ argRegs → s₁.gpr r = s.gpr r
  keeps : Keeps s s₁

theorem argsOut {R : Nat} {D : Addr} {s : State} (h : WholeIn V sp R D s) :
    WP isa (.block wholeArgs) s (ArgsOut V R D s) :=
  WP.mono (wholeArgs_ok h) fun _ ⟨a3, a4, a5, a6, a7, a8, a9, a10, a26, g, k⟩ =>
    ⟨a3, a4, a5, a6, a7, a8, a9, a10, a26, g, k⟩

/-- The call's precondition, and its regions, after `wholeArgs`. -/
theorem whole_call {R : Nat} {D : Addr} {s s₁ : State} (L : Lay (V .r29) (V .r30) (V .r31))
    (h : WholeIn V sp R D s) (a : ArgsOut V R D s s₁) :
    (Proof.Gcm.decryptBlocksToContract PPC64LE.abi).pre (s₁.callEntry.withRegions (callRd V) (callWr V D)) ∧
    Covers (callRd V ++ callWr V D) (s₁.rd ++ s₁.wr) ∧ Covers (callWr V D) s₁.wr := by
  obtain hq : Q V < 2 ^ 64 := by show (V .r23).toNat / 16 < 2 ^ 64; have := (V .r23).isLt; omega_using []
  obtain hle : Q V * 16 ≤ (V .r23).toNat := by show (V .r23).toNat / 16 * 16 ≤ _; exact Nat.div_mul_le_self _ _
  obtain hR : R < 2 ^ 64 := by rcases h.rounds with e | e | e <;> omega_using [e]
  have he := h.env
  have hsrc := h.src
  have hdst := h.dst
  have k₁ := a.keeps
  refine ⟨?_, ?_, ?_⟩
  · sig_eval [Proof.Gcm.decryptBlocksToContract, Proof.Gcm.decryptBlocksToSig, Proof.Gcm.decryptBlocksToPre,
      PPC64LE.abi, PPC64LE.argRegs]
    simp only [a.r3, a.r4, a.r5, a.r6, a.r7, a.r8, a.r9, a.r10, toNat64 hq, toNat64 hR]
    refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, L.cw, fitOff _ L.sw (by decide) (by decide),
      by have := hsrc.fit; omega_using [hle, this], by have := hdst.ok.fit; omega_using [hle, this], fitOff _ L.ww (by decide) (by decide),
      h.rounds, trivial⟩
    · simpa only [BitVec.add_zero, BitVec.ofNat_eq_ofNat] using
        L.ctx_st (a := 0) (n := 256) (d := 16) (k := 48) (by decide) (by decide)
    · exact hdst.ctx.sub_right (Region.sub_prefix hle)
    · simpa only [BitVec.add_zero, BitVec.ofNat_eq_ofNat] using
        L.ctx_w (a := 0) (n := 256) (d := 448) (k := 2112) (by decide) (by decide)
    · exact ((hsrc.st.sub_left (Region.sub_prefix hle)).sub_right (Lay.stSub (d := 16) (n := 48) (by decide))).symm
    · exact ((hdst.ok.st.sub_left (Region.sub_prefix hle)).sub_right (Lay.stSub (d := 16) (n := 48) (by decide))).symm
    · exact L.st_w (a := 16) (n := 48) (d := 448) (k := 2112) (by decide) (.inr ⟨by decide, by decide⟩)
    · exact (h.sd.sub_left (Region.sub_prefix hle)).sub_right (Region.sub_prefix hle)
    · exact (hsrc.w.sub_left (Region.sub_prefix hle)).sub_right (Lay.wSub (d := 448) (n := 2112) (by decide))
    · exact (hdst.ok.w.sub_left (Region.sub_prefix hle)).sub_right (Lay.wSub (d := 448) (n := 2112) (by decide))
  · rw [k₁.rd, k₁.wr]
    exact Covers.cons he.perm.ctx (Covers.cons (covers_prefix hsrc.rd hle)
      (Covers.cons (covers_left (he.perm.stC (d := 16) (n := 48) (by decide)))
        (Covers.cons (covers_left (covers_prefix hdst.wr hle))
          (Covers.cons (covers_left (he.perm.wC (d := 448) (n := 2112) (by decide))) Covers.nil))))
  · rw [k₁.wr]
    exact Covers.cons (he.perm.stC (d := 16) (n := 48) (by decide)) (Covers.cons (covers_prefix hdst.wr hle)
      (Covers.cons (he.perm.wC (d := 448) (n := 2112) (by decide)) Covers.nil))

theorem whole_ok [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] {R : Nat} {D : Addr}
    {s : State} (L : Lay (V .r29) (V .r30) (V .r31)) (h : WholeIn V sp R D s) :
    WP isa whole s (WholeOut V sp R D s) := by
  refine WP.seq (WP.mono (argsOut h) fun s₁ a => ?_)
  obtain hq : Q V < 2 ^ 64 := by show (V .r23).toNat / 16 < 2 ^ 64; have := (V .r23).isLt; omega_using []
  obtain hR : R < 2 ^ 64 := by rcases h.rounds with e | e | e <;> omega_using [e]
  have k₁ := a.keeps
  obtain he₁ : Env V sp s₁ := h.env.keep (fun r hr => a.regs r (by revert r; decide)) k₁.sp k₁.rd k₁.wr
  obtain ⟨hpre, hrd', hwr'⟩ := whole_call L h a
  refine WP.call (k := Proof.Gcm.decryptBlocksToContract PPC64LE.abi) SplitBlocks.decryptTo_correct
    (rd := callRd V) (wr := callWr V D) hpre hrd' hwr' ?_
  intro t hrd hwr hsp hf hcs _ hp
  sig_eval [Proof.Gcm.decryptBlocksToContract, Proof.Gcm.decryptBlocksToSig, Proof.Gcm.decryptBlocksToPost,
    PPC64LE.abi, PPC64LE.argRegs] at hp
  simp only [a.r3, a.r4, a.r5, a.r6, a.r7, a.r8, toNat64 hq, toNat64 hR, st48, k₁.mem] at hp
  rw [k₁.mem] at hf
  exact ⟨he₁.of_saved hcs hsp hrd hwr, hrd.trans k₁.rd, hwr.trans k₁.wr, (hcs _ (by decide)).trans a.r26,
    hp.1, hp.2.1, hp.2.2, hf⟩

/-- The last bytes' arguments, from the destination `D` in `r26`. -/
theorem partArgs_ok {s : State} {D : Addr} (he : Env V sp s) (h26 : s.gpr .r26 = D) :
    WP isa (.block partArgs) s fun s' =>
      s'.gpr .r24 = V .r27 + BitVec.ofNat 64 (16 * Q V) ∧ s'.gpr .r25 = BitVec.ofNat 64 ((V .r23).toNat % 16) ∧
      s'.gpr .r26 = D + BitVec.ofNat 64 (16 * Q V) ∧
      (∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r24 → r ≠ .r25 → r ≠ .r26 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain h23 := he.fr .r23 (by decide)
  obtain h27 := he.fr .r27 (by decide)
  obtain hand := and15 (V .r23)
  obtain hsub : V .r23 - BitVec.ofNat 64 ((V .r23).toNat % 16) = BitVec.ofNat 64 (16 * Q V) := by
    calc
      _ = BitVec.ofNat 64 (V .r23).toNat - BitVec.ofNat 64 ((V .r23).toNat % 16) := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      _ = _ := by rw [ofNat_sub64 (Nat.mod_le _ _) (V .r23).isLt]; congr 1; show _ = 16 * ((V .r23).toNat / 16); omega_using []
  simp only [partArgs]
  crun [h23, h27, hand, hsub, h26]
  exact ⟨fun r a b c d e => by simp [a, b, c, d, e], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- `partArgs`'s registers, from `s₁`. -/
structure PartOut (V : Reg → BitVec 64) (D : Addr) (s₁ s₂ : State) : Prop where
  r24 : s₂.gpr .r24 = V .r27 + BitVec.ofNat 64 (16 * Q V)
  r25 : s₂.gpr .r25 = BitVec.ofNat 64 ((V .r23).toNat % 16)
  r26 : s₂.gpr .r26 = D + BitVec.ofNat 64 (16 * Q V)
  regs : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r24 → r ≠ .r25 → r ≠ .r26 → s₂.gpr r = s₁.gpr r
  keeps : Keeps s₁ s₂

/-- After `whole` and `partArgs`, from `s`: the last bytes, for `cryptTailWith`. -/
theorem tail_in {R : Nat} {D : Addr} {s s₁ s₂ : State} (L : Lay (V .r29) (V .r30) (V .r31))
    (h : WholeIn V sp R D s) (hw : WholeOut V sp R D s s₁) (p : PartOut V D s₁ s₂) :
    TailIn true V sp R (blockAt s.mem (V .r30 + BitVec.ofNat 64 48)) (16 * Q V)
      (V .r27 + BitVec.ofNat 64 (16 * Q V)) (D + BitVec.ofNat 64 (16 * Q V)) ((V .r23).toNat - 16 * Q V)
      (ctxCiph s.mem (V .r29) R)
      (blockAt s.mem (V .r30 + BitVec.ofNat 64 48) = blockAt s.mem (V .r30 + BitVec.ofNat 64 48)) s₂ := by
  have hn := h.src.lt
  obtain h16 : 16 * Q V ≤ (V .r23).toNat := by show 16 * ((V .r23).toNat / 16) ≤ _; omega_using []
  obtain hk : (V .r23).toNat % 16 = (V .r23).toNat - 16 * Q V := by show _ = _ - 16 * ((V .r23).toNat / 16); omega_using []
  have hR := h.rounds
  have hdst := h.dst
  have k₂ := p.keeps
  obtain dCw : ∀ r ∈ [(⟨V .r30 + BitVec.ofNat 64 16, 48⟩ : Region), ⟨D, Q V * 16⟩,
      ⟨V .r31 + BitVec.ofNat 64 448, 2112⟩], (⟨V .r29, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.cs.sub_right (Lay.stSub (by decide))
    · exact hdst.ctx.sub_right (Region.sub_prefix (by omega_using [h16]))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
  obtain he₂ : Env V sp s₂ := hw.env.keep (fun r hr => p.regs r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide)) k₂.sp k₂.rd k₂.wr
  obtain rd₂ : s₂.rd = s.rd := k₂.rd.trans hw.rd
  obtain wr₂ : s₂.wr = s.wr := k₂.wr.trans hw.wr
  refine ⟨he₂, p.r24, by rw [p.r25, hk], fun _ => p.r26, h.r28, hR, .inr (by omega_using []),
    (h.src.of_eq rd₂ wr₂).drop h16, (hdst.of_eq rd₂ wr₂).drop h16, (fun h => nomatch h),
    .inr ((h.sd.sub_left (Offset.sub_base _ (by omega_using [h16]))).sub_right (Offset.sub_base _ (by omega_using [h16]))),
    ?_, fun hcb => ?_⟩
  · rw [k₂.mem]; exact ciph_frame hw.frame dCw hR
  · have := (Proof.Gcm.ctr_wholeTo (Proof.Gcm.ctr_zero s.mem (V .r30 + BitVec.ofNat 64 48)
      (V .r30 + BitVec.ofNat 64 64) (ctxCiph s.mem (V .r29) R) hcb) (by decide) hw.out hw.cb).2
    rw [Nat.zero_add] at this
    rw [k₂.mem]; exact this

/-- What the data's pass and its tag write. -/
abbrev passFrame (V : Reg → BitVec 64) (D : Addr) : List Region :=
  [⟨D, (V .r23).toNat⟩, ⟨V .r30, 80⟩, ⟨V .r31 + BitVec.ofNat 64 96, 32⟩, ⟨V .r31 + BitVec.ofNat 64 448, 2112⟩]

/-- After the data's pass and its tag, from `s₀`: the destination holds the
data decrypted, and `W + 112` the tag of the data, the ciphertext. -/
structure PassOut (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (a : List Byte) (D : Addr) (s₀ s : State) : Prop where
  env : Env V sp s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  dst : bytesAt s.mem D (V .r23).toNat = Spec.Gcm.gctr (ctxCiph s₀.mem (V .r29) R)
    (blockAt s₀.mem (V .r30 + BitVec.ofNat 64 48)) (bytesAt s₀.mem (V .r27) (V .r23).toNat)
  tag : bytesAt s.mem (V .r31 + BitVec.ofNat 64 112) 16 =
    Spec.Gcm.toBytes (ghashFrom (ctxH s₀.mem (V .r29)) (Spec.Gcm.ghash (ctxH s₀.mem (V .r29))
      (Spec.Gcm.blocks (Proof.Gcm.padded a (bytesAt s₀.mem (V .r27) (V .r23).toNat))))
      [Spec.Gcm.ofBytes (Proof.Gcm.lensBlock a.length (bytesAt s₀.mem (V .r27) (V .r23).toNat).length)] ^^^
      ctxCiph s₀.mem (V .r29) R (blockAt s₀.mem (V .r30)))
  frame : Frame (passFrame V D) s₀.mem s.mem

theorem pass_ok [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] {R : Nat} {D : Addr}
    {a : List Byte} {s : State} (L : Lay (V .r29) (V .r30) (V .r31)) (h : WholeIn V sp R D s)
    (ha : (V .r22).toNat = a.length) (hpos : 0 < (V .r23).toNat)
    (hab : Proof.Gcm.Absorbed s.mem (V .r30 + BitVec.ofNat 64 16) (V .r30 + BitVec.ofNat 64 32)
      (ctxH s.mem (V .r29)) (a ++ Spec.Gcm.zeros (Spec.Gcm.padLen a.length))) :
    WP isa (.seq passData (finTag 112)) s (PassOut V sp R a D s) := by
  have hn := h.src.lt
  obtain h16 : 16 * Q V ≤ (V .r23).toNat := by show 16 * ((V .r23).toNat / 16) ≤ _; omega_using []
  obtain hk : (V .r23).toNat % 16 = (V .r23).toNat - 16 * Q V := by show _ = _ - 16 * ((V .r23).toNat / 16); omega_using []
  obtain hkl : (V .r23).toNat - 16 * Q V < 16 := by show _ - 16 * ((V .r23).toNat / 16) < 16; omega_using []
  have hR := h.rounds
  have hdst := h.dst
  have hsrc := h.src
  let cph := ctxCiph s.mem (V .r29) R
  let icb := blockAt s.mem (V .r30 + BitVec.ofNat 64 48)
  -- the whole blocks
  refine WP.seq (WP.seq (WP.mono (whole_ok L h) fun s₁ hw => ?_))
  obtain dCw : ∀ r ∈ [(⟨V .r30 + BitVec.ofNat 64 16, 48⟩ : Region), ⟨D, Q V * 16⟩,
      ⟨V .r31 + BitVec.ofNat 64 448, 2112⟩], (⟨V .r29, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.cs.sub_right (Lay.stSub (by decide))
    · exact hdst.ctx.sub_right (Region.sub_prefix (by omega_using [h16]))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
  -- the last bytes' arguments
  refine WP.seq (WP.seq (WP.mono (partArgs_ok hw.env hw.r26) fun s₂ ⟨a24, a25, a26, g₂, k₂⟩ => ?_))
  obtain he₂ : Env V sp s₂ := hw.env.keep (fun r hr => g₂ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide)) k₂.sp k₂.rd k₂.wr
  obtain rd₂ : s₂.rd = s.rd := k₂.rd.trans hw.rd
  obtain wr₂ : s₂.wr = s.wr := k₂.wr.trans hw.wr
  obtain ti : TailIn true V sp R icb (16 * Q V) (V .r27 + BitVec.ofNat 64 (16 * Q V))
      (D + BitVec.ofNat 64 (16 * Q V)) ((V .r23).toNat - 16 * Q V) cph
      (blockAt s.mem (V .r30 + BitVec.ofNat 64 48) = icb) s₂ := by
    refine ⟨he₂, a24, by rw [a25, hk], fun _ => a26, h.r28, hR, .inr (by omega_using []),
      (hsrc.of_eq rd₂ wr₂).drop h16, (hdst.of_eq rd₂ wr₂).drop h16, (fun h => nomatch h),
      .inr ((h.sd.sub_left (Offset.sub_base _ (by omega_using [h16]))).sub_right (Offset.sub_base _ (by omega_using [h16]))),
      ?_, fun hcb => ?_⟩
    · rw [k₂.mem]; exact ciph_frame hw.frame dCw hR
    · have := (Proof.Gcm.ctr_wholeTo (Proof.Gcm.ctr_zero s.mem (V .r30 + BitVec.ofNat 64 48)
        (V .r30 + BitVec.ofNat 64 64) cph hcb) (by decide) hw.out hw.cb).2
      rw [Nat.zero_add] at this
      rw [k₂.mem]; exact this
  refine WP.mono (WP.with_rdwr (cryptTailWith_ok L ti hkl)) fun s₃ ⟨o, rd₃', wr₃', _⟩ => ?_
  obtain rd₃ : s₃.rd = s.rd := rd₃'.trans rd₂
  obtain wr₃ : s₃.wr = s.wr := wr₃'.trans wr₂
  -- the last bytes, buffered for GHASH
  refine WP.seq (WP.mono (SealFused.tailSetup_ok o.env) fun s₄ ⟨b24, b25, b26, g₄, k₄⟩ => ?_)
  obtain he₄ : Env V sp s₄ := o.env.keep (fun r hr => g₄ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide)) k₄.sp k₄.rd k₄.wr
  obtain rd₄ : s₄.rd = s.rd := k₄.rd.trans rd₃
  obtain wr₄ : s₄.wr = s.wr := k₄.wr.trans wr₃
  obtain hxpad : (a ++ Spec.Gcm.zeros (Spec.Gcm.padLen a.length)).length % 16 = 0 := by
    rw [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  let x := (a ++ Spec.Gcm.zeros (Spec.Gcm.padLen a.length)) ++ bytesAt s.mem (V .r27) (16 * Q V)
  obtain hx0 : x.length % 16 = 0 := by
    simp only [x, List.length_append, length_bytesAt] at hxpad ⊢; omega_using [hxpad]
  obtain hab₁ : Proof.Gcm.Absorbed s₁.mem (V .r30 + BitVec.ofNat 64 16) (V .r30 + BitVec.ofNat 64 32)
      (ctxH s.mem (V .r29)) x :=
    Proof.Gcm.absorb_whole hab hxpad (by rw [length_bytesAt]; omega_using []) (by rw [hw.hash, Proof.Gcm.blocksAt_eq])
  have hds := ti.dst
  obtain hab₄ : Proof.Gcm.Absorbed s₄.mem (V .r30 + BitVec.ofNat 64 16) (V .r30 + BitVec.ofNat 64 32)
      (ctxH s.mem (V .r29)) x := by
    refine hab₁.congr ?_ ?_
    · rw [k₄.mem, blockAt_frame o.frame (stp_crFrame L hds (d := 16) (k := 16) (by decide)), k₂.mem]
    · rw [hx0]; simp only [bytesAt, List.range_zero, List.map_nil]
  obtain hH₁ : blockAt s₁.mem (V .r29 + BitVec.ofNat 64 240) = ctxH s.mem (V .r29) := ctxH_keep hw.frame dCw
  obtain hH₄ : blockAt s₄.mem (V .r29 + BitVec.ofNat 64 240) = ctxH s.mem (V .r29) := by
    rw [k₄.mem, blockAt_frame o.frame (fun r hr => (ctx_crFrame L hds r hr).sub_left
      (Lay.ctxSub (d := 240) (n := 16) (by decide))), k₂.mem, hH₁]
  obtain hsufd : DataOk (V .r30) (V .r31) s₄ (V .r27 + BitVec.ofNat 64 (16 * Q V)) ((V .r23).toNat % 16) := by
    rw [hk]; exact (hsrc.of_eq rd₄ wr₄).drop h16
  obtain ai : AbsIn V sp 16 (ctxH s.mem (V .r29)) x (V .r27 + BitVec.ofNat 64 (16 * Q V))
      ((V .r23).toNat % 16) s₄ := by
    refine ⟨he₄, ?_, b25, by rw [hx0]; exact b26, hsufd, hH₄⟩
    rw [b24]
  refine WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) ai)) fun s₅ ⟨ab, rd₅', wr₅', _⟩ => ?_
  obtain rd₅ : s₅.rd = s.rd := rd₅'.trans rd₄
  obtain wr₅ : s₅.wr = s.wr := wr₅'.trans wr₄
  -- the source's last bytes, as they were
  obtain hsuf : bytesAt s₄.mem (V .r27 + BitVec.ofNat 64 (16 * Q V)) ((V .r23).toNat % 16) =
      bytesAt s.mem (V .r27 + BitVec.ofNat 64 (16 * Q V)) ((V .r23).toNat % 16) := by
    obtain hs : Region.Sub (⟨V .r27 + BitVec.ofNat 64 (16 * Q V), (V .r23).toNat % 16⟩ : Region)
        ⟨V .r27, (V .r23).toNat⟩ := Offset.sub_base _ (by omega_using [h16])
    rw [k₄.mem, bytesAt_frame o.frame ?_ (by omega_using []), k₂.mem, bytesAt_frame hw.frame ?_ (by omega_using [])]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hsrc.st.sub_left hs).sub_right (Lay.stSub (by decide))
      · exact (h.sd.sub_left hs).sub_right (Region.sub_prefix (by omega_using [h16]))
      · exact (hsrc.w.sub_left hs).sub_right (Lay.wSub (by decide))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [← hk]; exact (h.sd.sub_left hs).sub_right (Offset.sub_base _ (by omega_using [h16]))
      · exact (hsrc.st.sub_left hs).sub_right (Lay.stSub (by decide))
      · exact (hsrc.w.sub_left hs).sub_right (Lay.wSub (by decide))
  let ct := bytesAt s.mem (V .r27) (V .r23).toNat
  obtain hct : ct = bytesAt s.mem (V .r27) (16 * Q V) ++
      bytesAt s.mem (V .r27 + BitVec.ofNat 64 (16 * Q V)) ((V .r23).toNat % 16) := by
    rw [← bytesAt_add, show 16 * Q V + (V .r23).toNat % 16 = (V .r23).toNat by omega_using [h16, hk]]
  obtain hne : ct ≠ [] := by
    intro hz; have hh := congrArg List.length hz; rw [length_bytesAt, List.length_nil] at hh; omega_arith
  obtain habv := ab.abs hab₄
  obtain hgi : x ++ bytesAt s₄.mem (V .r27 + BitVec.ofNat 64 (16 * Q V)) ((V .r23).toNat % 16) =
      Spec.Gcm.ghashInput a ct := by
    rw [Proof.Gcm.ghashInput_of_ne hne, hct, hsuf]
    simp only [x, List.append_assoc]
  rw [hgi] at habv
  obtain hH₅ : blockAt s₅.mem (V .r29 + BitVec.ofNat 64 240) = ctxH s.mem (V .r29) := by
    rw [blockAt_frame ab.frame (ctx_absFrame L (.inr rfl))]; exact hH₄
  -- the tag
  refine WP.mono (WP.with_rdwr (finTag_ok L (o := 112) (.inr rfl) (a := a) (ct := ct) ab.env h.r28 hR hH₅
    (by rw [ha]) (length_bytesAt _ _ _).symm)) fun s₆ ⟨fg, rd₆', wr₆', _⟩ => ?_
  obtain hle : Q V * 16 ≤ (V .r23).toNat := by omega_using [h16]
  -- the key schedule and `J₀`, as they were
  obtain hc₅ : ciphOf s₅.mem (V .r29) R = cph := by
    refine (ciph_frame (abs_taFrame ab.frame) (ctx_taFrame L) hR).trans ?_
    rw [k₄.mem]
    refine (ciph_frame o.frame (ctx_crFrame L hds) hR).trans ?_
    rw [k₂.mem]
    exact ciph_frame hw.frame dCw hR
  obtain hj₅ : blockAt s₅.mem (V .r30) = blockAt s.mem (V .r30) := by
    rw [blockAt_frame (abs_taFrame ab.frame) (by
      simpa only [BitVec.add_zero] using stp_taFrame L (d := 0) (k := 16) (.inl (by decide))), k₄.mem,
      blockAt_frame o.frame (by simpa only [BitVec.add_zero] using stp_crFrame L hds (d := 0) (k := 16) (by decide)),
      k₂.mem]
    refine blockAt_frame hw.frame fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa only [BitVec.add_zero, BitVec.ofNat_eq_ofNat] using Lay.st_st (st := V .r30) (a := 0) (n := 16)
        (d := 16) (k := 48) (.inl (by decide)) (by decide) (by decide)
    · exact ((hdst.ok.st.sub_left (Region.sub_prefix hle)).sub_right (Region.sub_prefix (by decide))).symm
    · simpa only [BitVec.add_zero, BitVec.ofNat_eq_ofNat] using L.st_w (a := 0) (n := 16) (d := 448) (k := 2112)
        (by decide) (.inr ⟨by decide, by decide⟩)
  obtain hf := fg.out habv
  rw [hc₅, hj₅, ha] at hf
  -- the destination
  obtain hcw := (Proof.Gcm.ctr_wholeTo (Proof.Gcm.ctr_zero s.mem (V .r30 + BitVec.ofNat 64 48)
    (V .r30 + BitVec.ofNat 64 64) cph (icb := icb) rfl) (by decide) hw.out hw.cb).1
  obtain hdone : bytesAt s₃.mem D (16 * Q V) = bytesAt s₁.mem D (16 * Q V) := by
    rw [bytesAt_frame o.frame (fun r hr => ?_) (by omega_using [h16]), k₂.mem]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact split_disj h16 hn
    · exact (hdst.ok.st.sub_left (Region.sub_prefix h16)).sub_right (Lay.stSub (by decide))
    · exact (hdst.ok.w.sub_left (Region.sub_prefix h16)).sub_right (Lay.wSub (by decide))
  obtain hs₂ : bytesAt s₂.mem (V .r27 + BitVec.ofNat 64 (16 * Q V)) ((V .r23).toNat - 16 * Q V) =
      bytesAt s.mem (V .r27 + BitVec.ofNat 64 (16 * Q V)) ((V .r23).toNat - 16 * Q V) := by
    obtain hs : Region.Sub (⟨V .r27 + BitVec.ofNat 64 (16 * Q V), (V .r23).toNat - 16 * Q V⟩ : Region)
        ⟨V .r27, (V .r23).toNat⟩ := Offset.sub_base _ (by omega_using [h16])
    rw [k₂.mem, bytesAt_frame hw.frame ?_ (by omega_using [])]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hsrc.st.sub_left hs).sub_right (Lay.stSub (by decide))
    · exact (h.sd.sub_left hs).sub_right (Region.sub_prefix (by omega_using [h16]))
    · exact (hsrc.w.sub_left hs).sub_right (Lay.wSub (by decide))
  obtain key := done_appendTo (P := 0) (hdone.trans hcw) (by rw [Nat.zero_add, o.out rfl, hs₂])
  rw [show 16 * Q V + ((V .r23).toNat - 16 * Q V) = (V .r23).toNat by omega_using [h16]] at key
  obtain hd₆ : bytesAt s₆.mem D (V .r23).toNat = bytesAt s₃.mem D (V .r23).toNat := by
    obtain dT : ∀ r ∈ tagFrame (V .r30) (V .r31) 112, (⟨D, (V .r23).toNat⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hdst.ok.st.sub_right (Region.sub_prefix (by decide))
      · exact hdst.ok.w.sub_right (Lay.wSub (by decide))
      · exact hdst.ok.w.sub_right (Lay.wSub (by decide))
      · exact hdst.ok.w.sub_right (Lay.wSub (by decide))
    rw [bytesAt_frame fg.frame dT (by omega_using []),
      bytesAt_frame ab.frame (data_absFrame (.inr rfl) hdst.ok) (by omega_using []), k₄.mem]
  -- what was written
  let T : List Region := passFrame V D
  obtain F₁ : Frame T s.mem s₁.mem := hw.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨V .r30, 80⟩, by simp [T], Lay.stSub (by decide)⟩
    · exact ⟨⟨D, (V .r23).toNat⟩, by simp [T], Region.sub_prefix hle⟩
    · exact ⟨⟨V .r31 + BitVec.ofNat 64 448, 2112⟩, by simp [T], fun _ h => h⟩
  obtain F₃ : Frame T s₂.mem s₃.mem := o.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨D, (V .r23).toNat⟩, by simp [T], Offset.sub_base _ (by omega_using [h16])⟩
    · exact ⟨⟨V .r30, 80⟩, by simp [T], Lay.stSub (by decide)⟩
    · exact ⟨⟨V .r31 + BitVec.ofNat 64 448, 2112⟩, by simp [T], Offset.sub _ (by decide) (by decide)⟩
  obtain F₅ : Frame T s₄.mem s₅.mem := ab.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨V .r30, 80⟩, by simp [T], Lay.stSub (by decide)⟩
    · exact ⟨⟨V .r30, 80⟩, by simp [T], Lay.stSub (by decide)⟩
    · exact ⟨⟨V .r31 + BitVec.ofNat 64 448, 2112⟩, by simp [T], Offset.sub _ (by decide) (by decide)⟩
  obtain F₆ : Frame T s₅.mem s₆.mem := fg.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨V .r30, 80⟩, by simp [T], Region.sub_prefix (by decide)⟩
    · exact ⟨⟨V .r31 + BitVec.ofNat 64 96, 32⟩, by simp [T], Region.sub_prefix (by decide)⟩
    · exact ⟨⟨V .r31 + BitVec.ofNat 64 96, 32⟩, by simp [T], Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨V .r31 + BitVec.ofNat 64 448, 2112⟩, by simp [T], Offset.sub _ (by decide) (by decide)⟩
  rw [k₂.mem] at F₃
  rw [k₄.mem] at F₅
  refine ⟨fg.env, rd₆'.trans rd₅, wr₆'.trans wr₅, ?_, hf, F₁.trans (F₃.trans (F₅.trans F₆))⟩
  rw [hd₆, key, Proof.Gcm.gctr_eq]

end

end VG.Proof.AesGcm.PPC64LE.Pass

end

end

/-!
# AES-GCM on PPC64LE: `vg_aes_gcm_open_split`

Untrusted: everything here is checked by Lean. `vg_aes_gcm_open_split` is
`open`'s body with a pass over the data in place of `oneCrypt` and the
data's tag: its arguments are `open`'s, the data being the source, which it
only reads, with the destination after them on the stack (`splitPre`). Its
proof follows `open`'s, `openWith_wp`, from `HeadPre`, with the pass
(`pass_good`, from `Pass.pass_ok`) after the received tag is copied: the
destination holds the decryption of the source whatever the tags, and the
result says whether they are equal; its callers zero the destination when
they are not (`splitPPC64LE`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE VG.Impl.AesGcm.PPC64LE.OpenTo
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph fullTag zeros padLen j0 inc32 gctr decryptWith openResult)

/-- What `vg_aes_gcm_open_split` needs: `(ctx = r3, rounds = r4, nonce = r5,
nonce_len = r6, aad = r7, aad_len = r8, src = r9, len = r10, tag = [sp + 96],
tag_len = [sp + 104], scratch = [sp + 112], dst = [sp + 120])`: what `open`
needs, but the data is only read, with a destination of `len` bytes, apart
from the key context, the source and the working space. -/
def splitPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .r3, 256⟩
  let nonce : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
  let aad : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
  let src : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let scr : Region := ⟨stackArg s 2, 2560⟩
  let dst : Region := ⟨stackArg s 3, (s.gpr .r10).toNat⟩
  s.rd = [ctx, nonce, aad, src, tag, args s 4] ∧ s.wr = [dst, scr] ∧
    ctx.Disjoint scr ∧ nonce.Disjoint scr ∧ aad.Disjoint scr ∧ src.Disjoint scr ∧ tag.Disjoint scr ∧
    scr.Disjoint (args s 4) ∧ ctx.Disjoint dst ∧ src.Disjoint dst ∧ dst.Disjoint scr ∧
    (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧ (stackArg s 2).toNat + 2560 ≤ 2 ^ 64 ∧
    (stackArg s 3).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧ s.sp.toNat + 128 ≤ 2 ^ 64 ∧ rounds (s.gpr .r4)

/-- `vg_aes_gcm_open_split`: the result in the low 32 bits of `r3`, and the
plaintext at `dst` if the tag is right. It may leak whether it succeeds. -/
def splitPPC64LE : Contract isa where
  pre := splitPre
  post s s' :=
    match openRes s with
    | some pt => (s'.gpr .r3).setWidth 32 = 1 ∧ bytesAt s'.mem (stackArg s 3) (s.gpr .r10).toNat = pt
    | none => (s'.gpr .r3).setWidth 32 = 0
  pub s₁ s₂ := onePub 4 s₁ s₂ ∧ (rounds (s₁.gpr .r4) → (openRes s₁).isSome = (openRes s₂).isSome)

theorem HeadPre.of_split {s : State} (h : splitPre s) : HeadPre s := by
  obtain ⟨hrd, hwr, dcW, dnW, daW, ddW, dtW, dWA, _, _, _, fc, fn, fa, fd, ft, fW, _, _, hR⟩ := h
  obtain r : ∀ x, x ∈ s.rd → Covers [x] (s.rd ++ s.wr) := fun x hx => covers_mem (List.mem_append_left _ hx)
  refine ⟨r _ (by rw [hrd]; simp), r _ (by rw [hrd]; simp), r _ (by rw [hrd]; simp), r _ (by rw [hrd]; simp),
    r _ (by rw [hrd]; simp), covers_prefix (r (args s 4) (by rw [hrd]; simp)) (by decide),
    by rw [hwr]; exact covers_mem (by simp), dcW, dnW, daW, ddW, dtW,
    dWA.sub_right (Region.sub_prefix (by decide)), fc, fn, fa, fd, ft, fW, hR⟩

/-- What the end of `vg_aes_gcm_open_split` promises, given the result `r3`. -/
def SplitPost (s₀ s : State) : Prop :=
  match openRes s₀ with
  | some pt => s.gpr .r3 = 1 ∧ bytesAt s.mem (stackArg s₀ 3) (s₀.gpr .r10).toNat = pt
  | none => s.gpr .r3 = 0

/-- What the end of `vg_aes_gcm_open_split` leaves for `restore`. -/
abbrev SplitOut := OutWith SplitPost

/-- The destination's address, at `sp + 120`, as on entry: it is apart from `W`. -/
theorem dst_at {s₀ s : State} (h : splitPre s₀) (hf : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s.mem) :
    s.mem.readW (s₀.sp + BitVec.ofNat 64 120) 64 = stackArg s₀ 3 := by
  obtain ⟨_, _, _, _, _, _, _, dWA, _⟩ := h
  obtain hc : (args s₀ 4).Contains (s₀.sp + BitVec.ofNat 64 120) 8 := by
    have := Offset.contains_base (stackArgAddr s₀ 0) (d := 24) (n := 8) (k := 8 * 4) (by decide) (by decide)
    rwa [stackArgAddr_0, add_ofNat_assoc] at this
  rw [Frame.readW hf hc (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dWA.symm) (by decide)]
  rfl

theorem split_some {s₀ : State} : ∀ s, openRes s₀ = some (openPt s₀) → s.gpr .r3 = 1 →
    bytesAt s.mem (stackArg s₀ 3) (s₀.gpr .r10).toNat = openPt s₀ → SplitPost s₀ s := by
  intro s hr h1 hd; unfold SplitPost; rw [hr]; exact ⟨h1, hd⟩

theorem split_none {s₀ : State} : ∀ s, openRes s₀ = none → s.gpr .r3 = 0 →
    Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s.mem → SplitPost s₀ s := by
  intro s hr h0 _; unfold SplitPost; rw [hr]; exact h0

/-- `vg_aes_gcm_open_split`, once the tag length is allowed, from `s₄` (after
the entry): the additional data hashed, the received tag copied to `W`, the
data decrypted to the destination in one pass with its tag computed, and the
tags compared. -/
theorem pass_good [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] {s₀ s₄ : State}
    (h : splitPre s₀) (h4 : SO1 (stackArg s₀ 2) (stackArg s₀ 0) s₀ s₄) (h19 : s₄.gpr .r19 = stackArg s₀ 1)
    (hok : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = true) :
    WP isa (.seq oneAad (.seq recv (.seq (.ite (.zero .d .r23) (oneTag 112) (.seq passData (finTag 112)))
      (cmp 112)))) s₄ (SplitOut s₀) := by
  obtain hp := HeadPre.of_split h
  have hh := h
  obtain ⟨hrd, hwr, _, _, _, _, _, _, dcD, dsD, dDW, _, _, _, _, _, _, fD, _, _⟩ := hh
  obtain dcW := hp.dcW; have dnW := hp.dnW; have daW := hp.daW; have ddW := hp.ddW; have dtW := hp.dtW
  obtain fn := hp.fn; have fa := hp.fa; have fd := hp.fd; have hR := hp.hR
  obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
  obtain L₀ := oneLay hp.fc hp.fW dcW
  obtain he₄ := one_env h4 hp.ctx hp.w
  obtain L := L₀.v h4.r29 h4.r30 h4.r31
  have hk₄ := h4.en.keeps
  obtain toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  obtain dcF : ∀ r ∈ [(⟨stackArg s₀ 2, 2560⟩ : Region)], (⟨s₀.gpr .r3, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact dcW
  obtain F₄ : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s₄.mem := h4.en.frame.sub inW_saved
  -- `oneAad`
  obtain hN : DataOk (s₄.gpr .r30) (s₄.gpr .r31) s₄ (s₀.gpr .r5) (s₀.gpr .r6).toNat := by
    rw [h4.r30, h4.r31]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact hp.nonce,
      (s₀.gpr .r6).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW⟩
  obtain hAd : DataOk (s₄.gpr .r30) (s₄.gpr .r31) s₄ (s₄.gpr .r21) (s₄.gpr .r22).toNat := by
    rw [h4.r30, h4.r31, h4.r21, h4.r22]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact hp.aad,
      (s₀.gpr .r8).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW⟩
  refine WP.seq (WP.mono (WP.with_rdwr (oneAad_ok L he₄ rfl h4.r24 (by rw [h4.r25]; exact toN)
    (by rw [h4.r18]; exact toN) hN hAd)) fun s₅ ⟨oa, rd₅, wr₅, _⟩ => ?_)
  have f₅ := oa.frame
  rw [h4.r30, h4.r31] at f₅
  obtain F₅ : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s₅.mem := F₄.trans (f₅.sub inW_j0)
  -- `recv`
  obtain h19' : s₄.gpr .r19 = BitVec.ofNat 64 (stackArg s₀ 1).toNat := by rw [h19]; exact toN
  obtain hTr : Covers [⟨s₄.gpr .r20, (stackArg s₀ 1).toNat⟩] (s₅.rd ++ s₅.wr) := by
    rw [rd₅, wr₅, hk₄.rd, hk₄.wr, h4.r20]
    exact hp.tag
  obtain hTd : (⟨s₄.gpr .r20, (stackArg s₀ 1).toNat⟩ : Region).Disjoint ⟨s₄.gpr .r31 + BitVec.ofNat 64 256, 16⟩ := by
    rw [h4.r20, h4.r31]; exact dtW.sub_right (Lay.wSub (by decide))
  refine WP.seq (WP.mono (recv_ok oa.env h19' t1 t16 hTr hTd) fun s₆ ⟨hb₆, hf₆, g₆, k₆⟩ => ?_)
  obtain he₆ := oa.env.keep (fun r hr => g₆ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) k₆.sp k₆.rd k₆.wr
  rw [h4.r31] at hf₆ hb₆
  obtain F₆ : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s₆.mem := F₅.trans (hf₆.sub (inW_at (by decide)))
  -- what the data and the tags are
  let iv := bytesAt s₀.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat
  let a := bytesAt s₀.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat
  let ct := bytesAt s₀.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat
  let tg := bytesAt s₀.mem (stackArg s₀ 0) (stackArg s₀ 1).toNat
  let ciph := ctxCiph s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat
  let H := ctxH s₀.mem (s₀.gpr .r3)
  let Dst := stackArg s₀ 3
  let W := stackArg s₀ 2
  obtain hW256 : ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)], (⟨s₄.gpr .r29, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    rw [h4.r29]; exact dcW.sub_right (Lay.wSub (by decide))
  obtain hH₄ : blockAt s₄.mem (s₄.gpr .r29 + BitVec.ofNat 64 240) = H := by
    rw [h4.r29]; exact ctxH_keep F₄ dcF
  obtain hH₆ : blockAt s₆.mem (s₄.gpr .r29 + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame hf₆ (fun r hr => (hW256 r hr).sub_left (Lay.ctxSub (by decide))), oa.hH, hH₄]
  obtain iv₄ : bytesAt s₄.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat = iv :=
    bytes_W F₄ dnW (by have := (s₀.gpr .r6).isLt; omega_arith)
  obtain a₄ : bytesAt s₄.mem (s₄.gpr .r21) (s₄.gpr .r22).toNat = a := by
    rw [h4.r21, h4.r22]; exact bytes_W F₄ daW (by have := (s₀.gpr .r8).isLt; omega_arith)
  obtain ct₆ : bytesAt s₆.mem (s₄.gpr .r27) (s₄.gpr .r23).toNat = ct := by
    rw [h4.r27, h4.r23]; exact bytes_W F₆ ddW (by have := (s₀.gpr .r10).isLt; omega_arith)
  obtain hc₆ : ciphOf s₆.mem (s₄.gpr .r29) (s₀.gpr .r4).toNat = ciph := by rw [h4.r29]; exact ciph_keep F₆ dcF hR
  obtain st₆ : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)],
      (⟨s₄.gpr .r30 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hdk r hr; simp only [List.mem_singleton] at hr; subst hr
    rw [h4.r30]; exact L₀.st_w hdk (.inr ⟨by decide, by decide⟩)
  obtain hj₆ : blockAt s₆.mem (s₄.gpr .r30) = j0 H iv := by
    rw [blockAt_frame hf₆ (by simpa using st₆ (d := 0) (k := 16) (by decide)), oa.j, hH₄, iv₄]
  obtain hcb₆ : blockAt s₆.mem (s₄.gpr .r30 + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
    rw [blockAt_frame hf₆ (st₆ (by decide)), oa.cb, hH₄, iv₄]
  obtain hab₆ : Proof.Gcm.Absorbed s₆.mem (s₄.gpr .r30 + BitVec.ofNat 64 16) (s₄.gpr .r30 + BitVec.ofNat 64 32) H
      (a ++ zeros (padLen a.length)) := by
    have hx := oa.abs
    rw [hH₄, a₄] at hx
    refine hx.congr (blockAt_frame hf₆ (st₆ (by decide))) (bytesAt_frame hf₆ (st₆ ?_) (by omega_using []))
    have := Nat.mod_lt (a ++ zeros (padLen a.length)).length (by decide : 0 < 16)
    omega_using []
  obtain hr₆ : bytesAt s₆.mem (W + BitVec.ofNat 64 256) 16 = tg ++ zeros (16 - (stackArg s₀ 1).toNat) := by
    rw [hb₆, h4.r20]; congr 1; exact bytes_W F₅ dtW (by omega_arith)
  obtain sv₆ : SavedAt s₆.mem W s₀ :=
    ((h4.en.saved.frame f₅ (saved_j0Frame L₀)).frame hf₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide))))
  obtain hl₂₂ : (s₄.gpr .r22).toNat = a.length := by rw [h4.r22, length_bytesAt]
  obtain h28 : s₄.gpr .r28 = BitVec.ofNat 64 (s₀.gpr .r4).toNat := by rw [h4.r28]; exact toN
  -- the data and its tag, in one pass
  obtain mid : WP isa (.ite (.zero .d .r23) (oneTag 112) (.seq passData (finTag 112))) s₆ fun s₇ =>
      Env s₄.gpr s₀.sp s₇ ∧ s₇.rd = s₆.rd ∧ s₇.wr = s₆.wr ∧
      bytesAt s₇.mem (W + BitVec.ofNat 64 112) 16 = fullTag ciph H iv a ct ∧
      bytesAt s₇.mem Dst (s₀.gpr .r10).toNat = openPt s₀ ∧
      bytesAt s₇.mem (W + BitVec.ofNat 64 256) 16 = tg ++ zeros (16 - (stackArg s₀ 1).toNat) ∧
      SavedAt s₇.mem W s₀ := by
    obtain rd₆ : s₆.rd = s₀.rd := by rw [k₆.rd, rd₅, hk₄.rd]
    obtain wr₆ : s₆.wr = s₀.wr := by rw [k₆.wr, wr₅, hk₄.wr]
    obtain hd₆ : DataOk (s₄.gpr .r30) (s₄.gpr .r31) s₆ (s₄.gpr .r27) (s₄.gpr .r23).toNat := by
      rw [h4.r30, h4.r31, h4.r27, h4.r23]
      exact ⟨by rw [rd₆, wr₆]; exact hp.data, (s₀.gpr .r10).isLt, fd,
        ddW.sub_right (Lay.wSub (by decide)), ddW⟩
    obtain h23 : s₆.gpr .r23 = BitVec.ofNat 64 (s₀.gpr .r10).toNat := by
      rw [he₆.fr .r23 (by decide), h4.r23]; exact toN
    refine WP.ite _ (eval_zero h23 (s₀.gpr .r10).isLt) (fun ht => ?_) (fun hf => ?_)
    · -- no data
      obtain hz : (s₀.gpr .r10).toNat = 0 := by simpa using ht
      refine WP.mono (WP.with_rdwr (oneTag_ok L (o := 112) (.inr rfl) he₆ h28 hR hH₆ hl₂₂ hab₆ hd₆))
        fun s₇ ⟨ot, rd₇, wr₇, _⟩ => ?_
      have f₇ := ot.frame
      rw [h4.r30, h4.r31] at f₇
      refine ⟨ot.env, rd₇, wr₇, ?_, ?_, ?_, sv₆.frame f₇ (saved_otFrame L₀ (.inr rfl))⟩
      · have ho := ot.out
        rw [h4.r31, hc₆, hj₆, ct₆, ← Proof.Gcm.fullTag_eq] at ho
        exact ho
      · simp only [hz, bytesAt, List.range_zero, List.map_nil, openPt]
        rw [Proof.Gcm.gctr_eq]; simp [Proof.Gcm.xorKs_nil]
      · rw [bytesAt_frame f₇ (fun r hr => ?_) (by decide)]
        · exact hr₆
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (L₀.st_w (a := 0) (n := 48) (d := 256) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm.sub_right
            (by simpa using (Region.sub_prefix (by decide) : Region.Sub (⟨W + BitVec.ofNat 64 16, 48⟩ : Region) _))
        · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · -- the data, in one pass
      obtain hz : (s₀.gpr .r10).toNat ≠ 0 := by simpa using hf
      obtain wi : Pass.WholeIn s₄.gpr s₀.sp (s₀.gpr .r4).toNat Dst s₆ := by
        obtain hw : Covers [⟨Dst, (s₀.gpr .r10).toNat⟩] s₆.wr := by
          rw [wr₆, hwr]; exact covers_mem (by simp [Dst])
        refine ⟨he₆, h28, hR, hd₆, ?_, ?_, ?_, dst_at h F₆⟩
        · rw [h4.r29, h4.r30, h4.r31, h4.r23]
          exact ⟨⟨covers_left hw, (s₀.gpr .r10).isLt, fD, dDW.sub_right (Lay.wSub (by decide)), dDW⟩, hw, dcD⟩
        · rw [h4.r27, h4.r23]; exact dsD
        · rw [rd₆, wr₆]
          obtain hA : Covers [args s₀ 4] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
          have := in_off hA (d := 24) (n := 8) (by decide) (by decide)
          rwa [stackArgAddr_0, add_ofNat_assoc] at this
      obtain hab₆' : Proof.Gcm.Absorbed s₆.mem (s₄.gpr .r30 + BitVec.ofNat 64 16) (s₄.gpr .r30 + BitVec.ofNat 64 32)
          (ctxH s₆.mem (s₄.gpr .r29)) (a ++ zeros (padLen a.length)) := by
        rw [ctxH_eq, hH₆]; exact hab₆
      refine WP.mono (Pass.pass_ok L wi hl₂₂ (by rw [h4.r23]; omega_using [hz]) hab₆') fun s₇ po => ?_
      have hc₆' : ctxCiph s₆.mem (s₄.gpr .r29) (s₀.gpr .r4).toNat = ciph := hc₆
      obtain hH' : ctxH s₆.mem (s₄.gpr .r29) = H := by rw [ctxH_eq]; exact hH₆
      obtain pf : ∀ r ∈ Pass.passFrame s₄.gpr Dst, (⟨W + BitVec.ofNat 64 256, 16⟩ : Region).Disjoint r ∧
          (savedR W).Disjoint r := by
        intro r hr
        simp only [Pass.passFrame, h4.r30, h4.r31, h4.r23, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨(dDW.sub_right (Lay.wSub (by decide))).symm, (dDW.sub_right (Lay.wSub (by decide))).symm⟩
        · have := (L₀.st_w (a := 0) (n := 80) (d := 256) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
          exact ⟨by simpa only [BitVec.add_zero] using this, by simpa using L₀.saved_st (d := 0) (k := 80) (by decide)⟩
        · exact ⟨Lay.w_w (.inr (by decide)) (by decide) (by decide), saved_w (by decide) (.inl (by decide))⟩
        · exact ⟨Lay.w_w (.inl (by decide)) (by decide) (by decide), saved_w (by decide) (.inr (by decide))⟩
      refine ⟨po.env, po.rd, po.wr, ?_, ?_, ?_, sv₆.frame po.frame (fun r hr => (pf r hr).2)⟩
      · have ho := po.tag
        rw [h4.r31, hH', hc₆', hj₆, ct₆, ← Proof.Gcm.fullTag_eq] at ho
        exact ho
      · have ho := po.dst
        rw [hc₆', hcb₆, ct₆, h4.r23] at ho
        exact ho
      · rw [bytesAt_frame po.frame (fun r hr => (pf r hr).1) (by decide)]; exact hr₆
  refine WP.seq (WP.mono mid fun s₇ ⟨he₇, rd₇, wr₇, tag₇, dst₇, rcv₇, sv₇⟩ => ?_)
  -- `cmp 112`
  refine WP.mono (cmp_ok he₇ (o := 112) (.inr rfl) h19' t1 t16) fun s₈ ⟨h3₈, hf₈, g₈, k₈⟩ => ?_
  rw [h4.r31] at hf₈ h3₈
  obtain he₈ := he₇.keep (fun r hr => g₈ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) k₈.sp k₈.rd k₈.wr
  let X := (fullTag ciph H iv a ct).take (stackArg s₀ 1).toNat = tg
  obtain hX : (bytesAt s₇.mem (stackArg s₀ 2 + BitVec.ofNat 64 112) (stackArg s₀ 1).toNat ++
      zeros (16 - (stackArg s₀ 1).toNat) = bytesAt s₇.mem (stackArg s₀ 2 + BitVec.ofNat 64 256) 16) ↔ X := by
    rw [bytesAt_take _ _ t16, tag₇, rcv₇, List.append_cancel_right_eq]
  obtain r3₈ : s₈.gpr .r3 = if X then 1 else 0 := by
    rw [h3₈]; exact ite_congr (propext hX) (fun _ => rfl) (fun _ => rfl)
  obtain dst₈ : bytesAt s₈.mem Dst (s₀.gpr .r10).toNat = openPt s₀ := by
    rw [bytesAt_frame hf₈ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dDW.sub_right (Lay.wSub (by decide))) (by have := (s₀.gpr .r10).isLt; omega_using [])]
    exact dst₇
  refine ⟨(he₈.fr .r31 (by decide)).trans h4.r31, he₈.sp, fun r hr => ?_,
    k₈.rd.trans (rd₇.trans (k₆.rd.trans (rd₅.trans hk₄.rd))),
    k₈.wr.trans (wr₇.trans (k₆.wr.trans (wr₅.trans hk₄.wr))),
    sv₇.frame hf₈ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide))), ?_⟩
  · exact (he₈.fr r (by revert hr; revert r; decide)).trans (h4.en.low r hr)
  · unfold SplitPost
    rw [openRes_eq hok]
    by_cases hx : openTagOk s₀
    · rw [ite_eq_left hx]
      exact ⟨r3₈.trans (ite_eq_left hx), dst₈⟩
    · rw [ite_eq_right hx]
      exact r3₈.trans (ite_eq_right hx)

/-- The contract's postcondition, from `SplitPost`, through `restore`. -/
theorem splitPost_out {s₀ s s' : State} (op : SplitPost s₀ s) (hm : s'.mem = s.mem) (h3 : s'.gpr .r3 = s.gpr .r3) :
    splitPPC64LE.post s₀ s' := by
  unfold SplitPost at op
  unfold splitPPC64LE
  dsimp only
  rw [hm, h3]
  split <;> rename_i heq <;> rw [heq] at op
  · exact ⟨by rw [op.1]; rfl, op.2⟩
  · rw [op]; rfl

theorem split_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] {s₀ : State}
    (h : splitPPC64LE.pre s₀) :
    WP isa openSplit s₀ fun s' => abiPreserved s₀ s' ∧ splitPPC64LE.post s₀ s' := by
  have h' : splitPre s₀ := h
  obtain hp := HeadPre.of_split h'
  have hW := hp.w
  unfold openSplit
  refine WP.seq (WP.mono (openEntry_wp hp) fun s₂ ⟨h2, h19⟩ => ?_)
  -- the tag length
  obtain h19' : s₂.gpr .r19 = BitVec.ofNat 64 (stackArg s₀ 1).toNat := by rw [h19]; simp
  refine WP.seq (WP.mono (tagLenOk_ok h19' (stackArg s₀ 1).isLt) fun s₃ ⟨h25, g₃, k₃⟩ => ?_)
  obtain F₂ : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s₂.mem := h2.en.frame.sub inW_saved
  obtain mid : WP isa (.ite (.zero .d .r25) (.block [.li .r3 0]) openPass) s₃ (SplitOut s₀) := by
    refine WP.ite _ (eval_zero h25 (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
    · have hbad : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = false := by
        cases e : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat
        · rfl
        · simp [e] at ht
      obtain h₀ : WP isa (.block [.li .r3 0]) s₃ fun s' => s'.gpr .r3 = 0 ∧
          (∀ r, r ≠ .r3 → s'.gpr r = s₃.gpr r) ∧ Keeps s₃ s' := by
        crun []
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      refine WP.mono h₀ fun s' ⟨z3, g, k⟩ => ⟨?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
      · rw [g _ (by decide), g₃ _ (by decide) (by decide)]; exact h2.r31
      · rw [k.sp, k₃.sp]; exact h2.en.keeps.sp
      · rw [g r (by revert hr; revert r; decide), g₃ r (by revert hr; revert r; decide)
          (by revert hr; revert r; decide)]
        exact h2.en.low r hr
      · rw [k.rd, k₃.rd]; exact h2.en.keeps.rd
      · rw [k.wr, k₃.wr]; exact h2.en.keeps.wr
      · rw [k.mem, k₃.mem]; exact h2.en.saved
      · exact split_none s' (by simp only [openRes, openResult, hbad]; rfl) z3 (by rw [k.mem, k₃.mem]; exact F₂)
    · have hok : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = true := by
        cases e : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat
        · simp [e] at hf
        · rfl
      unfold openPass
      refine WP.seq (WP.of_runBlock ⟨_, rfl, ?_⟩)
      let s₄ := s₃.write .r25 (s₃.gpr .r18 ||| s₃.gpr .r18)
      obtain g₄ : ∀ r, r ≠ .r0 → r ≠ .r19 → s₄.gpr r = s₂.gpr r := fun r h0 h19 => by
        by_cases e : r = .r25
        · subst e
          have : s₄.gpr .r25 = s₃.gpr .r18 := by simp [s₄, State.write]
          rw [this, g₃ _ (by decide) (by decide), h2.r18, h2.r25]
        · have : s₄.gpr r = s₃.gpr r := by simp [s₄, State.write, e]
          rw [this, g₃ r h0 e]
      obtain h4 : SO1 (stackArg s₀ 2) (stackArg s₀ 0) s₀ s₄ := h2.keep g₄ ⟨k₃.mem, k₃.rd, k₃.wr, k₃.sp, k₃.lr⟩
      obtain e19 : s₄.gpr .r19 = s₃.gpr .r19 := by simp [s₄, State.write]
      exact pass_good h' h4 (by rw [e19, g₃ _ (by decide) (by decide)]; exact h19) hok
  refine WP.seq (WP.mono mid fun s₅ oo => ?_)
  refine WP.mono (restore_ok oo.r31 (by rw [oo.rd, oo.wr]; exact Covers.right hW) oo.saved oo.sp oo.low)
    fun s' ⟨ga, hm, h3, _⟩ => ⟨ga, splitPost_out oo.post hm h3⟩

end VG.Proof.AesGcm.PPC64LE

end

end

/-!
# AES-GCM decryption out of place, in one pass, PPC64LE: the function

Untrusted: everything here is checked by Lean. The contract the proof of
`vg_aes_gcm_open_to` is written against (`toK`), which the shared one implies
(`OpenTo/Verified.lean`), and its proof (`openTo_wp`). It calls
`vg_aes_gcm_open_split` by its contract (`splitPPC64LE`, `SplitOk`).

With `Pf` the base of the 2720 bytes of stack below the stack pointer
(`sp = Pf + 2720`), the function allocates its frame of 2720 bytes there
(`WP.alloc`), keeps our return address in it, and lays out the call's four
stack arguments, the working space being the rest of the frame
(`entered_wp`). It calls `vg_aes_gcm_open_split` (`called_wp`), which
writes only `dst` and the working space, and zeroes `dst` if it returned 0
(`after_wp`, `wipe_wp`); then it reloads our return address (`ret_wp`).
Every write is to `dst` or to the stack below `sp`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.PPC64LE.OpenTo

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE.OpenTo VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH openResult)
open VG.Proof.Gather.PPC64LE (eval_zero eval_nonzero ofNat_sub_one)
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd LrUpd wp_std wp_ld wp_mflr wp_mtlr wp_stb wp_addi wp_subi wp_li)

/-! ## The arguments and the contract -/

section
variable (s : State)

/-- The arguments `(ctx = r3, rounds = r4, nonce = r5, nonce_len = r6,
aad = r7, aad_len = r8, src = r9, len = r10, dst, dst_len, tag, tag_len)`,
the last four in memory. -/
abbrev C : Addr := s.gpr .r3
abbrev Rn : Nat := (s.gpr .r4).toNat
abbrev Nn : Addr := s.gpr .r5
abbrev NL : Nat := (s.gpr .r6).toNat
abbrev Ad : Addr := s.gpr .r7
abbrev AL : Nat := (s.gpr .r8).toNat
abbrev Src : Addr := s.gpr .r9
abbrev L : Nat := (s.gpr .r10).toNat
abbrev Dst : Addr := stackArg s 0
abbrev Tg : Addr := stackArg s 2
abbrev TL : Nat := (stackArg s 3).toNat

/-- The regions: the key context, the nonce, the additional data, the
ciphertext, the output, the tag, the stack arguments and the stack below
the stack pointer. -/
abbrev kR : Region := ⟨C s, 256⟩
abbrev nR : Region := ⟨Nn s, NL s⟩
abbrev aR : Region := ⟨Ad s, AL s⟩
abbrev sR : Region := ⟨Src s, L s⟩
abbrev dR : Region := ⟨Dst s, L s⟩
abbrev tR : Region := ⟨Tg s, TL s⟩
abbrev argR : Region := ⟨stackArgAddr s 0, 32⟩
abbrev stkR : Region := ⟨s.sp - BitVec.ofNat 64 2720, 2720⟩

/-- `vg_aes_gcm_open`'s result on the ciphertext at `src`. -/
abbrev res : Option (List Byte) :=
  openResult (ctxCiph s.mem (C s) (Rn s)) (ctxH s.mem (C s)) (TL s) (bytesAt s.mem (Nn s) (NL s))
    (bytesAt s.mem (Src s) (L s)) (bytesAt s.mem (Ad s) (AL s)) (bytesAt s.mem (Tg s) (TL s))

end

/-- What the proof of `vg_aes_gcm_open_to` needs: the layout of its shared
contract, with 2720 bytes of stack, `dst_len` its `len`. -/
structure ToPre (s : State) : Prop where
  w₁ : 2720 ≤ s.sp.toNat
  w₂ : s.sp.toNat + 32 + 96 ≤ 2 ^ 64
  rd : s.rd = [kR s, nR s, aR s, sR s, tR s, argR s]
  wr : s.wr = [dR s]
  kd : (kR s).Disjoint (dR s)
  nd : (nR s).Disjoint (dR s)
  ad : (aR s).Disjoint (dR s)
  sd : (sR s).Disjoint (dR s)
  dt : (dR s).Disjoint (tR s)
  da : (dR s).Disjoint (argR s)
  bk : (stkR s).Disjoint (kR s)
  bn : (stkR s).Disjoint (nR s)
  ba : (stkR s).Disjoint (aR s)
  bs : (stkR s).Disjoint (sR s)
  bd : (stkR s).Disjoint (dR s)
  bt : (stkR s).Disjoint (tR s)
  barg : (stkR s).Disjoint (argR s)
  ok : (C s).toNat + 256 ≤ 2 ^ 64
  on : (Nn s).toNat + NL s ≤ 2 ^ 64
  oa : (Ad s).toNat + AL s ≤ 2 ^ 64
  os : (Src s).toNat + L s ≤ 2 ^ 64
  od : (Dst s).toNat + L s ≤ 2 ^ 64
  ot : (Tg s).toNat + TL s ≤ 2 ^ 64
  hR : Rn s = 10 ∨ Rn s = 12 ∨ Rn s = 14
  dl : (stackArg s 1).toNat = L s

/-- `openToRoundsPost`, for the rounds of `ToPre`, with the result in `r3`. -/
def toPost (s s' : State) : Prop :=
  match res s with
  | some pt => (s'.gpr .r3).setWidth 32 = 1 ∧ bytesAt s'.mem (Dst s) (L s) = pt
  | none => (s'.gpr .r3).setWidth 32 = 0 ∧ bytesAt s'.mem (Dst s) (L s) = List.replicate (L s) 0

/-- What `vg_aes_gcm_open_to` may leak: whether it succeeds. -/
def toLeak (s : State) : List Nat :=
  if ¬(Rn s = 10 ∨ Rn s = 12 ∨ Rn s = 14) then [] else [if (res s).isSome = true then 1 else 0]

/-- What two runs agree on: the stack pointer, the arguments and the leak. -/
def toPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ toLeak s₁ = toLeak s₂ ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ ∀ i < 4, stackArg s₁ i = stackArg s₂ i

/-- `vg_aes_gcm_open_to`. -/
def toK : Contract isa where
  pre := ToPre
  post := toPost
  pub := toPub

/-! ## The function called -/

/-- The correctness of `vg_aes_gcm_open_split`, by its contract. -/
abbrev SplitOk : Prop :=
  ∀ s, splitPPC64LE.pre s → ∃ t s', Exec isa openSplit s t s' ∧ abiPreserved s s' ∧ splitPPC64LE.post s s'

/-- `vg_aes_gcm_open_split` allocates no stack. -/
theorem split_sdepth : sdepth openSplit = 0 := by
  decide +kernel

/-! ## The layout -/

section
variable (s : State)

/-- Our frame, the 2720 bytes of stack below the stack pointer: the stack
pointer in it. -/
abbrev Pf : Addr := s.sp - BitVec.ofNat 64 2720

/-- The doubleword at offset `a` of the frame. -/
abbrev fa (a : Nat) : Addr := Pf s + BitVec.ofNat 64 a

/-- Our stack argument `i`. -/
abbrev sa (i : Nat) : Addr := Pf s + BitVec.ofNat 64 (2816 + 8 * i)

/-- The frame past its header, which the frame makes writable, the whole
frame, and the working space. -/
abbrev FR : Region := ⟨Pf s + BitVec.ofNat 64 32, 2688⟩
abbrev FA : Region := ⟨Pf s, 2720⟩
abbrev scR : Region := ⟨fa s 160, 2560⟩

/-- The memory after the entry: the back chain at `Pf`, our return address
at `Pf + 152`, and `tag`, `tag_len`, the working space's address and `dst`
at `Pf + 96` … `Pf + 120`, for the call. -/
abbrev eMem : Mem :=
  (((((s.mem.write (Pf s) 8 s.sp).writeW (fa s 152) s.lr).writeW (fa s 96) (Tg s)).writeW (fa s 104)
    (stackArg s 3)).writeW (fa s 112) (fa s 160)).writeW (fa s 120) (Dst s)

/-- The regions the call of `vg_aes_gcm_open_split` reads and writes: its
stack arguments are at `Pf + 96`. -/
abbrev rdC : List Region := [kR s, nR s, aR s, sR s, tR s, ⟨fa s 96, 32⟩]
abbrev wrC : List Region := [dR s, scR s]

end

/-- What `ToPre` gives. -/
structure Lay (s : State) : Prop where
  pre : ToPre s
  hB : s.sp = Pf s + BitVec.ofNat 64 2720
  hBn : (Pf s).toNat + 2848 ≤ 2 ^ 64
  hargR : argR s = ⟨Pf s + BitVec.ofNat 64 2816, 32⟩

theorem lay {s : State} (hs : ToPre s) : Lay s := by
  have w₁ := hs.w₁
  have w₂ := hs.w₂
  obtain hB : s.sp = Pf s + BitVec.ofNat 64 2720 := (BitVec.sub_add_cancel s.sp _).symm
  obtain hBn : (Pf s).toNat + 2848 ≤ 2 ^ 64 := by
    obtain e := congrArg BitVec.toNat hB
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] at e
    have := (Pf s).isLt
    omega_arith
  refine ⟨hs, hB, hBn, ?_⟩
  show (⟨s.sp + BitVec.ofNat 64 (32 + 8 * (8 + 0)), 32⟩ : Region) = ⟨Pf s + BitVec.ofNat 64 2816, 32⟩
  rw [hB, Offset.add_ofNat_add_ofNat]

/-- Bytes of the frame, in the stack below the stack pointer. -/
theorem fr_sub (s : State) {a n : Nat} (ha : a + n ≤ 2720) :
    (⟨Pf s + BitVec.ofNat 64 a, n⟩ : Region).Sub (FA s) :=
  Offset.sub_base _ ha

theorem fr_in (s : State) {a : Nat} (h₁ : 32 ≤ a) (h₂ : a + 8 ≤ 2720) (wr : List Region) :
    InRegions (FR s :: wr) (Pf s + BitVec.ofNat 64 a) 8 :=
  ⟨_, List.mem_cons_self .., by
    show (⟨Pf s + BitVec.ofNat 64 32, 2688⟩ : Region).Contains (Pf s + BitVec.ofNat 64 a) 8
    rw [show a = 32 + (a - 32) by omega_arith, ← Offset.add_ofNat_add_ofNat]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- A doubleword of the frame, after a write to another. -/
theorem rd_sep (s : State) (m : Mem) (v : BitVec 64) {a b : Nat} (h : a + 8 ≤ b ∨ b + 8 ≤ a) (ha : a + 8 ≤ 2720)
    (hb : b + 8 ≤ 2720) :
    (m.writeW (Pf s + BitVec.ofNat 64 b) v).readW (Pf s + BitVec.ofNat 64 a) 64 =
      m.readW (Pf s + BitVec.ofNat 64 a) 64 :=
  Mem.readW_writeW_sep (Offset.sep (Pf s) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)

theorem fa_in (s : State) {a : Nat} (ha : a + 8 ≤ 2720) : (FA s).Contains (Pf s + BitVec.ofNat 64 a) (64 / 8) :=
  Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem frame_eMem (s : State) : Frame [FA s] s.mem (eMem s) := by
  obtain m := List.mem_singleton_self (FA s)
  exact (((((Frame.refl _ _).write m _ (Region.contains_self' (by decide))).writeW m _
    (fa_in s (by decide))).writeW m _ (fa_in s (by decide))).writeW m _ (fa_in s (by decide))).writeW m _
    (fa_in s (by decide)) |>.writeW m _ (fa_in s (by decide))

/-- The words of the frame after the entry. -/
structure Slots (s : State) (m : Mem) : Prop where
  ra : m.readW (fa s 152) 64 = s.lr
  tg : m.readW (fa s 96) 64 = Tg s
  tl : m.readW (fa s 104) 64 = stackArg s 3
  sc : m.readW (fa s 112) 64 = fa s 160
  dst : m.readW (fa s 120) 64 = Dst s

theorem slots_eMem (s : State) : Slots s (eMem s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := omega_arith) only [eMem, fa, rd_sep, Mem.readW_writeW_self64]

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem argIn : argR s ∈ s.rd := by rw [h.pre.rd]; simp

/-- Our stack argument `i`, from its address in our frame's terms. -/
theorem sa_eq {i : Nat} : stackArg s i = s.mem.readW (sa s i) 64 := by
  show s.mem.readW (s.sp + BitVec.ofNat 64 (32 + 8 * (8 + i))) 64 = _
  show _ = s.mem.readW (Pf s + BitVec.ofNat 64 (2816 + 8 * i)) 64
  rw [h.hB, Offset.add_ofNat_add_ofNat, show 2720 + (32 + 8 * (8 + i)) = 2816 + 8 * i by omega_arith]

theorem sa_in {i : Nat} (hi : i < 4) (u : State) (hrd : u.rd = s.rd) :
    InRegions (u.rd ++ u.wr) (sa s i) 8 :=
  ⟨_, List.mem_append_left _ (by rw [hrd]; exact h.argIn), by
    rw [h.hargR]
    show (⟨Pf s + BitVec.ofNat 64 2816, 32⟩ : Region).Contains (Pf s + BitVec.ofNat 64 (2816 + 8 * i)) 8
    rw [← Offset.add_ofNat_add_ofNat]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

theorem sa_sub {i : Nat} (hi : i < 4) : (⟨sa s i, 8⟩ : Region).Sub (argR s) := by
  rw [h.hargR]
  show Region.Sub ⟨Pf s + BitVec.ofNat 64 (2816 + 8 * i), 8⟩ ⟨Pf s + BitVec.ofNat 64 2816, 32⟩
  exact Offset.sub _ (by omega_arith) (by omega_arith)

/-- Our stack arguments are apart from the frame. -/
theorem sa_fa {i : Nat} (hi : i < 4) : ∀ r ∈ [FA s], (⟨sa s i, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint_base _ (by omega_arith) (by have := h.hBn; omega_arith)

theorem eArg {i : Nat} (hi : i < 4) : (eMem s).readW (sa s i) 64 = stackArg s i := by
  rw [Frame.readW (frame_eMem s) (Region.contains_self _ _) (h.sa_fa hi) (by decide), h.sa_eq]

/-- Our stack arguments are apart from `dst` and the working space. -/
theorem sa_dR {i : Nat} (hi : i < 4) : (⟨sa s i, 8⟩ : Region).Disjoint (dR s) :=
  h.pre.da.symm.sub_left (h.sa_sub hi)

theorem sa_sc {i : Nat} (hi : i < 4) : (⟨sa s i, 8⟩ : Region).Disjoint (scR s) := by
  show (⟨Pf s + BitVec.ofNat 64 (2816 + 8 * i), 8⟩ : Region).Disjoint ⟨Pf s + BitVec.ofNat 64 160, 2560⟩
  exact Offset.disjoint (Pf s) (.inr (by omega_arith)) (by omega_arith) (by have := h.hBn; omega_arith)

/-- `dst_len` is `len`. -/
theorem dstLen : stackArg s 1 = s.gpr .r10 := BitVec.eq_of_toNat_eq h.pre.dl

end Lay

/-! ## The phases -/

/-- After the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eMem s
  r12 : e.gpr .r12 = Pf s
  gpr : ∀ r, r ≠ .r0 → r ≠ .r12 → e.gpr r = s.gpr r
  sp : e.sp = Pf s
  rd : e.rd = s.rd
  wr : e.wr = FR s :: s.wr

theorem entered_wp {s : State} (h : Lay s) : WP isa (.block entry) (allocated 2720 s) (Entered s) := by
  have asp : (allocated 2720 s).sp = Pf s := rfl
  have awr : (allocated 2720 s).wr = FR s :: s.wr := rfl
  have amem : (allocated 2720 s).mem = s.mem.write (Pf s) 8 s.sp := rfl
  have ag (r : Reg) : (allocated 2720 s).gpr r = s.gpr r := rfl
  obtain fin : ∀ {a : Nat}, 32 ≤ a → a + 8 ≤ 2720 → InRegions (FR s :: s.wr) (Pf s + BitVec.ofNat 64 a) 8 :=
    fun h₁ h₂ => fr_in s h₁ h₂ _
  unfold entry
  refine Gather.wp_addSp (by decide) fun u₁ v₁ => ?_
  obtain p₁ : u₁.gpr .r12 = Pf s := by rw [v₁.gpr, asp]; exact BitVec.add_zero _
  obtain w₁ : u₁.wr = FR s :: s.wr := by rw [v₁.wr, awr]
  refine wp_mflr fun u₂ v₂ => ?_
  refine wp_std (a := fa s 152) (by decide) (by decide) (by rw [v₂.other _ (by decide), p₁])
    (by rw [v₂.wr, w₁]; exact fin (by decide) (by decide)) fun u₃ v₃ => ?_
  obtain p₃ : u₃.gpr .r12 = Pf s := by rw [v₃.gpr, v₂.other _ (by decide), p₁]
  obtain rd₃ : u₃.rd = s.rd := by rw [v₃.rd, v₂.rd, v₁.rd]; rfl
  obtain w₃ : u₃.wr = FR s :: s.wr := by rw [v₃.wr, v₂.wr, w₁]
  obtain m₃ : u₃.mem = (s.mem.write (Pf s) 8 s.sp).writeW (fa s 152) s.lr := by
    rw [v₃.mem, v₂.gpr, v₂.mem, v₁.mem, v₁.lr, amem]; rfl
  refine wp_ld (a := sa s 2) (by decide) (by decide) (by rw [p₃]) (h.sa_in (by decide) _ rd₃) fun u₄ v₄ => ?_
  refine wp_std (a := fa s 96) (by decide) (by decide) (by rw [v₄.other _ (by decide), p₃])
    (by rw [v₄.wr, w₃]; exact fin (by decide) (by decide)) fun u₅ v₅ => ?_
  obtain p₅ : u₅.gpr .r12 = Pf s := by rw [v₅.gpr, v₄.other _ (by decide), p₃]
  obtain rd₅ : u₅.rd = s.rd := by rw [v₅.rd, v₄.rd, rd₃]
  obtain w₅ : u₅.wr = FR s :: s.wr := by rw [v₅.wr, v₄.wr, w₃]
  obtain sa' : ∀ {i : Nat}, i < 4 → ∀ m : Mem, Frame [FA s] s.mem m → m.readW (sa s i) 64 = stackArg s i :=
    fun hi m hm => by rw [Frame.readW hm (Region.contains_self _ _) (h.sa_fa hi) (by decide), h.sa_eq]
  obtain fA : ∀ m a v, a + 8 ≤ 2720 → Frame [FA s] s.mem m → Frame [FA s] s.mem (m.writeW (fa s a) (v : BitVec 64)) :=
    fun m a v ha hm => hm.writeW (List.mem_singleton_self _) _ (fa_in s ha)
  obtain f₃ : Frame [FA s] s.mem u₃.mem := by
    rw [m₃]; exact fA _ _ _ (by decide) ((Frame.refl _ _).write (List.mem_singleton_self _) _
      (Region.contains_self' (by decide)))
  obtain m₅ : u₅.mem = u₃.mem.writeW (fa s 96) (Tg s) := by rw [v₅.mem, v₄.gpr, v₄.mem, sa' (by decide) _ f₃]
  obtain f₅ : Frame [FA s] s.mem u₅.mem := by rw [m₅]; exact fA _ _ _ (by decide) f₃
  refine wp_ld (a := sa s 3) (by decide) (by decide) (by rw [p₅]) (h.sa_in (by decide) _ rd₅) fun u₆ v₆ => ?_
  refine wp_std (a := fa s 104) (by decide) (by decide) (by rw [v₆.other _ (by decide), p₅])
    (by rw [v₆.wr, w₅]; exact fin (by decide) (by decide)) fun u₇ v₇ => ?_
  obtain p₇ : u₇.gpr .r12 = Pf s := by rw [v₇.gpr, v₆.other _ (by decide), p₅]
  obtain rd₇ : u₇.rd = s.rd := by rw [v₇.rd, v₆.rd, rd₅]
  obtain w₇ : u₇.wr = FR s :: s.wr := by rw [v₇.wr, v₆.wr, w₅]
  obtain m₇ : u₇.mem = u₅.mem.writeW (fa s 104) (stackArg s 3) := by
    rw [v₇.mem, v₆.gpr, v₆.mem, sa' (by decide) _ f₅]
  obtain f₇ : Frame [FA s] s.mem u₇.mem := by rw [m₇]; exact fA _ _ _ (by decide) f₅
  refine wp_addi (by decide) (by decide) fun u₈ v₈ => ?_
  refine wp_std (a := fa s 112) (by decide) (by decide) (by rw [v₈.other _ (by decide), p₇])
    (by rw [v₈.wr, w₇]; exact fin (by decide) (by decide)) fun u₉ v₉ => ?_
  obtain p₉ : u₉.gpr .r12 = Pf s := by rw [v₉.gpr, v₈.other _ (by decide), p₇]
  obtain rd₉ : u₉.rd = s.rd := by rw [v₉.rd, v₈.rd, rd₇]
  obtain w₉ : u₉.wr = FR s :: s.wr := by rw [v₉.wr, v₈.wr, w₇]
  obtain m₉ : u₉.mem = u₇.mem.writeW (fa s 112) (fa s 160) := by rw [v₉.mem, v₈.gpr, v₈.mem, p₇]
  obtain f₉ : Frame [FA s] s.mem u₉.mem := by rw [m₉]; exact fA _ _ _ (by decide) f₇
  refine wp_ld (a := sa s 0) (by decide) (by decide) (by rw [p₉]) (h.sa_in (by decide) _ rd₉) fun u₁₀ v₁₀ => ?_
  refine wp_std (a := fa s 120) (by decide) (by decide) (by rw [v₁₀.other _ (by decide), p₉])
    (by rw [v₁₀.wr, w₉]; exact fin (by decide) (by decide)) fun u₁₁ v₁₁ => WP.block_nil ?_
  refine ⟨?_, by rw [v₁₁.gpr, v₁₀.other _ (by decide), p₉], fun r h0 h12 => ?_, ?_, ?_, ?_⟩
  · rw [v₁₁.mem, v₁₀.gpr, v₁₀.mem, sa' (by decide) _ f₉, m₉, m₇, m₅, m₃]
  · rw [v₁₁.gpr, v₁₀.other _ h0, v₉.gpr, v₈.other _ h0, v₇.gpr, v₆.other _ h0, v₅.gpr, v₄.other _ h0, v₃.gpr,
      v₂.other _ h0, v₁.other _ h12, ag]
  · rw [v₁₁.sp, v₁₀.sp, v₉.sp, v₈.sp, v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, asp]
  · rw [v₁₁.rd, v₁₀.rd, rd₉]
  · rw [v₁₁.wr, v₁₀.wr, w₉]

section
variable (s : State)

/-- The call's state, with its permissions. -/
abbrev xS (c : State) : State := c.callEntry.withRegions (rdC s) (wrC s)

end

/-- The registers at the call: our arguments. -/
theorem Entered.callGpr {s c : State} (hc : Entered s c) (rd' wr' : List Region) {r : Reg}
    (hr : r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]) :
    ((c.callEntry).withRegions rd' wr').gpr r = s.gpr r := by
  simp only [State.withRegions_gpr]
  rw [c.callEntry_gpr (by revert hr; revert r; decide), hc.gpr r (by revert hr; revert r; decide)
    (by revert hr; revert r; decide)]

/-- The call's stack arguments, in its own terms. -/
theorem Entered.argAddr {s c : State} (hc : Entered s c) (rd wr : List Region) :
    stackArgAddr ((c.callEntry).withRegions rd wr) 0 = fa s 96 := by
  show c.sp + BitVec.ofNat 64 (32 + 8 * (8 + 0)) = Pf s + BitVec.ofNat 64 96
  rw [hc.sp]

theorem Entered.args {s c : State} (hc : Entered s c) (rd wr : List Region) :
    stackArg ((c.callEntry).withRegions rd wr) 0 = Tg s ∧
      stackArg ((c.callEntry).withRegions rd wr) 1 = stackArg s 3 ∧
      stackArg ((c.callEntry).withRegions rd wr) 2 = fa s 160 ∧
      stackArg ((c.callEntry).withRegions rd wr) 3 = Dst s := by
  obtain sl := slots_eMem s
  refine ⟨?_, ?_, ?_, ?_⟩
  · show c.mem.readW (c.sp + BitVec.ofNat 64 (32 + 8 * (8 + 0))) 64 = _
    rw [hc.sp, hc.mem]; exact sl.tg
  · show c.mem.readW (c.sp + BitVec.ofNat 64 (32 + 8 * (8 + 1))) 64 = _
    rw [hc.sp, hc.mem]; exact sl.tl
  · show c.mem.readW (c.sp + BitVec.ofNat 64 (32 + 8 * (8 + 2))) 64 = _
    rw [hc.sp, hc.mem]; exact sl.sc
  · show c.mem.readW (c.sp + BitVec.ofNat 64 (32 + 8 * (8 + 3))) 64 = _
    rw [hc.sp, hc.mem]; exact sl.dst

/-- What the call needs. -/
theorem Entered.call {s c : State} (h : Lay s) (hc : Entered s c) :
    splitPre (xS s c) ∧ Covers (rdC s ++ wrC s) (c.rd ++ c.wr) ∧ Covers (wrC s) c.wr := by
  have pre := h.pre
  obtain g := fun r hr => hc.callGpr (rdC s) (wrC s) (r := r) hr
  obtain ⟨a0, a1, a2, a3⟩ := hc.args (rdC s) (wrC s)
  have hBn := h.hBn
  obtain sc : (scR s).Sub (FA s) := fr_sub s (by decide)
  obtain hA : (⟨fa s 96, 32⟩ : Region).Disjoint (scR s) :=
    Offset.disjoint (Pf s) (.inl (by decide)) (by decide) (by omega_arith)
  refine ⟨?_, ?_, ?_⟩
  · have f160 : (fa s 160).toNat + 2560 ≤ 2 ^ 64 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 160) (by decide),
        Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith
    simp only [splitPre, VG.Proof.AesGcm.PPC64LE.args, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, g .r3 (by decide), g .r4 (by decide), g .r5 (by decide),
      g .r6 (by decide), g .r7 (by decide), g .r8 (by decide), g .r9 (by decide), g .r10 (by decide), a0, a1, a2,
      a3, hc.sp, hc.argAddr]
    exact ⟨trivial, trivial, pre.bk.symm.sub_right sc, pre.bn.symm.sub_right sc, pre.ba.symm.sub_right sc,
      pre.bs.symm.sub_right sc, pre.bt.symm.sub_right sc, hA.symm, pre.kd, pre.sd, (pre.bd.sub_left sc).symm,
      pre.ok, pre.on, pre.oa, pre.os, pre.ot, f160, pre.od, by omega_arith, pre.hR⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [rdC, wrC, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, pre.rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, pre.rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, pre.rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, pre.rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, pre.rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · refine ⟨FR s, List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..), 64, ?_,
        by show 64 + 32 ≤ 2688; omega_arith⟩
      exact (Offset.add_ofNat_add_ofNat (Pf s) 32 64).symm
    · exact ⟨_, List.mem_append_right _ (by rw [hc.wr, pre.wr]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · refine ⟨FR s, List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..), 128, ?_,
        by show 128 + 2560 ≤ 2688; omega_arith⟩
      exact (Offset.add_ofNat_add_ofNat (Pf s) 32 128).symm
  · refine Covers.of_sub fun r hr => ?_
    simp only [wrC, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by rw [hc.wr, pre.wr]; simp, 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · refine ⟨FR s, by rw [hc.wr]; exact List.mem_cons_self .., 128, ?_, by show 128 + 2560 ≤ 2688; omega_arith⟩
      exact (Offset.add_ofNat_add_ofNat (Pf s) 32 128).symm

/-- The call's result, on the call's state. -/
theorem Entered.xres {s c : State} (h : Lay s) (hc : Entered s c) : openRes (xS s c) = res s := by
  have pre := h.pre
  obtain g := fun r hr => hc.callGpr (rdC s) (wrC s) (r := r) hr
  obtain ⟨a0, a1, -, -⟩ := hc.args (rdC s) (wrC s)
  obtain hm : (xS s c).mem = eMem s := by
    simp only [State.withRegions_mem, State.callEntry_mem, hc.mem]
  have apart {r : Region} (h₁ : (stkR s).Disjoint r) : ∀ r' ∈ [FA s], r.Disjoint r' := by
    intro r' hr'
    simp only [List.mem_singleton] at hr'; subst hr'
    exact h₁.symm
  obtain ⟨hc', hh⟩ := Proof.AesGcm.ctx_frame (frame_eMem s) (apart pre.bk) pre.hR
  obtain hn : bytesAt (eMem s) (Nn s) (NL s) = bytesAt s.mem (Nn s) (NL s) :=
    Proof.Cmac.bytesAt_frame (frame_eMem s) (apart pre.bn) (Nat.le_of_lt (s.gpr .r6).isLt)
  obtain ha : bytesAt (eMem s) (Ad s) (AL s) = bytesAt s.mem (Ad s) (AL s) :=
    Proof.Cmac.bytesAt_frame (frame_eMem s) (apart pre.ba) (Nat.le_of_lt (s.gpr .r8).isLt)
  obtain ht : bytesAt (eMem s) (Tg s) (TL s) = bytesAt s.mem (Tg s) (TL s) :=
    Proof.Cmac.bytesAt_frame (frame_eMem s) (apart pre.bt) (Nat.le_of_lt (stackArg s 3).isLt)
  obtain hd : bytesAt (eMem s) (Src s) (L s) = bytesAt s.mem (Src s) (L s) :=
    Proof.Cmac.bytesAt_frame (frame_eMem s) (apart pre.bs) (Nat.le_of_lt (s.gpr .r10).isLt)
  simp only [openRes, hm, g .r3 (by decide), g .r4 (by decide), g .r5 (by decide), g .r6 (by decide),
    g .r7 (by decide), g .r8 (by decide), g .r9 (by decide), g .r10 (by decide), a0, a1]
  rw [hc', hh, hn, hd, ha, ht]

/-- What the call leaves of `dst` and `r3`: `vg_aes_gcm_open`'s result. -/
def Out (s : State) (e : BitVec 64) (m : Mem) : Prop :=
  match res s with
  | some pt => e.setWidth 32 = 1 ∧ bytesAt m (Dst s) (L s) = pt
  | none => e.setWidth 32 = 0

/-- After the call. -/
structure Called (s z : State) : Prop where
  ra : z.mem.readW (fa s 152) 64 = s.lr
  a0 : z.mem.readW (sa s 0) 64 = Dst s
  a1 : z.mem.readW (sa s 1) 64 = stackArg s 1
  out : Out s (z.gpr .r3) z.mem
  pres : ∀ r ∈ preserved, z.gpr r = s.gpr r
  sp : z.sp = Pf s
  rd : z.rd = s.rd
  wr : z.wr = FR s :: s.wr

theorem called_wp (hv : SplitOk) {s c : State} (h : Lay s) (hc : Entered s c) :
    WP isa (.call "vg_aes_gcm_open_split" openSplit) c (Called s) := by
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  obtain g := fun r hr => hc.callGpr (rdC s) (wrC s) (r := r) hr
  obtain ⟨-, -, -, a3⟩ := hc.args (rdC s) (wrC s)
  refine WP.callAny (k := splitPPC64LE) hv hcp hcov hw
    (fun z rd' wr' sp' fr' pres' post' => ?_) (by rw [split_sdepth]; decide)
  have hpost : match openRes (xS s c) with
      | some pt => ((z.withRegions (rdC s) (wrC s)).gpr .r3).setWidth 32 = 1 ∧
        bytesAt (z.withRegions (rdC s) (wrC s)).mem (stackArg (xS s c) 3) ((xS s c).gpr .r10).toNat = pt
      | none => ((z.withRegions (rdC s) (wrC s)).gpr .r3).setWidth 32 = 0 := post'
  rw [hc.xres h, a3, g .r10 (by decide)] at hpost
  simp only [State.withRegions_gpr, State.withRegions_mem] at hpost
  -- What the call kept: our frame's return address and our arguments.
  have kept {a : Addr} (hd : (⟨a, 8⟩ : Region).Disjoint (dR s)) (hs : (⟨a, 8⟩ : Region).Disjoint (scR s)) :
      z.mem.readW a 64 = c.mem.readW a 64 := by
    refine Frame.readW fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [wrC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact hd
    · exact hs
    · simp only [below, split_sdepth]
      intro x _ hc'
      simp only [Region.Contains] at hc'
      omega_using [hc']
  obtain ra : z.mem.readW (fa s 152) 64 = s.lr := by
    rw [kept (h.pre.bd.sub_left (fr_sub s (by decide)))
      (Offset.disjoint (Pf s) (.inl (by decide)) (by decide) (by have := h.hBn; omega_arith)), hc.mem,
      (slots_eMem s).ra]
  obtain a0 : z.mem.readW (sa s 0) 64 = Dst s := by
    rw [kept (h.sa_dR (by decide)) (h.sa_sc (by decide)), hc.mem, h.eArg (by decide)]
  obtain a1 : z.mem.readW (sa s 1) 64 = stackArg s 1 := by
    rw [kept (h.sa_dR (by decide)) (h.sa_sc (by decide)), hc.mem, h.eArg (by decide)]
  refine ⟨ra, a0, a1, ?_, fun r hr => by
    rw [pres' r hr, hc.gpr r (by revert hr; revert r; decide) (by revert hr; revert r; decide)],
    sp'.trans hc.sp, rd'.trans hc.rd, wr'.trans hc.wr⟩
  unfold Out
  revert hpost
  cases res s with
  | some pt => intro hp; exact hp
  | none => intro hp; exact hp

/-! ## After the call -/

theorem eval_zero_w (s : State) (r : Reg) : isa.eval (.zero .w r) s = some ((s.gpr r).setWidth 32 == 0) := by
  simp only [eval, State.read, Size.bits]

/-- `wipeLoop`: the `n` bytes at `D` zeroed, from `r9 = D`, `r10 = n` and
`r11 = 0`. -/
theorem wipeLoop_wp (u : State) {D : Addr} {n : Nat} (hn : n < 2 ^ 64) (hD : D.toNat + n ≤ 2 ^ 64)
    (h₉ : u.gpr .r9 = D) (h₁₀ : u.gpr .r10 = BitVec.ofNat 64 n) (h₁₁ : u.gpr .r11 = 0)
    (hw : Covers [⟨D, n⟩] u.wr) :
    WP isa wipeLoop u fun u' => Proof.Zeroize.Prefix u'.mem D n ∧ Frame [⟨D, n⟩] u.mem u'.mem ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.lr = u.lr := by
  unfold wipeLoop
  refine WP.ite (decide (n = 0)) (eval_zero h₁₀ hn) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), Frame.refl _ _, fun _ _ _ => rfl, rfl, rfl,
      rfl, rfl⟩
  · have h0 : n ≠ 0 := by simpa using hf
    refine WP.loop (M := isa)
      (fun (w : Nat) (v : State) => ∃ i, w = n - i ∧ i < n ∧ v.gpr .r9 = D + BitVec.ofNat 64 i ∧
        v.gpr .r10 = BitVec.ofNat 64 (n - i) ∧ (∀ r, r ≠ .r9 → r ≠ .r10 → v.gpr r = u.gpr r) ∧ v.rd = u.rd ∧
        v.wr = u.wr ∧ v.sp = u.sp ∧ v.lr = u.lr ∧ Frame [⟨D, n⟩] u.mem v.mem ∧
        Proof.Zeroize.Prefix v.mem D i) ?_ (n - 0) _
      ⟨0, rfl, by omega_using [h0], by rw [h₉]; exact (BitVec.add_zero _).symm, by rw [h₁₀, Nat.sub_zero],
        fun _ _ _ => rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    rintro w v ⟨i, rfl, hi, r9, r10, gv, rdv, wrv, spv, lrv, fv, pv⟩
    obtain hcn : (⟨D, n⟩ : Region).Contains (D + BitVec.ofNat 64 i) 1 :=
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hn, hi])
    refine wp_stb (a := D + BitVec.ofNat 64 i) (by decide) (by decide) (by rw [r9]; exact BitVec.add_zero _)
      (by rw [wrv]; exact hw _ _ ⟨_, List.mem_singleton_self _, hcn⟩) fun t₁ u₁ => ?_
    refine wp_addi (by decide) (by decide) fun t₂ u₂ => wp_subi (by decide) (by decide) fun t₃ u₃ =>
      WP.block_nil ?_
    obtain z₁ : (v.gpr .r11).setWidth 8 = (0 : BitVec 8) := by rw [gv _ (by decide) (by decide), h₁₁]; rfl
    obtain m₃ : t₃.mem = v.mem.writeW (D + BitVec.ofNat 64 i) (0 : BitVec 8) := by
      rw [u₃.mem, u₂.mem, u₁.mem, z₁]
    obtain f' : Frame [⟨D, n⟩] u.mem t₃.mem := by
      rw [m₃]; exact fv.writeW (List.mem_singleton_self _) _ hcn
    obtain p' : Proof.Zeroize.Prefix t₃.mem D (i + 1) := by
      rw [m₃]; exact Proof.Zeroize.prefix_writeW (w := 8) pv (by omega_using [hn, hi])
    obtain g' : ∀ r, r ≠ .r9 → r ≠ .r10 → t₃.gpr r = u.gpr r := fun r a b => by
      rw [u₃.other _ b, u₂.other _ a, u₁.gpr, gv r a b]
    obtain r9' : t₃.gpr .r9 = D + BitVec.ofNat 64 (i + 1) := by
      rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, r9, BitVec.add_assoc, ← BitVec.ofNat_add]
    obtain r10' : t₃.gpr .r10 = BitVec.ofNat 64 (n - (i + 1)) := by
      rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, r10, ofNat_sub_one (by omega_using [hi]), Nat.sub_sub]
    obtain rd' : t₃.rd = u.rd := by rw [u₃.rd, u₂.rd, u₁.rd, rdv]
    obtain wr' : t₃.wr = u.wr := by rw [u₃.wr, u₂.wr, u₁.wr, wrv]
    obtain sp' : t₃.sp = u.sp := by rw [u₃.sp, u₂.sp, u₁.sp, spv]
    obtain lr' : t₃.lr = u.lr := by rw [u₃.lr, u₂.lr, u₁.lr, lrv]
    obtain ev := eval_nonzero (r := .r10) (a := n - (i + 1)) r10' (by omega_using [hn])
    by_cases he : i + 1 = n
    · left
      exact ⟨by rw [ev]; simp [he], by rw [← he]; exact p', f', g', rd', wr', sp', lr'⟩
    · right
      exact ⟨by rw [ev]; simp; omega_using [hi, he], n - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, he], r9', r10', g', rd', wr', sp',
        lr', f', p'⟩

/-- The zeros of `Prefix`, as bytes. -/
theorem bytesAt_zeros {m : Mem} {D : Addr} {n : Nat} (h : Proof.Zeroize.Prefix m D n) :
    bytesAt m D n = List.replicate n 0 := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i h₁ h₂
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact h i (by simpa [bytesAt] using h₁)

/-- After `wipeArgs`: `dst` in `r9`, `len` in `r10` and zero in `r11`. -/
structure WArgs (s z a : State) : Prop where
  r9 : a.gpr .r9 = Dst s
  r10 : a.gpr .r10 = BitVec.ofNat 64 (L s)
  r11 : a.gpr .r11 = 0
  gpr : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → a.gpr r = z.gpr r
  mem : a.mem = z.mem
  sp : a.sp = z.sp
  lr : a.lr = z.lr
  rd : a.rd = z.rd
  wr : a.wr = z.wr

theorem wipeArgs_wp {s z : State} (h : Lay s) (hz : Called s z) : WP isa (.block wipeArgs) z (WArgs s z) := by
  unfold wipeArgs
  refine Gather.wp_addSp (by decide) fun u₁ v₁ => ?_
  obtain p₁ : u₁.gpr .r12 = Pf s := by rw [v₁.gpr, hz.sp]; exact BitVec.add_zero _
  refine wp_ld (a := sa s 0) (by decide) (by decide) (by rw [p₁]) (h.sa_in (by decide) _ (by rw [v₁.rd, hz.rd]))
    fun u₂ v₂ => ?_
  refine wp_ld (a := sa s 1) (by decide) (by decide) (by rw [v₂.other _ (by decide), p₁])
    (h.sa_in (by decide) _ (by rw [v₂.rd, v₁.rd, hz.rd])) fun u₃ v₃ => ?_
  refine wp_li (by decide) fun u₄ v₄ => WP.block_nil ?_
  refine ⟨?_, ?_, v₄.gpr, fun r h9 h10 h11 h12 => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.mem, hz.a0]
  · rw [v₄.other _ (by decide), v₃.gpr, v₂.mem, v₁.mem, hz.a1, h.dstLen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [v₄.other _ h11, v₃.other _ h10, v₂.other _ h9, v₁.other _ h12]
  · rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  · rw [v₄.sp, v₃.sp, v₂.sp, v₁.sp]
  · rw [v₄.lr, v₃.lr, v₂.lr, v₁.lr]
  · rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd]
  · rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr]

/-- Where `after` leaves the state: what follows the call, with `dst` and
`r3` as `toPost` has them. -/
structure Done (s u : State) : Prop where
  post : toPost s u
  ra : u.mem.readW (fa s 152) 64 = s.lr
  pres : ∀ r ∈ preserved, u.gpr r = s.gpr r
  sp : u.sp = Pf s
  rd : u.rd = s.rd
  wr : u.wr = FR s :: s.wr

/-- When the call failed: `dst` zeroed. -/
theorem wipe_wp {s z : State} (h : Lay s) (hz : Called s z) (hres : res s = none) : WP isa wipe z (Done s) := by
  unfold wipe
  refine WP.seq (WP.mono (wipeArgs_wp h hz) fun a ha => ?_)
  obtain hw : Covers [⟨Dst s, L s⟩] a.wr := by
    rw [ha.wr, hz.wr, h.pre.wr]; exact Gather.covers_mem fun r hr => by simp at hr; subst hr; simp
  refine WP.mono (wipeLoop_wp a (s.gpr .r10).isLt h.pre.od ha.r9 ha.r10 ha.r11 hw)
    fun u ⟨pz, fu, gu, rdu, wru, spu, _⟩ => ?_
  obtain g' : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → u.gpr r = z.gpr r := fun r a b c d => by
    rw [gu r a b, ha.gpr r a b c d]
  obtain keep : u.mem.readW (fa s 152) 64 = z.mem.readW (fa s 152) 64 := by
    rw [← ha.mem]
    refine fu.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact h.pre.bd.sub_left (fr_sub s (by decide))
  obtain hpres : ∀ r ∈ preserved, r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 := by decide
  have o := hz.out
  unfold Out at o
  rw [hres] at o
  refine ⟨?_, keep.trans hz.ra, fun r hr => ?_, spu.trans (ha.sp.trans hz.sp), by rw [rdu, ha.rd, hz.rd],
    by rw [wru, ha.wr, hz.wr]⟩
  · unfold toPost
    rw [hres]
    exact ⟨by rw [g' _ (by decide) (by decide) (by decide) (by decide)]; exact o, bytesAt_zeros pz⟩
  · obtain ⟨a₁, a₂, a₃, a₄⟩ := hpres r hr
    rw [g' r a₁ a₂ a₃ a₄]; exact hz.pres r hr

/-- After the call: `dst` zeroed if it failed. -/
theorem after_wp {s z : State} (h : Lay s) (hz : Called s z) : WP isa after z (Done s) := by
  unfold after
  have o := hz.out
  unfold Out at o
  cases hr : res s with
  | none =>
    rw [hr] at o
    exact WP.ite true (by rw [eval_zero_w, o]; rfl) (fun _ => wipe_wp h hz hr) (fun h' => absurd h' (by decide))
  | some pt =>
    rw [hr] at o
    refine WP.ite false (by rw [eval_zero_w, o.1]; rfl) (fun h' => absurd h' (by decide))
      (fun _ => WP.block_nil ⟨?_, hz.ra, hz.pres, hz.sp, hz.rd, hz.wr⟩)
    unfold toPost
    rw [hr]
    exact o

theorem toPost_congr {s u t : State} (hm : t.mem = u.mem) (hg : t.gpr .r3 = u.gpr .r3) (h : toPost s u) :
    toPost s t := by
  unfold toPost at h ⊢
  rw [hm, hg]
  exact h

/-- `toPost` reads the memory only in the output. -/
private theorem toPost_lost {s u t : State} (hb : bytesAt t.mem (Dst s) (L s) = bytesAt u.mem (Dst s) (L s))
    (hg : t.gpr .r3 = u.gpr .r3) (h : toPost s u) : toPost s t := by
  unfold toPost at h ⊢
  rw [hb, hg]; exact h

/-- The return address back in the link register, and the frame freed. -/
theorem ret_wp {s u : State} (h : Lay s) (hu : Done s u) :
    WP isa (.block Impl.AesGcm.PPC64LE.SealGather.ret) u fun y =>
      abiPreserved s (freed 2720 y) ∧ toPost s (freed 2720 y) := by
  unfold Impl.AesGcm.PPC64LE.SealGather.ret
  refine Gather.wp_addSp (by decide) fun u₁ v₁ => ?_
  refine wp_ld (a := fa s 152) (by decide) (by decide) (by rw [v₁.gpr, hu.sp, BitVec.add_zero])
    (by
      obtain ⟨r, hr, hc⟩ := fr_in s (a := 152) (by decide) (by decide) s.wr
      exact ⟨r, List.mem_append_right _ (by rw [v₁.wr, hu.wr]; exact hr), hc⟩) fun u₂ v₂ => ?_
  refine wp_mtlr fun u₃ v₃ => WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · -- The callee-saved registers.
    obtain hpres : ∀ r ∈ preserved, r ≠ .r0 ∧ r ≠ .r12 := by decide
    show u₃.gpr r = s.gpr r
    rw [v₃.gpr, v₂.other _ (hpres r hr).1, v₁.other _ (hpres r hr).2, hu.pres r hr]
  · -- The stack pointer.
    show u₃.sp + BitVec.ofNat 64 2720 = s.sp
    rw [v₃.sp, v₂.sp, v₁.sp, hu.sp]
    exact h.hB.symm
  · -- The link register.
    simp only [freed]
    rw [v₃.lr, v₂.gpr, v₁.mem, hu.ra]
  · -- The result and the plaintext.
    refine toPost_congr (u := u) ?_ ?_ hu.post
    · simp only [freed]
      rw [v₃.mem, v₂.mem, v₁.mem]
    · simp only [freed]
      rw [v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide)]

theorem openTo_wp (hv : SplitOk) {s : State} (hs : ToPre s) :
    WP isa openTo s fun z => abiPreserved s z ∧ toPost s z := by
  obtain h := lay hs
  have w₁ := hs.w₁
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by omega_arith) ?_
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (called_wp hv h he) fun z hz => ?_)
  refine WP.seq (WP.mono (after_wp h hz) fun u hu => ?_)
  refine WP.mono (ret_wp h hu) fun y ⟨ha, hp⟩ m _ fl => ⟨abiPreserved_lost ha, ?_⟩
  -- The `free` loses the frame's bytes, the stack the contract reserves, apart from the output.
  have hD : bytesAt m (Dst s) (L s) = bytesAt y.mem (Dst s) (L s) :=
    List.map_congr_left fun i hi => lost_byte fl (R := dR s) hs.bd.symm (List.mem_range.mp hi)
  exact toPost_lost (u := freed 2720 y) (hD.trans (by rw [freed_mem_eq])) (by rw [freed_gpr_eq]) hp

end VG.Proof.AesGcm.PPC64LE.OpenTo

end

end

/-!
# AES-GCM decryption out of place, in one pass, PPC64LE: constant time

Untrusted: everything here is checked by Lean. Two runs whose stack pointer,
arguments and leak agree (`toPub`) leak the same trace, related piece by
piece from the states the correctness proof describes (`Gather.PPC64LE.Eq2`):
the frame's push, the entry and the load of the return address are at the
stack pointer or our frame; the call is constant time by its callee's
contract, whose public data (its arguments and whether it succeeds,
`Entered.leak`) agree; the branch after it is on whether the tag is right,
our leak (`Called.zero`); and `wipe`'s loop runs on `dst` and `len`. As for
`vg_aes_gcm_seal_gather` (`Gather/CT.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.PPC64LE.OpenTo

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE.OpenTo
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_seq rel_taint rel_ite ct_of)

/-- The call's public data, from the arguments: whether it succeeds. -/
theorem Entered.leak {s c : State} (h : Lay s) (hc : Entered s c) :
    (rounds ((xS s c).gpr .r4) → (openRes (xS s c)).isSome = (res s).isSome) := fun _ => by
  rw [hc.xres h]

/-- Whether the call failed, from what it left. -/
theorem Called.zero {s z : State} (hz : Called s z) : ((z.gpr .r3).setWidth 32 == 0) = (res s).isNone := by
  have ho := hz.out
  unfold Out at ho
  revert ho
  cases res s with
  | some pt => intro ho; rw [ho.1]; rfl
  | none => intro ho; rw [ho]; rfl

theorem resNone {σ₁ σ₂ : State} (p₁ : ToPre σ₁) (p₂ : ToPre σ₂) (ql : toLeak σ₁ = toLeak σ₂) :
    (res σ₁).isNone = (res σ₂).isNone := by
  simp only [toLeak, p₁.hR, p₂.hR, not_true_eq_false, ↓reduceIte, List.cons.injEq, and_true] at ql
  revert ql
  cases res σ₁ <;> cases res σ₂ <;> simp

theorem resSome {σ₁ σ₂ : State} (p₁ : ToPre σ₁) (p₂ : ToPre σ₂) (ql : toLeak σ₁ = toLeak σ₂) :
    (res σ₁).isSome = (res σ₂).isSome := by
  simp only [toLeak, p₁.hR, p₂.hR, not_true_eq_false, ↓reduceIte, List.cons.injEq, and_true] at ql
  revert ql
  cases res σ₁ <;> cases res σ₂ <;> simp

theorem openTo_ct (hv : SplitOk) (hct : ConstantTime isa splitPPC64LE.pre splitPPC64LE.pub openSplit) :
    ConstantTime isa ToPre toPub openTo := by
  refine ct_of fun s₁ s₂ p₁ p₂ hq => ?_
  have h₁ := lay p₁
  have h₂ := lay p₂
  obtain ⟨qsp, ql, q3, q4, q5, q6, q7, q8, q9, q10, qa⟩ := hq
  have hP : Pf s₁ = Pf s₂ := by simp only [Pf, qsp]
  unfold openTo
  refine (RelCT.alloc (P := Eq2 s₁ s₂) (R := TT) (fun a b ⟨ha, hb⟩ => by subst a b; exact qsp)
    ((?_ : RelCT isa (Eq2 (allocated 2720 s₁) (allocated 2720 s₂)) _ TT).mono
      (fun a b ⟨s, t, ⟨hs, ht⟩, ha, hb⟩ => by subst s t; exact ⟨ha, hb⟩) fun _ _ h => h)).mono
      (fun _ _ h => h) fun _ _ _ => trivial
  -- The entry.
  refine rel_seq (rel_taint [] (show s₁.sp - BitVec.ofNat 64 2720 = s₂.sp - BitVec.ofNat 64 2720 by rw [qsp])
    (by simp) (by taint_decide)) (entered_wp h₁) (entered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC s₂ = rdC s₁ := by
    simp only [rdC, kR, nR, aR, sR, tR, C, Nn, NL, Ad, AL, Src, L, Tg, TL, fa, Pf, q3, q5, q6, q7, q8, q9, q10,
      qa 2 (by decide), qa 3 (by decide), qsp]
  have hwr : wrC s₂ = wrC s₁ := by simp only [wrC, dR, scR, Dst, L, fa, Pf, qa 0 (by decide), q10, qsp]
  have hx₂ : xS s₂ e₂ = e₂.callEntry.withRegions (rdC s₁) (wrC s₁) := by rw [← hrd, ← hwr]
  obtain ⟨cp₁, cv₁, cw₁⟩ := he₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := he₂.call h₂
  have lk₁ := he₁.leak h₁
  have lk₂ := he₂.leak h₂
  rw [hx₂] at cp₂ lk₂
  rw [hrd, hwr] at cv₂
  rw [hwr] at cw₂
  have g₁ := fun r hr => he₁.callGpr (rdC s₁) (wrC s₁) (r := r) hr
  have g₂ := fun r hr => he₂.callGpr (rdC s₁) (wrC s₁) (r := r) hr
  obtain ⟨a0₁, a1₁, a2₁, a3₁⟩ := he₁.args (rdC s₁) (wrC s₁)
  obtain ⟨a0₂, a1₂, a2₂, a3₂⟩ := he₂.args (rdC s₁) (wrC s₁)
  refine rel_seq (RelCT.call hv hct (rdC s₁) (wrC s₁) fun x y ⟨hx, hy⟩ => by
      subst hx hy
      refine ⟨cp₁, cp₂, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩, fun hr => ?_⟩, cv₁, cw₁, cv₂, cw₂⟩
      · rw [g₁ .r3 (by decide), g₂ .r3 (by decide), q3]
      · rw [g₁ .r4 (by decide), g₂ .r4 (by decide), q4]
      · rw [g₁ .r5 (by decide), g₂ .r5 (by decide), q5]
      · rw [g₁ .r6 (by decide), g₂ .r6 (by decide), q6]
      · rw [g₁ .r7 (by decide), g₂ .r7 (by decide), q7]
      · rw [g₁ .r8 (by decide), g₂ .r8 (by decide), q8]
      · rw [g₁ .r9 (by decide), g₂ .r9 (by decide), q9]
      · rw [g₁ .r10 (by decide), g₂ .r10 (by decide), q10]
      · simp only [State.withRegions_sp, State.callEntry_sp, he₁.sp, he₂.sp, hP]
      · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_using [hi]) with rfl | rfl | rfl | rfl
        · rw [a0₁, a0₂, Tg, Tg, qa 2 (by decide)]
        · rw [a1₁, a1₂, qa 3 (by decide)]
        · rw [a2₁, a2₂, fa, fa, hP]
        · rw [a3₁, a3₂, Dst, Dst, qa 0 (by decide)]
      · have hr₂ := hr
        rw [g₁ .r4 (by decide), q4, ← g₂ .r4 (by decide)] at hr₂
        rw [lk₁ hr, lk₂ hr₂, resSome p₁ p₂ ql])
    (called_wp hv h₁ he₁) (called_wp hv h₂ he₂) fun z₁ z₂ hz₁ hz₂ => ?_
  -- After the call: the same branch in both runs.
  have hn := resNone p₁ p₂ ql
  refine rel_seq ?_ (after_wp h₁ hz₁) (after_wp h₂ hz₂) fun u₁ u₂ hu₁ hu₂ => ?_
  · unfold after
    have ev₁ : isa.eval (.zero .w .r3) z₁ = some (res s₁).isNone := by rw [eval_zero_w, hz₁.zero]
    have ev₂ : isa.eval (.zero .w .r3) z₂ = some (res s₁).isNone := by rw [eval_zero_w, hz₂.zero, hn]
    refine rel_ite ev₁ ev₂ (fun _ => ?_) fun _ => ?_
    swap
    · exact rel_taint [] (by rw [hz₁.sp, hz₂.sp, hP]) (by simp) (by taint_decide)
    -- `wipe`, from the same public arguments.
    unfold wipe
    refine rel_seq (rel_taint [] (by rw [hz₁.sp, hz₂.sp, hP]) (by simp) (by taint_decide))
      (wipeArgs_wp h₁ hz₁) (wipeArgs_wp h₂ hz₂) fun w₁ w₂ hw₁ hw₂ => ?_
    exact rel_taint [.r9, .r10] (by rw [hw₁.sp, hw₂.sp, hz₁.sp, hz₂.sp, hP])
      (by
        simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
        exact ⟨by rw [hw₁.r9, hw₂.r9, Dst, Dst, qa 0 (by decide)], by rw [hw₁.r10, hw₂.r10, L, L, q10]⟩)
      (by taint_decide)
  -- Our return address.
  exact rel_taint [] (by rw [hu₁.sp, hu₂.sp, hP]) (by simp) (by taint_decide)

end VG.Proof.AesGcm.PPC64LE.OpenTo
