module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Crypt
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneShot
public import VerifiedGarbage.Impl.AesGcm.PPC64LE.OpenTo
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Groups
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Verified
public import VerifiedGarbage.Proof.Gcm.SplitBlocksContract
import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneEntry
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealFused
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CryptOk
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.FinTag
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.Gcm.StreamTo
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.Sig

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
  have h27 := he.fr .r27 (by decide)
  have h28 := he.fr .r28 (by decide)
  have h29 := he.r29; have h30 := he.r30; have h31 := he.r31
  have h23 := he.fr .r23 (by decide)
  have hsh : s.gpr .r23 >>> 4 = BitVec.ofNat 64 (Q V) := by
    rw [h23]
    calc
      _ = BitVec.ofNat 64 (V .r23).toNat >>> 4 := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      _ = _ := shr4 (V .r23).isLt
  have hsp := he.sp
  have h₀ : WP isa (.block [.addSp .r12 0]) s fun s₀ =>
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
  have e : ∀ r, r ≠ .r12 → r ≠ .r26 → s₁.gpr r = s.gpr r := fun r a b => (g₁ r b).trans (g₀ r a)
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
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (b := 2 ^ 64) (by omega)]
  have := Nat.mod_le (p.toNat + off) (2 ^ 64)
  omega

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
  have hq : Q V < 2 ^ 64 := by show (V .r23).toNat / 16 < 2 ^ 64; have := (V .r23).isLt; omega
  have hle : Q V * 16 ≤ (V .r23).toNat := by show (V .r23).toNat / 16 * 16 ≤ _; exact Nat.div_mul_le_self _ _
  have hR : R < 2 ^ 64 := by rcases h.rounds with e | e | e <;> omega
  have he := h.env
  have hsrc := h.src
  have hdst := h.dst
  have k₁ := a.keeps
  refine ⟨?_, ?_, ?_⟩
  · sig_eval [Proof.Gcm.decryptBlocksToContract, Proof.Gcm.decryptBlocksToSig, Proof.Gcm.decryptBlocksToPre,
      PPC64LE.abi, PPC64LE.argRegs]
    simp only [a.r3, a.r4, a.r5, a.r6, a.r7, a.r8, a.r9, a.r10, toNat64 hq, toNat64 hR]
    refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, L.cw, fitOff _ L.sw (by decide) (by decide),
      by have := hsrc.fit; omega, by have := hdst.ok.fit; omega, fitOff _ L.ww (by decide) (by decide),
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
  have hq : Q V < 2 ^ 64 := by show (V .r23).toNat / 16 < 2 ^ 64; have := (V .r23).isLt; omega
  have hR : R < 2 ^ 64 := by rcases h.rounds with e | e | e <;> omega
  have k₁ := a.keeps
  have he₁ : Env V sp s₁ := h.env.keep (fun r hr => a.regs r (by revert r; decide)) k₁.sp k₁.rd k₁.wr
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
  have h23 := he.fr .r23 (by decide)
  have h27 := he.fr .r27 (by decide)
  have hand := and15 (V .r23)
  have hsub : V .r23 - BitVec.ofNat 64 ((V .r23).toNat % 16) = BitVec.ofNat 64 (16 * Q V) := by
    calc
      _ = BitVec.ofNat 64 (V .r23).toNat - BitVec.ofNat 64 ((V .r23).toNat % 16) := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      _ = _ := by rw [ofNat_sub64 (Nat.mod_le _ _) (V .r23).isLt]; congr 1; show _ = 16 * ((V .r23).toNat / 16); omega
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
  have h16 : 16 * Q V ≤ (V .r23).toNat := by show 16 * ((V .r23).toNat / 16) ≤ _; omega
  have hk : (V .r23).toNat % 16 = (V .r23).toNat - 16 * Q V := by show _ = _ - 16 * ((V .r23).toNat / 16); omega
  have hR := h.rounds
  have hdst := h.dst
  have k₂ := p.keeps
  have dCw : ∀ r ∈ [(⟨V .r30 + BitVec.ofNat 64 16, 48⟩ : Region), ⟨D, Q V * 16⟩,
      ⟨V .r31 + BitVec.ofNat 64 448, 2112⟩], (⟨V .r29, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.cs.sub_right (Lay.stSub (by decide))
    · exact hdst.ctx.sub_right (Region.sub_prefix (by omega))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
  have he₂ : Env V sp s₂ := hw.env.keep (fun r hr => p.regs r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide)) k₂.sp k₂.rd k₂.wr
  have rd₂ : s₂.rd = s.rd := k₂.rd.trans hw.rd
  have wr₂ : s₂.wr = s.wr := k₂.wr.trans hw.wr
  refine ⟨he₂, p.r24, by rw [p.r25, hk], fun _ => p.r26, h.r28, hR, .inr (by omega),
    (h.src.of_eq rd₂ wr₂).drop h16, (hdst.of_eq rd₂ wr₂).drop h16, (fun h => nomatch h),
    .inr ((h.sd.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))),
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
  have h16 : 16 * Q V ≤ (V .r23).toNat := by show 16 * ((V .r23).toNat / 16) ≤ _; omega
  have hk : (V .r23).toNat % 16 = (V .r23).toNat - 16 * Q V := by show _ = _ - 16 * ((V .r23).toNat / 16); omega
  have hkl : (V .r23).toNat - 16 * Q V < 16 := by show _ - 16 * ((V .r23).toNat / 16) < 16; omega
  have hR := h.rounds
  have hdst := h.dst
  have hsrc := h.src
  let cph := ctxCiph s.mem (V .r29) R
  let icb := blockAt s.mem (V .r30 + BitVec.ofNat 64 48)
  -- the whole blocks
  refine WP.seq (WP.seq (WP.mono (whole_ok L h) fun s₁ hw => ?_))
  have dCw : ∀ r ∈ [(⟨V .r30 + BitVec.ofNat 64 16, 48⟩ : Region), ⟨D, Q V * 16⟩,
      ⟨V .r31 + BitVec.ofNat 64 448, 2112⟩], (⟨V .r29, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.cs.sub_right (Lay.stSub (by decide))
    · exact hdst.ctx.sub_right (Region.sub_prefix (by omega))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
  -- the last bytes' arguments
  refine WP.seq (WP.seq (WP.mono (partArgs_ok hw.env hw.r26) fun s₂ ⟨a24, a25, a26, g₂, k₂⟩ => ?_))
  have he₂ : Env V sp s₂ := hw.env.keep (fun r hr => g₂ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide)) k₂.sp k₂.rd k₂.wr
  have rd₂ : s₂.rd = s.rd := k₂.rd.trans hw.rd
  have wr₂ : s₂.wr = s.wr := k₂.wr.trans hw.wr
  have ti : TailIn true V sp R icb (16 * Q V) (V .r27 + BitVec.ofNat 64 (16 * Q V))
      (D + BitVec.ofNat 64 (16 * Q V)) ((V .r23).toNat - 16 * Q V) cph
      (blockAt s.mem (V .r30 + BitVec.ofNat 64 48) = icb) s₂ := by
    refine ⟨he₂, a24, by rw [a25, hk], fun _ => a26, h.r28, hR, .inr (by omega),
      (hsrc.of_eq rd₂ wr₂).drop h16, (hdst.of_eq rd₂ wr₂).drop h16, (fun h => nomatch h),
      .inr ((h.sd.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))),
      ?_, fun hcb => ?_⟩
    · rw [k₂.mem]; exact ciph_frame hw.frame dCw hR
    · have := (Proof.Gcm.ctr_wholeTo (Proof.Gcm.ctr_zero s.mem (V .r30 + BitVec.ofNat 64 48)
        (V .r30 + BitVec.ofNat 64 64) cph hcb) (by decide) hw.out hw.cb).2
      rw [Nat.zero_add] at this
      rw [k₂.mem]; exact this
  refine WP.mono (WP.with_rdwr (cryptTailWith_ok L ti hkl)) fun s₃ ⟨o, rd₃', wr₃', _⟩ => ?_
  have rd₃ : s₃.rd = s.rd := rd₃'.trans rd₂
  have wr₃ : s₃.wr = s.wr := wr₃'.trans wr₂
  -- the last bytes, buffered for GHASH
  refine WP.seq (WP.mono (SealFused.tailSetup_ok o.env) fun s₄ ⟨b24, b25, b26, g₄, k₄⟩ => ?_)
  have he₄ : Env V sp s₄ := o.env.keep (fun r hr => g₄ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide)) k₄.sp k₄.rd k₄.wr
  have rd₄ : s₄.rd = s.rd := k₄.rd.trans rd₃
  have wr₄ : s₄.wr = s.wr := k₄.wr.trans wr₃
  have hxpad : (a ++ Spec.Gcm.zeros (Spec.Gcm.padLen a.length)).length % 16 = 0 := by
    rw [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  let x := (a ++ Spec.Gcm.zeros (Spec.Gcm.padLen a.length)) ++ bytesAt s.mem (V .r27) (16 * Q V)
  have hx0 : x.length % 16 = 0 := by
    simp only [x, List.length_append, length_bytesAt] at hxpad ⊢; omega
  have hab₁ : Proof.Gcm.Absorbed s₁.mem (V .r30 + BitVec.ofNat 64 16) (V .r30 + BitVec.ofNat 64 32)
      (ctxH s.mem (V .r29)) x :=
    Proof.Gcm.absorb_whole hab hxpad (by rw [length_bytesAt]; omega) (by rw [hw.hash, Proof.Gcm.blocksAt_eq])
  have hds := ti.dst
  have hab₄ : Proof.Gcm.Absorbed s₄.mem (V .r30 + BitVec.ofNat 64 16) (V .r30 + BitVec.ofNat 64 32)
      (ctxH s.mem (V .r29)) x := by
    refine hab₁.congr ?_ ?_
    · rw [k₄.mem, blockAt_frame o.frame (stp_crFrame L hds (d := 16) (k := 16) (by decide)), k₂.mem]
    · rw [hx0]; simp only [bytesAt, List.range_zero, List.map_nil]
  have hH₁ : blockAt s₁.mem (V .r29 + BitVec.ofNat 64 240) = ctxH s.mem (V .r29) := ctxH_keep hw.frame dCw
  have hH₄ : blockAt s₄.mem (V .r29 + BitVec.ofNat 64 240) = ctxH s.mem (V .r29) := by
    rw [k₄.mem, blockAt_frame o.frame (fun r hr => (ctx_crFrame L hds r hr).sub_left
      (Lay.ctxSub (d := 240) (n := 16) (by decide))), k₂.mem, hH₁]
  have hsufd : DataOk (V .r30) (V .r31) s₄ (V .r27 + BitVec.ofNat 64 (16 * Q V)) ((V .r23).toNat % 16) := by
    rw [hk]; exact (hsrc.of_eq rd₄ wr₄).drop h16
  have ai : AbsIn V sp 16 (ctxH s.mem (V .r29)) x (V .r27 + BitVec.ofNat 64 (16 * Q V))
      ((V .r23).toNat % 16) s₄ := by
    refine ⟨he₄, ?_, b25, by rw [hx0]; exact b26, hsufd, hH₄⟩
    rw [b24]
  refine WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) ai)) fun s₅ ⟨ab, rd₅', wr₅', _⟩ => ?_
  have rd₅ : s₅.rd = s.rd := rd₅'.trans rd₄
  have wr₅ : s₅.wr = s.wr := wr₅'.trans wr₄
  -- the source's last bytes, as they were
  have hsuf : bytesAt s₄.mem (V .r27 + BitVec.ofNat 64 (16 * Q V)) ((V .r23).toNat % 16) =
      bytesAt s.mem (V .r27 + BitVec.ofNat 64 (16 * Q V)) ((V .r23).toNat % 16) := by
    have hs : Region.Sub (⟨V .r27 + BitVec.ofNat 64 (16 * Q V), (V .r23).toNat % 16⟩ : Region)
        ⟨V .r27, (V .r23).toNat⟩ := Offset.sub_base _ (by omega)
    rw [k₄.mem, bytesAt_frame o.frame ?_ (by omega), k₂.mem, bytesAt_frame hw.frame ?_ (by omega)]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hsrc.st.sub_left hs).sub_right (Lay.stSub (by decide))
      · exact (h.sd.sub_left hs).sub_right (Region.sub_prefix (by omega))
      · exact (hsrc.w.sub_left hs).sub_right (Lay.wSub (by decide))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [← hk]; exact (h.sd.sub_left hs).sub_right (Offset.sub_base _ (by omega))
      · exact (hsrc.st.sub_left hs).sub_right (Lay.stSub (by decide))
      · exact (hsrc.w.sub_left hs).sub_right (Lay.wSub (by decide))
  let ct := bytesAt s.mem (V .r27) (V .r23).toNat
  have hct : ct = bytesAt s.mem (V .r27) (16 * Q V) ++
      bytesAt s.mem (V .r27 + BitVec.ofNat 64 (16 * Q V)) ((V .r23).toNat % 16) := by
    rw [← bytesAt_add, show 16 * Q V + (V .r23).toNat % 16 = (V .r23).toNat by omega]
  have hne : ct ≠ [] := by
    intro hz; have hh := congrArg List.length hz; rw [length_bytesAt, List.length_nil] at hh; omega
  have habv := ab.abs hab₄
  have hgi : x ++ bytesAt s₄.mem (V .r27 + BitVec.ofNat 64 (16 * Q V)) ((V .r23).toNat % 16) =
      Spec.Gcm.ghashInput a ct := by
    rw [Proof.Gcm.ghashInput_of_ne hne, hct, hsuf]
    simp only [x, List.append_assoc]
  rw [hgi] at habv
  have hH₅ : blockAt s₅.mem (V .r29 + BitVec.ofNat 64 240) = ctxH s.mem (V .r29) := by
    rw [blockAt_frame ab.frame (ctx_absFrame L (.inr rfl))]; exact hH₄
  -- the tag
  refine WP.mono (WP.with_rdwr (finTag_ok L (o := 112) (.inr rfl) (a := a) (ct := ct) ab.env h.r28 hR hH₅
    (by rw [ha]) (length_bytesAt _ _ _).symm)) fun s₆ ⟨fg, rd₆', wr₆', _⟩ => ?_
  have hle : Q V * 16 ≤ (V .r23).toNat := by omega
  -- the key schedule and `J₀`, as they were
  have hc₅ : ciphOf s₅.mem (V .r29) R = cph := by
    refine (ciph_frame (abs_taFrame ab.frame) (ctx_taFrame L) hR).trans ?_
    rw [k₄.mem]
    refine (ciph_frame o.frame (ctx_crFrame L hds) hR).trans ?_
    rw [k₂.mem]
    exact ciph_frame hw.frame dCw hR
  have hj₅ : blockAt s₅.mem (V .r30) = blockAt s.mem (V .r30) := by
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
  have hf := fg.out habv
  rw [hc₅, hj₅, ha] at hf
  -- the destination
  have hcw := (Proof.Gcm.ctr_wholeTo (Proof.Gcm.ctr_zero s.mem (V .r30 + BitVec.ofNat 64 48)
    (V .r30 + BitVec.ofNat 64 64) cph (icb := icb) rfl) (by decide) hw.out hw.cb).1
  have hdone : bytesAt s₃.mem D (16 * Q V) = bytesAt s₁.mem D (16 * Q V) := by
    rw [bytesAt_frame o.frame (fun r hr => ?_) (by omega), k₂.mem]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact split_disj h16 hn
    · exact (hdst.ok.st.sub_left (Region.sub_prefix h16)).sub_right (Lay.stSub (by decide))
    · exact (hdst.ok.w.sub_left (Region.sub_prefix h16)).sub_right (Lay.wSub (by decide))
  have hs₂ : bytesAt s₂.mem (V .r27 + BitVec.ofNat 64 (16 * Q V)) ((V .r23).toNat - 16 * Q V) =
      bytesAt s.mem (V .r27 + BitVec.ofNat 64 (16 * Q V)) ((V .r23).toNat - 16 * Q V) := by
    have hs : Region.Sub (⟨V .r27 + BitVec.ofNat 64 (16 * Q V), (V .r23).toNat - 16 * Q V⟩ : Region)
        ⟨V .r27, (V .r23).toNat⟩ := Offset.sub_base _ (by omega)
    rw [k₂.mem, bytesAt_frame hw.frame ?_ (by omega)]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hsrc.st.sub_left hs).sub_right (Lay.stSub (by decide))
    · exact (h.sd.sub_left hs).sub_right (Region.sub_prefix (by omega))
    · exact (hsrc.w.sub_left hs).sub_right (Lay.wSub (by decide))
  have key := done_appendTo (P := 0) (hdone.trans hcw) (by rw [Nat.zero_add, o.out rfl, hs₂])
  rw [show 16 * Q V + ((V .r23).toNat - 16 * Q V) = (V .r23).toNat by omega] at key
  have hd₆ : bytesAt s₆.mem D (V .r23).toNat = bytesAt s₃.mem D (V .r23).toNat := by
    have dT : ∀ r ∈ tagFrame (V .r30) (V .r31) 112, (⟨D, (V .r23).toNat⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hdst.ok.st.sub_right (Region.sub_prefix (by decide))
      · exact hdst.ok.w.sub_right (Lay.wSub (by decide))
      · exact hdst.ok.w.sub_right (Lay.wSub (by decide))
      · exact hdst.ok.w.sub_right (Lay.wSub (by decide))
    rw [bytesAt_frame fg.frame dT (by omega),
      bytesAt_frame ab.frame (data_absFrame (.inr rfl) hdst.ok) (by omega), k₄.mem]
  -- what was written
  let T : List Region := passFrame V D
  have F₁ : Frame T s.mem s₁.mem := hw.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨V .r30, 80⟩, by simp [T], Lay.stSub (by decide)⟩
    · exact ⟨⟨D, (V .r23).toNat⟩, by simp [T], Region.sub_prefix hle⟩
    · exact ⟨⟨V .r31 + BitVec.ofNat 64 448, 2112⟩, by simp [T], fun _ h => h⟩
  have F₃ : Frame T s₂.mem s₃.mem := o.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨D, (V .r23).toNat⟩, by simp [T], Offset.sub_base _ (by omega)⟩
    · exact ⟨⟨V .r30, 80⟩, by simp [T], Lay.stSub (by decide)⟩
    · exact ⟨⟨V .r31 + BitVec.ofNat 64 448, 2112⟩, by simp [T], Offset.sub _ (by decide) (by decide)⟩
  have F₅ : Frame T s₄.mem s₅.mem := ab.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨V .r30, 80⟩, by simp [T], Lay.stSub (by decide)⟩
    · exact ⟨⟨V .r30, 80⟩, by simp [T], Lay.stSub (by decide)⟩
    · exact ⟨⟨V .r31 + BitVec.ofNat 64 448, 2112⟩, by simp [T], Offset.sub _ (by decide) (by decide)⟩
  have F₆ : Frame T s₅.mem s₆.mem := fg.frame.sub fun r hr => by
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
