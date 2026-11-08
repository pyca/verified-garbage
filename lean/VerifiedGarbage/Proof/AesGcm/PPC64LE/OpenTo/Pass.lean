module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Crypt
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneShot
public import VerifiedGarbage.Impl.AesGcm.PPC64LE.OpenTo
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Groups
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Verified
import VerifiedGarbage.Proof.Gcm.SplitBlocksContract
import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneEntry
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
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
  out : blocksAt s.mem D (Q V) = ctr32 (ctxCiph s₀.mem (V .r29) R)
    (blockAt s₀.mem (V .r30 + BitVec.ofNat 64 48)) (blocksAt s₀.mem (V .r27) (Q V))
  cb : blockAt s.mem (V .r30 + BitVec.ofNat 64 48) =
    Nat.repeat inc32 (Q V) (blockAt s₀.mem (V .r30 + BitVec.ofNat 64 48))
  hash : blockAt s.mem (V .r30 + BitVec.ofNat 64 16) = ghashFrom (ctxH s₀.mem (V .r29))
    (blockAt s₀.mem (V .r30 + BitVec.ofNat 64 16)) (blocksAt s₀.mem (V .r27) (Q V))
  frame : Frame [⟨V .r30 + BitVec.ofNat 64 16, 48⟩, ⟨D, Q V * 16⟩, ⟨V .r31 + BitVec.ofNat 64 448, 2112⟩]
    s₀.mem s.mem

/-- The registers `wholeArgs` sets. -/
def argRegs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12]

theorem wholeArgs_ok {R : Nat} {D : Addr} {s : State} (h : WholeIn V sp R D s) :
    WP isa (.block wholeArgs) s fun s' =>
      s'.gpr .r3 = V .r29 ∧ s'.gpr .r4 = BitVec.ofNat 64 R ∧ s'.gpr .r5 = V .r30 + BitVec.ofNat 64 16 ∧
      s'.gpr .r6 = V .r27 ∧ s'.gpr .r7 = BitVec.ofNat 64 (Q V) ∧ s'.gpr .r8 = D ∧
      s'.gpr .r9 = BitVec.ofNat 64 (Q V) ∧ s'.gpr .r10 = V .r31 + BitVec.ofNat 64 448 ∧
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
  have h₁ : WP isa (.block [mov .r3 .r29, mov .r4 .r28, .addi .r5 .r30 16, mov .r6 .r27, .lsr .d .r7 .r23 4,
      .addSp .r12 0]) s fun s₁ =>
      s₁.gpr .r3 = V .r29 ∧ s₁.gpr .r4 = BitVec.ofNat 64 R ∧ s₁.gpr .r5 = V .r30 + BitVec.ofNat 64 16 ∧
      s₁.gpr .r6 = V .r27 ∧ s₁.gpr .r7 = BitVec.ofNat 64 (Q V) ∧ s₁.gpr .r12 = s.sp ∧
      (∀ r, r ∉ argRegs → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    crun [mov, BitVec.or_self, h27, h28, h29, h30, h.r28, hsh]
    refine ⟨fun r hr => ?_, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, e, _, _, _, f⟩ := hr
    simp [a, b, c, d, e, f]
  rw [show wholeArgs = [mov .r3 .r29, mov .r4 .r28, .addi .r5 .r30 16, mov .r6 .r27, .lsr .d .r7 .r23 4,
      .addSp .r12 0] ++ ([.load .d .r8 .r12 120] ++ [mov .r9 .r7, .addi .r10 .r31 448]) from rfl]
  refine WP.block_append (WP.mono h₁ fun s₁ ⟨a3, a4, a5, a6, a7, a12, g₁, k₁⟩ => ?_)
  refine WP.block_append (WP.mono (ld_ok (t := .r8) (v := D) (by decide) (by decide) (by decide)
    (by rw [a12, k₁.rd, k₁.wr, hsp]; exact h.hi) (by rw [a12, k₁.mem, hsp]; exact h.hv))
    fun s₂ ⟨h8, g₂, k₂⟩ => ?_)
  have e31 : s₂.gpr .r31 = V .r31 := by
    rw [g₂ _ (by decide), g₁ _ (by decide)]; exact h31
  have e7 : s₂.gpr .r7 = BitVec.ofNat 64 (Q V) := by rw [g₂ _ (by decide)]; exact a7
  crun [mov, BitVec.or_self, e31, e7]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, k₁.trans (k₂.trans ⟨rfl, rfl, rfl, rfl, rfl⟩)⟩
  · simp only [g₂ _ (show Reg.r3 ≠ .r8 by decide)]; exact a3
  · simp only [g₂ _ (show Reg.r4 ≠ .r8 by decide)]; exact a4
  · simp only [g₂ _ (show Reg.r5 ≠ .r8 by decide)]; exact a5
  · simp only [g₂ _ (show Reg.r6 ≠ .r8 by decide)]; exact a6
  · exact h8
  · have hr' := hr
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    obtain ⟨_, _, _, _, _, a, b, c, _⟩ := hr'
    simp only [b, c, ite_false]
    rw [g₂ r a, g₁ r hr]

theorem fitOff (p : Addr) {bound off n : Nat} (hf : p.toNat + bound ≤ 2 ^ 64)
    (hb : bound < 2 ^ 64) (ho : off + n ≤ bound) : (p + BitVec.ofNat 64 off).toNat + n ≤ 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (b := 2 ^ 64) (by omega)]
  have := Nat.mod_le (p.toNat + off) (2 ^ 64)
  omega

theorem st48 (p : Addr) : p + BitVec.ofNat 64 16 + 32 = p + BitVec.ofNat 64 48 := by
  rw [BitVec.add_assoc]; rfl

theorem whole_ok [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] {R : Nat} {D : Addr}
    {s : State} (L : Lay (V .r29) (V .r30) (V .r31)) (h : WholeIn V sp R D s) :
    WP isa whole s (WholeOut V sp R D s) := by
  refine WP.seq (WP.mono (wholeArgs_ok h) fun s₁ ⟨a3, a4, a5, a6, a7, a8, a9, a10, g₁, k₁⟩ => ?_)
  have hq : Q V < 2 ^ 64 := by show (V .r23).toNat / 16 < 2 ^ 64; have := (V .r23).isLt; omega
  have hle : Q V * 16 ≤ (V .r23).toNat := by show (V .r23).toNat / 16 * 16 ≤ _; exact Nat.div_mul_le_self _ _
  have hR : R < 2 ^ 64 := by rcases h.rounds with e | e | e <;> omega
  have he := h.env
  have he₁ : Env V sp s₁ := he.keep (fun r hr => g₁ r (by revert r; decide)) k₁.sp k₁.rd k₁.wr
  have hsrc := h.src
  have hdst := h.dst
  refine WP.call (k := Proof.Gcm.decryptBlocksToContract PPC64LE.abi) SplitBlocks.decryptTo_correct
    (rd := [⟨V .r29, 256⟩, ⟨V .r27, Q V * 16⟩])
    (wr := [⟨V .r30 + BitVec.ofNat 64 16, 48⟩, ⟨D, Q V * 16⟩, ⟨V .r31 + BitVec.ofNat 64 448, 2112⟩]) ?_ ?_ ?_ ?_
  · sig_eval [Proof.Gcm.decryptBlocksToContract, Proof.Gcm.decryptBlocksToSig, Proof.Gcm.decryptBlocksToPre,
      PPC64LE.abi, PPC64LE.argRegs]
    simp only [a3, a4, a5, a6, a7, a8, a9, a10, toNat64 hq, toNat64 hR]
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
  · intro t hrd hwr hsp hf hcs _ hp
    sig_eval [Proof.Gcm.decryptBlocksToContract, Proof.Gcm.decryptBlocksToSig, Proof.Gcm.decryptBlocksToPost,
      PPC64LE.abi, PPC64LE.argRegs] at hp
    simp only [a3, a4, a5, a6, a7, a8, toNat64 hq, toNat64 hR, st48, k₁.mem] at hp
    rw [k₁.mem] at hf
    exact ⟨he₁.of_saved hcs hsp hrd hwr, hrd.trans k₁.rd, hwr.trans k₁.wr, hp.1, hp.2.1, hp.2.2, hf⟩

end

end VG.Proof.AesGcm.PPC64LE.Pass
