module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Blocks
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-OCB on PPC64LE: the functions called

Untrusted: everything here is checked by Lean. Calls of
`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` from their contract
(with `WP.call`): what they need (`BCall`), what they leave (`BPost`), and
that two calls with the same arguments leak the same (`blk_rel`). A block
the call transforms is `ENCIPHER` (or `DECIPHER`) of the key schedule
(`BPost.enc`, `BPost.dec`), as OCB's blocks in memory (`blockAtMem`). As on
AArch64 (`Proof/AesOcb/AArch64/Callee.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem aesWith aesInvWith)
open VG.Proof.Ocb (blockAtMem_of_state stateAt_of_statesAt)

theorem encryptBlocks_noFrames : Impl.Aes.PPC64LE.encryptBlocks.noFrames = true := by decide +kernel
theorem decryptBlocks_noFrames : Impl.Aes.PPC64LE.decryptBlocks.noFrames = true := by decide +kernel

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 64 R).toNat = R :=
  toNat_ofNat_lt (by omega)

theorem callEntry_gpr' (s : State) {r : Reg} (h : r ∉ linkRegs) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr _ h

/-- What a call of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` needs:
the key schedule at `K` for `R` rounds, `n` blocks at `D` and working space
at `S`. -/
structure BCall (s : State) (K D S : Addr) (R n : Nat) : Prop where
  r3 : s.gpr .r3 = K
  r4 : s.gpr .r4 = BitVec.ofNat 64 R
  r5 : s.gpr .r5 = D
  r6 : s.gpr .r6 = BitVec.ofNat 64 n
  r7 : s.gpr .r7 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  kd : (⟨K, 240⟩ : Region).Disjoint ⟨D, 16 * n⟩
  ks : (⟨K, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 2048⟩
  reads : Covers ([⟨K, 240⟩] ++ [⟨D, 16 * n⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨D, 16 * n⟩, ⟨S, 2048⟩] s.wr

/-- What a call of a function with the contract `blocksPPC64LE f` leaves. -/
structure BPost (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (s : State) (K D S : Addr) (R n : Nat)
    (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨D, 16 * n⟩, ⟨S, 2048⟩] s.mem s'.mem
  out : Spec.Aes.statesAt s'.mem D n = (Spec.Aes.statesAt s.mem D n).map (f R (bytesAt s.mem K (16 * (R + 1))))

theorem BCall.n_lt {s : State} {K D S : Addr} {R n : Nat} (h : BCall s K D S R n) : n < 2 ^ 64 := by
  have := h.wrap; omega

theorem BCall.pre {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s : State} {K D S : Addr} {R n : Nat}
    (h : BCall s K D S R n) :
    (Proof.Aes.blocksPPC64LE f).pre (s.callEntry.withRegions [⟨K, 240⟩] [⟨D, 16 * n⟩, ⟨S, 2048⟩]) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat_lt h.n_lt
  simp only [Proof.Aes.blocksPPC64LE, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs), h.r3, h.r4, h.r5, h.r6, h.r7, hR, hn]
  exact ⟨trivial, trivial, h.kd, h.ks, h.ds, h.wrap, h.rounds⟩

theorem blk_call {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksPPC64LE f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksPPC64LE f).post s s')
    (nf : c.noFrames = true) {s : State} {K D S : Addr} {R n : Nat} (h : BCall s K D S R n) :
    WP isa (.call name c) s (BPost f s K D S R n) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat_lt h.n_lt
  refine WP.call (k := Proof.Aes.blocksPPC64LE f) ok (rd := [⟨K, 240⟩]) (wr := [⟨D, 16 * n⟩, ⟨S, 2048⟩])
    h.pre h.reads h.writes ?_ nf
  intro s' hrd hwr hsp hf hsaved _ hpost
  simp only [Proof.Aes.blocksPPC64LE, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
    h.r3, h.r4, h.r5, h.r6, hR, hn] at hpost
  exact ⟨hrd, hwr, hsp, hsaved, hf, hpost⟩

/-- Block `i` after `vg_aes_encrypt_blocks`. -/
theorem BPost.enc {s s' : State} {K D S : Addr} {R n : Nat} (h : BPost Spec.Aes.cipher s K D S R n s') {i : Nat}
    (hi : i < n) :
    blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      aesWith R (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) :=
  blockAtMem_of_state _ (stateAt_of_statesAt h.out hi)

/-- Block `i` after `vg_aes_decrypt_blocks`. -/
theorem BPost.dec {s s' : State} {K D S : Addr} {R n : Nat} (h : BPost Spec.Aes.invCipher s K D S R n s') {i : Nat}
    (hi : i < n) :
    blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      aesInvWith R (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) :=
  blockAtMem_of_state _ (stateAt_of_statesAt h.out hi)

/-- The one block of a call on one block. -/
theorem BPost.enc0 {s s' : State} {K D S : Addr} {R : Nat} (h : BPost Spec.Aes.cipher s K D S R 1 s') :
    blockAtMem s'.mem D = aesWith R (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem D) := by
  have := h.enc (i := 0) (by decide)
  simpa using this

theorem blk_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksPPC64LE f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksPPC64LE f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksPPC64LE f).pre (Proof.Aes.blocksPPC64LE f).pub c)
    {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K D S : Addr, ∃ R n : Nat,
      BCall s₁ K D S R n ∧ BCall s₂ K D S R n ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call name c) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨K, D, S, R, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine RelCT.call (P := fun a b => a = s₁ ∧ b = s₂) ok ct [⟨K, 240⟩] [⟨D, 16 * n⟩, ⟨S, 2048⟩]
    (fun a b hab => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  obtain ⟨rfl, rfl⟩ := hab
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.blocksPPC64LE, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_gpr' _ (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.r7 ∉ linkRegs),
    h₁.r3, h₁.r4, h₁.r5, h₁.r6, h₁.r7, h₂.r3, h₂.r4, h₂.r5, h₂.r6, h₂.r7, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesOcb.PPC64LE
