import VerifiedGarbage.Proof.AesOcb.AArch64.Words
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant
import VerifiedGarbage.Proof.Ocb.State

/-!
# AES-OCB on AArch64: the functions called

Untrusted: everything here is checked by Lean. Calls of
`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` (of any implementation
`v`) from their contract (with `WP.call`): what they need (`BCall`), what
they leave (`BPost`), and that two calls with the same arguments leak the
same (`blk_rel`). A block the call transforms is `ENCIPHER` (or `DECIPHER`)
of the key schedule (`BPost.enc`, `BPost.dec`), as OCB's blocks in memory
(`blockAtMem`). `vg_aes_expand_key_scratch` is called as AES-GCM calls it
(`keyImpl`, with `Proof.AesGcm.AArch64.key_call`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem aesWith aesInvWith)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (toNat_ofNat_lt toNat_rounds callEntry_x0 callEntry_x1 callEntry_x2 callEntry_x3
  callEntry_x4)
open VG.Proof.Ocb (blockAtMem_of_state stateAt_of_statesAt)

/-- The implementation of `vg_aes_expand_key_scratch` that goes with `v`, as AES-GCM's
proofs take it. -/
def keyImpl (v : BlocksImpl) : Proof.AesGcm.AArch64.KeyImpl where
  fn := ⟨v.expand.name, v.expand.code⟩
  noFrames := v.expandNoFrames
  ok := v.expandOk
  ct := v.expandCt
  keepsV := v.expandKeepsV

/-- What a call of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` needs:
the key schedule at `K` for `R` rounds, `n` blocks at `D` and working space
at `S`. -/
structure BCall (s : State) (K D S : Addr) (R n : Nat) : Prop where
  x0 : s.gpr .x0 = K
  x1 : s.gpr .x1 = BitVec.ofNat 64 R
  x2 : s.gpr .x2 = D
  x3 : s.gpr .x3 = BitVec.ofNat 64 n
  x4 : s.gpr .x4 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  kd : (⟨K, 240⟩ : Region).Disjoint ⟨D, 16 * n⟩
  ks : (⟨K, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 2048⟩
  reads : Covers ([⟨K, 240⟩] ++ [⟨D, 16 * n⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨D, 16 * n⟩, ⟨S, 2048⟩] s.wr

/-- What a call of a function with the contract `blocksAArch64 f` leaves. -/
structure BPost (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (s : State) (K D S : Addr) (R n : Nat)
    (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨D, 16 * n⟩, ⟨S, 2048⟩] s.mem s'.mem
  out : Spec.Aes.statesAt s'.mem D n = (Spec.Aes.statesAt s.mem D n).map (f R (bytesAt s.mem K (16 * (R + 1))))

theorem BCall.n_lt {s : State} {K D S : Addr} {R n : Nat} (h : BCall s K D S R n) : n < 2 ^ 64 := by
  have := h.wrap; omega

theorem BCall.pre {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s : State} {K D S : Addr} {R n : Nat}
    (h : BCall s K D S R n) :
    (Proof.Aes.blocksAArch64 f).pre (s.callEntry.withRegions [⟨K, 240⟩] [⟨D, 16 * n⟩, ⟨S, 2048⟩]) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat_lt h.n_lt
  simp only [Proof.Aes.blocksAArch64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4,
    h.x0, h.x1, h.x2, h.x3, h.x4, hR, hn]
  exact ⟨trivial, trivial, h.kd, h.ks, h.ds, h.wrap, h.rounds⟩

theorem blk_call {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (nf : c.noFrames = true) {s : State} {K D S : Addr} {R n : Nat} (h : BCall s K D S R n) :
    WP isa (.call name c) s (BPost f s K D S R n) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat_lt h.n_lt
  refine WP.call (k := Proof.Aes.blocksAArch64 f) ok (rd := [⟨K, 240⟩])
    (wr := [⟨D, 16 * n⟩, ⟨S, 2048⟩]) h.pre h.reads h.writes ?_ nf
  intro s' hrd hwr hsp hf hsaved _ hpost
  simp only [Proof.Aes.blocksAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, h.x0, h.x1, h.x2, h.x3, hR, hn] at hpost
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
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksAArch64 f).pre (Proof.Aes.blocksAArch64 f).pub c)
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
  simp only [Proof.Aes.blocksAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₁.x4, h₂.x0, h₂.x1, h₂.x2, h₂.x3, h₂.x4, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesOcb.AArch64
