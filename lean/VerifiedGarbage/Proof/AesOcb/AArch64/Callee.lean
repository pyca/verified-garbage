module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
public import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant
public import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

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

@[expose] public section

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
the key schedule at `K` for `R` rounds, `n` blocks at `D` and `N` bytes of
working space at `S`. -/
structure BCall (s : State) (K D S : Addr) (R n : Nat) (N : Nat := 2048) : Prop where
  x0 : s.gpr .x0 = K
  x1 : s.gpr .x1 = BitVec.ofNat 64 R
  x2 : s.gpr .x2 = D
  x3 : s.gpr .x3 = BitVec.ofNat 64 n
  x4 : s.gpr .x4 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  kd : (⟨K, 240⟩ : Region).Disjoint ⟨D, 16 * n⟩
  ks : (⟨K, 240⟩ : Region).Disjoint ⟨S, N⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, N⟩
  reads : Covers ([⟨K, 240⟩] ++ [⟨D, 16 * n⟩, ⟨S, N⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨D, 16 * n⟩, ⟨S, N⟩] s.wr

/-- What a call of a function with the contract `blocksAArch64 f` leaves. -/
structure BPost (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (s : State) (K D S : Addr) (R n : Nat)
    (s' : State) (N : Nat := 2048) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨D, 16 * n⟩, ⟨S, N⟩] s.mem s'.mem
  out : Spec.Aes.statesAt s'.mem D n = (Spec.Aes.statesAt s.mem D n).map (f R (bytesAt s.mem K (16 * (R + 1))))

theorem BCall.n_lt {s : State} {K D S : Addr} {R n N : Nat} (h : BCall s K D S R n N) : n < 2 ^ 64 := by
  have := h.wrap; omega_using [this]

private theorem covers_lastB {xs T : List Region} {S : Addr} {M N : Nat} (h : Covers (xs ++ [⟨S, N⟩]) T)
    (hle : M ≤ N) : Covers (xs ++ [⟨S, M⟩]) T := by
  intro a n ⟨r, hr, hc⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact h a n ⟨r, List.mem_append_left _ hr, hc⟩
  · rw [List.mem_singleton] at hr; subst hr
    refine h a n ⟨⟨S, N⟩, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    simp only [Region.Contains] at hc ⊢; omega

/-- `BCall` with less working space, a prefix of it. -/
theorem BCall.shrink {s : State} {K D S : Addr} {R n M N : Nat} (h : BCall s K D S R n N) (hle : M ≤ N) :
    BCall s K D S R n M :=
  { h with
    ks := h.ks.sub_right (Region.sub_prefix hle)
    ds := h.ds.sub_right (Region.sub_prefix hle)
    reads := covers_lastB (xs := [⟨K, 240⟩, ⟨D, 16 * n⟩]) h.reads hle
    writes := covers_lastB (xs := [⟨D, 16 * n⟩]) h.writes hle }

theorem BCall.pre {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s : State} {K D S : Addr} {R n N : Nat}
    (h : BCall s K D S R n N) :
    (Proof.Aes.blocksAArch64With N f).pre (s.callEntry.withRegions [⟨K, 240⟩] [⟨D, 16 * n⟩, ⟨S, N⟩]) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat_lt h.n_lt
  simp only [Proof.Aes.blocksAArch64With, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4,
    h.x0, h.x1, h.x2, h.x3, h.x4, hR, hn]
  exact ⟨trivial, trivial, h.kd, h.ks, h.ds, h.wrap, h.rounds⟩

/-- A call of a function proven with `M` bytes of working space, given `N`,
at least as many. -/
theorem blk_callLe {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    {M N : Nat}
    (ok : ∀ s, (Proof.Aes.blocksAArch64With M f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64With M f).post s s')
    (nf : c.noFrames = true) (hle : M ≤ N) {s : State} {K D S : Addr} {R n : Nat} (h : BCall s K D S R n N) :
    WP isa (.call name c) s fun s' => BPost f s K D S R n s' N := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat_lt h.n_lt
  refine WP.call (k := Proof.Aes.blocksAArch64With M f) ok (rd := [⟨K, 240⟩])
    (wr := [⟨D, 16 * n⟩, ⟨S, M⟩]) (h.shrink hle).pre (h.shrink hle).reads (h.shrink hle).writes ?_ nf
  intro s' hrd hwr hsp hf hsaved _ hpost
  simp only [Proof.Aes.blocksAArch64With, Proof.Aes.blocksAArch64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, h.x0, h.x1, h.x2, h.x3, hR, hn]
    at hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf.sub fun r hr => ?_, hpost⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨⟨S, N⟩, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix hle⟩

theorem blk_call {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (nf : c.noFrames = true) {s : State} {K D S : Addr} {R n : Nat} (h : BCall s K D S R n) :
    WP isa (.call name c) s (BPost f s K D S R n) :=
  blk_callLe (M := 2048) ok nf (Nat.le_refl _) h

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

theorem blk_relLe {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    {M N : Nat}
    (ok : ∀ s, (Proof.Aes.blocksAArch64With M f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64With M f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksAArch64With M f).pre (Proof.Aes.blocksAArch64With M f).pub c)
    (hle : M ≤ N) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K D S : Addr, ∃ R n : Nat,
      BCall s₁ K D S R n N ∧ BCall s₂ K D S R n N ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call name c) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨K, D, S, R, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine RelCT.call (P := fun a b => a = s₁ ∧ b = s₂) ok ct [⟨K, 240⟩] [⟨D, 16 * n⟩, ⟨S, M⟩]
    (fun a b hab => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  obtain ⟨rfl, rfl⟩ := hab
  refine ⟨(h₁.shrink hle).pre, (h₂.shrink hle).pre, ?_, (h₁.shrink hle).reads, (h₁.shrink hle).writes,
    (h₂.shrink hle).reads, (h₂.shrink hle).writes⟩
  simp only [Proof.Aes.blocksAArch64With, Proof.Aes.blocksAArch64, State.withRegions_gpr, State.withRegions_sp,
    State.callEntry_sp, callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₁.x4, h₂.x0, h₂.x1, h₂.x2, h₂.x3, h₂.x4, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem blk_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksAArch64 f).pre (Proof.Aes.blocksAArch64 f).pub c)
    {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K D S : Addr, ∃ R n : Nat,
      BCall s₁ K D S R n ∧ BCall s₂ K D S R n ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call name c) fun _ _ => True :=
  blk_relLe (M := 2048) ok ct (Nat.le_refl _) h

end VG.Proof.AesOcb.AArch64
