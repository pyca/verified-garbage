import VerifiedGarbage.Proof.AesOcb.X86_64.Words
import VerifiedGarbage.Proof.AesCcm.X86_64.Callee
import VerifiedGarbage.Proof.Aes.X86_64.BlocksVariant

/-!
# AES-OCB on x86-64: the functions called

Untrusted: everything here is checked by Lean. Calls of
`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` (of any implementation
`v`) and of `vg_aes_expand_key` from their contracts (with `WP.call`): what
they need (`BCall`, `KCall`), what they leave (`BPost`, `KPost`), and that two
calls with the same arguments leak the same (`blk_rel`, `key_rel`). A block
the call transforms is `ENCIPHER` (or `DECIPHER`) of the key schedule
(`BPost.enc`, `BPost.dec`), as OCB's blocks in memory (`blockAtMem`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem aesWith aesInvWith)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (bytesAt_frame callEntry_frame disj_below toNat_rounds toNat_ofNat_of_lt)

/-! ## States and blocks -/

theorem bytesAt_toList (m : Mem) (p : Addr) : bytesAt m p 16 = (Spec.Aes.stateAt m p).toList := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ h₂
  simp [bytesAt, Spec.Aes.stateAt]

theorem stateAt_eq (m : Mem) (p : Addr) :
    Spec.Aes.stateAt m p = Vector.ofFn fun i => (Spec.Ocb.toBytes (blockAtMem m p)).getD i.1 0 := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (by simp [bytesAt])]
  apply Vector.ext
  intro i hi
  simp [Spec.Aes.stateAt, bytesAt, List.getD_eq_getElem?_getD, hi]

/-- The block at `p`, after a function of states replaced the state there. -/
theorem blockAtMem_of_state {m m' : Mem} {p : Addr} (g : Spec.Aes.State → Spec.Aes.State)
    (h : Spec.Aes.stateAt m' p = g (Spec.Aes.stateAt m p)) :
    blockAtMem m' p = Spec.Ocb.ofBytes (g (Vector.ofFn fun i => (Spec.Ocb.toBytes (blockAtMem m p)).getD i.1 0)).toList := by
  rw [blockAtMem, bytesAt_toList, h, stateAt_eq]

theorem stateAt_of_statesAt {m m' : Mem} {D : Addr} {n : Nat} {g : Spec.Aes.State → Spec.Aes.State}
    (h : Spec.Aes.statesAt m' D n = (Spec.Aes.statesAt m D n).map g) {i : Nat} (hi : i < n) :
    Spec.Aes.stateAt m' (D + BitVec.ofNat 64 (16 * i)) = g (Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16 * i))) := by
  have := congrArg (·[i]?) h
  simpa [Spec.Aes.statesAt, hi] using this

/-! ## `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` -/

/-- What a call of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` needs:
the key schedule at `K` for `R` rounds, `n` blocks at `D` and working space
at `S`. -/
structure BCall (s : State) (K D S : Addr) (R n : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = D
  rcx : s.gpr .rcx = BitVec.ofNat 64 n
  r8 : s.gpr .r8 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  kd : (⟨K, 240⟩ : Region).Disjoint ⟨D, 16 * n⟩
  ks : (⟨K, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 2048⟩
  stkK : (below (s.gpr .rsp) 8).Disjoint ⟨K, 240⟩
  stkD : (below (s.gpr .rsp) 8).Disjoint ⟨D, 16 * n⟩
  stkS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 2048⟩
  reads : Covers ([⟨K, 240⟩] ++ [⟨D, 16 * n⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨D, 16 * n⟩, ⟨S, 2048⟩] s.wr

/-- What a call of a function with the contract `blocksX86_64 f` leaves. -/
structure BPost (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (s : State) (K D S : Addr) (R n : Nat)
    (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨D, 16 * n⟩, ⟨S, 2048⟩, below (s.gpr .rsp) 8] s.mem s'.mem
  out : Spec.Aes.statesAt s'.mem D n = (Spec.Aes.statesAt s.mem D n).map (f R (bytesAt s.mem K (16 * (R + 1))))

theorem BCall.pre {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s : State} {K D S : Addr} {R n : Nat}
    (h : BCall s K D S R n) :
    (Proof.Aes.blocksX86_64 f).pre (s.callEntry.withRegions [⟨K, 240⟩] [⟨D, 16 * n⟩, ⟨S, 2048⟩]) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat_of_lt (show n < 2 ^ 64 by have := h.wrap; omega)
  simp only [Proof.Aes.blocksX86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hn]
  exact ⟨trivial, trivial, h.kd, h.ks, h.ds, h.stkD, h.stkS, h.wrap, h.rounds⟩

theorem blk_call {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (nosp : NoSp c) (depth : c.depth = 0) {s : State} {K D S : Addr} {R n : Nat} (h : BCall s K D S R n) :
    WP isa (.call name c) s (BPost f s K D S R n) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat_of_lt (show n < 2 ^ 64 by have := h.wrap; omega)
  refine WP.call (k := Proof.Aes.blocksX86_64 f) ok nosp (by rw [depth]; decide)
    (rd := [⟨K, 240⟩]) (wr := [⟨D, 16 * n⟩, ⟨S, 2048⟩]) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [depth] at hf
  simp only [Proof.Aes.blocksX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, hR, hn, hm₂] at hpost
  have fE := callEntry_frame s
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with rfl | rfl | rfl <;> decide
  have eK := bytesAt_frame fE (p := K) (n := 16 * (R + 1))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.stkK.sub_right (Region.sub_prefix hRb)).symm) (by omega)
  have eD : Spec.Aes.statesAt s.callEntry.mem D n = Spec.Aes.statesAt s.mem D n := by
    simp only [Spec.Aes.statesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    simp only [Spec.Aes.stateAt]
    apply Vector.ext
    intro j hj
    simp only [Vector.getElem_ofFn]
    rw [Offset.add_add]
    exact fE.bytes (R := ⟨D, 16 * n⟩) (disj_below h.stkD) (by show 16 * n ≤ 2 ^ 64; have := h.wrap; omega) (by show 16 * i + j < 16 * n; omega)
  rw [eK, eD] at hpost
  exact ⟨hrd, hwr, hcs, by simpa using hf, hpost⟩

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

theorem blk_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86_64 f).pre (Proof.Aes.blocksX86_64 f).pub c)
    {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K D S : Addr, ∃ R n : Nat,
      BCall s₁ K D S R n ∧ BCall s₂ K D S R n ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call name c) fun _ _ => True := by
  refine RelCT.callEx ok ct fun s₁ s₂ hp => ?_
  obtain ⟨K, D, S, R, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Aes.blocksX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_expand_key` -/

/-- What a call of `vg_aes_expand_key` needs: the key `Kp` of `KL` bytes,
the schedule `C` and the working space `S`. -/
structure KCall (s : State) (Kp C S : Addr) (KL : Nat) : Prop where
  rdi : s.gpr .rdi = Kp
  rsi : s.gpr .rsi = BitVec.ofNat 64 KL
  rdx : s.gpr .rdx = C
  rcx : s.gpr .rcx = S
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32
  kc : (⟨Kp, KL⟩ : Region).Disjoint ⟨C, 240⟩
  ks : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 512⟩
  cs : (⟨C, 240⟩ : Region).Disjoint ⟨S, 512⟩
  stkK : (below (s.gpr .rsp) 8).Disjoint ⟨Kp, KL⟩
  stkC : (below (s.gpr .rsp) 8).Disjoint ⟨C, 240⟩
  stkS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 512⟩
  reads : Covers ([⟨Kp, KL⟩] ++ [⟨C, 240⟩, ⟨S, 512⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 240⟩, ⟨S, 512⟩] s.wr

/-- What a call of `vg_aes_expand_key` leaves. -/
structure KPost (s : State) (Kp C S : Addr) (KL : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 240⟩, ⟨S, 512⟩, below (s.gpr .rsp) 8] s.mem s'.mem
  out : bytesAt s'.mem C (16 * (Spec.Aes.rounds (KL / 4) + 1)) = Spec.Aes.expandKey (bytesAt s.mem Kp KL)

theorem KCall.pre {s : State} {Kp C S : Addr} {KL : Nat} (h : KCall s Kp C S KL) :
    Proof.Aes.expandKeyX86_64.pre (s.callEntry.withRegions [⟨Kp, KL⟩] [⟨C, 240⟩, ⟨S, 512⟩]) := by
  have hK := toNat_ofNat_of_lt (n := KL) (by rcases h.klen with h | h | h <;> omega)
  simp only [Proof.Aes.expandKeyX86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, hK]
  exact ⟨trivial, trivial, h.kc, h.ks, h.cs, h.stkC, h.stkS, h.klen⟩

theorem key_call (v : BlocksImpl) {s : State} {Kp C S : Addr} {KL : Nat} (h : KCall s Kp C S KL) :
    WP isa (.call v.expand.name v.expand.code) s (KPost s Kp C S KL) := by
  have hK := toNat_ofNat_of_lt (n := KL) (by rcases h.klen with h | h | h <;> omega)
  refine WP.call (k := Proof.Aes.expandKeyX86_64) v.expandOk v.expandNosp
    (by rw [v.expandDepth]; decide) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [v.expandDepth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
  simp only [Proof.Aes.expandKeyX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, h.rdx, hK] at hpost
  rw [← hm₂, hpost, bytesAt_frame (callEntry_frame s) (disj_below h.stkK)
    (by rcases h.klen with h | h | h <;> omega)]

theorem key_rel (v : BlocksImpl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ Kp C S : Addr, ∃ KL : Nat,
      KCall s₁ Kp C S KL ∧ KCall s₂ Kp C S KL ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call v.expand.name v.expand.code) fun _ _ => True := by
  refine RelCT.callEx v.expandOk v.expandCt fun s₁ s₂ hp => ?_
  obtain ⟨Kp, C, S, KL, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Aes.expandKeyX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesOcb.X86_64
