import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksVerified
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerifyCT
import VerifiedGarbage.Proof.Framework.X86_64.Frame

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call`. -/
section

/-!
# AES-GCM on x86-64: calling `vg_aes_gcm_encrypt_blocks` and `_decrypt_blocks`

Untrusted: everything here is checked by Lean. What a call of either needs,
from a state whose `rsp` points to `scratch` (pushed in a frame), and what
it leaves (`blk_call`), from its contract (with `WP.call`); and that two
calls with the same public arguments leak the same (`blk_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ctr32 aesWith)

/-- What a call needs, from a state `s` with `scratch` at `rsp`: the key
context at `K` for `R` rounds, the counter block at `C`, `Y` at `Y`, `q`
blocks at `D` and working space at `S`. -/
structure BlkCall (s : State) (K C Y D S : Addr) (R q : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = C
  rcx : s.gpr .rcx = Y
  r8 : s.gpr .r8 = D
  r9 : s.gpr .r9 = BitVec.ofNat 64 q
  arg : s.mem.readW (s.gpr .rsp) 64 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  w_k : K.toNat + 256 ≤ 2 ^ 64
  w_c : C.toNat + 16 ≤ 2 ^ 64
  w_y : Y.toNat + 16 ≤ 2 ^ 64
  w_d : D.toNat + q * 16 ≤ 2 ^ 64
  w_s : S.toNat + 2112 ≤ 2 ^ 64
  w_sp : (s.gpr .rsp - 8).toNat + 16 ≤ 2 ^ 64
  k_c : (⟨K, 256⟩ : Region).Disjoint ⟨C, 16⟩
  k_y : (⟨K, 256⟩ : Region).Disjoint ⟨Y, 16⟩
  k_d : (⟨K, 256⟩ : Region).Disjoint ⟨D, q * 16⟩
  k_s : (⟨K, 256⟩ : Region).Disjoint ⟨S, 2112⟩
  c_y : (⟨C, 16⟩ : Region).Disjoint ⟨Y, 16⟩
  c_d : (⟨C, 16⟩ : Region).Disjoint ⟨D, q * 16⟩
  c_s : (⟨C, 16⟩ : Region).Disjoint ⟨S, 2112⟩
  y_d : (⟨Y, 16⟩ : Region).Disjoint ⟨D, q * 16⟩
  y_s : (⟨Y, 16⟩ : Region).Disjoint ⟨S, 2112⟩
  d_s : (⟨D, q * 16⟩ : Region).Disjoint ⟨S, 2112⟩
  /-- The stack: `scratch` on it, and the return addresses of the call and of
  its calls, in the 24 bytes from `rsp - 16`. -/
  t_k : (⟨s.gpr .rsp - 16, 24⟩ : Region).Disjoint ⟨K, 256⟩
  t_c : (⟨s.gpr .rsp - 16, 24⟩ : Region).Disjoint ⟨C, 16⟩
  t_y : (⟨s.gpr .rsp - 16, 24⟩ : Region).Disjoint ⟨Y, 16⟩
  t_d : (⟨s.gpr .rsp - 16, 24⟩ : Region).Disjoint ⟨D, q * 16⟩
  t_s : (⟨s.gpr .rsp - 16, 24⟩ : Region).Disjoint ⟨S, 2112⟩
  reads : Covers ([⟨K, 256⟩, ⟨s.gpr .rsp, 8⟩] ++ [⟨C, 16⟩, ⟨Y, 16⟩, ⟨D, q * 16⟩, ⟨S, 2112⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨Y, 16⟩, ⟨D, q * 16⟩, ⟨S, 2112⟩] s.wr

theorem sep_of_disj {a b : Addr} {n k : Nat} (h : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) : Mem.Sep a n b k :=
  fun x h₁ h₂ => h x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)

namespace BlkCall

variable {s : State} {K C Y D S : Addr} {R q : Nat} (h : VG.Proof.AesGcm.X86_64.BlkCall s K C Y D S R q)
include h

/-- The regions the callee may read and write. -/
abbrev rd (s : State) (K : Addr) : List Region := [⟨K, 256⟩, ⟨s.gpr .rsp, 8⟩]
abbrev wr (C Y D S : Addr) (q : Nat) : List Region := [⟨C, 16⟩, ⟨Y, 16⟩, ⟨D, q * 16⟩, ⟨S, 2112⟩]

omit h in
theorem stackArgAddr_eq (rd wr : List Region) : stackArgAddr (s.callEntry.withRegions rd wr) 0 = s.gpr .rsp := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp]
  exact BitVec.sub_add_cancel _ _

omit h in
/-- The stack the callee uses is in the 24 bytes below `rsp + 8`. -/
theorem below_sub : Region.Sub (below (s.gpr .rsp - 8) 8) ⟨s.gpr .rsp - 16, 24⟩ := by
  have e : s.gpr .rsp - 8 - BitVec.ofNat 64 8 = s.gpr .rsp - 16 := by
    rw [← Offset.sub_add_eq]; rfl
  show Region.Sub ⟨s.gpr .rsp - 8 - BitVec.ofNat 64 8, 8⟩ _
  rw [e]; exact Region.sub_prefix (by decide)

omit h in
theorem ret_sub : Region.Sub ⟨s.gpr .rsp - 8, 8⟩ ⟨s.gpr .rsp - 16, 24⟩ := by
  have e : s.gpr .rsp - 8 = s.gpr .rsp - 16 + BitVec.ofNat 64 8 := by
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl]
    exact Offset.sub_ofNat_eq _ (by decide)
  rw [e]; exact Offset.sub_base _ (by decide)

omit h in
theorem arg_sub : Region.Sub ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsp - 16, 24⟩ := by
  have e : s.gpr .rsp = s.gpr .rsp - 16 + BitVec.ofNat 64 16 := (BitVec.sub_add_cancel _ _).symm
  conv => lhs; rw [e]
  exact Offset.sub_base _ (by decide)

theorem arg_eq : stackArg (s.callEntry.withRegions (VG.Proof.AesGcm.X86_64.BlkCall.rd s K) (VG.Proof.AesGcm.X86_64.BlkCall.wr C Y D S q)) 0 = S := by
  have hsa := VG.Proof.AesGcm.X86_64.BlkCall.stackArgAddr_eq (s := s) (VG.Proof.AesGcm.X86_64.BlkCall.rd s K) (VG.Proof.AesGcm.X86_64.BlkCall.wr C Y D S q)
  have sep : Mem.Sep (s.gpr .rsp) (64 / 8) (s.gpr .rsp - 8) (64 / 8) := by
    have := Offset.sep_below (s.gpr .rsp) 8 (a := 0) (n := 8) (b := 8) (k := 8) (by decide) (by decide)
      (.inr (by decide)) (by decide) (by decide)
    simpa using this
  unfold stackArg; rw [hsa, State.withRegions_mem, State.callEntry_mem, Mem.readW_writeW_sep sep (by decide), h.arg]

theorem pre : Proof.AesGcm.blocksPre (s.callEntry.withRegions (VG.Proof.AesGcm.X86_64.BlkCall.rd s K) (VG.Proof.AesGcm.X86_64.BlkCall.wr C Y D S q)) := by
  have hq : (BitVec.ofNat 64 q).toNat = q := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.w_d; omega)
  have hR : (BitVec.ofNat 64 R).toNat = R := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rcases h.rounds with h | h | h <;> omega)
  have hsa := VG.Proof.AesGcm.X86_64.BlkCall.stackArgAddr_eq (s := s) (VG.Proof.AesGcm.X86_64.BlkCall.rd s K) (VG.Proof.AesGcm.X86_64.BlkCall.wr C Y D S q)
  have harg := h.arg_eq
  simp only [Proof.AesGcm.blocksPre, Proof.AesGcm.args, Proof.AesGcm.arg, Proof.AesGcm.ret, Proof.AesGcm.stk,
    Proof.AesGcm.rounds, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.callEntry_rsp,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hq, hR, hsa, harg, Nat.mul_one]
  have bs := VG.Proof.AesGcm.X86_64.BlkCall.below_sub (s := s)
  have rs := VG.Proof.AesGcm.X86_64.BlkCall.ret_sub (s := s)
  have as := VG.Proof.AesGcm.X86_64.BlkCall.arg_sub (s := s)
  refine ⟨trivial, trivial, h.k_c, h.k_y, h.k_d, h.k_s, h.c_y, h.c_d, h.c_s, (h.t_c.sub_left as).symm, h.y_d, h.y_s,
    (h.t_y.sub_left as).symm, h.d_s, (h.t_d.sub_left as).symm, (h.t_s.sub_left as).symm,
    h.t_c.sub_left rs, h.t_y.sub_left rs, h.t_d.sub_left rs, h.t_s.sub_left rs,
    h.t_k.sub_left bs, h.t_c.sub_left bs, h.t_y.sub_left bs, h.t_d.sub_left bs, h.t_s.sub_left bs,
    h.w_k, h.w_c, h.w_y, h.w_d, h.w_s, h.w_sp, h.rounds⟩

end BlkCall

theorem ctr_nosp_all (c : Proof.Aes.X86_64.Ctr32Impl) :
    c.callee.code.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]; intro i hi; simp [c.nosp i hi]

theorem gh_nosp_all (g : GhashImpl) : g.fn.code.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]; intro i hi; simp [g.nosp i hi]

theorem nosp_of_all {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c :=
  nosp_of (by rw [← Code.allInstrs_eq]; exact h)

section
variable (v : GcmImpl) (st : Option StitchImpl)

theorem encryptBlocks_nosp : NoSp (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc))) := by
  have hc := VG.Proof.AesGcm.X86_64.ctr_nosp_all v.ctr
  have hg := VG.Proof.AesGcm.X86_64.gh_nosp_all v.gh
  refine VG.Proof.AesGcm.X86_64.nosp_of_all ?_
  have hh := StitchImpl.head_nosp st fun i => i.encP
  simp only [Blocks.encrypt, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.allInstrs,
    GcmImpl.callees, hh, hc, hg, Bool.true_and, Bool.and_true, Bool.false_eq_true, ite_false,
    ite_true]; decide +kernel

theorem decryptBlocks_nosp : NoSp (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec))) := by
  have hc := VG.Proof.AesGcm.X86_64.ctr_nosp_all v.ctr
  have hg := VG.Proof.AesGcm.X86_64.gh_nosp_all v.gh
  refine VG.Proof.AesGcm.X86_64.nosp_of_all ?_
  have hh := StitchImpl.head_nosp st fun i => i.decP
  simp only [Blocks.decrypt, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.allInstrs,
    GcmImpl.callees, hh, hc, hg, Bool.true_and, Bool.and_true, Bool.false_eq_true, ite_false,
    ite_true]; decide +kernel

theorem encryptBlocks_depth : (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc))).depth = 1 := by
  have hh := StitchImpl.head_depth st fun i => i.encP
  simp only [Blocks.encrypt, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall,
    Code.depth, GcmImpl.callees, hh, v.ctr.depth, v.gh.depth, Bool.false_eq_true, ite_false, ite_true]; decide

theorem decryptBlocks_depth : (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec))).depth = 1 := by
  have hh := StitchImpl.head_depth st fun i => i.decP
  simp only [Blocks.decrypt, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall,
    Code.depth, GcmImpl.callees, hh, v.ctr.depth, v.gh.depth, Bool.false_eq_true, ite_false, ite_true]; decide

end

/-- What a call leaves, besides its result. -/
structure BlkPost (s : State) (C Y D S : Addr) (q : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame (BlkCall.wr C Y D S q ++ [below (s.gpr .rsp) 16]) s.mem s'.mem

namespace BlkCall

variable {s : State} {K C Y D S : Addr} {R q : Nat} (h : VG.Proof.AesGcm.X86_64.BlkCall s K C Y D S R q)
include h

/-- The values the call reads, at its entry, after the return address is stored. -/
theorem entry_eqs :
    Spec.Aes.bytesAt s.callEntry.mem K (16 * (R + 1)) = Spec.Aes.bytesAt s.mem K (16 * (R + 1)) ∧
      blockAt s.callEntry.mem C = blockAt s.mem C ∧ blockAt s.callEntry.mem Y = blockAt s.mem Y ∧
      blocksAt s.callEntry.mem D q = blocksAt s.mem D q ∧
      blockAt s.callEntry.mem (K + 240) = blockAt s.mem (K + 240) := by
  have fE := callEntry_frame s
  have rs : Region.Sub (below (s.gpr .rsp) 8) ⟨s.gpr .rsp - 16, 24⟩ := VG.Proof.AesGcm.X86_64.BlkCall.ret_sub (s := s)
  have hRb : 16 * (R + 1) ≤ 256 := by rcases h.rounds with h | h | h <;> subst h <;> decide
  refine ⟨bytesAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((h.t_k.sub_left rs).sub_right (Region.sub_prefix hRb)).symm) (by have := h.w_k; omega),
    blockAt_frame fE (disj_below (h.t_c.sub_left rs)), blockAt_frame fE (disj_below (h.t_y.sub_left rs)),
    blocksAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [Nat.mul_comm]; exact (h.t_d.sub_left rs).symm) (by have := h.w_d; omega),
    blockAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((h.t_k.sub_left rs).sub_right (Offset.sub_base (d := 240) _ (by decide))).symm)⟩

end BlkCall

/-- A call of `vg_aes_gcm_encrypt_blocks`. -/
theorem blkE_call (v : GcmImpl) {s : State} {K C Y D S : Addr} {R q : Nat} (h : VG.Proof.AesGcm.X86_64.BlkCall s K C Y D S R q) :
    WP isa (.call v.callees.enc.name v.callees.enc.code) s fun s' => VG.Proof.AesGcm.X86_64.BlkPost s C Y D S q s' ∧
      blocksAt s'.mem D q = ctr32 (aesWith R (Spec.Aes.bytesAt s.mem K (16 * (R + 1)))) (blockAt s.mem C)
        (blocksAt s.mem D q) ∧
      blockAt s'.mem C = Nat.repeat Spec.Gcm.inc32 q (blockAt s.mem C) ∧
      blockAt s'.mem Y = ghashFrom (blockAt s.mem (K + 240)) (blockAt s.mem Y) (blocksAt s'.mem D q) := by
  have hq : (BitVec.ofNat 64 q).toNat = q := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.w_d; omega)
  have hR : (BitVec.ofNat 64 R).toNat = R := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rcases h.rounds with h | h | h <;> omega)
  refine WP.call (k := Proof.AesGcm.encryptBlocksX86_64) (encryptBlocks_correct v v.stitch)
    (VG.Proof.AesGcm.X86_64.encryptBlocks_nosp v v.stitch) (by rw [VG.Proof.AesGcm.X86_64.encryptBlocks_depth]; decide)
    (rd := BlkCall.rd s K) (wr := BlkCall.wr C Y D S q) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [VG.Proof.AesGcm.X86_64.encryptBlocks_depth] at hf
  obtain ⟨eK, eC, eY, eD, eH⟩ := h.entry_eqs
  simp only [Proof.AesGcm.encryptBlocksX86_64, Spec.Gcm.ctxCiph, Spec.Gcm.ctxH, State.withRegions_gpr,
    State.withRegions_mem, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hq, hR, hm₂,
    eK, eC, eY, eD, eH] at hpost
  exact ⟨⟨hrd, hwr, hcs, hf⟩, hpost.1, hpost.2.1, by rw [hpost.1]; exact hpost.2.2⟩

/-- A call of `vg_aes_gcm_decrypt_blocks`. -/
theorem blkD_call (v : GcmImpl) {s : State} {K C Y D S : Addr} {R q : Nat} (h : VG.Proof.AesGcm.X86_64.BlkCall s K C Y D S R q) :
    WP isa (.call v.callees.dec.name v.callees.dec.code) s fun s' => VG.Proof.AesGcm.X86_64.BlkPost s C Y D S q s' ∧
      blocksAt s'.mem D q = ctr32 (aesWith R (Spec.Aes.bytesAt s.mem K (16 * (R + 1)))) (blockAt s.mem C)
        (blocksAt s.mem D q) ∧
      blockAt s'.mem C = Nat.repeat Spec.Gcm.inc32 q (blockAt s.mem C) ∧
      blockAt s'.mem Y = ghashFrom (blockAt s.mem (K + 240)) (blockAt s.mem Y) (blocksAt s.mem D q) := by
  have hq : (BitVec.ofNat 64 q).toNat = q := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.w_d; omega)
  have hR : (BitVec.ofNat 64 R).toNat = R := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rcases h.rounds with h | h | h <;> omega)
  refine WP.call (k := Proof.AesGcm.decryptBlocksX86_64) (decryptBlocks_correct v v.stitch)
    (VG.Proof.AesGcm.X86_64.decryptBlocks_nosp v v.stitch) (by rw [VG.Proof.AesGcm.X86_64.decryptBlocks_depth]; decide)
    (rd := BlkCall.rd s K) (wr := BlkCall.wr C Y D S q) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [VG.Proof.AesGcm.X86_64.decryptBlocks_depth] at hf
  obtain ⟨eK, eC, eY, eD, eH⟩ := h.entry_eqs
  simp only [Proof.AesGcm.decryptBlocksX86_64, Spec.Gcm.ctxCiph, Spec.Gcm.ctxH, State.withRegions_gpr,
    State.withRegions_mem, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hq, hR, hm₂,
    eK, eC, eY, eD, eH] at hpost
  exact ⟨⟨hrd, hwr, hcs, hf⟩, hpost.1, hpost.2.1, hpost.2.2⟩

/-- Two calls of `vg_aes_gcm_encrypt_blocks` or `_decrypt_blocks` with the same
arguments leak the same. -/
theorem blk_pub {s₁ s₂ : State} {K C Y D S : Addr} {R q : Nat} (h₁ : VG.Proof.AesGcm.X86_64.BlkCall s₁ K C Y D S R q)
    (h₂ : VG.Proof.AesGcm.X86_64.BlkCall s₂ K C Y D S R q) (hsp : s₁.gpr .rsp = s₂.gpr .rsp) :
    Proof.AesGcm.blocksPub (s₁.callEntry.withRegions (BlkCall.rd s₁ K) (BlkCall.wr C Y D S q))
      (s₂.callEntry.withRegions (BlkCall.rd s₂ K) (BlkCall.wr C Y D S q)) := by
  simp only [Proof.AesGcm.blocksPub, Proof.AesGcm.arg, h₁.arg_eq, h₂.arg_eq, State.withRegions_gpr,
    State.callEntry_rsp, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp), h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₂.rdi,
    h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem blkE_rel (v : GcmImpl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C Y D S : Addr, ∃ R q : Nat,
      VG.Proof.AesGcm.X86_64.BlkCall s₁ K C Y D S R q ∧ VG.Proof.AesGcm.X86_64.BlkCall s₂ K C Y D S R q ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call v.callees.enc.name v.callees.enc.code) fun _ _ => True := by
  refine RelCT.callEx (k := Proof.AesGcm.encryptBlocksX86_64) (encryptBlocks_correct v v.stitch)
    (Blocks.encrypt_ct v v.stitch) fun s₁ s₂ hp => ?_
  obtain ⟨K, C, Y, D, S, R, q, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  exact ⟨_, _, _, _, h₁.pre, h₂.pre, VG.Proof.AesGcm.X86_64.blk_pub h₁ h₂ hsp, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩

theorem blkD_rel (v : GcmImpl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C Y D S : Addr, ∃ R q : Nat,
      VG.Proof.AesGcm.X86_64.BlkCall s₁ K C Y D S R q ∧ VG.Proof.AesGcm.X86_64.BlkCall s₂ K C Y D S R q ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call v.callees.dec.name v.callees.dec.code) fun _ _ => True := by
  refine RelCT.callEx (k := Proof.AesGcm.decryptBlocksX86_64) (decryptBlocks_correct v v.stitch)
    (Blocks.decrypt_ct v v.stitch) fun s₁ s₂ hp => ?_
  obtain ⟨K, C, Y, D, S, R, q, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  exact ⟨_, _, _, _, h₁.pre, h₂.pre, VG.Proof.AesGcm.X86_64.blk_pub h₁ h₂ hsp, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Piece`. -/
section

/-!
# AES-GCM on x86-64: the whole blocks of `seal` and `open` in one call

Untrusted: everything here is checked by Lean. `oneBlocks f` keeps the
length at `W + 192` and computes the number of whole blocks (`ob1_ok`); if
there are any, it sets the arguments (`ob2_ok`), pushes `scratch` and calls
`f` (`vg_aes_gcm_encrypt_blocks` or `_decrypt_blocks`), then keeps the data
left after the whole blocks at `W + 200` and `W + 208` (`ob3_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith ctr32)

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

omit L in
/-- The length kept, and the number of whole blocks. -/
theorem ob1_ok {n : Nat} (hn : n < 2 ^ 64) {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 lenO)), .store (at_ .r15 tlenO) .rax, .shift .shr .rax 4,
      .alu .test .rax (.reg .rax)]) s fun s₁ => s₁.gpr .rax = BitVec.ofNat 64 (n / 16) ∧
      s₁.zf = some (decide (n / 16 = 0)) ∧ (∀ r, r ≠ .rax → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem.writeW (W + BitVec.ofNat 64 192) (BitVec.ofNat 64 n) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have q₁ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 192 + 8 ≤ 2560 by decide)
  have h4 := shr4 n hn
  have hz := and_self_beq (show n / 16 < 2 ^ 64 by omega)
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, w₁, hlen, h4], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, h4]
  · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, ite_true, h4, hz]
  · intro r hr; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr]
  all_goals simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
    wr_setReg, wr_setFlags, he.r15, hlen]

omit L in
/-- The data left after the whole blocks, kept. -/
theorem ob3_ok {D : Addr} {n : Nat} (hn : n < 2 ^ 64) {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 lenO)), .mov .rcx (.reg .rax), .alu .and .rcx (imm 15),
      .store (at_ .r15 lenO) .rcx, .alu .sub .rax (.reg .rcx), .alu .add .rax (.mem (at_ .r15 dataO)),
      .store (at_ .r15 dataO) .rax]) s fun s₅ =>
      (∀ r, r ≠ .rax → r ≠ .rcx → s₅.gpr r = s.gpr r) ∧
      s₅.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (16 * (n / 16)) ∧
      s₅.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n % 16) ∧
      Frame [⟨W + BitVec.ofNat 64 200, 16⟩] s.mem s₅.mem ∧ s₅.rd = s.rd ∧ s₅.wr = s.wr := by
  have q₁ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 200 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 208 + 8 ≤ 2560 by decide)
  have e15 := and15 (BitVec.ofNat 64 n)
  rw [toNat_ofNat_of_lt hn, imm_eq (by decide)] at e15
  have esub : BitVec.ofNat 64 n - BitVec.ofNat 64 (n % 16) = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [ofNat_sub (Nat.mod_le _ _) hn]; congr 1; omega
  have sep : Mem.Sep (W + BitVec.ofNat 64 200) (64 / 8) (W + BitVec.ofNat 64 208) (64 / 8) :=
    Offset.sep _ (.inl (by decide)) (by have := he.perm; omega) (by omega)
  have hdat' : (s.mem.writeW (W + BitVec.ofNat 64 208) (BitVec.ofNat 64 (n % 16))).readW
      (W + BitVec.ofNat 64 200) 64 = D := by rw [Mem.readW_writeW_sep sep (by decide), hdat]
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, q₂, w₁, w₂, hlen, e15, esub, hdat'], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r a b; simp [gpr_setReg, gpr_arithFlags, a, b]
  · simp [mem_arithFlags, mem_setReg, Mem.readW_writeW_self64, BitVec.add_comm]
  · simp only [mem_arithFlags, mem_setReg]
    rw [Mem.readW_writeW_sep (VG.Proof.AesGcm.X86_64.sep_of_disj (Offset.disjoint _ (.inr (by decide)) (by omega) (by omega)))
      (by decide), Mem.readW_writeW_self64]
  · have c : ∀ d, 200 ≤ d → d + 8 ≤ 216 → (⟨W + BitVec.ofNat 64 200, 16⟩ : Region).Contains
        (W + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    simp only [mem_arithFlags, mem_setReg]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))
  all_goals simp [rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

omit L in
theorem covers_cons_r {rs ts : List Region} (r : Region) (h : Covers rs ts) : Covers rs (r :: ts) :=
  fun a m hi => by obtain ⟨x, hx, hc⟩ := h a m hi; exact ⟨x, List.mem_cons_of_mem _ hx, hc⟩

end

/-- The arguments of the call. -/
theorem ob2_ok {Ctx St W SP : Addr} {R : Nat} {D : Addr} {s : State} (he : Env Ctx St W SP s)
    (hR : RoundsAt s.mem W R) (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D) :
    WP isa (.block (([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++
      ptr .rdx .r14 48 ++ ptr .rcx .r14 16 ++ ([.mov .r8 (.mem (at_ .r15 dataO)), .mov .r9 (.reg .rax)] : List Instr) ++
      ptr .rax .r15 bScrO)) s fun s₂ => s₂.gpr .rdi = Ctx ∧ s₂.gpr .rsi = BitVec.ofNat 64 R ∧
      s₂.gpr .rdx = St + BitVec.ofNat 64 48 ∧
      s₂.gpr .rcx = St + BitVec.ofNat 64 16 ∧ s₂.gpr .r8 = D ∧ s₂.gpr .r9 = s.gpr .rax ∧
      s₂.gpr .rax = W + BitVec.ofNat 64 448 ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → r ≠ .rax → s₂.gpr r = s.gpr r) ∧
      s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
  have q₁ := he.perm.wR (show 176 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r13, he.r14, he.r15, q₁, q₂, hR.1, hdat], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, he.r13]
  · simp [gpr_setReg, gpr_arithFlags, he.r15, hR.1]
  · simp [gpr_setReg, gpr_arithFlags, he.r14, imm_eq]
  · simp [gpr_setReg, gpr_arithFlags, he.r14, imm_eq]
  · simp [gpr_setReg, gpr_arithFlags, he.r15, hdat]
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [gpr_setReg, gpr_arithFlags, he.r15, imm_eq, bScrO]
  · intro r a b c d e f g; simp [gpr_setReg, gpr_arithFlags, a, b, c, d, e, f, g]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- What the frame of the call needs. -/
structure ObIn (Ctx St W SP : Addr) (R : Nat) (D : Addr) (n q : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  data : DataW Ctx St W SP s D n
  q_le : 16 * q ≤ n
  t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩
  t_w : (below SP 24).Disjoint ⟨W, 2560⟩
  t_d : (below SP 24).Disjoint ⟨D, n⟩
  sp24 : 24 ≤ SP.toNat
  rdi : s.gpr .rdi = Ctx
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = St + BitVec.ofNat 64 48
  rcx : s.gpr .rcx = St + BitVec.ofNat 64 16
  r8 : s.gpr .r8 = D
  r9 : s.gpr .r9 = BitVec.ofNat 64 q
  rax : s.gpr .rax = W + BitVec.ofNat 64 448
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  t_s : (below SP 24).Disjoint ⟨St, 80⟩

/-- The regions the call writes. -/
abbrev obFrame (St W SP D : Addr) (q : Nat) : List Region :=
  [⟨St + BitVec.ofNat 64 48, 16⟩, ⟨St + BitVec.ofNat 64 16, 16⟩,
    ⟨D, q * 16⟩, ⟨W + BitVec.ofNat 64 448, 2112⟩, below SP 24]

/-- The call, from the frame's push. -/
theorem ObIn.call {R : Nat} {D : Addr} {n q : Nat} {s : State} (h : VG.Proof.AesGcm.X86_64.ObIn Ctx St W SP R D n q s) :
    VG.Proof.AesGcm.X86_64.BlkCall (pushed [.rax] s) Ctx (St + BitVec.ofNat 64 48)
      (St + BitVec.ofNat 64 16) D (W + BitVec.ofNat 64 448) R q := by
  have hsp := h.env.rsp
  have psp : (pushed [.rax] s).gpr .rsp = SP - BitVec.ofNat 64 8 := by rw [pushed_rsp, hsp]; rfl
  have e24 : SP - BitVec.ofNat 64 8 - 16 = SP - BitVec.ofNat 64 24 := by rw [← Offset.sub_add_eq]; rfl
  have hn8 : 8 * [Reg.rax].length ≤ (s.gpr .rsp).toNat := by rw [hsp]; have := h.sp24; simp; omega
  obtain ⟨-, hpj⟩ := pushRegs_mem s [.rax] (by decide) hn8
  have harg : (pushed [.rax] s).mem.readW (SP - BitVec.ofNat 64 8) 64 = W + BitVec.ofNat 64 448 := by
    have := hpj 0 (by decide); rw [hsp] at this; rw [← h.rax]; exact this
  have ww := L.ww
  have sw := L.sw
  have hw := h.data.ok.wrap
  have hq := h.q_le
  have qd : Region.Sub ⟨D, q * 16⟩ ⟨D, n⟩ := Region.sub_prefix (by omega)
  have sS : Region.Sub ⟨W + BitVec.ofNat 64 448, 2112⟩ ⟨W, 2560⟩ := Lay.wSub (by decide)
  have sC : Region.Sub ⟨St + BitVec.ofNat 64 48, 16⟩ ⟨St, 80⟩ := Lay.stSub (by decide)
  have sY : Region.Sub ⟨St + BitVec.ofNat 64 16, 16⟩ ⟨St, 80⟩ := Lay.stSub (by decide)
  have tS : Region.Sub ⟨(pushed [.rax] s).gpr .rsp - 16, 24⟩ (below SP 24) := by
    rw [psp, e24]; exact fun _ h => h
  have toN : ∀ d, d < 2560 → (W + BitVec.ofNat 64 d).toNat = W.toNat + d := fun d hd => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]
  have toS : ∀ d, d < 80 → (St + BitVec.ofNat 64 d).toNat = St.toNat + d := fun d hd => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]
  refine ⟨by rw [pushed_gpr _ _ (by decide)]; exact h.rdi, by rw [pushed_gpr _ _ (by decide)]; exact h.rsi,
    by rw [pushed_gpr _ _ (by decide)]; exact h.rdx, by rw [pushed_gpr _ _ (by decide)]; exact h.rcx,
    by rw [pushed_gpr _ _ (by decide)]; exact h.r8, by rw [pushed_gpr _ _ (by decide)]; exact h.r9,
    by rw [psp]; exact harg, h.rounds, L.cw, ?_, ?_, by omega, by rw [toN 448 (by decide)]; omega, ?_,
    L.ctx_st (a := 0) (n := 256) (d := 48) (k := 16) (by decide) (by decide) |> fun h => by simpa using h,
    L.ctx_st (a := 0) (n := 256) (d := 16) (k := 16) (by decide) (by decide) |> fun h => by simpa using h,
    h.data.ctx.sub_right qd, (L.cw'.sub_right sS),
    L.st_st (.inr (by decide)) (by decide) (by decide), (h.data.ok.st.sub_right (Lay.stSub (by decide))).symm.sub_right qd,
    L.st_w (by decide) (.inr ⟨by decide, by decide⟩),
    (h.data.ok.st.sub_right (Lay.stSub (by decide))).symm.sub_right qd,
    L.st_w (by decide) (.inr ⟨by decide, by decide⟩), (h.data.ok.w.sub_left qd).sub_right sS,
    h.t_c.sub_left tS, (h.t_s.sub_left tS).sub_right sC, (h.t_s.sub_left tS).sub_right sY,
    (h.t_d.sub_left tS).sub_right qd, (h.t_w.sub_left tS).sub_right sS, ?_, ?_⟩
  · rw [toS 48 (by decide)]; omega
  · rw [toS 16 (by decide)]; omega
  · have e16 : SP - BitVec.ofNat 64 8 - 8 = SP - BitVec.ofNat 64 16 := by rw [← Offset.sub_add_eq]; rfl
    rw [psp, e16]; have := h.sp24
    rw [toNat_sub_ofNat (by omega)]; omega
  · simp only [pushed_rd, pushed_wr, psp, hsp]
    refine covers_cons ?_ (covers_cons ?_ (covers_cons ?_ (covers_cons ?_ (covers_cons ?_ ?_))))
    · exact fun a m hi => by
        obtain ⟨x, hx, hc⟩ := h.env.perm.ctx a m hi
        rcases List.mem_append.mp hx with hx | hx
        · exact ⟨x, List.mem_append_left _ hx, hc⟩
        · exact ⟨x, List.mem_append_right _ (List.mem_cons_of_mem _ hx), hc⟩
    · rw [show 8 * [Reg.rax].length = 8 from rfl]
      exact covers_of_mem (List.mem_append_right _ (List.mem_cons_self ..))
    all_goals refine covers_left (Covers.trans ?_ (VG.Proof.AesGcm.X86_64.covers_cons_r _ (Covers.refl _)))
    · exact h.env.perm.stC (by decide)
    · exact h.env.perm.stC (by decide)
    · exact Blocks.covers_prefix h.data.wr (by omega)
    · exact h.env.perm.wC (by decide)
  · simp only [pushed_wr, hsp]
    refine Covers.trans ?_ (VG.Proof.AesGcm.X86_64.covers_cons_r _ (Covers.refl _))
    refine covers_cons ?_ (covers_cons ?_ (covers_cons ?_ ?_))
    · exact h.env.perm.stC (by decide)
    · exact h.env.perm.stC (by decide)
    · exact Blocks.covers_prefix h.data.wr (by omega)
    · exact h.env.perm.wC (by decide)

/-- What the frame's push writes is apart from what the call reads. -/
theorem ObIn.push_eqs {R : Nat} {D : Addr} {n q : Nat} {s : State} (h : VG.Proof.AesGcm.X86_64.ObIn Ctx St W SP R D n q s) :
    Frame (VG.Proof.AesGcm.X86_64.obFrame St W SP D q) s.mem (pushed [.rax] s).mem ∧
    bytesAt (pushed [.rax] s).mem Ctx (16 * (R + 1)) = bytesAt s.mem Ctx (16 * (R + 1)) ∧
    blockAt (pushed [.rax] s).mem (St + BitVec.ofNat 64 48) =
      blockAt s.mem (St + BitVec.ofNat 64 48) ∧
    blockAt (pushed [.rax] s).mem (St + BitVec.ofNat 64 16) =
      blockAt s.mem (St + BitVec.ofNat 64 16) ∧
    blocksAt (pushed [.rax] s).mem D q = blocksAt s.mem D q ∧
    blockAt (pushed [.rax] s).mem (Ctx + 240) = blockAt s.mem (Ctx + 240) := by
  have hsp := h.env.rsp
  have hn8 : 8 * [Reg.rax].length ≤ (s.gpr .rsp).toNat := by rw [hsp]; have := h.sp24; simp; omega
  obtain ⟨hf, -⟩ := pushRegs_mem s [.rax] (by decide) hn8
  have hf' : Frame [below SP 8] s.mem (pushed [.rax] s).mem := by
    have := hf; rw [hsp] at this; exact this
  have b8 : Region.Sub (below SP 8) (below SP 24) := VG.X86_64.below_sub (by decide) (by decide)
  have hq := h.q_le
  have hRb : 16 * (R + 1) ≤ 256 := by rcases h.rounds with h | h | h <;> subst h <;> decide
  have sC : Region.Sub ⟨St + BitVec.ofNat 64 48, 16⟩ ⟨St, 80⟩ := Lay.stSub (by decide)
  have sY : Region.Sub ⟨St + BitVec.ofNat 64 16, 16⟩ ⟨St, 80⟩ := Lay.stSub (by decide)
  have one : ∀ {r : Region}, (below SP 24).Disjoint r → ∀ r' ∈ [below SP 8], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hd.sub_left b8).symm
  refine ⟨hf'.sub fun r hr => ⟨below SP 24, by simp [VG.Proof.AesGcm.X86_64.obFrame], by simp only [List.mem_singleton] at hr; subst hr; exact b8⟩,
    bytesAt_frame hf' (one (h.t_c.sub_right (Region.sub_prefix hRb))) (by have := L.cw; omega),
    blockAt_frame hf' (one (h.t_s.sub_right sC)), blockAt_frame hf' (one (h.t_s.sub_right sY)),
    blocksAt_frame hf' (one (h.t_d.sub_right (Region.sub_prefix (by omega)))) (by have := h.data.ok.wrap; omega),
    blockAt_frame hf' (one (h.t_c.sub_right (Offset.sub_base (d := 240) _ (by decide))))⟩

/-- The registers, permissions and memory after the frame of a call. -/
theorem ObIn.popped {R : Nat} {D : Addr} {n q : Nat} {s s₃ : State} (h : VG.Proof.AesGcm.X86_64.ObIn Ctx St W SP R D n q s)
    (bp : VG.Proof.AesGcm.X86_64.BlkPost (pushed [.rax] s) (St + BitVec.ofNat 64 48)
      (St + BitVec.ofNat 64 16) D (W + BitVec.ofNat 64 448) q s₃) :
    s₃.gpr .rsp = (pushed [.rax] s).gpr .rsp ∧ s₃.wr = (pushed [.rax] s).wr ∧
    (∀ r ∈ calleeSaved, (VG.X86_64.popped .rax 1 s₃).gpr r = s.gpr r) ∧ (VG.X86_64.popped .rax 1 s₃).rd = s.rd ∧
    (VG.X86_64.popped .rax 1 s₃).wr = s.wr ∧ Frame (VG.Proof.AesGcm.X86_64.obFrame St W SP D q) s.mem (VG.X86_64.popped .rax 1 s₃).mem := by
  have hsp := h.env.rsp
  have psp : (pushed [.rax] s).gpr .rsp = SP - BitVec.ofNat 64 8 := by rw [pushed_rsp, hsp]; rfl
  have r₃ := bp.saved _ (by decide : Reg.rsp ∈ calleeSaved)
  refine ⟨r₃, bp.wr, fun r hr => ?_, by rw [popped_rd, bp.rd, pushed_rd], by rw [popped_wr, bp.wr, pushed_wr]; rfl, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; rw [popped_rsp, r₃, psp, hsp]; exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ hr' (fun e => by subst e; simp [calleeSaved] at hr), bp.saved r hr, pushed_gpr _ _ hr']
  · rw [popped_mem]
    refine (ObIn.push_eqs L h).1.trans (bp.frame.sub fun r hr => ?_)
    simp only [BlkCall.wr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [VG.Proof.AesGcm.X86_64.obFrame], fun _ h => h⟩
    · exact ⟨_, by simp [VG.Proof.AesGcm.X86_64.obFrame], fun _ h => h⟩
    · exact ⟨_, by simp [VG.Proof.AesGcm.X86_64.obFrame], fun _ h => h⟩
    · exact ⟨_, by simp [VG.Proof.AesGcm.X86_64.obFrame], fun _ h => h⟩
    · refine ⟨below SP 24, by simp [VG.Proof.AesGcm.X86_64.obFrame], ?_⟩
      have e : SP - BitVec.ofNat 64 8 - BitVec.ofNat 64 16 = SP - BitVec.ofNat 64 24 := by
        rw [← Offset.sub_add_eq, ← BitVec.ofNat_add]
      show Region.Sub ⟨(pushed [.rax] s).gpr .rsp - BitVec.ofNat 64 16, 16⟩ _
      rw [psp, e]; exact Region.sub_prefix (by decide)

/-- The frame of the call of `vg_aes_gcm_encrypt_blocks`. -/
theorem obFrameE_ok (v : GcmImpl) {R : Nat} {D : Addr} {n q : Nat} {s : State} (h : VG.Proof.AesGcm.X86_64.ObIn Ctx St W SP R D n q s) :
    WP isa (.frame (.push [.rax]) (.call v.callees.enc.name v.callees.enc.code) (.pop .rax 1)) s fun s₄ =>
      (∀ r ∈ calleeSaved, s₄.gpr r = s.gpr r) ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
      Frame (VG.Proof.AesGcm.X86_64.obFrame St W SP D q) s.mem s₄.mem ∧
      blocksAt s₄.mem D q = ctr32 (aesWith R (bytesAt s.mem Ctx (16 * (R + 1))))
        (blockAt s.mem (St + BitVec.ofNat 64 48)) (blocksAt s.mem D q) ∧
      blockAt s₄.mem (St + BitVec.ofNat 64 48) =
        Nat.repeat Spec.Gcm.inc32 q (blockAt s.mem (St + BitVec.ofNat 64 48)) ∧
      blockAt s₄.mem (St + BitVec.ofNat 64 16) = Spec.Gcm.ghashFrom (blockAt s.mem (Ctx + 240))
        (blockAt s.mem (St + BitVec.ofNat 64 16)) (blocksAt s₄.mem D q) := by
  have hsp := h.env.rsp
  have hn8 : 8 * [Reg.rax].length ≤ (s.gpr .rsp).toNat := by rw [hsp]; have := h.sp24; simp; omega
  obtain ⟨-, eK, eC, eY, eD, eH⟩ := ObIn.push_eqs L h
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.mono (VG.Proof.AesGcm.X86_64.blkE_call v (ObIn.call L h)) fun s₃ ⟨bp, o₁, o₂, o₃⟩ => ?_)
  obtain ⟨r₃, w₃, cs, rd, wr, fr⟩ := ObIn.popped L h bp
  rw [eK, eC, eD] at o₁
  rw [eC] at o₂
  rw [eH, eY] at o₃
  exact ⟨r₃, w₃, cs, rd, wr, fr, by rw [popped_mem]; exact o₁, by rw [popped_mem]; exact o₂,
    by rw [popped_mem]; exact o₃⟩

/-- The frame of the call of `vg_aes_gcm_decrypt_blocks`. -/
theorem obFrameD_ok (v : GcmImpl) {R : Nat} {D : Addr} {n q : Nat} {s : State} (h : VG.Proof.AesGcm.X86_64.ObIn Ctx St W SP R D n q s) :
    WP isa (.frame (.push [.rax]) (.call v.callees.dec.name v.callees.dec.code) (.pop .rax 1)) s fun s₄ =>
      (∀ r ∈ calleeSaved, s₄.gpr r = s.gpr r) ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
      Frame (VG.Proof.AesGcm.X86_64.obFrame St W SP D q) s.mem s₄.mem ∧
      blocksAt s₄.mem D q = ctr32 (aesWith R (bytesAt s.mem Ctx (16 * (R + 1))))
        (blockAt s.mem (St + BitVec.ofNat 64 48)) (blocksAt s.mem D q) ∧
      blockAt s₄.mem (St + BitVec.ofNat 64 48) =
        Nat.repeat Spec.Gcm.inc32 q (blockAt s.mem (St + BitVec.ofNat 64 48)) ∧
      blockAt s₄.mem (St + BitVec.ofNat 64 16) = Spec.Gcm.ghashFrom (blockAt s.mem (Ctx + 240))
        (blockAt s.mem (St + BitVec.ofNat 64 16)) (blocksAt s.mem D q) := by
  have hsp := h.env.rsp
  have hn8 : 8 * [Reg.rax].length ≤ (s.gpr .rsp).toNat := by rw [hsp]; have := h.sp24; simp; omega
  obtain ⟨-, eK, eC, eY, eD, eH⟩ := ObIn.push_eqs L h
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.mono (VG.Proof.AesGcm.X86_64.blkD_call v (ObIn.call L h)) fun s₃ ⟨bp, o₁, o₂, o₃⟩ => ?_)
  obtain ⟨r₃, w₃, cs, rd, wr, fr⟩ := ObIn.popped L h bp
  rw [eK, eC, eD] at o₁
  rw [eC] at o₂
  rw [eH, eY, eD] at o₃
  exact ⟨r₃, w₃, cs, rd, wr, fr, by rw [popped_mem]; exact o₁, by rw [popped_mem]; exact o₂,
    by rw [popped_mem]; exact o₃⟩

end

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- What `oneBlocks` needs: the state of `seal` or `open` after `oneAad`. -/
structure ObPre (Ctx W SP : Addr) (R : Nat) (D : Addr) (n : Nat) (s : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  rounds : RoundsAt s.mem W R
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  data : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n
  t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩
  t_w : (below SP 24).Disjoint ⟨W, 2560⟩
  t_d : (below SP 24).Disjoint ⟨D, n⟩
  sp24 : 24 ≤ SP.toNat

/-- What `oneBlocks` leaves, but its result: the data left kept, and the
regions written. -/
structure ObPost (Ctx W SP : Addr) (D : Addr) (n : Nat) (s s' : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame (⟨W + BitVec.ofNat 64 192, 24⟩ :: VG.Proof.AesGcm.X86_64.obFrame (W + BitVec.ofNat 64 16) W SP D (n / 16)) s.mem s'.mem
  tlen : s'.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n
  dat : s'.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (16 * (n / 16))
  len : s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n % 16)

/-- The slots of `W` that `oneBlocks` reads are apart from what its call writes. -/
theorem ob_slots {D : Addr} {n q : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hq : q * 16 ≤ n)
    (t_w : (below SP 24).Disjoint ⟨W, 2560⟩) {d : Nat} (h₁ : 176 ≤ d) (h₂ : d + 8 ≤ 240) :
    ∀ r ∈ VG.Proof.AesGcm.X86_64.obFrame (W + BitVec.ofNat 64 16) W SP D q, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [VG.Proof.AesGcm.X86_64.obFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [add_ofNat_assoc]; exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · rw [add_ofNat_assoc]; exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · exact (hD.sub_left (Region.sub_prefix hq)).symm.sub_left (Lay.wSub (by omega)) |>.symm |> fun h => h.symm
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (t_w.sub_right (Lay.wSub (by omega))).symm

end

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Ok`. -/
section

/-!
# AES-GCM on x86-64: `oneBlocks`

Untrusted: everything here is checked by Lean. `oneBlocks` encrypts
(`oneBlocksE_ok`) or decrypts (`oneBlocksD_ok`) the `⌊n / 16⌋` whole blocks
of the data and absorbs them, from the counter block and the accumulator of
the state, and keeps what is left of the data.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith ctr32 ghashFrom inc32)

/-- The counter block and the accumulator, in the state. -/
abbrev cbA (W : Addr) : Addr := W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48
abbrev yA (W : Addr) : Addr := W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- The length kept, apart from what the call reads. -/
theorem w192_eqs {R : Nat} {D : Addr} {n : Nat} {s : State} (h : VG.Proof.AesGcm.X86_64.ObPre Ctx W SP R D n s) (v : BitVec 64) :
    let m := s.mem.writeW (W + BitVec.ofNat 64 192) v
    m.readW (W + BitVec.ofNat 64 176) 64 = s.mem.readW (W + BitVec.ofNat 64 176) 64 ∧
    m.readW (W + BitVec.ofNat 64 200) 64 = s.mem.readW (W + BitVec.ofNat 64 200) 64 ∧
    m.readW (W + BitVec.ofNat 64 208) 64 = s.mem.readW (W + BitVec.ofNat 64 208) 64 ∧
    bytesAt m Ctx (16 * (R + 1)) = bytesAt s.mem Ctx (16 * (R + 1)) ∧
    blockAt m (VG.Proof.AesGcm.X86_64.cbA W) = blockAt s.mem (VG.Proof.AesGcm.X86_64.cbA W) ∧ blockAt m (VG.Proof.AesGcm.X86_64.yA W) = blockAt s.mem (VG.Proof.AesGcm.X86_64.yA W) ∧
    blocksAt m D (n / 16) = blocksAt s.mem D (n / 16) ∧ blockAt m (Ctx + 240) = blockAt s.mem (Ctx + 240) ∧
    Frame [⟨W + BitVec.ofNat 64 192, 24⟩] s.mem m := by
  intro m
  have ww := L.ww
  have hf : Frame [⟨W + BitVec.ofNat 64 192, 8⟩] s.mem m :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have sep : ∀ d, d + 8 ≤ 192 ∨ 200 ≤ d → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 d) (64 / 8) (W + BitVec.ofNat 64 192) (64 / 8) :=
    fun d h₁ h₂ => Offset.sep _ (by omega) (by omega) (by omega)
  have one : ∀ {r : Region}, r.Disjoint ⟨W + BitVec.ofNat 64 192, 8⟩ →
      ∀ r' ∈ [(⟨W + BitVec.ofNat 64 192, 8⟩ : Region)], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  have hRb : 16 * (R + 1) ≤ 256 := by rcases h.rounds.2 with h | h | h <;> subst h <;> decide
  refine ⟨Mem.readW_writeW_sep (sep 176 (.inl (by decide)) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep 200 (.inr (by decide)) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep 208 (.inr (by decide)) (by decide)) (by decide),
    bytesAt_frame hf (one ((L.cw'.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))))
      (by have := L.cw; omega),
    blockAt_frame hf (one (by simp only [VG.Proof.AesGcm.X86_64.cbA, VG.Proof.AesGcm.X86_64.yA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide))),
    blockAt_frame hf (one (by simp only [VG.Proof.AesGcm.X86_64.cbA, VG.Proof.AesGcm.X86_64.yA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide))),
    blocksAt_frame hf (one ((h.data.ok.w.sub_left (Region.sub_prefix (by omega))).sub_right
      (Lay.wSub (by decide)))) (by have := h.data.ok.wrap; omega),
    blockAt_frame hf (one ((L.cw'.sub_left (Offset.sub_base (d := 240) _ (by decide))).sub_right
      (Lay.wSub (by decide)))),
    hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩⟩

/-- The bookkeeping of `oneBlocks` around its call: from the state `s₁` after
the length is kept to the end, given the call's frame (`hframe`). -/
theorem oneBlocks_core (f : Fn) {R : Nat} {D : Addr} {n : Nat} {s : State} (h : VG.Proof.AesGcm.X86_64.ObPre Ctx W SP R D n s)
    {Out : State → State → Prop}
    (hframe : ∀ s₂, VG.Proof.AesGcm.X86_64.ObIn Ctx (W + BitVec.ofNat 64 16) W SP R D n (n / 16) s₂ →
      WP isa (.frame (.push [.rax]) (.call f.name f.code) (.pop .rax 1)) s₂ fun s₄ =>
        (∀ r ∈ calleeSaved, s₄.gpr r = s₂.gpr r) ∧ s₄.rd = s₂.rd ∧ s₄.wr = s₂.wr ∧
        Frame (VG.Proof.AesGcm.X86_64.obFrame (W + BitVec.ofNat 64 16) W SP D (n / 16)) s₂.mem s₄.mem ∧ Out s₂ s₄)
    (h0 : n / 16 = 0 → ∀ s₁, s₁.mem = s.mem.writeW (W + BitVec.ofNat 64 192) (BitVec.ofNat 64 n) → Out s s₁)
    (hout : ∀ s₂ s₄ s₅, s₂.mem = s.mem.writeW (W + BitVec.ofNat 64 192) (BitVec.ofNat 64 n) → Out s₂ s₄ →
      Frame [⟨W + BitVec.ofNat 64 200, 16⟩] s₄.mem s₅.mem → Out s s₅) :
    WP isa (oneBlocks f) s fun s' => VG.Proof.AesGcm.X86_64.ObPost Ctx W SP D n s s' ∧ Out s s' := by
  have hn : n < 2 ^ 64 := h.data.ok.lt
  have he := h.env
  obtain ⟨e176, e200, e208, -, -, -, -, -, f192⟩ := VG.Proof.AesGcm.X86_64.w192_eqs L h (BitVec.ofNat 64 n)
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.ob1_ok hn he h.len) fun s₁ ⟨r₁, z₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) rd₁ wr₁
  have t₁ : s₁.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n := by rw [m₁, Mem.readW_writeW_self64]
  have hf₁ : Frame (⟨W + BitVec.ofNat 64 192, 24⟩ :: VG.Proof.AesGcm.X86_64.obFrame (W + BitVec.ofNat 64 16) W SP D (n / 16)) s.mem s₁.mem := by
    rw [m₁]; exact f192.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..
  refine WP.ite (decide (n / 16 = 0)) (by simp only [eval, z₁]) (fun hz => ?_) (fun hz => ?_)
  · simp only [decide_eq_true_eq] at hz
    refine WP.block_nil ⟨⟨he₁, rd₁, wr₁, hf₁, t₁, ?_, ?_⟩, h0 hz s₁ m₁⟩
    · rw [m₁, e200, h.dat, hz]; simp
    · rw [m₁, e208, h.len]; congr 1; omega
  · simp only [decide_eq_false_iff_not] at hz
    have hR₁ : RoundsAt s₁.mem W R := ⟨by rw [m₁, e176]; exact h.rounds.1, h.rounds.2⟩
    have hd₁ : s₁.mem.readW (W + BitVec.ofNat 64 200) 64 = D := by rw [m₁, e200, h.dat]
    refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.ob2_ok he₁ hR₁ hd₁) fun s₂ ⟨a1, a2, a3, a4, a5, a6, a7, g₂, m₂, rd₂, wr₂⟩ => ?_)
    have he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)) rd₂ wr₂
    have obi : VG.Proof.AesGcm.X86_64.ObIn Ctx (W + BitVec.ofNat 64 16) W SP R D n (n / 16) s₂ := ⟨he₂, h.data.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁),
      by omega, h.t_c, h.t_w, h.t_d, h.sp24, a1, a2, a3, a4, a5, by rw [a6, r₁], a7, h.rounds.2, h.t_w.sub_right (Lay.wSub (by decide))⟩
    refine WP.seq (WP.mono (hframe s₂ obi) fun s₄ ⟨cs₄, rd₄, wr₄, fr₄, o₄⟩ => ?_)
    have he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ := he₂.keep (fun r hr => cs₄ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])) rd₄ wr₄
    have kp : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
        s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
      rw [fr₄.readW (Region.contains_self _ _) (VG.Proof.AesGcm.X86_64.ob_slots L h.data.ok.w (by omega) h.t_w h₁ h₂) (by decide), m₂]
    have hd₄ : s₄.mem.readW (W + BitVec.ofNat 64 200) 64 = D := by rw [kp 200 (by decide) (by decide), hd₁]
    have hl₄ : s₄.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n := by
      rw [kp 208 (by decide) (by decide), m₁, e208, h.len]
    refine WP.mono (VG.Proof.AesGcm.X86_64.ob3_ok hn he₄ hd₄ hl₄) fun s₅ ⟨g₅, d₅, l₅, f₅, rd₅, wr₅⟩ => ?_
    have he₅ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ := he₄.keep (fun r hr => g₅ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) rd₅ wr₅
    refine ⟨⟨he₅, rd₅.trans (rd₄.trans (rd₂.trans rd₁)), wr₅.trans (wr₄.trans (wr₂.trans wr₁)), ?_, ?_, d₅, l₅⟩,
      hout s₂ s₄ s₅ (m₂.trans m₁) o₄ f₅⟩
    · refine hf₁.trans ?_
      rw [← m₂]
      refine (fr₄.mono fun r hr => List.mem_cons_of_mem _ hr).trans ?_
      exact f₅.sub fun r hr => ⟨_, List.mem_cons_self .., by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by decide)⟩
    · rw [f₅.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (.inl (by decide)) (by decide) (by decide)) (by decide),
        kp 192 (by decide) (by decide), t₁]


/-- What encrypting the whole blocks does, from `s` to `s'`. -/
def OutE (Ctx W : Addr) (R : Nat) (D : Addr) (q : Nat) (s s' : State) : Prop :=
  blocksAt s'.mem D q = ctr32 (aesWith R (bytesAt s.mem Ctx (16 * (R + 1)))) (blockAt s.mem (VG.Proof.AesGcm.X86_64.cbA W))
    (blocksAt s.mem D q) ∧
  blockAt s'.mem (VG.Proof.AesGcm.X86_64.cbA W) = Nat.repeat inc32 q (blockAt s.mem (VG.Proof.AesGcm.X86_64.cbA W)) ∧
  blockAt s'.mem (VG.Proof.AesGcm.X86_64.yA W) = ghashFrom (blockAt s.mem (Ctx + 240)) (blockAt s.mem (VG.Proof.AesGcm.X86_64.yA W)) (blocksAt s'.mem D q)

/-- What decrypting the whole blocks does, from `s` to `s'`. -/
def OutD (Ctx W : Addr) (R : Nat) (D : Addr) (q : Nat) (s s' : State) : Prop :=
  blocksAt s'.mem D q = ctr32 (aesWith R (bytesAt s.mem Ctx (16 * (R + 1)))) (blockAt s.mem (VG.Proof.AesGcm.X86_64.cbA W))
    (blocksAt s.mem D q) ∧
  blockAt s'.mem (VG.Proof.AesGcm.X86_64.cbA W) = Nat.repeat inc32 q (blockAt s.mem (VG.Proof.AesGcm.X86_64.cbA W)) ∧
  blockAt s'.mem (VG.Proof.AesGcm.X86_64.yA W) = ghashFrom (blockAt s.mem (Ctx + 240)) (blockAt s.mem (VG.Proof.AesGcm.X86_64.yA W)) (blocksAt s.mem D q)

/-- The kept slots written after the call are apart from the blocks, the
counter block and the accumulator. -/
theorem ob_after {R : Nat} {D : Addr} {n : Nat} {s : State} (h : VG.Proof.AesGcm.X86_64.ObPre Ctx W SP R D n s) {m m' : Mem}
    (hf : Frame [⟨W + BitVec.ofNat 64 200, 16⟩] m m') :
    blocksAt m' D (n / 16) = blocksAt m D (n / 16) ∧ blockAt m' (VG.Proof.AesGcm.X86_64.cbA W) = blockAt m (VG.Proof.AesGcm.X86_64.cbA W) ∧
    blockAt m' (VG.Proof.AesGcm.X86_64.yA W) = blockAt m (VG.Proof.AesGcm.X86_64.yA W) := by
  have one : ∀ {r : Region}, r.Disjoint ⟨W + BitVec.ofNat 64 200, 16⟩ →
      ∀ r' ∈ [(⟨W + BitVec.ofNat 64 200, 16⟩ : Region)], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  refine ⟨blocksAt_frame hf (one ((h.data.ok.w.sub_left (Region.sub_prefix (by omega))).sub_right
      (Lay.wSub (by decide)))) (by have := h.data.ok.wrap; omega),
    blockAt_frame hf (one (by simp only [VG.Proof.AesGcm.X86_64.cbA, VG.Proof.AesGcm.X86_64.yA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide))),
    blockAt_frame hf (one (by simp only [VG.Proof.AesGcm.X86_64.cbA, VG.Proof.AesGcm.X86_64.yA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide)))⟩

/-- `oneBlocks` of the encrypting function. -/
theorem oneBlocksE_ok (v : GcmImpl) {R : Nat} {D : Addr} {n : Nat} {s : State} (h : VG.Proof.AesGcm.X86_64.ObPre Ctx W SP R D n s) :
    WP isa (oneBlocks v.callees.enc) s fun s' => VG.Proof.AesGcm.X86_64.ObPost Ctx W SP D n s s' ∧ VG.Proof.AesGcm.X86_64.OutE Ctx W R D (n / 16) s s' := by
  obtain ⟨-, -, -, eK, eC, eY, eB, eH, -⟩ := VG.Proof.AesGcm.X86_64.w192_eqs L h (BitVec.ofNat 64 n)
  refine VG.Proof.AesGcm.X86_64.oneBlocks_core L _ h (fun s₂ hi => VG.Proof.AesGcm.X86_64.obFrameE_ok L v hi) (fun hz s₁ m₁ => ?_) (fun s₂ s₄ s₅ m₂ o f => ?_)
  · rw [VG.Proof.AesGcm.X86_64.OutE, hz, m₁, eC, eY]; exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨a₁, a₂, a₃⟩ := VG.Proof.AesGcm.X86_64.ob_after L h f
    obtain ⟨o₁, o₂, o₃⟩ := o
    simp only [m₂, eK, eC, eB, eY, eH] at o₁ o₂ o₃
    exact ⟨a₁.trans o₁, a₂.trans o₂, by rw [a₃, a₁]; exact o₃⟩

/-- `oneBlocks` of the decrypting function. -/
theorem oneBlocksD_ok (v : GcmImpl) {R : Nat} {D : Addr} {n : Nat} {s : State} (h : VG.Proof.AesGcm.X86_64.ObPre Ctx W SP R D n s) :
    WP isa (oneBlocks v.callees.dec) s fun s' => VG.Proof.AesGcm.X86_64.ObPost Ctx W SP D n s s' ∧ VG.Proof.AesGcm.X86_64.OutD Ctx W R D (n / 16) s s' := by
  obtain ⟨-, -, -, eK, eC, eY, eB, eH, -⟩ := VG.Proof.AesGcm.X86_64.w192_eqs L h (BitVec.ofNat 64 n)
  refine VG.Proof.AesGcm.X86_64.oneBlocks_core L _ h (fun s₂ hi => VG.Proof.AesGcm.X86_64.obFrameD_ok L v hi) (fun hz s₁ m₁ => ?_) (fun s₂ s₄ s₅ m₂ o f => ?_)
  · rw [VG.Proof.AesGcm.X86_64.OutD, hz, m₁, eC, eY]; exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨a₁, a₂, a₃⟩ := VG.Proof.AesGcm.X86_64.ob_after L h f
    obtain ⟨o₁, o₂, o₃⟩ := o
    simp only [m₂, eK, eC, eB, eY, eH] at o₁ o₂ o₃
    exact ⟨a₁.trans o₁, a₂.trans o₂, by rw [a₃]; exact o₃⟩

end

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts`. -/
section

/-!
# AES-GCM on x86-64: after `oneBlocks`

Untrusted: everything here is checked by Lean. What `seal` and `open` know
after `oneBlocks` (`ob_facts`): the whole blocks of the data in counter mode,
the counter after them, the accumulator over them, and everything else kept.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith ctr32 ghashFrom ghash blocks inc32 zeros padLen)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- What `seal` and `open` write after their entry, with `oneBlocks`. -/
abbrev oneFrameB (W D SP : Addr) (n : Nat) : List Region :=
  [⟨W, 128⟩, ⟨W + BitVec.ofNat 64 192, 32⟩, ⟨W + BitVec.ofNat 64 240, 2320⟩, ⟨D, n⟩, below SP 24]

theorem oneFrame_B {W D SP : Addr} {n k : Nat} (hk : k ≤ n) {m m' : Mem}
    (h : Frame (oneFrame W (D + BitVec.ofNat 64 k) SP (n - k)) m m') : Frame (VG.Proof.AesGcm.X86_64.oneFrameB W D SP n) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 192, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, fun _ h => h⟩
    · exact ⟨⟨D, n⟩, by simp, Offset.sub_base D (by omega)⟩
    · exact ⟨below SP 24, by simp, VG.X86_64.below_sub (by decide) (by decide)⟩

theorem obFrame_B {W D SP : Addr} {n : Nat} {m m' : Mem}
    (h : Frame (⟨W + BitVec.ofNat 64 192, 24⟩ :: VG.Proof.AesGcm.X86_64.obFrame (W + BitVec.ofNat 64 16) W SP D (n / 16)) m m') : Frame (VG.Proof.AesGcm.X86_64.oneFrameB W D SP n) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 192, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨W, 128⟩, by simp, by rw [add_ofNat_assoc]; exact Offset.sub_base W (by decide)⟩
    · exact ⟨⟨W, 128⟩, by simp, by rw [add_ofNat_assoc]; exact Offset.sub_base W (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP 24, by simp, fun _ h => h⟩

theorem oneB_trans {W D SP : Addr} {n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : Frame (VG.Proof.AesGcm.X86_64.oneFrameB W D SP n) m₁ m₂)
    (h₂ : Frame (VG.Proof.AesGcm.X86_64.oneFrameB W D SP n) m₂ m₃) : Frame (VG.Proof.AesGcm.X86_64.oneFrameB W D SP n) m₁ m₃ := h₁.trans h₂

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- The kept values are outside `oneFrameB`. -/
theorem kept_oneFrameB {D : Addr} {n d : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (t_w : (below SP 24).Disjoint ⟨W, 2560⟩) (h : (128 ≤ d ∧ d + 8 ≤ 192) ∨ (224 ≤ d ∧ d + 8 ≤ 240)) :
    ∀ r ∈ VG.Proof.AesGcm.X86_64.oneFrameB W D SP n, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := d) (n := 8) (d := 0) (k := 128) (.inr (by omega)) (by omega) (by decide)
  · exact L.w_w (by omega) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (hD.sub_right (Lay.wSub (by omega))).symm
  · exact (t_w.sub_right (Lay.wSub (by omega))).symm

theorem saved_oneFrameB {D : Addr} {n : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (t_w : (below SP 24).Disjoint ⟨W, 2560⟩) : ∀ r ∈ VG.Proof.AesGcm.X86_64.oneFrameB W D SP n, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 128) (n := 48) (d := 0) (k := 128) (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (hD.sub_right (Lay.wSub (by decide))).symm
  · exact (t_w.sub_right (Lay.wSub (by decide))).symm

/-- The key context is outside `oneFrameB`. -/
theorem ctx_oneFrameB {D : Addr} {n : Nat} (hC : (⟨Ctx, 256⟩ : Region).Disjoint ⟨D, n⟩)
    (t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩) : ∀ r ∈ VG.Proof.AesGcm.X86_64.oneFrameB W D SP n, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.cw'.sub_right (by simpa using Offset.sub_base W (d := 0) (n := 128) (k := 2560) (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact hC
  · exact t_c.symm

/-- The parts of the state `seal` and `open` keep through `oneBlocks`. -/
theorem st_obFrame {D : Addr} {n d k : Nat} (h : (d + k ≤ 16) ∨ (32 ≤ d ∧ d + k ≤ 48) ∨ (64 ≤ d ∧ d + k ≤ 80))
    (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (t_w : (below SP 24).Disjoint ⟨W, 2560⟩) :
    ∀ r ∈ (⟨W + BitVec.ofNat 64 192, 24⟩ :: VG.Proof.AesGcm.X86_64.obFrame (W + BitVec.ofNat 64 16) W SP D (n / 16)),
      (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [add_ofNat_assoc]
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · rw [add_ofNat_assoc]; exact L.w_w (by omega) (by omega) (by decide)
  · rw [add_ofNat_assoc]; exact L.w_w (by omega) (by omega) (by decide)
  · exact ((hD.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by omega))).symm
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (t_w.sub_right (Lay.wSub (by omega))).symm

/-- What `seal` and `open` know after `oneBlocks`, from what it did to the
whole blocks (`ho`, `hc`) and the accumulator (`hy`, over `Z`). -/
theorem ob_facts {R : Nat} {D : Addr} {n : Nat} {s s₃ : State} (h : VG.Proof.AesGcm.X86_64.ObPre Ctx W SP R D n s)
    (P : VG.Proof.AesGcm.X86_64.ObPost Ctx W SP D n s s₃) {H icb : Block} {x Z : List Byte}
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) (hcb : blockAt s.mem (VG.Proof.AesGcm.X86_64.cbA W) = icb)
    (habs : Absorbed s.mem (VG.Proof.AesGcm.X86_64.yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H x) (hx : x.length % 16 = 0)
    (ho : blocksAt s₃.mem D (n / 16) = ctr32 (ciphOf s.mem Ctx R) (blockAt s.mem (VG.Proof.AesGcm.X86_64.cbA W)) (blocksAt s.mem D (n / 16)))
    (hc : blockAt s₃.mem (VG.Proof.AesGcm.X86_64.cbA W) = Nat.repeat inc32 (n / 16) (blockAt s.mem (VG.Proof.AesGcm.X86_64.cbA W)))
    (hZ : Z.length % 16 = 0) (hy : blockAt s₃.mem (VG.Proof.AesGcm.X86_64.yA W) = ghashFrom H (blockAt s.mem (VG.Proof.AesGcm.X86_64.yA W)) (blocks Z)) :
    Frame (VG.Proof.AesGcm.X86_64.oneFrameB W D SP n) s.mem s₃.mem ∧ RoundsAt s₃.mem W R ∧
    blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H ∧ ciphOf s₃.mem Ctx R = ciphOf s.mem Ctx R ∧
    blockAt s₃.mem (W + BitVec.ofNat 64 16) = blockAt s.mem (W + BitVec.ofNat 64 16) ∧
    bytesAt s₃.mem D (16 * (n / 16)) = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem D (16 * (n / 16))) ∧
    Ctr s₃.mem (VG.Proof.AesGcm.X86_64.cbA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 64) (ciphOf s₃.mem Ctx R) icb (16 * (n / 16)) ∧
    Absorbed s₃.mem (VG.Proof.AesGcm.X86_64.yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H (x ++ Z) ∧
    bytesAt s₃.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) := by
  have fr := P.frame
  have hD := h.data.ok.w
  have hR := h.rounds.2
  have hlt := h.data.ok.lt
  have fB := VG.Proof.AesGcm.X86_64.obFrame_B fr
  have dC := VG.Proof.AesGcm.X86_64.ctx_oneFrameB L h.data.ctx h.t_c
  have hc₃ : ciphOf s₃.mem Ctx R = ciphOf s.mem Ctx R := ciph_frame fB dC hR
  have cw := Proof.Gcm.ctr_whole (ks := W + BitVec.ofNat 64 16 + BitVec.ofNat 64 64) (icb := icb) (n := 0)
    ⟨hcb, fun h => absurd rfl h⟩ rfl ho hc
  rw [Nat.zero_add, ← hc₃] at cw
  refine ⟨fB, rounds_frame fB (VG.Proof.AesGcm.X86_64.kept_oneFrameB L hD h.t_w (.inl ⟨by decide, by decide⟩)) h.rounds,
    by rw [blockAt_frame fB (fun r hr => (dC r hr).sub_left (Lay.ctxSub (by decide))), hH], hc₃,
    by simpa using blockAt_frame fr (VG.Proof.AesGcm.X86_64.st_obFrame L (d := 0) (k := 16) (.inl (by decide)) hD h.t_w),
    by rw [cw.1, hc₃], cw.2, Proof.Gcm.absorb_whole habs hx hZ (by rw [hy]), bytesAt_frame fr (fun r hr => ?_) (by omega)⟩
  have hs : Region.Sub ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n - 16 * (n / 16)⟩ ⟨D, n⟩ := Offset.sub_base D (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hD.sub_left hs).sub_right (Lay.wSub (by decide))
  · rw [add_ofNat_assoc]; exact (hD.sub_left hs).sub_right (Lay.wSub (by decide))
  · rw [add_ofNat_assoc]; exact (hD.sub_left hs).sub_right (Lay.wSub (by decide))
  · simpa using Offset.disjoint D (d := 16 * (n / 16)) (n := n - 16 * (n / 16)) (e := 0) (k := n / 16 * 16)
      (.inr (by omega)) (by omega) (by omega)
  · exact (hD.sub_left hs).sub_right (Lay.wSub (by decide))
  · exact (h.t_d.sub_right hs).symm

end

end VG.Proof.AesGcm.X86_64

end
