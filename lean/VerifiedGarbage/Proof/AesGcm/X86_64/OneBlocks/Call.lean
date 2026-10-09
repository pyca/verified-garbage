import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksVerified

/-!
# AES-GCM on x86-64: calling `vg_aes_gcm_encrypt_blocks` and `_decrypt_blocks`

Untrusted: everything here is checked by Lean. What a call of either needs,
from a state whose `rsp` points to `scratch` (pushed in a frame), for a key
context of kind `M` (`BlkCall M`), and what it leaves (`blkE_call`), from
its contract (with `WP.call`); and that two calls with the same public
arguments leak the same (`blkE_rel`). The functions called are given with
their proofs for that kind of key context (`BlkFn M`): those of
`vg_aes_gcm_init`'s (`GcmImpl.blkB`), and the `_precomputed` ones.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ctr32 aesWith)

/-- What a call needs, from a state `s` with `scratch` at `rsp`: the key
context at `K` for `R` rounds, the counter block at `C`, `Y` at `Y`, `q`
blocks at `D` and working space at `S`. -/
structure BlkCall (M : Gcm.X86_64.Stitch.CtxMode) (s : State) (K C Y D S : Addr) (R q : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = C
  rcx : s.gpr .rcx = Y
  r8 : s.gpr .r8 = D
  r9 : s.gpr .r9 = BitVec.ofNat 64 q
  arg : s.mem.readW (s.gpr .rsp) 64 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  w_k : K.toNat + M.len ≤ 2 ^ 64
  w_c : C.toNat + 16 ≤ 2 ^ 64
  w_y : Y.toNat + 16 ≤ 2 ^ 64
  w_d : D.toNat + q * 16 ≤ 2 ^ 64
  w_s : S.toNat + 2112 ≤ 2 ^ 64
  w_sp : (s.gpr .rsp - 8).toNat + 16 ≤ 2 ^ 64
  k_c : (⟨K, M.len⟩ : Region).Disjoint ⟨C, 16⟩
  k_y : (⟨K, M.len⟩ : Region).Disjoint ⟨Y, 16⟩
  k_d : (⟨K, M.len⟩ : Region).Disjoint ⟨D, q * 16⟩
  k_s : (⟨K, M.len⟩ : Region).Disjoint ⟨S, 2112⟩
  c_y : (⟨C, 16⟩ : Region).Disjoint ⟨Y, 16⟩
  c_d : (⟨C, 16⟩ : Region).Disjoint ⟨D, q * 16⟩
  c_s : (⟨C, 16⟩ : Region).Disjoint ⟨S, 2112⟩
  y_d : (⟨Y, 16⟩ : Region).Disjoint ⟨D, q * 16⟩
  y_s : (⟨Y, 16⟩ : Region).Disjoint ⟨S, 2112⟩
  d_s : (⟨D, q * 16⟩ : Region).Disjoint ⟨S, 2112⟩
  /-- The stack: `scratch` on it, and the return addresses of the call and of
  its calls, in the 24 bytes from `rsp - 16`. -/
  t_k : (⟨s.gpr .rsp - 16, 24⟩ : Region).Disjoint ⟨K, M.len⟩
  t_c : (⟨s.gpr .rsp - 16, 24⟩ : Region).Disjoint ⟨C, 16⟩
  t_y : (⟨s.gpr .rsp - 16, 24⟩ : Region).Disjoint ⟨Y, 16⟩
  t_d : (⟨s.gpr .rsp - 16, 24⟩ : Region).Disjoint ⟨D, q * 16⟩
  t_s : (⟨s.gpr .rsp - 16, 24⟩ : Region).Disjoint ⟨S, 2112⟩
  reads : Covers ([⟨K, M.len⟩, ⟨s.gpr .rsp, 8⟩] ++ [⟨C, 16⟩, ⟨Y, 16⟩, ⟨D, q * 16⟩, ⟨S, 2112⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨Y, 16⟩, ⟨D, q * 16⟩, ⟨S, 2112⟩] s.wr
  /-- What the key context holds, as its kind says. -/
  ok : M.ok s.mem K

theorem sep_of_disj {a b : Addr} {n k : Nat} (h : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) : Mem.Sep a n b k :=
  fun x h₁ h₂ => h x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)

namespace BlkCall

variable {M : Gcm.X86_64.Stitch.CtxMode} {s : State} {K C Y D S : Addr} {R q : Nat} (h : BlkCall M s K C Y D S R q)
include h

/-- The regions the callee may read and write. -/
abbrev rd (M : Gcm.X86_64.Stitch.CtxMode) (s : State) (K : Addr) : List Region := [⟨K, M.len⟩, ⟨s.gpr .rsp, 8⟩]
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

theorem arg_eq : stackArg (s.callEntry.withRegions (rd M s K) (wr C Y D S q)) 0 = S := by
  have hsa := stackArgAddr_eq (s := s) (rd M s K) (wr C Y D S q)
  have sep : Mem.Sep (s.gpr .rsp) (64 / 8) (s.gpr .rsp - 8) (64 / 8) := by
    have := Offset.sep_below (s.gpr .rsp) 8 (a := 0) (n := 8) (b := 8) (k := 8) (by decide) (by decide)
      (.inr (by decide)) (by decide) (by decide)
    simpa using this
  unfold stackArg; rw [hsa, State.withRegions_mem, State.callEntry_mem, Mem.readW_writeW_sep sep (by decide), h.arg]

theorem pre : Proof.AesGcm.blocksPreM M (s.callEntry.withRegions (rd M s K) (wr C Y D S q)) := by
  have hq : (BitVec.ofNat 64 q).toNat = q := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.w_d; omega)
  have hR : (BitVec.ofNat 64 R).toNat = R := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rcases h.rounds with h | h | h <;> omega)
  have hsa := stackArgAddr_eq (s := s) (rd M s K) (wr C Y D S q)
  have harg := h.arg_eq
  have hok : M.ok (s.callEntry.withRegions (rd M s K) (wr C Y D S q)).mem K := by
    rw [State.withRegions_mem]
    exact M.frame (callEntry_frame s) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.t_k.sub_left ret_sub).symm) h.w_k h.ok
  simp only [Proof.AesGcm.blocksPreM, Proof.AesGcm.args, Proof.AesGcm.arg, Proof.AesGcm.ret, Proof.AesGcm.stk,
    Proof.AesGcm.rounds, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.callEntry_rsp,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hq, hR, hsa, harg, Nat.mul_one]
  have bs := below_sub (s := s)
  have rs := ret_sub (s := s)
  have as := arg_sub (s := s)
  refine ⟨trivial, trivial, h.k_c, h.k_y, h.k_d, h.k_s, h.c_y, h.c_d, h.c_s, (h.t_c.sub_left as).symm, h.y_d, h.y_s,
    (h.t_y.sub_left as).symm, h.d_s, (h.t_d.sub_left as).symm, (h.t_s.sub_left as).symm,
    h.t_c.sub_left rs, h.t_y.sub_left rs, h.t_d.sub_left rs, h.t_s.sub_left rs,
    h.t_k.sub_left bs, h.t_c.sub_left bs, h.t_y.sub_left bs, h.t_d.sub_left bs, h.t_s.sub_left bs,
    h.w_k, h.w_c, h.w_y, h.w_d, h.w_s, h.w_sp, h.rounds, hok⟩

end BlkCall

theorem ctr_nosp_all (c : Proof.Aes.X86_64.Ctr32Impl) :
    c.callee.code.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]; intro i hi; simp [c.nosp i hi]

theorem gh_nosp_all (g : GhashImpl) : g.fn.code.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]; intro i hi; simp [g.nosp i hi]

theorem nosp_of_all {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c :=
  nosp_of (by rw [← Code.allInstrs_eq]; exact h)

section
variable (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} {aligned : Bool} (st : Option (StitchCode M aligned))

theorem encryptBlocks_nosp : NoSp (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc)) aligned (encFull st)) := by
  have hc := ctr_nosp_all v.ctr
  have hg := gh_nosp_all v.gh
  refine nosp_of_all ?_
  have hh := StitchImpl.head_nosp st (g := (·.full)) fun i => i.encP
  simp only [Blocks.encrypt, encFull, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.allInstrs,
    GcmImpl.callees, hh, hc, hg, Bool.true_and, Bool.and_true, Bool.false_eq_true, ite_false,
    ite_true]; decide +kernel

theorem decryptBlocks_nosp : NoSp (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec)) aligned) := by
  have hc := ctr_nosp_all v.ctr
  have hg := gh_nosp_all v.gh
  refine nosp_of_all ?_
  have hh := StitchImpl.head_nosp st (g := fun _ => false) fun i => i.decP
  rw [StitchImpl.any_false] at hh
  simp only [Blocks.decrypt, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.allInstrs,
    GcmImpl.callees, hh, hc, hg, Bool.true_and, Bool.and_true, Bool.false_eq_true, ite_false,
    ite_true]; decide +kernel

theorem encryptBlocks_depth : (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc)) aligned (encFull st)).depth = 1 := by
  have hh := StitchImpl.head_depth st (g := (·.full)) fun i => i.encP
  simp only [Blocks.encrypt, encFull, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall,
    Code.depth, GcmImpl.callees, hh, v.ctr.depth, v.gh.depth, Bool.false_eq_true, ite_false, ite_true]; decide

theorem decryptBlocks_depth : (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec)) aligned).depth = 1 := by
  have hh := StitchImpl.head_depth st (g := fun _ => false) fun i => i.decP
  rw [StitchImpl.any_false] at hh
  simp only [Blocks.decrypt, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall,
    Code.depth, GcmImpl.callees, hh, v.ctr.depth, v.gh.depth, Bool.false_eq_true, ite_false, ite_true]; decide

end

open Gcm.X86_64.Stitch (CtxMode) in
/-- An implementation of `vg_aes_gcm_encrypt_blocks` and `_decrypt_blocks`
for a key context of kind `M`, with what its callers need of it. -/
structure BlkFn (M : CtxMode) where
  enc : Fn
  dec : Fn
  encOk : ∀ s, (Proof.AesGcm.encryptBlocksX86_64M M).pre s →
    ∃ t s', Exec isa enc.code s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.encryptBlocksX86_64.post s s'
  decOk : ∀ s, (Proof.AesGcm.decryptBlocksX86_64M M).pre s →
    ∃ t s', Exec isa dec.code s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.decryptBlocksX86_64.post s s'
  encCt : ConstantTime isa (Proof.AesGcm.encryptBlocksX86_64M M).pre Proof.AesGcm.blocksPub enc.code
  decCt : ConstantTime isa (Proof.AesGcm.decryptBlocksX86_64M M).pre Proof.AesGcm.blocksPub dec.code
  encNosp : NoSp enc.code
  decNosp : NoSp dec.code
  encDepth : enc.code.depth = 1
  decDepth : dec.code.depth = 1
  encMx : enc.code.allInstrs (fun i => !loadsMxcsr i) = true
  decMx : dec.code.allInstrs (fun i => !loadsMxcsr i) = true
  encSp : enc.code.all (fun i => !X86_64.isa.writesSp i) = true
  decSp : dec.code.all (fun i => !X86_64.isa.writesSp i) = true
  encXd : enc.code.x86_64Depth ≤ 8
  decXd : dec.code.x86_64Depth ≤ 8

open Gcm.X86_64.Stitch (CtxMode) in
/-- `vg_aes_gcm_encrypt_blocks` and `_decrypt_blocks` calling `v`'s
implementations and interleaving with the loops `st`, named `e` and `d`. -/
def GcmImpl.blkM (v : GcmImpl) {M : CtxMode} {aligned : Bool} (st : Option (StitchCode M aligned)) (e d : String) : BlkFn M where
  enc := ⟨e, Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc)) aligned (encFull st)⟩
  dec := ⟨d, Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec)) aligned⟩
  encOk := encryptBlocksM_correct v st
  decOk := decryptBlocksM_correct v st
  encCt := Blocks.encrypt_ct v st
  decCt := Blocks.decrypt_ct v st
  encNosp := encryptBlocks_nosp v st
  decNosp := decryptBlocks_nosp v st
  encDepth := encryptBlocks_depth v st
  decDepth := decryptBlocks_depth v st
  encMx := encryptBlocks_mx v st
  decMx := decryptBlocks_mx v st
  encSp := encryptBlocks_spSafe v st
  decSp := decryptBlocks_spSafe v st
  encXd := encryptBlocks_xdepth v st
  decXd := decryptBlocks_xdepth v st

open Gcm.X86_64.Stitch (CtxMode) in
/-- `v`'s `vg_aes_gcm_encrypt_blocks` and `_decrypt_blocks`, for the key
context of `vg_aes_gcm_init`. -/
def GcmImpl.blkB (v : GcmImpl) : BlkFn CtxMode.base where
  enc := v.callees.enc
  dec := v.callees.dec
  encOk := by
    have h := (v.blkM (v.stitch.map (·.code CtxMode.base)) "" "").encOk
    simp only [GcmImpl.blkM, map_code_enc, StitchImpl.encFull_code] at h; exact h
  decOk := by
    have h := (v.blkM (v.stitch.map (·.code CtxMode.base)) "" "").decOk
    simp only [GcmImpl.blkM, map_code_dec] at h; exact h
  encCt := by
    have h := (v.blkM (v.stitch.map (·.code CtxMode.base)) "" "").encCt
    simp only [GcmImpl.blkM, map_code_enc, StitchImpl.encFull_code] at h; exact h
  decCt := by
    have h := (v.blkM (v.stitch.map (·.code CtxMode.base)) "" "").decCt
    simp only [GcmImpl.blkM, map_code_dec] at h; exact h
  encNosp := by
    have h := (v.blkM (v.stitch.map (·.code CtxMode.base)) "" "").encNosp
    simp only [GcmImpl.blkM, map_code_enc, StitchImpl.encFull_code] at h; exact h
  decNosp := by
    have h := (v.blkM (v.stitch.map (·.code CtxMode.base)) "" "").decNosp
    simp only [GcmImpl.blkM, map_code_dec] at h; exact h
  encDepth := by
    have h := (v.blkM (v.stitch.map (·.code CtxMode.base)) "" "").encDepth
    simp only [GcmImpl.blkM, map_code_enc, StitchImpl.encFull_code] at h; exact h
  decDepth := by
    have h := (v.blkM (v.stitch.map (·.code CtxMode.base)) "" "").decDepth
    simp only [GcmImpl.blkM, map_code_dec] at h; exact h
  encMx := encryptBlocks_mxB v v.stitch
  decMx := decryptBlocks_mxB v v.stitch
  encSp := encryptBlocks_spSafeB v v.stitch
  decSp := decryptBlocks_spSafeB v v.stitch
  encXd := encryptBlocks_xdepthB v v.stitch
  decXd := decryptBlocks_xdepthB v v.stitch

open Gcm.X86_64.Stitch (CtxMode) in
/-- `vg_aes_gcm_encrypt_blocks_precomputed` and `_decrypt_blocks_precomputed`,
calling `v`'s implementations and interleaving with its loops for that key
context (`GcmImpl.stitchP`). -/
def GcmImpl.blkP (v : GcmImpl) : BlkFn CtxMode.powers :=
  v.blkM v.stitchP (Spec.Gcm.encryptBlocksPrecomputedApi.name ++ v.suffix)
    (Spec.Gcm.decryptBlocksPrecomputedApi.name ++ v.suffix)

open Gcm.X86_64.Stitch (CtxMode) in
/-- `v`'s functions, with `B`'s `vg_aes_gcm_encrypt_blocks` and `_decrypt_blocks`. -/
def GcmImpl.withBlk (v : GcmImpl) {M : CtxMode} (B : BlkFn M) : Callees :=
  { v.callees with enc := B.enc, dec := B.dec }

theorem GcmImpl.withBlk_blkB (v : GcmImpl) : v.withBlk v.blkB = v.callees := rfl

/-- What a call leaves, besides its result. -/
structure BlkPost (s : State) (C Y D S : Addr) (q : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame (BlkCall.wr C Y D S q ++ [below (s.gpr .rsp) 16]) s.mem s'.mem

namespace BlkCall

variable {M : Gcm.X86_64.Stitch.CtxMode} {s : State} {K C Y D S : Addr} {R q : Nat} (h : BlkCall M s K C Y D S R q)
include h

/-- The values the call reads, at its entry, after the return address is stored. -/
theorem entry_eqs :
    Spec.Aes.bytesAt s.callEntry.mem K (16 * (R + 1)) = Spec.Aes.bytesAt s.mem K (16 * (R + 1)) ∧
      blockAt s.callEntry.mem C = blockAt s.mem C ∧ blockAt s.callEntry.mem Y = blockAt s.mem Y ∧
      blocksAt s.callEntry.mem D q = blocksAt s.mem D q ∧
      blockAt s.callEntry.mem (K + 240) = blockAt s.mem (K + 240) := by
  have fE := callEntry_frame s
  have rs : Region.Sub (below (s.gpr .rsp) 8) ⟨s.gpr .rsp - 16, 24⟩ := ret_sub (s := s)
  have hRb : 16 * (R + 1) ≤ 256 := by rcases h.rounds with h | h | h <;> subst h <;> decide
  refine ⟨bytesAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((h.t_k.sub_left rs).sub_right (Region.sub_prefix (Nat.le_trans hRb M.ge))).symm)
      (by have := h.w_k; have := M.ge; omega),
    blockAt_frame fE (disj_below (h.t_c.sub_left rs)), blockAt_frame fE (disj_below (h.t_y.sub_left rs)),
    blocksAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [Nat.mul_comm]; exact (h.t_d.sub_left rs).symm) (by have := h.w_d; omega),
    blockAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((h.t_k.sub_left rs).sub_right (Offset.sub_base (d := 240) _ (by have := M.ge; omega))).symm)⟩

end BlkCall

/-- A call of `vg_aes_gcm_encrypt_blocks`. -/
theorem blkE_call {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {s : State} {K C Y D S : Addr} {R q : Nat}
    (h : BlkCall M s K C Y D S R q) :
    WP isa (.call B.enc.name B.enc.code) s fun s' => BlkPost s C Y D S q s' ∧
      blocksAt s'.mem D q = ctr32 (aesWith R (Spec.Aes.bytesAt s.mem K (16 * (R + 1)))) (blockAt s.mem C)
        (blocksAt s.mem D q) ∧
      blockAt s'.mem C = Nat.repeat Spec.Gcm.inc32 q (blockAt s.mem C) ∧
      blockAt s'.mem Y = ghashFrom (blockAt s.mem (K + 240)) (blockAt s.mem Y) (blocksAt s'.mem D q) := by
  have hq : (BitVec.ofNat 64 q).toNat = q := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.w_d; omega)
  have hR : (BitVec.ofNat 64 R).toNat = R := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rcases h.rounds with h | h | h <;> omega)
  refine WP.call (k := Proof.AesGcm.encryptBlocksX86_64M M) B.encOk
    B.encNosp (by rw [B.encDepth]; decide)
    (rd := BlkCall.rd M s K) (wr := BlkCall.wr C Y D S q) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [B.encDepth] at hf
  obtain ⟨eK, eC, eY, eD, eH⟩ := h.entry_eqs
  simp only [Proof.AesGcm.encryptBlocksX86_64M, Proof.AesGcm.encryptBlocksX86_64, Spec.Gcm.ctxCiph, Spec.Gcm.ctxH, State.withRegions_gpr,
    State.withRegions_mem, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hq, hR, hm₂,
    eK, eC, eY, eD, eH] at hpost
  exact ⟨⟨hrd, hwr, hcs, hf⟩, hpost.1, hpost.2.1, by rw [hpost.1]; exact hpost.2.2⟩

/-- A call of `vg_aes_gcm_decrypt_blocks`. -/
theorem blkD_call {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {s : State} {K C Y D S : Addr} {R q : Nat}
    (h : BlkCall M s K C Y D S R q) :
    WP isa (.call B.dec.name B.dec.code) s fun s' => BlkPost s C Y D S q s' ∧
      blocksAt s'.mem D q = ctr32 (aesWith R (Spec.Aes.bytesAt s.mem K (16 * (R + 1)))) (blockAt s.mem C)
        (blocksAt s.mem D q) ∧
      blockAt s'.mem C = Nat.repeat Spec.Gcm.inc32 q (blockAt s.mem C) ∧
      blockAt s'.mem Y = ghashFrom (blockAt s.mem (K + 240)) (blockAt s.mem Y) (blocksAt s.mem D q) := by
  have hq : (BitVec.ofNat 64 q).toNat = q := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.w_d; omega)
  have hR : (BitVec.ofNat 64 R).toNat = R := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rcases h.rounds with h | h | h <;> omega)
  refine WP.call (k := Proof.AesGcm.decryptBlocksX86_64M M) B.decOk
    B.decNosp (by rw [B.decDepth]; decide)
    (rd := BlkCall.rd M s K) (wr := BlkCall.wr C Y D S q) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [B.decDepth] at hf
  obtain ⟨eK, eC, eY, eD, eH⟩ := h.entry_eqs
  simp only [Proof.AesGcm.decryptBlocksX86_64M, Proof.AesGcm.decryptBlocksX86_64, Spec.Gcm.ctxCiph, Spec.Gcm.ctxH, State.withRegions_gpr,
    State.withRegions_mem, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hq, hR, hm₂,
    eK, eC, eY, eD, eH] at hpost
  exact ⟨⟨hrd, hwr, hcs, hf⟩, hpost.1, hpost.2.1, hpost.2.2⟩

/-- Two calls of `vg_aes_gcm_encrypt_blocks` or `_decrypt_blocks` with the same
arguments leak the same. -/
theorem blk_pub {M : Gcm.X86_64.Stitch.CtxMode} {s₁ s₂ : State} {K C Y D S : Addr} {R q : Nat}
    (h₁ : BlkCall M s₁ K C Y D S R q) (h₂ : BlkCall M s₂ K C Y D S R q) (hsp : s₁.gpr .rsp = s₂.gpr .rsp) :
    Proof.AesGcm.blocksPub (s₁.callEntry.withRegions (BlkCall.rd M s₁ K) (BlkCall.wr C Y D S q))
      (s₂.callEntry.withRegions (BlkCall.rd M s₂ K) (BlkCall.wr C Y D S q)) := by
  simp only [Proof.AesGcm.blocksPub, Proof.AesGcm.arg, h₁.arg_eq, h₂.arg_eq, State.withRegions_gpr,
    State.callEntry_rsp, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp), h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₂.rdi,
    h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem blkE_rel {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C Y D S : Addr, ∃ R q : Nat,
      BlkCall M s₁ K C Y D S R q ∧ BlkCall M s₂ K C Y D S R q ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call B.enc.name B.enc.code) fun _ _ => True := by
  refine RelCT.callEx (k := Proof.AesGcm.encryptBlocksX86_64M M) B.encOk B.encCt fun s₁ s₂ hp => ?_
  obtain ⟨K, C, Y, D, S, R, q, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  exact ⟨_, _, _, _, h₁.pre, h₂.pre, blk_pub h₁ h₂ hsp, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩

theorem blkD_rel {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C Y D S : Addr, ∃ R q : Nat,
      BlkCall M s₁ K C Y D S R q ∧ BlkCall M s₂ K C Y D S R q ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call B.dec.name B.dec.code) fun _ _ => True := by
  refine RelCT.callEx (k := Proof.AesGcm.decryptBlocksX86_64M M) B.decOk B.decCt fun s₁ s₂ hp => ?_
  obtain ⟨K, C, Y, D, S, R, q, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  exact ⟨_, _, _, _, h₁.pre, h₂.pre, blk_pub h₁ h₂ hsp, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩

end VG.Proof.AesGcm.X86_64
