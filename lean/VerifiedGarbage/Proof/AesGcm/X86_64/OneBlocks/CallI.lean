module

public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call
public import VerifiedGarbage.Proof.AesGcm.X86_64.Iv96Contract
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM on x86-64: calling `vg_aes_gcm_decrypt_blocks_prepared_iv96`

Untrusted: everything here is checked by Lean. As `OneBlocks/Call.lean`, for
the function given the block index: from a state whose `rsp` points to
`scratch`, with the index in the word above it (`BlkCallI`), and what the call
leaves (`blkDI_call`). The function is given with its proofs (`DecFnI`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ctr32 aesWith ctrIndex)
open Gcm.X86_64.Stitch (CtxMode)

/-- An implementation of `vg_aes_gcm_decrypt_blocks_prepared_iv96` for a key
context of kind `M`, with what its callers need of it. -/
structure DecFnI (M : CtxMode) where
  fn : Fn
  ok : ∀ s, (Proof.AesGcm.decryptBlocksIv96X86_64M M).pre s →
    ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.decryptBlocksX86_64.post s s'
  ct : ConstantTime isa (Proof.AesGcm.decryptBlocksIv96X86_64M M).pre Proof.AesGcm.blocksPubI fn.code
  nosp : NoSp fn.code
  depth : fn.code.depth = 1
  mx : fn.code.allInstrs (fun i => !loadsMxcsr i) = true
  sp : fn.code.all (fun i => !X86_64.isa.writesSp i) = true
  xd : fn.code.x86_64Depth ≤ 8

/-- What a call of `vg_aes_gcm_decrypt_blocks_prepared_iv96` needs: `BlkCall`,
and the block index in the word above `scratch`, readable and apart from what
the call writes. -/
structure BlkCallI (M : CtxMode) (s : State) (K C Y D S : Addr) (R q : Nat) : Prop
    extends BlkCall M s K C Y D S R q where
  idx : ctrIndex (blockAt s.mem C) = (s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64).setWidth 32
  a_c : (⟨s.gpr .rsp, 16⟩ : Region).Disjoint ⟨C, 16⟩
  a_y : (⟨s.gpr .rsp, 16⟩ : Region).Disjoint ⟨Y, 16⟩
  a_d : (⟨s.gpr .rsp, 16⟩ : Region).Disjoint ⟨D, q * 16⟩
  a_s : (⟨s.gpr .rsp, 16⟩ : Region).Disjoint ⟨S, 2112⟩
  reads2 : Covers [⟨s.gpr .rsp + BitVec.ofNat 64 8, 8⟩] (s.rd ++ s.wr)
  w_sp2 : (s.gpr .rsp - 8).toNat + 24 ≤ 2 ^ 64

namespace BlkCallI

variable {M : CtxMode} {s : State} {K C Y D S : Addr} {R q : Nat} (h : BlkCallI M s K C Y D S R q)
include h

/-- The regions the callee may read: the key context, `scratch` and the index
(pushed apart). -/
abbrev rd (M : CtxMode) (s : State) (K : Addr) : List Region :=
  [⟨K, M.len⟩, ⟨s.gpr .rsp, 8⟩, ⟨s.gpr .rsp + BitVec.ofNat 64 8, 8⟩]

theorem pre : Proof.AesGcm.blocksPreMI M (s.callEntry.withRegions (rd M s K) (BlkCall.wr C Y D S q)) := by
  have h0 := h.toBlkCall
  have hp := h0.pre
  have hq : (BitVec.ofNat 64 q).toNat = q := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h0.w_d; omega)
  have hR : (BitVec.ofNat 64 R).toNat = R := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rcases h0.rounds with h | h | h <;> omega)
  have hsa := BlkCall.stackArgAddr_eq (s := s) (rd M s K) (BlkCall.wr C Y D S q)
  have hsa' := BlkCall.stackArgAddr_eq (s := s) (BlkCall.rd M s K) (BlkCall.wr C Y D S q)
  have harg := h0.arg_eq
  have hsa1 : stackArgAddr (s.callEntry.withRegions (rd M s K) (BlkCall.wr C Y D S q)) 1 =
      s.gpr .rsp + BitVec.ofNat 64 8 := by
    simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp]
    bv_omega
  have sep1 : Mem.Sep (s.gpr .rsp + BitVec.ofNat 64 8) (64 / 8) (s.gpr .rsp - 8) (64 / 8) := by
    have e : s.gpr .rsp + BitVec.ofNat 64 8 = s.gpr .rsp - 8 + BitVec.ofNat 64 16 := by bv_omega
    have b := Offset.sep_base (s.gpr .rsp - 8) (n := 8) (e := 16) (k := 8) (by decide) (by decide)
    rw [e]; exact fun x h₁ h₂ => b x h₂ h₁
  have hidx : (stackArg (s.callEntry.withRegions (rd M s K) (BlkCall.wr C Y D S q)) 1).setWidth 32 =
      ctrIndex (blockAt s.mem C) := by
    unfold stackArg
    rw [hsa1, State.withRegions_mem, State.callEntry_mem, Mem.readW_writeW_sep sep1 (by decide), h.idx]
  obtain ⟨-, eC, -, -, -⟩ := h0.entry_eqs
  have eqA : (stackArg (s.callEntry.withRegions (rd M s K) (BlkCall.wr C Y D S q)) 0) =
      stackArg (s.callEntry.withRegions (BlkCall.rd M s K) (BlkCall.wr C Y D S q)) 0 := rfl
  simp only [Proof.AesGcm.blocksPreM, Proof.AesGcm.args, Proof.AesGcm.arg, Proof.AesGcm.ret, Proof.AesGcm.stk,
    Proof.AesGcm.rounds, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_mem, hsa', State.callEntry_rsp,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp),
    h0.rdi, h0.rsi, h0.rdx, h0.rcx, h0.r8, h0.r9, hq, hR, harg, Nat.mul_one] at hp
  simp only [Proof.AesGcm.blocksPreMI, Proof.AesGcm.args, Proof.AesGcm.arg, Proof.AesGcm.ret, Proof.AesGcm.stk,
    Proof.AesGcm.rounds, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_mem, hsa, eqA, State.callEntry_rsp,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp),
    h0.rdi, h0.rsi, h0.rdx, h0.rcx, h0.r8, h0.r9, hq, hR, harg, Nat.mul_one]
  obtain ⟨-, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, -, a₁₁, a₁₂, -, a₁₄, -, -, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂, a₂₃, a₂₄,
    a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂, a₃₃⟩ := hp
  have e8 : State.gpr (s.callEntry) .rsp = s.gpr .rsp - 8 := State.callEntry_rsp s
  have e8' : s.gpr .rsp - 8 + BitVec.ofNat 64 8 = s.gpr .rsp := BitVec.sub_add_cancel _ _
  have e16 : s.gpr .rsp - 8 + BitVec.ofNat 64 16 = s.gpr .rsp + BitVec.ofNat 64 8 := by
    rw [show BitVec.ofNat 64 16 = (8 : Addr) + BitVec.ofNat 64 8 from rfl, ← BitVec.add_assoc,
      BitVec.sub_add_cancel]
  refine ⟨by simp [rd], ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by rw [e8']; exact Region.contains_self _ _⟩,
    ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
      by rw [e16]; exact Region.contains_self _ _⟩, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, ?_, a₁₁, a₁₂, ?_, a₁₄, ?_, ?_, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂, a₂₃,
    a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, ?_, a₃₂, a₃₃, ?_⟩
  all_goals first
    | exact h.a_c.symm
    | exact h.a_y.symm
    | exact h.a_d.symm
    | exact h.a_s.symm
    | exact h.w_sp2
    | (rw [eC]; exact hidx.symm)

/-- The regions the call reads, covered by the caller's. -/
theorem readsI : Covers (rd M s K ++ BlkCall.wr C Y D S q) (s.rd ++ s.wr) := by
  have r := h.toBlkCall.reads
  intro a n ⟨r', hr', hc⟩
  rcases List.mem_append.mp hr' with hr' | hr'
  · simp only [rd, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact r a n ⟨_, by simp, hc⟩
    · exact r a n ⟨_, by simp, hc⟩
    · exact h.reads2 a n ⟨_, List.mem_singleton_self _, hc⟩
  · exact r a n ⟨r', List.mem_append_right _ hr', hc⟩

end BlkCallI

/-- A call of `vg_aes_gcm_decrypt_blocks_prepared_iv96`. -/
theorem blkDI_call {M : CtxMode} (F : DecFnI M) {s : State} {K C Y D S : Addr} {R q : Nat}
    (h : BlkCallI M s K C Y D S R q) :
    WP isa (.call F.fn.name F.fn.code) s fun s' => BlkPost s C Y D S q s' ∧
      blocksAt s'.mem D q = ctr32 (aesWith R (Spec.Aes.bytesAt s.mem K (16 * (R + 1)))) (blockAt s.mem C)
        (blocksAt s.mem D q) ∧
      blockAt s'.mem C = Nat.repeat Spec.Gcm.inc32 q (blockAt s.mem C) ∧
      blockAt s'.mem Y = ghashFrom (blockAt s.mem (K + 240)) (blockAt s.mem Y) (blocksAt s.mem D q) := by
  have h0 := h.toBlkCall
  have hq : (BitVec.ofNat 64 q).toNat = q := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h0.w_d; omega)
  have hR : (BitVec.ofNat 64 R).toNat = R := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rcases h0.rounds with h | h | h <;> omega)
  refine WP.call (k := Proof.AesGcm.decryptBlocksIv96X86_64M M) F.ok F.nosp (by rw [F.depth]; decide)
    (rd := BlkCallI.rd M s K) (wr := BlkCall.wr C Y D S q) h.pre h.readsI h0.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [F.depth] at hf
  obtain ⟨eK, eC, eY, eD, eH⟩ := h0.entry_eqs
  simp only [Proof.AesGcm.decryptBlocksIv96X86_64M, Proof.AesGcm.decryptBlocksX86_64, Spec.Gcm.ctxCiph,
    Spec.Gcm.ctxH, State.withRegions_gpr,
    State.withRegions_mem, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h0.rdi, h0.rsi, h0.rdx, h0.rcx, h0.r8, h0.r9, hq, hR, hm₂,
    eK, eC, eY, eD, eH] at hpost
  exact ⟨⟨hrd, hwr, hcs, hf⟩, hpost.1, hpost.2.1, hpost.2.2⟩

end VG.Proof.AesGcm.X86_64
