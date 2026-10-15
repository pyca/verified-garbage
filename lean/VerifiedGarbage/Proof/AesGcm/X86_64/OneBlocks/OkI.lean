module

public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Ok
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CallI
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM on x86-64: `oneBlocks` calling the function given the block index

Untrusted: everything here is checked by Lean. `oneBlocks` of
`vg_aes_gcm_decrypt_blocks_prepared_iv96` (`oneBlocksDI_ok`) does what
`oneBlocks` of `_decrypt_blocks` does (`oneBlocksD_ok`), from a state whose
`SP` points to the block index of the counter block (pushed by the caller in
a frame of its own): the call's push of `scratch` puts it below the index,
where the function reads it (`obFrameDI_ok`, from `BlkCallI`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith ctr32 ghashFrom inc32 ctrIndex)
open Gcm.X86_64.Stitch (CtxMode)

/-- A readable word is a region the permissions cover. -/
theorem covers_of_inRegions {ts : List Region} {a : Addr} {k : Nat} (h : InRegions ts a k) :
    Covers [⟨a, k⟩] ts := by
  obtain ⟨r, hr, hc⟩ := h
  intro x m ⟨r', hr', hc'⟩
  simp only [List.mem_singleton] at hr'; subst hr'
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc hc' ⊢
  have : (x - r.base).toNat ≤ (x - a).toNat + (a - r.base).toNat := by
    rw [← Offset.sub_add_sub_cancel x a r.base, BitVec.toNat_add]; exact Nat.mod_le _ _
  omega

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- The call of `vg_aes_gcm_decrypt_blocks_prepared_iv96`, from the frame's
push, from a state whose `SP` holds the block index of the counter block,
readable, with the two words below it apart from what the call writes. -/
theorem ObIn.callI {M : CtxMode} {R : Nat} {D : Addr} {n q : Nat} {s : State}
    (h : ObIn M Ctx St W SP R D n q s)
    (hidx : ctrIndex (blockAt s.mem (St + BitVec.ofNat 64 48)) = (s.mem.readW SP 64).setWidth 32)
    (a_st : (⟨SP - BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨St, 80⟩)
    (a_w : (⟨SP - BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨W, 2560⟩)
    (a_d : (⟨SP - BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨D, n⟩)
    (r_sp : InRegions (s.rd ++ s.wr) SP 8) (w_sp : SP.toNat + 8 ≤ 2 ^ 64) :
    BlkCallI M (pushed [.rax] s) Ctx (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 16) D
      (W + BitVec.ofNat 64 448) R q := by
  have hsp := h.env.rsp
  have hn8 : 8 * [Reg.rax].length ≤ (s.gpr .rsp).toNat := by rw [hsp]; have := h.sp24; simp; omega
  obtain ⟨hf, -⟩ := pushRegs_mem s [.rax] (by decide) hn8
  rw [hsp] at hf
  have psp : (pushed [.rax] s).gpr .rsp = SP - BitVec.ofNat 64 8 := by rw [pushed_rsp, hsp]; rfl
  have p8 : (pushed [.rax] s).gpr .rsp + BitVec.ofNat 64 8 = SP := by rw [psp]; exact BitVec.sub_add_cancel _ _
  obtain ⟨-, -, eC, -, -, -⟩ := ObIn.push_eqs L h
  have hq := h.q_le
  have qd : Region.Sub ⟨D, q * 16⟩ ⟨D, n⟩ := Region.sub_prefix (by omega)
  refine ⟨ObIn.call L h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p8, eC, hidx]
    exact congrArg (BitVec.setWidth 32) (hf.readW (a := SP) (w := 64) (r := ⟨SP, 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint_below SP (n := 8) (k := 8) (by decide)) (by decide)).symm
  · rw [psp]; exact a_st.sub_right (Lay.stSub (by decide))
  · rw [psp]; exact a_st.sub_right (Lay.stSub (by decide))
  · rw [psp]; exact a_d.sub_right qd
  · rw [psp]; exact a_w.sub_right (Lay.wSub (by decide))
  · rw [p8, pushed_rd, pushed_wr]
    obtain ⟨r, hr, hc⟩ := r_sp
    refine covers_of_inRegions ⟨r, ?_, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ hr, List.mem_append_right _ (List.mem_cons_of_mem _ hr)]
  · have e16 : SP - BitVec.ofNat 64 8 - 8 = SP - BitVec.ofNat 64 16 := by rw [← Offset.sub_add_eq]; rfl
    rw [psp, e16]; have := h.sp24
    rw [toNat_sub_ofNat (by omega)]; omega

/-- The frame of the call of `vg_aes_gcm_decrypt_blocks_prepared_iv96`, from a
state whose `SP` holds the block index of the counter block, readable, with
the two words below it apart from what the call writes. -/
theorem obFrameDI_ok {M : CtxMode} (F : DecFnI M) {R : Nat} {D : Addr} {n q : Nat} {s : State}
    (h : ObIn M Ctx St W SP R D n q s)
    (hidx : ctrIndex (blockAt s.mem (St + BitVec.ofNat 64 48)) = (s.mem.readW SP 64).setWidth 32)
    (a_st : (⟨SP - BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨St, 80⟩)
    (a_w : (⟨SP - BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨W, 2560⟩)
    (a_d : (⟨SP - BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨D, n⟩)
    (r_sp : InRegions (s.rd ++ s.wr) SP 8) (w_sp : SP.toNat + 8 ≤ 2 ^ 64) :
    WP isa (.frame (.push [.rax]) (.call F.fn.name F.fn.code) (.pop .rax 1)) s fun s₄ =>
      (∀ r ∈ calleeSaved, s₄.gpr r = s.gpr r) ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
      Frame (obFrame St W SP D q) s.mem s₄.mem ∧
      blocksAt s₄.mem D q = ctr32 (aesWith R (bytesAt s.mem Ctx (16 * (R + 1))))
        (blockAt s.mem (St + BitVec.ofNat 64 48)) (blocksAt s.mem D q) ∧
      blockAt s₄.mem (St + BitVec.ofNat 64 48) =
        Nat.repeat Spec.Gcm.inc32 q (blockAt s.mem (St + BitVec.ofNat 64 48)) ∧
      blockAt s₄.mem (St + BitVec.ofNat 64 16) = Spec.Gcm.ghashFrom (blockAt s.mem (Ctx + 240))
        (blockAt s.mem (St + BitVec.ofNat 64 16)) (blocksAt s.mem D q) := by
  have hsp := h.env.rsp
  have hn8 : 8 * [Reg.rax].length ≤ (s.gpr .rsp).toNat := by rw [hsp]; have := h.sp24; simp; omega
  obtain ⟨-, eK, eC, eY, eD, eH⟩ := ObIn.push_eqs L h
  have hI := ObIn.callI L h hidx a_st a_w a_d r_sp w_sp
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.mono (blkDI_call F hI) fun s₃ ⟨bp, o₁, o₂, o₃⟩ => ?_)
  obtain ⟨r₃, w₃, cs, rd, wr, fr⟩ := ObIn.popped L h bp
  rw [eK, eC, eD] at o₁
  rw [eC] at o₂
  rw [eH, eY, eD] at o₃
  exact ⟨r₃, w₃, cs, rd, wr, fr, by rw [popped_mem]; exact o₁, by rw [popped_mem]; exact o₂,
    by rw [popped_mem]; exact o₃⟩

end

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) {M : CtxMode}
include L

/-- `oneBlocks` of the decrypting function given the block index, from a
state whose `SP` holds the block index of the counter block. -/
theorem oneBlocksDI_ok (F : DecFnI M) {R : Nat} {D : Addr} {n : Nat} {s : State} (h : ObPre M Ctx W SP R D n s)
    (hidx : ctrIndex (blockAt s.mem (cbA W)) = (s.mem.readW SP 64).setWidth 32)
    (a_w : (⟨SP - BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨W, 2560⟩)
    (a_d : (⟨SP - BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨D, n⟩)
    (r_sp : InRegions (s.rd ++ s.wr) SP 8) (w_sp : SP.toNat + 8 ≤ 2 ^ 64) :
    WP isa (oneBlocks F.fn) s fun s' => ObPost Ctx W SP D n s s' ∧ OutD Ctx W R D (n / 16) s s' := by
  obtain ⟨-, -, -, eK, eC, eY, eB, eH, -⟩ := w192_eqs L h (BitVec.ofNat 64 n)
  have a_st : (⟨SP - BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 16, 80⟩ :=
    a_w.sub_right (Lay.wSub (by decide))
  have sep : Mem.Sep SP (64 / 8) (W + BitVec.ofNat 64 192) (64 / 8) := by
    have hs : Region.Sub ⟨SP, 8⟩ ⟨SP - BitVec.ofNat 64 8, 16⟩ := by
      have := Offset.sub_base (SP - BitVec.ofNat 64 8) (d := 8) (n := 8) (k := 16) (by decide)
      rwa [BitVec.sub_add_cancel] at this
    exact sep_of_disj ((a_w.sub_right (Lay.wSub (d := 192) (n := 8) (by decide))).sub_left hs)
  refine oneBlocks_core L _ h (fun s₂ hi hm hrd hwr => obFrameDI_ok L F hi ?_ a_st a_w a_d
      (by rw [hrd, hwr]; exact r_sp) w_sp) (fun hz s₁ m₁ => ?_) (fun s₂ s₄ s₅ m₂ o f => ?_)
  · rw [hm, eC, Mem.readW_writeW_sep sep (by decide)]; exact hidx
  · rw [OutD, hz, m₁, eC, eY]; exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨a₁, a₂, a₃⟩ := ob_after L h f
    obtain ⟨o₁, o₂, o₃⟩ := o
    simp only [m₂, eK, eC, eB, eY, eH] at o₁ o₂ o₃
    exact ⟨a₁.trans o₁, a₂.trans o₂, by rw [a₃]; exact o₃⟩

end

end VG.Proof.AesGcm.X86_64
