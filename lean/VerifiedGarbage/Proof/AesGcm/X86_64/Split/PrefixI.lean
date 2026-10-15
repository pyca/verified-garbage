module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixOk
public import VerifiedGarbage.Proof.AesGcm.X86_64.Iv96Contract
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.OkI
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM `seal_split` on x86-64: `prefix` calling the function given the block index

Untrusted: everything here is checked by Lean. `prefix`, a word lower than
`SP` would be without it, with the word at `SP` holding the block index of
the counter block (2): the call of
`vg_aes_gcm_encrypt_blocks_to_prepared_iv96` pushes its three stack
arguments right below that word, so the index is its fourth. Its
precondition is `encryptBlocksToX86_64M`'s at that call (`callIn`), with the
index word readable and apart from what the call writes (`callPreI`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (covers_cons' covers_nil' sub_add_ofNat)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32 ctrIndex)

/-- `vg_aes_gcm_encrypt_blocks_to_prepared_iv96`, as `prefix` calls it. -/
structure BlkToFnI (M : CtxMode) where
  fn : Fn
  ok : ∀ s, (Proof.AesGcm.encryptBlocksToIv96X86_64M M).pre s →
    ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.AesGcm.encryptBlocksToIv96X86_64M M).post s s'
  ct : ConstantTime isa (Proof.AesGcm.encryptBlocksToIv96X86_64M M).pre Proof.AesGcm.blocksToPubI fn.code
  sp : SpSafe fn.code
  xd : fn.code.x86_64Depth ≤ 24
  mx : fn.code.allInstrs (fun i => !loadsMxcsr i) = true
  spAll : fn.code.all (fun i => !X86_64.isa.writesSp i) = true

/-- The regions the call reads: `callRd`, and the index word at `SP`. -/
abbrev callRdI (M : CtxMode) (Ctx SP S : Addr) (q : Nat) : List Region :=
  callRd M Ctx SP S q ++ [⟨SP, 8⟩]

/-- The state the call starts from. -/
abbrev callUI (M : CtxMode) (Ctx W SP D S : Addr) (q : Nat) (st : State) : State :=
  (pushed [.rax, .r10, .r11] st).callEntry.withRegions (callRdI M Ctx SP S q) (callWr W D q)

/-- What `prefix` needs of the index word at `SP`: the counter block's index
is 2, the word holds it, it is readable, and the call's four stack arguments
(its three, then it) are apart from the state and the data. -/
structure IdxI (Ctx W SP D : Addr) (n : Nat) (s : State) : Prop where
  cb : ctrIndex (blockAt s.mem (cbA W)) = 2
  w : (s.mem.readW SP 64).setWidth 32 = 2
  r : InRegions (s.rd ++ s.wr) SP 8
  aw : (⟨SP - BitVec.ofNat 64 24, 32⟩ : Region).Disjoint ⟨W, 2560⟩
  ad : (⟨SP - BitVec.ofNat 64 24, 32⟩ : Region).Disjoint ⟨D, n⟩
  top : SP.toNat + 8 ≤ 2 ^ 64

/-- Covered region by region. -/
theorem covers_append {rs rs' ts : List Region} (h : Covers rs ts) (h' : Covers rs' ts) : Covers (rs ++ rs') ts :=
  fun a j ⟨r, hr, hc⟩ => by
    rcases List.mem_append.mp hr with hr | hr
    · exact h a j ⟨r, hr, hc⟩
    · exact h' a j ⟨r, hr, hc⟩

section
variable {M : CtxMode} {Ctx W SP D S : Addr} {R n sl : Nat} {s : State} (h : PP M Ctx W SP D S R n sl s)
  (hI : IdxI Ctx W SP D n s)
include h hI

/-- What the call of `vg_aes_gcm_encrypt_blocks_to_prepared_iv96` starts
from: its precondition, and the regions it may access. -/
theorem callInI {q : Nat} (hq : 16 * q ≤ sl) {st : State}
    (hsp : st.gpr .rsp = SP) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) (hm : st.mem = s.mem)
    (h_di : st.gpr .rdi = Ctx) (h_si : st.gpr .rsi = BitVec.ofNat 64 R)
    (h_dx : st.gpr .rdx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)
    (h_cx : st.gpr .rcx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (h_8 : st.gpr .r8 = S)
    (h_9 : st.gpr .r9 = BitVec.ofNat 64 q) (h_10 : st.gpr .r10 = BitVec.ofNat 64 q) (h_11 : st.gpr .r11 = D)
    (h_ax : st.gpr .rax = W + BitVec.ofNat 64 448) :
    (Proof.AesGcm.encryptBlocksToIv96X86_64M M).pre (callUI M Ctx W SP D S q st) ∧
      Covers (callRdI M Ctx SP S q ++ callWr W D q)
        ((pushed [.rax, .r10, .r11] st).rd ++ (pushed [.rax, .r10, .r11] st).wr) ∧
      (Proof.AesGcm.arg (callUI M Ctx W SP D S q st) 3).setWidth 32 = 2 := by
  have L := h.lay
  have sp := h.sp56
  have top := hI.top
  have hn := h.data.ok.lt
  obtain ⟨hpre, cr, -, -, hU, a0, a1, a2⟩ := callIn h hq hsp hrd hwr hm h_di h_si h_dx h_cx h_8 h_9 h_10 h_11 h_ax
  -- The callee's view without the index: the same registers and memory.
  obtain ⟨-, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, -, b13, b14, b15, -, b17, b18, b19, -, -, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, -, b40, b41⟩ := hpre
  have hP : (pushed [.rax, .r10, .r11] st).gpr .rsp = SP - BitVec.ofNat 64 24 := by rw [pushed_rsp, hsp]; rfl
  have hn8 : 8 * [Reg.rax, .r10, .r11].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega
  have hpf := (pushRegs_mem st [.rax, .r10, .r11] (by decide) hn8).1
  rw [hsp] at hpf
  have hE : Frame [⟨SP - BitVec.ofNat 64 32, 8⟩] (pushed [.rax, .r10, .r11] st).mem
      (pushed [.rax, .r10, .r11] st).callEntry.mem := by
    have := callEntry_frame (pushed [.rax, .r10, .r11] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  have fS : Frame [below SP 56] st.mem (pushed [.rax, .r10, .r11] st).callEntry.mem :=
    (hpf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, stk56_sub (by decide) (by decide)⟩).trans
      (hE.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, stk56_sub (by decide) (by decide)⟩)
  have hU' : (callUI M Ctx W SP D S q st).gpr .rsp = SP - BitVec.ofNat 64 32 := hU
  have e8 : SP - BitVec.ofNat 64 32 + BitVec.ofNat 64 8 = SP - BitVec.ofNat 64 24 := sub_add_ofNat _ (by decide)
  have e32 : SP - BitVec.ofNat 64 32 + BitVec.ofNat 64 32 = SP := BitVec.sub_add_cancel _ _
  have hA4 : Proof.AesGcm.args (callUI M Ctx W SP D S q st) 4 = ⟨SP - BitVec.ofNat 64 24, 32⟩ := by
    simp only [Proof.AesGcm.args, stackArgAddr, hU', e8]
  -- The index word, at `SP`, outside the 56 bytes below it.
  have kI : (⟨SP, 8⟩ : Region).Disjoint (below SP 56) := Offset.base_disjoint_below SP (by omega)
  have harg : Proof.AesGcm.arg (callUI M Ctx W SP D S q st) 3 = s.mem.readW SP 64 := by
    simp only [Proof.AesGcm.arg, stackArg, stackArgAddr, State.withRegions_mem, hU',
      show 8 * (3 + 1) = 32 from rfl, e32]
    rw [fS.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact kI) (by decide), hm]
  have hidx : ctrIndex (blockAt (callUI M Ctx W SP D S q st).mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)) =
      (Proof.AesGcm.arg (callUI M Ctx W SP D S q st) 3).setWidth 32 := by
    have cW : Region.Sub (cbR W) ⟨W, 2560⟩ := fun a hc => st_w a (cb_sub a hc)
    rw [harg, State.withRegions_mem, blockAt_frame fS (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h.kw.sub_right cW).symm), hm]
    exact hI.cb.trans hI.w.symm
  have cbW : Region.Sub (cbR W) ⟨W, 2560⟩ := fun a hc => st_w a (cb_sub a hc)
  have yW : Region.Sub (yR W) ⟨W, 2560⟩ := fun a hc => st_w a (y_sub a hc)
  have ds : Region.Sub ⟨D, q * 16⟩ ⟨D, n⟩ := Region.sub_prefix (by have := h.sl_le; omega)
  have hsp32 : (SP - BitVec.ofNat 64 32).toNat = SP.toNat - 32 := toNat_sub_ofNat (by omega)
  have hrdU : (callUI M Ctx W SP D S q st).rd = callRdI M Ctx SP S q := rfl
  have hwrU : (callUI M Ctx W SP D S q st).wr = callWr W D q := rfl
  have hdi : (callUI M Ctx W SP D S q st).gpr .rdi = Ctx := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), pushed_gpr _ _ (by decide), h_di]
  have hr8 : (callUI M Ctx W SP D S q st).gpr .r8 = S := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), pushed_gpr _ _ (by decide), h_8]
  have hr9 : (callUI M Ctx W SP D S q st).gpr .r9 = BitVec.ofNat 64 q := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), pushed_gpr _ _ (by decide), h_9]
  have hdx : (callUI M Ctx W SP D S q st).gpr .rdx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48 := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), pushed_gpr _ _ (by decide), h_dx]
  have hqn : (BitVec.ofNat 64 q).toNat = q := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.sl_le; omega)
  refine ⟨⟨?_, ?_, ?_, ?_, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, ?_, b13, b14, b15, ?_, b17, b18, b19, ?_, ?_, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, ?_, b40, b41, ?_⟩, ?_, by rw [harg]; exact hI.w⟩
  · rw [hrdU, hdi]; simp
  · rw [hrdU, hr8, hr9, hqn]; simp
  · rw [hrdU, hU', e8]; exact covers_of_mem (by simp)
  · rw [hrdU, hU', e32]; exact ⟨_, by simp, Region.contains_self _ _⟩
  · rw [hA4, hdx]; exact (hI.aw.sub_right cbW).symm
  · rw [hA4]
    have hcx : (callUI M Ctx W SP D S q st).gpr .rcx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16 := by
      rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), pushed_gpr _ _ (by decide), h_cx]
    rw [hcx]; exact (hI.aw.sub_right yW).symm
  · have a0' : Proof.AesGcm.arg (callUI M Ctx W SP D S q st) 0 = D := a0
    have a1' : Proof.AesGcm.arg (callUI M Ctx W SP D S q st) 1 = BitVec.ofNat 64 q := a1
    rw [hA4, a0', a1', hqn]; exact (hI.ad.sub_right ds).symm
  · have a2' : Proof.AesGcm.arg (callUI M Ctx W SP D S q st) 2 = W + BitVec.ofNat 64 448 := a2
    rw [hA4, a2']; exact (hI.aw.sub_right sc_w).symm
  · rw [hU', hsp32]; omega
  · rw [hdx]; exact hidx
  · intro a j ⟨r, hr, hc⟩
    simp only [callRdI, List.append_assoc, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl | hr
    · exact cr a j ⟨r, List.mem_append_left _ hr, hc⟩
    · obtain ⟨t, ht, htc⟩ := covers_of_inRegions hI.r a j ⟨_, List.mem_singleton_self _, hc⟩
      rw [pushed_rd, pushed_wr, hrd, hwr]
      rcases List.mem_append.mp ht with ht | ht
      · exact ⟨t, List.mem_append_left _ ht, htc⟩
      · exact ⟨t, List.mem_append_right _ (List.mem_cons_of_mem _ ht), htc⟩
    · exact cr a j ⟨r, List.mem_append_right _ hr, hc⟩

/-- `prefix` calling `vg_aes_gcm_encrypt_blocks_to_prepared_iv96` (`T`): as
`prefix_ok`. -/
theorem prefix_okI (T : BlkToFnI M) :
    WP isa (SealSplit.prefix T.fn) s (PPost Ctx W SP D S R n sl 56 s) :=
  prefix_okG h T.fn fun hq _ hsp hrd hwr hm h_di h_si h_dx h_cx h_8 h_9 h_10 h_11 h_ax =>
    have c := callInI h hI hq hsp hrd hwr hm h_di h_si h_dx h_cx h_8 h_9 h_10 h_11 h_ax
    preCall_okG h _ rfl T.fn T.ok T.sp T.xd hq hsp hrd hwr hm h_di h_si h_dx h_cx h_8 h_9 h_10 h_11 h_ax _ c.1 c.2.1

end

end VG.Proof.AesGcm.X86_64.Split
