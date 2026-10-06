import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCtx
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# RSAES-OAEP encryption on x86-64: the precondition by name, and the frame

`EPre` names the facts of `encK.pre`; the frame is the `frameBytes` bytes
below `rsp` (`fb`), within the stack the function uses (`stkR`).
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)

variable (H : Spec.Mgf1.Hash) {G : Spec.Mgf1.Hash}

/-- `encK.pre`, by name. -/
structure EPre (s : State) : Prop where
  sp1 : encStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 64 ≤ 2 ^ 64
  hrd : s.rd = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩, ⟨stackArg s 4, H.len⟩, ⟨stackArgAddr s 0, 56⟩]
  hwr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩]
  d_out_n : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  d_out_e : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  d_out_lb : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  d_out_ms : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  d_out_sd : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 4, H.len⟩
  d_out_scr : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  d_out_args : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 56⟩
  d_n_scr : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  d_e_scr : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  d_lb_scr : (⟨stackArg s 0, (stackArg s 1).toNat⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  d_ms_scr : (⟨stackArg s 2, (stackArg s 3).toNat⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  d_sd_scr : (⟨stackArg s 4, H.len⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  d_scr_args : (⟨stackArg s 5, (stackArg s 6).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 56⟩
  d_ret_out : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  d_ret_n : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  d_ret_e : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  d_ret_lb : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  d_ret_ms : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  d_ret_sd : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 4, H.len⟩
  d_ret_scr : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  d_ret_args : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 56⟩
  d_stk_out : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  d_stk_n : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  d_stk_e : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  d_stk_lb : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  d_stk_ms : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  d_stk_sd : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨stackArg s 4, H.len⟩
  d_stk_scr : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  d_stk_args : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 56⟩
  wO : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wN : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wE : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wL : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wM : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wSd : (stackArg s 4).toNat + H.len ≤ 2 ^ 64
  wS : (stackArg s 5).toNat + (stackArg s 6).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .rcx).toNat
  k2 : (s.gpr .rcx).toNat ≤ 1024
  hsi : (s.gpr .rsi).toNat = (s.gpr .rcx).toNat
  L1 : 1 ≤ (s.gpr .r9).toNat
  L2 : (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat
  hsl : 16 * (s.gpr .rcx).toNat + 1024 ≤ (stackArg s 6).toNat

theorem EPre.of {s : State} (h : (encK H G).pre s) : EPre H s := by
  simp only [encK] at h
  obtain ⟨sp1, sp2, hrd, hwr, d_out_n, d_out_e, d_out_lb, d_out_ms, d_out_sd, d_out_scr, d_out_args, d_n_scr, d_e_scr, d_lb_scr, d_ms_scr, d_sd_scr, d_scr_args, d_ret_out, d_ret_n, d_ret_e, d_ret_lb, d_ret_ms, d_ret_sd, d_ret_scr, d_ret_args, d_stk_out, d_stk_n, d_stk_e, d_stk_lb, d_stk_ms, d_stk_sd, d_stk_scr, d_stk_args, wO, wN, wE, wL, wM, wSd, wS, ⟨k1, k2⟩, hsi, L1, L2, hsl⟩ := h
  exact ⟨sp1, sp2, hrd, hwr, d_out_n, d_out_e, d_out_lb, d_out_ms, d_out_sd, d_out_scr, d_out_args, d_n_scr, d_e_scr, d_lb_scr, d_ms_scr, d_sd_scr, d_scr_args, d_ret_out, d_ret_n, d_ret_e, d_ret_lb, d_ret_ms, d_ret_sd, d_ret_scr, d_ret_args, d_stk_out, d_stk_n, d_stk_e, d_stk_lb, d_stk_ms, d_stk_sd, d_stk_scr, d_stk_args, wO, wN, wE, wL, wM, wSd, wS, k1, k2, hsi, L1, L2, by unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hsl; omega⟩

/-! ## The frame -/

/-- The frame's base: `rsp` in the frame. -/
abbrev fb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 frameBytes

/-- The stack the function uses, below `rsp`. -/
def stkR (s : State) : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩

theorem sub_sub' (p : Addr) (a b : Nat) : p - BitVec.ofNat 64 a - BitVec.ofNat 64 b = p - BitVec.ofNat 64 (a + b) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add]

theorem frame_sub (s : State) : Region.Sub ⟨fb s, frameBytes⟩ (stkR s) :=
  Offset.sub_below _ (by decide) (by decide)

theorem ret_sub (s : State) : Region.Sub (below (fb s) 16) (stkR s) := by
  simp only [below, fb, sub_sub']
  exact Offset.sub_below _ (by decide) (by decide)

variable {H}

theorem fb_toNat {s : State} (hp : EPre H s) : (fb s).toNat + frameBytes = (s.gpr .rsp).toNat := by
  have := hp.sp1; unfold encStack at this
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega

theorem EPre.geo {s : State} (hp : EPre H s) : Geo (fb s) (stackArg s 5) := by
  have hF := fb_toNat hp
  have := hp.sp2
  have hsl := hp.hsl
  have hk := hp.k1
  have wS := hp.wS
  have sS : Region.Sub ⟨stackArg s 5, oRsa⟩ ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩ :=
    Region.sub_prefix (by unfold oRsa; omega)
  refine ⟨by unfold frameBytes at *; omega, by unfold oRsa; omega,
    ((hp.d_stk_scr.sub_left (frame_sub s)).sub_right sS), ((hp.d_stk_scr.sub_left (ret_sub s)).sub_right sS)⟩

/-- The address of stack argument `j`, from the frame. -/
theorem argAddr (s : State) (j : Nat) : off (fb s) (frameBytes + 8 + 8 * j) = stackArgAddr s j := by
  simp only [off, fb, stackArgAddr]
  rw [show frameBytes + 8 + 8 * j = frameBytes + 8 * (j + 1) by omega, BitVec.ofNat_add, ← BitVec.add_assoc,
    BitVec.sub_add_cancel]

theorem allocState_gpr' (bytes : Nat) (s : State) (r : Reg) :
    (allocState bytes s).gpr r = if r = .rsp then s.gpr .rsp - BitVec.ofNat 64 bytes else s.gpr r := rfl

/-- The frame's region. -/
abbrev frR (s : State) : Region := ⟨fb s, frameBytes⟩

theorem stackArgAddr_j (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega

/-- Stack argument `j`, read from memory changed only in the frame. -/
theorem arg_read {s : State} (hp : EPre H s) {m : Mem} (hf : Frame [frR s] s.mem m) {j : Nat} (hj : j < 7) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := ⟨stackArgAddr s 0, 56⟩) ?_ (fun r' hr' => ?_) (by decide)
  · rw [stackArgAddr_j s j]
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.d_stk_args.sub_left (frame_sub s)).symm

/-- One stack argument copied to a slot. -/
theorem copy1_ok {s : State} (hp : EPre H s) {u : State} (hsp : u.gpr .rsp = fb s) (hfr : frR s ∈ u.wr)
    (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem) {j d : Nat} (hj : j < 7) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block (argSlot j d)) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j) ∧ Frame [frR s] s.mem u'.mem := by
  have hF := fb_toNat hp
  have := hp.sp2
  have hsc : Scr u (fb s) frameBytes := Scr.of_mem hfr (by unfold frameBytes at *; omega)
  have hin : InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
    refine ⟨⟨stackArgAddr s 0, 56⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp), ?_⟩
    rw [argAddr, stackArgAddr_j s j]
    exact Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j)) ?_ rfl)
    fun u' ⟨hm, k⟩ => ⟨k, hm, hm ▸ hf.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by unfold frameBytes at *; omega))⟩
  xrun [argSlot, arg, ea_sp, hsp, hin, arg_read hp hf hj, hsc.st (d := d) hd]

theorem frame_w {s : State} (hp : EPre H s) {m m' : Mem} (hf : Frame [frR s] m m') {d : Nat}
    (hd : d + 8 ≤ frameBytes) (v : BitVec 64) : Frame [frR s] m (m'.writeW (off (fb s) d) v) := by
  have hF := fb_toNat hp
  have := hp.sp2
  exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by unfold frameBytes at *; omega))

/-- The slots `encPrologue` stores to, and what. -/
def encW (s : State) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (fun k => word s.mem (fb s) (8 * k))
    21 (s.gpr .rdi)) 22 (s.gpr .rdx)) 23 (s.gpr .rcx)) 24 (s.gpr .r8)) 25 (s.gpr .r9))
    27 (stackArg s 0)) 28 (stackArg s 1)) 29 (stackArg s 2)) 30 (stackArg s 3)) 31 (stackArg s 4))
    14 (stackArg s 5)) 26 (stackArg s 6)

theorem encPrologue_eq : encPrologue =
    ([.store (sp sOut) .rdi, .store (sp sN) .rdx, .store (sp sK) .rcx, .store (sp sE) .r8,
      .store (sp sEl) .r9] : List Instr) ++ argSlot 0 sLab ++ argSlot 1 sLabLen ++ argSlot 2 sMsg ++
    argSlot 3 sMsgLen ++ argSlot 4 sSeed ++ argSlot 5 sScr ++ argSlot 6 sScrLen := rfl

/-- The prologue: the slots as `encW` says, the working space untouched. -/
theorem encPro_ok {s : State} (hp : EPre H s) :
    WP isa (.block encPrologue) (allocState frameBytes s) fun t => Keep [.rax] (allocState frameBytes s) t ∧
      Lay t (fb s) (stackArg s 5) ∧ Rep t.mem (fb s) (stackArg s 5) (fun o => s.mem (off (stackArg s 5) o)) (encW s) ∧
      Frame [frR s] s.mem t.mem := by
  have hF := fb_toNat hp
  have := hp.sp2
  have G' := hp.geo
  have hsp : (allocState frameBytes s).gpr .rsp = fb s := rfl
  have hfr : frR s ∈ (allocState frameBytes s).wr := List.mem_cons_self ..
  have hsc : Scr (allocState frameBytes s) (fb s) frameBytes := Scr.of_mem hfr (by unfold frameBytes at *; omega)
  have R0 : Rep s.mem (fb s) (stackArg s 5) (fun o => s.mem (off (stackArg s 5) o))
      (fun k => word s.mem (fb s) (8 * k)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  rw [encPrologue_eq, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  have R1 := ((((R0.wf G' (k := 21) (by decide) (s.gpr .rdi)).wf G' (k := 22) (by decide) (s.gpr .rdx)).wf G'
    (k := 23) (by decide) (s.gpr .rcx)).wf G' (k := 24) (by decide) (s.gpr .r8)).wf G' (k := 25) (by decide)
    (s.gpr .r9)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = ((((s.mem.writeW (off (fb s) (8 * 21)) (s.gpr .rdi)).writeW
      (off (fb s) (8 * 22)) (s.gpr .rdx)).writeW (off (fb s) (8 * 23)) (s.gpr .rcx)).writeW (off (fb s) (8 * 24))
      (s.gpr .r8)).writeW (off (fb s) (8 * 25)) (s.gpr .r9)) ?_ rfl) fun t1 ⟨hm1, k1⟩ => ?_
  · xrun [ea_sp, hsp, hsc.st (d := sOut) (by decide), hsc.st (d := sN) (by decide), hsc.st (d := sK) (by decide),
      hsc.st (d := sE) (by decide), hsc.st (d := sEl) (by decide), allocState_gpr']
    rfl
  have f1 : Frame [frR s] s.mem t1.mem := by
    rw [hm1]
    exact frame_w hp (frame_w hp (frame_w hp (frame_w hp (frame_w hp (Frame.refl _ _) (by decide) _) (by decide) _)
      (by decide) _) (by decide) _) (by decide) _
  have sp1 : t1.gpr .rsp = fb s := k1.gpr (by decide)
  have hfr1 : frR s ∈ t1.wr := k1.2.2 ▸ hfr
  refine WP.mono (copy1_ok hp sp1 hfr1 k1.2.1 f1 (j := 0) (d := sLab) (by decide) (by decide))
    fun t2 ⟨k2, hm2, f2⟩ => ?_
  refine WP.mono (copy1_ok hp ((k2.gpr (by decide)).trans sp1) (k2.2.2 ▸ hfr1) (k2.2.1.trans k1.2.1) f2
    (j := 1) (d := sLabLen) (by decide) (by decide)) fun t3 ⟨k3, hm3, f3⟩ => ?_
  have k23 := k2.trans k3
  refine WP.mono (copy1_ok hp ((k23.gpr (by decide)).trans sp1) (k23.2.2 ▸ hfr1) (k23.2.1.trans k1.2.1) f3
    (j := 2) (d := sMsg) (by decide) (by decide)) fun t4 ⟨k4, hm4, f4⟩ => ?_
  have k24 := k23.trans k4
  refine WP.mono (copy1_ok hp ((k24.gpr (by decide)).trans sp1) (k24.2.2 ▸ hfr1) (k24.2.1.trans k1.2.1) f4
    (j := 3) (d := sMsgLen) (by decide) (by decide)) fun t5 ⟨k5, hm5, f5⟩ => ?_
  have k25 := k24.trans k5
  refine WP.mono (copy1_ok hp ((k25.gpr (by decide)).trans sp1) (k25.2.2 ▸ hfr1) (k25.2.1.trans k1.2.1) f5
    (j := 4) (d := sSeed) (by decide) (by decide)) fun t6 ⟨k6, hm6, f6⟩ => ?_
  have k26 := k25.trans k6
  refine WP.mono (copy1_ok hp ((k26.gpr (by decide)).trans sp1) (k26.2.2 ▸ hfr1) (k26.2.1.trans k1.2.1) f6
    (j := 5) (d := sScr) (by decide) (by decide)) fun t7 ⟨k7, hm7, f7⟩ => ?_
  have k27 := k26.trans k7
  refine WP.mono (copy1_ok hp ((k27.gpr (by decide)).trans sp1) (k27.2.2 ▸ hfr1) (k27.2.1.trans k1.2.1) f7
    (j := 6) (d := sScrLen) (by decide) (by decide)) fun t8 ⟨k8, hm8, f8⟩ => ?_
  have k18 : Keep [.rax] (allocState frameBytes s) t8 := (k1.trans (k27.trans k8)).mono (by decide)
  have R8 : Rep t8.mem (fb s) (stackArg s 5) (fun o => s.mem (off (stackArg s 5) o)) (encW s) := by
    rw [hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1]
    exact ((((((R1.wf G' (k := 27) (by decide) (stackArg s 0)).wf G' (k := 28) (by decide) (stackArg s 1)).wf G'
      (k := 29) (by decide) (stackArg s 2)).wf G' (k := 30) (by decide) (stackArg s 3)).wf G' (k := 31)
      (by decide) (stackArg s 4)).wf G' (k := 14) (by decide) (stackArg s 5)).wf G' (k := 26) (by decide)
      (stackArg s 6)
  have := hp.sp1
  refine ⟨k18, ⟨(k18.gpr (by decide)).trans hsp, k18.2.2 ▸ hfr, ?_, ?_, ?_, ?_, G'.dFS, G'.dRS⟩, R8, f8⟩
  · unfold encStack at this; unfold frameBytes at *; omega
  · unfold frameBytes at *; omega
  · have hsl := hp.hsl
    have hk := hp.k1
    refine ⟨⟨stackArg s 5, 0, (stackArg s 6).toNat * 8, by rw [k18.2.2]; simp [allocState, hp.hwr],
      (BitVec.add_zero _).symm, by unfold oRsa; omega, hp.wS.trans' (by omega)⟩, G'.Sw⟩
  · rw [show sScr = 8 * 14 from rfl]
    exact (R8.fr 14 (by decide)).trans (by simp [encW, upd])

end VG.Proof.RsaOaep.X86_64
