module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtx
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignPro
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import Mathlib.Tactic.Set

/-!
# RSASSA-PSS verification on x86-64: the precondition by name, the frame
and the prologue

`VPre` names the facts of `verifyK.pre`; the frame is the `frameBytes` bytes
below `rsp` (`fb`), within the stack the function uses (`vstkR`). From the
entry state, after the frame's push, `verifyPrologue` saves `rbx`, `rbp` and
`r12` and the arguments to their slots (`verifyPro_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)

variable (tsH tsG : List FnTable)

/-- `verifyK.pre`, by name. -/
structure VPre (s : State) : Prop where
  sp1 : verifyStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 88 ≤ 2 ^ 64
  tabH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem (stackArg s 8) (FnTable.words isa s T)
  tabG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem (stackArg s 9) (FnTable.words isa s T)
  hsy : (tabFns tsH ++ tabFns tsG).Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g)
  hrdE : s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩, ⟨stackArg s 8, 88⟩, ⟨stackArg s 9, 40⟩, ⟨stackArgAddr s 0, 80⟩]
  hwr : s.wr = [⟨stackArg s 4, (stackArg s 5).toNat * 8⟩]
  dns : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  des : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  ddgs : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  dsgs : (⟨stackArg s 0, (stackArg s 1).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  dsp : (⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
  dstH : (⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ : Region).Disjoint ⟨stackArg s 8, 88⟩
  dstG : (⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ : Region).Disjoint ⟨stackArg s 9, 40⟩
  dsa : (⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 80⟩
  dRn : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dRe : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dRdg : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dRsg : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  dRp : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
  dRtH : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 8, 88⟩
  dRtG : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 9, 40⟩
  dRa : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 80⟩
  dKn : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKe : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dKdg : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dKsg : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  dKp : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
  dKtH : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨stackArg s 8, 88⟩
  dKtG : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨stackArg s 9, 40⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 80⟩
  wN : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wE : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wDg : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wSg : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wS : (stackArg s 4).toNat + (stackArg s 5).toNat * 8 ≤ 2 ^ 64
  preWrap : (stackArg s 6).toNat + (stackArg s 7).toNat * 8 ≤ 2 ^ 64
  wTH : (stackArg s 8).toNat + 88 ≤ 2 ^ 64
  wTG : (stackArg s 9).toNat + 40 ≤ 2 ^ 64
  lv : Spec.Rsa.lenValid (s.gpr .rsi).toNat
  L1 : 1 ≤ (s.gpr .rcx).toNat
  L2 : (s.gpr .rcx).toNat ≤ (s.gpr .rsi).toNat
  hsg : (stackArg s 1).toNat = (s.gpr .rsi).toNat
  hsw : Spec.RsaPss.publicScratchWords (s.gpr .rsi).toNat ≤ (stackArg s 5).toNat
  preLen : (stackArg s 7).toNat = Spec.Rsa.precomputedWords (s.gpr .rsi).toNat
  hdl : Spec.RsaPss.digestLenOk 64 s.mem (stackArg s 8) (s.gpr .r9)

theorem VPre.of {s : State} (h : (verifyK tsH tsG).pre s) : VPre tsH tsG s := by
  simp only [verifyK] at h
  obtain ⟨sp1, sp2, tabH, tabG, hsy, hrdE, hwr, dns, des, ddgs, dsgs, dsp, dstH, dstG, dsa, dRn, dRe, dRdg, dRsg, dRs, dRp, dRtH, dRtG, dRa, dKn, dKe, dKdg, dKsg, dKs, dKp, dKtH, dKtG, dKa, wN, wE, wDg, wSg, wS, preWrap, wTH, wTG, lv, L1, L2, hsg, hsw, preLen, hdl⟩ := h
  exact ⟨sp1, sp2, tabH, tabG, hsy, hrdE, hwr, dns, des, ddgs, dsgs, dsp, dstH, dstG, dsa, dRn, dRe, dRdg, dRsg, dRs, dRp, dRtH, dRtG, dRa, dKn, dKe, dKdg, dKsg, dKs, dKp, dKtH, dKtG, dKa, wN, wE, wDg, wSg, wS, preWrap, wTH, wTG, lv, L1, L2, hsg, hsw, preLen, hdl⟩

variable {tsH tsG}

theorem VPre.k1 {s : State} (hp : VPre tsH tsG s) : 64 ≤ (s.gpr .rsi).toNat := hp.lv.1
theorem VPre.k2 {s : State} (hp : VPre tsH tsG s) : (s.gpr .rsi).toNat ≤ 1024 := hp.lv.2
theorem VPre.hsl {s : State} (hp : VPre tsH tsG s) :
    8 * (((s.gpr .rsi).toNat + 7) / 8) + 48 + 1024 ≤ (stackArg s 5).toNat := by
  have := hp.hsw
  unfold Spec.RsaPss.publicScratchWords Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords at this; omega

/-- The regions read: those of the inputs, and of the arguments. -/
theorem VPre.hrd {s : State} (hp : VPre tsH tsG s) :
    Covers [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArgAddr s 0, 80⟩] s.rd := by
  rw [hp.hrdE]
  apply Covers.of_sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩

theorem VPre.pre {s : State} (hp : VPre tsH tsG s) : InRegions s.rd (stackArg s 6) ((stackArg s 7).toNat * 8) := by
  rw [hp.hrdE]; exact ⟨_, by simp, Region.contains_self _ _⟩

theorem VPre.args {s : State} (hp : VPre tsH tsG s) : InRegions s.rd (stackArgAddr s 0) 80 := by
  rw [hp.hrdE]; exact ⟨_, by simp, Region.contains_self _ _⟩

/-! ## The frame -/

/-- The stack the function uses, below `rsp`. -/
def vstkR (s : State) : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩

theorem vframe_sub (s : State) : Region.Sub ⟨fb s, frameBytes⟩ (vstkR s) :=
  Offset.sub_below _ (by decide) (by decide)

theorem vret_sub (s : State) : Region.Sub (below (fb s) 16) (vstkR s) := by
  simp only [below, fb, sub_sub']
  exact Offset.sub_below _ (by decide) (by decide)

/-- The region the function writes: its stack and `scratch`. -/
def vscrR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩

abbrev vwrR (s : State) : List Region := [vstkR s, vscrR s]

/-- An input, apart from them. -/
theorem vin_apart {s : State} {R : Region} (hK : (vstkR s).Disjoint R) (hS : R.Disjoint (vscrR s)) :
    ∀ r ∈ vwrR s, R.Disjoint r := by
  intro r hr
  simp only [vwrR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hK.symm
  · exact hS

/-- An address of an input: in no writable region of the frame's state, nor
below the frame. -/
theorem VPre.outside {s : State} (hp : VPre tsH tsG s) {R : Region}
    (hS : R.Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩) (hK : (vstkR s).Disjoint R) {a : Addr}
    (ha : R.Contains a 1) : Outside (⟨fb s, frameBytes⟩ :: s.wr) (fb s) a := by
  refine ⟨fun r hr hc => ?_, fun hc => hK a (vret_sub s a hc) ha⟩
  rw [List.mem_cons, hp.hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hK a (vframe_sub s a hc) ha
  · exact hS a ha hc


theorem vfb_toNat {s : State} (hp : VPre tsH tsG s) : (fb s).toNat + frameBytes = (s.gpr .rsp).toNat := by
  have := hp.sp1; unfold verifyStack at this
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega

theorem VPre.geo {s : State} (hp : VPre tsH tsG s) : Geo (fb s) (stackArg s 4) := by
  have hF := vfb_toNat hp
  have := hp.sp2
  have hsl := hp.hsl
  have hk := hp.k1
  have wS := hp.wS
  have sS : Region.Sub ⟨stackArg s 4, oRsa⟩ ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ :=
    Region.sub_prefix (by unfold oRsa; omega)
  refine ⟨by omega, by unfold oRsa; omega, ((hp.dKs.sub_left (vframe_sub s)).sub_right sS),
    ((hp.dKs.sub_left (vret_sub s)).sub_right sS)⟩

/-- Stack argument `j`, read from memory changed only in the frame. -/
theorem varg_read {s : State} (hp : VPre tsH tsG s) {m : Mem} (hf : Frame [frR s] s.mem m) {j : Nat} (hj : j < 10) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := ⟨stackArgAddr s 0, 80⟩) ?_ (fun r' hr' => ?_) (by decide)
  · rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
    have := hp.sp2
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.dKa.sub_left (vframe_sub s)).symm

/-- The address of stack argument `j` is readable. -/
theorem varg_in {s : State} (hp : VPre tsH tsG s) {u : State} (hrd : u.rd = s.rd) {j : Nat} (hj : j < 10)
    (n : Nat := 8) (hn : n ≤ 8 := by decide) :
    InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) n := by
  have := hp.sp2
  rw [hrd]
  apply hp.hrd.left
  refine ⟨⟨stackArgAddr s 0, 80⟩, by simp, ?_⟩
  rw [argAddr, show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
    simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
  exact Offset.contains_base _ (by omega) (by omega)

theorem vframe_w {s : State} (hp : VPre tsH tsG s) {m m' : Mem} (hf : Frame [frR s] m m') {d : Nat}
    (hd : d + 8 ≤ frameBytes) (v : BitVec 64) : Frame [frR s] m (m'.writeW (off (fb s) d) v) := by
  have hF := vfb_toNat hp
  have := hp.sp2
  exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

/-- One stack argument copied to a slot. -/
theorem vcopy1_ok {s : State} (hp : VPre tsH tsG s) {u : State} (hsp : u.gpr .rsp = fb s) (hfr : frR s ∈ u.wr)
    (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem) {j d : Nat} (hj : j < 10) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block [.mov .rax (.mem (arg j)), .store (sp d) .rax]) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j) ∧ Frame [frR s] s.mem u'.mem := by
  have hF := vfb_toNat hp
  have := hp.sp2
  have hsc : Scr u (fb s) frameBytes := Scr.of_mem hfr (by omega)
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j)) ?_ rfl)
    fun u' ⟨hm, k⟩ => ⟨k, hm, hm ▸ vframe_w hp hf hd _⟩
  xrun [arg, ea_sp, hsp, varg_in hp hrd hj, varg_read hp hf hj, hsc.st (d := d) hd]

/-- The slots `verifyPrologue` stores to, and what. -/
def vproW (s : State) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (fun k => word s.mem (fb s) (8 * k))
    41 (s.gpr .rbx)) 42 (s.gpr .rbp)) 43 (s.gpr .r12)) 18 (s.gpr .rdi)) 17 (s.gpr .rsi)) 19 (s.gpr .rdx))
    20 (s.gpr .rcx)) 37 (s.gpr .r8)) 38 (stackArg s 0)) 21 (stackArg s 4)) 22 (stackArg s 5)

theorem verifyPrologue_eq : verifyPrologue =
    ([.store (sp sRbx) .rbx, .store (sp sRbp) .rbp, .store (sp sR12) .r12, .store (sp sN) .rdi,
      .store (sp sK) .rsi, .store (sp sE) .rdx, .store (sp sEl) .rcx, .store (sp sDig) .r8] : List Instr) ++
    ([.mov .rax (.mem (arg 0)), .store (sp sSig) .rax] : List Instr) ++
    ([.mov .rax (.mem (arg 4)), .store (sp sScr) .rax] : List Instr) ++
    ([.mov .rax (.mem (arg 5)), .store (sp sScrLen) .rax] : List Instr) := rfl

/-- The prologue: the slots as `vproW` says, the working space untouched. -/
theorem verifyPro_ok {s : State} (hp : VPre tsH tsG s) :
    WP isa (.block verifyPrologue) (allocState frameBytes s) fun t => Keep [.rax] (allocState frameBytes s) t ∧
      Lay t (fb s) (stackArg s 4) ∧ Rep t.mem (fb s) (stackArg s 4) (fun o => s.mem (off (stackArg s 4) o)) (vproW s) ∧
      Frame [frR s] s.mem t.mem := by
  have hF := vfb_toNat hp
  have := hp.sp2
  have G' := hp.geo
  set A := allocState frameBytes s with hA
  have hsp : A.gpr .rsp = fb s := rfl
  have hfr : frR s ∈ A.wr := List.mem_cons_self ..
  have hsc : Scr A (fb s) frameBytes := Scr.of_mem hfr (by omega)
  have R0 : Rep s.mem (fb s) (stackArg s 4) (fun o => s.mem (off (stackArg s 4) o))
      (fun k => word s.mem (fb s) (8 * k)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  rw [verifyPrologue_eq, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  have R1 := ((((((((R0.wf G' (k := 41) (by decide) (s.gpr .rbx)).wf G' (k := 42) (by decide) (s.gpr .rbp)).wf G'
    (k := 43) (by decide) (s.gpr .r12)).wf G' (k := 18) (by decide) (s.gpr .rdi)).wf G' (k := 17) (by decide)
    (s.gpr .rsi)).wf G' (k := 19) (by decide) (s.gpr .rdx)).wf G' (k := 20) (by decide) (s.gpr .rcx)).wf G'
    (k := 37) (by decide) (s.gpr .r8))
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = (((((((s.mem.writeW (off (fb s) (8 * 41)) (s.gpr .rbx)).writeW
      (off (fb s) (8 * 42)) (s.gpr .rbp)).writeW (off (fb s) (8 * 43)) (s.gpr .r12)).writeW (off (fb s) (8 * 18))
      (s.gpr .rdi)).writeW (off (fb s) (8 * 17)) (s.gpr .rsi)).writeW (off (fb s) (8 * 19)) (s.gpr .rdx)).writeW
      (off (fb s) (8 * 20)) (s.gpr .rcx)).writeW (off (fb s) (8 * 37)) (s.gpr .r8)) ?_ rfl) fun t1 ⟨hm1, k1⟩ => ?_
  · xrun [ea_sp, hsp, hsc.st (d := sRbx) (by decide), hsc.st (d := sRbp) (by decide), hsc.st (d := sR12) (by decide),
      hsc.st (d := sN) (by decide), hsc.st (d := sK) (by decide), hsc.st (d := sE) (by decide),
      hsc.st (d := sEl) (by decide), hsc.st (d := sDig) (by decide), allocState_gpr']
    rfl
  have f1 : Frame [frR s] s.mem t1.mem := by
    rw [hm1]
    exact vframe_w hp (vframe_w hp (vframe_w hp (vframe_w hp (vframe_w hp (vframe_w hp (vframe_w hp (vframe_w hp
      (Frame.refl _ _) (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _)
      (by decide) _) (by decide) _) (by decide) _
  have sp1 : t1.gpr .rsp = fb s := k1.gpr (by decide)
  refine WP.mono (vcopy1_ok hp sp1 (k1.2.2 ▸ hfr) k1.2.1 f1 (j := 0) (d := sSig) (by decide) (by decide))
    fun t2 ⟨k2, hm2, f2⟩ => ?_
  refine WP.mono (vcopy1_ok hp ((k2.gpr (by decide)).trans sp1) (k2.2.2 ▸ k1.2.2 ▸ hfr) (k2.2.1.trans k1.2.1) f2
    (j := 4) (d := sScr) (by decide) (by decide)) fun t3 ⟨k3, hm3, f3⟩ => ?_
  have k23 := k2.trans k3
  refine WP.mono (vcopy1_ok hp ((k23.gpr (by decide)).trans sp1) (k23.2.2 ▸ k1.2.2 ▸ hfr) (k23.2.1.trans k1.2.1) f3
    (j := 5) (d := sScrLen) (by decide) (by decide)) fun t4 ⟨k4, hm4, f4⟩ => ?_
  have k13 : Keep [.rax] A t4 := (k1.trans (k23.trans k4)).mono (by decide)
  have R3 : Rep t4.mem (fb s) (stackArg s 4) (fun o => s.mem (off (stackArg s 4) o)) (vproW s) := by
    rw [hm4, hm3, hm2, hm1]
    exact ((R1.wf G' (k := 38) (by decide) (stackArg s 0)).wf G' (k := 21) (by decide) (stackArg s 4)).wf G'
      (k := 22) (by decide) (stackArg s 5)
  have := hp.sp1
  have h392 : frameBytes = 392 := rfl
  have hvs : verifyStack = 808 := rfl
  refine ⟨k13, ⟨(k13.gpr (by decide)).trans hsp, k13.2.2 ▸ hfr, by omega, by omega, ?_, ?_, G'.dFS, G'.dRS⟩, R3, f4⟩
  · have hsl := hp.hsl
    have hk := hp.k1
    refine ⟨⟨stackArg s 4, 0, (stackArg s 5).toNat * 8, by rw [k13.2.2, hA]; simp [allocState, hp.hwr],
      (BitVec.add_zero _).symm, by unfold oRsa; omega, Nat.le_trans (by omega) hp.wS⟩, G'.Sw⟩
  · rw [show sScr = 8 * 21 from rfl]
    exact (R3.fr 21 (by decide)).trans (by simp [vproW, upd])

/-! ## The salt length's arguments -/

theorem zext32_beq_zero (x : BitVec 32) : (BitVec.setWidth 64 x == 0) = decide (x = 0) := by
  by_cases h : x = 0
  · subst h; rfl
  · have : BitVec.setWidth 64 x ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_setWidth] at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      exact this))
    rw [beq_eq_false_iff_ne.mpr this, decide_eq_false h]

end VG.Proof.RsaPss.X86_64
