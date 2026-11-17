module

public import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
public import VerifiedGarbage.Proof.RsaPss.X86_64.Loops
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCorrect
import VerifiedGarbage.Proof.RsaPss.EncodeEq
public import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.RsaPss.X86_64.Params
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCall
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCtx
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncParams
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignPro

/-! ### `RsaPss.X86_64.EncFrame`, which this module and modules that import it used -/

section

/-!
# EMSA-PSS's encoding on x86-64: the precondition by name, the frame and the
prologue

`Pre` names the facts of `encK.pre`; the frame is the `frameBytes` bytes
below `rsp` (`fb`), within the stack the function uses (`stkR`). From the
entry state, after the frame's push, `encPrologue` saves `rbx`, `rbp` and
`r12`, the arguments to their slots, and the mask and `lo = 0`
(`encPro_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Enc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)

variable (T : Tabs)

/-- `encK.pre`, by name. -/
structure Pre (s : State) : Prop where
  sp1 : encStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64
  hrd : s.rd = [⟨s.gpr .rdx, T.H.D⟩, ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, ⟨stackArg s 2, 56⟩, ⟨stackArg s 3, 56⟩,
    ⟨stackArgAddr s 0, 32⟩]
  hwr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩]
  dOdg : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, T.H.D⟩
  dOsa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  dOs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
  dOa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 32⟩
  ddgs : (⟨s.gpr .rdx, T.H.D⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
  dsas : (⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
  dsa : (⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 32⟩
  dRo : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dRdg : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, T.H.D⟩
  dRsa : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
  dRa : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 32⟩
  dKo : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKdg : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨s.gpr .rdx, T.H.D⟩
  dKsa : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint
    ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint
    ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 32⟩
  wO : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wDg : (s.gpr .rdx).toNat + T.H.D ≤ 2 ^ 64
  wSa : (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  wS : (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64
  b1 : 1 ≤ (s.gpr .r9).toNat
  b2 : (s.gpr .r9).toNat ≤ Proof.RsaPss.maxEmBits
  hel : (s.gpr .rsi).toNat = Spec.RsaPss.emLength (s.gpr .r9).toNat
  hsl : 1024 ≤ (stackArg s 1).toNat
  dOtH : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 2, 56⟩
  dOtG : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 3, 56⟩
  dstH : (⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ : Region).Disjoint ⟨stackArg s 2, 56⟩
  dstG : (⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ : Region).Disjoint ⟨stackArg s 3, 56⟩
  dRtH : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 2, 56⟩
  dRtG : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 3, 56⟩
  dKtH : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨stackArg s 2, 56⟩
  dKtG : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨stackArg s 3, 56⟩
  wTH : (stackArg s 2).toNat + 56 ≤ 2 ^ 64
  wTG : (stackArg s 3).toNat + 56 ≤ 2 ^ 64
  tabs : TabsAt T.H T.dn T.f T.G T.g (stackArg s 2) (stackArg s 3) s

theorem Pre.of {Hs Gs : Spec.Mgf1.Hash} {s : State} (h : (encK T Hs Gs).pre s) : Pre T s := by
  simp only [encK] at h
  obtain ⟨sp1, sp2, hrd, hwr, dOdg, dOsa, dOs, dOa, ddgs, dsas, dsa, dRo, dRdg, dRsa, dRs, dRa, dKo, dKdg,
    dKsa, dKs, dKa, wO, wDg, wSa, wS, b1, b2, hel, hsl, dOtH, dOtG, dstH, dstG, dRtH, dRtG, dKtH, dKtG, wTH, wTG,
    tabs⟩ := h
  exact ⟨sp1, sp2, hrd, hwr, dOdg, dOsa, dOs, dOa, ddgs, dsas, dsa, dRo, dRdg, dRsa, dRs, dRa, dKo, dKdg,
    dKsa, dKs, dKa, wO, wDg, wSa, wS, b1, b2, hel, hsl, dOtH, dOtG, dstH, dstG, dRtH, dRtG, dKtH, dKtG, wTH, wTG,
    tabs⟩

variable {T}

theorem Pre.k2 {s : State} (hp : Pre T s) : (s.gpr .rsi).toNat ≤ 1024 := by
  have := hp.hel; have := hp.b2; unfold Spec.RsaPss.emLength Proof.RsaPss.maxEmBits at *; omega_arith

/-! ## The frame -/

/-- The stack the function uses, below `rsp`. -/
def stkR (s : State) : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩

theorem frame_sub (s : State) : Region.Sub ⟨fb s, frameBytes⟩ (stkR s) :=
  Offset.sub_below _ (by decide) (by decide)

theorem ret_sub (s : State) : Region.Sub (below (fb s) 16) (stkR s) := by
  simp only [below, fb, sub_sub']
  exact Offset.sub_below _ (by decide) (by decide)

def outR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
def scrR (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩

/-- The three regions the function writes. -/
abbrev wrR (s : State) : List Region := [stkR s, outR s, scrR s]

/-- An input, apart from them. -/
theorem in_apart {s : State} {R : Region} (hK : (stkR s).Disjoint R) (hO : (outR s).Disjoint R)
    (hS : R.Disjoint (scrR s)) : ∀ r ∈ wrR s, R.Disjoint r := by
  intro r hr
  simp only [wrR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hK.symm
  · exact hO.symm
  · exact hS

/-- An address of an input: in no writable region of the frame's state, nor
below the frame. -/
theorem Pre.outside {s : State} (hp : Pre T s) {R : Region}
    (hO : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint R)
    (hS : R.Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩) (hK : (stkR s).Disjoint R) {a : Addr}
    (ha : R.Contains a 1) : Outside (⟨fb s, frameBytes⟩ :: s.wr) (fb s) a := by
  refine ⟨fun r hr hc => ?_, fun hc => hK a (ret_sub s a hc) ha⟩
  rw [List.mem_cons, hp.hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hK a (frame_sub s a hc) ha
  · exact hO a hc ha
  · exact hS a ha hc

theorem fb_toNat {s : State} (hp : Pre T s) : (fb s).toNat + frameBytes = (s.gpr .rsp).toNat := by
  have := hp.sp1; unfold encStack at this
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega_using [this]

theorem Pre.geo {s : State} (hp : Pre T s) : Geo (fb s) (stackArg s 0) := by
  have hF := fb_toNat hp
  have := hp.sp2
  have hsl := hp.hsl
  have wS := hp.wS
  have sS : Region.Sub ⟨stackArg s 0, oRsa⟩ ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ :=
    Region.sub_prefix (by unfold oRsa; omega_using [hsl])
  refine ⟨by omega_using [hF, this], by unfold oRsa; omega_using [hsl, wS], ((hp.dKs.sub_left (frame_sub s)).sub_right sS),
    ((hp.dKs.sub_left (ret_sub s)).sub_right sS)⟩

/-- Memory changed only in the frame. -/
theorem frame_wrR {s : State} {m : Mem} (h : Frame [frR s] s.mem m) : Frame (wrR s) s.mem m :=
  h.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub s⟩

/-- Memory changed only in the writable regions and below the frame. -/
theorem frame_keep {s u v : State} (hp : Pre T s) (hw : u.wr = frR s :: s.wr) (hsp : u.gpr .rsp = fb s)
    (hM : Frame (wrR s) s.mem u.mem)
    (hk : ∀ a, (∀ r ∈ u.wr, ¬ r.Contains a 1) → ¬ (below (u.gpr .rsp) 16).Contains a 1 → v.mem a = u.mem a) :
    Frame (wrR s) s.mem v.mem := by
  intro x hx
  refine (hk x (fun r hr hc => ?_) (fun hc => ?_)).trans (hM x hx)
  · rw [hw, hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hx _ (List.mem_cons_self ..) (frame_sub s x hc)
    · exact hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hc
    · exact hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) hc
  · rw [hsp] at hc; exact hx _ (List.mem_cons_self ..) (ret_sub s x hc)

/-! ## The prologue -/

/-- Stack argument `j`, read from memory changed only in the frame. -/
theorem arg_read {s : State} (hp : Pre T s) {m : Mem} (hf : Frame [frR s] s.mem m) {j : Nat} (hj : j < 4) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := ⟨stackArgAddr s 0, 32⟩) ?_ (fun r' hr' => ?_) (by decide)
  · rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_using []]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  · simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.dKa.sub_left (frame_sub s)).symm

theorem frame_w {s : State} (hp : Pre T s) {m m' : Mem} (hf : Frame [frR s] m m') {d : Nat}
    (hd : d + 8 ≤ frameBytes) (v : BitVec 64) : Frame [frR s] m (m'.writeW (off (fb s) d) v) := by
  have hF := fb_toNat hp
  have := hp.sp2
  exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd, hF]))

/-- The slots `encPrologue` stores to, and what, before the mask. -/
def proW (s : State) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd (fun k => word s.mem (fb s) (8 * k))
    41 (s.gpr .rbx)) 42 (s.gpr .rbp)) 43 (s.gpr .r12)) 16 (s.gpr .rdi)) 17 (s.gpr .rsi)) 37 (s.gpr .rdx))
    39 (s.gpr .rcx)) 40 (s.gpr .r8)) 21 (stackArg s 0)

/-- And after it. -/
def proW' (s : State) : Nat → BitVec 64 :=
  upd (upd (proW s) 25 (BitVec.setWidth 64 ((0xFF : Byte) >>>
    (8 * Spec.RsaPss.emLength (s.gpr .r9).toNat - (s.gpr .r9).toNat)))) 26 0

/-- One stack argument copied to a slot. -/
theorem copy1_ok {s : State} (hp : Pre T s) {u : State} (hsp : u.gpr .rsp = fb s) (hfr : frR s ∈ u.wr)
    (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem) {j d : Nat} (hj : j < 4) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block [.mov .rax (.mem (arg j)), .store (sp d) .rax]) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j) ∧ Frame [frR s] s.mem u'.mem := by
  have hF := fb_toNat hp
  have := hp.sp2
  have hsc : Scr u (fb s) frameBytes := Scr.of_mem hfr (by omega_using [hF])
  have hin : InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
    refine ⟨⟨stackArgAddr s 0, 32⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp), ?_⟩
    rw [argAddr, show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_using []]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j)) ?_ rfl)
    fun u' ⟨hm, k⟩ => ⟨k, hm, hm ▸ hf.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd, hF]))⟩
  xrun [arg, ea_sp, hsp, hin, arg_read hp hf hj, hsc.st (d := d) hd]

theorem encPrologue_eq : encPrologue =
    ([.store (sp sRbx) .rbx, .store (sp sRbp) .rbp, .store (sp sR12) .r12, .store (sp sOut) .rdi,
      .store (sp sK) .rsi, .store (sp sDig) .rdx, .store (sp sSalt) .rcx, .store (sp sSaltLen) .r8] : List Instr) ++
    ([.mov .rax (.mem (arg 0)), .store (sp sScr) .rax] : List Instr) ++ maskBits .r9 := rfl

/-- The prologue: the slots as `proW'` says, the working space untouched. -/
theorem encPro_ok {s : State} (hp : Pre T s) :
    WP isa (.block encPrologue) (allocState frameBytes s) fun t => Keep [.rax, .rcx] (allocState frameBytes s) t ∧
      Lay t (fb s) (stackArg s 0) ∧
      Rep t.mem (fb s) (stackArg s 0) (fun o => s.mem (off (stackArg s 0) o)) (proW' s) ∧
      Frame [frR s] s.mem t.mem := by
  have hF := fb_toNat hp
  have := hp.sp2
  have G' := hp.geo
  set A := allocState frameBytes s with hA
  have hsp : A.gpr .rsp = fb s := rfl
  have hfr : frR s ∈ A.wr := List.mem_cons_self ..
  have hsc : Scr A (fb s) frameBytes := Scr.of_mem hfr (by omega_using [hF])
  have R0 : Rep s.mem (fb s) (stackArg s 0) (fun o => s.mem (off (stackArg s 0) o))
      (fun k => word s.mem (fb s) (8 * k)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  rw [encPrologue_eq, WP.block_append_iff, WP.block_append_iff]
  have R1 := ((((((((R0.wf G' (k := 41) (by decide) (s.gpr .rbx)).wf G' (k := 42) (by decide) (s.gpr .rbp)).wf G'
    (k := 43) (by decide) (s.gpr .r12)).wf G' (k := 16) (by decide) (s.gpr .rdi)).wf G' (k := 17) (by decide)
    (s.gpr .rsi)).wf G' (k := 37) (by decide) (s.gpr .rdx)).wf G' (k := 39) (by decide) (s.gpr .rcx)).wf G'
    (k := 40) (by decide) (s.gpr .r8))
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = (((((((s.mem.writeW (off (fb s) (8 * 41)) (s.gpr .rbx)).writeW
      (off (fb s) (8 * 42)) (s.gpr .rbp)).writeW (off (fb s) (8 * 43)) (s.gpr .r12)).writeW (off (fb s) (8 * 16))
      (s.gpr .rdi)).writeW (off (fb s) (8 * 17)) (s.gpr .rsi)).writeW (off (fb s) (8 * 37)) (s.gpr .rdx)).writeW
      (off (fb s) (8 * 39)) (s.gpr .rcx)).writeW (off (fb s) (8 * 40)) (s.gpr .r8)) ?_ rfl) fun t1 ⟨hm1, k1⟩ => ?_
  · xrun [ea_sp, hsp, hsc.st (d := sRbx) (by decide), hsc.st (d := sRbp) (by decide),
      hsc.st (d := sR12) (by decide), hsc.st (d := sOut) (by decide), hsc.st (d := sK) (by decide),
      hsc.st (d := sDig) (by decide), hsc.st (d := sSalt) (by decide), hsc.st (d := sSaltLen) (by decide),
      allocState_gpr']
    rfl
  have f1 : Frame [frR s] s.mem t1.mem := by
    rw [hm1]
    exact frame_w hp (frame_w hp (frame_w hp (frame_w hp (frame_w hp (frame_w hp (frame_w hp (frame_w hp
      (Frame.refl _ _) (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _)
      (by decide) _) (by decide) _
  have sp1 : t1.gpr .rsp = fb s := k1.gpr (by decide)
  refine WP.mono (copy1_ok hp sp1 (k1.2.2 ▸ hfr) k1.2.1 f1 (j := 0) (d := sScr) (by decide) (by decide))
    fun t2 ⟨k2, hm2, f2⟩ => ?_
  have R2 : Rep t2.mem (fb s) (stackArg s 0) (fun o => s.mem (off (stackArg s 0) o)) (proW s) := by
    rw [hm2, hm1]; exact R1.wf G' (k := 21) (by decide) (stackArg s 0)
  have k12 : Keep [.rax] A t2 := (k1.trans k2).mono (by decide)
  have sp2 : t2.gpr .rsp = fb s := k12.gpr (by decide)
  have h392 : frameBytes = 392 := rfl
  have L2 : Lay t2 (fb s) (stackArg s 0) := by
    have := hp.sp1; unfold encStack at this
    refine ⟨sp2, k12.2.2 ▸ hfr, by omega_using [hF, h392, this], by omega_arith, ?_, ?_, G'.dFS, G'.dRS⟩
    · have hsl := hp.hsl
      refine ⟨⟨stackArg s 0, 0, (stackArg s 1).toNat * 8, by rw [k12.2.2, hA]; simp [allocState, hp.hwr],
        (BitVec.add_zero _).symm, by unfold oRsa; omega_using [hsl], by have := hp.wS; omega_using [this]⟩, G'.Sw⟩
    · rw [show sScr = 8 * 21 from rfl]
      exact (R2.fr 21 (by decide)).trans (by simp [proW, upd])
  have hb : t2.gpr .r9 = BitVec.ofNat 64 (s.gpr .r9).toNat := by
    rw [k12.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  refine WP.mono (maskBits_ok L2 R2 (r := .r9) (by decide) (b := (s.gpr .r9).toNat)
    (by simp only [proW, upd, Nat.reduceEqDiff, ite_true, ite_false]; rw [← hp.hel, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]) hb hp.b2) fun t3 ⟨L3, k3, R3, hm3⟩ => ?_
  refine ⟨(k12.trans k3).mono (by decide), L3, R3, ?_⟩
  rw [hm3]
  exact frame_w hp (frame_w hp f2 (d := sC) (by decide) _) (d := sLo) (by decide) _

/-! ## The tables' words -/

theorem tab_sub {s : State} (hp : Pre T s) {i : Nat} (hi : i = 2 ∨ i = 3) :
    (⟨stackArg s i, 56⟩ : Region) ∈ s.rd ∧ (stkR s).Disjoint ⟨stackArg s i, 56⟩ ∧
      (stackArg s i).toNat + 56 ≤ 2 ^ 64 := by
  rcases hi with rfl | rfl
  · exact ⟨by rw [hp.hrd]; simp, hp.dKtH, hp.wTH⟩
  · exact ⟨by rw [hp.hrd]; simp, hp.dKtG, hp.wTG⟩

/-- A word of a table, read from memory changed only in the frame. -/
theorem tab_rd {s : State} (hp : Pre T s) {m : Mem} (hf : Frame [frR s] s.mem m) {i j : Nat} (hi : i = 2 ∨ i = 3)
    (hj : j + 8 ≤ 56) : m.readW (off (stackArg s i) j) 64 = s.mem.readW (off (stackArg s i) j) 64 := by
  obtain ⟨-, hK, hw⟩ := tab_sub hp hi
  refine hf.readW (r := ⟨stackArg s i, 56⟩) (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])) (fun r' hr' => ?_)
    (by decide)
  simp only [List.mem_singleton] at hr'; subst hr'
  exact (hK.sub_left (frame_sub s)).symm

/-- One word of the table at `r11` copied to a slot. -/
theorem tabCopy_ok {s : State} (hp : Pre T s) {u : State} (hsp : u.gpr .rsp = fb s) (hfr : frR s ∈ u.wr)
    (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem) {i j d : Nat} (hi : i = 2 ∨ i = 3)
    (h11 : u.gpr .r11 = stackArg s i) (hj : j + 8 ≤ 56) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block [.mov .rax (.mem (at_ .r11 j)), .store (sp d) .rax]) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) d) (s.mem.readW (off (stackArg s i) j) 64) ∧ Frame [frR s] s.mem u'.mem := by
  have hF := fb_toNat hp
  have := hp.sp2
  obtain ⟨hm, -, hw⟩ := tab_sub hp hi
  have hsc : Scr u (fb s) frameBytes := Scr.of_mem hfr (by omega_using [hF])
  have hin : InRegions (u.rd ++ u.wr) (off (stackArg s i) j) 8 :=
    ⟨_, List.mem_append_left _ (by rw [hrd]; exact hm), Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) d)
      (s.mem.readW (off (stackArg s i) j) 64)) ?_ rfl)
    fun u' ⟨hm', k⟩ => ⟨k, hm', hm' ▸ frame_w hp hf hd _⟩
  xrun [ea_at, ea_sp, hsp, h11, hin, tab_rd hp hf hi hj, hsc.st (d := d) hd]

/-- Stack argument `j` to `r11`. -/
theorem argR11_ok {s : State} (hp : Pre T s) {u : State} (hsp : u.gpr .rsp = fb s) (hrd : u.rd = s.rd)
    (hf : Frame [frR s] s.mem u.mem) {j : Nat} (hj : j < 4) :
    WP isa (.block [.mov .r11 (.mem (arg j))]) u fun u' => Keep [.r11] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .r11 = stackArg s j := by
  have hF := fb_toNat hp
  have := hp.sp2
  have hin : InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
    refine ⟨⟨stackArgAddr s 0, 32⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp), ?_⟩
    rw [argAddr, show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_using []]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  refine WP.mono (WP.keep [.r11] (Q := fun u' => u'.mem = u.mem ∧ u'.gpr .r11 = stackArg s j) ?_ rfl)
    fun u' ⟨⟨hm, h⟩, k⟩ => ⟨k, hm, h⟩
  xrun [arg, ea_sp, hsp, hin, arg_read hp hf hj]

theorem hSlots_eq : hSlots = ([.mov .rax (.mem (at_ .r11 0)), .store (sp sIniH) .rax] : List Instr) ++
    ([.mov .rax (.mem (at_ .r11 24)), .store (sp sCmpH) .rax] : List Instr) ++
    ([.mov .rax (.mem (at_ .r11 32)), .store (sp sDigH) .rax] : List Instr) := rfl

theorem gSlots_eq : gSlots = ([.mov .rax (.mem (at_ .r11 0)), .store (sp sIniG) .rax] : List Instr) ++
    ([.mov .rax (.mem (at_ .r11 8)), .store (sp sUpdG) .rax] : List Instr) ++
    ([.mov .rax (.mem (at_ .r11 16)), .store (sp sFinG) .rax] : List Instr) ++
    ([.mov .rax (.mem (at_ .r11 48)), .store (sp sDG) .rax] : List Instr) := rfl

/-- The `MdHash` table's words to their slots, and `mgf1` to `r11`. -/
theorem hSl_ok {s : State} (hp : Pre T s) {u : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay u (fb s) (stackArg s 0)) (R : Rep u.mem (fb s) (stackArg s 0) V W) (hrd : u.rd = s.rd)
    (hf : Frame [frR s] s.mem u.mem) (h11 : u.gpr .r11 = stackArg s 2) :
    WP isa (.block (hSlots ++ ([.mov .r11 (.mem (arg 3))] : List Instr))) u fun u' => Keep [.rax, .r11] u u' ∧
      Lay u' (fb s) (stackArg s 0) ∧ u'.gpr .r11 = stackArg s 3 ∧ Frame [frR s] s.mem u'.mem ∧
      Rep u'.mem (fb s) (stackArg s 0) V (upd (upd (upd W 8 (s.mem.readW (off (stackArg s 2) 0) 64))
        9 (s.mem.readW (off (stackArg s 2) 24) 64)) 10 (s.mem.readW (off (stackArg s 2) 32) 64)) := by
  have G' := hp.geo
  have hsp := L.rsp
  have hfr := L.fr
  rw [hSlots_eq, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (tabCopy_ok hp hsp hfr hrd hf (.inl rfl) h11 (j := 0) (d := sIniH) (by decide) (by decide))
    fun u1 ⟨k1, hm1, f1⟩ => ?_
  refine WP.mono (tabCopy_ok hp ((k1.gpr (by decide)).trans hsp) (k1.2.2 ▸ hfr) (k1.2.1.trans hrd) f1 (.inl rfl)
    ((k1.gpr (by decide)).trans h11) (j := 24) (d := sCmpH) (by decide) (by decide)) fun u2 ⟨k2, hm2, f2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.mono (tabCopy_ok hp ((k12.gpr (by decide)).trans hsp) (k12.2.2 ▸ hfr) (k12.2.1.trans hrd) f2 (.inl rfl)
    ((k12.gpr (by decide)).trans h11) (j := 32) (d := sDigH) (by decide) (by decide)) fun u3 ⟨k3, hm3, f3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.mono (argR11_ok hp ((k13.gpr (by decide)).trans hsp) (k13.2.1.trans hrd) f3 (j := 3) (by decide))
    fun u4 ⟨k4, hm4, h4⟩ => ?_
  have R4 : Rep u4.mem (fb s) (stackArg s 0) V (upd (upd (upd W 8 (s.mem.readW (off (stackArg s 2) 0) 64))
      9 (s.mem.readW (off (stackArg s 2) 24) 64)) 10 (s.mem.readW (off (stackArg s 2) 32) 64)) := by
    rw [hm4, hm3, hm2, hm1]
    exact ((R.wf G' (k := 8) (by decide) _).wf G' (k := 9) (by decide) _).wf G' (k := 10) (by decide) _
  have k14 : Keep [.rax, .r11] u u4 := (k13.trans k4).mono (by decide)
  refine ⟨k14, L.of_rep' R R4 (by simp [upd]) (k14.gpr (by decide)) k14.2.2, h4, hm4 ▸ f3, R4⟩

/-- The `Hash` table's words to their slots. -/
theorem gSl_ok {s : State} (hp : Pre T s) {u : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay u (fb s) (stackArg s 0)) (R : Rep u.mem (fb s) (stackArg s 0) V W) (hrd : u.rd = s.rd)
    (hf : Frame [frR s] s.mem u.mem) (h11 : u.gpr .r11 = stackArg s 3) :
    WP isa (.block gSlots) u fun u' => Keep [.rax] u u' ∧ Lay u' (fb s) (stackArg s 0) ∧
      Frame [frR s] s.mem u'.mem ∧
      Rep u'.mem (fb s) (stackArg s 0) V (upd (upd (upd (upd W 11 (s.mem.readW (off (stackArg s 3) 0) 64))
        12 (s.mem.readW (off (stackArg s 3) 8) 64)) 13 (s.mem.readW (off (stackArg s 3) 16) 64))
        14 (s.mem.readW (off (stackArg s 3) 48) 64)) := by
  have G' := hp.geo
  have hsp := L.rsp
  have hfr := L.fr
  rw [gSlots_eq, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (tabCopy_ok hp hsp hfr hrd hf (.inr rfl) h11 (j := 0) (d := sIniG) (by decide) (by decide))
    fun u1 ⟨k1, hm1, f1⟩ => ?_
  refine WP.mono (tabCopy_ok hp ((k1.gpr (by decide)).trans hsp) (k1.2.2 ▸ hfr) (k1.2.1.trans hrd) f1 (.inr rfl)
    ((k1.gpr (by decide)).trans h11) (j := 8) (d := sUpdG) (by decide) (by decide)) fun u2 ⟨k2, hm2, f2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.mono (tabCopy_ok hp ((k12.gpr (by decide)).trans hsp) (k12.2.2 ▸ hfr) (k12.2.1.trans hrd) f2 (.inr rfl)
    ((k12.gpr (by decide)).trans h11) (j := 16) (d := sFinG) (by decide) (by decide)) fun u3 ⟨k3, hm3, f3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.mono (tabCopy_ok hp ((k13.gpr (by decide)).trans hsp) (k13.2.2 ▸ hfr) (k13.2.1.trans hrd) f3 (.inr rfl)
    ((k13.gpr (by decide)).trans h11) (j := 48) (d := sDG) (by decide) (by decide)) fun u4 ⟨k4, hm4, f4⟩ => ?_
  have R4 : Rep u4.mem (fb s) (stackArg s 0) V (upd (upd (upd (upd W 11 (s.mem.readW (off (stackArg s 3) 0) 64))
      12 (s.mem.readW (off (stackArg s 3) 8) 64)) 13 (s.mem.readW (off (stackArg s 3) 16) 64))
      14 (s.mem.readW (off (stackArg s 3) 48) 64)) := by
    rw [hm4, hm3, hm2, hm1]
    exact (((R.wf G' (k := 11) (by decide) _).wf G' (k := 12) (by decide) _).wf G' (k := 13) (by decide) _).wf G'
      (k := 14) (by decide) _
  have k14 : Keep [.rax] u u4 := (k13.trans k4).mono (by decide)
  exact ⟨k14, L.of_rep' R R4 (by simp [upd]) (k14.gpr (by decide)) k14.2.2, f4, R4⟩

end VG.Proof.RsaPss.X86_64.Enc

end

end

/-! ### `RsaPss.X86_64.CopyBytes`, which only this module used -/

section

/-!
# RSASSA-PSS on x86-64: copying bytes between two buffers

`n` bytes from `q` (`rsi`) to `p` (`rdi`), a byte at a time
(`copyBytes_ok`), for buffers apart: memory changes only at `p`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)

structure CBI (u₀ : State) (p q : Addr) (j : Nat) (v : State) : Prop where
  keep : Keep [.rax, .r8] u₀ v
  r8 : v.gpr .r8 = BitVec.ofNat 64 j
  mem : ∀ x, v.mem x = if (⟨p, j⟩ : Region).Contains x 1 then u₀.mem (q + (x - p)) else u₀.mem x

theorem copyBytes_ok {u₀ : State} {p q : Addr} {n : Nat} {cnt : Src} (hs : StepOk cnt n u₀ [.rax, .r8])
    (hn : 0 < n) (hpn : p.toNat + n ≤ 2 ^ 64) (hw : (⟨p, n⟩ : Region) ∈ u₀.wr)
    (hsrc : ∀ i < n, InRegions (u₀.rd ++ u₀.wr) (q + BitVec.ofNat 64 i) 1)
    (hd : ∀ i < n, ¬ (⟨p, n⟩ : Region).Contains (q + BitVec.ofNat 64 i) 1)
    (hdi : u₀.gpr .rdi = p) (hsi : u₀.gpr .rsi = q) (h8 : u₀.gpr .r8 = BitVec.ofNat 64 0) :
    WP isa (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rdi .r8) .rax] cnt) u₀ fun u' =>
      Keep [.rax, .r8] u₀ u' ∧
      ∀ x, u'.mem x = if (⟨p, n⟩ : Region).Contains x 1 then u₀.mem (q + (x - p)) else u₀.mem x := by
  refine WP.mono (byteLoop_ok hn hs (CBI u₀ p q) ?_ (u := u₀)
    ⟨Keep.refl _ _, h8, fun x => by simp [Region.Contains]⟩) fun u' I => ⟨I.keep, I.mem⟩
  intro j hj v I
  obtain hdv : v.gpr .rdi = p := (I.keep.gpr (by decide)).trans hdi
  obtain hsv : v.gpr .rsi = q := (I.keep.gpr (by decide)).trans hsi
  obtain hea : ∀ b : Addr, b + BitVec.ofNat 64 j + BitVec.ofNat 64 0 = b + BitVec.ofNat 64 j := fun b => by
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  obtain hin : InRegions v.wr (p + BitVec.ofNat 64 j) 1 :=
    ⟨_, I.keep.2.2 ▸ hw, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hpn, hj])⟩
  obtain hrd : InRegions (v.rd ++ v.wr) (q + BitVec.ofNat 64 j) 1 := by
    rw [I.keep.2.1, I.keep.2.2]; exact hsrc j hj
  obtain hq : v.mem (q + BitVec.ofNat 64 j) = u₀.mem (q + BitVec.ofNat 64 j) := by
    rw [I.mem, ifn]
    exact fun h => hd j hj (by
      simp only [Region.Contains] at h ⊢; omega_using [hj, h])
  refine WP.mono (WP.keep [.rax] (Q := fun v' => v'.gpr .r8 = BitVec.ofNat 64 j ∧
      v'.mem = v.mem.writeW (p + BitVec.ofNat 64 j) (u₀.mem (q + BitVec.ofNat 64 j))) ?_ rfl)
    fun v' ⟨⟨h8', hm⟩, k⟩ => ⟨(I.keep.trans k).mono (by decide), h8', fun v'' k' hm' h8'' => ?_⟩
  · xrun [ea_ix, hdv, hsv, I.r8, hea, hin, hrd, hq]
    simp
  refine ⟨(I.keep.trans (k.trans k')).mono (by decide), h8'', fun x => ?_⟩
  rw [hm', hm, VG.WriteBytes.writeW8_apply, I.mem x]
  by_cases he : x = p + BitVec.ofNat 64 j
  · subst he
    rw [ifp rfl, ifp (show (⟨p, j + 1⟩ : Region).Contains (p + BitVec.ofNat 64 j) 1 from
      Offset.contains_base _ (by omega_using []) (by omega_using [hpn, hj]))]
    congr 1
    rw [BitVec.add_comm p, BitVec.add_sub_cancel]
  · rw [ifn he]
    obtain hne : (x - p).toNat ≠ j := fun h => he (by
      rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel])
    obtain iff : (⟨p, j + 1⟩ : Region).Contains x 1 ↔ (⟨p, j⟩ : Region).Contains x 1 := by
      simp only [Region.Contains]; omega_using [hne]
    by_cases h1 : (⟨p, j⟩ : Region).Contains x 1
    · rw [ifp h1, ifp (iff.mpr h1)]
    · rw [ifn h1, ifn (fun h => h1 (iff.mp h))]

/-- The bytes the copy leaves at `p`. -/
theorem bytesAt_copied {m m' : Mem} {p q : Addr} {n : Nat} (hpn : p.toNat + n ≤ 2 ^ 64)
    (h : ∀ x, m' x = if (⟨p, n⟩ : Region).Contains x 1 then m (q + (x - p)) else m x) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m q n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  obtain hi := List.mem_range.mp hi
  rw [h, ifp (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hpn, hi])), BitVec.add_comm p, BitVec.add_sub_cancel]

end VG.Proof.RsaPss.X86_64

end

end


/-!
# EMSA-PSS's encoding on x86-64: correctness

`enc_body`: from the entry state, the body of the frame leaves `rax` and
`em` as `Spec.RsaPss.encode` says, with the callee-saved registers in their
slots; `enc_correct`: `encode` meets `encK` and keeps the callee-saved
registers, its return address and MXCSR's control bits.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Enc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)

variable {T : Tabs}

/-- What `encK.post` asks for: the encoding with the hash function `Hs` (of
digests of `D` bytes) and MGF1's `Gs`. -/
def encOut (D : Nat) (Hs Gs : Spec.Mgf1.Hash) (s : State) : Option (List Byte) :=
  Spec.RsaPss.encode Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) D)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) (s.gpr .r9).toNat

/-- The outcome, from the memory and `rax`. -/
def OutOk (D : Nat) (Hs Gs : Spec.Mgf1.Hash) (s : State) (m : Mem) (rax : BitVec 64) : Prop :=
  match encOut D Hs Gs s with
  | some e => rax.setWidth 32 = 1 ∧ Spec.Rsa.bytesAt m (s.gpr .rdi) (s.gpr .rsi).toNat = e
  | none => rax.setWidth 32 = 0

/-- Before the epilogue: the outcome, the saved registers in their slots. -/
structure EDone (D : Nat) (Hs Gs : Spec.Mgf1.Hash) (s t : State) : Prop where
  L : Lay t (fb s) (stackArg s 0)
  wr : t.wr = frR s :: s.wr
  cs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r
  rbx : t.mem.readW (off (fb s) sRbx) 64 = s.gpr .rbx
  rbp : t.mem.readW (off (fb s) sRbp) 64 = s.gpr .rbp
  r12 : t.mem.readW (off (fb s) sR12) 64 = s.gpr .r12
  out : OutOk D Hs Gs s t.mem (t.gpr .rax)

/-- A refusal: 0. -/
theorem ret0_done {D : Nat} {Hs Gs : Spec.Mgf1.Hash} {s t : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay t (fb s) (stackArg s 0)) (R : Rep t.mem (fb s) (stackArg s 0) V W) (hw : t.wr = frR s :: s.wr)
    (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r)
    (h41 : W 41 = s.gpr .rbx) (h42 : W 42 = s.gpr .rbp) (h43 : W 43 = s.gpr .r12) (hn : encOut D Hs Gs s = none) :
    WP isa ret0 t (EDone D Hs Gs s) := by
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rax = 0) ?_ rfl)
    fun t' ⟨⟨hm, hax⟩, k⟩ => ?_
  · xrun [ret0]
  obtain R' : Rep t'.mem (fb s) (stackArg s 0) V W := hm ▸ R
  refine ⟨L.congr (k.gpr (by decide)) k.2.2 (by rw [hm]), k.2.2.trans hw,
    fun r hr => (k.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide)).trans (hcs r hr), ?_, ?_, ?_, ?_⟩
  · rw [R'.rd (d := sRbx) 41 rfl (by decide), h41]
  · rw [R'.rd (d := sRbp) 42 rfl (by decide), h42]
  · rw [R'.rd (d := sR12) 43 rfl (by decide), h43]
  · simp only [OutOk, hn, hax]; rfl

variable (hH : Pbkdf2.Md.X86_64.HashOK T.H) (K : Pbkdf2.Md.X86_64.Callees T.H)
  (hG : Pbkdf2.Md.X86_64.Calls.StreamOK T.G) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x)
  (hGl : Gs.len = T.G.D) (hGv : Proof.Mgf1.Valid Gs) (hf : MdFnsSafe T.f) (hg : FnsSafe T.g) (hdk : DigOK T.H)

/-- The copy of `EM` to `em`. -/
theorem copyOut_ok {s u : State} (hp : Pre T s) {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay u (fb s) (stackArg s 0)) (R : Rep u.mem (fb s) (stackArg s 0) V W) (hw : u.wr = frR s :: s.wr)
    (h16 : W 16 = s.gpr .rdi) (h17 : W 17 = s.gpr .rsi) (hk1 : 1 ≤ (s.gpr .rsi).toNat) :
    WP isa copyOut u fun u' => Lay u' (fb s) (stackArg s 0) ∧ Keep [.rsi, .rdi, .r10, .rax, .r8] u u' ∧
      Rep u'.mem (fb s) (stackArg s 0) V W ∧
      Spec.Rsa.bytesAt u'.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
        (List.range (s.gpr .rsi).toNat).map (fun i => V (oEm + i)) ∧
      (∀ x, ¬ (outR s).Contains x 1 → u'.mem x = u.mem x) := by
  have hk2 := hp.k2
  obtain hF := fb_toNat hp
  have G' := hp.geo
  have hs := L.slot
  simp only [Bignum.word] at hs
  refine WP.seq (WP.mono (WP.keep [.rsi, .rdi, .r10, .r8] (Q := fun v => v.gpr .rsi = off (stackArg s 0) oEm ∧
      v.gpr .rdi = s.gpr .rdi ∧ v.gpr .r10 = BitVec.ofNat 64 (s.gpr .rsi).toNat ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧
      v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, h₁₀, h₃, hm⟩, hkv⟩ => ?_)
  · xrun [copyOut, scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sScr) (by decide),
      L.ld (d := sOut) (by decide), L.ld (d := sK) (by decide), hs, R.rd (d := sOut) 16 rfl (by decide),
      R.rd (d := sK) 17 rfl (by decide), h16, h17, VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide)]
    simp
  obtain Lv : Lay v (fb s) (stackArg s 0) := L.congr (hkv.gpr (by decide)) hkv.2.2 (by rw [hm])
  obtain hO : (outR s).Disjoint ⟨stackArg s 0, oRsa⟩ :=
    hp.dOs.sub_right (Region.sub_prefix (by have := hp.hsl; unfold oRsa; omega_using [this]))
  obtain hOF : (outR s).Disjoint ⟨fb s, frameBytes⟩ := (hp.dKo.sub_left (frame_sub s)).symm
  refine WP.mono (copyBytes_ok (p := s.gpr .rdi) (q := off (stackArg s 0) oEm) (n := (s.gpr .rsi).toNat)
    (stepR_ok (by omega_using [hk2]) v (show Reg.r10 ∉ [Reg.rax, .r8] by decide) (by decide) h₁₀) (by omega_using [hk1]) hp.wO
    (by rw [hkv.2.2, hw, hp.hwr]; simp) (fun i hi => by
      rw [off_plus]; exact Lv.sld8 (d := oEm + i) (by unfold oEm oRsa; omega_using [hk2, hi]))
    (fun i hi hc => hO _ hc (by
      rw [off_plus]; exact (cS _ (o := oEm + i) (n := 1) (by unfold oEm oRsa; omega_using [hk2, hi])).byte
        (by rw [BitVec.sub_self]; decide)))
    h₂ h₁ h₃) fun w ⟨kw, hmw⟩ => ?_
  obtain hout : ∀ x, ¬ (outR s).Contains x 1 → w.mem x = u.mem x := fun x hx => by
    simp only [outR] at hx; rw [hmw, ifn hx, hm]
  obtain Rw : Rep w.mem (fb s) (stackArg s 0) V W := R.of_outside hout hO hOF G'
  refine ⟨Lv.of_rep (hm ▸ R) Rw (kw.gpr (by decide)) kw.2.2, (hkv.trans kw).mono (by decide), Rw, ?_, hout⟩
  rw [bytesAt_copied hp.wO (by rw [hm] at hmw; exact hmw), bytesAt_off]
  exact List.map_congr_left fun i hi => R.scr _ (by have := List.mem_range.mp hi; unfold oEm oRsa; omega_using [hk2, this])

/-- An input's bytes, unchanged. -/
theorem bytesF_eq {s : State} {m : Mem} (hM : Frame (wrR s) s.mem m) {p : Addr} {n : Nat}
    (hd : ∀ r ∈ wrR s, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    (List.range n).map (bytesF m p) = Spec.Rsa.bytesAt s.mem p n :=
  bytesAt_frame hM hd hn

include hH K hG hGh hGl hGv hf hg hdk in
/-- After the checks: the encoding, its copy to `em`, and 1. -/
theorem encMain_ok (lk : Pbkdf2.Md.X86_64.MgfLink T.H hH) {s u : State} (hp : Pre T s) {V : Nat → Byte}
    {W : Nat → BitVec 64} (L : Lay u (fb s) (stackArg s 0)) (R : Rep u.mem (fb s) (stackArg s 0) V W)
    (hw : u.wr = frR s :: s.wr) (hrd : u.rd = s.rd) (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], u.gpr r = s.gpr r)
    (hM : Frame (wrR s) s.mem u.mem) (hT : HT T.H T.dn T.f W u.syms) (hGT : GT T.G T.g W u.syms)
    (h16 : W 16 = s.gpr .rdi) (h17 : W 17 = s.gpr .rsi)
    (h25 : W 25 = BitVec.setWidth 64 ((0xFF : Byte) >>> (8 * (s.gpr .rsi).toNat - (s.gpr .r9).toNat)))
    (h26 : W 26 = 0) (h37 : W 37 = s.gpr .rdx) (h39 : W 39 = s.gpr .rcx) (h40 : W 40 = s.gpr .r8)
    (h41 : W 41 = s.gpr .rbx) (h42 : W 42 = s.gpr .rbp) (h43 : W 43 = s.gpr .r12)
    (hfit : T.H.D + (s.gpr .r8).toNat + 2 ≤ (s.gpr .rsi).toNat)
    (hax : u.gpr .rax = BitVec.ofNat 64 ((s.gpr .rsi).toNat - (T.H.D + 2))) :
    WP isa (encMain T.f T.H T.g) u (EDone T.H.D lk.G Gs s) := by
  have hk2 := hp.k2
  have hD : T.H.D = lk.G.len := lk.len.symm
  obtain hHv := validG hH lk.hash lk.len
  obtain dg : ∀ r ∈ wrR s, (⟨s.gpr .rdx, T.H.D⟩ : Region).Disjoint r := in_apart hp.dKdg hp.dOdg hp.ddgs
  obtain sa : ∀ r ∈ wrR s, (⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ : Region).Disjoint r :=
    in_apart hp.dKsa hp.dOsa hp.dsas
  have hdg : (s.gpr .rdx).toNat + T.H.D ≤ 2 ^ 64 := hp.wDg
  have hsa := hp.wSa
  rw [encMain]
  simp only [seqs]
  -- The encoding.
  refine WP.seq (WP.mono (WP.keepIn (signEnc_safe hH hf hg) (signEnc_xd hf hg)
    (signEnc_ok hH K lk hG hGh hGl hGv hf hdk L R hT hGT (k := (s.gpr .rsi).toNat) (lo := 0)
      (sl := (s.gpr .r8).toNat) (c := (0xFF : Byte) >>> (8 * (s.gpr .rsi).toNat - (s.gpr .r9).toNat))
      (by rw [h17, BitVec.ofNat_toNat, BitVec.setWidth_eq]) h26 h25 h37 h39
      (by rw [h40, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hk2 (Nat.zero_le _) (by omega_using [hfit])
      (by rw [hax, Nat.sub_zero])
      (fun i hi => ⟨⟨s.gpr .rdx, T.H.D⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
        Offset.contains_base _ (by omega_using [hi]) (by omega_using [hfit, hi])⟩)
      (fun i hi => by
        have := hp.outside hp.dOdg hp.ddgs hp.dKdg (a := s.gpr .rdx + BitVec.ofNat 64 i)
          (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hfit, hi]))
        rwa [← hw] at this)
      (fun i hi => ⟨⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
        Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩)
      (fun i hi => by
        have := hp.outside hp.dOsa hp.dsas hp.dKsa (a := s.gpr .rcx + BitVec.ofNat 64 i)
          (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
        rwa [← hw] at this)))
    fun u1 ⟨⟨L1, rd1, wr1, cs1, V1, W1, R1, hW1, hV1⟩, f1⟩ => ?_)
  obtain hM1 := frame_keep hp hw L.rsp hM f1
  obtain hw1 : u1.wr = frR s :: s.wr := wr1.trans hw
  obtain g : ∀ j, j < nW → (j < 23 ∨ 32 < j) → W1 j = W j := fun j hj h => hW1 j hj h
  -- The copy.
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [copyOut]) (by exact Nat.zero_le 16)
    (copyOut_ok hp L1 R1 hw1 (by rw [g 16 (by decide) (by decide), h16]) (by rw [g 17 (by decide) (by decide), h17])
      (by omega_using [hfit]))) fun u2 ⟨⟨L2, k2, R2, hb2, ho2⟩, f2⟩ => ?_)
  -- 1.
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = u2.mem ∧ t'.gpr .rax = 1) (by xrun) rfl)
    fun t ⟨⟨hm, hax'⟩, k⟩ => ?_
  obtain R' : Rep t.mem (fb s) (stackArg s 0) V1 W1 := hm ▸ R2
  refine ⟨L2.congr (k.gpr (by decide)) k.2.2 (by rw [hm]), k.2.2.trans (k2.2.2.trans hw1),
    fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · have hr' : r ∉ [Reg.rax] ∧ r ∉ [Reg.rsi, .rdi, .r10, .rax, .r8] ∧ r ∈ [Reg.r13, .r14, .r15, .rsp] := by
      simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
    rw [k.gpr hr'.1, k2.gpr hr'.2.1, cs1 r hr'.2.2, hcs r hr]
  · rw [R'.rd (d := sRbx) 41 rfl (by decide), g 41 (by decide) (by decide), h41]
  · rw [R'.rd (d := sRbp) 42 rfl (by decide), g 42 (by decide) (by decide), h42]
  · rw [R'.rd (d := sR12) 43 rfl (by decide), g 43 (by decide) (by decide), h43]
  -- The outcome.
  obtain hdgB : (List.range T.H.D).map (bytesF u.mem (s.gpr .rdx)) = Spec.Rsa.bytesAt s.mem (s.gpr .rdx) T.H.D :=
    bytesF_eq hM dg (by omega_using [hfit])
  obtain hsaB : (List.range (s.gpr .r8).toNat).map (bytesF u.mem (s.gpr .rcx)) =
      Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat := bytesF_eq hM sa (by omega_using [])
  rw [hdgB, hsaB] at hV1
  have hel := hp.hel
  obtain hsl : (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat).length = (s.gpr .r8).toNat := by
    simp [Spec.Rsa.bytesAt]
  obtain he := RsaPss.encode_eq₂ lk.G Gs hHv hGv (mHash := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) T.H.D)
    (salt := Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) (emBits := (s.gpr .r9).toNat)
    (by simp [Spec.Rsa.bytesAt, hD]) hel.symm rfl (by rw [hsl, ← hD]; omega_using [hfit])
  simp only [OutOk, encOut, he, hsl]
  refine ⟨by rw [hax']; rfl, ?_⟩
  rw [hm, hb2]
  refine List.map_congr_left fun i hi => ?_
  rw [hV1 i (List.mem_range.mp hi), hD, Nat.sub_zero]

include hH hf hg in
theorem encBody_safe : (encBody T.f T.H T.g).allInstrs safeI = true := by
  simp only [encBody, encMain, encPrologue, maskBits, fitH, ret0, saltFits, copyOut, hSlots, gSlots, seqs,
    Code.allInstrs, signEnc_safe hH hf hg, rec_all, List.all_append, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include hf hg in
theorem encBody_xd : (encBody T.f T.H T.g).x86_64Depth ≤ 16 := by
  have := signEnc_xd (H := T.H) hf hg
  simp only [encBody, encMain, ret0, copyOut, seqs, Code.x86_64Depth, byteLoop, Nat.max_le]
  omega_using [this]

include hH hf hg in
theorem enc_spAll : (encode T.f T.H T.g).allInstrs (fun i => !isa.writesSp i) = true := by
  obtain he := encBody_safe hH hf hg
  rw [safeI_eq, allInstrs_and, Bool.and_eq_true] at he
  simp only [encode, Code.allInstrs, he.1]
  rfl

include hf hg in
theorem enc_xd : (encode T.f T.H T.g).x86_64Depth ≤ encStack := by
  have := encBody_xd (T := T) hf hg
  simp only [encode, Code.x86_64Depth, X86_64.Instr.frameBytes]
  unfold encStack frameBytes at *
  omega_using [this]

/-- The epilogue: the callee-saved registers restored and the outcome. -/
theorem restore_ok {Hs : Spec.Mgf1.Hash} {s t : State} (D : EDone T.H.D Hs Gs s t) :
    WP isa (.block restoreRegs) t fun t' => t'.gpr .rsp = fb s ∧ t'.wr = (allocState frameBytes s).wr ∧
      (∀ r ∈ calleeSaved, (freedF t').gpr r = s.gpr r) ∧ (encK T Hs Gs).post s (freedF t') := by
  refine WP.mono (WP.keep [.rbx, .rbp, .r12] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rbx = s.gpr .rbx ∧
      t'.gpr .rbp = s.gpr .rbp ∧ t'.gpr .r12 = s.gpr .r12) ?_ rfl) fun t' ⟨⟨hm, h1, h2, h3⟩, k⟩ => ?_
  · xrun [restoreRegs, ea_sp, D.L.rsp, D.L.ld (d := sRbx) (by decide), D.L.ld (d := sRbp) (by decide),
      D.L.ld (d := sR12) (by decide), D.rbx, D.rbp, D.r12]
  obtain hsp : t'.gpr .rsp = fb s := (k.gpr (by decide)).trans D.L.rsp
  refine ⟨hsp, k.2.2.trans D.wr, fun r hr => ?_, ?_⟩
  · simp only [freedF, State.setReg]
    by_cases hr' : r = .rsp
    · subst hr'; simp only [ite_true, hsp, fb]; exact BitVec.sub_add_cancel _ _
    · simp only [hr', ite_false]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact absurd rfl hr'
      · exact h3
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
  · have hax : (freedF t').gpr .rax = t.gpr .rax := by
      show (if Reg.rax = Reg.rsp then t'.gpr .rsp + BitVec.ofNat 64 frameBytes else t'.gpr .rax) = _
      rw [ifn (by decide), k.gpr (by decide)]
    have hmem : (freedF t').mem = t.mem := hm
    have hout := D.out
    simp only [OutOk, encOut] at hout
    simp only [encK, hax, hmem]
    exact hout

include hH K hG hGh hGl hGv hf hg hdk in
theorem enc_ok (lk : Pbkdf2.Md.X86_64.MgfLink T.H hH) {s : State} (h : (encK T lk.G Gs).pre s) :
    WP isa (encode T.f T.H T.g) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      (encK T lk.G Gs).post s s' ∧ s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  obtain hp := Pre.of T h
  obtain hF := fb_toNat hp
  have hk2 := hp.k2
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have hGl' : lk.G.len = T.H.D := lk.len
  refine wp_frame (by have := hp.sp1; unfold encStack frameBytes at *; omega_using [hF]) ?_
  refine WP.mono_mx (safe_mx (encBody_safe hH hf hg)) (Q := fun s₂ => s₂.gpr .rsp = fb s ∧
    s₂.wr = (allocState frameBytes s).wr ∧ (∀ r ∈ calleeSaved, (freedF s₂).gpr r = s.gpr r) ∧
      (encK T lk.G Gs).post s (freedF s₂)) ?_ fun t ⟨a, b, c, d⟩ hmx =>
    ⟨a, b, c, d, by rw [show (freedF t).mxcsr = t.mxcsr from rfl, hmx]; rfl⟩
  rw [encBody]
  simp only [seqs]
  -- The prologue, and the tables' words to their slots.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine X86_64.WP.mono_syms (encPro_ok hp) fun t1 ⟨k1, L1, R1, f1⟩ s1 => ?_
  refine X86_64.WP.mono_syms (argR11_ok hp L1.rsp k1.2.1 f1 (j := 2) (by decide)) fun t1' ⟨k1', hm1', h11⟩ s1' => ?_
  obtain L1' : Lay t1' (fb s) (stackArg s 0) := L1.congr (k1'.gpr (by decide)) k1'.2.2 (by rw [hm1'])
  refine WP.seq (X86_64.WP.mono_syms (hSl_ok hp L1' (hm1' ▸ R1) (k1'.2.1.trans k1.2.1) (hm1' ▸ f1) h11)
    fun t2 ⟨k2, L2, h2, f2, R2⟩ s2 => ?_)
  obtain hrd2 : t2.rd = s.rd := k2.2.1.trans (k1'.2.1.trans k1.2.1)
  refine WP.seq (X86_64.WP.mono_syms (gSl_ok hp L2 R2 hrd2 f2 h2) fun t3 ⟨k3, L3, f3, R3⟩ s3 => ?_)
  obtain sy3 : t3.syms = s.syms := s3.trans (s2.trans (s1'.trans s1))
  refine WP.seq (X86_64.WP.mono_syms (fitH_ok (H := T.H) (by omega_using [hDN, hN]) L3 R3 (k := (s.gpr .rsi).toNat)
    (by simp only [proW', proW, upd, Nat.reduceEqDiff, ite_true, ite_false]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by omega_using [hk2])) fun t4 ⟨k4, hm4, hax4, hc4⟩ s4 => ?_)
  obtain L4 : Lay t4 (fb s) (stackArg s 0) := L3.congr (k4.gpr (by decide)) k4.2.2 (by rw [hm4])
  obtain R4 := hm4 ▸ R3
  obtain hM4 : Frame (wrR s) s.mem t4.mem := hm4 ▸ frame_wrR f3
  obtain hw4 : t4.wr = frR s :: s.wr := k4.2.2.trans (k3.2.2.trans (k2.2.2.trans (k1'.2.2.trans k1.2.2)))
  obtain hrd4 : t4.rd = s.rd := k4.2.1.trans (k3.2.1.trans hrd2)
  obtain hcs4 : ∀ r ∈ [Reg.r13, .r14, .r15], t4.gpr r = s.gpr r := fun r hr => by
    have : r ∉ [Reg.rax] ∧ r ∉ [Reg.rax, .rcx] ∧ r ∉ [Reg.rax, .r11] ∧ r ∉ [Reg.r11] := by
      simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
    rw [k4.gpr this.1, k3.gpr this.1, k2.gpr this.2.2.1, k1'.gpr this.2.2.2, k1.gpr this.2.1]
    simp only [allocState_gpr']; rw [ifn (by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)]
  obtain sy4 : t4.syms = s.syms := s4.trans sy3
  refine WP.seq (WP.mono (Q := EDone T.H.D lk.G Gs s) ?_ fun t3 D => restore_ok D)
  obtain hsl : (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat).length = (s.gpr .r8).toNat := by
    simp [Spec.Rsa.bytesAt]
  have hel := hp.hel
  refine WP.ite (M := isa) _ (show isa.eval .b t4 = _ from hc4) (fun hb => ?_) (fun hb => ?_)
  · -- `emLen < hLen + 2`.
    rw [decide_eq_true_eq] at hb
    refine ret0_done L4 R4 hw4 hcs4 (by simp [proW', proW, upd]) (by simp [proW', proW, upd])
      (by simp [proW', proW, upd]) (RsaPss.encode_none₂ _ _ (by rw [hsl, ← hel, hGl']; omega_using [hb]))
  rw [decide_eq_false_iff_not] at hb
  -- The salt fits.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine X86_64.WP.mono_syms (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = s.gpr .r8 ∧ t.mem = t4.mem) (by
    xrun [ea_sp, L4.rsp, L4.ld (d := sSaltLen) (by decide), R4.rd (d := sSaltLen) 40 rfl (by decide)]
    simp [proW', proW, upd]) rfl) fun t5 ⟨⟨hdx5, hm5⟩, k5⟩ s5 => ?_
  refine X86_64.WP.mono_syms (saltFits_ok (H := T.H) (by omega_using [hDN, hN]) t5 (a := (s.gpr .rsi).toNat) (b := s.gpr .r8)
    (by omega_using [hb]) (by omega_using [hk2]) (by rw [k5.gpr (by decide)]; exact hax4) hdx5) fun t6 ⟨k6, hm6, hax6, hc6⟩ s6 => ?_
  obtain L6 : Lay t6 (fb s) (stackArg s 0) := L4.congr ((k6.gpr (by decide)).trans (k5.gpr (by decide)))
    (k6.2.2.trans k5.2.2) (by rw [hm6, hm5])
  obtain hm64 : t6.mem = t4.mem := by rw [hm6, hm5]
  obtain R6 := hm64 ▸ R4
  obtain hw6 : t6.wr = frR s :: s.wr := k6.2.2.trans (k5.2.2.trans hw4)
  obtain hrd6 : t6.rd = s.rd := k6.2.1.trans (k5.2.1.trans hrd4)
  obtain hcs6 : ∀ r ∈ [Reg.r13, .r14, .r15], t6.gpr r = s.gpr r := fun r hr => by
    rw [k6.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp),
      k5.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), hcs4 r hr]
  obtain sy6 : t6.syms = s.syms := s6.trans (s5.trans sy4)
  refine WP.ite (M := isa) _ (show isa.eval .b t6 = _ from hc6) (fun hb6 => ?_) (fun hb6 => ?_)
  · -- The salt does not fit.
    rw [decide_eq_true_eq] at hb6
    refine ret0_done L6 R6 hw6 hcs6 (by simp [proW', proW, upd]) (by simp [proW', proW, upd])
      (by simp [proW', proW, upd]) (RsaPss.encode_none₂ _ _ (by rw [hsl, ← hel, hGl']; omega_using [hb6]))
  rw [decide_eq_false_iff_not] at hb6
  have tb := hp.tabs
  refine encMain_ok hH K hG hGh hGl hGv hf hg hdk lk hp L6 R6 hw6 hrd6 hcs6 (hm64 ▸ hM4) ?_ ?_
    (by simp [proW', proW, upd]) (by simp [proW', proW, upd]) (by simp only [proW', upd]; simp; rw [hel])
    (by simp [proW', upd]) (by simp [proW', proW, upd]) (by simp [proW', proW, upd]) (by simp [proW', proW, upd])
    (by simp [proW', proW, upd]) (by simp [proW', proW, upd]) (by simp [proW', proW, upd]) (by omega_using [hb, hb6]) hax6
  · rw [sy6]; exact tb.hf.ht (by simpa [upd] using tb.h0) (by simpa [upd] using tb.h3) (by simpa [upd] using tb.h4)
  · rw [sy6]
    exact tb.gf.gt (by simpa [upd] using tb.g0) (by simpa [upd] using tb.g1) (by simpa [upd] using tb.g2) (by simpa [upd] using tb.g4)

include hH K hG hGh hGl hGv hf hg hdk in
/-- `encode` meets `encK`, keeping the callee-saved registers, its return
address and MXCSR's control bits. -/
theorem enc_correct (lk : Pbkdf2.Md.X86_64.MgfLink T.H hH) (s : State) (h : (encK T lk.G Gs).pre s) :
    ∃ t s', Exec isa (encode T.f T.H T.g) s t s' ∧ abiPreserved s s' ∧ (encK T lk.G Gs).post s s' := by
  obtain hp := Pre.of T h
  obtain hsp : SpSafe (encode T.f T.H T.g) := by
    obtain h' := enc_spAll hH hf hg
    rw [Code.allInstrs_eq] at h'
    intro i hi
    simpa using List.all_eq_true.mp h' i hi
  obtain hd := enc_xd (T := T) hf hg
  obtain hW := X86_64.WP.stackFrame hsp (by unfold encStack at hd; omega_using [hd])
    (enc_ok hH K hG hGh hGl hGv hf hg hdk lk h)
  obtain ⟨t, s', he, ⟨hcs, hpost, hmx⟩, hf'⟩ := hW
  refine ⟨t, s', he, ⟨hcs, ?_, hmx⟩, hpost⟩
  refine Mem.readW_congr fun i hi => hf' _ fun r hr hc => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dRo _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) hc
    · exact hp.dRs _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) hc
  · simp only [List.mem_singleton] at hr; subst hr
    have := hp.sp1; have := hp.sp2
    exact Offset.base_disjoint_below (s.gpr .rsp) (n := (encode T.f T.H T.g).x86_64Depth) (k := 8)
      (by unfold encStack at *; omega_using [hd]) _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) hc

end VG.Proof.RsaPss.X86_64.Enc
