module

public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCtx
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncParams
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCorrect
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignPro

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

variable (G : Spec.Mgf1.Hash)

/-- `encK.pre`, by name. -/
structure Pre (s : State) : Prop where
  sp1 : encStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64
  hrd : s.rd = [⟨s.gpr .rdx, G.len⟩, ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, ⟨stackArgAddr s 0, 16⟩]
  hwr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩]
  dOdg : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, G.len⟩
  dOsa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  dOs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
  dOa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 16⟩
  ddgs : (⟨s.gpr .rdx, G.len⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
  dsas : (⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
  dsa : (⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 16⟩
  dRo : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dRdg : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, G.len⟩
  dRsa : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
  dRa : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 16⟩
  dKo : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKdg : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨s.gpr .rdx, G.len⟩
  dKsa : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint
    ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint
    ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 16⟩
  wO : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wDg : (s.gpr .rdx).toNat + G.len ≤ 2 ^ 64
  wSa : (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  wS : (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64
  b1 : 1 ≤ (s.gpr .r9).toNat
  b2 : (s.gpr .r9).toNat ≤ Proof.RsaPss.maxEmBits
  hel : (s.gpr .rsi).toNat = Spec.RsaPss.emLength (s.gpr .r9).toNat
  hsl : 1024 ≤ (stackArg s 1).toNat

theorem Pre.of {s : State} (h : (encK G).pre s) : Pre G s := by
  simp only [encK] at h
  obtain ⟨sp1, sp2, hrd, hwr, dOdg, dOsa, dOs, dOa, ddgs, dsas, dsa, dRo, dRdg, dRsa, dRs, dRa, dKo, dKdg,
    dKsa, dKs, dKa, wO, wDg, wSa, wS, b1, b2, hel, hsl⟩ := h
  exact ⟨sp1, sp2, hrd, hwr, dOdg, dOsa, dOs, dOa, ddgs, dsas, dsa, dRo, dRdg, dRsa, dRs, dRa, dKo, dKdg,
    dKsa, dKs, dKa, wO, wDg, wSa, wS, b1, b2, hel, hsl⟩

variable {G}

theorem Pre.k2 {s : State} (hp : Pre G s) : (s.gpr .rsi).toNat ≤ 1024 := by
  have := hp.hel; have := hp.b2; unfold Spec.RsaPss.emLength Proof.RsaPss.maxEmBits at *; omega

/-! ## The frame -/

/-- The stack the function uses, below `rsp`. -/
def stkR (s : State) : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩

theorem frame_sub (s : State) : Region.Sub ⟨fb s, frameBytes⟩ (stkR s) :=
  Offset.sub_below _ (by decide) (by decide)

theorem ret_sub (s : State) : Region.Sub (below (fb s) 8) (stkR s) := by
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
theorem Pre.outside {s : State} (hp : Pre G s) {R : Region}
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

theorem fb_toNat {s : State} (hp : Pre G s) : (fb s).toNat + frameBytes = (s.gpr .rsp).toNat := by
  have := hp.sp1; unfold encStack at this
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega

theorem Pre.geo {s : State} (hp : Pre G s) : Geo (fb s) (stackArg s 0) := by
  have hF := fb_toNat hp
  have := hp.sp2
  have hsl := hp.hsl
  have wS := hp.wS
  have sS : Region.Sub ⟨stackArg s 0, oRsa⟩ ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ :=
    Region.sub_prefix (by unfold oRsa; omega)
  refine ⟨by omega, by unfold oRsa; omega, ((hp.dKs.sub_left (frame_sub s)).sub_right sS),
    ((hp.dKs.sub_left (ret_sub s)).sub_right sS)⟩

/-- Memory changed only in the frame. -/
theorem frame_wrR {s : State} {m : Mem} (h : Frame [frR s] s.mem m) : Frame (wrR s) s.mem m :=
  h.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub s⟩

/-- Memory changed only in the writable regions and below the frame. -/
theorem frame_keep {s u v : State} (hp : Pre G s) (hw : u.wr = frR s :: s.wr) (hsp : u.gpr .rsp = fb s)
    (hM : Frame (wrR s) s.mem u.mem)
    (hk : ∀ a, (∀ r ∈ u.wr, ¬ r.Contains a 1) → ¬ (below (u.gpr .rsp) 8).Contains a 1 → v.mem a = u.mem a) :
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
theorem arg_read {s : State} (hp : Pre G s) {m : Mem} (hf : Frame [frR s] s.mem m) {j : Nat} (hj : j < 2) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := ⟨stackArgAddr s 0, 16⟩) ?_ (fun r' hr' => ?_) (by decide)
  · rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.dKa.sub_left (frame_sub s)).symm

theorem frame_w {s : State} (hp : Pre G s) {m m' : Mem} (hf : Frame [frR s] m m') {d : Nat}
    (hd : d + 8 ≤ frameBytes) (v : BitVec 64) : Frame [frR s] m (m'.writeW (off (fb s) d) v) := by
  have hF := fb_toNat hp
  have := hp.sp2
  exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

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
theorem copy1_ok {s : State} (hp : Pre G s) {u : State} (hsp : u.gpr .rsp = fb s) (hfr : frR s ∈ u.wr)
    (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem) {j d : Nat} (hj : j < 2) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block [.mov .rax (.mem (arg j)), .store (sp d) .rax]) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j) ∧ Frame [frR s] s.mem u'.mem := by
  have hF := fb_toNat hp
  have := hp.sp2
  have hsc : Scr u (fb s) frameBytes := Scr.of_mem hfr (by omega)
  have hin : InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
    refine ⟨⟨stackArgAddr s 0, 16⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp), ?_⟩
    rw [argAddr, show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j)) ?_ rfl)
    fun u' ⟨hm, k⟩ => ⟨k, hm, hm ▸ hf.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))⟩
  xrun [arg, ea_sp, hsp, hin, arg_read hp hf hj, hsc.st (d := d) hd]

theorem encPrologue_eq : encPrologue =
    ([.store (sp sRbx) .rbx, .store (sp sRbp) .rbp, .store (sp sR12) .r12, .store (sp sOut) .rdi,
      .store (sp sK) .rsi, .store (sp sDig) .rdx, .store (sp sSalt) .rcx, .store (sp sSaltLen) .r8] : List Instr) ++
    ([.mov .rax (.mem (arg 0)), .store (sp sScr) .rax] : List Instr) ++ maskBits .r9 := rfl

/-- The prologue: the slots as `proW'` says, the working space untouched. -/
theorem encPro_ok {s : State} (hp : Pre G s) :
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
  have hsc : Scr A (fb s) frameBytes := Scr.of_mem hfr (by omega)
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
    refine ⟨sp2, k12.2.2 ▸ hfr, by omega, by omega, ?_, ?_, G'.dFS, G'.dRS⟩
    · have hsl := hp.hsl
      refine ⟨⟨stackArg s 0, 0, (stackArg s 1).toNat * 8, by rw [k12.2.2, hA]; simp [allocState, hp.hwr],
        (BitVec.add_zero _).symm, by unfold oRsa; omega, by have := hp.wS; omega⟩, G'.Sw⟩
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

end VG.Proof.RsaPss.X86_64.Enc
