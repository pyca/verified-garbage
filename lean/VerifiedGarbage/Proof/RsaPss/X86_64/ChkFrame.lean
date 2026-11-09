module

public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCtx
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncParams
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCorrect
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignPro

/-!
# EMSA-PSS's check of an encoding on x86-64: the precondition by name, the
frame and the prologue

`Pre` names the facts of `chkK.pre`; the frame is the `frameBytes` bytes
below `rsp` (`fb`), within the stack the function uses (`stkR`). From the
entry state, after the frame's push, `chkPrologue` saves `rbx`, `rbp` and
`r12`, the arguments to their slots, and the mask and `lo = 0`
(`chkPro_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Chk

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)

variable (T : Tabs)

/-- `chkK.pre`, by name. -/
structure Pre (s : State) : Prop where
  sp1 : chkStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64
  hrd : s.rd = [⟨s.gpr .rdi, T.H.D⟩, ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩, ⟨stackArg s 2, 40⟩, ⟨stackArg s 3, 40⟩,
    ⟨stackArgAddr s 0, 32⟩]
  hwr : s.wr = [⟨stackArg s 0, (stackArg s 1).toNat * 8⟩]
  ddgs : (⟨s.gpr .rdi, T.H.D⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
  dems : (⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
  dsa : (⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 32⟩
  dRdg : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, T.H.D⟩
  dRem : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
  dRa : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 32⟩
  dKdg : (⟨s.gpr .rsp - BitVec.ofNat 64 chkStack, chkStack⟩ : Region).Disjoint ⟨s.gpr .rdi, T.H.D⟩
  dKem : (⟨s.gpr .rsp - BitVec.ofNat 64 chkStack, chkStack⟩ : Region).Disjoint
    ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 chkStack, chkStack⟩ : Region).Disjoint
    ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 chkStack, chkStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 32⟩
  wDg : (s.gpr .rdi).toNat + T.H.D ≤ 2 ^ 64
  wEm : (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  wS : (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64
  b1 : 1 ≤ (s.gpr .rcx).toNat
  b2 : (s.gpr .rcx).toNat ≤ Proof.RsaPss.maxEmBits
  hel : (s.gpr .rdx).toNat = Spec.RsaPss.emLength (s.gpr .rcx).toNat
  hsl : 1024 ≤ (stackArg s 1).toNat
  dstH : (⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ : Region).Disjoint ⟨stackArg s 2, 40⟩
  dstG : (⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ : Region).Disjoint ⟨stackArg s 3, 40⟩
  dRtH : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 2, 40⟩
  dRtG : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 3, 40⟩
  dKtH : (⟨s.gpr .rsp - BitVec.ofNat 64 chkStack, chkStack⟩ : Region).Disjoint ⟨stackArg s 2, 40⟩
  dKtG : (⟨s.gpr .rsp - BitVec.ofNat 64 chkStack, chkStack⟩ : Region).Disjoint ⟨stackArg s 3, 40⟩
  wTH : (stackArg s 2).toNat + 40 ≤ 2 ^ 64
  wTG : (stackArg s 3).toNat + 40 ≤ 2 ^ 64
  tabs : TabsAt T.H T.dn T.f T.G T.g (stackArg s 2) (stackArg s 3) s

theorem Pre.of {Hs Gs : Spec.Mgf1.Hash} {s : State} (h : (chkK T Hs Gs).pre s) : Pre T s := by
  simp only [chkK] at h
  obtain ⟨sp1, sp2, hrd, hwr, ddgs, dems, dsa, dRdg, dRem, dRs, dRa, dKdg, dKem, dKs, dKa, wDg, wEm, wS, b1, b2,
    hel, hsl, dstH, dstG, dRtH, dRtG, dKtH, dKtG, wTH, wTG, tabs⟩ := h
  exact ⟨sp1, sp2, hrd, hwr, ddgs, dems, dsa, dRdg, dRem, dRs, dRa, dKdg, dKem, dKs, dKa, wDg, wEm, wS, b1, b2,
    hel, hsl, dstH, dstG, dRtH, dRtG, dKtH, dKtG, wTH, wTG, tabs⟩

variable {T}

theorem Pre.k2 {s : State} (hp : Pre T s) : (s.gpr .rdx).toNat ≤ 1024 := by
  have := hp.hel; have := hp.b2; unfold Spec.RsaPss.emLength Proof.RsaPss.maxEmBits at *; omega

theorem Pre.k1 {s : State} (hp : Pre T s) : 1 ≤ (s.gpr .rdx).toNat := by
  have := hp.hel; have := hp.b1; unfold Spec.RsaPss.emLength at *; omega

/-! ## The frame -/

/-- The stack the function uses, below `rsp`. -/
def stkR (s : State) : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 chkStack, chkStack⟩

theorem frame_sub (s : State) : Region.Sub ⟨fb s, frameBytes⟩ (stkR s) :=
  Offset.sub_below _ (by decide) (by decide)

theorem ret_sub (s : State) : Region.Sub (below (fb s) 16) (stkR s) := by
  simp only [below, fb, sub_sub']
  exact Offset.sub_below _ (by decide) (by decide)

def scrR (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩

/-- The two regions the function writes. -/
abbrev wrR (s : State) : List Region := [stkR s, scrR s]

/-- An input, apart from them. -/
theorem in_apart {s : State} {R : Region} (hK : (stkR s).Disjoint R) (hS : R.Disjoint (scrR s)) :
    ∀ r ∈ wrR s, R.Disjoint r := by
  intro r hr
  simp only [wrR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hK.symm
  · exact hS

/-- An address of an input: in no writable region of the frame's state, nor
below the frame. -/
theorem Pre.outside {s : State} (hp : Pre T s) {R : Region}
    (hS : R.Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩) (hK : (stkR s).Disjoint R) {a : Addr}
    (ha : R.Contains a 1) : Outside (⟨fb s, frameBytes⟩ :: s.wr) (fb s) a := by
  refine ⟨fun r hr hc => ?_, fun hc => hK a (ret_sub s a hc) ha⟩
  rw [List.mem_cons, hp.hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hK a (frame_sub s a hc) ha
  · exact hS a ha hc

theorem fb_toNat {s : State} (hp : Pre T s) : (fb s).toNat + frameBytes = (s.gpr .rsp).toNat := by
  have := hp.sp1; unfold chkStack at this
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega

theorem Pre.geo {s : State} (hp : Pre T s) : Geo (fb s) (stackArg s 0) := by
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
theorem frame_keep {s u v : State} (hp : Pre T s) (hw : u.wr = frR s :: s.wr) (hsp : u.gpr .rsp = fb s)
    (hM : Frame (wrR s) s.mem u.mem)
    (hk : ∀ a, (∀ r ∈ u.wr, ¬ r.Contains a 1) → ¬ (below (u.gpr .rsp) 16).Contains a 1 → v.mem a = u.mem a) :
    Frame (wrR s) s.mem v.mem := by
  intro x hx
  refine (hk x (fun r hr hc => ?_) (fun hc => ?_)).trans (hM x hx)
  · rw [hw, hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hx _ (List.mem_cons_self ..) (frame_sub s x hc)
    · exact hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hc
  · rw [hsp] at hc; exact hx _ (List.mem_cons_self ..) (ret_sub s x hc)

/-! ## The prologue -/

/-- Stack argument `j`, read from memory changed only in the frame. -/
theorem arg_read {s : State} (hp : Pre T s) {m : Mem} (hf : Frame [frR s] s.mem m) {j : Nat} (hj : j < 4) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := ⟨stackArgAddr s 0, 32⟩) ?_ (fun r' hr' => ?_) (by decide)
  · rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.dKa.sub_left (frame_sub s)).symm

theorem frame_w {s : State} (hp : Pre T s) {m m' : Mem} (hf : Frame [frR s] m m') {d : Nat}
    (hd : d + 8 ≤ frameBytes) (v : BitVec 64) : Frame [frR s] m (m'.writeW (off (fb s) d) v) := by
  have hF := fb_toNat hp
  have := hp.sp2
  exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

/-- The slots `chkPrologue` stores to, and what, before the mask. -/
def proW (s : State) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd (upd (upd (fun k => word s.mem (fb s) (8 * k))
    41 (s.gpr .rbx)) 42 (s.gpr .rbp)) 43 (s.gpr .r12)) 37 (s.gpr .rdi)) 38 (s.gpr .rsi)) 17 (s.gpr .rdx))
    36 (s.gpr .r8)) 21 (stackArg s 0)

/-- And after it. -/
def proW' (s : State) : Nat → BitVec 64 :=
  upd (upd (proW s) 25 (BitVec.setWidth 64 ((0xFF : Byte) >>>
    (8 * Spec.RsaPss.emLength (s.gpr .rcx).toNat - (s.gpr .rcx).toNat)))) 26 0

/-- One stack argument copied to a slot. -/
theorem copy1_ok {s : State} (hp : Pre T s) {u : State} (hsp : u.gpr .rsp = fb s) (hfr : frR s ∈ u.wr)
    (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem) {j d : Nat} (hj : j < 4) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block [.mov .rax (.mem (arg j)), .store (sp d) .rax]) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j) ∧ Frame [frR s] s.mem u'.mem := by
  have hF := fb_toNat hp
  have := hp.sp2
  have hsc : Scr u (fb s) frameBytes := Scr.of_mem hfr (by omega)
  have hin : InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
    refine ⟨⟨stackArgAddr s 0, 32⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp), ?_⟩
    rw [argAddr, show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j)) ?_ rfl)
    fun u' ⟨hm, k⟩ => ⟨k, hm, hm ▸ hf.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))⟩
  xrun [arg, ea_sp, hsp, hin, arg_read hp hf hj, hsc.st (d := d) hd]

theorem chkPrologue_eq : chkPrologue =
    ([.store (sp sRbx) .rbx, .store (sp sRbp) .rbp, .store (sp sR12) .r12, .store (sp sDig) .rdi,
      .store (sp sSig) .rsi, .store (sp sK) .rdx, .store (sp sSlen) .r8] : List Instr) ++
    ([.mov .rax (.mem (arg 0)), .store (sp sScr) .rax] : List Instr) ++ maskBits .rcx := rfl

/-- The prologue: the slots as `proW'` says, the working space untouched. -/
theorem chkPro_ok {s : State} (hp : Pre T s) :
    WP isa (.block chkPrologue) (allocState frameBytes s) fun t => Keep [.rax, .rcx] (allocState frameBytes s) t ∧
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
  rw [chkPrologue_eq, WP.block_append_iff, WP.block_append_iff]
  have R1 := (((((((R0.wf G' (k := 41) (by decide) (s.gpr .rbx)).wf G' (k := 42) (by decide) (s.gpr .rbp)).wf G'
    (k := 43) (by decide) (s.gpr .r12)).wf G' (k := 37) (by decide) (s.gpr .rdi)).wf G' (k := 38) (by decide)
    (s.gpr .rsi)).wf G' (k := 17) (by decide) (s.gpr .rdx)).wf G' (k := 36) (by decide) (s.gpr .r8))
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = ((((((s.mem.writeW (off (fb s) (8 * 41)) (s.gpr .rbx)).writeW
      (off (fb s) (8 * 42)) (s.gpr .rbp)).writeW (off (fb s) (8 * 43)) (s.gpr .r12)).writeW (off (fb s) (8 * 37))
      (s.gpr .rdi)).writeW (off (fb s) (8 * 38)) (s.gpr .rsi)).writeW (off (fb s) (8 * 17)) (s.gpr .rdx)).writeW
      (off (fb s) (8 * 36)) (s.gpr .r8)) ?_ rfl) fun t1 ⟨hm1, k1⟩ => ?_
  · xrun [ea_sp, hsp, hsc.st (d := sRbx) (by decide), hsc.st (d := sRbp) (by decide),
      hsc.st (d := sR12) (by decide), hsc.st (d := sDig) (by decide), hsc.st (d := sSig) (by decide),
      hsc.st (d := sK) (by decide), hsc.st (d := sSlen) (by decide), allocState_gpr']
    rfl
  have f1 : Frame [frR s] s.mem t1.mem := by
    rw [hm1]
    exact frame_w hp (frame_w hp (frame_w hp (frame_w hp (frame_w hp (frame_w hp (frame_w hp
      (Frame.refl _ _) (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _)
      (by decide) _
  have sp1 : t1.gpr .rsp = fb s := k1.gpr (by decide)
  refine WP.mono (copy1_ok hp sp1 (k1.2.2 ▸ hfr) k1.2.1 f1 (j := 0) (d := sScr) (by decide) (by decide))
    fun t2 ⟨k2, hm2, f2⟩ => ?_
  have R2 : Rep t2.mem (fb s) (stackArg s 0) (fun o => s.mem (off (stackArg s 0) o)) (proW s) := by
    rw [hm2, hm1]; exact R1.wf G' (k := 21) (by decide) (stackArg s 0)
  have k12 : Keep [.rax] A t2 := (k1.trans k2).mono (by decide)
  have sp2 : t2.gpr .rsp = fb s := k12.gpr (by decide)
  have h392 : frameBytes = 392 := rfl
  have L2 : Lay t2 (fb s) (stackArg s 0) := by
    have := hp.sp1; unfold chkStack at this
    refine ⟨sp2, k12.2.2 ▸ hfr, by omega, by omega, ?_, ?_, G'.dFS, G'.dRS⟩
    · have hsl := hp.hsl
      refine ⟨⟨stackArg s 0, 0, (stackArg s 1).toNat * 8, by rw [k12.2.2, hA]; simp [allocState, hp.hwr],
        (BitVec.add_zero _).symm, by unfold oRsa; omega, by have := hp.wS; omega⟩, G'.Sw⟩
    · rw [show sScr = 8 * 21 from rfl]
      exact (R2.fr 21 (by decide)).trans (by simp [proW, upd])
  have hb : t2.gpr .rcx = BitVec.ofNat 64 (s.gpr .rcx).toNat := by
    rw [k12.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  refine WP.mono (maskBits_ok L2 R2 (r := .rcx) (by decide) (b := (s.gpr .rcx).toNat)
    (by simp only [proW, upd, Nat.reduceEqDiff, ite_true, ite_false]; rw [← hp.hel, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]) hb hp.b2) fun t3 ⟨L3, k3, R3, hm3⟩ => ?_
  refine ⟨(k12.trans k3).mono (by decide), L3, R3, ?_⟩
  rw [hm3]
  exact frame_w hp (frame_w hp f2 (d := sC) (by decide) _) (d := sLo) (by decide) _

/-! ## The tables' words -/

theorem tab_sub {s : State} (hp : Pre T s) {i : Nat} (hi : i = 2 ∨ i = 3) :
    (⟨stackArg s i, 40⟩ : Region) ∈ s.rd ∧ (stkR s).Disjoint ⟨stackArg s i, 40⟩ ∧
      (stackArg s i).toNat + 40 ≤ 2 ^ 64 := by
  rcases hi with rfl | rfl
  · exact ⟨by rw [hp.hrd]; simp, hp.dKtH, hp.wTH⟩
  · exact ⟨by rw [hp.hrd]; simp, hp.dKtG, hp.wTG⟩

/-- A word of a table, read from memory changed only in the frame. -/
theorem tab_rd {s : State} (hp : Pre T s) {m : Mem} (hf : Frame [frR s] s.mem m) {i j : Nat} (hi : i = 2 ∨ i = 3)
    (hj : j + 8 ≤ 40) : m.readW (off (stackArg s i) j) 64 = s.mem.readW (off (stackArg s i) j) 64 := by
  obtain ⟨-, hK, hw⟩ := tab_sub hp hi
  refine hf.readW (r := ⟨stackArg s i, 40⟩) (Offset.contains_base _ (by omega) (by omega)) (fun r' hr' => ?_)
    (by decide)
  simp only [List.mem_singleton] at hr'; subst hr'
  exact (hK.sub_left (frame_sub s)).symm

/-- One word of the table at `r11` copied to a slot. -/
theorem tabCopy_ok {s : State} (hp : Pre T s) {u : State} (hsp : u.gpr .rsp = fb s) (hfr : frR s ∈ u.wr)
    (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem) {i j d : Nat} (hi : i = 2 ∨ i = 3)
    (h11 : u.gpr .r11 = stackArg s i) (hj : j + 8 ≤ 40) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block [.mov .rax (.mem (at_ .r11 j)), .store (sp d) .rax]) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) d) (s.mem.readW (off (stackArg s i) j) 64) ∧ Frame [frR s] s.mem u'.mem := by
  have hF := fb_toNat hp
  have := hp.sp2
  obtain ⟨hm, -, hw⟩ := tab_sub hp hi
  have hsc : Scr u (fb s) frameBytes := Scr.of_mem hfr (by omega)
  have hin : InRegions (u.rd ++ u.wr) (off (stackArg s i) j) 8 :=
    ⟨_, List.mem_append_left _ (by rw [hrd]; exact hm), Offset.contains_base _ (by omega) (by omega)⟩
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
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (WP.keep [.r11] (Q := fun u' => u'.mem = u.mem ∧ u'.gpr .r11 = stackArg s j) ?_ rfl)
    fun u' ⟨⟨hm, h⟩, k⟩ => ⟨k, hm, h⟩
  xrun [arg, ea_sp, hsp, hin, arg_read hp hf hj]

theorem hSlots_eq : hSlots = ([.mov .rax (.mem (at_ .r11 0)), .store (sp sIniH) .rax] : List Instr) ++
    ([.mov .rax (.mem (at_ .r11 24)), .store (sp sCmpH) .rax] : List Instr) ++
    ([.mov .rax (.mem (at_ .r11 32)), .store (sp sDigH) .rax] : List Instr) := rfl

theorem gSlots_eq : gSlots = ([.mov .rax (.mem (at_ .r11 0)), .store (sp sIniG) .rax] : List Instr) ++
    ([.mov .rax (.mem (at_ .r11 8)), .store (sp sUpdG) .rax] : List Instr) ++
    ([.mov .rax (.mem (at_ .r11 16)), .store (sp sFinG) .rax] : List Instr) ++
    ([.mov .rax (.mem (at_ .r11 32)), .store (sp sDG) .rax] : List Instr) := rfl

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
        14 (s.mem.readW (off (stackArg s 3) 32) 64)) := by
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
    ((k13.gpr (by decide)).trans h11) (j := 32) (d := sDG) (by decide) (by decide)) fun u4 ⟨k4, hm4, f4⟩ => ?_
  have R4 : Rep u4.mem (fb s) (stackArg s 0) V (upd (upd (upd (upd W 11 (s.mem.readW (off (stackArg s 3) 0) 64))
      12 (s.mem.readW (off (stackArg s 3) 8) 64)) 13 (s.mem.readW (off (stackArg s 3) 16) 64))
      14 (s.mem.readW (off (stackArg s 3) 32) 64)) := by
    rw [hm4, hm3, hm2, hm1]
    exact (((R.wf G' (k := 11) (by decide) _).wf G' (k := 12) (by decide) _).wf G' (k := 13) (by decide) _).wf G'
      (k := 14) (by decide) _
  have k14 : Keep [.rax] u u4 := (k13.trans k4).mono (by decide)
  exact ⟨k14, L.of_rep' R R4 (by simp [upd]) (k14.gpr (by decide)) k14.2.2, f4, R4⟩

end VG.Proof.RsaPss.X86_64.Chk
