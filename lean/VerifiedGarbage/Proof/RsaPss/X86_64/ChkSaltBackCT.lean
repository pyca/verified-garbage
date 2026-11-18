module

public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkFixedSaltCT
meta import VerifiedGarbage.Proof.RsaPss.X86_64.ChkFixedSaltCT
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Sha256.StateMem
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.RsaPss.X86_64.Params
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignPro
public import VerifiedGarbage.Proof.RsaPss.X86_64.CtBase
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCorrect
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCorrect
import VerifiedGarbage.Proof.RsaPss.MgfBytes
public import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
import VerifiedGarbage.Proof.RsaPss.SignEncode
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCtx
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCtx
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
public import VerifiedGarbage.Proof.RsaPss.X86_64.Checks
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.RsaPss.X86_64.Checks
meta import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaPss.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.RsaPss.EncodeEq
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncParams
import Mathlib.Tactic.Set

/-! ### `RsaPss.X86_64.EncFixed`, which the modules that import this one used -/

section

/-! ### `RsaPss.X86_64.EncCorrect`, which the modules that import this one used -/

section

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
theorem restore_ok {Hs : Spec.Mgf1.Hash} {s t : State} (hp : Pre T s) (D : EDone T.H.D Hs Gs s t) :
    WP isa (.block restoreRegs) t fun t' => t'.gpr .rsp = fb s ∧ t'.wr = (allocState frameBytes s).wr ∧
      ∀ m u, Frame [⟨fb s, frameBytes⟩] t'.mem m →
        (∀ r ∈ calleeSaved, ({ freedF t' with mem := m, unknowns := u } : State).gpr r = s.gpr r) ∧ (encK T Hs Gs).post s ({ freedF t' with mem := m, unknowns := u } : State) := by
  refine WP.mono (WP.keep [.rbx, .rbp, .r12] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rbx = s.gpr .rbx ∧
      t'.gpr .rbp = s.gpr .rbp ∧ t'.gpr .r12 = s.gpr .r12) ?_ rfl) fun t' ⟨⟨hm, h1, h2, h3⟩, k⟩ => ?_
  · xrun [restoreRegs, ea_sp, D.L.rsp, D.L.ld (d := sRbx) (by decide), D.L.ld (d := sRbp) (by decide),
      D.L.ld (d := sR12) (by decide), D.rbx, D.rbp, D.r12]
  obtain hsp : t'.gpr .rsp = fb s := (k.gpr (by decide)).trans D.L.rsp
  refine ⟨hsp, k.2.2.trans D.wr, fun m u fm => ⟨fun r hr => ?_, ?_⟩⟩
  · show (freedF t').gpr r = s.gpr r
    simp only [freedF, State.setReg]
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
    have hb : Spec.Rsa.bytesAt m (s.gpr .rdi) (s.gpr .rsi).toNat =
        Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat := by
      rw [← hm]
      exact Proof.Rsa.rsa_bytes_frame fm (s.gpr .rsi).isLt (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact (hp.dKo.sub_left (frame_sub s)).symm)
    have hout := D.out
    simp only [OutOk, encOut] at hout
    simp only [encK, hax]
    rw [hb]
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
    s₂.wr = (allocState frameBytes s).wr ∧ ∀ m u, Frame [⟨fb s, frameBytes⟩] s₂.mem m →
      (∀ r ∈ calleeSaved, ({ freedF s₂ with mem := m, unknowns := u } : State).gpr r = s.gpr r) ∧
      (encK T lk.G Gs).post s { freedF s₂ with mem := m, unknowns := u }) ?_ fun t ⟨a, b, c⟩ hmx =>
    ⟨a, b, fun m u fm => ⟨(c m u fm).1, (c m u fm).2,
      by rw [show ({ freedF t with mem := m, unknowns := u } : State).mxcsr = t.mxcsr from rfl, hmx]; rfl⟩⟩
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
  refine WP.seq (WP.mono (Q := EDone T.H.D lk.G Gs s) ?_ fun t3 D => restore_ok hp D)
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

end

end

/-!
# EMSA-PSS's encoding and its check on x86-64: the taint checks of the
pieces that do not depend on the hash function
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64

/-- The checks of `encode`'s own pieces. -/
structure EFixed : Prop where
  pro : ∃ hc, (taint.check (pT 2 [] [.rdi, .rsi, .rdx, .rcx, .r8, .r9])
    (.block (encPrologue ++ [.mov .r11 (.mem (arg 2))])) hc).isSome = true
  hSl : ∃ hc, (taint.check (pT 2 [] [.r11]) (.block (hSlots ++ [.mov .r11 (.mem (arg 3))])) hc).isSome = true
  gSl : ∃ hc, (taint.check (pT 2 [] [.r11]) (.block gSlots) hc).isSome = true
  ret0 : ∃ hc, (taint.check (pT 2 [] []) ret0 hc).isSome = true
  copyOut : ∃ hc, (taint.check (pT 2 [16, 17, 21] []) copyOut hc).isSome = true
  ret1 : ∃ hc, (taint.check (pT 2 [] []) (.block [.mov32 .rax (.imm 1)]) hc).isSome = true

theorem eFixed : EFixed :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩⟩

/-- The checks of `checkEncoding`'s own pieces. -/
structure CFixed : Prop where
  pro : ∃ hc, (taint.check (pT 1 [] [.rdi, .rsi, .rdx, .rcx, .r8])
    (.block (chkPrologue ++ [.mov .r11 (.mem (arg 2))])) hc).isSome = true
  hSl : ∃ hc, (taint.check (pT 1 [] [.r11]) (.block (hSlots ++ [.mov .r11 (.mem (arg 3))])) hc).isSome = true
  gSl : ∃ hc, (taint.check (pT 1 [] [.r11]) (.block gSlots) hc).isSome = true
  copyIn : ∃ hc, (taint.check (pT 1 [17, 21, 38] []) copyIn hc).isSome = true
  any1 : ∃ hc, (taint.check (pT 1 [] []) (.block [.mov32 .rax (.reg .r9), .alu .test .rax (.reg .rax)]) hc).isSome
    = true
  anyT : ∃ hc, (taint.check (pT 1 [] [])
    (.block [.mov32 .rax (.imm 0), .store (sp sAny) .rax, .mov .rdx (.mem (sp sSlen))]) hc).isSome = true
  anyE : ∃ hc, (taint.check (pT 1 [] [])
    (.block [.mov32 .rax (.imm 1), .store (sp sAny) .rax, .mov32 .rdx (.imm 0)]) hc).isSome = true
  ret0 : ∃ hc, (taint.check (pT 1 [] []) ret0 hc).isSome = true
  dbSlots : ∃ hc, (taint.check (pT 1 [26] [.rax]) (.block dbSlots) hc).isSome = true
  restore : ∃ hc, (taint.check (pT 1 [] []) (.block restoreRegs) hc).isSome = true

theorem cFixed : CFixed :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

end VG.Proof.RsaPss.X86_64

end

end

/-! ### `RsaPss.X86_64.SignCCt`, which the modules that import this one used -/

section

/-! ### `RsaPss.X86_64.SignFixed`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS signing on x86-64: the taint checks of the pieces that do not
depend on the hash function
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64

/-- `putH`'s last block: `0xbc` at `EM`'s last byte. -/
def putHTail : List Instr :=
  scr .rdi oEm ++ [.mov .rax (.mem (sp sK)), .alu .add .rdi (.reg .rax), .alu .sub .rdi (.imm 1),
    .mov32 .rax (.imm 0xbc), .store8 (at_ .rdi) .rax]

theorem putH_eq (H : Impl.Pbkdf2.Md.X86_64.Hash) : putH H =
    .seq (.block (([.mov .rdi (.mem (sp sEb)), .mov .rax (.mem (sp sDb)), .alu .add .rdi (.reg .rax)] : List Instr) ++
      scr .rsi oDig ++ ([.mov32 .r8 (.imm 0)] : List Instr)))
    (.seq (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rdi .r8) .rax] (.imm (BitVec.ofNat 32 H.D)))
      (.block putHTail)) := rfl

/-- The checks. -/
structure SFixed : Prop where
  pro : ∃ hc, (taint.check (pT 2 [] [.rdi, .rsi, .rdx, .rcx, .r8, .r9]) (.block (signPrologue ++ n0)) hc).isSome
    = true
  fail : ∃ hc, (taint.check (pT 2 [16, 17] []) signFail hc).isSome = true
  dbSlots : ∃ hc, (taint.check (pT 2 [26] [.rax]) (.block dbSlots) hc).isSome = true
  clearEm : ∃ hc, (taint.check (pT 2 [17, 21] []) clearEm hc).isSome = true
  putSalt : ∃ hc, (taint.check (pT 2 [23, 24, 39, 40] []) putSalt hc).isSome = true
  putHTail : ∃ hc, (taint.check (pT 2 [17, 21] []) (.block putHTail) hc).isSome = true
  clearTop : ∃ hc, (taint.check (pT 2 [23] []) (.block clearTop) hc).isSome = true
  privArgs : ∃ hc, (taint.check (pT 2 [] []) (.block privArgs) hc).isSome = true
  restore : ∃ hc, (taint.check (pT 2 [] []) (.block restoreRegs) hc).isSome = true

theorem sFixed : SFixed :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

end VG.Proof.RsaPss.X86_64

end

end

/-! ### `RsaPss.X86_64.SignCFixed`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS signing and verification on x86-64, around the encoding: the
taint checks of their own pieces
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64

/-- The checks. -/
structure SCFixed : Prop where
  pro : ∃ hc, (taint.check (pT 2 [] [.rdi, .rsi, .rdx, .rcx, .r8, .r9])
    (.block (signPrologue ++ n0 ++ [.mov .r11 (.mem (arg 16))])) hc).isSome = true
  idx : ∃ hc, (taint.check (pT 2 [] [.r11]) (.block idxSlot) hc).isSome = true
  prep : ∃ hc, (taint.check (pT 2 [17, 21, 22, 37, 39, 40, 47] [.rax]) (.block (emBitsB ++ encArgs ++ idxLoad))
    hc).isSome = true
  cmp : ∀ j ∈ idxs, ∃ hc, (taint.check (pT 2 [] [.r11]) (.block [.alu .cmp .r11 (.imm (BitVec.ofNat 32 j))])
    hc).isSome = true
  test : ∃ hc, (taint.check (pT 2 [] []) (.block [.alu32 .test .rax (.reg .rax)]) hc).isSome = true

theorem scFixed : SCFixed :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, fun j hj => by
    simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩⟩

/-- The arguments of `vg_rsa_private_checked_precomputed`. -/
theorem privArgsP_fixed : ∃ hc, (taint.check (pT 2 [] []) (.block privArgsP) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- Verification's. -/
structure VCFixed : Prop where
  pro : ∃ hc, (taint.check (pT 1 [] [.rdi, .rsi, .rdx, .rcx, .r8, .r9])
    (.block (verifyPrologue ++ n0 ++ [.mov .r11 (.mem (arg 8))])) hc).isSome = true
  idx : ∃ hc, (taint.check (pT 1 [] [.r11]) (.block idxSlot) hc).isSome = true
  prep : ∃ hc, (taint.check (pT 1 [17, 19, 20, 21, 22, 38] [.rax]) (.block (emBitsB ++ pubArgsC)) hc).isSome = true
  chkArgs : ∃ hc, (taint.check (pT 1 ([17, 21, 22, 37, 47] ++ [26, 27, 28]) []) (.block (chkArgs ++ idxLoad))
    hc).isSome = true
  cmp : ∀ j ∈ idxs, ∃ hc, (taint.check (pT 1 [] [.r11]) (.block [.alu .cmp .r11 (.imm (BitVec.ofNat 32 j))])
    hc).isSome = true
  acc : ∃ hc, (taint.check (pT 1 [] []) (.block [.alu .and .rax (.mem (sp sAcc))]) hc).isSome = true

theorem vcFixed : VCFixed :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, fun j hj => by
    simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩⟩

end VG.Proof.RsaPss.X86_64

end

end

/-! ### `RsaPss.X86_64.SignCVerified`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS signing on x86-64, around the encoding: the calling convention

`signC_correct`: `signC` meets `signK` and keeps the callee-saved registers,
its return address (which only its frame and calls are below) and MXCSR's
control bits (no instruction loads MXCSR).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.Rsa.X86_64 (chkContract)

variable {tsH tsG : List FnTable} {f : MdFns} {g : Impl.Mgf1.X86_64.Table.Fns} {privN : String}
  {privC : Prog isa}

theorem spAll_of {c : Prog isa} (hC : SpSafe c) : c.allInstrs (fun i => !isa.writesSp i) = true := by
  rw [Code.allInstrs_eq]; exact List.all_eq_true.mpr fun i hi => by rw [hC i hi]; rfl

/-- The calls of `byIdx` keep the stack pointer, and use at most `n` bytes of
stack. -/
theorem byIdx_calls {b : Nat → Prog isa} {n : Nat} : ∀ {is : List Nat},
    (∀ i ∈ is, (b i).allInstrs (fun i => !isa.writesSp i) = true ∧ (b i).x86_64Depth ≤ n) →
    (byIdx b is).allInstrs (fun i => !isa.writesSp i) = true ∧ (byIdx b is).x86_64Depth ≤ n
  | [], _ => ⟨rfl, Nat.zero_le _⟩
  | [i], h => h i (List.mem_singleton_self _)
  | i :: j :: is, h => by
    have ih := byIdx_calls (b := b) (n := n) (is := j :: is) fun k hk => h k (List.mem_cons_of_mem _ hk)
    have hi := h i (List.mem_cons_self ..)
    simp only [byIdx, Code.allInstrs, Code.x86_64Depth, ih.1, hi.1, Bool.and_true]
    exact ⟨rfl, by simp only [Nat.zero_max, Nat.max_le]; exact ⟨hi.2, ih.2⟩⟩

theorem enc_calls (hE : ∀ i ∈ idxs, SpSafe (encode f (ofIdx i) g))
    (hdE : ∀ i ∈ idxs, (encode f (ofIdx i) g).x86_64Depth ≤ encStack) :
    (byIdx (fun i => .call (encName i) (encode f (ofIdx i) g)) idxs).allInstrs (fun i => !isa.writesSp i) = true ∧
      (byIdx (fun i => .call (encName i) (encode f (ofIdx i) g)) idxs).x86_64Depth ≤ encStack + 8 :=
  byIdx_calls fun i hi => ⟨by simp only [Code.allInstrs]; exact spAll_of (hE i hi),
    by simp only [Code.x86_64Depth]; have := hdE i hi; omega_using [this]⟩

theorem signC_xd (hdE : ∀ i ∈ idxs, (encode f (ofIdx i) g).x86_64Depth ≤ encStack)
    (hE : ∀ i ∈ idxs, SpSafe (encode f (ofIdx i) g)) (hd : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes) :
    (Impl.RsaPss.X86_64.signC f g privN privC).x86_64Depth ≤ signStack := by
  have := (enc_calls hE hdE).2
  simp only [Impl.RsaPss.X86_64.signC, signCBody, signCBodyWith, seqs, Code.x86_64Depth, signFail, byteLoop,
    X86_64.Instr.frameBytes, Nat.zero_max, Nat.max_zero]
  unfold signStack Rsa.X86_64.stackBytes frameBytes encStack at *
  omega

/-- Code that writes `rsp` only in frames and calls, within `signStack`, and
leaves what `signK` says, the callee-saved registers and MXCSR's control
bits: it meets `signK` and keeps its return address. -/
theorem signCode_correct {c : Prog isa} (hsp : SpSafe c) (hd : c.x86_64Depth ≤ signStack) {s : State}
    (hp : SPre tsH tsG s)
    (hW : WP isa c s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ (signK tsH tsG).post s s' ∧
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10) :
    ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (signK tsH tsG).post s s' := by
  have hW := X86_64.WP.stackFrame hsp (by unfold signStack Rsa.X86_64.stackBytes at hd; omega_using [hd]) hW
  obtain ⟨t, s', he, ⟨hcs, hpost, hmx⟩, hf⟩ := hW
  refine ⟨t, s', he, ⟨hcs, ?_, hmx⟩, hpost⟩
  -- The return address.
  refine Mem.readW_congr fun i hi => hf _ fun r hr hc => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dRo _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) hc
    · exact hp.dRs _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) hc
  · simp only [List.mem_singleton] at hr; subst hr
    have := hp.sp1; have := hp.sp2
    exact Offset.base_disjoint_below (s.gpr .rsp) (n := c.x86_64Depth)
      (k := 8) (by unfold signStack at *; omega_arith) _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) hc

end VG.Proof.RsaPss.X86_64

end

end

/-! ### `RsaPss.X86_64.SignCtBase`, which only this module used -/

section

/-!
# RSASSA-PSS signing on x86-64: two runs

As for verification (`VerifyCtBase`): each run's entry state `s` agrees with
the first's, `a`, on the public data (`SSib`), from which both compute the
same public values (`sw`): the arguments, the encoding's length, `DB`'s
place and length, the mask of the top bits, the salt's length and the hash's
blocks. The digest, the salt and the private key are secret. A run's state
between two pieces is described by `SS`; both runs then start the next
piece's taint analysis from the same public values (`stwo`). The writable
regions after the frame are `out` and the working space.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable (tsH tsG : List FnTable) (Xs : State → State → Prop)

/-- Word 5 of the table `hash`: the index of its hash function. -/
def idxWord (s : State) : BitVec 64 := s.mem.readW (off (stackArg s 16) 40) 64

/-- The entry state `s` of a run, and the first's, `a`, with the same index
of the hash function of the table `hash` (word 5 of the table, which the
tables of `MdHash` the precondition allows give, and the public data fix). -/
def SSib (a s : State) : Prop := SPre tsH tsG a ∧ (signK tsH tsG).pub a s ∧ SPre tsH tsG s ∧
  idxWord s = idxWord a ∧ Xs a s

/-- A predicate of the state of a run, given its entry state, for every run
whose entry state agrees with `a`. -/
def SAt (J : State → State → Prop) (a t : State) : Prop := ∃ s, SSib tsH tsG Xs a s ∧ J s t

theorem spub_refl (s : State) : (signK tsH tsG).pub s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

variable {tsH tsG Xs}

namespace SSib

variable {a s : State} (h : SSib tsH tsG Xs a s)
include h

theorem gpr {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) : s.gpr r = a.gpr r :=
  (h.2.1.1 r hr).symm

theorem arg {i : Nat} (hi : i < 18) : stackArg s i = stackArg a i := by
  have := congrArg (fun l => l.getD i 0) h.2.1.2.1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some] at this
  exact this.symm

theorem nB : Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
    Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := h.2.1.2.2.1.symm

theorem eB : Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat =
    Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := h.2.1.2.2.2.1.symm

theorem pa : SPre tsH tsG a := h.1
theorem ps : SPre tsH tsG s := h.2.2.1

theorem idxw : idxWord s = idxWord a := h.2.2.2.1

theorem x : Xs a s := h.2.2.2.2

theorem fb : fb s = fb a := by
  simp only [VG.Proof.RsaPss.X86_64.fb, h.gpr (r := .rsp) (by decide)]

theorem wr : s.wr = a.wr := by
  rw [h.ps.hwr, h.pa.hwr, h.arg (i := 14) (by decide), h.arg (i := 15) (by decide), h.gpr (r := .rdi) (by decide),
    h.gpr (r := .rsi) (by decide)]

theorem frR : frR s = ⟨VG.Proof.RsaPss.X86_64.fb a, frameBytes⟩ := by
  simp only [VG.Proof.RsaPss.X86_64.frR, h.fb]

theorem n0 : s.mem (s.gpr .rdx) = a.mem (a.gpr .rdx) := by
  have := congrArg (fun l => l.getD 0 0) h.nB
  have hk := h.ps.k1
  have hk' := h.pa.k1
  simpa [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_range (show 0 < (s.gpr .rcx).toNat by omega_using [hk]),
    List.getElem?_range (show 0 < (a.gpr .rcx).toNat by omega_using [hk'])] using this

end SSib

/-! ## The public values -/

/-- The modulus' first byte. -/
def sn0v (s : State) : Nat := (s.mem (s.gpr .rdx)).toNat

/-- `lo`. -/
def slo (s : State) : Nat := loV (sn0v s)

/-- `emLen`. -/
def seml (s : State) : Nat := (s.gpr .rcx).toNat - slo s

/-- `dbLen`. -/
def sdb (D : Nat) (s : State) : Nat := seml s - D - 1

/-- The salt's length. -/
def ssl (s : State) : Nat := (stackArg s 13).toNat

/-- The blocks of the hash of `M'`. -/
def snb (H : Hash) (s : State) : Nat := (8 + H.D + ssl s + H.P.L) / H.P.B + 1

/-- The public words of the frame, by index. -/
def sw (H : Hash) (s : State) (k : Nat) : BitVec 64 :=
  match k with
  | 2 => stackArg s 16
  | 3 => stackArg s 17
  | 47 => idxWord s
  | 16 => s.gpr .rdi
  | 17 => s.gpr .rcx
  | 18 => s.gpr .rdx
  | 19 => s.gpr .r8
  | 20 => s.gpr .r9
  | 21 => stackArg s 14
  | 22 => stackArg s 15
  | 23 => off (stackArg s 14) (oEm + slo s)
  | 24 => BitVec.ofNat 64 (sdb H.D s)
  | 25 => maskV (sn0v s)
  | 26 => BitVec.ofNat 64 (slo s)
  | 27 => BitVec.ofNat 64 (8 + H.D + ssl s)
  | 28 => BitVec.ofNat 64 (snb H s)
  | 37 => stackArg s 10
  | 39 => stackArg s 12
  | 40 => stackArg s 13
  | _ => 0

/-- The public words `ks`. -/
def spw (H : Hash) (s : State) (ks : List Nat) : List (Nat × BitVec 64) := ks.map fun k => (k, sw H s k)

namespace SSib

variable {a s : State} (h : SSib tsH tsG Xs a s)
include h

theorem sn0v : sn0v s = sn0v a := by simp only [VG.Proof.RsaPss.X86_64.sn0v, h.n0]
theorem slo : slo s = slo a := by simp only [VG.Proof.RsaPss.X86_64.slo, h.sn0v]
theorem seml : seml s = seml a := by
  simp only [VG.Proof.RsaPss.X86_64.seml, h.slo, h.gpr (r := .rcx) (by decide)]
theorem sdb {D : Nat} : sdb D s = sdb D a := by simp only [VG.Proof.RsaPss.X86_64.sdb, h.seml]
theorem ssl : ssl s = ssl a := by simp only [VG.Proof.RsaPss.X86_64.ssl, h.arg (i := 13) (by decide)]
theorem snb {H : Hash} : snb H s = snb H a := by simp only [VG.Proof.RsaPss.X86_64.snb, h.ssl]

theorem sw {H : Hash} (k : Nat) : sw H s k = sw H a k := by
  unfold VG.Proof.RsaPss.X86_64.sw
  split <;> simp only [h.gpr (r := .rdi) (by decide),
    h.gpr (r := .rdx) (by decide), h.gpr (r := .rcx) (by decide), h.gpr (r := .r8) (by decide),
    h.gpr (r := .r9) (by decide), h.arg (i := 10) (by decide), h.arg (i := 12) (by decide),
    h.arg (i := 13) (by decide), h.arg (i := 14) (by decide), h.arg (i := 15) (by decide), h.slo, h.sdb, h.sn0v,
    h.snb, h.ssl, h.arg (i := 16) (by decide), h.arg (i := 17) (by decide), h.idxw]

/-- The frame, `out` and the working space are apart. -/
theorem rest : RestOk 2 (VG.Proof.RsaPss.X86_64.fb a) a.wr := by
  have hp := h.pa
  refine ⟨by rw [hp.hwr]; rfl, ?_, ?_⟩
  · rw [hp.hwr]
    refine List.Pairwise.cons ?_ (List.pairwise_pair.mpr hp.dOs)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dKo.sub_left (frame_sub a)
    · exact hp.dKs.sub_left (frame_sub a)
  · rw [hp.hwr]; intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have := hp.wO; have := hp.wS
    rcases hr with rfl | rfl <;> dsimp only <;> omega_arith

end SSib

/-! ## A run's state between pieces -/

/-- A run, with entry state `s`, between two pieces. -/
structure SS (H : Hash) (s t : State) (ks : List Nat) (rs : List (Reg × BitVec 64))
    (X : (Nat → Byte) → (Nat → BitVec 64) → Prop) : Prop where
  L : Lay t (fb s) (stackArg s 14)
  wr : t.wr = frR s :: s.wr
  W : ∃ V W, Rep t.mem (fb s) (stackArg s 14) V W ∧ (∀ k ∈ ks, W k = sw H s k) ∧ X V W
  regs : ∀ p ∈ rs, t.gpr p.1 = p.2
  sy : t.syms = s.syms

variable {H : Hash}

theorem ss_pub {a s t : State} (S : SSib tsH tsG Xs a s) {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SS H s t ks rs X) :
    Pub (fb a) (stackArg a 14) a.wr (spw H a ks) rs X t := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  refine ⟨?_, ?_, ⟨V, W, ?_, fun p hp => ?_, hx⟩, h.regs⟩
  · rw [← S.fb, ← S.arg (i := 14) (by decide)]; exact h.L
  · rw [h.wr, S.frR, S.wr]
  · rw [← S.fb, ← S.arg (i := 14) (by decide)]; exact R
  · simp only [spw, List.mem_map] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    rw [hw k hk, S.sw]

/-- A piece the analysis checks from `pT 2 ks rgs`. -/
theorem stwo {Φ : State → State → Prop} {c : Prog isa} (ks : List Nat) (rgs : List Reg)
    (rs : State → List (Reg × BitVec 64))
    (hΦ : ∀ a t, Φ a t → ∃ s X, SSib tsH tsG Xs a s ∧ SS H s t ks (rs a) X) (hr : ∀ a, (rs a).map Prod.fst = rgs)
    (hks : ∀ k ∈ ks, k < nW) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (pT 2 ks rgs) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  two_pub 2 ks rgs fb (fun a => stackArg a 14) State.wr (fun a => spw H a ks) rs
    (fun a t h => let ⟨_, X, S, v⟩ := hΦ a t h; ⟨X, ss_pub S v⟩) (fun a t h => let ⟨_, _, S, _⟩ := hΦ a t h; S.rest)
    (fun a => by simp [spw, Function.comp_def]) hr hks h

theorem SS.keep {s t t' : State} {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SS H s t ks rs X) {rs' : List Reg} (k : Keep rs' t t')
    (hm : t'.mem = t.mem) (hsp : Reg.rsp ∉ rs') (hrs : ∀ p ∈ rs, p.1 ∉ rs') (hs : t'.syms = t.syms) :
    SS H s t' ks rs X :=
  ⟨h.L.congr (k.gpr hsp) k.2.2 (by rw [hm]), k.2.2.trans h.wr, by rw [hm]; exact h.W,
    fun p hp => (k.gpr (hrs p hp)).trans (h.regs p hp), hs.trans h.sy⟩

theorem SS.next {s t t' : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SS H s t ks rs X) (L' : Lay t' (fb s) (stackArg s 14))
    (hwr : t'.wr = t.wr) {V' : Nat → Byte} {W' : Nat → BitVec 64} (R' : Rep t'.mem (fb s) (stackArg s 14) V' W')
    (hw : ∀ k ∈ ks', W' k = sw H s k) (hx : X' V' W') (hs : t'.syms = t.syms) : SS H s t' ks' [] X' :=
  ⟨L', hwr.trans h.wr, ⟨V', W', R', hw, hx⟩, (fun _ hp => by cases hp), hs.trans h.sy⟩

theorem SS.sub {s t : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SS H s t ks rs X) (hks : ∀ k ∈ ks', k ∈ ks)
    (rs' : List (Reg × BitVec 64)) (hrs : ∀ p ∈ rs', t.gpr p.1 = p.2) (hX : ∀ V W, X V W → X' V W) :
    SS H s t ks' rs' X' := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  exact ⟨h.L, h.wr, ⟨V, W, R, fun k hk => hw k (hks k hk), hX V W hx⟩, hrs, h.sy⟩

end VG.Proof.RsaPss.X86_64

end

end


/-!
# RSASSA-PSS signing on x86-64, around the encoding: constant time, and
`Verified`

The prologue and the check of the modulus' first byte (`spro_ct`), the
index of the table `hash`'s hash function (public: the tables are), `emBits`
and `encode`'s arguments (public: the modulus' length and first byte, and
places), the choice of `encode` by that index and its call (constant time by
its contract: its public data, the places and lengths and the tables' words,
agree), whose result is public (whether the salt fits, `encode_isSome₂`), the
private-key operation's arguments and call (`scall_ct`), and the epilogue,
in two runs whose entry states agree on the public data (`signC_ct`). With
`signC_correct`, `signC` meets the contract (`signC_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (chkContract)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable {tsH tsG : List FnTable} {Xs : State → State → Prop} {H : Hash}

/-! ## The public values -/

/-- `emBits`. -/
def seb (s : State) : Nat := ebV (s.gpr .rcx).toNat (sn0v s)

/-- `emLen`. -/
def sel (s : State) : Nat := Spec.RsaPss.emLength (seb s)

/-- `lo`. -/
def sclo (s : State) : Nat := (s.gpr .rcx).toNat - sel s

/-- Whether the encoding fits, for a digest of `digest_len` bytes. -/
def sfits (s : State) : Prop := (stackArg s 11).toNat + ssl s + 2 ≤ sel s

instance (s : State) : Decidable (sfits s) := inferInstanceAs (Decidable (_ ≤ _))

/-- The index of the table `hash`'s hash function. -/
def sidx (a : State) : Nat := (idxWord a).toNat

theorem SSib.seb {a s : State} (S : SSib tsH tsG Xs a s) : seb s = seb a := by
  simp only [VG.Proof.RsaPss.X86_64.seb, S.sn0v, S.gpr (r := .rcx) (by decide)]

theorem SSib.sel {a s : State} (S : SSib tsH tsG Xs a s) : sel s = sel a := by
  simp only [VG.Proof.RsaPss.X86_64.sel, S.seb]

theorem SSib.sclo {a s : State} (S : SSib tsH tsG Xs a s) : sclo s = sclo a := by
  simp only [VG.Proof.RsaPss.X86_64.sclo, S.sel, S.gpr (r := .rcx) (by decide)]

theorem SSib.sfits {a s : State} (S : SSib tsH tsG Xs a s) : sfits s ↔ sfits a := by
  simp only [VG.Proof.RsaPss.X86_64.sfits, S.sel, S.ssl, S.arg (i := 11) (by decide)]

theorem seb_ok {s : State} (hp : SPre tsH tsG s) :
    sclo s ≤ 1 ∧ 1 ≤ seb s ∧ seb s ≤ Proof.RsaPss.maxEmBits ∧ sel s ≤ 1024 := by
  obtain hk1 := hp.k1; have hk2 := hp.k2
  obtain hl8 : Nat.log2 (sn0v s) < 8 := RsaPss.log2_lt8 (s.mem (s.gpr .rdx))
  refine ⟨lo_le hl8 (by omega_arith), ?_, ?_, ?_⟩
  · unfold seb ebV; omega_arith
  · unfold seb ebV Proof.RsaPss.maxEmBits; omega_arith
  · unfold sel seb ebV Spec.RsaPss.emLength; omega_arith

/-- `encode`'s result, from whether it fits. -/
theorem rax_of {e : Option (List Byte)} {x : BitVec 64} {c : Bool} {P : List Byte → Prop}
    (h : match e with | some e' => x.setWidth 32 = 1 ∧ P e' | none => x.setWidth 32 = 0) (hc : e.isSome = c) :
    x.setWidth 32 = if c then 1 else 0 := by
  cases e with
  | none => subst hc; exact h
  | some e' => subst hc; exact h.1

variable (f : MdFns) (g : Impl.Mgf1.X86_64.Table.Fns) in
/-- What the tables give the runs whose entry states agree with `a`: the
functions `T` and hash functions `Hs`, `Gs`, the same for every run, that
`encode` for the index of `a`'s table computes with, in constant time. -/
structure SGood (a : State) (T : Tabs) (Hs Gs : Spec.Mgf1.Hash) : Prop where
  sel : ∀ s, (signK tsH tsG).pub a s → SPre tsH tsG s → ESel f g s (sidx a) T Hs Gs
  words : ∀ s, (signK tsH tsG).pub a s → SPre tsH tsG s →
    tabWords s.mem (stackArg s 16) (stackArg s 17) = tabWords a.mem (stackArg a 16) (stackArg a 17)
  ct : ConstantTime isa (encK T Hs Gs).pre (encK T Hs Gs).pub (encode f (ofIdx (sidx a)) g)

/-! ## The pieces -/

/-- After the frame's push. -/
def J0 (s t : State) : Prop := t = allocState frameBytes s

/-- The words the prologue stores. -/
def KS1 : List Nat := [16, 17, 18, 19, 20, 21, 22, 37, 39, 40]

/-- After the prologue: the modulus' first byte, ZF set if it is zero, and
the table `hash` in `r11`. -/
def SJ1 (H : Hash) (s t : State) : Prop :=
  SS H s t KS1 [(.r11, stackArg s 16)] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (sn0v s) ∧ t.zf = some (decide (sn0v s = 0))

/-- And the index in its slot. -/
def SJ2 (H : Hash) (s t : State) : Prop :=
  SS H s t (KS1 ++ [47]) [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (sn0v s) ∧ t.zf = some (decide (sn0v s = 0))

/-- At the end. -/
def SJR (H : Hash) (s t : State) : Prop := SS H s t [] [] fun _ _ => True

theorem spro_ct : RelCT isa (Two (SAt tsH tsG Xs J0)) (.block (signPrologue ++ n0 ++ ([.mov .r11 (.mem (arg 16))] : List Instr)))
    (Two (SAt tsH tsG Xs (SJ1 H))) := by
  obtain ⟨_, hc⟩ := scFixed.pro
  obtain ar : ∀ (s : State) {r : Reg}, r ≠ .rsp → (allocState frameBytes s).gpr r = s.gpr r := fun s r hr => by
    rw [allocState_gpr']; exact ifn hr _ _
  refine two_post (two_pub0 2 [.rdi, .rsi, .rdx, .rcx, .r8, .r9] fb State.wr
    (fun a => [(.rdi, a.gpr .rdi), (.rsi, a.gpr .rsi), (.rdx, a.gpr .rdx), (.rcx, a.gpr .rcx), (.r8, a.gpr .r8),
      (.r9, a.gpr .r9)])
    (fun a t ⟨s, S, ht⟩ => ⟨by rw [ht, allocState_gpr', ifp rfl, ← S.fb], by rw [ht, ← S.wr, ← S.fb]; rfl,
      fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> rw [ht, ar s (by decide)] <;>
          exact S.gpr (by decide)⟩)
    (fun a t ⟨s, S, _⟩ => S.rest) (fun _ => rfl) hc) fun a t ⟨s, S, ht⟩ => ?_
  subst ht
  have hp := S.ps
  rw [WP.block_append_iff, WP.block_append_iff]
  refine X86_64.WP.mono_syms (signPro_ok hp) fun t1 ⟨k1, L1, R1, f1⟩ sy1 => ?_
  refine X86_64.WP.mono_syms (n0_ok hp L1 R1 (by simp [proW, upd]) k1.2.1 (frame_wrR f1))
    fun t2 ⟨k2, hm2, hax2, hz2⟩ sy2 => ?_
  obtain hM2 : Frame (wrR s) s.mem t2.mem := hm2 ▸ frame_wrR f1
  obtain L2 : Lay t2 (fb s) (stackArg s 14) := L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2])
  refine X86_64.WP.mono_syms (r11Arg_ok hp L2.rsp (k2.2.1.trans k1.2.1) (argsKept_of hp hM2))
    fun t3 ⟨k3, hm3, h11, hz3⟩ sy3 =>
    ⟨s, S, ⟨⟨L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3]), k3.2.2.trans (k2.2.2.trans k1.2.2),
      ⟨_, _, hm3 ▸ hm2 ▸ R1, fun k hk => ?_, trivial⟩, fun p hp => by rw [List.mem_singleton.mp hp]; exact h11,
      sy3.trans (sy2.trans sy1)⟩, k3.2.1.trans (k2.2.1.trans k1.2.1), hm3 ▸ hM2,
      (k3.gpr (by decide)).trans hax2, hz3.trans hz2⟩⟩
  simp only [KS1, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [proW, upd, sw]

theorem sidx_ct : RelCT isa (Two (SAt tsH tsG Xs (SJ1 H))) (.block idxSlot) (Two (SAt tsH tsG Xs (SJ2 H))) := by
  obtain ⟨_, hc⟩ := scFixed.idx
  refine two_post (stwo (H := H) [] [.r11] (fun a => [(.r11, stackArg a 16)])
    (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (fun _ hk => by cases hk) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.arg (i := 16) (by decide)]; exact h.1.regs _ (List.mem_singleton_self _))
      fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hax, hz⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  refine X86_64.WP.mono_syms (idxSlot_ok S.ps v.L R hrd hM (v.regs _ (List.mem_singleton_self _)))
    fun u ⟨L', k', R', hz', hM'⟩ sy => ⟨s, S, ⟨v.next L' k'.2.2 R' (fun k hk => ?_) trivial sy, k'.2.1.trans hrd, hM',
      (k'.gpr (by decide)).trans hax, hz'.trans hz⟩⟩
  rcases List.mem_append.mp hk with hk | hk
  · have : k ≠ 47 := by simp only [KS1, List.mem_cons, List.not_mem_nil, or_false] at hk; omega_arith
    simp only [upd]; rw [ifn this]; exact hw k hk
  · rw [List.mem_singleton.mp hk]; simp [upd, sw, idxWord]

/-- A refusal: zeros to `out`. -/
theorem sfail_ct {Φ : State → State → Prop}
    (hΦ : ∀ a t, Φ a t → ∃ s X, SSib tsH tsG Xs a s ∧ SS H s t [16, 17] [] X) :
    RelCT isa (Two Φ) signFail (Two (SAt tsH tsG Xs (SJR H))) := by
  obtain ⟨_, hc⟩ := sFixed.fail
  refine two_post (stwo (H := H) [16, 17] [] (fun _ => []) hΦ (fun _ => rfl) (by decide) hc)
    fun a t h => ?_
  obtain ⟨s, X, S, v⟩ := hΦ a t h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  obtain hk1 := hp.k1; have hk2 := hp.k2
  obtain hout : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region) ∈ t.wr := by
    rw [v.wr, hp.hwr, ← hp.hsi]; simp
  obtain hO : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint (stkR s) := by rw [← hp.hsi]; exact hp.dKo.symm
  exact X86_64.WP.mono_syms (signFail_ok v.L R (out := s.gpr .rdi) (k := (s.gpr .rcx).toNat) (hw 16 (by decide))
    (by rw [hw 17 (by decide)]; show s.gpr .rcx = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega_arith) hk2
    hout (by rw [← hp.hsi]; exact hp.wO)
    ((by rw [← hp.hsi]; exact hp.dOs : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint
      ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩).sub_right (Region.sub_prefix (by have := hp.hsl; unfold oRsa; omega_arith)))
    (hO.sub_right (frame_sub s))) fun u ⟨L', k', R', _⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' (fun _ h => by cases h) trivial sy⟩

/-- Before the call. -/
def SJP (H : Hash) (s t : State) : Prop :=
  SS H s t [] [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    (∀ i < 14, word t.mem (fb s) (8 * i) = pArg s i) ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rcx ∧
    t.gpr .rdx = s.gpr .rdx ∧ t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9

/-- The words the private-key operation's arguments read. -/
def KSP : List Nat := [16, 17, 18, 19, 20, 22]

/-- Before `encode`. -/
def CJE (H : Hash) (s t : State) : Prop :=
  SS H s t KSP [] (fun _ W => W 0 = off (stackArg s 14) oEnc ∧ W 1 = stackArg s 15 - BitVec.ofNat 64 (oEnc / 8) ∧
      W 2 = stackArg s 16 ∧ W 3 = stackArg s 17) ∧
    t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧ sn0v s ≠ 0 ∧
    t.gpr .rdi = off (stackArg s 14) (oEm + sclo s) ∧ t.gpr .rsi = BitVec.ofNat 64 (sel s) ∧
    t.gpr .rdx = stackArg s 10 ∧ t.gpr .rcx = stackArg s 12 ∧ t.gpr .r8 = stackArg s 13 ∧
    t.gpr .r9 = BitVec.ofNat 64 (seb s) ∧ t.gpr .r11 = idxWord s

/-- After `encode`. -/
def CJC (H : Hash) (s t : State) : Prop :=
  SS H s t KSP [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    (t.gpr .rax).setWidth 32 = if decide (sfits s) then 1 else 0

/-- After the test. -/
def CJT (H : Hash) (s t : State) : Prop :=
  SS H s t KSP [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    t.zf = some (!decide (sfits s))

theorem cprep_ct :
    RelCT isa (Two fun a t => SAt tsH tsG Xs (SJ2 H) a t ∧ isa.eval .e t = some false)
      (.block (emBitsB ++ encArgs ++ idxLoad)) (Two (SAt tsH tsG Xs (CJE H))) := by
  obtain ⟨_, hc⟩ := scFixed.prep
  refine two_post (stwo (H := H) [17, 21, 22, 37, 39, 40, 47] [.rax] (fun a => [(.rax, BitVec.ofNat 64 (sn0v a))])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.sn0v]; exact h.2.2.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, he⟩ => ?_
  obtain ⟨v, hrd, hM, hax, hz⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  obtain hk1 := hp.k1; have hk2 := hp.k2
  obtain h0 : sn0v s ≠ 0 := fun h0 => by
    have : isa.eval .e t = some true := by rw [show isa.eval .e t = t.zf from rfl, hz, h0]; rfl
    rw [this] at he; cases he
  obtain eA : emBitsB ++ encArgs ++ idxLoad = emBitsB ++ (encA1 ++ encA2 ++ encA3) ++ (encA4 ++ idxLoad) := by
    simp only [encArgs_eq, List.append_assoc]
  rw [eA, WP.block_append_iff]
  refine X86_64.WP.mono_syms (WP.keepIn (by decide) (by exact Nat.zero_le 16)
    (encPrep_ok v.L R (hw 17 (by decide)) (hw 22 (by decide)) (hw 37 (by decide)) (hw 39 (by decide))
      (hw 40 (by decide)) (by omega_arith) hk2 (x := sn0v s) (BitVec.isLt _) h0 hax))
    fun u ⟨⟨L', k', R', di, si, dx, cx, r8, r9⟩, f⟩ sy => ?_
  obtain hM' := frame_keep hp v.wr v.L.rsp hM f
  rw [WP.block_append_iff]
  refine X86_64.WP.mono_syms (WP.keepIn (by decide) (by exact Nat.zero_le 16)
    (encA4_ok hp L' R' (k'.2.1.trans hrd) (argsKept_of hp hM'))) fun u2 ⟨⟨L2, k2, R2⟩, f2⟩ sy2 => ?_
  obtain hM2 := frame_keep hp (k'.2.2.trans v.wr) L'.rsp hM' f2
  refine X86_64.WP.mono_syms (idxLoad_ok L2 R2) fun u3 ⟨k3, hm3, h113⟩ sy3 => ?_
  obtain L3 : Lay u3 (fb s) (stackArg s 14) := L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3])
  obtain g : ∀ r, r ∉ [Reg.rax, .r11] → u3.gpr r = u.gpr r := fun r hr => by
    rw [k3.gpr (fun h => hr (by simp at h ⊢; exact .inr h)), k2.gpr (fun h => hr (by simp at h ⊢; exact .inl h))]
  refine ⟨s, S, ⟨v.next L3 (k3.2.2.trans (k2.2.2.trans k'.2.2)) (hm3 ▸ R2) (fun k hk => ?_)
      ⟨by simp [upd], by simp [upd], by simp [upd], by simp [upd]⟩ (sy3.trans (sy2.trans sy)),
    k3.2.1.trans (k2.2.1.trans (k'.2.1.trans hrd)), hm3 ▸ hM2, h0, (g _ (by decide)).trans di,
    (g _ (by decide)).trans si, (g _ (by decide)).trans dx, (g _ (by decide)).trans cx, (g _ (by decide)).trans r8,
    (g _ (by decide)).trans r9, ?_⟩⟩
  · simp only [KSP, List.mem_cons, List.not_mem_nil, or_false] at hk
    obtain hk' : k ∈ KS1 ++ [47] := by simp only [KS1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; omega_arith
    simp only [upd]
    rw [ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith),
      ifn (by omega_arith), ifn (by omega_arith)]
    exact hw k hk'
  · rw [h113]; simp only [upd]
    rw [ifn (by decide), ifn (by decide), ifn (by decide), ifn (by decide), ifn (by decide), ifn (by decide),
      ifn (by decide)]
    exact hw 47 (by decide)

/-- `encode`'s arguments, from the state before the call. -/
theorem encAt_of {f : MdFns} {g : Impl.Mgf1.X86_64.Table.Fns} {s t : State} (hp : SPre tsH tsG s) (h : CJE H s t)
    {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash} (E : ESel f g s i T Hs Gs) : EncAt T s t (sclo s) (seb s) (sel s) := by
  obtain ⟨v, hrd, hM, -, di, si, dx, cx, r8, r9, -⟩ := h
  obtain ⟨V, W, R, -, x0, x1, x2, x3⟩ := v.W
  obtain ⟨lo, e1, e2, -⟩ := seb_ok hp
  exact ⟨v.L.rsp, hrd, v.wr, hM, v.sy, (R.fr 0 (by decide)).trans x0, (R.fr 1 (by decide)).trans x1,
    (R.fr 2 (by decide)).trans x2, (R.fr 3 (by decide)).trans x3, di, si, dx, cx, r8, r9, lo, e1, e2, rfl, E.hD, E.tabs⟩

/-- The tables' words, at the call, as on entry. -/
theorem tabWords_call {s t : State} (hp : SPre tsH tsG s) (hM : Frame (wrR s) s.mem t.mem) (hsp : t.gpr .rsp = fb s) :
    tabWords t.callEntry.mem (stackArg s 16) (stackArg s 17) = tabWords s.mem (stackArg s 16) (stackArg s 17) := by
  obtain fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, hsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  obtain fSE : Frame (wrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret8_sub s⟩)
  simp only [tabWords, tab_read hp fSE (.inl rfl) (by decide : 0 + 8 ≤ 56), tab_read hp fSE (.inl rfl) (by decide : 24 + 8 ≤ 56),
    tab_read hp fSE (.inl rfl) (by decide : 32 + 8 ≤ 56), tab_read hp fSE (.inr rfl) (by decide : 0 + 8 ≤ 56),
    tab_read hp fSE (.inr rfl) (by decide : 8 + 8 ≤ 56), tab_read hp fSE (.inr rfl) (by decide : 16 + 8 ≤ 56),
    tab_read hp fSE (.inr rfl) (by decide : 48 + 8 ≤ 56)]

variable {f : MdFns} {g : Impl.Mgf1.X86_64.Table.Fns}
  (hsel : ∀ a, SPre tsH tsG a → ∃ T Hs Gs, SGood (tsH := tsH) (tsG := tsG) f g a T Hs Gs)
  (hspE : ∀ i ∈ idxs, SpSafe (encode f (ofIdx i) g))
  (hdE : ∀ i ∈ idxs, (encode f (ofIdx i) g).x86_64Depth ≤ encStack)

include hsel hspE hdE in
/-- The call of `encode` for the index `j`. -/
theorem ecall_ct {j : Nat} (hj : j ∈ idxs) :
    RelCT isa (Two fun a t => SAt tsH tsG Xs (CJE H) a t ∧ sidx a = j) (.call (encName j) (encode f (ofIdx j) g))
      (Two (SAt tsH tsG Xs (CJC H))) := by
  obtain g' : ∀ (t : State) (rd wr : List Region) {r : Reg}, r ≠ .rsp →
      (t.callEntry.withRegions rd wr).gpr r = t.gpr r :=
    fun t rd wr r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  refine two_post ?_ fun a t ⟨⟨s, S, h⟩, hja⟩ => ?_
  · refine (RelCT.exists_ (P := fun (x : Tabs × Spec.Mgf1.Hash × Spec.Mgf1.Hash) t₁ t₂ => ∃ a,
        (SAt tsH tsG Xs (CJE H) a t₁ ∧ sidx a = j) ∧ (SAt tsH tsG Xs (CJE H) a t₂ ∧ sidx a = j) ∧
        SGood (tsH := tsH) (tsG := tsG) f g a x.1 x.2.1 x.2.2 ∧ SPre tsH tsG a) fun x => ?_).mono
      (fun t₁ t₂ ⟨a, h₁, h₂⟩ => by
        have hpa : SPre tsH tsG a := h₁.1.choose_spec.1.1
        obtain ⟨T, Hs, Gs, G⟩ := hsel a hpa
        exact ⟨(T, Hs, Gs), a, h₁, h₂, G, hpa⟩) fun _ _ h => h
    by_cases hx : ∃ a, sidx a = j ∧ SGood (tsH := tsH) (tsG := tsG) f g a x.1 x.2.1 x.2.2 ∧ SPre tsH tsG a
    · obtain ⟨a₀, hj₀, G₀, hpa₀⟩ := hx
      obtain E₀ := G₀.sel a₀ (spub_refl tsH tsG a₀) hpa₀
      rw [hj₀] at E₀
      have hct := G₀.ct
      rw [hj₀] at hct
      refine RelCT.callEx (k := encK x.1 x.2.1 x.2.2) E₀.ok hct
        fun t₁ t₂ ⟨a, ⟨⟨s₁, S₁, h₁⟩, hj₁⟩, ⟨⟨s₂, S₂, h₂⟩, _⟩, G, hpa⟩ => ?_
      obtain p₁ := S₁.ps; have p₂ := S₂.ps
      obtain E₁ := G.sel s₁ S₁.2.1 S₁.2.2.1
      obtain E₂ := G.sel s₂ S₂.2.1 S₂.2.2.1
      obtain A₁ := encAt_of p₁ h₁ E₁
      obtain A₂ := encAt_of p₂ h₂ E₂
      obtain ⟨lo₁, -, -, l₁⟩ := seb_ok p₁
      obtain ⟨lo₂, -, -, l₂⟩ := seb_ok p₂
      obtain ⟨c₁, w₁⟩ := enc_covers (T := x.1) p₁ A₁.rd A₁.wr lo₁ l₁ A₁.hD
      obtain ⟨c₂, w₂⟩ := enc_covers (T := x.1) p₂ A₂.rd A₂.wr lo₂ l₂ A₂.hD
      refine ⟨_, _, _, _, enc_pre (Hs := x.2.1) (Gs := x.2.2) p₁ A₁, enc_pre (Hs := x.2.1) (Gs := x.2.2) p₂ A₂,
        ⟨fun r hr => ?_, ?_, ?_⟩, c₁, w₁, c₂, w₂, by rw [A₁.sp, A₂.sp, S₁.fb, S₂.fb]⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [g' _ _ _ (by decide), g' _ _ _ (by decide), A₁.di, A₂.di, S₁.arg (i := 14) (by decide),
            S₂.arg (i := 14) (by decide), S₁.sclo, S₂.sclo]
        · rw [g' _ _ _ (by decide), g' _ _ _ (by decide), A₁.si, A₂.si, S₁.sel, S₂.sel]
        · rw [g' _ _ _ (by decide), g' _ _ _ (by decide), A₁.dx, A₂.dx, S₁.arg (i := 10) (by decide),
            S₂.arg (i := 10) (by decide)]
        · rw [g' _ _ _ (by decide), g' _ _ _ (by decide), A₁.cx, A₂.cx, S₁.arg (i := 12) (by decide),
            S₂.arg (i := 12) (by decide)]
        · rw [g' _ _ _ (by decide), g' _ _ _ (by decide), A₁.r8, A₂.r8, S₁.arg (i := 13) (by decide),
            S₂.arg (i := 13) (by decide)]
        · rw [g' _ _ _ (by decide), g' _ _ _ (by decide), A₁.r9, A₂.r9, S₁.seb, S₂.seb]
        · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, A₁.sp,
            A₂.sp, S₁.fb, S₂.fb]
      · rw [stackArgs_four, stackArgs_four, stackArg_call p₁ A₁.sp _ _ (i := 0) (by decide),
          stackArg_call p₂ A₂.sp _ _ (i := 0) (by decide), stackArg_call p₁ A₁.sp _ _ (i := 1) (by decide),
          stackArg_call p₂ A₂.sp _ _ (i := 1) (by decide), stackArg_call p₁ A₁.sp _ _ (i := 2) (by decide),
          stackArg_call p₂ A₂.sp _ _ (i := 2) (by decide), stackArg_call p₁ A₁.sp _ _ (i := 3) (by decide),
          stackArg_call p₂ A₂.sp _ _ (i := 3) (by decide), A₁.w0, A₂.w0, A₁.w1, A₂.w1, A₁.w2, A₂.w2, A₁.w3, A₂.w3,
          S₁.arg (i := 14) (by decide), S₂.arg (i := 14) (by decide), S₁.arg (i := 15) (by decide),
          S₂.arg (i := 15) (by decide), S₁.arg (i := 16) (by decide), S₂.arg (i := 16) (by decide),
          S₁.arg (i := 17) (by decide), S₂.arg (i := 17) (by decide)]
      · rw [stackArg_call p₁ A₁.sp _ _ (i := 2) (by decide), stackArg_call p₂ A₂.sp _ _ (i := 2) (by decide),
          stackArg_call p₁ A₁.sp _ _ (i := 3) (by decide), stackArg_call p₂ A₂.sp _ _ (i := 3) (by decide),
          A₁.w2, A₂.w2, A₁.w3, A₂.w3, State.withRegions_mem, State.withRegions_mem, tabWords_call p₁ A₁.M A₁.sp,
          tabWords_call p₂ A₂.M A₂.sp, G.words s₁ S₁.2.1 S₁.2.2.1, G.words s₂ S₂.2.1 S₂.2.2.1]
    · exact RelCT.of_false fun _ _ ⟨a, ⟨_, hj₁⟩, _, G, hpa⟩ => hx ⟨a, hj₁, G, hpa⟩
  · obtain ⟨T, Hs, Gs, G⟩ := hsel a S.1
    have hp := S.ps
    obtain E := G.sel s S.2.1 S.2.2.1
    rw [hja] at E
    obtain A := encAt_of hp h E
    obtain ⟨v, hrd, hM, -⟩ := h
    obtain ⟨V, W, R, hw, -⟩ := v.W
    refine WP.mono (enc_call E.ok (hspE j hj) (hdE j hj) hp A R)
      fun u ⟨rd', wr', cs', _, hM', sy', R', hE⟩ => ⟨s, S, v.next (v.L.of_rep' R R' rfl (cs' .rsp (by decide)) wr') wr'
        R' hw trivial (sy'.trans v.sy.symm), rd'.trans hrd, hM', rax_of hE ?_⟩
    rw [RsaPss.encode_isSome₂ Hs Gs (by rw [Bignum.bytesAt_length]; exact E.hD.trans (hp.hdl Hs E.hH)),
      Bignum.bytesAt_length, ← hp.hdl Hs E.hH]
    rfl

include hsel hspE hdE in
/-- The choice of `encode` by the table's index, and its call. -/
theorem echoose_ct : RelCT isa (Two (SAt tsH tsG Xs (CJE H)))
    (byIdx (fun i => .call (encName i) (encode f (ofIdx i) g)) idxs) (Two (SAt tsH tsG Xs (CJC H))) := by
  refine byIdx_ct sidx (fun a t t' ⟨s, S, h⟩ k hm sy => ?_) (fun a t ⟨s, S, h⟩ => ?_) cmpOk_idxs
    (fun j hj => ?_) (fun j hj => ecall_ct hsel hspE hdE hj)
  · obtain ⟨v, hrd, hM, h0, di, si, dx, cx, r8, r9, r11⟩ := h
    obtain gk : ∀ r, t'.gpr r = t.gpr r := fun r => k.gpr (List.not_mem_nil)
    exact ⟨s, S, v.keep k hm (by simp) (fun _ hp => by cases hp) sy, k.2.1.trans hrd, hm ▸ hM, h0,
      (gk _).trans di, (gk _).trans si, (gk _).trans dx, (gk _).trans cx, (gk _).trans r8, (gk _).trans r9,
      (gk _).trans r11⟩
  · obtain ⟨T, Hs, Gs, G⟩ := hsel a S.1
    refine ⟨(G.sel a (spub_refl tsH tsG a) S.1).mem, ?_⟩
    rw [h.2.2.2.2.2.2.2.2.2.2, S.idxw, sidx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · obtain ⟨_, hc⟩ := scFixed.cmp j hj
    exact stwo (H := H) [] [.r11] (fun a => [(.r11, idxWord a)])
      (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (fun _ hk => by cases hk) _ (fun p hp => by
        rw [List.mem_singleton.mp hp, ← S.idxw]; exact h.2.2.2.2.2.2.2.2.2.2) fun _ _ x => x⟩)
      (fun _ => rfl) (by decide) hc

theorem ctest_ct : RelCT isa (Two (SAt tsH tsG Xs (CJC H))) (.block [.alu32 .test .rax (.reg .rax)])
    (Two (SAt tsH tsG Xs (CJT H))) := by
  obtain ⟨_, hc⟩ := scFixed.test
  refine two_post (stwo (H := H) [] [] (fun _ => [])
    (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hax⟩ := h
  refine X86_64.WP.mono_syms (test32_ok t) fun u ⟨k, hm, hz⟩ sy =>
    ⟨s, S, v.keep k hm (by decide) (fun _ hp => by cases hp) sy, k.2.1.trans hrd, hm ▸ hM, ?_⟩
  rw [hz, hax]
  by_cases hf : sfits s <;> simp [hf]

/-- An input, at the call, as on entry. -/
theorem sentry_bytes {s t : State} (hst : t.gpr .rsp = fb s) (hM : Frame (wrR s) s.mem t.mem)
    {R : Region} (hK : (stkR s).Disjoint R) (hO : (outR s).Disjoint R) (hS : R.Disjoint (scrR s))
    (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.callEntry.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  obtain fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, hst]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  obtain fSE : Frame (wrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret8_sub s⟩)
  exact bytesAt_frame fSE (in_apart hK hO hS) hl

theorem pArg_sib {a s : State} (S : SSib tsH tsG Xs a s) {i : Nat} (hi : i < 14) : pArg s i = pArg a i := by
  unfold pArg
  split
  · rw [S.arg (i := 14) (by decide)]
  · rw [S.gpr (r := .rcx) (by decide)]
  · rw [S.arg (i := 14) (by decide)]
  · rw [S.arg (i := 15) (by decide)]
  · exact S.arg (by omega_arith)

/-- The call's public data agree. -/
theorem scall_pub {a s₁ s₂ t₁ t₂ : State} (S₁ : SSib tsH tsG Xs a s₁) (h₁ : SJP H s₁ t₁) (S₂ : SSib tsH tsG Xs a s₂)
    (h₂ : SJP H s₂ t₂) :
    chkContract.pub (t₁.callEntry.withRegions (pRd s₁) (pWr s₁)) (t₂.callEntry.withRegions (pRd s₂) (pWr s₂)) := by
  obtain ⟨v₁, -, hM₁, ha₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩ := h₁
  obtain ⟨v₂, -, hM₂, ha₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩ := h₂
  have p₁ := S₁.ps
  have p₂ := S₂.ps
  obtain hE₁ : ∀ i < 14, stackArg (t₁.callEntry.withRegions (pRd s₁) (pWr s₁)) i = pArg a i :=
    fun i hi => ((stackArg_call p₁ v₁.L.rsp _ _ (by omega_using [hi])).trans (ha₁ i hi)).trans (pArg_sib S₁ hi)
  obtain hE₂ : ∀ i < 14, stackArg (t₂.callEntry.withRegions (pRd s₂) (pWr s₂)) i = pArg a i :=
    fun i hi => ((stackArg_call p₂ v₂.L.rsp _ _ (by omega_using [hi])).trans (ha₂ i hi)).trans (pArg_sib S₂ hi)
  obtain bn : ∀ {s t : State}, SSib tsH tsG Xs a s → t.gpr .rsp = fb s → Frame (wrR s) s.mem t.mem →
      Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
        Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := fun {s t} S hst hM => by
    have hp := S.ps
    rw [← S.nB]
    exact sentry_bytes (R := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩) hst hM hp.dKn hp.dOn hp.dns
      (by have := hp.wN; dsimp only; omega_arith)
  obtain be : ∀ {s t : State}, SSib tsH tsG Xs a s → t.gpr .rsp = fb s → Frame (wrR s) s.mem t.mem →
      Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .r8) (s.gpr .r9).toNat =
        Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := fun {s t} S hst hM => by
    have hp := S.ps
    rw [← S.eB]
    exact sentry_bytes (R := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩) hst hM hp.dKe hp.dOe hp.des
      (by have := hp.wE; dsimp only; omega_arith)
  obtain g : ∀ (t : State) (rd wr : List Region) {r : Reg}, r ≠ .rsp → (t.callEntry.withRegions rd wr).gpr r = t.gpr r :=
    fun t rd wr r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  refine ⟨fun r hr => ?_, List.map_congr_left fun i hi => ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), di₁, di₂, S₁.gpr (r := .rdi) (by decide),
        S₂.gpr (r := .rdi) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), si₁, si₂, S₁.gpr (r := .rcx) (by decide),
        S₂.gpr (r := .rcx) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), dx₁, dx₂, S₁.gpr (r := .rdx) (by decide),
        S₂.gpr (r := .rdx) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), cx₁, cx₂, S₁.gpr (r := .rcx) (by decide),
        S₂.gpr (r := .rcx) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), r8₁, r8₂, S₁.gpr (r := .r8) (by decide),
        S₂.gpr (r := .r8) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), r9₁, r9₂, S₁.gpr (r := .r9) (by decide),
        S₂.gpr (r := .r9) (by decide)]
    · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, v₁.L.rsp,
        v₂.L.rsp, S₁.fb, S₂.fb]
  · have hi := List.mem_range.mp hi
    rw [hE₁ i hi, hE₂ i hi]
  · rw [State.withRegions_mem, State.withRegions_mem, g _ _ _ (by decide), g _ _ _ (by decide),
      g _ _ _ (by decide), g _ _ _ (by decide), dx₁, dx₂, cx₁, cx₂, bn S₁ v₁.L.rsp hM₁, bn S₂ v₂.L.rsp hM₂]
  · rw [State.withRegions_mem, State.withRegions_mem, g _ _ _ (by decide), g _ _ _ (by decide),
      g _ _ _ (by decide), g _ _ _ (by decide), r8₁, r8₂, r9₁, r9₂, be S₁ v₁.L.rsp hM₁, be S₂ v₂.L.rsp hM₂]

variable {privN : String} {privC : Prog isa}
  (hv : ∀ s, chkContract.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContract.post s s')
  (hct : ConstantTime isa chkContract.pre chkContract.pub privC) (hspC : SpSafe privC)
  (hdC : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes)

theorem srestore_ct : RelCT isa (Two (SAt tsH tsG Xs (SJR H))) (.block restoreRegs) fun _ _ => True := by
  obtain ⟨_, hc⟩ := sFixed.restore
  exact stwo (H := H) [] [] (fun _ => []) (fun a t ⟨s, S, v⟩ => ⟨s, _, S, v⟩) (fun _ => rfl) (by decide) hc

include hsel hspE hdE in
/-- The body of `signC`'s frame, with the private-key operation's arguments
`args` and call constant time from the test of `encode`'s result on. -/
theorem scbodyWith_ct (H : Hash) {args : List Instr}
    (hpriv : RelCT isa (Two fun a t => SAt tsH tsG Xs (CJT H) a t ∧ isa.eval .e t = some false)
      (.seq (.block args) (.call privN privC)) (Two (SAt tsH tsG Xs (SJR H)))) :
    RelCT isa (Two (SAt tsH tsG Xs J0)) (signCBodyWith f g privN privC args) fun _ _ => True := by
  unfold signCBodyWith
  simp only [seqs]
  refine (spro_ct (H := H)).seq (sidx_ct.seq ((two_ite (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
      rw [show isa.eval .e t₁ = t₁.zf from rfl, show isa.eval .e t₂ = t₂.zf from rfl, h₁.2.2.2.2, h₂.2.2.2.2,
        S₁.sn0v, S₂.sn0v])
    (sfail_ct (Φ := fun a t => SAt tsH tsG Xs (SJ2 H) a t ∧ isa.eval .e t = some true)
      fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
    (cprep_ct.seq ((echoose_ct hsel hspE hdE).seq (ctest_ct.seq
      (two_ite (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
          rw [show isa.eval .e t₁ = t₁.zf from rfl, show isa.eval .e t₂ = t₂.zf from rfl, h₁.2.2.2,
            h₂.2.2.2, decide_eq_decide.mpr ((S₁.sfits).trans S₂.sfits.symm)])
        (sfail_ct (Φ := fun a t => SAt tsH tsG Xs (CJT H) a t ∧ isa.eval .e t = some true)
          fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
        hpriv))))).seq srestore_ct))

end VG.Proof.RsaPss.X86_64

end

end

/-! Constant-time public dispatch for PSS salt verification. -/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Chk
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {T : Tabs}

/-- Testing the public salt mode preserves the verification state. -/
theorem saltAny_ct : RelCT isa (Two (VAt T (JM T.H (X7 T.H))))
    (.block [.mov .rax (.mem (sp sAny)), .alu .test .rax (.reg .rax)])
    (Two fun a t => VAt T (JM T.H (X7 T.H)) a t ∧
      isa.eval .e t = some (decide (vw T.H a 35 = 0))) := by
  refine two_post (vtwo (T := T) (H := T.H) [35] [] (fun _ => [])
    (fun a t h => jm_vs h _) (fun _ => rfl) (by decide) (by taint_decide))
    fun a t ⟨s, S, v, hrd, hok⟩ => ?_
  obtain ⟨V, W, R, hw, _⟩ := v.W
  refine X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun u => u.mem = t.mem ∧
    u.zf = some (decide (W 35 = 0))) ?_ rfl) fun u ⟨⟨hm, hz⟩, ku⟩ sy => ?_
  · xrun [ea_sp, v.L.rsp, v.L.ld (d := sAny) (by decide), R.rd (d := sAny) 35 rfl (by decide)]
    rw [BitVec.and_self]
    rfl
  · refine ⟨⟨s, S, v.keep ku hm (by decide) (fun _ hp => by cases hp) sy, ku.2.1.trans hrd, hok⟩, ?_⟩
    change u.zf = _
    rw [hz, hw 35 (by decide), S.vw]

/-- The bound on the requested length is public too. -/
theorem saltLen_ct : RelCT isa (Two (VAt T (JM T.H (X7 T.H))))
    (.block [.mov .rax (.mem (sp sSlen)), .alu .cmp .rax (.mem (sp sDb))])
    (Two fun a t => VAt T (JM T.H (X7 T.H)) a t ∧
      isa.eval .b t = some (decide ((a.gpr .r8).toNat < vdb T.H.D a))) := by
  refine two_post (vtwo (T := T) (H := T.H) [24, 36] [] (fun _ => [])
    (fun a t h => jm_vs h _) (fun _ => rfl) (by decide) (by taint_decide))
    fun a t ⟨s, S, v, hrd, hok⟩ => ?_
  obtain ⟨V, W, R, hw, _⟩ := v.W
  have hk2 := S.ps.k2
  refine X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun u => u.mem = t.mem ∧
    u.cf = some (decide ((s.gpr .r8).toNat < vdb T.H.D s))) ?_ rfl) fun u ⟨⟨hm, hz⟩, ku⟩ sy => ?_
  · xrun [ea_sp, v.L.rsp, v.L.ld (d := sSlen) (by decide), v.L.ld (d := sDb) (by decide),
      R.rd (d := sSlen) 36 rfl (by decide), R.rd (d := sDb) 24 rfl (by decide),
      hw 36 (by decide), hw 24 (by decide)]
    simp only [vw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show vdb T.H.D s < 2 ^ 64 by unfold vdb veml; omega_using [])]
  · refine ⟨⟨s, S, v.keep ku hm (by decide) (fun _ hp => by cases hp) sy, ku.2.1.trans hrd, hok⟩, ?_⟩
    change u.cf = _
    rw [hz, S.rsl, S.vdb]

variable (hH : HashOK T.H) (K : Callees T.H) (hdk : DigOK T.H)

include hH K hdk in
theorem genericSaltBack_ct (hc : PssChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JM T.H (X7 T.H)))) (genericSaltBack T.f T.H)
      (Two (VAt T (JR T.H))) :=
  RelCT.assoc ((cyd_ct hH hc.verify).seq ((copyDb_ct hH hc.verify).seq
    ((shift_ct hH hc.verify).seq ((verifyNb_ct hH hc.verify).seq
      ((mhash_ct hH K hdk hc.hash1).seq (cmpH_ct hH hc.verify))))))

include hH K hdk in
theorem saltBack_ct (hc : PssChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JM T.H (X7 T.H)))) (saltBack T.f T.H)
      (Two (VAt T (JR T.H))) := by
  have generic := genericSaltBack_ct hH K hdk hc
  have fixed := fixedSaltBack_ct hH K hdk hc
  unfold saltBack
  refine saltAny_ct.seq (two_ite (fun a t₁ t₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_
    (generic.mono (fun _ _ => two_mono fun _ _ h => h.1.1) fun _ _ h => h))
  refine (saltLen_ct.seq (two_ite (fun a t₁ t₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_
    (generic.mono (fun _ _ => two_mono fun _ _ h => h.1.1) fun _ _ h => h))).mono
    (fun _ _ => two_mono fun _ _ h => h.1.1) (fun _ _ h => h)
  refine fixed.mono (fun _ _ => two_mono fun a t ⟨⟨⟨s, S, h⟩, hz⟩, hb⟩ => ?_) fun _ _ h => h
  have hf : (a.gpr .r8).toNat < vdb T.H.D a := by
    rw [hz, Option.some.injEq, decide_eq_true_eq] at hb
    exact hb
  exact ⟨s, S, h, by rwa [S.rsl, S.vdb]⟩

end VG.Proof.RsaPss.X86_64.Chk
