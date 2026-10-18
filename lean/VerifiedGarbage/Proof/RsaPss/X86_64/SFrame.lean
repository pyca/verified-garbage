module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SCtx
public import VerifiedGarbage.Proof.RsaPss.X86_64.VHead
public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS signing on x86-64: the frame and the prologues

The frame is RSAES-OAEP's (`fb`), within the stack RSAES-OAEP decryption
uses (`stkD`); the prologue stores the arguments to their slots
(`signPro_ok`, `signPW`) and the selectors' prologue the lengths of the
hash functions and the tables' words (`signSel_ok`, `signW`). `SEnv` is what
a state in the frame keeps of the entry for the calls.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sScrLen sOut sN sK sE sEl sSelH sSelG oRsa argSlot arg
  selPrologueWith)
open VG.Impl.Mgf1.X86_64 (sp)
open VG.Proof.RsaOaep.X86_64 (decStack stkD fb frR frame_subD ret_subD below_subD argAddr allocState_gpr'
  stackArgAddr_j tw fns_of_tab owned_one keep_cs3 Lay Rep Geo upd ea_sp Here TabAt selW fnW lenOf selProW_ok
  StepW cs_disj outR)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.RsaPkcs1Enc.X86_64 (privStack)

variable {s : State}

theorem fb_toNatS (hp : SPre s) : (fb s).toNat + frameBytes = (s.gpr .rsp).toNat := by
  have := hp.sp1; unfold decStack privStack at this
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega

theorem SPre.geo (hp : SPre s) : Geo (fb s) (stackArg s 14) := by
  have hF := fb_toNatS hp
  have := hp.sp2
  have hsl := hp.hsl
  have hk := hp.k1
  have wS := hp.wS
  have sS : Region.Sub ⟨stackArg s 14, oRsa⟩ (sscrR s) := Region.sub_prefix (by unfold oRsa; omega)
  refine ⟨by unfold frameBytes at *; omega, by unfold oRsa; omega,
    ((hp.dKs.sub_left (frame_subD s)).sub_right sS), ((hp.dKs.sub_left (ret_subD s)).sub_right sS)⟩

/-- A stack argument is readable. -/
theorem SPre.arg_in (hp : SPre s) {u : State} (hrd : u.rd = s.rd) {j : Nat} (hj : j < 20) :
    InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
  rw [hrd, hp.hrd]
  refine ⟨sargsR s, List.mem_append_left _ (by simp [srd]), ?_⟩
  rw [argAddr, stackArgAddr_j s j]
  exact Offset.contains_base _ (by omega) (by omega)

/-- A stack argument, read from memory changed only in the frame. -/
theorem arg_readS (hp : SPre s) {m : Mem} (hf : Frame [frR s] s.mem m) {j : Nat} (hj : j < 20) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := sargsR s) ?_ (fun r' hr' => ?_) (by decide)
  · rw [stackArgAddr_j s j]
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.dKa.sub_left (frame_subD s)).symm

theorem frame_wS (hp : SPre s) {m m' : Mem} (hf : Frame [frR s] m m') {d : Nat}
    (hd : d + 8 ≤ frameBytes) (v : BitVec 64) : Frame [frR s] m (m'.writeW (off (fb s) d) v) := by
  have hF := fb_toNatS hp
  have := hp.sp2
  exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by unfold frameBytes at *; omega))

/-- One stack argument copied to a slot. -/
theorem copy1S_ok (hp : SPre s) {u : State} (hsp : u.gpr .rsp = fb s) (hfr : frR s ∈ u.wr)
    (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem) {j d : Nat} (hj : j < 20) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block (argSlot j d)) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j) ∧ Frame [frR s] s.mem u'.mem := by
  have hF := fb_toNatS hp
  have := hp.sp2
  have hsc : Scr u (fb s) frameBytes := Scr.of_mem hfr (by unfold frameBytes at *; omega)
  have hin := hp.arg_in hrd hj
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j)) ?_ rfl)
    fun u' ⟨hm, k⟩ => ⟨k, hm, hm ▸ frame_wS hp hf hd _⟩
  xrun [argSlot, arg, ea_sp, hsp, hin, arg_readS hp hf hj, hsc.st (d := d) hd]

/-- The slots `signPrologue` stores to, and what. -/
def signPW (s : State) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (fun k => word s.mem (fb s) (8 * k))
    21 (s.gpr .rdi)) 22 (s.gpr .rdx)) 23 (s.gpr .rcx)) 24 (s.gpr .r8)) 25 (s.gpr .r9))
    27 (stackArg s 10)) 28 (stackArg s 12)) 29 (stackArg s 13)) 14 (stackArg s 14)) 26 (stackArg s 15)

theorem signPrologue_eq : signPrologue =
    ([.store (sp sOut) .rdi, .store (sp sN) .rdx, .store (sp sK) .rcx, .store (sp sE) .r8,
      .store (sp sEl) .r9] : List Instr) ++ argSlot 10 sDig ++ argSlot 12 sSalt ++ argSlot 13 sSaltLen ++
      argSlot 14 sScr ++ argSlot 15 sScrLen := rfl

/-- The prologue: the slots as `signPW` says, the working space untouched. -/
theorem signPro_ok (hp : SPre s) :
    WP isa (.block signPrologue) (allocState frameBytes s) fun t => Keep [.rax] (allocState frameBytes s) t ∧
      Lay t (fb s) (stackArg s 14) ∧
      Rep t.mem (fb s) (stackArg s 14) (fun o => s.mem (off (stackArg s 14) o)) (signPW s) ∧
      Frame [frR s] s.mem t.mem := by
  have hF := fb_toNatS hp
  have := hp.sp2
  have G' := hp.geo
  have hsp : (allocState frameBytes s).gpr .rsp = fb s := rfl
  have hfr : frR s ∈ (allocState frameBytes s).wr := List.mem_cons_self ..
  have hsc : Scr (allocState frameBytes s) (fb s) frameBytes := Scr.of_mem hfr (by unfold frameBytes at *; omega)
  have R0 : Rep s.mem (fb s) (stackArg s 14) (fun o => s.mem (off (stackArg s 14) o))
      (fun k => word s.mem (fb s) (8 * k)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  rw [signPrologue_eq, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
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
    exact frame_wS hp (frame_wS hp (frame_wS hp (frame_wS hp (frame_wS hp (Frame.refl _ _) (by decide) _)
      (by decide) _) (by decide) _) (by decide) _) (by decide) _
  have sp1 : t1.gpr .rsp = fb s := k1.gpr (by decide)
  have hfr1 : frR s ∈ t1.wr := k1.2.2 ▸ hfr
  refine WP.mono (copy1S_ok hp sp1 hfr1 k1.2.1 f1 (j := 10) (d := sDig) (by decide) (by decide))
    fun t2 ⟨k2, hm2, f2⟩ => ?_
  refine WP.mono (copy1S_ok hp ((k2.gpr (by decide)).trans sp1) (k2.2.2 ▸ hfr1) (k2.2.1.trans k1.2.1) f2
    (j := 12) (d := sSalt) (by decide) (by decide)) fun t3 ⟨k3, hm3, f3⟩ => ?_
  have k23 := k2.trans k3
  refine WP.mono (copy1S_ok hp ((k23.gpr (by decide)).trans sp1) (k23.2.2 ▸ hfr1) (k23.2.1.trans k1.2.1) f3
    (j := 13) (d := sSaltLen) (by decide) (by decide)) fun t4 ⟨k4, hm4, f4⟩ => ?_
  have k24 := k23.trans k4
  refine WP.mono (copy1S_ok hp ((k24.gpr (by decide)).trans sp1) (k24.2.2 ▸ hfr1) (k24.2.1.trans k1.2.1) f4
    (j := 14) (d := sScr) (by decide) (by decide)) fun t5 ⟨k5, hm5, f5⟩ => ?_
  have k25 := k24.trans k5
  refine WP.mono (copy1S_ok hp ((k25.gpr (by decide)).trans sp1) (k25.2.2 ▸ hfr1) (k25.2.1.trans k1.2.1) f5
    (j := 15) (d := sScrLen) (by decide) (by decide)) fun t6 ⟨k6, hm6, f6⟩ => ?_
  have k16 : Keep [.rax] (allocState frameBytes s) t6 := (k1.trans (k25.trans k6)).mono (by decide)
  have R6 : Rep t6.mem (fb s) (stackArg s 14) (fun o => s.mem (off (stackArg s 14) o)) (signPW s) := by
    rw [hm6, hm5, hm4, hm3, hm2, hm1]
    exact ((((R1.wf G' (k := 27) (by decide) (stackArg s 10)).wf G' (k := 28) (by decide) (stackArg s 12)).wf G'
      (k := 29) (by decide) (stackArg s 13)).wf G' (k := 14) (by decide) (stackArg s 14)).wf G' (k := 26)
      (by decide) (stackArg s 15)
  have := hp.sp1
  refine ⟨k16, ⟨(k16.gpr (by decide)).trans hsp, k16.2.2 ▸ hfr, ?_, ?_, ?_, ?_, G'.dFS, G'.dRS⟩, R6, f6⟩
  · unfold decStack privStack at this; unfold frameBytes at *; omega
  · unfold frameBytes at *; omega
  · have hsl := hp.hsl
    have hk := hp.k1
    refine ⟨⟨stackArg s 14, 0, (stackArg s 15).toNat * 8, by rw [k16.2.2]; simp [allocState, hp.hwr],
      (BitVec.add_zero _).symm, by unfold oRsa; omega, hp.wS.trans' (by omega)⟩, G'.Sw⟩
  · rw [show sScr = 8 * 14 from rfl]
    exact (R6.fr 14 (by decide)).trans (by simp [signPW, upd])

/-- A table, through the stack argument `j` (18 or 19), from the frame. -/
theorem SPre.tab (hp : SPre s) {u : State} (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem) {j : Nat}
    (hj : j = 18 ∨ j = 19) :
    TabAt u (fb s) j (stackArg s j) (tw s.mem (stackArg s j) 0) (tw s.mem (stackArg s j) 1)
      (tw s.mem (stackArg s j) 2) := by
  have hT : Region.Disjoint (frR s) ⟨stackArg s j, 24⟩ := by
    rcases hj with rfl | rfl
    · exact hp.dKtH.sub_left (frame_subD s)
    · exact hp.dKtG.sub_left (frame_subD s)
  have hw : (stackArg s j).toNat + 24 ≤ 2 ^ 64 := by rcases hj with rfl | rfl <;> [exact hp.wTH; exact hp.wTG]
  have hin : ∀ k < 3, InRegions (u.rd ++ u.wr) (off (stackArg s j) (8 * k)) 8 := fun k hk => by
    rw [hrd, hp.hrd]
    refine ⟨⟨stackArg s j, 24⟩, List.mem_append_left _ (by rcases hj with rfl | rfl <;> simp [srd]), ?_⟩
    exact Offset.contains_base _ (by omega) (by omega)
  have hrdw : ∀ k < 3, ∀ m', Frame [frR s] s.mem m' →
      m'.readW (off (stackArg s j) (8 * k)) 64 = tw s.mem (stackArg s j) k := fun k hk m' hm =>
    hm.readW (r := ⟨stackArg s j, 24⟩) (Offset.contains_base _ (by omega) (by omega))
      (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hT.symm) (by decide)
  refine ⟨hp.arg_in hrd (by omega), fun m' hm => arg_readS hp (hf.trans hm) (by omega), ?_, hin 1 (by decide),
    hin 2 (by decide), fun m' hm => ⟨?_, hrdw 1 (by decide) m' (hf.trans hm), hrdw 2 (by decide) m' (hf.trans hm)⟩⟩
  · have := hin 0 (by decide); simpa [off] using this
  · have := hrdw 0 (by decide) m' (hf.trans hm); simpa [off] using this

/-- The slots after `signPrologue` and the selectors' prologue, and what. -/
def signW (s : State) : Nat → BitVec 64 :=
  fnW (selW (signPW s) (sselH s) (sselG s) (lenOf (sselH s)) (lenOf (sselG s)))
    (tw s.mem (stabH s) 0) (tw s.mem (stabH s) 1) (tw s.mem (stabH s) 2)
    (tw s.mem (stabG s) 0) (tw s.mem (stabG s) 1) (tw s.mem (stabG s) 2)

/-- The selectors' prologue, after `signPrologue`. -/
theorem signSel_ok (hp : SPre s) {t : State} (k1 : Keep [.rax, .r10] (allocState frameBytes s) t)
    (L1 : Lay t (fb s) (stackArg s 14))
    (R1 : Rep t.mem (fb s) (stackArg s 14) (fun o => s.mem (off (stackArg s 14) o)) (signPW s))
    (f1 : Frame [frR s] s.mem t.mem) :
    WP isa (selPrologueWith pssLens 16 17) t fun t' => Lay t' (fb s) (stackArg s 14) ∧ Keep [.rax, .r10] t t' ∧
      Rep t'.mem (fb s) (stackArg s 14) (fun o => s.mem (off (stackArg s 14) o)) (signW s) ∧
      Frame [frR s] t.mem t'.mem := by
  have hrd : t.rd = s.rd := k1.2.1
  exact selProW_ok pssLensOK (mem_pssLens hp.iH) (mem_pssLens hp.iG) L1 R1 (hp.arg_in hrd (by decide))
    (hp.arg_in hrd (by decide)) (fun m' hm => ⟨by rw [arg_readS hp (f1.trans hm) (j := 16) (by decide)]; simp,
      by rw [arg_readS hp (f1.trans hm) (j := 17) (by decide)]; simp⟩)
    (hp.tab hrd f1 (.inl rfl)) (hp.tab hrd f1 (.inr rfl))

/-! ## In the frame -/

/-- Memory changed only in the stack the function uses, `out` and the
working space. -/
def FrS (s : State) (m : Mem) : Prop := Frame [stkD s, outR s, sscrR s] s.mem m

theorem FrS.bytes {m : Mem} (h : FrS s m) {p : Addr} {len : Nat} (hk : (stkD s).Disjoint ⟨p, len⟩)
    (ho : (outR s).Disjoint ⟨p, len⟩) (hs : (sscrR s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => Frame.bytes h (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hk.symm
  · exact ho.symm
  · exact hs.symm

theorem FrS.step {m m' : Mem} (h : FrS s m) {ws : List Region}
    (hws : ws = [frR s, outR s, sscrR s]) (h' : Frame (ws ++ [below (fb s) 16]) m m') : FrS s m' :=
  h.trans (h'.sub fun r hr => by
    rw [hws] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., frame_subD s⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., ret_subD s⟩)

theorem SPre.wr (hp : SPre s) : (allocState frameBytes s).wr = [frR s, outR s, sscrR s] := by
  simp [allocState, hp.hwr, outR]

theorem stkOS (s : State) : Owned decStack s [stkD s] := fun r hr x hx => by
  rw [List.mem_singleton] at hr; subst hr
  exact ⟨stkD s, List.mem_append_right _ (by simp [abi, decStack, privStack, frameBytes, stackBelow, stkD]), hx⟩

/-- What the function writes is the entry's own. -/
theorem SPre.owned (hp : SPre s) : Owned decStack s [frR s, outR s, sscrR s, below (fb s) 16] := by
  have hstk := stkOS s
  have hw : ∀ r ∈ s.wr, Owned decStack s [r] := fun r hr q hq x hx => by
    rw [List.mem_singleton] at hq; subst hq
    exact ⟨q, List.mem_append_left _ hr, hx⟩
  exact (hstk.sub (frame_subD s)).cons ((hw _ (by simp [hp.hwr, outR])).cons
    ((hw _ (by simp [hp.hwr])).cons (hstk.sub (ret_subD s))))

theorem SPre.scrO (hp : SPre s) : Owned decStack s [⟨stackArg s 14, oRsa⟩] := by
  have := hp.hsl; have := hp.k1
  exact (owned_one hp.owned (r := sscrR s) (by simp)).sub (Region.sub_prefix (by unfold oRsa; omega))

theorem SPre.sp16 (hp : SPre s) : 16 ≤ (fb s).toNat := by
  have := fb_toNatS hp; have := hp.sp1; unfold decStack privStack frameBytes at *; omega

/-- In the frame, from the entry state `s`: what the calls need of the
state too. -/
structure SEnv (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = [frR s, outR s, sscrR s]
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r
  mx : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
  fr : FrS s t.mem
  world : World decStack s t
  own : Owned decStack s [frR s, outR s, sscrR s, below (fb s) 16]
  scr : Owned decStack s [⟨stackArg s 14, oRsa⟩]
  sp16 : 16 ≤ (fb s).toNat

theorem SEnv.step {t t' : State} (he : SEnv s t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.gpr .rsp = t.gpr .rsp) (hcs : ∀ r ∈ calleeSaved, r ≠ .rsp → t'.gpr r = t.gpr r)
    (hmx : t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10)
    (hf : StepW (t.wr ++ [below (t.gpr .rsp) 16]) t t') : SEnv s t' :=
  ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, fun r hr h => (hcs r hr h).trans (he.cs r hr h),
    hmx.trans he.mx, FrS.step he.fr (ws := t.wr) he.wr (by rw [he.rsp] at hf; exact hf.frame),
    he.world.step hf.funs hf.syms hf.frame (by rw [he.wr, he.rsp]; exact he.own), he.own, he.scr, he.sp16⟩

/-- What the calls of the streaming functions need. -/
theorem SEnv.here {t : State} (he : SEnv s t) : Here decStack s t (fb s) (stackArg s 14) :=
  ⟨he.world, fun r hr => he.own r (List.subset_append_left _ [below (fb s) 16] (he.wr ▸ hr)), he.scr,
    fun r hr => he.own r (List.subset_append_right [frR s, outR s, sscrR s] _ hr), he.sp16⟩

/-- After the prologue (`W = signPW`) or the selectors' too (`W = signW`). -/
def JPS (W : State → Nat → BitVec 64) (s t : State) : Prop :=
  Keep [.rax, .r10] (allocState frameBytes s) t ∧ Lay t (fb s) (stackArg s 14) ∧
    Rep t.mem (fb s) (stackArg s 14) (fun o => s.mem (off (stackArg s 14) o)) (W s) ∧
    Frame [frR s] s.mem t.mem ∧ t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 ∧ t.funs = s.funs ∧
    t.syms = s.syms

theorem JPS.env {W : State → Nat → BitVec 64} {t : State} (hp : SPre s) (h : JPS W s t) : SEnv s t :=
  let ⟨k1, _, _, f1, mx1, fu1, sy1⟩ := h
  { rsp := (k1.gpr (by decide)).trans rfl
    rd := k1.2.1
    wr := k1.2.2.trans hp.wr
    cs := fun r hr h => by
      rw [k1.gpr (cs_disj [.rax, .r10] (by decide) r hr)]
      show (if r = .rsp then _ else s.gpr r) = s.gpr r
      simp only [h, ↓reduceIte]
    mx := mx1
    fr := Frame.sub f1 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_subD s⟩
    world := (World.refl decStack s).step fu1 sy1 f1 (owned_one hp.owned (List.mem_cons_self ..))
    own := hp.owned
    scr := hp.scrO
    sp16 := hp.sp16 }

theorem spro_step (hp : SPre s) : WP isa (.block signPrologue) (allocState frameBytes s) (JPS signPW s) :=
  WP.mono (VG.Proof.RsaOaep.X86_64.wp_good (VG.Proof.RsaOaep.X86_64.block_good _ rfl rfl) (signPro_ok hp))
    fun _ ⟨⟨k, L, R, f⟩, _, mx, w⟩ => ⟨k.mono (by decide), L, R, f, mx, w.funs, w.syms⟩

theorem ssel_step (hp : SPre s) {t : State} (h : JPS signPW s t) :
    WP isa (selPrologueWith pssLens 16 17) t (JPS signW s) := by
  obtain ⟨k1, L1, R1, f1, mx1, fu1, sy1⟩ := h
  exact WP.mono (VG.Proof.RsaOaep.X86_64.wp_good (VG.Proof.RsaOaep.X86_64.selPrologueWith_good pssLensH_good
    pssLensG_good 16 17) (signSel_ok hp k1 L1 R1 f1)) fun t2 ⟨⟨L2, k2, R2, f2⟩, _, mx2, w2⟩ =>
      ⟨(k1.trans k2).mono (by decide), L2, R2, f1.trans f2, mx2.trans mx1, w2.funs.trans fu1, w2.syms.trans sy1⟩

end VG.Proof.RsaPss.X86_64
