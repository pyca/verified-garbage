module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VCtx
public import VerifiedGarbage.Impl.RsaPss.X86_64
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS verification on x86-64: the frame and the prologues

The frame is RSAES-OAEP encryption's (`fb`, within `stkR`); the prologue
stores the arguments to their slots (`verPro_ok`, `verPW`) and the
selectors' prologue the lengths of the hash functions and the tables' words
(`verSel_ok`, `verW`). `VEnv` is what a state in the frame keeps of the
entry for the calls.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sScrLen sN sK sE sEl sSelH sSelG oRsa argSlot arg selPrologueWith)
open VG.Impl.Mgf1.X86_64 (sp)
open VG.Proof.RsaOaep.X86_64 (encStack stkR fb frR frame_sub ret_sub argAddr allocState_gpr' stackArgAddr_j tw
  fns_of_tab owned_one keep_cs3 Lay Rep Geo upd ea_sp Here TabAt selW fnW lenOf LensOK selProW_ok StepW
  cs_disj)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)

variable {s : State}

theorem fb_toNatV (hp : VPre s) : (fb s).toNat + frameBytes = (s.gpr .rsp).toNat := by
  have := hp.sp1; unfold encStack at this
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega

theorem VPre.geo (hp : VPre s) : Geo (fb s) (stackArg s 4) := by
  have hF := fb_toNatV hp
  have := hp.sp2
  have hsl := hp.hsl'
  have hk := hp.k1
  have wS := hp.wS
  have sS : Region.Sub ⟨stackArg s 4, oRsa⟩ (vscrR s) := Region.sub_prefix (by unfold oRsa; omega)
  refine ⟨by unfold frameBytes at *; omega, by unfold oRsa; omega,
    ((hp.dKS.sub_left (frame_sub s)).sub_right sS), ((hp.dKS.sub_left (ret_sub s)).sub_right sS)⟩

/-- A stack argument is readable. -/
theorem VPre.arg_in (hp : VPre s) {u : State} (hrd : u.rd = s.rd) {j : Nat} (hj : j < 12) :
    InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
  rw [hrd, hp.hrd]
  refine ⟨vargsR s, List.mem_append_left _ (by simp [vrd]), ?_⟩
  rw [argAddr, stackArgAddr_j s j]
  exact Offset.contains_base _ (by omega) (by omega)

/-- A stack argument, read from memory changed only in the frame. -/
theorem arg_readV (hp : VPre s) {m : Mem} (hf : Frame [frR s] s.mem m) {j : Nat} (hj : j < 12) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := vargsR s) ?_ (fun r' hr' => ?_) (by decide)
  · rw [stackArgAddr_j s j]
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.dKa.sub_left (frame_sub s)).symm

theorem frame_wV (hp : VPre s) {m m' : Mem} (hf : Frame [frR s] m m') {d : Nat}
    (hd : d + 8 ≤ frameBytes) (v : BitVec 64) : Frame [frR s] m (m'.writeW (off (fb s) d) v) := by
  have hF := fb_toNatV hp
  have := hp.sp2
  exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by unfold frameBytes at *; omega))

/-- One stack argument copied to a slot. -/
theorem copy1V_ok (hp : VPre s) {u : State} (hsp : u.gpr .rsp = fb s) (hfr : frR s ∈ u.wr)
    (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem) {j d : Nat} (hj : j < 12) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block (argSlot j d)) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j) ∧ Frame [frR s] s.mem u'.mem := by
  have hF := fb_toNatV hp
  have := hp.sp2
  have hsc : Scr u (fb s) frameBytes := Scr.of_mem hfr (by unfold frameBytes at *; omega)
  have hin := hp.arg_in hrd hj
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j)) ?_ rfl)
    fun u' ⟨hm, k⟩ => ⟨k, hm, hm ▸ frame_wV hp hf hd _⟩
  xrun [argSlot, arg, ea_sp, hsp, hin, arg_readV hp hf hj, hsc.st (d := d) hd]

/-- The slots `verifyPrologue` stores to, and what. -/
def verPW (s : State) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd (upd (upd (fun k => word s.mem (fb s) (8 * k))
    22 (s.gpr .rdi)) 23 (s.gpr .rsi)) 24 (s.gpr .rdx)) 25 (s.gpr .rcx)) 27 (s.gpr .r8))
    21 (stackArg s 0)) 14 (stackArg s 4)) 26 (stackArg s 5)

theorem verifyPrologue_eq : verifyPrologue =
    ([.store (sp sN) .rdi, .store (sp sK) .rsi, .store (sp sE) .rdx, .store (sp sEl) .rcx,
      .store (sp sDig) .r8] : List Instr) ++ argSlot 0 sSig ++ argSlot 4 sScr ++ argSlot 5 sScrLen := rfl

/-- The prologue: the slots as `verPW` says, the working space untouched. -/
theorem verPro_ok (hp : VPre s) :
    WP isa (.block verifyPrologue) (allocState frameBytes s) fun t => Keep [.rax] (allocState frameBytes s) t ∧
      Lay t (fb s) (stackArg s 4) ∧
      Rep t.mem (fb s) (stackArg s 4) (fun o => s.mem (off (stackArg s 4) o)) (verPW s) ∧
      Frame [frR s] s.mem t.mem := by
  have hF := fb_toNatV hp
  have := hp.sp2
  have G' := hp.geo
  have hsp : (allocState frameBytes s).gpr .rsp = fb s := rfl
  have hfr : frR s ∈ (allocState frameBytes s).wr := List.mem_cons_self ..
  have hsc : Scr (allocState frameBytes s) (fb s) frameBytes := Scr.of_mem hfr (by unfold frameBytes at *; omega)
  have R0 : Rep s.mem (fb s) (stackArg s 4) (fun o => s.mem (off (stackArg s 4) o))
      (fun k => word s.mem (fb s) (8 * k)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  rw [verifyPrologue_eq, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  have R1 := ((((R0.wf G' (k := 22) (by decide) (s.gpr .rdi)).wf G' (k := 23) (by decide) (s.gpr .rsi)).wf G'
    (k := 24) (by decide) (s.gpr .rdx)).wf G' (k := 25) (by decide) (s.gpr .rcx)).wf G' (k := 27) (by decide)
    (s.gpr .r8)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = ((((s.mem.writeW (off (fb s) (8 * 22)) (s.gpr .rdi)).writeW
      (off (fb s) (8 * 23)) (s.gpr .rsi)).writeW (off (fb s) (8 * 24)) (s.gpr .rdx)).writeW (off (fb s) (8 * 25))
      (s.gpr .rcx)).writeW (off (fb s) (8 * 27)) (s.gpr .r8)) ?_ rfl) fun t1 ⟨hm1, k1⟩ => ?_
  · xrun [ea_sp, hsp, hsc.st (d := sN) (by decide), hsc.st (d := sK) (by decide), hsc.st (d := sE) (by decide),
      hsc.st (d := sEl) (by decide), hsc.st (d := sDig) (by decide), allocState_gpr']
    rfl
  have f1 : Frame [frR s] s.mem t1.mem := by
    rw [hm1]
    exact frame_wV hp (frame_wV hp (frame_wV hp (frame_wV hp (frame_wV hp (Frame.refl _ _) (by decide) _)
      (by decide) _) (by decide) _) (by decide) _) (by decide) _
  have sp1 : t1.gpr .rsp = fb s := k1.gpr (by decide)
  have hfr1 : frR s ∈ t1.wr := k1.2.2 ▸ hfr
  refine WP.mono (copy1V_ok hp sp1 hfr1 k1.2.1 f1 (j := 0) (d := sSig) (by decide) (by decide))
    fun t2 ⟨k2, hm2, f2⟩ => ?_
  refine WP.mono (copy1V_ok hp ((k2.gpr (by decide)).trans sp1) (k2.2.2 ▸ hfr1) (k2.2.1.trans k1.2.1) f2
    (j := 4) (d := sScr) (by decide) (by decide)) fun t3 ⟨k3, hm3, f3⟩ => ?_
  have k23 := k2.trans k3
  refine WP.mono (copy1V_ok hp ((k23.gpr (by decide)).trans sp1) (k23.2.2 ▸ hfr1) (k23.2.1.trans k1.2.1) f3
    (j := 5) (d := sScrLen) (by decide) (by decide)) fun t4 ⟨k4, hm4, f4⟩ => ?_
  have k14 : Keep [.rax] (allocState frameBytes s) t4 := (k1.trans (k23.trans k4)).mono (by decide)
  have R4 : Rep t4.mem (fb s) (stackArg s 4) (fun o => s.mem (off (stackArg s 4) o)) (verPW s) := by
    rw [hm4, hm3, hm2, hm1]
    exact ((R1.wf G' (k := 21) (by decide) (stackArg s 0)).wf G' (k := 14) (by decide) (stackArg s 4)).wf G'
      (k := 26) (by decide) (stackArg s 5)
  have := hp.sp1
  refine ⟨k14, ⟨(k14.gpr (by decide)).trans hsp, k14.2.2 ▸ hfr, ?_, ?_, ?_, ?_, G'.dFS, G'.dRS⟩, R4, f4⟩
  · unfold encStack at this; unfold frameBytes at *; omega
  · unfold frameBytes at *; omega
  · have hsl := hp.hsl'
    have hk := hp.k1
    refine ⟨⟨stackArg s 4, 0, (stackArg s 5).toNat * 8, by rw [k14.2.2]; simp [allocState, hp.hwr],
      (BitVec.add_zero _).symm, by unfold oRsa; omega, hp.wS.trans' (by omega)⟩, G'.Sw⟩
  · rw [show sScr = 8 * 14 from rfl]
    exact (R4.fr 14 (by decide)).trans (by simp [verPW, upd])

/-- A number of `Spec.RsaPss.hashIds` and its length, of `pssLens`. -/
theorem mem_pssLens {i : Nat} (h : i ∈ Spec.RsaPss.hashIds) : (i, lenOf i) ∈ pssLens := by
  simp only [Spec.RsaPss.hashIds, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem pssLensOK : LensOK pssLens := ⟨by decide, by decide, by decide⟩

/-- A table, through the stack argument `j` (10 or 11), from the frame. -/
theorem VPre.tab (hp : VPre s) {u : State} (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem) {j : Nat}
    (hj : j = 10 ∨ j = 11) :
    TabAt u (fb s) j (stackArg s j) (tw s.mem (stackArg s j) 0) (tw s.mem (stackArg s j) 1)
      (tw s.mem (stackArg s j) 2) := by
  have hT : Region.Disjoint (frR s) ⟨stackArg s j, 24⟩ := by
    rcases hj with rfl | rfl
    · exact hp.dKtH.sub_left (frame_sub s)
    · exact hp.dKtG.sub_left (frame_sub s)
  have hw : (stackArg s j).toNat + 24 ≤ 2 ^ 64 := by rcases hj with rfl | rfl <;> [exact hp.wTH; exact hp.wTG]
  have hin : ∀ k < 3, InRegions (u.rd ++ u.wr) (off (stackArg s j) (8 * k)) 8 := fun k hk => by
    rw [hrd, hp.hrd]
    refine ⟨⟨stackArg s j, 24⟩, List.mem_append_left _ (by rcases hj with rfl | rfl <;> simp [vrd]), ?_⟩
    exact Offset.contains_base _ (by omega) (by omega)
  have hrdw : ∀ k < 3, ∀ m', Frame [frR s] s.mem m' →
      m'.readW (off (stackArg s j) (8 * k)) 64 = tw s.mem (stackArg s j) k := fun k hk m' hm =>
    hm.readW (r := ⟨stackArg s j, 24⟩) (Offset.contains_base _ (by omega) (by omega))
      (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hT.symm) (by decide)
  refine ⟨hp.arg_in hrd (by omega), fun m' hm => arg_readV hp (hf.trans hm) (by omega), ?_, hin 1 (by decide),
    hin 2 (by decide), fun m' hm => ⟨?_, hrdw 1 (by decide) m' (hf.trans hm), hrdw 2 (by decide) m' (hf.trans hm)⟩⟩
  · have := hin 0 (by decide); simpa [off] using this
  · have := hrdw 0 (by decide) m' (hf.trans hm); simpa [off] using this

/-- The slots after `verifyPrologue` and the selectors' prologue, and what. -/
def verW (s : State) : Nat → BitVec 64 :=
  fnW (selW (verPW s) (vselH s) (vselG s) (lenOf (vselH s)) (lenOf (vselG s)))
    (tw s.mem (vtabH s) 0) (tw s.mem (vtabH s) 1) (tw s.mem (vtabH s) 2)
    (tw s.mem (vtabG s) 0) (tw s.mem (vtabG s) 1) (tw s.mem (vtabG s) 2)

/-- The selectors' prologue, after `verifyPrologue`: the slots as `verW`
says, for the hash functions the selectors name. -/
theorem verSel_ok (hp : VPre s) {t : State} (k1 : Keep [.rax, .r10] (allocState frameBytes s) t)
    (L1 : Lay t (fb s) (stackArg s 4))
    (R1 : Rep t.mem (fb s) (stackArg s 4) (fun o => s.mem (off (stackArg s 4) o)) (verPW s))
    (f1 : Frame [frR s] s.mem t.mem) :
    WP isa (selPrologueWith pssLens 8 9) t fun t' => Lay t' (fb s) (stackArg s 4) ∧ Keep [.rax, .r10] t t' ∧
      Rep t'.mem (fb s) (stackArg s 4) (fun o => s.mem (off (stackArg s 4) o)) (verW s) ∧
      Frame [frR s] t.mem t'.mem := by
  have hrd : t.rd = s.rd := k1.2.1
  exact selProW_ok pssLensOK (mem_pssLens hp.iH) (mem_pssLens hp.iG) L1 R1 (hp.arg_in hrd (by decide))
    (hp.arg_in hrd (by decide)) (fun m' hm => ⟨by rw [arg_readV hp (f1.trans hm) (j := 8) (by decide)]; simp,
      by rw [arg_readV hp (f1.trans hm) (j := 9) (by decide)]; simp⟩)
    (hp.tab hrd f1 (.inl rfl)) (hp.tab hrd f1 (.inr rfl))

/-! ## In the frame -/

/-- Memory changed only in the stack the function uses and the working
space. -/
def FrV (s : State) (m : Mem) : Prop := Frame [stkR s, vscrR s] s.mem m

/-- The bytes of a region apart from those, as on entry. -/
theorem FrV.bytes {m : Mem} (h : FrV s m) {p : Addr} {len : Nat} (hk : (stkR s).Disjoint ⟨p, len⟩)
    (hs : (vscrR s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => Frame.bytes h (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hk.symm
  · exact hs.symm

/-- A step that changed memory only within the writable regions of a state
in the frame and the 16 bytes below it. -/
theorem FrV.step {m m' : Mem} (h : FrV s m) {ws : List Region}
    (hws : ws = [frR s, vscrR s]) (h' : Frame (ws ++ [below (fb s) 16]) m m') : FrV s m' :=
  h.trans (h'.sub fun r hr => by
    rw [hws] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., frame_sub s⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., ret_sub s⟩)

theorem VPre.wr (hp : VPre s) : (allocState frameBytes s).wr = [frR s, vscrR s] := by
  simp [allocState, hp.hwr]

/-- What the function writes is the entry's own: the frame and the 16 bytes
below it are in the stack it uses, the working space writable. -/
theorem VPre.owned (hp : VPre s) : Owned encStack s [frR s, vscrR s, below (fb s) 16] := by
  have hstk : Owned encStack s [stkR s] := fun r hr x hx => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨stkR s, List.mem_append_right _ (by simp [abi, encStack, stackBelow, stkR]), hx⟩
  have hw : ∀ r ∈ s.wr, Owned encStack s [r] := fun r hr q hq x hx => by
    rw [List.mem_singleton] at hq; subst hq
    exact ⟨q, List.mem_append_left _ hr, hx⟩
  exact (hstk.sub (frame_sub s)).cons ((hw _ (by simp [hp.hwr])).cons (hstk.sub (ret_sub s)))

theorem VPre.scrO (hp : VPre s) : Owned encStack s [⟨stackArg s 4, oRsa⟩] := by
  have := hp.hsl'; have := hp.k1
  exact (owned_one hp.owned (r := vscrR s) (by simp)).sub (Region.sub_prefix (by unfold oRsa; omega))

theorem VPre.sp16 (hp : VPre s) : 16 ≤ (fb s).toNat := by
  have := fb_toNatV hp; have := hp.sp1; unfold encStack frameBytes at *; omega

/-- In the frame, from the entry state `s`: what the calls need of the
state too. -/
structure VEnv (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = [frR s, vscrR s]
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r
  mx : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
  fr : FrV s t.mem
  world : World encStack s t
  own : Owned encStack s [frR s, vscrR s, below (fb s) 16]
  scr : Owned encStack s [⟨stackArg s 4, oRsa⟩]
  sp16 : 16 ≤ (fb s).toNat

theorem VEnv.step {t t' : State} (he : VEnv s t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.gpr .rsp = t.gpr .rsp) (hcs : ∀ r ∈ calleeSaved, r ≠ .rsp → t'.gpr r = t.gpr r)
    (hmx : t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10)
    (hf : StepW (t.wr ++ [below (t.gpr .rsp) 16]) t t') : VEnv s t' :=
  ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, fun r hr h => (hcs r hr h).trans (he.cs r hr h),
    hmx.trans he.mx, FrV.step he.fr (ws := t.wr) he.wr (by rw [he.rsp] at hf; exact hf.frame),
    he.world.step hf.funs hf.syms hf.frame (by rw [he.wr, he.rsp]; exact he.own), he.own, he.scr, he.sp16⟩

/-- What the calls of the streaming functions need. -/
theorem VEnv.here {t : State} (he : VEnv s t) : Here encStack s t (fb s) (stackArg s 4) :=
  ⟨he.world, fun r hr => he.own r (List.subset_append_left _ [below (fb s) 16] (he.wr ▸ hr)), he.scr,
    fun r hr => he.own r (List.subset_append_right [frR s, vscrR s] _ hr), he.sp16⟩

/-- After the prologue (`W = verPW`) or the selectors' too (`W = verW`): in
the frame, with the slots `W s`. -/
def JPV (W : State → Nat → BitVec 64) (s t : State) : Prop :=
  Keep [.rax, .r10] (allocState frameBytes s) t ∧ Lay t (fb s) (stackArg s 4) ∧
    Rep t.mem (fb s) (stackArg s 4) (fun o => s.mem (off (stackArg s 4) o)) (W s) ∧
    Frame [frR s] s.mem t.mem ∧ t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 ∧ t.funs = s.funs ∧
    t.syms = s.syms

/-- In the frame. -/
theorem JPV.env {W : State → Nat → BitVec 64} {t : State} (hp : VPre s) (h : JPV W s t) : VEnv s t :=
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
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub s⟩
    world := (World.refl encStack s).step fu1 sy1 f1 (owned_one hp.owned (List.mem_cons_self ..))
    own := hp.owned
    scr := hp.scrO
    sp16 := hp.sp16 }

end VG.Proof.RsaPss.X86_64
