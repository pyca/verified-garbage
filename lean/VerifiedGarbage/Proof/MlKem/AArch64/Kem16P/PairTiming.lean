module

public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Pair
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.SlotTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FinishTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import Std.Tactic.BVDecide.Normalize.Prop
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Pair
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.SlotTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.PairTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FinishTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import Std.Tactic.BVDecide.Normalize.Prop
meta import VerifiedGarbage.TCB.Axioms
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Squeeze
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Squeeze
meta import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P

/-!
# A pair computing PRF outputs leaks only public pointers and the public seed

As `Hybrid.pairMCode_relCT`, with the main squeezes of `Kem16P.stepP`
(`squeezeP_relCT`: a PRF slot by `slotPrf_relCT`, the others by
`Hybrid.plainStep_relCT`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon (PairAt pairR)
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Paired (Context stepWrites accepted seedState shakeStream BeginInput
  InitialReadyW initialCode finishCode finish_relCT initial_relCT exec_post seq_parts block_split blockAt)
open VG.Proof.MlKem.AArch64.Hybrid (Prepared3 prepareRegs3 plainStep_relCT startRegs3 frame)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint)
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Proof.Sha3 (iterF)

/-- One of the three main squeezes leaks only public pointers. -/
theorem pstep_relCT (L : KemLay) {init₁ init₂ s₁ s₂ : State} {p st R B₀ : Addr}
    {A₁ B₁ A₂ B₂ : Spec.Sha3.State} {N₀ m k : Nat} (hk : k < 3) (hN : N₀ + 2 < 256)
    (h4 : 4096 ≤ Impl.MlKem.AArch64.Kem16P.bufOff L N₀)
    (hl₁ : SqLayP p st R B₀ init₁) (hl₂ : SqLayP p st R B₀ init₂)
    (e28₁ : init₁.gpr .x28 = st) (e28₂ : init₂.gpr .x28 = st) (sp : init₁.sp = init₂.sp)
    (hR : st + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (h₁ : SInvP init₁ p st R B₀ A₁ B₁ N₀ m k s₁) (h₂ : SInvP init₂ p st R B₀ A₂ B₂ N₀ m k s₂) :
    RelCT isa (Eq2 s₁ s₂) (Impl.MlKem.AArch64.Kem16P.stepP L N₀ m k) TT := by
  unfold Impl.MlKem.AArch64.Kem16P.stepP
  split
  · exact slotPrf_relCT L (N := N₀ + k) (by omega)
      (by simp only [Impl.MlKem.AArch64.Kem16P.bufOff] at h4 ⊢; omega)
      h₁.ptr h₁.pa h₁.pb (by rw [h₁.keep.get .x28]; exact e28₁)
      h₂.ptr h₂.pa h₂.pb (by rw [h₂.keep.get .x28]; exact e28₂)
      (by rw [h₁.keep.sp, h₂.keep.sp, sp]) hR h₁.pair h₂.pair
      ((hl₁.frame h₁.keep.rd h₁.keep.wr h₁.keep.sp).slotLay hk)
      ((hl₂.frame h₂.keep.rd h₂.keep.wr h₂.keep.sp).slotLay hk)
  · exact plainStep_relCT (by rw [h₁.keep.sp, h₂.keep.sp, sp]) (by rw [h₁.ptr, h₂.ptr])
      (by rw [h₁.pa, h₂.pa]) (by rw [h₁.pb, h₂.pb])

theorem sinvP_zero {s : State} {p st R B₀ : Addr} {A B : Spec.Sha3.State} {N₀ m : Nat}
    (h19 : s.gpr .x19 = p) (h20 : s.gpr .x20 = p + 400) (h21 : s.gpr .x21 = p + 904)
    (pair : PairAt s.mem p A B) : SInvP s p st R B₀ A B N₀ m 0 s :=
  ⟨Keep.refl _ _, pair, h19, by rw [h20]; exact (BitVec.add_zero _).symm,
    by rw [h21]; exact (BitVec.add_zero _).symm, Frame.refl _ _,
    fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _),
    fun j hj => absurd hj (by simp)⟩

/-- **The three main squeezes** leak only public pointers. -/
theorem squeezeP_relCT (L : KemLay) {s₁ s₂ : State} {p st R B₀ : Addr}
    {A₁ B₁ A₂ B₂ : Spec.Sha3.State} {N₀ m : Nat} (hN : N₀ + 2 < 256)
    (hbo : Impl.MlKem.AArch64.Kem16P.bufOff L (N₀ + 2) < 65536)
    (h4 : 4096 ≤ Impl.MlKem.AArch64.Kem16P.bufOff L N₀)
    (hl₁ : SqLayP p st R B₀ s₁) (hl₂ : SqLayP p st R B₀ s₂)
    (e28₁ : s₁.gpr .x28 = st) (e28₂ : s₂.gpr .x28 = st) (sp : s₁.sp = s₂.sp)
    (hR : st + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (hB : st + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) = B₀)
    (h₁ : SInvP s₁ p st R B₀ A₁ B₁ N₀ m 0 s₁) (h₂ : SInvP s₂ p st R B₀ A₂ B₂ N₀ m 0 s₂) :
    RelCT isa (Eq2 s₁ s₂) (.seq (Impl.MlKem.AArch64.Kem16P.stepP L N₀ m 0)
      (.seq (Impl.MlKem.AArch64.Kem16P.stepP L N₀ m 1) (Impl.MlKem.AArch64.Kem16P.stepP L N₀ m 2))) TT := by
  refine rel_seq (pstep_relCT L (k := 0) (by decide) hN h4 hl₁ hl₂ e28₁ e28₂ sp hR h₁ h₂)
    (pstep_ok L (k := 0) (by decide) hN hbo hl₁ e28₁ hR hB h₁)
    (pstep_ok L (k := 0) (by decide) hN hbo hl₂ e28₂ hR hB h₂) fun t₁ t₂ ht₁ ht₂ => ?_
  refine rel_seq (pstep_relCT L (k := 1) (by decide) hN h4 hl₁ hl₂ e28₁ e28₂ sp hR ht₁ ht₂)
    (pstep_ok L (k := 1) (by decide) hN hbo hl₁ e28₁ hR hB ht₁)
    (pstep_ok L (k := 1) (by decide) hN hbo hl₂ e28₂ hR hB ht₂) fun u₁ u₂ hu₁ hu₂ => ?_
  exact pstep_relCT L (k := 2) (by decide) hN h4 hl₁ hl₂ e28₁ e28₂ sp hR hu₁ hu₂

def prepareP (L : KemLay) (sb ss a b N₀ m : Nat) : Prog isa :=
  .seq (.seq (.block (Impl.MlKem.AArch64.Paired.init sb ss a b L.k))
    (.seq (Impl.MlKem.AArch64.Kem16P.stepP L N₀ m 0)
      (.seq (Impl.MlKem.AArch64.Kem16P.stepP L N₀ m 1) (Impl.MlKem.AArch64.Kem16P.stepP L N₀ m 2))))
    (.block Impl.MlKem.AArch64.Rej8.rejConsts)

theorem prepareP_ok {w16 : Bool} (L : KemLay) {s : State} {p seed outA outB table st R B₀ : Addr}
    {sb ss a b N₀ m oa ob : Nat} (hN : N₀ + 2 < 256)
    (hbo : Impl.MlKem.AArch64.Kem16P.bufOff L (N₀ + 2) < 65536)
    (hss : ss < 65536) (hsb : sb + 32 ≤ 32768) (h8b : sb % 8 = 0)
    (h : BeginInput sb ss oa ob p seed outA outB table s) (hh : PrfInput p outA outB table st R B₀ s)
    (hR : st + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (hB : st + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) = B₀) :
    WP isa (prepareP L sb ss a b N₀ m) s
      (Prepared3 w16 (seedState s.mem seed a L.k) (seedState s.mem seed b L.k) oa ob p table s) := by
  refine WP.seq (WP.mono_syms (startP_ok (a := a) (b := b) (m := m) L hN hbo hss hsb h8b h.ptr h.seedPtr
    h.readable h.separate hh.lay hh.h28 hR hB) fun u ⟨ku, fu, _, u19, _, buA, buB, _⟩ sy => ?_)
  have cu : Context p outA outB table u := Context.frameP h.context ku.rd ku.wr fu hh.tS hh.tF hh.tB
  refine WP.mono_syms (Rej8.constants_ok u (by
    rw [u19]; exact Noise.inScratch cu.scratch (by decide) (by decide))) fun v ⟨kv, cv, mv, tv⟩ syv => ?_
  have fv : Frame [⟨p+1408,8⟩] u.mem v.mem := by
    rw [mv,u19]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 8)
  have fvBig : Frame (stepWrites p outA outB) u.mem v.mem := fv.sub (by
    intro r hr; rw [List.mem_singleton.mp hr]
    exact ⟨⟨p,2048⟩,by simp [stepWrites],Offset.sub_base p (by decide)⟩)
  have ctv := cu.frame kv.rd kv.wr fvBig
  have v19 : v.gpr .x19=p := (kv.get .x19).trans u19
  have v28 : v.gpr .x28=s.gpr .x28 := (kv.get .x28).trans (ku.get .x28 (by decide))
  have v16 : v.gpr .x16=table := by rw [tv,syv,sy,h.symbol]
  have streamA : ∀i<504,v.mem ((p+400)+BitVec.ofNat 64 i)=shakeStream (seedState s.mem seed a L.k) i := by
    intro i hi
    have hd : ∀r∈[Region.mk (p+1408) 8],(Region.mk (p+400) 504).Disjoint r := by
      intro r hr; rw [List.mem_singleton.mp hr]
      exact Offset.disjoint p (by decide) (by decide) (by decide)
    exact (fv.bytes hd (by change 504≤2^64; decide) hi).trans (buA.byte hi)
  have streamB : ∀i<504,v.mem ((p+904)+BitVec.ofNat 64 i)=shakeStream (seedState s.mem seed b L.k) i := by
    intro i hi
    have hd : ∀r∈[Region.mk (p+1408) 8],(Region.mk (p+904) 504).Disjoint r := by
      intro r hr; rw [List.mem_singleton.mp hr]
      exact Offset.disjoint p (by decide) (by decide) (by decide)
    exact (fv.bytes hd (by change 504≤2^64; decide) hi).trans (buB.byte hi)
  have ea := ctv.envW (w16 := w16) (N:=168) (off:=400) v16 (by decide) (by decide) (Or.inl rfl) streamA
  have eb := ctv.envW (w16 := w16) (N:=168) (off:=904) v16 (by decide) (by decide) (Or.inr rfl) streamB
  refine ⟨(ku.trans kv).mono (by simp [prepareRegs3]),?_,v19,v16⟩
  refine ⟨⟨?_,cv,?_,?_,?_⟩,⟨?_,cv,?_,?_,?_⟩,?_,?_⟩
  · rw [v19,v28,h.outLeft]; exact ea
  · rw [v19]; exact Noise.inScratch ctv.scratch (by decide) (by decide)
  · rw [v19]; exact Noise.inScratch ctv.scratch (by decide) (by decide)
  · rw [v19,v28,h.outLeft]; exact ctv.farA.symm.sub_right (Offset.sub_base p (by decide))
  · rw [v19,v28,h.outRight]; exact eb
  · rw [v19]; exact Noise.inScratch ctv.scratch (by decide) (by decide)
  · rw [v19]; exact Noise.inScratch ctv.scratch (by decide) (by decide)
  · rw [v19,v28,h.outRight]; exact ctv.farB.symm.sub_right (Offset.sub_base p (by decide))
  · rw [v19,v28,h.outLeft]; exact ctv.farA.symm
  · intro mask hm; rw [v19,v16]; exact ctv.tableScratch.sub_left (Rej8.table_sub table hm)

/-- The start of a PRF pair. -/
theorem prepareP_relCT (L : KemLay) {σ₁ σ₂ : State} {p seed outA outB table st R B₀ : Addr}
    {sb ss a b N₀ m oa ob : Nat} (hN : N₀ + 2 < 256)
    (hbo : Impl.MlKem.AArch64.Kem16P.bufOff L (N₀ + 2) < 65536)
    (h4 : 4096 ≤ Impl.MlKem.AArch64.Kem16P.bufOff L N₀)
    (hss : ss < 65536) (hsb : sb + 32 ≤ 32768) (h8b : sb % 8 = 0)
    (h₁ : BeginInput sb ss oa ob p seed outA outB table σ₁) (hh₁ : PrfInput p outA outB table st R B₀ σ₁)
    (h₂ : BeginInput sb ss oa ob p seed outA outB table σ₂) (hh₂ : PrfInput p outA outB table st R B₀ σ₂)
    (hR : st + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (hB : st + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) = B₀)
    (sp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) (prepareP L sb ss a b N₀ m) TT := by
  have b28 : σ₁.gpr .x28 = σ₂.gpr .x28 := by rw [hh₁.h28, hh₂.h28]
  have initCT : RelCT isa (Eq2 σ₁ σ₂) (.block (Impl.MlKem.AArch64.Paired.init sb ss a b L.k)) TT := by
    intro t v tr ur t' v' hh et ev
    obtain ⟨rfl, rfl⟩ := hh
    exact ⟨Paired.init_ct sb ss a b L.k _ _ _ _ _ _ trivial trivial
      (agree_of sp (by intro r hr; rw [List.mem_singleton.mp hr]; exact b28)) et ev, trivial⟩
  have iw₁ {o l : Nat} (h : o + l ≤ 2048) := Noise.inScratch hh₁.lay.scratch h (by decide)
  have iw₂ {o l : Nat} (h : o + l ≤ 2048) := Noise.inScratch hh₂.lay.scratch h (by decide)
  refine rel_seq (rel_seq initCT
    (Paired.init_ok (a := a) (b := b) (k := L.k) hss hsb h8b h₁.ptr h₁.seedPtr h₁.readable
      (fun j hj => iw₁ (by omega)) (fun j hj => iw₁ (by omega))
      (h₁.separate.sub_right (Offset.sub_base p (by decide)))
      (h₁.separate.sub_right (Region.sub_prefix (by decide : 400 ≤ 2048)))
      (Offset.disjoint_base p (by decide) (by decide)))
    (Paired.init_ok (a := a) (b := b) (k := L.k) hss hsb h8b h₂.ptr h₂.seedPtr h₂.readable
      (fun j hj => iw₂ (by omega)) (fun j hj => iw₂ (by omega))
      (h₂.separate.sub_right (Offset.sub_base p (by decide)))
      (h₂.separate.sub_right (Region.sub_prefix (by decide : 400 ≤ 2048)))
      (Offset.disjoint_base p (by decide) (by decide)))
    fun u₁ u₂ ⟨ku₁, _, _, h19₁, h20₁, h21₁, _, pair₁⟩ ⟨ku₂, _, _, h19₂, h20₂, h21₂, _, pair₂⟩ => ?_)
    (startP_ok (a := a) (b := b) (m := m) L hN hbo hss hsb h8b h₁.ptr h₁.seedPtr h₁.readable h₁.separate
      hh₁.lay hh₁.h28 hR hB)
    (startP_ok (a := a) (b := b) (m := m) L hN hbo hss hsb h8b h₂.ptr h₂.seedPtr h₂.readable h₂.separate
      hh₂.lay hh₂.h28 hR hB) fun w₁ w₂ hw₁ hw₂ => ?_
  · exact squeezeP_relCT L hN hbo h4 (hh₁.lay.frame ku₁.rd ku₁.wr ku₁.sp) (hh₂.lay.frame ku₂.rd ku₂.wr ku₂.sp)
      (by rw [ku₁.get .x28]; exact hh₁.h28) (by rw [ku₂.get .x28]; exact hh₂.h28)
      (by rw [ku₁.sp, ku₂.sp, sp]) hR hB
      (sinvP_zero h19₁ h20₁ h21₁ pair₁) (sinvP_zero h19₂ h20₂ h21₂ pair₂)
  · exact rel_taint [.x19, .x28] (by rw [hw₁.1.sp, hw₂.1.sp, sp])
      (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hw₁.2.2.2.1, hw₂.2.2.2.1]
        · rw [hw₁.1.get .x28 (by decide), hw₂.1.get .x28 (by decide), b28])
      ⟨_, by taint_decide⟩

theorem beginP_relCT {w16 : Bool} (L : KemLay) {σ₁ σ₂ : State} {p seed outA outB table st R B₀ : Addr}
    {sb ss a b N₀ m oa ob : Nat} (hN : N₀ + 2 < 256)
    (hbo : Impl.MlKem.AArch64.Kem16P.bufOff L (N₀ + 2) < 65536)
    (h4 : 4096 ≤ Impl.MlKem.AArch64.Kem16P.bufOff L N₀)
    (hss : ss < 65536) (hsb : sb + 32 ≤ 32768) (h8b : sb % 8 = 0) (hoa : oa < 65536) (hob : ob < 65536)
    (h₁ : BeginInput sb ss oa ob p seed outA outB table σ₁) (hh₁ : PrfInput p outA outB table st R B₀ σ₁)
    (h₂ : BeginInput sb ss oa ob p seed outA outB table σ₂) (hh₂ : PrfInput p outA outB table st R B₀ σ₂)
    (hR : st + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (hB : st + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) = B₀)
    (sp : σ₁.sp = σ₂.sp)
    (seedA : seedState σ₁.mem seed a L.k = seedState σ₂.mem seed a L.k)
    (seedB : seedState σ₁.mem seed b L.k = seedState σ₂.mem seed b L.k) :
    RelCT isa (fun t v => t = σ₁ ∧ v = σ₂) (beginPCode L sb ss a b N₀ m oa ob w16)
      (fun t v => BeginPPostW w16 (seedState σ₁.mem seed a L.k) (seedState σ₁.mem seed b L.k) p outA outB
          table st R B₀ N₀ m σ₁ t ∧
        BeginPPostW w16 (seedState σ₂.mem seed a L.k) (seedState σ₂.mem seed b L.k) p outA outB
          table st R B₀ N₀ m σ₂ v) := by
  let R' := fun t v : State => Prepared3 w16 (seedState σ₁.mem seed a L.k) (seedState σ₁.mem seed b L.k) oa ob p table σ₁ t ∧
    Prepared3 w16 (seedState σ₂.mem seed a L.k) (seedState σ₂.mem seed b L.k) oa ob p table σ₂ v
  have start : RelCT isa (fun t v => t = σ₁ ∧ v = σ₂) (prepareP L sb ss a b N₀ m) R' := by
    intro t v tr ur t' v' h et ev
    rcases h with ⟨ht, hv⟩; subst t; subst v
    exact ⟨(prepareP_relCT L hN hbo h4 hss hsb h8b h₁ hh₁ h₂ hh₂ hR hB sp _ _ _ _ _ _ ⟨rfl, rfl⟩ et ev).1,
      exec_post (prepareP_ok L hN hbo hss hsb h8b h₁ hh₁ hR hB) et,
      exec_post (prepareP_ok L hN hbo hss hsb h8b h₂ hh₂ hR hB) ev⟩
  have grouped : RelCT isa (fun t v => t = σ₁ ∧ v = σ₂)
      (.seq (prepareP L sb ss a b N₀ m) (initialCode oa ob w16)) (fun _ _ => True) := by
    refine RelCT.seq start ?_
    intro t v tr ur t' v' h et ev
    exact initial_relCT hoa hob h.1.ready (by rw [seedA, seedB]; exact h.2.ready)
      (h.1.keep.sp.trans (sp.trans h.2.keep.sp.symm))
      (h.1.pointer.trans h.2.pointer.symm)
      (by rw [h.1.keep.get .x28 (by decide), h.2.keep.get .x28 (by decide), hh₁.h28, hh₂.h28])
      (h.1.tablePtr.trans h.2.tablePtr.symm) t v tr ur t' v' ⟨rfl, rfl⟩ et ev
  have trace : RelCT isa (fun t v => t = σ₁ ∧ v = σ₂) (beginPCode L sb ss a b N₀ m oa ob w16)
      (fun _ _ => True) :=
    RelCT.assoc (RelCT.assoc grouped)
  intro t v tr ur t' v' h et ev
  rcases h with ⟨ht, hv⟩; subst t; subst v
  exact ⟨(trace σ₁ σ₂ tr ur t' v' ⟨rfl, rfl⟩ et ev).1,
    exec_post (beginP_ok L hN hbo hss hsb h8b hoa hob h₁ hh₁ hR hB) et,
    exec_post (beginP_ok L hN hbo hss hsb h8b hoa hob h₂ hh₂ hR hB) ev⟩

/-- **A pair computing PRF outputs** leaks only public pointers and the public seed. -/
theorem pairPCode_relCT {w16 : Bool} (L : KemLay) {σ₁ σ₂ : State} {p seed outA outB table st R B₀ : Addr}
    {sb ss a N₀ m oa ob : Nat} (hN : N₀ + 2 < 256)
    (hbo : Impl.MlKem.AArch64.Kem16P.bufOff L (N₀ + 2) < 65536)
    (h4 : 4096 ≤ Impl.MlKem.AArch64.Kem16P.bufOff L N₀)
    (hss : ss < 65536) (hsb : sb + 32 ≤ 32768) (h8b : sb % 8 = 0) (hoa : oa < 65536) (hob : ob < 65536)
    (h₁ : BeginInput sb ss oa ob p seed outA outB table σ₁) (hh₁ : PrfInput p outA outB table st R B₀ σ₁)
    (h₂ : BeginInput sb ss oa ob p seed outA outB table σ₂) (hh₂ : PrfInput p outA outB table st R B₀ σ₂)
    (hR : st + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (hB : st + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) = B₀)
    (sp : σ₁.sp = σ₂.sp)
    (seedA : seedState σ₁.mem seed a L.k = seedState σ₂.mem seed a L.k)
    (seedB : seedState σ₁.mem seed (a+1) L.k = seedState σ₂.mem seed (a+1) L.k) :
    RelCT isa (fun t v => t = σ₁ ∧ v = σ₂)
      (.seq (beginPCode L sb ss a (a+1) N₀ m oa ob w16) (finishCode w16)) (fun _ _ => True) := by
  let R' := fun t v : State =>
    BeginPPostW w16 (seedState σ₁.mem seed a L.k) (seedState σ₁.mem seed (a+1) L.k) p outA outB table st R B₀
      N₀ m σ₁ t ∧
    BeginPPostW w16 (seedState σ₂.mem seed a L.k) (seedState σ₂.mem seed (a+1) L.k) p outA outB table st R B₀
      N₀ m σ₂ v ∧
    t.syms = σ₁.syms ∧ v.syms = σ₂.syms
  have start : RelCT isa (fun t v => t = σ₁ ∧ v = σ₂) (beginPCode L sb ss a (a+1) N₀ m oa ob w16) R' := by
    intro t v tr ur t' v' h et ev
    rcases h with ⟨ht, hv⟩; subst t; subst v
    have hh := beginP_relCT L hN hbo h4 hss hsb h8b hoa hob h₁ hh₁ h₂ hh₂ hR hB sp seedA seedB
      σ₁ σ₂ tr ur t' v' ⟨rfl, rfl⟩ et ev
    exact ⟨hh.1, hh.2.1, hh.2.2, Exec.syms et, Exec.syms ev⟩
  refine RelCT.seq start ?_
  intro t v tr ur t' v' h et ev
  exact finish_relCT h.1.progress (by rw [seedA, seedB]; exact h.2.1.progress)
    (by rw [h.2.2.1]; exact h₁.symbol) (by rw [h.2.2.2]; exact h₂.symbol)
    h.1.flag (by rw [seedA, seedB]; exact h.2.1.flag)
    (h.1.keep.sp.trans (sp.trans h.2.1.keep.sp.symm)) t v tr ur t' v' ⟨rfl, rfl⟩ et ev

theorem pairP_exec {L : KemLay} {a N₀ m : Nat} {s t : State} {tr : List Leak}
    (h : Exec isa (Impl.MlKem.AArch64.Kem16P.pairP L a N₀ m) s tr t) :
    Exec isa (.seq (beginPCode L KEM.SB KEM.SS a (a+1) N₀ m (KEM.AH+1024*a) (KEM.AH+1024*(a+1)) true)
      (finishCode true)) s tr t := by
  simp only [Impl.MlKem.AArch64.Kem16P.pairP, seqs] at h
  obtain ⟨_,_,_,rfl,ei,h⟩ := seq_parts h
  obtain ⟨_,_,_,rfl,es,h⟩ := seq_parts h
  obtain ⟨_,_,_,rfl,ec,h⟩ := seq_parts h
  obtain ⟨_,_,_,rfl,ea,h⟩ := seq_parts h
  obtain ⟨_,_,_,rfl,eca,h⟩ := seq_parts h
  obtain ⟨_,_,_,rfl,eb,h⟩ := seq_parts h
  obtain ⟨_,_,_,rfl,ecb,h⟩ := seq_parts h
  obtain ⟨_,_,_,rfl,ex,er⟩ := seq_parts h
  have split := block_split (l:=[.str .x .x3 .x19 1696,.str .x .x4 .x19 1704])
    (r:=[.logic .and .x .x6 .x22 .x23]) ecb
  obtain ⟨_,_,_,rfl,ecbb,eand⟩ := seq_parts split
  have ee := Exec.seq (Exec.seq ei (Exec.seq es (Exec.seq ec
    (Exec.seq ea (Exec.seq eca (Exec.seq eb (Exec.seq ecbb eand))))))) (Exec.seq ex er)
  simpa only [beginPCode,initialCode,finishCode,seqs,List.append_assoc] using ee

end VG.Proof.MlKem.AArch64.Kem16P
