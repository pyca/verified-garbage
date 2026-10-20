module
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Begin
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Finish

import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.StepTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FinishTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import Std.Tactic.BVDecide.Normalize.Prop
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Begin
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Finish
meta import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.StepTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FinishTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import Std.Tactic.BVDecide.Normalize.Prop
meta import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# A hashing pair leaks only public pointers and the public seed

As `Paired.pairCode_relCT`: the start (`prepare3_relCT`: the
initialization by the taint analysis, the main squeezes by
`squeeze3_relCT`, the rejection constants by the taint analysis), the first
parse (`Paired.initial_relCT`) and the rest (`Paired.finish_relCT`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Paired (Context stepWrites accepted seedState shakeStream BeginInput
  InitialReadyW initialCode finishCode finish_relCT initial_relCT exec_post seq_parts block_split)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint)
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Proof.Sha3 (iterF)

def prepare3Code (L : KemLay) (sb ss a b i : Nat) : Prog isa :=
  .seq (.seq (.block (Impl.MlKem.AArch64.Paired.init sb ss a b L.k)) (Impl.MlKem.AArch64.Hybrid.squeeze3 L i))
    (.block Impl.MlKem.AArch64.Rej8.rejConsts)

def prepareRegs3 : List Reg := startRegs3 ++ [.x9, .x16]

structure Prepared3 (w16 : Bool) (A B : Spec.Sha3.State) (oa ob : Nat) (p table : Addr) (s t : State) :
    Prop where
  keep : Keep prepareRegs3 s t
  ready : InitialReadyW w16 (shakeStream A) (shakeStream B) oa ob t
  pointer : t.gpr .x19 = p
  tablePtr : t.gpr .x16 = table

theorem prepare3_ok {w16 : Bool} (L : KemLay) {s : State} {p seed outA outB table e st : Addr} {E : List Byte}
    {sb ss a b i oa ob : Nat} (hss : ss < 65536) (hsb : sb + 32 ≤ 32768) (h8b : sb % 8 = 0)
    (h : BeginInput sb ss oa ob p seed outA outB table s) (hh : HashInput L p outA outB table e st s)
    (hb : 136 * (3 * i + 2) < L.ekLen) (h8 : L.ekLen % 8 = 0) (hlim : L.ekLen ≤ 4096)
    (hash : stateAt s.mem st = hstate E (3 * i)) (hE : bytesAt s.mem e L.ekLen = E) :
    WP isa (prepare3Code L sb ss a b i) s
      (Prepared3 w16 (seedState s.mem seed a L.k) (seedState s.mem seed b L.k) oa ob p table s) := by
  refine WP.seq (WP.mono_syms (start3_ok (a := a) (b := b) L hss hsb h8b h.ptr h.seedPtr h.readable h.separate
    hh.lay hh.h25 hh.h28 hb h8 hlim hash hE) fun u ⟨ku, fu, _, u19, _, buA, buB, _, _⟩ sy => ?_)
  have cu : Context p outA outB table u := Context.frame3 h.context ku.rd ku.wr fu hh.tS hh.tF
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

/-- The start of a hashing pair. -/
theorem prepare3_relCT (L : KemLay) {σ₁ σ₂ : State} {p seed outA outB table e st : Addr}
    {E₁ E₂ : List Byte} {sb ss a b i oa ob : Nat}
    (hss : ss < 65536) (hsb : sb + 32 ≤ 32768) (h8b : sb % 8 = 0)
    (h₁ : BeginInput sb ss oa ob p seed outA outB table σ₁) (hh₁ : HashInput L p outA outB table e st σ₁)
    (h₂ : BeginInput sb ss oa ob p seed outA outB table σ₂) (hh₂ : HashInput L p outA outB table e st σ₂)
    (hb : 136 * (3 * i + 2) < L.ekLen) (h8 : L.ekLen % 8 = 0) (hlim : L.ekLen ≤ 4096)
    (hash₁ : stateAt σ₁.mem st = hstate E₁ (3 * i)) (hE₁ : bytesAt σ₁.mem e L.ekLen = E₁)
    (hash₂ : stateAt σ₂.mem st = hstate E₂ (3 * i)) (hE₂ : bytesAt σ₂.mem e L.ekLen = E₂)
    (sp : σ₁.sp = σ₂.sp)
    (habs : ∀ blk, 136 * blk < L.ekLen → ∃ h, (taint.check (Taint.ofRegs [.x25, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock L blk)) h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) (prepare3Code L sb ss a b i) TT := by
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
    fun u₁ u₂ ⟨ku₁, fu₁, _, h19₁, h20₁, h21₁, _, pair₁⟩ ⟨ku₂, fu₂, _, h19₂, h20₂, h21₂, _, pair₂⟩ => ?_)
    (start3_ok (a := a) (b := b) L hss hsb h8b h₁.ptr h₁.seedPtr h₁.readable h₁.separate
      hh₁.lay hh₁.h25 hh₁.h28 hb h8 hlim hash₁ hE₁)
    (start3_ok (a := a) (b := b) L hss hsb h8b h₂.ptr h₂.seedPtr h₂.readable h₂.separate
      hh₂.lay hh₂.h25 hh₂.h28 hb h8 hlim hash₂ hE₂) fun w₁ w₂ hw₁ hw₂ => ?_
  · have fi₁ : Frame [⟨p, 2048⟩] σ₁.mem u₁.mem := fu₁.sub (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨p, 2048⟩, by simp, Offset.sub_base p (by decide)⟩
      · exact ⟨⟨p, 2048⟩, by simp, Region.sub_prefix (by decide : 400 ≤ 2048)⟩)
    have fi₂ : Frame [⟨p, 2048⟩] σ₂.mem u₂.mem := fu₂.sub (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨p, 2048⟩, by simp, Offset.sub_base p (by decide)⟩
      · exact ⟨⟨p, 2048⟩, by simp, Region.sub_prefix (by decide : 400 ≤ 2048)⟩)
    have hs₁ : stateAt u₁.mem st = hstate E₁ (3 * i) := by
      rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame fi₁ (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hh₁.lay.dSP), hash₁]
    have hs₂ : stateAt u₂.mem st = hstate E₂ (3 * i) := by
      rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame fi₂ (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hh₂.lay.dSP), hash₂]
    have he₁ : bytesAt u₁.mem e L.ekLen = E₁ := by
      rw [VG.Proof.MlKem.bytesAt_frame fi₁ (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hh₁.lay.dEP) (by omega), hE₁]
    have he₂ : bytesAt u₂.mem e L.ekLen = E₂ := by
      rw [VG.Proof.MlKem.bytesAt_frame fi₂ (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hh₂.lay.dEP) (by omega), hE₂]
    exact squeeze3_relCT L hb h8 hlim (hh₁.lay.frame ku₁.rd ku₁.wr ku₁.sp) (hh₂.lay.frame ku₂.rd ku₂.wr ku₂.sp)
      (by rw [ku₁.get .x25]; exact hh₁.h25) (by rw [ku₁.get .x28]; exact hh₁.h28)
      (by rw [ku₂.get .x25]; exact hh₂.h25) (by rw [ku₂.get .x28]; exact hh₂.h28)
      (by rw [ku₁.sp, ku₂.sp, sp])
      (sinv3_zero L h19₁ h20₁ h21₁ pair₁ hs₁ he₁) (sinv3_zero L h19₂ h20₂ h21₂ pair₂ hs₂ he₂) habs
  · exact rel_taint [.x19, .x28] (by rw [hw₁.1.sp, hw₂.1.sp, sp])
      (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hw₁.2.2.2.1, hw₂.2.2.2.1]
        · rw [hw₁.1.get .x28 (by decide), hw₂.1.get .x28 (by decide), b28])
      ⟨_, by taint_decide⟩

theorem begin3_relCT {w16 : Bool} (L : KemLay) {σ₁ σ₂ : State} {p seed outA outB table e st : Addr}
    {E₁ E₂ : List Byte} {sb ss a b i oa ob : Nat}
    (hss : ss < 65536) (hsb : sb + 32 ≤ 32768) (h8b : sb % 8 = 0) (hoa : oa < 65536) (hob : ob < 65536)
    (h₁ : BeginInput sb ss oa ob p seed outA outB table σ₁) (hh₁ : HashInput L p outA outB table e st σ₁)
    (h₂ : BeginInput sb ss oa ob p seed outA outB table σ₂) (hh₂ : HashInput L p outA outB table e st σ₂)
    (hb : 136 * (3 * i + 2) < L.ekLen) (h8 : L.ekLen % 8 = 0) (hlim : L.ekLen ≤ 4096)
    (hash₁ : stateAt σ₁.mem st = hstate E₁ (3 * i)) (hE₁ : bytesAt σ₁.mem e L.ekLen = E₁)
    (hash₂ : stateAt σ₂.mem st = hstate E₂ (3 * i)) (hE₂ : bytesAt σ₂.mem e L.ekLen = E₂)
    (sp : σ₁.sp = σ₂.sp)
    (seedA : seedState σ₁.mem seed a L.k = seedState σ₂.mem seed a L.k)
    (seedB : seedState σ₁.mem seed b L.k = seedState σ₂.mem seed b L.k)
    (habs : ∀ blk, 136 * blk < L.ekLen → ∃ h, (taint.check (Taint.ofRegs [.x25, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock L blk)) h).isSome = true) :
    RelCT isa (fun t v => t = σ₁ ∧ v = σ₂) (begin3Code L sb ss a b i oa ob w16)
      (fun t v => Begin3PostW w16 L (seedState σ₁.mem seed a L.k) (seedState σ₁.mem seed b L.k) p outA outB table e st E₁ i σ₁ t ∧
        Begin3PostW w16 L (seedState σ₂.mem seed a L.k) (seedState σ₂.mem seed b L.k) p outA outB table e st E₂ i σ₂ v) := by
  let R := fun t v : State => Prepared3 w16 (seedState σ₁.mem seed a L.k) (seedState σ₁.mem seed b L.k) oa ob p table σ₁ t ∧
    Prepared3 w16 (seedState σ₂.mem seed a L.k) (seedState σ₂.mem seed b L.k) oa ob p table σ₂ v
  have start : RelCT isa (fun t v => t = σ₁ ∧ v = σ₂) (prepare3Code L sb ss a b i) R := by
    intro t v tr ur t' v' h et ev
    rcases h with ⟨ht, hv⟩; subst t; subst v
    exact ⟨(prepare3_relCT L hss hsb h8b h₁ hh₁ h₂ hh₂ hb h8 hlim hash₁ hE₁ hash₂ hE₂ sp habs
        _ _ _ _ _ _ ⟨rfl, rfl⟩ et ev).1,
      exec_post (prepare3_ok L hss hsb h8b h₁ hh₁ hb h8 hlim hash₁ hE₁) et,
      exec_post (prepare3_ok L hss hsb h8b h₂ hh₂ hb h8 hlim hash₂ hE₂) ev⟩
  have grouped : RelCT isa (fun t v => t = σ₁ ∧ v = σ₂)
      (.seq (prepare3Code L sb ss a b i) (initialCode oa ob w16)) (fun _ _ => True) := by
    refine RelCT.seq start ?_
    intro t v tr ur t' v' h et ev
    exact initial_relCT hoa hob h.1.ready (by rw [seedA, seedB]; exact h.2.ready)
      (h.1.keep.sp.trans (sp.trans h.2.keep.sp.symm))
      (h.1.pointer.trans h.2.pointer.symm)
      (by rw [h.1.keep.get .x28 (by decide), h.2.keep.get .x28 (by decide), hh₁.h28, hh₂.h28])
      (h.1.tablePtr.trans h.2.tablePtr.symm) t v tr ur t' v' ⟨rfl, rfl⟩ et ev
  have trace : RelCT isa (fun t v => t = σ₁ ∧ v = σ₂) (begin3Code L sb ss a b i oa ob w16) (fun _ _ => True) :=
    RelCT.assoc (RelCT.assoc grouped)
  intro t v tr ur t' v' h et ev
  rcases h with ⟨ht, hv⟩; subst t; subst v
  exact ⟨(trace σ₁ σ₂ tr ur t' v' ⟨rfl, rfl⟩ et ev).1,
    exec_post (begin3_ok L hss hsb h8b hoa hob h₁ hh₁ hb h8 hlim hash₁ hE₁) et,
    exec_post (begin3_ok L hss hsb h8b hoa hob h₂ hh₂ hb h8 hlim hash₂ hE₂) ev⟩

theorem pair3Code_relCT {w16 : Bool} (L : KemLay) {σ₁ σ₂ : State} {p seed outA outB table e st : Addr}
    {E₁ E₂ : List Byte} {a i : Nat} (hoa : KEM.AH+1024*a < 65536) (hob : KEM.AH+1024*(a+1) < 65536)
    (h₁ : BeginInput KEM.SB KEM.SS (KEM.AH+1024*a) (KEM.AH+1024*(a+1)) p seed outA outB table σ₁)
    (hh₁ : HashInput L p outA outB table e st σ₁)
    (h₂ : BeginInput KEM.SB KEM.SS (KEM.AH+1024*a) (KEM.AH+1024*(a+1)) p seed outA outB table σ₂)
    (hh₂ : HashInput L p outA outB table e st σ₂)
    (hb : 136 * (3 * i + 2) < L.ekLen) (h8 : L.ekLen % 8 = 0) (hlim : L.ekLen ≤ 4096)
    (hash₁ : stateAt σ₁.mem st = hstate E₁ (3 * i)) (hE₁ : bytesAt σ₁.mem e L.ekLen = E₁)
    (hash₂ : stateAt σ₂.mem st = hstate E₂ (3 * i)) (hE₂ : bytesAt σ₂.mem e L.ekLen = E₂)
    (sp : σ₁.sp = σ₂.sp)
    (seedA : seedState σ₁.mem seed a L.k = seedState σ₂.mem seed a L.k)
    (seedB : seedState σ₁.mem seed (a+1) L.k = seedState σ₂.mem seed (a+1) L.k)
    (habs : ∀ blk, 136 * blk < L.ekLen → ∃ h, (taint.check (Taint.ofRegs [.x25, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock L blk)) h).isSome = true) :
    RelCT isa (fun t v => t = σ₁ ∧ v = σ₂)
      (.seq (begin3Code L KEM.SB KEM.SS a (a+1) i (KEM.AH+1024*a) (KEM.AH+1024*(a+1)) w16) (finishCode w16))
      (fun _ _ => True) := by
  let R := fun t v : State =>
    Begin3PostW w16 L (seedState σ₁.mem seed a L.k) (seedState σ₁.mem seed (a+1) L.k) p outA outB table e st E₁ i σ₁ t ∧
    Begin3PostW w16 L (seedState σ₂.mem seed a L.k) (seedState σ₂.mem seed (a+1) L.k) p outA outB table e st E₂ i σ₂ v ∧
    t.syms = σ₁.syms ∧ v.syms = σ₂.syms
  have start : RelCT isa (fun t v => t = σ₁ ∧ v = σ₂)
      (begin3Code L KEM.SB KEM.SS a (a+1) i (KEM.AH+1024*a) (KEM.AH+1024*(a+1)) w16) R := by
    intro t v tr ur t' v' h et ev
    rcases h with ⟨ht, hv⟩; subst t; subst v
    have hh := begin3_relCT L (by decide) (by decide) (by decide) hoa hob h₁ hh₁ h₂ hh₂ hb h8 hlim hash₁ hE₁ hash₂ hE₂
      sp seedA seedB habs σ₁ σ₂ tr ur t' v' ⟨rfl, rfl⟩ et ev
    exact ⟨hh.1, hh.2.1, hh.2.2, Exec.syms et, Exec.syms ev⟩
  refine RelCT.seq start ?_
  intro t v tr ur t' v' h et ev
  exact finish_relCT h.1.progress (by rw [seedA, seedB]; exact h.2.1.progress)
    (by rw [h.2.2.1]; exact h₁.symbol) (by rw [h.2.2.2]; exact h₂.symbol)
    h.1.flag (by rw [seedA, seedB]; exact h.2.1.flag)
    (h.1.keep.sp.trans (sp.trans h.2.1.keep.sp.symm)) t v tr ur t' v' ⟨rfl, rfl⟩ et ev

theorem pair3_exec {w16 : Bool} {L : KemLay} {a i : Nat} {s t : State} {tr : List Leak}
    (h : Exec isa (Impl.MlKem.AArch64.Hybrid.pair3 L a i w16) s tr t) :
    Exec isa (.seq (begin3Code L KEM.SB KEM.SS a (a+1) i (KEM.AH+1024*a) (KEM.AH+1024*(a+1)) w16) (finishCode w16))
      s tr t := by
  simp only [Impl.MlKem.AArch64.Hybrid.pair3, seqs] at h
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
  simpa only [begin3Code,initialCode,finishCode,seqs,List.append_assoc] using ee

end VG.Proof.MlKem.AArch64.Hybrid
