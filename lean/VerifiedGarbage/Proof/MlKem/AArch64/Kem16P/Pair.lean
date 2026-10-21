module

public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Squeeze
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Pair
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.NextBlock
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Finish
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Result
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SpecPost
import VerifiedGarbage.Proof.MlKem.AArch64.Shared

/-!
# A pair computing PRF outputs, complete

As `Hybrid/Begin.lean` and `Hybrid/Pair.lean`, with `Kem16P.pairP` for
`Hybrid.pairM`: `beginP_ok`, its initialization, three main squeezes
(`startP_ok`) and the first parse of each stream; `pairPCode_ok`, then
`Paired.finishCode`; `PairPPostW.outcome`, its outcome in terms of the
specification. The PRF outputs stay in their buffers (`PrfBufs`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon (PairAt pairR)
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Paired (Context stepWrites ProgressW accepted seedState seedBytes shakeStream
  initialCode initialRegions initial_ok pair_frame pairRegs pairWorkingRegs finishCode finish_ok)
open VG.Proof.MlKem.AArch64.Hybrid (beginRegs3 pairWrites3 frame startWrites)
open VG.Proof.Sha3 (iterF)
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Spec.MlKem
open VG.Proof.MlKem

def beginPCode (L : KemLay) (sb ss a b N₀ m oa ob : Nat) (w16 : Bool := false) : Prog isa :=
  .seq (.block (Impl.MlKem.AArch64.Paired.init sb ss a b L.k))
    (.seq (.seq (Impl.MlKem.AArch64.Kem16P.stepP L N₀ m 0)
      (.seq (Impl.MlKem.AArch64.Kem16P.stepP L N₀ m 1) (Impl.MlKem.AArch64.Kem16P.stepP L N₀ m 2)))
      (.seq (.block Impl.MlKem.AArch64.Rej8.rejConsts) (initialCode oa ob w16)))

theorem pairP_iff (L : KemLay) (a N₀ m : Nat) (s : State) (Q : State → Prop) :
    WP isa (Impl.MlKem.AArch64.Kem16P.pairP L a N₀ m) s Q ↔
    WP isa (.seq (beginPCode L KEM.SB KEM.SS a (a+1) N₀ m (KEM.AH+1024*a) (KEM.AH+1024*(a+1)) true) (finishCode true)) s Q := by
  simp only [Impl.MlKem.AArch64.Kem16P.pairP, beginPCode, initialCode, finishCode, seqs,
    show [Instr.str .x .x3 .x19 1696,.str .x .x4 .x19 1704,.logic .and .x .x6 .x22 .x23]=
      [.str .x .x3 .x19 1696,.str .x .x4 .x19 1704]++[.logic .and .x .x6 .x22 .x23] from rfl]
  simp only [WP.seq_iff (M := isa),WP.block_append_iff (M := isa)]

/-- A PRF pair's memory beyond `Paired.BeginInput`. -/
structure PrfInput (p outA outB table st R B₀ : Addr) (s : State) : Prop where
  lay : SqLayP p st R B₀ s
  h28 : s.gpr .x28 = st
  tS : (Region.mk table 4096).Disjoint (stR st)
  tF : (Region.mk table 4096).Disjoint (frame s.sp)
  aS : (polyRegion outA).Disjoint (stR st)
  bS : (polyRegion outB).Disjoint (stR st)
  aF : (polyRegion outA).Disjoint (bufR B₀)
  bF : (polyRegion outB).Disjoint (bufR B₀)
  tB : (Region.mk table 4096).Disjoint (bufR B₀)

theorem Context.frameP {s t : State} {p a b c st sp B₀ : Addr} (h : Context p a b c s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hf : Frame (startWritesP p st sp B₀) s.mem t.mem)
    (tS : (Region.mk c 4096).Disjoint (stR st)) (tF : (Region.mk c 4096).Disjoint (frame sp))
    (tB : (Region.mk c 4096).Disjoint (bufR B₀)) :
    Context p a b c t := by
  refine ⟨by simpa only [hw] using h.scratch, by simpa only [hw] using h.outA,
    by simpa only [hw] using h.outB, h.farA, h.farB, h.apart, ?_, by simpa only [hr, hw] using h.readable,
    h.tableScratch, h.tableA, h.tableB⟩
  exact h.artifact.frame hf (by
    intro r hh
    simp only [startWritesP, startWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with (rfl | rfl | rfl) | rfl
    · exact h.tableScratch
    · exact tS
    · exact tF
    · exact tB)

/-- The writes of a PRF pair. -/
def pairWritesP (p a b st sp B₀ : Addr) : List Region := pairWrites3 p a b st sp ++ [bufR B₀]

structure BeginPPostW (w16 : Bool) (A B : Spec.Sha3.State) (p a b c st R B₀ : Addr) (N₀ m : Nat)
    (s t : State) : Prop where
  keep : Keep beginRegs3 s t
  frame : Frame (pairWritesP p a b st s.sp B₀) s.mem t.mem
  saved : Noise.Saved p s t.mem
  progress : ProgressW w16 A B 3 p a b c t
  flag : (t.gpr .x6).toNat = if (accepted A 3).length = 256 ∧ (accepted B 3).length = 256 then 1 else 0
  prf : PrfBufs t.mem B₀ s.mem R N₀ (min 3 m)

theorem beginP_ok {w16 : Bool} (L : KemLay) {s : State}
    {p seed outA outB table st R B₀ : Addr} {sb ss a b N₀ m oa ob : Nat}
    (hN : N₀ + 2 < 256) (hbo : Impl.MlKem.AArch64.Kem16P.bufOff L (N₀ + 2) < 65536)
    (hss : ss < 65536) (hsb : sb + 32 ≤ 32768) (h8b : sb % 8 = 0) (hoa : oa < 65536) (hob : ob < 65536)
    (h : Paired.BeginInput sb ss oa ob p seed outA outB table s) (hh : PrfInput p outA outB table st R B₀ s)
    (hR : st + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (hB : st + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) = B₀) :
    WP isa (beginPCode L sb ss a b N₀ m oa ob w16) s
      (BeginPPostW w16 (seedState s.mem seed a L.k) (seedState s.mem seed b L.k) p outA outB table st R B₀ N₀ m s) := by
  have ctx := h.context
  have combined := WP.mono_syms (startP_ok (a := a) (b := b) (m := m) L hN hbo hss hsb h8b h.ptr h.seedPtr
    h.readable h.separate hh.lay hh.h28 hR hB)
    (R := fun u => WP isa (.seq (.block Impl.MlKem.AArch64.Rej8.rejConsts) (initialCode oa ob w16)) u
      (BeginPPostW w16 (seedState s.mem seed a L.k) (seedState s.mem seed b L.k) p outA outB table st R B₀ N₀ m s))
    (fun u ⟨ku, fu, svu, u19, pu, buA, buB, pfu⟩ sy => by
      have cu : Context p outA outB table u := Context.frameP ctx ku.rd ku.wr fu hh.tS hh.tF hh.tB
      refine WP.seq (WP.mono_syms (Rej8.constants_ok u (by
        rw [u19]; exact Noise.inScratch cu.scratch (by decide) (by decide)))
        fun v ⟨kv, cv, mv, tv⟩ syv => ?_)
      have fv : Frame [⟨p+1408,8⟩] u.mem v.mem := by
        rw [mv,u19]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 8)
      have fvBig : Frame (stepWrites p outA outB) u.mem v.mem := fv.sub (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ⟨⟨p,2048⟩,by simp [stepWrites],Offset.sub_base p (by decide)⟩)
      have ctv := cu.frame kv.rd kv.wr fvBig
      have v19 : v.gpr .x19=p := (kv.get .x19).trans u19
      have v28 : v.gpr .x28=s.gpr .x28 := (kv.get .x28).trans (ku.get .x28)
      have v16 : v.gpr .x16=table := by rw [tv,syv,sy,h.symbol]
      have streamA : ∀i<504,v.mem ((p+400)+BitVec.ofNat 64 i)=shakeStream (seedState s.mem seed a L.k) i := by
        intro i hi
        have hd : ∀r∈[Region.mk (p+1408) 8],(Region.mk (p+400) 504).Disjoint r := by
          intro r hr; simp only [List.mem_singleton] at hr; subst r
          exact (Offset.disjoint p (d := 400) (e := 1408) (n := 504) (k := 8) (by decide) (by decide) (by decide))
        exact (fv.bytes hd (by change 504≤2^64; decide) hi).trans (buA.byte hi)
      have streamB : ∀i<504,v.mem ((p+904)+BitVec.ofNat 64 i)=shakeStream (seedState s.mem seed b L.k) i := by
        intro i hi
        have hd : ∀r∈[Region.mk (p+1408) 8],(Region.mk (p+904) 504).Disjoint r := by
          intro r hr; simp only [List.mem_singleton] at hr; subst r
          exact (Offset.disjoint p (d := 904) (e := 1408) (n := 504) (k := 8) (by decide) (by decide) (by decide))
        exact (fv.bytes hd (by change 504≤2^64; decide) hi).trans (buB.byte hi)
      have ea := ctv.envW (w16 := w16) (N := 168) (off := 400) v16 (by decide) (by decide) (Or.inl rfl) streamA
      have eb := ctv.envW (w16 := w16) (N := 168) (off := 904) v16 (by decide) (by decide) (Or.inr rfl) streamB
      have pv := pair_frame pu fv (by
        simp only [List.mem_singleton,forall_eq]
        exact Offset.base_disjoint p (by decide) (by decide))
      have svv := svu.frame fv (by
        simp only [List.mem_singleton,forall_eq]
        exact Offset.disjoint p (by decide) (by decide) (by decide))
      have pars := initial_ok hoa hob
        (by rw [v19,v28,h.outLeft]; exact ea)
        (by rw [v19,v28,h.outRight]; exact eb) cv
        (by rw [v19]; exact ctv.scratch)
        (by rw [v19,v28,h.outLeft]; exact ctv.farA.symm)
        (by rw [v19,v28,h.outRight]; exact ctv.farB.symm)
        (by rw [v28,h.outLeft,h.outRight]; exact ctv.apart)
        (by intro mask hm; rw [v19,v16]; exact ctv.tableScratch.sub_left (Rej8.table_sub table hm))
      refine WP.mono pars fun t ht' => ?_
      have ft : Frame (initialRegions p outA outB) v.mem t.mem := by
        simpa only [v19,v28,h.outLeft,h.outRight] using ht'.frame
      have ftBig : Frame (stepWrites p outA outB) v.mem t.mem := ft.sub (by
        intro r hr; simp only [initialRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_,by simp [stepWrites],fun _ h => h⟩
        · exact ⟨_,by simp [stepWrites],fun _ h => h⟩
        · exact ⟨⟨p,2048⟩,by simp [stepWrites],Offset.sub_base p (by decide)⟩
        · exact ⟨⟨p,2048⟩,by simp [stepWrites],Offset.sub_base p (by decide)⟩)
      have ctt := ctv.frame ht'.keep.rd ht'.keep.wr ftBig
      have pt := pair_frame pv ft (by
        intro r hr; simp only [initialRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ctx.farA.sub_left (Region.sub_prefix (by decide : 400≤2048))
        · exact ctx.farB.sub_left (Region.sub_prefix (by decide : 400≤2048))
        · exact Offset.base_disjoint p (by decide) (by decide)
        · exact Offset.base_disjoint p (by decide) (by decide))
      have svt := svv.frame ft (by
        intro r hr; simp only [initialRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ctx.farA.sub_left (Offset.sub_base p (by decide))
        · exact ctx.farB.sub_left (Offset.sub_base p (by decide))
        · exact Offset.disjoint p (by decide) (by decide) (by decide)
        · exact Offset.disjoint p (by decide) (by decide) (by decide))
      have fut : Frame (stepWrites p outA outB) u.mem t.mem := fvBig.trans ftBig
      refine ⟨((ku.trans kv).trans ht'.keep).mono (by simp [beginRegs3,List.append_assoc]),
        ((fu.mono (by simp [startWritesP, startWrites, pairWritesP, pairWrites3, stepWrites])).trans
          (fut.mono (fun r hr => List.mem_append_left _ (List.mem_append_left _ hr)))),svt,
        ⟨ctt,(ht'.keep.get .x19).trans v19,pt,?_,?_,?_,?_⟩,ht'.both,?_⟩
      · simpa only [accepted,v28,h.outLeft] using ht'.first
      · simpa only [accepted,v28,h.outRight] using ht'.second
      · have hh := ht'.savedA
        rw [v19,v28,h.outLeft] at hh
        exact hh
      · have hh := ht'.savedB
        rw [v19,v28,h.outRight] at hh
        exact hh
      · exact pfu.frame (by omega) fut (fun r hr => by
          simp only [stepWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact hh.lay.dPF.symm
          · exact hh.aF.symm
          · exact hh.bF.symm))
  exact WP.seq (WP.mono (WP.seq_iff.mp combined) fun u hu => WP.seq hu)

structure PairPPostW (w16 : Bool) (A B : Spec.Sha3.State) (p a b st R B₀ : Addr) (N₀ m : Nat)
    (s t : State) : Prop where
  keep : Keep pairRegs s t
  frame : Frame (pairWritesP p a b st s.sp B₀) s.mem t.mem
  left : CoeffsUpToW w16 t.mem a (accepted A 5).length (VG.Proof.MlKem.AArch64.Sample.cvW w16 (accepted A 5)) (fun _=>0)
  reducedLeft : ReducedW (cw w16) t.mem a
  right : CoeffsUpToW w16 t.mem b (accepted B 5).length (VG.Proof.MlKem.AArch64.Sample.cvW w16 (accepted B 5)) (fun _=>0)
  reducedRight : ReducedW (cw w16) t.mem b
  status : t.gpr .x24=s.gpr .x24 &&& BitVec.ofNat 64
    (if (accepted A 5).length=256 ∧ (accepted B 5).length=256 then 1 else 0)
  prf : PrfBufs t.mem B₀ s.mem R N₀ (min 3 m)

theorem pairPCode_ok {w16 : Bool} (L : KemLay) {s : State}
    {p seed outA outB table st R B₀ : Addr} {sb ss a N₀ m oa ob : Nat}
    (hN : N₀ + 2 < 256) (hbo : Impl.MlKem.AArch64.Kem16P.bufOff L (N₀ + 2) < 65536)
    (hss : ss < 65536) (hsb : sb + 32 ≤ 32768) (h8b : sb % 8 = 0) (hoa : oa < 65536) (hob : ob < 65536)
    (h : Paired.BeginInput sb ss oa ob p seed outA outB table s) (hh : PrfInput p outA outB table st R B₀ s)
    (hR : st + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (hB : st + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) = B₀)
    (h24 : s.gpr .x24 = 0 ∨ s.gpr .x24 = 1) :
    WP isa (.seq (beginPCode L sb ss a (a+1) N₀ m oa ob w16) (finishCode w16)) s
      (PairPPostW w16 (seedState s.mem seed a L.k) (seedState s.mem seed (a+1) L.k) p outA outB st R B₀ N₀ m s) := by
  refine WP.seq (WP.mono_syms (beginP_ok L hN hbo hss hsb h8b hoa hob h hh hR hB) fun u hu sy => ?_)
  let initial : State := { s with mem := u.mem }
  have hk : Keep pairWorkingRegs initial u :=
    let k := hu.keep.mono (rs' := pairWorkingRegs) (by decide)
    ⟨k.gpr, k.rd, k.wr, k.sp, k.vcs⟩
  refine WP.mono (finish_ok (initial := initial) hk (Frame.refl _ _) hu.saved hu.progress
    (by rw [sy]; exact h.symbol) hu.flag (hu.keep.get .x24) h24) fun t ht => ?_
  have fut : Frame (stepWrites p outA outB) u.mem t.mem := ht.frame
  refine ⟨⟨ht.keep.gpr, ht.keep.rd, ht.keep.wr, ht.keep.sp, ht.keep.vcs⟩,
    hu.frame.trans (fut.mono fun r hr => List.mem_append_left _ (List.mem_append_left _ hr)), ht.left,
    ht.reducedLeft, ht.right, ht.reducedRight, ht.status, ?_⟩
  exact hu.prf.frame (by omega) fut (fun r hr => by
    simp only [stepWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hh.lay.dPF.symm
    · exact hh.aF.symm
    · exact hh.bF.symm)

structure PairPOutcomeW (w16 : Bool) (A B : List Byte) (p a b st R B₀ : Addr) (N₀ m : Nat)
    (s t : State) : Prop where
  keep : Keep pairRegs s t
  frame : Frame (pairWritesP p a b st s.sp B₀) s.mem t.mem
  reducedLeft : ReducedW (cw w16) t.mem a
  reducedRight : ReducedW (cw w16) t.mem b
  left : sampleNTT 280 A=none ∨ sampleNTT 280 A=some (polyAtW (cw w16) t.mem a)
  right : sampleNTT 280 B=none ∨ sampleNTT 280 B=some (polyAtW (cw w16) t.mem b)
  status : t.gpr .x24=s.gpr .x24 &&& BitVec.ofNat 64
    (if (sampleNTT 280 A).isSome ∧ (sampleNTT 280 B).isSome then 1 else 0)
  prf : PrfBufs t.mem B₀ s.mem R N₀ (min 3 m)

theorem PairPPostW.outcome {w16 : Bool} {s t : State} {p seed a b st R B₀ : Addr} {i i' k N₀ m : Nat}
    (hk : 0<k) (hk256 : k≤256)
    (h : PairPPostW w16 (seedState s.mem seed i k) (seedState s.mem seed i' k) p a b st R B₀ N₀ m s t) :
    PairPOutcomeW w16 (seedBytes s.mem seed i k) (seedBytes s.mem seed i' k) p a b st R B₀ N₀ m s t := by
  have ra := Paired.accepted_result hk hk256 h.left
  have rb := Paired.accepted_result hk hk256 h.right
  refine ⟨h.keep,h.frame,h.reducedLeft,h.reducedRight,?_,?_,?_,h.prf⟩
  · rcases ra with ⟨_,ha⟩|⟨_,ha⟩
    · exact Or.inr ha
    · exact Or.inl ha
  · rcases rb with ⟨_,hb⟩|⟨_,hb⟩
    · exact Or.inr hb
    · exact Or.inl hb
  · rw [h.status]
    rcases ra with ⟨la,ha⟩|⟨la,ha⟩ <;> rcases rb with ⟨lb,hb⟩|⟨lb,hb⟩ <;>
      simp [ha,hb,la,lb]

end VG.Proof.MlKem.AArch64.Kem16P
