module

public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Squeeze
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.BeginTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Pair

/-!
# A hashing pair

`begin3_ok`: a hashing pair's initialization, its three main squeezes
(`start3_ok`), and the first parse of each stream (as `Paired.begin_ok`).
`pair3Code_ok`: then the rest of the pair (`Paired.finishCode`, unchanged),
from `Paired.finish_ok`.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon (PairAt pairR)
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Paired (Context stepWrites ProgressW accepted seedState shakeStream
  initialCode initialRegions initial_ok pair_frame)
open VG.Proof.Sha3 (iterF)
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Proof.MlKem (polyRegion)

def begin3Code (L : KemLay) (sb ss a b i oa ob : Nat) (w16 : Bool := false) : Prog isa :=
  .seq (.block (Impl.MlKem.AArch64.Paired.init sb ss a b L.k))
    (.seq (Impl.MlKem.AArch64.Hybrid.squeeze3 L i)
      (.seq (.block Impl.MlKem.AArch64.Rej8.rejConsts) (initialCode oa ob w16)))

def beginRegs3 : List Reg := startRegs3 ++ [.x9, .x16] ++
  [.x0, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x22, .x23]

/-- A hashing pair's memory beyond `Paired.BeginInput`. -/
structure HashInput (L : KemLay) (p outA outB table e st : Addr) (s : State) : Prop where
  lay : SqLay L p e st s
  h25 : s.gpr .x25 = e
  h28 : s.gpr .x28 = st
  tS : (Region.mk table 4096).Disjoint (stR st)
  tF : (Region.mk table 4096).Disjoint (frame s.sp)
  aS : (polyRegion outA).Disjoint (stR st)
  bS : (polyRegion outB).Disjoint (stR st)
  aE : (polyRegion outA).Disjoint ⟨e, L.ekLen⟩
  bE : (polyRegion outB).Disjoint ⟨e, L.ekLen⟩

/-- The writes of a hashing pair. -/
def pairWrites3 (p a b st sp : Addr) : List Region := stepWrites p a b ++ [stR st, frame sp]

structure Begin3PostW (w16 : Bool) (L : KemLay) (A B : Spec.Sha3.State) (p a b c e st : Addr) (E : List Byte) (i : Nat)
    (s t : State) : Prop where
  keep : Keep beginRegs3 s t
  frame : Frame (pairWrites3 p a b st s.sp) s.mem t.mem
  saved : Noise.Saved p s t.mem
  progress : ProgressW w16 A B 3 p a b c t
  flag : (t.gpr .x6).toNat = if (accepted A 3).length = 256 ∧ (accepted B 3).length = 256 then 1 else 0
  hash : stateAt t.mem st = hstate E (3 * i + 3)
  ek : bytesAt t.mem e L.ekLen = E

theorem Context.frame3 {s t : State} {p a b c st sp : Addr} (h : Context p a b c s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hf : Frame [⟨p, 2048⟩, stR st, frame sp] s.mem t.mem)
    (tS : (Region.mk c 4096).Disjoint (stR st)) (tF : (Region.mk c 4096).Disjoint (frame sp)) :
    Context p a b c t := by
  refine ⟨by simpa only [hw] using h.scratch, by simpa only [hw] using h.outA,
    by simpa only [hw] using h.outB, h.farA, h.farB, h.apart, ?_, by simpa only [hr, hw] using h.readable,
    h.tableScratch, h.tableA, h.tableB⟩
  exact h.artifact.frame hf (by
    intro r hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl
    · exact h.tableScratch
    · exact tS
    · exact tF)

theorem begin3_ok {w16 : Bool} (L : KemLay) {s : State} {p seed outA outB table e st : Addr} {E : List Byte}
    {sb ss a b i oa ob : Nat}
    (hss : ss < 65536) (hsb : sb + 32 ≤ 32768) (h8b : sb % 8 = 0) (hoa : oa < 65536) (hob : ob < 65536)
    (h : Paired.BeginInput sb ss oa ob p seed outA outB table s) (hh : HashInput L p outA outB table e st s)
    (hb : 136 * (3 * i + 2) < L.ekLen) (h8 : L.ekLen % 8 = 0) (hlim : L.ekLen ≤ 4096)
    (hash : stateAt s.mem st = hstate E (3 * i)) (hE : bytesAt s.mem e L.ekLen = E) :
    WP isa (begin3Code L sb ss a b i oa ob w16) s
      (Begin3PostW w16 L (seedState s.mem seed a L.k) (seedState s.mem seed b L.k) p outA outB table e st E i s) := by
  have ctx := h.context
  have combined := WP.mono_syms (start3_ok (a := a) (b := b) L hss hsb h8b h.ptr h.seedPtr h.readable h.separate
    hh.lay hh.h25 hh.h28 hb h8 hlim hash hE)
    (R := fun u => WP isa (.seq (.block Impl.MlKem.AArch64.Rej8.rejConsts) (initialCode oa ob w16)) u
      (Begin3PostW w16 L (seedState s.mem seed a L.k) (seedState s.mem seed b L.k) p outA outB table e st E i s))
    (fun u ⟨ku, fu, svu, u19, pu, buA, buB, hu, eu⟩ sy => by
      have cu : Context p outA outB table u := Context.frame3 ctx ku.rd ku.wr fu hh.tS hh.tF
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
      have sub : ∀ {o n : Nat}, o + n ≤ 2048 → Region.Sub ⟨p + BitVec.ofNat 64 o, n⟩ ⟨p, 2048⟩ :=
        fun h => Offset.sub_base p h
      refine ⟨((ku.trans kv).trans ht'.keep).mono (by simp [beginRegs3,List.append_assoc]),
        ((fu.mono (by simp [startWrites, pairWrites3, stepWrites])).trans
          (fut.mono (fun r hr => List.mem_append_left _ hr))),svt,
        ⟨ctt,(ht'.keep.get .x19).trans v19,pt,?_,?_,?_,?_⟩,ht'.both,?_,?_⟩
      · simpa only [accepted,v28,h.outLeft] using ht'.first
      · simpa only [accepted,v28,h.outRight] using ht'.second
      · have hh := ht'.savedA
        rw [v19,v28,h.outLeft] at hh
        exact hh
      · have hh := ht'.savedB
        rw [v19,v28,h.outRight] at hh
        exact hh
      · rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame fut (fun r hr => by
          simp only [stepWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact hh.lay.dSP
          · exact hh.aS.symm
          · exact hh.bS.symm), hu]
      · rw [VG.Proof.MlKem.bytesAt_frame fut (fun r hr => by
          simp only [stepWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact hh.lay.dEP
          · exact hh.aE.symm
          · exact hh.bE.symm) (by omega), eu])
  exact WP.seq (WP.mono (WP.seq_iff.mp combined) fun u hu => WP.seq hu)

end VG.Proof.MlKem.AArch64.Hybrid
