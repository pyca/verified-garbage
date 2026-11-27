module

public import VerifiedGarbage.Impl.Sm4.RISCV64.ExpandKey
public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Sm4.RISCV64.KeyVerified
import VerifiedGarbage.Proof.Sm4.RISCV64.Lit
import VerifiedGarbage.Proof.Sm4.RISCV64.Ecb
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Impl.Sm4.RISCV64.ExpandKey
meta import VerifiedGarbage.Spec.Sm4.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Sm4.RISCV64.KeyVerified
meta import VerifiedGarbage.Proof.Sm4.RISCV64.Lit
meta import VerifiedGarbage.Proof.Sm4.RISCV64.Ecb
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Interleave
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Call
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch

import VerifiedGarbage.Proof.Sm4.Layout
public import VerifiedGarbage.Proof.Sm4.Scratch
public import VerifiedGarbage.Impl.StackScratch.RISCV64
import VerifiedGarbage.Proof.Sm4.Common
meta import VerifiedGarbage.Proof.Sm4.Common
import VerifiedGarbage.Proof.Sm4.Planes
meta import VerifiedGarbage.Proof.Sm4.Planes
import VerifiedGarbage.Proof.Sm4.RISCV64.Round
meta import VerifiedGarbage.Proof.Sm4.RISCV64.Round
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Sharing the RISC-V SM4 key schedule without additional stack space -/

namespace VG.Proof.Sm4.RISCV64.KeyCall

open VG VG.RISCV64 VG.RISCV64.Straight VG.Impl.Sm4.RISCV64 VG.Proof.Sm4.RISCV64
open VG.Impl.Aes.RISCV64 (sb t0 t1 t2 m movR)
open VG.Impl.Sm4 (fkWord)
open VG.Proof.Sm4 (expandKeyRISCV64 readW64_bit)

structure Loaded (s0 s : State) : Prop where
  base : s.gpr sb = s0.gpr .a2
  schedule : s.gpr .a1 = s0.gpr .a1
  tail : ∀ c < 16, ∀ h < 2, slotW s (tailAt c h) =
    s0.mem.readW (s0.gpr .a0 + BitVec.ofNat 64 (8*h)) 64 ^^^ fkWord h
  saved : Saved s0 (s0.gpr .a2) s.mem
  frame : Frame [⟨s0.gpr .a2,8*slots⟩] s0.mem s.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  link : s.gpr .a0 = s0.gpr .ra

theorem prefix_ok {s0 : State} (hp : expandKeyRISCV64.pre s0) :
    ∃ s, runBlock isa keyPrefix s0 = some s ∧ Loaded s0 s := by
  obtain ⟨hrd,hwr,_dKS,dKB,_dSB,_fitK,_fitS,_fitB,hal⟩ := hp
  let b := s0.gpr .a2
  let K := s0.gpr .a0
  have hw : (⟨b,8*slots⟩ : Region) ∈ s0.wr := by
    rw [hwr]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  obtain ⟨s1,e1,hb1,g1,sv1,_v1,f1,rd1,wr1⟩ := prologue_ok []
    (by intro kv h; cases h) (by decide) (b := b) rfl hw hal
  have kp1 : s1.gpr .a0 = K := g1 _ (by decide) (by decide) (by decide)
  have keyIn (s : State) (rd : s.rd = s0.rd) (kp : s.gpr .a0 = K) (h : Nat) (hh : h < 2) :
      ∀ i < 2, InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 (8*h+4*i)) 4 := by
    intro i hi
    rw [kp]
    refine ⟨⟨K,16⟩,List.mem_append_left _ ?_,VG.Offset.contains_base _ (by omega_using [hh,hi]) (by omega_using [hh,hi])⟩
    rw [rd,hrd]
    exact List.mem_singleton_self _
  have keyRead (mm : Mem) (f : Frame [⟨b,8*slots⟩] s0.mem mm) (h : Nat) (hh : h < 2) :
      mm.readW (K+BitVec.ofNat 64 (8*h)) 64 = s0.mem.readW (K+BitVec.ofNat 64 (8*h)) 64 :=
    f.readW (r := ⟨K,16⟩) (VG.Offset.contains_base _ (by omega_using [hh]) (by omega_using [hh]))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKB) (by decide)
  obtain ⟨s2,e2,v2,k2,g2,rd2,wr2,f2⟩ := loadHalf_ok 0 (by decide) hb1 (by rw [wr1]; exact hw) hal
    (keyIn s1 rd1 kp1 0 (by decide))
  have hb2 : s2.gpr sb = b := (g2 _ (by decide) (by decide) (by decide) (by decide)).trans hb1
  have kp2 : s2.gpr .a0 = K := (g2 _ (by decide) (by decide) (by decide) (by decide)).trans kp1
  obtain ⟨s3,e3,v3,k3,g3,rd3,wr3,f3⟩ := loadHalf_ok 1 (by decide) hb2 (by rw [wr2,wr1]; exact hw) hal
    (keyIn s2 (rd2.trans rd1) kp2 1 (by decide))
  have hb3 : s3.gpr sb = b := (g3 _ (by decide) (by decide) (by decide) (by decide)).trans hb2
  obtain ⟨s4,e4,a4,o4,mem4,rd4,wr4⟩ := movR_ok s3 .a0 .ra
  have hb4 : s4.gpr sb = b := (o4 _ (by decide)).trans hb3
  have stail (h : Nat) (hh : h < 2) (c : Nat) (hc : c < 16) :
      slotW s3 (tailAt c h) = s0.mem.readW (K+BitVec.ofNat 64 (8*h)) 64 ^^^ fkWord h := by
    have split : h = 0 ∨ h = 1 := by omega_using [hh]
    rcases split with rfl | rfl
    · rw [k3 _ (by have h := tailAt_lt hc (show 0 < 2 by decide); rw [tableSlot_eq] at h; rw [slots_eq]; omega_using [h])
        (fun c' _ he => by simp only [tailAt] at he; omega_using [he]),v2 c hc,kp1,keyRead _ f1 0 (by decide)]
    · rw [v3 c hc,kp2,keyRead _ (f1.trans f2) 1 (by decide)]
  have saved : Saved s0 b s3.mem := by
    intro i hi
    have hk : savedSlot+i < slots := by rw [savedSlot_eq,slots_eq]; omega_using [hi]
    have hn (h : Nat) (hh : h < 2) : ∀ c < 16, savedSlot+i ≠ tailAt c h := by
      intro c hc eq
      have := tailAt_lt hc hh
      rw [tableSlot_eq] at this
      rw [savedSlot_eq] at eq
      omega_using [this,eq]
    have eq := (k3 _ hk (hn 1 (by decide))).trans (k2 _ hk (hn 0 (by decide)))
    simp only [slotW,hb3,hb1] at eq
    exact eq.trans (sv1 i hi)
  refine ⟨s4,?_,hb4,?_,?_,?_,?_,by rw [rd4,rd3,rd2,rd1],by rw [wr4,wr3,wr2,wr1],?_⟩
  · simp only [setSlots,List.flatMap_nil,List.append_nil] at e1
    rw [keyPrefix,Interleave.runBlock_append,Interleave.runBlock_append,Interleave.runBlock_append,
      e1,Option.bind_some,e2,Option.bind_some,e3,Option.bind_some,e4]

  · rw [o4 _ (by decide),g3 _ (by decide) (by decide) (by decide) (by decide),
      g2 _ (by decide) (by decide) (by decide) (by decide),g1 _ (by decide) (by decide) (by decide)]
  · intro c hc h hh
    have eq : slotW s4 (tailAt c h) = slotW s3 (tailAt c h) := by
      simp only [slotW,mem4,hb4,hb3]
    rw [eq]
    exact stail h hh c hc
  · rw [mem4]
    exact saved
  · rw [mem4]
    exact (f1.trans f2).trans f3
  · rw [a4,g3 _ (by decide) (by decide) (by decide) (by decide),
      g2 _ (by decide) (by decide) (by decide) (by decide),g1 _ (by decide) (by decide) (by decide)]



def coreHead : List Instr := setSlots (keyMasks ++ bsKs) ++ ckTable ++ toBs ++
  slotAddr .a4 tableEnd ++ slotAddr kr tableSlot

theorem coreHead_ok {s0 s : State} (hp : expandKeyRISCV64.pre s0) (hl : Loaded s0 s) :
    ∃ u, runBlock isa coreHead s = some u ∧
      EkInv s0 (s0.gpr .a2) (s0.gpr .a1) (Spec.Sm4.blockAt s0.mem (s0.gpr .a0)) 0 u := by
  obtain ⟨_rd0,wr0,_dKS,_dKB,_dSB,_fitK,_fitS,fitB,hal⟩ := hp
  let b := s0.gpr .a2
  have hw : (⟨b,8*slots⟩ : Region) ∈ s0.wr := by
    rw [wr0]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  obtain ⟨s1,e1,v1,k1,g1,rd1,wr1,f1⟩ := setSlots_ok (keyMasks ++ bsKs) hl.base
    (by rw [hl.wr]; exact hw) hal
    (fun kv hkv => by have h := masks_lt kv hkv; rw [tableSlot_eq]; omega_using [h]) (by decide)
  have hb1 : s1.gpr sb = b := (g1 _ (by decide) (by decide)).trans hl.base
  obtain ⟨s2,e2,v2,g2,rd2,wr2,f2⟩ := ckTable_ok hb1 (by rw [wr1,hl.wr]; exact hw) hal
  have hb2 : s2.gpr sb = b := (g2 _ (by decide) (by decide) (by decide)).trans hb1
  have notMask (k : Nat) (hk : 51 ≤ k) : k ∉ (keyMasks ++ bsKs).map (·.1) := by
    intro hin
    obtain ⟨kv,hkv,eq⟩ := List.mem_map.mp hin
    have h := (mask_range hkv).2
    rw [eq] at h
    omega_using [hk,h]
  have notCk (k : Nat) (hk : k < tableSlot ∨ tableEnd ≤ k) (hk' : k < slots) :
      slotW s2 k = slotW s1 k := by
    simp only [slotW,hb2,hb1]
    refine f2.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr
    subst hr
    rw [wordAddr]
    rw [tableSlot_eq,tableEnd_eq,slots_eq] at *
    exact VG.Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)
  have kc : KeyCtx s2 Spec.Sm4.ck :=
    { scr := by rw [hb2,wr2,wr1,hl.wr]; exact hw
      fit := by rw [hb2]; exact fitB
      al := by rw [hb2]; exact hal
      keys := fun e he => (VG.Proof.Sm4.planeOf_rel (Spec.Sm4.ck e)).congr fun j hj => by
        rw [hb2]
        exact v2 e he j hj }
  have masks : MasksOk s2 := fun kv hkv => by
    have h := mask_range hkv
    rw [notCk _ (Or.inl (by rw [tableSlot_eq]; omega_using [h]))
      (by rw [slots_eq]; omega_using [h]),v1 kv hkv]
  have tail2 : ∀ c < 16, ∀ h < 2, slotW s2 (tailAt c h) =
      s0.mem.readW (s0.gpr .a0 + BitVec.ofNat 64 (8*h)) 64 ^^^ fkWord h := by
    intro c hc h hh
    have hk := tailAt_lt hc hh
    have low : 51 ≤ tailAt c h := by simp only [tailAt,tailSlot_eq]; omega_using []
    rw [notCk _ (Or.inl hk) (by rw [slots_eq,tableSlot_eq] at *; omega_using [hk]),
      k1 _ (by rw [slots_eq,tableSlot_eq] at *; omega_using [hk]) (notMask _ low)]
    exact hl.tail c hc h hh
  obtain ⟨s3,e3,c3,_kr3,X3⟩ := toBs_step kc (Ctx.refl masks)
  obtain ⟨s4,e4,r4,o4,m4,rd4,wr4⟩ := slotAddr_ok s3 .a4 tableEnd
  obtain ⟨s5,e5,r5,o5,m5,rd5,wr5⟩ := slotAddr_ok s4 kr tableSlot
  have hb3 : s3.gpr sb = b := c3.base.trans hb2
  have hb5 : s5.gpr sb = b := by rw [o5 _ (by decide),o4 _ (by decide),hb3]
  have mem5 : s5.mem = s3.mem := m5.trans m4
  have keyBits : ∀ h < 2, ∀ t < 8, ∀ j < 8,
      (s0.mem.readW (s0.gpr .a0 + BitVec.ofNat 64 (8*h)) 64).getLsbD (8*t+j) =
      ((Spec.Sm4.blockAt s0.mem (s0.gpr .a0)).getD (8*h+t) 0).getLsbD j := by
    intro h hh t ht j hj
    rw [readW64_bit _ _ ht hj,VG.Proof.Sm4.blockAt_getD _ _ (by omega_using [hh,ht]),addr_add]
  have st : StRel s5 (fun _ => quads .key Spec.Sm4.ck 0
      (keyInit (Spec.Sm4.blockAt s0.mem (s0.gpr .a0)))) := fun w hw =>
    ((X3 w hw).congr fun j _ => by simp only [planes,slotW,mem5,hb5,hb3]).congr_right fun c hc =>
      (keyInit_rel keyBits tail2 c hc w hw).symm
  refine ⟨s5,?_,hb5,?_,?_,?_,?_,?_,st,fun i hi => by omega_using [hi],?_,?_,
    by rw [rd5,rd4,c3.rd,rd2,rd1,hl.rd],by rw [wr5,wr4,c3.wr,wr2,wr1,hl.wr]⟩
  · rw [coreHead,Interleave.runBlock_append,Interleave.runBlock_append,Interleave.runBlock_append,
      Interleave.runBlock_append,e1,Option.bind_some,e2,Option.bind_some,e3,Option.bind_some,e4,Option.bind_some,e5]
  · rw [o5 _ (by decide),o4 _ (by decide),c3.keep _ (by decide) (by decide),
      g2 _ (by decide) (by decide) (by decide),g1 _ (by decide) (by decide),hl.schedule]
    exact (BitVec.add_zero _).symm
  · rw [o5 _ (by decide),r4,hb3]
  · rw [AtEntry,r5,o4 _ (by decide),hb3]
    simp
    rfl
  · have kk := kc.of_ctx c3
    exact ⟨by rw [wr5,wr4,hb5,← hb3]; exact kk.scr,
      by rw [hb5,← hb3]; exact kk.fit,by rw [hb5,← hb3]; exact kk.al,
      fun e he => by rw [hb5,← hb3,mem5]; exact kk.keys e he⟩
  · intro kv hkv
    simp only [slotW,mem5,hb5,← hb3]
    exact c3.masks kv hkv
  · intro i hi
    have hk : savedSlot+i < slots := by rw [savedSlot_eq,slots_eq]; omega_using [hi]
    have eq3 : slotW s3 (savedSlot+i) = slotW s2 (savedSlot+i) := by
      simp only [slotW,hb3,hb2]
      refine c3.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr
      subst hr
      rw [hb2,wordAddr]
      exact VG.Offset.disjoint_base _ (by rw [tableSlot_eq,savedSlot_eq]; omega_using [])
        (by rw [savedSlot_eq]; omega_using [hi])
    have eq2 : slotW s2 (savedSlot+i) = slotW s (savedSlot+i) := by
      rw [notCk _ (Or.inr (by rw [tableEnd_eq,savedSlot_eq]; omega_using [])) hk,
        k1 _ hk (notMask _ (by rw [savedSlot_eq]; omega_using []))]
    show s5.mem.readW (wordAddr b (savedSlot+i)) 64 = _
    rw [mem5,← hl.saved i hi]
    have ee := eq3.trans eq2
    simpa only [slotW,hb3,hl.base] using ee
  · rw [mem5]
    have fm : Frame [⟨b,8*slots⟩] s.mem s1.mem := f1.sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_,List.mem_singleton_self _,Region.sub_prefix (by rw [tableSlot_eq,slots_eq]; decide)⟩)
    have fk : Frame [⟨b,8*slots⟩] s1.mem s2.mem := f2.sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_,List.mem_singleton_self _,VG.Offset.sub_base b (by rw [tableSlot_eq,slots_eq]; decide)⟩)
    have ft : Frame [⟨b,8*slots⟩] s2.mem s3.mem := c3.frame.sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_,List.mem_singleton_self _,?_⟩
      rw [hb2]
      exact Region.sub_prefix (by rw [tableSlot_eq,slots_eq]; decide))
    exact (((hl.frame.trans fm).trans fk).trans ft).mono (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self)


theorem Loaded.callEntry {s0 s : State} (h : Loaded s0 s) : Loaded s0 s.callEntry := by
  refine ⟨?_,?_,?_,h.saved,h.frame,h.rd,h.wr,?_⟩
  · rw [State.callEntry_gpr _ (by decide)]; exact h.base
  · rw [State.callEntry_gpr _ (by decide)]; exact h.schedule
  · intro c hc j hj
    simpa only [slotW,State.callEntry_mem,State.callEntry_gpr _ (show sb ∉ linkRegs by decide)] using h.tail c hc j hj
  · rw [State.callEntry_gpr _ (by decide)]; exact h.link

theorem core_wp {s0 s : State} (hp : expandKeyRISCV64.pre s0) (hl : Loaded s0 s) :
    WP isa expandKeyCore s (EkInv s0 (s0.gpr .a2) (s0.gpr .a1)
      (Spec.Sm4.blockAt s0.mem (s0.gpr .a0)) 8) := by
  obtain ⟨u,e,hi⟩ := coreHead_ok hp hl
  obtain ⟨_,hw,_,_,dsb,_,fs,fb,al⟩ := hp
  have pre : EkPre s0 (s0.gpr .a2) (s0.gpr .a1) :=
    ⟨by rw [hw]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _),
     by rw [hw]; exact List.mem_cons_self,dsb,fb,fs,al⟩
  exact WP.seq (WP.of_runBlock ⟨u,e,ekLoop_wp pre hi⟩)

def coreWrites : List Reg := expandKeyWrites.filter (· != .a0)

theorem called_correct (s0 : State) (hp : expandKeyRISCV64.pre s0) :
    ∃ t u, Exec isa expandKeyCalled s0 t u ∧ abiPreserved s0 u ∧ expandKeyRISCV64.post s0 u := by
  obtain ⟨s,e,hl⟩ := prefix_ok hp
  obtain ⟨tc,v,ec,hi,hk⟩ := WP.keep coreWrites (core_wp hp hl.callEntry) (by lit_decide) (by rfl)
  have ret : isa.ret s.callEntry v = some v := by
    simp only [isa,VG.RISCV64.ret]
    rw [hk.gpr (r := .ra) (by decide)]
    simp
  have call : Exec isa (.call "vg_sm4_expand_key_shared" expandKeyCore) s tc v :=
    by simpa only [isa,List.map_nil,List.nil_append,List.append_nil] using Exec.call (name := "vg_sm4_expand_key_shared") (call_callEntry s) ec ret
  obtain ⟨w,ew,ra,go,mm,rd,wr⟩ := movR_ok v .ra .a0
  have hw : (⟨s0.gpr .a2,8*slots⟩ : Region) ∈ w.wr := by
    rw [wr,hi.wr,hp.2.1]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have wb : w.gpr sb = s0.gpr .a2 := (go _ (by decide)).trans hi.base
  obtain ⟨u,eu,gu,ku,mu,_,_⟩ := restore_ok hw wb hp.2.2.2.2.2.2.2.2 (by rw [mm]; exact hi.saved)
  have ep : runBlock isa (movR .ra .a0 :: restoreRegs) v = some u := by
    rw [show movR .ra .a0 :: restoreRegs = [movR .ra .a0] ++ restoreRegs from rfl,
      Interleave.runBlock_append,ew,Option.bind_some,eu]
  obtain ⟨te,z,eup,hz⟩ := WP.of_runBlock (M := isa) (Q := fun z => z = u) ⟨u,ep,rfl⟩
  subst z
  obtain ⟨tp,z,ep,hz⟩ := WP.of_runBlock (M := isa) (Q := fun z => z = s) ⟨s,e,rfl⟩
  subst z
  have ex : Exec isa expandKeyCalled s0 (tp ++ (tc ++ te)) u :=
    .seq ep (.seq call eup)
  refine ⟨_,u,ex,⟨?_,Exec.sp ex,?_⟩,?_⟩
  · intro r hr
    simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [gu 0 (by decide),gu 1 (by decide),gu 2 (by decide),gu 3 (by decide),
      gu 4 (by decide),gu 5 (by decide),gu 6 (by decide),gu 7 (by decide),
      gu 8 (by decide),gu 9 (by decide),gu 10 (by decide),gu 11 (by decide)]
  · rw [ku _ (by decide) (by decide),ra,hk.gpr (r := .a0) (by decide),
      State.callEntry_gpr _ (by decide),hl.link]
  · show Spec.Sm4.scheduleAt u.mem (s0.gpr .a1) = _
    rw [expandKey_eq]
    apply Vector.ext
    intro i ih
    apply BitVec.eq_of_getLsbD_eq
    intro k kh
    rw [show k = 8*(k/8)+k%8 by omega_arith,
      VG.Proof.Sm4.getLsbD_scheduleAt _ _ ih (by omega_arith) (by omega_arith),
      Vector.getElem_ofFn,mu,mm]
    exact hi.sched i (by omega_arith) _ (by omega_arith) _ (by omega_arith)

public theorem called_verified :
    Verified target expandKeyCalled (Proof.Sm4.expandKeyScratchContract abi slots) :=
  Verified.of_correct called_correct
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0,.a1,.a2]) expandKeyTaint_agree (by taint_decide)) (by
      sig_implies [Proof.Sm4.expandKeyScratchContract,Proof.Sm4.expandKeyScratchSig,Proof.Sm4.expandKeyPost,
        expandKeyRISCV64,abi,argRegs,slots,savedSlot,tableEnd,tableSlot]
        [expandKeySat] using expandKeySat)

public theorem framed_verified :
    Verified target (Impl.StackScratch.RISCV64.withStackScratchWiped 3168 .a2 396 expandKeyCalled)
      (Spec.Sm4.expandKeyContract abi 3168) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.Sm4.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 396) (post := Proof.Sm4.expandKeyPost abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 3168) (words := 396) called_verified (by decide) (by decide) (by decide)
    (Proof.Sm4.expandKeyPostOut_local _) expandKeyFrameSat_pre

end VG.Proof.Sm4.RISCV64.KeyCall
