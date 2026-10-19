module
public import VerifiedGarbage.Proof.Blowfish.X86.Ecb

import VerifiedGarbage.Proof.Blowfish.X86.KeyEnc
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Blowfish.X86.KeyP
import VerifiedGarbage.Proof.Blowfish.X86.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.TCB.X86.Target

/-!
# Blowfish on x86 (32-bit): key expansion

`expandKey_correct`: our caller's registers saved, the initial schedule
written, the key XORed into the P-array, the 521 encryptions, and the
registers restored.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86

open VG VG.X86 VG.Impl.Blowfish VG.Impl.Blowfish.X86 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-- The key, the schedule and the working space of `s`. -/
abbrev keyR (s : State) : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
abbrev kSchR (s : State) : Region := ⟨(arg s 2).setWidth 64, 4168⟩
abbrev kBufR (s : State) : Region := ⟨(arg s 3).setWidth 64, 64⟩

/-- What key expansion may assume: the key and the arguments readable, the
schedule and the working space writable, apart, none wrapping around, and a
valid key length. -/
structure KeyPre (s : State) : Prop where
  rd : s.rd = [keyR s, argR s]
  wr : s.wr = [kSchR s, kBufR s]
  ks : (keyR s).Disjoint (kSchR s)
  kb : (keyR s).Disjoint (kBufR s)
  sb : (kSchR s).Disjoint (kBufR s)
  as : (argR s).Disjoint (kSchR s)
  ab : (argR s).Disjoint (kBufR s)
  rs : (retR s).Disjoint (kSchR s)
  rb : (retR s).Disjoint (kBufR s)
  fKey : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  fSch : (arg s 2).toNat + 4168 ≤ 2 ^ 32
  fBuf : (arg s 3).toNat + 64 ≤ 2 ^ 32
  fsp : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  valid : validKey (arg s 1).toNat

/-- What key expansion guarantees. -/
def KeyPost (s t : State) : Prop :=
  abiPreserved s t ∧
    scheduleAt t.mem ((arg s 2).setWidth 64) = expandKey (bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)

/-- The argument `i` (of the first four) within the arguments' region. -/
theorem argR_contains (s : State) (hsp : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {i : Nat} (hi : i < 4) :
    (argR s).Contains (addr (s.gpr .esp) (4 + 4 * i)) 4 := by
  show Region.Contains ⟨addr (s.gpr .esp) 4, 16⟩ (addr (s.gpr .esp) (4 + 4 * i)) 4
  rw [addr_of_fit (by omega_arith), addr_of_fit (by omega_arith), ← Offset.add_add]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- Saving our caller's registers in the working space at `B`, its address the fourth argument. -/
theorem save_run (s : State) {B : BitVec 32} (bfit : B.toNat + 40 ≤ 2 ^ 32)
    (hA : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4) (hv : s.mem.readW (addr (s.gpr .esp) 16) 32 = B)
    (w : ∀ d, d + 4 ≤ 16 → InRegions s.wr (slot B d) 4) :
    WP isa (.block save) s fun t =>
      t.mem = savedMem s.mem B (s.gpr .ebx) (s.gpr .esi) (s.gpr .edi) (s.gpr .ebp) ∧ t.gpr .ebp = B := by
  unfold save savedMem
  brun [addr_slot bfit, hA, hv, w 0 (by decide), w 4 (by decide), w 8 (by decide), w 12 (by decide)]

theorem argR_sub (s : State) (hsp : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {i : Nat} (hi : i < 4) :
    Region.Sub ⟨addr (s.gpr .esp) (4 + 4 * i), 4⟩ (argR s) := by
  show Region.Sub ⟨addr (s.gpr .esp) (4 + 4 * i), 4⟩ ⟨addr (s.gpr .esp) 4, 16⟩
  rw [addr_of_fit (by omega_arith), addr_of_fit (by omega_arith)]
  exact Offset.sub _ (by omega_arith) (by omega_arith)

theorem expandKey_correct {s : State} (h : KeyPre s) : WP isa Impl.Blowfish.X86.expandKey s (KeyPost s) := by
  obtain ⟨hrd, hwr, ks, kb, sb, as, ab, rs, rb, fKey, fSch, fBuf, fsp, valid⟩ := h
  let K := arg s 2
  let B := arg s 3
  have eK : K.toNat = (arg s 2).toNat := rfl
  have eB : B.toNat = (arg s 3).toNat := rfl
  have hL := valid.1
  have hL' := valid.2
  have bfit : B.toNat + 40 ≤ 2 ^ 32 := by omega_arith
  have bR : kBufR s ∈ s.wr := by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have sR : kSchR s ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  have rA : ∀ i, i < 4 → InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * i)) 4 := fun i hi => by
    rw [hrd]; exact ⟨argR s, List.mem_cons_of_mem _ List.mem_cons_self, argR_contains s fsp hi⟩
  have argF : ∀ {m : Mem}, Frame [kSchR s, kBufR s] s.mem m → ∀ i, i < 4 →
      m.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 = arg s i := fun hf i hi =>
    hf.readW (r := argR s) (argR_contains s fsp hi) (fun r hr => (mem_two hr).elim (· ▸ as) (· ▸ ab))
      (by decide)
  let key := bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat
  unfold Impl.Blowfish.X86.expandKey initSchedule
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.eax, .ebp] (save_run s bfit (rA 3 (by decide)) rfl (fun d hd =>
    ⟨_, bR, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)) (by decide))
    fun u₁ ⟨⟨m₁, b₁⟩, k₁⟩ => ?_
  have F₁ : Frame [kSchR s, kBufR s] s.mem u₁.mem := by
    rw [m₁]
    refine (savedMem_frame s.mem B _ _ _ _).sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨kBufR s, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by decide)⟩
  have r12 : InRegions (u₁.rd ++ u₁.wr) (addr (u₁.gpr .esp) 12) 4 := by
    rw [keep_reads k₁, k₁.gpr (by decide)]; exact rA 2 (by decide)
  have v12 : u₁.mem.readW (addr (u₁.gpr .esp) 12) 32 = K := by
    rw [k₁.gpr (by decide)]; exact argF F₁ 2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.ebx] (Q := fun t => t.gpr .ebx = K + BitVec.ofNat 32 0 ∧ t.mem = u₁.mem)
    (by brun [r12, v12]) (by decide)) fun u₂ ⟨⟨b₂, m₂⟩, k₂⟩ => ?_
  refine WP.mono (initSchedule_steps u₂ fSch b₂
    (by rw [k₂.2.2, k₁.2.2]; exact ⟨_, sR, Region.contains_self _ _⟩) 1042 (by decide)) fun u₃ I₃ => ?_
  have k₃ : Keep [.eax, .ebp, .ebx, .ecx] s u₃ := (k₁.trans (k₂.trans I₃.keep)).mono (by decide)
  have F₃ : Frame [kSchR s, kBufR s] s.mem u₃.mem := by
    refine F₁.trans ?_
    rw [← m₂]; exact I₃.frame.mono (by simp)
  -- the key into the P-array
  have KE : KeyEnv (arg s 0) (arg s 1).toNat u₃ := by
    refine ⟨fun i hi => ?_, ?_, ?_, by omega_arith, hL', fKey, ?_, by rw [k₃.gpr (by decide)]; exact fsp⟩
    · rw [keep_reads k₃, k₃.gpr (by decide)]; exact rA i (by omega_arith)
    · rw [k₃.gpr (by decide)]; exact argF F₃ 0 (by decide)
    · rw [k₃.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact argF F₃ 1 (by decide)
    · rw [keep_reads k₃, hrd]; exact ⟨_, List.mem_cons_self, Region.contains_self _ _⟩
  have subP : Region.Sub ⟨K.setWidth 64 + BitVec.ofNat 64 4096, 72⟩ (kSchR s) := Offset.sub_base _ (by decide)
  apply WP.seq
  refine WP.mono (keyP_run KE (by rw [keep_reads k₃, k₃.gpr (by decide)]; exact rA 2 (by decide))
    (by rw [k₃.gpr (by decide)]; exact argF F₃ 2 (by decide)) fSch
    (by rw [k₃.2.2]; exact ⟨_, sR, Offset.contains_base _ (by decide) (by omega_arith)⟩) (ks.sub_right subP)
    (by rw [k₃.gpr (by decide)]
        exact (as.sub_left (Region.sub_prefix (by decide))).sub_right subP)) fun u₄ I₄ => ?_
  have k₄ : Keep [.eax, .ebp, .ebx, .ecx, .edx, .esi, .edi] s u₄ := (k₃.trans I₄.keep).mono (by decide)
  have F₃₄ : Frame [kSchR s, kBufR s] u₃.mem u₄.mem := I₄.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, subP⟩
  -- the schedule so far
  have hkey : bytesAt u₃.mem ((arg s 0).setWidth 64) (arg s 1).toNat = key :=
    bytesAt_frame F₃ fun c hc r hr => by
      rcases mem_two hr with rfl | rfl
      · exact ks _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
      · exact kb _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  have hP : ∀ i < 18, u₄.mem.readW (K.setWidth 64 + BitVec.ofNat 64 (4096 + 4 * i)) 32 =
      initial.getD i 0 ^^^ Spec.Blowfish.keyWord key i := fun i hi => by
    rw [I₄.done i hi, hkey, table_P I₃.bytes hi]
  have hS : ∀ o < 4096, u₄.mem (K.setWidth 64 + BitVec.ofNat 64 o) = initByte o := fun o ho => by
    rw [I₄.frame _ fun r hr => ?_, I₃.bytes o (by omega_arith)]
    simp only [List.mem_singleton] at hr; subst hr
    exact (Offset.disjoint _ (d := o) (n := 1) (e := 4096) (k := 72) (by omega_arith) (by omega_arith) (by decide)) _
      (Region.contains_self _ _)
  have hK : scheduleAt u₄.mem (K.setWidth 64) = keyed key := keyed_of_mem hS hP
  -- the halves zeroed
  have k₁₄ : Keep [.ebx, .ecx, .eax, .edx, .esi, .edi] u₁ u₄ := ((k₂.trans I₃.keep).trans I₄.keep).mono (by decide)
  have b₄ : u₄.gpr .ebp = B := (k₁₄.gpr (by decide)).trans b₁
  have w16 : InRegions u₄.wr (slot B 16) 4 := by
    rw [k₄.2.2]; exact ⟨_, bR, Offset.contains_base _ (by decide) (by omega_arith)⟩
  have w20 : InRegions u₄.wr (slot B 20) 4 := by
    rw [k₄.2.2]; exact ⟨_, bR, Offset.contains_base _ (by decide) (by omega_arith)⟩
  apply WP.seq
  refine WP.mono (WP.keep [.eax] (Q := fun t => t.mem = (u₄.mem.writeW (slot B 16) (0#32)).writeW (slot B 20)
      (0#32)) (by brun [b₄, addr_slot bfit, w16, w20]) (by decide)) fun u₅ ⟨m₅, k₅⟩ => ?_
  have F₄₅ : Frame [⟨slot B 16, 8⟩] u₄.mem u₅.mem := by
    rw [m₅]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _
      (Offset.contains (e := 16) (k := 8) (d := 16) (n := 4) _ (by decide) (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains (e := 16) (k := 8) (d := 20) (n := 4) _ (by decide) (by decide)
        (by decide))
  have F₅ : Frame [kSchR s, kBufR s] s.mem u₅.mem := (F₃.trans F₃₄).trans (F₄₅.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub_base _ (by decide)⟩)
  -- the encryptions
  have EE : EncEnv K B s := by
    refine ⟨fSch, fBuf, ⟨_, sR, Region.contains_self _ _⟩, ⟨_, bR, Region.contains_self _ _⟩, sb,
      rA 2 (by decide), rfl, ?_, ?_⟩
    · exact as.symm.sub_right (argR_sub s fsp (i := 2) (by decide))
    · exact ab.symm.sub_right (argR_sub s fsp (i := 2) (by decide))
  have k₅' : Keep [.eax, .ebp, .ebx, .ecx, .edx, .esi, .edi] s u₅ := (k₄.trans k₅).mono (by decide)
  have I₅ : EncInv key K B s 0 u₅ := by
    refine ⟨by decide, k₅'.gpr (by decide), (k₅.gpr (by decide)).trans b₄, ?_, ?_, ?_, F₅, k₅'.2.1, k₅'.2.2⟩
    · rw [scheduleAt_eq_of_frame _ F₄₅ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact sb.sub_right (Offset.sub_base _ (by decide))), hK, ksIter_zero]
    · rw [m₅, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self32, Mem.readW_writeW_self32, ksIter_zero]; rfl
    · have S₁ : Saved u₁.mem B s := by rw [m₁]; exact saved_savedMem s.mem B s
      refine S₁.frame (rs := [kSchR s, ⟨slot B 16, 8⟩]) ?_ fun r hr => ?_
      · rw [← m₂]
        refine ((I₃.frame.mono (by simp)).trans (I₄.frame.sub fun r hr => ?_)).trans (F₄₅.mono (by simp))
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, subP⟩
      · rcases mem_two hr with rfl | rfl
        · exact sb.symm.sub_left (Region.sub_prefix (by decide))
        · exact Offset.base_disjoint _ (by decide) (by omega_arith)
  apply WP.seq
  refine WP.mono (encryptP_run EE I₅) fun u₆ I₆ => ?_
  apply WP.seq
  refine WP.mono (encryptS_run EE I₆) fun u₇ I₇ => ?_
  have hr : ∀ d, d + 4 ≤ 16 → InRegions (u₇.rd ++ u₇.wr) (slot B d) 4 := fun d hd => by
    rw [I₇.rd, I₇.wr]; exact region_in (EE.wB rfl (by omega_arith))
  refine WP.mono (WP.keep [.ebx, .esi, .edi, .ebp] (restore_run u₇ s I₇.ebp bfit hr I₇.saved) (by
      decide))
    fun t ⟨⟨tb, ts, td, tp, tm⟩, tk⟩ => ⟨⟨fun r hr => ?_, ?_⟩, by rw [tm, I₇.sched, expandKey_eq]⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [tb, ts, td, tp, (tk.gpr (by decide)).trans I₇.esp]
  · rw [tm]
    refine I₇.frame.readW (r := retR s) (contains_pre _ (by decide)) (fun r hr => ?_) (by decide)
    rcases mem_two hr with rfl | rfl
    exacts [rs, rb.sub_right (Region.sub_prefix (by decide))]

end VG.Proof.Blowfish.X86
