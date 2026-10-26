module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Tables
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Matrix
meta import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Tail
import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# The hashing encapsulation: its constant tables

The constant tables kept apart from every write, the 128 bytes below the stack
pointer the x3 calls use included (`TStk`, `WP.tables128`), for the
correctness of the hashing encapsulation (`Kem16/Encaps.lean`: the first phase,
`startH_ok`; the matrix, `matrixH_ok`; `H` and `G`, `tailH_ok`; then noise,
`u`, `v` and the epilogue).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Encaps
open VG.Proof.MlKem.AArch64.Optimized
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Spec.MlKem
open VG.Proof.MlKem

variable {P : KemLay} {prf : Nat→Nat→Prog isa}

/-- The constant tables, apart from the 128 bytes below the stack pointer. -/
structure TStk (s : State) : Prop where
  shuffle : (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint (frame s.sp)
  gamma : (Region.mk (s.syms "VG_MLKEM_GAMMA") 512).Disjoint (frame s.sp)
  forward : (Region.mk (s.syms "VG_MLKEM_NTT16_ZETAS") 512).Disjoint (frame s.sp)
  inverse : (NttR.fastInvRegion s).Disjoint (frame s.sp)
  fast : (NttR.fastRegion s).Disjoint (frame s.sp)

theorem TStk.of {s t : State} (h : TStk s) (hs : t.syms = s.syms) (hp : t.sp = s.sp) : TStk t := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [NttR.fastRegion, NttR.fastInvRegion, NttR.sRegion, hs, hp]
  exacts [h.shuffle, h.gamma, h.forward, h.inverse, h.fast]

theorem tables_frame128 {s t : State} (h : Tables s) (hk : TStk s)
    (hs : t.syms=s.syms) (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hp : t.sp=s.sp)
    (hf : Frame (s.wr++[frame s.sp]) s.mem t.mem) : Tables t := by
  have ext {r : Region} (a : ∀q∈s.wr,r.Disjoint q) (b : r.Disjoint (frame s.sp)) :
      ∀q∈s.wr++[frame s.sp],r.Disjoint q := by
    intro q hq; rcases List.mem_append.mp hq with hq|hq
    · exact a q hq
    · rw [List.mem_singleton.mp hq]; exact b
  have sh := ext h.shuffleApart hk.shuffle
  have ga := ext h.gammaApart hk.gamma
  have fw := ext h.transforms.forward.2.2 hk.forward
  have iv := ext h.transforms.inverse.2.2 hk.inverse
  have fa := ext h.transforms.fast.2.2 hk.fast
  refine ⟨?_,by simpa only [hs,hr,hw] using h.shuffleRead,
    by simpa only [hs,hw] using h.shuffleApart,
    by simpa only [hs,hp] using h.shuffleStack,?_,
    by simpa only [hs,hr,hw] using h.gammaRead,
    by simpa only [hs,hw] using h.gammaApart,
    by simpa only [hs,hp] using h.gammaStack,
    ⟨⟨?_,by simpa only [hs,hr,hw] using h.transforms.forward.2.1,
      by simpa only [hs,hw] using h.transforms.forward.2.2⟩,
     h.transforms.inverse.frameFar hs hr hw hf iv,
     by simpa only [hs,hp] using h.transforms.forwardStack,
     by simpa only [NttR.fastInvRegion,NttR.sRegion,hs,hp] using h.transforms.inverseStack,
     h.transforms.fast.frameFar hs hr hw hf fa,
     by simpa only [NttR.fastRegion,NttR.sRegion,hs,hp] using h.transforms.fastStack⟩⟩
  · rw [hs]; exact h.shuffle.frame hf sh
  · rw [hs]; intro i hi
    rw [hf.readW (r:=⟨s.syms "VG_MLKEM_GAMMA",512⟩)
      (Offset.contains_base _ (by omega) (by omega)) ga (by decide)]
    exact h.gamma i hi
  · rw [hs]; intro i hi
    rw [hf.readW (r:=⟨s.syms "VG_MLKEM_NTT16_ZETAS",512⟩)
      (Offset.contains_base _ (by omega) (by omega)) fw (by decide)]
    exact h.transforms.forward.1 i hi

theorem WP.tables128 {s : State} {c : Prog isa} {Q : State→Prop}
    (h : WP isa c s Q) (ht : Tables s) (hk : TStk s) (hn : c.aarch64Depth≤8) :
    WP isa c s fun t=>Q t ∧ Tables t := by
  obtain ⟨tr,t,he,hq⟩:=h
  refine ⟨tr,t,he,hq,?_⟩
  obtain ⟨hr,hw,hsp⟩:=VG.AArch64.Exec.rdwr he
  have hf := Frame.below_mono (VG.AArch64.Exec.frameSp he (by omega)) (b:=128) (by omega) (by decide)
  exact tables_frame128 ht hk (VG.AArch64.Exec.syms he) hr hw hsp hf

theorem mb_bW3 {L : Layout} {s₀ : State} (hp : Pre P L s₀) (hk : Stk128 P L s₀) :
    ∀ r ∈ bW3 P L s₀, (R (kA s₀) L.sc MB 32).Disjoint r := by
  have hw := hp.wf
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact sdisj hp (by lom) (by lom) (by lom)
    · exact sdisj hp (by lom) (by lom) (by lom)
    · exact sdisj hp (by lom) (by lom) (by lom)
    · exact below_R hp hp.scb (hp.fs (by lom))
  · rcases mem2' hr with rfl | rfl
    · exact sdisj hp (by lom) (by lom) (by lom)
    · exact (hk.R hp.scb (hp.fs (by lom))).symm

/-- `ek`, argument 0 of encapsulation. -/
def ekM (P : KemLay) : Msg := ⟨Impl.MlKem.AArch64.Hybrid.ekSrc P, 0, 0⟩

theorem ekM_base (s₀ : State) : ((ekM P).reg s₀).base = kA s₀ 0 := ptr_zero _

theorem ekM_ok {s₀ : State} (hp : Pre P (enL P) s₀) (hk : Stk128 P (enL P) s₀)
    (hs : SrcOk (Impl.MlKem.AArch64.Hybrid.ekSrc P)) : MsgOk P (enL P) (ekM P) s₀ := by
  have hw := hp.wf
  have ek0 : ∀ (o' l' : Nat), o' + l' ≤ SV P + 48 →
      ((ekM P).reg s₀).Disjoint (R (kA s₀) (enL P).sc o' l') := fun o' l' f' =>
    hp.args.rdisj (show 0 < 5 by decide) hp.scb (by simp [enL, ekM, Impl.MlKem.AArch64.Hybrid.ekSrc])
      (hp.fs f') (.inr (.inr hp.scw)) (.inl (by simp [enL, Layout.sc, ekM]))
  refine ⟨hs, fun s h => ?_, fun s h => ?_, (ek0 0 200 (by lom)).symm, fun r hr => ?_,
    ek0 SS 2048 (by lom), fun e he => ek0 _ _ (by lom), ?_⟩
  · show s.gpr .x25 + BitVec.ofNat 64 0 = _
    rw [ekM_base, h.x25, ptr_zero]; rfl
  · exact cov_r hp h (show 0 < 5 by decide) (by simp [enL, ekM, Impl.MlKem.AArch64.Hybrid.ekSrc])
  · rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact ek0 _ _ (by lom)
    · exact ek0 _ _ (by lom)
    · exact ek0 _ _ (by lom)
    · exact below_R hp (show 0 < 5 by decide) (by simp [enL, ekM, Impl.MlKem.AArch64.Hybrid.ekSrc])
  · exact hk.R (show 0 < 5 by decide) (by simp [enL, ekM, Impl.MlKem.AArch64.Hybrid.ekSrc])

end VG.Proof.MlKem.AArch64.Hybrid
