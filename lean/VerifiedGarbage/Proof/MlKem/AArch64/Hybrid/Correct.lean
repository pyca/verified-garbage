module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Tables
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Matrix
meta import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Start
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Tail

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
  inverse : (Region.mk (s.syms "VG_MLKEM_INTT16_ZETAS") 512).Disjoint (frame s.sp)

theorem TStk.of {s t : State} (h : TStk s) (hs : t.syms = s.syms) (hp : t.sp = s.sp) : TStk t := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hs, hp]
  exacts [h.shuffle, h.gamma, h.forward, h.inverse]

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
  refine ⟨?_,by simpa only [hs,hr,hw] using h.shuffleRead,
    by simpa only [hs,hw] using h.shuffleApart,
    by simpa only [hs,hp] using h.shuffleStack,?_,
    by simpa only [hs,hr,hw] using h.gammaRead,
    by simpa only [hs,hw] using h.gammaApart,
    by simpa only [hs,hp] using h.gammaStack,
    ⟨⟨?_,by simpa only [hs,hr,hw] using h.transforms.forward.2.1,
      by simpa only [hs,hw] using h.transforms.forward.2.2⟩,
     ⟨?_,by simpa only [hs,hr,hw] using h.transforms.inverse.2.1,
      by simpa only [hs,hw] using h.transforms.inverse.2.2⟩,
     by simpa only [hs,hp] using h.transforms.forwardStack,
     by simpa only [hs,hp] using h.transforms.inverseStack⟩⟩
  · rw [hs]; exact h.shuffle.frame hf sh
  · rw [hs]; intro i hi
    rw [hf.readW (r:=⟨s.syms "VG_MLKEM_GAMMA",512⟩)
      (Offset.contains_base _ (by omega) (by omega)) ga (by decide)]
    exact h.gamma i hi
  · rw [hs]; intro i hi
    rw [hf.readW (r:=⟨s.syms "VG_MLKEM_NTT16_ZETAS",512⟩)
      (Offset.contains_base _ (by omega) (by omega)) fw (by decide)]
    exact h.transforms.forward.1 i hi
  · rw [hs]; intro i hi
    rw [hf.readW (r:=⟨s.syms "VG_MLKEM_INTT16_ZETAS",512⟩)
      (Offset.contains_base _ (by omega) (by omega)) iv (by decide)]
    exact h.transforms.inverse.1 i hi

theorem WP.tables128 {s : State} {c : Prog isa} {Q : State→Prop}
    (h : WP isa c s Q) (ht : Tables s) (hk : TStk s) (hn : c.aarch64Depth≤8) :
    WP isa c s fun t=>Q t ∧ Tables t := by
  obtain ⟨tr,t,he,hq⟩:=h
  refine ⟨tr,t,he,hq,?_⟩
  obtain ⟨hr,hw,hsp⟩:=VG.AArch64.Exec.rdwr he
  have hf := Frame.below_mono (VG.AArch64.Exec.frameSp he (by omega)) (b:=128) (by omega) (by decide)
  exact tables_frame128 ht hk (VG.AArch64.Exec.syms he) hr hw hsp hf

theorem mb_bW3 {s₀ : State} (hp : Pre P (enL P) s₀) (hk : Stk128 P s₀) :
    ∀ r ∈ bW3 P s₀, (R (kA s₀) (enL P).sc MB 32).Disjoint r := by
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

end VG.Proof.MlKem.AArch64.Hybrid
