module

public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Tail
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Tables
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.EncapsTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# The hashing encapsulation is correct

`using_correctH`: the first phase (`startH_ok`), the matrix (`matrixH_ok`),
`H` and `G` (`tailH_ok`), then noise, `u`, `v` and the epilogue
(`restH_ok`), with the constant tables kept apart from every write, the
128 bytes below the stack pointer the x3 calls use included (`TStk`).
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

/-- Noise, `u`, `v` and the epilogue (`Encaps.fused_c_using_ok`, from the
facts at the state they start in). -/
theorem restH_ok (valid : PrfValid P (enL P) prf) {s₀ : State} (hp : Pre P (enL P) s₀) (hr : Noise.Room P)
    (hc : Calls P) {sB : State}
    (htr : Optimized.TransformTables sB)
    (hT : AfterT P s₀ (rhoE P s₀) sB)
    (ht : Dot.GammaArtifact sB.mem (sB.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨sB.syms "VG_MLKEM_GAMMA",512⟩] (sB.rd++sB.wr))
    (ha : ∀r∈encW P (enL P) s₀ 2 0, (⟨sB.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (hn : ∀r∈Noise.allWrites P false (kA s₀ (enL P).sc), (⟨sB.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r) :
    WP isa (Impl.MlKem.AArch64.Optimized.enRestUsing prf P) sB (Done P s₀ sB.mem (sB.gpr .x24)) := by
  have hB := hT.b
  have e0 : EInv P (enL P) s₀ 2 0 sB.mem sB.mem (sB.gpr .x24) (gE P s₀).2 (mE s₀) 0 0 sB :=
    ⟨hB.kb, rfl, hT.r, hT.m, fun i hi j hj => ⟨hB.reduced hi hj, rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩
  refine WP.seq (WP.mono (encrypt_rest_using valid hp hr hc encArgs (T := ekT (ekE P s₀)) (ekT_eq s₀) htr e0 ht hcT ha hn) fun s₁ ⟨mN,fN,e₁,v₁⟩ => ?_)
  refine WP.mono (epilogue_ok hp e₁.kb) fun s' ⟨abi, x0, hm⟩ => ⟨abi, by rw [x0, e₁.x24], ?_, ?_⟩
  · rw [hm,bytesAt_frame e₁.fr (fun r hh => key_far hp (.inr hh)) (by decide)]
    have hf : ∀r∈Noise.allWrites P false (kA s₀ (enL P).sc), (Region.mk (kA s₀ 2) 32).Disjoint r := by
      have hfar := Kem.noise_far hp hr (b := 2) (o := 0) (l := 32) (by enk) (by enk) (.inl (by enk))
      simpa only [R,ptr_zero] using hfar
    rw [bytesAt_frame fN hf (by decide)]; exact hT.key
  · rw [hm]
    exact ct_at (U := fun i => compressEncode P.du (KPke.encU P.params (aM P (enL P) s₀ sB.mem) (gE P s₀).2 i))
      (fun i hi => by have := e₁.u i hi; rwa [Nat.zero_add] at this) (by rwa [Nat.zero_add] at v₁)

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

/-- **The hashing encapsulation is correct.** -/
theorem using_correctH (hash : FixedHash.HashFn) (valid : PrfValid P (enL P) prf)
    (hG : FixedHash.HashCorrect hash .x28 KEM.ST KEM.WK 72 6 [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩]
      [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩]) {s₀ : State} (hp : Pre P (enL P) s₀) (hk : Stk128 P s₀)
    (ho : HashOk P) (hr : Noise.Room P) (hc : Calls P) (tables : Tables s₀) (ts : TStk s₀)
    (depthM : (Impl.MlKem.AArch64.Hybrid.matrixH P).aarch64Depth≤8)
    (depthT : (Impl.MlKem.AArch64.Hybrid.tailH hash).aarch64Depth≤1) :
    WP isa (Impl.MlKem.AArch64.Hybrid.encaps hash prf P) s₀ fun t =>
      abiPreserved s₀ t ∧ (encapsAArch64 P).post s₀ t := by
  have hw := hp.wf
  refine WP.seq (WP.mono_syms (WP.tablesDepth (startH_ok hp) tables
    (by unfold Impl.MlKem.AArch64.Hybrid.startH; exact Nat.zero_le _)) fun uA ⟨hA, ta⟩ syA => ?_)
  have tsA : TStk uA := ts.of syA (by rw [hA.kb.sp])
  have mt : MT3 P s₀ uA := ⟨matrix_table_of_kb hp hA.kb ta, by rw [← hA.kb.sp]; exact tsA.shuffle⟩
  have h0 : HInv P s₀ uA.mem (rhoE P s₀) (ekE P s₀) 0 0 uA :=
    ⟨BInv.zero hA.kb hA.x24 hA.rho, Frame.refl _ _, by rw [hstate_zero]; exact hA.zero⟩
  refine WP.seq (WP.mono_syms (WP.tables128 (matrixH_ok hp hk ho h0 mt) ta tsA depthM)
    fun uB ⟨⟨hB, _⟩, tb⟩ _ => ?_)
  have hm : bytesAt uB.mem (sA (enL P) s₀ MB) 32 = mE s₀ := by
    rw [bytesAt_frame hB.fr (mb_bW3 hp hk) (by decide)]; exact hA.m
  have hst := hB.hash
  rw [hstate_done (by
    have := ho.three
    have : (ekE P s₀).length = P.ekLen := bytesAt_length _ _ _
    simp only [Impl.MlKem.AArch64.Hybrid.hashPairs, Impl.MlKem.AArch64.Hybrid.blocks]
    omega)] at hst
  refine WP.seq (WP.mono (WP.tablesDepth (tailH_ok hash hG hp hB.b hm hst) tb depthT) fun uC ⟨hC, tc⟩ => ?_)
  refine WP.mono (restH_ok valid hp hr hc tc.transforms hC tc.gamma tc.gammaRead
    (readonly_enc hp hC.b.kb encArgs tc.gammaApart tc.gammaStack)
    (readonly_noise hp hr hC.b.kb tc.gammaApart)) fun t ht => ⟨ht.abi, post_of hC.b ht⟩

end VG.Proof.MlKem.AArch64.Hybrid
