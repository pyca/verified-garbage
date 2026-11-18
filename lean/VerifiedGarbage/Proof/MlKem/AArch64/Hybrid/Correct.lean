module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Tables
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Matrix
meta import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.IntervalCases
public import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid
public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

/-! ### `MlKem.AArch64.Hybrid.Tail`, which this module and modules that import it used -/

section

/-!
# The hashing encapsulation after the matrix

`tailHN_ok`: `H(ek)`, the first 32 bytes of the third state, into `HB`, and
`G(m ‖ H(ek))` (`Hybrid.tailH`), with `Â` stored with 16 bits (`w16`) or 32.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Encaps
open VG.Spec.Sha3 (stateAt bytesAt squeezeFrom)
open VG.Spec.MlKem
open VG.Proof.MlKem

variable {P : KemLay}

/-- The first 32 bytes of a state in memory are the first 32 bytes it squeezes. -/
theorem bytesAt_squeeze (m : Mem) (p : Addr) : bytesAt m p 32 = squeezeFrom 136 (stateAt m p) 0 32 := by
  apply List.ext_getElem
  · rw [bytesAt_length, Proof.Sha3.length_squeezeFrom (by decide) (by decide)]
  · intro i h1 h2
    obtain hi : i < 32 := by simpa only [bytesAt_length] using h1
    rw [Proof.Sha3.squeezeFrom_getElem (by decide) (by decide) _ hi, Nat.zero_add,
      Nat.div_eq_of_lt (by omega_using [hi] : i < 136), Nat.mod_eq_of_lt (by omega_using [hi] : i < 136)]
    show _ = Proof.Sha3.byteOf (stateAt m p) i
    rw [Proof.Sha3.byteOf_stateAt _ _ (by omega_using [hi])]
    simp only [bytesAt, List.getElem_map, List.getElem_range]

/-- What the tail leaves, after the first `n` entries of `Â`. -/
structure AfterTN (w16 : Bool) (P : KemLay) (s₀ : State) (ρ : List Byte) (n : Nat) (s : State) : Prop where
  b : BInvW w16 P (enL P) s₀ s.mem ρ n s
  key : bytesAt s.mem (kA s₀ 2) 32 = (gE P s₀).1
  r : bytesAt s.mem (sA (enL P) s₀ RB) 32 = (gE P s₀).2
  m : bytesAt s.mem (sA (enL P) s₀ MB) 32 = mE s₀

/-- What the tail writes: `H(ek)` into `HB`, then `G`'s state, working space and stack, the key and `r`. -/
abbrev tailW (P : KemLay) (s₀ : State) : List Region :=
  [Region.mk (kA s₀ 4 + BitVec.ofNat 64 HB) 32] ++
    [Region.mk (kA s₀ (enL P).sc + BitVec.ofNat 64 KEM.ST) 200,
      ⟨kA s₀ (enL P).sc + BitVec.ofNat 64 WK, 640⟩, below s₀.sp 16,
      ⟨kA s₀ ((enL P).slot 1) + BitVec.ofNat 64 0, 32⟩, ⟨kA s₀ (enL P).sc + BitVec.ofNat 64 RB, 32⟩]

/-- The tail, after the first `n` entries of `Â`, with what it writes. -/
theorem tailHN_ok {w16 : Bool} (hash : FixedHash.HashFn)
    (hG : FixedHash.HashCorrect hash .x28 ST WK 72 6 [⟨.x28,MB,32⟩,⟨.x28,HB,32⟩]
      [⟨.x26,0,32⟩,⟨.x28,RB,32⟩])
    {s₀ sB : State} (hp : Pre P (enL P) s₀) {ρ : List Byte} {n : Nat} (hn : n ≤ P.k*P.k)
    (hB : BInvW w16 P (enL P) s₀ sB.mem ρ n sB)
    (hm : bytesAt sB.mem (sA (enL P) s₀ MB) 32 = mE s₀)
    (hst : stateAt sB.mem (kA s₀ (enL P).sc) =
      Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 (BitVec.ofNat 8 6) (ekE P s₀))) :
    WP isa (Impl.MlKem.AArch64.Hybrid.tailH hash) sB fun s =>
      AfterTN w16 P s₀ ρ n s ∧ Frame (tailW P s₀) sB.mem s.mem := by
  have hw := hp.wf
  -- `H(ek)`
  refine WP.seq (WP.mono (KeyGen.copy_ok (S := kA s₀ 4) (D := kA s₀ 4) (so := KEM.ST) (dO := HB)
    (by decide) (by decide) (by decide) (by decide) (sdisj hp (by lom) (by lom) (by lom))
    hB.kb.x28 hB.kb.x28 (cov_sr hp hB.kb (by lom)) (cov_s hp hB.kb (by lom)))
    fun s₃ ⟨k₁, f₁, b₁⟩ => ?_)
  obtain kb₃ := hB.kb.frame k₁ f₁ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by lom)
  obtain far₁ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ HB ∨ HB + 32 ≤ o) →
      ∀ r ∈ [Region.mk (kA s₀ 4 + BitVec.ofNat 64 HB) 32], (R (kA s₀) (enL P).sc o l).Disjoint r :=
    fun f h r hr => by rw [List.mem_singleton.mp hr]; exact sdisj hp f (by lom) h
  obtain h₃ : bytesAt s₃.mem (sA (enL P) s₀ HB) 32 = H (ekE P s₀) := by
    rw [show sA (enL P) s₀ HB = kA s₀ 4 + BitVec.ofNat 64 HB from rfl, b₁,
      show KEM.ST = 0 from rfl, ptr_zero, H_eq, bytesAt_squeeze]
    show squeezeFrom 136 (stateAt sB.mem (kA s₀ (enL P).sc)) 0 32 = _
    rw [hst]; rfl
  obtain m₃ : bytesAt s₃.mem (sA (enL P) s₀ MB) 32 = mE s₀ := by
    rw [bytesAt_frame f₁ (far₁ (o := MB) (l := 32) (by lom) (by decide)) (by decide)]; exact hm
  obtain x24₃ : s₃.gpr .x24 = sB.gpr .x24 := k₁.get .x24
  -- `G(m ‖ H(ek))`
  refine WP.mono (hG (hsetup hp kb₃ (by decide : 72 ∈ Spec.Sha3.rates)) (by decide) (by simp)
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact pieceOk (k := 3) hp kb₃ (by decide) (by enk) (.inr (by decide)) (by decide) (by enk)
      · exact pieceOk (k := 3) hp kb₃ (by decide) (by enk) (.inr (by decide)) (by decide) (by enk))
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact pieceOk (k := 1) hp kb₃ (by decide) (by enk) (.inl (by enk)) (by decide) (by enk)
      · exact pieceOk (k := 3) hp kb₃ (by decide) (by enk) (.inr (by decide)) (by decide) (by enk))
    (by
      refine List.pairwise_pair.mpr ?_
      simp only [preg, kb₃.x26, e28 kb₃]
      exact hp.args.rdisj (by enk) (by enk) (by enk) (by enk) (by enk) (by enk)))
    fun s₄ ⟨k₄, o₄⟩ => ?_
  obtain kb₄ := kb₃.hash hp k₄ fun p hp' => by
    rcases mem2' hp' with rfl | rfl
    · exact ⟨1, 0, 32, rfl, by decide, by enk, by enk, .inl (by enk)⟩
    · exact ⟨3, RB, 32, rfl, by decide, by enk, by enk, .inr (.inr (by enk))⟩
  obtain msg : (List.map (pbytes s₃) [⟨.x28, MB, 32⟩, ⟨.x28, HB, 32⟩]).flatten = mE s₀ ++ H (ekE P s₀) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      e28 kb₃]
    rw [m₃, h₃]
  obtain ⟨o₁, o₂, -⟩ := o₄
  rw [msg] at o₁ o₂
  obtain hG' := G_eq (mE s₀ ++ H (ekE P s₀))
  obtain key₄ : bytesAt s₄.mem (kA s₀ 2) 32 = (gE P s₀).1 := by
    obtain e : kA s₀ 2 = s₃.gpr .x26 + BitVec.ofNat 64 0 := by rw [kb₃.x26, ptr_zero]; rfl
    rw [e, o₁]; show _ = (G (mE s₀ ++ H (ekE P s₀))).1; rw [hG']; rfl
  obtain r₄ : bytesAt s₄.mem (sA (enL P) s₀ RB) 32 = (gE P s₀).2 := by
    rw [← e28 kb₃, o₂]; show _ = (G (mE s₀ ++ H (ekE P s₀))).2; rw [hG']; rfl
  have k₄' := k₄
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₃.x28, kb₃.x26, kb₃.sp] at k₄'
  obtain far₄ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → 840 ≤ o → (o + l ≤ RB ∨ RB + 32 ≤ o) →
      ∀ r ∈ [Region.mk (kA s₀ (enL P).sc + BitVec.ofNat 64 KEM.ST) 200,
        ⟨kA s₀ (enL P).sc + BitVec.ofNat 64 WK, 640⟩, below s₀.sp 16,
        ⟨kA s₀ ((enL P).slot 1) + BitVec.ofNat 64 0, 32⟩, ⟨kA s₀ (enL P).sc + BitVec.ofNat 64 RB, 32⟩],
      (R (kA s₀) (enL P).sc o l).Disjoint r := fun f h8 hr r hm => by
    rcases mem5 hm with rfl | rfl | rfl | rfl | rfl
    · exact sdisj hp f (by lom) (by lom)
    · exact sdisj hp f (by lom) (by lom)
    · exact below_R hp hp.scb (hp.fs f)
    · exact hp.args.rdisj (by enk) (by enk) (hp.fs f) (by enk) (by enk) (by enk)
    · exact sdisj hp f (by lom) hr
  obtain far34 : ∀ {o l : Nat}, o + l ≤ SV P + 48 → 840 ≤ o → (o + l ≤ RB ∨ RB + 32 ≤ o) →
      (o + l ≤ HB ∨ HB + 32 ≤ o) →
      bytesAt s₄.mem (sA (enL P) s₀ o) l = bytesAt sB.mem (sA (enL P) s₀ o) l := fun f h8 hr hh => by
    rw [bytesAt_frame k₄'.frame (far₄ f h8 hr) (by lom), bytesAt_frame f₁ (far₁ f hh) (by lom)]
  obtain farA : ∀ (e : Nat), e < P.k * P.k → ∀ r ∈ [Region.mk (kA s₀ 4 + BitVec.ofNat 64 HB) 32] ++
      [Region.mk (kA s₀ (enL P).sc + BitVec.ofNat 64 KEM.ST) 200,
        ⟨kA s₀ (enL P).sc + BitVec.ofNat 64 WK, 640⟩, below s₀.sp 16,
        ⟨kA s₀ ((enL P).slot 1) + BitVec.ofNat 64 0, 32⟩, ⟨kA s₀ (enL P).sc + BitVec.ofNat 64 RB, 32⟩],
      (polyRegion (aP (enL P) s₀ e)).Disjoint r := fun e he r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact far₁ (o := AH + 1024 * e) (l := 1024) (by lom) (.inr (by lom)) r hr
    · exact far₄ (o := AH + 1024 * e) (l := 1024) (by lom) (by lom) (.inr (by lom)) r hr
  obtain f14 := (f₁.mono (fun r hr => List.mem_append_left _ hr)).trans
    (k₄'.frame.mono (fun r hr => List.mem_append_right [Region.mk (kA s₀ 4 + BitVec.ofNat 64 HB) 32] hr))
  refine ⟨⟨⟨kb₄, Frame.refl _ _, ?_, ?_, ?_, ?_⟩, key₄, r₄, ?_⟩, f14⟩
  · rw [far34 (o := SB) (l := 32) (by lom) (by lom) (by decide) (by decide)]; exact hB.rho
  · rw [k₄.cs _ (by decide) (by decide), x24₃]; exact hB.acc
  · intro e he; exact reducedW_frame f14 (farA e (by omega_using [hn, he])) (hB.red e he)
  · intro e he; rw [polyAtW_frame f14 (farA e (by omega_using [hn, he]))]; exact hB.res e he
  · rw [far34 (o := MB) (l := 32) (by lom) (by lom) (by decide) (by decide)]; exact hm

end VG.Proof.MlKem.AArch64.Hybrid

end

end

/-!
# The hashing encapsulation: its constant tables

The constant tables kept apart from every write, the 128 bytes below the stack
pointer the x3 calls use included (`TStk`, `WP.tables128`), for the
correctness of the hashing encapsulation (`Kem16/Encaps.lean`: the first phase,
`startH_ok`; the matrix, `matrixH_ok`; `H` and `G`, `tailHN_ok`; then noise,
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
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) ga (by decide)]
    exact h.gamma i hi
  · rw [hs]; intro i hi
    rw [hf.readW (r:=⟨s.syms "VG_MLKEM_NTT16_ZETAS",512⟩)
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) fw (by decide)]
    exact h.transforms.forward.1 i hi

theorem WP.tables128 {s : State} {c : Prog isa} {Q : State→Prop}
    (h : WP isa c s Q) (ht : Tables s) (hk : TStk s) (hn : c.aarch64Depth≤8) :
    WP isa c s fun t=>Q t ∧ Tables t := by
  obtain ⟨tr,t,he,hq⟩:=h
  refine ⟨tr,t,he,hq,?_⟩
  obtain ⟨hr,hw,hsp⟩:=VG.AArch64.Exec.rdwr he
  have hf := Frame.below_mono (VG.AArch64.Exec.frameSp he (by omega_using [hn])) (b:=128) (by omega_using [hn]) (by decide)
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
