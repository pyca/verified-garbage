module

public import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Inv
public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Row
import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Pair
import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Prefix
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Tail
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Permute
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! # The tail of the key generation hashing `ek` during the matrix

`tail_ok`: once every row of `t̂` is encoded and the third state has absorbed
the first `h` blocks of `ek`, `Kem16.kgTail`: `ρ` into both keys, each further
block of `ek` absorbed and permuted by `v`'s single-state permutation
(`block_step`), `H(ek)`, the first 32 bytes of the third state, and `z` into
`dk`, and the epilogue. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt keccakF)
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Hybrid (hstate)

variable {P : KemLay}

/-- `ek`, encoded. -/
abbrev ekK (P : KemLay) (s₀ : State) (mB : Mem) : List Byte := KPke.ekPKE P.params (aMW P s₀ mB) (dB s₀)

/-- After `ρ` and `b` blocks of `ek` in the third state. -/
structure TT (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (b : Nat) (s : State) : Prop where
  kb : KB P s₀ s
  e : EndInvW P s₀ mB v (P.k * P.k) s
  hash : stateAt s.mem (kA s₀ 3) = hstate (ekK P s₀ mB) b (Hybrid.dB (Kem16.kgSrc P))

theorem TT.ek {s₀ s : State} {mB : Mem} {v : BitVec 64} {b : Nat} (h : TT P s₀ mB v b s) :
    bytesAt s.mem (kA s₀ 1) P.ekLen = ekK P s₀ mB :=
  ek_at (T := tVW P s₀ mB) (ρ := rhoK P s₀) (fun i hi => (h.e.tl.ek i hi).1) h.e.rek

/-- The third state and the permutation's working space. -/
theorem st_wk_far {s₀ : State} (hp : Pre P s₀) {o l : Nat} (f : o + l ≤ 840) :
    Far P s₀ (R (kA s₀) 3 o l) := by
  have hw := hp.wf
  exact far_R hp (by decide) (by simp only [kL]; lom) (fun _ => .inl f) (by decide) (fun h => absurd h (by decide))

/-- **One more block of `ek`**, absorbed and permuted. -/
theorem block_step (v : Proof.Sha3.AArch64.Permutation) {s₀ s : State} (hp : Pre P s₀)
    {mB : Mem} {vv : BitVec 64} {b : Nat} (hb : 136 * b < P.ekLen) (H : TT P s₀ mB vv b s) :
    WP isa (.seq (.block (Hybrid.absorbBlock (Kem16.kgSrc P) b)) (Kem16.kgPerm v.callee)) s
      (TT P s₀ mB vv (b + 1)) := by
  have hw := hp.wf
  have hsv : 200 ≤ SV P := by lom
  have kb := H.kb
  have ek : (⟨kA s₀ 1, (Kem16.kgSrc P).len⟩ : Region) = R (kA s₀) 1 0 (kL P 1) := ekR s₀
  have fS : 0 + 200 ≤ kL P 3 := by
    show 0 + 200 ≤ P.scl; omega_using [hw.facts.2.2.2.2.2.2.2.2.1]
  have fE : 0 + kL P 1 ≤ kL P 1 := by omega
  refine WP.seq (WP.mono (Hybrid.absorbBlock_ok (Kem16.kgSrc P) (srcOkK hw)
    (by show s.gpr .x26 + BitVec.ofNat 64 0 = kA s₀ 1; rw [kb.x26, ptr_zero]) kb.x28 hb H.ek H.hash
    (by rw [ek]; exact cov_r hp kb (b := 1) (o := 0) (l := kL P 1) (by decide) fE)
    (by rw [stR_scratch]; exact cov_w hp kb (b := 3) (o := 0) (l := 200) (by decide) fS)
    (by rw [stR_scratch, ek]
        exact hp.args.rdisj (b₁ := 3) (o₁ := 0) (l₁ := 200) (b₂ := 1) (o₂ := 0) (l₂ := kL P 1)
          (by decide) (by decide) fS fE (.inl (by decide)))) fun t ⟨kt, ft, st⟩ => ?_)
  rw [stR_scratch] at ft
  have kbt := kb.frame kt ft (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨(st_far hp (b := 3) (o := SV P) (l := 48) (by decide) hp.sv (.inr hsv)),
      (st_far hp (by decide) (by kl) (.inl (by decide)))⟩
  have et := H.e.frame hp kbt (kt.get .x24) ft fun r hr => by
    rw [List.mem_singleton.mp hr]; exact st_wk_far hp (by decide)
  refine WP.mono (FixedHash.permute_ok v (hsetup hp kbt (rate := 136) (by decide))
    ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩) fun w ⟨kw, sw⟩ => ?_
  have e3 : STr .x28 KG.ST t = R (kA s₀) 3 0 200 := by simp only [STr, R, kbt.x28, KG.ST]
  have e4 : (⟨t.gpr .x28 + BitVec.ofNat 64 KG.WK, 512⟩ : Region) = R (kA s₀) 3 KG.WK 512 := by
    simp only [R, kbt.x28]
  rw [e3, e4] at kw
  have far : ∀ r ∈ [R (kA s₀) 3 0 200, R (kA s₀) 3 KG.WK 512], Far P s₀ r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact st_wk_far hp (by decide)
    · exact st_wk_far hp (by decide)
  have kbw := kbt.call kw fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨(st_far hp (b := 3) (o := SV P) (l := 48) (by decide) hp.sv (.inr hsv)),
        (st_far hp (by decide) (by kl) (.inl (by decide)))⟩
    · exact ⟨hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inr (.inr (by lom))),
        hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inl (by decide))⟩
  refine ⟨kbw, et.frame hp kbw (kw.cs .x24 (by decide) (by decide)) kw.frame far, ?_⟩
  rw [kbt.x28, show KG.ST = 0 from rfl, ptr_zero] at sw
  rw [sw, ← st]

/-- Blocks `b` to `b + d - 1` of `ek`. -/
theorem blocks_ok (v : Proof.Sha3.AArch64.Permutation) {s₀ : State} (hp : Pre P s₀) {mB : Mem}
    {vv : BitVec 64} : ∀ (d b : Nat), b + d ≤ Hybrid.blocks (Kem16.kgSrc P) → ∀ {s : State},
      TT P s₀ mB vv b s →
      WPs ((List.range' b d).map fun b => .seq (.block (Hybrid.absorbBlock (Kem16.kgSrc P) b))
        (Kem16.kgPerm v.callee)) s (TT P s₀ mB vv (b + d))
  | 0, b, _, s, H => by simpa only [List.range'_zero, List.map_nil, WPs, Nat.add_zero] using H
  | d + 1, b, hd, s, H => by
    have hw := hp.wf
    have hf := hw.facts
    have hb : 136 * b < P.ekLen := by
      simp only [Hybrid.blocks, Kem16.kgSrc, KemLay.ekLen] at hd ⊢
      have := Nat.lt_succ_iff.mp (show b < (384 * P.k + 32) / 136 + 1 by omega)
      have := (Nat.le_div_iff_mul_le (by decide)).1 this
      omega
    rw [List.range'_succ, List.map_cons]
    refine WPs.cons (WP.mono (block_step v hp hb H) fun t ht => ?_)
    have r := blocks_ok v hp d (b + 1) (by omega) ht
    rwa [show b + 1 + d = b + (d + 1) by omega] at r

/-- `H(ek)` and `z` into `dk`, and the epilogue. -/
theorem final_ok {s₀ s : State} (hp : Pre P s₀) {mB : Mem} {vv : BitVec 64}
    (HT : TT P s₀ mB vv (Hybrid.blocks (Kem16.kgSrc P)) s) :
    WP isa (.block (copy32 .x28 KG.ST .x27 (768 * P.k + 32) ++ copy32 .x25 32 .x27 (768 * P.k + 64) ++
      [mov .x0 .x24, .ldr .x .x30 .x28 (KG.SV P + 40), .ldr .x .x24 .x28 (KG.SV P),
        .ldr .x .x25 .x28 (KG.SV P + 8), .ldr .x .x26 .x28 (KG.SV P + 16),
        .ldr .x .x27 .x28 (KG.SV P + 24), .ldr .x .x28 .x28 (KG.SV P + 32)])) s (DoneW P s₀ mB vv) := by
  have hw := hp.wf
  have kb := HT.kb
  have hfull : stateAt s.mem (kA s₀ 3) = Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 (BitVec.ofNat 8 6) (ekK P s₀ mB)) := by
    rw [HT.hash]
    apply Hybrid.hstate_done
    rw [← HT.ek, VG.Proof.MlKem.bytesAt_length]
    simp only [Hybrid.blocks, Kem16.kgSrc]
    omega
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy_ok (S := kA s₀ 3) (D := kA s₀ 2) (so := KG.ST) (dO := 768 * P.k + 32) (by decide) (by decide)
    (by decide) (by lom) (hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl))
    kb.x28 kb.x27 (cov_r hp kb (b := 3) (by decide) (by kl))
    (cov_w hp kb (b := 2) (by decide) (by kl))) fun s₂ ⟨k₂, f₂, b₂⟩ => ?_
  have kb₂ := kb.frame k₂ f₂ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (b := 2) (o := 768 * P.k + 32) (l := 32) (by decide) (by kl) (.inl (by decide)) (by decide)
  have h₂ := HT.e.frame hp kb₂ (k₂.get .x24) f₂ fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
  have hh₂ : bytesAt s₂.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 32)) 32 = H (ekK P s₀ mB) := by
    rw [b₂, show KG.ST = 0 from rfl, ptr_zero, H_eq, Hybrid.bytesAt_squeeze, hfull]; rfl
  refine WP.mono (copy_ok (S := kA s₀ 0) (D := kA s₀ 2) (so := 32) (dO := 768 * P.k + 64) (by decide) (by decide)
    (by decide) (by lom) (hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl))
    kb₂.x25 kb₂.x27 (cov_r hp kb₂ (b := 0) (by decide) (by kl))
    (cov_w hp kb₂ (b := 2) (by decide) (by kl))) fun s₃ ⟨k₃, f₃, b₃⟩ => ?_
  have kb₃ := kb₂.frame k₃ f₃ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (b := 2) (o := 768 * P.k + 64) (l := 32) (by decide) (by kl) (.inl (by decide)) (by decide)
  have far₃ : ∀ r ∈ [R (kA s₀) 2 (768 * P.k + 64) 32], Far P s₀ r := fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
  have h₃ := h₂.frame hp kb₃ (k₃.get .x24) f₃ far₃
  have hh₃ : bytesAt s₃.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 32)) 32 = H (ekK P s₀ mB) := by
    rw [bytesAt_frame f₃ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl)) (by decide)]
    exact hh₂
  have z₃ : bytesAt s₃.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 64)) 32 = zB s₀ := by rw [b₃]; exact kb₂.z
  have ek₃ : bytesAt s₃.mem (kA s₀ 1) P.ekLen = ekK P s₀ mB :=
    ek_at (T := tVW P s₀ mB) (ρ := rhoK P s₀) (fun i hi => (h₃.tl.ek i hi).1) h₃.rek
  have dk₃ : bytesAt s₃.mem (kA s₀ 2) P.dkLen = KPke.dkPKE P.params (dB s₀) ++
      ekK P s₀ mB ++ H (ekK P s₀ mB) ++ zB s₀ :=
    dk_at (cat_at (T := KPke.kgS P.params (dB s₀)) fun j hj => h₃.tl.dk j hj)
      (ek_at (T := tVW P s₀ mB) (ρ := rhoK P s₀) (fun i hi => by rw [ptr_add]; exact (h₃.tl.ek i hi).2)
        (by rw [ptr_add, show 384 * P.k + 384 * P.k = 768 * P.k by omega]; exact h₃.rdk)) hh₃ z₃
  refine WP.mono (restore_ok hp kb₃) fun s' ⟨abi, x0, hm⟩ => ⟨abi, by rw [x0, h₃.tl.c.x24], ?_, ?_⟩
  · rw [hm]; exact ek₃
  · rw [hm]; exact dk₃

/-- **The tail**, once every row is encoded and the matrix has absorbed its blocks of `ek`. -/
theorem tail_ok (v : Proof.Sha3.AArch64.Permutation) {s₀ s : State} (hp : Pre P s₀)
    (H : IL P s₀ (P.k * P.k) P.k (Kem16.hashedBy P (P.k * P.k / 2)) s) :
    WP isa (Kem16.kgTail v.callee P) s (DoneW P s₀ s.mem (s.gpr .x24)) := by
  have hw := hp.wf
  have hf := hw.facts
  have kb := H.b.kb
  have hh := H.hr
  have hle : 136 * Kem16.hashedBy P (P.k * P.k / 2) ≤ P.ekLen := by
    simp only [KemLay.ekLen]; omega
  have tl : TLW P s₀ s.mem (s.gpr .x24) (P.k * P.k) P.k s :=
    ⟨⟨kb, H.b.rho, H.b.sig, rfl, Nat.le_refl _, fun e he => ⟨H.b.red e he, rfl⟩⟩, H.sp, H.dk, H.rows⟩
  unfold Kem16.kgTail
  refine WPs.seqs (by simp) (WPs.append (WPs.append ?_))
  refine WPs.cons (WP.mono (rho_okW hp tl) fun s₁ ⟨kb₁, e₁, f₁⟩ => ?_)
  simp only [WPs]
  have ek₁ : bytesAt s₁.mem (kA s₀ 1) P.ekLen = ekK P s₀ s.mem :=
    ek_at (T := tVW P s₀ s.mem) (ρ := rhoK P s₀) (fun i hi => (e₁.tl.ek i hi).1) e₁.rek
  have hs₁ : stateAt s₁.mem (kA s₀ 3) = hstate (ekK P s₀ s.mem) (Kem16.hashedBy P (P.k * P.k / 2))
      (Hybrid.dB (Kem16.kgSrc P)) := by
    rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame f₁ (fun r hr => by
      rw [stR_scratch]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (st_far hp (by decide) (by kl) (.inl (by decide))).symm
      · exact (st_far hp (by decide) (by kl) (.inl (by decide))).symm), H.hash, ← ek₁]
    refine hstate_prefix hle ?_
    have e1 : kA s₀ 1 = kA s₀ 1 + BitVec.ofNat 64 0 := (ptr_zero _).symm
    rw [e1, bytesAt_frame f₁ (fun q hq => ?_) (by have := kL_le hw 1; simp only [kL] at this; omega)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hp.args.rdisj (b₁ := 1) (o₁ := 0) (l₁ := 136 * Kem16.hashedBy P (P.k * P.k / 2)) (by decide) (by decide)
        (by simp only [kL]; omega) (by kl) (.inr (.inl (by omega)))
    · exact hp.args.rdisj (b₁ := 1) (o₁ := 0) (by decide) (by decide) (by simp only [kL]; omega) (by kl)
        (.inl (by decide))
  have hb : Kem16.hashedBy P (P.k * P.k / 2) ≤ Hybrid.blocks (Kem16.kgSrc P) := by
    simp only [Hybrid.blocks, Kem16.kgSrc]
    have := (Nat.le_div_iff_mul_le (k := 136) (by decide)).2
      (show Kem16.hashedBy P (P.k * P.k / 2) * 136 ≤ P.ekLen by omega)
    omega
  have r := blocks_ok v hp (Hybrid.blocks (Kem16.kgSrc P) - Kem16.hashedBy P (P.k * P.k / 2))
    (Kem16.hashedBy P (P.k * P.k / 2)) (by omega) (s := s₁) ⟨kb₁, e₁, hs₁⟩
  rw [Nat.add_sub_cancel' hb] at r
  exact WPs.mono r fun u hu => WPs.single (final_ok hp hu)

end VG.Proof.MlKem.AArch64.KeyGen
