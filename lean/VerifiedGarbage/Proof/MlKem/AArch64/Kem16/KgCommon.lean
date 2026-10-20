module

public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.KgEnd
import VerifiedGarbage.Proof.Framework.Block

/-! # The 16-bit key generation's invariants

`CInvW`, `TLW`, `EndInvW` and `DoneW`: `CInv`, `TL`, `EndInv` and `Done` with
`Â` and `ŝ` stored with 16 bits, and the end of key generation over them
(`end_using_okW`), whose code reads only the encoded keys. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)
open VG.Proof.MlKem (cw)

variable {P : KemLay}

structure CInvW (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (n : Nat) (s : State) : Prop where
  kb : KB P s₀ s
  rho : bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 SB) 32 = rhoK P s₀
  sig : bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 SG) 32 = KPke.kgSigma P.params (dB s₀)
  x24 : s.gpr .x24 = v
  le : n ≤ P.k * P.k
  ahat : ∀ e < n, ReducedW 16 s.mem (AR s₀ e) ∧ polyAtW 16 s.mem (AR s₀ e) = polyAtW 16 mB (AR s₀ e)

theorem CInvW.frame {s₀ : State} {mB : Mem} {v : BitVec 64} {n : Nat} {s s' : State} (h : CInvW P s₀ mB v n s)
    (hk : KB P s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀ r ∈ W, (R (kA s₀) 3 SB 32).Disjoint r ∧ (R (kA s₀) 3 SG 32).Disjoint r ∧
      (R (kA s₀) 3 AH (1024 * (P.k * P.k))).Disjoint r) : CInvW P s₀ mB v n s' := by
  have hle := h.le
  have ha : ∀ e < n, ∀ r ∈ W, (polyRegion (AR s₀ e)).Disjoint r := fun e he r hr =>
    (hW r hr).2.2.sub_left (by
      rw [show AR s₀ e = kA s₀ 3 + BitVec.ofNat 64 AH + BitVec.ofNat 64 (1024 * e) by rw [ptr_add]]
      exact sub_offset' (by omega))
  refine ⟨hk, ?_, ?_, by rw [hx, h.x24], hle, fun e he => ⟨reducedW_frame (w16 := true) hf (ha e he) (h.ahat e he).1, ?_⟩⟩
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).1) (by decide)]; exact h.rho
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.1) (by decide)]; exact h.sig
  · exact (polyAtW_frame (w16 := true) hf (ha e he)).trans (h.ahat e he).2

abbrev aMW (P : KemLay) (s₀ : State) (mB : Mem) (i j : Nat) : Poly := polyAtW 16 mB (AR s₀ (P.k * i + j))

abbrev tVW (P : KemLay) (s₀ : State) (mB : Mem) (i : Nat) : Poly := KPke.kgT P.params (aMW P s₀ mB) (dB s₀) i

structure TLW (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (n i : Nat) (s : State) : Prop where
  c : CInvW P s₀ mB v n s
  sp : ∀ j < P.k, PolyIsW 16 s.mem (kA s₀ 3 + BitVec.ofNat 64 (sOff P j)) (KPke.kgS P.params (dB s₀) j)
  dk : ∀ j < P.k, bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 (384 * j)) 384 =
    encode12 (KPke.kgS P.params (dB s₀) j)
  ek : ∀ i' < i, bytesAt s.mem (kA s₀ 1 + BitVec.ofNat 64 (384 * i')) 384 = encode12 (tVW P s₀ mB i') ∧
    bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 (384 * P.k + 384 * i')) 384 = encode12 (tVW P s₀ mB i')

theorem TLW.frame {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {n i : Nat} {s s' : State}
    (h : TLW P s₀ mB v n i s) (hk : KB P s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region}
    (hf : Frame W s.mem s'.mem) (hW : ∀ r ∈ W, Apart P s₀ i r) : TLW P s₀ mB v n i s' := by
  have hw := hp.wf
  refine ⟨h.c.frame hk hx hf fun r hr => ⟨(hW r hr).1, (hW r hr).2.1,
    (hW r hr).2.2.1.sub_left (R.sub2 (Nat.le_refl _) (by omega))⟩, fun j hj => ?_, fun j hj => ?_,
    fun i' hi' => ⟨?_, ?_⟩⟩
  · exact polyIsW_frame_poly (w16 := true) hf (fun r hr => (hW r hr).2.2.1.sub_left (R.sub2 (by lom) (by lom))) (h.sp j hj)
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.2.sub_left (R.sub2 (by omega)
      (by have := mul_succ_le (a := 384) hj; omega))) (by decide)]
    exact h.dk j hj
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.1.sub_left (R.sub2 (by omega)
      (by have := mul_succ_le (a := 384) hi'; omega))) (by decide)]
    exact (h.ek i' hi').1
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.2.sub_left (R.sub2 (by omega)
      (by have := mul_succ_le (a := 384) hi'; omega))) (by decide)]
    exact (h.ek i' hi').2

structure DoneW (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  abi : abiPreserved s₀ s
  x0 : s.gpr .x0 = v
  ek : bytesAt s.mem (kA s₀ 1) P.ekLen = KPke.ekPKE P.params (aMW P s₀ mB) (dB s₀)
  dk : bytesAt s.mem (kA s₀ 2) P.dkLen = KPke.dkPKE P.params (dB s₀) ++
    KPke.ekPKE P.params (aMW P s₀ mB) (dB s₀) ++ H (KPke.ekPKE P.params (aMW P s₀ mB) (dB s₀)) ++ zB s₀

structure EndInvW (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (n : Nat) (s : State) : Prop where
  tl : TLW P s₀ mB v n P.k s
  rek : bytesAt s.mem (kA s₀ 1 + BitVec.ofNat 64 (384 * P.k)) 32 = rhoK P s₀
  rdk : bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k)) 32 = rhoK P s₀

theorem EndInvW.frame {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {n : Nat} {s s' : State}
    (h : EndInvW P s₀ mB v n s) (hk : KB P s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region}
    (hf : Frame W s.mem s'.mem) (hW : ∀ r ∈ W, Far P s₀ r) : EndInvW P s₀ mB v n s' :=
  ⟨h.tl.frame hp hk hx hf fun r hr => (hW r hr).1,
    by rw [bytesAt_frame hf (fun r hr => (hW r hr).2.1) (by decide)]; exact h.rek,
    by rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2) (by decide)]; exact h.rdk⟩

theorem rho_okW {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {n : Nat} {s : State}
    (h : TLW P s₀ mB v n P.k s) :
    WP isa (.block (copy32 .x28 SB .x26 (384 * P.k) ++ copy32 .x28 SB .x27 (768 * P.k))) s fun s' =>
      KB P s₀ s' ∧ EndInvW P s₀ mB v n s' ∧
        Frame [R (kA s₀) 1 (384 * P.k) 32, R (kA s₀) 2 (768 * P.k) 32] s.mem s'.mem := by
  have hw := hp.wf
  have kb := h.c.kb
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (S := kA s₀ 3) (D := kA s₀ 1) (so := SB) (dO := 384 * P.k) (by decide) (by decide)
    (by decide) (by lom) (hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl))
    kb.x28 kb.x26 (cov_r hp kb (b := 3) (by decide) (by kl))
    (cov_w hp kb (b := 1) (by decide) (by kl))) fun sa ⟨ka, fa, ba⟩ => ?_
  have kba := kb.frame ka fa (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (b := 1) (o := 384 * P.k) (l := 32) (by decide) (by kl) (.inl (by decide)) (by decide)
  have tla := h.frame hp kba (ka.get .x24) fa fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact apart_R hp (b := 1) (o := 384 * P.k) (l := 32) (Nat.le_refl _) (by decide) (by kl) (by kl)
      (fun _ => Nat.le_refl _) (by kl)
  refine WP.mono (copy_ok (S := kA s₀ 3) (D := kA s₀ 2) (so := SB) (dO := 768 * P.k) (by decide) (by decide)
    (by decide) (by lom) (hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl))
    kba.x28 kba.x27 (cov_r hp kba (b := 3) (by decide) (by kl))
    (cov_w hp kba (b := 2) (by decide) (by kl))) fun sb ⟨kb', fb, bb⟩ => ?_
  have kbb := kba.frame kb' fb (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (b := 2) (o := 768 * P.k) (l := 32) (by decide) (by kl) (.inl (by decide)) (by decide)
  refine ⟨kbb, ⟨tla.frame hp kbb (kb'.get .x24) fb (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact apart_R hp (b := 2) (o := 768 * P.k) (l := 32) (Nat.le_refl _) (by decide) (by kl) (by kl)
      (by kl) (fun _ => by omega)), ?_, ?_⟩, ?_⟩
  · rw [bytesAt_frame fb (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl)) (by decide), ba]
    exact h.c.rho
  · rw [bb, bytesAt_frame fa (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl)) (by decide)]
    exact h.c.rho
  · exact (fa.mono (by simp)).trans (fb.mono (by simp))

theorem post_ofW {s₀ sB s' : State} (hB : BInvW true P s₀ (P.k * P.k) sB) (hD : DoneW P s₀ sB.mem (sB.gpr .x24) s') :
    (keyGenAArch64 P).post s₀ s' := by
  show Outcome (fun iters => keyGenInternal P.params iters (bytesAt s₀.mem (s₀.gpr .x0) 32)
    (bytesAt s₀.mem (s₀.gpr .x0 + 32) 32)) ((s'.gpr .x0).setWidth 32)
    (bytesAt s'.mem (s₀.gpr .x1) P.ekLen, bytesAt s'.mem (s₀.gpr .x2) P.dkLen)
  have ed : bytesAt s₀.mem (s₀.gpr .x0) 32 = dB s₀ := by
    show _ = bytesAt s₀.mem (s₀.gpr .x0 + BitVec.ofNat 64 0) 32
    rw [ptr_zero]
  have ez : bytesAt s₀.mem (s₀.gpr .x0 + 32) 32 = zB s₀ := rfl
  have ek : bytesAt s'.mem (s₀.gpr .x1) P.ekLen = KPke.ekPKE P.params (aMW P s₀ sB.mem) (dB s₀) := hD.ek
  have dk : bytesAt s'.mem (s₀.gpr .x2) P.dkLen = KPke.dkPKE P.params (dB s₀) ++
      KPke.ekPKE P.params (aMW P s₀ sB.mem) (dB s₀) ++ H (KPke.ekPKE P.params (aMW P s₀ sB.mem) (dB s₀)) ++
      zB s₀ := hD.dk
  rw [ed, ez, ek, dk, hD.x0, hB.acc]
  by_cases hA : allOk P s₀ (P.k * P.k)
  · rw [ite_eq_left hA]
    refine .inl ⟨rfl, 280, ?_⟩
    show keyGenInternal P.params 280 (dB s₀) (zB s₀) = _
    rw [KPke.keyGenInternal_eq, KPke.kpkeKeyGen_some (p := P.params) rfl (a := aMW P s₀ sB.mem)
      fun i hi j hj => ?_]
    · rfl
    · have hi : i < P.k := hi
      have hj : j < P.k := hj
      have he : P.k * i + j < P.k * P.k := ij_lt hi hj
      have hke := ij_div (i := i) hj
      have r := hB.res (P.k * i + j) he
      have ok := hA (P.k * i + j) he
      rw [hke.1, hke.2] at r ok
      rcases r with r | r
      · rw [r] at ok; simp at ok
      · exact r
  · rw [ite_eq_right hA]
    refine .inr ⟨rfl, ?_⟩
    obtain ⟨e, he, hn⟩ : ∃ e, e < P.k * P.k ∧ ¬ (sampleNTT 280 (matSeed (rhoK P s₀) (e / P.k) (e % P.k))).isSome :=
      Classical.byContradiction fun hc => hA fun e he => Classical.byContradiction fun hn => hc ⟨e, he, hn⟩
    show keyGenInternal P.params 280 _ _ = none
    rw [KPke.keyGenInternal_eq, KPke.kpkeKeyGen_none (p := P.params) (i := e / P.k) (j := e % P.k)
      (div_lt he) (mod_lt he) (Option.not_isSome_iff_eq_none.mp hn)]
    rfl

end VG.Proof.MlKem.AArch64.KeyGen
