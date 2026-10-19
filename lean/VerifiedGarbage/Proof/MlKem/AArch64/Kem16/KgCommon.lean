module

public import VerifiedGarbage.Proof.MlKem.AArch64.KeyGen
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenEnd
public import VerifiedGarbage.Proof.MlKem.CoeffW

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

structure CInvW (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  kb : KB P s₀ s
  rho : bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 SB) 32 = rhoK P s₀
  sig : bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 SG) 32 = KPke.kgSigma P.params (dB s₀)
  x24 : s.gpr .x24 = v
  ahat : ∀ e < P.k * P.k, ReducedW 16 s.mem (AR s₀ e) ∧ polyAtW 16 s.mem (AR s₀ e) = polyAtW 16 mB (AR s₀ e)

theorem CInvW.frame {s₀ : State} {mB : Mem} {v : BitVec 64} {s s' : State} (h : CInvW P s₀ mB v s)
    (hk : KB P s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀ r ∈ W, (R (kA s₀) 3 SB 32).Disjoint r ∧ (R (kA s₀) 3 SG 32).Disjoint r ∧
      (R (kA s₀) 3 AH (1024 * (P.k * P.k))).Disjoint r) : CInvW P s₀ mB v s' := by
  have ha : ∀ e < P.k * P.k, ∀ r ∈ W, (polyRegion (AR s₀ e)).Disjoint r := fun e he r hr =>
    (hW r hr).2.2.sub_left (by
      rw [show AR s₀ e = kA s₀ 3 + BitVec.ofNat 64 AH + BitVec.ofNat 64 (1024 * e) by rw [ptr_add]]
      exact sub_offset' (by omega))
  refine ⟨hk, ?_, ?_, by rw [hx, h.x24], fun e he => ⟨reducedW_frame (w16 := true) hf (ha e he) (h.ahat e he).1, ?_⟩⟩
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).1) (by decide)]; exact h.rho
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.1) (by decide)]; exact h.sig
  · exact (polyAtW_frame (w16 := true) hf (ha e he)).trans (h.ahat e he).2

abbrev aMW (P : KemLay) (s₀ : State) (mB : Mem) (i j : Nat) : Poly := polyAtW 16 mB (AR s₀ (P.k * i + j))

abbrev tVW (P : KemLay) (s₀ : State) (mB : Mem) (i : Nat) : Poly := KPke.kgT P.params (aMW P s₀ mB) (dB s₀) i

structure TLW (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (i : Nat) (s : State) : Prop where
  c : CInvW P s₀ mB v s
  sp : ∀ j < P.k, PolyIsW 16 s.mem (kA s₀ 3 + BitVec.ofNat 64 (sOff P j)) (KPke.kgS P.params (dB s₀) j)
  dk : ∀ j < P.k, bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 (384 * j)) 384 =
    encode12 (KPke.kgS P.params (dB s₀) j)
  ek : ∀ i' < i, bytesAt s.mem (kA s₀ 1 + BitVec.ofNat 64 (384 * i')) 384 = encode12 (tVW P s₀ mB i') ∧
    bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 (384 * P.k + 384 * i')) 384 = encode12 (tVW P s₀ mB i')

theorem TLW.frame {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {i : Nat} {s s' : State}
    (h : TLW P s₀ mB v i s) (hk : KB P s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region}
    (hf : Frame W s.mem s'.mem) (hW : ∀ r ∈ W, Apart P s₀ i r) : TLW P s₀ mB v i s' := by
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

structure EndInvW (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  tl : TLW P s₀ mB v P.k s
  rek : bytesAt s.mem (kA s₀ 1 + BitVec.ofNat 64 (384 * P.k)) 32 = rhoK P s₀
  rdk : bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k)) 32 = rhoK P s₀

theorem EndInvW.frame {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {s s' : State}
    (h : EndInvW P s₀ mB v s) (hk : KB P s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region}
    (hf : Frame W s.mem s'.mem) (hW : ∀ r ∈ W, Far P s₀ r) : EndInvW P s₀ mB v s' :=
  ⟨h.tl.frame hp hk hx hf fun r hr => (hW r hr).1,
    by rw [bytesAt_frame hf (fun r hr => (hW r hr).2.1) (by decide)]; exact h.rek,
    by rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2) (by decide)]; exact h.rdk⟩

theorem rho_okW {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {s : State} (h : TLW P s₀ mB v P.k s) :
    WP isa (.block (copy32 .x28 SB .x26 (384 * P.k) ++ copy32 .x28 SB .x27 (768 * P.k))) s fun s' =>
      KB P s₀ s' ∧ EndInvW P s₀ mB v s' := by
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
  refine ⟨kbb, tla.frame hp kbb (kb'.get .x24) fb (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact apart_R hp (b := 2) (o := 768 * P.k) (l := 32) (Nat.le_refl _) (by decide) (by kl) (by kl)
      (by kl) (fun _ => by omega)), ?_, ?_⟩
  · rw [bytesAt_frame fb (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl)) (by decide), ba]
    exact h.c.rho
  · rw [bb, bytesAt_frame fa (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl)) (by decide)]
    exact h.c.rho

theorem hek_using_okW (hash : FixedHash.HashFn)
 (hH : FixedHash.HashCorrect hash .x28 ST WK 136 6
  [⟨.x26,0,P.ekLen⟩] [⟨.x27,768*P.k+32,32⟩]) {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {s : State} (kb : KB P s₀ s)
    (h : EndInvW P s₀ mB v s) :
    WP isa (hash .x28 ST WK 136 6 [⟨.x26, 0, P.ekLen⟩] [⟨.x27, 768 * P.k + 32, 32⟩]) s
      fun s' => KB P s₀ s' ∧ EndInvW P s₀ mB v s' ∧
      bytesAt s'.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 32)) 32 =
        H (KPke.ekPKE P.params (aMW P s₀ mB) (dB s₀)) := by
  have hw := hp.wf
  have e28 : ∀ o, s.gpr .x28 + BitVec.ofNat 64 o = kA s₀ 3 + BitVec.ofNat 64 o := fun o => by rw [kb.x28]
  refine WP.mono (hH (hsetup hp kb (by decide : 136 ∈ Spec.Sha3.rates)) (by decide) (by simp)
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (b := 1) hp kb (by decide) (by kl) (by decide) (by kl) (by decide))
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (b := 2) hp kb (by decide) (by kl) (by kl) (by decide) (by decide))
    (List.pairwise_singleton _ _)) fun s' ⟨k', o'⟩ => ?_
  have kb' := kb.hash hp k' fun p hp' => by
    rw [List.mem_singleton.mp hp']
    exact ⟨2, 768 * P.k + 32, 32, rfl, by decide, by decide, by kl, .inl (by decide)⟩
  have msg : (List.map (pbytes s) [⟨.x26, 0, P.ekLen⟩]).flatten = KPke.ekPKE P.params (aMW P s₀ mB) (dB s₀) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      kb.x26, ptr_zero]
    exact ek_at (T := tVW P s₀ mB) (ρ := rhoK P s₀) (fun i hi => (h.tl.ek i hi).1) h.rek
  obtain ⟨o, -⟩ := o'
  rw [msg, kb.x27] at o
  refine ⟨kb', h.frame hp kb' (k'.cs _ (by decide) (by decide)) k'.frame fun r hr => ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil] at hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · rw [VG.Proof.MlKem.AArch64.STr, e28]
      exact far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
    · rw [VG.Proof.MlKem.AArch64.WKr, e28]
      exact far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
    · rw [kb.sp]; exact far_below hp
    · simp only [preg, kb.x27]
      exact far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
  · rw [o, H_eq]; rfl

theorem end_using_okW (hash : FixedHash.HashFn)
 (hH : FixedHash.HashCorrect hash .x28 ST WK 136 6
  [⟨.x26,0,P.ekLen⟩] [⟨.x27,768*P.k+32,32⟩]) {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {s : State} (h : TLW P s₀ mB v P.k s) :
    WP isa (FixedHashCallers.kgEndUsing hash P) s (DoneW P s₀ mB v) := by
  have hw := hp.wf
  refine WP.seq (WP.mono (rho_okW hp h) fun s₁ ⟨kb₁, h₁⟩ => WP.seq (WP.mono (hek_using_okW hash hH hp kb₁ h₁)
    fun s₂ ⟨kb₂, h₂, hh₂⟩ => ?_))
  rw [WP.block_append_iff]
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
  have hh₃ : bytesAt s₃.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 32)) 32 =
      H (KPke.ekPKE P.params (aMW P s₀ mB) (dB s₀)) := by
    rw [bytesAt_frame f₃ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl)) (by decide)]
    exact hh₂
  have z₃ : bytesAt s₃.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 64)) 32 = zB s₀ := by rw [b₃]; exact kb₂.z
  have ek₃ : bytesAt s₃.mem (kA s₀ 1) P.ekLen = KPke.ekPKE P.params (aMW P s₀ mB) (dB s₀) :=
    ek_at (T := tVW P s₀ mB) (ρ := rhoK P s₀) (fun i hi => (h₃.tl.ek i hi).1) h₃.rek
  have dk₃ : bytesAt s₃.mem (kA s₀ 2) P.dkLen = KPke.dkPKE P.params (dB s₀) ++
      KPke.ekPKE P.params (aMW P s₀ mB) (dB s₀) ++ H (KPke.ekPKE P.params (aMW P s₀ mB) (dB s₀)) ++ zB s₀ :=
    dk_at (cat_at (T := KPke.kgS P.params (dB s₀)) fun j hj => h₃.tl.dk j hj)
      (ek_at (T := tVW P s₀ mB) (ρ := rhoK P s₀) (fun i hi => by rw [ptr_add]; exact (h₃.tl.ek i hi).2)
        (by rw [ptr_add, show 384 * P.k + 384 * P.k = 768 * P.k by omega]; exact h₃.rdk)) hh₃ z₃
  refine WP.mono (restore_ok hp kb₃) fun s' ⟨abi, x0, hm⟩ => ⟨abi, by rw [x0, h₃.tl.c.x24], ?_, ?_⟩
  · rw [hm]; exact ek₃
  · rw [hm]; exact dk₃

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
