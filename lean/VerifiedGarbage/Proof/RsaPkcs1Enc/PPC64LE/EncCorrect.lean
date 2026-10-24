module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.EncCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.RecoverMask
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_rsa_pkcs1_encrypt_precomputed` on PPC64LE: correctness

After the call (`AfterCall`), the result and `out` are masked with `PS`'s
zero test (`vg_rsa_pkcs1_recover_precomputed`'s `maskLoop`), `EM` is zeroed
(`encode`'s `fillLoop`) and the registers restored (`tail_ok`): if `pre`
holds the modulus' values, RSAES-PKCS1-V1_5-ENCRYPT (RFC 8017 §7.2.1).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Enc

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Precomputed VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.PPC64LE
open VG.Proof.RsaPkcs1Sig.PPC64LE.Rec (maskOf maskOf_bytes maskOf_byte)
open VG.Proof.RsaPkcs1Sig (bytesAt_length frame_writeBytes)

/-- The result and `out`, from the entry state `s`: the octets `encrypt`
returns, or zeros. -/
def Post (s s' : State) : Prop :=
  abiPreserved s s' ∧ (PreOk s →
    Spec.Rsa.written s'.mem (s.gpr .r3) (s.gpr .r6).toNat ((s'.gpr .r3).setWidth 32)
      (Spec.RsaPkcs1Enc.encrypt (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) (msgB s) (psB s)))

theorem zbit_mask (l : List Byte) : zbit l - BitVec.ofNat 64 1 = maskOf (zbit l = 0) := by
  unfold maskOf zbit; split <;> decide

theorem zbit_eq_zero {l : List Byte} : zbit l = 0 ↔ l.all (· != 0) = true := by
  unfold zbit; split <;> simp_all

theorem encrypt_eq {s : State} (hp : PreE s) :
    Spec.RsaPkcs1Enc.encrypt (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) (msgB s) (psB s) =
      if zbit (psB s) = 0 then pubOut s else none := by
  have := hp.ml; have := hp.pl
  unfold Spec.RsaPkcs1Enc.encrypt pubOut
  simp only [bytesAt_length, zbit_eq_zero]
  by_cases h : (psB s).all (· != 0) = true
  · rw [ite_eq_left ⟨by omega, by omega, h⟩, ite_eq_left h]
  · rw [ite_eq_right (fun h' => h h'.2.2), ite_eq_right h]

/-- Writes of the frame above the slots keep `Saves`. -/
theorem saves_frameW1 {s t w : State} {rs : List Reg} (h : Saves s t) (o : Keep rs t w) {e n : Nat}
    (he : oLr + 8 ≤ e) (hen : e + n ≤ frameBytes) (hm : Frame [⟨fb s + BitVec.ofNat 64 e, n⟩] t.mem w.mem)
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) : Saves s w := by
  have hd : ∀ {d' k : Nat}, d' + k ≤ oLr + 8 → ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 e, n⟩ : Region)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d', k⟩ r := fun hk r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by omega)) (by unfold oLr at hk; omega) (by unfold frameBytes at hen; omega)
  exact ⟨o.sp.trans h.sp, o.wr.trans h.wr,
    fun r hr => (o.gpr _ (not_kept hrs (List.mem_append_right _ hr))).trans (h.hi r hr),
    h.sv.frame_in saved_offs hm (hd (by decide)),
    by rw [hm.readW (Region.contains_self _ _) (hd (by decide)) (by decide)]; exact h.ls⟩

theorem tail_ok {s t : State} (hp : PreE s) (ha : AfterCall s t) :
    WP isa tail t fun w => Post s (freed frameBytes w) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  unfold tail maskArgs
  refine WP.seq (wp_addSp fun t₁ o₁ e₁ => ?_)
  rw [ha.sv.sp, BitVec.add_zero] at e₁
  refine wp_ld (a := fb s + BitVec.ofNat 64 oZ) (by rw [e₁])
    (by rw [o₁.rd, o₁.wr, ha.sv.wr]; exact in_fr' s _ _ (by decide) (by decide)) fun t₂ o₂ e₂ =>
    wp_subi fun t₃ o₃ e₃ => wp_and fun t₄ o₄ e₄ => wp_mov fun t₅ o₅ e₅ => wp_mov fun t₆ o₆ e₆ => wp_nil ?_
  have O₆ : Only [.r12, .r9, .r9, .r3, .r11, .r8] t t₆ :=
    o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans o₆))))
  have sv₆ : Saves s t₆ := ha.sv.keep O₆.keep (R := []) (by rw [O₆.mem]; exact Frame.refl _ _)
    (fun r h => nomatch h)
  have r9₆ : t₆.gpr .r9 = maskOf (zbit (psB s) = 0) := by
    rw [o₆.get .r9, o₅.get .r9, o₄.get .r9, e₃, e₂, o₁.mem, ha.slot, zbit_mask]
  have r3₆ : t₆.gpr .r3 = t.gpr .r3 &&& maskOf (zbit (psB s) = 0) := by
    rw [o₆.get .r3, o₅.get .r3, e₄, o₃.get .r3, o₂.get .r3, o₁.get .r3, ← r9₆, o₆.get .r9, o₅.get .r9,
      o₄.get .r9]
  have hout : ∀ i < (s.gpr .r6).toNat, InRegions (fr s :: s.wr) (s.gpr .r3 + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨oR s, List.mem_cons_of_mem _ (by rw [hp.hwr]; simp),
      Offset.contains_base _ (by rw [hp.ok]; omega) (by have := hp.wo; omega)⟩
  have hdo : (kR s).Disjoint ⟨s.gpr .r3, (s.gpr .r6).toNat⟩ := by rw [← oR_eq hp]; exact hp.ko
  refine WP.seq (WP.mono (Rec.maskLoop_ok (p := s.gpr .r3) (n := (s.gpr .r6).toNat) (by omega) (by omega)
    (by rw [o₆.get .r11, e₅, o₄.get .r28, o₃.get .r28, o₂.get .r28, o₁.get .r28, ha.r28])
    (by rw [e₆, o₅.get .r29, o₄.get .r29, o₃.get .r29, o₂.get .r29, o₁.get .r29, ha.r29]; simp)
    (fun i hi => by rw [sv₆.wr]; exact hout i hi)) fun u ⟨ku, mu⟩ => ?_)
  have hB : Spec.Rsa.bytesAt t₆.mem (s.gpr .r3) (s.gpr .r6).toNat =
      Spec.Rsa.bytesAt t.mem (s.gpr .r3) (s.gpr .r6).toNat := by rw [O₆.mem]
  rw [r9₆, maskOf_bytes, bytesAt_length, hB] at mu
  generalize hX : (if zbit (psB s) = 0 then Spec.Rsa.bytesAt t.mem (s.gpr .r3) (s.gpr .r6).toNat
    else List.replicate (s.gpr .r6).toNat 0) = X at mu
  have hXl : X.length = (s.gpr .r6).toNat := by rw [← hX]; split <;> simp [bytesAt_length]
  have svu : Saves s u := sv₆.keep ku (R := [⟨s.gpr .r3, (s.gpr .r6).toNat⟩])
    (by have h := frame_writeBytes t₆.mem (s.gpr .r3) X; rw [hXl] at h; rw [mu]; exact h)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hdo)
  unfold wipeArgs
  refine WP.seq (wp_addSp fun w₁ p₁ f₁ => wp_addi fun w₂ p₂ f₂ => wp_mov fun w₃ p₃ f₃ =>
    wp_li (by decide) fun w₄ p₄ f₄ => wp_nil ?_)
  rw [svu.sp, BitVec.add_zero] at f₁
  have P₄ : Only [.r12, .r4, .r11, .r0] u w₄ := p₁.trans (p₂.trans (p₃.trans p₄))
  have svw : Saves s w₄ := svu.keep P₄.keep (R := []) (by rw [P₄.mem]; exact Frame.refl _ _)
    (fun r h => nomatch h)
  have hem : ∀ {i : Nat}, i < (s.gpr .r6).toNat → InRegions (fr s :: s.wr) (emA s + BitVec.ofNat 64 i) 1 :=
    fun hi => by
      rw [add_ofNat_ofNat]; exact in_fr s _ (by unfold oEM oEM1; omega) (by unfold oEM oEM1 frameBytes; omega)
  refine WP.seq (WP.mono (fill_ok (p := emA s) (n := (s.gpr .r6).toNat) (b := 0) (by omega) (by omega)
    (by rw [p₄.get .r4, p₃.get .r4, f₂, f₁])
    (by rw [p₄.get .r11, f₃, p₂.get .r29, p₁.get .r29, ku.get .r29, o₆.get .r29, o₅.get .r29, o₄.get .r29,
      o₃.get .r29, o₂.get .r29, o₁.get .r29, ha.r29]; simp)
    (by rw [f₄]; rfl)
    (fun i hi => by rw [svw.wr]; exact hem hi)) fun w₅ ⟨k₅, m₅⟩ => ?_)
  have fr₅ : Frame [⟨fb s + BitVec.ofNat 64 oEM, (s.gpr .r6).toNat⟩] w₄.mem w₅.mem := by
    have h := frame_writeBytes w₄.mem (emA s) (List.replicate (s.gpr .r6).toNat (0 : Byte))
    rw [List.length_replicate] at h; rw [m₅]; exact h
  have sv₅ : Saves s w₅ := saves_frameW1 svw k₅ (by decide) (by unfold oEM oEM1 frameBytes; omega) fr₅
  refine WP.mono (restore_ok sv₅) fun w' ⟨habi, h3, hm⟩ => ⟨habi, fun hc => ?_⟩
  have hbytes : Spec.Rsa.bytesAt w'.mem (s.gpr .r3) (s.gpr .r6).toNat = X := by
    rw [hm, Proof.RsaPkcs1Sig.bytes_apart (R := ⟨s.gpr .r3, (s.gpr .r6).toNat⟩) fr₅
      (hdo.sub_left (em_sub hp)).symm (by dsimp only; omega), P₄.mem, mu, bytes_written hXl (by omega)]
  have hr : w'.gpr .r3 = t.gpr .r3 &&& maskOf (zbit (psB s) = 0) := by
    rw [h3, k₅.get .r3, P₄.get .r3, ku.get .r3, r3₆]
  rw [freed_mem, freed_gpr, hr, encrypt_eq hp]
  have hres := ha.res hc
  unfold maskOf
  by_cases hz : zbit (psB s) = 0
  · simp only [hz, ↓reduceIte, BitVec.and_allOnes] at hX ⊢
    rw [← hX] at hbytes
    revert hres
    cases pubOut s with
    | none => exact fun h => ⟨h.1, hbytes.trans h.2⟩
    | some y => exact fun h => ⟨h.1, hbytes.trans h.2⟩
  · simp only [hz, ↓reduceIte] at hX ⊢
    rw [← hX] at hbytes
    exact ⟨by simp, hbytes⟩

theorem preCall_ok {s w : State} (hp : PreE s) (hw : Setup s w) : WP isa preCall w (AtCall s) :=
  em_ok hp hw fun _ hy => callArgs_ok hp hy

theorem code_ok {s : State} (hp : PreE s) : WP isa code s (Post s) := by
  unfold code
  refine WP.alloc (by decide) hp.sp1 ?_
  unfold body
  refine WP.seq (WP.mono (setup_ok hp (by rw [allocated_sp]) (by rw [allocated_wr, frameR_eq])
    (by rw [allocated_rd])
    (by rw [allocated_mem]; exact Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ (fb_contains s))
    (fun r _ => by rw [allocated_gpr]) (by rw [allocated_lr])) fun w hw => ?_)
  refine WP.seq (WP.mono (preCall_ok hp hw) fun t ht => ?_)
  exact WP.seq (WP.mono (call_ok hp ht) fun t' ht' => tail_ok hp ht')

/-- The correctness of `vg_rsa_pkcs1_encrypt_precomputed`, against its
shared contract. -/
theorem code_correct (s : State) (h : (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi frameBytes).pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi frameBytes).post s s' := by
  obtain ⟨t, s', he, habi, hr⟩ := code_ok (preE_of h)
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs,
    stackArgs_six, List.append_eq]
  exact hr

end VG.Proof.RsaPkcs1Enc.PPC64LE.Enc
