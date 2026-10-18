module

public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyDeriveStep
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignBody
import VerifiedGarbage.Proof.Framework.Omega

/-! # Key generation after an accepted domain: the sampler, then the derivation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_sampleStatus_le (S : Spec.Dsa.Random.Sample) : VG.Proof.Dsa.Random.sampleStatus S ≤ 2 := by
  unfold VG.Proof.Dsa.Random.sampleStatus; split
  · decide
  · split <;> decide

/-- The draw and its status stored: the frame state, the flag for success, and x. -/
theorem keygen_sampled {extra : Nat} {s t b : State} {h : GenerateKeyABI extra s}
    {hq : 1 < Spec.Dsa.decodeBE (keygenQBytes s)} {draws : Nat} (ht : KeygenState h 0 t)
    (hrb : RandomReady (keygenContextOf h t.mem hq) 0 draws b) (hkb : Keep randomVolatile t b)
    :
    WP isa (.seq Random.sample (.block (Random.store Random.oStatus .x0 ++ ([.subImm .x .x4 .x0 1] : List Instr)))) b
      fun d =>
        KeygenState h (keygenDraw s).used d ∧
        d.gpr .x4 = BitVec.ofNat 64 (VG.Proof.Dsa.Random.sampleStatus (keygenDraw s)) - 1 ∧
        word d.mem (randomBase s) Random.oStatus =
          BitVec.ofNat 64 (VG.Proof.Dsa.Random.sampleStatus (keygenDraw s)) ∧
        (∀ k, (keygenDraw s).scalar = some k →
          Spec.Rsa.bytesAt d.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat =
            Spec.Dsa.encodeBE (s.gpr .x6).toNat k) := by
  have hd : randomRemaining (keygenContextOf h t.mem hq) 0 128 = keygenDraw s := by
    unfold randomRemaining; rfl
  refine WP.seq (WP.mono (random_sample_encoded hq hrb)
    fun c ⟨hcax, _, _, hnonce, _, ⟨draws', hrc⟩, hkc⟩ => ?_)
  rw [hd, Nat.zero_add] at hrc
  rw [hd] at hcax hnonce
  have hkc' : Keep randomVolatile b c := hkc.mono (by decide)
  have hkt : Keep randomVolatile t c := (hkb.trans hkc').mono (by decide)
  have hsc : KeygenState h (keygenDraw s).used c :=
    ht.of_ready hrc hkt
  refine WP.mono (keygen_storeStatus_ok hsc.scr hsc.sp) fun d ⟨hdm, hdz, hkd⟩ => ?_
  have hsd := hsc.write_status hdm (hkd.mono (by decide))
  rw [hcax] at hdm hdz
  refine ⟨hsd, hdz, by rw [hdm, word_writeW_self], fun k hk => ?_⟩
  have hn := hnonce k hk
  simp only [keygenContextOf, keygen_q_length h] at hn
  have hql : (s.gpr .x6).toNat ≤ 32 := by
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega
  rw [hdm]
  exact (random_outside_bytes (writeW_outside _ _ _ (by decide))
    (show Random.oNonce + (s.gpr .x6).toNat ≤ 2 ^ 64 by unfold Random.oNonce; omega)
    (Or.inr (by decide))).trans hn

theorem keygen_generate (v : Backend) {s t : State} {h : GenerateKeyABI v.stack s}
    (ht : KeygenState h 0 t) (hQ : word t.mem (randomBase s) Random.oQ = s.gpr .x3 + s.gpr .x5)
    (hc : keygenChecked s = true) :
    WP isa (GenerateKey.generate (keygenDeriveName v) (Generate.deriveKey v.mul)) t
      (KeygenGenerated h) := by
  have hq := keygen_q_valid h hc
  have hres := keygen_result_checked h hc
  unfold GenerateKey.generate
  refine WP.seq (WP.mono (keygen_prepare ht hQ hq) fun b ⟨hbz, ⟨draws, hrb⟩, hkb⟩ => ?_)
  refine WP.ite false (by simp [eval, State.read, hbz]) (fun he => Bool.noConfusion he) fun _ => ?_
  apply WP.assoc
  refine WP.seq (WP.mono (keygen_sampled ht hrb hkb) fun d ⟨hsd, hdz, hdw, hnd⟩ => ?_)
  have hlt : VG.Proof.Dsa.Random.sampleStatus (keygenDraw s) < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (keygen_sampleStatus_le _) (by decide)
  cases hx : (keygenDraw s).scalar with
  | none =>
    have hs1 : VG.Proof.Dsa.Random.sampleStatus (keygenDraw s) ≠ 1 := by
      simp only [VG.Proof.Dsa.Random.sampleStatus, hx]; split <;> decide
    refine WP.ite false (by
      change some (d.gpr .x4 == (0#64)) = some false
      rw [hdz]
      congr 1
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro he
      apply hs1
      have he' : BitVec.ofNat 64 (VG.Proof.Dsa.Random.sampleStatus (keygenDraw s)) = 1 :=
        by simpa only [BitVec.sub_eq_iff_eq_add, BitVec.zero_add] using he
      have := congrArg BitVec.toNat he'
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this)
      (fun he => Bool.noConfusion he) fun _ => ?_
    refine WP.block_nil ?_
    unfold KeygenGenerated
    rw [hres]
    simp only [hx]
    exact ⟨hsd, hdw, fun h1 => absurd h1 hs1⟩
  | some k =>
    have hs1 : VG.Proof.Dsa.Random.sampleStatus (keygenDraw s) = 1 := by
      simp only [VG.Proof.Dsa.Random.sampleStatus, hx]
    rw [hs1] at hdz
    refine WP.ite true (by change some (d.gpr .x4 == (0#64)) = some true; rw [hdz]; rfl) (fun _ => ?_) (fun he => Bool.noConfusion he)
    refine WP.mono (keygen_derive_step v hsd (hnd k hx)) fun u ⟨hu, hw, hb⟩ => ?_
    unfold KeygenGenerated
    rw [hres]
    simp only [hx]
    exact ⟨hu, hw, fun _ => hb⟩

end VG.Proof.Dsa.AArch64
