import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTD
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Small

/-!
# An RSA key from its primes on AArch64: constant time, `d` too small

`smallMask` (`smallMask_ct`): the constant 1, word `w` of `[aC]` set
(`smallBlk_k`, whose base the taint analysis sees from `w` and the stride),
`ltA`, and `kOk` and'ed in; the facts after it from `smallMask_k`
(`KG FF`, which is `KFront` but for `KS`: `FF.front`). The mask in `x15`,
on which the code branches, is the status' (`FF.x15`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- After `smallMask`: `d` with `kOk`, and the mask of `d` too small in `x15`. -/
abbrev FF : KIn → State → Prop := fun I t => PF I t ∧ DRes I I.E I.L t.mem ∧
  ∃ ok : Bool, word t.mem I.B (8 * kOk) = mask ok ∧ ((∃ d, Spec.Rsa.inverse I.E I.L = some d) ↔ ok = true) ∧
    t.gpr .x15 = mask (decide (av I t.mem aDd ≤ 2 ^ (8 * I.pl)) && ok)

theorem FF.front {I : KIn} {s₀ t : State} (h : KS I s₀ t) (hf : FF I t) : KFront I s₀ t :=
  ⟨h, hf.1.1, hf.1.2.1, hf.1.2.2.1, hf.1.2.2.2.1, hf.1.2.2.2.2.1, hf.2.1, hf.2.2⟩

theorem smallMask_eq : smallMask = constA 1 ++ (([.block (ws ++ (base aC .x16 ++ ([.lsr .x .x3 .x12 1,
    .lsl .x .x3 .x3 3, .add .x .x16 .x16 .x3, movi .x3 1, st .x3 .x16] : List Instr)))] : List (Prog isa)) ++
    (ltA aDd aC ++ ([.block [ldh .x3 kOk, .logic .and .x .x15 .x15 .x3]] : List (Prog isa)))) := by
  simp only [smallMask, List.append_assoc]

/-- `smallMask`'s middle block: word `W / 2` of `[aC]` set, for any contents
of `[aC]`. -/
theorem smallBlk_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) :
    WP isa (.block (ws ++ (base aC .x16 ++ ([.lsr .x .x3 .x12 1, .lsl .x .x3 .x3 3, .add .x .x16 .x16 .x3, movi .x3 1,
      st .x3 .x16] : List Instr)))) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aC] s.mem t.mem := by
  have hn := h.ws.scr.nowrap
  have hw2 := h.ws.w2
  have sC := h.ws.sl (j := aC) (by decide)
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (wsBase16_ok h aC) fun s₂ ⟨⟨h16, h12, _, m₂⟩, k₂⟩ => ?_
  have hs₂ := h.ws.scr.congr k₂.wr
  have ew : BitVec.ofNat 64 I.W >>> 1 = BitVec.ofNat 64 (I.W / 2) := ofNat_shr1 (by omega)
  have e8 : BitVec.ofNat 64 (I.W / 2) <<< 3 = BitVec.ofNat 64 (8 * (I.W / 2)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show I.W / 2 < 2 ^ 64 by omega)]
    omega
  have ea : off I.B (slot I.W aC) + BitVec.ofNat 64 (8 * (I.W / 2)) = off I.B (slot I.W aC + 8 * (I.W / 2)) :=
    VG.Offset.add_add _ _ _
  refine WP.mono (WP.keep [.x3, .x16] (Q := fun t => t.mem = s.mem.writeW (off I.B (slot I.W aC + 8 * (I.W / 2)))
      (1 : BitVec 64)) (by
    brun [h16, h12, ew, e8, ea, hs₂.st (d := slot I.W aC + 8 * (I.W / 2)) (by omega), m₂]
    rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨m₃, k₃⟩ => ?_
  exact h.arrW (j := aC) (by decide) (by omega) (by omega) ⟨_, m₃⟩ (k₂.trans k₃)

/-- `smallMask` leaks the same in runs with the same public data, and leaves
`FF` (`smallMask_k`). -/
theorem smallMask_ct : RelCT isa (Two (KG DF)) (seqs smallMask) (Two (KG FF)) := by
  refine kg_ct ?_ fun I _ s h L ⟨hf, ok, hok, hiff, hdd⟩ => ?_
  · refine RelCT.mono (P := Two (KG NF)) ?_ (fun _ _ h => two_kg (fun _ _ _ => trivial) h) fun _ _ h => h
    rw [smallMask_eq]
    refine rs_app (by simp [constA]) (by simp) (constA_ct 1 (by decide) (stab_nf _ _) (by taint_decide)
      (by taint_decide)) ?_
    refine kg_app0 (G := NF) (by simp) (by simp [ltA, cmpA]) (show RelCT isa _ (seqs [.block _]) _ from
      kg_wsb0 (by taint_decide)) (fun I _ s h _ _ => WP.mono (smallBlk_k h) fun _ ⟨ht, _⟩ => ⟨ht, trivial⟩) ?_
    exact rs_app (by simp [ltA, cmpA]) (by simp) (ltA_ct (G := NF) (by decide) (by decide)
      (fun _ _ _ _ _ _ _ _ => trivial) (by taint_decide))
      (show RelCT isa _ (seqs [.block _]) _ from two_taint [.x0] (pins_kg NF) (by taint_decide))
  · have e8 : 64 * (I.pl / 8) = 8 * I.pl := by have := L.pl8; omega
    refine WP.mono (smallMask_k h L.W hok) fun t ⟨ht, f, h15⟩ => ?_
    have hw : word t.mem I.B (8 * kOk) = mask ok := (f.word (by decide) (by decide) (by decide)).trans hok
    have hD : av I t.mem aDd = av I s.mem aDd := f.av (by decide) (by decide) (by decide) h.hZ
    refine ⟨ht, PF.frame (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.hZ hf f,
      ⟨ok, hw, hiff, fun d hd => hD.trans (hdd d hd)⟩, ok, hw, hiff, ?_⟩
    rw [h15, hD, e8]

/-- The status 2: `d` exists and is at most `2^(8 pl)`. -/
theorem KIn.st_two {I : KIn} : I.st = 2 ↔ ∃ d, Spec.Rsa.inverse I.E I.L = some d ∧ d ≤ 2 ^ (8 * I.pl) := by
  have hW : 8 * I.pl = 16 * I.pl / 2 := by omega
  have hswap : (if I.P₀ < I.Q₀ then (I.Q₀, I.P₀) else (I.P₀, I.Q₀)) = (I.P, I.Q) := by
    by_cases h : I.P₀ < I.Q₀ <;> simp [KIn.P, KIn.Q, h]
  simp only [KIn.st]
  constructor
  · intro h2
    unfold Spec.RsaKeyGen.keyOp at h2
    generalize hk : Spec.RsaKeyGen.keyFromPrimes (16 * I.pl) (Spec.Rsa.os2ip I.eb) (Spec.Rsa.os2ip I.pb)
      (Spec.Rsa.os2ip I.qb) = r at h2
    unfold Spec.RsaKeyGen.keyFromPrimes at hk
    rw [hswap] at hk
    dsimp only at hk
    rw [show Nat.lcm (I.P - 1) (I.Q - 1) = I.L from rfl, ← hW] at hk
    rcases hi : Spec.Rsa.inverse I.E I.L with _ | d
    · rw [hi] at hk; subst hk; simp [Spec.RsaKeyGen.keyStatus] at h2
    · rw [hi] at hk
      dsimp only at hk
      by_cases hd : d ≤ 2 ^ (8 * I.pl)
      · exact ⟨d, rfl, hd⟩
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hd)] at hk
        obtain ⟨x, rfl⟩ : ∃ x, r = .inl x := by
          rw [← hk]
          split
          · exact ⟨_, rfl⟩
          · split <;> exact ⟨_, rfl⟩
        cases x <;> simp [Spec.RsaKeyGen.keyStatus] at h2
  · rintro ⟨d, hd, hsm⟩
    have hr : Spec.RsaKeyGen.keyFromPrimes (16 * I.pl) (Spec.Rsa.os2ip I.eb) (Spec.Rsa.os2ip I.pb)
        (Spec.Rsa.os2ip I.qb) = .inr () := by
      unfold Spec.RsaKeyGen.keyFromPrimes
      rw [hswap]
      dsimp only
      rw [show Nat.lcm (I.P - 1) (I.Q - 1) = I.L from rfl, hd, ← hW]
      dsimp only
      rw [ite_eq_left hsm]
    unfold Spec.RsaKeyGen.keyOp
    rw [hr]
    rfl

/-- The branch's mask is the status' (x86-64's `front_zf`). -/
theorem FF.x15 {I : KIn} {t : State} (h : FF I t) : t.gpr .x15 = mask (decide (I.st = 2)) := by
  obtain ⟨-, ⟨_, _, _, hdd⟩, ok, _, hiff, h15⟩ := h
  rw [h15]
  refine congrArg mask ?_
  cases hc : ok
  · rw [hc] at hiff
    rw [Bool.and_false]
    refine (decide_eq_false fun h => ?_).symm
    obtain ⟨d, hd, _⟩ := KIn.st_two.mp h
    exact absurd (hiff.mp ⟨d, hd⟩) (by simp)
  · rw [hc] at hiff
    obtain ⟨d, hd⟩ := hiff.mpr rfl
    rw [Bool.and_true, hdd d hd]
    exact decide_eq_decide.mpr ⟨fun h => KIn.st_two.mpr ⟨d, hd, h⟩, fun h => by
      obtain ⟨d', hd', h'⟩ := KIn.st_two.mp h
      rw [hd] at hd'; cases hd'; exact h'⟩

end VG.Proof.RsaKeyGen.AArch64.Key
