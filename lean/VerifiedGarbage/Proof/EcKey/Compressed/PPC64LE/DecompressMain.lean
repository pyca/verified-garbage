module

public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Main
public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE.Decompress
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.EcKey.Compressed
public import VerifiedGarbage.Proof.EcKey.Compressed.Root

import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Peer
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Poly
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.RootPow
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Select
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Check
import VerifiedGarbage.Proof.EcKey.Compressed.Decode
import VerifiedGarbage.Proof.EcKey.PPC64LE.Finish
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Peer
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Validate
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Finish
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.GetElem
/-!
# SEC 1 point decompression on PPC64LE: the whole function

`decompress_ok`: `decompress` writes `04 ‖ x ‖ y`, for `y` the root of the
tag's parity that a square-root method `root` gives (`CandidateCorrect`:
the code's candidate computes it), or zeros, and returns 1 or 0, restoring
the callee-saved registers and `lr`: the signature's setup, the key's
parsing (`decompressPeer_ok`), `x³ + a x + b` (`rhs_ok`), the candidate,
the root of the tag's parity (`selectRoot_ok`), its checks
(`checkRoot_ok`), and the public key's result (`pkFinishWith_ok`).
`decompress_correct`: the same, against `decompressContract`.
-/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/PPC64LE/DecompressContract.lean`, which only this module imported.
section

/-!
# SEC 1 point decompression on PPC64LE: the contract the proof is written against

`vg_ec_<curve>_decompress_public_key(out, public, scratch)`, with the
arguments in `r3`–`r5` and the result in `r3` (ELFv2), for any curve, whose
result is the functional decoder's (`Impl.EcKey.Compressed.decode`) with a
square root `root`; `decompress_implies` moves it to
`Spec.EcKey.Instance.decompressPublicKeyContract` by the root's facts
(`RootFacts`).
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE

def decompressContract (C : Spec.Weierstrass.Curve)
    (root : Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C) : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 2 * C.len + 1⟩
    let pk : Region := ⟨s.gpr .r4, C.len + 1⟩
    let ws : Region := ⟨s.gpr .r5, 8192⟩
    s.rd = [pk] ∧ s.wr = [out, ws] ∧
      pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
      (s.gpr .r3).toNat + (2 * C.len + 1) ≤ 2 ^ 64 ∧
      (s.gpr .r4).toNat + (C.len + 1) ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match Impl.EcKey.Compressed.decode C root (Spec.EcKey.bytesAt s.mem (s.gpr .r4) (C.len + 1)) with
    | some Q => s'.gpr .r3 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .r3) (2 * C.len + 1) = Spec.EcKey.encodePoint Q
    | none => s'.gpr .r3 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .r3) (2 * C.len + 1) = List.replicate (2 * C.len + 1) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5

theorem decompress_implies (I : Spec.EcKey.Instance)
    (root : Spec.Weierstrass.Fe I.curve → Spec.Weierstrass.Fe I.curve)
    (hf : RootFacts root)
    (hsat : ∃ s, (I.decompressPublicKeyContract abi 0).pre s) :
    (decompressContract I.curve root).Implies (I.decompressPublicKeyContract abi 0) where
  pre := by
    sig_implies_pre [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, decompressContract]
  post := by
    intro s s' _ h
    sig_post [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, decompressContract]
    cases he : Impl.EcKey.Compressed.decode I.curve root
        (Spec.EcKey.bytesAt s.mem (s.gpr .r4) (I.curve.len + 1)) with
    | none =>
      simp only [decompressContract, he] at h
      exact Or.inr ⟨by rw [h.1]; rfl, (decode_none_iff hf _).mp he, h.2⟩
    | some Q =>
      simp only [decompressContract, he] at h
      exact Or.inl ⟨by rw [h.1]; rfl, Q, decode_sound he, h.2⟩
  pub := by
    sig_implies_pub [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, decompressContract]
  sat := hsat

/-- A state satisfying the precondition, for encodings of `len` bytes. -/
def decompressSatState (len : Nat) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, len + 1⟩]
  wr := [⟨0x1000, 2 * len + 1⟩, ⟨0x8000, 8192⟩]

end VG.Proof.EcKey.Compressed.PPC64LE
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Proof.Ecdh.PPC64LE VG.Spec.Weierstrass
open VG.Impl.Ecdh.PPC64LE (QY R2P BP QXM QYM W0 W1 W2 W3)
open VG.Impl.EcKey.Compressed.PPC64LE (args)
open VG.Impl.EcKey.Compressed (chooseRoot)

variable {c : Cfg}

/-! ## The square root's candidate -/

/-- The slots the candidate may write. -/
abbrev candSlots : List Nat := [EXPP, ACC, PT, T0, T1, T3, T4, T5, W0]

/-- What the candidate may write: its slots, the tables of `p - 2` and
`n - 2`, and the functions' own working space. -/
abbrev candW (c : Cfg) : List (Nat × Nat) :=
  slW c candSlots ++ [(bitsAt c.n 1, 64 * c.n), (bitsAt c.n 2, 64 * c.n), (own c.n, 64 * c.n)]

/-- The code's candidate computes `root` of what `W2` holds, in Montgomery
form, writing only `candW`. -/
def CandidateCorrect (c : Cfg) (root : Fe c.C → Fe c.C) : Prop :=
  ∀ (base : Addr) (s : State), WsReg s base → sv c base s W2 < c.C.p →
    sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p →
    WP isa (Impl.EcKey.Compressed.PPC64LE.rootCandidate c) s fun s' =>
      WsReg s' base ∧ Rk powClob s s' ∧ Unch base (candW c) s.mem s'.mem ∧ sv c base s' ACC < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) = root (toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2))

theorem candW_fixed (h7 : c.n < 10) : FixedOk c (candW c) :=
  (fixedOk_slW (by decide)).append (fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact fixedOk_tbl h7 1 _ (List.mem_singleton_self _)
    · exact fixedOk_tbl h7 2 _ (List.mem_singleton_self _)
    · exact fixedOk_own h7 _ (List.mem_singleton_self _))

theorem candW_le (h7 : c.n < 10) : ∀ w ∈ candW c, w.1 + w.2 ≤ size := by
  have hsz : size = 8192 := rfl
  have := own_below_bits c h7 0
  have := bitsAt_le c h7 (j := 0) (by decide)
  have := bitsAt_le c h7 (j := 1) (by decide)
  have := bitsAt_le c h7 (j := 2) (by decide)
  refine le_append (fun w hw => ?_) (fun w hw => ?_)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have hl : ∀ i ∈ candSlots, i < 45 := by decide
    have := sl_le c h7 (hl i hi)
    dsimp only; omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> (dsimp only; omega_arith)

theorem apart_candW (h7 : c.n < 10) {i : Nat} (hi : i < 45) (hw : i ∉ candSlots) :
    ∀ w ∈ candW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_slW hw) (fun w h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact apart_tbl h7 hi 1 _ (List.mem_singleton_self _)
    · exact apart_tbl h7 hi 2 _ (List.mem_singleton_self _)
    · exact apart_own h7 hi _ (List.mem_singleton_self _))

/-- For `p ≡ 3 mod 4`, the candidate is `rhs^((p+1)/4)`. -/
theorem candidateThree_correct (hc : CfgOk c) (hp : c.C.p % 4 = 3) :
    CandidateCorrect c Impl.EcKey.Compressed.rootThreeModFour := fun base s hw hB hO =>
  WP.mono (rootThree_ok hc hp hw hB hO) fun s' ⟨hw', k, U, lt, v⟩ =>
    ⟨hw', k, U.mono (fun w hw'' => by
      simp only [rootPowerW, List.mem_cons, List.not_mem_nil, or_false] at hw''
      rcases hw'' with rfl | rfl | rfl | rfl | rfl <;> simp [candW, slW]), lt,
      by rw [v]; simp only [Impl.EcKey.Compressed.rootThreeModFour, pow_eq_npow]⟩

/-! ## The key and its point -/

/-- The key's tag and `x`. -/
abbrev keyTag (s : State) : Byte := s.mem (s.gpr .r4)

/-- `x³ + a x + b`, for the key's `x`. -/
def keyRhs (c : Cfg) (s : State) : Fe c.C :=
  let x := Fin.ofNat c.C.p (keyX c s)
  x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b

/-- The root of the tag's parity, if there is one. -/
def keyRoot (c : Cfg) (root : Fe c.C → Fe c.C) (s : State) : Fe c.C :=
  chooseRoot (root (keyRhs c s)) ((keyTag s).toNat % 2)

/-- The code accepts the key: its tag `02` or `03`, `x < p`, and the root
squares to `x³ + a x + b` and has the tag's parity. -/
def DAccept (c : Cfg) (root : Fe c.C → Fe c.C) (s : State) : Prop :=
  ((keyTag s = 2 ∨ keyTag s = 3) ∧ keyX c s < c.C.p) ∧
    (keyRoot c root s * keyRoot c root s = keyRhs c s ∧ (keyRoot c root s).val % 2 = (keyTag s).toNat % 2)

instance (c : Cfg) (root : Fe c.C → Fe c.C) (s : State) : Decidable (DAccept c root s) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The arguments: `out` (`1 + 2 len` bytes), `public` (`1 + len` bytes)
and `scratch`, readable and writable as the contract says and apart from
each other as it says. -/
structure DPre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, 1 + c.C.len⟩]
  wr : s.wr = [⟨s.gpr .r3, 1 + 2 * c.C.len⟩, ⟨s.gpr .r5, size⟩]
  pk_sc : Region.Disjoint ⟨s.gpr .r4, 1 + c.C.len⟩ ⟨s.gpr .r5, size⟩
  out_sc : Region.Disjoint ⟨s.gpr .r3, 1 + 2 * c.C.len⟩ ⟨s.gpr .r5, size⟩
  out_fit : (s.gpr .r3).toNat + (1 + 2 * c.C.len) ≤ 2 ^ 64
  pk_fit : (s.gpr .r4).toNat + (1 + c.C.len) ≤ 2 ^ 64
  sc_fit : (s.gpr .r5).toNat + size ≤ 2 ^ 64

theorem DPre.setup {s : State} (hp : DPre c s) : SetupPre c args (s.write .r12 (s.gpr .r4)) := by
  have hr12 : (s.write .r12 (s.gpr .r4)).gpr .r12 = s.gpr .r4 := by simp only [write_gpr, ite_true]
  have hr5 : (s.write .r12 (s.gpr .r4)).gpr .r5 = s.gpr .r5 := by
    simp only [write_gpr, reduceCtorEq, ite_false]
  have hlen : c.C.len ≤ 1 + c.C.len := by omega_arith
  have hin : ∀ e, e + 8 ≤ c.C.len → InRegions ((s.write .r12 (s.gpr .r4)).rd ++ (s.write .r12 (s.gpr .r4)).wr)
      ((s.write .r12 (s.gpr .r4)).gpr .r12 + BitVec.ofNat 64 e) 8 := fun e he => by
    rw [hr12, write_rd, write_wr]
    exact inRegions_words (len := 1 + c.C.len) (by rw [hp.rd]; simp) (by have := hp.pk_fit; omega_arith) e (by omega_arith)
  have hd : Region.Disjoint ⟨(s.write .r12 (s.gpr .r4)).gpr .r12, c.C.len⟩
      ⟨(s.write .r12 (s.gpr .r4)).gpr .r5, size⟩ := by
    rw [hr12, hr5]; exact hp.pk_sc.sub_left (Region.sub_prefix hlen)
  have hf : ((s.write .r12 (s.gpr .r4)).gpr .r12).toNat + c.C.len ≤ 2 ^ 64 := by
    rw [hr12]; have := hp.pk_fit; omega_arith
  have hwr : (⟨(s.write .r12 (s.gpr .r4)).gpr .r5, size⟩ : Region) ∈ (s.write .r12 (s.gpr .r4)).wr := by
    rw [hr5, write_wr, hp.wr]; simp
  have hsf : ((s.write .r12 (s.gpr .r4)).gpr .r5).toNat + size ≤ 2 ^ 64 := by rw [hr5]; exact hp.sc_fit
  exact ⟨.inl rfl, by decide, by decide, by decide, by decide, hwr, hsf, hin, hin, hin, hd, hd, hd, hf, hf, hf⟩

theorem decompress_eq' (c : Cfg) : Impl.EcKey.Compressed.PPC64LE.decompress c =
    .seq (.block (mov .r12 .r4 :: c.setupWith args))
      (.seq (.block (Impl.EcKey.Compressed.PPC64LE.decompressPeer c))
      (.seq (fprog c.SP (Impl.EcKey.Compressed.PPC64LE.rhsOps c))
      (.seq (.seq (Impl.EcKey.Compressed.PPC64LE.rootCandidate c)
        (.seq (Impl.EcKey.Compressed.PPC64LE.selectRoot c) (Impl.EcKey.Compressed.PPC64LE.checkRoot c)))
      (.block (Impl.EcKey.Compressed.PPC64LE.decompressFinish c))))) := rfl

/-- `vg_ec_<curve>_decompress_public_key` writes the uncompressed key, or
zeros, and returns 1 or 0, restoring the callee-saved registers and `lr`. -/
theorem decompress_ok (hc : CfgOk c) {root : Fe c.C → Fe c.C} (hroot : CandidateCorrect c root)
    {s₀ : State} (hp : DPre c s₀) :
    WP isa (Impl.EcKey.Compressed.PPC64LE.decompress c) s₀ fun s' => CKeep s₀ s' ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .r3) (1 + 2 * c.C.len) =
        (if DAccept c root s₀ then 4 :: (toBytes c.C.len (keyX c s₀) ++ toBytes c.C.len (keyRoot c root s₀).val)
          else List.replicate (1 + 2 * c.C.len) 0) ∧
      s'.gpr .r3 = (if DAccept c root s₀ then 1 else 0) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hlhi := hc.len_hi
  have hl8 := hc.len8
  have hp3 := hc.p_ge
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  rw [decompress_eq']
  -- `public` to `r12`, and the setup.
  refine WP.seq (wp_step exec_mov (WP.mono (stage₀' hc hp.setup) fun s₂ ⟨S₂, kp₂⟩ => ?_))
  have hr5 : (s₀.write .r12 (s₀.gpr .r4)).gpr .r5 = s₀.gpr .r5 := by
    simp only [write_gpr, reduceCtorEq, ite_false]
  generalize hb : (s₀.write .r12 (s₀.gpr .r4)).gpr args.sc = base at S₂
  replace hb : s₀.gpr .r5 = base := hr5.symm.trans hb
  have hn := S₂.ws.nowrap
  have r12₂ : s₂.gpr .r12 = s₀.gpr .r4 := by
    rw [kp₂.gpr _ (by decide)]; simp only [write_gpr, ite_true]
  have W₂ : Outside base 0 size s₀.mem s₂.mem :=
    S₂.whole.outside fun w hw => by rw [List.mem_singleton.mp hw]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  have hpsc : Region.Disjoint ⟨s₀.gpr .r4, 1 + c.C.len⟩ ⟨base, size⟩ := by rw [← hb]; exact hp.pk_sc
  -- The key.
  refine WP.seq (WP.mono (decompressPeer_ok hc S₂.ws
    (by rw [r12₂]; exact hp.pk_fit) (by rw [r12₂, S₂.rk.rd, S₂.rk.wr, write_rd, write_wr, hp.rd]; simp)
    (by rw [r12₂]; exact hpsc) S₂.fixed.mp) fun s₃ ⟨hw₃, k₃, U₃, r2₃, bp₃, x₃, d₃, f₃⟩ => ?_)
  rw [r12₂] at x₃ d₃ f₃
  have K₃ := S₂.toKeep.step h7 (k₃.rk (rs' := peerClob)) (hU := U₃)
    (hW := (fixedOk_slW (by decide)).append fixedOk_flag)
    (hWs := le_append (fun w hw => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      have hl₃ : ∀ i ∈ [R2P, BP, E, D], i < 45 := by decide
      have := sl_le c h7 (hl₃ i hi); dsimp only; omega_arith)
      (fun w hw => by
        rw [List.mem_singleton.mp hw]; have := sl_le c h7 (i := FLAG) (by decide); dsimp only; omega_arith))
  have hq0 : s₂.mem (s₀.gpr .r4) = keyTag s₀ := by
    have := keep_of_disjoint' W₂ hpsc (by omega_arith) (i := 0) (by omega_arith) (by omega_arith)
    rwa [BitVec.add_zero] at this
  have x₃' : sv c base s₃ E = keyX c s₀ := by
    rw [x₃, bytesAt_keep W₂ (hpsc.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith) (by omega_arith)]
  rw [hq0] at d₃ f₃
  have hf₃ : flagW c base s₃ = mask64 ((keyTag s₀ = 2 ∨ keyTag s₀ = 3) ∧ keyX c s₀ < c.C.p) := by
    rw [f₃, S₂.flag, BitVec.allOnes_and, mask64_and, x₃']
  -- `x³ + a x + b`.
  refine WP.seq (WP.mono (rhs_ok hc K₃.ws r2₃ K₃.fixed.ap bp₃) fun s₄ ⟨hw₄, k₄, U₄, lt₄, v₄⟩ => ?_)
  have K₄ := K₃.step h7 k₄ (hU := U₄) (hW := (fixedOk_slW (by decide)).append (fixedOk_own h7))
    (hWs := le_append (fun w hw => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      have hl₄ : ∀ i ∈ [QXM, W1, W2, W3], i < 45 := by decide
      have := sl_le c h7 (hl₄ i hi); dsimp only; omega_arith)
      (fun w hw => by rw [List.mem_singleton.mp hw]; have := own_below_bits c h7 0; have := bitsAt_le c h7 (j := 0) (by decide); dsimp only; omega_arith))
  have e₄ : ∀ {i}, i < 45 → i ∉ [QXM, W1, W2, W3] → sv c base s₄ i = sv c base s₃ i := fun hi hl =>
    sv_unch U₄ h7 hn hi (apart_append (apart_slW hl) (apart_own h7 hi))
  have ew₄ : ∀ {i}, i < 45 → i ∉ [QXM, W1, W2, W3] → word s₄.mem base (c.sl i) = word s₃.mem base (c.sl i) :=
    fun hi hl => U₄.word (fun w hw => (apart_append (apart_slW hl) (apart_own h7 hi) w hw).imp
      (fun h => by omega_arith) id) (by have := sl_le c h7 hi; omega_arith)
  rw [x₃'] at v₄
  -- The candidate.
  refine WP.seq (WP.seq (WP.mono (hroot base s₄ K₄.ws lt₄ K₄.fixed.onep) fun s₅ ⟨hw₅, k₅, U₅, lt₅, v₅⟩ => ?_))
  have K₅ := K₄.step h7 k₅ (hU := U₅) (hW := candW_fixed h7) (hWs := candW_le h7)
  have e₅ : ∀ {i}, i < 45 → i ∉ candSlots → sv c base s₅ i = sv c base s₄ i := fun hi hl =>
    sv_unch U₅ h7 hn hi (apart_candW h7 hi hl)
  have ew₅ : ∀ {i}, i < 45 → i ∉ candSlots → word s₅.mem base (c.sl i) = word s₄.mem base (c.sl i) :=
    fun hi hl => U₅.word (fun w hw => (apart_candW h7 hi hl w hw).imp (fun h => by omega_arith) id)
      (by have := sl_le c h7 hi; omega_arith)
  rw [v₄] at v₅
  -- The root of the tag's parity.
  refine WP.seq (WP.mono (selectRoot_ok hc K₅.ws K₅.fixed.one K₅.fixed.zero) fun s₆ ⟨hw₆, k₆, U₆, lt₆, v₆⟩ => ?_)
  have K₆ := K₅.step h7 k₆ (hU := U₆) (hW := (fixedOk_slW (by decide)).append (fixedOk_own h7))
    (hWs := le_append (fun w hw => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      have hl₆ : ∀ i ∈ [QY, W0], i < 45 := by decide
      have := sl_le c h7 (hl₆ i hi); dsimp only; omega_arith)
      (fun w hw => by rw [List.mem_singleton.mp hw]; have := own_below_bits c h7 0; have := bitsAt_le c h7 (j := 0) (by decide); dsimp only; omega_arith))
  have e₆ : ∀ {i}, i < 45 → i ∉ [QY, W0] → sv c base s₆ i = sv c base s₅ i := fun hi hl =>
    sv_unch U₆ h7 hn hi (apart_append (apart_slW hl) (apart_own h7 hi))
  have ew₆ : ∀ {i}, i < 45 → i ∉ [QY, W0] → word s₆.mem base (c.sl i) = word s₅.mem base (c.sl i) :=
    fun hi hl => U₆.word (fun w hw => (apart_append (apart_slW hl) (apart_own h7 hi) w hw).imp
      (fun h => by omega_arith) id) (by have := sl_le c h7 hi; omega_arith)
  have tagD : word s₅.mem base (c.sl D) = (keyTag s₀).setWidth 64 := by
    rw [ew₅ (by decide) (by decide), ew₄ (by decide) (by decide), d₃]
  have tagN : (word s₅.mem base (c.sl D)).toNat = (keyTag s₀).toNat := by
    rw [tagD, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))]
  rw [v₅, tagN] at v₆
  have y₆ : Fin.ofNat c.C.p (sv c base s₆ QY) = keyRoot c root s₀ := v₆
  have yv₆ : sv c base s₆ QY = (keyRoot c root s₀).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt lt₆] using congrArg Fin.val y₆
  -- The checks.
  have w2₆ : sv c base s₆ W2 = sv c base s₄ W2 :=
    (e₆ (by decide) (by decide)).trans (e₅ (by decide) (by decide))
  have r2₆ : sv c base s₆ R2P = c.R * c.R % c.C.p := by
    rw [e₆ (by decide) (by decide), e₅ (by decide) (by decide), e₄ (by decide) (by decide)]; exact r2₃
  have fl₆ : flagW c base s₆ = mask64 ((keyTag s₀ = 2 ∨ keyTag s₀ = 3) ∧ keyX c s₀ < c.C.p) := by
    rw [flagW, ew₆ (i := FLAG) (by decide) (by decide), ew₅ (by decide) (by decide),
      ew₄ (by decide) (by decide), ← flagW, hf₃]
  refine WP.mono (checkRoot_ok hc K₆.ws lt₆ (by rw [w2₆]; exact lt₄) r2₆ fl₆) fun s₇ ⟨hw₇, k₇, U₇, f₇⟩ => ?_
  have K₇ := K₆.step h7 k₇ (hU := U₇) (hW := ((fixedOk_slW (by decide)).append (fixedOk_own h7)).append fixedOk_flag)
    (hWs := le_append (le_append (fun w hw => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      have hl₇ : ∀ i ∈ [QYM, W1, W3], i < 45 := by decide
      have := sl_le c h7 (hl₇ i hi); dsimp only; omega_arith)
      (fun w hw => by rw [List.mem_singleton.mp hw]; have := own_below_bits c h7 0; have := bitsAt_le c h7 (j := 0) (by decide); dsimp only; omega_arith))
      (fun w hw => by rw [List.mem_singleton.mp hw]; have := sl_le c h7 (i := FLAG) (by decide); dsimp only; omega_arith))
  have e₇ : ∀ {i}, i < 45 → i ∉ [QYM, W1, W3] → i ≠ FLAG → sv c base s₇ i = sv c base s₆ i := fun hi hl hf =>
    sv_unch U₇ h7 hn hi (apart_append (apart_append (apart_slW hl) (apart_own h7 hi)) (apart_flag h0 hf))
  have hacc : flagW c base s₇ = mask64 (decide (DAccept c root s₀) = true) := by
    have hD₆ : (word s₆.mem base (c.sl D)).toNat = (keyTag s₀).toNat := by
      rw [ew₆ (by decide) (by decide), tagN]
    rw [f₇, y₆, w2₆, v₄, yv₆, hD₆]
    simp only [mask64, decide_eq_true_eq, DAccept, keyRhs, and_assoc]
  have h14 : s₇.gpr .r14 = s₀.gpr .r3 := by
    rw [K₇.r14]; simp only [write_gpr, reduceCtorEq, ite_false]
  have x₇ : sv c base s₇ E = keyX c s₀ := by
    rw [e₇ (by decide) (by decide) (by decide), e₆ (by decide) (by decide), e₅ (by decide) (by decide),
      e₄ (by decide) (by decide), x₃']
  have y₇ : sv c base s₇ QY = (keyRoot c root s₀).val := by
    rw [e₇ (by decide) (by decide) (by decide), yv₆]
  -- The result.
  refine WP.mono (VG.Proof.EcKey.PPC64LE.pkFinishWith_ok hc (x := E) (y := QY) (by decide) (by decide) K₇.ws h14
    hp.out_fit (by rw [K₇.rk.wr, write_wr, hp.wr]; simp) (by rw [← hb]; exact hp.out_sc) _ hacc)
    fun s' ⟨bytes, r3, lr, r14, r31, rk, _⟩ => ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro r hr
    have hsv := K₇.fixed.saved
    have hcases : ∀ r ∈ preserved, r = .r14 ∨ r = .r31 ∨
        (r ∉ [Reg.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] ∧ r ∉ work) := by decide
    rcases hcases r hr with rfl | rfl | ⟨h₁, h₂⟩
    · rw [r14, hsv (.r14, 0) (by decide)]; simp only [write_gpr, reduceCtorEq, ite_false]
    · rw [r31, hsv (.r31, 8) (by decide)]; simp only [write_gpr, reduceCtorEq, ite_false]
    · have h12 : r ≠ .r12 := fun h => h₂ (by rw [h]; decide)
      rw [rk.gpr r h₁, K₇.rk.gpr r h₂]; simp only [write_gpr, h12, ite_false]
  · rw [rk.sp, K₇.rk.sp, write_sp]
  · rw [lr, K₇.fixed.savedLr, write_lr]
  · rw [bytes, x₇, y₇]
    by_cases hk : DAccept c root s₀ <;> simp [hk]
  · rw [r3]; by_cases hk : DAccept c root s₀ <;> simp [hk]

/-- The key's bytes: its tag, then `x`. -/
theorem key_bytes (m : Mem) (p : Addr) (L : Nat) :
    Spec.Ecdsa.bytesAt m p (L + 1) = m p :: Spec.Ecdsa.bytesAt m (p + BitVec.ofNat 64 1) L := by
  rw [Nat.add_comm L 1, bytesAt_add]
  simp only [Spec.Ecdsa.bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero,
    List.cons_append, List.nil_append]

theorem decompress_key (c : Cfg) (root : Fe c.C → Fe c.C) (s : State) :
    Impl.EcKey.Compressed.decode c.C root (Spec.EcKey.bytesAt s.mem (s.gpr .r4) (c.C.len + 1)) =
      if DAccept c root s then some (.affine (Fin.ofNat c.C.p (keyX c s)) (keyRoot c root s)) else none := by
  have hb := key_bytes s.mem (s.gpr .r4) c.C.len
  exact decode_checked_eq root (length_bytesAt _ _ _)
    (by change (Spec.Ecdsa.bytesAt _ _ _).head? = _; rw [hb]; rfl)
    (by change ofBytes ((Spec.Ecdsa.bytesAt _ _ _).drop 1) = _; rw [hb]; rfl)

theorem decompress_correct (c : Cfg) (hc : CfgOk c) (root : Fe c.C → Fe c.C) (hroot : CandidateCorrect c root)
    (s : State) (hs : (decompressContract c.C root).pre s) :
    ∃ t s', Exec isa (Impl.EcKey.Compressed.PPC64LE.decompress c) s t s' ∧
      abiPreserved s s' ∧ (decompressContract c.C root).post s s' := by
  obtain ⟨hrd, hwr, hpo, hpw, how, hfit, hpkfit, hwfit⟩ := hs
  have hp : DPre c s :=
    ⟨by rw [hrd, show c.C.len + 1 = 1 + c.C.len by omega_arith],
      by rw [hwr, show 2 * c.C.len + 1 = 1 + 2 * c.C.len by omega_arith],
      by simpa only [show c.C.len + 1 = 1 + c.C.len by omega_arith] using hpw,
      by simpa only [show 2 * c.C.len + 1 = 1 + 2 * c.C.len by omega_arith] using how,
      by omega_arith, by omega_arith, hwfit⟩
  obtain ⟨t, s', he, K, bytes, ret⟩ := decompress_ok hc hroot hp
  refine ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, ?_⟩
  dsimp only [decompressContract]
  rw [decompress_key]
  change Spec.EcKey.bytesAt s'.mem (s.gpr .r3) (1 + 2 * c.C.len) = _ at bytes
  rw [show 1 + 2 * c.C.len = 2 * c.C.len + 1 by omega_arith] at bytes
  by_cases hk : DAccept c root s
  · rw [ite_eq_left hk] at bytes ret ⊢
    refine ⟨ret, ?_⟩
    rw [bytes]
    simp only [Spec.EcKey.encodePoint, Fin.val_ofNat, Nat.mod_eq_of_lt hk.1.2]
  · rw [ite_eq_right hk] at bytes ret ⊢
    exact ⟨ret, bytes⟩

end VG.Proof.EcKey.Compressed.PPC64LE
