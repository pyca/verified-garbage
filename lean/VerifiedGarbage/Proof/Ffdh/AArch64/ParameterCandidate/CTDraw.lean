module

public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.MrDraw
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrRound
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Round
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Draw
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.MrDraw
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrRound
meta import VerifiedGarbage.Proof.RsaKeyGen.Slots
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Round
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Draw
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# An FFDH parameter candidate on AArch64: constant time of a draw

Every value of the candidate is public, so two runs with the same public
data follow the same path: each piece is checked by the taint analysis from
registers that correctness pins (`round_ct`, `drawHead_ct`, `draw_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-! ## A round -/

/-- The public data of a round: the working space, `N` and the witness. -/
structure RQ where
  L : WsP
  N : Nat
  a : Nat

/-- Before a round. -/
def RA (q : RQ) (s : State) : Prop :=
  4 ≤ q.L.w ∧ q.L.w ≤ 128 ∧ slot q.L.w aE + 8 * (q.L.w + 2) ≤ q.L.Z ∧ q.N % 2 = 1 ∧ 3 ≤ q.N ∧ q.a < q.N ∧
    (∃ bm, MrCtx s q.L.B q.L.Z q.L.w q.N bm) ∧ ECtx s.mem q.L.B q.L.w q.N ∧
    wv s.mem q.L.B (slot q.L.w aR2) q.L.w = 2 ^ (64 * q.L.w) * 2 ^ (64 * q.L.w) % q.N ∧
    wv s.mem q.L.B (slot q.L.w aX) q.L.w = q.a

/-- Before the kernel. -/
def RB (q : RQ) (s : State) : Prop :=
  4 ≤ q.L.w ∧ q.L.w ≤ 128 ∧ slot q.L.w aE + 8 * (q.L.w + 2) ≤ q.L.Z ∧ q.N % 2 = 1 ∧ 3 ≤ q.N ∧
    (∃ bm, MrCtx s q.L.B q.L.Z q.L.w q.N bm) ∧ ECtx s.mem q.L.B q.L.w q.N ∧
    wv s.mem q.L.B (slot q.L.w aXm) q.L.w = q.a % q.N * 2 ^ (64 * q.L.w) % q.N

/-- After the kernel. -/
def RF (q : RQ) (s : State) : Prop :=
  Ws s q.L.B q.L.Z q.L.w ∧ word s.mem q.L.B (8 * kFlag) = mask (Proof.MillerRabin.Round.round q.N q.a)

theorem roundMm_ok (M : Mont) {q : RQ} {s : State} (h : RA q s) : WP isa (M.mm aXm aX aR2) s (RB q) := by
  obtain ⟨h4, h128, hEZ, hodd, hc3, ha, ⟨bm, hc⟩, he, hR2, hx⟩ := h
  have hn := hc.ws.scr.nowrap
  have hw' : q.L.w < 2 ^ 31 := by omega_arith
  have hRc : Nat.Coprime (2 ^ (64 * q.L.w)) q.N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc0 : 0 < q.N := by omega_arith
  have hg := hc.good
  refine WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 hw' (o := aXm) (a := aX) (b := aR2) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hR2, hc.n]; exact Nat.mod_lt _ hc0)) fun t ⟨_, hlt, hy, ha₁, k⟩ => ?_
  rw [hc.n] at hlt hy
  rw [hx, hR2] at hy
  have hXm : wv t.mem q.L.B (slot q.L.w aXm) q.L.w = q.a % q.N * 2 ^ (64 * q.L.w) % q.N := by
    rw [← Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt ha]
    refine VG.Proof.Bignum.mont_cancel hRc ?_
    rw [hy, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have f₁ : Frm q.L.B [(slot q.L.w aAcc, 8 * (q.L.w + 2)), (slot q.L.w aTmp, 8 * (q.L.w + 2)),
      (slot q.L.w aXm, 8 * (q.L.w + 2))] s.mem t.mem := Frm.of_arrays ha₁ (by simp)
  refine ⟨h4, h128, hEZ, hodd, hc3, ⟨bm, hc.of_frm f₁ (by kmut) k (by decide)
    (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)⟩,
    he.of_frm f₁ (fun r hr => Or.inr (rdRanges_lt q.L.w r (by
      simp only [rdRanges]; exact List.mem_append_left _ (List.mem_append_left _ hr)))) (by omega_arith), hXm⟩

theorem roundMm_ct (M : Mont) : RelCT isa (Two RA) (M.mm aXm aX aR2) (Two RB) :=
  two_post (two_map (fun q : RQ => q.L) (fun _ _ ⟨_, _, _, _, _, _, ⟨_, hc⟩, _⟩ => ⟨_, hc.good⟩)
    (M.ct (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))))) fun _ _ h => roundMm_ok M h

theorem roundKernel_ct (R : Kernel) : RelCT isa (Two RB) (seqs R.run) (Two RF) :=
  two_post (two_map (fun q : RQ => q.L)
    (fun q _ ⟨h4, h128, hEZ, hodd, hc3, ⟨bm, hc⟩, he, hx⟩ => ⟨h4, h128, hEZ, q.N, bm, q.a, hc, he, hodd, hc3, hx⟩)
    R.ct) fun _ _ ⟨h4, h128, hEZ, hodd, hc3, ⟨_, hc⟩, he, hx⟩ =>
      WP.mono (R.ok hc he h4 h128 hEZ hodd hc3 hx) fun _ ⟨⟨_, hct⟩, _, hf, _⟩ => ⟨hct.ws, hf⟩

/-- The end of a round. -/
theorem roundEnd_ct : RelCT isa (Two RF) (seqs [.block [ldh .x3 kFlag],
      .ite (.zero .x .x3) (.block [movi .x3 2, sth .x3 kStat])
        (.block [ldh .x3 fIdx, ldh .x4 fChecks, .addImm .x .x3 .x3 1, .subs .x .x5 .x3 .x4, movi .x6 4, movi .x7 1,
          .csel .x .x5 .x7 .x6, sth .x3 fIdx, sth .x5 kStat])]) fun _ _ => True := by
  have pw : ∀ {Φ : RQ → State → Prop}, (∀ q s, Φ q s → Ws s q.L.B q.L.Z q.L.w) → Pins Φ [.x0] :=
    fun h => pins_ws' (fun q : RQ => q.L.B) (fun q : RQ => q.L.Z) (fun q : RQ => q.L.w) h
  refine RelCT.seq (two_piece (Ψ := fun q t => Ws t q.L.B q.L.Z q.L.w ∧
      isa.eval (.zero .x .x3) t = some (!Proof.MillerRabin.Round.round q.N q.a)) [.x0] (pw fun _ _ h => h.1)
      (by taint_decide) fun q s ⟨hw, hF⟩ => ?_) (two_ite (fun _ _ _ h₁ h₂ => by rw [h₁.2, h₂.2])
      (two_taint [.x0] (pw fun _ _ h => h.1.1) (by taint_decide))
      (two_taint [.x0] (pw fun _ _ h => h.1.1) (by taint_decide)))
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = mask (Proof.MillerRabin.Round.round q.N q.a) ∧ t.mem = s.mem)
    (by brun [hw.x0, hdr_enc (show kFlag < 32 by decide),
      hw.scr.ld (d := 8 * kFlag) (by simp only [kFlag, kPlen, sFn]; omega_arith), hF])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h3, hm⟩, k⟩ => ⟨?_, ?_⟩
  · exact hw.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide)
  · rw [eval_zero, h3, mask_beq]

/-- A round leaks the same in runs with the same public data. -/
theorem round_ct (M : Mont) (R : Kernel) :
    RelCT isa (Two RA) (seqs (VG.Impl.Ffdh.AArch64.ParameterCandidate.round M.mm R.run)) fun _ _ => True := by
  simp only [VG.Impl.Ffdh.AArch64.ParameterCandidate.round]
  refine ct_app' (by simp) (by simp) ?_ roundEnd_ct
  refine ct_app' (a := [M.mm aXm aX aR2]) (by simp) R.nonempty ?_ (roundKernel_ct R)
  rw [seqs_one]; exact roundMm_ct M

/-! ## A draw -/

/-- The public data of a draw: the candidate's, the modulus's, and the
octets read before it. -/
structure DD where
  p : PP
  w : Nat
  N : Nat
  mb : Nat
  K : Nat
  u : Nat

/-- Before a draw. -/
def DA (d : DD) (s : State) : Prop :=
  MrDims d.p d.w d.N d.mb d.K ∧ MrFix d.p d.w d.N d.mb d.K s ∧
    word s.mem d.p.B (8 * kUsed) = BitVec.ofNat 64 d.u ∧ (∃ i, word s.mem d.p.B (8 * fIdx) = BitVec.ofNat 64 i ∧
    i < 2 ^ 62) ∧ d.u + mLen d.mb ≤ d.p.r.length

/-- The working space of a draw. -/
def DW (d : DD) (s : State) : Prop := Ws s d.p.B d.p.Z d.w

/-- Before the cut. -/
def DC (d : DD) (s : State) : Prop :=
  Ws s d.p.B d.p.Z d.w ∧ mK d.mb ≤ 64 ∧ word s.mem d.p.B (8 * fTop) = BitVec.ofNat 64 (2 ^ mK d.mb - 1)

/-- Before the octets' block. -/
def DL (d : DD) (s : State) : Prop :=
  Ws s d.p.B d.p.Z d.w ∧ word s.mem d.p.B (8 * kRand) = d.p.rp ∧
    word s.mem d.p.B (8 * kUsed) = BitVec.ofNat 64 d.u ∧ word s.mem d.p.B (8 * kLen) = BitVec.ofNat 64 (mLen d.mb)

/-- The registers `loadBE` needs. -/
def dbVal (B rp : Addr) (w u len : Nat) : Reg → BitVec 64
  | .x0 => B
  | .x8 => off B (slot w aX)
  | .x1 => rp + BitVec.ofNat 64 u
  | _ => BitVec.ofNat 64 len

/-- The block before `loadBE`. -/
theorem drawBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {rp : Addr} {u len : Nat}
    (hR : word s.mem B (8 * kRand) = rp) (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 u)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 len) :
    WP isa (.block (ws ++ base aX .x8 ++ [ldh .x1 kRand, ldh .x3 kUsed, .add .x .x1 .x1 .x3,
      ldh .x2 kLen, .add .x .x3 .x3 .x2, sth .x3 kUsed])) s fun t =>
      ∀ r ∈ [Reg.x0, .x8, .x1, .x2], t.gpr r = dbVal B rp w u len r := by
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨⟨_, h11, m₂, _⟩, k₂⟩ =>
    WP.mono (base_ok aX .x8 ((k₂.gpr .x0 (by decide)).trans h.x0) h11) fun s₃ ⟨⟨h8, m₃, _⟩, k₃⟩ =>
      WP.mono (WP.keep [.x1, .x3, .x2] (Q := fun t => t.gpr .x1 = rp + BitVec.ofNat 64 u ∧
        t.gpr .x2 = BitVec.ofNat 64 len) (by
          have h0₃ : s₃.gpr .x0 = B := ((k₂.trans k₃).gpr .x0 (by decide)).trans h.x0
          have hs₃ := h.scr.congr (k₂.trans k₃).wr
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega_arith)
          brun [h0₃, hdr_enc (show kRand < 32 by decide), hdr_enc (show kUsed < 32 by decide),
            hdr_enc (show kLen < 32 by decide), m₃, m₂, hl₃ kRand (by decide), hl₃ kUsed (by decide),
            hl₃ kLen (by decide), hs₃.st (d := 8 * kUsed) (by have := h.h256; simp only [kUsed, sFn]; omega_arith),
            hR, hU, hK])
        (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h1, h2⟩, k₄⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (((k₂.trans k₃).trans k₄).gpr .x0 (by decide)).trans h.x0
        · exact (k₄.gpr .x8 (by decide)).trans h8
        · exact h1
        · exact h2))

theorem zeroAD_ct : RelCT isa (Two DL) (zeroA aX) (Two DL) := by
  have e : zeroA aX = .seq (.block (ws ++ (base aX .x8 ++ [movi .x7 0]))) zeroAcc := by
    simp only [zeroA, List.append_assoc]
  rw [e]
  refine ws_ct (fun d : DD => d.p.B) (fun d : DD => d.p.Z) (fun d : DD => d.w) (fun _ _ h => h.1)
    (by taint_decide) fun d s h => ?_
  rw [← e]
  obtain ⟨hw, hR, hU, hK⟩ := h
  have hn := hw.scr.nowrap
  refine WP.mono (zeroA_ok hw (show aX < 16 by decide)) fun t ⟨_, o, _, _, _, k⟩ => ?_
  have f : Frm d.p.B [(slot d.w aX, 8 * (d.w + 2))] s.mem t.mem := Frm.of_outside o (List.mem_singleton_self _)
  have hh : ∀ i < 32, word t.mem d.p.B (8 * i) = word s.mem d.p.B (8 * i) := fun i hi =>
    f.word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (hdr_lt_slot d.w aX hi)) (by omega_arith)
  exact ⟨hw.congr' f (by msb_mut) k (by decide), (hh _ (by decide)).trans hR, (hh _ (by decide)).trans hU,
    (hh _ (by decide)).trans hK⟩

/-- The octets into `aX`. -/
theorem drawLoad_ct : RelCT isa (Two DL) (seqs [zeroA aX, .block (ws ++ base aX .x8 ++ [ldh .x1 kRand,
    ldh .x3 kUsed, .add .x .x1 .x1 .x3, ldh .x2 kLen, .add .x .x3 .x3 .x2, sth .x3 kUsed]), loadBE])
    fun _ _ => True :=
  RelCT.seq zeroAD_ct (RelCT.seq (two_piece (Ψ := fun d t => ∀ r ∈ [Reg.x0, .x8, .x1, .x2],
      t.gpr r = dbVal d.p.B d.p.rp d.w d.u (mLen d.mb) r) [.x0]
      (pins_ws' (fun d : DD => d.p.B) (fun d : DD => d.p.Z) (fun d : DD => d.w) fun _ _ h => h.1)
      (by taint_decide)
      fun _ _ ⟨hw, hR, hU, hK⟩ => drawBlk_ok hw hR hU hK)
    (two_taint _ (pins_of _ (fun d => dbVal d.p.B d.p.rp d.w d.u (mLen d.mb)) fun _ _ h => h) (by taint_decide)))

/-- The range's pieces, from the working space. -/
theorem drawRange_ct : RelCT isa (Two DW)
    (seqs [.block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
      countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16],
      .block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++ ws ++
        base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4,
        next .x16, next .x17, .subImm .x .x14 .x12 1]),
      cmpLoop,
      .block [.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15]]) fun _ _ => True := by
  refine two_map (Φ' := fun (q : WPub) t => Ws t q.L.B q.L.Z q.L.w)
    (fun d : DD => (⟨⟨d.p.B, d.p.Z, d.w⟩, d.p.rp, d.u⟩ : WPub)) (fun _ _ h => h) ?_
  have e : ([.block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
      countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16],
      .block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++ ws ++
        base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4,
        next .x16, next .x17, .subImm .x .x14 .x12 1]),
      cmpLoop,
      .block [.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15]] : List (Prog isa)) =
      [.block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
        countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16]] ++
      ([.block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++ ws ++
        base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4,
        next .x16, next .x17, .subImm .x .x14 .x12 1]), cmpLoop] ++
      [.block [.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15]]) := rfl
  rw [e]
  exact ct_app' (by simp) (by simp) witLow_ct (ct_app' (by simp) (by simp) witCmp_ct
    (two_taint _ (pins_of _ (fun p : WPub => wsVal p.L.B p.L.w) fun _ _ h => h) (by taint_decide)))

theorem drawHead_eq : drawHead = ([zeroA aX, .block (ws ++ base aX .x8 ++ [ldh .x1 kRand,
    ldh .x3 kUsed, .add .x .x1 .x1 .x3, ldh .x2 kLen, .add .x .x3 .x3 .x2, sth .x3 kUsed]), loadBE] : List (Prog isa)) ++
    (([.block (ws ++ base aX .x16 ++ ([.lsl .x .x5 .x12 3, .add .x .x5 .x16 .x5, .subImm .x .x5 .x5 8, ldh .x4 fTop,
      ld .x3 .x5, .logic .and .x .x3 .x3 .x4, st .x3 .x5] : List Instr))] : List (Prog isa)) ++
    ([.block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
      countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16],
      .block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++ ws ++
        base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4,
        next .x16, next .x17, .subImm .x .x14 .x12 1]),
      cmpLoop,
      .block [.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15]] : List (Prog isa))) := rfl

/-- After `drawHead`. -/
def DM (d : DD) (s : State) : Prop :=
  MrDims d.p d.w d.N d.mb d.K ∧ ∃ i s₀, DrawMid d.p d.w d.N d.mb d.K i d.u s₀ s ∧ i < 2 ^ 62

/-- `drawHead` leaks the same in runs with the same public data. -/
theorem drawHead_ct : RelCT isa (Two DA) (seqs drawHead) (Two DM) := by
  refine two_post ?_ fun d s ⟨hd, h, hU, ⟨i, hI, hi⟩, hroom⟩ =>
    WP.mono (drawHead_ok hd h hU hI hroom) fun t ht => ⟨hd, i, s, ht, hi⟩
  rw [drawHead_eq]
  refine ct_app' (by simp) (by simp) (Ψ := DC) (two_post (two_map (Φ' := DL) id (fun d s ⟨_, h, hU, _⟩ =>
    ⟨h.st.ws, h.st.args.rand, hU, h.len⟩) drawLoad_ct) fun d s ⟨hd, h, hU, _, hroom⟩ => ?_) ?_
  · have hmb1 := hd.mb1
    have hw := hd.hw
    have hn := h.st.ws.scr.nowrap
    exact WP.mono (drawLoad_ok h.st.ws h.st.args.rand hU h.len (by simp only [mLen]; omega_arith)
      (by rw [hw]; simp only [mLen, mW]; omega_arith) (src_take (src_drop h.st.src d.u) (mLen d.mb))
      (by simp only [List.length_take, List.length_drop]; omega_arith)) fun t ⟨_, _, f, hw', _⟩ =>
        ⟨hw', by simp only [mK, mW]; omega_arith, by
          rw [f.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [fTop]; omega_arith)]; exact h.top⟩
  refine ct_app' (by simp) (by simp) (Ψ := DW) ?_ drawRange_ct
  rw [seqs_one]
  exact ws_block_ct (fun d : DD => d.p.B) (fun d : DD => d.p.Z) (fun d : DD => d.w) (fun _ _ h => h.1)
    (by taint_decide) fun d s ⟨hw, hk, hT⟩ => WP.mono (drawCut_ok hw hk hT) fun t ⟨_, f, k⟩ =>
      hw.congr' f (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _) k (by decide)

theorem mask_decide_beq (P : Prop) [Decidable P] : (mask (decide P) == 0) = !decide P := by
  cases decide P <;> decide

/-- A draw leaks the same in runs with the same public data. -/
theorem draw_ct (M : Mont) (R : Kernel) :
    RelCT isa (Two DA) (seqs (draw M.mm R.run)) fun _ _ => True := by
  rw [draw_eq]
  refine ct_app' (by simp [drawHead, draw]) (by simp) drawHead_ct ?_
  rw [seqs_one]
  have hz : ∀ d s, DM d s → isa.eval (.zero .x .x9) s =
      some (!decide (2 ≤ wA d.mb d.p.r d.u ∧ wA d.mb d.p.r d.u < d.N - 1)) := fun d s ⟨_, i, s₀, h, _⟩ => by
    rw [eval_zero, h.x9, mask_decide_beq]
  refine two_ite (fun d s₁ s₂ h₁ h₂ => by rw [hz d s₁ h₁, hz d s₂ h₂]) ?_ ?_
  · exact two_taint [.x0] (pins_ws' (fun d : DD => d.p.B) (fun d : DD => d.p.Z) (fun d : DD => d.w)
      fun _ _ ⟨⟨_, _, _, h, _⟩, _⟩ => h.fix.st.ws) (by taint_decide)
  · refine two_map (Φ' := RA) (fun d : DD => (⟨⟨d.p.B, d.p.Z, d.w⟩, d.N, wA d.mb d.p.r d.u⟩ : RQ)) ?_ (round_ct M R)
    rintro d s ⟨hm, hb⟩
    have hz' := hz d s hm
    obtain ⟨hd, i, s₀, h, _⟩ := hm
    rw [hz'] at hb
    have hacc : 2 ≤ wA d.mb d.p.r d.u ∧ wA d.mb d.p.r d.u < d.N - 1 := by
      simpa using hb
    have hw := hd.hw
    have hmb1 := hd.mb1
    have hmb2 := hd.mb2
    exact ⟨by rw [hw]; simp only [mW]; omega_arith, by rw [hw]; simp only [mW]; omega_arith, hd.eZ, hd.odd, hd.n3,
      show wA d.mb d.p.r d.u < d.N by omega_arith, h.fix.ctx, h.fix.ex, h.fix.r2, h.ax⟩

end VG.Proof.Ffdh.AArch64.ParameterCandidate
