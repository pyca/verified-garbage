module

public import VerifiedGarbage.Proof.Rsa.Arm.RvMont4
public import VerifiedGarbage.Proof.Rsa.Arm.RvMM
import VerifiedGarbage.Proof.Rsa.Arm.RvKM
import VerifiedGarbage.Proof.Rsa.Arm.RvMmul2
import VerifiedGarbage.Proof.Rsa.Arm.RvCtx
import VerifiedGarbage.Proof.Rsa.Arm.RvMont2
import VerifiedGarbage.Proof.Rsa.Arm.RvOps2
import VerifiedGarbage.Proof.Rsa.Arm.RvOps

/-! # `vg_rsa_recover_primes` on ARMv7: `R mod n` and `n - R mod n` (`mont_vp`)

The stage of the candidates, `KM`: Montgomery multiplication ready (`MM`),
and the key arrays `n`, 0, 1, `R² mod n`, `R mod n` and `n - R mod n` (the
Montgomery forms of 1 and -1), with the retained exponent state.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf Layout)

/-- `R = 2^(64 w6)`, and `R mod n`. -/
abbrev Rm (P : RP) : Nat := 2 ^ (64 * P.w6)
abbrev Ov (P : RP) : Nat := Rm P % P.n

/-- The arrays of the candidates. -/
def AM (P : RP) : Nat → Nat :=
  upd (upd (upd (upd (upd (upd (fun _ => 0) aN P.n) aZ 0) aOne 1) mR2 (R2v P)) aO (Ov P)) aNg (P.n - Ov P)

abbrev liveM : List Nat := [aNg, aO, mR2, aOne, aZ, aN]

/-- The stage of the candidates, with the arrays `AW` and the header words
`V` live. -/
abbrev KM (P : RP) (σ : State) (AW : Nat → Nat) (liveW : List Nat) (V : Nat → Nat) (ls : List Nat)
    (s : State) : Prop :=
  KS P σ (AM P) liveM AW liveW V ls s ∧ MM P s ∧ Ws s P.B P.Z P.w nArr

section
variable {P : RP}

theorem n_lt {σ : State} (pre : In P σ) : P.n < 2 ^ (32 * P.w) := by
  have := bytes_lt σ.mem (State.addr P.nP) P.K
  rw [pre.nB] at this
  have kw := pre.sizes.kw
  exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))

theorem n_lt64 {σ : State} (pre : In P σ) : P.n < Rm P := by
  have := bytes_lt σ.mem (State.addr P.nP) P.K
  rw [pre.nB] at this
  exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by simp only [RP.w6]; omega))

theorem montC_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) {E : State → Prop} (keepHalves : Bool := true) :
    VP (fun σ s => E σ ∧ R01 P σ s keepHalves ∧ MR P s ∧ numAt s.mem (State.addr P.M0) P.w6 0 = P.n ∧
        numAt s.mem (State.addr P.M0) P.w6 4 = R2v P) montC
      (fun σ s => E σ ∧ KM P σ (AWh P σ P.c) (montWide keepHalves) (Vh P σ P.c) (montSlots keepHalves) s) := by
  have hn0 : 0 < P.n := by omega_arith
  simp only [montC, seqs]
  let L1 := mR2 :: live01
  let A1 := fun σ => upd (A01 P σ) mR2 (R2v P)
  let K0 := fun σ s => E σ ∧ K01 P σ s keepHalves ∧ MM P s ∧ numAt s.mem (State.addr P.M0) P.w6 4 = R2v P
  let K1 := fun σ s => K0 σ s ∧ Ws s P.B P.Z P.w nArr
  let K2 := fun σ s => E σ ∧ KS P σ (A1 σ) L1 (AWh P σ P.c) (montWide keepHalves) (Vh P σ P.c) (montSlots keepHalves) s ∧ MM P s ∧
    Ws s P.B P.Z P.w nArr
  let K3 := fun σ s => E σ ∧ KS P σ (upd (A1 σ) mXm 1) (mXm :: L1) (AWh P σ P.c) (montWide keepHalves) (Vh P σ P.c) (montSlots keepHalves) s ∧
    MM P s ∧ Ws s P.B P.Z P.w nArr
  let K4 := fun σ s => E σ ∧ KS P σ (upd (upd (A1 σ) mXm 1) (mBase + iXm) (Ov P)) ((mBase + iXm) :: mXm :: L1)
    (AWh P σ P.c) (montWide keepHalves) (Vh P σ P.c) (montSlots keepHalves) s ∧ MM P s ∧ Ws s P.B P.Z P.w nArr
  let K5 := fun σ s => E σ ∧ KS P σ (upd (upd (upd (A1 σ) mXm 1) (mBase + iXm) (Ov P)) aO (Ov P))
    (aO :: (mBase + iXm) :: mXm :: L1) (AWh P σ P.c) (montWide keepHalves) (Vh P σ P.c) (montSlots keepHalves) s ∧ MM P s ∧ Ws s P.B P.Z P.w nArr
  refine VP.seq (G := K2) (VP.block_append (G := K1) (VP.block_append (G := K0) ?_ ?_) ?_)
    (VP.seq (G := K3) ?_ (VP.seq (G := K4) ?_ (VP.seq (G := K5) ?_ ?_)))
  -- The base.
  · show VP _ (.block ([(Reg.r8, aoS)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, mr, n0, r2⟩ => ?_
    · rw [h₁.2.1.bs.sp, h₁.2.1.bs.pre.sp, h₂.2.1.bs.sp, h₂.2.1.bs.pre.sp]
    · refine h.bs.ldrSp (o := aoS) (by decide) (by decide) (by decide) fun t u => WP.block_nil ?_
      have r := u.rest (ws := [.r8]) (by simp)
      exact ⟨e, (h.of_rest u.mem r.sp r.rd r.wr).toKS (u.gpr.trans h.bs.pre.aS),
        MM.of_rest ⟨mr, n0⟩ r u.mem, by rw [u.mem]; exact r2⟩
  -- The context.
  · refine VP.taint [.r8] ctxw_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨e, h, hm, r2⟩ => ?_
    · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1.r8, h₂.2.1.r8]
    · exact WP.mono (ctxw_ok h.bs h.r8 h.cnt) fun t ⟨ht, r, m⟩ =>
        ⟨⟨e, h.of_rest r m (by decide), hm.of_rest r m, by rw [m]; exact r2⟩, ht⟩
  -- `R² mod n`'s top words cleared.
  · refine VP.ctx clrTopR2_taint (fun σ s h => h.2) fun σ s ⟨⟨e, h, hm, r2⟩, hw⟩ => ?_
    have sz := h.sizes
    have hf := h.bs.pre.fS
    rw [← List.append_nil (clrTop mR2)]
    refine clrTop_ok hw (j := mR2) (by decide) (by decide) (by show 2 ≤ 2 * P.w6 + 2; omega_arith)
      fun t ht k v r => WP.block_nil ⟨e, h.write_w k (by decide) (by simp) (h.r8_of r) r.sp r.rd r.wr ?_
        (by cases keepHalves <;> decide) (by simp),
        hm.of_keep1 h.bs k (by decide) (by decide) (by simp) r.sp r.rd r.wr, ht⟩
    rw [v, show P.w - 2 = 2 * P.w6 by simp only [RP.w]; omega_arith, ← r2, numAt_val32 sz hf]; rfl
  -- `[mXm] := 1`.
  · refine VP.ctx xmOne_taint (fun σ s h => h.2.2.2) fun σ s ⟨e, h, hm, hw⟩ => ?_
    refine WP.mono (h.copy_m hm hw (o := mXm) (a := aOne) (by decide) (by decide) (by simp [L1]) (by decide)
      (by cases keepHalves <;> decide)) fun t ⟨ht, mt, hwt, _⟩ => ⟨e, ?_, mt, hwt⟩
    have : A1 σ aOne = 1 := by simp [A1, A01, upd, mR2, aOne]
    rwa [this] at ht
  -- `R mod n = 1 · R² · R⁻¹`.
  · refine (mmul_vp (P := P) (o := iXm) (a := iXm) (b := iR2) (by decide) hn.1 (E := E)
      (A := fun σ => upd (A1 σ) mXm 1) (live := mXm :: L1) (AW := fun σ => AWh P σ P.c) (liveW := montWide keepHalves)
      (V := fun σ => Vh P σ P.c) (ls := montSlots keepHalves) (T := fun _ => Ov P) (by decide) (by decide) (by decide)
      (by decide) (by cases keepHalves <;> decide) fun σ _ => ?_).mono
      (fun σ s h => ⟨h.1, h.2.1, h.2.2.1⟩) fun σ s h => h
    have e1 : upd (A1 σ) mXm 1 (mBase + iXm) = 1 := by simp [upd, mXm, mBase, iXm]
    have e2 : upd (A1 σ) mXm 1 (mBase + iR2) = R2v P := by simp [A1, upd, mXm, mBase, iR2, mR2]
    rw [e1, e2]
    refine ⟨by omega_arith, Nat.mod_lt _ hn0, Nat.mod_lt _ hn0, ?_⟩
    rw [Nat.one_mul, Nat.mod_mod, Nat.mod_mul_mod, ← Nat.pow_add, show 64 * P.w6 + 64 * P.w6 = 128 * P.w6 by omega_arith]
  -- `[aO] := R mod n`.
  · refine VP.ctx oXm_taint (fun σ s h => h.2.2.2) fun σ s ⟨e, h, hm, hw⟩ => ?_
    refine WP.mono (h.copy_m hm hw (o := aO) (a := mXm) (by decide) (by decide) (by simp) (by decide)
      (by cases keepHalves <;> decide)) fun t ⟨ht, mt, hwt, _⟩ => ⟨e, ?_, mt, hwt⟩
    rwa [show mXm = mBase + iXm from rfl, upd_self] at ht
  -- `[aNg] := n - R mod n`.
  · refine VP.ctx ngO_taint (fun σ s h => h.2.2.2) fun σ s ⟨e, h, hm, hw⟩ => ?_
    have pre := h.bs.pre
    refine WP.mono (h.sub3_m hm hw (o := aNg) (a := aN) (b := aO) (by decide) (by decide) (by simp [L1]) (by simp)
      (by decide) (by decide) (by cases keepHalves <;> decide))
      fun t ⟨X, ht, mt, hwt, _, hx, hb⟩ => ⟨e, ?_, mt, hwt⟩
    have hX : X < 2 ^ (32 * P.w) := by
      rw [← show num t.mem P.B P.w aNg = X by rw [ht.arrs aNg (by simp), upd_self]]
      exact val32_lt _ _ _ _
    have eN : upd (upd (upd (A1 σ) mXm 1) (mBase + iXm) (Ov P)) aO (Ov P) aN = P.n := by
      simp [A1, A01, Aload, upd, aO, aN, mBase, iXm, mXm, mR2, aOne, aZ, wE, wD]
    have eO : upd (upd (upd (A1 σ) mXm 1) (mBase + iXm) (Ov P)) aO (Ov P) aO = Ov P := by simp [upd]
    rw [eN, eO] at hx
    have hO : Ov P < P.n := Nat.mod_lt _ hn0
    have nl := n_lt pre
    have hXv : X = P.n - Ov P := by
      rcases (by omega_arith : (t.gpr .r11).toNat = 0 ∨ (t.gpr .r11).toNat = 1) with h0 | h1
      · rw [h0] at hx; omega_arith
      · rw [h1] at hx; omega_arith
    rw [hXv] at ht
    refine ht.mono (fun j hj => ⟨?_, ?_⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
    · simp only [liveM, L1, live01, List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega_arith
    · simp only [liveM, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [AM, A1, A01, Aload, upd, aO, aN, aNg, mBase, iXm, mXm, mR2, aOne, aZ, wE, wD]

/-- `mont`. -/
theorem montFull_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) (hs : Sizes P) {E : State → Prop} (keepHalves : Bool := true) :
    VP (fun σ s => E σ ∧ MontStart P σ s keepHalves) mont (fun σ s => E σ ∧ KM P σ (AWh P σ P.c) (montWide keepHalves) (Vh P σ P.c) (montSlots keepHalves) s) := by
  simp only [mont, seqs]
  refine (montA_vp keepHalves).seq ((setup_vp keepHalves).seq (VP.seq (G := fun σ s => E σ ∧ PreP P σ s keepHalves) ?_
    ((precompute_vp hn hs keepHalves).seq (montC_vp hn keepHalves))))
  show VP _ (.block ([(Reg.r4, aoN), (Reg.r6, aoK)].map fun p => Instr.ldrSp p.1 p.2)) _
  refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, lay, wd, r0, sv⟩ => ?_
  · rw [h₁.2.1.bs.sp, h₁.2.1.bs.pre.sp, h₂.2.1.bs.sp, h₂.2.1.bs.pre.sp]
  · have hb := h.bs
    refine hb.ldrSp (o := aoN) (by decide) (by decide) (by decide) fun s1 u1 => ?_
    have r1 := u1.rest (ws := [.r4]) (by simp)
    have hb1 := hb.of_rest r1 u1.mem
    refine hb1.ldrSp (o := aoK) (by decide) (by decide) (by decide) fun t u2 => WP.block_nil ?_
    have r2 := u2.rest (ws := [.r6]) (by simp)
    have m : t.mem = s.mem := u2.mem.trans u1.mem
    refine ⟨e, h.of_rest m (r2.sp.trans r1.sp) (r2.rd.trans r1.rd) (r2.wr.trans r1.wr), m ▸ lay, m ▸ wd, ?_,
      m ▸ sv, ?_, ?_⟩
    · rw [u2.other _ (by decide), u1.other _ (by decide), r0]
    · rw [u2.other _ (by decide), u1.gpr, hb.pre.aN]
    · rw [u2.gpr, hb.pre.aK]

/-- The original two-pass search needs only the odd part of the exponent. -/
theorem mont_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) (hs : Sizes P) {E : State → Prop} :
    VP (fun σ s => E σ ∧ HI P σ P.c s) mont
      (fun σ s => E σ ∧ KM P σ (AWh P σ P.c) [wR] (Vh P σ P.c) [sTc] s) := by
  refine (montFull_vp hn hs).mono (fun _ _ h => h) fun σ s h => ⟨h.1, ?_, h.2.2⟩
  exact h.2.1.mono (fun j hj => ⟨hj, rfl⟩)
    (fun j hj => ⟨by simp only [List.mem_singleton] at hj; subst hj; simp [montWide], rfl⟩) (fun d hd => ⟨hd, rfl⟩)

end

end VG.Proof.Rsa.Arm.Recover
