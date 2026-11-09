module
-- separate module: the proof of Appendix C.2's body is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Prod
import VerifiedGarbage.Proof.Rsa.ProductExact
import VerifiedGarbage.Proof.Rsa.Arm.Stage.MM
import VerifiedGarbage.Proof.Rsa.Arm.Stage.KS
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ctx
import VerifiedGarbage.Proof.Rsa.Arm.MulMod
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops2
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops
public import VerifiedGarbage.Proof.Rsa.Arm.RdOps
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
public import VerifiedGarbage.Proof.Rsa.Arm.RdTaint
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Tools
import VerifiedGarbage.Proof.Rsa.TwosMath
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # `vg_rsa_recover_primes_det` on ARMv7: `d e - 1` and the halvings

From the product `d e` (`Recover.prod`): `x = d e - 1` and whether `d e ≥ 2`
(`deMinus_vp`); then `u = n - 1` and the `32 w` halvings (`twos_vp`), whose
step is any `f` with the halvings' formula (Appendix C.2's model,
`Proof/Rsa/RecoverDet.lean`, calls it `twoStep`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

/-- `M = d e`. -/
abbrev Mv (P : RP) (σ : State) : Nat := dv P σ * P.e

/-- The modulus of the product. -/
abbrev mTop (P : RP) : Nat := 2 ^ (32 * P.W - 1)

/-- The arrays with `W` words after the product. -/
def AWp (P : RP) (σ : State) : Nat → Nat := upd (upd (AW1 P σ) wMod (mTop P)) wM (Mv P σ)

section
variable {P : RP}

theorem prod_val {P : RP} {σ : State} (h : In P σ) :
    (0 + P.e % 2 ^ (8 * P.el) * dv P σ) % mTop P = Mv P σ := by
  have he : P.e < 2 ^ (8 * P.el) := by have := bytes_lt σ.mem (State.addr P.eP) P.el; rwa [h.eB] at this
  have hd : dv P σ < 2 ^ (8 * P.dl) := bytes_lt σ.mem (State.addr P.dP) P.dl
  have sz := h.sizes
  have := h.el2; have := h.dl2
  exact VG.Proof.Rsa.recover_product_exact hd he
    (by simp only [RP.W, RP.w, RP.w6]; omega)

theorem prod_vp {E : State → Prop} :
    VP (fun σ s => E σ ∧ KS P σ (Aload P σ) [aN] (AW1 P σ) [wZ, wE, wD, wM, wMod] (fun _ => 0) [] s) prod
      (fun σ s => E σ ∧ KS P σ (Aload P σ) [aN] (AWp P σ) [wM, wMod, wZ] (fun _ => 0) [] s ∧
        Ws s P.B P.Z P.W 22) := by
  have eP : prod = .seq (.block (ctxW ++ (setTop wMod ++ ([.ldrSp .r6 aoEl] ++
      [.mov .r6 (.shifted .r6 .lsl 3)])))) (mulMod wZ wE wD wM wMod wT) := rfl
  rw [eP]
  -- The stages.
  let K0 := fun σ s => E σ ∧ KS P σ (Aload P σ) [aN] (AW1 P σ) [wZ, wE, wD, wM, wMod] (fun _ => 0) [] s
  let K1 := fun σ s => K0 σ s ∧ Ws s P.B P.Z P.W 22
  let K2 := fun σ s => E σ ∧ KS P σ (Aload P σ) [aN] (upd (AW1 P σ) wMod (mTop P))
    [wMod, wZ, wE, wD, wM, wMod] (fun _ => 0) [] s ∧ Ws s P.B P.Z P.W 22
  let K3 := fun σ s => K2 σ s ∧ s.gpr .r6 = BitVec.ofNat 32 P.el
  let K4 := fun σ s => K2 σ s ∧ s.gpr .r6 = BitVec.ofNat 32 (8 * P.el)
  have ws_regs : ∀ s₁ s₂ : State,
      Ws s₁ P.B P.Z P.W 22 → Ws s₂ P.B P.Z P.W 22 → ∀ r ∈ [Reg.r7, .r8, .r9], s₁.gpr r = s₂.gpr r := by
    intro s₁ s₂ h₁ h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · rw [h₁.r7, h₂.r7]
    · rw [h₁.r8, h₂.r8]
    · rw [h₁.r9, h₂.r9]
  refine VP.seq (G := K4) (VP.block_append (G := K1) ?_ (VP.block_append (G := K2) ?_
    (VP.block_append (G := K3) ?_ ?_))) ?_
  -- `ctxW`.
  · refine VP.taint [.r8] ctxW_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s h => ?_
    · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.r8, h₂.2.r8]
    · exact WP.mono (ctxW_ok h.2.bs h.2.r8 h.2.cnt) fun t ⟨ht, r, m⟩ =>
        ⟨⟨h.1, h.2.of_rest r m (by decide)⟩, ht⟩
  -- The modulus.
  · refine VP.taint [.r7, .r8, .r9] setTop_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ =>
      ws_regs s₁ s₂ h₁.2 h₂.2) fun σ s ⟨⟨e, h⟩, hw⟩ => ?_
    rw [← List.append_nil (setTop wMod)]
    refine setTop_ok hw (j := wMod) (by decide) (by decide) (by show 1 ≤ 2 * P.w + 2; omega)
      fun t ht k v r => WP.block_nil ⟨e, h.write_W k (by decide) (by simp) (h.r8_of r) r.sp r.rd r.wr ?_
        (by simp only [List.mem_singleton]; rintro j rfl; decide) (by simp), ht⟩
    have z : val32 s.mem (State.addr P.B) (arr P.W wMod) (P.W - 1) = 0 := by
      have e0 : num s.mem P.B P.W wMod = 0 := by rw [h.arrsW wMod (by simp)]; rfl
      have e1 := val32_succ s.mem (State.addr P.B) (arr P.W wMod) (P.W - 1)
      rw [show P.W - 1 + 1 = P.W by simp only [RP.W]; omega] at e1
      change val32 _ _ _ _ = 0 at e0
      omega
    rw [v, z, Nat.zero_add, ← Nat.pow_add]
    congr 1
  -- `e_len`.
  · show VP _ (.block ([(Reg.r6, aoEl)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, hw⟩ => ?_
    · rw [h₁.2.1.bs.sp, h₁.2.1.bs.pre.sp, h₂.2.1.bs.sp, h₂.2.1.bs.pre.sp]
    · exact h.bs.ldrSp (o := aoEl) (by decide) (by decide) (by decide) fun t u => WP.block_nil
        ⟨⟨e, h.of_rest (u.rest (ws := [.r6]) (by simp)) u.mem (by decide), hw.of_upd u (by decide) (by decide)
          (by decide)⟩, u.gpr.trans h.bs.pre.aEl⟩
  -- `8 e_len`.
  · refine VP.taint [] shl3_taint (fun _ _ _ _ _ _ r hr => absurd hr (List.not_mem_nil)) fun σ s ⟨⟨e, h, hw⟩, r6⟩ => ?_
    refine wp_mov (op2_lsl (by decide)) fun t u => WP.block_nil ⟨⟨e, h.of_rest (u.rest (ws := [.r6]) (by simp))
      u.mem (by decide), hw.of_upd u (by decide) (by decide) (by decide)⟩, ?_⟩
    rw [u.gpr, r6]
    have := h.bs.pre.el2; have := h.bs.pre.k2
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  -- `mulMod`.
  · refine VP.taint [.r6, .r7, .r8, .r9] mulMod_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_)
      fun σ s ⟨⟨e, h, hw⟩, r6⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | hr
      · rw [h₁.2, h₂.2]
      · exact ws_regs s₁ s₂ h₁.1.2.2 h₂.1.2.2 r (by simpa using hr)
    have el1 := h.bs.pre.el1; have el2 := h.bs.pre.el2; have k2 := h.bs.pre.k2
    have sz := h.sizes
    refine WP.mono (mulMod_ok hw (by decide) (by decide) (by omega) (by omega) r6)
      fun t ⟨ht, k, r, v⟩ => ⟨e, ?_, ht⟩
    have g : ∀ j, j ∈ [wMod, wZ, wE, wD, wM, wMod] → num s.mem P.B P.W j = upd (AW1 P σ) wMod (mTop P) j :=
      fun j hj => h.arrsW j hj
    have gZ : num s.mem P.B P.W wZ = 0 := by rw [g wZ (by simp)]; simp [AW1, upd, wZ, wMod, wD, wE]
    have gE : num s.mem P.B P.W wE = P.e := by rw [g wE (by simp)]; simp [AW1, upd, wMod, wD, wE]
    have gD : num s.mem P.B P.W wD = dv P σ := by rw [g wD (by simp)]; simp [AW1, upd, wMod, wD]
    have gA : num s.mem P.B P.W wM = 0 := by rw [g wM (by simp)]; simp [AW1, upd, wM, wMod, wD, wE]
    have gM : num s.mem P.B P.W wMod = mTop P := by rw [g wMod (by simp)]; simp [upd]
    have dl2 := h.bs.pre.dl2
    have hmt : 0 < mTop P := Nat.two_pow_pos _
    have hd : dv P σ < mTop P := by
      have hb := bytes_lt σ.mem (State.addr P.dP) P.dl
      exact Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by simp only [RP.W, RP.w, RP.w6]; omega))
    have vM := v gZ (by rw [gA, gM]; exact hmt) (by rw [gD, gM]; exact hd)
      (by rw [gM, show 2 * mTop P = 2 ^ (32 * P.W - 1 + 1) by rw [Nat.pow_succ, Nat.mul_comm],
          show 32 * P.W - 1 + 1 = 32 * P.W by simp only [RP.W]; omega])
    rw [gA, gE, gD, gM, prod_val h.bs.pre] at vM
    refine h.core k (fun j hj => by
        simp only [mulArrs, List.mem_cons, List.not_mem_nil, or_false] at hj
        exact fitZ_W sz (by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro d (rfl | rfl) <;> decide)
      (by rw [r.gpr _ (by decide), h.r8]) r.sp r.rd r.wr
      (h.arrs_W k (by simp only [List.mem_singleton]; rintro j rfl; decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro d (rfl | rfl) <;> decide))
      h.live_lt ?_ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro j (rfl | rfl | rfl) <;> decide)
      (by simp) (by simp)
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · rw [vM]; simp [AWp, upd]
    · rw [k.num (by decide) (by decide) (fit_W sz (by decide)), gM]; simp [AWp, upd, wM, wMod]
    · rw [k.num (by decide) (by decide) (fit_W sz (by decide)), gZ]; simp [AWp, AW1, upd, wM, wMod, wZ, wE, wD]

end

end VG.Proof.Rsa.Arm.Recover

namespace VG.Proof.Rsa.Arm.RecoverDet
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Recover
open VG.Impl.Rsa.Arm.Keys hiding aT1 aT2 aT3 aT4
open VG.Proof.X25519.Arm
open VG.Impl.Rsa.Arm.RecoverDet
open VG.Impl.Rsa.Arm.Recover (nArr)
open VG.Proof.Rsa (sub32 b2n)

/-- A stage: `E`, the key working space, and its context with `v` words. -/
abbrev Dk (P : RP) (E : State → Prop) (A : State → Nat → Nat) (L : List Nat) (AW : State → Nat → Nat)
    (LW : List Nat) (V : State → Nat → Nat) (LS : List Nat) (v N : Nat) (σ s : State) : Prop :=
  E σ ∧ KS P σ (A σ) L (AW σ) LW (V σ) LS s ∧ Ws s P.B P.Z v N

/-- `d e`, `d e - 1` modulo `2^(32 W)`, and whether `d e ≥ 2`. -/
abbrev deV (P : RP) (σ : State) : Nat := Mv P σ
abbrev xV (P : RP) (σ : State) : Nat := sub32 P.W (deV P σ) 1
abbrev okDEv (P : RP) (σ : State) : Bool := !(decide (deV P σ < 1) || decide (xV P σ < 1))

/-- After `deMinus`. -/
def AN (P : RP) : Nat → Nat := upd (fun _ => 0) aN P.n
def AW1 (P : RP) (σ : State) : Nat → Nat := upd (upd (upd (fun _ => 0) wZ 0) wOne 1) wX (xV P σ)
def V1 (P : RP) (σ : State) : Nat → Nat := upd (fun _ => 0) sOkDE (b2n (okDEv P σ))

section
variable {P : RP}

theorem ws_regs' {s₁ s₂ : State} {v N : Nat} (h₁ : Ws s₁ P.B P.Z v N) (h₂ : Ws s₂ P.B P.Z v N) :
    ∀ r ∈ ctxRegs, s₁.gpr r = s₂.gpr r := by
  simp only [ctxRegs, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · rw [h₁.r7, h₂.r7]
  · rw [h₁.r8, h₂.r8]
  · rw [h₁.r9, h₂.r9]

/-- A piece the taint analysis checks with `r7`–`r9` public, between stages
with the working space's context. -/
theorem VP.dctx {F G : State → State → Prop} {c : Prog isa} {v N : Nat} (cert : DCert c)
    (hws : ∀ σ s, F σ s → Ws s P.B P.Z v N) (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G :=
  VP.taint _ cert (fun _ _ _ _ h₁ h₂ => ws_regs' (hws _ _ h₁) (hws _ _ h₂)) wp

theorem b2n_lt_one (p : Prop) [Decidable p] : b2n (decide p) ≤ 1 := by
  unfold b2n; split <;> omega

theorem b2n_nor (p q : Prop) [Decidable p] [Decidable q] :
    (if b2n (decide p) = 0 ∧ b2n (decide q) = 0 then 1 else 0) = b2n (!(decide p || decide q)) := by
  unfold b2n; by_cases a : p <;> by_cases b : q <;> simp [a, b]

theorem deMinus_ok {σ s : State}
    (h : KS P σ (Aload P σ) [VG.Impl.Rsa.Arm.Recover.aN] (AWp P σ)
      [VG.Impl.Rsa.Arm.Recover.wM, VG.Impl.Rsa.Arm.Recover.wMod, VG.Impl.Rsa.Arm.Recover.wZ] (fun _ => 0) [] s)
    (hw : Ws s P.B P.Z P.W 22) :
    WP isa deMinus s fun t => KS P σ (AN P) [aN] (AW1 P σ) [wX, wOne, wZ] (V1 P σ) [sOkDE] t ∧
      Ws t P.B P.Z P.W 22 := by
  simp only [deMinus, seqs]
  refine WP.seq (WP.mono (h.sub_W hw (o := wZ) (a := VG.Impl.Rsa.Arm.Recover.wM)
    (b := VG.Impl.Rsa.Arm.Recover.wM) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s1 ⟨h1, hw1, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h1.copy_W hw1 (o := wOne) (a := wZ) (by decide) (by decide) (by decide) (by decide))
    fun s2 ⟨h2, hw2, _⟩ => ?_)
  refine WP.seq (h2.setOne_W hw2 (j := wOne) (by decide) (by decide) fun s3 h3 hw3 _ => WP.block_nil ?_)
  refine WP.seq (WP.mono (h3.sub_W hw3 (o := wX) (a := VG.Impl.Rsa.Arm.Recover.wM) (b := wOne) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s4 ⟨h4, hw4, _, c4⟩ => ?_)
  refine WP.seq (h4.brw hw4 (d := sB0) (by decide) fun s5 h5 hw5 _ => WP.block_nil ?_)
  refine WP.seq (WP.mono (h5.sub_W hw5 (o := wT1) (a := wX) (b := wOne) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s6 ⟨h6, hw6, _, c6⟩ => ?_)
  refine h6.brw hw6 (d := sB1) (by decide) fun s7 h7 hw7 _ => ?_
  refine h7.norS hw7 (d := sOkDE) (a := sB0) (b := sB1) (by decide) (by decide)
    (by rw [upd_ne _ _ (by decide), upd_self, c4]; exact b2n_lt_one _)
    (by rw [upd_self, c6]; exact b2n_lt_one _) (by decide) fun t ht hwt => WP.block_nil ⟨?_, hwt⟩
  refine ht.mono (fun j hj => ?_) (fun j hj => ?_) (fun d hd => ?_)
  · simp only [List.mem_singleton] at hj; subst hj
    exact ⟨by decide, by simp only [AN, Aload]; rd_ev⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;> simp only [AW1, AWp, xV, deV] <;> rd_ev <;> simp [sub32]
  · simp only [List.mem_singleton] at hd; subst hd
    refine ⟨by decide, ?_⟩
    rw [upd_self, V1, upd_self, upd_self, upd_ne _ _ (show sB0 ≠ sB1 by decide), upd_self, c4, c6, b2n_nor]
    simp only [okDEv, xV, deV, AWp]
    rd_ev

theorem deMinus_vp {E : State → Prop} :
    VP (fun σ s => E σ ∧ KS P σ (Aload P σ) [VG.Impl.Rsa.Arm.Recover.aN] (AWp P σ)
      [VG.Impl.Rsa.Arm.Recover.wM, VG.Impl.Rsa.Arm.Recover.wMod, VG.Impl.Rsa.Arm.Recover.wZ] (fun _ => 0) [] s ∧
      Ws s P.B P.Z P.W 22) deMinus
      (Dk P E (fun _ => AN P) [aN] (AW1 P) [wX, wOne, wZ] (V1 P) [sOkDE] P.W 22) :=
  VP.dctx deMinus_taint (fun _ _ h => h.2.2) fun _ _ ⟨e, h, hw⟩ =>
    WP.mono (deMinus_ok h hw) fun _ ⟨ht, hwt⟩ => ⟨e, ht, hwt⟩

/-! ## The halvings -/

/-- `(u, x / 2^k, 2^k x)` after `k` halvings from `(n - 1, x mod 2^(32 w), x)`. -/
abbrev ts (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) (k : Nat) : Nat × Nat × Nat :=
  f^[k] (sub32 P.w P.n 1, xV P σ % 2 ^ (32 * P.w), xV P σ)

def AT (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) (k : Nat) : Nat → Nat :=
  upd (upd (upd (upd (upd (fun _ => 0) aOneN 1) aZN 0) aN P.n) aX2 (ts P f σ k).2.1) aU (ts P f σ k).1
def AWT (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) (k : Nat) : Nat → Nat :=
  upd (upd (upd (fun _ => 0) wZ 0) wOne 1) wX3 (ts P f σ k).2.2
def VT (P : RP) (σ : State) (k : Nat) : Nat → Nat :=
  upd (upd (fun _ => 0) sOkDE (b2n (okDEv P σ))) sK (32 * P.w - k)

abbrev LT : List Nat := [aU, aX2, aN, aZN, aOneN]
abbrev LWT : List Nat := [wX3, wOne, wZ]
abbrev LST : List Nat := [sK, sOkDE]

/-- After `k` halvings. -/
def TI (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) (k : Nat) (s : State) : Prop :=
  KS P σ (AT P f σ k) LT (AWT P f σ k) LWT (VT P σ k) LST s ∧ Ws s P.B P.Z P.w nArr

theorem twosPre_ok {f : Nat × Nat × Nat → Nat × Nat × Nat} {σ s : State}
    (h : KS P σ (AN P) [aN] (AW1 P σ) [wX, wOne, wZ] (V1 P σ) [sOkDE] s) (hw : Ws s P.B P.Z P.W 22) :
    WP isa twosPre s (TI P f σ 0) := by
  have sz := h.sizes
  simp only [twosPre, twosInit, seqs]
  refine WP.seq (WP.seq (WP.mono (h.copy_W hw (o := wX3) (a := wX) (by decide) (by decide) (by decide)
    (by decide)) fun s1 ⟨h1, hw1, _⟩ => ?_))
  refine WP.seq (h1.toN hw1 fun s2 h2 hw2 _ => WP.block_nil ?_)
  have h2' := h2.narrow (j := wX) (by decide) (by decide)
  rw [show 2 * wX = aX2 from rfl] at h2'
  have h3 := h2'.mono (A' := upd (AN P) aX2 (xV P σ % 2 ^ (32 * P.w))) (live' := [aX2, aN])
    (AW' := upd (AW1 P σ) wX3 (xV P σ)) (liveW' := [wX3, wOne, wZ]) (V' := V1 P σ) (ls' := [sOkDE])
    (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;> simp only [AN, AW1] <;> rd_ev)
    (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> exact ⟨by decide, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  refine WP.seq (WP.mono (h3.sub_w hw2 (o := aZN) (a := aN) (b := aN) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s4 ⟨h4, hw4, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h4.copy_w hw4 (o := aOneN) (a := aZN) (by decide) (by decide) (by decide)
    (by decide)) fun s5 ⟨h5, hw5, _, _⟩ => ?_)
  refine WP.seq (h5.setOne_w hw5 (j := aOneN) (by decide) (by decide) fun s6 h6 hw6 _ => WP.block_nil ?_)
  refine WP.mono (h6.sub_w hw6 (o := aU) (a := aN) (b := aOneN) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s7 ⟨h7, hw7, _, _⟩ => ?_
  refine h7.cntInit hw7 (e := 5) (by decide) (by have := sz.wle; omega) fun t ht hwt => WP.block_nil ⟨?_, hwt⟩
  refine ht.mono (fun j hj => ?_) (fun j hj => ?_) (fun d hd => ?_)
  · simp only [LT, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp only [AT, AN, ts, Function.iterate_zero, id] <;> rd_ev
  · simp only [LWT, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp only [AWT, AW1, ts, Function.iterate_zero, id] <;> rd_ev
  · simp only [LST, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;> simp only [VT, V1] <;> rd_ev

section
variable {σ s : State} {A : Nat → Nat} {live : List Nat} {AW : Nat → Nat} {liveW : List Nat}
  {V : Nat → Nat} {ls : List Nat}

/-- `halfIf j sl`: `[j]` halved if the header word `sl` holds 1. -/
theorem _root_.VG.Proof.Rsa.Arm.Recover.KS.halfIf {j sl : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.w nArr)
    (hj : j ∈ live) (hsl : sl ∈ ls) (bit : V sl ≤ 1) (hj1 : j ≠ aT1) (hj2 : j ≠ aT2)
    (hT : ∀ i ∈ live, i ≠ aT1 ∧ i ≠ aT2) (hlW : ∀ i ∈ liveW, i ≠ 18 ∧ j / 2 ≠ i) :
    WP isa (halfIf j sl) s fun t =>
      KS P σ (upd A j (if V sl = 0 then A j else A j / 2)) live AW liveW V ls t ∧ Ws t P.B P.Z P.w nArr := by
  unfold VG.Impl.Rsa.Arm.RecoverDet.halfIf
  simp only [seqs]
  refine WP.seq (WP.mono (h.copy_w hv (o := aT1) (a := j) (by decide) hj (Ne.symm hj1)
    fun i hi => Ne.symm (hlW i hi).1) fun s1 ⟨h1, hv1, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h1.copy_w hv1 (o := aT2) (a := j) (by decide) (List.mem_cons_of_mem _ hj)
    (Ne.symm hj2) fun i hi => Ne.symm (hlW i hi).1) fun s2 ⟨h2, hv2, _, _⟩ => ?_)
  refine WP.seq (h2.clr11 hv2 fun s3 h3 hv3 z3 => WP.block_nil ?_)
  refine WP.seq (WP.mono (h3.half_w hv3 (j := aT2) (List.mem_cons_self ..) z3
    fun i hi => Ne.symm (hlW i hi).1) fun s4 ⟨h4, hv4, _⟩ => ?_)
  refine WP.mono (h4.sel_w hv4 (o := j) (a := aT1) (b := aT2) (sl := sl) (h.live_lt j hj) (by simp) (by simp)
    hj1 hj2 hsl bit fun i hi => (hlW i hi).2) fun t ⟨ht, hvt, _⟩ => ⟨?_, hvt⟩
  refine ht.mono (fun i hi => ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ hi))), ?_⟩) (fun i hi => ⟨hi, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  have a1 := (hT i hi).1; have a2 := (hT i hi).2
  by_cases e : i = j
  · subst e
    simp only [upd_self, upd_ne _ _ (show aT1 ≠ aT2 by decide), upd_ne _ _ hj1]
  · simp only [upd_ne _ _ e, upd_ne _ _ a1, upd_ne _ _ a2]

end

/-- The step of the halvings. -/
abbrev TwoF (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) : Prop :=
  ∀ u x y, f (u, x, y) = if u % 2 = 0 then
    (if x % 2 = 0 then (u / 2, x / 2, 2 * y % 2 ^ (32 * P.W)) else (u / 2, x, y)) else (u, x, y)

theorem ts_succ (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) (k : Nat) :
    ts P f σ (k + 1) = f (ts P f σ k) := by
  simp only [ts]; rw [Function.iterate_succ_apply']

theorem twosBody_ok {f : Nat × Nat × Nat → Nat × Nat × Nat} (hf : TwoF P f) {σ s : State} {k : Nat}
    (h : TI P f σ k s) (hk : k < 32 * P.w) :
    WP isa twosBody s fun t => TI P f σ (k + 1) t ∧ t.z = decide (32 * P.w - (k + 1) = 0) := by
  obtain ⟨h, hv⟩ := h
  have sz := h.sizes
  generalize eu : (ts P f σ k).1 = u at *
  generalize ex : (ts P f σ k).2.1 = x at *
  generalize ey : (ts P f σ k).2.2 = y at *
  have aU' : AT P f σ k aU = u := by simp only [AT]; rd_ev; exact eu
  have aX' : AT P f σ k aX2 = x := by simp only [AT]; rd_ev; exact ex
  have wY : AWT P f σ k wX3 = y := by simp only [AWT]; rd_ev; exact ey
  simp only [twosBody, seqs, twosFlags]
  refine WP.seq ?_
  simp only [List.append_assoc]
  refine h.bitOf_w hv (j := aU) (sl := sU) (by decide) (by decide) fun s1 h1 hv1 _ => ?_
  refine h1.bitOf_w hv1 (j := aX2) (sl := sX) (by decide) (by decide) fun s2 h2 hv2 _ => ?_
  rw [aU'] at h2; rw [aX'] at h2
  refine h2.notS hv2 (d := sEven) (a := sU) (by decide) (by rd_ev <;> omega) (by decide) fun s3 h3 hv3 => ?_
  refine h3.norS hv3 (d := sBoth) (a := sU) (b := sX) (by decide) (by decide) (by rd_ev <;> omega) (by rd_ev <;> omega)
    (by decide) fun s4 h4 hv4 => WP.block_nil ?_
  refine WP.seq (WP.mono (h4.halfIf hv4 (j := aU) (sl := sEven) (by decide) (by decide) (by rd_ev <;> omega)
    (by decide) (by decide) (by decide) (by decide)) fun s5 ⟨h5, hv5⟩ => ?_)
  refine WP.seq (WP.mono (h5.halfIf hv5 (j := aX2) (sl := sBoth) (by decide) (by decide)
    (by rd_ev <;> split <;> omega) (by decide) (by decide) (by decide) (by decide)) fun s6 ⟨h6, hv6⟩ => ?_)
  refine WP.seq (h6.toW hv6 fun s7 h7 hv7 _ => WP.block_nil ?_)
  refine WP.seq (WP.mono (h7.copy_W hv7 (o := wT1) (a := wX3) (by decide) (by decide) (by decide) (by decide))
    fun s8 ⟨h8, hv8, _⟩ => ?_)
  refine WP.seq (WP.mono (h8.copy_W hv8 (o := wT2) (a := wX3) (by decide) (by decide) (by decide) (by decide))
    fun s9 ⟨h9, hv9, _⟩ => ?_)
  refine WP.seq (h9.clr11 hv9 fun s10 h10 hv10 z10 => WP.block_nil ?_)
  refine WP.seq (WP.mono (h10.shl_W hv10 (j := wT2) (by decide) (by omega) (by decide))
    fun s11 ⟨h11, hv11, _, _⟩ => ?_)
  rw [z10] at h11
  refine WP.seq (WP.mono (h11.sel_W hv11 (o := wX3) (a := wT1) (b := wT2) (sl := sBoth) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rd_ev <;> split <;> omega) (by decide))
    fun s12 ⟨h12, hv12, _⟩ => ?_)
  refine h12.toN hv12 fun s13 h13 hv13 _ => ?_
  have wl := sz.wle
  have vK : VT P σ k sK = 32 * P.w - k := by simp only [VT]; rd_up
  refine WP.mono (h13.cntNext hv13 (by decide) (by rd_up; rw [vK]; omega)
    (by rd_up; rw [vK]; omega)) fun t ⟨ht, hvt, zt⟩ => ⟨⟨?_, hvt⟩, ?_⟩
  rotate_left
  · rw [zt]; rd_up; rw [vK, Nat.sub_sub]
  have hs := ts_succ P f σ k
  rw [show ts P f σ k = (u, x, y) from Prod.ext eu (Prod.ext ex ey), hf] at hs
  refine ht.mono (fun j hj => ?_) (fun j hj => ?_) (fun d hd => ?_)
  · simp only [LT, List.mem_cons, List.not_mem_nil, or_false] at hj
    refine ⟨by rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide, ?_⟩
    simp only [AT, hs]
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> rd_ev <;> simp only [eu, ex] <;>
      (rcases Nat.mod_two_eq_zero_or_one u with a | a <;> rcases Nat.mod_two_eq_zero_or_one x with b | b <;>
        simp [a, b])
  · simp only [LWT, List.mem_cons, List.not_mem_nil, or_false] at hj
    refine ⟨by rcases hj with rfl | rfl | rfl <;> decide, ?_⟩
    simp only [AWT, hs]
    rcases hj with rfl | rfl | rfl <;> rd_ev <;> simp only [ey] <;>
      (rcases Nat.mod_two_eq_zero_or_one u with a | a <;> rcases Nat.mod_two_eq_zero_or_one x with b | b <;>
        simp [a, b])
  · simp only [LST, List.mem_cons, List.not_mem_nil, or_false] at hd
    refine ⟨by rcases hd with rfl | rfl <;> decide, ?_⟩
    rcases hd with rfl | rfl <;> rd_up <;> simp only [VT] <;> rd_up <;> omega

/-- A loop of `K ≥ 1` iterations whose body takes the stage `I k` to `I (k + 1)`, with Z when
`K - (k + 1) = 0`. -/
theorem VP.count {E : State → Prop} {I : Nat → State → State → Prop} {body : Prog isa} {K : Nat}
    (pos : 0 < K) (hb : ∀ k, k < K → VP (fun σ s => E σ ∧ I k σ s) body
      (fun σ s => (E σ ∧ I (k + 1) σ s) ∧ s.z = decide (K - (k + 1) = 0))) :
    VP (fun σ s => E σ ∧ I 0 σ s) (.loop body .ne) (fun σ s => E σ ∧ I K σ s) := by
  let J := fun n σ s => E σ ∧ n ≤ K ∧ I (K - n) σ s
  have hl := VP.loop (I := J) (body := body) (c := .ne) (Q := fun σ s => E σ ∧ I K σ s) (fun n => ?_)
  · refine (hl (K - 1)).mono (fun σ s ⟨e, h⟩ => ⟨e, by omega, by rw [show K - (K - 1 + 1) = 0 by omega]; exact h⟩)
      fun _ _ h => h
  · refine (VP.of_imp (p := n + 1 ≤ K) (fun σ s h => h.2.1) fun hn => ?_)
    refine (hb (K - (n + 1)) (by omega)).mono (fun σ s ⟨e, _, h⟩ => ⟨e, h⟩) fun σ s ⟨⟨e, h⟩, z⟩ => ⟨?_, ?_, ?_⟩
    · show some (!s.z) = some (decide (0 < n))
      rw [z, show K - (K - (n + 1) + 1) = n by omega]
      by_cases h0 : n = 0 <;> simp [h0, Nat.pos_iff_ne_zero]
    · intro h0; subst h0; refine ⟨e, ?_⟩; rw [show K - (0 + 1) + 1 = K by omega] at h; exact h
    · intro hp; refine ⟨e, by omega, ?_⟩; rw [show K - (n + 1) + 1 = K - n by omega] at h; exact h

theorem twos_vp {f : Nat × Nat × Nat → Nat × Nat × Nat} (hf : TwoF P f) {E : State → Prop} :
    VP (Dk P E (fun _ => AN P) [aN] (AW1 P) [wX, wOne, wZ] (V1 P) [sOkDE] P.W 22) twos
      (fun σ s => E σ ∧ TI P f σ (32 * P.w) s) := by
  refine VP.seq (G := fun σ s => E σ ∧ TI P f σ 0 s) (VP.dctx twosPre_taint (fun _ _ h => h.2.2)
    fun σ s ⟨e, h, hw⟩ => WP.mono (twosPre_ok h hw) fun t ht => ⟨e, ht⟩) ?_
  refine VP.of_imp (p := 0 < 32 * P.w) (fun σ s ⟨_, h, _⟩ => by show 0 < 32 * (2 * P.w6 + 2); omega) fun pos => ?_
  exact VP.count (E := E) (I := fun k σ s => TI P f σ k s) pos fun k hk => VP.dctx twosBody_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h⟩ =>
    WP.mono (twosBody_ok hf h hk) fun t ⟨ht, z⟩ => ⟨⟨e, ht⟩, z⟩

end

end VG.Proof.Rsa.Arm.RecoverDet
