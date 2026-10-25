module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Fin
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Args
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.WBody
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.MontP
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Slot
import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.RangeCover

/-!
# A candidate on PPC64LE: trial division and Miller–Rabin

`test_ok`: once `gcd(c − 1, e) = 1`, the test's arguments into the header
(`testArgs_ok`), trial division (`DivOk`), and unless it finds a divisor, the
working space prepared (`prep_ok`), the witnesses (`millerRabin_ok`) and the
result (`testResult`): each way it ends gives the contract's results.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (test testResult trialDiv finish finNone finPrime nArr hTrial testArgs)
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth hUsed hStat hRand hRandLen hK hChecks)
open VG.Impl.RsaKeyGen (TrialTable32.symbol TrialTable32.packed)
open VG.Proof.MillerRabin.PPC64LE.Search (Prep)
open VG.Proof.MillerRabin.PPC64LE (RoundImpl Env arr)
open VG.Proof.Bignum (slot)

/-- The table of trial division, from the call's start. -/
structure TabOk (s0 : State) : Prop where
  fit : (s0.syms TrialTable32.symbol).toNat + 8 * 1024 ≤ 2 ^ 64
  rd : (⟨s0.syms TrialTable32.symbol, 8 * 1024⟩ : Region) ∈ s0.rd
  held : ∀ i < 1024, s0.mem.readW (s0.syms TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 64 =
    TrialTable32.packed.getD i 0
  dj : ∀ ρ ∈ [cO s0, cU s0, cS s0, cF s0], (⟨s0.syms TrialTable32.symbol, 8 * 1024⟩ : Region).Disjoint ρ

/-- The scratch region, as the proofs state it. -/
abbrev sB (s0 : State) : Addr := PPC64LE.stackArg s0 1

/-- The scratch's length in words. -/
abbrev sL (s0 : State) : Nat := (PPC64LE.stackArg s0 2).toNat

theorem cS_eq (s0 : State) : cS s0 = ⟨sB s0, 8 * sL s0⟩ := by simp only [cS, Nat.mul_comm]

/-- What changes within the scratch, from `Ctx`'s view. -/
theorem frame_scr {s0 : State} {m m' : Mem} (h : Frame [(⟨sB s0, 8 * sL s0⟩ : Region)] m m') :
    Frame [cS s0, below (off (cB s0) 176) 176] m m' := h.mono (by rw [cS_eq]; simp)

/-- `Outs` within the scratch. -/
theorem frame_outs {s0 : State} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs (sB s0) rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ 8 * sL s0) : Frame [cS s0, below (off (cB s0) 176) 176] m m' :=
  frame_scr (frame_of_outs h hr)

/-- The table's words through `Bx`. -/
theorem TabOk.held_at {s0 s : State} (h : TabOk s0) (hb : Bx s0 s) {i : Nat} (hi : i < 1024) :
    s.mem.readW (s0.syms TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 64 = TrialTable32.packed.getD i 0 := by
  rw [hb.out.readW (r := ⟨s0.syms TrialTable32.symbol, 8 * 1024⟩)
    (Offset.contains_base _ (by omega) (by have := h.fit; omega)) h.dj (by decide)]
  exact h.held i hi

/-- Octets of an input through `Bx`. -/
theorem bytes_bx {s0 s : State} (hb : Bx s0 s) {A : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (hd : ∀ ρ ∈ [cO s0, cU s0, cS s0, cF s0], (⟨A, n⟩ : Region).Disjoint ρ) :
    Spec.Rsa.bytesAt s.mem A n = Spec.Rsa.bytesAt s0.mem A n :=
  bytes_keep hb.out hn hd

/-- The facts once `gcd(c − 1, e) = 1`, for the candidate `c` of `w` words. -/
structure TIn (s0 s : State) (w c : Nat) : Prop where
  ctx : Ctx s0 s
  env : Env s (sB s0) (8 * sL s0) w
  lay : Lay s.mem (sB s0) (sL s0) w
  h35 : slot w nArr ≤ 8 * sL s0
  arr0 : arr s.mem (sB s0) w 0 = c
  shape : PrimeShape (64 * w) c
  hw : oL s0 = 8 * w
  hw64 : w ≤ 64
  r26 : s.gpr .r26 = s0.gpr .r10
  r27 : s.gpr .r27 = PPC64LE.stackArg s0 0
  r28 : s.gpr .r28 = BitVec.ofNat 64 (8 * w)
  h8 : 8 * w ≤ rL s0
  syms : s.syms = s0.syms
  tab : TabOk s0
  hop : cOp s0 = if Spec.RsaKeyGen.obviouslyComposite (64 * w) c then
      some (.rejected, (Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)).drop (8 * w))
    else (Spec.RsaKeyGen.primalityTest c ((Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)).drop (8 * w))).map
      fun pr => (if pr.1 then .prime c else .rejected, pr.2)

/-- `Ctx` through code that keeps memory, the regions and `r2`, `r23`–`r25`. -/
theorem Ctx.keep {s0 s t : State} {rs : List Reg} (h : Ctx s0 s) (k : Keep rs s t) (hm : t.mem = s.mem)
    (hr : ∀ r ∈ [Reg.r2, .r23, .r24, .r25], r ∉ rs := by decide) : Ctx s0 t :=
  h.step k.sp k.rd k.wr (by rw [hm]; exact Frame.refl _ _) (k.gpr _ (hr _ (by simp)))
    (k.gpr _ (hr _ (by simp))) (k.gpr _ (hr _ (by simp))) (k.gpr _ (hr _ (by simp)))

/-- The test's result from the status and octets used the witnesses left. -/
theorem res_ok {s0 u : State} {w c : Nat} (hc : Ctx s0 u) (hp : Prep u (sB s0) (sL s0) w c)
    (hw : oL s0 = 8 * w) (hres : match Spec.RsaKeyGen.primalityTest c
        ((Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)).drop (8 * w)) with
      | none => word u.mem (sB s0) (8 * hStat) = BitVec.ofNat 64 0
      | some (b, rest) => word u.mem (sB s0) (8 * hStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
          word u.mem (sB s0) (8 * hUsed) = BitVec.ofNat 64 (rL s0 - rest.length))
    (hop : cOp s0 = (Spec.RsaKeyGen.primalityTest c
        ((Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)).drop (8 * w))).map
      fun pr => (if pr.1 then .prime c else .rejected, pr.2)) :
    WP isa testResult u fun t => Bx s0 t ∧ CQ s0 (t.gpr .r3) t.mem := by
  have e := hp.env
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  rw [slot_lin] at hZ
  have hcS : (cO s0).Disjoint ⟨sB s0, 8 * sL s0⟩ := by rw [← cS_eq]; exact hc.bx.pre.oS
  generalize hpt : Spec.RsaKeyGen.primalityTest c ((Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)).drop (8 * w)) = pt
    at hres hop
  unfold testResult
  refine WP.seq (WP.mono (WP.keep [.r28, .r3] (Q := fun t => t.gpr .r28 = word u.mem (sB s0) (8 * hUsed) ∧
      t.gpr .r3 = word u.mem (sB s0) (8 * hStat) ∧ t.mem = u.mem) (by
    simp only [ldh, hUsed, hStat]
    prun [e.h31, hs.ld (d := 152) (n := 8) (by omega), hs.ld (d := 160) (n := 8) (by omega)]) (by decide)) fun t₁ ⟨⟨a28, a3, m₁⟩, k₁⟩ => ?_)
  have c₁ := hc.keep k₁ m₁
  rcases pt with _ | ⟨b, rest⟩
  · refine WP.ite _ (eval_zero_ofNat _ _ (by decide) (a3.trans hres)) (fun _ => ?_) (fun h => absurd h (by decide))
    exact finNone_post c₁ (by rw [hop]; rfl)
  · obtain ⟨hst, hus⟩ := hres
    refine WP.ite _ (eval_zero_ofNat _ _ (by split <;> decide) (a3.trans hst))
      (fun h => absurd h (by cases b <;> decide)) (fun _ => ?_)
    refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 (if b then 0 else 1) ∧
        t.mem = t₁.mem) (by
      prun [a3, hst]
      cases b <;> rfl) (by decide)) fun t₂ ⟨⟨b3, m₂⟩, k₂⟩ => ?_)
    have c₂ := c₁.keep k₂ m₂
    refine WP.ite _ (eval_zero_ofNat _ _ (by split <;> decide) b3) (fun h => ?_) (fun h => ?_)
    · have hb : b = true := by revert h; cases b <;> decide
      subst hb
      have p₂ := hp.keep (e.keep (k₁.trans k₂) (by decide)) (fun _ _ => by rw [m₂, m₁]) (fun _ _ => by rw [m₂, m₁])
      refine finPrime_post c₂ p₂.env.hs p₂.env.h31 (by rw [hw]; omega) hw (by omega) hcS ?_ (by rw [hop]; rfl)
        (by rw [k₂.gpr _ (by decide), a28, hus])
      rw [← slot0 (w := w)]; exact p₂.n
    · have hb : b = false := by revert h; cases b <;> decide
      subst hb
      refine fin_ok 3 (by decide) c₂ (by rw [hop]; rfl) (by rw [outOf, hop]; rfl)
        (by rw [k₂.gpr _ (by decide), a28, hus, usedOf, hop]; rfl)

theorem bytesAt_length (m : Mem) (A : Addr) (n : Nat) : (Spec.Rsa.bytesAt m A n).length = n := by
  simp [Spec.Rsa.bytesAt]

theorem hR_dj {s0 : State} (hp : CIn s0) : ∀ r ∈ [cO s0, cU s0, cS s0, cF s0], (cR s0).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.oR.symm
  · exact hp.uR.symm
  · exact hp.rS
  · exact hp.Fr.symm

theorem hP_dj {s0 : State} (hp : CIn s0) : ∀ r ∈ [cO s0, cU s0, cS s0, cF s0], (cP s0).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.oP.symm
  · exact hp.uP.symm
  · exact hp.pS
  · exact hp.Fp.symm

theorem hE_dj {s0 : State} (hp : CIn s0) : ∀ r ∈ [cO s0, cU s0, cS s0, cF s0], (cE s0).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.oE.symm
  · exact hp.uE.symm
  · exact hp.eS
  · exact hp.Fe.symm

/-- What holds of the call throughout the test. -/
structure TC (s0 : State) (w c : Nat) : Prop where
  h35 : slot w nArr ≤ 8 * sL s0
  shape : PrimeShape (64 * w) c
  hw : oL s0 = 8 * w
  hw64 : w ≤ 64
  h8 : 8 * w ≤ rL s0
  tab : TabOk s0
  hop : cOp s0 = if Spec.RsaKeyGen.obviouslyComposite (64 * w) c then
      some (.rejected, (Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)).drop (8 * w))
    else (Spec.RsaKeyGen.primalityTest c ((Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)).drop (8 * w))).map
      fun pr => (if pr.1 then .prime c else .rejected, pr.2)

theorem TIn.tc {s0 s : State} {w c : Nat} (h : TIn s0 s w c) : TC s0 w c :=
  ⟨h.h35, h.shape, h.hw, h.hw64, h.h8, h.tab, h.hop⟩

theorem TC.c8 {s0 : State} {w c : Nat} (h : TC s0 w c) (hw4 : 4 ≤ w) : 8161 < c := by
  have := h.shape.2.1
  have : 2 ^ 14 ≤ 2 ^ (64 * w - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- The test's arguments in the header. -/
structure THdr (s0 : State) (w : Nat) (m : Mem) : Prop where
  rand : word m (sB s0) (8 * hRand) = s0.gpr .r10
  randLen : word m (sB s0) (8 * hRandLen) = PPC64LE.stackArg s0 0
  used : word m (sB s0) (8 * hUsed) = BitVec.ofNat 64 (8 * w)
  kk : word m (sB s0) (8 * hK) = BitVec.ofNat 64 (8 * w)
  checks : word m (sB s0) (8 * hChecks) = BitVec.ofNat 64 (VG.Proof.RsaKeyGen.checksW w)

theorem THdr.keep {s0 : State} {w : Nat} {m m' : Mem} (h : THdr s0 w m)
    (ow : ∀ d, 128 ≤ d → d + 8 ≤ 224 → word m' (sB s0) d = word m (sB s0) d) : THdr s0 w m' :=
  ⟨(ow _ (by simp only [hRand]; omega) (by simp only [hRand]; omega)).trans h.rand,
    (ow _ (by simp only [hRandLen]; omega) (by simp only [hRandLen]; omega)).trans h.randLen,
    (ow _ (by simp only [hUsed]; omega) (by simp only [hUsed]; omega)).trans h.used,
    (ow _ (by simp only [hK]; omega) (by simp only [hK]; omega)).trans h.kk,
    (ow _ (by simp only [hChecks]; omega) (by simp only [hChecks]; omega)).trans h.checks⟩

/-- After `testArgs`. -/
structure T1 (s0 : State) (w c : Nat) (s : State) : Prop where
  ctx : Ctx s0 s
  env : Env s (sB s0) (8 * sL s0) w
  lay : Lay s.mem (sB s0) (sL s0) w
  arr0 : arr s.mem (sB s0) w 0 = c
  hdr : THdr s0 w s.mem
  trial : word s.mem (sB s0) (8 * hTrial) = BitVec.ofNat 64 (nTrial w)
  r28 : s.gpr .r28 = BitVec.ofNat 64 (8 * w)
  syms : s.syms = s0.syms
  tc : TC s0 w c

theorem argsS {s0 s : State} {w c : Nat} (h : TIn s0 s w c) : WP isa (.block testArgs) s (T1 s0 w c) := by
  have hp := h.ctx.bx.pre
  have e := h.env
  have hnw := e.hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  rw [slot_lin] at hZ
  refine WP.mono_syms (testArgs_ok e h.lay.wW h.hw64) fun t₁ ⟨⟨ao, o₁, _⟩, k₁⟩ sy₁ => ?_
  have ow : ∀ d, d + 8 ≤ 128 ∨ 224 ≤ d → d + 8 ≤ 8 * sL s0 → word t₁.mem (sB s0) d = word s.mem (sB s0) d :=
    fun d hd hd' => o₁.word hd (by omega)
  refine ⟨h.ctx.step k₁.sp k₁.rd k₁.wr (frame_scr (frame_of_outside o₁ (by omega))) (k₁.gpr _ (by decide))
    (k₁.gpr _ (by decide)) (k₁.gpr _ (by decide)) (k₁.gpr _ (by decide)), e.keep k₁ (by decide),
    ⟨(ow 0 (by omega) (by omega)).trans h.lay.len, (ow 48 (by omega) (by omega)).trans h.lay.wW,
      (ow 224 (by omega) (by omega)).trans h.lay.strideW,
      fun j hj => (ow _ (by omega) (by omega)).trans (h.lay.arrW j hj)⟩,
    by rw [← h.arr0]; exact o₁.val32 (by rw [slot_lin]; omega) (by rw [slot_lin]; omega),
    ⟨ao.rand.trans h.r26, ao.randLen.trans h.r27, ao.used.trans h.r28,
      ao.k.trans (by rw [h.ctx.r24, ← h.hw]; exact (ofNat_toNat64 _).symm), ao.checks⟩, ao.trial,
    (k₁.gpr _ (by decide)).trans h.r28, sy₁.trans h.syms, h.tc⟩

/-- Trial division's start. -/
theorem T1.divIn {s0 s : State} {w c : Nat} (h : T1 s0 w c s) : DivIn s (sB s0) (8 * sL s0) w (nTrial w) :=
  ⟨h.env, h.trial, by unfold nTrial; split <;> decide, by unfold nTrial; split <;> decide,
    by rw [h.syms]; exact h.tc.tab.fit, by rw [h.syms, h.ctx.bx.rd]; exact h.tc.tab.rd,
    fun i hi => by rw [h.syms]; exact h.tc.tab.held_at h.ctx.bx hi⟩

theorem T1.tabDj {s0 s : State} {w c : Nat} (h : T1 s0 w c s) :
    Region.Disjoint ⟨s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol, 8 * 1024⟩ ⟨sB s0, 8 * sL s0⟩ := by
  rw [h.syms, ← cS_eq]; exact h.tc.tab.dj _ (by simp)

/-- After trial division. -/
structure T2 (s0 : State) (w c : Nat) (s : State) : Prop where
  ctx : Ctx s0 s
  env : Env s (sB s0) (8 * sL s0) w
  lay : Lay s.mem (sB s0) (sL s0) w
  arr0 : arr s.mem (sB s0) w 0 = c
  hdr : THdr s0 w s.mem
  f : s.gpr .r22 = BitVec.ofNat 64 (if Spec.RsaKeyGen.obviouslyComposite (64 * w) c then 1 else 0)
  r28 : s.gpr .r28 = BitVec.ofNat 64 (8 * w)
  tc : TC s0 w c

theorem trialS {trial : Prog isa} (D : DivOk trial) {s0 s : State} {w c : Nat} (h : T1 s0 w c s) :
    WP isa (trialDiv trial) s (T2 s0 w c) := by
  have hp := h.ctx.bx.pre
  have e := h.env
  have hnw := e.hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  rw [slot_lin] at hZ
  refine WP.mono (trialDiv_ok D h.divIn h.tabDj) fun t₂ ⟨f₂, m₂, g₂, r23₂, r24₂, rd₂, wr₂, sp₂⟩ => ?_
  rw [h.arr0, show nTrial w = if w ≤ 16 then 512 else 1024 from rfl, trialPrefix_spec (h.tc.c8 hw4)] at f₂
  have w₂ : Frame [cS s0, below (off (cB s0) 176) 176] s.mem t₂.mem := by
    rw [m₂]
    refine frame_scr (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW
      (List.mem_singleton_self _) _ ?_) <;> exact Offset.contains_base _ (by omega) (by omega)
  have o₂ : Outs (sB s0) [(24, 8), (40, 8)] s.mem t₂.mem := by
    rw [m₂]
    exact (Outs.of_outside (writeW_outside _ _ (d := 24) _ (by omega)) (by simp)).trans
      (Outs.of_outside (writeW_outside _ _ (d := 40) _ (by omega)) (by simp))
  have ow : ∀ d, d + 8 ≤ 24 ∨ (32 ≤ d ∧ d + 8 ≤ 40) ∨ 48 ≤ d → d + 8 ≤ 8 * sL s0 →
      word t₂.mem (sB s0) d = word s.mem (sB s0) d := fun d hd hd' =>
    o₂.word (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp only [] <;> omega) (by omega)
  refine ⟨h.ctx.step sp₂ rd₂ wr₂ w₂ (g₂ _ (by decide)) r23₂ r24₂ (g₂ _ (by decide)),
    ⟨e.hs.congr wr₂, (g₂ _ (by decide)).trans e.h10, (g₂ _ (by decide)).trans e.h29,
      (g₂ _ (by decide)).trans e.h11, (g₂ _ (by decide)).trans e.h31, e.hw, e.hw', e.hZ⟩,
    ⟨(ow 0 (by omega) (by omega)).trans h.lay.len, (ow 48 (by omega) (by omega)).trans h.lay.wW,
      (ow 224 (by omega) (by omega)).trans h.lay.strideW,
      fun j hj => (ow _ (by omega) (by omega)).trans (h.lay.arrW j hj)⟩, ?_,
    h.hdr.keep fun d h1 h2 => ow d (by omega) (by omega), f₂, (g₂ _ (by decide)).trans h.r28, h.tc⟩
  rw [← h.arr0]
  exact o₂.val32 (fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp only [slot_lin] <;> omega) (by rw [slot_lin]; omega)

/-- A divisor: rejected. -/
theorem compFin {s0 s : State} {w c : Nat} (h : T2 s0 w c s)
    (hoc : Spec.RsaKeyGen.obviouslyComposite (64 * w) c = true) :
    WP isa (finish 3) s fun t => Bx s0 t ∧ CQ s0 (t.gpr .r3) t.mem := by
  have hop := h.tc.hop
  have h8 := h.tc.h8
  rw [hoc] at hop
  simp only [↓reduceIte] at hop
  refine fin_ok 3 (by decide) h.ctx (by rw [hop]; rfl) (by rw [outOf, hop]) ?_
  rw [h.r28, usedOf, hop]
  simp only [List.length_drop, bytesAt_length]
  congr 1; omega

/-- The working space prepared. -/
structure T3 (s0 : State) (w c : Nat) (s : State) : Prop where
  ctx : Ctx s0 s
  prep : Prep s (sB s0) (sL s0) w c
  lin : LIn s (sB s0) (s0.gpr .r10) (sL s0) w c (rL s0) (VG.Proof.RsaKeyGen.checksW w)
    (Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0))
  hu0 : word s.mem (sB s0) (8 * hUsed) = BitVec.ofNat 64 (8 * w)
  tc : TC s0 w c
  noc : Spec.RsaKeyGen.obviouslyComposite (64 * w) c = false

theorem prepS {s0 s : State} {w c : Nat} (h : T2 s0 w c s)
    (hoc : Spec.RsaKeyGen.obviouslyComposite (64 * w) c = false) :
    WP isa VG.Impl.MillerRabin.PPC64LE.Search.montPrepHi s (T3 s0 w c) := by
  have hp := h.ctx.bx.pre
  have e := h.env
  have hnw := e.hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  have h35 := h.tc.h35
  simp only [nArr] at h35
  rw [slot_lin] at hZ h35
  have hfS := hp.fS
  have hcB := cB_fit hp
  have hrl := (PPC64LE.stackArg s0 0).isLt
  refine WP.mono (prep_ok e h.lay h.arr0 h.tc.shape.1 (by have := h.tc.c8 hw4; omega) (by
    have := h.tc.shape.2.1
    have : 2 ^ (64 * (w - 1)) < 2 ^ (64 * w - 2) := Nat.pow_lt_pow_right (by decide) (by omega)
    omega)) fun t₃ ⟨⟨p₃, o₃⟩, k₃⟩ => ?_
  have c₃ := h.ctx.step k₃.sp k₃.rd k₃.wr (frame_outs o₃ (fun x hx => by
    simp only [VG.Proof.MillerRabin.PPC64LE.Search.mpRanges, VG.Impl.MillerRabin.PPC64LE.aE, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp only [slot_lin] <;> omega)) (k₃.gpr _ (by decide))
    (k₃.gpr _ (by decide)) (k₃.gpr _ (by decide)) (k₃.gpr _ (by decide))
  have ow₃ : ∀ d, 64 ≤ d → d + 8 ≤ 256 → word t₃.mem (sB s0) d = word s.mem (sB s0) d := fun d h1 h3 =>
    o₃.word (fun x hx => by
      simp only [VG.Proof.MillerRabin.PPC64LE.Search.mpRanges, VG.Impl.MillerRabin.PPC64LE.aE, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp only [slot_lin] <;> omega) (by omega)
  have hd := h.hdr.keep (m' := t₃.mem) fun d h1 h2 => ow₃ d (by omega) (by omega)
  have bF : below (off (cB s0) 176) 176 = ⟨cB s0, 176⟩ := by
    simp only [below, off, BitVec.add_sub_cancel]
  have sp₃ : t₃.sp = off (cB s0) 176 := c₃.bx.sp
  have P : LIn t₃ (sB s0) (s0.gpr .r10) (sL s0) w c (rL s0) (VG.Proof.RsaKeyGen.checksW w)
      (Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)) := {
    h35 := h.tc.h35
    shape := h.tc.shape
    hch := (VG.Proof.RsaKeyGen.checksW_eq w (by have := h.tc.hw64; omega) hw4).symm
    hch' := by have := VG.Proof.RsaKeyGen.checksW_le w; omega
    rand := hd.rand
    rlen := hd.randLen.trans (ofNat_toNat64 _).symm
    kk := hd.kk
    chk := hd.checks
    hrl := hrl
    tape := bytes_bx c₃.bx hrl (hR_dj hp)
    rN := fun i hi => ⟨cR s0, List.mem_append_left _ (by rw [c₃.bx.rd]; exact hp.rR),
      Offset.contains_base _ (by simp only [rL] at hi; omega) (by have := hp.fr; simp only [rL] at hi; omega)⟩
    rD := by
      intro ρ hρ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
      rcases hρ with rfl | rfl
      · rw [← cS_eq]; exact hp.rS
      · rw [sp₃, bF]; exact (hp.Fr.sub_left (Region.sub_prefix (by decide))).symm
    wr := by rw [c₃.bx.wr, bodyWr, hp.wr, ← cS_eq]; simp
    hsp := by rw [sp₃]; simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    hstk := by rw [sp₃, bF, ← cS_eq]; exact hp.FS.sub_left (Region.sub_prefix (by decide)) }
  exact ⟨c₃, p₃, P, hd.used, h.tc, hoc⟩

/-- After the witnesses. -/
structure T4 (s0 : State) (w c : Nat) (s : State) : Prop where
  ctx : Ctx s0 s
  prep : Prep s (sB s0) (sL s0) w c
  res : match Spec.RsaKeyGen.primalityTest c ((Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)).drop (8 * w)) with
    | none => word s.mem (sB s0) (8 * hStat) = BitVec.ofNat 64 0
    | some (b, rest) => word s.mem (sB s0) (8 * hStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
        word s.mem (sB s0) (8 * hUsed) = BitVec.ofNat 64 (rL s0 - rest.length)
  tc : TC s0 w c
  noc : Spec.RsaKeyGen.obviouslyComposite (64 * w) c = false

theorem mrStage {s0 s : State} {w c : Nat} (R : RoundImpl) (h : T3 s0 w c s) :
    WP isa (VG.Impl.RsaKeyGen.PPC64LE.Witness.millerRabin R.name R.code) s (T4 s0 w c) := by
  have hp := h.ctx.bx.pre
  have hcB := cB_fit hp
  have bF : below (off (cB s0) 176) 176 = ⟨cB s0, 176⟩ := by
    simp only [below, off, BitVec.add_sub_cancel]
  refine WP.mono (millerRabin_ok R h.lin h.prep h.hu0 h.tc.h8) fun t₄ ho => ?_
  have f₄ := ho.frame
  rw [h.ctx.bx.sp, ← cS_eq] at f₄
  have cs₄ : ∀ r ∈ [Reg.r2, .r23, .r24, .r25], t₄.gpr r = s.gpr r := fun r hr =>
    ho.cs r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;>
      decide) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;>
      decide) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;>
      decide)
  exact ⟨h.ctx.step ho.sp ho.rd ho.wr f₄ (cs₄ _ (by simp)) (cs₄ _ (by simp)) (cs₄ _ (by simp)) (cs₄ _ (by simp)),
    ho.prep, ho.res, h.tc, h.noc⟩

theorem T4.result_ok {s0 s : State} {w c : Nat} (h : T4 s0 w c s) :
    WP isa testResult s fun t => Bx s0 t ∧ CQ s0 (t.gpr .r3) t.mem := by
  have hop := h.tc.hop
  rw [h.noc] at hop
  simp only [Bool.false_eq_true, ↓reduceIte] at hop
  exact res_ok h.ctx h.prep h.tc.hw h.res hop

/-- Once `gcd(c − 1, e) = 1`: trial division, then Miller–Rabin. -/
theorem test_ok {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) {s0 s : State} {w c : Nat}
    (h : TIn s0 s w c) :
    WP isa (test trial R.name R.code) s fun t => Bx s0 t ∧ CQ s0 (t.gpr .r3) t.mem := by
  unfold test
  simp only [VG.Impl.RsaKeyGen.PPC64LE.Candidate.seqs]
  refine WP.seq (WP.mono (argsS h) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (trialS D h₁) fun t₂ h₂ => ?_)
  refine WP.ite _ (eval_nonzero_ofNat' _ _ (by split <;> decide) h₂.f) (fun hz => ?_) (fun hz => ?_)
  · exact compFin h₂ (by revert hz; cases Spec.RsaKeyGen.obviouslyComposite (64 * w) c <;> decide)
  · have hoc : Spec.RsaKeyGen.obviouslyComposite (64 * w) c = false := by
      revert hz; cases Spec.RsaKeyGen.obviouslyComposite (64 * w) c <;> decide
    refine WP.seq (WP.mono (prepS h₂ hoc) fun t₃ h₃ => ?_)
    exact WP.seq (WP.mono (mrStage R h₃) fun t₄ h₄ => h₄.result_ok)

end VG.Proof.RsaKeyGen.PPC64LE.Cand
