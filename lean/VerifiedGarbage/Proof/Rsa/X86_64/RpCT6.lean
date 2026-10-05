import VerifiedGarbage.Proof.Rsa.X86_64.RpCT5

/-!
# `vg_rsa_recover_primes` on x86-64: constant time, the candidates

A candidate leaks the same in runs whose working spaces agree
(`candBody_ct`); the candidates tried are the public number of tries
(`candLoop_ct`): the loop stops after candidate `j` iff `j + 1` is that
number, which `recoverPrimes.go` fixes (`go_ge`, `go_le`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)
open VG.Spec.Rsa (splitTwos recoverStep recoverPrimes recoverTries)

/-! ## The number of tries -/

theorem go_ge (n t r : Nat) : ∀ k, k ≤ recoverTries → recoverTries - k ≤ (recoverPrimes.go n t r k).2
  | 0, _ => by rw [recoverPrimes.go]; exact Nat.le_refl _
  | k + 1, hk => by
    rw [recoverPrimes.go]
    split
    · show recoverTries - (k + 1) ≤ recoverTries - k
      omega
    · have := go_ge n t r k (by omega)
      omega

theorem go_le (n t r : Nat) : ∀ k, k ≤ recoverTries → (recoverPrimes.go n t r k).2 ≤ recoverTries
  | 0, _ => by rw [recoverPrimes.go]
  | k + 1, hk => by
    rw [recoverPrimes.go]
    split
    · show recoverTries - k ≤ recoverTries
      omega
    · exact go_le n t r k (by omega)

/-- After candidate `j` fails, at least `j + 2` are tried. -/
theorem go_ge1 (n t r : Nat) {k : Nat} (hk : k < recoverTries) :
    recoverTries - k ≤ (recoverPrimes.go n t r (k + 1)).2 := by
  rw [recoverPrimes.go]
  split
  · exact Nat.le_refl _
  · exact go_ge n t r k (by omega)

/-- The loop's condition after candidate `j`, from the tries. -/
theorem cand_cond (n t r : Nat) {j : Nat} (hj : j < (recoverPrimes.go n t r recoverTries).2)
    (hgo : recoverPrimes.go n t r recoverTries = recoverPrimes.go n t r (recoverTries - j)) :
    (!(!(decide (j + 1 < 100) && !(recoverStep n t r (j + 2)).isSome))) =
      decide (j + 1 < (recoverPrimes.go n t r recoverTries).2) := by
  have hle := go_le n t r recoverTries (Nat.le_refl _)
  have hj100 : j < recoverTries := by omega
  rw [hgo, VG.Proof.Rsa.go_eq n t r hj100]
  cases hs : recoverStep n t r (j + 2) with
  | some y => simp
  | none =>
    simp only [Option.isSome_none, Bool.not_false, Bool.and_true, Bool.not_not]
    by_cases h1 : j + 1 < 100
    · obtain ⟨k, hk⟩ : ∃ k, recoverTries - (j + 1) = k + 1 := ⟨recoverTries - (j + 1) - 1, by unfold recoverTries; omega⟩
      have := go_ge1 n t r (k := k) (by unfold recoverTries at *; omega)
      rw [hk]
      simp only [h1, decide_true]
      exact (decide_eq_true (by unfold recoverTries at *; omega)).symm
    · have e : recoverTries - (j + 1) = 0 := by unfold recoverTries; omega
      rw [e, recoverPrimes.go]
      simp only [h1, decide_false]
      exact (decide_eq_false (by unfold recoverTries; omega)).symm

namespace Rp

/-! ## A candidate -/

/-- At a candidate's start: the constants, and the candidate `c < 100`. -/
def CA (p : RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t c : Nat), Cst s p.B p.Z (wk p.k) minv N p.el r t ∧
    word s.mem p.B (8 * sCand) = BitVec.ofNat 64 c ∧ c < 100

/-- The constants. -/
def CK (p : RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t : Nat), Cst s p.B p.Z (wk p.k) minv N p.el r t

theorem CK.ws {p : RpP} {s : State} (h : CK p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨_, _, _, _, hc⟩ := h
  exact hc.ws

/-- After `gBlk`. -/
def CG (p : RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t : Nat), Cst s p.B p.Z (wk p.k) minv N p.el r t ∧
    s.gpr .r12 = BitVec.ofNat 64 (wk p.k) ∧ s.gpr .rcx = BitVec.ofNat 64 0

/-- After `g R mod n` in `Xm` (`hg`), then copied to `G`. -/
def CX (j : Nat) (p : RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t g : Nat), Cst s p.B p.Z (wk p.k) minv N p.el r t ∧
    wv s.mem p.B (slot (wk p.k) j) (wk p.k) < N ∧
    wv s.mem p.B (slot (wk p.k) j) (wk p.k) % N = g * 2 ^ (64 * wk p.k) % N

/-- `setWord`'s registers after its load. -/
def swXVal (p : RpP) : Reg → BitVec 64
  | .r8 => off p.B (slot (wk p.k) aX)
  | .r12 => BitVec.ofNat 64 (wk p.k)
  | .rcx => BitVec.ofNat 64 0
  | _ => 0

theorem setX_ct : RelCT isa (Two CG) (setWord aX .rcx) (Two CK) := by
  rw [setWord_eq]
  refine pin_ct [.rdi, .r12, .rcx] [.r8, .r12, .rcx] swXVal (fun _ _ _ h₁ h₂ r hr => ?_) (by taint_decide)
    (fun p s h => ?_) (by taint_decide) fun p s h => ?_
  · obtain ⟨_, _, _, _, hc₁, a₁, b₁⟩ := h₁
    obtain ⟨_, _, _, _, hc₂, a₂, b₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hc₁.ws.rdi, hc₂.ws.rdi]
    · rw [a₁, a₂]
    · rw [b₁, b₂]
  · obtain ⟨_, _, _, _, hc, h12, hcx⟩ := h
    have hw := hc.ws
    have := hw.h256
    have hl : InRegions (s.rd ++ s.wr) (off p.B (8 * sArr aX)) 8 :=
      hw.scr.ld (by have := hw.hZ; have := hdr_lt_slot (wk p.k) 16 (show sArr aX < 32 by decide); omega)
    refine WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = off p.B (slot (wk p.k) aX)) (by
      xrun [State.ea, hdr, hw.rdi, hdrOff, hl, hw.harr aX (by decide)]) rfl) fun t ⟨h8, k⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h8
    · exact (k.gpr (by decide)).trans h12
    · exact (k.gpr (by decide)).trans hcx
  · rw [← setWord_eq]
    obtain ⟨minv, N, r, t, hc, h12, hcx⟩ := h
    have hw1 := hc.ws.w1
    have hw2 := hc.ws.w2
    have hg := hc.good
    refine WP.mono (setWord_ok hc.ws.scr hc.ws.rdi hg.1.hdr hg.2 h12 (by omega) (by omega) (o := aX) (by decide)
      (ri := .rcx) (by decide) (i := 0) (by omega) hcx) fun u ⟨_, o, k⟩ => ?_
    exact ⟨minv, N, r, t, hc.congr (Frm.rg_of_out o (Nat.le_refl _) [aX] [] (by decide)) (by decide) (by simp) k
      (by decide)⟩

/-- `g`, `g R mod n`, its copy and `Y = R mod n`, and the exponentiation. -/
theorem candA_ct (M : Mont) : RelCT isa (Two CA)
    (seqs [.block gBlk, setWord aX .rcx, M.mm aXm aX aR2, copyA aG aXm, copyA aY aO, expLoop M.mm])
    fun _ _ => True := by
  have hK : ∀ p s, CK p s → Ws s p.B p.Z (wk p.k) := fun _ _ h => h.ws
  have hX : ∀ j p s, CX j p s → Ws s p.B p.Z (wk p.k) := fun _ _ _ ⟨_, _, _, _, _, hc, _⟩ => hc.ws
  simp only [seqs]
  refine RelCT.seq (R := Two CG) (blk_gct RpP.B RpP.Z (fun p => wk p.k)
    (fun _ _ ⟨_, _, _, _, _, hc, _⟩ => hc.ws) (by taint_decide) fun p s h => ?_) ?_
  · obtain ⟨minv, N, r, t, c, hc, hcand, -⟩ := h
    exact WP.mono (gBlk_ok hc.ws hcand) fun u ⟨_, hcx, h12, m, k⟩ =>
      ⟨minv, N, r, t, hc.congr (js := []) (hs := []) (by rw [m]; exact Frm.refl _ _ _) (by simp) (by simp) k
        (by decide), h12, hcx⟩
  refine RelCT.seq setX_ct (RelCT.seq (R := Two (CX aXm)) (mm_gct RpP.B RpP.Z (fun p => wk p.k) hK M
    (o := aXm) (a := aX) (b := aR2) (by unfold MmUse; decide) fun p s h => ?_) ?_)
  · obtain ⟨minv, N, r, t, hc⟩ := h
    have hg := hc.good
    have hw2 := hc.ws.w2
    refine WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 (by omega) (o := aXm) (a := aX) (b := aR2) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.hinv
      (by rw [hc.hn]; exact hc.hr2lt)) fun u ⟨_, hlt, hm, ha, k⟩ => ?_
    rw [hc.hn] at hlt hm
    exact ⟨minv, N, r, t, _, hc.congr (Frm.rg_of_arrays ha [aXm, aAcc, aTmp] [] (by decide)) (by decide) (by simp)
      k (by decide), hlt, g_mont hc.coprime hc.hr2 hm⟩
  refine RelCT.seq (R := Two (CX aG)) (copyA_gct RpP.B RpP.Z (fun p => wk p.k) (hX aXm) (by taint_decide)
    fun p s h => ?_) (RelCT.seq (R := Two EX) (copyA_gct RpP.B RpP.Z (fun p => wk p.k) (hX aG) (by taint_decide)
      fun p s h => ?_) ((expLoop_ct M).mono (fun _ _ h => h) fun _ _ _ => trivial))
  · obtain ⟨minv, N, r, t, g, hc, hlt, hm⟩ := h
    have hZ16 := hc.hZ16
    refine WP.mono (copyA_ok hc.ws (o := aG) (a := aXm) (by decide) (by decide) (by decide)) fun u ⟨hv, o, k⟩ => ?_
    have hf : Frm p.B (rg (wk p.k) [aG] []) s.mem u.mem := Frm.rg_of_out o (by omega) _ _ (by decide)
    exact ⟨minv, N, r, t, g, hc.congr hf (by decide) (by simp) k (by decide), by rw [hv]; exact hlt,
      by rw [hv]; exact hm⟩
  · obtain ⟨minv, N, r, t, g, hc, hlt, hm⟩ := h
    have hZ16 := hc.hZ16
    refine WP.mono (copyA_ok hc.ws (o := aY) (a := aO) (by decide) (by decide) (by decide)) fun u ⟨hv, o, k⟩ => ?_
    have hf : Frm p.B (rg (wk p.k) [aY] []) s.mem u.mem := Frm.rg_of_out o (by omega) _ _ (by decide)
    have hG : wv u.mem p.B (slot (wk p.k) aG) (wk p.k) = wv s.mem p.B (slot (wk p.k) aG) (wk p.k) :=
      hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)
    exact ⟨minv, N, r, t, g, hc.congr hf (by decide) (by simp) k (by decide), by rw [hG]; exact hlt,
      by rw [hG]; exact hm, by rw [hv, hc.ho]⟩

/-- The checks of `y = ±1` and the start of the squarings. -/
theorem candB_ct : RelCT isa (Two CK) (seqs (eqA aY aO ++ ([.block (eqStore sC2)] ++ (eqA aY aNg ++
    [.block chkBlk])))) fun _ _ => True := by
  have hK : ∀ p s, CK p s → Ws s p.B p.Z (wk p.k) := fun _ _ h => h.ws
  have same : ∀ p s u, CK p s → u.mem = s.mem → ∀ {regs : List Reg}, Keep regs s u → .rdi ∉ regs → CK p u :=
    fun p s u ⟨minv, N, r, t, hc⟩ m _ k hr => ⟨minv, N, r, t, hc.congr (js := []) (hs := [])
      (by rw [m]; exact Frm.refl _ _ _) (by simp) (by simp) k hr⟩
  refine RelCT.seqs_append (by simp [eqA]) (by simp) (RelCT.seq (R := Two CK) (eqA_gct RpP.B RpP.Z
    (fun p => wk p.k) hK (by taint_decide) fun p s h => WP.mono (eqA_ok h.ws (a := aY) (b := aO) (by decide)
      (by decide)) fun u ⟨_, m, k⟩ => same p s u h m k (by decide)) ?_)
  refine RelCT.seqs_append (by simp) (by simp [eqA]) (RelCT.seq (R := Two CK) ?_ ?_)
  · simp only [seqs]
    refine blk_gct RpP.B RpP.Z (fun p => wk p.k) hK (by taint_decide) fun p s h => ?_
    obtain ⟨minv, N, r, t, hc⟩ := h
    have h256 := hc.ws.h256
    exact WP.mono (eqStore_ok hc.ws (i := sC2) (by decide) (by decide)) fun u ⟨m, k⟩ =>
      ⟨minv, N, r, t, hc.congr (js := []) (Frm.rg_of_hdr (m ▸ writeW_outside _ _ _ (by simp only [sC2, sFn]; omega))
        [] [sC2] (List.mem_singleton_self _)) (by decide) (by decide) k (by decide)⟩
  refine RelCT.seqs_append (by simp [eqA]) (by simp) (RelCT.seq (R := Two CK) (eqA_gct RpP.B RpP.Z
    (fun p => wk p.k) hK (by taint_decide) fun p s h => WP.mono (eqA_ok h.ws (a := aY) (b := aNg) (by decide)
      (by decide)) fun u ⟨_, m, k⟩ => same p s u h m k (by decide)) ?_)
  simp only [seqs]
  exact two_taint [.rdi] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]) (by taint_decide)

/-- After the start of the squarings. -/
theorem candBody_ct (M : Mont) : RelCT isa (Two CA) (candBody M.mm) fun _ _ => True := by
  rw [show candBody M.mm = seqs ([.block gBlk, setWord aX .rcx, M.mm aXm aX aR2, copyA aG aXm, copyA aY aO,
      expLoop M.mm] ++ ((eqA aY aO ++ ([.block (eqStore sC2)] ++ (eqA aY aNg ++ [.block chkBlk]))) ++
        [.loop (sqBody M.mm) .ne, .block candNext])) by
    simp only [candBody, List.append_assoc, List.cons_append, List.nil_append]]
  refine RelCT.seqs_append (by simp) (by simp [eqA]) (RelCT.seq (R := Two fun p s => ∃ (minv : BitVec 64)
      (N r t y : Nat), Cst s p.B p.Z (wk p.k) minv N p.el r t ∧
        wv s.mem p.B (slot (wk p.k) aY) (wk p.k) = y * 2 ^ (64 * wk p.k) % N ∧ y < N)
    (two_post (candA_ct M) fun p s ⟨minv, N, r, t, c, hc, hcand, hc100⟩ => ?_) ?_)
  · have hN : 0 < N := by have := hc.n1; omega
    exact WP.mono (candA_ok M hc hcand hc100) fun u ⟨hf, k, hY⟩ =>
      ⟨minv, N, r, t, _, hc.congr hf (by decide) (by decide) k (by decide), hY,
        by rw [VG.Proof.Bignum.powMod_eq]; exact Nat.mod_lt _ hN⟩
  refine RelCT.seqs_append (by simp [eqA]) (by simp) (RelCT.seq (R := Two fun p s =>
      0 < 64 * (wk p.k + (p.el + 7) / 8) ∧ SQI p 0 s)
    (two_post (two_map id (fun _ _ ⟨minv, N, r, t, _, hc, _⟩ => ⟨minv, N, r, t, hc⟩) candB_ct)
      fun p s h => ?_) ?_)
  · obtain ⟨minv, N, r, t, y, hc, hY, hy⟩ := h
    have hZ16 := hc.hZ16
    have hw1 := hc.ws.w1
    refine WP.mono (candB_ok hc hY hy) fun u ⟨hf, k, hc2, hc3, hc1⟩ => ⟨by omega, ?_⟩
    have hc₂ := hc.congr hf (by decide) (by decide) k (by decide)
    refine ⟨u, minv, N, r, t, VG.Proof.Rsa.sqStart N y, hc₂, Frm.refl _ _ _, Keep.refl _ _, ?_, hy, hc1, hc2, hc3⟩
    rw [hf.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hY
  show RelCT isa _ (.seq (.loop (sqBody M.mm) .ne) (.block candNext)) _
  exact RelCT.seq (sqLoop_ct M) (two_taint [.rdi] (fun _ _ _ ⟨_, _, _, _, _, _, hc₁, hI₁⟩ ⟨_, _, _, _, _, _, hc₂, hI₂⟩
    r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [(hc₁.congr hI₁.frm (by decide) sq_hs hI₁.keep (by decide)).ws.rdi,
        (hc₂.congr hI₂.frm (by decide) sq_hs hI₂.keep (by decide)).ws.rdi]) (by taint_decide))

/-! ## The candidates -/

/-- The candidates' invariant: `j` tried from `s₀`, and the public count. -/
def CL (p : RpP) (j : Nat) (u : State) : Prop :=
  ∃ (s₀ : State) (minv : BitVec 64) (N r t : Nat), Cst s₀ p.B p.Z (wk p.k) minv N p.el r t ∧
    p.cnt = (recoverPrimes.go N t r recoverTries).2 ∧ CandI s₀ p.B (wk p.k) N t r j u

theorem candLoopL_ct (M : Mont) : RelCT isa (Two fun p s => 0 < p.cnt ∧ CL p 0 s) (.loop (candBody M.mm) .ne)
    (Two fun (_ : RpP) (_ : State) => True) :=
  two_loop RpP.cnt (two_map (fun q => q.1) (fun q s hq => by
      obtain ⟨hj, s₀, minv, N, r, t, hc, hcnt, hI⟩ := hq
      have := go_le N t r recoverTries (Nat.le_refl _)
      exact ⟨minv, N, r, t, q.2, hc.congr hI.frm (by decide) cand_hs hI.keep (by decide), hI.cand,
        by have : recoverTries = 100 := rfl; omega⟩) (candBody_ct M))
    fun p j s hj ⟨s₀, minv, N, r, t, hc, hcnt, hI⟩ => by
      have hle := go_le N t r recoverTries (Nat.le_refl _)
      have hj100 : j < 100 := by have : recoverTries = 100 := rfl; omega
      have hcu := hc.congr hI.frm (by decide) cand_hs hI.keep (by decide)
      refine WP.mono (candBody_ok M hcu hI.cand hj100) fun u' ⟨hz, hf, k, hcand, _, _⟩ => ⟨?_, fun hlt => ?_,
        fun _ => trivial⟩
      · rw [hcnt] at hj ⊢
        simp only [eval, hz, Option.map_some]
        exact congrArg some (cand_cond N t r hj hI.go)
      · refine ⟨s₀, minv, N, r, t, hc, hcnt, (hI.frm.rg_trans hf).rg_mono (by decide) (by decide),
          (hI.keep.trans k).mono (by decide), hcand, ?_⟩
        rw [hI.go, VG.Proof.Rsa.go_eq N t r hj100]
        rw [hcnt, hI.go, VG.Proof.Rsa.go_eq N t r hj100] at hlt
        cases hs : recoverStep N t r (j + 2) with
        | some y => rw [hs] at hlt; exact absurd hlt (by simp)
        | none => rfl

/-- The public count is `recoverPrimes.go`'s, once `d e` passes step 1. -/
theorem cnt_eq {I : RpIn} (hv : Spec.Rsa.modulusValid I.N I.k = true) (L : RpLens I) (hm0 : 0 < I.D * I.E - 1)
    (heven : (I.D * I.E - 1) % 2 = 0) :
    I.pub.cnt = (recoverPrimes.go I.N (splitTwos (I.D * I.E - 1)).1 (splitTwos (I.D * I.E - 1)).2
      recoverTries).2 := by
  have h1 : ¬(I.D * I.E < 2 ∨ (I.D * I.E - 1) % 2 = 1) := by omega
  show (Spec.Rsa.primesKey I.nb I.eb I.db).2 = _
  simp only [Spec.Rsa.primesKey, L.nbl, hv, ite_true]
  rw [← VG.Proof.Rsa.recoverPrimes_go h1]
  split <;> simp_all

/-- After the candidates: `recoverPrimes.go`'s result, and what the factors
need. -/
def GR3 (p : RpP) (s : State) : Prop :=
  ∃ (I : RpIn) (m₀ : Mem) (minv : BitVec 64) (res : Option Nat) (cnt : Nat), I.pub = p ∧ RpS I m₀ s ∧
    RpLens I ∧ RpOuts I ∧ Spec.Rsa.modulusValid I.N I.k = true ∧
    Cst s I.B I.Z (wk I.k) minv I.N I.el (splitTwos (I.D * I.E - 1)).2 (splitTwos (I.D * I.E - 1)).1 ∧
    recoverPrimes.go I.N (splitTwos (I.D * I.E - 1)).1 (splitTwos (I.D * I.E - 1)).2 recoverTries =
      (res.map (pqOf I.N), cnt) ∧ word s.mem I.B (8 * sC3) = mask res.isSome ∧
    (∀ y, res = some y → wv s.mem I.B (slot (wk I.k) aY) (wk I.k) = y * 2 ^ (64 * wk I.k) % I.N ∧ y < I.N ∧
      y * y % I.N = 1)

theorem candLoop_ct (M : Mont) : RelCT isa (Two GR2) (candLoop M.mm) (Two GR3) := by
  refine two_post (RelCT.seq (blk_gct RpP.B RpP.Z (fun p => wk p.k)
    (fun _ _ ⟨_, _, e, S, _⟩ => e ▸ S.ws) (by taint_decide) fun p s h => ?_) ((candLoopL_ct M).mono (fun _ _ h => h) fun _ _ _ => trivial)) fun p s h => ?_
  · obtain ⟨I, m₀, rfl, S, L, O, hv, hc, hm0, heven⟩ := h
    dsimp only [RpIn.pub]
    have h256 := hc.ws.h256
    refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = s.mem.writeW (off I.B (8 * sCand))
        (BitVec.ofNat 64 0)) (by
      xrun [State.ea, hdr, hc.ws.rdi, hdrOff,
        hc.ws.scr.st (d := 8 * sCand) (by simp only [sCand, Impl.Bignum.X86_64.Public.sV, sFn]; omega)]
      rfl) rfl) fun u ⟨m₁, k₁⟩ => ⟨?_, s, _, I.N, _, _, hc, cnt_eq hv L hm0 heven, ?_, k₁.mono (by decide),
        by rw [m₁, word_writeW_self], rfl⟩
    · rw [show (Spec.Rsa.primesKey I.nb I.eb I.db).2 = I.pub.cnt from rfl, cnt_eq hv L hm0 heven]
      exact VG.Proof.Rsa.go_pos _ _ _ _ (Nat.le_refl _)
    · rw [m₁]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sCand, Impl.Bignum.X86_64.Public.sV, sFn]; omega))
        _ _ (by decide)
  · obtain ⟨I, m₀, rfl, S, L, O, hv, hc, hm0, heven⟩ := h
    exact WP.mono (candLoop_ok M hc) fun u ⟨res, cnt, hgo, _, hc3, hy, hf, k⟩ =>
      ⟨I, m₀, _, res, cnt, rfl, S.step hf (by decide) (by decide) k (by decide), L, O, hv,
        hc.congr hf (by decide) cand_hs k (by decide), hgo, hc3, hy⟩

end Rp

end VG.Proof.Rsa.X86_64
