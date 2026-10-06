import VerifiedGarbage.Proof.Rsa.X86_64.RpOut

/-!
# `vg_rsa_recover_primes` on x86-64: `rest`

From `M = m = d e - 1`, even and positive, and `-n⁻¹` in the header: the
halvings, Montgomery form, the candidates and the factors (`rpRest_ok`):
`recoverPrimes.go`'s result and the factors written masked by it.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)
open VG.Spec.Rsa (splitTwos recoverStep recoverPrimes recoverTries)

/-- The halvings' frame, as arrays and slots. -/
theorem frm_halving {B : Addr} {w : Nat} {m m' : Mem}
    (h : Frm B [(slot w aM, 16 * (w + 2)), (slot w aH, 16 * (w + 2)), (8 * sT, 8)] m m') :
    Frm B (rg w [aM, aM + 1, aH, aH + 1] [sT]) m m' := fun x hx => h x fun r hr => by
  have eM := slot_add w aM 1
  have eH := slot_add w aH 1
  have a := hx _ (rg_mem_arr (w := w) (j := aM) [sT] (by decide))
  have b := hx _ (rg_mem_arr (w := w) (j := aM + 1) [sT] (by decide))
  have c := hx _ (rg_mem_arr (w := w) (j := aH) [sT] (by decide))
  have d := hx _ (rg_mem_arr (w := w) (j := aH + 1) [sT] (by decide))
  have e := hx _ (rg_mem_hdr (w := w) [aM, aM + 1, aH, aH + 1] (show sT ∈ [sT] by decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  dsimp only at a b c d e
  rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega

/-- What `rest` needs. -/
structure RestPre (I : RpIn) (m₀ : Mem) (N m : Nat) (s : State) : Prop where
  S : RpS I m₀ s
  L : RpLens I
  odd : N % 2 = 1
  lo : 2 ^ (64 * (wk I.k - 1)) ≤ N
  n : wv s.mem I.B (slot (wk I.k) aN) (wk I.k) = N
  inv : ((word s.mem I.B (slot (wk I.k) aN)).toNat * (word s.mem I.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0
  M : wv s.mem I.B (slot (wk I.k) aM) (2 * (wk I.k + 2)) = m
  m0 : 0 < m
  even : m % 2 = 0
  mlt : m < 2 ^ (64 * (wk I.k + (I.el + 7) / 8))
  oP : OutOk s I.B I.Z I.pP I.k
  oQ : OutOk s I.B I.Z I.pQ I.k
  a : Apart I.pP I.k I.pQ I.k

theorem rest_eq (mul : Nat → Nat → Nat → Prog isa) : rest mul = seqs ([halving] ++ (mont mul ++ ([candLoop mul] ++
    (([.block [.mov .rax (.mem (hdr sC3)), .store (hdr sMask) .rax], mul aY aY aOne, zeroA fU,
      .block (ws ++ base aY .r8 ++ base aOne .r10 ++ base fU .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr)),
      wordLoop 0 subBody] : List (Prog isa)) ++
    ([zeroA fV, copyA fV aN, zeroA fX₁, .block (setOneA fX₁), zeroA fX₂, inverse fU fV fX₁ fX₂ aN fT,
      zeroA fQ, copyA fQ aN, divmod fQ fR fV fT] ++
    (([.block (ws ++ base fV .rbx ++ base fQ .r10 ++ ([.mov32 .rbp (.imm 0)] : List Instr)), wordLoop 0 ltBody,
      .block [.mov .r15 (.reg .rbp)], wordLoop 0 cswapBody] : List (Prog isa)) ++
    (storeA fV sP Impl.Bignum.X86_64.Public.sK Impl.Bignum.X86_64.Public.sMask ++
      (storeA fQ sQ Impl.Bignum.X86_64.Public.sK Impl.Bignum.X86_64.Public.sMask ++
        ([.block retMask] : List (Prog isa)))))))))) := by
  simp only [rest, fin, List.append_assoc, List.cons_append, List.nil_append]

/-- `rest`: `recoverPrimes.go`'s result, and `p` and `q` written masked by
it. -/
theorem rpRest_ok (M : Mont) {I : RpIn} {m₀ : Mem} {N m : Nat} {s : State} (h : RestPre I m₀ N m s) :
    WP isa (rest M.mm) s fun u => ∃ res : Option Nat, ∃ cnt : Nat,
      recoverPrimes.go N (splitTwos m).1 (splitTwos m).2 recoverTries = (res.map (pqOf N), cnt) ∧
      (List.range I.k).map (fun i => u.mem (I.pP + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (match res with | some y => (pqOf N y).1 | none => 0) I.k ∧
      (List.range I.k).map (fun i => u.mem (I.pQ + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (match res with | some y => (pqOf N y).2 | none => 0) I.k ∧
      u.gpr .rax = BitVec.ofNat 64 res.isSome.toNat ∧ (∀ i < 6, u.gpr (saved.getD i .rax) = I.sv i) ∧
      (∀ x, I.Z ≤ ofs I.B x → (∀ i < I.k, x ≠ I.pP + BitVec.ofNat 64 i) →
        (∀ i < I.k, x ≠ I.pQ + BitVec.ofNat 64 i) → u.mem x = m₀ x) ∧
      u.gpr .rsp = I.sp := by
  have L := h.L
  have hk1 := L.k1
  have hk2 := L.k2
  have hel1 := L.el1
  have hel2 := L.el2
  have S := h.S
  have hZ16 : slot (wk I.k) 16 ≤ 2 ^ 64 := by have := S.ws.scr.nowrap; have := S.ws.hZ; omega
  have hw1 := S.ws.w1
  have hN1 : 1 < N := by
    have : 2 ^ 64 ≤ 2 ^ (64 * (wk I.k - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    have := h.lo; omega
  rw [rest_eq]
  -- The halvings.
  refine wp_seqs_append (by simp) (by simp [mont]) (WP.mono (halving_ok S.ws S.args.el hel1
    (by unfold wk; omega) h.M h.m0 h.mlt) fun s₁ ⟨_, hr₁, ht₁, hf₁', k₁⟩ => ?_)
  have hf₁ := frm_halving hf₁'
  have S₁ := S.step hf₁ (by decide) (by decide) k₁ (by decide)
  have hn₁ : wv s₁.mem I.B (slot (wk I.k) aN) (wk I.k) = N := by
    rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact h.n
  have hi₁ : ((word s₁.mem I.B (slot (wk I.k) aN)).toNat * (word s₁.mem I.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 := by
    rw [hf₁.rg_word0 hZ16 (by decide) (by decide) (by decide), hf₁.rg_word (by decide) (by decide)]; exact h.inv
  -- Montgomery form.
  refine wp_seqs_append (by simp [mont]) (by simp) (WP.mono (mont_ok M S₁.ws hi₁ hn₁ h.odd h.lo)
    fun s₂ ⟨_, hr2lt, hr2, hone, ho, hng, hf₂, k₂⟩ => ?_)
  have S₂ := S₁.step hf₂ (by decide) (by decide) k₂ (by decide)
  have hspl := VG.Proof.Rsa.splitTwos_spec h.m0
  have hrlt : (splitTwos m).2 < 2 ^ (64 * (wk I.k + (I.el + 7) / 8)) := by
    have : (splitTwos m).2 ≤ m :=
      calc (splitTwos m).2 ≤ 2 ^ (splitTwos m).1 * (splitTwos m).2 := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
        _ = m := hspl.1.symm
    have := h.mlt; omega
  have ht1 : 1 ≤ (splitTwos m).1 := by
    rcases Nat.eq_zero_or_pos (splitTwos m).1 with h0 | h0
    · have := hspl.1; rw [h0, Nat.pow_zero, Nat.one_mul] at this; have := hspl.2; have := h.even; omega
    · exact h0
  have ht2 := VG.Proof.Rsa.splitTwos_lt h.m0 h.mlt
  have hc₂ : Cst s₂ I.B I.Z (wk I.k) (word s₂.mem I.B (8 * sMinv)) N I.el (splitTwos m).2 (splitTwos m).1 := by
    refine ⟨S₂.ws, rfl, ?_, ?_, hr2lt, hr2, hone, ho, hng, S₂.args.el, ?_, ?_, h.odd, h.lo, hel1,
      by unfold wk; omega, ht1, ht2⟩
    · rw [hf₂.rg_word0 hZ16 (by decide) (by decide) (by decide), hf₂.rg_word (by decide) (by decide)]; exact hi₁
    · rw [hf₂.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hn₁
    · rw [hf₂.rg_wv2 hZ16 (by decide) (by decide) (by decide) (by decide) (by unfold wk; omega)]
      rw [wv_low_of_lt (v := wk I.k + (I.el + 7) / 8) (w := 2 * (wk I.k + 2)) (by unfold wk; omega)
        (by rw [hr₁]; exact hrlt), hr₁]
    · rw [hf₂.rg_word (by decide) (by decide)]; exact ht₁
  -- The candidates.
  refine wp_seqs_append (by simp) (by simp) (WP.mono (candLoop_ok M hc₂)
    fun s₃ ⟨res, cnt, hgo, _, hc3, hy, hf₃, k₃⟩ => ?_)
  have S₃ := S₂.step hf₃ (by decide) (by decide) k₃ (by decide)
  have hc₃ := hc₂.congr hf₃ (by decide) cand_hs k₃ (by decide)
  -- `u = y - 1`.
  refine wp_seqs_append (by simp) (by simp) (WP.mono (finA_ok M hc₃ hc3 (res := res) fun y hres => by
    obtain ⟨a, b, c⟩ := hy y hres
    refine ⟨a, b, ?_⟩
    rcases Nat.eq_zero_or_pos y with h0 | h0
    · rw [h0, Nat.zero_mul, Nat.zero_mod] at c; cases c
    · exact h0) fun s₄ ⟨hf₄, k₄, hm₄, hU0, hU⟩ => ?_)
  have S₄ := S₃.step hf₄ (by decide) (by decide) k₄ (by decide)
  have hn₄ : wv s₄.mem I.B (slot (wk I.k) aN) (wk I.k) = N := by
    rw [hf₄.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hc₃.hn
  -- `p = gcd(u, n)`, `q = n / p`.
  refine wp_seqs_append (by simp) (by simp) (WP.mono (finB_ok S₄.ws hn₄ h.odd hN1 hU0)
    fun s₅ ⟨hf₅, k₅, _, hv₅, hq₅, _⟩ => ?_)
  have S₅ := S₄.step hf₅ (by decide) (by decide) k₅ (by decide)
  -- The larger first.
  refine wp_seqs_append (by simp) (by simp [storeA]) (WP.mono (finC_ok S₅.ws)
    fun s₆ ⟨hf₆, k₆, _, hv₆, hq₆⟩ => ?_)
  have S₆ := S₅.step hf₆ (by decide) (by simp) k₆ (by decide)
  have hm₆ : word s₆.mem I.B (8 * sMask) = mask res.isSome := by
    rw [hf₆.rg_word (by decide) (by simp), hf₅.rg_word (by decide) (by decide)]; exact hm₄
  -- The stores.
  refine WP.mono (rpStores_ok S₆.ws S₆.args hm₆ (by omega) (by unfold wk; omega)
    ⟨fun i hi => by rw [S₆.wr, ← S.wr]; exact h.oP.wr i hi, h.oP.sep⟩
    ⟨fun i hi => by rw [S₆.wr, ← S.wr]; exact h.oQ.wr i hi, h.oQ.sep⟩ h.a)
    fun u ⟨bP, bQ, hax, hsv, hfr, k₇⟩ => ?_
  have hval : ∀ y, res = some y →
      wv s₆.mem I.B (slot (wk I.k) fV) (wk I.k) = (pqOf N y).1 ∧
      wv s₆.mem I.B (slot (wk I.k) fQ) (wk I.k) = (pqOf N y).2 := fun y hres => by
    rw [hv₆, hq₆, hv₅, hq₅, hU y hres]
    exact ⟨rfl, rfl⟩
  refine ⟨res, cnt, hgo, ?_, ?_, hax, hsv, fun x hx n1 n2 => by rw [hfr x n1 n2]; exact S₆.inScr x hx,
    (k₇.gpr (by decide)).trans S₆.rsp⟩
  · rw [bP]
    cases hres : res with
    | none => rfl
    | some y => simp only [Option.isSome_some, ite_true]; exact congrArg (Spec.Rsa.i2osp · I.k) (hval y hres).1
  · rw [bQ]
    cases hres : res with
    | none => rfl
    | some y => simp only [Option.isSome_some, ite_true]; exact congrArg (Spec.Rsa.i2osp · I.k) (hval y hres).2

end VG.Proof.Rsa.X86_64
