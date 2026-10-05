import VerifiedGarbage.Proof.Rsa.X86_64.RpRest
import VerifiedGarbage.Proof.Rsa.X86_64.CvMain
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode

/-!
# `vg_rsa_recover_primes` on x86-64: `main`

From a valid modulus, `main` loads `n`, `e` and `d`, computes `-n⁻¹` and
`M = d e`, and either writes zeros (`d e - 1` odd or not positive) or runs
`rest` (`rpMain_ok`): `recoverPrimes`'s result, written.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)
open VG.Spec.Rsa (splitTwos recoverStep recoverPrimes recoverTries)

/-- The inputs as numbers. -/
abbrev RpIn.N (I : RpIn) : Nat := Spec.Rsa.os2ip I.nb
abbrev RpIn.E (I : RpIn) : Nat := Spec.Rsa.os2ip I.eb
abbrev RpIn.D (I : RpIn) : Nat := Spec.Rsa.os2ip I.db

/-- What `main` needs on entry. -/
structure RpPre (I : RpIn) (s : State) : Prop where
  scr : Scr s I.B I.Z
  rdi : s.gpr .rdi = I.B
  args : RpArgs s.mem I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD I.sv
  n : Src s I.B I.Z I.pN I.nb
  e : Src s I.B I.Z I.pE I.eb
  d : Src s I.B I.Z I.pD I.db
  L : RpLens I
  oP : OutOk s I.B I.Z I.pP I.k
  oQ : OutOk s I.B I.Z I.pQ I.k
  a : Apart I.pP I.k I.pQ I.k
  wr : s.wr = I.W
  rsp : s.gpr .rsp = I.sp

theorem rpMain_eq (mul : Nat → Nat → Nat → Prog isa) : main mul = seqs (([.block CrtValues.head] : List (Prog isa)) ++
    ((loadA aN Impl.Bignum.X86_64.Public.sN Impl.Bignum.X86_64.Public.sK ++
      (loadA aE Impl.Bignum.X86_64.Public.sE Impl.Bignum.X86_64.Public.sElen ++ loadA aD sD sDl)) ++
    (([.block minvBlk] : List (Prog isa)) ++ (prod ++
    (([.block skipBlk, wordLoop 0 orBody, .block skipTest] : List (Prog isa)) ++
      ([.ite .ne fail (rest mul)] : List (Prog isa))))))) := by
  simp only [main, List.append_assoc, List.cons_append, List.nil_append]

/-- `head`: the working space, the mask all ones, and `RpS` from the
memory on entry to `main`. -/
theorem rpHeadS_ok {I : RpIn} {s : State} (h : RpPre I s) :
    WP isa (.block CrtValues.head) s fun t => RpS I s.mem t := by
  have L := h.L
  have hZ := L.z
  refine WP.mono (cvHead_ok h.scr h.rdi L.k1 L.k2 hZ h.args.k) fun s₁ ⟨hw₁, _, f₁, k₁⟩ => ?_
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  have k1 := L.k1
  have hi₁ : InScr I.B I.Z s.mem s₁.mem := InScr.of_frm f₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega)
  exact ⟨hw₁, h.args.congr fun i hi => f₁.word_eq (fun r hr => by
      unfold rArg at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega) (by unfold rArg at hi; omega),
    h.n.congrK hi₁ k₁, h.e.congrK hi₁ k₁, h.d.congrK hi₁ k₁, hi₁, k₁.2.2.trans h.wr,
    (k₁.gpr (by decide)).trans h.rsp⟩

/-- The skip's frame, as arrays and slots. -/
theorem frm_skip {B : Addr} {w : Nat} {m m' : Mem} (h : Frm B [(slot w aM, 8), (8 * sC2, 8)] m m') :
    Frm B (rg w [aM] [sC2]) m m' := h.widen (by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega)
  · exact rg_cover_hdr _ (by decide))

/-- `main`, from a valid modulus: `recoverPrimes`'s factors written, or
zeros. -/
theorem rpMain_ok (M : Mont) {I : RpIn} {s : State} (h : RpPre I s)
    (hv : Spec.Rsa.modulusValid I.N I.k = true) :
    WP isa (main M.mm) s fun t => ∃ res : Option (Nat × Nat),
      (recoverPrimes I.N I.E I.D).1 = res ∧
      (List.range I.k).map (fun i => t.mem (I.pP + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (match res with | some v => v.1 | none => 0) I.k ∧
      (List.range I.k).map (fun i => t.mem (I.pQ + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (match res with | some v => v.2 | none => 0) I.k ∧
      t.gpr .rax = BitVec.ofNat 64 res.isSome.toNat ∧ (∀ i < 6, t.gpr (saved.getD i .rax) = I.sv i) ∧
      (∀ x, I.Z ≤ ofs I.B x → (∀ i < I.k, x ≠ I.pP + BitVec.ofNat 64 i) →
        (∀ i < I.k, x ≠ I.pQ + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      t.gpr .rsp = s.gpr .rsp := by
  have L := h.L
  have k1 := L.k1
  have k2 := L.k2
  have hel1 := L.el1
  have hel2 := L.el2
  have hdl2 := L.dl2
  have hn := h.scr.nowrap
  have hZ := L.z
  obtain ⟨hNo, hlo⟩ := valid_lo hv
  have hlo' : 2 ^ (64 * (wk I.k - 1)) ≤ I.N := by
    refine Nat.le_trans ?_ hlo
    rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by unfold wk; omega)
  have hEl : I.E < 2 ^ (64 * ((I.el + 7) / 8)) := by
    have := os2ip_lt I.eb; rw [L.ebl] at this; exact Nat.lt_of_lt_of_le this (pow256_le_wk I.el)
  have hDl : I.D < 2 ^ (64 * wk I.k) := by
    have := os2ip_lt I.db; rw [L.dbl] at this
    exact Nat.lt_of_lt_of_le this (by rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by unfold wk; omega))
  rw [rpMain_eq]
  -- The head.
  refine wp_seqs_append (by simp) (by simp [loadA]) (WP.mono (rpHeadS_ok h) fun s₁ S₁ => ?_)
  have hZ16 : slot (wk I.k) 16 ≤ 2 ^ 64 := by have := S₁.ws.scr.nowrap; have := S₁.ws.hZ; omega
  -- The loads.
  refine wp_seqs_append (by simp [loadA]) (by simp) (WP.mono (rpLoads_ok S₁ L)
    fun s₂ ⟨S₂, _, vN, vE, vD, _⟩ => ?_)
  -- `-n⁻¹`.
  refine wp_seqs_append (by simp) (by simp [prod]) (WP.mono (minvBlk_ok S₂.ws (by
    rw [show (word s₂.mem I.B (slot (wk I.k) aN)).toNat % 2 = wv s₂.mem I.B (slot (wk I.k) aN) (wk I.k) % 2 by
      rw [wv_low (by have := S₂.ws.w1; omega)]; omega, vN]; exact hNo)) fun s₃ ⟨hi₃, f₃, k₃⟩ => ?_)
  have S₃ := S₂.step f₃ (by simp) (by decide) k₃ (by decide)
  -- `M = d e`.
  have vE₃ : wv s₃.mem I.B (slot (wk I.k) aE) (wk I.k) = I.E := by
    rw [f₃.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega), vE]
  have vD₃ : wv s₃.mem I.B (slot (wk I.k) aD) (wk I.k) = I.D := by
    rw [f₃.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega), vD]
  refine wp_seqs_append (by simp [prod]) (by simp) (WP.mono (prod_ok S₃.ws S₃.args.el hel1
    (by unfold wk; omega) (by rw [vE₃]; exact hEl)) fun s₄ ⟨vM₄, o₄, k₄⟩ => ?_)
  rw [vD₃, vE₃] at vM₄
  have sM := S₃.ws.sl (j := aM + 1) (by decide)
  have f₄ : Frm I.B (rg (wk I.k) [aM, aM + 1] []) s₃.mem s₄.mem :=
    Frm.rg_of_out2 o₄ (Nat.le_refl _) _ _ (by decide) (by decide)
  have S₄ := S₃.step f₄ (by decide) (by simp) k₄ (by decide)
  have hDE : I.D * I.E < 2 ^ (64 * (wk I.k + (I.el + 7) / 8)) := by
    rw [Nat.mul_add, Nat.pow_add]; exact Nat.mul_lt_mul'' hDl hEl
  -- Whether `d e - 1` is even and positive.
  refine wp_seqs_append (by simp) (by simp) (WP.mono (skip_ok S₄.ws S₄.args.el hel1 (by unfold wk; omega)
    (by rw [vM₄]; exact hDE)) fun s₅ ⟨hz₅, vM₅, f₅', _, k₅⟩ => ?_)
  rw [vM₄] at hz₅ vM₅
  have f₅ := frm_skip f₅'
  have S₅ := S₄.step f₅ (by decide) (by decide) k₅ (by decide)
  have hspec : (I.D * I.E < 2 ∨ (I.D * I.E - 1) % 2 = 1) ↔ ¬(I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E) := by omega
  simp only [seqs]
  refine WP.ite (!decide (I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E)) (by simp [eval, hz₅]) (fun hb => ?_) (fun hb => ?_)
  · -- Zeros.
    have hb' : ¬(I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E) := by simp at hb; omega
    have hnone := VG.Proof.Rsa.recoverPrimes_none (n := I.N) (hspec.mpr hb')
    refine WP.mono (rpFail_ok S₅.ws.scr S₅.ws.rdi (by omega) S₅.args (by omega) (by omega)
      ⟨fun i hi => by rw [S₅.wr, ← h.wr]; exact h.oP.wr i hi, h.oP.sep⟩
      ⟨fun i hi => by rw [S₅.wr, ← h.wr]; exact h.oQ.wr i hi, h.oQ.sep⟩ h.a)
      fun t ⟨z1, z2, hax, hsv, hfr, hsp⟩ => ⟨none, by rw [hnone], ?_, ?_, by rw [hax]; rfl, hsv,
        fun x hx n1 n2 => by rw [hfr x n1 n2]; exact S₅.inScr x hx, hsp.trans (S₅.rsp.trans h.rsp.symm)⟩
    · rw [List.map_congr_left fun i hi => z1 i (List.mem_range.mp hi)]; rw [i2osp_zero']; simp
    · rw [List.map_congr_left fun i hi => z2 i (List.mem_range.mp hi)]; rw [i2osp_zero']; simp
  · -- `rest`.
    have hb' : I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E := by simpa using hb
    have hgo := VG.Proof.Rsa.recoverPrimes_go (n := I.N) (fun h' => (hspec.mp h') hb')
    have vN₅ : wv s₅.mem I.B (slot (wk I.k) aN) (wk I.k) = I.N := by
      rw [f₅.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega),
        f₄.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega),
        f₃.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega), vN]
    have hi₅ : ((word s₅.mem I.B (slot (wk I.k) aN)).toNat * (word s₅.mem I.B (8 * sMinv)).toNat + 1) %
        2 ^ 64 = 0 := by
      rw [f₅.rg_word0 hZ16 (by decide) (by decide) (by decide), f₅.rg_word (by decide) (by decide),
        f₄.rg_word0 hZ16 (by decide) (by decide) (by decide), f₄.rg_word (by decide) (by decide)]; exact hi₃
    refine WP.mono (rpRest_ok M (m := I.D * I.E - 1) (N := I.N) ⟨S₅, L, hNo, hlo', vN₅, hi₅,
      by rw [vM₅]; omega, by omega, by omega, by omega,
      ⟨fun i hi => by rw [S₅.wr, ← h.wr]; exact h.oP.wr i hi, h.oP.sep⟩,
      ⟨fun i hi => by rw [S₅.wr, ← h.wr]; exact h.oQ.wr i hi, h.oQ.sep⟩, h.a⟩)
      fun t ⟨res, cnt, hres, bP, bQ, hax, hsv, hfr, hsp⟩ => ?_
    refine ⟨res.map (pqOf I.N), by rw [hgo, hres], ?_, ?_, by rw [hax]; cases res <;> rfl, hsv, hfr,
      hsp.trans h.rsp.symm⟩
    · rw [bP]; cases res <;> rfl
    · rw [bQ]; cases res <;> rfl

end VG.Proof.Rsa.X86_64
