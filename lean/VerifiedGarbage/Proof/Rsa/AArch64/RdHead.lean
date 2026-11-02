module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdOps
public import VerifiedGarbage.Proof.Rsa.AArch64.CvStore
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
import VerifiedGarbage.Proof.Rsa.AArch64.RpProd
import VerifiedGarbage.Proof.Rsa.AArch64.CvHead
import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `vg_rsa_recover_primes_det` on AArch64: the head, `d e` and `d e - 1`

`head_ok`: the header for the narrow width and the mask all ones (`G`);
`loads_ok` and `prodD_ok`: `n`, `e`, `d` and `d e`; `deMinus_ok`: `d e - 1`
(wide) and `RecoverDet.okDE` and'ed into the mask.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Rsa.RecoverDet

/-- A valid modulus is odd and at least `256^(k - 1)`. -/
theorem rvalid_lo {N k : Nat} (hv : Spec.Rsa.modulusValid N k = true) : N % 2 = 1 ∧ 256 ^ (k - 1) ≤ N := by
  rw [Spec.Rsa.modulusValid, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hv
  obtain ⟨⟨⟨h1, -⟩, -⟩, h4⟩ := hv
  exact ⟨by simpa using h1, of_decide_eq_true h4⟩

theorem rpow256_le (len : Nat) : 256 ^ len ≤ 2 ^ (64 * ((len + 7) / 8)) := by
  rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by omega)

/-- The inputs as numbers. -/
abbrev numN (I : RpIn) : Nat := Spec.Rsa.os2ip I.nb
abbrev numE (I : RpIn) : Nat := Spec.Rsa.os2ip I.eb
abbrev numD (I : RpIn) : Nat := Spec.Rsa.os2ip I.db

/-- What `main` needs on entry. -/
structure DPre (I : RpIn) (s : State) : Prop where
  scr : Scr s I.B I.Z
  x0 : s.gpr .x0 = I.B
  args : RpArgs s.mem I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD
  n : Src s I.B I.Z I.pN I.nb
  e : Src s I.B I.Z I.pE I.eb
  d : Src s I.B I.Z I.pD I.db
  L : RpLens I
  el8 : I.el ≤ 8
  oP : OutOk s I.B I.Z I.pP I.k
  oQ : OutOk s I.B I.Z I.pQ I.k
  a : Apart I.pP I.k I.pQ I.k
  wr : s.wr = I.W

/-- A difference over `N` bits, as `RecoverDet.wsub`. -/
theorem sub_wsub {N A Bv T : Nat} (hT : T < 2 ^ N)
    (h : T + Bv = A + 2 ^ N * (!decide (Bv ≤ A)).toNat) : T = wsub N A Bv := by
  unfold wsub
  by_cases c : Bv ≤ A
  · simp only [c, decide_true, Bool.not_true, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at h
    rw [show A + 2 ^ N - Bv = (A - Bv) + 2 ^ N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [c, decide_false, Bool.not_false, Bool.toNat_true, Nat.mul_one] at h
    rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- `oneA j`: `[j] := 1` over its `w + 2` words. -/
theorem oneA_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) {j : Nat} (hj : j < 16) :
    WP isa (seqs (oneA j)) s fun t => G I m₀ w c t ∧ wv t.mem I.B (slot w j) (w + 2) = 1 ∧
      Outside I.B (slot w j) (8 * (w + 2)) s.mem t.mem ∧ Keep [.x3, .x7, .x8, .x11, .x12, .x14, .x16] s t := by
  have hn := h.ws.scr.nowrap
  have sj := h.ws.sl hj
  simp only [oneA, seqs]
  refine WP.seq (WP.mono (zeroA_ok h.ws hj) fun s₁ ⟨z₁, o₁, _, _, _, k₁⟩ => ?_)
  have h₁ := h.out hj (Nat.le_refl _) o₁ k₁ (by decide)
  refine WP.mono (setOneA_ok h₁.ws hj) fun t ⟨hm, k₂⟩ => ?_
  have o₂ := writeW_outside s₁.mem I.B (1 : BitVec 64) (d := slot w j) (by omega)
  rw [← hm] at o₂
  refine ⟨h₁.out hj (by omega) o₂ k₂ (by decide), ?_, fun x hx => by rw [o₂ x (by omega), o₁ x hx],
    (k₁.trans k₂).mono (by decide)⟩
  have e₁ := wv_low (m := s₁.mem) (B := I.B) (e := slot w j) (w := w + 2) (by omega)
  rw [wv_low (by omega), o₂.wv (Or.inr (by omega)) (by omega), hm, word_writeW_self]
  rw [z₁] at e₁
  have : wv s₁.mem I.B (slot w j + 8) (w + 2 - 1) = 0 := by
    have := Nat.zero_le (word s₁.mem I.B (slot w j)).toNat
    rcases Nat.eq_zero_or_pos (wv s₁.mem I.B (slot w j + 8) (w + 2 - 1)) with e | e
    · exact e
    · exfalso; have : 2 ^ 64 * 1 ≤ 2 ^ 64 * wv s₁.mem I.B (slot w j + 8) (w + 2 - 1) := Nat.mul_le_mul_left _ e
      omega
  rw [this]; rfl

/-! ## The head and the loads -/

/-- `head ++ setNar`: the working space at the narrow width, the mask all
ones. -/
theorem head_ok {I : RpIn} {s : State} (h : DPre I s) :
    WP isa (.block (VG.Impl.Rsa.AArch64.Keys.head ++ setNar)) s fun t => G I s.mem (vk I.k) true t ∧
      Keep [.x3, .x4, .x7, .x12] s t := by
  have L := h.L
  rw [WP.block_append_iff]
  refine WP.mono (cvHead_ok h.scr h.x0 L.k1 L.k2 L.z h.args.k) fun s₁ ⟨hw₁, hm₁, f₁, k₁⟩ => ?_
  have k1 := L.k1
  have hz := L.z
  have hi₁ : InScr I.B I.Z s.mem s₁.mem := InScr.of_frm f₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [sW, sArr, sStride, Public.sMask, sFn] <;> omega)
  have g₁ : G I s.mem (wk I.k) true s₁ := ⟨hw₁, h.args.congr fun i hi => f₁.word_eq (fun r hr => by
      unfold rArg at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only [sW, sArr, sStride, Public.sMask, sFn] <;> omega)
      (by unfold rArg at hi; omega),
    h.n.congrK hi₁ k₁, h.e.congrK hi₁ k₁, h.d.congrK hi₁ k₁, hi₁, k₁.wr.trans h.wr, hm₁⟩
  exact WP.mono (g₁.setNar_ok L) fun t ⟨g, _, k₂⟩ => ⟨g, (k₁.trans k₂).mono (by decide)⟩

/-- After a piece that changes only arrays `j` and `j + 1`. -/
theorem G.out2 {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s t : State} (h : G I m₀ w c s) {j n : Nat}
    (hj : j + 1 < 16) (hn : n ≤ 16 * (w + 2)) (o : Outside I.B (slot w j) n s.mem t.mem) {regs : List Reg}
    (k : Keep regs s t) (hr : .x0 ∉ regs) : G I m₀ w c t :=
  h.step (Frm.of_outside o (List.mem_singleton_self _)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; unfold slot hdrBytes; dsimp only; omega) (fun r hr => by
    rw [List.mem_singleton.mp hr]; have := h.ws.sl hj; dsimp only; rw [slot_succ] at this; omega) k hr

open VG.Impl.Rsa.AArch64.Recover (sD sDl aE aD aM prod) in
/-- The head, the loads and `d e` (narrow arrays 10 and 11, wide array 5). -/
theorem prefix_ok {I : RpIn} {s : State} (h : DPre I s) :
    WP isa (seqs (([.block (VG.Impl.Rsa.AArch64.Keys.head ++ setNar)] : List (Prog isa)) ++ (loadA Public.aN Public.sN Public.sK ++
      (loadA aE Public.sE Public.sElen ++ (loadA aD sD sDl ++ prod))))) s fun t =>
      G I s.mem (vk I.k) true t ∧ wv t.mem I.B (slot (vk I.k) 0) (vk I.k) = numN I ∧
      wv t.mem I.B (slot (vk I.k) aM) (2 * (vk I.k + 2)) = numD I * numE I := by
  have L := h.L
  have k1 := L.k1
  have k2 := L.k2
  have hel1 := L.el1
  have hel8 := h.el8
  have hdl2 := L.dl2
  have hZ := L.z
  have hEl : numE I < 2 ^ (64 * ((I.el + 7) / 8)) := by
    have := os2ip_lt I.eb; rw [L.ebl] at this; exact Nat.lt_of_lt_of_le this (rpow256_le I.el)
  refine wp_seqs_append (by simp) (by simp [loadA]) (WP.mono (head_ok h) fun s₁ ⟨g₁, k₁⟩ => ?_)
  have hn := g₁.ws.scr.nowrap
  have hZ16 := g₁.ws.hZ
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (loadA_ok g₁.ws (j := Public.aN) (by decide)
    (by decide) (by decide) g₁.args.n g₁.args.k g₁.n L.nbl (by omega) (by simp only [vk]; omega))
    fun s₂ ⟨vN, o₂, _, _, k₂⟩ => ?_)
  have g₂ := g₁.out (by decide) (Nat.le_refl _) o₂ k₂ (by decide)
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (loadA_ok g₂.ws (j := aE) (by decide)
    (by decide) (by decide) g₂.args.e g₂.args.el g₂.e L.ebl hel1 (by simp only [vk]; omega))
    fun s₃ ⟨vE, o₃, _, _, k₃⟩ => ?_)
  have g₃ := g₂.out (by decide) (Nat.le_refl _) o₃ k₃ (by decide)
  refine wp_seqs_append (by simp [loadA]) (by simp [prod]) (WP.mono (loadA_ok g₃.ws (j := aD) (by decide)
    (by decide) (by decide) g₃.args.d g₃.args.dl g₃.d L.dbl L.dl1 (by simp only [vk]; omega))
    fun s₄ ⟨vD, o₄, _, _, k₄⟩ => ?_)
  have g₄ := g₃.out (by decide) (Nat.le_refl _) o₄ k₄ (by decide)
  have sl : ∀ j, slot (vk I.k) j = 256 + j * (8 * (vk I.k + 2)) := fun j => rfl
  have vE₄ : wv s₄.mem I.B (slot (vk I.k) aE) (vk I.k) = numE I := by
    rw [o₄.wv (by simp only [sl, aE, aD]; omega) (by simp only [sl, aE] at *; omega), vE]
  refine WP.mono (prod_ok g₄.ws g₄.args.el hel1 (by simp only [vk]; omega) (by rw [vE₄]; exact hEl))
    fun t ⟨vM, o₅, k₅⟩ => ⟨g₄.out2 (by decide) (by omega) o₅ k₅ (by decide), ?_, ?_⟩
  · rw [o₅.wv (by simp only [sl, aM]; omega) (by simp only [sl, aM] at *; omega),
      o₄.wv (by simp only [sl, aD]; omega) (by simp only [sl, aD] at *; omega),
      o₃.wv (by simp only [sl, aE]; omega) (by simp only [sl, aE] at *; omega)]; exact vN
  · rw [vM, vD, vE₄]

theorem okDE_eq (wb de : Nat) : okDE wb de = (decide (1 ≤ de) && decide (1 ≤ deX wb de)) := by
  unfold okDE
  by_cases a : 1 ≤ de <;> by_cases b : 1 ≤ deX wb de <;> simp [a, b] <;> omega

/-- The slots as numbers. -/
theorem slotN (w j : Nat) : slot w j = 256 + j * (8 * (w + 2)) := rfl

/-- `deMinus`: `X = d e - 1` (wide array 6) and `okDE` and'ed into the mask. -/
theorem deMinus_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I)
    {de : Nat} (hM : wv s.mem I.B (slot (vk I.k) 10) (2 * (vk I.k + 2)) = de) (hde : de < 2 ^ (64 * vk I.k)) :
    WP isa deMinus s fun t => G I m₀ (Wk I.k) (c && okDE (64 * Wk I.k) de) t ∧
      wv t.mem I.B (slot (Wk I.k) wX) (Wk I.k) = deX (64 * Wk I.k) de ∧
      Frm I.B (hdrW ++ [(8 * Public.sMask, 8), (slot (Wk I.k) wOne, 8 * (Wk I.k + 2)), (slot (Wk I.k) wX, 8 * Wk I.k),
        (slot (Wk I.k) wT, 8 * Wk I.k)]) s.mem t.mem := by
  have k1 := L.k1
  have k2 := L.k2
  have hZ := L.z
  have hpw : 2 ^ (64 * vk I.k) ≤ 2 ^ (64 * Wk I.k) := Nat.pow_le_pow_right (by decide) (by simp only [Wk]; omega)
  unfold deMinus
  rw [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [oneA]) (WP.mono (h.setWid_ok L) fun s₁ ⟨g₁, f₁, k₁⟩ => ?_)
  have hn := g₁.ws.scr.nowrap
  have hZ16 := g₁.ws.hZ
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have e10 : slot (vk I.k) 10 = slot (Wk I.k) wM := by simp only [slotN, Wk, wM]; omega
  have hM₀ : wv s₁.mem I.B (slot (vk I.k) 10) (2 * (vk I.k + 2)) = de := by
    rw [f₁.wv_eq (fun r hr => by
        simp only [hdrW, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp only [slotN, sW, sArr, sStride, sFn] <;> omega)
        (by simp only [slotN] at hZ16 ⊢; omega), hM]
  have hM₁ : wv s₁.mem I.B (slot (Wk I.k) wM) (Wk I.k) = de := by
    rw [← e10, wv_low_of_lt (w := 2 * (vk I.k + 2)) (by simp only [Wk]; omega) (by omega), hM₀]
  refine wp_seqs_append (by simp [oneA]) (by simp) (WP.mono (oneA_ok g₁ (j := wOne) (by decide)) fun s₂ ⟨g₂, v₂, o₂, k₂⟩ => ?_)
  have hOne : wv s₂.mem I.B (slot (Wk I.k) wOne) (Wk I.k) = 1 := by
    rw [wv_low_of_lt (w := Wk I.k + 2) (by omega) (by rw [v₂]; exact Nat.one_lt_two_pow (by simp only [Wk]; omega)), v₂]
  have hM₂ : wv s₂.mem I.B (slot (Wk I.k) wM) (Wk I.k) = de := by
    rw [o₂.wv (rd_sep (by decide) (by omega) (Nat.le_refl _)) (g₁.bnd (by decide) (by omega)), hM₁]
  refine WP.seq (WP.mono (subA_ok g₂.ws (o := wX) (a := wM) (b := wOne) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₃ ⟨v₃, h15₃, _, o₃, k₃⟩ => ?_)
  have g₃ := g₂.out (by decide) (by omega) o₃ k₃ (by decide)
  rw [hM₂, hOne] at v₃ h15₃
  have hX : wv s₃.mem I.B (slot (Wk I.k) wX) (Wk I.k) = deX (64 * Wk I.k) de :=
    sub_wsub (wv_lt _ _ _ _) v₃
  refine WP.seq (WP.mono (andMask_ok g₃ h15₃) fun s₄ ⟨g₄, o₄, k₄⟩ => ?_)
  have hX₄ : wv s₄.mem I.B (slot (Wk I.k) wX) (Wk I.k) = deX (64 * Wk I.k) de := by
    rw [o₄.wv (hd_sep (by decide)) (g₁.bnd (by decide) (by omega)), hX]
  have hOne₄ : wv s₄.mem I.B (slot (Wk I.k) wOne) (Wk I.k) = 1 := by
    rw [o₄.wv (hd_sep (by decide)) (g₁.bnd (by decide) (by omega)),
      o₃.wv (rd_sep (by decide) (by omega) (by omega)) (g₁.bnd (by decide) (by omega)), hOne]
  refine WP.seq (WP.mono (subA_ok g₄.ws (o := wT) (a := wX) (b := wOne) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₅ ⟨_, h15₅, _, o₅, k₅⟩ => ?_)
  have g₅ := g₄.out (by decide) (by omega) o₅ k₅ (by decide)
  rw [hX₄, hOne₄] at h15₅
  refine WP.mono (andMask_ok g₅ h15₅) fun t ⟨g₆, o₆, _⟩ => ⟨?_, ?_, ?_⟩
  · rw [okDE_eq, ← Bool.and_assoc]; exact g₆
  · rw [o₆.wv (hd_sep (by decide)) (g₁.bnd (by decide) (by omega)),
      o₅.wv (rd_sep (by decide) (by omega) (by omega)) (g₁.bnd (by decide) (by omega)), hX₄]
  · intro x hx
    have a := hx (slot (Wk I.k) wOne, 8 * (Wk I.k + 2)) (by simp)
    have b := hx (slot (Wk I.k) wX, 8 * Wk I.k) (by simp)
    have d := hx (slot (Wk I.k) wT, 8 * Wk I.k) (by simp)
    have e := hx (8 * Public.sMask, 8) (by simp)
    have f := fun r (hr : r ∈ hdrW) => hx r (by simp only [List.mem_append]; exact .inl hr)
    dsimp only at a b d e
    rw [o₆ x e, o₅ x d, o₄ x e, o₃ x b, o₂ x a, f₁ x f]

/-! ## Narrow and wide ranges -/

theorem slot_mul (v j : Nat) : slot v j = 256 + j * (8 * (v + 2)) := rfl

/-- Narrow array `j`'s first `k` words are apart from wide array `i`'s first `n` bytes. -/
theorem nw_sep {v i j k n : Nat} (h1 : j ≠ 2 * i) (h2 : j ≠ 2 * i + 1) (hk : k ≤ v + 2) (hn : n ≤ 16 * (v + 2)) :
    slot v j + 8 * k ≤ slot (2 * v + 2) i ∨ slot (2 * v + 2) i + n ≤ slot v j := by
  rw [slot_wide]
  rcases Nat.lt_or_ge j (2 * i) with c | c
  · left; have := slot_lt (w := v) c; omega
  · right
    have : slot v (2 * i + 2) ≤ slot v j := slot_mono (by omega)
    rw [show 2 * i + 2 = 2 * i + 1 + 1 by omega, slot_succ, slot_succ] at this; omega

/-- Wide array `i`'s first `k` words are apart from narrow array `j`'s first `n` bytes. -/
theorem wn_sep {v i j k n : Nat} (h1 : j ≠ 2 * i) (h2 : j ≠ 2 * i + 1) (hk : k ≤ 2 * v + 4) (hn : n ≤ 8 * (v + 2)) :
    slot (2 * v + 2) i + 8 * k ≤ slot v j ∨ slot v j + n ≤ slot (2 * v + 2) i := by
  rw [slot_wide]
  rcases Nat.lt_or_ge j (2 * i) with c | c
  · right; have := slot_lt (w := v) c; omega
  · left
    have : slot v (2 * i + 2) ≤ slot v j := slot_mono (by omega)
    rw [show 2 * i + 2 = 2 * i + 1 + 1 by omega, slot_succ, slot_succ] at this; omega

/-- The narrow arrays are in the address space. -/
theorem G.bndv {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I)
    {j k : Nat} (hj : j < 32) (hk : k ≤ vk I.k + 2) : slot (vk I.k) j + 8 * k ≤ 2 ^ 64 := by
  have := h.ws.scr.nowrap; have := L.z; have := L.k1
  have : slot (vk I.k) j + 8 * (vk I.k + 2) ≤ slot (vk I.k) 32 := slot_lt hj
  simp only [slot_mul, vk] at *; omega

/-- The wide arrays are in the address space. -/
theorem G.bndW {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I)
    {j k : Nat} (hj : j < 16) (hk : k ≤ Wk I.k + 2) : slot (Wk I.k) j + 8 * k ≤ 2 ^ 64 := by
  have := h.ws.scr.nowrap; have := L.z; have := L.k1
  have : slot (Wk I.k) j + 8 * (Wk I.k + 2) ≤ slot (Wk I.k) 16 := slot_lt hj
  simp only [slot_mul, Wk, vk] at *; omega

/-- Words of arrays are kept by a rewrite of the header. -/
theorem Frm.hdrW_wv {B : Addr} {m m' : Mem} (f : Frm B hdrW m m') {d k : Nat} (hd : 256 ≤ d) (hb : d + 8 * k ≤ 2 ^ 64) :
    wv m' B d k = wv m B d k :=
  f.wv_eq (fun r hr => by
    simp only [hdrW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [sW, sArr, sStride, sFn] <;> omega) hb

theorem Frm.hdrW_word {B : Addr} {m m' : Mem} (f : Frm B hdrW m m') {d : Nat} (hd : 256 ≤ d) (hb : d + 8 ≤ 2 ^ 64) :
    word m' B d = word m B d :=
  f.word_eq (fun r hr => by
    simp only [hdrW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [sW, sArr, sStride, sFn] <;> omega) hb

theorem slot_ge (w j : Nat) : 256 ≤ slot w j := by unfold slot hdrBytes; omega

/-- Word `k` of array `j` is apart from array `i`'s first `n` bytes. -/
theorem wd_sep {w i j n k : Nat} (h : j ≠ i) (hn : n ≤ 8 * (w + 2)) (hk : k + 1 ≤ w + 2) :
    slot w j + 8 * k + 8 ≤ slot w i ∨ slot w i + n ≤ slot w j + 8 * k := by
  have := slot_sep (w := w) h; omega

/-- Words outside the header's rewritten slots and the ranges `rs` are kept. -/
theorem Frm.hdr_wv {B : Addr} {m m' : Mem} {rs : List (Nat × Nat)} (f : Frm B (hdrW ++ rs) m m') {d k : Nat}
    (hd : 256 ≤ d) (hb : d + 8 * k ≤ 2 ^ 64) (hrs : ∀ r ∈ rs, d + 8 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) :
    wv m' B d k = wv m B d k :=
  f.wv_eq (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [hdrW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [sW, sArr, sStride, sFn] <;> omega
    · exact hrs r hr) hb

theorem Frm.hdr_word {B : Addr} {m m' : Mem} {rs : List (Nat × Nat)} (f : Frm B (hdrW ++ rs) m m') {d : Nat}
    (hd : 256 ≤ d) (hb : d + 8 ≤ 2 ^ 64) (hrs : ∀ r ∈ rs, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d) :
    word m' B d = word m B d :=
  f.word_eq (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [hdrW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [sW, sArr, sStride, sFn] <;> omega
    · exact hrs r hr) hb

/-- Word `k` of narrow array `j` is apart from wide array `i`'s first `n` bytes. -/
theorem wdw_sep {v i j k n : Nat} (h1 : j ≠ 2 * i) (h2 : j ≠ 2 * i + 1) (hk : k + 1 ≤ v + 2) (hn : n ≤ 16 * (v + 2)) :
    slot v j + 8 * k + 8 ≤ slot (2 * v + 2) i ∨ slot (2 * v + 2) i + n ≤ slot v j + 8 * k := by
  have := nw_sep (k := k + 1) h1 h2 hk hn; omega

/-- Separation from each of a list of ranges. -/
macro "sep_tac" : tactic => `(tactic| (
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r hr
  repeat' rcases hr with rfl | hr
  all_goals first
    | exact rd_sep (by decide) (by omega) (by omega)
    | exact nw_sep (by decide) (by decide) (by omega) (by omega)
    | exact wn_sep (by decide) (by decide) (by omega) (by omega)
    | exact wd_sep (by decide) (by omega) (by omega)
    | exact wdw_sep (by decide) (by decide) (by omega) (by omega)
    | exact .inr (by omega)
    | (subst hr; first
      | exact rd_sep (by decide) (by omega) (by omega)
      | exact nw_sep (by decide) (by decide) (by omega) (by omega)
      | exact wn_sep (by decide) (by decide) (by omega) (by omega)
      | exact wd_sep (by decide) (by omega) (by omega)
      | exact wdw_sep (by decide) (by decide) (by omega) (by omega)
      | exact .inr (by omega))))

end VG.Proof.Rsa.AArch64.Rd
