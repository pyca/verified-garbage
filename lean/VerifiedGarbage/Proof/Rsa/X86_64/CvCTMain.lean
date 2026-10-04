import VerifiedGarbage.Proof.Rsa.X86_64.CvCT

/-!
# `vg_rsa_crt_values` on x86-64: constant time, `main`

The pieces of `CvCT.lean` in sequence (`loads_ct`, `pqCheck_ct`,
`invPart_ct`, `divs_ct`), the stores (`stores_ct`, from `GS`), and `main`
(`cvMain_ct`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)
open VG.Impl.Rsa.X86_64 (copyWords)

/-! ## Sequences -/

theorem ct_cons {α : Type} {Φ Ψ Ξ : α → State → Prop} {e : Prog isa} {l : List (Prog isa)} (hl : l ≠ [])
    (he : RelCT isa (Two Φ) e (Two Ψ)) (hr : RelCT isa (Two Ψ) (seqs l) (Two Ξ)) :
    RelCT isa (Two Φ) (seqs (e :: l)) (Two Ξ) := by
  obtain ⟨d, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  exact RelCT.seq he hr

theorem ct_one {α : Type} {Φ Ψ : α → State → Prop} {e : Prog isa} (he : RelCT isa (Two Φ) e (Two Ψ)) :
    RelCT isa (Two Φ) (seqs [e]) (Two Ψ) := he

theorem ct_app {α : Type} {Φ Ψ Ξ : α → State → Prop} {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ [])
    (hA : RelCT isa (Two Φ) (seqs a) (Two Ψ)) (hB : RelCT isa (Two Ψ) (seqs b) (Two Ξ)) :
    RelCT isa (Two Φ) (seqs (a ++ b)) (Two Ξ) :=
  RelCT.seqs_append ha hb (RelCT.seq hA hB)

/-! ## The loads -/

theorem loadA_ct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : CvP → Addr)
    (len : CvP → Nat)
    (hA : ∀ p s, GA p s → Bignum.X86_64.word s.mem p.B (8 * sPtr) = ptr p ∧
      Bignum.X86_64.word s.mem p.B (8 * sLen) = BitVec.ofNat 64 (len p) ∧
      (∃ bs, Src s p.B p.Z (ptr p) bs ∧ bs.length = len p) ∧ 1 ≤ len p ∧ len p ≤ 8 * wk p.k)
    {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.rdi]) (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr sLen))] : List Instr))) hc₂).isSome = true) :
    RelCT isa (Two GA) (seqs (loadA j sPtr sLen)) (Two GA) :=
  RelCT.seq (zeroA_ct hj ht₁) (loadTail_ct hj hP hL ptr len hA ht₂)

/-- The four loads. -/
theorem loads_ct : RelCT isa (Two GA) (seqs (loadA aN Impl.Bignum.X86_64.Public.sN Impl.Bignum.X86_64.Public.sK ++
    (loadA aP sP sPl ++ (loadA aQ sQ sQl ++ loadA aD sD sDl)))) (Two GA) := by
  have k8 : ∀ {k : Nat}, k ≤ 8 * wk k := fun {k} => by unfold wk; omega
  refine ct_app (by simp [loadA]) (by simp [loadA]) (loadA_ct (by decide) (by decide) (by decide) CvP.pN CvP.k
    (fun p s h => ?_) (by taint_decide) (by taint_decide)) (ct_app (by simp [loadA]) (by simp [loadA])
    (loadA_ct (by decide) (by decide) (by decide) CvP.pP CvP.pl (fun p s h => ?_) (by taint_decide) (by taint_decide))
    (ct_app (by simp [loadA]) (by simp [loadA])
    (loadA_ct (by decide) (by decide) (by decide) CvP.pQ CvP.ql (fun p s h => ?_) (by taint_decide) (by taint_decide))
    (loadA_ct (by decide) (by decide) (by decide) CvP.pD CvP.dl (fun p s h => ?_) (by taint_decide)
      (by taint_decide))))
  all_goals
    obtain ⟨I, m₀, c, rfl, h, L, -⟩ := h
    dsimp only [CvIn.pub]
    have := L.k1
  · exact ⟨h.args.n, h.args.k, ⟨_, h.n, L.nl⟩, by omega, k8⟩
  · exact ⟨h.args.p, h.args.pl, ⟨_, h.p, L.pbl⟩, L.pl1, by have := L.pl2; have := @k8 I.k; omega⟩
  · exact ⟨h.args.q, h.args.ql, ⟨_, h.q, L.qbl⟩, L.ql1, by have := L.ql2; have := @k8 I.k; omega⟩
  · exact ⟨h.args.d, h.args.dl, ⟨_, h.d, L.dbl⟩, L.dl1, by have := L.dl2; have := @k8 I.k; omega⟩

/-! ## The arithmetic -/

theorem pqCheck_ct : RelCT isa (Two GA) (seqs pqCheck) (Two GA) := by
  unfold pqCheck
  exact ct_app (by simp) (by simp)
    (ct_app (by simp) (by simp [eqA])
      (ct_app (by simp) (by simp)
        (ct_app (by simp) (by simp [eqA])
          (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
            (ct_cons (by simp) (copyA_ct (by decide) (by decide) (by decide) (by taint_decide))
              (ct_one (divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by taint_decide)))))
          (eqA_ct (by decide) (by decide) (by taint_decide)))
        (ct_cons (by simp) andZero_ct (ct_one (zeroA_ct (by decide) (by taint_decide)))))
      (eqA_ct (by decide) (by decide) (by taint_decide)))
    (ct_cons (by simp) andZero_ct (ct_one (andOdd_ct (by decide) (by taint_decide))))

theorem invSetup_ct : RelCT isa (Two GA) (seqs invSetup) (Two GI) := by
  refine two_post ((?_ : RelCT isa (Two GA) (seqs invSetup) (Two GA)).mono (fun _ _ h => h) fun _ _ _ => trivial)
    fun p s h => ?_
  · unfold invSetup
    exact ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
      (ct_cons (by simp) (copyA_ct (by decide) (by decide) (by decide) (by taint_decide))
      (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
      (ct_cons (by simp) (copyA_ct (by decide) (by decide) (by decide) (by taint_decide))
      (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
      (ct_cons (by simp) (setOneA_ct (by decide) (by taint_decide))
      (ct_one (zeroA_ct (by decide) (by taint_decide))))))))
  · obtain ⟨I, m₀, c, rfl, h', L, O, hm⟩ := h
    exact WP.mono (invSetup_ok h' L) fun t ⟨ht, mt, u0, _, vm, x1, x2, _⟩ =>
      ⟨⟨I, m₀, c, rfl, ht, L, O, mt.trans hm⟩, u0, vm, x1, x2⟩

theorem invPart_ct : RelCT isa (Two GA) (seqs invPart) (Two GA) := by
  unfold invPart
  exact ct_app (by simp [invSetup]) (by simp) invSetup_ct
    (ct_app (by simp) (by simp [eqA])
      (ct_cons (by simp) (inverse_ct (by taint_decide))
        (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
          (ct_one (setOneA_ct (by decide) (by taint_decide)))))
      (ct_app (by simp [eqA]) (by simp) (eqA_ct (by decide) (by decide) (by taint_decide)) (ct_one andZero_ct)))

theorem divisor_ct {j : Nat} (hj : j < 16) (hjC : aC ≠ j) (hjU : aU ≠ j) {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .rsi ++ base aC .rbx)) copyWords)
      hc₁).isSome = true) :
    RelCT isa (Two GA) (seqs (divisor j)) (Two GA) := by
  unfold divisor
  exact ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
    (ct_cons (by simp) (copyA_ct (by decide) hj hjC ht)
    (ct_cons (by simp) (decA_ct (by decide) (by taint_decide))
    (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
    (ct_one (copyA_ct (by decide) (by decide) (by decide) (by taint_decide))))))

/-- `dP` and `dQ`. -/
theorem divs_ct : RelCT isa (Two GA) (seqs ((divisor aP ++ ([divmod aU aV aC aT] : List (Prog isa))) ++
    (([zeroA aX₁, copyA aX₁ aV] : List (Prog isa)) ++ (divisor aQ ++ ([divmod aU aV aC aT] : List (Prog isa))))))
    (Two GA) :=
  ct_app (by simp [divisor]) (by simp)
    (ct_app (by simp [divisor]) (by simp) (divisor_ct (by decide) (by decide) (by decide) (by taint_decide))
      (ct_one (divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by taint_decide))))
    (ct_app (by simp) (by simp [divisor])
      (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
        (ct_one (copyA_ct (by decide) (by decide) (by decide) (by taint_decide))))
      (ct_app (by simp [divisor]) (by simp) (divisor_ct (by decide) (by decide) (by decide) (by taint_decide))
        (ct_one (divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by taint_decide)))))

end VG.Proof.Rsa.X86_64
