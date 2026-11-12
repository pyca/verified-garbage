module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTSqrt
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTQDiv
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTParts
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Code
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Main
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTFail
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Stages
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Entry
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTSqrt
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTQDiv
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTParts
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Code
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Main
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTFail
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Stages
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Entry
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: constant time but for `n` and `e`

`main`, piece by piece (`main_ct`), then the entry, the modulus' check and
the failure path (`rdCode_ct`), and the contract's `ConstantTime`
(`rdCode_constantTime`). The pieces' runs agree from `GD`, whose facts are
those of the header the pieces need; `divA`'s division needs its divisor
normalized, which the correctness of what precedes it gives (`pre3_ok`,
`divA12_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-! ## `e`'s length for the wide products -/

/-- `e`'s length `4 W - 8` in the header. -/
def FE (I : RpIn) (s : State) : Prop :=
  word s.mem I.B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (4 * wW I.k - 8)

theorem stab_FE {Q : Nat → Prop} (hQ : ∀ y, Q y → y < 160 ∨ 168 ≤ y) : Stab FE Q :=
  stab_hdr (i := Impl.Bignum.X86_64.Public.sElen) (by decide) (fun I => BitVec.ofNat 64 (4 * wW I.k - 8))
    (fun y hy => by have := hQ y hy; simp only [Impl.Bignum.X86_64.Public.sElen, sFn]; omega_arith)

abbrev FT : RpIn → State → Prop := fun _ _ => True

theorem gr_ct {w : Nat → Nat} {F : RpIn → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (Two (GD w F)) c Q) : RelCT isa (Two (GR w F)) c Q :=
  h.mono (fun _ _ h => two_mono (fun _ _ h => h.1) h) fun _ _ h => h

theorem drop_ct {w : Nat → Nat} {F G : RpIn → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (Two (GD w G)) c Q) (hFG : ∀ I s, F I s → G I s) : RelCT isa (Two (GD w F)) c Q :=
  h.mono (fun _ _ h => two_mono (fun _ _ h => h.mono fun I _ => hFG I _) h) fun _ _ h => h

theorem setEl_ct : RelCT isa (Two (GD wW FT)) (.block setEl) (Two (GD wW FE)) :=
  two_post (two_taint [.rdi] pins_GD (by taint_decide)) fun p s h =>
    WP.mono (hdr_gd (i := Impl.Bignum.X86_64.Public.sElen)
      (by unfold DOk; simp only [Impl.Bignum.X86_64.Public.sElen, sFn]; omega_arith) (by decide) (by decide)
      (fun p => BitVec.ofNat 64 (4 * wW p.k - 8)) stab_true
      (fun p s h => WP.mono (setEl_ok h.ws) fun t ⟨hm, k⟩ => ⟨hm, _, k, by decide⟩) p s h)
      fun _ ht => ht.mono fun _ _ hI => hI.2

/-! ## The stages -/

theorem arrT : Arr FT := stab_true
theorem arrE : Arr FE := stab_FE fun y hy => .inr (by omega_arith)
theorem mskT : Stab FT fun y => 176 ≤ y ∧ y < 184 := stab_true
theorem mskE : Stab FE fun y => 176 ≤ y ∧ y < 184 := stab_FE fun y hy => .inr (by omega_arith)
theorem widT : Stab FT fun y => 48 ≤ y ∧ y < 128 ∨ 224 ≤ y ∧ y < 232 := stab_true
theorem deMinus_ct : RelCT isa (Two (GD wW FT)) (seqs deMinus) (Two (GD wW FT)) :=
  ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 1) (by decide) arrT (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (setOneA_ct (j := 1) (by decide) arrT (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (subA_ct (t := 2) (a := 5) (b := 1) (by decide) (by decide) (by decide)
      (by decide) (by decide) arrT (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (gr_ct (andZero_ct mskT))
    (ct_cons (List.cons_ne_nil _ _) (subA_ct (t := 3) (a := 2) (b := 1) (by decide) (by decide) (by decide)
      (by decide) (by decide) arrT (by taint_decide))
    (ct_one (gr_ct (andZero_ct mskT)))))))

theorem twosInit_ct : RelCT isa (Two (GD nv FT)) (seqs twosInit) (Two (GD nv FT)) :=
  ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 6) (by decide) arrT (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (copyA_ct (o := 6) (a := 4) (by decide) (by decide) (by decide) arrT
      (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 7) (by decide) arrT (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (subA_ct (t := 7) (a := 0) (b := 2) (by decide) (by decide) (by decide)
      (by decide) (by decide) arrT (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (gr_ct (zeroA_ct (j := 12) (by decide) arrT (by taint_decide)))
    (ct_one (zeroA_ct (j := 13) (by decide) arrT (by taint_decide)))))))

theorem hZ26 {F : RpIn → State → Prop} (p : RpP) (s : State) (h : GD nv F p s) : slot (nv p.k) 26 ≤ p.Z := by
  obtain ⟨I, m₀, rfl, -, L, -⟩ := h
  exact (rd_bounds L.k1 L.k2 L.z).2.1

theorem hw20 {F : RpIn → State → Prop} (p : RpP) (s : State) (h : GD nv F p s) : nv p.k < 2 ^ 20 := by
  obtain ⟨I, m₀, rfl, -, L, -⟩ := h
  exact (rd_bounds L.k1 L.k2 L.z).2.2.1

theorem prodE_ct : RelCT isa (Two (GD wW FE)) (seqs Recover.prod) (Two (GD wW FE)) :=
  prod_ct arrE (fun p => 4 * wW p.k - 8) fun p s h => by
    obtain ⟨I, m₀, rfl, -, -, -, -, -, hE⟩ := h
    exact ⟨hE, by show 1 ≤ 4 * (2 * (wk I.k + 1) + 2) - 8; omega_arith, by omega_arith⟩

theorem prod1_ct : RelCT isa (Two (GD nv F1)) (seqs Recover.prod) (Two (GD nv F1)) :=
  prod_ct arr_F1 RpP.el fun p s h => by
    obtain ⟨I, m₀, rfl, -, L, -, -, -, ha, -⟩ := h
    exact ⟨ha.el, L.el1, by have := L.el2; show I.el ≤ 8 * nv I.k; unfold nv wk; omega_arith⟩

/-! ## Before `divA` -/

/-- From a valid modulus. -/
def GMv (p : RpP) (s : State) : Prop :=
  ∃ I : RpIn, pubD I = p ∧ RpPre I s ∧ I.el ≤ 8 ∧ Spec.Rsa.modulusValid I.N I.k = true

theorem preA_ct [InvLaw] : RelCT isa (Two GM) (seqs (p1 ++ (p2 ++ ([.block (width true)] : List (Prog isa))))) (Two (GD wW FT)) := by
  have e : p1 ++ (p2 ++ ([.block (width true)] : List (Prog isa))) = [.block RecoverDet.head] ++
      ((loadA Impl.Bignum.X86_64.Public.aN Impl.Bignum.X86_64.Public.sN Impl.Bignum.X86_64.Public.sK ++
        ([zeroA 1] ++ (loadA Recover.aE Impl.Bignum.X86_64.Public.sE Impl.Bignum.X86_64.Public.sElen ++
        loadA Recover.aD Recover.sD Recover.sDl))) ++ (Recover.prod ++ ([.block (width true)] ++
      (deMinus ++ ([.block (width false)] ++ (twosInit ++ (twos ++ ([gcdW 6 12 7] ++
      [.block (width true)])))))))) := by
    simp only [p1, p2, List.append_assoc]
  rw [e]
  have ne : ∀ {a : Prog isa} {l : List (Prog isa)}, [a] ++ l ≠ [] := List.cons_ne_nil _ _
  exact ct_app ne (by simp [loadA]) (ct_one head_ct) (ct_app (by simp [loadA]) (by simp [Recover.prod])
    loads_ct (ct_app (by simp [Recover.prod]) ne prod1_ct
    (ct_app ne (by simp [deMinus]) (ct_one (drop_ct (width_ct true widT (by taint_decide)) fun _ _ _ => trivial))
    (ct_app (by simp [deMinus]) ne deMinus_ct
    (ct_app ne (by simp [twosInit]) (ct_one (width_ct false widT (by taint_decide)))
    (ct_app (by simp [twosInit]) (by simp [twos, wordStages]) twosInit_ct
    (ct_app (by simp [twos, wordStages]) ne (twos_ct arrT stab_true)
    (ct_cons ne (gcdW_ct (iU := 6) (iV := 12) (iM := 7) hZ26 hw20 (by decide) (by decide)
      (by decide) arrT (by taint_decide))
      (ct_one (width_ct true widT (by taint_decide)))))))))))

/-- What `divA`'s first parts need: `n`, `g` and `x` (wide). -/
def FA (I : RpIn) (s : State) : Prop :=
  (∃ G X, wv s.mem I.B (slot (wW I.k) 0) (wW I.k) = I.N ∧ wv s.mem I.B (slot (wW I.k) 6) (wW I.k) = G ∧
    G < 2 ^ (64 * (wk I.k + 1)) ∧ wv s.mem I.B (slot (wW I.k) 2) (wW I.k) = X) ∧
  2 ^ (64 * (wk I.k - 1)) ≤ I.N ∧ I.N < 2 ^ (64 * wk I.k)

theorem preA_ok [InvLaw] : RelCT isa (Two GMv) (seqs (p1 ++ (p2 ++ ([.block (width true)] : List (Prog isa))))) (Two (GD wW FA)) :=
  two_post ((ct_pre preA_ct fun _ _ ⟨I, e, h, hel, _⟩ => ⟨I, e, h, hel⟩).mono (fun _ _ h => h)
    fun _ _ _ => trivial) fun p s ⟨I, e, h, hel, hv⟩ => by
      obtain ⟨-, hNk, hNlo, -⟩ := rd_nums h.L hel hv
      exact WP.mono (pre3_ok h hel hv) fun t ⟨m₀, G, X, S, hm, n, g, gl, x⟩ =>
        ⟨I, m₀, e, S, h.L, h.outs, hel, hm, ⟨G, X, n, g, gl, x⟩, hNlo, hNk⟩

/-! ## `divA` -/

/-- `e`'s length and `sC`. -/
abbrev FEC : RpIn → State → Prop := fun I s => FE I s ∧ MC I s

theorem arrEC : ArrC FEC :=
  (stab_FE fun y hy => by omega_arith).and (stab_MC fun y hy => by omega_arith)

theorem divAp_ct : RelCT isa (Two (GD wW FA))
    (seqs (([.block setEl, copyA 8 6, copyA 9 2] : List (Prog isa)) ++ Recover.prod ++
      ([.block (clzTop 0), zeroA 8, shlZ 0 8, zeroA 9, shlZ 10 9] : List (Prog isa)))) (Two fun p s => GD wW FEC p s ∧ FDp p s) := by
  have hC : Arr FEC := arrEC.arr
  have weak : RelCT isa (Two (GD wW FT)) (seqs ([.block setEl, copyA 8 6, copyA 9 2] ++ Recover.prod ++
      [.block (clzTop 0), zeroA 8, shlZ 0 8, zeroA 9, shlZ 10 9])) (Two (GD wW FEC)) :=
    ct_app (by simp) (List.cons_ne_nil _ _)
      (ct_app (List.cons_ne_nil _ _) (by simp [Recover.prod]) (ct_cons (List.cons_ne_nil _ _) setEl_ct
        (ct_cons (List.cons_ne_nil _ _) (copyA_ct (o := 8) (a := 6) (by decide) (by decide) (by decide) arrE
          (by taint_decide))
        (ct_one (copyA_ct (o := 9) (a := 2) (by decide) (by decide) (by decide) arrE (by taint_decide)))))
        prodE_ct)
      (ct_cons (List.cons_ne_nil _ _) (clzTop_ct (j := 0) (by decide)
        (stab_FE fun y hy => by simp only [sC, sFn] at hy; omega_arith)
        (fun p s h => by have := h.kb; have := wW_eq p.k; omega_arith) (by taint_decide))
      (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 8) (by decide) hC (by taint_decide))
      (ct_cons (List.cons_ne_nil _ _) (shlZ_ct (a := 0) (d := 8) (by decide) (by decide) (by decide) arrE
        (by taint_decide))
      (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 9) (by decide) hC (by taint_decide))
      (ct_one (shlZ_ct (a := 10) (d := 9) (by decide) (by decide) (by decide) arrE (by taint_decide)))))))
  refine two_post ((ct_pre weak fun p s h => h.mono fun _ _ _ => trivial).mono (fun _ _ h => h)
    fun _ _ _ => trivial) fun p s h => ?_
  obtain ⟨I, m₀, e, h', L, O, he, ⟨c, hm⟩, ⟨G, X, hN, hG, hGv, hX⟩, hNlo, hNhi⟩ := id h
  subst e
  have kb : 8 ≤ wk I.k := h.kb.1
  have hnw := h'.ws.scr.nowrap
  have hZ := h'.ws.hZ
  rw [slotE] at hZ
  refine WP.mono (divA12_ok h'.ws (wW_eq I.k) kb hN hNlo hNhi hG hGv hX) fun t ⟨top, ⟨z, hz, hzC⟩, el, mm, f, k, hw⟩ =>
    ⟨h.next (F' := FEC) f (fun y hy => ⟨?_, ?_⟩) k (by simp [mmRegs]) (fun c' hc' => ⟨c', by show mw t.mem I.B = _; rw [mm]; exact hc'⟩)
      fun J e' _ => ?_, top⟩
  · unfold DaP at hy; unfold DOk; simp only [slotE] at hy; omega_arith
  · unfold DaP at hy; simp only [slotE] at hy; show y < I.Z; omega_arith
  · have eB : J.B = I.B := congrArg RpP.B e'
    have eK : J.k = I.k := congrArg RpP.k e'
    refine ⟨?_, z, hz, ?_⟩
    · show word t.mem J.B _ = _; rw [eB, el, eK]
    · show word t.mem J.B _ = _; rw [eB, hzC]

theorem divAr_ct : RelCT isa (Two (GD wW FEC)) (seqs [zeroA 6, shrZ 12 6, subA 14 11 0, .block andNz, copyA 7 11])
    (Two (GD wW FEC)) := by
  have hC : Arr FEC := arrEC.arr
  exact ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 6) (by decide) hC (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (shrZ_ct (a := 12) (d := 6) (by decide) (by decide) (by decide) arrE
      (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (subA_ct (t := 14) (a := 11) (b := 0) (by decide) (by decide) (by decide)
      (by decide) (by decide) hC (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (andNz_ct ((stab_FE fun y hy => by omega_arith).and
      (stab_MC fun y hy => by omega_arith)))
    (ct_one (copyA_ct (o := 7) (a := 11) (by decide) (by decide) (by decide) hC (by taint_decide))))))

/-! ## `divB` -/

theorem gd_fd {G : RpIn → State → Prop} {p : RpP} {s : State} (h : GD wW (fun I s => G I s ∧ FD I s) p s) :
    GD wW G p s ∧ FDp p s := by
  obtain ⟨I, m₀, rfl, h', L, O, he, hm, hG, hd⟩ := h
  exact ⟨⟨I, m₀, rfl, h', L, O, he, hm, hG⟩, hd⟩

theorem divB_ct : RelCT isa (Two (GD wW FEC)) (seqs divB) (Two (GD wW FEC)) := by
  have hC : Arr FEC := arrEC.arr
  have hMk : Stab FEC fun y => 176 ≤ y ∧ y < 184 :=
    (stab_FE fun y hy => by omega_arith).and (stab_MC fun y hy => by omega_arith)
  unfold divB
  exact ct_app (by simp [qDiv, normDN]) (List.cons_ne_nil _ _)
    (ct_app (by simp [qDiv, normDN]) (by simp [eqA])
    (ct_app (by simp [qDiv, normDN]) (List.cons_ne_nil _ _)
    (ct_app (by simp [normDN]) (by simp [qDiv])
    (ct_app (List.cons_ne_nil _ _) (by simp [normDN, wordStages])
      (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 5) (by decide) hC (by taint_decide))
      (ct_cons (List.cons_ne_nil _ _) (subA_ct (t := 5) (a := 0) (b := 6) (by decide) (by decide) (by decide)
        (by decide) (by decide) hC (by taint_decide))
      (ct_cons (List.cons_ne_nil _ _) (gr_ct (zeroA_ct (j := 2) (by decide) hC (by taint_decide)))
      (ct_one (addA_ct (o := 2) (a := 7) (b := 1) (by decide) (by decide) (by decide) (by decide) (by decide) hC
        (by taint_decide))))))
      (ct_post (ct_pre (normDN_ct (F := FE) arrE (stab_FE fun y hy => by simp only [sB2, sFn] at hy; omega_arith)
        (stab_FE fun y hy => by simp only [sC, sFn] at hy; omega_arith)) fun _ _ h => h.mono fun _ _ h => h.1)
        fun _ _ h => h))
    (ct_pre (qDiv_ct (F := FEC) 1 (by decide) (by decide) arrEC (by taint_decide) (by taint_decide))
      fun _ _ h => gd_fd h))
    (ct_one (zeroA_ct (j := 3) (by decide) hC (by taint_decide))))
    (eqA_ct (a := 12) (b := 3) (by decide) (by decide) hC (by taint_decide)))
    (ct_cons (List.cons_ne_nil _ _) (andZero_ct hMk)
    (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 4) (by decide) hC (by taint_decide))
    (ct_one (addA_ct (o := 4) (a := 11) (b := 1) (by decide) (by decide) (by decide) (by decide) (by decide) hC
      (by taint_decide)))))

/-! ## `b² - 4 n`, its square root, the factors -/

theorem minus4n_ct : RelCT isa (Two (GD wW FE)) (seqs minus4n) (Two (GD wW FE)) :=
  ct_app (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
    (ct_app (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
      (ct_cons (List.cons_ne_nil _ _) (copyA_ct (o := 8) (a := 4) (by decide) (by decide) (by decide) arrE
        (by taint_decide))
      (ct_one (copyA_ct (o := 9) (a := 4) (by decide) (by decide) (by decide) arrE (by taint_decide))))
      (prodB_ct arrE fun p s h => by
        obtain ⟨I, m₀, rfl, -, -, -, -, -, hE⟩ := h
        show word s.mem I.B _ = BitVec.ofNat 64 (8 * nv I.k)
        rw [hE]; congr 1; simp only [wW]; omega_arith))
    (ct_cons (List.cons_ne_nil _ _) (shlA_ct (fun _ _ h => h) false (j := 0) (by decide) arrE
      (fun _ s _ => ⟨_, shlPre_zero s⟩) (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (shlA_ct (fun _ _ h => h.1) false (j := 0) (by decide) arrE
      (fun _ s _ => ⟨_, shlPre_zero s⟩) (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (gr_ct (subA_ct (t := 12) (a := 10) (b := 0) (by decide) (by decide)
      (by decide) (by decide) (by decide) arrE (by taint_decide)))
    (ct_cons (List.cons_ne_nil _ _) (gr_ct (andZero_ct mskE))
    (ct_cons (List.cons_ne_nil _ _) (subA_ct (t := 13) (a := 12) (b := 1) (by decide) (by decide) (by decide)
      (by decide) (by decide) arrE (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (gr_ct (andZero_ct mskE))
    (ct_one (copyA_ct (o := 7) (a := 12) (by decide) (by decide) (by decide) arrE (by taint_decide)))))))))

theorem p4_ct : RelCT isa (Two (GD wW FEC)) (seqs p4) (Two (GD nv FT)) :=
  ct_app (by simp [minus4n]) (by simp [RecoverDet.sqrt, normX]) (ct_pre minus4n_ct fun _ _ h => h.mono fun _ _ h => h.1)
    (ct_app (by simp [RecoverDet.sqrt, normX]) (List.cons_ne_nil _ _)
      (sqrt_ct (F := FE) (stab_FE fun y hy => by unfold SqW at hy; omega_arith))
      (ct_one (drop_ct (G := G1 FE) (width_ct false ((((stab_FE fun y hy => by omega_arith).and
        (stab_mz fun y hy => by omega_arith)).and (stab_mk fun y hy => by omega_arith)).and
        (stab_MC fun y hy => by omega_arith)) (by taint_decide)) fun _ _ h => h) |>.mono
          (fun _ _ h => h) fun _ _ h => two_mono (fun _ _ h => h.mono fun _ _ _ => trivial) h))

theorem factors_eq : factors = [zeroA 10, addA 10 8 4, shrA 10, zeroA 11, subA 11 8 4, shrA 11] ++
    (storeA 10 Recover.sP Impl.Bignum.X86_64.Public.sK Impl.Bignum.X86_64.Public.sMask ++
    (storeA 11 Recover.sQ Impl.Bignum.X86_64.Public.sK Impl.Bignum.X86_64.Public.sMask ++
    ([.block retMask] : List (Prog isa)))) := by
  simp only [factors, List.append_assoc]

theorem factors_ct : RelCT isa (Two (GD nv FT)) (seqs factors) fun _ _ => True := by
  rw [factors_eq]
  exact RelCT.seqs_append (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) (RelCT.seq
    (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 10) (by decide) arrT (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (addA_ct (o := 10) (a := 8) (b := 4) (by decide) (by decide) (by decide)
      (by decide) (by decide) arrT (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (shrA_ct (j := 10) (by decide) arrT (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 11) (by decide) arrT (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (subA_ct (t := 11) (a := 8) (b := 4) (by decide) (by decide) (by decide)
      (by decide) (by decide) arrT (by taint_decide))
    (ct_one (gr_ct (shrA_ct (j := 11) (by decide) arrT (by taint_decide)))))))))
    (stores_ct.mono (fun _ _ h => two_mono (fun _ _ h => GD.gt h) h) fun _ _ h => h))

theorem factorsT_ct : RelCT isa (Two (GD nv FT)) (seqs factors) (Two fun (_ : RpP) (_ : State) => True) :=
  factors_ct.mono (fun _ _ h => h) fun _ _ _ => ⟨(default : RpP), trivial, trivial⟩

/-! ## `main` -/

theorem main_split : RecoverDet.main = seqs ((p1 ++ (p2 ++ ([.block (width true)] : List (Prog isa)))) ++
    ((([.block setEl, copyA 8 6, copyA 9 2] : List (Prog isa)) ++ Recover.prod ++
      ([.block (clzTop 0), zeroA 8, shlZ 0 8, zeroA 9, shlZ 10 9] : List (Prog isa))) ++ (qDiv 3 ++ (([zeroA 6, shrZ 12 6, subA 14 11 0, .block andNz, copyA 7 11] : List (Prog isa)) ++
    (divB ++ (p4 ++ factors)))))) := by
  rw [main_eq]
  simp only [p1, p2, p3, p4, divA, List.append_assoc, List.cons_append, List.nil_append]

/-- `main` leaks the same in two runs with the same public data, from a valid modulus. -/
theorem main_ct [InvLaw] : RelCT isa (Two GMv) RecoverDet.main fun _ _ => True := by
  rw [main_split]
  exact (ct_app (by simp) (by simp) preA_ok (ct_app (by simp) (by simp [qDiv]) divAp_ct
    (ct_app (by simp [qDiv]) (List.cons_ne_nil _ _) (qDiv_ct (F := FEC) 3 (by decide) (by decide) arrEC
      (by taint_decide) (by taint_decide))
    (ct_app (List.cons_ne_nil _ _) (by simp [divB]) divAr_ct
    (ct_app (by simp [divB]) (by simp [minus4n]) divB_ct
    (ct_app (by simp [minus4n]) (by simp [factors]) p4_ct
      factorsT_ct)))))).mono
    (fun _ _ h => h) fun _ _ _ => trivial

/-! ## The code -/

/-- A state the contract allows, with the public data `p`. -/
def RDRel (p : RpP) (s : State) : Prop := rdContract.pre s ∧ pubD (rpIn s) = p

/-- After `entry`'s first instruction. -/
def RD1 (p : RpP) (t : State) : Prop :=
  ∃ s, RDRel p s ∧ t.gpr .r11 = p.B ∧ t.gpr .rsp = p.sp ∧
    WP isa (.block ((Recover.entry.drop 1) ++ [.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
      .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))])) t (RpHeadPost s)

/-- After `entry` and the reloads. -/
def RD2 (p : RpP) (t : State) : Prop := ∃ s, RDRel p s ∧ RpHeadPost s t

/-- After the modulus' check. -/
def RD3 (p : RpP) (t : State) : Prop :=
  ∃ s t₁, RDRel p s ∧ RpHeadPost s t₁ ∧ t.mem = t₁.mem ∧ Keep [.rax, .rbp, .rsi] t₁ t ∧
    t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k)

/-- `RecoverDet.code` leaks the same in runs that agree on the public data. -/
theorem rdCode_ct [InvLaw] : RelCT isa (Two RDRel) RecoverDet.code fun _ _ => True := by
  unfold RecoverDet.code
  refine RelCT.seq (R := Two RD3) (RelCT.block_append (RelCT.seq (R := Two RD2) ?_ ?_)) ?_
  · rw [rpEntry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := RD1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (congrArg RpP.sp h₁.2).trans (congrArg RpP.sp h₂.2).symm) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := rpCtx_of (rd_rp hs.1).1
    have hh : WP isa (.block (([.mov .r11 (.mem { base := .rsp, disp := 40 })] : List Instr) ++
        ((Recover.entry.drop 1) ++ [.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
          .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))]))) s (RpHeadPost s) := by
      rw [← rpEntry_split]; exact rpHead_ok' c
    have e4 : s.gpr .rsp + BitVec.ofInt 64 40 = stackArgAddr s 4 := rfl
    have hB' : s.mem.readW (stackArgAddr s 4) 64 = stackArg s 4 := rfl
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 4)
      (by xrun [State.ea, e4, c.ha 4 (by decide), hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
        ⟨s, hs, h11.trans (congrArg RpP.B hs.2), (k.gpr (by decide)).trans (congrArg RpP.sp hs.2), hw⟩
  -- The modulus' check.
  · refine two_piece [.rdx, .rcx] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.rdx, h₂.rdx]
        exact (congrArg RpP.pN c₁.2).trans (congrArg RpP.pN c₂.2).symm
      · rw [h₁.rcx, h₂.rcx]
        exact congrArg (BitVec.ofNat 64) ((congrArg RpP.k c₁.2).trans (congrArg RpP.k c₂.2).symm))
      (by taint_decide) ?_
    rintro p t ⟨s, hs, h⟩
    have c := rpCtx_of (rd_rp hs.1).1
    have hnb := c.n.congrK h.inScr h.keep
    have hnl : (rpIn s).nb.length = (s.gpr .r9).toNat := bytesAt_length _ _ _
    refine WP.mono (invalid_ok h.rdx h.rcx c.L.k1 c.L.k2 hnl (fun i hi => hnb.rd i (by rw [hnl]; exact hi))
      (fun i hi => hnb.val i _)) fun t' ⟨hz, hm, k⟩ => ⟨s, t, hs, h, hm, k, ?_⟩
    rw [hz, ← hs.2]
    rfl
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁⟩ ⟨_, _, _, _, _, _, z₂⟩ => by
    simp only [eval, z₁, z₂]) ?_ ?_
  · exact Rp.failR_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, _⟩, _⟩ => by
      have hpre := rpPre_of (rpCtx_of (rd_rp hs.1).1) h hm k
      have L := hpre.L
      have O := hpre.outs
      exact ⟨fk (rpIn s), hs.2, hpre.scr, hpre.rdi, hpre.args, hpre.wr,
        ⟨L.k1, L.k2, L.el1, L.el2, L.dl1, L.dl2, L.nbl, L.ebl, List.length_replicate, L.z⟩,
        ⟨O.p, O.q, O.sp, O.sq, O.a⟩⟩) h)
      fun _ _ h => h
  · exact main_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, z⟩, hc⟩ =>
      ⟨rpIn s, hs.2, rpPre_of (rpCtx_of (rd_rp hs.1).1) h hm k, (rd_rp hs.1).2, by
        simp only [eval, z, Option.map_some, Option.some.injEq, Bool.not_eq_false'] at hc
        rw [← hs.2] at hc
        exact hc⟩) h) fun _ _ h => h

/-- `vg_rsa_recover_primes_det` is constant time but for `n` and `e`. -/
theorem rdCode_constantTime [InvLaw] : ConstantTime isa rdContract.pre rdContract.pub RecoverDet.code := by
  refine RelCT.constantTime (rdCode_ct.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨pubD (rpIn s₁), ⟨h₁, rfl⟩, ⟨h₂, ?_⟩⟩)
    fun _ _ h => h)
  obtain ⟨hr, a0, a1, a2, a3, a4, a5, hn, he⟩ := hp
  have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
  have w₁ := h₁.1.2.2.1
  have w₂ := h₂.1.2.2.1
  simp only [pubD, fk, RpIn.pub, rpIn, RpP.mk.injEq]
  refine ⟨a4.symm, by rw [a5], by rw [r .r9 (by decide)], by rw [a1], by rw [a3], r .rdi (by decide),
    r .rdx (by decide), r .r8 (by decide), a0.symm, a2.symm, hn.symm, he.symm, ?_, r .rsp (by decide)⟩
  rw [w₁, w₂, r .rdi (by decide), r .rsi (by decide), r .rdx (by decide), r .rcx (by decide), a4, a5]

end VG.Proof.Rsa.X86_64.Rd
