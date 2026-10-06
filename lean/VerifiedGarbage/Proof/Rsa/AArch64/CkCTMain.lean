import VerifiedGarbage.Proof.Rsa.AArch64.CkCT

/-!
# `vg_rsa_check_key` on AArch64: constant time, `main`

The pieces of `CkCT.lean` in sequence: the phases of the checks
(`ckPQ_ct`, `ckMod_ct`, `ckQI_ct`), and `main` (`ckMain_ct`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem toGKb {α : Type} {Φ : α → State → Prop} {c : Prog isa} {js js' : List Nat}
    (h : RelCT isa (Two Φ) c (Two (GKb js))) (hj : ∀ j ∈ js', j ∈ js) : RelCT isa (Two Φ) c (Two (GKb js')) :=
  h.mono (fun _ _ h => h) fun _ _ h => two_mono (fun _ _ h => h.mono hj) h

theorem toGK {α : Type} {Φ : α → State → Prop} {c : Prog isa} {js : List Nat}
    (h : RelCT isa (Two Φ) c (Two (GKb js))) : RelCT isa (Two Φ) c (Two GK) :=
  h.mono (fun _ _ h => h) fun _ _ h => two_mono (fun _ _ h => h.1) h

theorem ofGK {Ψ : CkP → State → Prop} {c : Prog isa} (h : RelCT isa (Two (GKb [])) c (Two Ψ)) :
    RelCT isa (Two GK) c (Two Ψ) :=
  h.mono (fun _ _ h => two_mono (fun _ _ h => ⟨h, by simp⟩) h) fun _ _ h => h

/-- The loads of `main`, from `GK`. -/
theorem ld_ct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : CkP → Addr)
    (len : CkP → Nat) {js : List Nat} (hjs : ∀ i ∈ js, i ≠ j ∧ i < 16)
    (hA : ∀ (I : CkIn) (m₀ : Mem) (s : State), CkS I m₀ s → CkLens I → word s.mem I.B (8 * sPtr) = ptr I.pub ∧
      word s.mem I.B (8 * sLen) = BitVec.ofNat 64 (len I.pub) ∧
      (∃ bs, Src s I.B I.Z (ptr I.pub) bs ∧ bs.length = len I.pub) ∧ 1 ≤ len I.pub ∧ len I.pub ≤ I.k)
    {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x8 ++ [movi .x7 0])) zeroAcc)
      hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base j .x8 ++ [ldh .x1 sPtr, ldh .x2 sLen]))
      hc₂).isSome = true)
    {hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₃ : (taint.check (Taint.ofRegs [.x0, .x8, .x1, .x2]) loadBE hc₃).isSome = true) :
    RelCT isa (Two (GKb js)) (seqs (loadA j sPtr sLen)) (Two (GKb (j :: js))) :=
  loadA_ckct hj hP hL hjs ptr len (fun p s h => by
    obtain ⟨I, m₀, c, rfl, hs, L, -⟩ := h
    exact hA I m₀ s hs L) ht₁ ht₂ ht₃

/-! ## The phases -/

theorem ckPQ_ct : RelCT isa (Two GK) (seqs (loadA aX sP sPlen ++ (loadA aR sQ sQlen ++
    (mulXR ++ (eqA aA 0 ++ ([.block andZero] : List (Prog isa))))))) (Two GK) := by
  refine ofGK (ct_app (by simp [loadA]) (by simp [loadA]) (ld_ct (by decide) (by decide) (by decide) CkP.pP CkP.pl
    (by simp) (fun I m₀ s hs L => ⟨hs.args.p, hs.args.pl, ⟨_, hs.p, L.pbl⟩, L.pl1, Nat.le_of_lt L.pl2⟩)
    (by taint_decide) (by taint_decide) (by taint_decide)) (ct_app (by simp [loadA]) (by simp [mulXR])
    (ld_ct (by decide) (by decide) (by decide) CkP.pQ CkP.ql (by decide)
      (fun I m₀ s hs L => ⟨hs.args.q, hs.args.ql, ⟨_, hs.q, L.qbl⟩, L.ql1, Nat.le_of_lt L.ql2⟩)
      (by taint_decide) (by taint_decide) (by taint_decide))
    (ct_app (by simp [mulXR]) (by simp [eqA]) (mulXR_ckct (by taint_decide) (by taint_decide) |>.mono
      (fun _ _ h => two_mono (fun _ _ h => h.mono (by simp)) h) fun _ _ h => h)
      (ct_app (by simp [eqA]) (by simp) (eqA_ckct (by decide) (by decide) (by taint_decide))
        (ct_one andZero_ckct)))))

theorem modOne_ckct : RelCT isa (Two GK) (seqs modOne) (Two GK) := by
  unfold modOne
  rw [List.append_assoc]
  exact ct_app (a := [divmod aA aRem aM aT]) (by simp) (by simp [eqA]) (ct_one (divmod_ckct (by taint_decide)
    (by taint_decide))) (ct_app (by simp [eqA]) (by simp) (eqA_ckct (a := aRem) (b := aOne) (by decide) (by decide)
      (by taint_decide)) (ct_one andZero_ckct))

theorem ckDN_ct : RelCT isa (Two GK) (seqs (loadA aX sD sDlen ++ ltA aX 0)) (Two GK) :=
  toGK (ofGK (ct_app (by simp [loadA]) (by simp [ltA]) (ld_ct (by decide) (by decide) (by decide) CkP.pD CkP.dl
    (by decide) (fun I m₀ s hs L => ⟨hs.args.d, hs.args.dl, ⟨_, hs.d, L.dbl⟩, L.dl1, L.dl2⟩)
    (by taint_decide) (by taint_decide) (by taint_decide))
    (ltA_ckct (by decide) (by decide) (by decide) (by taint_decide))))

/-- The checks modulo `X - 1`. -/
theorem ckMod_ct {sX sXlen sDX : Nat} (hsX : sX < 32) (hsL : sXlen < 32) (hsD : sDX < 32) (pX pDX : CkP → Addr)
    (xl : CkP → Nat)
    (hX : ∀ (I : CkIn) (m₀ : Mem) (s : State), CkS I m₀ s → CkLens I → word s.mem I.B (8 * sX) = pX I.pub ∧
      word s.mem I.B (8 * sXlen) = BitVec.ofNat 64 (xl I.pub) ∧
      (∃ bs, Src s I.B I.Z (pX I.pub) bs ∧ bs.length = xl I.pub) ∧ 1 ≤ xl I.pub ∧ xl I.pub ≤ I.k)
    (hDX : ∀ (I : CkIn) (m₀ : Mem) (s : State), CkS I m₀ s → CkLens I → word s.mem I.B (8 * sDX) = pDX I.pub ∧
      word s.mem I.B (8 * sXlen) = BitVec.ofNat 64 (xl I.pub) ∧
      (∃ bs, Src s I.B I.Z (pDX I.pub) bs ∧ bs.length = xl I.pub) ∧ 1 ≤ xl I.pub ∧ xl I.pub ≤ I.k)
    {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (htX : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base aM .x8 ++ [ldh .x1 sX, ldh .x2 sXlen]))
      hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (htDX : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base aX .x8 ++ [ldh .x1 sDX, ldh .x2 sXlen]))
      hc₂).isSome = true) :
    RelCT isa (Two GK) (seqs (modChecks sX sXlen sDX)) (Two GK) := by
  rw [modChecks_eq]
  have ldX := toGK (ofGK (ld_ct (j := aM) (by decide) hsX hsL pX xl (by decide) hX (by taint_decide) htX (by taint_decide)))
  have ldDX := ofGK (ld_ct (j := aX) (by decide) hsD hsL pDX xl (by decide) hDX (by taint_decide) htDX (by taint_decide))
  have ldD := ofGK (ld_ct (j := aX) (by decide) (by decide) (by decide) CkP.pD CkP.dl (by decide)
    (fun I m₀ s hs L => ⟨hs.args.d, hs.args.dl, ⟨_, hs.d, L.dbl⟩, L.dl1, L.dl2⟩)
    (by taint_decide) (by taint_decide) (by taint_decide))
  have mE := mulE_ckct (by taint_decide) (by taint_decide)
  exact ct_app (by simp [loadA]) (by simp) ldX (ct_app (a := [.block (decA aM)]) (by simp) (by simp [loadA])
    (ct_one (decA_ckct (by decide) (by taint_decide)))
    (ct_app (by simp [loadA]) (by simp [ltA]) ldDX
    (ct_app (by simp [ltA]) (by simp [loadA]) (toGK (ltA_ckct (a := aX) (b := aM) (js := [aX]) (by decide)
      (by decide) (by decide) (by taint_decide)))
    (ct_app (by simp [loadA]) (by simp [mulE]) ldD
    (ct_app (by simp [mulE]) (by simp [modOne]) mE
    (ct_app (by simp [modOne]) (by simp [loadA]) modOne_ckct
    (ct_app (by simp [loadA]) (by simp [mulE]) ldDX
    (ct_app (by simp [mulE]) (by simp [modOne]) mE modOne_ckct))))))))

/-- `qInv < p` and `q qInv ≡ 1 (mod p)`. -/
theorem ckQI_ct : RelCT isa (Two GK) (seqs (loadA aM sP sPlen ++ (loadA aX sQI sPlen ++ (ltA aX aM ++
    (loadA aR sQ sQlen ++ (mulXR ++ modOne)))))) (Two GK) :=
  ct_app (by simp [loadA]) (by simp [loadA]) (toGK (ofGK (ld_ct (by decide) (by decide) (by decide) CkP.pP CkP.pl
    (by decide) (fun I m₀ s hs L => ⟨hs.args.p, hs.args.pl, ⟨_, hs.p, L.pbl⟩, L.pl1, Nat.le_of_lt L.pl2⟩)
    (by taint_decide) (by taint_decide) (by taint_decide))))
  (ofGK (ct_app (by simp [loadA]) (by simp [ltA]) (ld_ct (by decide) (by decide) (by decide) CkP.pQi CkP.pl
    (by decide) (fun I m₀ s hs L => ⟨hs.args.qi, hs.args.pl, ⟨_, hs.qi, L.qibl⟩, L.pl1, Nat.le_of_lt L.pl2⟩)
    (by taint_decide) (by taint_decide) (by taint_decide))
  (ct_app (by simp [ltA]) (by simp [loadA]) (ltA_ckct (a := aX) (b := aM) (js := [aX]) (by decide) (by decide)
    (by decide) (by taint_decide))
  (ct_app (by simp [loadA]) (by simp [mulXR]) (toGKb (ld_ct (by decide) (by decide) (by decide) CkP.pQ CkP.ql
    (js := [aX]) (by decide) (fun I m₀ s hs L => ⟨hs.args.q, hs.args.ql, ⟨_, hs.q, L.qbl⟩, L.ql1, Nat.le_of_lt L.ql2⟩)
    (by taint_decide) (by taint_decide) (by taint_decide)) (js' := [aX, aR]) (by decide))
  (ct_app (by simp [mulXR]) (by simp [modOne]) (mulXR_ckct (by taint_decide) (by taint_decide))
    modOne_ckct)))))

/-! ## `main` -/

/-- On entry to `main`. -/
def GKM (p : CkP) (s : State) : Prop := ∃ I : CkIn, I.pub = p ∧ CkPre I s

theorem pins_GKM : Pins GKM [.x0] := fun _ _ _ ⟨_, e₁, h₁⟩ ⟨_, e₂, h₂⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁.x0, h₂.x0]
  exact (congrArg CkP.B e₁).trans (congrArg CkP.B e₂).symm

theorem ckHead_ct : RelCT isa (Two GKM) (.block VG.Impl.Rsa.AArch64.CheckKey.head) (Two GK) :=
  two_piece [.x0] pins_GKM (by taint_decide) fun _ s ⟨I, e, h⟩ =>
    WP.mono (ckHeadS_ok h) fun _ ⟨ht, hm⟩ => ⟨I, s.mem, true, e, ht, h.L, hm⟩

theorem retMaskK_ct : RelCT isa (Two GK) (.block retMask) (Two fun (_ : CkP) (_ : State) => True) :=
  two_post (two_taint [.x0] pins_GK (by taint_decide)) fun _ _ h => by
    obtain ⟨I, m₀, c, rfl, hs, -, hm⟩ := h
    exact WP.mono (cvExit_ok hs.ws hm) fun _ _ => trivial

/-- `main` leaks the same in two runs with the same public data. -/
theorem ckMain_ct : RelCT isa (Two GKM) VG.Impl.Rsa.AArch64.CheckKey.main fun _ _ => True := by
  rw [ckMain_eq]
  refine (ct_app (by simp) (by simp [loadA]) (ct_one ckHead_ct)
    (ct_app (by simp [loadA]) (by simp [loadA]) (toGK (ofGK (ld_ct (by decide) (by decide) (by decide) CkP.pN CkP.k
      (by decide) (fun I m₀ s hs L => ⟨hs.args.n, hs.args.k, ⟨_, hs.n, L.nl⟩, show 1 ≤ I.k by have := L.k1; omega, Nat.le_refl _⟩)
      (by taint_decide) (by taint_decide) (by taint_decide))))
    (ct_app (by simp [loadA]) (by simp) (toGK (ofGK (ld_ct (by decide) (by decide) (by decide) CkP.pE CkP.el
      (by decide) (fun I m₀ s hs L => ⟨hs.args.e, hs.args.el, ⟨_, hs.e, L.ebl⟩, L.el1, L.el2⟩)
      (by taint_decide) (by taint_decide) (by taint_decide))))
    (ct_app (by simp) (by simp [loadA]) (ct_cons (by simp) (zeroA_ckct (by decide) (by taint_decide))
      (ct_one (setOneA_ckct (by decide) (by taint_decide))))
    (ct_app (by simp [loadA]) (by simp [loadA]) ckDN_ct
    (ct_app (by simp [loadA]) (by simp [modChecks]) ckPQ_ct
    (ct_app (by simp [modChecks]) (by simp [modChecks]) (ckMod_ct (by decide) (by decide) (by decide) CkP.pP CkP.pDp
      CkP.pl (fun I m₀ s hs L => ⟨hs.args.p, hs.args.pl, ⟨_, hs.p, L.pbl⟩, L.pl1, Nat.le_of_lt L.pl2⟩)
      (fun I m₀ s hs L => ⟨hs.args.dp, hs.args.pl, ⟨_, hs.dp, L.dpbl⟩, L.pl1, Nat.le_of_lt L.pl2⟩)
      (by taint_decide) (by taint_decide))
    (ct_app (by simp [modChecks]) (by simp [loadA]) (ckMod_ct (by decide) (by decide) (by decide) CkP.pQ CkP.pDq
      CkP.ql (fun I m₀ s hs L => ⟨hs.args.q, hs.args.ql, ⟨_, hs.q, L.qbl⟩, L.ql1, Nat.le_of_lt L.ql2⟩)
      (fun I m₀ s hs L => ⟨hs.args.dq, hs.args.ql, ⟨_, hs.dq, L.dqbl⟩, L.ql1, Nat.le_of_lt L.ql2⟩)
      (by taint_decide) (by taint_decide))
    (ct_app (by simp [loadA]) (by simp) ckQI_ct (ct_one retMaskK_ct)))))))))).mono
    (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.Rsa.AArch64
