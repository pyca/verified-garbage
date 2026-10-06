import VerifiedGarbage.Proof.Rsa.AArch64.CvCT

/-!
# `vg_rsa_crt_values` on AArch64: constant time, `main`

The pieces of `CvCT.lean` in sequence (`loads_ct`, `pqCheck_ct`,
`invPart_ct`, `divisor_ct`), the stores (`stores_ct`, from `GS`), and
`main` (`cvMain_ct`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.Keys.CrtValues
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN)

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

/-- The four loads. -/
theorem loads_ct : RelCT isa (Two GA) (seqs (loadA aN Public.sN Public.sK ++
    (loadA aP sP sPl ++ (loadA aQ sQ sQl ++ loadA aD sD sDl)))) (Two GA) := by
  have k8 : ∀ {k : Nat}, k ≤ 8 * wk k := fun {k} => by unfold wk; omega
  refine ct_app (by simp [loadA]) (by simp [loadA]) (loadA_ct (by decide) (by decide) (by decide) CvP.pN CvP.k
    (fun p s h => ?_) (by taint_decide) (by taint_decide) (by taint_decide)) (ct_app (by simp [loadA])
    (by simp [loadA]) (loadA_ct (by decide) (by decide) (by decide) CvP.pP CvP.pl (fun p s h => ?_)
      (by taint_decide) (by taint_decide) (by taint_decide))
    (ct_app (by simp [loadA]) (by simp [loadA])
    (loadA_ct (by decide) (by decide) (by decide) CvP.pQ CvP.ql (fun p s h => ?_) (by taint_decide)
      (by taint_decide) (by taint_decide))
    (loadA_ct (by decide) (by decide) (by decide) CvP.pD CvP.dl (fun p s h => ?_) (by taint_decide)
      (by taint_decide) (by taint_decide))))
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
                (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)))))
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

theorem divisor_ct {j : Nat} (hj : j < 16) (hjC : aC ≠ j) {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x16 ++ base aC .x17)) copyWords)
      hc₁).isSome = true) :
    RelCT isa (Two GA) (seqs (divisor j)) (Two GA) := by
  unfold divisor
  exact ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
    (ct_cons (by simp) (copyA_ct (by decide) hj hjC ht)
    (ct_cons (by simp) (decA_ct (by decide) (by taint_decide))
    (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
    (ct_one (copyA_ct (by decide) (by decide) (by decide) (by taint_decide))))))

/-! ## The stores -/

/-- Between the stores: the working space, the header, the mask, and the
outputs, but not memory outside the working space. -/
def GS (p : CvP) (s : State) : Prop :=
  ∃ (I : CvIn) (c : Bool), I.pub = p ∧ Ws s I.B I.Z (wk I.k) ∧
    CvArgs s.mem I.B I.k I.pl I.ql I.dl I.pDp I.pDq I.pQi I.pN I.pP I.pQ I.pD ∧ s.wr = I.W ∧ CvLens I ∧
    CvOuts I ∧ mword s.mem I.B = mask c

theorem GS.ws {p : CvP} {s : State} (h : GS p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨I, c, rfl, h, -⟩ := h
  exact h

theorem GA.gs {p : CvP} {s : State} (h : GA p s) : GS p s := by
  obtain ⟨I, m₀, c, rfl, h, L, O, hm⟩ := h
  exact ⟨I, c, rfl, h.ws, h.args, h.wr, L, O, hm⟩

theorem pins_GS : Pins GS [.x0] := pins_ws CvP.B CvP.Z (fun p => wk p.k) fun _ _ h => h.ws

/-- The registers `storeBE` needs pinned: the base, the end of the output
and its length. -/
def soVal (B base ptr : Addr) (len : Nat) : Reg → BitVec 64
  | .x0 => B
  | .x8 => base
  | .x1 => ptr + BitVec.ofNat 64 len
  | .x9 => BitVec.ofNat 64 len
  | _ => 0

/-- The block before `storeBE`: the base of `[j]`, the pointer, the length
and the mask. -/
theorem storeBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j sPtr sLen len : Nat} {ptr : Addr}
    (hP : sPtr < 32) (hL : sLen < 32) (hp : word s.mem B (8 * sPtr) = ptr)
    (hl : word s.mem B (8 * sLen) = BitVec.ofNat 64 len) :
    WP isa (.block (ws ++ base j .x8 ++ [ldh .x1 sPtr, ldh .x9 sLen, .add .x .x1 .x1 .x9, ldh .x15 Public.sMask]))
      s fun t => ∀ r ∈ [Reg.x0, .x8, .x1, .x9], t.gpr r = soVal B (off B (slot w j)) ptr len r := by
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨⟨_, h11, m₂, _⟩, k₂⟩ =>
    WP.mono (base_ok j .x8 ((k₂.gpr .x0 (by decide)).trans h.x0) h11) fun s₃ ⟨⟨h8, m₃, _⟩, k₃⟩ =>
      WP.mono (WP.keep [.x1, .x9, .x15] (Q := fun t => t.gpr .x1 = ptr + BitVec.ofNat 64 len ∧
          t.gpr .x9 = BitVec.ofNat 64 len) (by
          have h0₃ : s₃.gpr .x0 = B := ((k₂.trans k₃).gpr .x0 (by decide)).trans h.x0
          have hs₃ := h.scr.congr (k₂.trans k₃).wr
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega)
          brun [h0₃, hdr_enc hP, hdr_enc hL, hdr_enc (show Public.sMask < 32 by decide), m₃, m₂, hl₃ sPtr hP,
            hl₃ sLen hL, hl₃ Public.sMask (by decide), hp, hl])
        rfl rfl rfl)
      fun t ⟨⟨h1, h9⟩, k₄⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (((k₂.trans k₃).trans k₄).gpr .x0 (by decide)).trans h.x0
        · exact (k₄.gpr .x8 (by decide)).trans h8
        · exact h1
        · exact h9))

theorem storeA_ct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : CvP → Addr)
    (len : CvP → Nat)
    (hA : ∀ p s, GS p s → word s.mem p.B (8 * sPtr) = ptr p ∧ word s.mem p.B (8 * sLen) = BitVec.ofNat 64 (len p) ∧
      (∀ i < len p, InRegions p.W (ptr p + BitVec.ofNat 64 i) 1) ∧
      (∀ i < len p, p.Z ≤ ofs p.B (ptr p + BitVec.ofNat 64 i)) ∧ 1 ≤ len p ∧ len p ≤ 8 * wk p.k)
    {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base j .x8 ++ [ldh .x1 sPtr, ldh .x9 sLen,
      .add .x .x1 .x1 .x9, ldh .x15 Public.sMask])) hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x8, .x1, .x9]) storeBE hc₂).isSome = true) :
    RelCT isa (Two GS) (seqs (storeA j sPtr sLen Public.sMask)) (Two GS) :=
  pin_ct [.x0] [.x0, .x8, .x1, .x9] (fun p => soVal p.B (off p.B (slot (wk p.k) j)) (ptr p) (len p)) pins_GS ht₁
    (fun p s h => by
      obtain ⟨hp, hl, -⟩ := hA p s h
      exact storeBlk_ok h.ws hP hL hp hl) ht₂ fun p s h => by
      obtain ⟨hp, hl, hwr, hsep, hl1, hlw⟩ := hA p s h
      obtain ⟨I, c, rfl, hw, ha, hW, L, O, hm⟩ := h
      dsimp only [CvIn.pub] at hp hl hwr hsep hl1 hlw ⊢
      have hn := hw.scr.nowrap
      have h256 := hw.h256
      refine WP.mono (storeA_ws hw hj hP hL hp hl hm hl1 hlw (fun i hi => by rw [hW]; exact hwr i hi) hsep)
        fun t ⟨_, _, ht, hf, k⟩ => ?_
      have fw : ∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i) :=
        fun i hi => hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)
      exact ⟨I, c, rfl, ht, ha.congr fun i hi => fw i (by unfold argSlot at hi; omega), k.wr.trans hW, L, O,
        (fw _ (by decide)).trans hm⟩

theorem retMask_ct : RelCT isa (Two GS) (.block retMask) fun _ _ => True :=
  two_taint [.x0] pins_GS (by taint_decide)

/-- The stores and the exit. -/
theorem stores_ct : RelCT isa (Two GS) (seqs (storeA aX₂ sQi sPl Public.sMask ++
    (storeA aX₁ sDp sPl Public.sMask ++ (storeA aV sDq sQl Public.sMask ++
      ([.block retMask] : List (Prog isa)))))) (Two fun (_ : CvP) (_ : State) => True) := by
  have k8 : ∀ {k l : Nat}, l < k → l ≤ 8 * wk k := fun {k l} h => by unfold wk; omega
  refine (ct_app (by simp [storeA]) (by simp [storeA])
    (storeA_ct (by decide) (by decide) (by decide) CvP.pQi CvP.pl (fun p s h => ?_) (by taint_decide)
      (by taint_decide))
    (ct_app (by simp [storeA]) (by simp [storeA])
      (storeA_ct (by decide) (by decide) (by decide) CvP.pDp CvP.pl (fun p s h => ?_) (by taint_decide)
        (by taint_decide))
      (ct_app (by simp [storeA]) (by simp)
        (storeA_ct (by decide) (by decide) (by decide) CvP.pDq CvP.ql (fun p s h => ?_) (by taint_decide)
          (by taint_decide))
        (ct_one (Ψ := fun (_ : CvP) (_ : State) => True) (two_post retMask_ct fun _ _ h => by
          obtain ⟨I, c, rfl, hw, -, -, -, -, hm⟩ := h
          exact WP.mono (cvExit_ok hw hm) fun _ _ => trivial)))))
  all_goals
    obtain ⟨I, c, rfl, -, ha, -, L, O, -⟩ := h
    dsimp only [CvIn.pub]
  · exact ⟨ha.qi, ha.pl, O.qi, O.sqi, L.pl1, k8 L.pl2⟩
  · exact ⟨ha.dp, ha.pl, O.dp, O.sdp, L.pl1, k8 L.pl2⟩
  · exact ⟨ha.dq, ha.ql, O.dq, O.sdq, L.ql1, k8 L.ql2⟩

end VG.Proof.Rsa.AArch64
