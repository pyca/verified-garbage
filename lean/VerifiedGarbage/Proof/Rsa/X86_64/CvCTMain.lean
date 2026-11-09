module

public import VerifiedGarbage.Proof.Rsa.X86_64.CvCT
public import VerifiedGarbage.Proof.Rsa.X86_64.CvMain
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
/-!
# `vg_rsa_crt_values` on x86-64: constant time, `main`

The pieces of `CvCT.lean` in sequence (`loads_ct`, `pqCheck_ct`,
`divs_ct`), the stores (`stores_ct`, from `GS`); `invPart_ct` and `main`
(`cvMain_ct`) are in `CvCTInv.lean`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
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
    (hA : ∀ p s, GA p s → Bignum.word s.mem p.B (8 * sPtr) = ptr p ∧
      Bignum.word s.mem p.B (8 * sLen) = BitVec.ofNat 64 (len p) ∧
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

/-- A cleared product accumulator, for the multiplication. -/
def GZ (p : CvP) (s : State) : Prop :=
  GA p s ∧ wv s.mem p.B (slot (wk p.k) aU) (2 * wk p.k + 2) = 0

/-- Array-only changes to the two contiguous product slots preserve `GA`. -/
theorem GA.product {p : CvP} {s t : State} (h : GA p s)
    (ho : Outside p.B (slot (wk p.k) aU) (8 * (2 * wk p.k + 2)) s.mem t.mem)
    {rs : List Reg} (hk : Keep rs s t) (hr : .rdi ∉ rs ∧ .rsp ∉ rs) : GA p t := by
  obtain ⟨I, m₀, c, rfl, h, L, O, hm⟩ := h
  refine ⟨I, m₀, c, rfl, h.product ho hk hr, L, O, ?_⟩
  change Outside I.B (slot (wk I.k) aU) (8 * (2 * wk I.k + 2)) s.mem t.mem at ho
  rw [mword_out ho, hm]

/-- The product's zeroing uses only the public workspace dimensions. -/
theorem productZero_ct : RelCT isa (Two GA) (seqs Impl.Rsa.X86_64.Crt.zeroAccs) (Two GZ) := by
  refine two_post (two_map (fun p : CvP => (⟨p.B, p.Z, wk p.k⟩ : VG.Proof.Bignum.X86_64.Ws))
    (fun _ _ h => ⟨_, h.ws.good⟩) zeroAccs_ct) fun p s h => ?_
  have hw := h.ws.w2
  exact WP.mono (zeroAccs_ok h.ws.good.1 h.ws.good.2 (by omega)) fun t ⟨hz, ho, hk⟩ =>
    ⟨h.product ho hk (by decide), wv_zero hz⟩

/-- The multiplication is checked after pinning its width and array bases. -/
theorem product_ct : RelCT isa (Two GZ)
    (.seq (.block productSetup) Impl.Rsa.X86_64.Crt.mulRows) (Two GA) := by
  unfold productSetup
  simp only [List.append_assoc]
  refine ws_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.1.ws) (by taint_decide) fun p s h => ?_
  exact WP.mono (product_ok h.1.ws h.2) fun t ⟨_, ho, hk⟩ => h.1.product ho hk (by decide)

/-- The public registers the full-product comparison reads. -/
def ProductEq (p : CvP) (s : State) : Prop :=
  s.gpr .rdi = p.B ∧ s.gpr .r12 = BitVec.ofNat 64 (wk p.k) ∧
  s.gpr .rbx = off p.B (slot (wk p.k) aU) ∧ s.gpr .r10 = off p.B (slot (wk p.k) aN)

theorem productEq_ct : RelCT isa (Two GA) (seqs Impl.Rsa.X86_64.Crt.eqCheck) fun _ _ => True := by
  unfold Impl.Rsa.X86_64.Crt.eqCheck
  simp only [seqs, show Impl.Bignum.X86_64.Public.aAcc = aU from rfl]
  refine RelCT.seq (two_piece (Ψ := ProductEq) [.rdi] pins_GA (by taint_decide) fun p s h => ?_)
    (two_taint [.rdi, .r12, .rbx, .r10] (pins_of (fun (p : CvP) r => if r = .rdi then p.B else
      if r = .r12 then BitVec.ofNat 64 (wk p.k) else if r = .rbx then off p.B (slot (wk p.k) aU) else
      off p.B (slot (wk p.k) aN)) fun _ _ h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2) (by taint_decide))
  have hw := h.ws
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8 := fun i hi =>
    hw.scr.ld (by have := hw.h256; omega)
  exact WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t =>
    t.gpr .r12 = BitVec.ofNat 64 (wk p.k) ∧ t.gpr .rbx = off p.B (slot (wk p.k) aU) ∧
    t.gpr .r10 = off p.B (slot (wk p.k) aN)) (by
      xrun [State.ea, hdr, hw.rdi, hdrOff, hl sW (by decide), hl (sArr aU) (by decide),
        hl (sArr aN) (by decide), hw.hw, hw.harr aU (by decide), hw.harr aN (by decide)]) rfl)
    fun t ⟨ht, hk⟩ => ⟨(hk.gpr (by decide)).trans hw.rdi, ht⟩

theorem pqCheck_ct : RelCT isa (Two GA) (seqs pqCheck) (Two GA) := by
  refine two_post ?_ fun p s h => ?_
  · unfold pqCheck
    rw [List.append_assoc]
    exact RelCT.seqs_append (by simp [Impl.Rsa.X86_64.Crt.zeroAccs]) (by simp)
      (RelCT.seq productZero_ct (by
        change RelCT isa (Two GZ) (.seq (.block productSetup) (.seq Impl.Rsa.X86_64.Crt.mulRows
          (seqs Impl.Rsa.X86_64.Crt.eqCheck))) _
        exact RelCT.assoc (RelCT.seq product_ct productEq_ct)))
  · obtain ⟨I, m₀, c, rfl, h, L, O, hm⟩ := h
    exact WP.mono (cvCheck_ok h L hm) fun t ⟨ht, hmt, _⟩ => ⟨I, m₀, _, rfl, ht, L, O, hmt⟩

theorem divisor_ct {j : Nat} (hj : j < 16) (hjC : aC ≠ j) {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .rsi ++ base aC .rbx)) copyWords)
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
    CvArgs s.mem I.B I.k I.pl I.ql I.dl I.pDp I.pDq I.pQi I.pN I.pP I.pQ I.pD I.sv ∧ s.wr = I.W ∧ CvLens I ∧
    CvOuts I ∧ mword s.mem I.B = mask c

theorem GS.ws {p : CvP} {s : State} (h : GS p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨I, c, rfl, h, -⟩ := h
  exact h

theorem GA.gs {p : CvP} {s : State} (h : GA p s) : GS p s := by
  obtain ⟨I, m₀, c, rfl, h, L, O, hm⟩ := h
  exact ⟨I, c, rfl, h.ws, h.args, h.wr, L, O, hm⟩

theorem pins_GS : Pins GS [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]

/-- The block before `storeBE`: the base of `[j]`, the pointer, the length
and the mask. -/
theorem storeBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j sPtr sLen len : Nat} {ptr : Addr}
    (hP : sPtr < 32) (hL : sLen < 32) (hp : Bignum.word s.mem B (8 * sPtr) = ptr)
    (hl : Bignum.word s.mem B (8 * sLen) = BitVec.ofNat 64 len) :
    WP isa (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)), .mov .rcx (.mem (hdr sLen)),
      .mov .r15 (.mem (hdr Impl.Bignum.X86_64.Public.sMask))] : List Instr)))
      s fun t => t.gpr .rbx = off B (slot w j) ∧ t.gpr .rsi = ptr ∧ t.gpr .rcx = BitVec.ofNat 64 len ∧
        t.gpr .rdi = B := by
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨_, h9, m₂, k₂⟩ =>
    WP.mono (base_ok j (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h.rdi) h9) fun s₃ ⟨hbx, m₃, k₃⟩ =>
      WP.mono (WP.keep [.rsi, .rcx, .r15] (Q := fun t => t.gpr .rsi = ptr ∧ t.gpr .rcx = BitVec.ofNat 64 len) (by
          have hdi₃ : s₃.gpr .rdi = B := ((k₂.trans k₃).gpr (by decide)).trans h.rdi
          have hs₃ := h.scr.congr (k₂.trans k₃).2.2
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega)
          xrun [State.ea, hdr, hdi₃, hdrOff, m₃, m₂, hl₃ sPtr hP, hl₃ sLen hL,
            hl₃ Impl.Bignum.X86_64.Public.sMask (by decide), hp, hl]) rfl)
      fun _ ⟨⟨hsi, hcx⟩, k₄⟩ => ⟨(k₄.gpr (by decide)).trans hbx, hsi, hcx,
        ((k₂.trans k₃).trans k₄ |>.gpr (by decide)).trans h.rdi⟩))

theorem storeA_ct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : CvP → Addr)
    (len : CvP → Nat)
    (hA : ∀ p s, GS p s → Bignum.word s.mem p.B (8 * sPtr) = ptr p ∧
      Bignum.word s.mem p.B (8 * sLen) = BitVec.ofNat 64 (len p) ∧
      (∀ i < len p, InRegions p.W (ptr p + BitVec.ofNat 64 i) 1) ∧
      (∀ i < len p, p.Z ≤ ofs p.B (ptr p + BitVec.ofNat 64 i)) ∧ 1 ≤ len p ∧ len p ≤ 8 * wk p.k)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr sLen)), .mov .r15 (.mem (hdr Impl.Bignum.X86_64.Public.sMask))] : List Instr))) hc).isSome
      = true) :
    RelCT isa (Two GS) (seqs (storeA j sPtr sLen Impl.Bignum.X86_64.Public.sMask)) (Two GS) :=
  pin_ct [.rdi] [.rdi, .rbx, .rsi, .rcx] (fun p => ioVal p.B (off p.B (slot (wk p.k) j)) (ptr p) (len p)) pins_GS ht
    (fun p s h => by
      obtain ⟨hp, hl, -⟩ := hA p s h
      exact WP.mono (storeBlk_ok h.ws hP hL hp hl) fun t ⟨hbx, hsi, hcx, hdi⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdi
        · exact hbx
        · exact hsi
        · exact hcx)
    (by taint_decide) fun p s h => by
      obtain ⟨hp, hl, hwr, hsep, hl1, hlw⟩ := hA p s h
      obtain ⟨I, c, rfl, hw, ha, hW, L, O, hm⟩ := h
      dsimp only [CvIn.pub] at hp hl hwr hsep hl1 hlw ⊢
      have hn := hw.scr.nowrap
      have h256 := hw.h256
      refine WP.mono (storeA_ws hw hj hP hL hp hl hm hl1 hlw (fun i hi => by rw [hW]; exact hwr i hi) hsep)
        fun t ⟨_, _, ht, hf, k⟩ => ?_
      have fw : ∀ i < 32, Bignum.word t.mem I.B (8 * i) = Bignum.word s.mem I.B (8 * i) :=
        fun i hi => hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)
      exact ⟨I, c, rfl, ht, ha.congr fun i hi => fw i (by unfold argSlot at hi; omega), k.2.2.trans hW, L, O,
        (fw _ (by decide)).trans hm⟩

theorem retMask_ct : RelCT isa (Two GS) (.block retMask) fun _ _ => True :=
  two_taint [.rdi] pins_GS (by taint_decide)

/-- The stores and the exit. -/
theorem stores_ct : RelCT isa (Two GS) (seqs (storeA aX₂ sQi sPl Impl.Bignum.X86_64.Public.sMask ++
    (storeA aX₁ sDp sPl Impl.Bignum.X86_64.Public.sMask ++ (storeA aV sDq sQl Impl.Bignum.X86_64.Public.sMask ++
      ([.block retMask] : List (Prog isa)))))) (Two fun (_ : CvP) (_ : State) => True) := by
  have k8 : ∀ {k l : Nat}, l < k → l ≤ 8 * wk k := fun {k l} h => by unfold wk; omega
  refine (ct_app (by simp [storeA]) (by simp [storeA])
    (storeA_ct (by decide) (by decide) (by decide) CvP.pQi CvP.pl (fun p s h => ?_) (by taint_decide))
    (ct_app (by simp [storeA]) (by simp [storeA])
      (storeA_ct (by decide) (by decide) (by decide) CvP.pDp CvP.pl (fun p s h => ?_) (by taint_decide))
      (ct_app (by simp [storeA]) (by simp)
        (storeA_ct (by decide) (by decide) (by decide) CvP.pDq CvP.ql (fun p s h => ?_) (by taint_decide))
        (ct_one (Ψ := fun (_ : CvP) (_ : State) => True)
          (retMask_ct.mono (fun _ _ h => h) fun _ _ _ => ⟨default, trivial, trivial⟩)))))
  all_goals
    obtain ⟨I, c, rfl, -, ha, -, L, O, -⟩ := h
    dsimp only [CvIn.pub]
  · exact ⟨ha.qi, ha.pl, O.qi, O.sqi, L.pl1, k8 L.pl2⟩
  · exact ⟨ha.dp, ha.pl, O.dp, O.sdp, L.pl1, k8 L.pl2⟩
  · exact ⟨ha.dq, ha.ql, O.dq, O.sdq, L.ql1, k8 L.ql2⟩

/-! ## `main` -/

/-- On entry to `main`. -/
def GM (p : CvP) (s : State) : Prop := ∃ I : CvIn, I.pub = p ∧ CvPre I s

theorem pins_GM : Pins GM [.rdi] := fun _ _ _ ⟨_, e₁, h₁⟩ ⟨_, e₂, h₂⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁.rdi, h₂.rdi]
  exact (congrArg CvP.B e₁).trans (congrArg CvP.B e₂).symm

theorem CvPre.outs {I : CvIn} {s : State} (h : CvPre I s) : CvOuts I :=
  ⟨fun i hi => by rw [← h.wr]; exact h.oQi.wr i hi, fun i hi => by rw [← h.wr]; exact h.oDp.wr i hi,
    fun i hi => by rw [← h.wr]; exact h.oDq.wr i hi, h.oQi.sep, h.oDp.sep, h.oDq.sep, h.a1, h.a2, h.a3⟩

theorem head_ct : RelCT isa (Two GM) (.block head) (Two GA) :=
  two_piece [.rdi] pins_GM (by taint_decide) fun _ s ⟨I, e, h⟩ =>
    WP.mono (cvHeadS_ok h) fun _ ⟨ht, hm⟩ => ⟨I, s.mem, true, e, ht, h.L, h.outs, hm⟩

end VG.Proof.Rsa.X86_64
