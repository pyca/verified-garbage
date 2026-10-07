import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTBase
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Tail
import VerifiedGarbage.Proof.Rsa.AArch64.CvCTCode

/-!
# An RSA key from its primes on AArch64: constant time, the outputs

The zeros and the stores take each output's pointer and length from the
header, which correctness pins to the public data (`zeroOutK_ct`,
`storeAK_ct`), and leave the header and the working space as they were
(`EG`: from the stores on, memory outside the working space changes, so
`KS` no longer holds); the exit reads the header.
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- From the outputs on: the header and the working space of some inputs
with the public data `p`, with the facts `M`. -/
def EG (M : KIn → State → Prop) (p : KP) (s : State) : Prop :=
  ∃ I, I.pub = p.q ∧ Ws s I.B I.Z I.W ∧ KArgs s.mem I ∧ s.wr = I.Wr ∧ KLens I ∧ KOuts I ∧ M I s

theorem pins_EG (M : KIn → State → Prop) : Pins (EG M) [.x0] := fun _ _ _ ⟨_, e₁, w₁, _⟩ ⟨_, e₂, w₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [w₁.x0, w₂.x0]
  exact (congrArg KQ.B e₁).trans (congrArg KQ.B e₂).symm

theorem EG.of_kg {M : KIn → State → Prop} {p : KP} {s : State} (h : KG M p s) : EG M p s :=
  let ⟨I, _, he, _, hk, L, O, hM⟩ := h
  ⟨I, he, hk.ws, hk.args, hk.wr, L, O, hM⟩

/-- Where an output is, in the header. -/
abbrev OutHdr (sPtr sLen : Nat) (ptr : KQ → Addr) (len : KQ → Nat) : Prop :=
  ∀ I (m : Mem), KArgs m I → KLens I → word m I.B (8 * sPtr) = ptr I.pub ∧
    word m I.B (8 * sLen) = BitVec.ofNat 64 (len I.pub) ∧ (ptr I.pub, len I.pub) ∈ outsL I ∧ 1 ≤ len I.pub ∧
    len I.pub ≤ 8 * I.W

/-- Facts of the header. -/
abbrev HdrStab (M : KIn → State → Prop) : Prop :=
  ∀ I s t, M I s → (∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i)) → M I t

/-- `EG`'s parts after a change outside the working space. -/
theorem EG.after {M : KIn → State → Prop} (hM : HdrStab M) {I : KIn} {s t : State} (hw : Ws s I.B I.Z I.W)
    (ha : KArgs s.mem I) (hW : s.wr = I.Wr) (hm : M I s) (hf : Frm I.B [(I.Z, 2 ^ 64)] s.mem t.mem)
    {rs : List Reg} (k : Keep rs s t) (hr : .x0 ∉ rs) :
    Ws t I.B I.Z I.W ∧ KArgs t.mem I ∧ t.wr = I.Wr ∧ M I t := by
  have h256 := hw.h256
  have fw : ∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i) := fun i hi => frm_word hf h256 hi
  exact ⟨hw.congr hf (fun r hr' => by rw [List.mem_singleton.mp hr']; exact Or.inl (by omega)) k hr,
    ha.congr fun i hi => fw i (by omega), k.wr.trans hW, hM I s t hm fw⟩

theorem zeroOutK_ct {M : KIn → State → Prop} (hM : HdrStab M) {sPtr sLen : Nat} (hP : sPtr < 32) (hL : sLen < 32)
    (ptr : KQ → Addr) (len : KQ → Nat) (hA : OutHdr sPtr sLen ptr len) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x1 sPtr, ldh .x2 sLen, movi .x3 0]) hc).isSome = true) :
    RelCT isa (Two (EG M)) (zeroOut sPtr sLen) (Two (EG M)) :=
  pin_ct [.x0] [.x1, .x2] (fun p : KP => zoVal (ptr p.q) (len p.q)) (pins_EG M) ht
    (fun p s h => by
      obtain ⟨I, he, hw, ha, -, L, -⟩ := h
      obtain ⟨hp, hl, -⟩ := hA I s.mem ha L
      rw [he] at hp hl
      have hn := hw.scr.nowrap
      have h256 := hw.h256
      have hl' : ∀ i < 32, InRegions (s.rd ++ s.wr) (off I.B (8 * i)) 8 := fun i hi => hw.scr.ld (by omega)
      refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = ptr p.q ∧
        t.gpr .x2 = BitVec.ofNat 64 (len p.q)) (by
        brun [hw.x0, hdr_enc hP, hdr_enc hL, hl' sPtr hP, hl' sLen hL]
        exact ⟨hp, hl⟩) rfl rfl rfl) fun t ⟨⟨h1, h2⟩, _⟩ r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h2)
    (by taint_decide) fun p s h => by
      obtain ⟨I, he, hw, ha, hW, L, O, hm⟩ := h
      obtain ⟨hp, hl, ho, hl1, hlw⟩ := hA I s.mem ha L
      have hw2 := hw.w2
      refine WP.mono (zeroOut_ok hw.scr hw.x0 hw.h256 hP hL hp hl hl1 (by omega)
        ⟨fun i hi => by rw [hW]; exact O.wr _ ho i hi, O.sep _ ho⟩) fun t ⟨_, hx, k⟩ => ?_
      obtain ⟨a, b, c, d⟩ := EG.after hM hw ha hW hm (frm_scr (O.sep _ ho) hx) k (by decide)
      exact ⟨I, he, a, b, c, L, O, d⟩

/-- The block before `storeBE`, with `kOk` the mask (`storeBlk_ok`). -/
theorem storeBlkK_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j sPtr sLen len : Nat} {ptr : Addr}
    (hP : sPtr < 32) (hL : sLen < 32) (hp : word s.mem B (8 * sPtr) = ptr)
    (hl : word s.mem B (8 * sLen) = BitVec.ofNat 64 len) :
    WP isa (.block (ws ++ base j .x8 ++ ([ldh .x1 sPtr, ldh .x9 sLen, .add .x .x1 .x1 .x9, ldh .x15 kOk] :
      List Instr))) s fun t => ∀ r ∈ [Reg.x0, .x8, .x1, .x9], t.gpr r = soVal B (off B (slot w j)) ptr len r := by
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨⟨_, h11, m₂, _⟩, k₂⟩ =>
    WP.mono (base_ok j .x8 ((k₂.gpr .x0 (by decide)).trans h.x0) h11) fun s₃ ⟨⟨h8, m₃, _⟩, k₃⟩ =>
      WP.mono (WP.keep [.x1, .x9, .x15] (Q := fun t => t.gpr .x1 = ptr + BitVec.ofNat 64 len ∧
          t.gpr .x9 = BitVec.ofNat 64 len) (by
          have h0₃ : s₃.gpr .x0 = B := ((k₂.trans k₃).gpr .x0 (by decide)).trans h.x0
          have hs₃ := h.scr.congr (k₂.trans k₃).wr
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega)
          brun [h0₃, hdr_enc hP, hdr_enc hL, hdr_enc (show kOk < 32 by decide), m₃, m₂, hl₃ sPtr hP,
            hl₃ sLen hL, hl₃ kOk (by decide), hp, hl])
        rfl rfl rfl)
      fun t ⟨⟨h1, h9⟩, k₄⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (((k₂.trans k₃).trans k₄).gpr .x0 (by decide)).trans h.x0
        · exact (k₄.gpr .x8 (by decide)).trans h8
        · exact h1
        · exact h9))

theorem stab_hdr_kok : HdrStab KokM := fun _ _ _ ⟨c, h⟩ fw => ⟨c, (fw _ (by decide)).trans h⟩

theorem storeA_eq (j sPtr sLen : Nat) : seqs (storeA j sPtr sLen kOk) = .seq (.block (ws ++ base j .x8 ++
    ([ldh .x1 sPtr, ldh .x9 sLen, .add .x .x1 .x1 .x9, ldh .x15 kOk] : List Instr))) storeBE := rfl

theorem storeAK_ct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : KQ → Addr)
    (len : KQ → Nat) (hA : OutHdr sPtr sLen ptr len) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base j .x8 ++
      ([ldh .x1 sPtr, ldh .x9 sLen, .add .x .x1 .x1 .x9, ldh .x15 kOk] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (EG KokM)) (seqs (storeA j sPtr sLen kOk)) (Two (EG KokM)) := by
  rw [storeA_eq]
  refine pin_ct [.x0] [.x0, .x8, .x1, .x9]
    (fun p : KP => soVal p.q.B (off p.q.B (slot p.q.W j)) (ptr p.q) (len p.q)) (pins_EG KokM) ht
    (fun p s h => by
      obtain ⟨I, he, hw, ha, -, L, -⟩ := h
      obtain ⟨hp, hl, -⟩ := hA I s.mem ha L
      rw [← he]
      exact storeBlkK_ok hw hP hL hp hl) (by taint_decide) fun p s h => ?_
  rw [← storeA_eq]
  obtain ⟨I, he, hw, ha, hW, L, O, c, hm⟩ := h
  obtain ⟨hp, hl, ho, hl1, hlw⟩ := hA I s.mem ha L
  refine WP.mono (storeK_ws hw hj hP hL hp hl hm hl1 hlw (fun i hi => by rw [hW]; exact O.wr _ ho i hi)
    (O.sep _ ho)) fun t ⟨_, _, ht, hf, k⟩ => ?_
  have h256 := hw.h256
  have fw : ∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i) := fun i hi => frm_word hf h256 hi
  exact ⟨I, he, ht, ha.congr fun i hi => fw i (by omega), k.wr.trans hW, L, O, c, (fw _ (by decide)).trans hm⟩

/-! ## The outputs' places -/

theorem outN : OutHdr kNo kNl KQ.pN (fun q => 2 * q.pl) := fun I _ ha L =>
  ⟨ha.no, ha.nl, by simp [outsL, KIn.pub], by have := L.pl1; simp only [KIn.pub]; omega,
    by simp only [KIn.pub]; rw [L.W]; have := L.pl8; omega⟩

theorem outD : OutHdr kDo kNl KQ.pD (fun q => 2 * q.pl) := fun I _ ha L =>
  ⟨ha.dd, ha.nl, by simp [outsL, KIn.pub], by have := L.pl1; simp only [KIn.pub]; omega,
    by simp only [KIn.pub]; rw [L.W]; have := L.pl8; omega⟩

theorem outP : OutHdr kPp kPl KQ.pP KQ.pl := fun I _ ha L =>
  ⟨ha.pp, ha.pl, by simp [outsL, KIn.pub], by have := L.pl1; simp only [KIn.pub]; omega,
    by simp only [KIn.pub]; rw [L.W]; have := L.pl8; omega⟩

theorem outQ : OutHdr kQp kPl KQ.pQ KQ.pl := fun I _ ha L =>
  ⟨ha.qp, ha.pl, by simp [outsL, KIn.pub], by have := L.pl1; simp only [KIn.pub]; omega,
    by simp only [KIn.pub]; rw [L.W]; have := L.pl8; omega⟩

theorem outDp : OutHdr kDp kPl KQ.pDp KQ.pl := fun I _ ha L =>
  ⟨ha.dp, ha.pl, by simp [outsL, KIn.pub], by have := L.pl1; simp only [KIn.pub]; omega,
    by simp only [KIn.pub]; rw [L.W]; have := L.pl8; omega⟩

theorem outDq : OutHdr kDq kPl KQ.pDq KQ.pl := fun I _ ha L =>
  ⟨ha.dq, ha.pl, by simp [outsL, KIn.pub], by have := L.pl1; simp only [KIn.pub]; omega,
    by simp only [KIn.pub]; rw [L.W]; have := L.pl8; omega⟩

theorem outQi : OutHdr kQi kPl KQ.pQi KQ.pl := fun I _ ha L =>
  ⟨ha.qi, ha.pl, by simp [outsL, KIn.pub], by have := L.pl1; simp only [KIn.pub]; omega,
    by simp only [KIn.pub]; rw [L.W]; have := L.pl8; omega⟩

/-! ## The zeros and the stores -/

theorem zeros2_ct : RelCT isa (Two (EG NF)) (zeros 2) fun _ _ => True := by
  have hM : HdrStab NF := fun _ _ _ _ _ => trivial
  unfold zeros
  simp only [seqs]
  exact RelCT.seq (zeroOutK_ct hM (by decide) (by decide) _ _ outN (by taint_decide))
    (RelCT.seq (zeroOutK_ct hM (by decide) (by decide) _ _ outD (by taint_decide))
    (RelCT.seq (zeroOutK_ct hM (by decide) (by decide) _ _ outP (by taint_decide))
    (RelCT.seq (zeroOutK_ct hM (by decide) (by decide) _ _ outQ (by taint_decide))
    (RelCT.seq (zeroOutK_ct hM (by decide) (by decide) _ _ outDp (by taint_decide))
    (RelCT.seq (zeroOutK_ct hM (by decide) (by decide) _ _ outDq (by taint_decide))
    (RelCT.seq (zeroOutK_ct hM (by decide) (by decide) _ _ outQi (by taint_decide))
      (two_taint [.x0] (pins_EG NF) (by taint_decide))))))))

theorem outputs_eq2 : outputs = storeA aQt kNo kNl kOk ++ (storeA aDd kDo kNl kOk ++ (storeA aPa kPp kPl kOk ++
    (storeA aQa kQp kPl kOk ++ (storeA aX₁ kDp kPl kOk ++ (storeA aV kDq kPl kOk ++ (storeA aX₂ kQi kPl kOk ++
    ([.block retOk] : List (Prog isa)))))))) := by
  simp only [outputs, List.append_assoc]

theorem outputs_ct : RelCT isa (Two (EG KokM)) (seqs outputs) fun _ _ => True := by
  rw [outputs_eq2]
  refine rs_app (by simp [storeA]) (by simp [storeA]) (storeAK_ct (by decide) (by decide) (by decide) _ _ outN
    (by taint_decide)) ?_
  refine rs_app (by simp [storeA]) (by simp [storeA]) (storeAK_ct (by decide) (by decide) (by decide) _ _ outD
    (by taint_decide)) ?_
  refine rs_app (by simp [storeA]) (by simp [storeA]) (storeAK_ct (by decide) (by decide) (by decide) _ _ outP
    (by taint_decide)) ?_
  refine rs_app (by simp [storeA]) (by simp [storeA]) (storeAK_ct (by decide) (by decide) (by decide) _ _ outQ
    (by taint_decide)) ?_
  refine rs_app (by simp [storeA]) (by simp [storeA]) (storeAK_ct (by decide) (by decide) (by decide) _ _ outDp
    (by taint_decide)) ?_
  refine rs_app (by simp [storeA]) (by simp [storeA]) (storeAK_ct (by decide) (by decide) (by decide) _ _ outDq
    (by taint_decide)) ?_
  refine rs_app (by simp [storeA]) (by simp) (storeAK_ct (by decide) (by decide) (by decide) _ _ outQi
    (by taint_decide)) ?_
  exact two_taint [.x0] (pins_EG KokM) (by taint_decide)

end VG.Proof.RsaKeyGen.AArch64.Key
