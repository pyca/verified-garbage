import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.CTTail

/-!
# An RSA key from its primes on x86-64: constant time, the outputs

The zeros and the stores take each output's pointer and length from the
header, which correctness pins to the public data (`zeroOutK_ct`,
`storeAK_ct`), and leave the header and the working space as they were
(`EG`); the exit reads the header.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64.Public (exit)

/-- From the outputs on: the header and the working space of some inputs
with the public data `p`, with the facts `M`. -/
def EG (M : KIn → State → Prop) (p : KP) (s : State) : Prop :=
  ∃ I, I.pub = p.q ∧ Ws s I.B I.Z I.W ∧ KArgs s.mem I ∧ s.wr = I.Wr ∧ KLens I ∧ KOuts I ∧ M I s

theorem pins_EG (M : KIn → State → Prop) : Pins (EG M) [.rdi] := fun _ _ _ ⟨I₁, e₁, w₁, _⟩ ⟨I₂, e₂, w₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [w₁.rdi, w₂.rdi]
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

theorem EG.after {M : KIn → State → Prop} (hM : HdrStab M) {I : KIn} {s t : State} (hw : Ws s I.B I.Z I.W)
    (ha : KArgs s.mem I) (hW : s.wr = I.Wr) (hm : M I s) (hf : Frm I.B [(I.Z, 2 ^ 64)] s.mem t.mem) {rs : List Reg}
    (k : Keep rs s t) (hr : .rdi ∉ rs) :
    Ws t I.B I.Z I.W ∧ KArgs t.mem I ∧ t.wr = I.Wr ∧ M I t := by
  have h256 := hw.h256
  have fw : ∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i) := fun i hi => frm_word hf h256 hi
  exact ⟨hw.congr hf (fun r hr' => by rw [List.mem_singleton.mp hr']; exact Or.inl (by omega)) k hr,
    ha.congr fun i hi => fw i (by omega), k.2.2.trans hW, hM I s t hm fw⟩

/-- `zeroOut`'s loop's registers. -/
def zoVal (ptr : Addr) (len : Nat) : Reg → BitVec 64
  | .rsi => ptr
  | .rcx => BitVec.ofNat 64 len
  | _ => 0

theorem zeroOutK_ct {M : KIn → State → Prop} (hM : HdrStab M) {sPtr sLen : Nat} (hP : sPtr < 32) (hL : sLen < 32)
    (ptr : KQ → Addr) (len : KQ → Nat) (hA : OutHdr sPtr sLen ptr len) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rsi (.mem (hdr sPtr)), .mov .rcx (.mem (hdr sLen)),
      .mov32 .rax (.imm 0)]) hc).isSome = true) :
    RelCT isa (Two (EG M)) (zeroOut sPtr sLen) (Two (EG M)) :=
  pin_ct [.rdi] [.rsi, .rcx] (fun p : KP => zoVal (ptr p.q) (len p.q)) (pins_EG M) ht
    (fun p s h => by
      obtain ⟨I, he, hw, ha, -, L, -⟩ := h
      obtain ⟨hp, hl, -⟩ := hA I s.mem ha L
      rw [he] at hp hl
      have hl' : ∀ i < 32, InRegions (s.rd ++ s.wr) (off I.B (8 * i)) 8 := fun i hi =>
        hw.scr.ld (by have := hw.h256; omega)
      refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = ptr p.q ∧
        t.gpr .rcx = BitVec.ofNat 64 (len p.q)) (by
        xrun [State.ea, hdr, hw.rdi, hdrOff, hl' sPtr hP, hl' sLen hL]
        exact ⟨hp, hl⟩) rfl) fun t ⟨⟨h1, h2⟩, _⟩ r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h2)
    (by taint_decide) fun p s h => by
      obtain ⟨I, he, hw, ha, hW, L, O, hm⟩ := h
      obtain ⟨hp, hl, ho, hl1, hlw⟩ := hA I s.mem ha L
      have hw2 := hw.w2
      refine WP.mono (zeroOut_ok hw.scr hw.rdi hw.h256 hP hL hp hl hl1 (by omega)
        ⟨fun i hi => by rw [hW]; exact O.wr _ ho i hi, O.sep _ ho⟩) fun t ⟨_, hx, k⟩ => ?_
      obtain ⟨a, b, c, d⟩ := EG.after hM hw ha hW hm (frm_scr (O.sep _ ho) hx) k (by decide)
      exact ⟨I, he, a, b, c, L, O, d⟩

/-- The block before `storeBE`, with `kOk` the mask. -/
theorem storeBlkK_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j sPtr sLen len : Nat} {ptr : Addr}
    (hP : sPtr < 32) (hL : sLen < 32) (hp : word s.mem B (8 * sPtr) = ptr)
    (hl : word s.mem B (8 * sLen) = BitVec.ofNat 64 len) :
    WP isa (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)), .mov .rcx (.mem (hdr sLen)),
      .mov .r15 (.mem (hdr kOk))] : List Instr)))
      s fun t => t.gpr .rbx = off B (slot w j) ∧ t.gpr .rsi = ptr ∧ t.gpr .rcx = BitVec.ofNat 64 len ∧
        t.gpr .rdi = B := by
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨_, h9, m₂, k₂⟩ =>
    WP.mono (base_ok j (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h.rdi) h9) fun s₃ ⟨hbx, m₃, k₃⟩ =>
      WP.mono (WP.keep [.rsi, .rcx, .r15] (Q := fun t => t.gpr .rsi = ptr ∧ t.gpr .rcx = BitVec.ofNat 64 len) (by
          have hdi₃ : s₃.gpr .rdi = B := ((k₂.trans k₃).gpr (by decide)).trans h.rdi
          have hs₃ := h.scr.congr (k₂.trans k₃).2.2
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega)
          xrun [State.ea, hdr, hdi₃, hdrOff, m₃, m₂, hl₃ sPtr hP, hl₃ sLen hL, hl₃ kOk (by decide), hp, hl]) rfl)
      fun _ ⟨⟨hsi, hcx⟩, k₄⟩ => ⟨(k₄.gpr (by decide)).trans hbx, hsi, hcx,
        ((k₂.trans k₃).trans k₄ |>.gpr (by decide)).trans h.rdi⟩))

theorem stab_hdr_kok : HdrStab KokM := fun _ _ _ ⟨c, h⟩ fw => ⟨c, (fw _ (by decide)).trans h⟩

theorem storeAK_ct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : KQ → Addr)
    (len : KQ → Nat) (hA : OutHdr sPtr sLen ptr len) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr sLen)), .mov .r15 (.mem (hdr kOk))] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (EG KokM)) (seqs (storeA j sPtr sLen kOk)) (Two (EG KokM)) :=
  pin_ct [.rdi] [.rdi, .rbx, .rsi, .rcx]
    (fun p : KP => ioVal p.q.B (off p.q.B (slot (2 * p.q.pl / 8) j)) (ptr p.q) (len p.q)) (pins_EG KokM) ht
    (fun p s h => by
      obtain ⟨I, he, hw, ha, -, L, -⟩ := h
      obtain ⟨hp, hl, -⟩ := hA I s.mem ha L
      rw [← he]
      exact WP.mono (storeBlkK_ok hw hP hL hp hl) fun t ⟨hbx, hsi, hcx, hdi⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdi
        · exact hbx
        · exact hsi
        · exact hcx)
    (by taint_decide) fun p s h => by
      obtain ⟨I, he, hw, ha, hW, L, O, c, hm⟩ := h
      obtain ⟨hp, hl, ho, hl1, hlw⟩ := hA I s.mem ha L
      refine WP.mono (storeK_ws hw hj hP hL hp hl hm hl1 hlw (fun i hi => by rw [hW]; exact O.wr _ ho i hi)
        (O.sep _ ho)) fun t ⟨_, _, ht, hf, k⟩ => ?_
      have h256 := hw.h256
      have fw : ∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i) := fun i hi => frm_word hf h256 hi
      exact ⟨I, he, ht, ha.congr fun i hi => fw i (by omega), k.2.2.trans hW, L, O, c, (fw _ (by decide)).trans hm⟩

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

theorem zeros_ct : RelCT isa (Two (EG NF)) (zeros 2) fun _ _ => True := by
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
      (two_taint [.rdi] (pins_EG NF) (by taint_decide))))))))

theorem outputs_eq2 : outputs = storeA aQt kNo kNl kOk ++ (storeA aDd kDo kNl kOk ++ (storeA aPa kPp kPl kOk ++
    (storeA aQa kQp kPl kOk ++ (storeA aX₁ kDp kPl kOk ++ (storeA aV kDq kPl kOk ++ (storeA aX₂ kQi kPl kOk ++
    ([.block (([.mov .rax (.mem (hdr kOk)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)] : List (Prog isa)))))))) := by
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
  exact two_taint [.rdi] (pins_EG KokM) (by taint_decide)

/-- `keyPart`, from a mask in `kOk`. -/
theorem keyPart_ct : RelCT isa (Two (KG fun I t => NF I t ∧ KokM I t)) keyPart fun _ _ => True := by
  rw [keyPart]
  simp only [List.append_assoc]
  refine rs_app (by simp [qinvPart]) (by simp [crtPart, divisorOf]) qinvPart_ct ?_
  refine rs_app (by simp [crtPart, divisorOf]) (by simp [nPart]) crtPart_ct ?_
  refine rs_app (by simp [nPart]) (by simp) nPart_ct ?_
  refine rs_app (by simp) (by simp [outputs, storeA]) (finalMask_ct (stab_nf _ _)) ?_
  exact outputs_ct.mono (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, EG.of_kg (h₁.imp fun _ h => h.2), EG.of_kg (h₂.imp fun _ h => h.2)⟩)
    fun _ _ h => h

end VG.Proof.RsaKeyGen.X86_64.Key
