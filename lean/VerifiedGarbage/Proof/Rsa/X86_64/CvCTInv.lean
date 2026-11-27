module

-- separate module: the inverse's constant time, whose proofs import algebra, and `CvCTMain` is imported by many modules
public import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
public import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
public import VerifiedGarbage.Proof.Rsa.X86_64.CvInv
import VerifiedGarbage.Proof.Rsa.X86_64.CvCT
import VerifiedGarbage.Proof.Rsa.X86_64.CvMain
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvInv
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Rsa.X86_64.WordFastCT
public import VerifiedGarbage.Proof.Rsa.X86_64.WordGuard
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordFastCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordGuard
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `Rsa.X86_64.WordChoiceCT`, which only this module used -/

section

/-! # Constant-time public selection of CRT remainder algorithms -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The word reducer's extended array window remains inside RSA's workspace. -/
theorem GA.wordFrame {p : CvP} {s t : State} (h : GA p s)
    (ff : Frm p.B (WordDivide.normRanges (wk p.k)) s.mem t.mem) (kk : Keep mmRegs s t) : GA p t := by
  obtain ⟨I, m₀, c, rfl, h, L, O, hm⟩ := h
  have hw : 6 ≤ wk I.k := by have := L.k1; unfold wk; omega_using [this]
  have hZ : slot (wk I.k) 17 ≤ I.Z := by
    have hk := L.k1
    have hz := L.z
    simp only [slot, Impl.Bignum.hdrBytes, wk]; omega_using [hk, hz]
  have hn := h.ws.scr.nowrap
  refine ⟨I, m₀, c, rfl, h.step ff ?_ ?_ kk (by decide), L, O, ?_⟩
  · intro r hr
    simp only [WordDivide.normRanges, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact Mut.ofSlot _ _ _
    · exact WordDivide.all_mut hr
  · intro r hr
    simp only [WordDivide.normRanges, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact h.ws.sl (by decide)
    · exact WordDivide.all_bound h.ws hZ hr
  · rw [← hm]
    apply ff.word_eq _ (by change 8 * 22 + 8 ≤ 2 ^ 64; decide)
    intro r hr
    simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [VG.Impl.Rsa.X86_64.WordDivide.aM, VG.Impl.Rsa.X86_64.WordDivide.aR,
        VG.Impl.Rsa.X86_64.WordDivide.aT, VG.Impl.Rsa.X86_64.WordDivide.aV, slot, Public.sMask, sFn,
        Impl.Bignum.hdrBytes] <;> omega_arith

theorem wordFast_ct : RelCT isa (Two GA) (.seq (.block VG.Impl.Rsa.X86_64.WordDivide.normalize)
    VG.Impl.Rsa.X86_64.WordDivide.code) (Two GA) := by
  refine two_post (two_map (fun p : CvP => (⟨p.B, p.Z, wk p.k, 0⟩ : WordDivide.Pub)) ?_ WordDivide.fast_ct) ?_
  · rintro p s ⟨I, m₀, c, rfl, h, L, O, hm⟩
    have hk := L.k1
    have hz := L.z
    refine ⟨h.ws, ?_, ?_⟩
    · change slot (wk I.k) 17 ≤ I.Z
      simp only [slot, Impl.Bignum.hdrBytes, wk]; omega_using [hk, hz]
    · change 6 ≤ wk I.k
      unfold wk; omega_using [hk]
  · intro p s h
    obtain ⟨I, m₀, c, rfl, hs, L, O, hm⟩ := h
    have hk := L.k1
    have hz := L.z
    have hZ : slot (wk I.k) 17 ≤ I.Z := by
      simp only [slot, Impl.Bignum.hdrBytes, wk]; omega_using [hk, hz]
    exact WP.mono (WordDivide.fast_ok hs.ws hZ (by unfold wk; omega_using [hk])) fun t ⟨_, ff, kk⟩ =>
      (show GA I.pub s from ⟨I, m₀, c, rfl, hs, L, O, hm⟩).wordFrame ff kk

def WordHead (p : CvP) (s : State) : Prop :=
  GA p s ∧ s.gpr .r12 = BitVec.ofNat 64 (wk p.k) ∧ s.gpr .rdx = p.pN

def publicGuard (p : CvP) : BitVec 64 :=
  WordDivide.guardVal (wk p.k) p.k p.pl p.ql ((p.nb[0]?).getD 0)

def WordTest (p : CvP) (s : State) : Prop := GA p s ∧ s.zf = some (publicGuard p == 0)

theorem wordHead_ct : RelCT isa (Two GA) (.block wordGuardHead) (Two WordHead) := by
  unfold wordGuardHead
  refine ws_block_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.ws) (by taint_decide) ?_
  rintro p s ⟨I, m₀, c, rfl, h, L, O, hm⟩
  exact WP.mono (WordDivide.guardHead_ok h) fun t ⟨ht, mt, h12, hdx⟩ =>
    ⟨⟨I, m₀, c, rfl, ht, L, O, by rw [mt]; exact hm⟩, h12, hdx⟩

theorem wordTail_ct : RelCT isa (Two WordHead) (.block wordGuardTail) (Two WordTest) := by
  refine two_piece [.rdi, .rdx] ?_ (by taint_decide) ?_
  · intro p s₁ s₂ h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.ws.rdi, h₂.1.ws.rdi]
    · rw [h₁.2.2, h₂.2.2]
  · rintro p s ⟨⟨I, m₀, c, rfl, h, L, O, hm⟩, h12, hdx⟩
    refine WP.mono (WordDivide.guardTail_ok h L h12 hdx) fun t ⟨ht, mt, hz⟩ => ?_
    refine ⟨⟨I, m₀, c, rfl, ht, L, O, by rw [mt]; exact hm⟩, ?_⟩
    have hnl : 0 < I.nb.length := by rw [L.nl]; have := L.k1; omega_using [this]
    simpa only [publicGuard, CvIn.pub, List.getElem?_eq_getElem hnl, Option.getD_some] using hz

/-- Both branches preserve the same public construction state. -/
theorem wordChoice_ct {j : Nat} (hj : j < 16) (hjC : aC ≠ j) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .rsi ++ base aC .rbx)) copyWords)
      hc).isSome = true) : RelCT isa (Two GA) (wordChoice j) (Two GA) := by
  unfold wordChoice
  refine RelCT.seq wordHead_ct (RelCT.seq wordTail_ct ?_)
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_
  · exact (RelCT.seq (divisor_ct hj hjC ht) wordFast_ct).mono
      (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) (fun _ _ h => h)
  · exact (ct_app (by simp [divisor]) (by simp) (divisor_ct hj hjC ht)
      (ct_one (divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by taint_decide)))).mono
      (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) (fun _ _ h => h)

end VG.Proof.Rsa.X86_64

end

end

/-!
# `vg_rsa_crt_values` on x86-64: constant time of the inverse and of `main`

`invQ_ct`, `invPart_ct` and `cvMain_ct`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

/-- The registers the inverse at the primes' width needs pinned: `ws`'s and
the width in `r13`. -/
def nVal (B : Addr) (w n : Nat) : Reg → BitVec 64
  | .rdi => B
  | .r12 => BitVec.ofNat 64 w
  | .r9 => BitVec.ofNat 64 (8 * (w + 2))
  | .r13 => BitVec.ofNat 64 n
  | _ => 0

/-- The inverse at the primes' width, `⌈max(p_len, q_len) / 8⌉`, which the
public lengths fix. -/
theorem invQ_ct [InvLaw] {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9, .r13]) (inverseN aQ aV aX₂ aP) hc).isSome = true) :
    RelCT isa (Two GA) (.seq (.block (ws ++ nPQ)) (inverseN aQ aV aX₂ aP)) (Two GA) :=
  pin_ct [.rdi] [.rdi, .r12, .r9, .r13] (fun p => nVal p.B (wk p.k) (nOf p.pl p.ql)) pins_GA (by taint_decide)
    (fun p s h => by
      obtain ⟨I, m₀, c, rfl, h', L, -⟩ := h
      exact WP.mono (nPQ_ok h'.ws h'.args.pl h'.args.ql (by have := L.pl2; have := L.k2; omega_arith)
        (by have := L.ql2; have := L.k2; omega_arith)) fun t ⟨h12, h9, h13, hdi, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdi
        · exact h12
        · exact h9
        · exact h13)
    ht fun _ _ h => by
    obtain ⟨I, m₀, c, rfl, h', L, O, hm⟩ := h
    have hn := h'.ws.scr.nowrap
    have hZ26 : slot (wk I.k) 26 ≤ I.Z := by
      have := slot_lin (wk I.k) 26; have := L.z; have := L.k1; unfold wk at *; omega_arith
    have hw20 : wk I.k < 2 ^ 20 := by have := L.k2; unfold wk; omega_using [this]
    have e16 := slot_lin (wk I.k) 16
    exact WP.mono (invQ_gen h'.ws hZ26 hw20 h'.args.pl h'.args.ql L.pl1 (by have := L.pl2; unfold wk; omega_using [this])
      (by have := L.ql2; unfold wk; omega_using [this])) fun t ⟨_, f, k, _⟩ =>
      ⟨I, m₀, c, rfl, h'.step f (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact Mut.ofSlot _ _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> dsimp only
        · have := h'.ws.sl (j := aV) (by decide); omega_arith
        · have := h'.ws.sl (j := aX₂) (by decide); omega_arith
        · have := slot_lin (wk I.k) 26; omega_arith) k (by decide), L, O,
        (f.word_eq (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> dsimp only
          · have := hdr_lt_slot (wk I.k) aV (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith
          · have := hdr_lt_slot (wk I.k) aX₂ (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith
          · have := hdr_lt_slot (wk I.k) 16 (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith)
          (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith)).trans hm⟩

/-- `guarded a b`, from and to `GA`. -/
theorem cvGuarded_ct {a b : Prog isa} (ha : RelCT isa (Two GA) a (Two GA)) (hb : RelCT isa (Two GA) b (Two GA)) :
    RelCT isa (Two GA) (guarded a b) (Two GA) := by
  unfold guarded
  refine RelCT.seq wordHead_ct (RelCT.seq wordTail_ct ?_)
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_
  · exact ha.mono (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) (fun _ _ h => h)
  · exact hb.mono (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) (fun _ _ h => h)

theorem skip_ct : RelCT isa (Two GA) (.block []) (Two GA) :=
  two_piece [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide) fun _ _ h => WP.block_nil h

/-- `invQ_ct` for `inverseNS`. -/
theorem invQS_ct [InvLaw] {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9, .r13]) (inverseNS aQ aV aX₂ aP) hc).isSome = true) :
    RelCT isa (Two GA) (.seq (.block (ws ++ nPQ)) (inverseNS aQ aV aX₂ aP)) (Two GA) :=
  pin_ct [.rdi] [.rdi, .r12, .r9, .r13] (fun p => nVal p.B (wk p.k) (nOf p.pl p.ql)) pins_GA (by taint_decide)
    (fun p s h => by
      obtain ⟨I, m₀, c, rfl, h', L, -⟩ := h
      exact WP.mono (nPQ_ok h'.ws h'.args.pl h'.args.ql (by have := L.pl2; have := L.k2; omega_arith)
        (by have := L.ql2; have := L.k2; omega_arith)) fun t ⟨h12, h9, h13, hdi, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdi
        · exact h12
        · exact h9
        · exact h13)
    ht fun _ _ h => by
    obtain ⟨I, m₀, c, rfl, h', L, O, hm⟩ := h
    have hZ26 : slot (wk I.k) 26 ≤ I.Z := by
      have := slot_lin (wk I.k) 26; have := L.z; have := L.k1; unfold wk at *; omega_arith
    have hw20 : wk I.k < 2 ^ 20 := by have := L.k2; unfold wk; omega_using [this]
    exact WP.mono (invQS_gen h'.ws hZ26 hw20 h'.args.pl h'.args.ql L.pl1 (by have := L.pl2; unfold wk; omega_using [this])
      (by have := L.ql2; unfold wk; omega_using [this])) fun t ⟨_, f, k⟩ => by
      obtain ⟨ht, hmt, -⟩ := cvInvFrame h' f k L
      exact ⟨I, m₀, c, rfl, ht, L, O, hmt.trans hm⟩

/-- The shift of `qTail`: `[x₂] 2^T` into word `Q` of `[d]`. -/
theorem qShift_ct : RelCT isa (Two GA) (.seq (.block shSetup) (wordLoop 1 shlClBody)) (Two GA) := by
  have e : shSetup = ws ++ ([.shift .shr .r12 1, .mov .rax (.reg .r12), .shift .shl .rax 4, .alu .sub .rax (.reg .r12),
      .alu .add .rax (.imm 10), .mov .rcx (.reg .rax), .alu .and .rcx (.imm 63), .shift .shr .rax 6,
      .shift .shl .rax 3, .alu .add .r12 (.imm 1)] ++ (base aX₂ .r8 ++ (base aD .rsi ++ ([.alu .add .rsi (.reg .rax)] ++
      [.mov .rax (.mem (at0 .r8)), .shiftCl .shl .rax, .store (at0 .rsi) .rax])))) := by
    simp only [shSetup, List.append_assoc]
  rw [e]
  refine ws_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.ws) (by taint_decide) fun p s h => ?_
  rw [← e]
  obtain ⟨I, m₀, c, rfl, h', L, O, hm⟩ := h
  exact WP.mono (qShift_ok h') fun t ⟨ht, _, o⟩ => ⟨I, m₀, c, rfl, ht, L, O, by
    rw [← hm]
    exact o.word (Or.inl (by have := hdr_lt_slot (wk I.k) aD (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith))
      (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith)⟩

/-- `qTail`'s reduction, from the dividend's top digit (`startT`). -/
theorem wordFastT_ct : RelCT isa (Two GA) (.seq (.block VG.Impl.Rsa.X86_64.WordDivide.normalize)
    (VG.Impl.Rsa.X86_64.WordDivide.codeWith VG.Impl.Rsa.X86_64.WordDivide.startT)) (Two GA) := by
  refine two_post (two_map (fun p : CvP => (⟨p.B, p.Z, wk p.k, 0⟩ : WordDivide.Pub)) ?_
    (WordDivide.fastAtWith_ct ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩ (fun W => tailQ W + 2)
      fun W hW hW' => startT_ok hW hW')) ?_
  · rintro p s ⟨I, m₀, c, rfl, h, L, O, hm⟩
    have hk := L.k1
    have hz := L.z
    refine ⟨h.ws, ?_, ?_⟩
    · change slot (wk I.k) 17 ≤ I.Z
      simp only [slot, Impl.Bignum.hdrBytes, wk]; omega_using [hk, hz]
    · change 6 ≤ wk I.k
      unfold wk; omega_using [hk]
  · intro p s h
    obtain ⟨I, m₀, c, rfl, hs, L, O, hm⟩ := h
    have hk := L.k1
    have hz := L.z
    have hZ : slot (wk I.k) 17 ≤ I.Z := by
      simp only [slot, Impl.Bignum.hdrBytes, wk]; omega_using [hk, hz]
    have hW : 6 ≤ wk I.k := by unfold wk; omega_using [hk]
    exact WP.mono (WordDivide.fastAtWith_ok hs.ws hZ hW (startT_ok hW hs.ws.w2)) fun t ⟨_, ff, kk⟩ =>
      (show GA I.pub s from ⟨I, m₀, c, rfl, hs, L, O, hm⟩).wordFrame ff kk

theorem qTail_ct : RelCT isa (Two GA) (seqs qTail) (Two GA) := by
  unfold qTail
  exact ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
    (ct_cons (by simp) (copyA_ct (by decide) (by decide) (by decide) (by taint_decide))
    (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
    (ct_cons (by simp) qShift_ct
    (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
    (ct_cons (by simp) (copyA_ct (by decide) (by decide) (by decide) (by taint_decide))
    (ct_cons (by simp) wordFastT_ct
    (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
    (ct_cons (by simp) (copyA_ct (by decide) (by decide) (by decide) (by taint_decide))
    (ct_one (copyA_ct (by decide) (by decide) (by decide) (by taint_decide)))))))))))

theorem invPart_ct [InvLaw] : RelCT isa (Two GA) (seqs invPart) (Two GA) := by
  unfold invPart gcdPart
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  exact ct_cons (by simp) (cvGuarded_ct (invQS_ct (by taint_decide)) (invQ_ct (by taint_decide)))
    (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
      (ct_cons (by simp) (setOneA_ct (by decide) (by taint_decide))
        (ct_app (by simp [eqA]) (by simp) (eqA_ct (by decide) (by decide) (by taint_decide))
          (ct_cons (by simp) andZero_ct (ct_one (cvGuarded_ct qTail_ct skip_ct))))))

/-- `main` leaks the same in two runs with the same public data. -/
theorem cvMain_ct [InvLaw] : RelCT isa (Two GM) main fun _ _ => True := by
  rw [main_eq]
  exact (ct_app (by simp) (by simp [loadA]) (ct_one head_ct)
    (ct_app (by simp [loadA]) (by simp [pqCheck]) loadsB_ct
    (ct_app (by simp [pqCheck]) (by simp [invPart]) pqCheck_ct
    (ct_app (by simp [invPart]) (by simp) invPart_ct
    (ct_app (by simp) (by simp)
      (ct_one (wordChoice_ct (by decide) (by decide) (by taint_decide)))
    (ct_app (by simp) (by simp)
      (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
        (ct_one (copyA_ct (by decide) (by decide) (by decide) (by taint_decide))))
    (ct_app (by simp) (by simp [storeA])
      (ct_one (wordChoice_ct (by decide) (by decide) (by taint_decide)))
      (stores_ct.mono (fun _ _ h => two_mono (fun _ _ h => h.gs) h) fun _ _ h => h)))))))).mono
    (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.Rsa.X86_64
