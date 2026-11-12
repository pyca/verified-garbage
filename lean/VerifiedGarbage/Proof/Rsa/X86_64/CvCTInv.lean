module

-- separate module: the inverse's constant time, whose proofs import algebra, and `CvCTMain` is imported by many modules
public import VerifiedGarbage.Proof.Rsa.X86_64.WordChoiceCT
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
public import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
public import VerifiedGarbage.Proof.Rsa.X86_64.CvInv
import VerifiedGarbage.Proof.Rsa.X86_64.CvTail
import VerifiedGarbage.Proof.Rsa.X86_64.CvCT
import VerifiedGarbage.Proof.Rsa.X86_64.CvMain
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordChoiceCT
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvInv
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvTail
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# `vg_rsa_crt_values` on x86-64: constant time of the inverse and of `main`

`invQ_ct`, `invPart_ct` and `cvMain_ct`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)
open VG.Impl.Rsa.X86_64 (copyWords)

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
      exact WP.mono (nPQ_ok h'.ws h'.args.pl h'.args.ql (by have := L.pl2; have := L.k2; omega)
        (by have := L.ql2; have := L.k2; omega)) fun t ⟨h12, h9, h13, hdi, _⟩ r hr => by
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
      have := slot_lin (wk I.k) 26; have := L.z; have := L.k1; unfold wk at *; omega
    have hw20 : wk I.k < 2 ^ 20 := by have := L.k2; unfold wk; omega
    have e16 := slot_lin (wk I.k) 16
    exact WP.mono (invQ_gen h'.ws hZ26 hw20 h'.args.pl h'.args.ql L.pl1 (by have := L.pl2; unfold wk; omega)
      (by have := L.ql2; unfold wk; omega)) fun t ⟨_, f, k, _⟩ =>
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
theorem guarded_ct {a b : Prog isa} (ha : RelCT isa (Two GA) a (Two GA)) (hb : RelCT isa (Two GA) b (Two GA)) :
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
      exact WP.mono (nPQ_ok h'.ws h'.args.pl h'.args.ql (by have := L.pl2; have := L.k2; omega)
        (by have := L.ql2; have := L.k2; omega)) fun t ⟨h12, h9, h13, hdi, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdi
        · exact h12
        · exact h9
        · exact h13)
    ht fun _ _ h => by
    obtain ⟨I, m₀, c, rfl, h', L, O, hm⟩ := h
    have hZ26 : slot (wk I.k) 26 ≤ I.Z := by
      have := slot_lin (wk I.k) 26; have := L.z; have := L.k1; unfold wk at *; omega
    have hw20 : wk I.k < 2 ^ 20 := by have := L.k2; unfold wk; omega
    exact WP.mono (invQS_gen h'.ws hZ26 hw20 h'.args.pl h'.args.ql L.pl1 (by have := L.pl2; unfold wk; omega)
      (by have := L.ql2; unfold wk; omega)) fun t ⟨_, f, k⟩ => by
      obtain ⟨ht, hmt, -⟩ := cvInvFrame h' f k L
      exact ⟨I, m₀, c, rfl, ht, L, O, hmt.trans hm⟩

/-- The doublings of `qTail`. -/
theorem tailDbl_ct : RelCT isa (Two GA) (.seq (.block dblSetup) (.loop tailDbl .ne)) (Two GA) := by
  have e : dblSetup = ws ++ (tailK ++ [.mov .r11 (.reg .rax), .alu .and .r11 (.imm 63), .alu .add .r11 (.imm 1),
      .mov .r12 (.reg .r13), .alu .add .r12 (.imm 1)]) := by simp only [dblSetup, List.append_assoc]
  rw [e]
  refine ws_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.ws) (by taint_decide) fun p s h => ?_
  rw [← e]
  obtain ⟨I, m₀, c, rfl, h', L, O, hm⟩ := h
  refine WP.seq (WP.mono (dblSetup_ok h'.ws) fun s₃ ⟨r11, r12, r9, m₃, k₃⟩ => ?_)
  have h₃ := h'.step (rs := []) (by rw [m₃]; exact Frm.refl _ _ _) (by simp) (by simp) k₃ (by decide)
  exact WP.mono (tailLoop_ok h₃ r9 r12 r11) fun t ⟨ht, o, _, _⟩ =>
    ⟨I, m₀, c, rfl, ht, L, O, by rw [mword_out o, m₃]; exact hm⟩

/-- The placement of `qTail`. -/
theorem placeCopy_ct : RelCT isa (Two GA) (.seq (.block place) copyWords) (Two GA) := by
  have e : place = ws ++ (tailK ++ ([.shift .shr .rax 6, .mov .r13 (.reg .rax), .alu .sub .r12 (.reg .r13),
      .shift .shl .r13 3] ++ (base aX₂ .rsi ++ (base aD .rbx ++ [.alu .add .rbx (.reg .r13)])))) := by
    simp only [place, List.append_assoc]
  rw [e]
  refine ws_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.ws) (by taint_decide) fun p s h => ?_
  rw [← e]
  obtain ⟨I, m₀, c, rfl, h', L, O, hm⟩ := h
  exact WP.mono (placeCopy_ok h') fun t ⟨ht, _, o⟩ => ⟨I, m₀, c, rfl, ht, L, O, by
    rw [← hm]
    exact o.word (Or.inl (by have := hdr_lt_slot (wk I.k) aD (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith))
      (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith)⟩

theorem qTail_ct : RelCT isa (Two GA) (seqs qTail) (Two GA) := by
  unfold qTail
  exact ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
    (ct_cons (by simp) (copyA_ct (by decide) (by decide) (by decide) (by taint_decide))
    (ct_cons (by simp) tailDbl_ct
    (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
    (ct_cons (by simp) placeCopy_ct
    (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
    (ct_cons (by simp) (copyA_ct (by decide) (by decide) (by decide) (by taint_decide))
    (ct_cons (by simp) wordFast_ct
    (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
    (ct_cons (by simp) (copyA_ct (by decide) (by decide) (by decide) (by taint_decide))
    (ct_one (copyA_ct (by decide) (by decide) (by decide) (by taint_decide))))))))))))

theorem invPart_ct [InvLaw] : RelCT isa (Two GA) (seqs invPart) (Two GA) := by
  unfold invPart gcdPart
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  exact ct_cons (by simp) (guarded_ct (invQS_ct (by taint_decide)) (invQ_ct (by taint_decide)))
    (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
      (ct_cons (by simp) (setOneA_ct (by decide) (by taint_decide))
        (ct_app (by simp [eqA]) (by simp) (eqA_ct (by decide) (by decide) (by taint_decide))
          (ct_cons (by simp) andZero_ct (ct_one (guarded_ct qTail_ct skip_ct))))))

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
