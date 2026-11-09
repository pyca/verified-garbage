module

-- separate module: the inverse's constant time, whose proofs import algebra, and `CvCTMain` is imported by many modules
public import VerifiedGarbage.Proof.Rsa.X86_64.WordChoiceCT
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
public import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
public import VerifiedGarbage.Proof.Rsa.X86_64.CvInv
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

theorem invPart_ct [InvLaw] : RelCT isa (Two GA) (seqs invPart) (Two GA) := by
  unfold invPart
  exact ct_app (by simp) (by simp [eqA])
    (ct_cons (by simp) (invQ_ct (by taint_decide))
      (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
        (ct_one (setOneA_ct (by decide) (by taint_decide)))))
    (ct_app (by simp [eqA]) (by simp) (eqA_ct (by decide) (by decide) (by taint_decide)) (ct_one andZero_ct))


/-- `main` leaks the same in two runs with the same public data. -/
theorem cvMain_ct [InvLaw] : RelCT isa (Two GM) main fun _ _ => True := by
  rw [main_eq]
  exact (ct_app (by simp) (by simp [loadA]) (ct_one head_ct)
    (ct_app (by simp [loadA]) (by simp [pqCheck]) loads_ct
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
