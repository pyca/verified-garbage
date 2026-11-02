module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Entry
import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverDet
import VerifiedGarbage.Proof.Rsa.Ranges
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Prod
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.Div
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Entry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
meta import VerifiedGarbage.Impl.Rsa.X86_64.RecoverDet
meta import VerifiedGarbage.Proof.Rsa.Ranges
meta import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Prod
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.Div
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Rsa.RecoverMath
public import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Args
import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTCode
import VerifiedGarbage.Proof.Rsa.X86_64.CvFail
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Rsa.RecoverMath
meta import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Args
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTCode
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# `vg_rsa_recover_primes_det` on x86-64: the public data, and the failure path in constant time

`RpP`: the public data (the working space, the pointers and lengths, `n` and
`e`). The failure path leaks only those (`Rp.failR_ct`), as do the entry
and the check of the modulus (`rpEntry_split`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

/-- The public data of `vg_rsa_recover_primes_det`. -/
structure RpP where
  B : Addr
  Z : Nat
  k : Nat
  el : Nat
  dl : Nat
  pP : Addr
  pQ : Addr
  pN : Addr
  pE : Addr
  pD : Addr
  nb : List Byte
  eb : List Byte
  W : List Region
  sp : Addr
  deriving Inhabited

/-- The public part of the inputs. -/
def RpIn.pub (I : RpIn) : RpP :=
  ⟨I.B, I.Z, I.k, I.el, I.dl, I.pP, I.pQ, I.pN, I.pE, I.pD, I.nb, I.eb, I.W, I.sp⟩

/-- The outputs: writable, outside the working space, and apart. -/
structure RpOuts (I : RpIn) : Prop where
  p : ∀ i < I.k, InRegions I.W (I.pP + BitVec.ofNat 64 i) 1
  q : ∀ i < I.k, InRegions I.W (I.pQ + BitVec.ofNat 64 i) 1
  sp : ∀ i < I.k, I.Z ≤ ofs I.B (I.pP + BitVec.ofNat 64 i)
  sq : ∀ i < I.k, I.Z ≤ ofs I.B (I.pQ + BitVec.ofNat 64 i)
  a : Apart I.pP I.k I.pQ I.k

theorem RpPre.outs {I : RpIn} {s : State} (h : RpPre I s) : RpOuts I :=
  ⟨fun i hi => by rw [← h.wr]; exact h.oP.wr i hi, fun i hi => by rw [← h.wr]; exact h.oQ.wr i hi,
    h.oP.sep, h.oQ.sep, h.a⟩

end VG.Proof.Rsa.X86_64

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

namespace Rp

/-! ## `fail` -/

/-- Between the zeros of `fail`. -/
def GFr (p : RpP) (s : State) : Prop :=
  ∃ I : RpIn, I.pub = p ∧ Scr s I.B I.Z ∧ s.gpr .rdi = I.B ∧
    RpArgs s.mem I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD I.sv ∧ s.wr = I.W ∧ RpLens I ∧ RpOuts I

theorem pins_GFr : Pins GFr [.rdi] := fun _ _ _ ⟨_, e₁, _, h₁, _⟩ ⟨_, e₂, _, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁, h₂]
  exact (congrArg RpP.B e₁).trans (congrArg RpP.B e₂).symm

theorem zeroOutR_ct {sPtr : Nat} (hP : sPtr < 32) (ptr : RpP → Addr)
    (hA : ∀ p s, GFr p s → word s.mem p.B (8 * sPtr) = ptr p ∧
      (∀ i < p.k, InRegions p.W (ptr p + BitVec.ofNat 64 i) 1) ∧
      (∀ i < p.k, p.Z ≤ ofs p.B (ptr p + BitVec.ofNat 64 i)))
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK)), .mov32 .rax (.imm 0)]) hc).isSome = true) :
    RelCT isa (Two GFr) (zeroOut sPtr Impl.Bignum.X86_64.Public.sK) (Two GFr) :=
  pin_ct [.rdi] [.rsi, .rcx] (fun p => zoVal (ptr p) p.k) pins_GFr ht
    (fun p s h => by
      obtain ⟨hp, -⟩ := hA p s h
      obtain ⟨I, rfl, hs, hdi, ha, -, L, -⟩ := h
      have hn := hs.nowrap
      have h256 : 8 * 32 ≤ I.Z := by have := L.z; have := L.k1; omega_arith
      have hl' : ∀ i < 32, InRegions (s.rd ++ s.wr) (off I.B (8 * i)) 8 := fun i hi => hs.ld (by omega_arith)
      refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = ptr I.pub ∧
        t.gpr .rcx = BitVec.ofNat 64 I.k) (by
        xrun [State.ea, hdr, hdi, hdrOff, hl' sPtr hP, hl' Impl.Bignum.X86_64.Public.sK (by decide)]
        exact ⟨hp, ha.k⟩) rfl) fun t ⟨⟨h1, h2⟩, _⟩ r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h2)
    (by taint_decide) fun p s h => by
      obtain ⟨hp, hwr, hsep⟩ := hA p s h
      obtain ⟨I, rfl, hs, hdi, ha, hW, L, O⟩ := h
      dsimp only [RpIn.pub] at hp hwr hsep ⊢
      have hn := hs.nowrap
      have h256 : 8 * 32 ≤ I.Z := by have := L.z; have := L.k1; omega_arith
      have hk1 := L.k1
      have hk2 := L.k2
      refine WP.mono (zeroOut_ok hs hdi h256 hP (by decide) hp ha.k (by omega_arith) (by omega_arith)
        ⟨fun i hi => by rw [hW]; exact hwr i hi, hsep⟩) fun t ⟨_, hx, k⟩ => ?_
      have fw : ∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i) :=
        fun i hi => (frm_scr hsep hx).word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega_arith))
          (by omega_arith)
      exact ⟨I, rfl, hs.congr k.2.2, (k.gpr (by decide)).trans hdi, ha.congr fun i hi => fw i (by
        unfold rArg at hi; omega_arith), k.2.2.trans hW, L, O⟩

/-- `fail` leaks the same in two runs with the same public data. -/
theorem failR_ct : RelCT isa (Two GFr) fail fun _ _ => True := by
  unfold fail
  refine (ct_cons (by simp) (zeroOutR_ct (by decide) RpP.pP (fun p s h => ?_) (by taint_decide))
    (ct_cons (by simp) (zeroOutR_ct (by decide) RpP.pQ (fun p s h => ?_) (by taint_decide))
    (ct_one (Ψ := fun (_ : RpP) (_ : State) => True)
      ((two_taint [.rdi] pins_GFr (by taint_decide)).mono (fun _ _ h => h)
        fun _ _ _ => ⟨default, trivial, trivial⟩)))).mono (fun _ _ h => h) fun _ _ _ => trivial
  all_goals
    obtain ⟨I, rfl, -, -, ha, -, L, O⟩ := h
    dsimp only [RpIn.pub]
  · exact ⟨ha.p, O.p, O.sp⟩
  · exact ⟨ha.q, O.q, O.sq⟩

end Rp

/-! ## The code -/

theorem rpEntry_split : entry ++ ([.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
    .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))] : List Instr) =
    ([.mov .r11 (.mem { base := .rsp, disp := 40 })] : List Instr) ++
      ((entry.drop 1) ++ [.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
        .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))]) := rfl

end VG.Proof.Rsa.X86_64
