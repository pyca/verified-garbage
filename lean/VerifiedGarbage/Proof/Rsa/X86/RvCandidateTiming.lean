module

public import VerifiedGarbage.Proof.Rsa.X86.RvAddressTiming
public import VerifiedGarbage.Proof.Rsa.X86.RvExpTiming
public import VerifiedGarbage.Proof.Rsa.X86.RvCandidateExpInit

/-! # Candidate exponentiation relates different private exponents -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Recover

structure CandidateData (g : Geo) (m eLen dLen : Nat) where
  s0 : State
  A : Nat → Nat
  AW : Nat → Nat
  V : Nat → Nat
  zero : A aZ = 0
  value : A mBase = m
  bound : m < 2 ^ (64 * g.n)
  inverse : (m * V sInv + 1) % 2 ^ 32 = 0
  odd : m % 2 = 1
  large : 101 < m
  one : A aO = 2 ^ (64 * g.n) % m
  neg : A aNg = m - 2 ^ (64 * g.n) % m
  r2 : A mR2 = 2 ^ (128 * g.n) % m
  candidate : V sCand < 100
  baseBound : V sCand + 2 < m
  ae : CallArgument s0 g.B g.Z 7 (BitVec.ofNat 32 eLen)
  ad : CallArgument s0 g.B g.Z 9 (BitVec.ofNat 32 dLen)
  tc : V sTc ≤ 8 * (dLen + eLen)
  rb : AW wR < 2 ^ (8 * (dLen + eLen))
  count : 0 < 8 * (dLen + eLen)
  limit : 8 * (dLen + eLen) ≤ 16384

def CandidateData.Start {g : Geo} {m eLen dLen : Nat} (C : CandidateData g m eLen dLen) (s : State) :=
  KS g C.s0 C.A liveM C.AW [wR] C.V slotsExp s

def CandidateData.Exp {g : Geo} {m eLen dLen : Nat} (C : CandidateData g m eLen dLen) (k : Nat) (s : State) :=
  EI g C.s0 C.A C.AW C.V m (C.V sCand + 2) (C.AW wR) (8 * (dLen + eLen)) k s

theorem ks_address_agree {g : Geo} {s0 t0 s t : State} {A B AW BW V W : Nat → Nat}
    {al bl aw bw sl tl : List Nat}
    (h : KS g s0 A al AW aw V sl s) (j : KS g t0 B bl BW bw W tl t)
    (sp : s0.gpr .esp = t0.gpr .esp) : VG.X86.Taint.Agree argumentTaint s t := by
  apply agree_regs (rs := [.edi, .esp])
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (ks_agree h j).rf.1 _ (by decide)
  · exact (h.rest.1 _ (by decide)).trans (sp.trans (j.rest.1 _ (by decide)).symm)

theorem candExp_relCT {g : Geo} {m eLen dLen : Nat} (C D : CandidateData g m eLen dLen)
    (sp : C.s0.gpr .esp = D.s0.gpr .esp) :
    RelCT isa (fun s t => C.Start s ∧ D.Start t) (candExp g.n)
      (fun s t => C.Exp (8 * (dLen + eLen)) s ∧ D.Exp (8 * (dLen + eLen)) t) := by
  intro s t tr ur sf tf ⟨hs, ht⟩ es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 er =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 fr =>
      have eq1 := ((candSet_address g.n).trace _ _ _ _ _ _ (ks_address_agree hs ht sp) e1 f1).1
      have cs := wp_result (candSet_ok hs C.zero C.candidate C.ae C.ad (by have := C.limit; omega)) e1
      have ds := wp_result (candSet_ok ht D.zero D.candidate D.ae D.ad (by have := D.limit; omega)) f1
      cases er with
      | @seq _ _ _ x _ _ _ e2 e3 =>
        cases fr with
        | @seq _ _ _ y _ _ _ f2 f3 =>
          have eq2 := ((mmul_public g.n mG mG mR2).trace _ _ _ _ _ _ (ks_agree cs ds) e2 f2).1
          have initialC := wp_result (candExpInit_ok hs C.zero C.value C.bound C.inverse C.odd C.one C.r2
            C.candidate C.baseBound C.ae C.ad C.limit) (Exec.seq e1 e2)
          have initialD := wp_result (candExpInit_ok ht D.zero D.value D.bound D.inverse D.odd D.one D.r2
            D.candidate D.baseBound D.ae D.ad D.limit) (Exec.seq f1 f2)
          obtain ⟨eq3, is, it⟩ := expLoop_relCT g C.s0 D.s0 C.A D.A C.AW D.AW C.V D.V m
            (C.V sCand + 2) (D.V sCand + 2) (C.AW wR) (D.AW wR) (8 * (dLen + eLen))
            C.value D.value C.bound C.inverse D.inverse C.odd (by have := C.large; omega)
            C.one D.one C.count C.limit _ _ _ _ _ _ ⟨initialC, initialD⟩ e3 f3
          exact ⟨by rw [eq1, eq2, eq3], is, it⟩

end VG.Proof.Rsa.X86.Recover
