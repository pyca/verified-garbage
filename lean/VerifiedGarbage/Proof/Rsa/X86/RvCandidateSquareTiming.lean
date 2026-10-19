module

public import VerifiedGarbage.Proof.Rsa.X86.RvCandidateTiming
public import VerifiedGarbage.Proof.Rsa.X86.RvCandidateSquareInit
public import VerifiedGarbage.Proof.Rsa.X86.RvSquareTiming

/-! # A candidate's squaring search keeps its private values secret -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (sqStart sqIter)

def CandidateData.SquareStart {g : Geo} {m eLen dLen : Nat}
    (C : CandidateData g m eLen dLen) (y : Nat) (s : State) :=
  KS g C.s0 (upd C.A mY (y * 2 ^ (64 * g.n) % m)) liveSq C.AW [wR]
    (upd C.V sCnt 0) slotsExp s

def CandidateData.SquareEnd {g : Geo} {m eLen dLen : Nat}
    (C : CandidateData g m eLen dLen) (y : Nat) (s : State) :=
  SI g C.s0 C.A C.AW (upd C.V sCnt 0) m (8 * (dLen + eLen)) 0
    (sqIter m (C.V sTc) (8 * (dLen + eLen)) (sqStart m y)) s

theorem candSquare_relCT {g : Geo} {m eLen dLen : Nat} (C D : CandidateData g m eLen dLen)
    (sp : C.s0.gpr .esp = D.s0.gpr .esp) (y z : Nat) (yl : y < m) (zl : z < m) :
    RelCT isa (fun s t => C.SquareStart y s ∧ D.SquareStart z t) (candSquare g.n)
      (fun s t => C.SquareEnd y s ∧ D.SquareEnd z t) := by
  intro s t tr ur sf tf ⟨hs, ht⟩ es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 er =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 fr =>
      cases er with
      | @seq _ _ _ x _ _ _ e2 er =>
        cases fr with
        | @seq _ _ _ y1 _ _ _ f2 fr =>
          cases er with
          | @seq _ _ _ x1 _ _ _ e3 e4 =>
            cases fr with
            | @seq _ _ _ y2 _ _ _ f3 f4 =>
              have prefixS := Exec.seq e1 (Exec.seq e2 e3)
              have prefixT := Exec.seq f1 (Exec.seq f2 f3)
              have eqPrefix := ((candSquareInit_address g.n).trace _ _ _ _ _ _
                (ks_address_agree hs ht sp) prefixS prefixT).1
              have initialC := wp_result (candSquareInit_ok hs C.odd (by have := C.large; omega)
                C.one C.neg yl C.ae C.ad C.limit) prefixS
              have initialD := wp_result (candSquareInit_ok ht D.odd (by have := D.large; omega)
                D.one D.neg zl D.ae D.ad D.limit) prefixT
              obtain ⟨eqLoop, is, it⟩ := sqLoop_relCT g C.s0 D.s0 C.A D.A C.AW D.AW
                (upd C.V sCnt 0) (upd D.V sCnt 0) m (8 * (dLen + eLen)) (sqStart m y) (sqStart m z)
                C.value D.value C.bound
                (by simpa only [upd_ne _ _ (by decide : sInv ≠ sCnt)] using C.inverse)
                (by simpa only [upd_ne _ _ (by decide : sInv ≠ sCnt)] using D.inverse)
                C.odd (by have := C.large; omega) C.one D.one C.neg D.neg
                (by simpa only [upd_ne _ _ (by decide : sTc ≠ sCnt)] using C.tc)
                (by simpa only [upd_ne _ _ (by decide : sTc ≠ sCnt)] using D.tc)
                C.count C.limit _ _ _ _ _ _ ⟨initialC, initialD⟩ e4 f4
              refine ⟨?_, ?_, ?_⟩
              · simpa only [List.append_assoc] using congrArg₂ (fun a b : List Leak => a ++ b) eqPrefix eqLoop
              · simpa only [CandidateData.SquareEnd, upd_ne _ _ (by decide : sTc ≠ sCnt)] using is
              · simpa only [CandidateData.SquareEnd, upd_ne _ _ (by decide : sTc ≠ sCnt)] using it

end VG.Proof.Rsa.X86.Recover
