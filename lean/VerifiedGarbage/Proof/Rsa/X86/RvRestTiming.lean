module

public import VerifiedGarbage.Proof.Rsa.X86.RvPrepared
public import VerifiedGarbage.Proof.Rsa.X86.RvPrepareTiming
public import VerifiedGarbage.Proof.Rsa.X86.RvCandidateLoopTiming
public import VerifiedGarbage.Proof.Rsa.X86.RvFinishTiming

/-! # The accepted recovery path leaks only the declared attempt count -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Spec.Rsa (recoverPrimes)

theorem rest_relCT (g : CallGeometry) (s0 t0 : State)
    (left : Inputs g s0) (right : Inputs g t0) (sp : s0.gpr .esp = t0.gpr .esp)
    (goS : GoOn (product g s0.mem)) (goT : GoOn (product g t0.mem))
    (boundS : inputValue g s0.mem 0 < 2 ^ (64 * g.n))
    (boundT : inputValue g t0.mem 0 < 2 ^ (64 * g.n))
    (oddS : inputValue g s0.mem 0 % 2 = 1) (oddT : inputValue g t0.mem 0 % 2 = 1)
    (largeS : 101 < inputValue g s0.mem 0) (largeT : 101 < inputValue g t0.mem 0)
    (modulus : inputValue g s0.mem 0 = inputValue g t0.mem 0)
    (tries : (recoverPrimes (inputValue g s0.mem 0) (inputValue g s0.mem 1) (inputValue g s0.mem 2)).2 =
      (recoverPrimes (inputValue g t0.mem 0) (inputValue g t0.mem 1) (inputValue g t0.mem 2)).2) :
    RelCT isa (fun s t => NumbersState g s0 s ∧ NumbersState g t0 t) (rest g.n) (fun _ _ => True) := by
  intro s t tr ur sf tf ⟨hs, ht⟩ es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 er =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 fr =>
      cases er with
      | @seq _ _ _ x _ _ _ e2 er =>
        cases fr with
        | @seq _ _ _ y _ _ _ f2 fr =>
          have prefixS := Exec.seq e1 e2
          have prefixT := Exec.seq f1 f2
          have eqPrefix := (prepare_relCT g s0 t0 left right sp _ _ _ _ _ _ ⟨hs, ht⟩ prefixS prefixT).1
          obtain ⟨p⟩ := wp_result (prepare_ok left hs goS boundS oddS largeS) prefixS
          obtain ⟨q⟩ := wp_result (prepare_ok right ht goT boundT oddT largeT) prefixT
          rw [← modulus] at q
          have commonSP : p.context.s0.gpr .esp = q.context.s0.gpr .esp := by
            rw [p.baseline, q.baseline]; exact sp
          have tries' := tries
          rw [← modulus] at tries'
          have attempts : p.context.tries = q.context.tries :=
            p.attempts.trans (tries'.trans q.attempts.symm)
          cases er with
          | @seq _ _ _ a _ _ _ e3 e4 =>
            cases fr with
            | @seq _ _ _ b _ _ _ f3 f4 =>
              have eqSearch := (candLoop_relCT p.context q.context commonSP p.counter q.counter
                p.twos q.twos attempts _ _ _ _ _ _ ⟨p.state, q.state⟩ e3 f3).1
              obtain ⟨j, st, _, cs, smallS, _, _⟩ := wp_result
                (p.context.search_ok p.state p.counter p.twos) e3
              obtain ⟨l, tt, _, ds, smallT, _, _⟩ := wp_result
                (q.context.search_ok q.state q.counter q.twos) f3
              have inputS : Inputs g p.context.s0 := p.baseline.symm ▸ left
              have inputT : Inputs g q.context.s0 := q.baseline.symm ▸ right
              have eqFinish := (fin_relCT g p.context.s0 q.context.s0 p.context.A q.context.A
                p.context.AW q.context.AW (VJ p.context.V (j + 1)) (VJ q.context.V (l + 1))
                (inputValue g s0.mem 0) (8 * ((g.args 9).toNat + (g.args 7).toNat)) 0 st tt
                inputS inputT commonSP p.context.value q.context.value p.modulus q.modulus p.context.bound
                (by simpa [VJ, upd, sInv, sCand, sCnt] using p.context.inverse)
                (by simpa [VJ, upd, sInv, sCand, sCnt] using q.context.inverse)
                p.context.odd (by have := p.context.large; omega) p.context.zero q.context.zero p.unit q.unit
                smallS smallT _ _ _ _ _ _ ⟨cs, ds⟩ e4 f4).1
              refine ⟨?_, trivial⟩
              simpa only [List.append_assoc] using
                congrArg₂ (fun a b : List Leak => a ++ b) eqPrefix
                  (congrArg₂ (fun a b : List Leak => a ++ b) eqSearch eqFinish)

end VG.Proof.Rsa.X86.Recover
