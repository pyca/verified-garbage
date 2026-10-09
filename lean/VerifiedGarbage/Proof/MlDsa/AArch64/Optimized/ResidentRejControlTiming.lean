import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourPhaseTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWidePhaseTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarPhaseTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParse

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

theorem control_pair {P Q R S : State → Prop} {c : Prog isa}
    (hsp : ∀s t,P s → Q t → s.sp=t.sp)
    (hl : ∀s,P s → WP isa c s R) (hr : ∀s,Q s → WP isa c s S)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (hc : (taint.check (Taint.ofRegs []) c hint).isSome=true) :
    RelCT isa (fun s t => P s ∧ Q t) c (fun s t => R s ∧ S t) := by
  have hh : RelCT isa (fun s t => P s ∧ Q t) c (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ h => ⟨hsp _ _ h.1 h.2,by simp [Taint.ofRegs,RegSet.mem_ofList]⟩) hc
  exact (hh.wp (fun _ _ h => ⟨hl _ h.1,hr _ h.2⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem fourSetup_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hsp : σ.sp=τ.sp) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (.block (vectorSetup++guard))
      (fun s t => FourReady σ b p n d L s ∧ FourReady τ b p n d L t) :=
  control_pair (fun _ _ hs ht => hs.keep.sp.trans (hsp.trans ht.keep.sp.symm))
    (fun _ h => fourSetup_ok h) (fun _ h => fourSetup_ok h) (by taint_decide)

theorem wideControl_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hsp : σ.sp=τ.sp) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (.block (([.movz .x .x17 16 0] : List Instr)++wideGuard))
      (fun s t => WideReady σ b p n d L s ∧ WideReady τ b p n d L t) :=
  control_pair (fun _ _ hs ht => hs.keep.sp.trans (hsp.trans ht.keep.sp.symm))
    (fun _ h => wideControl_ok h) (fun _ h => wideControl_ok h) (by taint_decide)

theorem parseFour_relCT (v : Nat) {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hmod : d%4=n%4) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (parse4 v) (fun _ _ => True) := by
  unfold parse4
  apply RelCT.seq (fourSetup_relCT hsp)
  apply RelCT.seq (fourPhase_relCT hs ht hm hsp hmod)
  exact RelCT.exists_ (fun j => scalarPhase_relCT hs ht hm hsp (d := j))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
