module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Resume
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Semantics
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Saved
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

/-! ### `MlKem.AArch64.Paired.Restore`, which the modules that import this one used -/

section

/-! # Restore the sampler caller while retaining its accumulated success flag -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64

/-- Registers that may change across one complete paired matrix sample. -/
def pairRegs : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x24]

def pairWorkingRegs : List Reg := pairRegs++Impl.MlKem.AArch64.Paired.saved

theorem restored_keep {initial s t : State} (h : Keep pairWorkingRegs initial s)
    (ht : Only Impl.MlKem.AArch64.Paired.saved s t)
    (hr : ∀r∈Impl.MlKem.AArch64.Paired.saved,t.gpr r=initial.gpr r) :
    Keep pairRegs initial t := by
  refine ⟨?_,ht.rd.trans h.rd,ht.wr.trans h.wr,ht.sp.trans h.sp,
    fun r hp => (ht.vcs r hp).trans (h.vcs r hp)⟩
  intro r hn
  by_cases hs : r∈Impl.MlKem.AArch64.Paired.saved
  · exact hr r hs
  · rw [ht.get r hs,h.get r (by simp only [pairWorkingRegs,List.mem_append,not_or]; exact ⟨hn,hs⟩)]

/-- The restore block does not disturb either the sampled polynomials or x24. -/
theorem restore_ok {initial s : State} {p : Addr}
    (h : Keep pairWorkingRegs initial s) (hp : s.gpr .x19=p)
    (sv : Noise.Saved p initial s.mem) (hc : Covers [⟨p,2048⟩] s.wr) :
    WP isa (.block (Impl.MlKem.AArch64.Paired.saved.zipIdx.reverse.map fun (r,i)=>
      .ldr .x r .x19 (1800+8*i))) s fun t =>
      Keep pairRegs initial t ∧ t.mem=s.mem ∧ t.gpr .x24=s.gpr .x24 := by
  refine WP.mono (Noise.restores_ok hp sv (fun i hi=>?_)) fun t ⟨ht,hr⟩ =>
    ⟨restored_keep h ht hr,ht.mem,ht.get .x24 (by decide)⟩
  exact in_rd_wr (rd:=s.rd) (Noise.inScratch hc (by omega_using [hi]) (by decide))

end VG.Proof.MlKem.AArch64.Paired

end

end

/-! # Successful initial rejection bypasses both continuation blocks -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem full_coeffs {w16 : Bool} {m : Mem} {p : Addr} {L : List Zq}
    (h : Rej8.Scalar.CoeffsW w16 m p L) (hl : L.length=256) :
    CoeffsUpToW w16 m p L.length (Sample.cvW w16 L) (fun _=>0) := by
  intro i hi
  have hh : i<L.length := by omega_using [hl, hi]
  rw [ite_eq_left hh]
  exact h i hh

theorem fast_finish {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s : State}
    (h : ProgressW w16 A B 3 p a b c s)
    (hf : (accepted A 3).length=256 ∧ (accepted B 3).length=256)
    (hs : s.gpr .x24=0 ∨ s.gpr .x24=1) : ResumePostW w16 A B p a b s s := by
  have ea := accepted_full hf.1 (by decide : 3≤5)
  have eb := accepted_full hf.2 (by decide : 3≤5)
  have ca := full_coeffs h.left hf.1
  have cb := full_coeffs h.right hf.2
  refine ⟨Keep.refl _ _,Frame.refl _ _,?_,?_,?_,?_,?_⟩
  · rw [ea]; exact ca
  · exact Sample.reduced_of_coeffs ca
  · rw [eb]; exact cb
  · exact Sample.reduced_of_coeffs cb
  · rw [ea,eb,ite_eq_left hf]
    rcases hs with hs|hs <;> rw [hs] <;> rfl

theorem finish_branch {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s : State}
    (step : ∀{t : State}{n : Nat}, n=3 ∨ n=4 → ProgressW w16 A B n p a b c t →
      t.syms "VG_MLKEM_REJ_SHUFFLE"=c → WP isa (Impl.MlKem.AArch64.Paired.extraStep sha3 w16) t (AdvancedW w16 A B (n+1) p a b c t))
    (h : ProgressW w16 A B 3 p a b c s) (sy : s.syms "VG_MLKEM_REJ_SHUFFLE"=c)
    (hf : (s.gpr .x6).toNat=if (accepted A 3).length=256 ∧ (accepted B 3).length=256 then 1 else 0)
    (hs : s.gpr .x24=0 ∨ s.gpr .x24=1) :
    WP isa (.ite (.zero .x .x6) (Impl.MlKem.AArch64.Paired.extraPair sha3 w16) (.block [])) s
      (ResumePostW w16 A B p a b s) := by
  refine WP.ite (s.gpr .x6 == 0) (eval_zero _ _) (fun _=>resume_ok (sha3 := sha3) step h sy) (fun hz=>?_)
  have full : (accepted A 3).length=256 ∧ (accepted B 3).length=256 := by
    by_contra hh
    have he : s.gpr .x6=0 := BitVec.eq_of_toNat_eq (by rw [hf,ite_eq_right hh]; rfl)
    rw [he] at hz
    contradiction
  exact wp_nil (fast_finish h full hs)

end VG.Proof.MlKem.AArch64.Paired
