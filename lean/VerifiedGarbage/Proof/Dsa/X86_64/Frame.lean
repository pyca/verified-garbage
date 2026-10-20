module

public import VerifiedGarbage.Proof.Dsa.X86_64.Product
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Bignum.CrtExp
import Mathlib.Tactic.Set

/-! # Framing the DSA child workspaces -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Child header temporaries, arrays and exponentiation table. The link,
modulus width and array pointers are outside this region. -/
def workRanges (w : Nat) : List (Nat × Nat) := [(136, slot w 8 + tabBytes w - 136)]

theorem workRanges_ok (w : Nat) : ∀ r ∈ workRanges w,
    8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 8 + tabBytes w := by
  have : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega
  simp only [workRanges, List.mem_singleton, forall_eq]
  omega

/-- Array writes are confined to the child's mutable region. -/
theorem arrays_work {mem mem' : Mem} {B : Addr} {w : Nat} {js : List Nat}
    (hf : Arrays B w js mem mem') (hj : ∀ j ∈ js, j < 8) :
    Frm B (workRanges w) mem mem' := by
  intro x hx
  apply hf x
  intro j hmem
  have hi := slot_le (w := w) (hj j hmem)
  have lo : 256 ≤ slot w j := by unfold slot hdrBytes; omega
  have h := hx (136, slot w 8 + tabBytes w - 136) (List.mem_singleton_self _)
  omega

/-- Recover the complete child context after array-only writes. -/
theorem arrays_context {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) {js : List Nat}
    (hf : Arrays (off B o) wx js s.mem t.mem) (hj : ∀ j ∈ js, j < 8)
    (hk : Keep mmRegs s t) : SubCtx t B Z o w wx minv :=
  hc.of_frmT (arrays_work hf hj) (workRanges_ok wx) hk.2.2 (hk.gpr (by decide))

/-- All exponentiation changes fit the same mutable region. -/
theorem exp_work {s t : State} {B : Addr} {w : Nat}
    (hf : Frm B (crtExpRanges w) s.mem t.mem) : Frm B (workRanges w) s.mem t.mem := by
  intro x hx
  apply hf x
  intro r hr
  have ho := crtExpRanges_ok w r hr
  have h := hx (136, slot w 8 + tabBytes w - 136) (List.mem_singleton_self _)
  have : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega
  omega

/-- A child's writes leave the parent's call header unchanged. -/
theorem work_parent {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hf : Frm (off B o) (workRanges wx) s.mem t.mem)
    {i : Nat} (hi : i < 32) : word t.mem B (8 * i) = word s.mem B (8 * i) := by
  have ho := hc.lo
  have hn := hc.scr.nowrap
  have hhi := hc.hi
  have : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega
  have : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  exact hf.word_below (fun r hr => (workRanges_ok wx r hr).2) (by omega) (by omega) (by omega)

/-- A source outside the active arithmetic prefix remains unchanged. -/
theorem work_source {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hf : Frm (off B o) (workRanges wx) s.mem t.mem)
    (hk : Keep mmRegs s t) {p : Addr} {bytes : List Byte} (hs : Src s B Z p bytes) :
    Src t B Z p bytes := by
  have hn := hc.scr.nowrap
  have hhi := hc.hi
  have hsize : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  apply hs.congrK _ hk
  apply InScr.of_frm (hf.rebase (by omega) (fun r hr => by have := workRanges_ok wx r hr; omega))
  intro r hr
  simp only [shiftRanges, workRanges, List.map_cons, List.map_nil, List.mem_singleton] at hr
  subst r
  simp only
  omega

/-- The modulus and its inverse survive the fixed-window exponentiation. -/
theorem modCtx_exp {s t : State} {B : Addr} {Z w m : Nat} {minv : BitVec 64}
    (hc : ModCtx s B Z w minv m) (ht : Good t B Z w minv)
    (hf : Frm B (crtExpRanges w) s.mem t.mem) (hZ : slot w 8 ≤ Z) :
    ModCtx t B Z w minv m := by
  have hn := hc.good.scr.nowrap
  have hsep := crtExpRanges_arr w (j := aN) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hslot := slot_le (w := w) (show aN < 8 by decide)
  refine ⟨ht, ?_, ?_⟩
  · rw [hf.wv_eq (fun r hr => by have := hsep r hr; omega) (by omega)]
    exact hc.modulus
  · rw [hf.word_eq (fun r hr => by have := hsep r hr; omega) (by omega)]
    exact hc.inverse

end VG.Proof.Dsa.X86_64
