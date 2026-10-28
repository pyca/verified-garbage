module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputePair
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputeFn
import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.TimeCompute
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeValid
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeBase
import VerifiedGarbage.Proof.Bignum.X86.PublicArgumentTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeInputs
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.In
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeExp

/-! # The precomputation of a valid modulus leaks only the public lengths and pointers

Argument 1's overwrite is checked by the taint analysis; the computation
after it is related on states whose permissions are narrowed to `pre` and
the working space (`compute_relCT`), and the runs from the states
themselves leak the same traces (`relCT_narrow`).
-/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86.PrecomputeRt
open VG.Proof.Bignum.X86.PublicRt (wb Both)
open VG.Proof.Bignum.X86.PublicContext (pcArgs pcSetWidth_ok pcCompute_ok pcBytesAt_frame)

def PrecomputeValidPair (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s t : State) : Prop :=
  PrecomputePair base bytes len args s t ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) len)) len = true ∧
    Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len = Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) len

section
variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- The permissions of `compute`'s narrowed runs: everything readable, `pre` and the working space
writable. -/
abbrev pcNarrowW (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) : List Region :=
  [⟨byteAddr (args 0), 2 * wb len⟩, ⟨base, bytes⟩]

theorem narrow_pcIn {s : State} (h : PcIn base bytes len args s) :
    PcIn base bytes len args (s.withRegions (s.rd ++ s.wr) (pcNarrowW base bytes len args)) := by
  refine ⟨⟨h.scratch.edi, by simp, h.scratch.nowrap, h.scratch.stk⟩, h.lower, h.upper, h.space,
    fun i hi => ⟨⟨?_, (h.stack i hi).stack.apart⟩, (h.stack i hi).value⟩, h.wLen, h.nLen, h.hbase, h.hbytes,
    h.outFit, h.nFit, ⟨_, List.mem_cons_self .., Region.contains_self _ _⟩, ?_, h.outApart, h.nApart, h.outArgs⟩
  · obtain ⟨r, hr, hc⟩ := (h.stack i hi).stack.read
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · obtain ⟨r, hr, hc⟩ := h.nRead; exact ⟨r, List.mem_append_left _ hr, hc⟩

/-- What the runs of `compute` from the states themselves need. -/
def PcAt (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  PcIn base bytes len args s ∧ CallRoom (s.gpr .esp) base bytes ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
    s.gpr .esp = sp ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 28⟩ ⟨byteAddr (args 0), 2 * wb len⟩ ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 28⟩ ⟨base, bytes⟩

theorem compute_narrow_relCT (sp : BitVec 32) :
    RelCT isa (Both (PcAt base bytes len args sp)) PrecomputeFn.compute fun _ _ => True := by
  have narrow : ∀ {s : State}, PcAt base bytes len args sp s →
      CIn base bytes len args sp (s.withRegions (s.rd ++ s.wr) (pcNarrowW base bytes len args)) := by
    intro s ⟨h, R, top, e, V, Do, Ds⟩
    refine ⟨narrow_pcIn h, R, top, ⟨top, fun r hr => ?_⟩, e, V⟩
    simp only [State.withRegions, pcNarrowW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Do
    · exact Ds
  refine VG.Proof.Bignum.X86.PublicRt.relCT_narrow (Pn := Both (CIn base bytes len args sp))
    (fun s => s.rd ++ s.wr) (fun _ => pcNarrowW base bytes len args) (fun s₁ s₂ ⟨S₁, S₂⟩ => ?_) (compute_relCT sp)
  have cov : ∀ {s : State}, PcAt base bytes len args sp s → Covers (pcNarrowW base bytes len args) s.wr := by
    intro s S
    rintro a n ⟨r, hr, hc⟩
    simp only [pcNarrowW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Covers.one S.1.outWrite a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, S.1.scratch.wr, hc⟩
  have wp : ∀ {s : State}, PcAt base bytes len args sp s →
      ∃ F, WP isa PrecomputeFn.compute (s.withRegions (s.rd ++ s.wr) (pcNarrowW base bytes len args)) F := by
    intro s S
    obtain ⟨h, R, top, _, _, V⟩ := narrow S
    exact ⟨_, pcCompute_ok h R top V⟩
  exact ⟨Covers.append_left (Covers.refl _) (Covers.right (cov S₁)), cov S₁,
    Covers.append_left (Covers.refl _) (Covers.right (cov S₂)), cov S₂, wp S₁, wp S₂, narrow S₁, narrow S₂⟩

theorem pcAt_of {s u : State} (h : PrecomputeInputs base bytes len args s)
    (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true)
    (P : PcIn base bytes len (pcArgs len args) u) (F : Frame [⟨addr (s.gpr .esp) 8, 4⟩] s.mem u.mem)
    (K : Keeps [.eax] s u) : PcAt base bytes len (pcArgs len args) (s.gpr .esp) u := by
  have esp : u.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  have a0 : pcArgs len args 0 = args 0 := by simp [pcArgs]
  have a2 : pcArgs len args 2 = args 2 := by simp [pcArgs]
  have W : 2 * wb len = 16 * Spec.Rsa.modulusWords len := by simp only [wb]; omega
  have N : Spec.Rsa.bytesAt u.mem (byteAddr (args 2)) len = Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len := by
    refine pcBytesAt_frame F (fun r hr => ?_) (by have := h.upper; omega)
    rw [List.mem_singleton.mp hr]
    have := h.nArg
    simpa only [stackAddress] using this
  refine ⟨P, by rw [esp]; exact h.room, by rw [esp]; exact h.top, esp, by rw [a2, N]; exact valid,
    by rw [esp, a0, W]; exact h.spOut, by rw [esp]; exact h.spScratch⟩

end

theorem precomputeValid_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (PrecomputeValidPair base bytes len args) PrecomputeFn.valid (fun _ _ => True) := by
  intro s t tr ur sf tf H E F
  unfold PrecomputeFn.valid at E F
  cases E with
  | @seq _ _ _ u _ _ _ E1 E2 =>
    cases F with
    | @seq _ _ _ v _ _ _ F1 F2 =>
      have CT : RelCT isa (VG.X86.Taint.Agree argumentTaint) (.block PrecomputeFn.setWidth)
          (VG.X86.Taint.Agree argumentTaint) := checkedProgramChange (hint := .block []) rfl rfl
      have T1 := (CT _ _ _ _ _ _ H.1.agree E1 F1).1
      obtain ⟨Pu, Fu, Ku⟩ := wp_result (pcSetWidth_ok H.1.left) E1
      obtain ⟨Pv, Fv, Kv⟩ := wp_result (pcSetWidth_ok H.1.right) F1
      have Cu := pcAt_of H.1.left H.2.1 Pu Fu Ku
      have Cv := pcAt_of H.1.right H.2.2.1 Pv Fv Kv
      rw [← H.1.sp] at Cv
      have T2 := (compute_narrow_relCT (s.gpr .esp) _ _ _ _ _ _ ⟨Cu, Cv⟩ E2 F2).1
      exact ⟨by rw [T1, T2], trivial⟩

end VG.Proof.Bignum.X86
