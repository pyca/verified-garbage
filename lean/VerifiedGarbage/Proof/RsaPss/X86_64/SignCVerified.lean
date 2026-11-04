module
public import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCtx
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCtx
public import VerifiedGarbage.Proof.Framework.X86_64.Depth

public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCorrect
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.RsaPss.X86_64.Safe

/-!
# RSASSA-PSS signing on x86-64, around the encoding: the calling convention

`signC_correct`: `signC` meets `signK` and keeps the callee-saved registers,
its return address (which only its frame and calls are below) and MXCSR's
control bits (no instruction loads MXCSR).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.Rsa.X86_64 (chkContract)

variable {tsH tsG : List FnTable} {f : MdFns} {g : Impl.Mgf1.X86_64.Table.Fns} {privN : String}
  {privC : Prog isa}

theorem spAll_of {c : Prog isa} (hC : SpSafe c) : c.allInstrs (fun i => !isa.writesSp i) = true := by
  rw [Code.allInstrs_eq]; exact List.all_eq_true.mpr fun i hi => by rw [hC i hi]; rfl

/-- The calls of `byIdx` keep the stack pointer, and use at most `n` bytes of
stack. -/
theorem byIdx_calls {b : Nat → Prog isa} {n : Nat} : ∀ {is : List Nat},
    (∀ i ∈ is, (b i).allInstrs (fun i => !isa.writesSp i) = true ∧ (b i).x86_64Depth ≤ n) →
    (byIdx b is).allInstrs (fun i => !isa.writesSp i) = true ∧ (byIdx b is).x86_64Depth ≤ n
  | [], _ => ⟨rfl, Nat.zero_le _⟩
  | [i], h => h i (List.mem_singleton_self _)
  | i :: j :: is, h => by
    have ih := byIdx_calls (b := b) (n := n) (is := j :: is) fun k hk => h k (List.mem_cons_of_mem _ hk)
    have hi := h i (List.mem_cons_self ..)
    simp only [byIdx, Code.allInstrs, Code.x86_64Depth, ih.1, hi.1, Bool.and_true]
    exact ⟨rfl, by simp only [Nat.zero_max, Nat.max_le]; exact ⟨hi.2, ih.2⟩⟩

theorem enc_calls (hE : ∀ i ∈ idxs, SpSafe (encode f (ofIdx i) g))
    (hdE : ∀ i ∈ idxs, (encode f (ofIdx i) g).x86_64Depth ≤ encStack) :
    (byIdx (fun i => .call (encName i) (encode f (ofIdx i) g)) idxs).allInstrs (fun i => !isa.writesSp i) = true ∧
      (byIdx (fun i => .call (encName i) (encode f (ofIdx i) g)) idxs).x86_64Depth ≤ encStack + 8 :=
  byIdx_calls fun i hi => ⟨by simp only [Code.allInstrs]; exact spAll_of (hE i hi),
    by simp only [Code.x86_64Depth]; have := hdE i hi; omega⟩

theorem signC_spAll (hE : ∀ i ∈ idxs, SpSafe (encode f (ofIdx i) g))
    (hdE : ∀ i ∈ idxs, (encode f (ofIdx i) g).x86_64Depth ≤ encStack) (hC : SpSafe privC) :
    (Impl.RsaPss.X86_64.signC f g privN privC).allInstrs (fun i => !isa.writesSp i) = true := by
  simp only [Impl.RsaPss.X86_64.signC, signCBody, seqs, Code.allInstrs, (enc_calls hE hdE).1, spAll_of hC, rec_all,
    List.all_append, signFail, Bool.and_true, Bool.true_and]
  rfl

theorem signC_sp (hE : ∀ i ∈ idxs, SpSafe (encode f (ofIdx i) g))
    (hdE : ∀ i ∈ idxs, (encode f (ofIdx i) g).x86_64Depth ≤ encStack) (hC : SpSafe privC) :
    SpSafe (Impl.RsaPss.X86_64.signC f g privN privC) := by
  have h := signC_spAll (privN := privN) hE hdE hC
  rw [Code.allInstrs_eq] at h
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem signC_xd (hdE : ∀ i ∈ idxs, (encode f (ofIdx i) g).x86_64Depth ≤ encStack)
    (hE : ∀ i ∈ idxs, SpSafe (encode f (ofIdx i) g)) (hd : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes) :
    (Impl.RsaPss.X86_64.signC f g privN privC).x86_64Depth ≤ signStack := by
  have := (enc_calls hE hdE).2
  simp only [Impl.RsaPss.X86_64.signC, signCBody, seqs, Code.x86_64Depth, signFail, byteLoop,
    X86_64.Instr.frameBytes, Nat.zero_max, Nat.max_zero]
  unfold signStack Rsa.X86_64.stackBytes frameBytes encStack at *
  omega

theorem signC_correct
    (hsel : ∀ s, (signK tsH tsG).pre s → ∃ i T Hs Gs, ESel f g s i T Hs Gs)
    (hE : ∀ i ∈ idxs, SpSafe (encode f (ofIdx i) g))
    (hdE : ∀ i ∈ idxs, (encode f (ofIdx i) g).x86_64Depth ≤ encStack)
    (hv : ∀ s, chkContract.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContract.post s s')
    (hC : SpSafe privC) (hdC : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes)
    (s : State) (h : (signK tsH tsG).pre s) :
    ∃ t s', Exec isa (Impl.RsaPss.X86_64.signC f g privN privC) s t s' ∧ abiPreserved s s' ∧
      (signK tsH tsG).post s s' := by
  have hp := SPre.of tsH tsG h
  have hd := signC_xd (privN := privN) hdE hE hdC
  obtain ⟨i, T, Hs, Gs, E⟩ := hsel s h
  have hW := X86_64.WP.stackFrame (signC_sp hE hdE hC)
    (by unfold signStack Rsa.X86_64.stackBytes at hd; omega)
    (signC_ok (privN := privN) hE hdE hv hC hdC h E)
  obtain ⟨t, s', he, ⟨hcs, hpost, hmx⟩, hf⟩ := hW
  refine ⟨t, s', he, ⟨hcs, ?_, hmx⟩, hpost⟩
  -- The return address.
  refine Mem.readW_congr fun i hi => hf _ fun r hr hc => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dRo _ (Offset.contains_base _ (by omega) (by omega)) hc
    · exact hp.dRs _ (Offset.contains_base _ (by omega) (by omega)) hc
  · simp only [List.mem_singleton] at hr; subst hr
    have := hp.sp1; have := hp.sp2
    exact Offset.base_disjoint_below (s.gpr .rsp) (n := (Impl.RsaPss.X86_64.signC f g privN privC).x86_64Depth)
      (k := 8) (by unfold signStack at *; omega) _ (Offset.contains_base _ (by omega) (by omega)) hc

end VG.Proof.RsaPss.X86_64
