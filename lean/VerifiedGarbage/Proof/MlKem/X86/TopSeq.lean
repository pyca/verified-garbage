module

public import VerifiedGarbage.Proof.MlKem.X86.Common
public import VerifiedGarbage.Proof.MlKem.X86.Top
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.PolyContract
import VerifiedGarbage.Proof.MlKem.X86.TopCall
import VerifiedGarbage.Proof.MlKem.X86.Mul
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.MlKem.X86.Cbd
import VerifiedGarbage.Proof.MlKem.X86.Encode12
import VerifiedGarbage.Proof.MlKem.X86.Decode12

/-! ### `MlKem.X86.TopPrim2`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86 (32-bit): calls of the primitives of two arguments

As `TopPrim.lean`, for `vg_mlkem_add` and `vg_mlkem_sub` (`acc_call`),
`vg_mlkem_cbd2`, `vg_mlkem_encode12` and `vg_mlkem_decode12`, with their first
argument in `eax` and their second in `ecx`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

theorem cbd2_nosp : NoSp Impl.MlKem.X86.cbd2 := NoSp.of_all (by decide +kernel)
theorem cbd2_stack : stackUse Impl.MlKem.X86.cbd2 = 16 := by decide +kernel
theorem encode12_nosp : NoSp Impl.MlKem.X86.encode12 := NoSp.of_all (by decide +kernel)
theorem encode12_stack : stackUse Impl.MlKem.X86.encode12 = 16 := by decide +kernel
theorem decode12_nosp : NoSp Impl.MlKem.X86.decode12 := NoSp.of_all (by decide +kernel)
theorem decode12_stack : stackUse Impl.MlKem.X86.decode12 = 16 := by decide +kernel
theorem add_nosp : NoSp Impl.MlKem.X86.add := NoSp.of_all (by decide +kernel)
theorem add_stack : stackUse Impl.MlKem.X86.add = 16 := by decide +kernel
theorem sub_nosp : NoSp Impl.MlKem.X86.sub := NoSp.of_all (by decide +kernel)
theorem sub_stack : stackUse Impl.MlKem.X86.sub = 16 := by decide +kernel

/-- `f ← op(f, g)` (`vg_mlkem_add` or `vg_mlkem_sub`), with `f` at `(fa, fo)` and `g` at `(ga, go)`. -/
theorem acc_call {op : Poly → Poly → Poly} {nm : String} {c : Prog isa}
    (hv : Verified X86.target c (accSig.contract X86.abi (pre := fun f g m => Reduced m f ∧ Reduced m g)
      (post := fun f g m m' _ => PolyIs m' f (op (polyAt m f) (polyAt m g))) (writeArgs := true) (stack := 16)))
    (hsp : NoSp c) (hst : stackUse c = 16) (fa fo ga go : Nat)
    (hc : (Y.okW ⟨fa, fo, 1024⟩ && Y.ok ⟨ga, go, 1024⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨ga, go, 1024⟩) = true) (hN : 44 ≤ Y.stk)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧
      s.gpr .ecx = Buf.ptr s₀ ⟨ga, go, 1024⟩ ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧ Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) (op (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callWith [.ecx, .eax] nm c) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨h0, h1⟩, d01⟩ := hc
  have h0' := (Lay.okW_iff.mp h0).1
  have h1' := h1
  refine call_piece hv hsp (by decide) (by decide)
    (by rw [hst]; simp only [List.length_cons, List.length_nil]; omega_arith)
    (fun s₀ => [Buf.rgn s₀ ⟨ga, go, 1024⟩]) (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (E1 s₀) 8])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => wr_sub hp (bs := [⟨fa, fo, 1024⟩]) (by simp [h0]) (by omega_arith))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · obtain ⟨h, hax, hcx, x0, x1⟩ := hA s₀ s hp ha
    have hE' : 28 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact ctx_E hp h (N := 28) (by omega_arith)
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      rw [h.esp]; simp only [List.length_cons, List.length_nil]; omega_arith
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨ga, go, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have eA : argAddr (pushed [.ecx, .eax] s).callEntry 0 = (E1 s₀ - BitVec.ofNat 32 8).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.ecx, .eax] s).callEntry.gpr .esp = E1 s₀ - BitVec.ofNat 32 12 := by
      rw [callEntry_esp', h.esp]; rfl
    have b0 := Buf.stkD hp h0' (N := 4 * 2 + 4 + 16) (by omega_arith)
    have b1 := Buf.stkD hp h1' (N := 4 * 2 + 4 + 16) (by omega_arith)
    obtain ⟨r0₁, r0₂, r0₃⟩ := entry_regions hE' b0
    obtain ⟨r1₁, r1₂, r1₃⟩ := entry_regions hE' b1
    obtain ⟨rA₂, rA₃⟩ := entry_self (E := E1 s₀) (k := 2) (K := 16) hE'
    have cv := covers_of (s := s) (n := 2) (rd := [Buf.rgn s₀ ⟨ga, go, 1024⟩])
      (wr := [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (E1 s₀) 8])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl
        exact Buf.within hp h1' h.rd h.wr) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (Buf.withinW hp h0' (Lay.okW_iff.mp h0).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    -- The callee's entry state stays opaque to `sig_pre`, which would unfold it.
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    sig_pre [accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    have ek := @ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega_arith)
    refine ⟨by rw [sub_toNat (by omega_arith)]; omega_arith, by rw [sub_toNat (by omega_arith)]; have := (E1 s₀).isLt; omega_arith,
      trivial, trivial, Buf.disj hp h0' h1' d01, r0₁, r1₁, r0₂, r1₂, rA₂, r0₃, r1₃, rA₃,
      Buf.fit hp h0', Buf.fit hp h1', reduced_congr (ek h0') x0, reduced_congr (ek h1') x1⟩
  · obtain ⟨h, hax, hcx, -⟩ := hA s₀ s hp ha
    obtain ⟨h', hax', hcx', -⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hcx, hcx', hq.ptr h1']
      · rw [hax, hax', hq.ptr h0']
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 28) (by omega_arith); simp only [List.length_cons, List.length_nil]; omega_arith
    refine ⟨by simp only [Buf.rgn, hq.ptr h1'], by simp only [Buf.rgn, hq.ptr h0', hq.E1], ?_⟩
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    generalize he' : (pushed [.ecx, .eax] s').callEntry = e'
    sig_pub [accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · obtain ⟨h, hax, hcx, -⟩ := hA s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 28) (by omega_arith); simp only [List.length_cons, List.length_nil]; omega_arith
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨ga, go, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have ek := @ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega_arith)
    generalize he : (pushed [.ecx, .eax] s).callEntry = e at post
    sig_post [accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1] at post
    rw [polyAt_congr (ek h0'), polyAt_congr (ek h1')] at post
    replace post := polyIs_congr (lost_keep hp h (k := 2) (by omega_arith) m₂ h0') post
    exact hQ s₀ s s' hp ha h' e₃ (fr_conv hp (a := 8) (N := 28) (by omega_arith) (by omega_arith)
      (by rw [hst] at fr; exact fr)) post


/-- `f ← SamplePolyCBD₂(b)`, with the 128 bytes `b` at `(ba, bo)` and `f` at `(fa, fo)`. -/
theorem cbd2_call (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 128⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 128⟩ ⟨fa, fo, 1024⟩) = true) (hN : 44 ≤ Y.stk)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨ba, bo, 128⟩ ∧
      s.gpr .ecx = Buf.ptr s₀ ⟨fa, fo, 1024⟩)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) (samplePolyCBD 2 (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 128⟩) 128)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callWith [.ecx, .eax] "vg_mlkem_cbd2" Impl.MlKem.X86.cbd2) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨h0, h1⟩, d01⟩ := hc
  have h0' := h0
  have h1' := (Lay.okW_iff.mp h1).1
  refine call_piece Cbd.verified cbd2_nosp (by decide) (by decide)
    (by rw [cbd2_stack]; simp only [List.length_cons, List.length_nil]; omega_arith)
    (fun s₀ => [Buf.rgn s₀ ⟨ba, bo, 128⟩]) (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (E1 s₀) 8])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => wr_sub hp (bs := [⟨fa, fo, 1024⟩]) (by simp [h1]) (by omega_arith))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · obtain ⟨h, hax, hcx⟩ := hA s₀ s hp ha
    have hE' : 28 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact ctx_E hp h (N := 28) (by omega_arith)
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      rw [h.esp]; simp only [List.length_cons, List.length_nil]; omega_arith
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨ba, bo, 128⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have eA : argAddr (pushed [.ecx, .eax] s).callEntry 0 = (E1 s₀ - BitVec.ofNat 32 8).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.ecx, .eax] s).callEntry.gpr .esp = E1 s₀ - BitVec.ofNat 32 12 := by
      rw [callEntry_esp', h.esp]; rfl
    have b0 := Buf.stkD hp h0' (N := 4 * 2 + 4 + 16) (by omega_arith)
    have b1 := Buf.stkD hp h1' (N := 4 * 2 + 4 + 16) (by omega_arith)
    obtain ⟨r0₁, r0₂, r0₃⟩ := entry_regions hE' b0
    obtain ⟨r1₁, r1₂, r1₃⟩ := entry_regions hE' b1
    obtain ⟨rA₂, rA₃⟩ := entry_self (E := E1 s₀) (k := 2) (K := 16) hE'
    have cv := covers_of (s := s) (n := 2) (rd := [Buf.rgn s₀ ⟨ba, bo, 128⟩])
      (wr := [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (E1 s₀) 8])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl
        exact Buf.within hp h0' h.rd h.wr) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (Buf.withinW hp h1' (Lay.okW_iff.mp h1).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    -- The callee's entry state stays opaque to `sig_pre`, which would unfold it.
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    sig_pre [cbd2Contract, cbd2Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    have ek := @ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega_arith)
    refine ⟨by rw [sub_toNat (by omega_arith)]; omega_arith, by rw [sub_toNat (by omega_arith)]; have := (E1 s₀).isLt; omega_arith,
      trivial, trivial, Buf.disj hp h0' h1' d01, r0₁, r1₁, r0₂, r1₂, rA₂, r0₃, r1₃, rA₃,
      Buf.fit hp h0', Buf.fit hp h1'⟩
  · obtain ⟨h, hax, hcx⟩ := hA s₀ s hp ha
    obtain ⟨h', hax', hcx'⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hcx, hcx', hq.ptr h1']
      · rw [hax, hax', hq.ptr h0']
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 28) (by omega_arith); simp only [List.length_cons, List.length_nil]; omega_arith
    refine ⟨by simp only [Buf.rgn, hq.ptr h0'], by simp only [Buf.rgn, hq.ptr h1', hq.E1], ?_⟩
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    generalize he' : (pushed [.ecx, .eax] s').callEntry = e'
    sig_pub [cbd2Contract, cbd2Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · obtain ⟨h, hax, hcx⟩ := hA s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 28) (by omega_arith); simp only [List.length_cons, List.length_nil]; omega_arith
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨ba, bo, 128⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have ek := @ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega_arith)
    generalize he : (pushed [.ecx, .eax] s).callEntry = e at post
    sig_post [cbd2Contract, cbd2Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1] at post
    rw [bytesAt_congr (ek h0')] at post
    replace post := polyIs_congr (lost_keep hp h (k := 2) (by omega_arith) m₂ h1') post
    exact hQ s₀ s s' hp ha h' e₃ (fr_conv hp (a := 8) (N := 28) (by omega_arith) (by omega_arith)
      (by rw [cbd2_stack] at fr; exact fr)) post


/-- `out ← ByteEncode₁₂(f)`, with `f` at `(fa, fo)` and the 384 bytes `out` at `(oa, oo)`. -/
theorem encode12_call (fa fo oa oo : Nat)
    (hc : (Y.ok ⟨fa, fo, 1024⟩ && Y.okW ⟨oa, oo, 384⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨oa, oo, 384⟩) = true) (hN : 44 ≤ Y.stk)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧
      s.gpr .ecx = Buf.ptr s₀ ⟨oa, oo, 384⟩ ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨oa, oo, 384⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, 384⟩) 384 = encode12 (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callWith [.ecx, .eax] "vg_mlkem_encode12" Impl.MlKem.X86.encode12) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨h0, h1⟩, d01⟩ := hc
  have h0' := h0
  have h1' := (Lay.okW_iff.mp h1).1
  refine call_piece Encode12.verified encode12_nosp (by decide) (by decide)
    (by rw [encode12_stack]; simp only [List.length_cons, List.length_nil]; omega_arith)
    (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩]) (fun s₀ => [Buf.rgn s₀ ⟨oa, oo, 384⟩] ++ [below (E1 s₀) 8])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => wr_sub hp (bs := [⟨oa, oo, 384⟩]) (by simp [h1]) (by omega_arith))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · obtain ⟨h, hax, hcx, x0⟩ := hA s₀ s hp ha
    have hE' : 28 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact ctx_E hp h (N := 28) (by omega_arith)
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      rw [h.esp]; simp only [List.length_cons, List.length_nil]; omega_arith
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨oa, oo, 384⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have eA : argAddr (pushed [.ecx, .eax] s).callEntry 0 = (E1 s₀ - BitVec.ofNat 32 8).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.ecx, .eax] s).callEntry.gpr .esp = E1 s₀ - BitVec.ofNat 32 12 := by
      rw [callEntry_esp', h.esp]; rfl
    have b0 := Buf.stkD hp h0' (N := 4 * 2 + 4 + 16) (by omega_arith)
    have b1 := Buf.stkD hp h1' (N := 4 * 2 + 4 + 16) (by omega_arith)
    obtain ⟨r0₁, r0₂, r0₃⟩ := entry_regions hE' b0
    obtain ⟨r1₁, r1₂, r1₃⟩ := entry_regions hE' b1
    obtain ⟨rA₂, rA₃⟩ := entry_self (E := E1 s₀) (k := 2) (K := 16) hE'
    have cv := covers_of (s := s) (n := 2) (rd := [Buf.rgn s₀ ⟨fa, fo, 1024⟩])
      (wr := [Buf.rgn s₀ ⟨oa, oo, 384⟩] ++ [below (E1 s₀) 8])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl
        exact Buf.within hp h0' h.rd h.wr) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (Buf.withinW hp h1' (Lay.okW_iff.mp h1).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    -- The callee's entry state stays opaque to `sig_pre`, which would unfold it.
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    sig_pre [encode12Contract, encode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    have ek := @ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega_arith)
    refine ⟨by rw [sub_toNat (by omega_arith)]; omega_arith, by rw [sub_toNat (by omega_arith)]; have := (E1 s₀).isLt; omega_arith,
      trivial, trivial, Buf.disj hp h0' h1' d01, r0₁, r1₁, r0₂, r1₂, rA₂, r0₃, r1₃, rA₃,
      Buf.fit hp h0', Buf.fit hp h1', reduced_congr (ek h0') x0⟩
  · obtain ⟨h, hax, hcx, -⟩ := hA s₀ s hp ha
    obtain ⟨h', hax', hcx', -⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hcx, hcx', hq.ptr h1']
      · rw [hax, hax', hq.ptr h0']
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 28) (by omega_arith); simp only [List.length_cons, List.length_nil]; omega_arith
    refine ⟨by simp only [Buf.rgn, hq.ptr h0'], by simp only [Buf.rgn, hq.ptr h1', hq.E1], ?_⟩
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    generalize he' : (pushed [.ecx, .eax] s').callEntry = e'
    sig_pub [encode12Contract, encode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · obtain ⟨h, hax, hcx, -⟩ := hA s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 28) (by omega_arith); simp only [List.length_cons, List.length_nil]; omega_arith
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨oa, oo, 384⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have ek := @ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega_arith)
    generalize he : (pushed [.ecx, .eax] s).callEntry = e at post
    sig_post [encode12Contract, encode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1] at post
    rw [polyAt_congr (ek h0')] at post
    replace post := (bytesAt_congr (lost_keep hp h (k := 2) (by omega_arith) m₂ h1')).trans post
    exact hQ s₀ s s' hp ha h' e₃ (fr_conv hp (a := 8) (N := 28) (by omega_arith) (by omega_arith)
      (by rw [encode12_stack] at fr; exact fr)) post


/-- `f ← ByteDecode₁₂(b)`, with the 384 bytes `b` at `(ba, bo)` and `f` at `(fa, fo)`. -/
theorem decode12_call (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 384⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 384⟩ ⟨fa, fo, 1024⟩) = true) (hN : 44 ≤ Y.stk)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨ba, bo, 384⟩ ∧
      s.gpr .ecx = Buf.ptr s₀ ⟨fa, fo, 1024⟩)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) (decode12 (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 384⟩) 384)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callWith [.ecx, .eax] "vg_mlkem_decode12" Impl.MlKem.X86.decode12) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨h0, h1⟩, d01⟩ := hc
  have h0' := h0
  have h1' := (Lay.okW_iff.mp h1).1
  refine call_piece Decode12.verified decode12_nosp (by decide) (by decide)
    (by rw [decode12_stack]; simp only [List.length_cons, List.length_nil]; omega_arith)
    (fun s₀ => [Buf.rgn s₀ ⟨ba, bo, 384⟩]) (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (E1 s₀) 8])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => wr_sub hp (bs := [⟨fa, fo, 1024⟩]) (by simp [h1]) (by omega_arith))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · obtain ⟨h, hax, hcx⟩ := hA s₀ s hp ha
    have hE' : 28 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact ctx_E hp h (N := 28) (by omega_arith)
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      rw [h.esp]; simp only [List.length_cons, List.length_nil]; omega_arith
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨ba, bo, 384⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have eA : argAddr (pushed [.ecx, .eax] s).callEntry 0 = (E1 s₀ - BitVec.ofNat 32 8).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.ecx, .eax] s).callEntry.gpr .esp = E1 s₀ - BitVec.ofNat 32 12 := by
      rw [callEntry_esp', h.esp]; rfl
    have b0 := Buf.stkD hp h0' (N := 4 * 2 + 4 + 16) (by omega_arith)
    have b1 := Buf.stkD hp h1' (N := 4 * 2 + 4 + 16) (by omega_arith)
    obtain ⟨r0₁, r0₂, r0₃⟩ := entry_regions hE' b0
    obtain ⟨r1₁, r1₂, r1₃⟩ := entry_regions hE' b1
    obtain ⟨rA₂, rA₃⟩ := entry_self (E := E1 s₀) (k := 2) (K := 16) hE'
    have cv := covers_of (s := s) (n := 2) (rd := [Buf.rgn s₀ ⟨ba, bo, 384⟩])
      (wr := [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (E1 s₀) 8])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl
        exact Buf.within hp h0' h.rd h.wr) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (Buf.withinW hp h1' (Lay.okW_iff.mp h1).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    -- The callee's entry state stays opaque to `sig_pre`, which would unfold it.
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    sig_pre [decode12Contract, decode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    have ek := @ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega_arith)
    refine ⟨by rw [sub_toNat (by omega_arith)]; omega_arith, by rw [sub_toNat (by omega_arith)]; have := (E1 s₀).isLt; omega_arith,
      trivial, trivial, Buf.disj hp h0' h1' d01, r0₁, r1₁, r0₂, r1₂, rA₂, r0₃, r1₃, rA₃,
      Buf.fit hp h0', Buf.fit hp h1'⟩
  · obtain ⟨h, hax, hcx⟩ := hA s₀ s hp ha
    obtain ⟨h', hax', hcx'⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hcx, hcx', hq.ptr h1']
      · rw [hax, hax', hq.ptr h0']
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 28) (by omega_arith); simp only [List.length_cons, List.length_nil]; omega_arith
    refine ⟨by simp only [Buf.rgn, hq.ptr h0'], by simp only [Buf.rgn, hq.ptr h1', hq.E1], ?_⟩
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    generalize he' : (pushed [.ecx, .eax] s').callEntry = e'
    sig_pub [decode12Contract, decode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · obtain ⟨h, hax, hcx⟩ := hA s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 28) (by omega_arith); simp only [List.length_cons, List.length_nil]; omega_arith
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨ba, bo, 384⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have ek := @ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega_arith)
    generalize he : (pushed [.ecx, .eax] s).callEntry = e at post
    sig_post [decode12Contract, decode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1] at post
    rw [bytesAt_congr (ek h0')] at post
    replace post := polyIs_congr (lost_keep hp h (k := 2) (by omega_arith) m₂ h1') post
    exact hQ s₀ s s' hp ha h' e₃ (fr_conv hp (a := 8) (N := 28) (by omega_arith) (by omega_arith)
      (by rw [decode12_stack] at fr; exact fr)) post


end VG.Proof.MlKem.X86.Top

end

end

/-! ### `MlKem.X86.TopPrim`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86 (32-bit): calls of the primitives in the top-level functions

Each primitive is called (`call_piece`) with its buffers named as `Buf`s, from
registers holding their addresses; its contract's precondition
(`Sig.contract`) at the callee's entry comes from `Ctx` and the buffers'
layout, and its postcondition is restated on the caller's memory.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

theorem ntt_nosp : NoSp Impl.MlKem.X86.ntt := NoSp.of_all (by decide +kernel)
theorem ntt_stack : stackUse Impl.MlKem.X86.ntt = 16 := by decide +kernel
theorem nttInv_nosp : NoSp Impl.MlKem.X86.nttInv := NoSp.of_all (by decide +kernel)
theorem nttInv_stack : stackUse Impl.MlKem.X86.nttInv = 16 := by decide +kernel

/-- `NTT` or `NTT⁻¹` in place, of the polynomial at `(fa, fo)`, with the scratch at `(sa, so)`. -/
theorem inPlace_call {t : Poly → Poly} {nm : String} {c : Prog isa}
    (hv : Verified X86.target c (inPlaceContract X86.abi t 16)) (hsp : NoSp c) (hst : stackUse c = 16)
    (fa fo sa so : Nat)
    (hc : (Y.okW ⟨fa, fo, 1024⟩ && Y.okW ⟨sa, so, 1024⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨sa, so, 1024⟩) = true)
    (hN : 44 ≤ Y.stk)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧
      s.gpr .ecx = Buf.ptr s₀ ⟨sa, so, 1024⟩ ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨fa, fo, 1024⟩, ⟨sa, so, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) (t (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callWith [.ecx, .eax] nm c) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hF, hS⟩, dFS⟩ := hc
  obtain hF' := (Lay.okW_iff.mp hF).1
  obtain hS' := (Lay.okW_iff.mp hS).1
  refine call_piece hv hsp (by decide) (by decide) (by rw [hst]; simp only [List.length_cons, List.length_nil]; omega_arith)
    (fun _ => []) (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩, Buf.rgn s₀ ⟨sa, so, 1024⟩, below (E1 s₀) 8])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_) (fun s₀ hp r hr => ?_)
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · obtain ⟨h, hax, hcx, hred⟩ := hA s₀ s hp ha
    obtain hE := ctx_E hp h (N := 28) (by omega_arith)
    obtain fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      simp only [List.length_cons, List.length_nil]; omega_arith
    obtain a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    obtain a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨sa, so, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    obtain eA : argAddr (pushed [.ecx, .eax] s).callEntry 0 = (E1 s₀ - BitVec.ofNat 32 8).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    obtain eSp : (pushed [.ecx, .eax] s).callEntry.gpr .esp = E1 s₀ - BitVec.ofNat 32 12 := by
      rw [callEntry_esp', h.esp]; rfl
    obtain hE' : 28 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact hE
    obtain bF := Buf.stkD hp hF' (N := 4 * 2 + 4 + 16) (by omega_arith)
    obtain bS := Buf.stkD hp hS' (N := 4 * 2 + 4 + 16) (by omega_arith)
    obtain ⟨rF₁, rF₂, rF₃⟩ := entry_regions hE' bF
    obtain ⟨rS₁, rS₂, rS₃⟩ := entry_regions hE' bS
    obtain ⟨rA₂, rA₃⟩ := entry_self (E := E1 s₀) (k := 2) (K := 16) hE'
    obtain ef := callEntry_frame fit (by decide)
    obtain cv := covers_of (s := s) (n := 2) (rd := []) (wr := [Buf.rgn s₀ ⟨fa, fo, 1024⟩,
        Buf.rgn s₀ ⟨sa, so, 1024⟩, below (E1 s₀) 8]) (fun r hr => absurd hr (by simp)) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr (Buf.withinW hp hF' (Lay.okW_iff.mp hF).2 h.wr)
      · exact .inr (Buf.withinW hp hS' (Lay.okW_iff.mp hS).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    -- The callee's entry state stays opaque to `sig_pre`, which would unfold it.
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    sig_pre [inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    refine ⟨by rw [sub_toNat (by omega_arith)]; omega_arith, by rw [sub_toNat (by omega_arith)]; have := (E1 s₀).isLt; omega_arith,
      trivial, Buf.disj hp hF' hS' dFS, rF₁, rS₁, rF₂, rS₂, rA₂, rF₃, rS₃, rA₃,
      Buf.fit hp hF', Buf.fit hp hS', ?_⟩
    refine reduced_frame ef (fun r hr => ?_) hred
    rw [List.mem_singleton] at hr; subst hr; rw [h.esp]
    exact (bF.sub_left (below_sub (by simp) hE')).symm
  · obtain ⟨h, hax, hcx, -⟩ := hA s₀ s hp ha
    obtain ⟨h', hax', hcx', -⟩ := hA s₀' s' hp' ha'
    obtain hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    obtain hr : ∀ r ∈ [Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hcx, hcx', hq.ptr hS']
      · rw [hax, hax', hq.ptr hF']
    obtain fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 28) (by omega_arith); simp only [List.length_cons, List.length_nil]; omega_arith
    refine ⟨rfl, by simp only [Buf.rgn, hq.ptr hF', hq.ptr hS', hq.E1], ?_⟩
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    generalize he' : (pushed [.ecx, .eax] s').callEntry = e'
    sig_pub [inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Buf.inW hp hF' (Lay.okW_iff.mp hF).2
    · exact Buf.inW hp hS' (Lay.okW_iff.mp hS).2
    · exact ⟨cR Y s₀, TPre.cW, stk_sub hp (by omega_arith) (by have := hp.sp16; omega_arith)⟩
  · obtain ⟨h, hax, -, -⟩ := hA s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    obtain fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 28) (by omega_arith); simp only [List.length_cons, List.length_nil]; omega_arith
    obtain a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    obtain hE' : 28 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact ctx_E hp h (N := 28) (by omega_arith)
    obtain bF := Buf.stkD hp hF' (N := 4 * 2 + 4 + 16) (by omega_arith)
    generalize he : (pushed [.ecx, .eax] s).callEntry = e at post
    sig_post [inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0] at post
    rw [polyAt_frame (callEntry_frame fit (by decide)) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [h.esp]
      exact (bF.sub_left (below_sub (by simp) hE')).symm)] at post
    replace post := polyIs_congr (lost_keep hp h (k := 2) (by omega_arith) m₂ hF') post
    refine hQ s₀ s s' hp ha h' e₃ (fr.sub fun r hr => ?_) post
    rw [hst] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨Buf.rgn s₀ ⟨fa, fo, 1024⟩, by simp, fun _ h => h⟩
    · exact ⟨Buf.rgn s₀ ⟨sa, so, 1024⟩, by simp, fun _ h => h⟩
    · exact ⟨below (E1 s₀) 28, by simp, stk_sub hp (by omega_arith) (by omega_arith)⟩
    · exact ⟨below (E1 s₀) 28, by simp, fun _ h => h⟩

theorem mul_nosp : NoSp Impl.MlKem.X86.multiplyNTTs := NoSp.of_all (by decide +kernel)
theorem mul_stack : stackUse Impl.MlKem.X86.multiplyNTTs = 16 := by decide +kernel

/-- `h ← MultiplyNTTs(f, g)`, with the polynomials at `(ha, ho)`, `(fa, fo)`, `(ga, go)` and the scratch
at `(sa, so)`, in `eax`, `ecx`, `edx` and `edi`. -/
theorem mul_call (oa oo fa fo ga go sa so : Nat)
    (hc : (Y.okW ⟨oa, oo, 1024⟩ && Y.ok ⟨fa, fo, 1024⟩ && Y.ok ⟨ga, go, 1024⟩ && Y.okW ⟨sa, so, 1024⟩ &&
      Y.sep ⟨oa, oo, 1024⟩ ⟨fa, fo, 1024⟩ && Y.sep ⟨oa, oo, 1024⟩ ⟨ga, go, 1024⟩ &&
      Y.sep ⟨oa, oo, 1024⟩ ⟨sa, so, 1024⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨sa, so, 1024⟩ &&
      Y.sep ⟨ga, go, 1024⟩ ⟨sa, so, 1024⟩) = true) (hN : 52 ≤ Y.stk)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨oa, oo, 1024⟩ ∧
      s.gpr .ecx = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧ s.gpr .edx = Buf.ptr s₀ ⟨ga, go, 1024⟩ ∧
      s.gpr .edi = Buf.ptr s₀ ⟨sa, so, 1024⟩ ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧
      Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨oa, oo, 1024⟩, ⟨sa, so, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨oa, oo, 1024⟩)
        (multiplyNTTs (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callWith [.edi, .edx, .ecx, .eax] "vg_mlkem_multiply_ntts" Impl.MlKem.X86.multiplyNTTs) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hH, hF'⟩, hG'⟩, hS⟩, dHF⟩, dHG⟩, dHS⟩, dFS⟩, dGS⟩ := hc
  obtain hH' := (Lay.okW_iff.mp hH).1
  obtain hS' := (Lay.okW_iff.mp hS).1
  refine call_piece Mul.verified mul_nosp (by decide) (by decide)
    (by rw [mul_stack]; simp only [List.length_cons, List.length_nil]; omega_arith)
    (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩, Buf.rgn s₀ ⟨ga, go, 1024⟩])
    (fun s₀ => [Buf.rgn s₀ ⟨oa, oo, 1024⟩, Buf.rgn s₀ ⟨sa, so, 1024⟩] ++ [below (E1 s₀) 16])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => wr_sub hp (bs := [⟨oa, oo, 1024⟩, ⟨sa, so, 1024⟩]) (by simp [hH, hS]) (by omega_arith))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · obtain ⟨h, hax, hcx, hdx, hdi, rF, rG⟩ := hA s₀ s hp ha
    obtain hE' : 36 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact ctx_E hp h (N := 36) (by omega_arith)
    obtain fit : 4 * [Reg.edi, Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      rw [h.esp]; simp only [List.length_cons, List.length_nil]; omega_arith
    obtain a0 : arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨oa, oo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    obtain a1 : arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    obtain a2 : arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 2 = Buf.ptr s₀ ⟨ga, go, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hdx
    obtain a3 : arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 3 = Buf.ptr s₀ ⟨sa, so, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hdi
    obtain eA : argAddr (pushed [.edi, .edx, .ecx, .eax] s).callEntry 0 = (E1 s₀ - BitVec.ofNat 32 16).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    obtain eSp : (pushed [.edi, .edx, .ecx, .eax] s).callEntry.gpr .esp = E1 s₀ - BitVec.ofNat 32 20 := by
      rw [callEntry_esp', h.esp]; rfl
    obtain bH := Buf.stkD hp hH' (N := 4 * 4 + 4 + 16) (by omega_arith)
    obtain bF := Buf.stkD hp hF' (N := 4 * 4 + 4 + 16) (by omega_arith)
    obtain bG := Buf.stkD hp hG' (N := 4 * 4 + 4 + 16) (by omega_arith)
    obtain bS := Buf.stkD hp hS' (N := 4 * 4 + 4 + 16) (by omega_arith)
    obtain ⟨rH₁, rH₂, rH₃⟩ := entry_regions hE' bH
    obtain ⟨rF₁, rF₂, rF₃⟩ := entry_regions hE' bF
    obtain ⟨rG₁, rG₂, rG₃⟩ := entry_regions hE' bG
    obtain ⟨rS₁, rS₂, rS₃⟩ := entry_regions hE' bS
    obtain ⟨rA₂, rA₃⟩ := entry_self (E := E1 s₀) (k := 4) (K := 16) hE'
    obtain cv := covers_of (s := s) (n := 4) (rd := [Buf.rgn s₀ ⟨fa, fo, 1024⟩, Buf.rgn s₀ ⟨ga, go, 1024⟩])
      (wr := [Buf.rgn s₀ ⟨oa, oo, 1024⟩, Buf.rgn s₀ ⟨sa, so, 1024⟩] ++ [below (E1 s₀) 16])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Buf.within hp hF' h.rd h.wr
        · exact Buf.within hp hG' h.rd h.wr) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr (Buf.withinW hp hH' (Lay.okW_iff.mp hH).2 h.wr)
      · exact .inr (Buf.withinW hp hS' (Lay.okW_iff.mp hS).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    -- The callee's entry state stays opaque to `sig_pre`, which would unfold it.
    generalize he : (pushed [.edi, .edx, .ecx, .eax] s).callEntry = e
    sig_pre [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp]
    obtain ek := @ent_keep Y s₀ s hp h [.edi, .edx, .ecx, .eax] (by decide) (by simp; omega_arith)
    refine ⟨by rw [sub_toNat (by omega_arith)]; omega_arith, by rw [sub_toNat (by omega_arith)]; have := (E1 s₀).isLt; omega_arith,
      trivial, trivial, Buf.disj hp hH' hF' dHF, Buf.disj hp hH' hG' dHG, Buf.disj hp hH' hS' dHS, rH₁,
      Buf.disj hp hF' hS' dFS, rF₁, Buf.disj hp hG' hS' dGS, rG₁, rS₁, rH₂, rF₂, rG₂, rS₂, rA₂,
      rH₃, rF₃, rG₃, rS₃, rA₃, Buf.fit hp hH', Buf.fit hp hF', Buf.fit hp hG', Buf.fit hp hS',
      reduced_congr (ek hF') rF, reduced_congr (ek hG') rG⟩
  · obtain ⟨h, hax, hcx, hdx, hdi, -⟩ := hA s₀ s hp ha
    obtain ⟨h', hax', hcx', hdx', hdi', -⟩ := hA s₀' s' hp' ha'
    obtain hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    obtain hr : ∀ r ∈ [Reg.edi, Reg.edx, Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hdi, hdi', hq.ptr hS']
      · rw [hdx, hdx', hq.ptr hG']
      · rw [hcx, hcx', hq.ptr hF']
      · rw [hax, hax', hq.ptr hH']
    obtain fit : 4 * [Reg.edi, Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 36) (by omega_arith); simp only [List.length_cons, List.length_nil]; omega_arith
    refine ⟨by simp only [Buf.rgn, hq.ptr hF', hq.ptr hG'], by simp only [Buf.rgn, hq.ptr hH', hq.ptr hS', hq.E1], ?_⟩
    generalize he : (pushed [.edi, .edx, .ecx, .eax] s).callEntry = e
    generalize he' : (pushed [.edi, .edx, .ecx, .eax] s').callEntry = e'
    sig_pub [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide), callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · obtain ⟨h, hax, hcx, hdx, -⟩ := hA s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    obtain fit : 4 * [Reg.edi, Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 36) (by omega_arith); simp only [List.length_cons, List.length_nil]; omega_arith
    obtain a0 : arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨oa, oo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    obtain a1 : arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    obtain a2 : arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 2 = Buf.ptr s₀ ⟨ga, go, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hdx
    obtain ek := @ent_keep Y s₀ s hp h [.edi, .edx, .ecx, .eax] (by decide) (by simp; omega_arith)
    generalize he : (pushed [.edi, .edx, .ecx, .eax] s).callEntry = e at post
    sig_post [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2] at post
    rw [polyAt_congr (ek hF'), polyAt_congr (ek hG')] at post
    replace post := polyIs_congr (lost_keep hp h (k := 4) (by omega_arith) m₂ hH') post
    exact hQ s₀ s s' hp ha h' e₃ (fr_conv hp (a := 16) (N := 36) (by omega_arith) (by omega_arith)
      (by rw [mul_stack] at fr; exact fr)) post

end VG.Proof.MlKem.X86.Top

end

end

/-!
# ML-KEM on x86 (32-bit): the calls of the top-level functions, with their arguments

A buffer's address, computed by `ptrTo` from `esi` or from the argument on the
stack (`ptrTo_ok`); the block that sets a call's arguments (`setup_piece`,
whose addresses depend only on `esp` and `esi`); and each call with it
(`nttC_piece`, …), whose postcondition relates the state before the block to
the state after the call.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

/-! ## Single instructions -/

theorem Only.flags (s : State) (d : Reg) (x : BitVec 32) (c o : Bool) :
    Only [d] s ((arithFlags s x c o).setReg d x) :=
  ⟨fun r hr => by
    simp only [State.setReg]
    rw [ite_eq_right_iff.mpr fun (e : r = d) => absurd (e ▸ List.mem_singleton_self d) hr]
    rfl, rfl, rfl, rfl⟩

theorem wp_movi {d : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = v → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  wp_cons (s' := s.setReg d v) (by simp only [exec, readSrc, Option.map_some])
    (k _ (Only.setReg s d v) (by simp [State.setReg]))

theorem wp_addi {d : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d + v → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d + v) (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat))
      (addOverflow (s.gpr d) v (s.gpr d + v))).setReg d (s.gpr d + v))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]))

theorem wp_movr' {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  wp_movr (k _ (Only.setReg s d _) (by simp [State.setReg]))

theorem wp_movm' {d b : Reg} {disp : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hin : InRegions (s.rd ++ s.wr) (s.ea (at_ b disp)) 4)
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.mem.readW (s.ea (at_ b disp)) 32 → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem (at_ b disp)) :: is)) s Q :=
  wp_movm hin (k _ (Only.setReg s d _) (by simp [State.setReg]))

theorem Ctx.only {s₀ s s' : State} (h : Ctx Y s₀ s) {ds : List Reg} (o : Only ds s s')
    (hd : Reg.esp ∉ ds) (hd' : Reg.esi ∉ ds) : Ctx Y s₀ s' :=
  h.same (o.gpr _ hd) (o.gpr _ hd') o.rd o.wr o.mem

/-! ## Addresses -/

theorem ptrTo_ok {s₀ s : State} (hp : TPre Y s₀) (h : Ctx Y s₀ s) {b : Buf} (hb : Y.ok b = true) {r : Reg}
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Only [r] s s' → s'.gpr r = b.ptr s₀ → WP isa (.block is) s' Q) :
    WP isa (.block (ptrTo Y.sc r b ++ is)) s Q := by
  obtain ⟨hb₁, -, -⟩ := Lay.ok_iff.mp hb
  unfold ptrTo
  rw [List.cons_append, List.singleton_append]
  split
  · rename_i e
    refine wp_movr' fun s₁ o₁ v₁ => ?_
    exact wp_addi fun s₂ o₂ v₂ => k s₂ (o₁.trans o₂ |>.mono (by simp)) (by rw [v₂, v₁, h.esi, Buf.ptr, e])
  · have ea : s.ea (at_ .esp (20 + 4 * b.arg)) = argAddr s₀ b.arg := h.argEa
    refine wp_movm' (by rw [ea]; exact h.argIn hp hb₁) fun s₁ o₁ v₁ => ?_
    exact wp_addi fun s₂ o₂ v₂ => k s₂ (o₁.trans o₂ |>.mono (by simp))
      (by rw [v₂, v₁, ea, h.argw hp hb₁])

/-- A block that sets registers, whose addresses depend only on `esp` and `esi`. -/
theorem setup_piece {is : List Instr} (P : State → State → Prop)
    (hw : ∀ s₀ s, TPre Y s₀ → Ctx Y s₀ s → WP isa (.block is) s fun s₁ => Ctx Y s₀ s₁ ∧ s₁.mem = s.mem ∧ P s₀ s₁)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    {ht : Taint.Hint VG.X86.Taint.T} (t : (VG.X86.taint.check (τr [.esp, .esi]) (.block is) ht).isSome = true) :
    Piece (TPre Y) (TPub Y lk) A (fun s₀ s₁ => ∃ s, A s₀ s ∧ Ctx Y s₀ s₁ ∧ s₁.mem = s.mem ∧ P s₀ s₁)
      (.block is) :=
  Piece.taint [.esp, .esi] (fun s₀ s hp ha => (hw s₀ s hp (hA s₀ s hp ha)).mono fun s₁ h₁ => ⟨s, ha, h₁⟩)
    (fun s₀ s₀' s s' hp _ hq ha ha' r hr => by
      have h := hA s₀ s hp ha
      have h' := hA s₀' s' ‹_› ha'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.esp, h'.esp, hq.E1]
      · rw [h.esi, h'.esi, hq.sc hp]) t

/-- Two addresses, in `eax` and `ecx`. -/
theorem ptr2_ok {s₀ s : State} (hp : TPre Y s₀) (h : Ctx Y s₀ s) {b₀ b₁ : Buf} (h₀ : Y.ok b₀ = true)
    (h₁ : Y.ok b₁ = true) :
    WP isa (.block (ptrTo Y.sc .eax b₀ ++ ptrTo Y.sc .ecx b₁)) s fun s' => Ctx Y s₀ s' ∧ s'.mem = s.mem ∧
      s'.gpr .eax = b₀.ptr s₀ ∧ s'.gpr .ecx = b₁.ptr s₀ := by
  rw [← List.append_nil (ptrTo Y.sc .ecx b₁)]
  refine ptrTo_ok hp h h₀ fun s₁ o₁ v₁ => ?_
  have c₁ := h.only o₁ (by decide) (by decide)
  refine ptrTo_ok hp c₁ h₁ fun s₂ o₂ v₂ => WP.block_nil_iff.mpr ?_
  exact ⟨c₁.only o₂ (by decide) (by decide), o₂.mem.trans o₁.mem, by rw [o₂.gpr _ (by decide), v₁], v₂⟩

/-- The block setting two addresses. -/
theorem setup2 {b₀ b₁ : Buf} (h₀ : Y.ok b₀ = true) (h₁ : Y.ok b₁ = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    {ht : Taint.Hint VG.X86.Taint.T}
    (t : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax b₀ ++ ptrTo Y.sc .ecx b₁)) ht).isSome = true) :
    Piece (TPre Y) (TPub Y lk) A (fun s₀ s₁ => ∃ s, A s₀ s ∧ Ctx Y s₀ s₁ ∧ s₁.mem = s.mem ∧
      (s₁.gpr .eax = b₀.ptr s₀ ∧ s₁.gpr .ecx = b₁.ptr s₀)) (.block (ptrTo Y.sc .eax b₀ ++ ptrTo Y.sc .ecx b₁)) :=
  setup_piece _ (fun _ _ hp h => (ptr2_ok hp h h₀ h₁).mono fun _ ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩) hA t

/-- `f ← NTT(f)` or `NTT⁻¹(f)`, with its arguments. -/
theorem inPlaceC_piece {t : Poly → Poly} {nm : String} {c : Prog isa}
    (hv : Verified X86.target c (inPlaceContract X86.abi t 16)) (hsp : NoSp c) (hst : stackUse c = 16)
    (fa fo sa so : Nat)
    (hc : (Y.okW ⟨fa, fo, 1024⟩ && Y.okW ⟨sa, so, 1024⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨sa, so, 1024⟩) = true)
    (hN : 44 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++ ptrTo Y.sc .ecx ⟨sa, so, 1024⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨fa, fo, 1024⟩, ⟨sa, so, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) (t (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (.seq (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++ ptrTo Y.sc .ecx ⟨sa, so, 1024⟩)) (callWith [.ecx, .eax] nm c)) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  refine Piece.seq (setup2 (Lay.okW_iff.mp hc'.1.1).1 (Lay.okW_iff.mp hc'.1.2).1 (fun s₀ s hp ha => (hA s₀ s hp ha).1) tt)
    (inPlace_call hv hsp hst fa fo sa so hc hN (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂⟩ =>
      ⟨h₁, e₁, e₂, m₁ ▸ (hA s₀ s hp ha).2⟩) fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  rw [m₁] at fr post
  exact hQ s₀ s s' hp ha h' fr post

/-- `f ← op(f, g)` (`vg_mlkem_add` or `vg_mlkem_sub`), with its arguments. -/
theorem accC_piece {op : Poly → Poly → Poly} {nm : String} {c : Prog isa}
    (hv : Verified X86.target c (accSig.contract X86.abi (pre := fun f g m => Reduced m f ∧ Reduced m g)
      (post := fun f g m m' _ => PolyIs m' f (op (polyAt m f) (polyAt m g))) (writeArgs := true) (stack := 16)))
    (hsp : NoSp c) (hst : stackUse c = 16) (fa fo ga go : Nat)
    (hc : (Y.okW ⟨fa, fo, 1024⟩ && Y.ok ⟨ga, go, 1024⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨ga, go, 1024⟩) = true)
    (hN : 44 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++ ptrTo Y.sc .ecx ⟨ga, go, 1024⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧
      Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (op (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (.seq (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++ ptrTo Y.sc .ecx ⟨ga, go, 1024⟩)) (callWith [.ecx, .eax] nm c)) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  refine Piece.seq (setup2 (Lay.okW_iff.mp hc'.1.1).1 hc'.1.2 (fun s₀ s hp ha => (hA s₀ s hp ha).1) tt)
    (acc_call hv hsp hst fa fo ga go hc hN (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂⟩ =>
      ⟨h₁, e₁, e₂, m₁ ▸ (hA s₀ s hp ha).2.1, m₁ ▸ (hA s₀ s hp ha).2.2⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  rw [m₁] at fr post
  exact hQ s₀ s s' hp ha h' fr post

/-- `f ← SamplePolyCBD₂(b)`, with its arguments. -/
theorem cbd2C_piece (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 128⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 128⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 44 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax ⟨ba, bo, 128⟩ ++ ptrTo Y.sc .ecx ⟨fa, fo, 1024⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (samplePolyCBD 2 (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 128⟩) 128)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (cbd2C Y.sc ⟨ba, bo, 128⟩ ⟨fa, fo, 1024⟩) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  refine Piece.seq (setup2 hc'.1.1 (Lay.okW_iff.mp hc'.1.2).1 hA tt)
    (cbd2_call ba bo fa fo hc hN (fun s₀ s₁ hp ⟨_, _, h₁, _, e₁, e₂⟩ => ⟨h₁, e₁, e₂⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  rw [m₁] at fr post
  exact hQ s₀ s s' hp ha h' fr post

/-- `o ← ByteEncode₁₂(f)`, with its arguments. -/
theorem enc12C_piece (fa fo oa oo : Nat)
    (hc : (Y.ok ⟨fa, fo, 1024⟩ && Y.okW ⟨oa, oo, 384⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨oa, oo, 384⟩) = true)
    (hN : 44 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++ ptrTo Y.sc .ecx ⟨oa, oo, 384⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨oa, oo, 384⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, 384⟩) 384 =
        encode12 (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (enc12C Y.sc ⟨fa, fo, 1024⟩ ⟨oa, oo, 384⟩) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  refine Piece.seq (setup2 hc'.1.1 (Lay.okW_iff.mp hc'.1.2).1 (fun s₀ s hp ha => (hA s₀ s hp ha).1) tt)
    (encode12_call fa fo oa oo hc hN (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂⟩ =>
      ⟨h₁, e₁, e₂, m₁ ▸ (hA s₀ s hp ha).2⟩) fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  rw [m₁] at fr post
  exact hQ s₀ s s' hp ha h' fr post

/-- `f ← ByteDecode₁₂(b)`, with its arguments. -/
theorem dec12C_piece (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 384⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 384⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 44 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax ⟨ba, bo, 384⟩ ++ ptrTo Y.sc .ecx ⟨fa, fo, 1024⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (decode12 (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 384⟩) 384)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (dec12C Y.sc ⟨ba, bo, 384⟩ ⟨fa, fo, 1024⟩) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  refine Piece.seq (setup2 hc'.1.1 (Lay.okW_iff.mp hc'.1.2).1 hA tt)
    (decode12_call ba bo fa fo hc hN (fun s₀ s₁ hp ⟨_, _, h₁, _, e₁, e₂⟩ => ⟨h₁, e₁, e₂⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  rw [m₁] at fr post
  exact hQ s₀ s s' hp ha h' fr post

end VG.Proof.MlKem.X86.Top
