import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Spec.EcKey.Generic

/-!
# Verified elliptic-curve functions that call the field products

A function whose code `c` calls the field products (P-521's
`vg_p521_mul_mod_p`) is proven correct as `c.inline`, the products' code
where the calls are, and constant time as `c`, by taint tracking, which
follows the calls (`Verified.of_inline_ct`). Its contract has 8 bytes of
stack, for the calls' return address, which no buffer overlaps
(`Sig.clear_of_pre_consts`), and its postcondition reads memory only in its
output buffers (`bytesAt_patch`).
-/

namespace VG.X86_64

/-- Inlining moves the instructions of each function called into its
caller. -/
theorem _root_.VG.Code.allInstrs_inline {I C : Type} (p : I → Bool) :
    ∀ c : Code I C, c.inline.allInstrs p = c.allInstrs p
  | .block _ => rfl
  | .seq a b => by simp only [Code.inline, Code.allInstrs, Code.allInstrs_inline p a, Code.allInstrs_inline p b]
  | .ite _ t e => by simp only [Code.inline, Code.allInstrs, Code.allInstrs_inline p t, Code.allInstrs_inline p e]
  | .loop b _ => by simp only [Code.inline, Code.allInstrs, Code.allInstrs_inline p b]
  | .call _ _ => rfl
  | .frame _ b _ => by simp only [Code.inline, Code.allInstrs, Code.allInstrs_inline p b]

/-- `c` is verified against `k` if `c.inline` is correct and `c` constant
time against a contract `k₀` that `k` implies, `k₀`'s postcondition does
not read the 8 bytes below `rsp`, and `k` keeps every buffer away from
them. -/
theorem Verified.of_inline_ct {c : Prog isa} (hc : c.InlineOk = true) {k₀ k : Contract isa}
    (hcor : ∀ s, k₀.pre s → ∃ t s', Exec isa c.inline s t s' ∧ abiPreserved s s' ∧ k₀.post s s')
    (hct : ConstantTime isa k₀.pre k₀.pub c) (himp : k₀.Implies k)
    (hclear : ∀ s, k.pre s → Clear (hole (s.gpr .rsp)) s)
    (hpost : ∀ s b hv u, k.pre s → k₀.post s b → k₀.post s (b.patch (hole (s.gpr .rsp)) hv u)) :
    Verified target c k := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ =>
    hct s₁ s₂ t₁ t₂ s₁' s₂' (himp.pre _ h₁) (himp.pre _ h₂) (himp.pub _ _ h₁ h₂ hp) e₁ e₂, himp.sat⟩
  obtain ⟨t, b, he, ha, hp⟩ := hcor s (himp.pre s hs)
  obtain ⟨hv, u, ta, ha', _, _⟩ := Exec.of_inline hc he (hclear s hs)
  exact ⟨ta, _, ha', abiPreserved_patch hv u ha, himp.post s _ hs (hpost s b hv u hs hp)⟩

/-- `Sig.clear_of_pre`, under the calling convention with static tables. -/
theorem Sig.clear_of_pre_consts {c : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    {sig : Sig} {pre : Curry (sig.words (abi.withConsts (c :: cs)).ptrBits) (Mem → Prop)}
    {post : sig.Post (abi.withConsts (c :: cs)).ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words (abi.withConsts (c :: cs)).ptrBits) (Mem → List Nat))} {s : State}
    (h : (sig.contract (abi.withConsts (c :: cs)) pre post wa 8 leak).pre s) : Clear (hole (s.gpr .rsp)) s := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  · obtain ⟨hwf, hrd, hwr, _, hres, _⟩ := h
    have hh : hole (s.gpr .rsp) ∈ (abi.withConsts (c :: cs)).reserved 8 s := by
      simp [abi, Abi.withConsts, stackBelow, hole]
    obtain ⟨-, hdrop, -, hct⟩ := hwf
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rw [← List.take_append_drop (s.rd.length - (c :: cs).length) s.rd] at hr
      rcases List.mem_append.mp hr with hr | hr
      · rw [show s.rd.take (s.rd.length - (c :: cs).length) = (abi.withConsts (c :: cs)).rd s from rfl,
          hrd] at hr
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
        exact (hres _ hh a (List.mem_filter.mp ha).1).symm
      · rw [show s.rd = abi.rd s from rfl, hdrop] at hr
        exact (hct r hr).2.2 _ hh
    · rw [show s.wr = (abi.withConsts (c :: cs)).wr s from rfl, hwr] at hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact (hres _ hh a (List.mem_filter.mp ha).1).symm

theorem abi_wf0 (ws : List Nat) (s : State) (h : abi.wf ws 8 s) : abi.wf ws 0 s := by
  simp only [abi] at h ⊢
  split at h
  · rename_i hl; simp only [hl, ite_true]
  · rename_i hl; simp only [hl, ite_false]; exact ⟨trivial, h.2⟩

/-- A contract with 8 bytes of stack asks more than the same with none: its
reserved memory is the return address and the 8 bytes below it. -/
theorem Sig.pre_stack0 {c : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    {sig : Sig} {pre : Curry (sig.words (abi.withConsts (c :: cs)).ptrBits) (Mem → Prop)}
    {post : sig.Post (abi.withConsts (c :: cs)).ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words (abi.withConsts (c :: cs)).ptrBits) (Mem → List Nat))} {s : State}
    (h : (sig.contract (abi.withConsts (c :: cs)) pre post wa 8 leak).pre s) :
    (sig.contract (abi.withConsts (c :: cs)) pre post wa 0 leak).pre s := by
  simp only [Sig.contract] at h ⊢
  split at h
  · exact h.elim
  · obtain ⟨⟨hw, hdrop, hheld, hct⟩, hrd, hwr, hpw, hres, hb, hp⟩ := h
    have hsub : ∀ r ∈ (abi.withConsts (c :: cs)).reserved 0 s, r ∈ (abi.withConsts (c :: cs)).reserved 8 s := by
      intro r hr; simp only [abi, Abi.withConsts, stackBelow, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact .inl hr
    refine ⟨⟨?_, hdrop, hheld, fun t ht => ⟨(hct t ht).1, (hct t ht).2.1, fun r hr => (hct t ht).2.2 r (hsub r hr)⟩⟩,
      hrd, hwr, hpw, fun r hr => hres r (hsub r hr), hb, hp⟩
    exact abi_wf0 _ s hw

/-- A contract that implies the one with no stack implies the one with 8
bytes of stack, if that one can be met. -/
theorem _root_.VG.Contract.Implies.stack8 {c : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    {sig : Sig} {pre : Curry (sig.words (abi.withConsts (c :: cs)).ptrBits) (Mem → Prop)}
    {post : sig.Post (abi.withConsts (c :: cs)).ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words (abi.withConsts (c :: cs)).ptrBits) (Mem → List Nat))} {k₀ : Contract isa}
    (h : k₀.Implies (sig.contract (abi.withConsts (c :: cs)) pre post wa 0 leak))
    (hsat : ∃ s, (sig.contract (abi.withConsts (c :: cs)) pre post wa 8 leak).pre s) :
    k₀.Implies (sig.contract (abi.withConsts (c :: cs)) pre post wa 8 leak) :=
  ⟨fun s hs => h.pre s (Sig.pre_stack0 hs), fun s s' hs hp => h.post s s' (Sig.pre_stack0 hs) hp,
    fun s₁ s₂ h₁ h₂ hp => h.pub s₁ s₂ (Sig.pre_stack0 h₁) (Sig.pre_stack0 h₂) hp, hsat⟩

/-- `Sig.pre_stack0`, under the calling convention without static tables. -/
theorem Sig.pre_stack0_abi {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    {s : State} (h : (sig.contract abi pre post wa 8 leak).pre s) : (sig.contract abi pre post wa 0 leak).pre s := by
  simp only [Sig.contract] at h ⊢
  split at h
  · exact h.elim
  · obtain ⟨hw, hrd, hwr, hpw, hres, hb, hp⟩ := h
    have hsub : ∀ r ∈ abi.reserved 0 s, r ∈ abi.reserved 8 s := by
      intro r hr; simp only [abi, stackBelow, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact .inl hr
    exact ⟨abi_wf0 _ s hw, hrd, hwr, hpw, fun r hr => hres r (hsub r hr), hb, hp⟩

/-- `Contract.Implies.stack8`, under the calling convention without static
tables. -/
theorem _root_.VG.Contract.Implies.stack8_abi {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    {k₀ : Contract isa} (h : k₀.Implies (sig.contract abi pre post wa 0 leak))
    (hsat : ∃ s, (sig.contract abi pre post wa 8 leak).pre s) :
    k₀.Implies (sig.contract abi pre post wa 8 leak) :=
  ⟨fun s hs => h.pre s (Sig.pre_stack0_abi hs), fun s s' hs hp => h.post s s' (Sig.pre_stack0_abi hs) hp,
    fun s₁ s₂ h₁ h₂ hp => h.pub s₁ s₂ (Sig.pre_stack0_abi h₁) (Sig.pre_stack0_abi h₂) hp, hsat⟩

/-- The bytes of a buffer that misses the hole are those of the run with
calls. -/
theorem bytes_patch {H : Region} {hv : Mem} {u : Nat → BitVec 64} {b : State} {p : Addr} {n : Nat}
    (h : ∀ i < n, ¬ H.Contains (p + BitVec.ofNat 64 i) 1) :
    ((List.range n).map fun i => (b.patch H hv u).mem (p + BitVec.ofNat 64 i)) =
      (List.range n).map fun i => b.mem (p + BitVec.ofNat 64 i) := by
  refine List.map_congr_left fun i hi => ?_
  simp only [State.patch, overlay, h i (List.mem_range.mp hi), ite_false]

theorem bytesAt_patch {H : Region} {hv : Mem} {u : Nat → BitVec 64} {b : State} {p : Addr} {n : Nat}
    (h : ∀ i < n, ¬ H.Contains (p + BitVec.ofNat 64 i) 1) :
    Spec.Ecdsa.bytesAt (b.patch H hv u).mem p n = Spec.Ecdsa.bytesAt b.mem p n :=
  bytes_patch h

theorem EcKey.bytesAt_patch {H : Region} {hv : Mem} {u : Nat → BitVec 64} {b : State} {p : Addr}
    {n : Nat} (h : ∀ i < n, ¬ H.Contains (p + BitVec.ofNat 64 i) 1) :
    Spec.EcKey.bytesAt (b.patch H hv u).mem p n = Spec.EcKey.bytesAt b.mem p n :=
  bytes_patch h

/-- Every byte of a writable region misses the hole. -/
theorem Clear.wr_bytes {H : Region} {s : State} (hc : Clear H s) {p : Addr} {n : Nat}
    (hr : (⟨p, n⟩ : Region) ∈ s.wr) (hn : n ≤ 2 ^ 64) : ∀ i < n, ¬ H.Contains (p + BitVec.ofNat 64 i) 1 :=
  fun i hi => hc _ (List.mem_append_right _ hr) _ (by
    simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat p (by omega)]; omega)

end VG.X86_64
