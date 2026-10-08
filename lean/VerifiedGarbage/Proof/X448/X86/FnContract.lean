import VerifiedGarbage.Proof.X448.X86.Fn
import VerifiedGarbage.Proof.X25519.X86.Basic

/-!
# X448 on x86 (32-bit): the field functions' contracts

The contracts the field functions are proven against (`binX86`, `a24X86`):
the facts of the shared contracts of `Spec/X448/Field16.lean` stated for x86
(`fnPre`: the working space, and the arguments on the stack), which the
shared contracts imply (`sig_implies`, in `FnVerified.lean`). The entry
those facts give (`FnEntry.of_pre`), and the shared postcondition from what
the proofs state (`FnOut.post`).
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

/-- The working space, the first argument. -/
abbrev wsOf (s : State) : Addr := (arg s 0).setWidth 64

/-- The shared contracts' facts about the state, for arguments of `len` bytes. -/
def fnPre (len : Nat) (s : State) : Prop :=
  (s.gpr .esp).toNat + 4 + len ≤ 2 ^ 32 ∧ s.rd = [⟨argAddr s 0, len⟩] ∧ s.wr = [⟨wsOf s, 8192⟩] ∧
    Region.Disjoint ⟨wsOf s, 8192⟩ ⟨argAddr s 0, len⟩ ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨wsOf s, 8192⟩ ∧ (arg s 0).toNat + 8192 ≤ 2 ^ 32

/-- The binary functions' contract, for the relation `r` of the values. -/
def binX86 (r : Nat → Nat → Nat → Prop) : Contract isa where
  pre s := fnPre 16 s ∧ Spec.X448.Field16.Fits (arg s 1) ∧ Spec.X448.Field16.Fits (arg s 2) ∧
    Spec.X448.Field16.Fits (arg s 3) ∧ Spec.X448.Field16.Limbs s.mem (wsOf s) (arg s 2) ∧
    Spec.X448.Field16.Limbs s.mem (wsOf s) (arg s 3)
  post s s' := Spec.X448.Field16.Limbs s'.mem (wsOf s) (arg s 1) ∧
    r (Spec.X448.Field16.valAt s'.mem (wsOf s) (arg s 1)) (Spec.X448.Field16.valAt s.mem (wsOf s) (arg s 2))
      (Spec.X448.Field16.valAt s.mem (wsOf s) (arg s 3)) ∧
    Spec.X448.Field16.Keeps (wsOf s) (arg s 1) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3

/-- `vg_gf448_r16_mul_a24`'s contract. -/
def a24X86 : Contract isa where
  pre s := fnPre 12 s ∧ Spec.X448.Field16.Fits (arg s 1) ∧ Spec.X448.Field16.Fits (arg s 2) ∧
    Spec.X448.Field16.Limbs s.mem (wsOf s) (arg s 2)
  post s s' := Spec.X448.Field16.Limbs s'.mem (wsOf s) (arg s 1) ∧
    Spec.X448.Field16.valAt s'.mem (wsOf s) (arg s 1) % Spec.X448.P =
      39081 * Spec.X448.Field16.valAt s.mem (wsOf s) (arg s 2) % Spec.X448.P ∧
    Spec.X448.Field16.Keeps (wsOf s) (arg s 1) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2

theorem not_contains_ofs {base x : Addr} (h : ¬ (⟨base, 8192⟩ : Region).Contains x 1) :
    8192 ≤ ofs base x := by
  simp only [Region.Contains] at h; simp only [ofs]; omega

/-- The entry the facts of the contract give. -/
theorem FnEntry.of_pre {s : State} {n : Nat} (hn : 3 ≤ n) (h : fnPre (4 * n) s)
    (ho : Spec.X448.Field16.Fits (arg s 1)) (ha : Spec.X448.Field16.Fits (arg s 2)) :
    FnEntry s (wsOf s) n (arg s 1).toNat (arg s 2).toNat := by
  obtain ⟨hsp, hrd, hwr, hdis, hret, hfit⟩ := h
  have cont : ∀ i < n, (⟨argAddr s 0, 4 * n⟩ : Region).Contains (argAddr s i) 4 := fun i hi =>
    VG.Proof.X25519.X86.sub_contains (x := s.gpr .esp) (a := 4) (k := 4 * n) (by omega) (by omega)
      (by omega) (by decide)
  refine ⟨rfl, by rw [hwr]; exact List.mem_singleton_self _, hfit, ⟨fun i hi => ?_, fun i hi k hk => ?_⟩, hn,
    fun k hk => ?_, by simp, by simp,
    ho, ha⟩
  · exact ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), cont i hi⟩
  · refine not_contains_ofs fun hw => hdis _ hw ((cont i hi).byte ?_)
    rw [Offset.add_sub_cancel_left]; simp only [BitVec.toNat_ofNat]; omega
  · refine not_contains_ofs fun hw => hret _ ?_ hw
    simp only [Region.Contains]
    rw [Offset.add_sub_cancel_left]; simp only [BitVec.toNat_ofNat]; omega

/-- The value of an element, as `Spec` states it. -/
theorem valN_spec (m : Mem) (ws : Addr) (o : BitVec 32) :
    ∀ n, Spec.X448.Field16.valN m ws o n = valN (limbs m ws o.toNat) n
  | 0 => rfl
  | n + 1 => by
    rw [Spec.X448.Field16.valN, valN, valN_spec m ws o n, radix, ← Nat.pow_mul]
    rfl

theorem valAt_eq (m : Mem) (ws : Addr) (o : BitVec 32) :
    Spec.X448.Field16.valAt m ws o = fe m ws o.toNat := valN_spec m ws o 28

theorem limbs_spec {m : Mem} {ws : Addr} {o : BitVec 32} :
    Spec.X448.Field16.Limbs m ws o ↔ Bounded m ws o.toNat := Iff.rfl

/-- `Keeps` from the frame of the field functions. -/
theorem FieldMem.keeps {base : Addr} {o : BitVec 32} {m m' : Mem} (h : FieldMem base o.toNat m m') :
    Spec.X448.Field16.Keeps base o m m' := by
  intro i hi hw ho
  simp only [Spec.X448.Field16.ownAt, Spec.X448.Field16.elemBytes, Spec.X448.Field16.limbs] at hw ho
  exact h _ (by rw [ofs, Mem.sub_ofNat_toNat base (by omega)]; omega)
    (by rw [ofs, Mem.sub_ofNat_toNat base (by omega)]; simp only [ACC]; omega)

end VG.Proof.X448.X86
