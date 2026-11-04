module

public import VerifiedGarbage.Impl.MdHashTable.X86
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Block
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# The digest of a hash value on x86 (32-bit)

`digestK H`: the contract of `digest out` (`Impl/MdHashTable/X86.lean`) for
a hash function `H` whose streaming code's digest code is `out`: with the
`N` bytes of the hash value at `ebx` readable and the `N` bytes at `eax`
writable, apart, and apart from the return address, it writes `H.digest` of
the hash value to `eax` (`digest_ok`, from what `OutOk` says of `out`), in
constant time for the same pointers (`digest_ct`, from the taint check of
`out`).
-/

@[expose] public section

namespace VG.Proof.MdHashTable.X86

open VG VG.X86
open VG.Impl.MdHashTable.X86 (digest)
open VG.Proof.MdStream (Md)

variable {B N L : Nat} (H : Md B N L)

/-- The contract of `digest(value = ebx, out = eax)`. -/
def digestK : Contract isa where
  pre s :=
    let value : Region := ⟨(s.gpr .ebx).setWidth 64, N⟩
    let out : Region := ⟨(s.gpr .eax).setWidth 64, N⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [value] ∧ s.wr = [out] ∧ value.Disjoint out ∧ ret.Disjoint out ∧ (s.gpr .ebx).toNat + N ≤ 2 ^ 32 ∧
      (s.gpr .eax).toNat + N ≤ 2 ^ 32
  post s s' := s'.mem =
    WriteBytes.writeBytes s.mem ((s.gpr .eax).setWidth 64) (H.digest (H.stateAt s.mem ((s.gpr .ebx).setWidth 64)))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ s₁.gpr .ebx = s₂.gpr .ebx ∧ s₁.gpr .eax = s₂.gpr .eax

variable {H}

/-- `digest out` meets `digestK H`. -/
theorem digest_ok {out : List Instr} (ho : Proof.Pbkdf2.Md.X86.OutOk H out) :
    ∀ s, (digestK H).pre s → ∃ t s', Exec isa (digest out) s t s' ∧ abiPreserved s s' ∧ (digestK H).post s s' := by
  intro s ⟨hrd, hwr, hvo, hro, hb, ha⟩
  have hw := ho s hb ha (by rw [hrd]; exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _),
      Region.contains_self _ _⟩) (by rw [hwr]; exact ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩) hvo
  obtain ⟨t, s', he, hg, -, -, hm⟩ := hw
  refine ⟨t, s', he, ⟨fun r hr => hg r ?_ ?_, ?_⟩, hm⟩
  · rintro rfl; simp [calleeSaved] at hr
  · rintro rfl; simp [calleeSaved] at hr
  · have hl : (H.digest (H.stateAt s.mem ((s.gpr .ebx).setWidth 64))).length = N := H.digest_length _
    rw [hm]
    exact (WriteBytes.writeBytes_frame s.mem ((s.gpr .eax).setWidth 64) _ (R := ⟨(s.gpr .eax).setWidth 64, N⟩)
      (by rw [hl]; exact Region.contains_self _ _)).readW (r := ⟨(s.gpr .esp).setWidth 64, 32 / 8⟩)
      (Region.contains_self _ _) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hro) (by decide)

/-- `digest out` is constant time for the same pointers. -/
theorem digest_ct {out : List Instr}
    (hc : ∃ hc, (VG.Taint.check VG.X86.taint (τr [.esp, .ebx, .eax]) (digest out) hc).isSome = true) :
    ConstantTime isa (digestK H).pre (digestK H).pub (digest out) := by
  obtain ⟨_, hc⟩ := hc
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ hp e₁ e₂
  refine (RelCT.taint (A := VG.X86.taint) (P := fun a b => (digestK H).pub a b) (τr [.esp, .ebx, .eax])
    (fun a b h => agree_regs fun r hr => ?_) hc s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂).1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨h1, h2, h3⟩ := h
  rcases hr with rfl | rfl | rfl <;> assumption

end VG.Proof.MdHashTable.X86
