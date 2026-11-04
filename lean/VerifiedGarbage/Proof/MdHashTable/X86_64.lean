module

public import VerifiedGarbage.Impl.MdHashTable.X86_64
public import VerifiedGarbage.Proof.MdStream.X86_64.Common
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# The digest of a hash value on x86-64

`digestK H`: the contract of `digest P` (`Impl/MdHashTable/X86_64.lean`) for
a hash function `H` whose streaming code has the parameters `P`: it writes
`H.digest` of the hash value at `rdi` to `rsi` (`digest_verified`, from
what `Shape` says of `P.out`).
-/

@[expose] public section

namespace VG.Proof.MdHashTable.X86_64

open VG VG.X86_64 VG.Impl.MdStream.X86_64 VG.Proof.MdStream.X86_64
open VG.Impl.MdHashTable.X86_64 (digest)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

variable {P : Params} (H : MdStream.Md P.B P.N P.L)

/-- The contract of `digest(value = rdi, out = rsi)`: the `N` bytes of the
hash value readable, the `N` bytes of `out` writable, apart, and apart from
the return address; `out` then holds the digest of the hash value. -/
def digestK : Contract isa where
  pre s :=
    let value : Region := ⟨s.gpr .rdi, P.N⟩
    let out : Region := ⟨s.gpr .rsi, P.N⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [value] ∧ s.wr = [out] ∧ value.Disjoint out ∧ ret.Disjoint value ∧ ret.Disjoint out
  post s s' := s'.mem = WriteBytes.writeBytes s.mem (s.gpr .rsi) (H.digest (H.stateAt s.mem (s.gpr .rdi)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi

variable {H}

theorem digest_wp (hs : Shape H) {s : State} (hpre : (digestK H).pre s) :
    WP isa (digest P) s fun s' => gprPreserved s s' ∧
      s'.mem = WriteBytes.writeBytes s.mem (s.gpr .rsi) (H.digest (H.stateAt s.mem (s.gpr .rdi))) := by
  obtain ⟨hrd, hwr, hvo, hrv, hro⟩ := hpre
  unfold digest
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r8, .r9, .rbx, .rbp] (Q := fun t => t.gpr .r8 = s.gpr .rbx ∧ t.gpr .r9 = s.gpr .rbp ∧
      t.gpr .rbx = s.gpr .rdi ∧ t.gpr .rbp = s.gpr .rsi ∧ t.mem = s.mem) ?_ rfl) fun t ⟨⟨h8, h9, hb, hp, hm⟩, k⟩ => ?_
  · xrun
  have i₁ : InRegions (t.rd ++ t.wr) (t.gpr .rbx) P.N := by
    rw [hb, k.2.1, hrd]; exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Region.contains_self _ _⟩
  have i₂ : InRegions t.wr (t.gpr .rbp) P.N := by
    rw [hp, k.2.2, hwr]; exact ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have i₃ : Region.Disjoint ⟨t.gpr .rbx, P.N⟩ ⟨t.gpr .rbp, P.N⟩ := by rw [hb, hp]; exact hvo
  refine WP.mono (hs.out t i₁ i₂ i₃) fun u ⟨hg, _, _, hmu⟩ => ?_
  refine WP.mono (WP.keep [.rbx, .rbp] (Q := fun v => v.gpr .rbx = u.gpr .r8 ∧ v.gpr .rbp = u.gpr .r9 ∧
      v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, hmv⟩, k'⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · xrun
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₁, hg .r8 (by decide), h8]
    · rw [h₂, hg .r9 (by decide), h9]
    all_goals rw [k'.gpr (by decide), hg _ (by decide), k.gpr (by decide)]
  · have hl : (H.digest (H.stateAt s.mem (s.gpr .rdi))).length = P.N := H.digest_length _
    rw [hmv, hmu, hp, hb, hm]
    refine (WriteBytes.writeBytes_frame s.mem (s.gpr .rsi) _ (R := ⟨s.gpr .rsi, P.N⟩)
      (by rw [hl]; exact Region.contains_self _ _)).readW (r := ⟨s.gpr .rsp, 64 / 8⟩) (Region.contains_self _ _)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hro) (by decide)
  · rw [hmv, hmu, hp, hb, hm]

/-- `digest P` meets `digestK H`, for code that never loads MXCSR (which the
kernel checks of each instance). -/
theorem digest_verified (hs : Shape H) (hmx : (digest P).allInstrs (fun i => !loadsMxcsr i) = true) :
    ∀ s, (digestK H).pre s → ∃ t s', Exec isa (digest P) s t s' ∧ abiPreserved s s' ∧ (digestK H).post s s' :=
  fun _ hpre => let ⟨t, s', he, hg, hm⟩ := digest_wp hs hpre
    ⟨t, s', he, abiPreserved_of_exec hmx he hg, hm⟩

end VG.Proof.MdHashTable.X86_64
