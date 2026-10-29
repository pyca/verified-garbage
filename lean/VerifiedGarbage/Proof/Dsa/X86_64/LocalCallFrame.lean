module

public import VerifiedGarbage.Proof.Dsa.X86_64.Call

/-! # Framing arithmetic calls whose result is a local scratch buffer -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def localCallRanges (o wx d k : Nat) : List (Nat × Nat) :=
  [(128, 48), (o + 136, slot wx 8 + tabBytes wx - 136), (d, k)]

theorem callFrame_local {B : Addr} {o wx d k : Nat} {mem mem' : Mem}
    (hf : CallFrame B o wx (off B d) k mem mem')
    (ho : o + slot wx 8 + tabBytes wx ≤ 2 ^ 64) (hd : d + k ≤ 2 ^ 64) :
    Frm B (localCallRanges o wx d k) mem mem' := by
  have hslot : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  intro x hx
  apply hf x (hx (128, 48) (by simp [localCallRanges]))
  · intro r hr
    simp only [workRanges, List.mem_singleton] at hr
    subst r
    have h := hx (o + 136, slot wx 8 + tabBytes wx - 136) (by simp [localCallRanges])
    rcases ofs_rebase B x (o := o) (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only at * <;> omega
  · intro j hj he
    have h := hx (d, k) (by simp [localCallRanges])
    rw [he, ofs_off B (by omega)] at h
    simp only at h
    omega

/-- A local result cannot change a disjoint initialized child. -/
theorem localCall_ready {B : Addr} {o wx d k other ow m : Nat} {mi : BitVec 64} {mem mem' : Mem}
    (hf : Frm B (localCallRanges o wx d k) mem mem') (hready : ChildReady mem B other ow m mi)
    (hlo : 176 ≤ other) (hhi : other + slot ow 8 ≤ 2 ^ 64)
    (hsep : other + slot ow 8 ≤ o ∨ o + slot wx 8 + tabBytes wx ≤ other)
    (hout : other + slot ow 8 ≤ d ∨ d + k ≤ other) : ChildReady mem' B other ow m mi := by
  have hslot : 256 ≤ slot ow 8 := by unfold slot hdrBytes; omega
  have hwork : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have he : ∀ e, e + 8 ≤ slot ow 8 → word mem' (off B other) e = word mem (off B other) e := by
    intro e he
    rw [word_off, word_off]
    apply hf.word_eq _ (by omega)
    intro r hr
    simp only [localCallRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · right; omega
    · rcases hsep with hsep | hsep
      · left; omega
      · right; omega
    · rcases hout with hout | hout
      · left; omega
      · right; omega
  have hn := slot_le (w := ow) (show VG.Impl.Bignum.X86_64.Public.aN < 8 by decide)
  refine ⟨hready.header.of_words (fun i hi => he _ (by omega)), ?_, ?_⟩
  · rw [wv_congr (m := mem) (m' := mem') (fun i hi => he _ (by omega))]
    exact hready.modulus
  · rw [he _ (by omega)]
    exact hready.inverse

end VG.Proof.Dsa.X86_64
