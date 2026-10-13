module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CT
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealSplit

/-!
# ChaCha20-Poly1305 with the data's first bytes from `src`, x86-64: what `seal` starts from

`SealSplit.sealSplitBody` runs as `seal` (`CT.lean`) with two more stack
arguments, `src` (`sp`) and `src_len` (`SL`), at `rsp + 24` and `rsp + 32`:
what its entry state must satisfy besides `seal`'s `APre` (`SPre`), and the
bytes it encrypts (`PTs`: the data, but for its bytes `[mm, SL)`, from
`src`; `mm` is the number of bytes the prologue's keystream covers, whose
bytes of `src` the caller has already copied to the data).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Split

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Spec.Poly1305 (bytesAt)

section
variable (s₀ : State)
/-- `src` and `src_len`, `[rsp + 24]` and `[rsp + 32]`. -/
abbrev sp : Addr := stackArg s₀ 2
abbrev SL : Nat := (stackArg s₀ 3).toNat
abbrev spR : Region := ⟨sp s₀, SL s₀⟩
/-- The two stack arguments. -/
abbrev arg2R : Region := ⟨stackArgAddr s₀ 2, 16⟩
/-- The bytes the prologue's keystream covers. -/
abbrev mm : Nat := mOf 960 1024 (L s₀)
end

/-- The bytes encrypted, in memory `m`: `[mm, SL)` from `src`, the rest from
the data. -/
def PTs (s₀ : State) (m : Mem) : List Byte :=
  (List.range (L s₀)).map fun k =>
    if mm s₀ ≤ k ∧ k < SL s₀ then m (sp s₀ + BitVec.ofNat 64 k) else m (dp s₀ + BitVec.ofNat 64 k)

/-- What `sealSplitBody` needs besides `seal`'s precondition: `src_len` at
most the length, `src` and the stack arguments readable, and apart from what
the code writes. -/
structure SPre (s₀ : State) : Prop where
  hp : APre true s₀
  g2 : arg2R s₀ ∈ s₀.rd
  s_rd : spR s₀ ∈ s₀.rd
  le : SL s₀ ≤ L s₀
  s_c : (spR s₀).Disjoint (ctxR s₀)
  s_d : (spR s₀).Disjoint (dR s₀)
  s_k : (spR s₀).Disjoint (stkR s₀)
  g_c : (arg2R s₀).Disjoint (ctxR s₀)
  g_d : (arg2R s₀).Disjoint (dR s₀)
  g_t : (arg2R s₀).Disjoint (tR s₀)
  g_k : (arg2R s₀).Disjoint (stkR s₀)
  wrap_s : (sp s₀).toNat + SL s₀ ≤ 2 ^ 64

theorem length_PTs (s₀ : State) (m : Mem) : (PTs s₀ m).length = L s₀ := by simp [PTs]

theorem PTs_getD {s₀ : State} (m : Mem) {k : Nat} (hk : k < L s₀) :
    (PTs s₀ m).getD k 0 =
      if mm s₀ ≤ k ∧ k < SL s₀ then m (sp s₀ + BitVec.ofNat 64 k) else m (dp s₀ + BitVec.ofNat 64 k) := by
  simp only [PTs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    Option.getD_some]

/-- With at most 960 bytes, the prologue's keystream covers them all, and
`src` is all copied. -/
theorem PTs_small {s₀ : State} (hle : SL s₀ ≤ L s₀) (hs : L s₀ ≤ 960) (m : Mem) :
    PTs s₀ m = bytesAt m (dp s₀) (L s₀) := by
  have hm : mm s₀ = L s₀ := by simp only [mm, mOf, hs, ite_true]
  simp only [PTs, bytesAt]
  exact List.map_congr_left fun k hk => by
    have := List.mem_range.mp hk
    rw [ite_eq_right fun h => by omega]

/-- The stack arguments `src` and `src_len` survive a frame apart from them. -/
theorem arg_frame {s₀ : State} {j : Nat} (hj : j = 2 ∨ j = 3) {rs : List Region} {m m' : Mem}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (arg2R s₀).Disjoint r) :
    m'.readW (stackArgAddr s₀ j) 64 = m.readW (stackArgAddr s₀ j) 64 := by
  refine hf.readW ?_ hd (by decide)
  rcases hj with rfl | rfl
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · show (arg2R s₀).Contains (s₀.gpr .rsp + BitVec.ofNat 64 (8 * (3 + 1))) (64 / 8)
    rw [show s₀.gpr .rsp + BitVec.ofNat 64 (8 * (3 + 1)) = s₀.gpr .rsp + BitVec.ofNat 64 (8 * (2 + 1)) +
      BitVec.ofNat 64 8 by rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
    exact Offset.contains_base _ (by lit_omega) (by lit_omega)

/-- A byte of `src` is not in the context. -/
theorem SPre.nctx {s₀ : State} (hT : SPre s₀) {k a n : Nat} (hk : k < SL s₀) (ha : a + n ≤ 1696) :
    ¬ (sub s₀ a n).Contains (sp s₀ + BitVec.ofNat 64 k) 1 :=
  fun hc => hT.s_c _ (Offset.contains_base _ (by omega) (by have := hT.wrap_s; omega)) (sub_ctx s₀ ha _ hc)

/-- A byte of `src` is not in the data. -/
theorem SPre.ndR {s₀ : State} (hT : SPre s₀) {k : Nat} (hk : k < SL s₀) :
    ¬ (dR s₀).Contains (sp s₀ + BitVec.ofNat 64 k) 1 :=
  fun hc => hT.s_d _ (Offset.contains_base _ (by omega) (by have := hT.wrap_s; omega)) hc

/-- A byte of `src` is not in the stack below `rsp`. -/
theorem SPre.nstk {s₀ : State} (hT : SPre s₀) {k : Nat} (hk : k < SL s₀) :
    ¬ (stkR s₀).Contains (sp s₀ + BitVec.ofNat 64 k) 1 :=
  fun hc => hT.s_k _ (Offset.contains_base _ (by omega) (by have := hT.wrap_s; omega)) hc

end VG.Proof.ChaCha20Poly1305.X86_64.Split
