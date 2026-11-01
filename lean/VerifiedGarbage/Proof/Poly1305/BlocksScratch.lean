module

public import VerifiedGarbage.Spec.Poly1305.Contract
public import VerifiedGarbage.Proof.Poly1305.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_poly1305_blocks` with its working space as an argument

On targets where `blocks` needs working space beyond the state's (PPC64LE,
which saves nonvolatile registers in it), it runs in a frame of its own
(`Verified.stackScratch`), around code proved with the working space as an
argument: `blocksScratchContract` is `blocksContract` with a 128-byte
`scratch` buffer appended, whatever it holds. The frame needs the
postcondition to read the memory on entry only within the function's buffers
(`blocksPost_local`): the blocks, and the state through `Repr`, which reads
only its first 56 bytes (`repr_congr`).
-/

@[expose] public section

namespace VG.Proof.Poly1305

open VG.Spec.Poly1305

/-- `blocksContract`'s postcondition. -/
def blocksPost (pb : Nat) : blocksSig.Post pb := fun state blocks n m m' _ =>
  ∀ key msg, Repr m state key msg → Repr m' state key (msg ++ bytesAt m blocks (16 * n.toNat))

theorem blocksContract_eq {M : ISA} (A : Abi M) (stack : Nat) :
    blocksContract A stack = blocksSig.contract A (post := blocksPost A.ptrBits) (stack := stack) :=
  rfl

/-- `vg_poly1305_blocks` with `scratch: *mut [u64; 16]`. -/
def blocksScratchSig : Sig where
  params := [("state", .array true .u64 16), ("blocks", .slice false (.array .u8 16) "n"),
    ("scratch", .array true .u64 16)]

/-- `blocksContract`, whatever `scratch` is. -/
def blocksScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  blocksScratchSig.contract A
    (post := fun state blocks n _scratch => blocksPost A.ptrBits state blocks n) (stack := stack)

theorem bytesAt_congr' {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    bytesAt m₂ p n = bytesAt m₁ p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- A state represents a message by its first 56 bytes alone. -/
theorem repr_congr {m₁ m₂ : Mem} {p : Addr} {key msg : List Byte}
    (h : ∀ i < 56, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i))
    (hr : Repr m₁ p key msg) : Repr m₂ p key msg := by
  obtain ⟨h0, h1, h2⟩ := hr
  refine ⟨h0, ?_, ?_⟩
  · have e : bytesAt m₂ (p + BitVec.ofNat 64 24) 32 = bytesAt m₁ (p + BitVec.ofNat 64 24) 32 :=
      bytesAt_congr' fun i hi => by rw [Offset.add_add]; exact h _ (by omega)
    rw [show p + 24 = p + BitVec.ofNat 64 24 from rfl, e]
    exact h1
  · rw [bytesAt_congr' fun i hi => h i (by omega)]; exact h2

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on the
region. -/
theorem agree_of' {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

theorem blocksPost_local (pb : Nat) : ∀ vs m₁ m₂ m' r, vs.length = (blocksSig.words pb).length →
    (∀ b ∈ Sig.bufs blocksSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (blocksSig.words pb) (blocksPost pb) vs m₁ m' r →
      Curry.apply (blocksSig.words pb) (blocksPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨bl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [blocksSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  have hs := agree_of' hb.1
  have hd := agree_of' hb.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb] (blocksPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb] (blocksPost pb) _ m₂ m' r
  dsimp only [Curry.apply, blocksPost, ArgWord.ofRaw] at h ⊢
  intro key msg hrep
  rw [bytesAt_congr' fun i hi => hd i (by
    have := Nat.mod_le n.toNat (2 ^ pb)
    simp only [BitVec.toNat_setWidth] at hi
    simp only [Elem.size]
    omega)]
  exact h key msg (repr_congr (fun i hi => (hs i (by simp only [Elem.size]; omega)).symm) hrep)

end VG.Proof.Poly1305
