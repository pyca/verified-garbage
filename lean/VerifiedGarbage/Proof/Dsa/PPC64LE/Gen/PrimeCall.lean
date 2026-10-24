module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Bytes
public import VerifiedGarbage.Spec.Dsa.ProbablePrime
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: calling the probable-prime test

`PrimeOk L code`: a verified probable-prime test of layout `L`, which uses at
most 176 bytes of stack. The witnesses from `u` on (`GP.randP`, `GP.rRand`)
are unchanged since the call's entry (`GI.randBytes`). A call's changes to
the working space are only in the test's ranges (`frame_of_keeps`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- A verified test of layout `L`, with the stack it uses. -/
structure PrimeOk (L : Spec.Dsa.ProbablePrime.Layout) (code : Prog isa) : Prop where
  verified : Verified target code (Spec.Dsa.ProbablePrime.contract L abi 176)
  stack : sdepth code ≤ 176

/-- A region's writes and a working space's kept bytes: what changed is the
working space's ranges `rs` and the other regions. -/
theorem frame_of_keeps {B : Addr} {wsLen : Nat} {rs : List (Nat × Nat)} {rest : List Region} {m m' : Mem}
    (hB : B.toNat + 8 * wsLen ≤ 2 ^ 64) (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ 8 * wsLen)
    (f : Frame (⟨B, wsLen * 8⟩ :: rest) m m') (hk : Spec.Dsa.ModPow.Keeps B wsLen rs m m') :
    Frame (rs.map (fun r => ⟨B + BitVec.ofNat 64 r.1, r.2⟩) ++ rest) m m' := by
  intro x hx
  by_cases hin : (⟨B, wsLen * 8⟩ : Region).Contains x 1
  · simp only [Region.Contains] at hin
    have hi : (x - B).toNat < 8 * wsLen := by omega
    have ex : x = B + BitVec.ofNat 64 (x - B).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm]; exact (BitVec.sub_add_cancel x B).symm
    rw [ex]
    refine hk _ hi fun r hr => ?_
    have hr' := hx _ (List.mem_append_left _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
    have hb := hrs r hr
    by_contra hc
    simp only [not_or, Nat.not_lt, Nat.not_le] at hc
    apply hr'
    have e : x - (B + BitVec.ofNat 64 r.1) = BitVec.ofNat 64 ((x - B).toNat - r.1) := by
      apply BitVec.eq_of_toNat_eq
      rw [← BitVec.sub_sub,
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    show (x - (B + BitVec.ofNat 64 r.1)).toNat + 1 ≤ r.2
    rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  · exact f x fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hin
      · exact hx r (List.mem_append_right _ hr)

/-! ## The witnesses -/

/-- Where the witnesses from `u` on start: `witnesses` itself when none is left. -/
abbrev GP.randP (G : GP) (u : Nat) : Addr := if u = G.witLen then G.wit else G.wit + BitVec.ofNat 64 u

/-- The witnesses from `u` on. -/
abbrev GP.rRand (G : GP) (u : Nat) : Region := ⟨G.randP u, G.witLen - u⟩

section
variable {G : GP} {STK : Nat} {σ s : State} {V : Nat → BitVec 64} {LS : List Nat}

theorem GI.witFit (h : GI G STK σ V LS s) : G.wit.toNat + G.witLen ≤ 2 ^ 64 := by
  have := h.pre.nW; rw [← h.hG]; exact this

theorem GI.randSub (h : GI G STK σ V LS s) {u : Nat} (hu : u ≤ G.witLen) : Region.Sub (G.rRand u) G.rWit := by
  have := h.witFit
  rcases Nat.lt_or_ge u G.witLen with hl | hl
  · show Region.Sub ⟨_, _⟩ _
    rw [GP.randP, ite_eq_right (by omega)]; exact Offset.sub_base _ (by omega)
  · intro a ha; simp only [Region.Contains, show G.witLen - u = 0 by omega] at ha; omega

theorem GI.randFit (h : GI G STK σ V LS s) {u : Nat} (hu : u ≤ G.witLen) :
    (G.randP u).toNat + (G.witLen - u) ≤ 2 ^ 64 := by
  have := h.witFit
  rcases Nat.lt_or_ge u G.witLen with hl | hl
  · rw [GP.randP, ite_eq_right (by omega), BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := u) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · have := (G.randP u).isLt; omega

/-- The witnesses are apart from what the search changes. -/
theorem GI.wit_apart (h : GI G STK σ V LS s) : ∀ r ∈ [G.rScr, rBelow σ STK], G.rWit.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [← h.hG]; exact h.pre.wC
  · rw [← h.hG]; exact h.pre.bW.symm

/-- The witnesses from `u` on, in memory. -/
theorem GI.randBytes (h : GI G STK σ V LS s) {u : Nat} (hu : u ≤ G.witLen) :
    Spec.Rsa.bytesAt s.mem (G.randP u) (G.witLen - u) = G.witB.drop u := by
  have fit := h.witFit
  have hw : Spec.Rsa.bytesAt s.mem G.wit G.witLen = G.witB := by
    rw [VG.Proof.Dsa.Generation.frame_bytesAt h.frame h.wit_apart (by omega), ← h.hG]; rfl
  rcases Nat.lt_or_ge u G.witLen with hl | hl
  · obtain ⟨d, hd⟩ : ∃ d, G.witLen = u + d := ⟨G.witLen - u, by omega⟩
    rw [GP.randP, ite_eq_right (by omega), show G.witLen - u = d by omega, ← hw, hd,
      VG.Proof.Dsa.Generation.bytesAt_append, List.drop_left' (by simp [Spec.Rsa.bytesAt])]
  · rw [show G.witLen - u = 0 by omega, List.drop_of_length_le (by
      rw [← hw]; simp [Spec.Rsa.bytesAt]; omega)]
    rfl

end

end VG.Proof.Dsa.PPC64LE.Gen
