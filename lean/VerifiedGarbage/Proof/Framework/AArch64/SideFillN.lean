module

public import VerifiedGarbage.Proof.Framework.AArch64.SideFill

/-!
# The cleanup of code that calls several implementations (AArch64)

`Code.fill2` (`SideFill.lean`) has two kinds of holes. A function that calls
more implementations than two (AES-GCM's: of `vg_aes_ctr32`, its out-of-place
form, `vg_aes_expand_key_scratch` and `vg_ghash`) has a kind of hole for each:
hole `k` is a call whose body is `k + 1` empty blocks in sequence
(`Code.holeIx`), and `Code.fillN bs` replaces each hole `k` by `bs[k]`. As
there, the kernel evaluates the code with its holes once, whatever the
implementations: `side_depth_of_fillN` gives a property of every instruction
(`sideAll p`, for any `p`: no write of PSTATE.DIT, or the registers a cleanup
needs kept, `calleeSide`) and the depth of the stack, from those of the code
with its holes and of the implementations.
-/

@[expose] public section

namespace VG

/-- The number of the hole a call's body stands for: `.block []` is hole 0,
`.seq (.block []) (.block [])` hole 1, and so on (`Code.fill2`'s two are the
first two). -/
def Code.holeIx {M : ISA} : Prog M → Option Nat
  | .block [] => some 0
  | .seq (.block []) y => (holeIx y).map (· + 1)
  | _ => none

/-- `c` with each call that is hole `k` (`Code.holeIx` of its body) replaced
by the code `bs[k]`, in the bodies of the functions `c` calls too. -/
def Code.fillN {M : ISA} (bs : List (Prog M)) : Prog M → Prog M
  | .block is => .block is
  | .seq x y => .seq (fillN bs x) (fillN bs y)
  | .ite cd t e => .ite cd (fillN bs t) (fillN bs e)
  | .loop x cd => .loop (fillN bs x) cd
  | .call m body => match body.holeIx with
    | some k => bs.getD k (.call m body)
    | none => .call m (fillN bs body)
  | .frame i x j => .frame i (fillN bs x) j
  | .icall i m x y => .icall i m x y

/-- `Code.aarch64Depth` of code with holes, hole `k` standing for code of
depth `ds[k]`. -/
def Code.aarch64DepthN (ds : List Nat) : Prog AArch64.isa → Nat
  | .block _ => 0
  | .seq x y => max (aarch64DepthN ds x) (aarch64DepthN ds y)
  | .ite _ t e => max (aarch64DepthN ds t) (aarch64DepthN ds e)
  | .loop x _ => aarch64DepthN ds x
  | .call _ body => match body.holeIx with
    | some k => ds.getD k body.aarch64Depth
    | none => aarch64DepthN ds body
  | .frame i x _ => aarch64DepthN ds x + i.frameUnits
  | .icall _ _ x y => max x.aarch64Depth y.aarch64Depth

private theorem depth_getD {bs : List (Prog AArch64.isa)} {ds : List Nat}
    (h : List.Forall₂ (fun b d => b.aarch64Depth ≤ d) bs ds) (k : Nat) (x : Prog AArch64.isa) :
    (bs.getD k x).aarch64Depth ≤ ds.getD k x.aarch64Depth := by
  induction h generalizing k with
  | nil => exact Nat.le_refl _
  | cons hd _ ih =>
    cases k with
    | zero => exact hd
    | succ k => simpa only [List.getD_cons_succ] using ih k

theorem Code.aarch64Depth_fillN_le {bs : List (Prog AArch64.isa)} {ds : List Nat}
    (h : List.Forall₂ (fun b d => b.aarch64Depth ≤ d) bs ds) (e : Prog AArch64.isa) :
    (Code.fillN bs e).aarch64Depth ≤ Code.aarch64DepthN ds e := by
  induction e with
  | block is => exact Nat.le_refl _
  | seq x y ihx ihy =>
    simp only [Code.fillN, Code.aarch64Depth, Code.aarch64DepthN]
    omega_using [ihx, ihy]
  | ite cd t e iht ihe =>
    simp only [Code.fillN, Code.aarch64Depth, Code.aarch64DepthN]
    omega_using [iht, ihe]
  | loop x cd ih => simpa only [Code.fillN, Code.aarch64Depth, Code.aarch64DepthN] using ih
  | call m body ih =>
    unfold Code.fillN Code.aarch64DepthN
    split
    · exact depth_getD h _ (.call m body)
    · simpa only [Code.aarch64Depth] using ih
  | frame i x j ih =>
    simp only [Code.fillN, Code.aarch64Depth, Code.aarch64DepthN]
    omega_using [ih]
  | icall i m x y => exact Nat.le_refl _

namespace AArch64.ScrubAll

/-- `sideAll` of code with its holes filled, from the code's and the
fillings'. -/
theorem sideAll_fillN {p : Instr → Bool} {bs : List (Prog isa)} {e : Prog isa}
    (hb : ∀ b ∈ bs, sideAll p b = true) (he : sideAll p e = true) :
    sideAll p (Code.fillN bs e) = true := by
  induction e with
  | block is => exact he
  | seq x y ihx ihy =>
    simp only [Code.fillN, sideAll, Bool.and_eq_true] at he ⊢
    exact ⟨ihx he.1, ihy he.2⟩
  | ite cd t e iht ihe =>
    simp only [Code.fillN, sideAll, Bool.and_eq_true] at he ⊢
    exact ⟨iht he.1, ihe he.2⟩
  | loop x cd ih => simp only [Code.fillN, sideAll] at he ⊢; exact ih he
  | call m body ih =>
    unfold Code.fillN
    split
    · rename_i k _
      rw [List.getD_eq_getElem?_getD]
      cases hk : bs[k]? with
      | none => exact he
      | some b => exact hb b (List.mem_of_getElem? hk)
    · simp only [sideAll] at he ⊢; exact ih he
  | frame i x j ih =>
    simp only [Code.fillN, sideAll, Bool.and_eq_true] at he ⊢
    exact ⟨⟨he.1.1, ih he.1.2⟩, he.2⟩
  | icall i m x y => simp only [sideAll, Bool.false_eq_true] at he

/-- What a cleanup needs of code `c` that is the closed code `e` with its
holes filled by `bs`: `sideAll p` and the depth of `e`, which the kernel
evaluates once, and those of each of `bs`. -/
theorem side_depth_of_fillN {p : Instr → Bool} {c e : Prog isa} {bs : List (Prog isa)}
    {ds : List Nat} {d : Nat} (hc : c = Code.fillN bs e) (hb : ∀ b ∈ bs, sideAll p b = true)
    (hd : List.Forall₂ (fun b n => b.aarch64Depth ≤ n) bs ds) (he : sideAll p e = true)
    (hde : Code.aarch64DepthN ds e ≤ d) : sideAll p c = true ∧ c.aarch64Depth ≤ d := by
  subst hc
  exact ⟨sideAll_fillN hb he, Nat.le_trans (Code.aarch64Depth_fillN_le hd e) hde⟩

end AArch64.ScrubAll

end VG
