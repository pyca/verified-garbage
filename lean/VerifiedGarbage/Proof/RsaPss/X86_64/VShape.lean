module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VCTBase
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS verification on x86-64: the points of `verifyMain`, for two runs

`VS P`: in the frame, with the argument slots, `DB`'s address and length
(words 33 and 44) and what `P` says of the frame's words; the words of the
public slots, as the entry state's public data fix them (`vwv`), and the
streaming functions the code calls (`VSib.calls`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes oEm oRsa)
open VG.Proof.RsaOaep.X86_64 (encStack stkR fb frR frame_sub Lay Rep upd nW tw Like Calls Fns frT lenOf)

/-- The checks passed. -/
def VFit (s : State) : Prop := n0v s ≠ 0 ∧ lenOf (vselH s) + 2 + vsl s ≤ vk s - loV (n0v s)

/-- `DB`'s offset in our working space, `dbLen`, and `hLen`. -/
abbrev vE (s : State) : Nat := oEm + loV (n0v s)
abbrev vDb (s : State) : Nat := vk s - loV (n0v s) - (lenOf (vselH s) + 2) + 1
abbrev vD (s : State) : Nat := lenOf (vselH s)

/-- In the frame, with the argument slots, `DB`'s address and length, and `P`
of the frame's words, after the checks. -/
def VS (P : State → (Nat → BitVec 64) → Prop) (s t : State) : Prop :=
  VEnv s t ∧ Lay t (fb s) (stackArg s 4) ∧
    (∃ V W, Rep t.mem (fb s) (stackArg s 4) V W ∧ ArgsV s W ∧ W 33 = off (stackArg s 4) (vE s) ∧
      W 44 = BitVec.ofNat 64 (vDb s) ∧ P s W) ∧ VFit s

/-- The public slots' words. -/
def vwv (s : State) (k : Nat) : BitVec 64 :=
  if k = 33 then off (stackArg s 4) (vE s) else if k = 44 then BitVec.ofNat 64 (vDb s) else vcW s k

variable {kH kG : Nat}

theorem VSib.e_eq {a s : State} (S : VSib kH kG a s) : vE s = vE a := by simp only [vE, S.n0]

theorem VSib.db_eq {a s : State} (S : VSib kH kG a s) : vDb s = vDb a := by
  simp only [vDb, vk, S.n0, S.gpr (r := .rsi) (by decide), vselH, S.arg (j := 8) (by decide)]

theorem VSib.d_eq {a s : State} (S : VSib kH kG a s) : vD s = vD a := by
  simp only [vD, vselH, S.arg (j := 8) (by decide)]

theorem VSib.sl_eq {a s : State} (S : VSib kH kG a s) : vsl s = vsl a := by
  simp only [vsl, S.fixed, S.arg (j := 3) (by decide)]

theorem VSib.wv_eq {a s : State} (S : VSib kH kG a s) {k : Nat} (hk : k ∈ vKs ∨ k = 33 ∨ k = 44) :
    vwv s k = vwv a k := by
  unfold vwv
  by_cases h33 : k = 33
  · rw [ifp h33, ifp h33, S.e_eq, S.arg (j := 4) (by decide)]
  · rw [ifn h33, ifn h33]
    by_cases h44 : k = 44
    · rw [ifp h44, ifp h44, S.db_eq]
    · rw [ifn h44, ifn h44]
      rcases hk with hk | hk | hk
      · exact S.cw hk
      · exact absurd hk h33
      · exact absurd hk h44

theorem VS.words {P : State → (Nat → BitVec 64) → Prop} {s t : State} (h : VS P s t) {k : Nat}
    (hk : k ∈ vKs ∨ k = 33 ∨ k = 44) : word t.mem (fb s) (8 * k) = vwv s k := by
  obtain ⟨-, -, ⟨V, W, R, hA, h33, h44, -⟩, -⟩ := h
  have hlt : k < nW := by
    rcases hk with hk | rfl | rfl
    · have := vKs_iff hk; unfold nW frameBytes; omega
    · decide
    · decide
  rw [R.fr k hlt]
  unfold vwv
  by_cases e33 : k = 33
  · subst e33; rw [ifp rfl]; exact h33
  · rw [ifn e33]
    by_cases e44 : k = 44
    · subst e44; rw [ifp rfl]; exact h44
    · rw [ifn e44]
      rcases hk with hk | hk | hk
      · exact hA k hk
      · exact absurd hk e33
      · exact absurd hk e44

/-- Code the taint analysis checks from the public slots `ks`, at a point
`VS P`. -/
theorem v_taintS {J : State → State → Prop} {P : State → (Nat → BitVec 64) → Prop} (hJ : ∀ s t, J s t → VS P s t)
    (rs : List Reg) (ks : List Nat) (hks : ∀ k ∈ ks, k ∈ vKs ∨ k = 33 ∨ k = 44) (hpin : Pins (VAt kH kG J) rs)
    {c : Prog isa} (h : ∃ hc, (taint.check (frT rs ks 1) c hc).isSome = true) :
    RelCT isa (Two (VAt kH kG J)) c fun _ _ => True :=
  v_taintF (ks := ks) vwv (fun s t _ j => ⟨(hJ s t j).1, fun k hk => (hJ s t j).words (hks k hk)⟩)
    (fun a s S k hk => S.wv_eq (hks k hk)) rs (fun k hk => by
      rcases hks k hk with h | rfl | rfl
      · have := vKs_iff h; unfold nW frameBytes; omega
      · decide
      · decide) hpin h

/-- The streaming functions of the table `j` (10 or 11), the anchor's, which a
state in the frame of a run from a sibling of the anchor may call. -/
theorem VSib.calls {a s t : State} (S : VSib kH kG a s) (he : VEnv s t) {T : Spec.HashFns.Streaming} {j : Nat}
    (hj : j = 10 ∨ j = 11) (fF : VFns s T j) :
    Calls encStack T a (VG.Proof.RsaOaep.X86_64.fb a) (stackArg a 4) (VG.Proof.RsaOaep.X86_64.tw a.mem (stackArg a j) 0)
      (VG.Proof.RsaOaep.X86_64.tw a.mem (stackArg a j) 1) (VG.Proof.RsaOaep.X86_64.tw a.mem (stackArg a j) 2) t := by
  refine ⟨s, ?_, ?_, S.like⟩
  · have := he.here; rwa [S.fb, S.arg (j := 4) (by decide)] at this
  · have e0 := S.tw hj (i := 0) (by decide)
    have e1 := S.tw hj (i := 1) (by decide)
    have e2 := S.tw hj (i := 2) (by decide)
    unfold VFns at fF
    rwa [e0, e1, e2] at fF

end VG.Proof.RsaPss.X86_64
