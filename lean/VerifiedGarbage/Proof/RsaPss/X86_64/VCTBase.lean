module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VContract
public import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfCT
public import VerifiedGarbage.Proof.RsaOaep.X86_64.SelCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS verification on x86-64: relating two runs

Each point of the code is described, in each run, by what correctness says of
it from that run's entry state, which has the same public data as an anchor
(`VAt`, as in RSAES-OAEP's `EncCT.lean`): the pieces between the calls are
checked by the taint analysis from the frame's public slots (`v_taintF`),
the branches are on public data (`v_ite`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes oRsa)
open VG.Proof.RsaOaep.X86_64 (encStack stkR fb frR frame_sub Lay Rep upd nW tw tw_eq Like frT two_taintF
  bytesAt_getD selW fnW)

variable (kH kG : Nat)

/-- An entry state with the anchor `a`'s public data, the selectors `kH` and
`kG` and the anchor's regions. -/
def VSib (a s : State) : Prop :=
  VPre s ∧ vPub a s ∧ vselH s = kH ∧ vselG s = kG ∧ s.rd = a.rd ∧ s.wr = a.wr

/-- What `J` says of a run from an entry state with the anchor's public data. -/
def VAt (J : State → State → Prop) (a t : State) : Prop := ∃ s, VSib kH kG a s ∧ J s t

variable {kH kG}

theorem vPub_refl (s : State) : vPub s s :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [abi]⟩

theorem VSib.gpr {a s : State} (h : VSib kH kG a s) {r : Reg}
    (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) : s.gpr r = a.gpr r := (h.2.1.1 r hr).symm

theorem VSib.arg {a s : State} (h : VSib kH kG a s) {j : Nat} (hj : j ∈ [0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11]) :
    stackArg s j = stackArg a j := (h.2.1.2.1 j hj).symm

theorem VSib.fb {a s : State} (h : VSib kH kG a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _; rw [h.gpr (r := .rsp) (by decide)]

theorem VSib.scr_eq {a s : State} (h : VSib kH kG a s) : vscrR s = vscrR a := by
  simp only [vscrR, h.arg (j := 4) (by decide), h.arg (j := 5) (by decide)]

theorem VSib.fixed {a s : State} (h : VSib kH kG a s) : vfixed s = vfixed a := by
  simp only [vfixed, h.2.1.2.2.1]

theorem VSib.n0 {a s : State} (h : VSib kH kG a s) : n0v s = n0v a := by
  have hk := h.1.k1
  have := congrArg (fun l => l.getD 0 0) h.2.1.2.2.2.1
  rw [bytesAt_getD _ _ (by rw [← h.gpr (r := .rsi) (by decide)]; omega), bytesAt_getD _ _ (by omega)] at this
  simp only [BitVec.add_zero] at this
  unfold n0v; rw [this]

theorem VSib.tw {a s : State} (h : VSib kH kG a s) {j : Nat} (hj : j = 10 ∨ j = 11) {i : Nat} (hi : i < 3) :
    tw s.mem (stackArg s j) i = tw a.mem (stackArg a j) i := by
  rcases hj with rfl | rfl
  · exact (tw_eq h.2.1.2.2.2.2.2.2.1 hi).symm
  · exact (tw_eq h.2.1.2.2.2.2.2.2.2.1 hi).symm

/-- An entry with the anchor's public data and regions is like it. -/
theorem VSib.like {a s : State} (h : VSib kH kG a s) : Like a s := by
  obtain ⟨f, c, y⟩ := h.2.1.2.2.2.2.2.2.2.2
  simp only [abi, Option.elim] at y
  exact ⟨⟨f.symm, c.symm, by simp only [abi, Option.elim]; exact y.symm⟩, h.2.2.2.2.1, h.2.2.2.2.2,
    h.gpr (r := .rsp) (by decide)⟩

theorem VSib.cw {a s : State} (h : VSib kH kG a s) {k : Nat} (hk : k ∈ vKs) : vcW s k = vcW a k := by
  simp only [vKs, List.mem_cons, List.not_mem_nil, or_false] at hk
  have e : ∀ j ∈ [0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11], stackArg s j = stackArg a j := fun j hj => h.arg hj
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [vcW, verW, fnW, selW, verPW, upd, vselH, vselG, e 0 (by decide), e 3 (by decide), e 4 (by decide),
    e 5 (by decide), e 8 (by decide), e 9 (by decide), h.fixed, h.n0, h.tw (j := 10) (.inl rfl) (i := 0) (by decide),
    h.tw (j := 10) (.inl rfl) (i := 1) (by decide), h.tw (j := 10) (.inl rfl) (i := 2) (by decide),
    h.tw (j := 11) (.inr rfl) (i := 0) (by decide), h.tw (j := 11) (.inr rfl) (i := 1) (by decide),
    h.tw (j := 11) (.inr rfl) (i := 2) (by decide),
    h.gpr (r := .rdi) (by decide), h.gpr (r := .rsi) (by decide), h.gpr (r := .rdx) (by decide),
    h.gpr (r := .rcx) (by decide), h.gpr (r := .r8) (by decide)]

/-- The frame and the working space, for the taint analysis. -/
theorem VEnv.frv {s t : State} (hp : VPre s) (he : VEnv s t) :
    VG.Proof.RsaOaep.X86_64.FrV 1 (fb s) [vscrR s] t where
  rsp := he.rsp
  wr := he.wr
  two := rfl
  pw := .cons (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.dKS.sub_left (frame_sub s))
    (.cons (fun _ h => absurd h List.not_mem_nil) .nil)
  len r hr := by
    rw [List.mem_singleton.mp hr]
    have := hp.wS; show (stackArg s 5).toNat * 8 ≤ 2 ^ 64; omega

/-- Code the taint analysis checks from the frame's slots `ks`, whose words
`wv s` the entry's public data fix. -/
theorem v_taintF {J : State → State → Prop} {ks : List Nat} (wv : State → Nat → BitVec 64)
    (hJ : ∀ s t, VPre s → J s t → VEnv s t ∧ ∀ k ∈ ks, word t.mem (fb s) (8 * k) = wv s k)
    (hsib : ∀ a s, VSib kH kG a s → ∀ k ∈ ks, wv s k = wv a k)
    (rs : List Reg) (hk : ∀ k ∈ ks, k < nW) (hpin : Pins (VAt kH kG J) rs) {c : Prog isa}
    (h : ∃ hc, (taint.check (frT rs ks 1) c hc).isSome = true) :
    RelCT isa (Two (VAt kH kG J)) c fun _ _ => True :=
  two_taintF rs ks fb (fun a => [vscrR a]) wv (fun a t ⟨s, S, j⟩ => by
      obtain ⟨e, hw⟩ := hJ s t S.1 j
      rw [← S.fb, ← S.scr_eq]
      exact ⟨e.frv S.1, fun k hk => (hw k hk).trans (hsib a s S k hk)⟩)
    hpin hk h

/-- What correctness says after a piece. -/
theorem v_post {J J' : State → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two (VAt kH kG J)) c fun _ _ => True)
    (hw : ∀ a s t, VSib kH kG a s → J s t → WP isa c t (J' s)) :
    RelCT isa (Two (VAt kH kG J)) c (Two (VAt kH kG J')) :=
  two_post hct fun a t ⟨s, S, j⟩ => WP.mono (hw a s t S j) fun _ j' => ⟨s, S, j'⟩

/-- Registers whose values the entry's public data fix. -/
theorem v_pins {J : State → State → Prop} (rs : List Reg) (f : State → Reg → BitVec 64)
    (hJ : ∀ s t, VPre s → J s t → ∀ r ∈ rs, t.gpr r = f s r)
    (hs : ∀ a s, VSib kH kG a s → ∀ r ∈ rs, f s r = f a r) : Pins (VAt kH kG J) rs :=
  fun _ _ _ ⟨_, S₁, j₁⟩ ⟨_, S₂, j₂⟩ r hr => by
    rw [hJ _ _ S₁.1 j₁ r hr, hJ _ _ S₂.1 j₂ r hr, hs _ _ S₁ r hr, hs _ _ S₂ r hr]

/-- A branch on a condition that the entry state's public data fixes. -/
theorem v_ite {J : State → State → Prop} {cond : isa.Cond} {th el : Prog isa} {Q : State → State → Prop}
    (f : State → Option Bool) (hf : ∀ s t, J s t → isa.eval cond t = f s)
    (hs : ∀ a s, VSib kH kG a s → f s = f a)
    (ht : RelCT isa (Two fun a t => VAt kH kG J a t ∧ isa.eval cond t = some true) th Q)
    (he : RelCT isa (Two fun a t => VAt kH kG J a t ∧ isa.eval cond t = some false) el Q) :
    RelCT isa (Two (VAt kH kG J)) (.ite cond th el) Q :=
  two_ite (fun _ _ _ ⟨_, S₁, j₁⟩ ⟨_, S₂, j₂⟩ => by rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]) ht he

/-- In a branch, what its condition says of the entry state. -/
theorem v_branch {J J' : State → State → Prop} {cond : isa.Cond} {b : Bool} {c : Prog isa}
    {Q : State → State → Prop} (h : ∀ s t, VPre s → J s t → isa.eval cond t = some b → J' s t)
    (hct : RelCT isa (Two (VAt kH kG J')) c Q) :
    RelCT isa (Two fun a t => VAt kH kG J a t ∧ isa.eval cond t = some b) c Q :=
  hct.mono (fun _ _ ⟨a, ⟨⟨s₁, S₁, j₁⟩, e₁⟩, ⟨⟨s₂, S₂, j₂⟩, e₂⟩⟩ =>
    ⟨a, ⟨s₁, S₁, h _ _ S₁.1 j₁ e₁⟩, ⟨s₂, S₂, h _ _ S₂.1 j₂ e₂⟩⟩) fun _ _ h => h

end VG.Proof.RsaPss.X86_64
