module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SContract
public import VerifiedGarbage.Proof.RsaPss.X86_64.VCTBase
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS signing on x86-64: relating two runs

As verification's (`VCTBase.lean`): each point of the code is described,
in each run, by what correctness says of it from that run's entry state,
which has the same public data as an anchor (`SAt`); the pieces between the
calls are checked by the taint analysis from the frame's public slots
(`s_taintF`), the branches are on public data (`s_ite`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes oRsa)
open VG.Proof.RsaOaep.X86_64 (decStack stkD fb frR frame_subD Lay Rep upd nW tw tw_eq Like frT two_taintF
  bytesAt_getD selW fnW outR fns_of_tab FnsD)

variable (kH kG : Nat)

/-- An entry state with the anchor `a`'s public data, the selectors `kH` and
`kG` and the anchor's regions. -/
def SSib (a s : State) : Prop :=
  SPre s ∧ sPub a s ∧ sselH s = kH ∧ sselG s = kG ∧ s.rd = a.rd ∧ s.wr = a.wr

/-- What `J` says of a run from an entry state with the anchor's public data. -/
def SAt (J : State → State → Prop) (a t : State) : Prop := ∃ s, SSib kH kG a s ∧ J s t

variable {kH kG}

theorem sPub_refl (s : State) : sPub s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, by simp only [abi, Option.elim]⟩⟩

theorem SSib.gpr {a s : State} (h : SSib kH kG a s) {r : Reg}
    (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) : s.gpr r = a.gpr r := (h.2.1.1 r hr).symm

theorem SSib.arg {a s : State} (h : SSib kH kG a s) {j : Nat} (hj : j < 20) : stackArg s j = stackArg a j :=
  ((List.map_inj_left.mp h.2.1.2.1) j (List.mem_range.mpr hj)).symm

theorem SSib.fb {a s : State} (h : SSib kH kG a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _; rw [h.gpr (r := .rsp) (by decide)]

theorem SSib.out_eq {a s : State} (h : SSib kH kG a s) : outR s = outR a := by
  unfold outR; rw [h.gpr (r := .rdi) (by decide), h.gpr (r := .rsi) (by decide)]

theorem SSib.scr_eq {a s : State} (h : SSib kH kG a s) : sscrR s = sscrR a := by
  simp only [sscrR, h.arg (j := 14) (by decide), h.arg (j := 15) (by decide)]

theorem SSib.n0 {a s : State} (h : SSib kH kG a s) : sn0v s = sn0v a := by
  have hk := h.1.k1
  have := congrArg (fun l => l.getD 0 0) h.2.1.2.2.1
  rw [bytesAt_getD _ _ (by rw [← h.gpr (r := .rcx) (by decide)]; omega), bytesAt_getD _ _ (by omega)] at this
  simp only [BitVec.add_zero] at this
  unfold sn0v; rw [this]

theorem SSib.tw {a s : State} (h : SSib kH kG a s) {j : Nat} (hj : j = 18 ∨ j = 19) {i : Nat} (hi : i < 3) :
    tw s.mem (stackArg s j) i = tw a.mem (stackArg a j) i := by
  rcases hj with rfl | rfl
  · exact (tw_eq h.2.1.2.2.2.2.1 hi).symm
  · exact (tw_eq h.2.1.2.2.2.2.2.1 hi).symm

/-- An entry with the anchor's public data and regions is like it. -/
theorem SSib.like {a s : State} (h : SSib kH kG a s) : Like a s := by
  obtain ⟨f, c, y⟩ := h.2.1.2.2.2.2.2.2
  simp only [abi, Option.elim] at y
  exact ⟨⟨f.symm, c.symm, by simp only [abi, Option.elim]; exact y.symm⟩, h.2.2.2.2.1, h.2.2.2.2.2,
    h.gpr (r := .rsp) (by decide)⟩

theorem SSib.cw {a s : State} (h : SSib kH kG a s) {k : Nat} (hk : k ∈ vKs) : scW s k = scW a k := by
  simp only [vKs, List.mem_cons, List.not_mem_nil, or_false] at hk
  have e : ∀ j < 20, stackArg s j = stackArg a j := fun j hj => h.arg hj
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [scW, signW, fnW, selW, signPW, upd, sselH, sselG, e 10 (by decide), e 12 (by decide), e 13 (by decide),
    e 14 (by decide), e 15 (by decide), e 16 (by decide), e 17 (by decide), h.n0,
    h.tw (j := 18) (.inl rfl) (i := 0) (by decide), h.tw (j := 18) (.inl rfl) (i := 1) (by decide),
    h.tw (j := 18) (.inl rfl) (i := 2) (by decide), h.tw (j := 19) (.inr rfl) (i := 0) (by decide),
    h.tw (j := 19) (.inr rfl) (i := 1) (by decide), h.tw (j := 19) (.inr rfl) (i := 2) (by decide),
    h.gpr (r := .rdi) (by decide), h.gpr (r := .rdx) (by decide), h.gpr (r := .rcx) (by decide),
    h.gpr (r := .r8) (by decide), h.gpr (r := .r9) (by decide)]

/-- The streaming functions of the table `i` (18 or 19), for the selector's
hash function. -/
theorem SSib.fns {a s : State} (S : SSib kH kG a s) {T : Spec.HashFns.Streaming} {i : Nat}
    (h : (i = 18 ∧ Spec.HashFns.streaming kH = some T) ∨ (i = 19 ∧ Spec.HashFns.streaming kG = some T)) :
    FnsD s T i := by
  rcases h with ⟨rfl, sT'⟩ | ⟨rfl, sT'⟩
  · obtain ⟨T', _, sT, _, _, hF⟩ := fns_of_tab S.1.fH
    rw [S.2.2.1, sT', Option.some.injEq] at sT
    subst sT; exact hF
  · obtain ⟨T', _, sT, _, _, hF⟩ := fns_of_tab S.1.fG
    rw [S.2.2.2.1, sT', Option.some.injEq] at sT
    subst sT; exact hF

/-- The frame and the writable regions, for the taint analysis. -/
theorem SEnv.frv {s t : State} (hp : SPre s) (he : SEnv s t) :
    VG.Proof.RsaOaep.X86_64.FrV 2 (fb s) [outR s, sscrR s] t where
  rsp := he.rsp
  wr := he.wr
  two := rfl
  pw := by
    refine .cons ?_ (.cons ?_ (.cons (fun _ h => absurd h List.not_mem_nil) .nil))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.dKO.sub_left (frame_subD s)
      · exact hp.dKs.sub_left (frame_subD s)
    · intro r hr
      rw [List.mem_singleton.mp hr]
      exact hp.dOs
  len r hr := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Nat.le_of_lt (BitVec.isLt _)
    · have := hp.wS; show (stackArg s 15).toNat * 8 ≤ 2 ^ 64; omega

/-- Code the taint analysis checks from the frame's slots `ks`, whose words
`wv s` the entry's public data fix. -/
theorem s_taintF {J : State → State → Prop} {ks : List Nat} (wv : State → Nat → BitVec 64)
    (hJ : ∀ s t, SPre s → J s t → SEnv s t ∧ ∀ k ∈ ks, word t.mem (fb s) (8 * k) = wv s k)
    (hsib : ∀ a s, SSib kH kG a s → ∀ k ∈ ks, wv s k = wv a k)
    (rs : List Reg) (hk : ∀ k ∈ ks, k < nW) (hpin : Pins (SAt kH kG J) rs) {c : Prog isa}
    (h : ∃ hc, (taint.check (frT rs ks 2) c hc).isSome = true) :
    RelCT isa (Two (SAt kH kG J)) c fun _ _ => True :=
  two_taintF rs ks fb (fun a => [outR a, sscrR a]) wv (fun a t ⟨s, S, j⟩ => by
      obtain ⟨e, hw⟩ := hJ s t S.1 j
      rw [← S.fb, ← S.out_eq, ← S.scr_eq]
      exact ⟨e.frv S.1, fun k hk => (hw k hk).trans (hsib a s S k hk)⟩)
    hpin hk h

/-- What correctness says after a piece. -/
theorem s_post {J J' : State → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two (SAt kH kG J)) c fun _ _ => True)
    (hw : ∀ a s t, SSib kH kG a s → J s t → WP isa c t (J' s)) :
    RelCT isa (Two (SAt kH kG J)) c (Two (SAt kH kG J')) :=
  two_post hct fun a t ⟨s, S, j⟩ => WP.mono (hw a s t S j) fun _ j' => ⟨s, S, j'⟩

/-- Registers whose values the entry's public data fix. -/
theorem s_pins {J : State → State → Prop} (rs : List Reg) (f : State → Reg → BitVec 64)
    (hJ : ∀ s t, SPre s → J s t → ∀ r ∈ rs, t.gpr r = f s r)
    (hs : ∀ a s, SSib kH kG a s → ∀ r ∈ rs, f s r = f a r) : Pins (SAt kH kG J) rs :=
  fun _ _ _ ⟨_, S₁, j₁⟩ ⟨_, S₂, j₂⟩ r hr => by
    rw [hJ _ _ S₁.1 j₁ r hr, hJ _ _ S₂.1 j₂ r hr, hs _ _ S₁ r hr, hs _ _ S₂ r hr]

/-- A branch on a condition that the entry state's public data fixes. -/
theorem s_ite {J : State → State → Prop} {cond : isa.Cond} {th el : Prog isa} {Q : State → State → Prop}
    (f : State → Option Bool) (hf : ∀ s t, J s t → isa.eval cond t = f s)
    (hs : ∀ a s, SSib kH kG a s → f s = f a)
    (ht : RelCT isa (Two fun a t => SAt kH kG J a t ∧ isa.eval cond t = some true) th Q)
    (he : RelCT isa (Two fun a t => SAt kH kG J a t ∧ isa.eval cond t = some false) el Q) :
    RelCT isa (Two (SAt kH kG J)) (.ite cond th el) Q :=
  two_ite (fun _ _ _ ⟨_, S₁, j₁⟩ ⟨_, S₂, j₂⟩ => by rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]) ht he

/-- In a branch, what its condition says of the entry state. -/
theorem s_branch {J J' : State → State → Prop} {cond : isa.Cond} {b : Bool} {c : Prog isa}
    {Q : State → State → Prop} (h : ∀ s t, SPre s → J s t → isa.eval cond t = some b → J' s t)
    (hct : RelCT isa (Two (SAt kH kG J')) c Q) :
    RelCT isa (Two fun a t => SAt kH kG J a t ∧ isa.eval cond t = some b) c Q :=
  hct.mono (fun _ _ ⟨a, ⟨⟨s₁, S₁, j₁⟩, e₁⟩, ⟨⟨s₂, S₂, j₂⟩, e₂⟩⟩ =>
    ⟨a, ⟨s₁, S₁, h _ _ S₁.1 j₁ e₁⟩, ⟨s₂, S₂, h _ _ S₂.1 j₂ e₂⟩⟩) fun _ _ h => h

end VG.Proof.RsaPss.X86_64
