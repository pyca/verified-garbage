module

public import VerifiedGarbage.Proof.RsaPss.AArch64.Mgf
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
public import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfTCT
public import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.RsaPss.AArch64.Mgf
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfTCT
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
meta import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# RSASSA-PSS on AArch64: `mgfXor` is constant time

Two runs of `mgfXor` with the same frame, working space, `DB` (its place `e`
and length `db`, public) and table of `Hash`, whose functions are at the same
addresses (`MS`), leak the same trace (`mgfXor_ct`): MGF1's arguments to
its slots by the taint analysis (from `scratch`, `DB` and `dbLen`, which the
anchor fixes), then OAEP's MGF1 with a table, constant time from what
`setup_ok` establishes in each run (`Table.mgfXorT_tr`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two)
open VG.Proof.MlKem.AArch64 (Keep)

/-- What two runs of `mgfXor` share: the frame, the working space, `DB`,
the table of `Hash`, and the addresses of its functions. -/
structure MA where
  F : Addr
  S : Addr
  e : Nat
  db : Nat
  p : Addr
  ai : Addr
  au : Addr
  af : Addr

/-- `mgfXor`'s start, with the anchor's frame, working space, `DB` and
table. -/
structure MS (G : Impl.Pbkdf2.Md.AArch64.Stream) (g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns) (D : Nat) (a : MA)
    (t : State) : Prop where
  L : Lay t a.F a.S
  hd : DbAt D a.e a.db
  x24 : t.gpr .x24 = off a.S a.e
  x25 : t.gpr .x25 = BitVec.ofNat 64 a.db
  env : Env G g t a.F a.S a.p
  ai : t.syms G.initN = a.ai
  au : t.syms G.updN = a.au
  af : t.syms G.finN = a.af

section
variable {G : Impl.Pbkdf2.Md.AArch64.Stream} (hG : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK G)
  {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns}

/-- A hash function with no sizes, for the taint analysis of MGF1's
arguments without their immediates. -/
def zH' : Hash := ⟨⟨0, 0, 0, 0, [], []⟩, 0, 0, "", .block [], "", .block [], "", .block [], "", .block [], "", "", ""⟩

include hG in
theorem mgfXor_ct {H : Hash} : RelCT isa (Two (MS G g H.D)) (mgfXor H g) fun _ _ => True := by
  unfold mgfXor
  refine RelCT.alloc (R := fun _ _ => True) ((RelCT.exists_ (P := fun a σ₁ σ₂ =>
      (∃ s, MS G g H.D a s ∧ σ₁ = allocated mgfFrame s) ∧ ∃ t, MS G g H.D a t ∧ σ₂ = allocated mgfFrame t)
    fun a => ?_).mono (fun _ _ ⟨s, t, ⟨a, h₁, h₂⟩, e₁, e₂⟩ => ⟨a, ⟨s, h₁, e₁⟩, t, h₂, e₂⟩) fun _ _ h => h)
  by_cases hf : Proof.RsaOaep.AArch64.MFit (a.e + a.db - mgfOff) H.D (a.e - mgfOff) a.db
  swap
  · refine RelCT.of_false fun _ _ ⟨⟨s, h, _⟩, _⟩ => hf ?_
    have := h.hd.fit; have := h.hd.e1; have := h.hd.db1
    exact ⟨by unfold Impl.RsaOaep.AArch64.oSt mgfOff oY oEm at *; omega, by unfold Impl.RsaOaep.AArch64.oSt mgfOff oY oEm at *; omega,
      .inr (by unfold mgfOff oEm at *; omega), h.hd.db1, by unfold oY oEm at *; omega⟩
  let F : State → State → Prop := fun σ u => ∃ s, MS G g H.D a s ∧ σ = allocated mgfFrame s ∧
    u.syms = s.syms ∧ Proof.RsaOaep.AArch64.Lay u (mF a.F) (off a.S mgfOff) ∧
    Proof.RsaOaep.AArch64.Rep u.mem (mF a.F) (off a.S mgfOff) (fun o => s.mem (off (off a.S mgfOff) o))
      (argsW s (mF a.F) H.D) ∧
    Proof.RsaOaep.AArch64.Table.Tab G g (mF a.F) (off a.S mgfOff) a.p (mgfFrame + sMgfT) u ∧
    Proof.RsaOaep.AArch64.MArgs (argsW s (mF a.F) H.D) (off a.S mgfOff) (a.e + a.db - mgfOff) H.D (a.e - mgfOff) a.db
  refine RelCT.seq (((RelCT.taint (A := taint) (Taint.ofRegs [.x20, .x24, .x25]) (fun s₁ s₂ hp => ?_)
      (c := .block (mgfArgs H))
      (Taint.isSome_check_of_eraseOff (c := .block (mgfArgs H)) (c' := Code.eraseOff (.block (mgfArgs zH')))
        (τ := Taint.ofRegs [.x20, .x24, .x25]) rfl (by taint_decide))).wpDep
      (F := F) fun s₁ s₂ hp => ?_).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  · obtain ⟨⟨s, h₁, rfl⟩, t, h₂, rfl⟩ := hp
    refine ⟨by simp only [allocated, h₁.L.sp, h₂.L.sp], fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    show s.gpr r = t.gpr r
    rcases hr with rfl | rfl | rfl
    · rw [h₁.L.x20, h₂.L.x20]
    · rw [h₁.x24, h₂.x24]
    · rw [h₁.x25, h₂.x25]
  · obtain ⟨⟨s, h₁, rfl⟩, t, h₂, rfl⟩ := hp
    exact ⟨WP.mono (setup_ok h₁.L h₁.hd h₁.x24 h₁.x25 h₁.env) fun u ⟨_, sy, _, L, R, T, _, A⟩ => ⟨s, h₁, rfl, sy, L, R, T, A⟩,
      WP.mono (setup_ok h₂.L h₂.hd h₂.x24 h₂.x25 h₂.env) fun u ⟨_, sy, _, L, R, T, _, A⟩ => ⟨t, h₂, rfl, sy, L, R, T, A⟩⟩
  refine (Proof.RsaOaep.AArch64.Table.mgfXorT_tr hG (F := mF a.F) (S := off a.S mgfOff) (p := a.p) (ai := a.ai)
    (au := a.au) (af := a.af) (sArg := mgfFrame + sMgfT) (by decide) hf
    (X := fun W u => Proof.RsaOaep.AArch64.MArgs W (off a.S mgfOff) (a.e + a.db - mgfOff) H.D (a.e - mgfOff) a.db ∧
      Proof.RsaOaep.AArch64.Table.Tab G g (mF a.F) (off a.S mgfOff) a.p (mgfFrame + sMgfT) u ∧
      u.syms G.initN = a.ai ∧ u.syms G.updN = a.au ∧ u.syms G.finN = a.af)
    (fun _ _ h => h) (by taint_decide)).mono (fun t₁ t₂ ⟨_, _, _, f₁, f₂⟩ => ?_) fun _ _ h => h
  obtain ⟨s₁, h₁, -, y₁, L₁, R₁, T₁, A₁⟩ := f₁
  obtain ⟨s₂, h₂, -, y₂, L₂, R₂, T₂, A₂⟩ := f₂
  exact ⟨⟨_, _, L₁, R₁, A₁, T₁, by rw [y₁, h₁.ai], by rw [y₁, h₁.au], by rw [y₁, h₁.af]⟩,
    ⟨_, _, L₂, R₂, A₂, T₂, by rw [y₂, h₂.ai], by rw [y₂, h₂.au], by rw [y₂, h₂.af]⟩⟩

end

end VG.Proof.RsaPss.AArch64
