module

public import VerifiedGarbage.Impl.RsaPss.X86_64.AnyHash
public import VerifiedGarbage.Proof.Framework.X86_64.Dispatch
public import VerifiedGarbage.Proof.RsaPss.X86_64.Basic
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSASSA-PSS on x86-64 with the hash functions as arguments: the dispatches

`dispatch d f hs` loads the selector in the slot `d` and runs `f` of the
hash function it names, by `Dispatch.X86_64.chain` on `cases f hs`, whose
keys are `0, …, hs.length - 1` (`cases_keys`). With the selector `k`, it runs
`f hs[k]` from a state that differs from the one before only in `rax` (the
selector) and the flags (`dispatch_ok`), and two runs with the same
selector are constant time if `f hs[k]` is (`dispatch_relCT`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG VG.X86_64 VG.Impl.RsaPss.X86_64 VG.Impl.RsaPss.X86_64.AnyHash
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off)
open VG.Proof.Dispatch.X86_64 (FlagsOnly)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

theorem cases_keys (f : Hash → Prog isa) (hs : List Hash) :
    Proof.Dispatch.keys (cases f hs) = List.range hs.length := by
  apply List.ext_getElem (by simp [Proof.Dispatch.keys, cases])
  intro i h₁ h₂
  simp [Proof.Dispatch.keys, cases]

theorem mem_cases {f : Hash → Prog isa} {hs : List Hash} {k : Nat} {c : Prog isa}
    (h : (k, c) ∈ cases f hs) : ∃ hk : k < hs.length, c = f hs[k] := by
  simp only [cases, List.mem_mapIdx, Prod.mk.injEq] at h
  obtain ⟨i, hi, rfl, rfl⟩ := h
  exact ⟨hi, rfl⟩

theorem keys_bound {f : Hash → Prog isa} {hs : List Hash} (hl : hs.length ≤ 2 ^ 31) :
    ∀ k ∈ Proof.Dispatch.keys (cases f hs), k < 2 ^ 31 := fun k hk => by
  rw [cases_keys, List.mem_range] at hk; omega

theorem keys_nodup (f : Hash → Prog isa) (hs : List Hash) : (Proof.Dispatch.keys (cases f hs)).Nodup := by
  rw [cases_keys]; exact List.nodup_range

/-- The chain on `rax`, the selector `k`. -/
theorem chain_ok {f : Hash → Prog isa} {hs : List Hash} {s : State} {Q : State → Prop} {k : Nat}
    (hl : hs.length ≤ 2 ^ 31) (hk : k < hs.length) (hax : s.gpr .rax = BitVec.ofNat 64 k)
    (h : ∀ s', FlagsOnly s s' → WP isa (f hs[k]) s' Q) :
    WP isa (Impl.Dispatch.X86_64.chain (cases f hs)) s Q := by
  have hsel : Proof.Dispatch.X86_64.sel s = k := by
    rw [Proof.Dispatch.X86_64.sel, hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine Proof.Dispatch.chain_wp Proof.Dispatch.X86_64.tests (cases f hs) (keys_bound hl)
    (by rw [hsel, cases_keys, List.mem_range]; exact hk) (keys_nodup f hs) fun c hc s' hr _ => ?_
  rw [hsel] at hc
  obtain ⟨_, rfl⟩ := mem_cases hc
  exact h s' hr

/-- The dispatch on the selector `k` in the slot `d = 8 j` of the frame. -/
theorem dispatch_ok {f : Hash → Prog isa} {hs : List Hash} {u : State} {F S : Addr} {V : Nat → Byte}
    {W : Nat → BitVec 64} (L : Lay u F S) (R : Rep u.mem F S V W) {d j k : Nat} (hd : d = 8 * j) (hj : j < nW)
    (hW : W j = BitVec.ofNat 64 k) (hl : hs.length ≤ 2 ^ 31) (hk : k < hs.length) {Q : State → Prop}
    (h : ∀ v, Keep [.rax] u v → v.mem = u.mem → v.gpr .rax = BitVec.ofNat 64 k → WP isa (f hs[k]) v Q) :
    WP isa (dispatch d f hs) u Q := by
  have hrd : u.mem.readW (off F d) 64 = BitVec.ofNat 64 k := by rw [R.rd j hd hj, hW]
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun v => v.gpr .rax = BitVec.ofNat 64 k ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨hax, hm⟩, kv⟩ => chain_ok hl hk hax fun v' hf => ?_)
  · xrun [ea_sp, L.rsp, L.ld (d := d) (by subst hd; unfold nW at hj; omega), hrd]
  · refine h v' ⟨fun r hr => (hf.gpr r).trans (kv.gpr hr), hf.rd.trans kv.2.1, hf.wr.trans kv.2.2⟩
      (hf.mem.trans hm) ((hf.gpr .rax).trans hax)

open VG.Proof.Bignum.X86_64 (Two two_post)

/-- Two runs of the dispatch with the same selector `k`, loaded by a block
`hload` checks and after which `Ψ` holds, are constant time if `f hs[k]` is
from states differing from those only in the flags. -/
theorem dispatch_relCT {α : Type} {Φ Ψ : α → State → Prop} {d : Nat} {f : Hash → Prog isa} {hs : List Hash}
    {k : Nat} (hk : k < hs.length) (hl : hs.length ≤ 2 ^ 31)
    (hload : RelCT isa (Two Φ) (.block [.mov .rax (.mem (sp d))]) fun _ _ => True)
    (hw : ∀ a s, Φ a s → WP isa (.block [.mov .rax (.mem (sp d))]) s fun s' => Ψ a s' ∧
      s'.gpr .rax = BitVec.ofNat 64 k)
    {Q : State → State → Prop} (hcase : RelCT isa (Two fun a s => ∃ s₀, Ψ a s₀ ∧ FlagsOnly s₀ s) (f hs[k]) Q) :
    RelCT isa (Two Φ) (dispatch d f hs) Q := by
  have hsel : ∀ s : State, s.gpr .rax = BitVec.ofNat 64 k → Proof.Dispatch.X86_64.sel s = k := fun s h => by
    rw [Proof.Dispatch.X86_64.sel, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine RelCT.seq (two_post (Ψ := fun a s => Ψ a s ∧ s.gpr .rax = BitVec.ofNat 64 k) hload hw) ?_
  refine Proof.Dispatch.chain_relCT Proof.Dispatch.X86_64.tests (keys_bound hl) (keys_nodup f hs)
    (fun s₁ s₂ ⟨a, h₁, h₂⟩ => ⟨by rw [hsel _ h₁.2, hsel _ h₂.2], by
      rw [hsel _ h₁.2, cases_keys, List.mem_range]; exact hk⟩) fun k' c hc => ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨a₁, a₂, ⟨a, h₁, h₂⟩, hk₁, r₁, r₂, _, _⟩ e₁ e₂
  rw [hsel _ h₁.2] at hk₁
  subst hk₁
  obtain ⟨_, rfl⟩ := mem_cases hc
  exact hcase _ _ _ _ _ _ ⟨a, ⟨a₁, h₁.1, r₁⟩, ⟨a₂, h₂.1, r₂⟩⟩ e₁ e₂

end VG.Proof.RsaPss.X86_64.Any
