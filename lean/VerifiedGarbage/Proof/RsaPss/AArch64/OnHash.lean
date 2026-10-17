module

public import VerifiedGarbage.Impl.RsaPss.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.Dispatch
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSASSA-PSS on AArch64: choosing the hash function

`onHash d hs f` loads the number `k` of a hash function from the slot `d`
into `x8` and runs `f H` for the `k`th of `hs`, `H`, through a dispatch
(`Dispatch.AArch64.chain`) that writes only `x9`: it runs as `f H` from a
state that differs only in `x8` and `x9` (`onHash_wp`), and two runs with the
same `k` are constant time if `f H` is (`onHash_two`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only wp_nil)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two two_taint two_post wp_ldrSp)
open VG.Proof.Dispatch (keys chain_wp chain_relCT)
open VG.Proof.Dispatch.AArch64 (WritesOnly sel tests)

theorem keys_byHash (f : Hash → Prog isa) :
    ∀ (i : Nat) (hs : List Hash), keys (byHash f i hs) = List.range' i hs.length
  | _, [] => rfl
  | i, _ :: hs => by
    simp only [byHash, keys, List.map_cons, List.length_cons, List.range'_succ]
    exact congrArg _ (keys_byHash f (i + 1) hs)

theorem mem_byHash {f : Hash → Prog isa} :
    ∀ {i : Nat} {hs : List Hash} {k : Nat} {c : Prog isa}, (k, c) ∈ byHash f i hs →
      ∃ H, hs[k - i]? = some H ∧ i ≤ k ∧ c = f H
  | _, [], _, _, h => absurd h List.not_mem_nil
  | i, H :: hs, k, c, h => by
    rcases List.mem_cons.mp h with e | e
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨H, by simp, Nat.le_refl _, rfl⟩
    · obtain ⟨H', h₁, h₂, rfl⟩ := mem_byHash e
      refine ⟨H', ?_, by omega, rfl⟩
      rw [show k - i = (k - (i + 1)) + 1 by omega]
      simpa using h₁

theorem writesOnly_only {t : Reg} {s s' : State} (h : WritesOnly t s s') : Only [t] s s' := by
  obtain ⟨v, rfl⟩ := h
  exact ⟨fun r hr => by simp only [State.write]; rw [ite_eq_right_iff.mpr (fun e => absurd e (by simpa using hr))], rfl, rfl, rfl, rfl,
    fun _ _ => rfl⟩

/-- The dispatch: `f H` runs, from a state differing only in `x8` and `x9`. -/
theorem onHash_wp {d : Nat} {hs : List Hash} {f : Hash → Prog isa} {k : Nat} {H : Hash}
    (hk : hs[k]? = some H) (hl : hs.length ≤ 4096) (hd : d % 8 = 0 ∧ d < 32768) {s : State} {Q : State → Prop}
    (hin : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 d) 8)
    (hsel : s.mem.readW (s.sp + BitVec.ofNat 64 d) 64 = BitVec.ofNat 64 k)
    (h : ∀ s', Only [.x8, .x9] s s' → WP isa (f H) s' Q) :
    WP isa (onHash d hs f) s Q := by
  have hkl : k < hs.length := by
    rcases Nat.lt_or_ge k hs.length with e | e
    · exact e
    · rw [List.getElem?_eq_none e] at hk; cases hk
  unfold onHash ld
  refine WP.seq (WP.mono (Q := fun u => Only [.x8] s u ∧ sel .x8 u = k)
    (wp_ldrSp hd hin fun u o e => wp_nil ⟨o, ?_⟩) fun u ⟨o, hu⟩ => ?_)
  · simp only [sel, e, hsel, BitVec.toNat_ofNat]; omega
  refine chain_wp (tests .x9 .x8 (by decide)) _ (fun k' hk' => ?_) ?_ ?_ fun c hc s' hw _ => ?_
  · rw [keys_byHash, List.mem_range'_1] at hk'; omega
  · rw [hu, keys_byHash, List.mem_range'_1]; omega
  · rw [keys_byHash]; exact List.nodup_range'
  · obtain ⟨H', h₁, -, rfl⟩ := mem_byHash hc
    rw [hu, Nat.sub_zero, hk] at h₁
    cases h₁
    exact h _ ((o.trans (writesOnly_only hw)).mono)

/-- Two runs of the dispatch, with the same hash function: constant time if
the hash function's code is, from states that differ from the runs' only
in `x8` and `x9`. -/
theorem onHash_two {α : Type} {Φ : α → State → Prop} {d : Nat} {hs : List Hash} {f : Hash → Prog isa}
    {Q : State → State → Prop} (hl : hs.length ≤ 4096) (hd : d % 8 = 0 ∧ d < 32768) (k : α → Nat)
    (hΦ : ∀ a s, Φ a s → InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 d) 8 ∧
      s.mem.readW (s.sp + BitVec.ofNat 64 d) 64 = BitVec.ofNat 64 (k a) ∧ k a < hs.length)
    (hsp : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → s₁.sp = s₂.sp) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (VG.AArch64.Taint.ofRegs []) (.block [ld .x8 d]) hc).isSome = true)
    (h : ∀ a H, hs[k a]? = some H → RelCT isa (fun s₁ s₂ => ∃ s₁₀ s₂₀, Φ a s₁₀ ∧ Φ a s₂₀ ∧
      Only [.x8, .x9] s₁₀ s₁ ∧ Only [.x8, .x9] s₂₀ s₂) (f H) Q) :
    RelCT isa (Two Φ) (onHash d hs f) Q := by
  unfold onHash ld
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ u₀, Φ a u₀ ∧ Only [.x8] u₀ u ∧ sel .x8 u = k a)
    (two_taint [] (fun a s₁ s₂ h₁ h₂ => ⟨hsp a s₁ s₂ h₁ h₂, fun _ h => absurd h List.not_mem_nil⟩)
      ht) fun a s hs' => ?_) ?_
  · obtain ⟨hin, hsel, hkl⟩ := hΦ a s hs'
    refine wp_ldrSp hd hin fun u o e => wp_nil ⟨s, hs', o, ?_⟩
    simp only [sel, e, hsel, BitVec.toNat_ofNat]; omega
  refine chain_relCT (tests .x9 .x8 (by decide)) (fun k' hk' => ?_) (by rw [keys_byHash]; exact List.nodup_range')
    (fun s₁ s₂ ⟨a, ⟨u₁, h₁, o₁, e₁⟩, ⟨u₂, h₂, o₂, e₂⟩⟩ => ⟨by rw [e₁, e₂], ?_⟩) fun k' c hc => ?_
  · rw [keys_byHash, List.mem_range'_1] at hk'; omega
  · rw [e₁, keys_byHash, List.mem_range'_1]; exact ⟨Nat.zero_le _, by have := (hΦ a u₁ h₁).2.2; omega⟩
  obtain ⟨H, hH, -, rfl⟩ := mem_byHash hc
  rw [Nat.sub_zero] at hH
  rintro s₁ s₂ t₁ t₂ s₁' s₂' ⟨b₁, b₂, ⟨a, ⟨u₁, h₁, o₁, e₁⟩, ⟨u₂, h₂, o₂, e₂⟩⟩, hk, w₁, w₂, -, -⟩ x₁ x₂
  rw [e₁] at hk
  subst hk
  exact h a H hH _ _ _ _ _ _ ⟨u₁, u₂, h₁, h₂, (o₁.trans (writesOnly_only w₁)).mono, (o₂.trans (writesOnly_only w₂)).mono⟩ x₁ x₂

end VG.Proof.RsaPss.AArch64
