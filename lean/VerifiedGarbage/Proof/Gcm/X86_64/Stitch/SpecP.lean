import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Spec
import VerifiedGarbage.Spec.Gcm.Precomputed
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32

/-!
# Interleaved loops with the powers of the hash subkey in the key context

Untrusted: everything here is checked by Lean. `SPreP s₀`: `SPre s₀`, and the
key context, of 1024 bytes, holds the powers of its hash subkey
(`Spec.Gcm.PowersRepr`), apart from the data and the working space, which the
loops write. `StitchOkP` is `StitchOk` from it: loops that read the powers
instead of computing them.

`CtxMode` names the two kinds of key context the callers pass: the 256 bytes
of `vg_aes_gcm_init` (`base`), and the 1024 bytes with the powers
(`powers`): its length, and what it holds beyond `KeyRepr` (`ok`), which
writes elsewhere keep (`frame`). `SPreM` and `StitchOkM` are `SPre` and
`StitchOk` for either: any loops meet `StitchOkM` for any mode
(`StitchOk.toM`), and those that read the powers for `powers`
(`StitchOkP.toM`).
-/

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64

/-- The key context with its powers: 1024 bytes. -/
abbrev kPR (s₀ : State) : Region := ⟨kp s₀, 1024⟩

structure SPreP (s₀ : State) : Prop where
  base : SPre s₀
  k_in : InRegions (s₀.rd ++ s₀.wr) (kp s₀) 1024
  wrap_k : (kp s₀).toNat + 1024 ≤ 2 ^ 64
  d_k : (dR s₀).Disjoint (kPR s₀)
  p_k : (pR s₀).Disjoint (kPR s₀)
  pow : Spec.Gcm.PowersRepr s₀.mem (kp s₀)

/-- Interleaved loops `enc` and `dec` that read the powers meet the contracts. -/
def StitchOkP (enc dec : Prog isa) : Prop :=
  (∀ s₀, SPreP s₀ → WP isa enc s₀ (EPost s₀)) ∧ (∀ s₀, SPreP s₀ → WP isa dec s₀ (DPost s₀))

/-! ## Both kinds of key context -/

/-- A kind of key context: its length and what it holds beyond `KeyRepr`. -/
structure CtxMode where
  len : Nat
  ok : Mem → Addr → Prop
  ge : 256 ≤ len
  le : len ≤ 1024
  frame : ∀ {rs : List Region} {m m' : Mem} {p : Addr}, Frame rs m m' →
    (∀ r ∈ rs, (⟨p, len⟩ : Region).Disjoint r) → p.toNat + len ≤ 2 ^ 64 → ok m p → ok m' p

/-- The key context of `vg_aes_gcm_init`. -/
def CtxMode.base : CtxMode where
  len := 256
  ok _ _ := True
  ge := Nat.le_refl _
  le := by decide
  frame _ _ _ _ := trivial

/-- The key context of `vg_aes_gcm_init_precomputed`, with the powers. -/
def CtxMode.powers : CtxMode where
  len := 1024
  ok m p := Spec.Gcm.PowersRepr m p
  ge := by decide
  le := Nat.le_refl _
  frame {rs m m' p} hf hd hw h := by
    have kb : ∀ o, o + 16 ≤ 1024 → Spec.Gcm.blockAt m' (p + BitVec.ofNat 64 o) = Spec.Gcm.blockAt m (p + BitVec.ofNat 64 o) :=
      fun o ho => VG.Proof.Aes.X86_64.AesNi.blockAt_frame hf fun r hr =>
        (hd r hr).sub_left (Offset.sub_base _ ho)
    have hH : Spec.Gcm.ctxH m' p = Spec.Gcm.ctxH m p := kb 240 (by decide)
    intro k hk
    rw [kb _ (by omega), h k hk, hH]

/-- The key context of `m` as a region. -/
abbrev kMR (M : CtxMode) (s₀ : State) : Region := ⟨kp s₀, M.len⟩

/-- `SPre`, for a key context of kind `M`. -/
structure SPreM (M : CtxMode) (s₀ : State) : Prop where
  base : SPre s₀
  k_in : InRegions (s₀.rd ++ s₀.wr) (kp s₀) M.len
  wrap_k : (kp s₀).toNat + M.len ≤ 2 ^ 64
  d_k : (dR s₀).Disjoint (kMR M s₀)
  p_k : (pR s₀).Disjoint (kMR M s₀)
  ok : M.ok s₀.mem (kp s₀)

/-- `StitchOk`, for a key context of kind `M`. -/
def StitchOkM (M : CtxMode) (enc dec : Prog isa) : Prop :=
  (∀ s₀, SPreM M s₀ → WP isa enc s₀ (EPost s₀)) ∧ (∀ s₀, SPreM M s₀ → WP isa dec s₀ (DPost s₀))

theorem StitchOk.toM {enc dec : Prog isa} (h : StitchOk enc dec) (M : CtxMode) : StitchOkM M enc dec :=
  ⟨fun s₀ hp => h.1 s₀ hp.base, fun s₀ hp => h.2 s₀ hp.base⟩

theorem SPreM.toP {s₀ : State} (h : SPreM CtxMode.powers s₀) : SPreP s₀ :=
  ⟨h.base, h.k_in, h.wrap_k, h.d_k, h.p_k, h.ok⟩

theorem StitchOkP.toM {enc dec : Prog isa} (h : StitchOkP enc dec) : StitchOkM CtxMode.powers enc dec :=
  ⟨fun s₀ hp => h.1 s₀ hp.toP, fun s₀ hp => h.2 s₀ hp.toP⟩

end VG.Proof.Gcm.X86_64.Stitch
