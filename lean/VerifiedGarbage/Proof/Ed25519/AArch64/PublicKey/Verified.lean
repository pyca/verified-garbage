module

public import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.CTCommon
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X25519.AArch64.Ladder
meta import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.CTCommon
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X25519.AArch64.Ladder
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-! # Constant time of the public key's derivation after its first step (AArch64) -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.AArch64.PublicKey.CTReady`. -/
section
namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

def baseValues : List (Reg × Value) := [(.x0, .caller 0 0), (.x1, .frame 32), (.x2, .caller 2 0)]

variable {L : Lay} {t : State}

def base_ready (hL : L.Ok) (hsy : t.syms Impl.Ed25519.AArch64.combSym = L.T) (hm : TblWords L.T t.mem)
    (hs : Slots L baseValues t) :
    Whole.CallReady scalarBaseLocal L.E L.inputs L.outputs t := by
  have h0 := hs (.x0, .caller 0 0) (by decide)
  have h1 := hs (.x1, .frame 32) (by decide)
  have h2 := hs (.x2, .caller 2 0) (by decide)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  exact ⟨[⟨L.E + 32, 32⟩, L.TB], L.outputs, base_pre hL ⟨h0, h1, h2⟩ hsy hm, base_covers L, base_writes L⟩

end VG.Proof.Ed25519.AArch64.PublicKey
end

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey

variable {L : Lay} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem base_ct [VG.Proof.Ed25519.AArch64.Divstep.Sound] (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L baseValues))
    (.call "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase)
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb scalarBase_ok scalarBase_ct (Whole.depth_of_noFrames base_noFrames)
    (fun _ _ hy hm h => base_ready hL hy hm h)
  · intro a b ar aw br bw hsp hy hg
    exact ⟨hsp, hg (.x0, .caller 0 0) (by decide), hg (.x1, .frame 32) (by decide),
      hg (.x2, .caller 2 0) (by decide), hy⟩
  · simp [baseValues, linkRegs]

theorem prune_ct : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block prune)
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp (Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (by taint_decide)) ?_ ?_
  · intro t ⟨hc, hy, _⟩
    exact WP.mono_syms (prune_step hc (digest := Spec.Ed25519.bytesAt t.mem (L.E + 192) 64) rfl)
      fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩
  · intro t ⟨hc, hy, _⟩
    exact WP.mono_syms (prune_step hc (digest := Spec.Ed25519.bytesAt t.mem (L.E + 192) 64) rfl)
      fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩

theorem wipe_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block wipe)
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp (Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (by taint_decide)) ?_ ?_
  · intro t ⟨hc, hy, _⟩; exact WP.mono_syms (wipe_step hc hL) fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩
  · intro t ⟨hc, hy, _⟩; exact WP.mono_syms (wipe_step hc hL) fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩

/-- The public key after a first step related to itself, as the copy of a cached digest is. -/
theorem bodyFrom_ct [VG.Proof.Ed25519.AArch64.Divstep.Sound] {first : Prog isa}
    (hfirst : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) first
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True))
    (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (bodyFrom first)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have b := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb baseValues
    (by decide) (by simp [baseValues, Whole.valid]) (by simp [baseValues])
    (by decide) (by taint_decide)
  exact hfirst.seq (prune_ct.seq ((b.seq (base_ct hL ha hb)).seq (wipe_ct hL)))

theorem lay_eq {n : Nat} {post : State → State → Prop} {s t : State}
    (hp : (pkLocalWith n post).pub s t) : lay n s = lay n t := by
  obtain ⟨sp, h0, h1, h2, hsy⟩ := hp
  simp only [lay, Whole.base, sp, h0, h1, h2, hsy]

end VG.Proof.Ed25519.AArch64.PublicKey
end
