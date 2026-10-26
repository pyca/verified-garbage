module

public import VerifiedGarbage.Proof.Rsa.Arm.RvKS
import VerifiedGarbage.Proof.Rsa.KeyViews
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Basic.IsEmpty.Defs
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # `vg_rsa_recover_primes` on ARMv7: the operations on a stage

The operations of the key working space (`Impl/Rsa/Arm/KeyWs.lean`), with
`w` words (`_w`) or `W` words (`_W`), from a stage `KS` to the next, the
value they write recorded in its arrays or header words.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys

/-- The arrays after a step that writes `[o] := x` alone. -/
theorem Arrs.upd1 {m m' : Mem} {B : BitVec 32} {v : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B v A live) {o x : Nat} {ds : List Nat} (k : Keep B v [o] ds m m')
    (hd : ∀ d ∈ ds, d + 4 ≤ hdr) (fit : ∀ j ∈ live, arr v j + S v ≤ 2 ^ 64)
    (e : num m' B v o = x) : Arrs m' B v (upd A o x) (o :: live) :=
  VG.Proof.Rsa.KeyWorkspace.Arrs.upd1 h k hd fit e

end VG.Proof.Rsa.Arm.Keys

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

section
variable {P : RP} {σ s t : State} {A : Nat → Nat} {live : List Nat} {AW : Nat → Nat} {liveW : List Nat}
  {V : Nat → Nat} {ls : List Nat}

/-- A step with `w` words that writes `[o] := x` alone, and header words `ds`. -/
theorem KS.write_w {o x : Nat} {ds : List Nat} (h : KS P σ A live AW liveW V ls s)
    (k : Keep P.B P.w [o] ds s.mem t.mem) (ho : o < nArr) (hds : ∀ d ∈ ds, SlotOk d)
    (r8 : t.gpr .r8 = P.B) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (e : num t.mem P.B P.w o = x) (hlW : ∀ j ∈ liveW, o / 2 ≠ j)
    (hls : ∀ d ∈ ls, ∀ e ∈ ds, d + 4 ≤ e ∨ e + 4 ≤ d) : KS P σ (upd A o x) (o :: live) AW liveW V ls t :=
  h.core k (by simpa using fitZ_w h.sizes ho) hds r8 sp rd wr
    (h.arrs.upd1 k (fun d hd => (hds d hd).1) (fun j hj => fit_w h.sizes (h.live_lt j hj)) e)
    (fun j hj => (List.mem_cons.mp hj).elim (fun e => e ▸ ho) (h.live_lt j))
    (h.arrsW_w k (fun j hj i hi => by simp at hi; subst hi; exact hlW j hj) hds) h.liveW_lt
    (h.sl_keep k hls) h.ls_ok

/-- A step with `W` words that writes `[o] := x` alone, and header words `ds`. -/
theorem KS.write_W {o x : Nat} {ds : List Nat} (h : KS P σ A live AW liveW V ls s)
    (k : Keep P.B P.W [o] ds s.mem t.mem) (ho : o < 22) (hds : ∀ d ∈ ds, SlotOk d)
    (r8 : t.gpr .r8 = P.B) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (e : num t.mem P.B P.W o = x) (hl : ∀ j ∈ live, j / 2 ≠ o)
    (hls : ∀ d ∈ ls, ∀ e ∈ ds, d + 4 ≤ e ∨ e + 4 ≤ d) : KS P σ A live (upd AW o x) (o :: liveW) V ls t :=
  h.core k (by simpa using fitZ_W h.sizes ho) hds r8 sp rd wr
    (h.arrs_W k (fun j hj i hi => by simp at hi; subst hi; exact hl j hj) hds) h.live_lt
    (h.arrsW.upd1 k (fun d hd => (hds d hd).1) (fun j hj => fit_W h.sizes (h.liveW_lt j hj)) e)
    (fun j hj => (List.mem_cons.mp hj).elim (fun e => e ▸ ho) (h.liveW_lt j))
    (h.sl_keep k hls) h.ls_ok

/-- A step that writes the header word `d := x` alone. -/
theorem KS.slot1 {d x v : Nat} (h : KS P σ A live AW liveW V ls s) (k : Keep P.B v [] [d] s.mem t.mem)
    (hd : SlotOk d) (r8 : t.gpr .r8 = P.B) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (e : slot t.mem P.B d = x) : KS P σ A live AW liveW (upd V d x) (d :: ls) t := by
  have kw : Keep P.B P.w [] [d] s.mem t.mem := fun y hy => k y fun r hr => hy r (by simpa [ranges] using hr)
  refine h.core kw (by simp) (by simpa using hd) r8 sp rd wr (h.arrs_w kw (by simp) (by simpa using hd))
    h.live_lt (h.arrsW_w kw (by simp) (by simpa using hd)) h.liveW_lt (fun d' hd' => ?_) (fun d' hd' => ?_)
  · by_cases e' : d' = d
    · subst e'; rw [upd_self]; exact e
    · have hd'' := (List.mem_cons.mp hd').resolve_left e'
      have a1 := h.ls_ok d' hd''
      rw [upd_ne _ _ e', kw.slot a1.1 (fun e he => by
        simp only [List.mem_singleton] at he
        rw [he]; have := a1.2.2; have := hd.2.2; omega), h.sl d' hd'']
  · rcases List.mem_cons.mp hd' with rfl | hd''
    · exact hd
    · exact h.ls_ok d' hd''

end

end VG.Proof.Rsa.Arm.Recover
