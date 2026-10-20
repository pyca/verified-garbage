module
public import VerifiedGarbage.Impl.AesGcm.X86_64.SealSplit
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT

import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Body
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# AES-GCM `seal_split` on x86-64: the end, in two runs

Untrusted: everything here is checked by Lean. `FinRel` states what
constant time needs of the end of `seal_split`: two runs from states that
hold the same public slots of `W`, the total length `N` in its slot, leak the
same trace. `Short.finish_rel` proves it of `Short.finishWith`
(`finRel_finishWith`), `oneCrypt_rel` and `oneTag_rel` of
`SealSplit.finCalls` (`finRel_calls`). Before it, `oneBlocks` keeps the
total length kept at `auxO` (`oneBlocks_aux`), and `fixTlen` puts it back
(`fixTlen_oneS`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts KsOk KsRel FinI finish_rel)

/-- What constant time needs of the end `fin` of `seal_split`. -/
def FinRel (M : CtxMode) (fin : Prog isa) : Prop :=
  ∀ {Ctx W SP A D : Addr} {R al n N : Nat}, Lay Ctx (W + BitVec.ofNat 64 16) W SP → (R = 10 ∨ R = 12 ∨ R = 14) →
    n < 2 ^ 64 → (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩ →
    RelCT isa (OneS₂ M Ctx W SP R A al D n (some N)) fin fun _ _ => True

/-- The end without calls, with the keystream of `ks`. -/
theorem finRel_finishWith {M : CtxMode} (hF : ShortFacts) {ks : Prog isa} (hks : KsOk ks) (hkr : KsRel ks) :
    FinRel M (Short.finishWith ks) := by
  intro Ctx W SP A D R al n N _ hR hn _
  exact (finish_rel hF hks hkr (Ctx := Ctx) (W := W) (SP := SP) (D := D) hR hn).mono
    (fun _ _ g => ⟨⟨g.1.env, g.1.rounds.1, g.1.dat, g.1.len⟩, ⟨g.2.env, g.2.rounds.1, g.2.dat, g.2.len⟩⟩)
    fun _ _ g => g

/-- The end with calls: `oneCrypt` and `oneTag 0`. -/
theorem finRel_calls (v : GcmImpl) {M : CtxMode} : FinRel M (SealSplit.finCalls v.callees) := by
  intro Ctx W SP A D R al n N L _ _ hDW
  exact RelCT.seq (oneCrypt_rel v L hDW) (oneTag_rel v L (.inl rfl) hDW)

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) {M : CtxMode}
include L

/-- The total length put back, from `auxO`. -/
theorem fixTlen_oneS {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n N : Nat} {T : Option Nat} {s : State}
    (h : OneS M Ctx W SP R A al D n T s) (haux : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N) :
    WP isa (.block SealSplit.fixTlen) s (OneS M Ctx W SP R A al D n (some N)) := by
  refine WP.mono (fixTlen_ok h.env haux) fun s' ⟨m, g, rd, wr⟩ => ?_
  have sep : ∀ d, (d + 8 ≤ 192 ∨ 200 ≤ d) → d + 8 ≤ 2560 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    intro d hd hd'
    rw [m]
    exact Mem.readW_writeW_sep (Offset.sep W (by omega) (by have := L.ww; omega) (by have := L.ww; omega))
      (by decide)
  have fW : Frame [⟨W + BitVec.ofNat 64 192, 8⟩] s.mem s'.mem := by
    rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨h.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g _ (by decide)) rd wr,
    ⟨by rw [sep 176 (.inl (by decide)) (by decide)]; exact h.rounds.1, h.rounds.2⟩,
    by rw [sep 232 (.inr (by decide)) (by decide)]; exact h.aad,
    by rw [sep 184 (.inl (by decide)) (by decide)]; exact h.alen,
    by rw [sep 200 (.inr (by decide)) (by decide)]; exact h.dat,
    by rw [sep 208 (.inr (by decide)) (by decide)]; exact h.len,
    h.dA.of_eq rd wr, h.dD.of_eq rd wr, fun _ e => by cases e; rw [m, Mem.readW_writeW_self64],
    h.ext.keep rd wr fW fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact h.ext.cw.sub_right (Lay.wSub (by decide))⟩

/-- `oneBlocks`, keeping what is at `auxO`. -/
theorem oneBlocks_aux (B : BlkFn M) {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n N : Nat} {T : Option Nat}
    (t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩) (t_w : (below SP 24).Disjoint ⟨W, 2560⟩)
    (t_d : (below SP 24).Disjoint ⟨D, n⟩) (sp24 : 24 ≤ SP.toNat) {s : State}
    (h : OneS M Ctx W SP R A al D n T s) (haux : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N) :
    WP isa (oneBlocks B.enc) s fun s' =>
      OneS M Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s' ∧
      s'.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N := by
  have hD := h.dD.ok.w
  refine WP.mono (oneBlocks_core L B.enc (Out := fun _ _ => True) ⟨h.env, h.rounds, h.dat, h.len, h.dD, t_c, t_w, t_d, sp24,
    h.ext⟩ (fun s₂ hi => WP.mono (obFrameE_ok L B hi) fun _ o => ⟨o.1, o.2.1, o.2.2.1, o.2.2.2.1, trivial⟩)
    (fun _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)) fun s' ⟨P, _⟩ => ⟨ObPost.oneS L t_w h P, ?_⟩
  have d216 : ∀ r ∈ (⟨W + BitVec.ofNat 64 192, 24⟩ :: obFrame (W + BitVec.ofNat 64 16) W SP D (n / 16)),
      (⟨W + BitVec.ofNat 64 216, 8⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Offset.disjoint W (.inr (by decide)) (by have := L.ww; omega) (by have := L.ww; omega)
    · exact ob_slots L hD (by have := h.dD.ok.lt; omega) t_w (by decide) (by decide) r hr
  rw [P.frame.readW (Region.contains_self _ _) d216 (by decide), haux]

end

end VG.Proof.AesGcm.X86_64.Split
