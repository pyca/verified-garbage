module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Setup
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH domain validation on x86-64: workspace preservation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem Work.keep {p : CdP} {mi : BitVec 64} {s t : State} {rs : List Reg}
    (h : Work p mi s) (hm : t.mem = s.mem) (k : Keep rs s t) : Work p mi t :=
  ⟨h.base.keep (by rw [hm]; exact InScr.refl _ _ _) k (fun _ _ => by rw [hm]), h.mem.congr hm k.2.2,
    ⟨by rw [hm]; exact h.xv.n, by rw [hm]; exact h.xv.inv, by rw [hm]; exact h.xv.one⟩,
    by rw [hm]; exact h.ws, by rw [hm]; exact h.g, by rw [hm]; exact h.q⟩

/-- Arithmetic changes that leave the modulus and one intact. -/
theorem Work.child {p : CdP} {mi : BitVec 64} {s t : State}
    {rs : List (Nat × Nat)} {regs : List Reg} (h : Work p mi s)
    (hd : s.gpr .rdi = off p.B (inner p.w)) (hf : Frm (off p.B (inner p.w)) rs s.mem t.mem)
    (hr : ∀ r ∈ rs, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot p.w 8)
    (hN : ∀ r ∈ rs, r.1 + r.2 ≤ slot p.w aN ∨ slot p.w aN + 8 * (p.w + 2) ≤ r.1)
    (hOne : ∀ r ∈ rs, r.1 + r.2 ≤ slot p.w aOne ∨ slot p.w aOne + 8 * (p.w + 2) ≤ r.1)
    (k : Keep regs s t) : Work p mi t ∧ InScr p.B p.Z s.mem t.mem ∧
      (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) := by
  have hc := h.mem.ctx hd
  have hk := h.base.k1
  have hZ := h.base.hZ
  have hw := room_k hk hZ
  change inner p.w + slot p.w 8 + tabBytes p.w 32 ≤ p.Z at hw
  have hn := hc.good.scr.nowrap
  have hwl : 1 ≤ p.w := by unfold CdP.w; omega
  obtain ⟨hb, hi, hs⟩ := h.base.child hc (L := slot p.w 8) (by omega) hf (fun r hr' => (hr r hr').2) k
  refine ⟨⟨hb, h.mem.of_child hf hr k.2.2, h.xv.of_frmA hn hwl hf (fun r hr' => ⟨hN r hr', hOne r hr'⟩),
    (hs _ (by decide)).trans h.ws, (hs _ (by decide)).trans h.g, (hs _ (by decide)).trans h.q⟩, hi, fun i hi => hs i (by omega)⟩

theorem Work.enter {p : CdP} {mi : BitVec 64} {s : State} (h : Work p mi s)
    (hd : s.gpr .rdi = p.B) : WP isa (.block [enter]) s fun t =>
      Work p mi t ∧ t.gpr .rdi = off p.B (inner p.w) ∧ t.mem = s.mem ∧ Keep [.rdi] s t := by
  have hb := h.base
  have hw := room_k hb.k1 hb.hZ
  have hk := hb.k1
  have hk' := hb.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  refine WP.mono (enter_ok (Outer.of_mem h.mem hd hw (by omega) (by omega)) h.ws)
    fun t ⟨hdi, hm, k⟩ => ⟨h.keep hm k, hdi, hm, k⟩

end VG.Proof.Ffdh.X86_64.CheckDomain
