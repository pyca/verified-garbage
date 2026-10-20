module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.CutSetup
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Cut
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Contract

/-! # FFDH on x86-64: preserve domain and initialized y while sampling x -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Cutting x preserves all other inputs and every scratch word. -/
theorem Inputs.cut_keep {p : GkP} {rb : List Byte} {s t : State} (h : Inputs p rb s)
    (hc : CutInv s p.rp p.xp rb p.ld p.msk rb.length t) :
    Inputs p rb t ∧ Src t p.B p.Z p.xp (p.cut rb) ∧
      (∀ d, d + 8 ≤ p.Z → word t.mem p.B d = word s.mem p.B d) := by
  have ho : VG.Proof.Rsa.X86_64.OutOk s p.B p.Z p.xp rb.length := by rw [h.base.rl]; exact h.base.x
  have hout := hc.outside ho
  have hh : ∀ d, d + 8 ≤ p.Z → word t.mem p.B d = word s.mem p.B d :=
    fun d hd => hout.word (Or.inl hd) (by have := h.base.scr.nowrap; omega)
  have hg : Src t p.B p.Z p.dp p.dom := hc.src_keep h.base.dom (by
    rw [h.base.rl, h.base.doml]; exact h.base.xd)
  have hr : Src t p.B p.Z p.rp rb := hc.src_keep h.base.rand (by
    rw [h.base.rl]; exact h.base.xr)
  have hy : Src t p.B p.Z p.yp (List.replicate p.k 0) := hc.src_keep h.y (by
    rw [h.base.rl, List.length_replicate]; exact h.base.xy)
  have hZ := h.base.hZ
  have hbase : Base p rb t := by
    refine ⟨h.base.k1, h.base.k2, h.base.dl, h.base.doml, h.base.rl, h.base.hZ,
      h.base.scr.congr hc.keep.2.2, hg, hr,
      ⟨fun i hi => by rw [hc.keep.2.2]; exact h.base.x.wr i hi, h.base.x.sep⟩,
      ⟨fun i hi => by rw [hc.keep.2.2]; exact h.base.y.wr i hi, h.base.y.sep⟩,
      h.base.xy, h.base.xd, h.base.xr, h.base.yd, h.base.yr, ?_, h.base.valid⟩
    intro e he
    rw [hh _ (by
      simp only [GkP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [sDom, sDomLen, sK, sY, sX, sRand, sFn] <;> omega)]
    exact h.base.hdr e he
  refine ⟨⟨hbase, (hc.keep.gpr (by decide)).trans h.rdi, hy, ?_, ?_⟩,
    hc.src (by rw [h.base.rl]; exact h.base.ld_lt) ho, hh⟩
  · rw [hh _ (by change 224 ≤ p.Z; omega)]; exact h.g
  · rw [hh _ (by change 232 ≤ p.Z; omega)]; exact h.q

/-- The full cut loop, ready to select the public exponent slice. -/
theorem cut_inputs {p : GkP} {rb : List Byte} {s : State} (h : Inputs p rb s) (hr : CutRegs p s) :
    WP isa (.loop (.block cutBody) .ne) s fun t =>
      Inputs p rb t ∧ Src t p.B p.Z p.xp (p.cut rb) ∧
      (∀ d, d + 8 ≤ p.Z → word t.mem p.B d = word s.mem p.B d) ∧
      t.gpr .r8 = BitVec.ofNat 64 p.ld ∧ RunFrame p s.mem t.mem ∧ Keep [.rax, .rdx, .rbx, .r10, .r11, .rcx, .r14] s t := by
  obtain ⟨hrp, hxp, hm, hld, hcx, h14⟩ := hr
  have hk := h.base.k1
  have hk' := h.base.k2
  refine WP.mono (cut_ok (rb := rb) (by rw [h.base.rl]; omega) (by rw [h.base.rl]; omega)
    (by rw [h.base.rl]; exact h.base.ld_lt) hrp hxp hcx hld hm (by rw [h.base.rl]; exact h14)
    h.base.rand.rd (fun i hi => h.base.x.wr i (by rwa [h.base.rl] at hi))
    (fun i hi => by simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some] using h.base.rand.val i hi)
    (fun i hi j hj => Ne.symm (h.base.xr j (by rwa [h.base.rl] at hj) i (by rwa [h.base.rl] at hi))))
    fun t hc => ?_
  obtain ⟨ht, hx, hh⟩ := h.cut_keep hc
  refine ⟨ht, hx, hh, (hc.keep.gpr (by decide)).trans hld, ?_, hc.keep⟩
  exact RunFrame.of_x (fun a hx => hc.frame a (fun i hi => hx i (by rwa [h.base.rl] at hi)))

end VG.Proof.Ffdh.X86_64.GenerateKey
