module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.HalveStep

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Rsa.X86.DivCount
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
/-! # Preparing and running the complete native common-halving schedule -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/TwosBody.lean`, which only this module imported.
section

/-! # One public iteration of the native RSA LCM halving schedule -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (kFlag aU aV aPhi aPm aQm aHalf)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

structure HalveLoop (s₀ : State) (B : Addr) (Z n i : Nat) (s : State) : Prop where
  workspace : Ws s B Z n 32
  frame : Keep B n halveArrays [kFlag] s₀.mem s.mem
  rest : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s₀ s
  counter : s.gpr .esi = BitVec.ofNat 32 (32 * n - i)
  value : triple s.mem B n = VG.Proof.RsaKeyGen.halveIter i (triple s₀.mem B n)

theorem twoStep_ok {s₀ s : State} {B : Addr} {Z n i : Nat}
    (H : HalveLoop s₀ B Z n i s) (index : i < 32 * n) :
    WP isa twoStep s fun t => HalveLoop s₀ B Z n (i + 1) t ∧
      t.zf = some (decide (i + 1 = 32 * n)) := by
  have bound : 32 * n < 2 ^ 32 := by have := H.workspace.old.wle; omega
  unfold twoStep
  refine WP.seq (WP.mono (halveStep_ok H.workspace) fun u ⟨hu, Ou, value, Ku⟩ => ?_)
  refine WP.mono (VG.Proof.Rsa.X86.Div.count_ok u) fun t ⟨counter, Zf, memory, Kt⟩ => ?_
  have before : u.gpr .esi = s.gpr .esi := Ku.1 _ (by decide)
  rw [H.value, ← VG.Proof.RsaKeyGen.halveIter_succ'] at value
  refine ⟨⟨hu.keep Kt (by rw [memory]; exact Outside.refl _ _ _ _), ?_, H.rest.trans ((Ku.mono (by decide)).widen Kt), ?_, ?_⟩, ?_⟩
  · rw [memory]
    exact H.frame.trans Ou
  · rw [counter, before, H.counter]
    change BitVec.ofNat 32 (32 * n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · rw [memory]
    exact value
  · rw [Zf, before, H.counter]
    change some (BitVec.ofNat 32 (32 * n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show 32 * n - i - 1 = 0 ↔ i + 1 = 32 * n by omega]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/TwosLoop.lean`, which only this module imported.
section

/-! # The complete fixed schedule matches the shared LCM arithmetic -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (kFlag aU aV aPhi aPm aQm aHalf)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem twos_loop {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (counter : s.gpr .esi = BitVec.ofNat 32 (32 * n)) :
    WP isa (.loop twoStep .ne) s fun t => HalveLoop s B Z n (32 * n) t := by
  have positive : 0 < 32 * n := by have := h.wpos; omega
  have initial : HalveLoop s B Z n 0 s :=
    ⟨h, VG.Proof.Rsa.X86.Keys.Keep.refl B n halveArrays [kFlag] s.mem, Keeps.refl .., by simpa only [Nat.sub_zero] using counter, rfl⟩
  refine WP.loop (M := isa)
    (fun remaining t => ∃ i, remaining = 32 * n - i ∧ i < 32 * n ∧ HalveLoop s B Z n i t)
    ?_ (32 * n) s ⟨0, by omega, positive, initial⟩
  rintro remaining t ⟨i, rfl, index, H⟩
  refine WP.mono (twoStep_ok H index) fun u ⟨next, Zf⟩ => ?_
  by_cases last : i + 1 = 32 * n
  · exact .inl ⟨by simp only [eval, Zf, last, decide_true, Option.map_some, Bool.not_true], last ▸ next⟩
  · exact .inr ⟨by simp only [eval, Zf, decide_eq_false last, Option.map_some, Bool.not_false],
      32 * n - (i + 1), by omega, i + 1, rfl, by omega, next⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (kFlag aU aV aPhi aPm aQm aHalf)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem twos_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa twos s fun t =>
      Ws t B Z n 32 ∧ Keep B n halveArrays [kFlag] s.mem t.mem ∧
      triple t.mem B n = VG.Proof.RsaKeyGen.halveIter (32 * n)
        (num s.mem B n aPm, num s.mem B n aQm, num s.mem B n aPhi) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have fu := h.fit64 (j := aU) (by decide)
  have fq := h.fit64 (j := aQm) (by decide)
  have ff := h.fit64 (j := aPhi) (by decide)
  unfold twos VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (WP.mono (copy_ok h (by decide) (by decide) (by decide)) fun u ⟨hu, Ou, copiedU, Ku, _⟩ => ?_)
  refine WP.seq (WP.mono (copy_ok hu (by decide) (by decide) (by decide)) fun v ⟨hv, Ov, copiedV, Kv, _⟩ => ?_)
  refine WP.seq (VG.Proof.Rsa.X86.KeyRt.bits_ok hv.full fun w Kw mw count => WP.block_nil ?_)
  rw [kw_full hv.width] at count
  have hw := hv.keep Kw (by rw [mw]; exact Outside.refl _ _ _ _)
  refine WP.mono (twos_loop hw count) fun t H => ?_
  have valueW : triple w.mem B n =
      (num s.mem B n aPm, num s.mem B n aQm, num s.mem B n aPhi) := by
    unfold triple
    rw [mw, Ov.num (j := aU) (by decide) (by simp) fu, copiedU, copiedV,
      Ou.num (j := aQm) (by decide) (by simp) fq,
      Ov.num (j := aPhi) (by decide) (by simp) ff,
      Ou.num (j := aPhi) (by decide) (by simp) ff]
  have frame : Keep B n halveArrays [kFlag] v.mem t.mem := by
    have F := H.frame
    rw [mw] at F
    exact F
  refine ⟨H.workspace, ?_, ?_, ?_⟩
  · exact ((Ou.join Ov (js := halveArrays) (ds := [kFlag])
      (by simp [halveArrays]) (by simp) (by simp [halveArrays]) (by simp))).trans frame
  · rw [H.value, valueW]
  · exact (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans
      ((Kw.mono (by decide)).trans H.rest))

end VG.Proof.RsaKeyGen.X86.KeyRuntime
