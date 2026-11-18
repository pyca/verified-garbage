module

public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Scalar
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Rsa.X86.DivCount
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEven
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain

/-! ### `RsaKeyGen.X86.KeyRuntime.Twos`, which the modules that import this one used -/

section

/-! ### `RsaKeyGen.X86.KeyRuntime.HalveStep`, which this module and modules that import it used -/

section

/-! # A native step of the shared LCM halving algorithm -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Even.lean`, which only this module imported.
section

/-! # Common parity at a public runtime width -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep slot)
open VG.Impl.RsaKeyGen.X86.Key (aU aV kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem bothEven_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (.block bothEven) s fun t => Ws t B Z n 32 ∧ Keep B n [] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag =
        (if num s.mem B n aU % 2 = 0 ∧ num s.mem B n aV % 2 = 0 then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx] s t := by
  obtain fu := h.arr_fit (j := aU) (by decide)
  obtain fv := h.arr_fit (j := aV) (by decide)
  have nowrap := h.old.workspace.nowrap
  unfold bothEven
  refine h.ptr_ok (arr aU) (by decide) (by decide)
    (by simp only [arr, offset_array, Width.words]; unfold VG.Proof.Rsa.X86.Keys.S at fu; omega)
    fun u Ku mu Pu => ?_
  obtain hu := h.keep Ku (by rw [mu]; exact Outside.refl _ _ _ _)
  refine wp_movS (VG.Proof.Mont.X86.Rt.readSrc_ptr hu.full.rt Pu (d := 0)
    (by simp only [arr, offset_array, Width.words]; unfold VG.Proof.Rsa.X86.Keys.S at fu; omega))
    fun v V _ => ?_
  obtain Kv : Keeps [.eax, .ecx, .edx] s v := (Ku.mono (by decide)).trans (V.keeps.mono (by decide))
  obtain mv : v.mem = s.mem := V.mem.trans mu
  obtain hv := h.keep Kv (by rw [mv]; exact Outside.refl _ _ _ _)
  refine hv.ptr_ok (arr aV) (by decide) (by decide)
    (by simp only [arr, offset_array, Width.words]; unfold VG.Proof.Rsa.X86.Keys.S at fv; omega)
    fun w Kw mw Pw => ?_
  obtain hw := hv.keep Kw (by rw [mw]; exact Outside.refl _ _ _ _)
  refine wp_orS (VG.Proof.Mont.X86.Rt.readSrc_ptr hw.full.rt Pw (d := 0)
    (by simp only [arr, offset_array, Width.words]; unfold VG.Proof.Rsa.X86.Keys.S at fv; omega))
    fun x X => ?_
  refine wp_logicS (.inl rfl) rfl fun y Y => wp_logicS (.inr rfl) rfl fun z Zf => ?_
  obtain K : Keeps [.eax, .ecx, .edx] s z := (Kv.trans (Kw.mono (by decide))).trans
    ((X.keeps.mono (by decide)).trans ((Y.keeps.mono (by decide)).trans (Zf.keeps.mono (by decide))))
  obtain memory : z.mem = s.mem := Zf.mem.trans (Y.mem.trans (X.mem.trans (mw.trans mv)))
  obtain hz := h.keep K (by rw [memory]; exact Outside.refl _ _ _ _)
  obtain value : z.gpr .ecx =
      ((s.mem.readW (off B (VG.Proof.Rsa.X86.Keys.arr n aU)) 32 |||
        s.mem.readW (off B (VG.Proof.Rsa.X86.Keys.arr n aV)) 32) &&& (1 : BitVec 32)) ^^^ 1 := by
    rw [Zf.gpr, Y.gpr, X.gpr, Kw.1 _ (by decide), V.gpr, mw, V.mem, mu,
      Nat.add_zero, arr, offset_array, Width.words, arr, offset_array, Width.words]
    rfl
  refine WP.mono (store_slot hz (d := kFlag) (by decide) .ecx) fun t ⟨ht, O, flag, Kt⟩ => ?_
  rw [memory] at O
  refine ⟨ht, O, ?_, K.trans (Kt.mono (by decide))⟩
  rw [flag, value, VG.Proof.RsaKeyGen.X86.Key.even_bit,
    ← VG.Proof.RsaKeyGen.X86.Key.num_parity _ _ h.wpos aU,
    ← VG.Proof.RsaKeyGen.X86.Key.num_parity _ _ h.wpos aV]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Half.lean`, which only this module imported.
section

/-! # Conditional halving for the native RSA LCM schedule -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (kFlag aPa aQa aPm aQm aPhi aHalf)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem halfIf_ok {s : State} {B : Addr} {Z n j : Nat}
    (h : Ws s B Z n 32) (hj : j < 31) (bit : slot s.mem B kFlag ≤ 1) :
    WP isa (halfIf j) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aHalf, j] [] s.mem t.mem ∧
      num t.mem B n j = (if slot s.mem B kFlag = 0 then num s.mem B n j else num s.mem B n j / 2) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  obtain hf : kFlag + 4 ≤ hdr := by decide
  obtain fj := h.fit64 (j := j) (by omega)
  unfold halfIf seqs
  refine WP.seq (WP.mono (copy_ok h (by decide) (by omega) (by unfold aHalf; omega)) fun u ⟨hu, Ou, copied, Ku, _⟩ => ?_)
  refine WP.seq (wp_movS rfl fun v V _ => WP.block_nil ?_)
  obtain hv := hu.keep V.keeps (by rw [V.mem]; exact Outside.refl _ _ _ _)
  obtain zero : (v.gpr .ebx).toNat ≤ 1 := by rw [V.gpr]; decide
  refine WP.seq (WP.mono (half_ok hv (by decide) zero) fun w ⟨hw, Ow, halved, Kw⟩ => ?_)
  obtain ev : (v.gpr .ebx).toNat = 0 := by rw [V.gpr]; rfl
  rw [V.mem, ev, Nat.mul_zero, Nat.add_zero, copied] at halved
  obtain valueU : num u.mem B n j = num s.mem B n j :=
    Ou.num (by simp only [List.mem_singleton]; intro k e; subst k; unfold aHalf; omega) (by simp) fj
  obtain valueW : num w.mem B n j = num s.mem B n j := by
    rw [Ow.num (by simp only [List.mem_singleton]; intro k e; subst k; unfold aHalf; omega) (by simp) fj,
      V.mem, valueU]
  obtain flagW : slot w.mem B kFlag = slot s.mem B kFlag := by
    rw [Ow.slot hf (by simp), V.mem, Ou.slot hf (by simp)]
  refine WP.mono (sel_ok hw (by omega) (by omega) (by decide) hf (by rw [flagW]; exact bit) (by right; unfold aHalf; omega))
    fun t ⟨ht, Ot, selected, Kt⟩ => ?_
  obtain middle : Keep B n [aHalf] [] u.mem w.mem := by rw [V.mem] at Ow; exact Ow
  exact ⟨ht, (Ou.trans middle).join Ot (js := [aHalf, j]) (ds := []),
    by rw [selected, flagW, valueW, halved],
    (Ku.mono (by decide)).trans ((V.keeps.mono (by decide)).trans
      ((Kw.mono (by decide)).trans (Kt.mono (by decide))))⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (kFlag aU aV aPhi aPm aQm aHalf)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

def triple (m : Mem) (B : Addr) (n : Nat) : Nat × Nat × Nat :=
  (num m B n aU, num m B n aV, num m B n aPhi)

def halveArrays : List Nat := [aHalf, aU, aV, aPhi]

theorem halveStep_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (Impl.RsaKeyGen.X86.KeyRuntime.halveStep) s fun t =>
      Ws t B Z n 32 ∧ Keep B n halveArrays [kFlag] s.mem t.mem ∧
      triple t.mem B n = VG.Proof.RsaKeyGen.halveStep (triple s.mem B n) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  obtain hf : kFlag + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by decide
  obtain fu := h.fit64 (j := aU) (by decide)
  obtain fv := h.fit64 (j := aV) (by decide)
  obtain ff := h.fit64 (j := aPhi) (by decide)
  unfold Impl.RsaKeyGen.X86.KeyRuntime.halveStep VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (WP.mono (bothEven_ok h) fun u ⟨hu, Ou, flag, Ku⟩ => ?_)
  obtain Uu : num u.mem B n aU = num s.mem B n aU := Ou.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; exact hf) fu
  obtain Vu : num u.mem B n aV = num s.mem B n aV := Ou.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; exact hf) fv
  obtain Fu : num u.mem B n aPhi = num s.mem B n aPhi := Ou.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; exact hf) ff
  obtain bitU : slot u.mem B kFlag ≤ 1 := by rw [flag]; split <;> omega_using []
  refine WP.seq (WP.mono (halfIf_ok hu (by decide) bitU) fun v ⟨hv, Ov, halfU, Kv⟩ => ?_)
  obtain Vv : num v.mem B n aV = num s.mem B n aV := by rw [Ov.num (by decide) (by simp) fv, Vu]
  obtain Fv : num v.mem B n aPhi = num s.mem B n aPhi := by rw [Ov.num (by decide) (by simp) ff, Fu]
  obtain flagV : slot v.mem B kFlag = slot u.mem B kFlag := Ov.slot hf (by simp)
  obtain bitV : slot v.mem B kFlag ≤ 1 := by rw [flagV]; exact bitU
  refine WP.seq (WP.mono (halfIf_ok hv (by decide) bitV) fun w ⟨hw, Ow, halfV, Kw⟩ => ?_)
  obtain Uw : num w.mem B n aU = num v.mem B n aU := Ow.num (by decide) (by simp) fu
  obtain Fw : num w.mem B n aPhi = num s.mem B n aPhi := by rw [Ow.num (by decide) (by simp) ff, Fv]
  obtain flagW : slot w.mem B kFlag = slot u.mem B kFlag := by rw [Ow.slot hf (by simp), flagV]
  obtain bitW : slot w.mem B kFlag ≤ 1 := by rw [flagW]; exact bitU
  refine WP.mono (halfIf_ok hw (by decide) bitW) fun t ⟨ht, Ot, halfF, Kt⟩ => ?_
  obtain Ut : num t.mem B n aU = num v.mem B n aU := by rw [Ot.num (by decide) (by simp) fu, Uw]
  obtain Vt : num t.mem B n aV = num w.mem B n aV := Ot.num (by decide) (by simp) fv
  refine ⟨ht, (((Ou.join Ov (js := halveArrays) (ds := [kFlag])
    (by simp) (by simp) (by simp [halveArrays]) (by simp)).join Ow
    (js := halveArrays) (ds := [kFlag]) (by simp) (by simp) (by simp [halveArrays]) (by simp)).join Ot
    (js := halveArrays) (ds := [kFlag]) (by simp) (by simp) (by simp [halveArrays]) (by simp)), ?_,
    (Ku.mono (by decide)).trans (Kv.trans (Kw.trans Kt))⟩
  · unfold triple
    rw [Ut, Vt, halfU, halfV, halfF, flagV, flagW, Uu, Vv, Fw, flag]
    unfold VG.Proof.RsaKeyGen.halveStep
    by_cases p : num s.mem B n aU % 2 = 0 ∧ num s.mem B n aV % 2 = 0
    · simp [p]
    · simp [p]

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

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

end

end

/-! # Canonicalize the LCM factors by a masked parity swap -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/EvenFlag.lean`, which only this module imported.
section

/-! # Negating the runtime parity bit uses the existing header frame -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep slot)
open VG.Impl.RsaKeyGen.X86.Key (kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem evenFlag_ok {s : State} {B : Addr} {Z n input : Nat}
    (h : Ws s B Z n 32) (hi : input < 32) :
    WP isa (evenFlag input) s fun t => Ws t B Z n 32 ∧ Keep B n [] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag = (if num s.mem B n input % 2 = 0 then 1 else 0) ∧
      Keeps [.eax, .edx] s t := by
  unfold evenFlag
  refine WP.seq (WP.mono (bitOf_ok h hi (by decide)) fun u ⟨hu, Ou, flag, Ku⟩ => ?_)
  refine wp_movS (readSrc_sc hu.old.workspace (d := kFlag) (by have := hu.hdr_le; unfold VG.Impl.Rsa.X86.Keys.hdr at this; unfold kFlag; omega))
    fun v V _ => wp_logicS (.inr rfl) rfl fun w W => ?_
  have K : Keeps [.eax, .edx] u w := (V.keeps.trans W.keeps).mono (by decide)
  have memory : w.mem = u.mem := W.mem.trans V.mem
  have hw := hu.keep K (by rw [memory]; exact Outside.refl _ _ _ _)
  refine WP.mono (store_slot hw (d := kFlag) (by decide) .eax) fun t ⟨ht, Ot, result, Kt⟩ => ?_
  rw [memory] at Ot
  refine ⟨ht, Ou.trans Ot, ?_, Ku.trans (K.trans (Kt.mono (by decide)))⟩
  rw [result, W.gpr, V.gpr]
  have bit : (u.mem.readW (off B kFlag) 32).toNat ≤ 1 := by
    change slot u.mem B kFlag ≤ 1
    rw [flag]; omega
  change (u.mem.readW (off B kFlag) 32 ^^^ (1 : BitVec 32)).toNat = _
  rw [VG.Proof.Rsa.KeyBits32.bv_xor_bits bit (by decide)]
  change (slot u.mem B kFlag + 1) % 2 = _
  rw [flag]
  have remainder := Nat.mod_lt (num s.mem B n input) (by decide : 0 < 2)
  split <;> omega

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (kFlag aU aV)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem oddSecond_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa oddSecond s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aU, aV] [kFlag] s.mem t.mem ∧
      num t.mem B n aU = (if num s.mem B n aV % 2 = 0 then num s.mem B n aV else num s.mem B n aU) ∧
      num t.mem B n aV = (if num s.mem B n aV % 2 = 0 then num s.mem B n aU else num s.mem B n aV) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have hf : kFlag + 4 ≤ hdr := by decide
  have fu := h.fit64 (j := aU) (by decide)
  have fv := h.fit64 (j := aV) (by decide)
  have ft := h.fit64 (j := aT1) (by decide)
  unfold oddSecond seqs
  refine WP.seq (WP.mono (evenFlag_ok h (by decide)) fun u ⟨hu, Ou, flag, Ku⟩ => ?_)
  have Uu : num u.mem B n aU = num s.mem B n aU :=
    Ou.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; exact hf) fu
  have Vu : num u.mem B n aV = num s.mem B n aV :=
    Ou.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; exact hf) fv
  refine WP.seq (WP.mono (copy_ok hu (by decide) (by decide) (by decide)) fun v ⟨hv, Ov, copied, Kv, _⟩ => ?_)
  have Uv : num v.mem B n aU = num s.mem B n aU := by rw [Ov.num (by decide) (by simp) fu, Uu]
  have Vv : num v.mem B n aV = num s.mem B n aV := by rw [Ov.num (by decide) (by simp) fv, Vu]
  have Tv : num v.mem B n aT1 = num s.mem B n aU := copied.trans Uu
  have flagV : slot v.mem B kFlag = slot u.mem B kFlag := Ov.slot hf (by simp)
  have bitV : slot v.mem B kFlag ≤ 1 := by rw [flagV, flag]; split <;> omega_using []
  refine WP.seq (WP.mono (sel_ok hv (by decide) (by decide) (by decide) hf bitV (by decide))
    fun w ⟨hw, Ow, selectedU, Kw⟩ => ?_)
  have Vw : num w.mem B n aV = num s.mem B n aV := by rw [Ow.num (by decide) (by simp) fv, Vv]
  have Tw : num w.mem B n aT1 = num s.mem B n aU := by rw [Ow.num (by decide) (by simp) ft, Tv]
  have flagW : slot w.mem B kFlag = slot u.mem B kFlag := by rw [Ow.slot hf (by simp), flagV]
  have bitW : slot w.mem B kFlag ≤ 1 := by rw [flagW, flag]; split <;> omega_using []
  refine WP.mono (sel_ok hw (by decide) (by decide) (by decide) hf bitW (by decide))
    fun t ⟨ht, Ot, selectedV, Kt⟩ => ?_
  have U : num t.mem B n aU = if slot u.mem B kFlag = 0 then num s.mem B n aU else num s.mem B n aV := by
    rw [Ot.num (by decide) (by simp) fu, selectedU, flagV, Uv, Vv]
  have V : num t.mem B n aV = if slot u.mem B kFlag = 0 then num s.mem B n aV else num s.mem B n aU := by
    rw [selectedV, flagW, Vw, Tw]
  refine ⟨ht, (((Ou.join Ov (js := [aT1, aU, aV]) (ds := [kFlag])).join Ow
    (js := [aT1, aU, aV]) (ds := [kFlag])).join Ot
    (js := [aT1, aU, aV]) (ds := [kFlag])), ?_, ?_,
    (Ku.mono (by decide)).trans (Kv.trans (Kw.trans Kt))⟩
  · rw [U, flag]
    by_cases p : num s.mem B n aV % 2 = 0 <;> simp [p]
  · rw [V, flag]
    by_cases p : num s.mem B n aV % 2 = 0 <;> simp [p]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
