module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Inverse
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseKeeps
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StackRange
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentFrame
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DivisionFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.OddModulus
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ScalarKey
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Scalar
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.GcdIsOne
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEvenFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge
import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionLoad
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # A modulus-width fallback for public even exponents -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aE aL aDen aU aV aD kEv kOk kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (exponentRanges exponentTemps exponent_keep_frame
  exponent_temps_inverse inverse_array_layout)

theorem dEven_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (even : val32 s.mem B kEv 2 % 2 = 0)
    (loaded : num s.mem B n aE = val32 s.mem B kEv 2) :
    WP isa dEven s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (exponentRanges n) s.mem t.mem ∧ slot t.mem B kOk ≤ 1 ∧
      Spec.Rsa.inverse (val32 s.mem B kEv 2) (num s.mem B n aL) =
        (if slot t.mem B kOk = 0 then none else some (num t.mem B n aD)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let e := val32 s.mem B kEv 2
  let L := num s.mem B n aL
  let valid := L % 2 = 1 ∧ 3 ≤ L
  let M := if valid then L else 3
  have eo : e % 2 = 0 := even
  have mo : M % 2 = 1 := by
    unfold M
    split
    · next H => exact H.1
    · decide
  have ml : 1 < M := by unfold M; split <;> omega
  unfold dEven seqs
  refine WP.seq (WP.mono (oddModulus_ok h (by decide) (by decide) (by decide))
    fun u ⟨hu, Ou, flag, modulus, Ku⟩ => ?_)
  change num u.mem B n aDen = M at modulus
  change slot u.mem B kFlag = (if valid then 1 else 0) at flag
  have Eu : num u.mem B n aE = e :=
    (Ou.num (by decide) (by decide) (h.fit64 (by decide))).trans loaded
  have frameU := exponent_keep_frame (by decide) (by decide) Ou
  refine WP.seq (WP.mono (saveSlot_ok hu (by decide) (by decide))
    fun v ⟨hv, Ov, saved, Kv⟩ => ?_)
  have maskV : slot v.mem B kOk = (if valid then 1 else 0) := saved.trans flag
  have Mv : num v.mem B n aDen = M :=
    (Ov.num (by simp) (by decide) (h.fit64 (by decide))).trans modulus
  have Ev : num v.mem B n aE = e :=
    (Ov.num (by simp) (by decide) (h.fit64 (by decide))).trans Eu
  have frameV := exponent_keep_frame (by decide) (by decide) Ov
  refine WP.seq (WP.mono (arrayDivision_ok hv (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [Mv]; omega))
    fun w ⟨hw, Ow, _, R, Kw⟩ => ?_)
  rw [Ev, Mv] at R
  have Mw : num w.mem B n aDen = M :=
    (arrayDivision_preserves_num (by decide) (by decide) (by decide) (h.fit64 (by decide)) Ow).trans Mv
  have maskW : slot w.mem B kOk = (if valid then 1 else 0) :=
    (arrayDivision_preserves_slot (by decide) Ow).trans maskV
  have frameW := exponent_division_frame Ow
  have layout := inverse_array_layout hw.old (Nat.le_refl n) (by decide : aV < 32)
    (by decide : aDen < 32) (by decide) (by decide)
  refine WP.seq (WP.mono (inverseFrom_ok (w := .modulus)
    (src := VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aV)
    (mo := VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen) hw (by decide) (by decide) layout (by change num w.mem B n aDen % 2 = 1; rw [Mw]; exact mo)
    (by change 1 < num w.mem B n aDen; rw [Mw]; exact ml))
    fun a ⟨ha, Oa, gcd, congruence, boundX, Ka⟩ => ?_)
  change num a.mem B n 1 = Nat.gcd (num w.mem B n aV) (num w.mem B n aDen) at gcd
  change (num w.mem B n aDen : Int) ∣ (num a.mem B n 3 : Int) * num w.mem B n aV - num a.mem B n 1 at congruence
  change num a.mem B n 3 < num w.mem B n aDen at boundX
  rw [R, Mw] at gcd congruence
  rw [Mw] at boundX
  rw [gcd] at congruence
  have maskA : slot a.mem B kOk = (if valid then 1 else 0) :=
    (hw.inverse_slot (by decide) Oa).trans maskW
  have spW : w.gpr .esp = s.gpr .esp := by
    rw [Kw.1 .esp (by decide), Kv.1 .esp (by decide), Ku.1 .esp (by decide)]
  have frameA : OutsS B (s.gpr .esp) (exponentRanges n) w.mem a.mem := by
    rw [← spW]
    exact OutsS.lift (fun _ _ O => (exponent_temps_inverse (Nat.le_refl n) O).mono
      (fun r hr => List.mem_append_left _ hr)) Oa
  refine WP.seq (WP.mono (gcdIsOne_ok (w := .modulus) ha (by decide) (by decide)) fun b ⟨hb, Ob, flagB, Kb⟩ => ?_)
  simp only [Width.words] at Ob
  change slot b.mem B kFlag = (if num a.mem B n 1 = 1 then 1 else 0) at flagB
  rw [gcd] at flagB
  have maskB : slot b.mem B kOk = (if valid then 1 else 0) :=
    (Ob.slot (by decide) (by decide)).trans maskA
  have Xb : num b.mem B n 3 = num a.mem B n 3 :=
    Ob.num (by decide) (by decide) (h.fit64 (by decide))
  have frameB := exponent_keep_frame (by decide) (by decide) Ob
  refine WP.seq (WP.mono (andS_ok hb (by decide) (by decide) (by decide)
    (by rw [maskB]; split <;> omega) (by rw [flagB]; split <;> omega))
    fun c ⟨hc, Oc, maskC, Kc⟩ => ?_)
  rw [maskB, flagB] at maskC
  have Xc : num c.mem B n 3 = num a.mem B n 3 :=
    (Oc.num (by simp) (by decide) (h.fit64 (by decide))).trans Xb
  have frameC := exponent_keep_frame (by decide) (by decide) Oc
  refine WP.mono (copy_ok hc (by decide) (by decide) (by decide)) fun t ⟨ht, Ot, copied, Kt, _⟩ => ?_
  rw [Xc] at copied
  have maskT : slot t.mem B kOk =
      (if (if valid then 1 else 0) = 1 ∧ (if Nat.gcd (e % M) M = 1 then 1 else 0) = 1 then 1 else 0) :=
    (Ot.slot (by decide) (by simp)).trans maskC
  have frameT := exponent_keep_frame (by decide) (by simp) Ot
  refine ⟨ht, (((((OutsS.of_outs ((frameU.trans frameV).trans frameW)).trans frameA).trans
      (OutsS.of_outs frameB)).trans (OutsS.of_outs frameC)).trans (OutsS.of_outs frameT)),
    ?_, ?_, (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans
      (Kw.trans (Ka.trans ((Kb.mono (by decide)).trans ((Kc.mono (by decide)).trans (Kt.mono (by decide)))))))⟩
  · rw [maskT]
    by_cases V : valid <;> by_cases G : Nat.gcd (e % M) M = 1 <;> simp [V, G]
  · change Spec.Rsa.inverse e L = _
    by_cases V : valid
    · have ME : M = L := ite_eq_left V
      have V' : L % 2 = 1 ∧ 3 ≤ L := V
      by_cases G : Nat.gcd (e % M) M = 1
      · have C : (L : Int) ∣ (num a.mem B n 3 : Int) * (e % L) - 1 := by
          rw [G, ME] at congruence
          exact congruence
        have I := VG.Proof.RsaKeyGen.inverse_even V'.2 C (by simpa only [ME] using boundX)
        simpa only [maskT, V, G, ite_true, true_and, Nat.one_ne_zero, ite_false, copied] using I
      · have I := VG.Proof.RsaKeyGen.inverse_even_none eo (by
          intro H; exact G (by simpa only [ME] using H.2.2))
        simpa only [maskT, V, G, ite_true, ite_false, Nat.zero_ne_one, and_false, ↓reduceIte] using I
    · have I := VG.Proof.RsaKeyGen.inverse_even_none eo (by
        intro H; exact V ⟨H.1, H.2.1⟩)
      simpa only [maskT, V, ite_false, Nat.zero_ne_one, false_and, ↓reduceIte] using I

end VG.Proof.RsaKeyGen.X86.KeyRuntime
