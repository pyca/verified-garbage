module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Impl.Bignum.X86_64.MontFnSpecialized
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxMont
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86_64.Template

/-! ### `Bignum.X86_64.MontFnSpecialized`, which only this module used -/

section

/-! # Inlined ADX specialization preserves the complete executed trace -/

@[expose] public section
namespace VG.Proof.Bignum.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.MontFn
open VG.Proof.MlKem.X86_64
namespace Specialized

theorem result {c : Prog isa} {s t : State} {tr : List Leak} {Q : State → Prop}
    (h : WP isa c s Q) (e : Exec isa c s tr t) : Q t := by
  obtain ⟨_, u, eu, hu⟩ := h
  exact (Exec.det eu e).2 ▸ hu

theorem prune_ite {s t : State} {tr : List Leak} {c : Cond} {p q : Prog isa} {v : Bool}
    (hv : isa.eval c s = some v) :
    Exec isa (.ite c (if v then p else .block []) (if v then .block [] else q)) s tr t ↔
      Exec isa (.ite c p q) s tr t := by
  cases v <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals
    constructor <;> intro h
    all_goals
      rcases Exec.ite_inv h with ⟨tr, rfl, hc, he⟩ | ⟨tr, rfl, hc, he⟩
      all_goals first | exact .iteT hc he | exact .iteF hc he | simp_all

theorem tiled_iff {s t : State} {tr : List Leak} {a b : Nat}
    (ha : a < 8) (hb : b < 8) (hcx : s.gpr .rcx = BitVec.ofNat 64 a)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 b) :
    Exec isa (MontFnSpecialized.tiled a b) s tr t ↔ Exec isa tiled s tr t := by
  have step := cmpIdx_ok ha hb hcx h8
  constructor <;> intro h <;> cases h with
  | seq ec er =>
    have hu := result step ec
    cases er with
    | seq ei ef =>
      have hv := hu.1
      have he := fun {t : State} {tr : List Leak} => prune_ite (c := .e) (t := t) (tr := tr) (p := AdxTiledSquare.rawSquareBare xA)
        (q := AdxTiledProduct.rawProductBare xA xB) hv
      simp only [decide_eq_true_eq] at he
      first | exact .seq ec (.seq (he.mp ei) ef) | exact .seq ec (.seq (he.mpr ei) ef)

theorem body_iff {s t : State} {tr : List Leak} {a b : Nat}
    (ha : a < 8) (hb : b < 8) (hcx : s.gpr .rcx = BitVec.ofNat 64 a)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 b) :
    Exec isa (MontFnSpecialized.body a b) s tr t ↔ Exec isa adxBody s tr t := by
  constructor <;> intro h <;> cases h with
  | seq ec ei =>
    have hc : ∀ i ∈ instrs (.block alignTest : Prog isa), Taint.clobbers i .rcx = false := by decide
    have h8' : ∀ i ∈ instrs (.block alignTest : Prog isa), Taint.clobbers i .r8 = false := by decide
    have he := fun {t : State} {tr : List Leak} => tiled_iff (t := t) (tr := tr) ha hb ((Exec.gpr hc ec).trans hcx) ((Exec.gpr h8' ec).trans h8)
    cases ei with
    | iteT hb et => first | exact .seq ec (.iteT hb (he.mp et)) | exact .seq ec (.iteT hb (he.mpr et))
    | iteF hb ef => exact .seq ec (.iteF hb ef)

theorem mm_iff {s t : State} {tr : List Leak} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    {o a b : Nat} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    (ho : o < 8) (ha : a < 8) (hb : b < 8) :
    Exec isa (MontFnSpecialized.mm o a b) s tr t ↔ Exec isa (mmFnAdx o a b) s tr t := by
  have argsStep := fnArgs_ok s o a b
  constructor <;> intro h <;> cases h with
  | seq ea er =>
    obtain ⟨hdx, hcx, h8, hm, ku⟩ := result argsStep ea
    have headStep := adxHead_ok (hg.scr.congr ku.2.2) ((ku.gpr (by decide)).trans hg.rdi)
      (hm ▸ hg.hdr) hZ ho ha hb hdx hcx h8
    cases er with
    | seq eh er =>
      obtain ⟨_, _, hcxv, h8v, _⟩ := result headStep eh
      cases er with
      | seq eb ef =>
        have he := fun {t : State} {tr : List Leak} => body_iff (t := t) (tr := tr) ha hb hcxv h8v
        first | exact .seq ea (.seq eh (.seq (he.mp eb) ef))
              | exact .seq ea (.seq eh (.seq (he.mpr eb) ef))

end Specialized

/-- The callable ADX kernel, with its unused operation omitted at each
inline site. Executed instructions, states and leakage are unchanged. -/
def Mont.fnAdxSpecialized : Mont where
  mm := MontFnSpecialized.mm
  ok hg hZ hw hw' _ _ _ ho ha hb ho1 ho2 ha1 ha2 hb1 hb2 hinv hB := by
    obtain ⟨tr, t, he, post⟩ := Mont.fnAdx.ok hg hZ hw hw' ho ha hb ho1 ho2 ha1 ha2 hb1 hb2 hinv hB
    exact ⟨tr, t, (Specialized.mm_iff hg hZ ho ha hb).mpr he, post⟩
  ct := by
    intro o a b use s t tr₁ tr₂ u v ⟨d, hs, ht⟩ es et
    obtain ⟨mi, gs, hZ⟩ := hs
    obtain ⟨mj, gt, hZt⟩ := ht
    have bounds : o < 8 ∧ a < 8 ∧ b < 8 := by
      rcases use with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide
    exact Mont.fnAdx.ct use s t tr₁ tr₂ u v ⟨d, ⟨mi, gs, hZ⟩, ⟨mj, gt, hZt⟩⟩
      ((Specialized.mm_iff gs hZ bounds.1 bounds.2.1 bounds.2.2).mp es)
      ((Specialized.mm_iff gt hZt bounds.1 bounds.2.1 bounds.2.2).mp et)

end VG.Proof.Bignum.X86_64

end

end


/-!
# The BMI2/ADX shared Miller–Rabin round: the variant's code and proofs

The variant `VG.Variants.MillerRabin.X86_64.Adx.variant`
(`Variants/MillerRabin/X86_64/Adx.lean`), with the proofs its interface asks
for. Its callers multiply by calls of `vg_rsa_mont_mul_adx`, rather than
each inlining its unrolled code.
-/

@[expose] public section

namespace VG.Proof.Variants.MillerRabin.X86_64.Adx

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

def arith : RoundArith where
  mont := Mont.fnAdx
  inlineMont := Mont.fnAdxSpecialized
  inlineDepth := by
    intro o a b
    unfold Mont.fnAdxSpecialized
    change (Impl.Bignum.X86_64.MontFnSpecialized.mm o a b).x86_64Depth = 0
    unfold Impl.Bignum.X86_64.MontFnSpecialized.mm
      Impl.Bignum.X86_64.MontFnSpecialized.body Impl.Bignum.X86_64.MontFnSpecialized.tiled
    split <;> rfl
  inlineSafe := by
    intro o a b
    change (Impl.Bignum.X86_64.MontFnSpecialized.mm o a b).allInstrs
      (fun i => !loadsMxcsr i && !isa.writesSp i) = true
    unfold Impl.Bignum.X86_64.MontFnSpecialized.mm
      Impl.Bignum.X86_64.MontFnSpecialized.body Impl.Bignum.X86_64.MontFnSpecialized.tiled
    split <;> rfl
  inlineNoMx := by
    intro o a b
    change (Impl.Bignum.X86_64.MontFnSpecialized.mm o a b).allInstrs (fun i => !touchesMxcsr i) = true
    unfold Impl.Bignum.X86_64.MontFnSpecialized.mm
      Impl.Bignum.X86_64.MontFnSpecialized.body Impl.Bignum.X86_64.MontFnSpecialized.tiled
    split <;> rfl
  mm := Impl.Bignum.X86_64.MontFn.call "vg_rsa_mont_mul_adx" Impl.Bignum.X86_64.MontFn.mulAdx
  mmOk := call_inlineOk (by decide +kernel)
  mmInline _ _ _ := rfl
  mxSafe := by decide +kernel
  arithDepth := by intro o a b; rfl
  arithSafe := by intro o a b; rfl


def variant : RoundImpl := RoundImpl.ofArith arith (by decide +kernel) (by decide +kernel) "_adx" ["bmi2", "adx"]

end VG.Proof.Variants.MillerRabin.X86_64.Adx
