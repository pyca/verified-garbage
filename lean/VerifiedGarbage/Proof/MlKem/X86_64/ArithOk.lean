module

import VerifiedGarbage.Proof.MlKem.X86_64.NttInv
import VerifiedGarbage.Proof.MlKem.X86_64.YAddSub
import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
import VerifiedGarbage.Proof.MlKem.X86_64.Cbd16Avx2
import VerifiedGarbage.Proof.MlKem.X86_64.Decode12Avx2
import VerifiedGarbage.Proof.MlKem.X86_64.Encode12Avx2
public import VerifiedGarbage.Impl.MlKem.X86_64.Frag
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.MlKem.X86_64.KgMul
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Proof.MlKem.X86_64.Cbd16
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
import VerifiedGarbage.Proof.MlKem.X86_64.Decode12
import VerifiedGarbage.Proof.MlKem.X86_64.Encode12
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.MlKem.PolyW
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncodeAvx2
import VerifiedGarbage.Proof.MlKem.X86_64.MulAvx2
import VerifiedGarbage.Proof.MlKem.X86_64.NttLazy
import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay42
import VerifiedGarbage.Proof.MlKem.X86_64.YNttPack
import VerifiedGarbage.Proof.Sha3.X86_64.X4.Wp

/-!
# The polynomial arithmetic a top-level function of ML-KEM calls on x86-64

What the top-level functions need of the implementations of the
polynomial primitives they call (`Impl.MlKem.X86_64.Arith`): each meets its contract, is constant time, never
writes the stack pointer, makes no calls, and keeps MXCSR's control bits
(`ArithOk`). `Arith.sse` and `Arith.sse16` do (`ArithOk.sse`,
`ArithOk.sse16`); the top-level functions call the one that goes with their
implementation of `vg_mlkem_sample_ntt4` (`Callee4.arith`,
`Sample4Impl.arith`). The primitives with AVX2 that the K-PKE functions
inline do too (`PrimsOk.avx2`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem nosp_of {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c := by
  rw [Code.allInstrs_eq] at h
  intro i hi
  simpa using List.all_eq_true.mp h i hi

/-- What a caller needs of a function with the contract `k`. -/
structure CalleeOk (k : Contract isa) (c : Prog isa) : Prop where
  ok : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s'
  ct : ConstantTime isa k.pre k.pub c
  nosp : NoSp c
  depth : c.depth = 0
  ctl : ctlOk c = true
  sp : c.all (fun i => !isa.writesSp i) = true

/-- The polynomial primitives `A` are correct, constant time, and safe to call. -/
structure PrimsOk (A : Prims) : Prop where
  add : CalleeOk (accK Spec.MlKem.add) A.add
  sub : CalleeOk (accK Spec.MlKem.sub) A.sub
  dec12 : CalleeOk decode12K A.dec12
  enc12 : CalleeOk encode12K A.enc12

/-- The polynomial arithmetic `A` is correct, constant time, and safe to call. -/
structure ArithOk (A : Arith) : Prop extends PrimsOk A.toPrims where
  nttInv : CalleeOk (inPlaceK nttInv) A.nttInv
  cbd : CalleeOk cbd2K A.cbd
  cbd16 : CalleeOk Cbd16.cbd2_16K A.cbd16
  dm : ∀ k, k = 3 ∨ k = 4 → CalleeOk (decMulK k) (A.decMul k)
  em : ∀ k, k = 3 ∨ k = 4 → CalleeOk (encMulK k) (A.encMul k)
  km : ∀ k, k = 3 ∨ k = 4 → CalleeOk (kgMulK k) (keygenMul A.bodies k)

theorem ArithOk.sse : ArithOk .sse where
  nttInv := ⟨nttInv_correct, nttInv_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩
  add := ⟨add_correct, add_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩
  sub := ⟨sub_correct, sub_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩
  cbd := ⟨cbd2_correct, cbd2_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩
  cbd16 := ⟨cbd2_16_correct, cbd2_16_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩
  dec12 := ⟨decode12_correct, decode12_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩
  enc12 := ⟨encode12_correct, encode12_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩
  dm k hk := by
    rcases hk with rfl | rfl
    · exact ⟨decMulSse3_correct, decMulSse3_ct, nosp_of (by lit_decide), by lit_decide, decMulSse3_ctl,
        Code.all_of_allInstrs (by lit_decide)⟩
    · exact ⟨decMulSse4_correct, decMulSse4_ct, nosp_of (by lit_decide), by lit_decide, decMulSse4_ctl,
        Code.all_of_allInstrs (by lit_decide)⟩
  em k hk := by
    rcases hk with rfl | rfl
    · exact ⟨encMulSse3_correct, encMulSse3_ct, nosp_of (by lit_decide), by lit_decide, encMulSse3_ctl,
        Code.all_of_allInstrs (by lit_decide)⟩
    · exact ⟨encMulSse4_correct, encMulSse4_ct, nosp_of (by lit_decide), by lit_decide, encMulSse4_ctl,
        Code.all_of_allInstrs (by lit_decide)⟩
  km k hk := by
    rcases hk with rfl | rfl
    · exact ⟨kgMulSse3_correct, kgMulSse3_ct, nosp_of (by lit_decide), by lit_decide, kgMulSse3_ctl,
        Code.all_of_allInstrs (by lit_decide)⟩
    · exact ⟨kgMulSse4_correct, kgMulSse4_ct, nosp_of (by lit_decide), by lit_decide, kgMulSse4_ctl,
        Code.all_of_allInstrs (by lit_decide)⟩

/-- The baseline, but for `vg_mlkem16_cbd2_avx2`. -/
theorem ArithOk.sse16 : ArithOk .sse16 :=
  { ArithOk.sse with
    cbd16 := ⟨cbd2_16Y_correct, cbd2_16Y_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
      Code.all_of_allInstrs (by lit_decide)⟩ }

theorem PrimsOk.avx2 : PrimsOk .avx2 where
  add := ⟨addY_correct, addY_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩
  sub := ⟨subY_correct, subY_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩
  dec12 := ⟨decode12Y_correct, decode12Y_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩
  enc12 := ⟨encode12Y_correct, encode12Y_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩

/-- A call of `vg_mlkem*_decrypt_mul` keeps MXCSR's control bits. -/
theorem ArithOk.dm_ctl {A : Arith} (hA : ArithOk A) {n : String} {k : Nat} (hk : k = 3 ∨ k = 4 := by decide) :
    ctlOk (.call n (A.decMul k)) = true := (hA.dm k hk).ctl

/-- A call of `vg_mlkem*_decrypt_mul` never writes the stack pointer. -/
theorem ArithOk.dm_sp {A : Arith} (hA : ArithOk A) {n : String} {k : Nat} (hk : k = 3 ∨ k = 4 := by decide) :
    (Code.call n (A.decMul k) : Prog isa).all (fun i => !isa.writesSp i) = true := (hA.dm k hk).sp

/-- A call of `vg_mlkem*_encrypt_mul` keeps MXCSR's control bits. -/
theorem ArithOk.em_ctl {A : Arith} (hA : ArithOk A) {n : String} {k : Nat} (hk : k = 3 ∨ k = 4 := by decide) :
    ctlOk (.call n (A.encMul k)) = true := (hA.em k hk).ctl

/-- A call of `vg_mlkem*_encrypt_mul` never writes the stack pointer. -/
theorem ArithOk.em_sp {A : Arith} (hA : ArithOk A) {n : String} {k : Nat} (hk : k = 3 ∨ k = 4 := by decide) :
    (Code.call n (A.encMul k) : Prog isa).all (fun i => !isa.writesSp i) = true := (hA.em k hk).sp

/-- A call of `vg_mlkem*_keygen_mul` keeps MXCSR's control bits. -/
theorem ArithOk.km_ctl {A : Arith} (hA : ArithOk A) {n : String} {k : Nat} (hk : k = 3 ∨ k = 4 := by decide) :
    ctlOk (.call n (keygenMul A.bodies k)) = true := (hA.km k hk).ctl

/-- A call of `vg_mlkem*_keygen_mul` never writes the stack pointer. -/
theorem ArithOk.km_sp {A : Arith} (hA : ArithOk A) {n : String} {k : Nat} (hk : k = 3 ∨ k = 4 := by decide) :
    (Code.call n (keygenMul A.bodies k) : Prog isa).all (fun i => !isa.writesSp i) = true := (hA.km k hk).sp

end VG.Proof.MlKem.X86_64
