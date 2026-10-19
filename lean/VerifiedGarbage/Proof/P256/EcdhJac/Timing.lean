module

public import VerifiedGarbage.Proof.P256.EcdhJac.Lit
meta import VerifiedGarbage.Proof.P256.EcdhJac.Lit
import VerifiedGarbage.Proof.P256.EcdhJac.Prefix
meta import VerifiedGarbage.Proof.P256.EcdhJac.Prefix
import VerifiedGarbage.Proof.Ecdh.AArch64.Verified
meta import VerifiedGarbage.Proof.Ecdh.AArch64.Verified
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
public import VerifiedGarbage.Proof.Ecdh.AArch64.Contract
public import VerifiedGarbage.Proof.Ecdh.AArch64.Lit
public import VerifiedGarbage.Proof.Ecdh.AArch64.MulOk
public import VerifiedGarbage.Proof.Ecdh.AArch64.Prefix
public import VerifiedGarbage.Proof.Framework.RelCT
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import Mathlib.Data.Finset.Card
meta import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Impl.P256.VerifyRegisters
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Function
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross0
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross1
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross2
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross3
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDiag
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDouble
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductLow
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductTop
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
import VerifiedGarbage.Proof.Mont.AArch64.Rounds
import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Spec.Ecdh.P256
import VerifiedGarbage.Spec.Weierstrass.Mul
meta import VerifiedGarbage.Impl.P256.VerifyRegisters
meta import VerifiedGarbage.Proof.EcKey.PublicKey
meta import VerifiedGarbage.Proof.Ecdh.AArch64.MulOk
meta import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
meta import VerifiedGarbage.Proof.Ecdh.Exchange
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
meta import VerifiedGarbage.Proof.Ecdsa.Sign
meta import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd64
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.BitByte
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Pratt
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.AArch64.Blocks
meta import VerifiedGarbage.Proof.Mont.AArch64.Chain
meta import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Product
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Function
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross0
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross1
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross2
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross3
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDiag
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDouble
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductLow
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductTop
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
meta import VerifiedGarbage.Proof.Mont.AArch64.Rounds
meta import VerifiedGarbage.Proof.P256.Prime
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelect
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
meta import VerifiedGarbage.Spec.Ecdh.P256
meta import VerifiedGarbage.Spec.Weierstrass.Mul

@[expose] public section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Ecdh.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Impl.Ecdsa.AArch64

theorem keepsV : Impl.P256.EcdhJac.exchange.allInstrs AArch64.keepsV = true := by lit_decide

theorem middle_callsKeep : CallsKeep finish := by lit_decide

theorem middle_keepsUntouched : KeepsUntouched finish := by lit_decide

abbrev Public := AArch64.Taint.Agree (Taint.ofRegs [.x0,.x20])
abbrev Ready (s t : State) : Prop := MulInput p256 s ∧ MulInput p256 t ∧ Public s t

theorem before_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3])) before :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2,.x3])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem multiply_ct : ConstantTime isa (fun _ => True) Public multiply :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x20])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem finish_ct : ConstantTime isa (fun _ => True) Public finish :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x20])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem before_relCT (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds) :
    RelCT isa (fun s t => ecdhAArch64.pre s ∧ ecdhAArch64.pre t ∧ ecdhAArch64.pub s t)
      before Ready := by
  intro s t ts tt s' t' ⟨ps,pt,h0,h1,h2,h3,hsp⟩ es et
  obtain ⟨_,_,es',hs,xs,os⟩ := Frontend.beforeMul_ok (p256_ok hI) hL (pre_of ps)
  obtain ⟨_,_,et',ht,xt,ot⟩ := Frontend.beforeMul_ok (p256_ok hI) hL (pre_of pt)
  obtain ⟨_,rfl⟩ := es.det es'
  obtain ⟨_,rfl⟩ := et.det et'
  have pub : AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3]) s t := by
    refine ⟨hsp,?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  refine ⟨before_ct _ _ _ _ _ _ trivial trivial pub es et,hs,ht,
    (Exec.sp es).trans (hsp.trans (Exec.sp et).symm),?_⟩
  intro r hr
  simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact xs.trans (h3.trans xt.symm)
  · exact os.trans (h0.trans ot.symm)

/-- Recover the public output pointer after its round trip through private scratch. -/
theorem multiply_relCT (hm : MulWithInverseOk p256 mq Impl.P256.EcdhInverse.inverse) : RelCT isa Ready multiply Public := by
  intro s t ts tt s' t' ⟨⟨bs,gs,ps,hss,fs,hps,lxs,lys,reps⟩,
    ⟨bt,gt,pt,hst,ft,hpt,lxt,lyt,rept⟩,hp⟩ es et
  have ws := hm hss fs hps lxs lys reps (rest:=.block [])
    (R:=fun u => MulPost p256 bs gs ps (sv p256 bs s K) s u) (fun _ h => WP.block_nil h)
  have wt := hm hst ft hpt lxt lyt rept (rest:=.block [])
    (R:=fun u => MulPost p256 bt gt pt (sv p256 bt t K) t u) (fun _ h => WP.block_nil h)
  obtain ⟨_,_,xs,hs⟩ := WP.assoc' ws
  obtain ⟨_,_,xt,ht⟩ := WP.assoc' wt
  have esn : Exec isa (.seq multiply (.block [])) s (ts++[]) s' := .seq es (.block rfl)
  have etn : Exec isa (.seq multiply (.block [])) t (tt++[]) t' := .seq et (.block rfl)
  obtain ⟨_,rfl⟩ := esn.det xs
  obtain ⟨_,rfl⟩ := etn.det xt
  refine ⟨multiply_ct _ _ _ _ _ _ trivial trivial hp es et,
    (Exec.sp es).trans (hp.1.trans (Exec.sp et).symm),?_⟩
  intro r hr
  simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact hs.scr.x0.trans (hss.x0.symm.trans ((hp.2 _ (by simp [Taint.mem_ofRegs])).trans
      (hst.x0.trans ht.scr.x0.symm)))
  · exact hs.x20.trans ((hp.2 _ (by simp [Taint.mem_ofRegs])).trans ht.x20.symm)

private theorem regroup {s t : State} {tr}
    (h : Exec isa Impl.P256.EcdhJac.exchange s tr t) :
    Exec isa (.seq before (.seq multiply finish)) s tr t := by
  cases h with
  | seq a h => cases h with
    | seq b h => cases h with
      | seq c h => cases h with
        | seq d h => cases h with
          | seq p h => cases h with
            | seq w h => cases h with
              | seq i f =>
                simpa only [before, multiply, mq, finish, Impl.P256.EcdhJac.Frontend.before,
                  Impl.P256.EcdhJac.c, List.append_assoc] using
                  (Exec.seq (Exec.seq a (Exec.seq b (Exec.seq c d)))
                    (Exec.seq (Exec.seq (Exec.seq p w) i) f))

theorem constantTime (hL : Weierstrass.Law Spec.P256.curve)
    (hI : Weierstrass.AArch64.InvSounds) (hm : MulWithInverseOk p256 mq Impl.P256.EcdhInverse.inverse) :
    ConstantTime isa ecdhAArch64.pre ecdhAArch64.pub Impl.P256.EcdhJac.exchange := by
  have hf : RelCT isa Public finish (fun _ _ => True) := by
    intro s t ts tt s' t' hp es et
    exact ⟨finish_ct _ _ _ _ _ _ trivial trivial hp es et,trivial⟩
  have h := RelCT.constantTime ((before_relCT hL hI).seq ((multiply_relCT hm).seq hf))
  intro s t ts tt s' t' ps pt hp es et
  exact h _ _ _ _ _ _ ps pt hp (regroup es) (regroup et)

end VG.Proof.P256.EcdhJac
