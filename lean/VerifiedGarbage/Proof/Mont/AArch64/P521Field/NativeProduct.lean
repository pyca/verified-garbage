module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamProduct
import VerifiedGarbage.Proof.Framework.Block

/-! Connect the compositional product proof to the measured instruction order. -/

-- separate module: checked slice identities keep proof normalization out of emitted code
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field

def nativeProductCode : List Instr := (mulFnBlocks.flatten.drop 16).take 354
def nativeProductRest : List Instr := (mulFnBlocks.flatten.drop 55).take 315

theorem chunks_eq {α : Type} {xs ys : List α} (n : Nat)
    (ht : xs.take n=ys.take n) (hd : xs.drop n=ys.drop n) : xs=ys := by
  calc
    xs = xs.take n++xs.drop n := (List.take_append_drop n xs).symm
    _ = ys.take n++ys.drop n := by rw [ht,hd]
    _ = ys := List.take_append_drop n ys

theorem nativeProduct_split : nativeProductCode=row0Code++nativeProductRest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem product_normalized : productCode=(row0Loads++row0Arithmetic)++nativeProductRest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

/-- Moving independent loads is used only by the proof. The emitted product
retains exactly the interleaved load/product schedule measured on M1. -/
theorem native_product_ok {s : State} {pa pb pt : Addr}
    (ha : Ptr s .x1 pa 72) (hb : Ptr s .x2 pb 72) (ht : PtrW s .x27 pt 64)
    (stable : StableInput s pa pt)
    (ha' : wordsVal s.mem pa 0 9<2^521) (hb' : wordsVal s.mem pb 0 9<2^521) :
    WP isa (.block nativeProductCode) s (ProductInv s pa pt (wordsVal s.mem pb 0 9)) := by
  have h := product_ok ha hb ht stable ha' hb'
  rw [product_normalized,WP.block_append_iff] at h
  rw [nativeProduct_split,WP.block_append_iff]
  exact WP.hoistLoads row0_hoist h

end VG.Proof.Mont.AArch64.P521Field
