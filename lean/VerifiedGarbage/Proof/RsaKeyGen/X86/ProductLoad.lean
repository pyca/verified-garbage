module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Product
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.Words

/-! # Loading a native multiplication row -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Product
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86

theorem load_ok {s : State} {base : Addr} {size i a mult : Nat}
    (hs : Scr s base size)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (ha : 4 * i + a + 4 ≤ size) (hm : mult + 4 ≤ size) :
    WP isa (.block (Impl.RsaKeyGen.X86.Product.load a mult)) s fun t =>
      t.mem = s.mem.writeW (off base mult) (s.mem.readW (off base (4 * i + a)) 32) ∧
      Keeps [.eax] s t := by
  unfold Impl.RsaKeyGen.X86.Product.load
  refine wp_movS (readSrc_at hs hp ha) fun u U _ => ?_
  have hu := hs.of_keeps U.keeps (by decide)
  refine wp_storeS (hu.ea (by omega)) (hu.write hm) fun t T => WP.block_nil ?_
  exact ⟨by rw [T.mem, U.mem, U.gpr], U.keeps.trans (T.keeps _)⟩

end VG.Proof.RsaKeyGen.X86.Product
