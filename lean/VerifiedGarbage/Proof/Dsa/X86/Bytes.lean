module

public import VerifiedGarbage.Impl.Dsa.X86.Bytes
public import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
public import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # DSA component decoding, encoding and failure-output masking -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86

theorem toBytes_encodeBE (n x : Nat) : Spec.Weierstrass.toBytes n x = Spec.Dsa.encodeBE n x := by
  apply List.ext_getElem
  · simp only [Spec.Weierstrass.toBytes, Spec.Dsa.encodeBE, List.length_map, List.length_reverse, List.length_range]
  · intro i hi hj
    simp only [Spec.Weierstrass.toBytes, Spec.Dsa.encodeBE, List.getElem_map, List.getElem_reverse,
      List.length_range, List.getElem_range]

theorem loadComponent_ok {s : State} {base : Addr} {size len n out : Nat}
    (hs : Scr s base size) (ho : out + 8 * n ≤ size)
    (hp : (s.gpr .esi).toNat + len ≤ 2 ^ 32) (h4 : 4 ≤ len) (hlen : len ≤ 8 * n)
    (hr : ∀ d, d + 4 ≤ len → InRegions (s.rd ++ s.wr) ((s.gpr .esi).setWidth 64 + BitVec.ofNat 64 d) 4)
    (hd : Region.Disjoint ⟨(s.gpr .esi).setWidth 64, len⟩ ⟨off base out, 8 * n⟩) :
    WP isa (.block (loadComponent len n out)) s fun t =>
      wordsVal t.mem base out n = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((s.gpr .esi).setWidth 64) len) ∧
      Keeps [.eax] s t ∧ Outside base out (8 * n) s.mem t.mem :=
  VG.Proof.Weierstrass.X86.loadBytes_ok hs (by decide) ho hp h4 hlen hr hd

theorem storeComponent_ok {s : State} {base : Addr} {size len n input : Nat}
    (hs : Scr s base size) (accepted : Bool)
    (hc : s.gpr .ecx = if accepted then BitVec.allOnes 32 else 0)
    (ha : input + 8 * n ≤ size) (h4 : 4 ≤ len) (hlen : len ≤ 8 * n)
    (hp : (s.gpr .esi).toNat + len ≤ 2 ^ 32)
    (hw : ∀ e k, e + k ≤ len → InRegions s.wr ((s.gpr .esi).setWidth 64 + BitVec.ofNat 64 e) k)
    (hd : Region.Disjoint ⟨off base input, 8 * n⟩ ⟨(s.gpr .esi).setWidth 64, len⟩) :
    WP isa (.block (storeComponent len n input)) s fun t =>
      Spec.Rsa.bytesAt t.mem ((s.gpr .esi).setWidth 64) len =
        (if accepted then Spec.Dsa.encodeBE len (wordsVal s.mem base input n) else List.replicate len 0) ∧
      Keeps [.eax, .edx] s t ∧ Outside ((s.gpr .esi).setWidth 64) 0 len s.mem t.mem := by
  refine WP.mono (VG.Proof.Weierstrass.X86.storeBytes_ok (d := 0) hs (by decide) (by decide) accepted hc
    ha h4 hlen (by omega) (by simpa only [BitVec.add_zero] using hw) (by simpa only [BitVec.add_zero] using hd))
    fun t ⟨V, K, O⟩ => ?_
  simp only [BitVec.add_zero, toBytes_encodeBE] at V O
  exact ⟨V, K, O⟩

end VG.Proof.Dsa.X86
