module

public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Prepare
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Arith
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Pack
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallPack
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst
import VerifiedGarbage.Proof.MlDsa.Arith.Mem

/-! # Canonical transforms used to prepare ML-DSA keys -/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.PreparedKey
open VG.Impl.MlDsa.AArch64.Call (Ptr callAt)
open VG.Spec.Sha3 (bytesAt)

theorem transform_ok {S : Nat} (hS : S < 2 ^ 64)
    (C : CalleeOk S Impl.MlDsa.AArch64.Arith.Neon.ntt
      (inPlaceContract AArch64.abi ntt S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s)
    {offset : Nat}
    (hc : ipChk rbs wbs (.x26, offset) (.x28, 0) = true)
    {f : Poly} (hf : PolyIs s.mem (pa s (.x26, offset)) f) :
    WP isa (transform offset) s fun t =>
      PPostB S s t [((.x26, offset), 1024), ((.x28, 0), 1024)] ∧
      t.gpr .x24 = s.gpr .x24 ∧
      PolyIs t.mem (pa s (.x26, offset)) (ntt f) := by
  refine WP.mono (ipAt_ok hS C L hc hf.1) fun t ⟨ht, h24, hp⟩ => ?_
  exact ⟨ht, h24, by rwa [hf.2] at hp⟩

theorem unpackTransform_ok {S : Nat} (hS : S < 2 ^ 64)
    (Cbu : CalleeOk S Impl.MlDsa.AArch64.Pack.bitUnpack
      (bitUnpackContract AArch64.abi S))
    (Cntt : CalleeOk S Impl.MlDsa.AArch64.Arith.Neon.ntt
      (inPlaceContract AArch64.abi ntt S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s)
    {src offset len a b : Nat}
    (hc : rwChk rbs wbs (.x25, src) len (.x26, offset) 1024 = true)
    (hi : ipChk rbs wbs (.x26, offset) (.x28, 0) = true)
    (hb : BpOk a b len) :
    WP isa (.seq
      (callAt "vg_mldsa_bit_unpack" Impl.MlDsa.AArch64.Pack.bitUnpack
        [(.x0, .ptr (.x25, src)), (.x1, .imm len), (.x2, .imm a),
          (.x3, .imm b), (.x4, .ptr (.x26, offset))])
      (transform offset)) s fun t =>
      PPostB S s t [((.x26, offset), 1024), ((.x28, 0), 1024)] ∧
      t.gpr .x24 = s.gpr .x24 ∧
      PolyIs t.mem (pa s (.x26, offset))
        (ntt (toRq (bitUnpack (bytesAt s.mem (pa s (.x25, src)) len) a b))) := by
  refine WP.seq (WP.mono (buAt_ok (nm := "vg_mldsa_bit_unpack") hS Cbu L hc hb)
    fun u ⟨hu, h24, hp⟩ => ?_)
  rw [← hu.pa (p := (.x26, offset)) (show Reg.x26 ∈ keptRegs by decide)] at hp
  refine WP.mono (transform_ok hS Cntt (L.post hu) hi hp) fun t ⟨ht, ht24, htp⟩ => ?_
  refine ⟨hu.trans ht (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact show Reg.x26 ∈ keptRegs by decide
      · exact show Reg.x28 ∈ keptRegs by decide)
    (by simp) (by simp), ht24.trans h24, ?_⟩
  rwa [hu.pa (p := (.x26, offset)) (show Reg.x26 ∈ keptRegs by decide)] at htp

theorem publicPoly_ok {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay 16 rbs wbs s) {p : Params} {i : Nat}
    (hc : rwChk rbs wbs (.x25, 32 + 320 * i) 320
      (.x26, p.pkLen + 1024 * i) 1024 = true)
    (hi : ipChk rbs wbs (.x26, p.pkLen + 1024 * i) (.x28, 0) = true) :
    WP isa (publicPoly p i) s fun t =>
      PPostB 16 s t [((.x26, p.pkLen + 1024 * i), 1024), ((.x28, 0), 1024)] ∧
      t.gpr .x24 = s.gpr .x24 ∧
      PolyIs t.mem (pa s (.x26, p.pkLen + 1024 * i))
        (ntt ((simpleBitUnpack (bytesAt s.mem (pa s (.x25, 32 + 320 * i)) 320)
          t1Max).map fun c => ofInt (c * 2 ^ d : Nat))) := by
  unfold publicPoly
  refine WP.seq (WP.mono (KeyGen.t1At_ok (P := Impl.MlDsa.AArch64.KeyGen.prims)
    (by decide) KeyGen.prims_ok.unpackT1 L hc) fun u ⟨hu, h24, hp⟩ => ?_)
  rw [← hu.pa (p := (.x26, p.pkLen + 1024 * i)) (show Reg.x26 ∈ keptRegs by decide)] at hp
  refine WP.mono (transform_ok (by decide) KeyGen.prims_ok.ntt (L.post hu) hi hp)
    fun t ⟨ht, ht24, htp⟩ => ?_
  refine ⟨hu.trans ht (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact show Reg.x26 ∈ keptRegs by decide
      · exact show Reg.x28 ∈ keptRegs by decide)
    (by simp) (by simp), ht24.trans h24, ?_⟩
  rwa [hu.pa (p := (.x26, p.pkLen + 1024 * i)) (show Reg.x26 ∈ keptRegs by decide)] at htp

end VG.Proof.MlDsa.AArch64.PreparedKey
