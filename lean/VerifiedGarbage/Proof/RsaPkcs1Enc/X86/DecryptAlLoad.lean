module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Decrypt
public import VerifiedGarbage.Proof.Bignum.X86.ByteOps

/-! # Read an alternative-length candidate as two big-endian bytes -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem alLoad_ok {s : State} (p : Addr)
    (ptr0 : s.ea ⟨.esi, 0⟩ = p) (ptr1 : s.ea ⟨.esi, 1⟩ = p + 1)
    (read0 : InRegions (s.rd ++ s.wr) p 1) (read1 : InRegions (s.rd ++ s.wr) (p + 1) 1) :
    WP isa (.block alLoad) s fun t => t.mem = s.mem ∧ Keeps [.eax, .edx] s t ∧
      t.gpr .eax = BitVec.ofNat 32 (256 * (s.mem p).toNat) ∧
      t.gpr .edx = BitVec.ofNat 32 (s.mem (p + 1)).toNat := by
  unfold alLoad
  refine wp_loadByte ptr0 read0 fun a A => ?_
  have axA : a.gpr .eax = BitVec.ofNat 32 (s.mem p).toNat := by
    rw [A.gpr]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  refine wp_addS rfl fun b B _ => ?_
  have axB : b.gpr .eax = BitVec.ofNat 32 (2 * (s.mem p).toNat) := by
    rw [B.gpr, axA]
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  refine wp_addS rfl fun c C _ => ?_
  have axC : c.gpr .eax = BitVec.ofNat 32 (4 * (s.mem p).toNat) := by
    rw [C.gpr, axB]
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  refine wp_addS rfl fun d D _ => ?_
  have axD : d.gpr .eax = BitVec.ofNat 32 (8 * (s.mem p).toNat) := by
    rw [D.gpr, axC]
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  refine wp_addS rfl fun e E _ => ?_
  have axE : e.gpr .eax = BitVec.ofNat 32 (16 * (s.mem p).toNat) := by
    rw [E.gpr, axD]
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  refine wp_addS rfl fun f F _ => ?_
  have axF : f.gpr .eax = BitVec.ofNat 32 (32 * (s.mem p).toNat) := by
    rw [F.gpr, axE]
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  refine wp_addS rfl fun g G _ => ?_
  have axG : g.gpr .eax = BitVec.ofNat 32 (64 * (s.mem p).toNat) := by
    rw [G.gpr, axF]
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  refine wp_addS rfl fun h H _ => ?_
  have axH : h.gpr .eax = BitVec.ofNat 32 (128 * (s.mem p).toNat) := by
    rw [H.gpr, axG]
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  refine wp_addS rfl fun i I _ => ?_
  have axI : i.gpr .eax = BitVec.ofNat 32 (256 * (s.mem p).toNat) := by
    rw [I.gpr, axH]
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  have Ki : Keeps [.eax] s i := ((((((((A.keeps).trans B.keeps).trans C.keeps).trans D.keeps).trans E.keeps).trans F.keeps).trans G.keeps).trans H.keeps).trans I.keeps
  have Mi : i.mem = s.mem := I.mem.trans (H.mem.trans (G.mem.trans (F.mem.trans (E.mem.trans (D.mem.trans (C.mem.trans (B.mem.trans (A.mem))))))))
  refine wp_loadByte (by
    change (i.gpr .esi + BitVec.ofNat 32 1).setWidth 64 = p + 1
    rw [Ki.1 .esi (by decide)]
    exact ptr1) (by rw [Ki.2.1, Ki.2.2]; exact read1) fun t T => WP.block_nil ?_
  refine ⟨T.mem.trans Mi, (Ki.mono (by decide)).trans (T.keeps.mono (by decide)),
    by rw [T.other .eax (by decide)]; exact axI, ?_⟩
  rw [T.gpr, Mi]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

end VG.Proof.RsaPkcs1Enc.X86.Dec
