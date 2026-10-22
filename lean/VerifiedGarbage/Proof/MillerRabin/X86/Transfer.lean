module

public import VerifiedGarbage.Proof.MillerRabin.X86.Copy

/-! # Composing public pointer setup with the existing verified buffer copy -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Bignum.X86

def transferClobbers : List Reg := [.eax, .ebx, .esi, .edx, .ecx]

structure TransferResult (s : State) (src dst : BitVec 32) (n : Nat) (t : State) : Prop where
  value : t.mem.read (byteAddr dst) n = s.mem.read (byteAddr src) n
  dest : t.gpr .ebx = dst + BitVec.ofNat 32 n
  source : t.gpr .esi = src + BitVec.ofNat 32 n
  frame : Frame [⟨byteAddr dst, n⟩] s.mem t.mem
  keeps : Keeps transferClobbers s t

theorem TransferResult.bytes {s t : State} {src dst : BitVec 32} {n i : Nat}
    (h : TransferResult s src dst n t) (hi : i < n) :
    t.mem (byteAddr dst + BitVec.ofNat 64 i) = s.mem (byteAddr src + BitVec.ofNat 64 i) := by
  have e := congrArg (fun v : BitVec (8 * n) => v.extractLsb' (8 * i) 8) h.value
  rw [Mem.extractLsb'_read _ _ hi, Mem.extractLsb'_read _ _ hi] at e
  exact e

theorem ptr32_stack (sp : BitVec 32) (d : Nat) :
    sp + BitVec.ofNat 32 d = ptr32 (byteAddr sp) d := by
  apply BitVec.eq_of_toNat_eq
  simp only [ptr32, byteAddr, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.add_mod_mod]
  have h := sp.isLt
  omega

theorem transfer_ok {s : State} {src dst : BitVec 32} {n : Nat} {setup : List Instr}
    (positive : 0 < n) (small : n < 2 ^ 32)
    (srcFit : src.toNat + n ≤ 2 ^ 32) (dstFit : dst.toNat + n ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr src) n)
    (write : InRegions s.wr (byteAddr dst) n)
    (apart : Region.Disjoint ⟨byteAddr src, n⟩ ⟨byteAddr dst, n⟩)
    (prepare : WP isa (.block setup) s fun t =>
      Keeps transferClobbers s t ∧ t.mem = s.mem ∧
      t.gpr .esi = src ∧ t.gpr .ebx = dst ∧ t.gpr .ecx = BitVec.ofNat 32 n) :
    WP isa (.seq (.block setup) VG.Impl.Bignum.X86.copyBytes) s (TransferResult s src dst n) := by
  refine WP.seq (WP.mono prepare fun t ⟨K, mem, ps, pd, count⟩ => ?_)
  refine WP.mono (copyBuffers_ok positive small srcFit dstFit
    (by rw [K.2.1, K.2.2]; exact read) (by rw [K.2.2]; exact write) apart ps pd count) ?_
  rintro u ⟨V, D, S, F, R⟩
  rw [mem] at V F
  exact ⟨V, D, S, F, K.trans (R.mono (by decide))⟩

end VG.Proof.MillerRabin.X86
