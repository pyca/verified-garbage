module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Prefix
public import VerifiedGarbage.Proof.Gcm.StreamTo
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.Gcm.Stream

/-! # GCM state after the optional contiguous POWER fused prefix -/

public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Gcm (Block blockAt blocksAt ctxH ctxCiph ctr32)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (Absorbed Ctr xorKs)
open VG.Proof.AesGcm.PPC64LE.DirectGather (prefixLen prefixBlocks prefixEq)

abbrev prefixAreas (s : State) (k : Nat) : List Region := [⟨s.gpr .r30+48,16⟩,⟨s.gpr .r30+16,16⟩,
  ⟨s.gpr .r27,k⟩,⟨s.gpr .r31+448,704⟩]

structure PrefixMath (s t : State) (H icb : Block) (x : List Byte) : Prop where
  data : let k := prefixLen (s.gpr .r23).toNat
    bytesAt t.mem (s.gpr .r27) k=xorKs (ctxCiph s.mem (s.gpr .r29) (s.gpr .r28).toNat) icb 0 (bytesAt s.mem (s.gpr .r19) k)
  ctr : Ctr t.mem (s.gpr .r30+48) (s.gpr .r30+64) (ctxCiph s.mem (s.gpr .r29) (s.gpr .r28).toNat) icb (prefixLen (s.gpr .r23).toNat)
  auth : Absorbed t.mem (s.gpr .r30+16) (s.gpr .r30+32) H (x++bytesAt t.mem (s.gpr .r27) (prefixLen (s.gpr .r23).toNat))
  frame : Frame (prefixAreas s (prefixLen (s.gpr .r23).toNat)) s.mem t.mem

theorem PrefixResult.math {s t : State} {H icb : Block} {x : List Byte} (q : PrefixResult s t)
    (cipher : Ctr s.mem (s.gpr .r30+48) (s.gpr .r30+64) (ctxCiph s.mem (s.gpr .r29) (s.gpr .r28).toNat) icb 0)
    (auth : Absorbed s.mem (s.gpr .r30+16) (s.gpr .r30+32) H x) (xa : x.length%16=0) (hh : ctxH s.mem (s.gpr .r29)=H) :
    PrefixMath s t H icb x := by
  let n := (s.gpr .r23).toNat
  by_cases small : n<512
  · have z : prefixLen (s.gpr .r23).toNat=0 := by change (if n<512 then 0 else _)=0;simp only [small,↓reduceIte]
    have e := q.effect
    change if n<512 then _ else _ at e
    simp only [small,↓reduceIte] at e
    constructor
    · simp [z,bytesAt,xorKs]
    · simpa only [e,z] using cipher
    · simpa [z,bytesAt,e] using auth
    · rw [e];exact Frame.refl _ _
  · have blocks : prefixBlocks (s.gpr .r23).toNat=fusedBlocks s := by
      change (if n<512 then 0 else 8*(n/128))=_;simp only [small,↓reduceIte];rfl
    have k := (prefixEq (s.gpr .r23).toNat).symm
    rw [blocks] at k
    have e := q.effect
    change if n<512 then _ else _ at e
    simp only [small,↓reduceIte] at e
    obtain ⟨u,mem,z⟩ := e
    have out : SplitBlocks.bufferOutput (called s)=ctr32 (ctxCiph s.mem (s.gpr .r29) (s.gpr .r28).toNat)
      (blockAt s.mem (s.gpr .r30+48)) (blocksAt s.mem (s.gpr .r19) (fusedBlocks s)) := by
      unfold SplitBlocks.bufferOutput
      change ctr32 _ _ (blocksAt _ _ ((fusedState s).gpr .r8).toNat)=_
      rw [count_eq];rfl
    have crypt := Proof.Gcm.ctr_wholeTo cipher (by decide) (z.data.trans out) z.counter
    have hash := z.hash
    rw [←z.data,Proof.Gcm.blocksAt_eq,hh] at hash
    constructor
    · rw [k,mem];exact crypt.1
    · rw [k,mem];simpa only [Nat.zero_add] using crypt.2
    · rw [k,mem]
      exact Proof.Gcm.absorb_whole auth xa (by simp [length_bytesAt]) hash
    · rw [k,mem];exact z.frame

end VG.Proof.AesGcm.PPC64LE.Contiguous
