module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeContext
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeDispatch
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeChecks
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeWrite
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Encode a digest once the lengths of its hash function are chosen -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Bignum VG.Proof.Bignum.X86 VG.WriteBytes
open VG.Impl.RsaPkcs1Sig.X86 Spec.RsaPkcs1Sig

/-- `checked` once `lens h` has set the lengths of a hash function `h`
named by the number. -/
theorem checked_ok {s0 s1 : State} {x : BitVec 32} {k : Nat} (pre : EPre s0 x k)
    (h : Hash) (id : Hash.ofId x.toNat = some h) (k1 : Keeps [.eax, .ebx] s0 s1)
    (mem1 : s1.mem = s0.mem) (info : s1.gpr .ebx = BitVec.ofNat 32 (h.prefix.length + h.len))
    (len : s1.gpr .eax = BitVec.ofNat 32 h.len) :
    WP isa checked s1 (EPost s0 x k) := by
  let dl := (s0.gpr .ebp).toNat
  let H := Spec.Rsa.bytesAt s0.mem (byteAddr (s0.gpr .esi)) dl
  have hlen : H.length = dl := bytesAt_length _ _ _
  have hfail : ∀ u, Keeps clob s0 u → u.mem = s0.mem → Spec.RsaPkcs1Sig.encode h H k = none →
      WP isa fail u (EPost s0 x k) := by
    intro u keep mem none
    apply refuse_ok keep mem
    simpa only [encodeId, id, Option.bind_some] using none
  unfold checked
  refine WP.seq (WP.mono (cmpLen_ok s1) fun s2 ⟨f2, zf⟩ => ?_)
  have k2 : Keeps [.eax, .ebx] s0 s2 := k1.trans (f2.keeps _)
  have mem2 : s2.mem = s0.mem := f2.2.1.trans mem1
  have dlreg : s1.gpr .ebp = BitVec.ofNat 32 dl := by
    rw [k1.1 _ (by decide)]
    simp only [dl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  by_cases matchLen : dl = h.len
  · refine WP.ite false (by simp [eval, zf, dlreg, len, matchLen]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (cmpK_ok s2) fun s3 ⟨k3, mem3, cf⟩ => ?_)
    have info2 : s2.gpr .ebx = BitVec.ofNat 32 (h.prefix.length + h.len) := by rw [f2.1]; exact info
    have flag : s3.cf = some (decide (k < h.prefix.length + h.len + 11)) := by
      rw [cf, k2.1 .ecx (by decide), pre.length, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := pre.bound; omega), info2, add11_toNat (prefix_length_le h)]
    have kept : Keeps [.eax, .ebx] s0 s3 := k2.widen k3
    have mem : s3.mem = s0.mem := mem3.trans mem2
    by_cases short : k < h.prefix.length + h.len + 11
    · refine WP.ite true (by simp [eval, flag, short]) (fun _ => hfail s3 (kept.mono (by decide)) mem ?_) (by simp)
      simp only [Spec.RsaPkcs1Sig.encode, digestInfo, List.length_append, hlen, matchLen]
      simp [short]
    · refine WP.ite false (by simp [eval, flag, short]) (by simp) (fun _ => ?_)
      have digestLen : s0.gpr .ebp = BitVec.ofNat 32 h.len := by
        rw [← matchLen]
        simp only [dl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      have ready : WPre s0 x h k s3 := {
        keep := kept
        mem := mem
        info := (k3.1 .ebx (by decide)).trans info2
        digest := digestLen
        hash := pre.hash
        id := id
        length := pre.length
        room := by omega
        bound := pre.bound }
      refine WP.mono (write_ok pre.buf ready (matchLen ▸ pre.digest)) fun t ⟨ax, written⟩ => ?_
      refine ⟨written.rest, ?_⟩
      have encoded : encodeId x H k = some
          ([0x00, 0x01] ++ List.replicate (k - (h.prefix.length + h.len) - 3) 0xff ++
            [0x00] ++ h.prefix ++ Spec.Rsa.bytesAt s0.mem (byteAddr (s0.gpr .esi)) h.len) := by
        simp only [encodeId, id, Option.bind_some, Spec.RsaPkcs1Sig.encode, digestInfo,
          List.length_append, hlen, matchLen]
        simp [short, H, dl, matchLen, List.append_assoc]
      change EOut s0 t (encodeId x H k)
      rw [encoded]
      exact ⟨ax, written.mem⟩
  · have different : BitVec.ofNat 32 dl ≠ BitVec.ofNat 32 h.len := by
      intro eq
      have nat := congrArg BitVec.toNat eq
      have dlbound : dl < 2 ^ 32 := (s0.gpr .ebp).isLt
      have hashbound := prefix_length_le h
      simp only [BitVec.toNat_ofNat] at nat
      omega
    refine WP.ite true (by simp [eval, zf, dlreg, len, different])
      (fun _ => hfail s2 (k2.mono (by decide)) mem2 ?_) (by simp)
    simp [Spec.RsaPkcs1Sig.encode, hlen, matchLen]

/-- `checked` once `noLens` has set the lengths for a number that names no
hash function: both checks fail but the first one, which may pass, and the
second fails since `k ≤ 1024 < 2048 + 11`. -/
theorem unchecked_ok {s0 s1 : State} {x : BitVec 32} {k : Nat} (pre : EPre s0 x k)
    (id : Hash.ofId x.toNat = none) (k1 : Keeps [.eax, .ebx] s0 s1)
    (mem1 : s1.mem = s0.mem) (info : s1.gpr .ebx = 2048) :
    WP isa checked s1 (EPost s0 x k) := by
  have none : encodeId x (Spec.Rsa.bytesAt s0.mem (byteAddr (s0.gpr .esi)) (s0.gpr .ebp).toNat) k =
      none := by
    simp only [encodeId, id, Option.bind_none]
  unfold checked
  refine WP.seq (WP.mono (cmpLen_ok s1) fun s2 ⟨f2, zf⟩ => ?_)
  have k2 : Keeps [.eax, .ebx] s0 s2 := k1.trans (f2.keeps _)
  have mem2 : s2.mem = s0.mem := f2.2.1.trans mem1
  refine WP.ite (!(s1.gpr .ebp == s1.gpr .eax)) (by simp [eval, zf])
    (fun _ => refuse_ok (k2.mono (by decide)) mem2 none) fun _ => ?_
  refine WP.seq (WP.mono (cmpK_ok s2) fun s3 ⟨k3, mem3, cf⟩ => ?_)
  have flag : s3.cf = some true := by
    rw [cf, k2.1 .ecx (by decide), pre.length, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := pre.bound; omega), f2.1, info]
    have := pre.bound
    simp only [show (2048 + 11 : BitVec 32).toNat = 2059 from rfl, Option.some.injEq,
      decide_eq_true_eq]
    omega
  refine WP.ite true (by simp [eval, flag]) (fun _ => refuse_ok ((k2.widen k3).mono (by decide))
    (mem3.trans mem2) none) (by simp)

end VG.Proof.RsaPkcs1Sig.X86
