module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.QCandidate
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashResources
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.X86.Generation.Hash
import VerifiedGarbage.Proof.Dsa.X86.Generation.Shape

/-! # Native subgroup candidates match the existing DSA specification -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86
open VG.Impl.Dsa.X86.Generation
open VG.Proof.Ffdh.ParameterCandidate (shapedOctets)

theorem qCandidate_ok {H : Hash} (K : HashOK H) {s : State} {input output scratch : BitVec 32} (len : Nat)
    (R : HashResources K input output scratch len s) (hn : 2 ≤ len) (hD : H.D = len) (hF : H.F = len)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * len) bs)
    (hashLen : ∀ bs, (Spec.Dsa.seedHash (8 * len) bs).length = len)
    (si : s.gpr .esi = input) (di : s.gpr .edi = output) (bp : s.gpr .ebp = scratch) :
    WP isa (qCandidate H len) s fun t =>
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem (output.setWidth 64) len) =
        Spec.Dsa.qCandidate (8 * len) (Spec.Sha256.bytesAt s.mem (input.setWidth 64) len) ∧
      Frame [⟨(scratch + 512#32).setWidth 64, H.S⟩, ⟨output.setWidth 64, H.F⟩,
        ⟨scratch.setWidth 64, K.Wb⟩, stk s] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx] s t := by
  unfold qCandidate
  refine WP.seq (WP.mono (seedHash_ok K len R si di bp) fun u ⟨hashed, frame, keeps⟩ => ?_)
  let bs := Spec.Dsa.seedHash (8 * len) (Spec.Sha256.bytesAt s.mem (input.setWidth 64) len)
  have bl : bs.length = len := hashLen _
  rw [hD, hF, hash] at hashed
  have written : Spec.Rsa.bytesAt u.mem (output.setWidth 64) len = bs := by
    rw [List.take_of_length_le (by simp only [Spec.Sha256.bytesAt, List.length_map, List.length_range]; exact Nat.le_refl _)] at hashed
    exact hashed
  have fit : output.toNat + bs.length ≤ 2 ^ 32 := by rw [bl, ← hF]; exact R.outputBound
  have writable : ∀ i < bs.length, InRegions u.wr (off (output.setWidth 64) i) 1 := by
    intro i hi
    rw [keeps.2.2]
    apply R.finWr
    exact ⟨⟨output.setWidth 64, H.F⟩, by simp, Offset.contains_base _ (by rw [hF, ← bl]; exact hi) (by have := R.lenBound; omega)⟩
  have bytes : ∀ i < bs.length, u.mem (off (output.setWidth 64) i) = bs.getD i 0 := by
    intro i hi
    have e := congrArg (fun xs : List Byte => xs[i]?) written
    simpa only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range (by omega : i < len),
      Option.map_some, List.getElem?_eq_getElem hi, Option.some.injEq, List.getD_eq_getElem?_getD,
      Option.getD_some] using e
  have step := shape_ok (by omega : 2 ≤ bs.length) ((keeps.1 _ (by decide)).trans di) fit
    (fun i hi => by
      obtain ⟨r, hr, hc⟩ := writable i hi
      exact ⟨r, List.mem_append_right _ hr, hc⟩) writable bytes
  rw [bl] at step
  refine WP.mono step fun t ⟨out, framed, kept⟩ => ⟨?_, ?_, keeps.trans (kept.mono (by decide))⟩
  · rw [out]
    exact VG.Proof.Dsa.Generation.qCandidate_octets (by omega) _ (by rw [hashLen])
  · refine frame.trans (framed.mono ?_)
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    rw [hF]; simp
end VG.Proof.Dsa.X86.Generation
