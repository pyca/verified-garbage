module

public import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
public import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig

/-!
# `vg_chacha20_poly1305_open_to` with its working space, and the locality of its contract

`openToScratchContract n` is `openToContract` with an `n`-word `work`
buffer appended, whatever it holds, as `Scratch.lean`'s are for `seal` and
`open`. The facts that `withStackScratch…`'s frames need of `openToContract`
(`Spec/ChaCha20Poly1305/OutOfPlace.lean`), as `Scratch.lean` gives them of
`openZeroContract`: its precondition reads no memory (`openToPre_local`),
its postcondition reads the memory on entry only within the key, the nonce,
the additional data, the source and the tag (`openToPost_local`) and the
memory on return only within the destination (`openToPost_out`), and its
leak reads the memory only within its buffers (`openToLeak_local`).
-/
-- separate module: every target's `open_to` imports it, and none of `Scratch.lean`'s importers need it

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305

open VG.Spec.ChaCha20Poly1305

/-- `vg_chacha20_poly1305_open_to` with `work: *mut [u64; n]`. -/
def openToScratchSig (n : Nat) : Sig where
  params := [("key", .array false .u8 32), ("nonce", .array false .u8 12),
    ("aad", .slice false .u8 "aad_len"), ("src", .slice false .u8 "len"),
    ("dst", .slice true .u8 "dst_len"), ("tag", .array false .u8 16), ("work", .array true .u64 n)]
  ret := some .u32

/-- `openToContract`, whatever `work` is. -/
def openToScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (openToScratchSig n).contract A
    (pre := fun key nonce aad aadLen src len dst dstLen tag _work =>
      openToPre A.ptrBits key nonce aad aadLen src len dst dstLen tag)
    (post := fun key nonce aad aadLen src len dst dstLen tag _work =>
      openToPost A.ptrBits key nonce aad aadLen src len dst dstLen tag)
    (writeArgs := true) (stack := stack)
    (leak := some fun key nonce aad aadLen src len dst dstLen tag _work =>
      openToLeak A.ptrBits key nonce aad aadLen src len dst dstLen tag)

variable (pb : Nat)

theorem openToPost_curry (key nonce aad al src len dst dl tag : BitVec 64) (m m' : Mem) (r : BitVec 32) :
    Curry.apply (openToSig.words pb) (openToPost pb) [key, nonce, aad, al, src, len, dst, dl, tag] m m' r =
      openZeroPostB (Spec.Poly1305.bytesAt m key 32) (Spec.Poly1305.bytesAt m nonce 12)
        (Spec.Poly1305.bytesAt m aad (al.setWidth pb).toNat)
        (Spec.Poly1305.bytesAt m src (len.setWidth pb).toNat) (Spec.Poly1305.bytesAt m tag 16)
        (Spec.Poly1305.bytesAt m' dst (len.setWidth pb).toNat) (len.setWidth pb).toNat r := rfl

theorem openToLeak_curry (key nonce aad al src len dst dl tag : BitVec 64) (m : Mem) :
    Curry.apply (openToSig.words pb) (openToLeak pb) [key, nonce, aad, al, src, len, dst, dl, tag] m =
      [if (decrypt (Spec.Poly1305.bytesAt m key 32) (Spec.Poly1305.bytesAt m nonce 12)
        (Spec.Poly1305.bytesAt m aad (al.setWidth pb).toNat)
        (Spec.Poly1305.bytesAt m src (len.setWidth pb).toNat)
        (Spec.Poly1305.bytesAt m tag 16)).isSome then 1 else 0] := rfl

/-- The nine arguments, one by one. -/
theorem nine {α : Type} {vs : List α} (h : vs.length = 9) :
    ∃ a b c d e f g i j, vs = [a, b, c, d, e, f, g, i, j] := by
  match vs, h with
  | [a, b, c, d, e, f, g, i, j], _ => exact ⟨a, b, c, d, e, f, g, i, j, rfl⟩

theorem openToSig_length : (openToSig.words pb).length = 9 := rfl

theorem openToPre_local : ∀ vs (m₁ m₂ : Mem), vs.length = (openToSig.words pb).length →
    (∀ b ∈ Sig.bufs openToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openToSig.words pb) (openToPre pb) vs m₁ →
      Curry.apply (openToSig.words pb) (openToPre pb) vs m₂ := by
  intro vs m₁ m₂ hlen _ h
  obtain ⟨_, _, _, _, _, _, _, _, _, rfl⟩ := nine (hlen.trans (openToSig_length pb))
  exact h

theorem openToPost_local : ∀ vs m₁ m₂ m' r, vs.length = (openToSig.words pb).length →
    (∀ b ∈ Sig.bufs openToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openToSig.words pb) (openToPost pb) vs m₁ m' r →
      Curry.apply (openToSig.words pb) (openToPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨key, nonce, aad, al, src, len, dst, dl, tag, rfl⟩ := nine (hlen.trans (openToSig_length pb))
  simp only [openToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  replace h := Eq.mp (openToPost_curry pb key nonce aad al src len dst dl tag m₁ m' r) h
  refine Eq.mpr (openToPost_curry pb key nonce aad al src len dst dl tag m₂ m' r) ?_
  rw [bytesAt_congr (agree_of hb.1), bytesAt_congr (agree_of hb.2.1),
    bytesAt_congr_len (agree_of hb.2.2.1), bytesAt_congr_len (p := src) (agree_of hb.2.2.2.1),
    bytesAt_congr (p := tag) (agree_of hb.2.2.2.2.2)]
  exact h

/-- With the precondition (`dst_len = len`), the postcondition reads the
memory on return only within the destination. -/
theorem openToPost_out : ∀ vs m m₁ m₂ r, vs.length = (openToSig.words pb).length →
    Curry.apply (openToSig.words pb) (openToPre pb) vs m →
    (∀ b ∈ Sig.bufs openToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openToSig.words pb) (openToPost pb) vs m m₁ r →
      Curry.apply (openToSig.words pb) (openToPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hpre hb h
  obtain ⟨key, nonce, aad, al, src, len, dst, dl, tag, rfl⟩ := nine (hlen.trans (openToSig_length pb))
  simp only [openToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hdl : (dl.setWidth pb).toNat = (len.setWidth pb).toNat := hpre.1
  replace h := Eq.mp (openToPost_curry pb key nonce aad al src len dst dl tag m m₁ r) h
  refine Eq.mpr (openToPost_curry pb key nonce aad al src len dst dl tag m m₂ r) ?_
  have hd := hb.2.2.2.2.1
  rw [bytesAt_congr (p := dst) (n := (len.setWidth pb).toNat) fun i hi => agree_of hd i (by
    rw [← hdl, BitVec.toNat_setWidth] at hi
    exact Nat.lt_of_lt_of_le hi (Nat.mod_le _ _))]
  exact h

theorem openToLeak_local : Sig.LeakLocal pb openToSig (some (openToLeak pb)) := by
  intro vs m₁ m₂ hlen hb
  obtain ⟨key, nonce, aad, al, src, len, dst, dl, tag, rfl⟩ := nine (hlen.trans (openToSig_length pb))
  simp only [openToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  rw [openToLeak_curry, openToLeak_curry, bytesAt_congr (fun i hi => (agree_of hb.1 i hi).symm),
    bytesAt_congr (fun i hi => (agree_of hb.2.1 i hi).symm),
    bytesAt_congr_len (fun i hi => (agree_of hb.2.2.1 i hi).symm),
    bytesAt_congr_len (p := src) (fun i hi => (agree_of hb.2.2.2.1 i hi).symm),
    bytesAt_congr (p := tag) (fun i hi => (agree_of hb.2.2.2.2.2 i hi).symm)]

end VG.Proof.ChaCha20Poly1305
