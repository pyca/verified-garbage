module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMessageWrite

/-! # Write a public PRF label after its two-byte counter -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem messageLabel_ok {g : Geometry} {bs : Fin 9 → List Byte} {s0 : State} {xs : List Byte}
    (ptr : s0.gpr .edi = g.workspace + BitVec.ofNat 32 sMsg) :
    ∀ (vs : List Nat) (n : Nat) (s : State), MessageWritten g bs s0 xs (n + 2) s →
      n + vs.length + 2 ≤ 16 →
      (∀ j < vs.length, xs.getD (n + 2 + j) 0 = BitVec.ofNat 8 (vs.getD j 0)) →
      WP isa (.block ((vs.zipIdx n).flatMap fun vi => putByte (vi.2 + 2) vi.1)) s
        (MessageWritten g bs s0 xs (n + vs.length + 2)) := by
  intro vs
  induction vs with
  | nil =>
    intro n s h _ _
    simpa only [List.zipIdx_nil, List.flatMap_nil, List.length_nil, Nat.add_zero] using WP.block_nil h
  | cons v vs ih =>
    intro n s h bound bytes
    simp only [List.zipIdx_cons, List.flatMap_cons]
    rw [WP.block_append_iff]
    refine WP.mono (h.put ptr (by simp only [List.length_cons] at bound; omega)
      (by simpa only [Nat.add_zero, List.getD_cons_zero] using bytes 0 (by simp))) ?_
    intro t ht
    have ht' : MessageWritten g bs s0 xs (n + 1 + 2) t := by
      simpa only [show n + 2 + 1 = n + 1 + 2 by omega] using ht
    have tail := ih (n + 1) t ht' (by simp only [List.length_cons] at bound; omega)
      (fun j hj => by
        have next := bytes (j + 1) (by simp only [List.length_cons]; omega)
        simpa only [List.getD_cons_succ, show n + 2 + (j + 1) = n + 1 + 2 + j by omega] using next)
    simpa only [List.length_cons, show n + 1 + vs.length + 2 = n + (vs.length + 1) + 2 by omega] using tail

end VG.Proof.RsaPkcs1Enc.X86.Dec
