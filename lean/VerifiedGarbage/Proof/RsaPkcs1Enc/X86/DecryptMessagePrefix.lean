module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMessageLabel

/-! # Encode the PRF counter and label -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt
open VG.Proof.RsaPkcs1Enc
open VG.Proof.RsaPkcs1Sig

theorem messagePrefix_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) {i L : Nat} (vs : List Nat)
    (ptr : s.gpr .edi = g.workspace + BitVec.ofNat 32 sMsg)
    (counter : s.gpr .ebx = BitVec.ofNat 32 i) (counterBound : i < 256)
    (room : vs.length + 4 ≤ 16) :
    WP isa (.block (putByte 0 0 ++ ([.store8 ⟨.edi, 1⟩ .bl] : List Instr) ++ putLabel vs)) s
      (MessageWritten g bs s (prfMessage i (vs.map (BitVec.ofNat 8)) L) (vs.length + 2)) := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono ((MessageWritten.start h (prfMessage i (vs.map (BitVec.ofNat 8)) L)).put ptr (by decide) (by
    simp only [prfMessage, i2osp_two_lt counterBound, List.cons_append, List.nil_append]
    rfl)) ?_
  intro a ha
  refine WP.mono (ha.store ptr (by decide : 1 < 16) .bl (by
    change (a.gpr .ebx).setWidth 8 = _
    rw [ha.keep.1 .ebx (by decide), counter, BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 32)]
    simp only [prfMessage, i2osp_two_lt counterBound, List.cons_append, List.nil_append]
    rfl)) ?_
  intro b hb
  have label := messageLabel_ok ptr vs 0 b hb (by omega) (fun j hj => by
    simp only [prfMessage, i2osp_two_lt counterBound, List.cons_append, List.nil_append]
    rw [show 0 + 2 + j = j + 2 by omega, List.getD_cons_succ, List.getD_cons_succ,
      ]
    simp only [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (l₁ := vs.map (BitVec.ofNat 8)) (l₂ := Spec.Rsa.i2osp (8 * L) 2) (by simpa only [List.length_map] using hj)]
    simp only [List.getElem?_map,
      List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some])
  simpa only [putLabel, Nat.zero_add] using label

end VG.Proof.RsaPkcs1Enc.X86.Dec
