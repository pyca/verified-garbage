module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Data
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH on x86-64: sampled bytes are the specified scalar -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.Spec.Rsa VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem Base.cut_length {p : GkP} {rb : List Byte} {s : X86_64.State} (h : Base p rb s) :
    (p.cut rb).length = p.k := by
  rw [KeyScalar.cut_length _ (by rw [h.rl]; exact h.ld_lt), h.rl]

theorem Base.xb_length {p : GkP} {rb : List Byte} {s : X86_64.State} (h : Base p rb s) :
    (p.xb rb).length = p.n := by rw [List.length_drop, h.cut_length]

/-- Skipping the known zero prefix preserves the sampled scalar's value. -/
theorem Base.sample_value {p : GkP} {rb : List Byte} {s : X86_64.State} (h : Base p rb s)
    (hm : p.mv = true) : os2ip (p.xb rb) = p.scalar rb := by
  rw [KeyScalar.os2ip_cut_drop]
  exact h.cutv hm

/-- The bound's cut is `scalarOfOctets`. -/
theorem GkP.bounded_cut {p : GkP} {rb : List Byte} (hb : p.Bounded) (hk : 64 ≤ p.k)
    (hd : p.dom.length = 2 * p.k ∨ p.dom.length = 3 * p.k) (hl : rb.length = p.k) (hm : p.mv = true) :
    os2ip (p.cut rb) = Spec.Ffdh.scalarOfOctets p.params rb := by
  have hh := valid_facts hm hk
  have hbl : p.bb.length = p.k := KeyScalar.bnd_length hd
  have hn : p.bb ≠ [] := by intro he; rw [he] at hbl; simp at hbl; omega
  have hbc : p.bc = p.bb[lead p.bb]'(lead_lt hn) := by
    simp only [GkP.bc, hb.1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (lead_lt hn), Option.getD_some]
  have hmv : (p.msk.setWidth 8).toNat = 2 ^ Spec.RsaKeyGen.bitLength p.bc.toNat - 1 := by
    rw [hb.2, BitVec.toNat_setWidth, smear64_value,
      Nat.mod_eq_of_lt (KeyScalar.smearN_lt _ p.bc.isLt), KeyScalar.smearN_eq _ p.bc.isLt]
  rw [show p.cut rb = KeyScalar.cut rb (lead p.bb) (p.msk.setWidth 8) by simp only [GkP.cut, hb.1]]
  exact KeyScalar.cut_eq (by omega) hd (fun _ => ⟨hh.1, hh.2.1⟩) hl (by rw [hmv, hbc])

/-- The full-width cut is the canonical encoding of the sampled scalar. -/
theorem Base.cut_i2osp {p : GkP} {rb : List Byte} {s : X86_64.State} (h : Base p rb s)
    (hm : p.mv = true) : p.cut rb = i2osp (p.scalar rb) p.k := by
  have hv : os2ip (p.cut rb) = p.scalar rb := by
    rw [← KeyScalar.os2ip_cut_drop rb p.ld (p.msk.setWidth 8)]
    exact h.sample_value hm
  have he := VG.Proof.Rsa.i2osp_os2ip (p.cut rb)
  rw [h.cut_length, hv] at he
  exact he.symm

end VG.Proof.Ffdh.X86_64.GenerateKey
