module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Data
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Shape
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.HalveOctets
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages

/-! ### `Ffdh.X86_64.ParameterCandidate.Halve`, which only this module used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.HalveByte`, which only this module used -/

section

/-! # FFDH parameter candidates on x86-64: one byte of q -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.ParameterCandidate

private theorem half_or (b : Byte) {carry : Nat} (hc : carry ≤ 1) :
    b.toNat / 2 ||| 128 * carry = b.toNat / 2 + 128 * carry := by
  have hb := b.isLt
  have he : carry = 0 ∨ carry = 1 := by omega_using [hc]
  rcases he with rfl | rfl
  · simp
  · simpa only [Nat.mul_one] using Nat.or_two_pow_eq_add_of_lt (show b.toNat / 2 < 2 ^ 7 by omega_using [])

theorem half_machine (b : Byte) {carry : Nat} (hc : carry ≤ 1) :
    (((b.setWidth 64) >>> 1) ||| BitVec.ofNat 64 (128 * carry)).setWidth 8 = halfByte carry b := by
  have hb := b.isLt
  apply BitVec.eq_of_toNat_eq
  rw [halfByte_val hc]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  rw [Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega_using []),
    Nat.mod_eq_of_lt (show 128 * carry < 2 ^ 64 by omega_using [hc]), half_or b hc,
    Nat.mod_eq_of_lt (show b.toNat / 2 + 128 * carry < 2 ^ 8 by omega_using [hc])]

theorem carry_machine (b : Byte) :
    ((b.setWidth 64 &&& 1) <<< 7) = BitVec.ofNat 64 (128 * (b.toNat % 2)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    show (1 : BitVec 64).toNat = 1 from rfl]
  rw [Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by have := b.isLt; omega_using []), Nat.and_one_is_mod]
  congr 1
  omega_using []

theorem halveByte_ok {s : State} {op : Addr} {j k carry : Nat} {b : Byte}
    (hj : j < k) (hk : k < 2 ^ 31) (hc : carry ≤ 1)
    (hp : s.gpr .r10 = off op j) (hn : s.gpr .rcx = BitVec.ofNat 64 (k - j))
    (hcarry : s.gpr .r8 = BitVec.ofNat 64 (128 * carry))
    (hrd : InRegions (s.rd ++ s.wr) (off op j) 1) (hwr : InRegions s.wr (off op j) 1)
    (hb : s.mem (off op j) = b) :
    WP isa (.block halveByte) s fun t =>
      t.mem = s.mem.writeW (off op j) (halfByte carry b) ∧
      t.gpr .r10 = off op (j + 1) ∧ t.gpr .rcx = BitVec.ofNat 64 (k - (j + 1)) ∧
      t.gpr .r8 = BitVec.ofNat 64 (128 * (b.toNat % 2)) ∧
      t.zf = some (decide (j + 1 = k)) ∧ Keep [.rax, .rdx, .r8, .r10, .rcx] s t := by
  have hsub : BitVec.ofNat 64 (k - j) - 1 = BitVec.ofNat 64 (k - (j + 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    omega_using [hj]
  have hz : (BitVec.ofNat 64 (k - (j + 1)) == 0) = decide (j + 1 = k) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at this
      omega_using [hj, hk, this]
    · intro h
      rw [h, Nat.sub_self]
      rfl
  have hp' : off op j + 1 = off op (j + 1) := by
    simp only [off, BitVec.add_assoc, ofNat_add_one]
  refine WP.mono (WP.keep [.rax, .rdx, .r8, .r10, .rcx]
    (Q := fun t => t.mem = s.mem.writeW (off op j) (halfByte carry b) ∧
      t.gpr .r10 = off op (j + 1) ∧ t.gpr .rcx = BitVec.ofNat 64 (k - (j + 1)) ∧
      t.gpr .r8 = BitVec.ofNat 64 (128 * (b.toNat % 2)) ∧ t.zf = some (decide (j + 1 = k)))
    (by unfold halveByte; xrun [State.ea, at0, hp, hn, hcarry,
      show off op j + BitVec.ofInt 64 0 = off op j from by simp,
      hrd, hwr, hb, half_machine b hc, carry_machine b, hsub, hz, hp']) rfl)
    fun _ ⟨⟨hm, hp', hn', hc', hz'⟩, hkeep⟩ => ⟨hm, hp', hn', hc', hz', hkeep⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end


/-! # FFDH parameter candidates on x86-64: in-place byte halving -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.ParameterCandidate

structure HalfInv (s₀ : State) (op : Addr) (bs : List Byte) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .rdx, .r8, .r10, .rcx] s₀ t
  ptr : t.gpr .r10 = off op j
  count : t.gpr .rcx = BitVec.ofNat 64 (bs.length - j)
  carry : t.gpr .r8 = BitVec.ofNat 64 (128 * carryAt 0 bs j)
  bytes : ∀ i < j, t.mem (off op i) = (halfOctets 0 bs).getD i 0
  frame : ∀ a, (∀ i < j, a ≠ off op i) → t.mem a = s₀.mem a

theorem halfStep_ok {s₀ t : State} {op : Addr} {bs : List Byte} {j : Nat}
    (hk : bs.length < 2 ^ 31) (hj : j < bs.length)
    (hwr : ∀ i < bs.length, InRegions s₀.wr (off op i) 1)
    (hb : ∀ i < bs.length, s₀.mem (off op i) = bs.getD i 0)
    (h : HalfInv s₀ op bs j t) : WP isa (.block halveByte) t fun u =>
      u.zf = some (decide (j + 1 = bs.length)) ∧ HalfInv s₀ op bs (j + 1) u := by
  have hwr' : InRegions t.wr (off op j) 1 := by rw [h.keep.2.2]; exact hwr j hj
  have hrd' : InRegions (t.rd ++ t.wr) (off op j) 1 :=
    let ⟨r, hr, hc⟩ := hwr'; ⟨r, List.mem_append_right _ hr, hc⟩
  have hb' : t.mem (off op j) = bs.getD j 0 := by
    rw [h.frame _ (fun i hi => out_ne (by omega_using [hk, hj]) (by omega_using [hk, hj, hi]) (by omega_using [hi]))]
    exact hb j hj
  refine WP.mono (halveByte_ok hj hk (carryAt_le (by decide) bs j) h.ptr h.count h.carry hrd' hwr' hb')
    fun u ⟨hm, hp, hn, hc, hz, k⟩ => ?_
  refine ⟨hz, ⟨(h.keep.trans k).mono (by decide), hp, hn, ?_, ?_, ?_⟩⟩
  · rw [carryAt_next 0 hj]
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] using hc
  · intro i hi
    rw [hm, WriteBytes.writeW8_apply]
    by_cases he : i = j
    · subst he
      rw [ite_eq_left rfl]
      have hhl : i < (halfOctets 0 bs).length := by rw [halfOctets_length]; exact hj
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
        List.getElem?_eq_getElem hhl, Option.getD_some] using (halfOctets_get 0 hj).symm
    · rw [ite_eq_right (out_ne (by omega_using [hk, hj, hi]) (by omega_using [hk, hj]) he)]
      exact h.bytes i (by omega_using [hi, he])
  · intro a ha
    rw [hm, WriteBytes.writeW8_apply, ite_eq_right (ha j (by omega_using []))]
    exact h.frame a (fun i hi => ha i (by omega_using [hi]))

theorem halfLoop_ok {s : State} {op : Addr} {bs : List Byte}
    (hk1 : 1 ≤ bs.length) (hk : bs.length < 2 ^ 31)
    (hp : s.gpr .r10 = op) (hn : s.gpr .rcx = BitVec.ofNat 64 bs.length) (hc : s.gpr .r8 = 0)
    (hwr : ∀ i < bs.length, InRegions s.wr (off op i) 1)
    (hb : ∀ i < bs.length, s.mem (off op i) = bs.getD i 0) :
    WP isa (.loop (.block halveByte) .ne) s (HalfInv s op bs bs.length) :=
  wp_upto (a := 0) (by omega_using [hk1]) (HalfInv s op bs)
    (fun j _ hj t ht => halfStep_ok hk hj hwr hb ht) (fun _ h => h)
    ⟨Keep.refl _ _, by rw [hp]; simp, by rw [hn, Nat.sub_zero], by simpa [carryAt] using hc,
      fun i hi => by omega, fun _ _ => rfl⟩

/-- Form q in place, preserving every byte outside the candidate buffer. -/
theorem halve_ok {s : State} {op : Addr} {bs : List Byte}
    (hk1 : 1 ≤ bs.length) (hk : bs.length < 2 ^ 31)
    (hp : s.gpr .rdi = op) (hn : s.gpr .rcx = BitVec.ofNat 64 bs.length)
    (hwr : ∀ i < bs.length, InRegions s.wr (off op i) 1)
    (hb : ∀ i < bs.length, s.mem (off op i) = bs.getD i 0) :
    WP isa halve s fun t => Spec.Rsa.bytesAt t.mem op bs.length = halfOctets 0 bs ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op bs.length) = Spec.Rsa.os2ip bs / 2 ∧
      (∀ a, (∀ i < bs.length, a ≠ off op i) → t.mem a = s.mem a) ∧
      Keep [.rax, .rdx, .r8, .r10, .rcx] s t := by
  unfold halve
  refine WP.seq (WP.mono (WP.keep [.r10, .r8] (Q := fun u => u.gpr .r10 = op ∧ u.gpr .r8 = 0 ∧ u.mem = s.mem)
    (by xrun [hp]) rfl) fun u ⟨⟨hpu, hcu, hmu⟩, ku⟩ => ?_)
  refine WP.mono (halfLoop_ok hk1 hk hpu ((ku.gpr (by decide)).trans hn) hcu
    (fun i hi => by rw [ku.2.2]; exact hwr i hi)
    (fun i hi => by rw [hmu]; exact hb i hi)) fun t ht => ?_
  have he : Spec.Rsa.bytesAt t.mem op bs.length = halfOctets 0 bs := by
    apply List.ext_getElem
    · rw [bytesAt_length, halfOctets_length]
    · intro i hi hi'
      have hil : i < bs.length := by rwa [bytesAt_length] at hi
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      change t.mem (off op i) = (halfOctets 0 bs)[i]
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some] using ht.bytes i hil
  exact ⟨he, by rw [he, halfOctets_zero], (fun a ha => (ht.frame a ha).trans (congrFun hmu a)),
    (ku.trans ht.keep).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end


/-! # FFDH parameter generation on x86-64: derive q in the output buffer -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

theorem halveOutput_ok {p : CandidateP} {used : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B)
    (hp : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem p.op p.k) = p.P) :
    WP isa halveOutput s fun t => CandidateTape p used t ∧ t.gpr .rdi = p.B ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem p.op p.k) = p.Q ∧
      CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep mmRegs s t := by
  let bs := Spec.Rsa.bytesAt s.mem p.op p.k
  have hlen : bs.length = p.k := bytesAt_length _ _ _
  have hrd : ∀ j < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * j)) 8 :=
    fun j hj => h.base.scr.ld (by omega_using [hj, h.base.header_room])
  have hOut := h.base.hdr (oOut, p.op) (by simp [CandidateP.headers])
  have hLen := h.base.hdr (oLen, BitVec.ofNat 64 p.k) (by simp [CandidateP.headers])
  unfold halveOutput
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rbp, .rax, .rcx, .rdi] (Q := fun u =>
    u.gpr .rbp = p.B ∧ u.gpr .rdi = p.op ∧ u.gpr .rcx = BitVec.ofNat 64 p.k ∧ u.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hOut, hLen, hrd oOut (by decide), hrd oLen (by decide)]) rfl)
    fun u ⟨⟨hbp, hop, hcx, hm⟩, k⟩ => ?_)
  refine WP.seq (WP.mono (halve_ok (bs := bs) (by omega_using [hlen, h.base.widths.1])
    (by omega_using [hlen, h.base.widths.2]) hop (by rw [hlen]; exact hcx)
    (fun i hi => by rw [k.2.2]; exact h.base.out.wr i (by omega_using [hlen, hi]))
    (fun i hi => by
      rw [hm]
      have hb := bytesAt_read s.mem p.op (by omega_using [hlen, hi] : i < p.k)
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using hb))
    fun v ⟨_, hv, hf, kv⟩ => ?_)
  have hbpv : v.gpr .rbp = p.B := (kv.gpr (by decide)).trans hbp
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = p.B ∧ t.mem = v.mem)
    (by xrun [hbpv]) rfl) fun t ⟨⟨hdt, hmt⟩, kt⟩ => ?_
  have kk : Keep (.rdi :: mmRegs) s t := ((k.trans kv).trans kt).mono (by decide)
  have kk' := keep_modulus kk (hdt.trans hdi.symm)
  have hframe : ∀ a, (∀ i < p.k, a ≠ off p.op i) → t.mem a = s.mem a := by
    intro a ha
    rw [hmt, hf a (by simpa only [hlen] using ha), hm]
  obtain ⟨ht, hs, hfr⟩ := h.after_bytes hframe kk' (by decide)
  have hodd : p.P % 2 = 1 := (VG.Proof.Ffdh.ParameterCandidate.candidate_shape
    (by omega_using [h.base.bits1]) (Spec.Rsa.os2ip p.prefix)).1
  have hhalf : p.P / 2 = p.Q := by unfold CandidateP.Q; omega_using [hodd]
  refine ⟨ht, hdt, ?_, hs, hfr, kk'⟩
  rw [hmt]
  simpa only [hlen, bs, hp, hhalf] using hv

end VG.Proof.Ffdh.X86_64.ParameterCandidate
