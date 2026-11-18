module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseData
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Core
public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Masks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Data
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
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

/-! ### `Ffdh.X86_64.ParameterCandidate.HalveOutput`, which the modules that import this one used -/

section

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

end

end

/-! ### `Ffdh.X86_64.ParameterCandidate.ShapeOriginal`, which the modules that import this one used -/

section

/-! # FFDH parameter generation on x86-64: reconstruct p from the original prefix -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

theorem shapeOriginal_ok {p : CandidateP} {used : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B) (havail : p.k ≤ p.rand.length) :
    WP isa shapeOriginal s fun t => CandidateTape p used t ∧ t.gpr .rdi = p.B ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem p.op p.k) = p.P ∧
      CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep mmRegs s t ∧
      (∀ j < 32, word t.mem p.B (8 * j) = word s.mem p.B (8 * j)) := by
  have hrd : ∀ j < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * j)) 8 :=
    fun j hj => h.base.scr.ld (by omega_using [hj, h.base.header_room])
  have hOut := h.base.hdr (oOut, p.op) (by simp [CandidateP.headers])
  have hRand := h.base.hdr (oRandStart, p.rp) (by simp [CandidateP.headers])
  have hLen := h.base.hdr (oLen, BitVec.ofNat 64 p.k) (by simp [CandidateP.headers])
  have hBits := h.base.hdr (oBits, BitVec.ofNat 64 p.bits) (by simp [CandidateP.headers])
  have hprefix : p.prefix.length = p.k := by simp only [CandidateP.prefix, List.length_take, Nat.min_eq_left havail]
  unfold shapeOriginal
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rbp, .rax, .rsi, .rcx, .rdx, .rdi] (Q := fun u =>
    u.gpr .rbp = p.B ∧ u.gpr .rdi = p.op ∧ u.gpr .rsi = p.rp ∧
    u.gpr .rcx = BitVec.ofNat 64 p.k ∧ u.gpr .rdx = BitVec.ofNat 64 p.bits ∧ u.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hOut, hRand, hLen, hBits,
      hrd oOut (by decide), hrd oRandStart (by decide), hrd oLen (by decide), hrd oBits (by decide)]) rfl)
    fun u ⟨⟨hbp, hop, hrp, hcx, hdx, hm⟩, k⟩ => ?_)
  have hsrc : Src u p.B p.Z p.rp p.prefix := source_take
    (h.base.rand.congrK (by rw [hm]; exact InScr.refl _ _ _) k) p.k
  refine WP.seq (WP.mono (shape_ok (Nat.le_trans (by decide) h.base.bits1) h.base.bits2 (hprefix.trans h.base.len) hrp hop
    (by rw [hprefix]; exact hcx) hdx hsrc.rd
    (fun i hi => by rw [k.2.2]; exact h.base.out.wr i (by omega_using [hprefix, hi]))
    (fun i hi => by
      rw [hsrc.val i hi]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some])
    (fun i hi j hj he => h.base.outRand j (by omega_using [hprefix, hj]) i
      (by omega_using [hprefix, havail, hi]) he.symm))
    fun v ⟨_, hv, hf, kv⟩ => ?_)
  have hbpv : v.gpr .rbp = p.B := (kv.gpr (by decide)).trans hbp
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = p.B ∧ t.mem = v.mem)
    (by xrun [hbpv]) rfl) fun t ⟨⟨hdt, hmt⟩, kt⟩ => ?_
  have kk : Keep (.rdi :: mmRegs) s t := ((k.trans kv).trans kt).mono (by decide)
  have kk' := keep_modulus kk (hdt.trans hdi.symm)
  have hframe : ∀ a, (∀ i < p.k, a ≠ off p.op i) → t.mem a = s.mem a := by
    intro a ha
    rw [hmt, hf a (by simpa only [hprefix] using ha), hm]
  obtain ⟨ht, hs, hfr⟩ := h.after_bytes hframe kk' (by decide)
  refine ⟨ht, hdt, ?_, hs, hfr, kk', ?_⟩
  · rw [hmt]
    simpa only [hprefix, CandidateP.P] using hv
  · intro j hj
    exact words_outside_bytes h.base.size64 hframe h.base.out.sep _
      (by omega_using [hj, h.base.header_room])

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! ### `Ffdh.X86_64.ParameterCandidate.Phase`, which only this module used -/

section

/-! # FFDH parameter generation on x86-64: per-modulus witness policy -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

def phaseMem (m : Mem) (O : Addr) (bits : Nat) (c : Checks) : Mem :=
  ((m.writeW (off O (8 * oWitnessBits)) (BitVec.ofNat 64 bits)).writeW
    (off O (8 * oWitnessLen)) (BitVec.ofNat 64 ((bits + 7) / 8))).writeW
    (off O (8 * oChecks)) (BitVec.ofNat 64 (checksCount c (Spec.Ffdh.primeChecks bits)))

/-- The threshold is checked against this modulus, including q's smaller width. -/
theorem phaseWidth_ok {s : State} {O : Addr} {bits : Nat}
    (hs : Scr s O 256) (hdi : s.gpr .rdi = O)
    (hb : bits < 2 ^ 32) (hbits : s.gpr .rdx = BitVec.ofNat 64 bits) (c : Checks) :
    WP isa (.block (phaseWidth c)) s fun t =>
      t.mem = phaseMem s.mem O bits c ∧ t.gpr .rax = off O 256 ∧ Keep [.rax, .rcx, .rdx] s t := by
  have hwr : ∀ j < 32, InRegions s.wr (off O (8 * j)) 8 := fun j hj => hs.st (by omega_arith)
  have hcf : decide ((BitVec.ofNat 64 bits).toNat <
      (BitVec.signExtend 64 (2049 : BitVec 32)).toNat) = decide (bits ≤ 2048) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    change decide (bits < 2049) = decide (bits ≤ 2048)
    exact decide_eq_decide.mpr (by omega_arith)
  have hchecks : (if !decide (bits ≤ 2048) then (128#32).setWidth 64 else (64#32).setWidth 64) =
      BitVec.ofNat 64 (Spec.Ffdh.primeChecks bits) := by
    by_cases h : bits ≤ 2048 <;> simp [Spec.Ffdh.primeChecks, h]
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t =>
    t.mem = phaseMem s.mem O bits c ∧ t.gpr .rax = off O 256) ?_ (by cases c <;> rfl))
    fun t ⟨⟨hm, ha⟩, k⟩ => ⟨hm, ha, k⟩
  cases c <;> simp only [phaseWidth, Checks.code, List.cons_append, List.nil_append, List.append_nil]
  · xrun [phaseWidth, Checks.code, phaseMem, checksCount, State.ea, hdr, hdi, hdrOff, hbits,
      hwr oWitnessBits (by decide), hwr oWitnessLen (by decide), hwr oChecks (by decide),
      shr3_w bits hb, hcf, cmov_reg_value, eval]
    constructor
    · congr 1
    · rfl
  · xrun [phaseWidth, Checks.code, phaseMem, checksCount, State.ea, hdr, hdi, hdrOff, hbits,
      hwr oWitnessBits (by decide), hwr oWitnessLen (by decide), hwr oChecks (by decide),
      shr3_w bits hb, hcf, cmov_reg_value, eval]
    constructor
    · rfl
    · rfl
  · xrun [phaseWidth, Checks.code, phaseMem, checksCount, State.ea, hdr, hdi, hdrOff, hbits,
      hwr oWitnessBits (by decide), hwr oWitnessLen (by decide), hwr oChecks (by decide),
      shr3_w bits hb, hcf, cmov_reg_value, eval]
    constructor
    · congr 1
      by_cases h : bits ≤ 2048 <;> simp [Spec.Ffdh.primeChecks, h]
    · rfl

theorem phaseMem_frame (m : Mem) (O : Addr) (bits : Nat) (c : Checks) :
    Frm O [(8 * oWitnessBits, 24)] m (phaseMem m O bits c) := by
  have hf (m : Mem) (d : Nat) (v : BitVec 64) (h1 : 8 * oWitnessBits ≤ d)
      (h2 : d + 8 ≤ 8 * oWitnessBits + 24) : Frm O [(8 * oWitnessBits, 24)] m (m.writeW (off O d) v) :=
    by
      have hd : d + 8 ≤ 2 ^ 64 := by
        have hh : 8 * oWitnessBits + 24 ≤ 2 ^ 64 := by decide
        omega_arith
      exact Frm.of_outside ((writeW_outside m O (d := d) v hd).mono h1 h2) (by simp)
  unfold phaseMem
  exact (hf m (8 * oWitnessBits) (BitVec.ofNat 64 bits) (by decide) (by decide)).trans
    ((hf _ (8 * oWitnessLen) (BitVec.ofNat 64 ((bits + 7) / 8)) (by decide) (by decide)).trans
      (hf _ (8 * oChecks) (BitVec.ofNat 64 (checksCount c (Spec.Ffdh.primeChecks bits))) (by decide) (by decide)))

theorem phaseSelect_ok {s : State} {O : Addr} {bits : Nat}
    (hs : Scr s O 256) (hdi : s.gpr .rdi = O)
    (hb1 : 1 ≤ bits)
    (hb : word s.mem O (8 * oBits) = BitVec.ofNat 64 bits) (q : Bool) :
    WP isa (.block (([.mov .rdx (.mem (hdr oBits))] : List Instr) ++
      (if q then [.alu .sub .rdx (.imm 1)] else []))) s fun t =>
      t.gpr .rdx = BitVec.ofNat 64 (if q then bits - 1 else bits) ∧
      t.mem = s.mem ∧ Keep [.rdx] s t := by
  refine WP.mono (WP.keep [.rdx] (Q := fun t =>
    t.gpr .rdx = BitVec.ofNat 64 (if q then bits - 1 else bits) ∧ t.mem = s.mem) ?_
    (by cases q <;> rfl)) fun t ⟨⟨hd, hm⟩, k⟩ => ⟨hd, hm, k⟩
  have hl := hs.ld (d := 8 * oBits) (by decide)
  cases q
  · simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
    xrun [State.ea, hdr, hdi, hdrOff, hl, hb]
  · simp only [↓reduceIte, List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi, hdrOff, hl, hb]
    exact BitVec.ofNat_sub_ofNat_of_le (w := 64) bits 1 (by decide) hb1

theorem phaseHead_ok {s : State} {O : Addr} {bits : Nat}
    (hs : Scr s O 256) (hdi : s.gpr .rdi = O)
    (hb1 : 1 ≤ bits) (hb2 : bits < 2 ^ 32)
    (hb : word s.mem O (8 * oBits) = BitVec.ofNat 64 bits) (q : Bool) (c : Checks) :
    WP isa (.block (phaseHead q c)) s fun t =>
      t.mem = phaseMem s.mem O (if q then bits - 1 else bits) c ∧
      t.gpr .rax = off O 256 ∧ Keep [.rax, .rcx, .rdx] s t := by
  unfold phaseHead
  rw [WP.block_append_iff]
  refine WP.mono (phaseSelect_ok hs hdi hb1 hb q) fun u ⟨hd, hm, k⟩ => ?_
  have hbu : (if q then bits - 1 else bits) < 2 ^ 32 := by cases q <;> simp_all <;> omega_arith
  refine WP.mono (phaseWidth_ok (hs.congr k.2.2) ((k.gpr (by decide)).trans hdi) hbu hd c)
    fun t ⟨hmem, ha, k'⟩ => ?_
  exact ⟨by rw [hmem, hm], ha, (k.trans k').mono (by decide)⟩

theorem phaseMem_len (m : Mem) (O : Addr) (bits : Nat) (c : Checks) :
    word (phaseMem m O bits c) O (8 * oWitnessLen) = BitVec.ofNat 64 ((bits + 7) / 8) := by
  unfold phaseMem
  rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]

theorem phaseMem_bits (m : Mem) (O : Addr) (bits : Nat) (c : Checks) :
    word (phaseMem m O bits c) O (8 * oWitnessBits) = BitVec.ofNat 64 bits := by
  unfold phaseMem
  rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
    hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]

theorem phaseMem_checks (m : Mem) (O : Addr) (bits : Nat) (c : Checks) :
    word (phaseMem m O bits c) O (8 * oChecks) = BitVec.ofNat 64 (checksCount c (Spec.Ffdh.primeChecks bits)) := by
  unfold phaseMem
  exact word_writeW_self _ _ _ _

def phaseRanges : List (Nat × Nat) :=
  [(8 * oWitnessBits, 24)] ++ [(8 * oInner, 8), (256, 8 * 17)]

theorem phaseSetup_ok {s : State} {O : Addr} {Z bits : Nat}
    (hs : Scr s O Z) (hdi : s.gpr .rdi = O)
    (hb1 : 1 ≤ bits) (hb2 : bits < 2 ^ 32)
    (hb : word s.mem O (8 * oBits) = BitVec.ofNat 64 bits) (q : Bool) (c : Checks)
    (hz : 256 + slot (wsWords (((if q then bits - 1 else bits) + 7) / 8)) 8 ≤ Z) :
    WP isa (phaseSetup q c) s fun t => ∃ mi,
      Good t (off O 256) (Z - 256) (wsWords (((if q then bits - 1 else bits) + 7) / 8)) mi ∧
      word t.mem (off O 256) (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = O ∧
      word t.mem O (8 * oInner) = off O 256 ∧
      word t.mem O (8 * oWitnessBits) = BitVec.ofNat 64 (if q then bits - 1 else bits) ∧
      word t.mem O (8 * oWitnessLen) = BitVec.ofNat 64 (((if q then bits - 1 else bits) + 7) / 8) ∧
      word t.mem O (8 * oChecks) = BitVec.ofNat 64 (checksCount c (Spec.Ffdh.primeChecks (if q then bits - 1 else bits))) ∧
      Frm O phaseRanges s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  let b := if q then bits - 1 else bits
  let len := (b + 7) / 8
  let w := wsWords len
  have hz256 : 256 ≤ Z := by omega_arith
  have hs256 : Scr s O 256 := by
    simpa [off] using hs.sub (o := 0) (n := 256) (by omega_arith) (by decide)
  unfold phaseSetup
  refine WP.seq (WP.mono (phaseHead_ok hs256 hdi hb1 hb2 hb q c) fun u ⟨hm, ha, k⟩ => ?_)
  have hf : Frm O [(8 * oWitnessBits, 24)] s.mem u.mem := by rw [hm]; exact phaseMem_frame _ _ _ _
  have hu : Scr u O Z := hs.congr k.2.2
  have hlen : word u.mem O (8 * oWitnessLen) = BitVec.ofNat 64 len := by
    rw [hm]; exact phaseMem_len _ _ _ _
  have hlen32 : len < 2 ^ 32 := by
    have hl : b ≤ bits := by dsimp [b]; cases q <;> simp
    dsimp only [len]
    omega_arith
  refine WP.seq (WP.mono (wsNew_ok hu ((k.gpr (by decide)).trans hdi) ha
    (by decide : oInner < 32) (by decide : oWitnessLen < 32) (by decide) hlen hlen32 (by decide) hz)
    fun v ⟨hinner, hlink, hw, harr, hd, hf', k'⟩ => ?_)
  have hv : Scr v O Z := hu.congr k'.2.2
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off O 256 ∧ t.mem = v.mem)
    (by xrun [State.ea, hdr, hd, hdrOff, hv.ld (d := 8 * oInner) (by unfold oInner; omega_arith), hinner]) rfl)
    fun t ⟨⟨hdt, hmt⟩, kt⟩ => ?_
  have hst : Scr t (off O 256) (Z - 256) :=
    (hv.congr kt.2.2).sub (by omega_arith) (by unfold slot VG.Impl.Bignum.hdrBytes at hz; omega_arith)
  have hhead : ∀ j < 18, word v.mem O (8 * j) = word u.mem O (8 * j) := by
    intro j hj
    apply hf'.word_eq
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · left; change 8 * j + 8 ≤ 160; omega_arith
      · left; omega_arith
    · omega_arith
  refine ⟨word t.mem (off O 256) (8 * sMinv), ⟨hst, hdt, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    ((k.trans k').trans kt).mono (by decide)⟩
  · apply hdr_any
    · rw [hmt]; exact hw
    · intro j hj; rw [hmt]; exact harr j hj
  · rw [hmt]; exact hlink
  · rw [hmt]; exact hinner
  · rw [hmt, hhead _ (by decide), hm]; exact phaseMem_bits _ _ _ _
  · rw [hmt, hhead _ (by decide), hm]; exact phaseMem_len _ _ _ _
  · rw [hmt, hhead _ (by decide), hm]; exact phaseMem_checks _ _ _ _
  · rw [hmt]
    exact hf.append hf'

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end


/-! # FFDH parameter generation on x86-64: enter either modulus phase -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

theorem phaseSetup_state_ok {p : CandidateP} {used : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B) (q : Bool) (c : Checks) :
    WP isa (phaseSetup q c) s fun t => ∃ mi,
      CandidateTape p used t ∧ Good t (off p.B 256) (p.Z - 256) (p.phaseWords q) mi ∧
      PhaseHeader p q c t ∧ CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧
      Keep (.rdi :: mmRegs) s t ∧
      Spec.Rsa.bytesAt t.mem p.op p.k = Spec.Rsa.bytesAt s.mem p.op p.k := by
  have hws : wsWords (p.phaseLen q) = p.phaseWords q := by
    unfold wsWords
    change max 2 (p.phaseWords q) = p.phaseWords q
    exact Nat.max_eq_right (by omega_using [(h.base.phase_room q).1])
  have hbits := h.base.hdr (oBits, BitVec.ofNat 64 p.bits) (by simp [CandidateP.headers])
  refine WP.mono (phaseSetup_ok h.base.scr hdi (by omega_using [h.base.bits1])
    (by omega_using [h.base.bits2]) hbits q c (by
      change 256 + slot (wsWords (p.phaseLen q)) 8 ≤ p.Z
      rw [hws]
      omega_using [(h.base.phase_dims q).z, h.base.header_room]))
    fun t ⟨mi, hg, hl, _, hb, hn, hc, hf, k⟩ => ?_
  change Good t (off p.B 256) (p.Z - 256) (wsWords (p.phaseLen q)) mi at hg
  rw [hws] at hg
  have hfit : ∀ r ∈ phaseRanges, r.1 + r.2 ≤ p.Z := by
    intro r hr
    simp only [phaseRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change 144 ≤ p.Z; omega_using [h.base.header_room]
    · change 168 ≤ p.Z; omega_using [h.base.header_room]
    · change 392 ≤ p.Z; omega_using [h.base.room, h.base.widths.1]
  have hh : ∀ j < 15, word t.mem p.B (8 * j) = word s.mem p.B (8 * j) := by
    intro j hj
    apply hf.word_eq
    · intro r hr
      simp only [phaseRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · left; change 8 * j + 8 ≤ 120; omega_using [hj]
      · left; change 8 * j + 8 ≤ 160; omega_using [hj]
      · left; omega_using [hj]
    · omega_using [hj]
  have hframe : CandidateFrame p s.mem t.mem := CandidateFrame.of_scr (InScr.of_frm hf hfit)
  exact ⟨mi, h.keep hframe hh k ((k.gpr (by decide)).trans h.base.sp), hg,
    ⟨hb, hn, hc, hl⟩, fun j hj => hh j (by omega_using [hj]), hframe, k,
    h.base.output_eq (InScr.of_frm hf hfit)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
