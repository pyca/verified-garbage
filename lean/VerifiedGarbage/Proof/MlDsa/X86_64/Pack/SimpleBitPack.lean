module

import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlDsa.Pack.Bits
public import VerifiedGarbage.Proof.MlDsa.Pack.Mem
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.Bits
import VerifiedGarbage.Proof.MlKem.Encode
public import VerifiedGarbage.Impl.MlDsa.X86_64.Pack.Stream
public import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.MlDsa.Pack.Bits
meta import VerifiedGarbage.Proof.MlDsa.Pack.Mem
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.MlKem.Bits
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Pack.Stream
meta import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
meta import VerifiedGarbage.Proof.MlDsa.Pack.Stream
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
meta import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.Impl.MlDsa.X86_64.Pack.Encode
public import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
meta import VerifiedGarbage.Proof.MlDsa.Contract
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Pack.Encode
meta import VerifiedGarbage.Proof.MlKem.X86_64.Contracts

/-! ### `MlDsa.X86_64.Pack.Contracts`, which this module and modules that import it used -/

section

/-!
# ML-DSA on x86-64: the contracts of the encodings, for the proofs

For each function of this group, a contract with the facts of its shared
contract (`Proof/MlDsa/Contract.lean`) spelled out for x86-64: the arguments in
their registers, the permitted regions, their disjointness, and the
postcondition. The proofs are written against these, and `Verified.of_correct`
moves them to the shared contracts, which imply them. Also: `sel_ok`, the
branch of `sel` on a 32-bit argument.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Pack
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (retR pR dArg sub_beq_zero32)

/-- `vg_mldsa_simple_bit_pack(f = rdi, b = esi, out = rdx, len = rcx)`. -/
def simpleBitPackK : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rdi)] ∧ s.wr = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] ∧
    (pR (s.gpr .rdi)).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ ∧ (retR s).Disjoint (pR (s.gpr .rdi)) ∧
    (retR s).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ ∧ dArg s .rsi ∈ simpleBitPackBounds ∧
    (s.gpr .rcx).toNat = 32 * bitlen (dArg s .rsi) ∧ ∀ i < n, (coeffAt s.mem (s.gpr .rdi) i).toNat ≤ dArg s .rsi
  post s s' := Spec.Sha3.bytesAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
    simpleBitPack (natPolyAt s.mem (s.gpr .rdi)) (dArg s .rsi)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32

/-- `vg_mldsa_bit_pack(f = rdi, a = esi, b = edx, out = rcx, len = r8)`. -/
def bitPackK : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rdi)] ∧ s.wr = [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩] ∧
    (pR (s.gpr .rdi)).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ ∧ (retR s).Disjoint (pR (s.gpr .rdi)) ∧
    (retR s).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ ∧ (dArg s .rsi, dArg s .rdx) ∈ bitPackParams ∧
    (s.gpr .r8).toNat = 32 * bitlen (dArg s .rsi + dArg s .rdx) ∧ Reduced s.mem (s.gpr .rdi) ∧
    ∀ i < n, -(dArg s .rsi : Int) ≤ modPm (coeffAt s.mem (s.gpr .rdi) i).toNat q ∧
      modPm (coeffAt s.mem (s.gpr .rdi) i).toNat q ≤ dArg s .rdx
  post s s' := Spec.Sha3.bytesAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat =
    bitPack ((polyAt s.mem (s.gpr .rdi)).map fun c => modPm c.val q) (dArg s .rsi) (dArg s .rdx)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32 ∧
    (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32

/-- `vg_mldsa_bit_unpack(v = rdi, len = rsi, a = edx, b = ecx, f = r8)`. -/
def bitUnpackK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩] ∧ s.wr = [pR (s.gpr .r8)] ∧
    Region.Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ (pR (s.gpr .r8)) ∧
    (retR s).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ∧ (retR s).Disjoint (pR (s.gpr .r8)) ∧
    (dArg s .rdx, dArg s .rcx) ∈ bitPackParams ∧ (s.gpr .rsi).toNat = 32 * bitlen (dArg s .rdx + dArg s .rcx)
  post s s' := PolyIs s'.mem (s.gpr .r8)
    (toRq (bitUnpack (Spec.Sha3.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (dArg s .rdx) (dArg s .rcx)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32 ∧
    (s₁.gpr .rcx).setWidth 32 = (s₂.gpr .rcx).setWidth 32

/-- `vg_mldsa_unpack_t1(v = rdi, f = rsi)`. -/
def unpackT1K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 320⟩] ∧ s.wr = [pR (s.gpr .rsi)] ∧
    Region.Disjoint ⟨s.gpr .rdi, 320⟩ (pR (s.gpr .rsi)) ∧ (retR s).Disjoint ⟨s.gpr .rdi, 320⟩ ∧
    (retR s).Disjoint (pR (s.gpr .rsi))
  post s s' := PolyIs s'.mem (s.gpr .rsi)
    ((simpleBitUnpack (Spec.Sha3.bytesAt s.mem (s.gpr .rdi) 320) t1Max).map fun c => ofInt (c * 2 ^ d : Nat))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-! ## Branching on a width -/

theorem cmp_ok (r : Reg) (k : BitVec 32) (s : State) :
    WP isa (.block [.alu32 .cmp r (.imm k)]) s fun s' =>
      s'.zf = some (BitVec.setWidth 32 (s.gpr r) - k == 0) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  xrun

/-- The same registers, memory and permissions. -/
def Same (s s' : State) : Prop := s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem sel_ok (r : Reg) (v : Nat) (p e : Prog isa) (s : State) {Q : State → Prop}
    (hp : ∀ s', Same s s' → (s.gpr r).setWidth 32 = BitVec.ofNat 32 v → WP isa p s' Q)
    (he : ∀ s', Same s s' → (s.gpr r).setWidth 32 ≠ BitVec.ofNat 32 v → WP isa e s' Q) :
    WP isa (sel r v p e) s Q := by
  unfold sel
  refine WP.seq (WP.mono (cmp_ok r _ s) fun s' ⟨z, hg, hm, hrd, hwr⟩ => ?_)
  refine WP.ite (M := isa) _ (show isa.eval .e s' = _ from z) (fun h => ?_) (fun h => ?_)
  · rw [sub_beq_zero32, decide_eq_true_eq] at h
    exact hp s' ⟨hg, hm, hrd, hwr⟩ h
  · rw [sub_beq_zero32, decide_eq_false_iff_not] at h
    exact he s' ⟨hg, hm, hrd, hwr⟩ h

theorem lo_ne {s : State} {r : Reg} {v : Nat} (h : (s.gpr r).setWidth 32 ≠ BitVec.ofNat 32 v) :
    dArg s r ≠ v := fun e => h (by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, ← e]; exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm)

theorem lo_of_eq {s : State} {r : Reg} {v : Nat} (h : (s.gpr r).setWidth 32 = BitVec.ofNat 32 v) :
    dArg s r = v % 2 ^ 32 := by
  unfold dArg; rw [h, BitVec.toNat_ofNat]

end VG.Proof.MlDsa.X86_64.Pack

end

end

/-! ### `MlDsa.X86_64.Pack.Loop`, which this module and modules that import it used -/

section

/-! ### `MlDsa.X86_64.Pack.Stream`, which this module and modules that import it used -/

section

/-!
# ML-DSA on x86-64: streaming fields through `r10`

The group bodies of `Impl/MlDsa/X86_64/Pack/Stream.lean`, for any width `d`,
group of `c` fields and `nb` bytes, and any code `ld` that loads a field's
value (`LdOk`) or `fin` that stores a coefficient from it (`FinOk`):

* `packBody_ok`: the `nb` bytes stored are those of the number `G` whose
  base-`2ᵈ` digits are the values of the group's coefficients;
* `unpackBody_ok`: the word stored for field `j` is `fin`'s of digit `j` of
  the number whose bytes are the group's.

In packing, the accumulator is a slice of the number throughout
(`Pack/Stream.lean`); in unpacking, the load of a field is the slice of the
number at its bytes (`read_slice`), which holds the field (`ldOff_fit`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Pack
open VG.Proof.MlKem.X86_64 (Keep Keep.refl Keep.trans Keep.mono Keep.gpr WP.keep Written Written.nil
  Written.snoc Written.congr Written.frame rotr_toNat shr_toNat b8_eq64 ifp ifn sx_ofNat r10zero_ok)
open VG.Proof.MlKem (digits ofNat8_eq)
open VG.Proof.MlDsa.Pack

theorem ea_at' (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_]
  congr 1

/-- `r10 ← r10 + rax · 2^sh`. -/
theorem shiftAdd_ok {sh : Nat} (hsh : sh < 64) (s : State) (hx : (s.gpr .rax).toNat < 2 ^ (64 - sh))
    (hs : (s.gpr .r10).toNat + (s.gpr .rax).toNat * 2 ^ sh < 2 ^ 64) :
    WP isa (.block (shiftAdd sh)) s fun s' =>
      ((s'.gpr .r10).toNat = (s.gpr .r10).toNat + (s.gpr .rax).toNat * 2 ^ sh ∧ s'.mem = s.mem) ∧
        Keep [.rax, .r10] s s' := by
  by_cases h : sh = 0
  · subst h
    refine WP.keep _ ?_ (Proof.MlKem.X86_64.writesOnly_of (by decide))
    simp only [shiftAdd, ite_true, List.nil_append]
    xrun
    rw [BitVec.toNat_add]
    simp only [Nat.pow_zero, Nat.mul_one] at hs ⊢
    exact Nat.mod_eq_of_lt hs
  · refine WP.keep _ ?_ (by simp only [shiftAdd, h, ite_false]; rfl)
    simp only [shiftAdd, h, ite_false, List.singleton_append]
    xrun [show 1 ≤ 64 - sh by omega_arith, show 64 - sh ≤ 63 by omega_arith]
    rw [BitVec.toNat_add, rotr_toNat _ (by omega_arith) hx, show 64 - (64 - sh) = sh by omega_arith, Nat.mod_eq_of_lt hs]

/-! ## Packing -/

theorem packByte_ok (t : Nat) (s : State) (hout : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 t) 1) :
    WP isa (.block (packByte t)) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .r8 + BitVec.ofNat 64 t) (BitVec.setWidth 8 (s.gpr .r10)) ∧
        s'.gpr .r10 = s.gpr .r10 >>> 8) ∧ Keep [.r10] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold packByte
  xrun [ea_at', hout]

/-- The bytes `k, …, k + nf - 1` of the output from the accumulator `X`,
whose byte `u` is byte `k + u` of the output. -/
theorem flush_ok {k nf : Nat} {m₀ : Mem} {o : Addr} {V8 : Nat → Byte} (X : Nat)
    (hX : ∀ u < nf, BitVec.ofNat 8 (X / 2 ^ (8 * u)) = V8 (k + u)) (hk : k + nf < 2 ^ 64) (s : State)
    (h8 : s.gpr .r8 = o) (hout : ∀ u < nf, InRegions s.wr (o + BitVec.ofNat 64 (k + u)) 1)
    (hw : Written m₀ s.mem o k V8) (hr : (s.gpr .r10).toNat = X) :
    WP isa (.block ((List.range nf).flatMap fun u => packByte (k + u))) s fun s' =>
      Written m₀ s'.mem o (k + nf) V8 ∧ (s'.gpr .r10).toNat = X / 2 ^ (8 * nf) ∧ Keep [.r10] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => Keep [.r10] s s' ∧
    (s'.gpr .r10).toNat = X / 2 ^ (8 * u) ∧ Written m₀ s'.mem o (k + u) V8)
    (fun u s' hu ⟨hkp, hr', hw'⟩ => ?_) nf (Nat.le_refl _) s ⟨Keep.refl _ _, by simp [hr], hw⟩)
    fun s' ⟨hkp, hr', hw'⟩ => ⟨hw', hr', hkp⟩
  have h8' : s'.gpr .r8 = o := (hkp.gpr (by decide)).trans h8
  refine WP.mono (packByte_ok (k + u) s' (by rw [hkp.2.2, h8']; exact hout u hu))
    fun s'' ⟨⟨hm, h10⟩, hk'⟩ => ⟨(hkp.trans hk').mono (by decide), ?_, ?_⟩
  · rw [h10, shr_toNat, hr', Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]
  · rw [hm, h8']
    refine (hw'.snoc (by omega_arith) _).congr fun t ht => ?_
    by_cases e : t = k + u
    · subst e; rw [ifp rfl, b8_eq64, hr', hX u hu]
    · rw [ifn e]

/-- `ld j` loads into `rax` the value `F` of the word at `rdi + 4j`, and
writes only `rax` and `r11`. -/
def LdOk (ld : Nat → List Instr) (F : BitVec 32 → Nat) : Prop :=
  ∀ j s, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 4 →
    WP isa (.block (ld j)) s fun s' =>
      ((s'.gpr .rax).toNat = F (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) ∧ s'.mem = s.mem) ∧
        Keep [.rax, .r11] s s'

/-- The bytes of `G`. -/
abbrev bytesOf (G : Nat) (t : Nat) : Byte := BitVec.ofNat 8 (G / 2 ^ (8 * t))

/-- Field `j`: its value, digit `j` of `G`, into `r10`, then the bytes it
completes. -/
theorem packCoef_ok {ld : Nat → List Instr} {F : BitVec 32 → Nat} (hld : LdOk ld F) {d j G : Nat}
    (hd : d ≤ 20) {m₀ : Mem} (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 4)
    (hv : F (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) = G / 2 ^ (d * j) % 2 ^ d)
    (hout : ∀ t < d * (j + 1) / 8, InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 t) 1)
    (hw : Written m₀ s.mem (s.gpr .r8) (d * j / 8) (bytesOf G))
    (hr : (s.gpr .r10).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8))) (hj : d * (j + 1) < 2 ^ 32) :
    WP isa (.block (packCoef ld d j)) s fun s' =>
      Written m₀ s'.mem (s.gpr .r8) (d * (j + 1) / 8) (bytesOf G) ∧
        (s'.gpr .r10).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * (j + 1) / 8)) ∧
        Keep [.rax, .r10, .r11] s s' := by
  unfold packCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (hld j s hin) fun s₁ ⟨⟨ax₁, m₁⟩, k₁⟩ => ?_
  have hx : (s₁.gpr .rax).toNat < 2 ^ d := by rw [ax₁, hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)
  have hr₁ : (s₁.gpr .r10).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)) := by rw [k₁.gpr (by decide), hr]
  have hacc := pack_acc_lt G d j
  have hpd : 2 ^ d ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hd
  have hp8 : 2 ^ (d * j % 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega_arith)
  refine WP.mono (shiftAdd_ok (sh := d * j % 8) (by omega_arith) s₁
    (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega_arith))) (by
      rw [hr₁]
      have := Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_refl (2 ^ (d * j % 8))) (Nat.two_pow_pos _)
      have : 2 ^ d * 2 ^ (d * j % 8) ≤ 2 ^ 20 * 2 ^ 7 := Nat.mul_le_mul hpd hp8
      omega_arith))
    fun s₂ ⟨⟨r₂, m₂⟩, k₂⟩ => ?_
  have hjs : d * (j + 1) = d * j + d := Nat.mul_succ d j
  have hX : (s₂.gpr .r10).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * j / 8)) := by
    rw [r₂, hr₁, ax₁, hv, pack_add]
  have h8 : s₂.gpr .r8 = s.gpr .r8 := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  refine WP.mono (flush_ok (k := d * j / 8) (nf := d * (j + 1) / 8 - d * j / 8) (m₀ := m₀) (o := s.gpr .r8)
    (V8 := bytesOf G) _ (fun u hu => ?_) (by omega_arith) s₂ h8 (fun u hu => ?_) (by rw [m₂, m₁]; exact hw) hX)
    fun s₃ ⟨hw₃, hr₃, k₃⟩ => ⟨?_, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · refine ofNat8_eq ?_
    rw [show (256 : Nat) = 2 ^ 8 from rfl, pack_byte G _ _ _ (by
      have : d * j / 8 + u < d * (j + 1) / 8 := by omega_arith
      omega_arith)]
  · rw [k₂.2.2, k₁.2.2]; exact hout _ (by omega_arith)
  · rwa [show d * j / 8 + (d * (j + 1) / 8 - d * j / 8) = d * (j + 1) / 8 by
      have : d * j / 8 ≤ d * (j + 1) / 8 := Nat.div_le_div_right (by rw [Nat.mul_succ]; omega_arith)
      omega_arith] at hw₃
  · rw [hr₃, pack_shift, show d * j / 8 + (d * (j + 1) / 8 - d * j / 8) = d * (j + 1) / 8 by
      have : d * j / 8 ≤ d * (j + 1) / 8 := Nat.div_le_div_right (by rw [Nat.mul_succ]; omega_arith)
      omega_arith]

/-- A group: the `nb` bytes of the number whose base-`2ᵈ` digits are the
values of its `c` coefficients, stored at `r8`. -/
theorem packBody_ok {ld : Nat → List Instr} {F : BitVec 32 → Nat} (hld : LdOk ld F) {d c nb : Nat}
    (hd : d ≤ 20) (hdc : d * c = 8 * nb) (hc : c ≤ 8) (s : State)
    (hin : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 4)
    (hout : ∀ t < nb, InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 t) 1)
    (hsep : ∀ j < c, Region.Disjoint ⟨s.gpr .rdi + BitVec.ofNat 64 (4 * j), 4⟩ ⟨s.gpr .r8, nb⟩)
    (hF : ∀ j < c, F (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) < 2 ^ d) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      Written s.mem s'.mem (s.gpr .r8) nb (bytesOf (digits d ((List.range c).map fun j =>
          F (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32)))) ∧
        s'.gpr .rdi = s.gpr .rdi + BitVec.ofNat 64 (4 * c) ∧ s'.gpr .r8 = s.gpr .r8 + BitVec.ofNat 64 nb ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧
        Keep [.rax, .rcx, .rdi, .r8, .r10, .r11] s s' := by
  generalize hG : digits d ((List.range c).map fun j => F (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32)) = G
  have hdig : ∀ j < c, G / 2 ^ (d * j) % 2 ^ d = F (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) :=
    fun j hj => by rw [← hG]; exact digits_range_get hF hj
  unfold packBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (r10zero_ok s) fun s₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_
  have di₁ : s₁.gpr .rdi = s.gpr .rdi := k₁.gpr (by decide)
  have r8₁ : s₁.gpr .r8 = s.gpr .r8 := k₁.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.rax, .r10, .r11] s₁ s' ∧
      Written s.mem s'.mem (s.gpr .r8) (d * j / 8) (bytesOf G) ∧
      (s'.gpr .r10).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)))
    (fun j s' hj ⟨hk, hw, hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, by rw [m₁, Nat.mul_zero, Nat.zero_div]; exact Written.nil _ _ _,
      by rw [z₁, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]; rfl⟩) fun s₂ ⟨k₂, hw₂, _⟩ => ?_
  · have di : s'.gpr .rdi = s.gpr .rdi := (hk.gpr (by decide)).trans di₁
    have r8 : s'.gpr .r8 = s.gpr .r8 := (hk.gpr (by decide)).trans r8₁
    have hj8 : d * (j + 1) / 8 ≤ nb := by
      have := Nat.mul_le_mul_left d (show j + 1 ≤ c by omega_arith); omega_arith
    have hj32 := Nat.mul_le_mul hd (show j + 1 ≤ 8 by omega_arith)
    refine WP.mono (packCoef_ok hld (G := G) (m₀ := s.mem) hd s' (by rw [hk.2.1, hk.2.2, k₁.2.1, k₁.2.2, di]; exact hin j hj)
      ?_ (fun t ht => by rw [hk.2.2, k₁.2.2, r8]; exact hout t (by omega_arith)) (by rw [r8]; exact hw) hr (by omega_arith))
      fun s'' ⟨hw', hr', hk'⟩ => ⟨(hk.trans hk').mono (by decide), by rw [← r8]; exact hw', hr'⟩
    -- The word is the one on entry: the bytes written are elsewhere.
    rw [di, hdig j hj]
    congr 1
    refine (hw.frame (R := ⟨s.gpr .r8, nb⟩) ?_).readW (Region.contains_self _ _) ?_ (by decide)
    · have := Nat.mul_le_mul_left d (Nat.le_of_lt hj)
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega_arith
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hsep j hj
  · have hc8 : d * c / 8 = nb := by omega_arith
    have := Nat.mul_le_mul hd hc
    rw [hc8] at hw₂
    refine WP.mono (Proof.MlKem.X86_64.CE.tail_ok c nb (by omega_arith) (by omega_arith) s₂)
      fun s₃ ⟨⟨di₃, r8₃, cx₃, z₃, m₃⟩, k₃⟩ => ⟨by rw [m₃]; exact hw₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [di₃, k₂.gpr (by decide), di₁]
    · rw [r8₃, k₂.gpr (by decide), r8₁]
    · rw [cx₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · rw [z₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · exact ((k₁.trans k₂).trans k₃).mono (by decide)

/-! ## Unpacking -/

/-- `n` bytes at `a + o` that are bytes `o, …, o + n - 1` of `H`. -/
theorem read_slice (m : Mem) (a : Addr) (H : Nat) : ∀ (n o : Nat),
    (∀ u < n, (m (a + BitVec.ofNat 64 (o + u))).toNat = H / 2 ^ (8 * (o + u)) % 2 ^ 8) →
    (m.read (a + BitVec.ofNat 64 o) n).toNat = H / 2 ^ (8 * o) % 2 ^ (8 * n)
  | 0, o, _ => by simp only [Mem.read, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]; rfl
  | n + 1, o, h => by
    have h0 : (m (a + BitVec.ofNat 64 o)).toNat = H / 2 ^ (8 * o) % 2 ^ 8 := by simpa using h 0 (by omega_using [])
    rw [Proof.Mont.read_toNat_succ, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
      read_slice m a H n (o + 1) (fun u hu => by rw [show o + 1 + u = o + (u + 1) by omega_using []]; exact h (u + 1) (by omega_using [hu])),
      show 8 * (n + 1) = 8 + 8 * n by omega_using [], mod_two_pow_add, Nat.div_div_eq_div_mul, ← Nat.pow_add,
      show 8 * o + 8 = 8 * (o + 1) by omega_using [], h0]

/-- `fin j` stores the coefficient `W x` of the field `x < 2ᵈ` in `rax` to
`rsi + 4j`, and writes only `rax` and `r11`. -/
def FinOk (fin : Nat → List Instr) (d : Nat) (W : Nat → BitVec 32) : Prop :=
  ∀ j s, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 4 → (s.gpr .rax).toNat < 2 ^ d →
    WP isa (.block (fin j)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) (W (s.gpr .rax).toNat) ∧ Keep [.rax, .r11] s s'

/-- The load of a field: the `ldW nb` bytes at `rdi + o`, as a number. -/
theorem ldLoad_ok {d nb j : Nat} (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (ldOff d nb j)) (ldW nb)) :
    WP isa (.block (if 4 ≤ nb then [.mov32 .rax (.mem (at_ .rdi (ldOff d nb j)))]
      else [.movzx16 .rax (at_ .rdi (ldOff d nb j))])) s fun s' =>
      ((s'.gpr .rax).toNat = (s.mem.read (s.gpr .rdi + BitVec.ofNat 64 (ldOff d nb j)) (ldW nb)).toNat ∧
        s'.mem = s.mem) ∧ Keep [.rax] s s' := by
  by_cases h : 4 ≤ nb
  · have hw : ldW nb = 4 := ifp h 4 2
    rw [hw] at hin ⊢
    simp only [h, ite_true]
    refine WP.keep _ ?_ (by rfl)
    xrun [ea_at', hin]
    have := (s.mem.read (s.gpr .rdi + BitVec.ofNat 64 (ldOff d nb j)) 4).isLt
    simp only [Mem.readW, BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega_using [])]
  · have hw : ldW nb = 2 := ifn h 4 2
    rw [hw] at hin ⊢
    simp only [h, ite_false]
    refine WP.keep _ ?_ (by rfl)
    xrun [ea_at', hin, State.load16]
    have := (s.mem.read (s.gpr .rdi + BitVec.ofNat 64 (ldOff d nb j)) 2).isLt
    simp only [Mem.readW, BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega_using [])]

/-- The field from the loaded bytes: shifted right by `sh` and masked to `d`
bits. -/
theorem ldMask_ok (d sh : Nat) (hd : d ≤ 20) (hsh : sh < 32) (s : State)
    (hx : (s.gpr .rax).toNat < 2 ^ 32) :
    WP isa (.block ((if sh = 0 then [] else [.shift32 .shr .rax sh]) ++
      ([.alu32 .and .rax (.imm (BitVec.ofNat 32 (2 ^ d - 1)))] : List Instr))) s fun s' =>
      ((s'.gpr .rax).toNat = (s.gpr .rax).toNat / 2 ^ sh % 2 ^ d ∧ s'.mem = s.mem) ∧ Keep [.rax] s s' := by
  have hp : 2 ^ d ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hd
  by_cases h : sh = 0
  · subst h
    simp only [ite_true, List.nil_append]
    refine WP.keep _ ?_ (by rfl)
    xrun
    rw [Proof.MlKem.X86_64.toNat_setWidth64, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx, Nat.pow_zero, Nat.div_one]
  · simp only [h, ite_false, List.singleton_append]
    refine WP.keep _ ?_ (by rfl)
    xrun [show 1 ≤ sh by omega_arith, show sh ≤ 31 by omega_arith]
    rw [Proof.MlKem.X86_64.toNat_setWidth64, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      Nat.and_two_pow_sub_one_eq_mod]
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx, Nat.shiftRight_eq_div_pow]

/-- The shift and width of the load of field `j` fit it: it starts at or
after the load, and ends within it. -/
theorem ldOff_fit {d nb j : Nat} (hd : d ≤ 20) (hnb : 2 ≤ nb) (hsm : nb < 4 → d ≤ 9) (hj : d * j + d ≤ 8 * nb) :
    8 * ldOff d nb j ≤ d * j ∧ d * j - 8 * ldOff d nb j + d ≤ 8 * ldW nb ∧ ldOff d nb j + ldW nb ≤ nb := by
  unfold ldOff ldW
  split <;> omega_arith

/-- Field `j`: its value, digit `j` of `H`, stored by `fin`. -/
theorem unpackCoef_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} (hfin : FinOk fin d W)
    (hd1 : 1 ≤ d) (hd : d ≤ 20) {nb H j : Nat} (hnb : 2 ≤ nb) (hsm : nb < 4 → d ≤ 9) (hj : d * j + d ≤ 8 * nb)
    (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (ldOff d nb j)) (ldW nb))
    (hb : ∀ t < nb, (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat = H / 2 ^ (8 * t) % 2 ^ 8)
    (hout : InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block (unpackCoef fin d nb j)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) (W (H / 2 ^ (d * j) % 2 ^ d)) ∧
        Keep [.rax, .r11] s s' := by
  obtain ⟨ho, hsh, hon⟩ := ldOff_fit hd hnb hsm hj
  have hw4 : ldW nb ≤ 4 := by unfold ldW; split <;> omega_using []
  unfold unpackCoef ldField
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldLoad_ok s hin) fun s₁ ⟨⟨ax₁, m₁⟩, k₁⟩ => ?_
  have hv : (s₁.gpr .rax).toNat = H / 2 ^ (8 * ldOff d nb j) % 2 ^ (8 * ldW nb) := by
    rw [ax₁, read_slice _ _ H _ _ fun u hu => hb _ (by omega_arith)]
  have hx : (s₁.gpr .rax).toNat < 2 ^ 32 := by
    rw [hv]
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) (by omega_arith))
  refine WP.mono (ldMask_ok d _ hd (by omega_arith) s₁ hx) fun s₂ ⟨⟨ax₂, m₂⟩, k₂⟩ => ?_
  have hf : (s₂.gpr .rax).toNat = H / 2 ^ (d * j) % 2 ^ d := by
    rw [ax₂, hv, VG.Proof.MlKem.mod_pow_div_mod _ hsh, Nat.div_div_eq_div_mul, ← Nat.pow_add,
      show 8 * ldOff d nb j + (d * j - 8 * ldOff d nb j) = d * j by omega_arith]
  have si : s₂.gpr .rsi = s.gpr .rsi := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  refine WP.mono (hfin j s₂ (by rw [k₂.2.2, k₁.2.2, si]; exact hout) (by rw [hf]; exact Nat.mod_lt _ (Nat.two_pow_pos d)))
    fun s₃ ⟨m₃, k₃⟩ => ⟨by rw [m₃, si, hf, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- A group: the word stored for field `j` is `W` of digit `j` of the
number whose bytes are the group's `nb` bytes at `rdi`. -/
theorem unpackBody_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} (hfin : FinOk fin d W)
    {c nb : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 20) (hdc : d * c = 8 * nb) (hc : c ≤ 8) (hnb : 2 ≤ nb)
    (hsm : nb < 4 → d ≤ 9) (s : State)
    (hin : ∀ t n, t + n ≤ nb → InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 t) n)
    (hout : ∀ j < c, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 4)
    (hsep : ∀ t < nb, Region.Disjoint ⟨s.gpr .rdi + BitVec.ofNat 64 t, 1⟩ ⟨s.gpr .rsi, 4 * c⟩) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      (∀ j < c, s'.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 32 =
        W (digits 8 ((List.range nb).map fun t => (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat) /
          2 ^ (d * j) % 2 ^ d)) ∧
        Frame [⟨s.gpr .rsi, 4 * c⟩] s.mem s'.mem ∧
        s'.gpr .rdi = s.gpr .rdi + BitVec.ofNat 64 nb ∧ s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 (4 * c) ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧
        Keep [.rax, .rcx, .rsi, .rdi, .r10, .r11] s s' := by
  generalize hH : digits 8 ((List.range nb).map fun t => (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat) = H
  have hbyte : ∀ t < nb, H / 2 ^ (8 * t) % 2 ^ 8 = (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat :=
    fun t ht => by rw [← hH]; exact digits_range_get (fun t _ => BitVec.isLt _) ht
  have := Nat.mul_le_mul hd hc
  unfold unpackBody
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.rax, .r11] s s' ∧
      Frame [⟨s.gpr .rsi, 4 * c⟩] s.mem s'.mem ∧
      (∀ j' < j, s'.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * j')) 32 = W (H / 2 ^ (d * j') % 2 ^ d)))
    (fun j s' hj ⟨hk, hf, hw⟩ => ?_) c (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s₂ ⟨k₂, hf₂, hw₂⟩ => ?_
  · have di : s'.gpr .rdi = s.gpr .rdi := hk.gpr (by decide)
    have si : s'.gpr .rsi = s.gpr .rsi := hk.gpr (by decide)
    have hj' : d * j + d ≤ 8 * nb := by
      have := Nat.mul_le_mul_left d (show j + 1 ≤ c by omega_arith); rw [Nat.mul_succ] at this; omega_arith
    obtain ⟨-, -, hon⟩ := ldOff_fit hd hnb hsm hj'
    refine WP.mono (unpackCoef_ok hfin hd1 hd (H := H) hnb hsm hj' s'
      (by rw [hk.2.1, hk.2.2, di]; exact hin _ _ hon)
      (fun t ht => by
        rw [di, hbyte t ht]
        refine congrArg BitVec.toNat (hf _ fun r hr => ?_)
        simp only [List.mem_singleton] at hr; subst hr
        exact hsep t ht _ (Region.contains_self _ _))
      (by rw [hk.2.2, si]; exact hout j hj))
      fun s'' ⟨m'', hk'⟩ => ⟨(hk.trans hk').mono (by decide), ?_, fun j' hj' => ?_⟩
    · rw [m'', si]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
    · rw [m'', si]
      by_cases e : j' = j
      · subst e; rw [Mem.readW_writeW_self32]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), hw j' (by omega_arith)]
  · refine WP.mono (Proof.MlKem.X86_64.DD.tail_ok c nb (by omega_arith) (by omega_arith) s₂)
      fun s₃ ⟨⟨di₃, si₃, cx₃, z₃, m₃⟩, k₃⟩ => ⟨fun j hj => ?_, by rw [m₃]; exact hf₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [m₃, hw₂ j hj, ← hH]
    · rw [di₃, k₂.gpr (by decide)]
    · rw [si₃, k₂.gpr (by decide)]
    · rw [cx₃, k₂.gpr (by decide)]
    · rw [z₃, k₂.gpr (by decide)]
    · exact (k₂.trans k₃).mono (by decide)

end VG.Proof.MlDsa.X86_64.Pack

end

end

/-!
# ML-DSA on x86-64: the loops over the groups

`packLoop_ok`: the loop of `packBody` writes the packing of the values of the
256 coefficients at `f`; `unpackLoop_ok`: the loop of `unpackBody` writes, for
each field of the bytes at `v`, `fin`'s coefficient of it. Both for any width
and any `ld` or `fin`, from the group lemmas of `Stream.lean`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Pack
open VG.Spec.MlDsa (bitsToBytes)
open VG.Proof.MlDsa (coeffAt)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86_64 (Keep Keep.refl Keep.trans Keep.mono Keep.gpr Written Written.step ptr_step
  wp_counted WP.keep)
open VG.Proof.MlKem (digits take_drop_eq bytesAt_getD bytesAt_eq! bytesAt_length bytes_map_take_drop)
open VG.Proof.MlDsa.Pack

/-- The value of each coefficient is less than `2ᵈ`, and the groups tile the
polynomial and the output. -/
structure Shape (d c nb : Nat) : Prop where
  d1 : 1 ≤ d
  d20 : d ≤ 20
  dc : d * c = 8 * nb
  c0 : 0 < c
  c8 : c ≤ 8
  cN : c * (256 / c) = 256
  bN : nb * (256 / c) = 32 * d

theorem Shape.nb20 {d c nb : Nat} (h : Shape d c nb) : nb ≤ 20 := by
  have := Nat.mul_le_mul h.d20 h.c8; have := h.dc; omega_arith

theorem Shape.group {d c nb : Nat} (h : Shape d c nb) {i : Nat} (hi : i < 256 / c) :
    c * i + c ≤ 256 ∧ nb * i + nb ≤ 32 * d := by
  have h1 := Nat.mul_le_mul_left c (show i + 1 ≤ 256 / c by omega_arith)
  have h2 := Nat.mul_le_mul_left nb (show i + 1 ≤ 256 / c by omega_arith)
  rw [Nat.mul_succ] at h1 h2
  have := h.cN; have := h.bN
  omega_arith

theorem off_add (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem inRegions_of {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (h : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, h⟩

theorem getD_map_toNat (B : List Byte) (k : Nat) : (B.map (·.toNat)).getD k 0 = (B.getD k 0).toNat := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]; cases B[k]? <;> rfl

/-- The registers a loop writes. -/
abbrev packRegs : List Reg := [.rax, .rcx, .rdi, .r8, .r10, .r11]
abbrev unpackRegs : List Reg := [.rax, .rcx, .rsi, .rdi, .r10, .r11]

/-! ## Packing -/

section
variable {ld : Nat → List Instr} {F : BitVec 32 → Nat} (hld : LdOk ld F) {d c nb : Nat} (hs : Shape d c nb)
  {f o : Addr} {s₀ sE : State} (hin : polyRegion f ∈ s₀.rd ++ s₀.wr) (hout : (⟨o, 32 * d⟩ : Region) ∈ s₀.wr)
  (hsep : Region.Disjoint (polyRegion f) ⟨o, 32 * d⟩) (hF : ∀ i < 256, F (coeffAt s₀.mem f i) < 2 ^ d)
include hld hs hin hout hsep hF

/-- The values of the coefficients. -/
abbrev vals (F : BitVec 32 → Nat) (m : Mem) (f : Addr) : List Nat := (List.range 256).map fun i => F (coeffAt m f i)

omit hld hs hin hout hsep hF in
theorem vals_lt {d : Nat} {m : Mem} {f : Addr} (hF : ∀ i < 256, F (coeffAt m f i) < 2 ^ d) :
    ∀ a ∈ vals F m f, a < 2 ^ d := fun a ha => by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha; exact hF i (List.mem_range.mp hi)

/-- After `i` groups. -/
structure PInv (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = f + BitVec.ofNat 64 (4 * c * i)
  r8 : s.gpr .r8 = o + BitVec.ofNat 64 (nb * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨o, 32 * d⟩] s₀.mem s.mem
  done : ∀ k < nb * i, s.mem (o + BitVec.ofNat 64 k) = (bitsToBytes (fieldBits d (vals F s₀.mem f)))[k]!
  keep : Keep packRegs sE s

theorem packStep {i : Nat} (hi : i < 256 / c) {s : State} (hI : PInv (f := f) (o := o) (s₀ := s₀) (sE := sE) (F := F) (d := d) (c := c) (nb := nb) i s) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      PInv (f := f) (o := o) (s₀ := s₀) (sE := sE) (F := F) (d := d) (c := c) (nb := nb) (i + 1) s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  obtain ⟨hci, hbi⟩ := hs.group hi
  have hnb := hs.nb20
  have hd20 := hs.d20
  have ha : ∀ j < c, s.gpr .rdi + BitVec.ofNat 64 (4 * j) = coeffAddr f (c * i + j) := fun j _ => by
    rw [hI.rdi, off_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  have hb : ∀ t, s.gpr .r8 + BitVec.ofNat 64 t = o + BitVec.ofNat 64 (nb * i + t) := fun t => by
    rw [hI.r8, off_add]
  -- The words of the group are those on entry.
  have hw : ∀ j < c, s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32 = coeffAt s₀.mem f (c * i + j) :=
    fun j hj => by
      rw [ha j hj]
      exact coeffAt_frame hI.frame (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
        (by omega_arith)
  refine WP.mono (packBody_ok hld hs.d20 hs.dc hs.c8 s
    (fun j hj => by rw [ha j hj, hI.rd, hI.wr]; exact inRegions_of hin (coeff_contains f (by omega_arith)))
    (fun t ht => by rw [hb, hI.wr]; exact inRegions_of hout (Offset.contains_base o (by omega_arith) (by omega_arith)))
    (fun j hj => by
      rw [ha j hj, hI.r8]
      exact (hsep.sub_left (Offset.sub_base f (by omega_arith))).sub_right (Offset.sub_base o (by omega_arith)))
    (fun j hj => by rw [hw j hj]; exact hF _ (by omega_arith)))
    fun s' ⟨hW, di', r8', cx', z', k'⟩ => ⟨?_, cx', z'⟩
  have hW' : Written s.mem s'.mem (o + BitVec.ofNat 64 (nb * i)) nb
      fun t => (bitsToBytes (fieldBits d (vals F s₀.mem f)))[nb * i + t]! := by
    rw [← hI.r8]
    refine hW.congr fun t ht => ?_
    rw [pack_group (c := c) (by have := hs.d1; omega_arith) hs.dc (by simp) (vals_lt hF) ht (by omega_arith),
      take_drop_eq _ 0 (by simp; omega_arith)]
    refine congrArg (fun L => BitVec.ofNat 8 (digits d L / 2 ^ (8 * t))) (List.map_congr_left fun j hj => ?_)
    have hj := List.mem_range.mp hj
    rw [hw j hj, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega_arith)]
    rfl
  obtain ⟨hf', hd'⟩ := Written.step hI.frame hI.done hW' hbi (by omega_arith)
  refine ⟨?_, ?_, ?_, ?_, hf', fun k hk => hd' k (by rw [Nat.mul_succ] at hk; omega_arith),
    (hI.keep.trans k').mono (by decide)⟩
  · rw [di', hI.rdi]; exact ptr_step _ i (4 * c)
  · rw [r8', hI.r8]; exact ptr_step _ i nb
  · rw [k'.2.1, hI.rd]
  · rw [k'.2.2, hI.wr]

theorem packLoop_ok {s : State} (hdi : s.gpr .rdi = f) (h8 : s.gpr .r8 = o) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa (packLoop ld d c nb) s fun s' =>
      bytesAt s'.mem o (32 * d) = bitsToBytes (fieldBits d (vals F s₀.mem f)) ∧
        Frame [⟨o, 32 * d⟩] s₀.mem s'.mem ∧ Keep packRegs s s' := by
  have h0 := hs.c0
  have hN : 256 / c ≤ 256 := Nat.div_le_self _ _
  have hN0 : 0 < 256 / c := Nat.div_pos (by have := hs.c8; omega_arith) h0
  refine WP.mono (wp_counted (N := 256 / c)
    (v := BitVec.ofNat 32 (256 / c)) (by rw [BitVec.toNat_ofNat]; omega_arith) hN0
    (PInv (f := f) (o := o) (s₀ := s₀) (sE := s) (F := F) (d := d) (c := c) (nb := nb))
    (fun s₂ m₂ k₂ => ⟨?_, ?_, ?_, ?_, ?_, fun k hk => absurd hk (by omega_arith), k₂.mono (by decide)⟩)
    fun i hi s hI => packStep hld hs hin hout hsep hF hi hI)
    fun s' hI => ⟨?_, hI.frame, hI.keep⟩
  · rw [k₂.gpr (by decide), hdi]; simp
  · rw [k₂.gpr (by decide), h8]; simp
  · rw [k₂.2.1, hrd]
  · rw [k₂.2.2, hwr]
  · rw [m₂, hm]; exact Frame.refl _ _
  · exact bytesAt_eq! (pack_length d _ (by simp)) fun k hk => hI.done k (by rw [hs.bN]; exact hk)

end

/-! ## Unpacking -/

section
variable {fin : Nat → List Instr} {W : Nat → BitVec 32} {d c nb : Nat} (hfin : FinOk fin d W)
  (hs : Shape d c nb) (hu : 2 ≤ nb ∧ (nb < 4 → d ≤ 9)) {v p : Addr} {s₀ sE : State}
  (hin : (⟨v, 32 * d⟩ : Region) ∈ s₀.rd ++ s₀.wr)
  (hout : polyRegion p ∈ s₀.wr) (hsep : Region.Disjoint ⟨v, 32 * d⟩ (polyRegion p))
include hfin hs hu hin hout hsep

/-- The number whose bytes are the input. -/
abbrev inNum (m : Mem) (v : Addr) (d : Nat) : Nat := digits 8 ((bytesAt m v (32 * d)).map (·.toNat))

/-- After `i` groups. -/
structure UInv (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = v + BitVec.ofNat 64 (nb * i)
  rsi : s.gpr .rsi = p + BitVec.ofNat 64 (4 * c * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [polyRegion p] s₀.mem s.mem
  done : ∀ k < c * i, coeffAt s.mem p k = W (inNum s₀.mem v d / 2 ^ (d * k) % 2 ^ d)
  keep : Keep unpackRegs sE s

theorem unpackStep {i : Nat} (hi : i < 256 / c) {s : State}
    (hI : UInv (v := v) (p := p) (s₀ := s₀) (sE := sE) (W := W) (d := d) (c := c) (nb := nb) i s) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      UInv (v := v) (p := p) (s₀ := s₀) (sE := sE) (W := W) (d := d) (c := c) (nb := nb) (i + 1) s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  obtain ⟨hci, hbi⟩ := hs.group hi
  have hnb := hs.nb20
  have hd20 := hs.d20
  have ha : ∀ j, s.gpr .rsi + BitVec.ofNat 64 (4 * j) = coeffAddr p (c * i + j) := fun j => by
    rw [hI.rsi, off_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  have hb : ∀ t, s.gpr .rdi + BitVec.ofNat 64 t = v + BitVec.ofNat 64 (nb * i + t) := fun t => by
    rw [hI.rdi, off_add]
  have hsub : Region.Sub ⟨s.gpr .rsi, 4 * c⟩ (polyRegion p) := by
    rw [hI.rsi]; exact Offset.sub_base p (by rw [Nat.mul_assoc]; omega_arith)
  refine WP.mono (unpackBody_ok hfin hs.d1 hs.d20 hs.dc hs.c8 hu.1 hu.2 s
    (fun t n ht => by rw [hb, hI.rd, hI.wr]; exact inRegions_of hin (Offset.contains_base v (by omega_arith) (by omega_arith)))
    (fun j hj => by rw [ha, hI.wr]; exact inRegions_of hout (coeff_contains p (by omega_arith)))
    (fun t ht => by
      rw [hb]
      exact (hsep.sub_left (Offset.sub_base v (by omega_arith))).sub_right hsub))
    fun s' ⟨hw, hf, di', si', cx', z', k'⟩ => ⟨?_, cx', z'⟩
  -- The bytes of the group, on entry.
  have hB : (List.range nb).map (fun t => (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat) =
      (((bytesAt s₀.mem v (32 * d)).map (·.toNat)).drop (nb * i)).take nb := by
    rw [take_drop_eq _ 0 (by rw [List.length_map, bytesAt_length]; omega_arith)]
    refine List.map_congr_left fun t ht => ?_
    have ht := List.mem_range.mp ht
    rw [getD_map_toNat, bytesAt_getD _ _ (by omega_arith), hb]
    refine congrArg BitVec.toNat (hI.frame _ fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact hsep _ (Offset.contains_base v (by omega_arith) (by omega_arith))
  have hlt : ∀ a ∈ (bytesAt s₀.mem v (32 * d)).map (·.toNat), a < 2 ^ 8 := fun a ha => by
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha; exact x.isLt
  refine ⟨?_, ?_, ?_, ?_, hI.frame.trans (hf.sub fun r hr => ?_), fun k hk => ?_,
    (hI.keep.trans k').mono (by decide)⟩
  · rw [di', hI.rdi]; exact ptr_step _ i nb
  · rw [si', hI.rsi]; exact ptr_step _ i (4 * c)
  · rw [k'.2.1, hI.rd]
  · rw [k'.2.2, hI.wr]
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hsub⟩
  by_cases hk' : k < c * i
  · -- Written before.
    rw [← hI.done k hk', coeffAt_eq, coeffAt_eq]
    refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [hI.rsi]
    exact Offset.disjoint p (by rw [Nat.mul_assoc]; omega_arith) (by omega_arith) (by rw [Nat.mul_assoc]; omega_arith)
  · -- Written by this group.
    have hj : k - c * i < c := by rw [Nat.mul_succ] at hk; omega_arith
    have := hw (k - c * i) hj
    rw [ha, show c * i + (k - c * i) = k by omega_arith, hB, digits_group hs.dc hlt hj,
      show c * i + (k - c * i) = k by omega_arith] at this
    rw [coeffAt_eq, this]

theorem unpackLoop_ok {s : State} (hdi : s.gpr .rdi = v) (hsi : s.gpr .rsi = p) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa (unpackLoop fin d c nb) s fun s' =>
      (∀ k < 256, coeffAt s'.mem p k = W (inNum s₀.mem v d / 2 ^ (d * k) % 2 ^ d)) ∧
        Frame [polyRegion p] s₀.mem s'.mem ∧ Keep unpackRegs s s' := by
  have h0 := hs.c0
  have hN : 256 / c ≤ 256 := Nat.div_le_self _ _
  have hN0 : 0 < 256 / c := Nat.div_pos (by have := hs.c8; omega_arith) h0
  refine WP.mono (wp_counted (N := 256 / c)
    (v := BitVec.ofNat 32 (256 / c)) (by rw [BitVec.toNat_ofNat]; omega_arith) hN0
    (UInv (v := v) (p := p) (s₀ := s₀) (sE := s) (W := W) (d := d) (c := c) (nb := nb))
    (fun s₂ m₂ k₂ => ⟨?_, ?_, ?_, ?_, ?_, fun k hk => absurd hk (by omega_arith), k₂.mono (by decide)⟩)
    fun i hi s hI => unpackStep hfin hs hu hin hout hsep hi hI)
    fun s' hI => ⟨fun k hk' => hI.done k (by rw [hs.cN]; exact hk'), hI.frame, hI.keep⟩
  · rw [k₂.gpr (by decide), hdi]; simp
  · rw [k₂.gpr (by decide), hsi]; simp
  · rw [k₂.2.1, hrd]
  · rw [k₂.2.2, hwr]
  · rw [m₂, hm]; exact Frame.refl _ _

end

end VG.Proof.MlDsa.X86_64.Pack

end

end

/-!
# ML-DSA on x86-64: `vg_mldsa_simple_bit_pack`

The loop is proven once for every width (`packLoop_ok`), and the function by
its three cases.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86_64 (Keep Keep.refl Keep.trans Keep.mono Keep.gpr WP.keep retR pR dArg regsLo agree_regsLo
  gprPreserved_of toNat_setWidth64 read_zero)
open VG.Proof.MlDsa.Pack

theorem sbpLd_ok : LdOk sbpLd BitVec.toNat := fun j s hin => by
  refine WP.keep _ ?_ (by rfl)
  unfold sbpLd
  xrun [ea_at', hin]
  rw [toNat_setWidth64]

/-- A value at most `b` is less than `2 ^ bitlen b`. -/
theorem lt_bitlen {x b : Nat} (h : x ≤ b) : x < 2 ^ bitlen b := Nat.lt_of_le_of_lt h Nat.lt_log2_self

theorem sbpPro_ok (s : State) :
    WP isa (.block [.mov32 .rsi (.reg .rsi), .mov .r8 (.reg .rdx)]) s fun s' =>
      (dArg s' .rsi = dArg s .rsi ∧ s'.gpr .r8 = s.gpr .rdx ∧ s'.mem = s.mem) ∧ Keep [.rsi, .r8] s s' := by
  refine WP.keep _ ?_ (Proof.MlKem.X86_64.writesOnly_of (by decide))
  xrun [dArg]

theorem sbp_wp {s₀ : State} (hp : simpleBitPackK.pre s₀) :
    WP isa Impl.MlDsa.X86_64.Pack.simpleBitPack s₀ fun s' =>
      simpleBitPackK.post s₀ s' ∧ Frame [⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩] s₀.mem s'.mem := by
  obtain ⟨hrd, hwr, hsep, -, -, hb, hlen, hle⟩ := hp
  have go : ∀ {d c nb : Nat}, Shape d c nb → bitlen (dArg s₀ .rsi) = d → ∀ s : State,
      s.gpr .rdi = s₀.gpr .rdi → s.gpr .r8 = s₀.gpr .rdx → s.rd = s₀.rd → s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (packLoop sbpLd d c nb) s fun s' =>
        simpleBitPackK.post s₀ s' ∧ Frame [⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩] s₀.mem s'.mem := by
    intro d c nb hs hd s h1 h2 h3 h4 h5
    rw [hd] at hlen
    refine WP.mono (packLoop_ok sbpLd_ok hs (f := s₀.gpr .rdi) (o := s₀.gpr .rdx) (s₀ := s₀)
      (by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _))
      (by rw [hwr, hlen]; exact List.mem_singleton_self _) (by rw [← hlen]; exact hsep)
      (fun i hi => by rw [← hd]; exact lt_bitlen (hle i hi)) h1 h2 h3 h4 h5)
      fun s' ⟨hB, hf, _⟩ => ⟨?_, by rw [hlen]; exact hf⟩
    show bytesAt s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat = simpleBitPack _ _
    rw [hlen, hB, simpleBitPack_eq, natPolyAt_toList, hd]
  unfold Impl.MlDsa.X86_64.Pack.simpleBitPack
  refine WP.seq (WP.mono (sbpPro_ok s₀) fun s₁ ⟨⟨si₁, r8₁, m₁⟩, k₁⟩ => ?_)
  have di₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.gpr (by decide)
  refine sel_ok .rsi 15 _ _ s₁ (fun s₂ ⟨g₂, m₂, rd₂, wr₂⟩ h => ?_) (fun s₂ ⟨g₂, m₂, rd₂, wr₂⟩ h => ?_)
  · have e : dArg s₀ .rsi = 15 := by rw [← si₁, lo_of_eq h]
    exact go (d := 4) (c := 2) (nb := 1) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by rw [e]; decide) s₂
      (by rw [g₂, di₁]) (by rw [g₂, r8₁]) (by rw [rd₂, k₁.2.1]) (by rw [wr₂, k₁.2.2]) (by rw [m₂, m₁])
  have n15 : dArg s₀ .rsi ≠ 15 := by rw [← si₁]; exact lo_ne h
  have ds₂ : dArg s₂ .rsi = dArg s₀ .rsi := by unfold dArg; rw [g₂]; exact si₁
  refine sel_ok .rsi 43 _ _ s₂ (fun s₃ ⟨g₃, m₃, rd₃, wr₃⟩ h => ?_) (fun s₃ ⟨g₃, m₃, rd₃, wr₃⟩ h => ?_)
  · have e : dArg s₀ .rsi = 43 := by rw [← ds₂, lo_of_eq h]
    exact go (d := 6) (c := 4) (nb := 3) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by rw [e]; decide) s₃
      (by rw [g₃, g₂, di₁]) (by rw [g₃, g₂, r8₁]) (by rw [rd₃, rd₂, k₁.2.1]) (by rw [wr₃, wr₂, k₁.2.2])
      (by rw [m₃, m₂, m₁])
  · have n43 : dArg s₀ .rsi ≠ 43 := by rw [← ds₂]; exact lo_ne h
    have e : dArg s₀ .rsi = 1023 := by
      simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with e | e | e
      · exact e
      · exact absurd e n43
      · exact absurd e n15
    exact go (d := 10) (c := 4) (nb := 5) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by rw [e]; decide) s₃
      (by rw [g₃, g₂, di₁]) (by rw [g₃, g₂, r8₁]) (by rw [rd₃, rd₂, k₁.2.1]) (by rw [wr₃, wr₂, k₁.2.2])
      (by rw [m₃, m₂, m₁])

theorem simpleBitPack_correct (s : State) (hs : simpleBitPackK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Pack.simpleBitPack s t s' ∧ abiPreserved s s' ∧
      simpleBitPackK.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := Impl.MlDsa.X86_64.Pack.simpleBitPack)
    [.rax, .rcx, .rsi, .rdi, .r8, .r10, .r11] (sbp_wp hs) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

theorem simpleBitPack_ct :
    ConstantTime isa simpleBitPackK.pre simpleBitPackK.pub Impl.MlDsa.X86_64.Pack.simpleBitPack :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rdx, .rcx, .rsp] [.rsi])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1])
      fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hp.2.2.2.2)
    (by taint_decide)

/-- In memory of zeros, every coefficient is 0. -/
theorem coeffAt_zero (p : Addr) (i : Nat) : coeffAt (fun _ => 0) p i = 0 := by
  simp only [coeffAt, Mem.readW, read_zero]
  rfl

/-- A state satisfying the precondition. -/
def simpleBitPackSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 15 | .rdx => 0x2000 | .rcx => 128 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 128⟩]

theorem simpleBitPack_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Pack.simpleBitPack (simpleBitPackContract X86_64.abi) :=
  Verified.of_correct simpleBitPack_correct simpleBitPack_ct
    { pre := by sig_implies_pre [simpleBitPackContract, simpleBitPackSig, simpleBitPackK, X86_64.abi, X86_64.argRegs]
      post := by sig_implies_post [simpleBitPackContract, simpleBitPackSig, simpleBitPackK, X86_64.abi, X86_64.argRegs]
      pub := by sig_implies_pub [simpleBitPackContract, simpleBitPackSig, simpleBitPackK, X86_64.abi, X86_64.argRegs]
      sat := by
        refine ⟨simpleBitPackSat, ?_⟩
        sig_pre [simpleBitPackContract, simpleBitPackSig, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | exact fun i _ => by rw [coeffAt_zero]; exact Nat.zero_le _
          | (simp only [simpleBitPackBounds, t1Max_eq]; decide)
          | decide }

end VG.Proof.MlDsa.X86_64.Pack
