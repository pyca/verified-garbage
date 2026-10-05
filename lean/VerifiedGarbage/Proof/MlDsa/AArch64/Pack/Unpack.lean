import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.HintUnpack
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Encode
import VerifiedGarbage.Proof.MlDsa.Pack.Arith

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit`. -/
section

/-!
# ML-DSA on AArch64: the encodings as literals

The code of the packing functions, built by functions of the width, as
literals (`materialize_code`, `Proof/Framework/Lit.lean`).
-/

namespace VG

materialize_code Impl.MlDsa.AArch64.Pack.simpleBitPack
materialize_code Impl.MlDsa.AArch64.Pack.bitPack
materialize_code Impl.MlDsa.AArch64.Pack.bitUnpack
materialize_code Impl.MlDsa.AArch64.Pack.unpackT1

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Pack.SimpleBitPack`. -/
section

/-!
# ML-DSA on AArch64: `vg_mldsa_simple_bit_pack`

The loop is proven once for every width (`packLoop_ok`), and the function by
its three cases, which the length chooses.
-/

namespace VG.Proof.MlDsa.AArch64.Pack

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64 (Only wp_ldrw wp_nil toNat_readW32 abi_of agree_of)
open VG.Proof.MlDsa.Pack

theorem sbpLd_ok (K12 K13 : BitVec 64) : LdOk sbpLd BitVec.toNat K12 K13 := fun j _ _ _ hj hin =>
  wp_ldrw ⟨by omega, by omega⟩ rfl hin fun _ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_nil ⟨by rw [e₁, toNat_readW32], o₁.mono⟩

/-- A value at most `b` is less than `2 ^ bitlen b`. -/
theorem lt_bitlen {x b : Nat} (h : x ≤ b) : x < 2 ^ bitlen b := Nat.lt_of_le_of_lt h Nat.lt_log2_self

/-- The bound and the width, by the length. -/
theorem sbp_cases {b len : Nat} (hb : b ∈ simpleBitPackBounds) (hlen : len = 32 * bitlen b) :
    (b = 15 ∧ bitlen b = 4 ∧ len = 128) ∨ (b = 43 ∧ bitlen b = 6 ∧ len = 192) ∨
      (b = 1023 ∧ bitlen b = 10 ∧ len = 320) := by
  simp only [simpleBitPackBounds, t1Max_eq, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact .inr (.inr ⟨rfl, rfl, hlen⟩)
  · exact .inr (.inl ⟨rfl, rfl, hlen⟩)
  · exact .inl ⟨rfl, rfl, hlen⟩

theorem sbp_wp {s₀ : State} (hp : simpleBitPackK.pre s₀) :
    WP isa Impl.MlDsa.AArch64.Pack.simpleBitPack s₀ fun s' => simpleBitPackK.post s₀ s' := by
  obtain ⟨hrd, hwr, hsep, hb, hlen, hle⟩ := hp
  have go : ∀ {d c nb : Nat}, Shape d c nb → bitlen (wArg s₀ .x1) = d → ∀ s : State, Only [.x9] s₀ s →
      WP isa (packLoop sbpLd d c nb) s fun s' => simpleBitPackK.post s₀ s' := by
    intro d c nb hs hd s o
    rw [hd] at hlen
    refine WP.mono (packLoop_ok (VG.Proof.MlDsa.AArch64.Pack.sbpLd_ok (s.gpr .x12) (s.gpr .x13)) hs (f := s₀.gpr .x0) (o := s₀.gpr .x2)
      (s₀ := s₀) (by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _))
      (by rw [hwr, hlen]; exact List.mem_singleton_self _) (by rw [← hlen]; exact hsep)
      (fun i hi => by rw [← hd]; exact VG.Proof.MlDsa.AArch64.Pack.lt_bitlen (hle i hi)) (o.get .x0) (o.get .x2) rfl rfl o.rd o.wr o.mem)
      fun s' ⟨hB, _, _⟩ => ?_
    show bytesAt s'.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat = simpleBitPack _ _
    rw [hlen, hB, simpleBitPack_eq, natPolyAt_toList, hd]
  have hc := VG.Proof.MlDsa.AArch64.Pack.sbp_cases hb hlen
  unfold Impl.MlDsa.AArch64.Pack.simpleBitPack
  refine sel_ok (by decide) (fun s₁ o₁ h => ?_) (fun s₁ o₁ h => ?_)
  · have e : bitlen (wArg s₀ .x1) = 4 := by omega
    exact go (d := 4) (c := 2) (nb := 1) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e s₁ o₁
  refine sel_ok (by decide) (fun s₂ o₂ h' => ?_) (fun s₂ o₂ h' => ?_)
  · have e : bitlen (wArg s₀ .x1) = 6 := by rw [o₁.get .x3] at h'; omega
    exact go (d := 6) (c := 4) (nb := 3) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e s₂ (o₁.trans o₂).mono
  · have e : bitlen (wArg s₀ .x1) = 10 := by rw [o₁.get .x3] at h'; omega
    exact go (d := 10) (c := 4) (nb := 5) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e s₂ (o₁.trans o₂).mono

theorem simpleBitPack_correct (s : State) (hs : simpleBitPackK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Pack.simpleBitPack s t s' ∧ abiPreserved s s' ∧
      simpleBitPackK.post s s' := by
  obtain ⟨t, s', he, hb⟩ := VG.Proof.MlDsa.AArch64.Pack.sbp_wp hs
  exact ⟨t, s', he, abi_of rfl (by lit_decide) he, hb⟩

theorem simpleBitPack_ct :
    ConstantTime isa simpleBitPackK.pre simpleBitPackK.pub Impl.MlDsa.AArch64.Pack.simpleBitPack :=
  VG.Taint.constantTime (A := VG.AArch64.taint) (Taint.ofRegs [.x0, .x2, .x3])
    (fun _ _ _ _ ⟨h0, h2, h3, hsp⟩ => agree_of hsp (by simp [h0, h2, h3])) (by taint_decide)

/-- A state satisfying the precondition. -/
def simpleBitPackSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 15 | .x2 => 0x2000 | .x3 => 128 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 128⟩]

theorem simpleBitPack_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Pack.simpleBitPack (simpleBitPackContract AArch64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.AArch64.Pack.simpleBitPack_correct VG.Proof.MlDsa.AArch64.Pack.simpleBitPack_ct
    { pre := by sig_implies_pre [simpleBitPackContract, simpleBitPackSig, simpleBitPackK, AArch64.abi,
        AArch64.argRegs]
      post := by sig_implies_post [simpleBitPackContract, simpleBitPackSig, simpleBitPackK, AArch64.abi,
        AArch64.argRegs]
      pub := by sig_implies_pub [simpleBitPackContract, simpleBitPackSig, simpleBitPackK, AArch64.abi,
        AArch64.argRegs]
      sat := by
        refine ⟨VG.Proof.MlDsa.AArch64.Pack.simpleBitPackSat, ?_⟩
        sig_pre [simpleBitPackContract, simpleBitPackSig, AArch64.abi, AArch64.argRegs]
        and_intros
        all_goals first
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | exact fun i _ => by rw [VG.Proof.MlDsa.AArch64.Pack.coeffAt_zero]; exact Nat.zero_le _
          | (simp only [simpleBitPackBounds, t1Max_eq]; decide)
          | decide }

end VG.Proof.MlDsa.AArch64.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Pack.BitPack`. -/
section

/-!
# ML-DSA on AArch64: `vg_mldsa_bit_pack`

The value of a coefficient `x` is `b - x` in 64 bits, plus `q` times its sign
bit (`subModQ`), which is `b - (x mod± q)` for a reduced `x`
(`Pack/Arith.lean`). The loop is proven once for every width (`packLoop_ok`),
and the function by its five cases, which the length chooses.
-/

namespace VG.Proof.MlDsa.AArch64.Pack

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64 (Only wp_ldrw wp_sub wp_lsr wp_madd wp_mov wp_movImm wp_nil abi_of agree_of)
open VG.Proof.MlDsa.Pack

/-- `b - x`, plus `q` if it is negative, as the code computes it in 64 bits. -/
def subModQ (b x : BitVec 64) : BitVec 64 := b - x + ((b - x) >>> 63) * BitVec.ofNat 64 q

theorem subModQ_toNat {b x : Nat} (hb : b < q) (hx : x < q) :
    (VG.Proof.MlDsa.AArch64.Pack.subModQ (BitVec.ofNat 64 b) (BitVec.ofNat 64 x)).toNat = (b + q - x) % q := by
  have hq : q = 8380417 := rfl
  have hs : (BitVec.ofNat 64 b - BitVec.ofNat 64 x).toNat = (2 ^ 64 - x + b) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := b) (by omega),
      Nat.mod_eq_of_lt (a := x) (by omega)]
  unfold VG.Proof.MlDsa.AArch64.Pack.subModQ
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hs,
    BitVec.toNat_ofNat, hq]
  by_cases h : x ≤ b
  · rw [show (2 ^ 64 - x + b) % 2 ^ 64 = b - x by omega]
    omega
  · rw [show (2 ^ 64 - x + b) % 2 ^ 64 = 2 ^ 64 - x + b by omega]
    omega

/-- The value `bpLd` loads of a word, for `b = B`. -/
abbrev bpVal (B : Nat) (w : BitVec 32) : Nat := (VG.Proof.MlDsa.AArch64.Pack.subModQ (BitVec.ofNat 64 B) (w.setWidth 64)).toNat

theorem bpLd_ok (B : Nat) : LdOk bpLd (VG.Proof.MlDsa.AArch64.Pack.bpVal B) (BitVec.ofNat 64 B) (BitVec.ofNat 64 q) :=
  fun j s h12 h13 hj hin =>
  wp_ldrw ⟨by omega, by omega⟩ rfl hin fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_sub fun s₂ o₂ e₂ => VG.Proof.MlKem.AArch64.wp_lsr (by decide) fun s₃ o₃ e₃ =>
    wp_madd fun s₄ o₄ e₄ => VG.Proof.MlKem.AArch64.wp_nil ⟨by
      rw [e₄, e₃, o₃.get .x10, o₃.get .x13, e₂, o₂.get .x13, o₁.get .x12, o₁.get .x13, h12, h13, e₁]; rfl,
      (((o₁.trans o₂).trans o₃).trans o₄).mono⟩

/-- The arguments and the width, by the length. -/
theorem bp_cases {a b len : Nat} (hab : (a, b) ∈ bitPackParams) (hlen : len = 32 * bitlen (a + b)) :
    (b = 2 ∧ bitlen (a + b) = 3 ∧ len = 96) ∨ (b = 4 ∧ bitlen (a + b) = 4 ∧ len = 128) ∨
      (b = 4096 ∧ bitlen (a + b) = 13 ∧ len = 416) ∨ (b = 131072 ∧ bitlen (a + b) = 18 ∧ len = 576) ∨
      (b = 524288 ∧ bitlen (a + b) = 20 ∧ len = 640) := by
  rcases mem_bitPackParams hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .inl ⟨rfl, rfl, hlen⟩
  · exact .inr (.inl ⟨rfl, rfl, hlen⟩)
  · exact .inr (.inr (.inl ⟨rfl, rfl, hlen⟩))
  · exact .inr (.inr (.inr (.inl ⟨rfl, rfl, hlen⟩)))
  · exact .inr (.inr (.inr (.inr ⟨rfl, rfl, hlen⟩)))

/-- The values the loop packs are those of `BitPack`. -/
theorem bitPack_vals {m : Mem} {f : Addr} (hr : Reduced m f) {b : Nat} (hb : b ≤ q / 2)
    (hle : ∀ i < n, modPm (coeffAt m f i).toNat q ≤ b) :
    ((polyAt m f).map fun c => modPm c.val q).toList.map (fun wi => ((b : Int) - wi).toNat) =
      vals (VG.Proof.MlDsa.AArch64.Pack.bpVal b) m f := by
  rw [Vector.toList_map, polyAt, toList_ofFn (fun i => Fin.ofNat q (coeffAt m f i).toNat), List.map_map,
    List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hx := hr i hi
  simp only [Function.comp_apply, Fin.val_ofNat, Nat.mod_eq_of_lt hx]
  rw [VG.Proof.MlDsa.AArch64.Pack.bpVal, ← BitVec.ofNat_toNat, VG.Proof.MlDsa.AArch64.Pack.subModQ_toNat (by omega) hx, sub_modPm hx hb (hle i hi)]

theorem bp_wp {s₀ : State} (hp : bitPackK.pre s₀) :
    WP isa Impl.MlDsa.AArch64.Pack.bitPack s₀ fun s' => bitPackK.post s₀ s' := by
  obtain ⟨hrd, hwr, hsep, hab, hlen, hred, hbnd⟩ := hp
  have hc := VG.Proof.MlDsa.AArch64.Pack.bp_cases hab hlen
  have go : ∀ {d c nb B : Nat}, Shape d c nb → wArg s₀ .x2 = B → bitlen (wArg s₀ .x1 + wArg s₀ .x2) = d →
      ∀ s : State, s.gpr .x0 = s₀.gpr .x0 → s.gpr .x2 = s₀.gpr .x3 → s.gpr .x13 = BitVec.ofNat 64 q →
      s.rd = s₀.rd → s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (bpWidth B d c nb) s fun s' => bitPackK.post s₀ s' := by
    intro d c nb B hs hB hd s h0 h2 h13 h3 h4 h5
    rw [hd] at hlen
    have hq : q = 8380417 := rfl
    have hB19 : B ≤ 2 ^ 19 := by omega
    refine WP.seq ?_
    rw [← List.append_nil (Impl.MlKem.AArch64.movImm _ _)]
    refine wp_movImm fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_nil ?_
    refine WP.mono (packLoop_ok (VG.Proof.MlDsa.AArch64.Pack.bpLd_ok B) hs (f := s₀.gpr .x0) (o := s₀.gpr .x3) (s₀ := s₀)
      (by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _))
      (by rw [hwr, hlen]; exact List.mem_singleton_self _) (by rw [← hlen]; exact hsep)
      (fun i hi => ?_) (by rw [o₁.get .x0, h0]) (by rw [o₁.get .x2, h2]) e₁ (by rw [o₁.get .x13, h13])
      (by rw [o₁.rd, h3]) (by rw [o₁.wr, h4]) (by rw [o₁.mem, h5]))
      fun s' ⟨hB', _, _⟩ => ?_
    · obtain ⟨h₁, h₂⟩ := hbnd i hi
      rw [hB] at h₂
      have hx := hred i hi
      rw [VG.Proof.MlDsa.AArch64.Pack.bpVal, ← BitVec.ofNat_toNat, VG.Proof.MlDsa.AArch64.Pack.subModQ_toNat (by omega) hx, ← sub_modPm hx (by omega) h₂, ← hd, hB]
      exact VG.Proof.MlDsa.AArch64.Pack.lt_bitlen (sub_modPm_le h₁ h₂)
    · show bytesAt s'.mem (s₀.gpr .x3) (s₀.gpr .x4).toNat = bitPack _ _ _
      rw [hlen, hB', bitPack_eq, VG.Proof.MlDsa.AArch64.Pack.bitPack_vals hred (by omega) (fun i hi => (hbnd i hi).2), hd,
        hB]
  unfold Impl.MlDsa.AArch64.Pack.bitPack
  refine WP.seq (VG.Proof.MlKem.AArch64.wp_mov fun s₁ o₁ e₁ => ?_)
  rw [← List.append_nil (Impl.MlKem.AArch64.movImm _ _)]
  refine wp_movImm fun s₂ o₂ e₂ => VG.Proof.MlKem.AArch64.wp_nil ?_
  have k₂ := o₁.trans o₂
  have h0 : s₂.gpr .x0 = s₀.gpr .x0 := k₂.get .x0
  have h2 : s₂.gpr .x2 = s₀.gpr .x3 := by rw [o₂.get .x2, e₁]
  have h4 : s₂.gpr .x4 = s₀.gpr .x4 := k₂.get .x4
  have h13 : s₂.gpr .x13 = BitVec.ofNat 64 q := e₂
  refine sel_ok (by decide) (fun s₃ o₃ h => ?_) (fun s₃ o₃ h => ?_)
  · rw [h4] at h
    exact go (d := 3) (c := 8) (nb := 3) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by omega) (by omega) s₃ (by rw [o₃.get .x0, h0]) (by rw [o₃.get .x2, h2]) (by rw [o₃.get .x13, h13])
      (by rw [o₃.rd, k₂.rd]) (by rw [o₃.wr, k₂.wr]) (by rw [o₃.mem, k₂.mem])
  have k₃ := k₂.trans o₃
  rw [h4] at h
  refine sel_ok (by decide) (fun s₄ o₄ h' => ?_) (fun s₄ o₄ h' => ?_)
  · rw [o₃.get .x4, h4] at h'
    exact go (d := 4) (c := 2) (nb := 1) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by omega) (by omega) s₄ (by rw [o₄.get .x0, k₃.get .x0]) (by rw [o₄.get .x2, o₃.get .x2, h2])
      (by rw [o₄.get .x13, o₃.get .x13, h13]) (by rw [o₄.rd, k₃.rd]) (by rw [o₄.wr, k₃.wr])
      (by rw [o₄.mem, k₃.mem])
  have k₄ := k₃.trans o₄
  rw [o₃.get .x4, h4] at h'
  refine sel_ok (by decide) (fun s₅ o₅ h'' => ?_) (fun s₅ o₅ h'' => ?_)
  · rw [o₄.get .x4, o₃.get .x4, h4] at h''
    exact go (d := 13) (c := 8) (nb := 13) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by omega) (by omega) s₅ (by rw [o₅.get .x0, k₄.get .x0]) (by rw [o₅.get .x2, o₄.get .x2, o₃.get .x2, h2])
      (by rw [o₅.get .x13, o₄.get .x13, o₃.get .x13, h13]) (by rw [o₅.rd, k₄.rd]) (by rw [o₅.wr, k₄.wr])
      (by rw [o₅.mem, k₄.mem])
  have k₅ := k₄.trans o₅
  rw [o₄.get .x4, o₃.get .x4, h4] at h''
  refine sel_ok (by decide) (fun s₆ o₆ h''' => ?_) (fun s₆ o₆ h''' => ?_)
  · rw [o₅.get .x4, o₄.get .x4, o₃.get .x4, h4] at h'''
    exact go (d := 18) (c := 4) (nb := 9) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by omega) (by omega) s₆ (by rw [o₆.get .x0, k₅.get .x0])
      (by rw [o₆.get .x2, o₅.get .x2, o₄.get .x2, o₃.get .x2, h2])
      (by rw [o₆.get .x13, o₅.get .x13, o₄.get .x13, o₃.get .x13, h13]) (by rw [o₆.rd, k₅.rd])
      (by rw [o₆.wr, k₅.wr]) (by rw [o₆.mem, k₅.mem])
  · rw [o₅.get .x4, o₄.get .x4, o₃.get .x4, h4] at h'''
    exact go (d := 20) (c := 2) (nb := 5) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by omega) (by omega) s₆ (by rw [o₆.get .x0, k₅.get .x0])
      (by rw [o₆.get .x2, o₅.get .x2, o₄.get .x2, o₃.get .x2, h2])
      (by rw [o₆.get .x13, o₅.get .x13, o₄.get .x13, o₃.get .x13, h13]) (by rw [o₆.rd, k₅.rd])
      (by rw [o₆.wr, k₅.wr]) (by rw [o₆.mem, k₅.mem])

theorem bitPack_correct (s : State) (hs : bitPackK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Pack.bitPack s t s' ∧ abiPreserved s s' ∧ bitPackK.post s s' := by
  obtain ⟨t, s', he, hb⟩ := VG.Proof.MlDsa.AArch64.Pack.bp_wp hs
  exact ⟨t, s', he, abi_of rfl (by lit_decide) he, hb⟩

theorem bitPack_ct : ConstantTime isa bitPackK.pre bitPackK.pub Impl.MlDsa.AArch64.Pack.bitPack :=
  VG.Taint.constantTime (A := VG.AArch64.taint) (Taint.ofRegs [.x0, .x3, .x4])
    (fun _ _ _ _ ⟨h0, h3, h4, hsp⟩ => agree_of hsp (by simp [h0, h3, h4])) (by taint_decide)

/-- A state satisfying the precondition. -/
def bitPackSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 2 | .x2 => 2 | .x3 => 0x2000 | .x4 => 96 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 96⟩]

theorem bitPack_verified : Verified AArch64.target Impl.MlDsa.AArch64.Pack.bitPack (bitPackContract AArch64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.AArch64.Pack.bitPack_correct VG.Proof.MlDsa.AArch64.Pack.bitPack_ct
    { pre := by sig_implies_pre [bitPackContract, bitPackSig, bitPackK, AArch64.abi, AArch64.argRegs]
      post := by sig_implies_post [bitPackContract, bitPackSig, bitPackK, AArch64.abi, AArch64.argRegs]
      pub := by sig_implies_pub [bitPackContract, bitPackSig, bitPackK, AArch64.abi, AArch64.argRegs]
      sat := by
        refine ⟨VG.Proof.MlDsa.AArch64.Pack.bitPackSat, ?_⟩
        sig_pre [bitPackContract, bitPackSig, AArch64.abi, AArch64.argRegs]
        and_intros
        all_goals first
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | exact fun i _ => by rw [VG.Proof.MlDsa.AArch64.Pack.coeffAt_zero]; decide
          | (simp only [bitPackParams]; decide)
          | decide }

end VG.Proof.MlDsa.AArch64.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Unpack`. -/
section

/-!
# ML-DSA on AArch64: `vg_mldsa_bit_unpack` and `vg_mldsa_unpack_t1`

The coefficient of a field `y` is `b - y` in 64 bits, plus `q` times its sign
bit (`subModQ`), which is `b - y` in `ℤ_q` (`Pack/Arith.lean`), or `y · 2¹³`.
The loop is proven once for every width (`unpackLoop_ok`), and
`vg_mldsa_bit_unpack` by its five cases, which the length chooses.
-/

namespace VG.Proof.MlDsa.AArch64.Pack

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64 (Only wp_sub wp_lsr wp_lsl wp_madd wp_mov wp_movImm wp_strw wp_nil abi_of agree_of
  toNat_lsl_n)
open VG.Proof.MlDsa.Pack

/-- The word `buFin` stores for the field `y`, for `b = B`. -/
abbrev buWord (B y : Nat) : BitVec 32 := (VG.Proof.MlDsa.AArch64.Pack.subModQ (BitVec.ofNat 64 B) (BitVec.ofNat 64 y)).setWidth 32

theorem buFin_ok (B d : Nat) : FinOk buFin d (VG.Proof.MlDsa.AArch64.Pack.buWord B) (BitVec.ofNat 64 B) (BitVec.ofNat 64 q) :=
  fun j s h12 h13 hj hout _ =>
  VG.Proof.MlKem.AArch64.wp_sub fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_lsr (by decide) fun s₂ o₂ e₂ => wp_madd fun s₃ o₃ e₃ =>
    wp_strw ⟨by omega, by omega⟩ (by rw [o₃.get .x4, o₂.get .x4, o₁.get .x4])
      (by rw [o₃.wr, o₂.wr, o₁.wr]; exact hout) fun s₄ h₄ => VG.Proof.MlKem.AArch64.wp_nil ⟨by
        rw [h₄.mem, o₃.mem, o₂.mem, o₁.mem, e₃, e₂, o₂.get .x10, o₂.get .x13, e₁, o₁.get .x13, h12, h13,
          VG.Proof.MlDsa.AArch64.Pack.buWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl,
        (((o₁.keep.trans o₂.keep).trans o₃.keep).trans h₄.keep).mono⟩

/-- The word `t1Fin` stores for the field `y`. -/
abbrev t1Word (y : Nat) : BitVec 32 := (BitVec.ofNat 64 y <<< 13).setWidth 32

theorem t1Fin_ok (K12 K13 : BitVec 64) : FinOk t1Fin 10 VG.Proof.MlDsa.AArch64.Pack.t1Word K12 K13 := fun j s _ _ hj hout _ =>
  wp_lsl (by decide) fun s₁ o₁ e₁ =>
    wp_strw ⟨by omega, by omega⟩ (by rw [o₁.get .x4]) (by rw [o₁.wr]; exact hout) fun s₂ h₂ => VG.Proof.MlKem.AArch64.wp_nil ⟨by
      rw [h₂.mem, o₁.mem, e₁, VG.Proof.MlDsa.AArch64.Pack.t1Word, BitVec.ofNat_toNat, BitVec.setWidth_eq], (o₁.keep.trans h₂.keep).mono⟩

/-- A field of `d ≤ 20` bits of the input. -/
theorem field_lt (X d k : Nat) (hd : d ≤ 20) : X / 2 ^ (d * k) % 2 ^ d < 2 ^ 20 :=
  Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos d)) (Nat.pow_le_pow_right (by decide) hd)

theorem bu_wp {s₀ : State} (hp : bitUnpackK.pre s₀) :
    WP isa Impl.MlDsa.AArch64.Pack.bitUnpack s₀ fun s' => bitUnpackK.post s₀ s' := by
  obtain ⟨hrd, hwr, hsep, hab, hlen⟩ := hp
  have hc := VG.Proof.MlDsa.AArch64.Pack.bp_cases hab hlen
  have go : ∀ {d c nb B : Nat}, Shape d c nb → wArg s₀ .x3 = B → bitlen (wArg s₀ .x2 + wArg s₀ .x3) = d →
      ∀ s : State, s.gpr .x0 = s₀.gpr .x0 → s.gpr .x4 = s₀.gpr .x4 → s.gpr .x13 = BitVec.ofNat 64 q →
      s.rd = s₀.rd → s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (buWidth B d c nb) s fun s' => bitUnpackK.post s₀ s' := by
    intro d c nb B hs hB hd s h0 h4 h13 h3 h5 h6
    rw [hd] at hlen
    have hq : q = 8380417 := rfl
    have hB19 : B ≤ 2 ^ 19 := by omega
    refine WP.seq ?_
    rw [← List.append_nil (Impl.MlKem.AArch64.movImm _ _)]
    refine wp_movImm fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_nil ?_
    refine WP.mono (unpackLoop_ok (VG.Proof.MlDsa.AArch64.Pack.buFin_ok B d) hs (v := s₀.gpr .x0) (p := s₀.gpr .x4) (s₀ := s₀)
      (by rw [hrd, hlen]; exact List.mem_append_left _ (List.mem_singleton_self _))
      (by rw [hwr]; exact List.mem_singleton_self _) (by rw [← hlen]; exact hsep)
      (by rw [o₁.get .x0, h0]) (by rw [o₁.get .x4, h4]) e₁ (by rw [o₁.get .x13, h13])
      (by rw [o₁.rd, h3]) (by rw [o₁.wr, h5]) (by rw [o₁.mem, h6]))
      fun s' ⟨hc', _, _⟩ => ?_
    show PolyIs s'.mem (s₀.gpr .x4) (toRq (bitUnpack (bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat) _ _))
    refine polyIs_of_toNat fun i hi => ?_
    have hy := VG.Proof.MlDsa.AArch64.Pack.field_lt (inNum s₀.mem (s₀.gpr .x0) d) d i hs.d20
    have hy' := hy
    unfold inNum at hy'
    rw [hc' i hi, VG.Proof.MlDsa.AArch64.Pack.buWord, BitVec.toNat_setWidth, VG.Proof.MlDsa.AArch64.Pack.subModQ_toNat (by omega) (by omega),
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (show 0 < q by decide)) (by decide)),
      toRq, Vector.getElem_map, bitUnpack_get _ _ _ hi, hlen, hd, hB, ofInt_sub (by omega)]
  unfold Impl.MlDsa.AArch64.Pack.bitUnpack
  refine WP.seq ?_
  rw [← List.append_nil (Impl.MlKem.AArch64.movImm _ _)]
  refine wp_movImm fun s₂ o₂ e₂ => VG.Proof.MlKem.AArch64.wp_nil ?_
  have h0 : s₂.gpr .x0 = s₀.gpr .x0 := o₂.get .x0
  have h1 : s₂.gpr .x1 = s₀.gpr .x1 := o₂.get .x1
  have h4 : s₂.gpr .x4 = s₀.gpr .x4 := o₂.get .x4
  have h13 : s₂.gpr .x13 = BitVec.ofNat 64 q := e₂
  refine sel_ok (by decide) (fun s₃ o₃ h => ?_) (fun s₃ o₃ h => ?_)
  · rw [h1] at h
    exact go (d := 3) (c := 8) (nb := 3) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by omega) (by omega) s₃ (by rw [o₃.get .x0, h0]) (by rw [o₃.get .x4, h4]) (by rw [o₃.get .x13, h13])
      (by rw [o₃.rd, o₂.rd]) (by rw [o₃.wr, o₂.wr]) (by rw [o₃.mem, o₂.mem])
  have k₃ := o₂.trans o₃
  rw [h1] at h
  refine sel_ok (by decide) (fun s₄ o₄ h' => ?_) (fun s₄ o₄ h' => ?_)
  · rw [o₃.get .x1, h1] at h'
    exact go (d := 4) (c := 2) (nb := 1) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by omega) (by omega) s₄ (by rw [o₄.get .x0, k₃.get .x0]) (by rw [o₄.get .x4, k₃.get .x4])
      (by rw [o₄.get .x13, o₃.get .x13, h13]) (by rw [o₄.rd, k₃.rd]) (by rw [o₄.wr, k₃.wr])
      (by rw [o₄.mem, k₃.mem])
  have k₄ := k₃.trans o₄
  rw [o₃.get .x1, h1] at h'
  refine sel_ok (by decide) (fun s₅ o₅ h'' => ?_) (fun s₅ o₅ h'' => ?_)
  · rw [o₄.get .x1, o₃.get .x1, h1] at h''
    exact go (d := 13) (c := 8) (nb := 13) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by omega) (by omega) s₅ (by rw [o₅.get .x0, k₄.get .x0]) (by rw [o₅.get .x4, k₄.get .x4])
      (by rw [o₅.get .x13, o₄.get .x13, o₃.get .x13, h13]) (by rw [o₅.rd, k₄.rd]) (by rw [o₅.wr, k₄.wr])
      (by rw [o₅.mem, k₄.mem])
  have k₅ := k₄.trans o₅
  rw [o₄.get .x1, o₃.get .x1, h1] at h''
  refine sel_ok (by decide) (fun s₆ o₆ h''' => ?_) (fun s₆ o₆ h''' => ?_)
  · rw [o₅.get .x1, o₄.get .x1, o₃.get .x1, h1] at h'''
    exact go (d := 18) (c := 4) (nb := 9) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by omega) (by omega) s₆ (by rw [o₆.get .x0, k₅.get .x0]) (by rw [o₆.get .x4, k₅.get .x4])
      (by rw [o₆.get .x13, o₅.get .x13, o₄.get .x13, o₃.get .x13, h13]) (by rw [o₆.rd, k₅.rd])
      (by rw [o₆.wr, k₅.wr]) (by rw [o₆.mem, k₅.mem])
  · rw [o₅.get .x1, o₄.get .x1, o₃.get .x1, h1] at h'''
    exact go (d := 20) (c := 2) (nb := 5) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by omega) (by omega) s₆ (by rw [o₆.get .x0, k₅.get .x0]) (by rw [o₆.get .x4, k₅.get .x4])
      (by rw [o₆.get .x13, o₅.get .x13, o₄.get .x13, o₃.get .x13, h13]) (by rw [o₆.rd, k₅.rd])
      (by rw [o₆.wr, k₅.wr]) (by rw [o₆.mem, k₅.mem])

theorem bitUnpack_correct (s : State) (hs : bitUnpackK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Pack.bitUnpack s t s' ∧ abiPreserved s s' ∧ bitUnpackK.post s s' := by
  obtain ⟨t, s', he, hb⟩ := VG.Proof.MlDsa.AArch64.Pack.bu_wp hs
  exact ⟨t, s', he, abi_of rfl (by lit_decide) he, hb⟩

theorem bitUnpack_ct : ConstantTime isa bitUnpackK.pre bitUnpackK.pub Impl.MlDsa.AArch64.Pack.bitUnpack :=
  VG.Taint.constantTime (A := VG.AArch64.taint) (Taint.ofRegs [.x0, .x1, .x4])
    (fun _ _ _ _ ⟨h0, h1, h4, hsp⟩ => agree_of hsp (by simp [h0, h1, h4])) (by taint_decide)

/-- A state satisfying the precondition. -/
def bitUnpackSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 96 | .x2 => 2 | .x3 => 2 | .x4 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 96⟩]
  wr := [⟨0x2000, 1024⟩]

theorem bitUnpack_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Pack.bitUnpack (bitUnpackContract AArch64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.AArch64.Pack.bitUnpack_correct VG.Proof.MlDsa.AArch64.Pack.bitUnpack_ct
    { pre := by sig_implies_pre [bitUnpackContract, bitUnpackSig, bitUnpackK, AArch64.abi, AArch64.argRegs]
      post := by sig_implies_post [bitUnpackContract, bitUnpackSig, bitUnpackK, AArch64.abi, AArch64.argRegs]
      pub := by sig_implies_pub [bitUnpackContract, bitUnpackSig, bitUnpackK, AArch64.abi, AArch64.argRegs]
      sat := by
        refine ⟨VG.Proof.MlDsa.AArch64.Pack.bitUnpackSat, ?_⟩
        sig_pre [bitUnpackContract, bitUnpackSig, AArch64.abi, AArch64.argRegs]
        and_intros
        all_goals first
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | (simp only [bitPackParams]; decide)
          | decide }

/-! ## `vg_mldsa_unpack_t1` -/

theorem t1_wp {s₀ : State} (hp : unpackT1K.pre s₀) :
    WP isa Impl.MlDsa.AArch64.Pack.unpackT1 s₀ fun s' => unpackT1K.post s₀ s' := by
  obtain ⟨hrd, hwr, hsep⟩ := hp
  refine WP.seq (VG.Proof.MlKem.AArch64.wp_mov fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_nil ?_)
  refine WP.mono (unpackLoop_ok (VG.Proof.MlDsa.AArch64.Pack.t1Fin_ok (s₁.gpr .x12) (s₁.gpr .x13)) (c := 4) (nb := 5)
    ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ (v := s₀.gpr .x0) (p := s₀.gpr .x1) (s₀ := s₀)
    (by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _))
    (by rw [hwr]; exact List.mem_singleton_self _) hsep (o₁.get .x0) e₁ rfl rfl o₁.rd o₁.wr o₁.mem)
    fun s' ⟨hc, _, _⟩ => ?_
  refine polyIs_of_toNat fun i hi => ?_
  have hy : inNum s₀.mem (s₀.gpr .x0) 10 / 2 ^ (10 * i) % 2 ^ 10 < 2 ^ 10 := Nat.mod_lt _ (by decide)
  rw [hc i hi, VG.Proof.MlDsa.AArch64.Pack.t1Word, BitVec.toNat_setWidth, toNat_lsl_n (by rw [BitVec.toNat_ofNat]; omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show _ < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show _ < 2 ^ 32 by omega),
    Vector.getElem_map, simpleBitUnpack_get _ _ hi, show bitlen t1Max = 10 by decide, ofInt_t1 hy]

theorem unpackT1_correct (s : State) (hs : unpackT1K.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Pack.unpackT1 s t s' ∧ abiPreserved s s' ∧ unpackT1K.post s s' := by
  obtain ⟨t, s', he, hb⟩ := VG.Proof.MlDsa.AArch64.Pack.t1_wp hs
  exact ⟨t, s', he, abi_of rfl (by lit_decide) he, hb⟩

theorem unpackT1_ct : ConstantTime isa unpackT1K.pre unpackT1K.pub Impl.MlDsa.AArch64.Pack.unpackT1 :=
  VG.Taint.constantTime (A := VG.AArch64.taint) (Taint.ofRegs [.x0, .x1])
    (fun _ _ _ _ ⟨h0, h1, hsp⟩ => agree_of hsp (by simp [h0, h1])) (by taint_decide)

/-- A state satisfying the precondition. -/
def unpackT1Sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 320⟩]
  wr := [⟨0x2000, 1024⟩]

theorem unpackT1_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Pack.unpackT1 (unpackT1Contract AArch64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.AArch64.Pack.unpackT1_correct VG.Proof.MlDsa.AArch64.Pack.unpackT1_ct
    { pre := by sig_implies_pre [unpackT1Contract, unpackT1Sig, unpackT1K, AArch64.abi, AArch64.argRegs]
      post := by sig_implies_post [unpackT1Contract, unpackT1Sig, unpackT1K, AArch64.abi, AArch64.argRegs]
      pub := by sig_implies_pub [unpackT1Contract, unpackT1Sig, unpackT1K, AArch64.abi, AArch64.argRegs]
      sat := by
        refine ⟨VG.Proof.MlDsa.AArch64.Pack.unpackT1Sat, ?_⟩
        sig_pre [unpackT1Contract, unpackT1Sig, AArch64.abi, AArch64.argRegs]
        and_intros
        all_goals first
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | decide }

end VG.Proof.MlDsa.AArch64.Pack

end
