import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Proof.X448.X86.Verified
import VerifiedGarbage.Impl.Ed448.X86.Scalar
import VerifiedGarbage.Impl.Ed448.X86.ScalarBase
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Inline

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.ScalarStep`. -/
section

/-!
# Ed448 scalar arithmetic on x86 (32-bit): one chunk

`fold o` computes the limbs of `l + h c` into `TF` from the remainder at `o`
and the chunk at `W` (`fold_ok`); `reduceT o` the remainder of `TF` modulo
`L` into `o` (`reduceT_ok`); together, `step o` folds a chunk into the
remainder (`step_ok`). The working space is X448's (`Scr`: its base in
`edi`), its numbers X448's limbs (`limbs`, `fe`, `Bounded`).
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.Radix16 VG.Proof.X448.X86 VG.Proof.Ed448.Limbs16
open VG.Impl.Ed448.X86 (W TF RA SK SS SR cLimb cLimbs kLimb foldHead foldSrc fold csubSrc reduceT step)
open VG.Spec.Ed448 (L)
open VG.Proof.Ed448 (cL)

/-! ## Constants -/

theorem cLimb_high {k : Nat} (h : 14 ≤ k) : cLimb k = 0 := by
  rw [cLimb, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
    simp only [cLimbs, List.length_cons, List.length_nil]; omega)]
  rfl

theorem cLimb_lt (k : Nat) : cLimb k < VG.Proof.X448.Radix16.radix := by
  by_cases h : k < 14
  · have : ∀ k < 14, cLimb k < VG.Proof.X448.Radix16.radix := by decide
    exact this k h
  · rw [VG.Proof.Ed448.X86.cLimb_high (by omega)]; decide

theorem kLimb_lt (k : Nat) : kLimb k < VG.Proof.X448.Radix16.radix := by
  unfold kLimb; split
  · decide
  · exact VG.Proof.Ed448.X86.cLimb_lt k

theorem kLimb_mid {k : Nat} (h1 : 14 ≤ k) (h2 : k ≠ 27) : kLimb k = 0 := by
  rw [kLimb, ite_eq_right h2, VG.Proof.Ed448.X86.cLimb_high h1]

theorem valN_cLimb : VG.Proof.X448.Radix16.valN cLimb 28 = cL := by decide +kernel

theorem valN_kLimb : VG.Proof.X448.Radix16.valN kLimb 28 = VG.Proof.X448.Radix16.radix ^ 28 - L := by decide +kernel

/-! ## Instruction facts -/

theorem readSc {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 4 ≤ 8192) :
    VG.X86.readSrc s (.mem (Impl.X448.X86.sc d)) = some (word s.mem base d) := by
  simp only [VG.X86.readSrc, hs.ea (by omega : d < 8192), State.load32, hs.read hd, ite_true]

theorem toNat_imm {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 32 v).toNat = v := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem toNat_add_lt {a b : BitVec 32} (h : a.toNat + b.toNat < 2 ^ 32) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem toNat_shr (x : BitVec 32) (n : Nat) : (x >>> n).toNat = x.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- Rotating a number below `2^14` right by 30 multiplies it by 4. -/
theorem toNat_rotr30 (x : BitVec 32) (h : x.toNat < 16384) : (x.rotateRight 30).toNat = 4 * x.toNat := by
  have hz : x >>> 30 = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [VG.Proof.Ed448.X86.toNat_shr]
    change x.toNat / 2 ^ 30 = 0
    omega
  have e : x.rotateRight 30 = x <<< 2 := by
    rw [BitVec.rotateRight_def, hz]; exact BitVec.zero_or
  rw [e, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  change x.toNat * 4 % 4294967296 = _
  omega

theorem toNat_and14 (x : BitVec 32) : (x &&& (16383 : BitVec 32)).toNat = x.toNat % 16384 := by
  rw [BitVec.toNat_and, show (16383 : BitVec 32).toNat = 2 ^ 14 - 1 by rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-- The product of `mul` below `2^32`. -/
theorem toNat_mul_lt {a b : Nat} (h : a * b < 2 ^ 32) : (BitVec.ofNat 32 (a * b)).toNat = a * b :=
  VG.Proof.Ed448.X86.toNat_imm h

/-! ## Folding a chunk in -/

/-- A remainder's place: after `TF`, with offsets below 4096. -/
def Buf (o : Nat) : Prop := TF + 112 ≤ o ∧ o + 112 ≤ 4096

theorem TF_eq : TF = 64 := rfl
theorem W_eq : W = 16 := rfl

theorem foldHead_ok {o : Nat} (ho : VG.Proof.Ed448.X86.Buf o) {s : State} {base : Addr} (hs : Scr s base)
    (h27 : limbs s.mem base o 27 < 16384) (h26 : limbs s.mem base o 26 < VG.Proof.X448.Radix16.radix) :
    WP isa (.block (foldHead o)) s fun t =>
      (t.gpr .ecx).toNat = foldH (limbs s.mem base o) ∧ (t.gpr .ebx).toNat = 0 ∧
      Keeps [.eax, .ebx, .ecx] s t ∧ t.mem = s.mem := by
  obtain ⟨_, ho2⟩ := ho
  unfold foldHead
  refine load_ok hs (by omega) fun s1 u1 => ?_
  refine wp_shift (by decide) fun s2 u2 => ?_
  have hs2 := (hs.of_upd u1 (by decide)).of_upd u2 (by decide)
  refine load_ok hs2 (by omega) fun s3 u3 => ?_
  refine wp_shift (by decide) fun s4 u4 => ?_
  refine wp_alu (Or.inl rfl) rfl fun s5 u5 _ => ?_
  refine VG.Proof.X448.X86.wp_mov rfl fun s6 u6 => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · have e1 : (s4.gpr .ecx).toNat = limbs s.mem base o 26 / 16384 := by
      rw [u4.other .ecx (by decide), u3.other .ecx (by decide)]
      have : s2.gpr .ecx = s1.gpr .ecx >>> 14 := u2.gpr
      rw [this, VG.Proof.Ed448.X86.toNat_shr, u1.gpr]
    have e2 : (s4.gpr .eax).toNat = 4 * limbs s.mem base o 27 := by
      have : s4.gpr .eax = (s3.gpr .eax).rotateRight 30 := u4.gpr
      rw [this, u3.gpr, u2.mem, u1.mem]
      exact VG.Proof.Ed448.X86.toNat_rotr30 _ h27
    rw [u6.other .ecx (by decide), u5.gpr]
    change (s4.gpr .ecx + s4.gpr .eax).toNat = _
    rw [VG.Proof.Ed448.X86.toNat_add_lt (by rw [e1, e2]; simp only [VG.Proof.X448.Radix16.radix] at h26; omega), e1, e2]
    rfl
  · rw [u6.gpr]; rfl
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  · rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]

/-- One source of `fold`: limb `k` of `l + h c` before carrying. -/
theorem foldSrc_ok {o : Nat} (ho : VG.Proof.Ed448.X86.Buf o) {base : Addr} {r : Nat → Nat} {w : Nat}
    (hH : foldH r < VG.Proof.X448.Radix16.radix) (hsum : ∀ k < 28, foldC cLimb r w k ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix)
    {k : Nat} (hk : k < 28) {s : State} (hs : Scr s base)
    (hr : ∀ j < 28, limbs s.mem base o j = r j) (hw : (word s.mem base W).toNat = w)
    (h1 : (s.gpr .ecx).toNat = foldH r) :
    WP isa (.block (foldSrc o k)) s fun t =>
      (t.gpr .eax).toNat = foldC cLimb r w k ∧ Keeps [.eax, .edx] s t ∧ t.mem = s.mem := by
  obtain ⟨ho1, ho2⟩ := ho
  have hT := VG.Proof.Ed448.X86.TF_eq
  have hW := VG.Proof.Ed448.X86.W_eq
  have hs' := hsum k hk
  unfold foldC at hs' ⊢
  unfold foldSrc
  have hc := VG.Proof.Ed448.X86.cLimb_lt k
  have hprod : (BitVec.ofNat 32 (cLimb k)).toNat * (s.gpr .ecx).toNat < 2 ^ 32 := by
    rw [VG.Proof.Ed448.X86.toNat_imm (by simp only [VG.Proof.X448.Radix16.radix] at hc; omega), h1]
    have := Nat.mul_le_mul (Nat.le_of_lt_succ hc) (Nat.le_of_lt_succ hH)
    omega
  have prod : ∀ t : State, t.gpr .eax = BitVec.ofNat 32
      ((BitVec.ofNat 32 (cLimb k)).toNat * (s.gpr .ecx).toNat) →
      (t.gpr .eax).toNat = foldH r * cLimb k := fun t ht => by
    rw [ht, VG.Proof.Ed448.X86.toNat_mul_lt hprod, VG.Proof.Ed448.X86.toNat_imm (by simp only [VG.Proof.X448.Radix16.radix] at hc; omega), h1, Nat.mul_comm]
  by_cases k0 : k = 0
  · subst k0
    rw [ite_eq_left rfl]
    refine VG.Proof.X448.X86.wp_mov rfl fun s1 u1 => VG.Proof.X448.X86.wp_mul fun s2 e2 m2 k2 => ?_
    have hs2 := (hs.of_upd u1 (by decide)).of_keeps k2 (by decide)
    refine wp_alu (Or.inl rfl) (VG.Proof.Ed448.X86.readSc hs2 (by omega)) fun s3 u3 _ => WP.block_nil ⟨?_, ?_, ?_⟩
    · have p2 := prod s2 (by rw [e2, u1.gpr, u1.other .ecx (by decide)])
      have ww : (word s2.mem base W).toNat = w := by rw [m2, u1.mem, hw]
      rw [u3.gpr]
      change (s2.gpr .eax + word s2.mem base W).toNat = _
      simp only [foldL, ite_true] at hs' ⊢
      rw [VG.Proof.Ed448.X86.toNat_add_lt (by rw [p2, ww]; omega), p2, ww, Nat.add_comm]
    · exact (u1.rest (by decide)).trans (k2.trans (u3.rest (by decide)))
    · rw [u3.mem, m2, u1.mem]
  rw [ite_eq_right k0]
  by_cases k14 : k < 14
  · rw [ite_eq_left k14]
    refine VG.Proof.X448.X86.wp_mov rfl fun s1 u1 => VG.Proof.X448.X86.wp_mul fun s2 e2 m2 k2 => ?_
    have hs2 := (hs.of_upd u1 (by decide)).of_keeps k2 (by decide)
    refine wp_alu (Or.inl rfl) (VG.Proof.Ed448.X86.readSc hs2 (by omega)) fun s3 u3 _ => WP.block_nil ⟨?_, ?_, ?_⟩
    · have p2 := prod s2 (by rw [e2, u1.gpr, u1.other .ecx (by decide)])
      have ww : limbs s2.mem base o (k - 1) = r (k - 1) := by
        rw [m2, u1.mem]; exact hr (k - 1) (by omega)
      rw [u3.gpr]
      change (s2.gpr .eax + word s2.mem base (o + 4 * (k - 1))).toNat = _
      simp only [foldL, k0, ite_false, show k < 27 by omega, ite_true] at hs' ⊢
      have ww' : (word s2.mem base (o + 4 * (k - 1))).toNat = r (k - 1) := ww
      rw [VG.Proof.Ed448.X86.toNat_add_lt (by rw [p2, ww']; omega), p2, ww', Nat.add_comm]
    · exact (u1.rest (by decide)).trans (k2.trans (u3.rest (by decide)))
    · rw [u3.mem, m2, u1.mem]
  rw [ite_eq_right k14]
  by_cases k27 : k < 27
  · rw [ite_eq_left k27]
    refine load_ok hs (by omega) fun s1 u1 => WP.block_nil ⟨?_, u1.rest (by decide), u1.mem⟩
    rw [u1.gpr]
    simp only [foldL, k0, ite_false, k27, ite_true, VG.Proof.Ed448.X86.cLimb_high (by omega : 14 ≤ k), Nat.mul_zero,
      Nat.add_zero]
    exact hr (k - 1) (by omega)
  · rw [ite_eq_right k27]
    refine load_ok hs (by omega) fun s1 u1 => ?_
    refine wp_alu (Or.inr (Or.inr (Or.inl rfl))) rfl fun s2 u2 _ => WP.block_nil
      ⟨?_, (u1.rest (by decide)).trans (u2.rest (by decide)), by rw [u2.mem, u1.mem]⟩
    rw [u2.gpr]
    change (s1.gpr .eax &&& (16383 : BitVec 32)).toNat = _
    rw [VG.Proof.Ed448.X86.toNat_and14, u1.gpr]
    simp only [foldL, k0, ite_false, k27, VG.Proof.Ed448.X86.cLimb_high (by omega : 14 ≤ k), Nat.mul_zero, Nat.add_zero]
    exact congrArg (· % 16384) (hr 26 (by decide))

/-- `fold o`: the limbs of `l + h c` into `TF`. -/
theorem fold_ok {o : Nat} (ho : VG.Proof.Ed448.X86.Buf o) {s : State} {base : Addr} (hs : Scr s base)
    (hl : Bounded s.mem base o) (hv : VG.Proof.X448.X86.fe s.mem base o < L) (hw : (word s.mem base W).toNat < VG.Proof.X448.Radix16.radix) :
    WP isa (.block (VG.Impl.Ed448.X86.fold o)) s fun t =>
      Keeps [.eax, .ebx, .ecx, .edx] s t ∧ Outside base TF 112 s.mem t.mem ∧
      Bounded t.mem base TF ∧ VG.Proof.X448.X86.fe t.mem base TF < 2 * L ∧
      VG.Proof.X448.X86.fe t.mem base TF % L = ((word s.mem base W).toNat + VG.Proof.X448.Radix16.radix * VG.Proof.X448.X86.fe s.mem base o) % L := by
  have hT := VG.Proof.Ed448.X86.TF_eq
  have hW := VG.Proof.Ed448.X86.W_eq
  obtain ⟨ho1, ho2⟩ := ho
  obtain ⟨h27, hH, hsum, hlt, hmod⟩ := fold_facts (c := cLimb) (fun k _ => VG.Proof.Ed448.X86.cLimb_lt k) VG.Proof.Ed448.X86.valN_cLimb hl hv hw
  unfold VG.Impl.Ed448.X86.fold
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.foldHead_ok ⟨ho1, ho2⟩ hs h27 (hl 26 (by decide))) fun s1 ⟨e1, e5, k1, m1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  refine WP.mono (carryPass_ok (rb := .edi) (o := TF) (d := TF) (s0 := s1)
    (c := foldC cLimb (limbs s.mem base o) (word s.mem base W).toNat) (by decide) (by omega)
    (fun k hk => hs1.ea (by omega)) (fun k hk => hs1.write (by omega)) e5 hsum ?_) fun t ht => ?_
  · intro k hk s' hp
    have hs' := hs1.of_keeps hp.regs (by decide)
    have hm := hp.mem
    rw [m1] at hm
    refine VG.Proof.Ed448.X86.foldSrc_ok ⟨ho1, ho2⟩ hH hsum hk hs' (fun j hj => ?_) ?_ ?_
    · exact hm.limbs (Or.inr (by omega)) (by omega) hj
    · rw [hm.word (Or.inl (by omega)) (by omega)]
    · rw [hp.regs.1 _ (by decide)]; exact e1
  · generalize hc : foldC cLimb (limbs s.mem base o) (word s.mem base W).toNat = c at ht hlt hmod hsum
    have hval : VG.Proof.X448.X86.fe t.mem base TF = VG.Proof.X448.Radix16.valN c 28 := by
      show VG.Proof.X448.Radix16.valN (limbs t.mem base TF) 28 = _
      rw [VG.Proof.X448.Radix16.valN_congr ht.outs]
      exact digits_val (Nat.lt_of_lt_of_le hlt two_L_le)
    refine ⟨(k1.mono (by decide)).trans (ht.regs.mono (by decide)), ?_, fun k hk => ?_,
      by rw [hval]; exact hlt, by rw [hval]; exact hmod⟩
    · rw [← m1]; exact ht.mem
    · rw [ht.outs k hk]; exact VG.Proof.X448.Radix16.digit_lt _ _

/-! ## The conditional subtraction -/

/-- One source of the subtraction: limb `k` of `TF` plus limb `k` of `K`. -/
theorem csubSrc_ok {k : Nat} (hk : k < 28) {s : State} {base : Addr} (hs : Scr s base)
    (hl : limbs s.mem base TF k < VG.Proof.X448.Radix16.radix) :
    WP isa (.block (csubSrc k)) s fun t =>
      (t.gpr .eax).toNat = limbs s.mem base TF k + kLimb k ∧ Keeps [.eax, .edx] s t ∧ t.mem = s.mem := by
  have hT := VG.Proof.Ed448.X86.TF_eq
  unfold csubSrc
  by_cases hkk : k < 14 ∨ k = 27
  · rw [ite_eq_left hkk]
    refine load_ok hs (by omega) fun s1 u1 => wp_alu (Or.inl rfl) rfl fun s2 u2 _ =>
      WP.block_nil ⟨?_, (u1.rest (by decide)).trans (u2.rest (by decide)), by rw [u2.mem, u1.mem]⟩
    have hkl := VG.Proof.Ed448.X86.kLimb_lt k
    have e1 : (s1.gpr .eax).toNat = limbs s.mem base TF k := by rw [u1.gpr]
    have e2 : (BitVec.ofNat 32 (kLimb k)).toNat = kLimb k := VG.Proof.Ed448.X86.toNat_imm (by simp only [VG.Proof.X448.Radix16.radix] at hkl; omega)
    rw [u2.gpr]
    change (s1.gpr .eax + BitVec.ofNat 32 (kLimb k)).toNat = _
    rw [VG.Proof.Ed448.X86.toNat_add_lt (by rw [e1, e2]; simp only [VG.Proof.X448.Radix16.radix] at hl hkl; omega), e1, e2]
  · rw [ite_eq_right hkk]
    refine load_ok hs (by omega) fun s1 u1 => WP.block_nil ⟨?_, u1.rest (by decide), u1.mem⟩
    rw [u1.gpr, VG.Proof.Ed448.X86.kLimb_mid (by omega) (by omega), Nat.add_zero]

theorem selectStep_ok {o : Nat} (ho : VG.Proof.Ed448.X86.Buf o) {k : Nat} (hk : k < 28) {s : State} {base : Addr}
    (hs : Scr s base) {sw : Bool} (hc : s.gpr .ecx = VG.Proof.X448.X86.mask sw) :
    WP isa (.block (Impl.Ed448.X86.selectStep o k)) s fun t =>
      t.mem = s.mem.writeW (off base (o + 4 * k))
        (if sw then word s.mem base (o + 4 * k) else word s.mem base (TF + 4 * k)) ∧
      Keeps [.eax, .edx] s t := by
  obtain ⟨ho1, ho2⟩ := ho
  have hT := VG.Proof.Ed448.X86.TF_eq
  unfold Impl.Ed448.X86.selectStep
  refine load_ok hs (by omega) fun t ht => ?_
  have ts := hs.of_upd ht (by decide)
  refine load_ok ts (by omega) fun u hu => ?_
  have us := ts.of_upd hu (by decide)
  refine wp_alu (by simp [plain]) rfl fun v hv _ => ?_
  have vs := us.of_upd hv (by decide)
  refine wp_alu (by simp [plain]) rfl fun w hw _ => ?_
  have ws := vs.of_upd hw (by decide)
  refine wp_alu (by simp [plain]) rfl fun x hx _ => ?_
  have xs := ws.of_upd hx (by decide)
  refine store_ok xs (by omega) fun y hy => WP.block_nil ⟨?_, ?_⟩
  · rw [hy.mem, hx.mem, hw.mem, hv.mem, hu.mem, ht.mem, hx.gpr]
    change _ = s.mem.writeW _ _
    simp only [aluVal]
    rw [hw.other .eax (by decide), hv.other .eax (by decide), hu.other .eax (by decide), ht.gpr,
      hw.gpr, hv.gpr, aluVal, hu.gpr, ht.mem, hu.other .eax (by decide), ht.gpr,
      hv.other .ecx (by decide), hu.other .ecx (by decide), ht.other .ecx (by decide), hc]
    change s.mem.writeW _ (_ ^^^ ((_ ^^^ _) &&& VG.Proof.X448.X86.mask sw)) = _
    rw [BitVec.xor_comm (word s.mem base (o + 4 * k)), (xor_sel sw _ _).1]
  · exact ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans
      ((hv.rest (by decide)).trans ((hw.rest (by decide)).trans ((hx.rest (by decide)).trans (hy.rest _))))))

theorem select_ok {o : Nat} (ho : VG.Proof.Ed448.X86.Buf o) {s : State} {base : Addr} (hs : Scr s base) {sw : Bool}
    (hc : s.gpr .ecx = VG.Proof.X448.X86.mask sw) :
    WP isa (.block ((List.range 28).flatMap (Impl.Ed448.X86.selectStep o))) s fun t =>
      (∀ i < 28, limbs t.mem base o i = if sw then limbs s.mem base o i else limbs s.mem base TF i) ∧
      Outside base o 112 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  obtain ⟨ho1, ho2⟩ := ho
  have hT := VG.Proof.Ed448.X86.TF_eq
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base o i = if sw then limbs s.mem base o i else limbs s.mem base TF i) ∧
    Outside base o (4 * n) s.mem t.mem ∧ Keeps [.eax, .edx] s t
  have st : ∀ n t, n < 28 → inv n t → WP isa (.block (Impl.Ed448.X86.selectStep o n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (VG.Proof.Ed448.X86.selectStep_ok ⟨ho1, ho2⟩ hn (hs.of_keeps tk (by decide)) ((tk.1 _ (by decide)).trans hc))
      fun u ⟨um, uk⟩ => ?_
    have out : Outside base (o + 4 * n) 4 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by omega)
    refine ⟨?_, (tm.mono (by omega) (by omega)).trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (word u.mem base (o + 4 * i)).toNat = _
    rw [um, word_write t.mem base (by omega) (by omega)]
    by_cases h : i = n
    · rw [ite_eq_left h, h, tm.word (Or.inr (by omega)) (by omega),
        tm.word (Or.inl (by omega)) (by omega)]
      cases sw <;> rfl
    · rw [ite_eq_right h]; exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 28) inv st 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- `reduceT o`: `TF` (below `2L`) modulo `L`, into `o`. -/
theorem reduceT_ok {o : Nat} (ho : VG.Proof.Ed448.X86.Buf o) {s : State} {base : Addr} (hs : Scr s base)
    (hl : Bounded s.mem base TF) (hv : VG.Proof.X448.X86.fe s.mem base TF < 2 * L) :
    WP isa (.block (reduceT o)) s fun t =>
      Keeps [.eax, .ebx, .ecx, .edx] s t ∧ Outside base o 112 s.mem t.mem ∧
      Bounded t.mem base o ∧ VG.Proof.X448.X86.fe t.mem base o = VG.Proof.X448.X86.fe s.mem base TF % L := by
  obtain ⟨ho1, ho2⟩ := ho
  have hT := VG.Proof.Ed448.X86.TF_eq
  unfold reduceT
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zeroCarry_ok s) fun s1 ⟨e1, m1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (carryPass_ok (rb := .edi) (o := o) (d := o) (s0 := s1)
    (c := fun k => limbs s.mem base TF k + kLimb k) (by decide) (by omega)
    (fun k hk => hs1.ea (by omega)) (fun k hk => hs1.write (by omega)) (by rw [e1]; rfl)
    (fun k hk => by have := hl k hk; have := VG.Proof.Ed448.X86.kLimb_lt k; simp only [VG.Proof.X448.Radix16.radix] at *; omega) ?_)
    fun s2 h2 => ?_
  · intro k hk s' hp
    have hs' := hs1.of_keeps hp.regs (by decide)
    have et : limbs s'.mem base TF k = limbs s.mem base TF k := by
      rw [hp.mem.limbs (Or.inl (by omega)) (by omega) hk, m1]
    refine WP.mono (VG.Proof.Ed448.X86.csubSrc_ok hk hs' (by rw [et]; exact hl k hk)) fun t ⟨e, kt, mt⟩ => ⟨?_, kt, mt⟩
    rw [e, et]
  generalize hcf : (fun k => limbs s.mem base TF k + kLimb k) = c at h2
  have hval := VG.Proof.X448.Radix16.pass_eq c 28
  have hcv : VG.Proof.X448.Radix16.valN c 28 = VG.Proof.X448.X86.fe s.mem base TF + (VG.Proof.X448.Radix16.radix ^ 28 - L) := by
    rw [← hcf, VG.Proof.X448.Radix16.valN_add, VG.Proof.Ed448.X86.valN_kLimb]
  have hy := VG.Proof.X448.Radix16.valN_lt (f := VG.Proof.X448.Radix16.digit c) (n := 28) fun k _ => VG.Proof.X448.Radix16.digit_lt _ _
  rw [hcv] at hval
  have hLM := two_L_le
  generalize hM : VG.Proof.X448.Radix16.radix ^ 28 = M at hy hval hLM
  obtain ⟨hc1, hsel⟩ := csub_facts hLM hv hy hval
  rw [← h2.carry] at hc1
  rw [WP.block_append_iff]
  refine WP.mono (freezeMask_ok (s := s2) rfl (by omega)) fun s3 ⟨e3, m3, k3⟩ => ?_
  have hs3 := (hs1.of_keeps h2.regs (by decide)).of_keeps k3 (by decide)
  refine WP.mono (VG.Proof.Ed448.X86.select_ok ⟨ho1, ho2⟩ hs3 e3) fun t ⟨ht, mt, kt⟩ => ?_
  have hlt : ∀ k < 28, limbs t.mem base o k =
      if VG.Proof.X448.Radix16.carry c 28 = 1 then VG.Proof.X448.Radix16.digit c k else limbs s.mem base TF k := by
    intro k hk
    rw [ht k hk, m3, h2.outs k hk, h2.mem.limbs (Or.inl (by omega)) (by omega) hk, m1, ← h2.carry]
    simp only [decide_eq_true_eq]
  refine ⟨(k1.mono (by decide)).trans ((h2.regs.mono (by decide)).trans ((k3.mono (by decide)).trans
    (kt.mono (by decide)))), ?_, fun k hk => ?_, ?_⟩
  · rw [← m1]
    exact h2.mem.trans (by rw [← m3]; exact mt)
  · rw [hlt k hk]; split
    · exact VG.Proof.X448.Radix16.digit_lt _ _
    · exact hl k hk
  · rw [← hsel]
    change VG.Proof.X448.Radix16.valN (limbs t.mem base o) 28 = _
    rw [VG.Proof.X448.Radix16.valN_congr hlt]
    split
    · rfl
    · rfl

/-! ## One chunk -/

/-- `step o`: the chunk at `W` folded into the remainder at `o`. -/
theorem step_ok {o : Nat} (ho : VG.Proof.Ed448.X86.Buf o) {s : State} {base : Addr} (hs : Scr s base)
    (hl : Bounded s.mem base o) (hv : VG.Proof.X448.X86.fe s.mem base o < L) (hw : (word s.mem base W).toNat < VG.Proof.X448.Radix16.radix) :
    WP isa (.block (VG.Impl.Ed448.X86.step o)) s fun t =>
      Keeps [.eax, .ebx, .ecx, .edx] s t ∧ Outside2 base TF 112 o 112 s.mem t.mem ∧
      Bounded t.mem base o ∧
      VG.Proof.X448.X86.fe t.mem base o = ((word s.mem base W).toNat + VG.Proof.X448.Radix16.radix * VG.Proof.X448.X86.fe s.mem base o) % L := by
  obtain ⟨ho1, ho2⟩ := ho
  unfold VG.Impl.Ed448.X86.step
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.fold_ok ⟨ho1, ho2⟩ hs hl hv hw) fun u ⟨ku, fu, lu, vu, mu⟩ => ?_
  refine WP.mono (VG.Proof.Ed448.X86.reduceT_ok ⟨ho1, ho2⟩ (hs.of_keeps ku (by decide)) lu vu)
    fun t ⟨kt, ft, lt, vt⟩ => ⟨ku.trans kt, fun p h1 h2 => (ft p h2).trans (fu p h1), lt, by rw [vt, mu]⟩

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.ScalarLoop`. -/
section

/-!
# Ed448 scalar arithmetic on x86 (32-bit): the loops

The remainder of an input's bytes from the top, sixteen bits at a time
(`byteLoop_ok`), and of the product's limbs (`limbLoop_ok`), and the
remainders they start from (`zeroR_ok`).
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.Radix16 VG.Proof.X448.X86 VG.Proof.Ed448.Limbs16
open VG.Impl.Ed448.X86 (W TF RA SK SS SR readBytes byteStep zeroR readLimb limbStep step)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-- `[x + n + d]`, for `x + n + d` below `2^32`. -/
theorem addr_add2 (x : BitVec 32) {n d : Nat} (h : x.toNat + n + d < 2 ^ 32) :
    VG.X86.addr (x + BitVec.ofNat 32 n) d = x.setWidth 64 + BitVec.ofNat 64 (n + d) := by
  rw [← addr_eq (by omega)]
  simp only [VG.X86.addr, BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## What the loops change -/

/-- What the loops leave unchanged: all registers but `eax`, `ebx`, `ecx`,
`edx` and `ebp`, and the memory outside `[W, TF + 112)` and the remainder at
`o`. -/
structure LoopKeep (base : Addr) (o : Nat) (s t : State) : Prop where
  regs : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t
  mem : Outside2 base W 160 o 112 s.mem t.mem

theorem LoopKeep.refl (base : Addr) (o : Nat) (s : State) : VG.Proof.Ed448.X86.LoopKeep base o s s :=
  ⟨Keeps.refl _ _, Outside2.refl _ _ _ _ _ _⟩

theorem LoopKeep.trans {base : Addr} {o : Nat} {s t u : State} (h : VG.Proof.Ed448.X86.LoopKeep base o s t)
    (h' : VG.Proof.Ed448.X86.LoopKeep base o t u) : VG.Proof.Ed448.X86.LoopKeep base o s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

/-- A step's frame, and the chunk's store, within the loops'. -/
theorem outside2_step {base : Addr} {o : Nat} {m m' : Mem} (h : Outside2 base TF 112 o 112 m m') :
    Outside2 base W 160 o 112 m m' := fun p h1 h2 => h p (by simp only [TF, W] at h1 ⊢; omega) h2

theorem outside2_W {base : Addr} {o : Nat} {m m' : Mem} (h : Outside base W 4 m m') :
    Outside2 base W 160 o 112 m m' := fun p h1 _ => h p (by simp only [W] at h1 ⊢; omega)

/-- A byte beyond the working space, unchanged across the loops. -/
theorem outside2_byte {base : Addr} {x nx y ny : Nat} {m m' : Mem} (h : Outside2 base x nx y ny m m')
    {a : Addr} (ha : 8192 ≤ ofs base a) (hx : x + nx ≤ 8192) (hy : y + ny ≤ 8192) : m' a = m a :=
  h a (Or.inr (by omega)) (Or.inr (by omega))

/-! ## Reading two bytes -/

theorem readBytes_ok {s : State} {base : Addr} (hs : Scr s base) {p : BitVec 32} {n N : Nat}
    (hn : n + 2 ≤ N) (hp : s.gpr .esi = p) (hfit : p.toNat + N ≤ 2 ^ 32)
    (hc : s.gpr .ebp = BitVec.ofNat 32 (n + 2))
    (hr : ∀ i < N, InRegions (s.rd ++ s.wr) (p.setWidth 64 + BitVec.ofNat 64 i) 1) :
    WP isa (.block readBytes) s fun t =>
      Keeps [.eax, .edx, .ebp] s t ∧ Outside base W 4 s.mem t.mem ∧ t.gpr .ebp = BitVec.ofNat 32 n ∧
      (word t.mem base W).toNat = (s.mem (p.setWidth 64 + BitVec.ofNat 64 n)).toNat +
        256 * (s.mem (p.setWidth 64 + BitVec.ofNat 64 (n + 1))).toNat := by
  unfold readBytes
  refine wp_alu (Or.inr (Or.inl rfl)) rfl fun s1 u1 _ => ?_
  refine VG.Proof.X448.X86.wp_mov rfl fun s2 u2 => wp_alu (Or.inl rfl) rfl fun s3 u3 _ => ?_
  have e1 : s1.gpr .ebp = BitVec.ofNat 32 n := by
    rw [u1.gpr]
    change s.gpr .ebp - BitVec.ofNat 32 2 = _
    rw [hc, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have e3 : s3.gpr .edx = p + BitVec.ofNat 32 n := by
    rw [u3.gpr]
    change s2.gpr .edx + s2.gpr .ebp = _
    rw [u2.gpr, u2.other .ebp (by decide), u1.other .esi (by decide), hp, e1]
  have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  refine wp_load8 (a := p.setWidth 64 + BitVec.ofNat 64 n)
    (by change VG.X86.addr (s3.gpr .edx) 0 = _; rw [e3, VG.Proof.Ed448.X86.addr_add2 p (by omega), Nat.add_zero])
    (by rw [u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hr n (by omega)) fun s4 u4 => ?_
  refine wp_load8 (a := p.setWidth 64 + BitVec.ofNat 64 (n + 1))
    (by change VG.X86.addr (s4.gpr .edx) 1 = _; rw [u4.other .edx (by decide), e3, VG.Proof.Ed448.X86.addr_add2 p (by omega)])
    (by rw [u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hr (n + 1) (by omega))
    fun s5 u5 => ?_
  refine wp_shift (by decide) fun s6 u6 => wp_alu (Or.inl rfl) rfl fun s7 u7 _ => ?_
  have hs7 := ((((((hs.of_upd u1 (by decide)).of_upd u2 (by decide)).of_upd u3 (by decide)).of_upd u4
    (by decide)).of_upd u5 (by decide)).of_upd u6 (by decide)).of_upd u7 (by decide)
  refine store_ok hs7 (by simp only [W]; omega) fun s8 u8 => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans
        ((u7.rest (by decide)).trans (u8.rest _)))))))
  · rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, m3]
    exact writeW_outside _ _ _ (by simp only [W]; omega)
  · rw [u8.gpr, u7.other .ebp (by decide), u6.other .ebp (by decide), u5.other .ebp (by decide),
      u4.other .ebp (by decide), u3.other .ebp (by decide), u2.other .ebp (by decide), e1]
  · have value : s7.gpr .eax = BitVec.ofNat 32 ((s.mem (p.setWidth 64 + BitVec.ofNat 64 n)).toNat +
        256 * (s.mem (p.setWidth 64 + BitVec.ofNat 64 (n + 1))).toNat) := by
      rw [u7.gpr]
      change s6.gpr .eax + s6.gpr .edx = _
      have : s6.gpr .edx = (s5.gpr .edx).rotateRight 24 := u6.gpr
      rw [u6.other .eax (by decide), this, u5.other .eax (by decide), u4.gpr, u5.gpr, u4.mem, m3,
        byte_rotate]
      apply BitVec.eq_of_toNat_eq
      have h0 := (s.mem (p.setWidth 64 + BitVec.ofNat 64 n)).isLt
      have h1 := (s.mem (p.setWidth 64 + BitVec.ofNat 64 (n + 1))).isLt
      simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
        Nat.shiftLeft_eq, BitVec.toNat_ofNat]
      omega
    have hw : (word s8.mem base W) = s7.gpr .eax := by
      rw [u8.mem, Proof.X448.X86.word, Mem.readW_writeW_self32]
    rw [hw, value]
    have h0 := (s.mem (p.setWidth 64 + BitVec.ofNat 64 n)).isLt
    have h1 := (s.mem (p.setWidth 64 + BitVec.ofNat 64 (n + 1))).isLt
    exact VG.Proof.Ed448.X86.toNat_imm (by omega)

/-! ## The byte loop -/

/-- After the steps from the top down to byte `n`. -/
structure ByteInv (base : Addr) (o N : Nat) (P : Addr) (s0 : State) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ N
  even : n % 2 = 0
  counter : s.gpr .ebp = BitVec.ofNat 32 n
  lim : Bounded s.mem base o
  value : VG.Proof.X448.X86.fe s.mem base o = decodeLE ((bytesAt s0.mem P N).drop n) % L
  keeps : VG.Proof.Ed448.X86.LoopKeep base o s0 s

theorem cmp_zero {s : State} {n : Nat} (hn : n < 2 ^ 32) (hc : s.gpr .ebp = BitVec.ofNat 32 n)
    {t : State} (hz : t.zf = some (s.gpr .ebp - 0 == 0)) : t.zf = some (decide (n = 0)) := by
  rw [hz, hc, show BitVec.ofNat 32 n - (0 : BitVec 32) = BitVec.ofNat 32 n from BitVec.sub_zero _,
    VG.Proof.X448.X86.ofNat_beq_zero hn]

theorem byteLoop_ok {o N : Nat} (ho : VG.Proof.Ed448.X86.Buf o) {s0 : State} {base : Addr} (hs : Scr s0 base)
    {p : BitVec 32} (hp : s0.gpr .esi = p) (hfit : p.toNat + N ≤ 2 ^ 32)
    (hread : ∀ i < N, InRegions (s0.rd ++ s0.wr) (p.setWidth 64 + BitVec.ofNat 64 i) 1)
    (hfar : ∀ i < N, 8192 ≤ ofs base (p.setWidth 64 + BitVec.ofNat 64 i))
    {n0 : Nat} (hn0 : 0 < n0) (hle : n0 ≤ N) (heven : n0 % 2 = 0)
    (hc : s0.gpr .ebp = BitVec.ofNat 32 n0) (hl : Bounded s0.mem base o)
    (hv : VG.Proof.X448.X86.fe s0.mem base o = decodeLE ((bytesAt s0.mem (p.setWidth 64) N).drop n0) % L) :
    WP isa (.loop (.block (byteStep o)) .ne) s0 fun t => VG.Proof.Ed448.X86.LoopKeep base o s0 t ∧
      Bounded t.mem base o ∧ VG.Proof.X448.X86.fe t.mem base o = decodeLE (bytesAt s0.mem (p.setWidth 64) N) % L := by
  obtain ⟨ho1, ho2⟩ := ho
  have hN : N ≤ 2 ^ 32 := by omega
  apply WP.loop (VG.Proof.Ed448.X86.ByteInv base o N (p.setWidth 64) s0) (n := n0)
  · intro n s hi
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by have := hi.even; have := hi.positive; omega⟩
    have hk : k + 2 ≤ N := hi.bound
    have hss : Scr s base := hs.of_keeps hi.keeps.regs (by decide)
    have hps : s.gpr .esi = p := (hi.keeps.regs.1 _ (by decide)).trans hp
    have hrs : ∀ i < N, InRegions (s.rd ++ s.wr) (p.setWidth 64 + BitVec.ofNat 64 i) 1 := by
      rw [hi.keeps.regs.2.1, hi.keeps.regs.2.2]; exact hread
    unfold byteStep
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed448.X86.readBytes_ok hss hk hps hfit hi.counter hrs) fun u ⟨ku, mu, cu, wu⟩ => ?_
    have hsu : Scr u base := hss.of_keeps ku (by decide)
    have hwu : (word u.mem base W).toNat < VG.Proof.X448.Radix16.radix := by
      rw [wu]
      have := (s.mem (p.setWidth 64 + BitVec.ofNat 64 k)).isLt
      have := (s.mem (p.setWidth 64 + BitVec.ofNat 64 (k + 1))).isLt
      simp only [VG.Proof.X448.Radix16.radix]
      omega
    have lu : ∀ j < 28, limbs u.mem base o j = limbs s.mem base o j :=
      fun j hj => mu.limbs (Or.inr (by simp only [W, TF] at ho1 ⊢; omega)) (by omega) hj
    have fu : VG.Proof.X448.X86.fe u.mem base o = VG.Proof.X448.X86.fe s.mem base o := VG.Proof.X448.Radix16.valN_congr lu
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed448.X86.step_ok ⟨ho1, ho2⟩ hsu (fun j hj => by rw [lu j hj]; exact hi.lim j hj)
      (by rw [fu, hi.value]; exact Nat.mod_lt _ Proof.Ed448.L_pos) hwu) fun v ⟨kv, mv, lv, vv⟩ => ?_
    refine VG.Proof.X448.X86.wp_cmp rfl fun t ht hz => WP.block_nil ?_
    have mb : ∀ i < N, s.mem (p.setWidth 64 + BitVec.ofNat 64 i) =
        s0.mem (p.setWidth 64 + BitVec.ofNat 64 i) :=
      fun i hi' => VG.Proof.Ed448.X86.outside2_byte hi.keeps.mem (hfar i hi') (by decide) (by omega)
    have val : VG.Proof.X448.X86.fe t.mem base o = decodeLE ((bytesAt s0.mem (p.setWidth 64) N).drop k) % L := by
      rw [ht.mem, vv, wu, fu, hi.value, mod_fold, mb k (by omega), mb (k + 1) (by omega),
        decode_drop2 _ _ hk]
    have keep : VG.Proof.Ed448.X86.LoopKeep base o s0 t := hi.keeps.trans
      ⟨(ku.mono (by decide)).trans ((kv.mono (by decide)).trans (ht.rest _)),
        by rw [ht.mem]; exact (VG.Proof.Ed448.X86.outside2_W mu).trans (VG.Proof.Ed448.X86.outside2_step mv)⟩
    have c10 : t.gpr .ebp = BitVec.ofNat 32 k := by
      rw [ht.gpr, kv.1 _ (by decide), cu]
    have zt : t.zf = some (decide (k = 0)) :=
      VG.Proof.Ed448.X86.cmp_zero (by omega) (by rw [kv.1 _ (by decide), cu]) hz
    by_cases k0 : k = 0
    · subst k0
      refine .inl ⟨by simp only [eval, zt, decide_true, Option.map_some, Bool.not_true], keep,
        by rw [ht.mem]; exact lv, ?_⟩
      simpa only [List.drop_zero] using val
    · refine .inr ⟨by simp only [eval, zt, decide_eq_false k0, Option.map_some, Bool.not_false], k,
        by omega, ⟨by omega, by omega, by have := hi.even; omega, c10, by rw [ht.mem]; exact lv, val,
          keep⟩⟩
  · exact ⟨hn0, hle, heven, hc, hl, hv, LoopKeep.refl _ _ _⟩

/-! ## The product's limbs -/

theorem ACC_eq : Impl.X448.X86.ACC = 3584 := rfl

theorem readLimb_ok {s : State} {base : Addr} (hs : Scr s base) {j : Nat} (hj : j < 56)
    (hc : s.gpr .ebp = BitVec.ofNat 32 (4 * (j + 1))) :
    WP isa (.block readLimb) s fun t =>
      Keeps [.eax, .edx, .ebp] s t ∧ Outside base W 4 s.mem t.mem ∧
      t.gpr .ebp = BitVec.ofNat 32 (4 * j) ∧
      word t.mem base W = word s.mem base (Impl.X448.X86.ACC + 4 * j) := by
  have hA := VG.Proof.Ed448.X86.ACC_eq
  have hfit := hs.nowrap
  unfold readLimb
  refine wp_alu (Or.inr (Or.inl rfl)) rfl fun s1 u1 _ => ?_
  refine VG.Proof.X448.X86.wp_mov rfl fun s2 u2 => wp_alu (Or.inl rfl) rfl fun s3 u3 _ => ?_
  have e1 : s1.gpr .ebp = BitVec.ofNat 32 (4 * j) := by
    rw [u1.gpr]
    change s.gpr .ebp - BitVec.ofNat 32 4 = _
    rw [hc, show 4 * (j + 1) = 4 * j + 4 by omega, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have e3 : s3.gpr .edx = s.gpr .edi + BitVec.ofNat 32 (4 * j) := by
    rw [u3.gpr]
    change s2.gpr .edx + s2.gpr .ebp = _
    rw [u2.gpr, u2.other .ebp (by decide), u1.other .edi (by decide), e1]
  have hs3 := ((hs.of_upd u1 (by decide)).of_upd u2 (by decide)).of_upd u3 (by decide)
  refine wp_load (a := off base (Impl.X448.X86.ACC + 4 * j))
    (by
      change VG.X86.addr (s3.gpr .edx) Impl.X448.X86.ACC = _
      rw [e3, VG.Proof.Ed448.X86.addr_add2 _ (by omega), hs.edi, Nat.add_comm])
    (by rw [u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hs.read (by omega)) fun s4 u4 => ?_
  refine store_ok (hs3.of_upd u4 (by decide)) (by simp only [W]; omega) fun s5 u5 =>
    WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest _))))
  · rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    exact writeW_outside _ _ _ (by simp only [W]; omega)
  · rw [u5.gpr, u4.other .ebp (by decide), u3.other .ebp (by decide), u2.other .ebp (by decide), e1]
  · rw [u5.mem, Proof.X448.X86.word, Mem.readW_writeW_self32, u4.gpr, u3.mem, u2.mem, u1.mem]

/-- After the steps from the top limb down to limb `j`. -/
structure LimbInv (base : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  positive : 0 < j
  bound : j ≤ 56
  counter : s.gpr .ebp = BitVec.ofNat 32 (4 * j)
  lim : Bounded s.mem base RA
  value : VG.Proof.X448.X86.fe s.mem base RA = accFrom (limbs s0.mem base Impl.X448.X86.ACC) j % L
  keeps : VG.Proof.Ed448.X86.LoopKeep base RA s0 s

theorem limbLoop_ok {s0 : State} {base : Addr} (hs : Scr s0 base)
    (hacc : ∀ j < 56, limbs s0.mem base Impl.X448.X86.ACC j < VG.Proof.X448.Radix16.radix)
    (hc : s0.gpr .ebp = BitVec.ofNat 32 (4 * 56)) (hl : Bounded s0.mem base RA)
    (hv : VG.Proof.X448.X86.fe s0.mem base RA = 0) :
    WP isa (.loop (.block limbStep) .ne) s0 fun t => VG.Proof.Ed448.X86.LoopKeep base RA s0 t ∧
      Bounded t.mem base RA ∧
      VG.Proof.X448.X86.fe t.mem base RA = VG.Proof.X448.Radix16.valN (limbs s0.mem base Impl.X448.X86.ACC) 56 % L := by
  have hA := VG.Proof.Ed448.X86.ACC_eq
  have ho : VG.Proof.Ed448.X86.Buf RA := ⟨by decide, by decide⟩
  apply WP.loop (VG.Proof.Ed448.X86.LimbInv base s0) (n := 56)
  · intro n s hi
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by have := hi.positive; omega⟩
    have hj : j < 56 := hi.bound
    have hss : Scr s base := hs.of_keeps hi.keeps.regs (by decide)
    have la : ∀ i < 56, limbs s.mem base Impl.X448.X86.ACC i =
        limbs s0.mem base Impl.X448.X86.ACC i := fun i hi' =>
      congrArg BitVec.toNat (hi.keeps.mem.word (Or.inr (by simp only [W]; omega))
        (Or.inr (by simp only [RA]; omega)) (by omega))
    unfold limbStep
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed448.X86.readLimb_ok hss hj hi.counter) fun u ⟨ku, mu, cu, wu⟩ => ?_
    have hsu : Scr u base := hss.of_keeps ku (by decide)
    have hwu : (word u.mem base W).toNat < VG.Proof.X448.Radix16.radix := by
      rw [wu]; change limbs s.mem base Impl.X448.X86.ACC j < _; rw [la j hj]; exact hacc j hj
    have lu : ∀ i < 28, limbs u.mem base RA i = limbs s.mem base RA i :=
      fun i hi' => mu.limbs (Or.inr (by simp only [W, RA]; omega)) (by simp only [RA]; omega) hi'
    have fu : VG.Proof.X448.X86.fe u.mem base RA = VG.Proof.X448.X86.fe s.mem base RA := VG.Proof.X448.Radix16.valN_congr lu
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed448.X86.step_ok ho hsu (fun i hi' => by rw [lu i hi']; exact hi.lim i hi')
      (by rw [fu, hi.value]; exact Nat.mod_lt _ Proof.Ed448.L_pos) hwu) fun v ⟨kv, mv, lv, vv⟩ => ?_
    refine VG.Proof.X448.X86.wp_cmp rfl fun t ht hz => WP.block_nil ?_
    have val : VG.Proof.X448.X86.fe t.mem base RA = accFrom (limbs s0.mem base Impl.X448.X86.ACC) j % L := by
      rw [ht.mem, vv, wu, fu, hi.value, mod_fold, accFrom_step _ hj]
      change ((limbs s.mem base Impl.X448.X86.ACC j) + _) % L = _
      rw [la j hj]
    have keep : VG.Proof.Ed448.X86.LoopKeep base RA s0 t := hi.keeps.trans
      ⟨(ku.mono (by decide)).trans ((kv.mono (by decide)).trans (ht.rest _)),
        by rw [ht.mem]; exact (VG.Proof.Ed448.X86.outside2_W mu).trans (VG.Proof.Ed448.X86.outside2_step mv)⟩
    have c10 : t.gpr .ebp = BitVec.ofNat 32 (4 * j) := by
      rw [ht.gpr, kv.1 _ (by decide), cu]
    have zt : t.zf = some (decide (4 * j = 0)) :=
      VG.Proof.Ed448.X86.cmp_zero (by omega) (by rw [kv.1 _ (by decide), cu]) hz
    by_cases j0 : j = 0
    · subst j0
      refine .inl ⟨by simp only [eval, zt, decide_true, Option.map_some, Bool.not_true], keep,
        by rw [ht.mem]; exact lv, ?_⟩
      rw [val, accFrom_zero]
    · refine .inr ⟨by simp only [eval, zt, decide_eq_false (by omega : ¬4 * j = 0), Option.map_some,
        Bool.not_false], j, by omega, ⟨by omega, by omega, c10, by rw [ht.mem]; exact lv, val, keep⟩⟩
  · refine ⟨by decide, by decide, hc, hl, ?_, LoopKeep.refl _ _ _⟩
    rw [hv]
    exact (Nat.zero_mod _).symm.trans (by rfl)

/-! ## The remainders the loops start from -/

theorem zeroR_ok {o : Nat} (ho : o + 112 ≤ 4096) {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (zeroR o)) s fun t =>
      Keeps [.eax] s t ∧ Outside base o 112 s.mem t.mem ∧ (∀ k < 28, limbs t.mem base o k = 0) := by
  unfold zeroR
  rw [show ∀ (i : Instr) (is : List Instr), i :: is = [i] ++ is from fun _ _ => rfl,
    WP.block_append_iff]
  refine WP.mono (zeroEax_ok s) fun t ⟨tz, tm, tk⟩ => ?_
  refine WP.mono (fill_ok (hs.of_keeps tk (by decide)) (o := o) (n := 28) (by omega) tz)
    fun u ⟨uf, um, uk⟩ => ⟨tk.trans (uk.mono (by simp)), by rw [← tm]; exact um, uf⟩

theorem Bounded_zero {m : Mem} {base : Addr} {o : Nat} (h : ∀ k < 28, limbs m base o k = 0) :
    Bounded m base o := fun k hk => by rw [h k hk]; decide

theorem fe_zero {m : Mem} {base : Addr} {o : Nat} (h : ∀ k < 28, limbs m base o k = 0) :
    VG.Proof.X448.X86.fe m base o = 0 := (VG.Proof.X448.Radix16.valN_congr h).trans (valN_zero 28)

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.ScalarIO`. -/
section

/-!
# Ed448 scalar arithmetic on x86 (32-bit): entry and exit

The cdecl arguments (`Args`: they stay on the stack, which the code does not
write, `Args.load`), the callee-saved registers saved in the working space
(`save_ok`, as X448 saves them), the remainders of the inputs
(`reduce114_ok`, `reduce57_ok`), and the result: the remainder's limbs as 56
bytes and a zero byte, its encoding, then the registers restored
(`finish_ok`).
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.Radix16 VG.Proof.X448.X86 VG.Proof.Ed448.Limbs16
open VG.Impl.Ed448.X86 (W TF RA SK SS SR zeroR reduce114 reduce57 packLimb finish)
open VG.Spec.Ed448 (L bytesAt decodeLE encodeLE)

/-! ## The arguments -/

/-- The `n` cdecl arguments of 4 bytes on the stack, readable and disjoint
from the working space, the argument `sc`. -/
structure Args (s₀ : State) (n sc : Nat) : Prop where
  in_rd : (⟨argAddr s₀ 0, 4 * n⟩ : Region) ∈ s₀.rd
  sp_fit : (s₀.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32
  sc_lt : sc < n
  sc_in : scR (arg s₀ sc) ∈ s₀.wr
  sc_fit : (arg s₀ sc).toNat + 8192 ≤ 2 ^ 32
  args_sc : (⟨argAddr s₀ 0, 4 * n⟩ : Region).Disjoint (scR (arg s₀ sc))
  ret_sc : (VG.Proof.X448.X86.retR s₀).Disjoint (scR (arg s₀ sc))

namespace Args
variable {s₀ : State} {n sc : Nat} (hp : VG.Proof.Ed448.X86.Args s₀ n sc)
include hp

theorem arg_contains {i : Nat} (hi : i < n) :
    (⟨argAddr s₀ 0, 4 * n⟩ : Region).Contains (addr (s₀.gpr .esp) (4 + 4 * i)) 4 :=
  VG.Proof.X25519.X86.sub_contains (x := s₀.gpr .esp) (a := 4) (k := 4 * n)
    (by have := hp.sp_fit; omega) (by omega) (by omega) (by decide)

/-- An argument, in memory the code has written only in the working space. -/
theorem arg_same {m : Mem} (hf : Frame [scR (arg s₀ sc)] s₀.mem m) {i : Nat} (hi : i < n) :
    m.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  hf.readW (hp.arg_contains hi)
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.args_sc) (by decide)

theorem load {s : State} (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd)
    (hw : s.wr = s₀.wr) (hm : Outside ((arg s₀ sc).setWidth 64) 0 8192 s₀.mem s.mem)
    {i : Nat} (hi : i < n) {d : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Upd s t d (arg s₀ i) → WP isa (.block is) t Q) :
    WP isa (.block (.mov d (.mem (Impl.X448.X86.at_ .esp (4 + 4 * i))) :: is)) s Q := by
  refine wp_load (a := addr (s₀.gpr .esp) (4 + 4 * i))
    (by change addr (s.gpr .esp) (4 + 4 * i) = _; rw [hsp])
    (by rw [hr, hw]; exact ⟨_, List.mem_append_left _ hp.in_rd, hp.arg_contains hi⟩) fun t ht => ?_
  rw [hp.arg_same hm.frame hi] at ht
  exact k t ht

end Args

/-! ## Saving the callee-saved registers -/

theorem save_ok {s : State} {n sc : Nat} (hp : VG.Proof.Ed448.X86.Args s n sc) :
    WP isa (.block (Impl.Ed448.X86.save (4 + 4 * sc))) s fun t =>
      Scr t ((arg s sc).setWidth 64) ∧ VG.Proof.X448.X86.Saved ((arg s sc).setWidth 64) s.gpr t.mem ∧
      Outside ((arg s sc).setWidth 64) 0 16 s.mem t.mem ∧ Keeps [.eax, .edi] s t := by
  change WP isa (.block (.mov .eax (.mem (Impl.X448.X86.at_ .esp (4 + 4 * sc))) ::
    (Spill.saveCode .eax VG.Proof.X448.X86.savedSlots ++ [.mov .edi (.reg .eax)]))) s _
  refine hp.load rfl rfl rfl (Outside.refl _ _ _ _) hp.sc_lt fun t ht => ?_
  have hfit := hp.sc_fit
  refine Spill.save_ofNat_ok VG.Proof.X448.X86.savedSlots (n := 16) (by decide) (by rw [ht.gpr]; omega)
    (fun p h => by rw [ht.gpr, ht.wr]; exact ⟨_, hp.sc_in, contains_sc (by have := VG.Proof.X448.X86.savedSlots_bound p h; omega)⟩)
    fun u hu => ?_
  have hm : u.mem = Spill.saveMem s.mem (off ((arg s sc).setWidth 64)) s.gpr VG.Proof.X448.X86.savedSlots := by
    rw [hu.mem, ht.gpr, ht.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => ht.other _ (by revert p h; decide)
  refine wp_mov rfl fun v hv => WP.block_nil ?_
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, (ht.rest (by decide)).trans
    (⟨fun r _ => by rw [hu.gpr], hu.rd, hu.wr⟩ : Keeps [.eax, .edi] t u) |>.trans (hv.rest (by decide))⟩
  · rw [hv.gpr, hu.gpr, ht.gpr]
  · rw [hv.wr, hu.wr, ht.wr]; exact hp.sc_in
  · rw [hv.gpr, hu.gpr, ht.gpr]; exact hfit
  · rw [hv.mem, hm]; exact Spill.saveMem_saved_ofNat _ _ _ (n := 16) (by decide) (by decide)
  · rw [hv.mem, hm]
    exact Outside.of_frame (Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p h =>
      Offset.contains_base _ (VG.Proof.X448.X86.savedSlots_bound p h) (by have := VG.Proof.X448.X86.savedSlots_bound p h; omega))

/-! ## The remainders of the inputs -/

theorem init114_ok {o : Nat} (ho : VG.Proof.Ed448.X86.Buf o) {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (zeroR o ++ ([.mov .ebp (.imm 114)] : List Instr))) s fun v =>
      VG.Proof.Ed448.X86.LoopKeep base o s v ∧ v.gpr .ebp = BitVec.ofNat 32 114 ∧ Bounded v.mem base o ∧
        fe v.mem base o = 0 := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.zeroR_ok ho.2 hs) fun u ⟨ku, fu, zu⟩ =>
    wp_mov rfl fun v hv => WP.block_nil
      ⟨⟨(ku.mono (by decide)).trans (hv.rest (by decide)), by
        rw [hv.mem]; exact fun p _ h2 => fu p h2⟩,
        hv.gpr, by rw [hv.mem]; exact VG.Proof.Ed448.X86.Bounded_zero zu, by rw [hv.mem]; exact VG.Proof.Ed448.X86.fe_zero zu⟩

/-- The input's bytes, readable and beyond the working space. -/
structure Input (s : State) (base : Addr) (p : BitVec 32) (N : Nat) : Prop where
  fit : p.toNat + N ≤ 2 ^ 32
  read : ∀ i < N, InRegions (s.rd ++ s.wr) (p.setWidth 64 + BitVec.ofNat 64 i) 1
  far : ∀ i < N, 8192 ≤ ofs base (p.setWidth 64 + BitVec.ofNat 64 i)

theorem Input.of_keeps {s t : State} {base : Addr} {p : BitVec 32} {N : Nat} (h : VG.Proof.Ed448.X86.Input s base p N)
    {rs : List Reg} (hk : Keeps rs s t) : VG.Proof.Ed448.X86.Input t base p N :=
  ⟨h.fit, by rw [hk.2.1, hk.2.2]; exact h.read, h.far⟩

/-- An input's bytes across a change of the working space. -/
theorem Input.bytes {s : State} {base : Addr} {p : BitVec 32} {N : Nat} (h : VG.Proof.Ed448.X86.Input s base p N)
    {m m' : Mem} (hm : Outside base 0 8192 m m') :
    bytesAt m' (p.setWidth 64) N = bytesAt m (p.setWidth 64) N := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => hm _ (Or.inr ?_)
  simp only [List.mem_range] at hi
  exact h.far i hi

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 8192 ≤ ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega)
    (by omega)) ?_
  simp only [Region.Contains]; simp only [ofs] at h; omega

/-- The working space lies beyond a region of `n` bytes disjoint from it. -/
theorem far_out {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩)
    {i : Nat} (hi : i < 8192) : n ≤ ofs p (off base i) := by
  refine Nat.le_of_not_lt fun h => hd _ ?_ (Offset.contains_base base (d := i) (n := 1) (k := 8192)
    (by omega) (by omega))
  simp only [Region.Contains]
  change ofs p (off base i) + 1 ≤ n
  omega

theorem Input.of_region {s : State} {base : Addr} {p : BitVec 32} {N : Nat} (hfit : p.toNat + N ≤ 2 ^ 32)
    (hin : (⟨p.setWidth 64, N⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : (⟨p.setWidth 64, N⟩ : Region).Disjoint ⟨base, 8192⟩) : VG.Proof.Ed448.X86.Input s base p N :=
  ⟨hfit, fun i hi => ⟨_, hin, Offset.contains_base _ (by omega) (by omega)⟩,
    fun i hi => VG.Proof.Ed448.X86.far hd hi (by omega)⟩

theorem LoopKeep.whole {base : Addr} {o : Nat} {s t : State} (h : VG.Proof.Ed448.X86.LoopKeep base o s t)
    (ho : o + 112 ≤ 8192) : Outside base 0 8192 s.mem t.mem :=
  fun p hp => h.mem p (by simp only [W]; omega) (by omega)

theorem reduce114_ok {o : Nat} (ho : VG.Proof.Ed448.X86.Buf o) {s : State} {base : Addr} (hs : Scr s base)
    {p : BitVec 32} (hp : s.gpr .esi = p) (hin : VG.Proof.Ed448.X86.Input s base p 114) :
    WP isa (reduce114 o) s fun t => VG.Proof.Ed448.X86.LoopKeep base o s t ∧ Bounded t.mem base o ∧
      fe t.mem base o = decodeLE (bytesAt s.mem (p.setWidth 64) 114) % L := by
  unfold reduce114
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.init114_ok ho hs) fun v ⟨kv, cv, lv, vv⟩ => ?_)
  have mb := hin.bytes (kv.whole (by have := ho.2; omega))
  refine WP.mono (VG.Proof.Ed448.X86.byteLoop_ok (N := 114) ho (hs.of_keeps kv.regs (by decide))
    ((kv.regs.1 _ (by decide)).trans hp) hin.fit (by rw [kv.regs.2.1, kv.regs.2.2]; exact hin.read)
    hin.far (n0 := 114) (by decide) (by decide) (by decide) cv lv
    (by rw [vv, List.drop_eq_nil_of_le (by rw [Proof.Ed448.bytesAt_length]),
      show decodeLE [] = 0 from rfl, Nat.zero_mod]))
    fun t ⟨kt, lt, vt⟩ => ⟨kv.trans kt, lt, by rw [vt, mb]⟩

theorem init57_ok {o : Nat} (ho : VG.Proof.Ed448.X86.Buf o) {s : State} {base : Addr} (hs : Scr s base)
    {p : BitVec 32} (hp : s.gpr .esi = p) (hin : VG.Proof.Ed448.X86.Input s base p 57) :
    WP isa (.block (zeroR o ++ ([.movzx8 .eax (Impl.X448.X86.at_ .esi 56), Impl.X448.X86.st .eax o,
      .mov .ebp (.imm 56)] : List Instr))) s fun v =>
      VG.Proof.Ed448.X86.LoopKeep base o s v ∧ v.gpr .ebp = BitVec.ofNat 32 56 ∧ Bounded v.mem base o ∧
      fe v.mem base o = decodeLE ((bytesAt s.mem (p.setWidth 64) 57).drop 56) % L := by
  obtain ⟨ho1, ho2⟩ := ho
  have hT := VG.Proof.Ed448.X86.TF_eq
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.zeroR_ok ho2 hs) fun u ⟨ku, fu, zu⟩ => ?_
  have hpu : u.gpr .esi = p := (ku.1 _ (by decide)).trans hp
  have hsu := hs.of_keeps ku (by decide)
  refine wp_load8 (a := p.setWidth 64 + BitVec.ofNat 64 56)
    (by change addr (u.gpr .esi) 56 = _; rw [hpu]; exact addr_eq (by have := hin.fit; omega))
    (by rw [ku.2.1, ku.2.2]; exact hin.read 56 (by decide)) fun u1 v1 => ?_
  refine store_ok (hsu.of_upd v1 (by decide)) (by omega) fun u2 v2 => wp_mov rfl fun v hv =>
    WP.block_nil ?_
  have byte : u.mem (p.setWidth 64 + BitVec.ofNat 64 56) = s.mem (p.setWidth 64 + BitVec.ofNat 64 56) :=
    fu _ (Or.inr (by have := hin.far 56 (by decide); omega))
  have m2 : v.mem = u.mem.writeW (off base (o + 4 * 0))
      ((s.mem (p.setWidth 64 + BitVec.ofNat 64 56)).setWidth 32) := by
    rw [hv.mem, v2.mem, v1.gpr, v1.mem, byte]; rfl
  have lv : ∀ k < 28, limbs v.mem base o k =
      if k = 0 then (s.mem (p.setWidth 64 + BitVec.ofNat 64 56)).toNat else 0 := by
    intro k hk
    change (word v.mem base (o + 4 * k)).toNat = _
    rw [m2, word_write u.mem base (by omega) (by omega)]
    by_cases k0 : k = 0
    · rw [ite_eq_left k0, ite_eq_left k0, BitVec.toNat_setWidth_of_le (by decide)]
    · rw [ite_eq_right k0, ite_eq_right k0]; exact zu k hk
  have hlt := (s.mem (p.setWidth 64 + BitVec.ofNat 64 56)).isLt
  refine ⟨⟨(ku.mono (by decide)).trans ((v1.rest (by decide)).trans ((v2.rest _).trans
    (hv.rest (by decide)))), ?_⟩, hv.gpr, fun k hk => ?_, ?_⟩
  · rw [m2]
    intro q _ h2
    rw [writeW_outside _ _ _ (by omega) q (by omega)]
    exact fu q h2
  · rw [lv k hk]; split
    · simp only [VG.Proof.X448.Radix16.radix]; omega
    · decide
  · rw [decode_drop1 _ _ (by decide : 56 + 1 = 57)]
    have hL : 256 < L := by decide +kernel
    rw [Nat.mod_eq_of_lt (by omega)]
    show VG.Proof.X448.Radix16.valN (limbs v.mem base o) 28 = _
    rw [show (28 : Nat) = 1 + 27 from rfl, VG.Proof.X448.Radix16.valN_split,
      VG.Proof.X448.Radix16.valN_congr (n := 27) (g := fun _ => 0) (fun k hk => by rw [lv _ (by omega), ite_eq_right (by omega)]),
      valN_zero]
    simp only [VG.Proof.X448.Radix16.valN, lv 0 (by decide), ite_true, Nat.mul_zero, Nat.pow_zero, Nat.one_mul,
      Nat.zero_add, Nat.add_zero]

theorem reduce57_ok {o : Nat} (ho : VG.Proof.Ed448.X86.Buf o) {s : State} {base : Addr} (hs : Scr s base)
    {p : BitVec 32} (hp : s.gpr .esi = p) (hin : VG.Proof.Ed448.X86.Input s base p 57) :
    WP isa (reduce57 o) s fun t => VG.Proof.Ed448.X86.LoopKeep base o s t ∧ Bounded t.mem base o ∧
      fe t.mem base o = decodeLE (bytesAt s.mem (p.setWidth 64) 57) % L := by
  unfold reduce57
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.init57_ok ho hs hp hin) fun v ⟨kv, cv, lv, vv⟩ => ?_)
  have mb := hin.bytes (kv.whole (by have := ho.2; omega))
  refine WP.mono (VG.Proof.Ed448.X86.byteLoop_ok (N := 57) ho (hs.of_keeps kv.regs (by decide))
    ((kv.regs.1 _ (by decide)).trans hp) hin.fit (by rw [kv.regs.2.1, kv.regs.2.2]; exact hin.read)
    hin.far (n0 := 56) (by decide) (by decide) (by decide) cv lv (by rw [vv, mb]))
    fun t ⟨kt, lt, vt⟩ => ⟨kv.trans kt, lt, by rw [vt, mb]⟩

/-! ## The result -/

/-- Writes to the output preserve a word of the disjoint working space. -/
theorem out_word {m m' : Mem} {base p : Addr} {n d : Nat} (h : Outside p 0 n m m')
    (hd : d + 4 ≤ 8192) (hfar : ∀ j < 8192, n ≤ ofs p (off base j)) :
    word m' base d = word m base d := by
  apply Mem.readW_congr
  intro i hi
  rw [Offset.add_add]
  exact h _ (Or.inr (by have := hfar (d + i) (by omega); simp only [off] at this; omega))

theorem packLimb_ok {s : State} {base p : Addr} (hs : Scr s base) {o : Nat} (ho : o + 112 ≤ 4096)
    (hb : Bounded s.mem base o) {i : Nat} (hi : i < 28) (hp : (s.gpr .esi).setWidth 64 = p)
    (hfit : (s.gpr .esi).toNat + 57 ≤ 2 ^ 32)
    (hw : ∀ j < 2, InRegions s.wr (off p (2 * i + j)) 1) :
    WP isa (.block (packLimb o i)) s fun t =>
      VG.Proof.X448.Radix16.decoded t.mem p i = limbs s.mem base o i ∧ Outside p (2 * i) 2 s.mem t.mem ∧ Keeps [.eax] s t := by
  have ea : ∀ j < 2, addr (s.gpr .esi) (2 * i + j) = off p (2 * i + j) := by
    intro j hj; rw [addr_eq (by omega), hp]
  unfold packLimb
  refine load_ok hs (by omega) fun t ht => ?_
  refine VG.Proof.X448.X86.wp_store8 (a := off p (2 * i))
    (by change addr (t.gpr .esi) _ = _; rw [ht.other .esi (by decide)]; exact ea 0 (by decide))
    (by rw [ht.wr]; exact hw 0 (by decide)) fun u hu => ?_
  refine wp_shift (by decide) fun v hv => ?_
  refine VG.Proof.X448.X86.wp_store8 (a := off p (2 * i + 1))
    (by change addr (v.gpr .esi) _ = _
        rw [hv.other .esi (by decide), hu.gpr, ht.other .esi (by decide)]; exact ea 1 (by decide))
    (by rw [hv.wr, hu.wr, ht.wr]; exact hw 1 (by decide)) fun w hw' => WP.block_nil ⟨?_, ?_, ?_⟩
  · have hm : w.mem = packMem s.mem p i (word s.mem base (o + 4 * i)) := by
      rw [hw'.mem, hv.mem, hu.mem, ht.mem, Reg8.reg, hv.gpr, hu.gpr, ht.gpr]; rfl
    rw [hm]; exact packMem_decoded _ _ hi _ (hb i hi)
  · have hm : w.mem = packMem s.mem p i (word s.mem base (o + 4 * i)) := by
      rw [hw'.mem, hv.mem, hu.mem, ht.mem, Reg8.reg, hv.gpr, hu.gpr, ht.gpr]; rfl
    rw [hm]; exact packMem_outside _ _ hi _
  · exact ((ht.rest (by decide)).trans ((hu.rest _).trans
      ((hv.rest (by decide)).trans (hw'.rest _))))

theorem packAll_ok {s : State} {base p : Addr} (hs : Scr s base) {o : Nat} (ho : o + 112 ≤ 4096)
    (hb : Bounded s.mem base o) (hp : (s.gpr .esi).setWidth 64 = p)
    (hfit : (s.gpr .esi).toNat + 57 ≤ 2 ^ 32) (hw : ∀ j < 56, InRegions s.wr (off p j) 1)
    (hfar : ∀ j < 8192, 57 ≤ ofs p (off base j)) :
    WP isa (.block ((List.range 28).flatMap (packLimb o))) s fun t =>
      (∀ i < 28, VG.Proof.X448.Radix16.decoded t.mem p i = limbs s.mem base o i) ∧
      Outside p 0 56 s.mem t.mem ∧ Keeps [.eax] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, VG.Proof.X448.Radix16.decoded t.mem p i = limbs s.mem base o i) ∧ Outside p 0 (2 * n) s.mem t.mem ∧
      Keeps [.eax] s t
  have st : ∀ n t, n < 28 → inv n t → WP isa (.block (packLimb o n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have eq : ∀ j < 28, limbs t.mem base o j = limbs s.mem base o j := by
      intro j hj
      exact congrArg BitVec.toNat (VG.Proof.Ed448.X86.out_word tm (by omega) fun i hi => Nat.le_trans (by omega) (hfar i hi))
    have tb : Bounded t.mem base o := by intro j hj; rw [eq j hj]; exact hb j hj
    refine WP.mono (VG.Proof.Ed448.X86.packLimb_ok (p := p) (hs.of_keeps tk (by decide)) ho tb hn
      (by rw [tk.1 _ (by decide)]; exact hp) (by rw [tk.1 _ (by decide)]; exact hfit)
      (by intro j hj; rw [tk.2.2]; exact hw _ (by omega))) fun u ⟨uv, um, uk⟩ => ?_
    refine ⟨?_, (tm.mono (by decide) (by omega)).trans (um.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    by_cases h : i = n
    · subst i; exact uv.trans (eq n hn)
    · have byte : ∀ j < 2, u.mem (off p (2 * i + j)) = t.mem (off p (2 * i + j)) := by
        intro j hj
        exact um _ (Or.inl (by rw [ofs_off' p (by omega)]; omega))
      simp only [VG.Proof.X448.Radix16.decoded, byteN]
      have b0 := byte 0 (by decide)
      have b1 := byte 1 (by decide)
      simp only [off, Nat.add_zero] at b0 b1
      rw [b0, b1]
      exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 28) inv st 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- The registers `finish` changes. -/
def finishRegs : List Reg := [.eax, .ebx, .esi, .edi, .ebp]

/-- `finish o`: the remainder at `o` as 57 bytes at the output (the argument
0), and the callee-saved registers restored. -/
theorem finish_ok {s₀ s : State} {n sc : Nat} (hp : VG.Proof.Ed448.X86.Args s₀ n sc) (h0 : 0 < n)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    {base : Addr} (hbase : (arg s₀ sc).setWidth 64 = base)
    (hm : Outside base 0 8192 s₀.mem s.mem) (hs : Scr s base) {o : Nat} (ho : o + 112 ≤ 4096)
    (hb : Bounded s.mem base o)
    (hout : (⟨(arg s₀ 0).setWidth 64, 57⟩ : Region) ∈ s₀.wr) (hofit : (arg s₀ 0).toNat + 57 ≤ 2 ^ 32)
    (hfar : ∀ j < 8192, 57 ≤ ofs ((arg s₀ 0).setWidth 64) (off base j))
    (sv : VG.Proof.X448.X86.Saved base s₀.gpr s.mem) :
    WP isa (.block (finish o)) s fun t =>
      (∀ p ∈ VG.Proof.X448.X86.savedSlots, t.gpr p.1 = s₀.gpr p.1) ∧ Keeps VG.Proof.Ed448.X86.finishRegs s t ∧
      Outside ((arg s₀ 0).setWidth 64) 0 57 s.mem t.mem ∧
      bytesAt t.mem ((arg s₀ 0).setWidth 64) 57 = encodeLE 57 (fe s.mem base o) := by
  unfold finish
  simp only [List.cons_append, List.append_assoc]
  refine hp.load hsp hr hwr (hbase ▸ hm) h0 fun v hv => ?_
  generalize hP : (arg s₀ 0).setWidth 64 = P at hout hfar ⊢
  have hvs := hs.of_upd hv (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.packAll_ok hvs ho (hv.mem ▸ hb) (by rw [hv.gpr, hP]) (by rw [hv.gpr]; exact hofit)
    (by intro j hj; rw [hv.wr, hwr]; exact ⟨_, hout, Offset.contains_base _ (by omega) (by omega)⟩)
    hfar) fun w ⟨wd, wm, wk⟩ => ?_
  refine wp_mov rfl fun x hx => ?_
  have hxs : x.gpr .esi = arg s₀ 0 := by
    rw [hx.other .esi (by decide), wk.1 _ (by decide), hv.gpr]
  refine VG.Proof.X448.X86.wp_store8 (a := P + BitVec.ofNat 64 56)
    (by change addr (x.gpr .esi) 56 = _; rw [hxs, addr_eq (by omega), hP])
    (by rw [hx.wr, wk.2.2, hv.wr, hwr]; exact ⟨_, hout, Offset.contains_base _ (by decide) (by decide)⟩)
    fun y hy => ?_
  have hm2 : y.mem = w.mem.writeW (P + BitVec.ofNat 64 56) (0 : BitVec 8) := by
    rw [hy.mem, Reg8.reg, hx.gpr, hx.mem]; rfl
  have ym : Outside P 0 57 s.mem y.mem := by
    rw [hm2, ← hv.mem]
    intro q hq
    rw [writeW8_outside _ _ _ (by decide) (by intro e; simp only [ofs] at hq e; omega)]
    exact wm q (by omega)
  have ys := ((hvs.of_keeps wk (by decide)).of_upd hx (by decide)).of_keeps (hy.rest []) (by decide)
  have svy : VG.Proof.X448.X86.Saved base s₀.gpr y.mem := sv.of_readW fun q hq => by
    have := VG.Proof.X448.X86.savedSlots_bound q hq
    exact VG.Proof.Ed448.X86.out_word ym (by omega) hfar
  refine WP.mono (VG.Proof.X448.X86.restore_ok ys svy) fun t ⟨tr, tm, tk⟩ => ?_
  refine ⟨tr, ?_, by rw [tm]; exact ym, ?_⟩
  · refine (hv.rest (by decide)).trans ((wk.mono (by decide)).trans ((hx.rest (by decide)).trans
      ((hy.rest _).trans (tk.mono ?_))))
    intro r hr; simp only [restoreRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [tm]
    refine encode_57 hb (fun k hk => ?_) ?_
    · have e := wd k hk
      rw [hv.mem] at e
      rw [← e]
      simp only [VG.Proof.X448.Radix16.decoded, byteN]
      have b : ∀ i < 56, y.mem (P + BitVec.ofNat 64 i) = w.mem (P + BitVec.ofNat 64 i) := fun i hi => by
        rw [hm2, writeW8_outside _ _ _ (by decide) (by rw [ofs_off' P (by omega)]; omega)]
      rw [b (2 * k) (by omega), b (2 * k + 1) (by omega)]
    · rw [hm2, writeW8_apply, ite_eq_left rfl]

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.BaseEncode`. -/
section

/-!
# Ed448 base-point multiplication on x86 (32-bit): the encoding

`baseEncode`: `Z` inverted into slot 21, `y = Y/Z` into slot 4 and
`x = X/Z` into slot 1; `x` fully reduced and its low bit written as the top
bit of the output's 57th byte; `y` copied into slot 1, fully reduced and
written to the output's first 56 bytes (RFC 8032 §5.2.2); then the
callee-saved registers restored (`baseEncode_ok`). The 57 bytes are
`encodePoint` of the point in slots 0–2 (`Proof.Ed448.encodePoint_code`).
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Impl.Ed448.X86 (signBit baseEncode)
open VG.Impl.X448.X86 (slot X2 ACC ld at_)
open VG.Spec.Ed448 (bytesAt)

theorem invEnv_x0 (e : Env) : invEnv e 0 = e 0 := rfl

/-- The value of slot 1 mod 2 is its limb 0's. -/
theorem fe_mod2 (m : Mem) (base : Addr) : fe m base X2 % 2 = limbs m base X2 0 % 2 := by
  have h : ∀ n, VG.Proof.X448.Radix16.valN (limbs m base X2) (n + 1) % 2 = limbs m base X2 0 % 2 := by
    intro n
    induction n with
    | zero => simp [VG.Proof.X448.Radix16.valN]
    | succ n ih =>
      have e : (2 ^ 16) ^ (n + 1) * limbs m base X2 (n + 1) =
          2 * ((2 ^ 16) ^ n * 2 ^ 15 * limbs m base X2 (n + 1)) := by
        rw [Nat.pow_succ]; grind
      rw [VG.Proof.X448.Radix16.valN_succ, Nat.add_mod, ih, VG.Proof.X448.Radix16.radix, e, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod]
  exact h 27

/-- The low bit of a word, rotated into bit 7 of its low byte. -/
theorem sign_byte (w : BitVec 32) :
    ((w &&& (1 : BitVec 32)).rotateRight 25).setWidth 8 = BitVec.ofNat 8 (128 * (w.toNat % 2)) := by
  have e : w &&& (1 : BitVec 32) = BitVec.ofNat 32 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 2 ^ 1 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := w.toNat % 2)
        (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))]
  have h : ∀ b < 2, ((BitVec.ofNat 32 b).rotateRight 25).setWidth 8 = BitVec.ofNat 8 (128 * b) := by
    decide
  rw [e]; exact h _ (Nat.mod_lt _ (by decide))

def encodeFields : List FieldOp := [.mul 4 1 21, .mul 1 0 21]

theorem encodeFields_impl :
    [.mul (slot 4) (slot 1) (slot 21), .mul X2 (slot 0) (slot 21)] = encodeFields.map FieldOp.impl := by
  decide +kernel

/-- The registers the encoding may change. -/
def encRegs : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi]

theorem baseEncode_ok {s₀ s : State} {n sc : Nat} (hA : VG.Proof.Ed448.X86.Args s₀ n sc) (h0 : 0 < n)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    {base : Addr} (hbase : (arg s₀ sc).setWidth 64 = base)
    (hm : Outside base 0 8192 s₀.mem s.mem) (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (hout : (⟨(arg s₀ 0).setWidth 64, 57⟩ : Region) ∈ s₀.wr) (hofit : (arg s₀ 0).toNat + 57 ≤ 2 ^ 32)
    (hd : (⟨(arg s₀ 0).setWidth 64, 57⟩ : Region).Disjoint ⟨base, 8192⟩)
    {g : Reg → BitVec 32} (sv : VG.Proof.X448.X86.Saved base g s.mem) :
    WP isa baseEncode s fun t =>
      bytesAt t.mem ((arg s₀ 0).setWidth 64) 57 =
        Spec.Ed448.encodePoint ⟨E s.mem base 0, E s.mem base 1, E s.mem base 2⟩ ∧
      (∀ p ∈ VG.Proof.X448.X86.savedSlots, t.gpr p.1 = g p.1) ∧ Keeps VG.Proof.Ed448.X86.encRegs s t ∧
      Frame [⟨base, 8192⟩, ⟨(arg s₀ 0).setWidth 64, 57⟩] s.mem t.mem := by
  have hfar : ∀ j < 8192, 57 ≤ ofs ((arg s₀ 0).setWidth 64) (off base j) := fun j hj => VG.Proof.Ed448.X86.far_out hd hj
  have hfar56 : ∀ j < 8192, 56 ≤ ofs ((arg s₀ 0).setWidth 64) (off base j) :=
    fun j hj => Nat.le_trans (by decide) (hfar j hj)
  have hw57 : ∀ j < 57, InRegions s₀.wr (off ((arg s₀ 0).setWidth 64) j) 1 := fun j hj =>
    ⟨_, hout, Offset.contains_base _ (by omega) (by omega)⟩
  unfold baseEncode
  refine WP.seq (WP.mono (VG.Proof.X448.X86.invert_ok hs hb) fun s₁ ⟨k₁, b₁, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  rw [VG.Proof.Ed448.X86.encodeFields_impl]
  refine WP.seq (WP.mono (VG.Proof.X448.X86.ops_ok hs₁ b₁ VG.Proof.Ed448.X86.encodeFields) fun s₂ ⟨k₂, b₂, e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have ex : E s₂.mem base 1 = E s.mem base 0 * Proof.X448.invert (E s.mem base 2) := by
    rw [e₂, e₁]
    simp only [applyOps, VG.Proof.Ed448.X86.encodeFields, FieldOp.apply, opMul, Function.update_self]
    rw [Function.update_of_ne (show (21 : Index) ≠ 4 by decide),
      Function.update_of_ne (show (0 : Index) ≠ 4 by decide), VG.Proof.Ed448.X86.invEnv_x0, invEnv_eval]
  have ey : E s₂.mem base 4 = E s.mem base 1 * Proof.X448.invert (E s.mem base 2) := by
    rw [e₂, e₁]
    simp only [applyOps, VG.Proof.Ed448.X86.encodeFields, FieldOp.apply, opMul]
    rw [Function.update_of_ne (show (4 : Index) ≠ 1 by decide), Function.update_self, invEnv_x2,
      invEnv_eval]
  simp only [List.append_assoc]
  -- `x` fully reduced.
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.freeze_ok hs₂ (b₂ 1)) fun s₃ ⟨bx₃, vx₃, m₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have m03 : Outside base 0 8192 s.mem s₃.mem :=
    ((k₁.mem.whole (by decide) (by decide)).trans (k₂.mem.whole (by decide) (by decide))).trans
      (m₃.whole (by decide))
  have kk : Keeps (.esi :: workRegs) s s₃ :=
    k₁.regs.trans ((k₂.regs.mono (by decide)).trans (k₃.mono (by decide)))
  -- Its bit, to the output's byte 56.
  rw [Impl.Ed448.X86.signBit, List.cons_append]
  refine hA.load (kk.1 _ (by decide) |>.trans hsp) (kk.2.1.trans hr) (kk.2.2.trans hwr)
    (hbase ▸ hm.trans m03) h0 fun s₄ u₄ => ?_
  refine load_ok (hs₃.of_upd u₄ (by decide)) (by decide) fun s₅ u₅ => ?_
  refine wp_alu (Or.inr (Or.inr (Or.inl rfl))) rfl fun s₆ u₆ _ => ?_
  refine wp_shift (by decide) fun s₇ u₇ => ?_
  have esi₇ : s₇.gpr .esi = arg s₀ 0 := by
    rw [u₇.other .esi (by decide), u₆.other .esi (by decide), u₅.other .esi (by decide), u₄.gpr]
  refine VG.Proof.X448.X86.wp_store8 (a := (arg s₀ 0).setWidth 64 + BitVec.ofNat 64 56)
    (by change addr (s₇.gpr .esi) 56 = _; rw [esi₇]; exact addr_eq (by omega))
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, kk.2.2, hwr]; exact hw57 56 (by decide)) fun s₈ u₈ => ?_
  have hx : (E s₂.mem base 1).val = fe s₂.mem base X2 % Spec.X448.P := Proof.X448.toFe_val _
  have byte₈ : s₈.mem ((arg s₀ 0).setWidth 64 + BitVec.ofNat 64 56) =
      BitVec.ofNat 8 (128 * ((E s.mem base 0 * Proof.X448.invert (E s.mem base 2)).val % 2)) := by
    rw [u₈.mem, writeW8_apply, ite_eq_left rfl, Reg8.reg]
    have : s₇.gpr .eax = (s₅.gpr .eax &&& (1 : BitVec 32)).rotateRight 25 := by
      rw [u₇.gpr]; change (s₆.gpr .eax).rotateRight 25 = _; rw [u₆.gpr]; rfl
    rw [this, VG.Proof.Ed448.X86.sign_byte, u₅.gpr, u₄.mem, ← ex, hx, ← vx₃, VG.Proof.Ed448.X86.fe_mod2]; rfl
  have m₈ : s₈.mem = s₃.mem.writeW ((arg s₀ 0).setWidth 64 + BitVec.ofNat 64 56)
      ((s₇.gpr Reg8.al.reg).setWidth 8) := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have o₈ : Outside ((arg s₀ 0).setWidth 64) 0 57 s₃.mem s₈.mem := by
    rw [m₈]; intro q hq
    exact writeW8_outside _ _ _ (d := 56) (by decide) (by omega)
  have w₈ : ∀ d, d + 4 ≤ 8192 → word s₈.mem base d = word s₃.mem base d := fun d hd4 =>
    VG.Proof.Ed448.X86.out_word o₈ hd4 hfar
  have hs₈ : Scr s₈ base := (((hs₃.of_upd u₄ (by decide)).of_upd u₅ (by decide)).of_upd u₆ (by decide)).of_upd
    u₇ (by decide) |>.of_keeps (u₈.rest []) (by decide)
  have E₈ : E s₈.mem base = E s₃.mem base := by
    funext i
    simp only [E, VG.Proof.X448.X86.F]
    exact congrArg Proof.X448.toFe (VG.Proof.X448.Radix16.valN_congr fun j hj =>
      congrArg BitVec.toNat (w₈ _ (by have := i.isLt; simp only [slot]; omega)))
  have E₃ : E s₃.mem base = E s₂.mem base := by
    rw [E_update (o := 1) m₃]
    funext i
    by_cases hi : i = 1
    · subst hi; rw [Function.update_self]
      change Proof.X448.toFe (fe s₃.mem base X2) = Proof.X448.toFe (fe s₂.mem base X2)
      rw [vx₃]; exact Proof.X448.toFe_mod _
    · rw [Function.update_of_ne hi]
  have b₃ : BoundedEnv s₃.mem base := bounded_update (o := 1) m₃ b₂ bx₃
  have b₈ : BoundedEnv s₈.mem base := fun i j hj => by
    change (word s₈.mem base (slot i.val + 4 * j)).toNat < _
    rw [w₈ _ (by have := i.isLt; simp only [slot]; omega)]; exact b₃ i j hj
  -- `y` into slot 1, fully reduced.
  change WP isa (.block (Impl.X448.X86.copy X2 (slot 4) ++ _)) s₈ _
  rw [WP.block_append_iff]
  refine WP.mono (copyE hs₈ b₈ 1 4) fun s₉ ⟨k₉, b₉, e₉⟩ => ?_
  have hs₉ := k₉.scr hs₈
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.freeze_ok hs₉ (b₉ 1)) fun s₁₀ ⟨by₁₀, vy₁₀, m₁₀, k₁₀⟩ => ?_
  have hs₁₀ := hs₉.of_keeps k₁₀ (by decide)
  have y₁₀ : fe s₁₀.mem base X2 = (E s.mem base 1 * Proof.X448.invert (E s.mem base 2)).val := by
    have hy : (E s₉.mem base 1).val = fe s₉.mem base X2 % Spec.X448.P := Proof.X448.toFe_val _
    have h9 : E s₉.mem base 1 = E s₈.mem base 4 := by
      rw [e₉]; exact Function.update_self _ _ _
    rw [vy₁₀, ← hy, h9, E₈, E₃, ey]
  -- The output.
  have esi₁₀ : s₁₀.gpr .esi = arg s₀ 0 := by
    rw [k₁₀.1 _ (by decide), k₉.regs.1 _ (by decide), u₈.gpr, esi₇]
  have wr₁₀ : s₁₀.wr = s₀.wr := by
    rw [k₁₀.2.2, k₉.regs.2.2, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, kk.2.2, hwr]
  rw [WP.block_append_iff]
  refine WP.mono (output_ok (p := (arg s₀ 0).setWidth 64) hs₁₀ by₁₀ (by rw [esi₁₀])
    (by rw [esi₁₀]; omega) (fun j hj => by rw [wr₁₀]; exact hw57 j (by omega)) hfar56)
    fun s₁₁ ⟨v₁₁, o₁₁, k₁₁⟩ => ?_
  -- The saved registers.
  have sv₃ : VG.Proof.X448.X86.Saved base g s₃.mem :=
    ((sv.outside2 k₁.mem (by decide) (by decide)).outside2 k₂.mem (by decide) (by decide)).field m₃
      (by decide)
  have sv₈ : VG.Proof.X448.X86.Saved base g s₈.mem := sv₃.of_readW fun q hq => by
    have := VG.Proof.X448.X86.savedSlots_bound q hq; exact w₈ _ (by omega)
  have sv₁₀ : VG.Proof.X448.X86.Saved base g s₁₀.mem :=
    (sv₈.outside2 k₉.mem (by decide) (by decide)).field m₁₀ (by decide)
  have sv₁₁ : VG.Proof.X448.X86.Saved base g s₁₁.mem := sv₁₀.of_readW fun q hq => by
    have := VG.Proof.X448.X86.savedSlots_bound q hq
    exact VG.Proof.Ed448.X86.out_word o₁₁ (by omega) fun j hj => Nat.le_trans (by decide) (hfar j hj)
  have hs₁₁ : Scr s₁₁ base := hs₁₀.of_keeps k₁₁ (by decide)
  refine WP.mono (VG.Proof.X448.X86.restore_ok hs₁₁ sv₁₁) fun t ⟨rt, mt, kt⟩ => ?_
  have f810 : Outside base 0 8192 s₈.mem s₁₀.mem :=
    (k₉.mem.whole (by decide) (by decide)).trans (m₁₀.whole (by decide))
  refine ⟨?_, rt, ?_, ?_⟩
  · have b56 : s₁₁.mem ((arg s₀ 0).setWidth 64 + BitVec.ofNat 64 56) =
        s₈.mem ((arg s₀ 0).setWidth 64 + BitVec.ofNat 64 56) := by
      rw [o₁₁ _ (Or.inr (by rw [ofs_off' _ (by decide)]))]
      exact f810 _ (Or.inr (VG.Proof.Ed448.X86.far hd (i := 56) (by decide) (by decide)))
    rw [mt, Limbs16.bytesAt_57, v₁₁, y₁₀, b56, byte₈, Proof.Ed448.encodePoint_code]
  · refine (k₁.regs.mono ?_).trans ((k₂.regs.mono ?_).trans ((k₃.mono ?_).trans
      ((u₄.rest ?_).trans ((u₅.rest ?_).trans ((u₆.rest ?_).trans ((u₇.rest ?_).trans
      ((u₈.rest _).trans ((k₉.regs.mono ?_).trans ((k₁₀.mono ?_).trans ((k₁₁.mono ?_).trans
      (kt.mono ?_)))))))))))
    all_goals first | decide | (intro r hr; revert r; decide)
  · rw [mt]
    have ws : ∀ r ∈ [(⟨base, 8192⟩ : Region)], r ∈ [(⟨base, 8192⟩ : Region),
        ⟨(arg s₀ 0).setWidth 64, 57⟩] := by simp
    have os : ∀ r ∈ [(⟨(arg s₀ 0).setWidth 64, 57⟩ : Region)], r ∈ [(⟨base, 8192⟩ : Region),
        ⟨(arg s₀ 0).setWidth 64, 57⟩] := by simp
    refine ((Outside.frame m03).mono ws).trans (((Outside.frame o₈).mono os).trans
      (((Outside.frame f810).mono ws).trans (((Outside.frame o₁₁).sub fun r hr => ?_))))
    refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
    rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.BaseLocal`. -/
section

/-!
# Ed448 base-point multiplication on x86 (32-bit): the contract the proof is written against

`scalarBaseLocal`, in a module of its own: callers proven for any code
meeting it need not import the proof.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86
open VG.Spec.Ed448 (bytesAt)

/-- `vg_ed448_scalar_base(out, scalar, scratch)`, whose arguments are on the
stack (cdecl). -/
def scalarBaseLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let scalar : Region := ⟨(arg s 1).setWidth 64, 57⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [scalar, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s t := VG.Spec.Ed448.bytesAt t.mem ((arg s 0).setWidth 64) 57 =
    Spec.Ed448.scalarBase (VG.Spec.Ed448.bytesAt s.mem ((arg s 1).setWidth 64) 57)
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.BaseSetup`. -/
section

/-!
# Ed448 base-point multiplication on x86 (32-bit): the entry

Every slot set to its initial value (`initSlots_ok`): `R = (0 : 1 : 1)`, `B`
the base point, `d`, and zero elsewhere, every limb below `2¹⁶`. Then the
scalar's 57 bytes expanded into its 456 bits at `BITS` (`baseBytes_ok`), as
X448 expands its scalar (`bitJ`).
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Impl.Ed448.X86 (initVal initLimb initStep initSlot initSlots baseByte)
open VG.Impl.X448.X86 (slot ACC st BITS bitJ at_)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-! ## The slots -/

theorem initVal_lt (i : Nat) : initVal i < Spec.X448.P := by
  unfold initVal
  repeat (first | exact Fin.isLt _ | (split; exact Fin.isLt _) | split)
  decide +kernel

theorem initLimb_lt (i k : Nat) : initLimb i k < 65536 := Nat.mod_lt _ (by decide)

theorem valN_digits (v : Nat) : ∀ n, VG.Proof.X448.Radix16.valN (fun k => v / 2 ^ (16 * k) % 65536) n = v % VG.Proof.X448.Radix16.radix ^ n
  | 0 => by simp [VG.Proof.X448.Radix16.valN, Nat.mod_one]
  | n + 1 => by
    rw [VG.Proof.X448.Radix16.valN_succ, VG.Proof.Ed448.X86.valN_digits v n, Nat.mod_pow_succ, VG.Proof.X448.Radix16.radix, ← Nat.pow_mul]

theorem initStep_ok {s : State} {base : Addr} (hs : Scr s base)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * 16)) (hb : s.gpr .ebx = 0) {i k : Nat}
    (hi : i < 22) (hk : k < 28) :
    WP isa (.block (initStep i k)) s fun t =>
      t.mem = s.mem.writeW (off base (slot i + 4 * k)) (BitVec.ofNat 32 (initLimb i k)) ∧
        Keeps [.eax] s t := by
  have hsl : slot i + 4 * k + 4 ≤ 4096 := by simp only [slot]; omega
  have ea : ∀ u : State, Scr u base → u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * 16) →
      u.ea (VG.Impl.X448.X86.at_ .ebp (128 * i + 4 * k)) = off base (slot i + 4 * k) := fun u hu hpu => by
    rw [rowEa hu hpu (by omega)]; congr 1; simp only [slot]; omega
  unfold initStep
  split
  · rename_i h0
    refine wp_store (ea s hs hp) (hs.write (by omega)) fun t ht => WP.block_nil ⟨?_, ht.rest _⟩
    rw [ht.mem, hb, h0]; rfl
  · refine VG.Proof.X448.X86.wp_mov rfl fun u hu => ?_
    have hsu := hs.of_upd hu (by decide)
    refine wp_store (ea u hsu (by rw [hu.other .ebp (by decide), hu.other .edi (by decide)]; exact hp))
      (hsu.write (by omega)) fun t ht =>
      WP.block_nil ⟨by rw [ht.mem, hu.mem, hu.gpr], (hu.rest (by decide)).trans (ht.rest _)⟩

theorem initSlot_ok {s : State} {base : Addr} (hs : Scr s base)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * 16)) (hb : s.gpr .ebx = 0) {i : Nat}
    (hi : i < 22) :
    WP isa (.block (initSlot i)) s fun t =>
      (∀ k < 28, limbs t.mem base (slot i) k = initLimb i k) ∧
        Outside base (slot i) 112 s.mem t.mem ∧ Keeps [.eax] s t := by
  have hsl : slot i + 112 ≤ 4096 := by simp only [slot]; omega
  let inv := fun n (t : State) => (∀ k < n, limbs t.mem base (slot i) k = initLimb i k) ∧
    Outside base (slot i) 112 s.mem t.mem ∧ Keeps [.eax] s t
  refine wp_range_flatMap (M := isa) (N := 28) inv (fun n t hn ⟨tf, tm, tk⟩ => ?_) 28 (by decide) s
    ⟨fun _ h => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  refine WP.mono (VG.Proof.Ed448.X86.initStep_ok (hs.of_keeps tk (by decide))
    (by rw [tk.1 _ (by decide), tk.1 _ (by decide)]; exact hp) ((tk.1 _ (by decide)).trans hb) hi hn)
    fun u ⟨um, uk⟩ => ⟨fun k hk => ?_, tm.trans ?_, tk.trans uk⟩
  · change (word u.mem base (slot i + 4 * k)).toNat = _
    rw [um, word_write t.mem base (by omega) (by omega)]
    by_cases h : k = n
    · rw [ite_eq_left h, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := VG.Proof.Ed448.X86.initLimb_lt i n; omega)]
    · rw [ite_eq_right h]; exact tf k (by omega)
  · rw [um]; exact (writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)

theorem initSlots_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block initSlots) s fun t =>
      (∀ i < 22, ∀ k < 28, limbs t.mem base (slot i) k = initLimb i k) ∧
        Outside base 64 2816 s.mem t.mem ∧ Keeps [.eax, .ebx, .ebp] s t := by
  unfold initSlots
  refine VG.Proof.X448.X86.wp_mov rfl fun u₁ hu₁ => wp_alu (Or.inl rfl) rfl fun u₂ hu₂ _ => VG.Proof.X448.X86.wp_mov rfl fun u hu => ?_
  have hsu := ((hs.of_upd hu₁ (by decide)).of_upd hu₂ (by decide)).of_upd hu (by decide)
  have ku : Keeps [.eax, .ebx, .ebp] s u :=
    (hu₁.rest (by decide)).trans ((hu₂.rest (by decide)).trans (hu.rest (by decide)))
  have hpu : u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * 16) := by
    rw [hu.other .ebp (by decide), hu.other .edi (by decide), hu₂.gpr, hu₂.other .edi (by decide),
      hu₁.other .edi (by decide)]
    change u₁.gpr .ebp + BitVec.ofNat 32 64 = _
    rw [hu₁.gpr]
  have mu : u.mem = s.mem := by rw [hu.mem, hu₂.mem, hu₁.mem]
  let inv := fun n (t : State) => (∀ i < n, ∀ k < 28, limbs t.mem base (slot i) k = initLimb i k) ∧
    Outside base 64 2816 u.mem t.mem ∧ Keeps [.eax] u t
  refine WP.mono (wp_range_flatMap (M := isa) (N := 22) inv (fun n t hn ⟨tf, tm, tk⟩ => ?_) 22
    (by decide) u ⟨fun _ h => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩)
    fun t ⟨tf, tm, tk⟩ => ⟨tf, by rw [← mu]; exact tm, ku.trans (tk.mono (by simp))⟩
  refine WP.mono (VG.Proof.Ed448.X86.initSlot_ok (hsu.of_keeps tk (by decide))
    (by rw [tk.1 _ (by decide), tk.1 _ (by decide)]; exact hpu) ((tk.1 _ (by decide)).trans hu.gpr) hn)
    fun v ⟨vf, vm, vk⟩ => ⟨fun i hi k hk => ?_, tm.trans (vm.mono (by simp only [slot]; omega)
      (by simp only [slot]; omega)), tk.trans vk⟩
  by_cases h : i = n
  · subst h; exact vf k hk
  · rw [vm.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) hk]
    exact tf i (by omega) k hk

/-- The slots' values. -/
theorem initSlots_E {m : Mem} {base : Addr}
    (h : ∀ i < 22, ∀ k < 28, limbs m base (slot i) k = initLimb i k) (i : Index) :
    VG.Proof.X448.X86.E m base i = Proof.X448.toFe (initVal i.val) := by
  simp only [VG.Proof.X448.X86.E, VG.Proof.X448.X86.F, VG.Proof.X448.X86.fe]
  rw [VG.Proof.X448.Radix16.valN_congr (g := fun k => initVal i.val / 2 ^ (16 * k) % 65536) (h i.val i.isLt), VG.Proof.Ed448.X86.valN_digits,
    Nat.mod_eq_of_lt (Nat.lt_trans (VG.Proof.Ed448.X86.initVal_lt _) (by decide +kernel))]

theorem initSlots_bounded {m : Mem} {base : Addr}
    (h : ∀ i < 22, ∀ k < 28, limbs m base (slot i) k = initLimb i k) : BoundedEnv m base :=
  fun i k hk => by rw [h i.val i.isLt k hk]; exact VG.Proof.Ed448.X86.initLimb_lt _ _

/-! ## The scalar's bits -/

/-- `bitJ i j` for the 57 bytes of a scalar (X448's `bitJ_ok`, which is for
56). -/
theorem bitJ57_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 57)
    {b : BitVec 8} (ha : s.gpr .eax = b.setWidth 32) {j : Nat} (hj : j < 8) :
    WP isa (.block (bitJ i j)) s fun t =>
      t.mem = s.mem.writeW (off base (VG.Impl.X448.X86.BITS + (8 * i + j)))
        (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧ Keeps [.edx] s t := by
  rw [Impl.X448.X86.bitJ, WP.block_append_iff]
  refine WP.mono (bitShift_ok hj) fun t ⟨tv, tm, tk⟩ => ?_
  refine wp_alu (by simp [plain]) rfl fun u hu _ => ?_
  have us := (hs.of_keeps tk (by decide)).of_upd hu (by decide)
  have ea := us.ea (d := VG.Impl.X448.X86.BITS + 8 * i + j) (by simp only [VG.Impl.X448.X86.BITS]; omega)
  have wr := us.write (d := VG.Impl.X448.X86.BITS + 8 * i + j) (n := 1) (by simp only [VG.Impl.X448.X86.BITS]; omega)
  refine VG.Proof.X448.X86.wp_store8 ea wr fun v hv => WP.block_nil ⟨?_, tk.trans ?_⟩
  · rw [hv.mem, hu.mem, tm, Reg8.reg, hu.gpr]
    change s.mem.writeW _ ((t.gpr .edx &&& (1 : BitVec 32)).setWidth 8) = _
    rw [tv, ha, bit_byte b j hj, Nat.add_assoc]
  · exact (hu.rest (by decide)).trans (hv.rest _)

theorem byteBits57_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 57)
    {b : BitVec 8} (ha : s.gpr .eax = b.setWidth 32) :
    WP isa (.block ((List.range 8).flatMap (bitJ i))) s fun t =>
      (∀ j < 8, t.mem (off base (VG.Impl.X448.X86.BITS + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
      Outside base (VG.Impl.X448.X86.BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.edx] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, t.mem (off base (VG.Impl.X448.X86.BITS + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
    Outside base (VG.Impl.X448.X86.BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.edx] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (bitJ i n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (VG.Proof.Ed448.X86.bitJ57_ok (hs.of_keeps tk (by decide)) hi
      ((tk.1 _ (by decide)).trans ha) hn) fun u ⟨um, uk⟩ => ?_
    refine ⟨?_, tm.trans ?_, tk.trans uk⟩
    · intro j hj
      rw [um, writeW8_apply]
      have eq : off base (VG.Impl.X448.X86.BITS + (8 * i + j)) = off base (VG.Impl.X448.X86.BITS + (8 * i + n)) ↔ j = n := by
        rw [off_eq_iff base (by simp only [VG.Impl.X448.X86.BITS]; omega) (by simp only [VG.Impl.X448.X86.BITS]; omega)]
        omega
      by_cases he : j = n
      · rw [ite_eq_left (eq.mpr he), he]
      · rw [ite_eq_right (fun h => he (eq.mp h))]; exact tf j (by omega)
    · intro x hx
      rw [um]
      exact writeW8_outside _ _ _ (by simp only [VG.Impl.X448.X86.BITS]; omega) (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hj => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- The 57 bytes at `esi` expanded into their bits at `BITS`. -/
theorem baseBytes_ok {s : State} {base k : Addr} (hs : Scr s base)
    (hk : (s.gpr .esi).setWidth 64 = k) (hfit : (s.gpr .esi).toNat + 57 ≤ 2 ^ 32)
    (hr : ∀ i < 57, InRegions (s.rd ++ s.wr) (off k i) 1)
    (hd : ∀ i < 57, 8192 ≤ ofs base (off k i)) :
    WP isa (.block ((List.range 57).flatMap baseByte)) s fun t =>
      Keeps [.eax, .edx] s t ∧ Outside base VG.Impl.X448.X86.BITS 456 s.mem t.mem ∧
      ∀ j < 456, t.mem (off base (VG.Impl.X448.X86.BITS + j)) =
        BitVec.ofNat 8 ((decodeLE (bytesAt s.mem k 57) >>> j) &&& 1) := by
  let inv := fun n (t : State) => Keeps [.eax, .edx] s t ∧ Outside base VG.Impl.X448.X86.BITS (8 * n) s.mem t.mem ∧
    ∀ j < 8 * n, t.mem (off base (VG.Impl.X448.X86.BITS + j)) =
      BitVec.ofNat 8 (((s.mem (off k (j / 8))).toNat >>> (j % 8)) &&& 1)
  have step : ∀ n t, n < 57 → inv n t → WP isa (.block (baseByte n)) t (inv (n + 1)) := by
    intro n t hn ⟨tk, tm, tb⟩
    have ea : t.ea (VG.Impl.X448.X86.at_ .esi n) = off k n := by
      change VG.X86.addr (t.gpr .esi) n = _
      rw [tk.1 _ (by decide), addr_eq (by omega), hk]
    unfold baseByte
    refine wp_load8 ea (by rw [tk.2.1, tk.2.2]; exact hr n hn) fun u hu => ?_
    have us := (hs.of_keeps tk (by decide)).of_upd hu (by decide)
    refine WP.mono (VG.Proof.Ed448.X86.byteBits57_ok us hn hu.gpr) fun v ⟨vb, vm, vk⟩ => ?_
    have byte : t.mem (off k n) = s.mem (off k n) :=
      tm _ (Or.inr (by have := hd n hn; simp only [VG.Impl.X448.X86.BITS]; omega))
    refine ⟨tk.trans ((hu.rest (by decide)).trans (vk.mono (by simp))), ?_, ?_⟩
    · rw [hu.mem] at vm
      exact (tm.mono (by omega) (by omega)).trans (vm.mono (by omega) (by omega))
    · intro j hj
      rcases Nat.lt_or_ge j (8 * n) with h | h
      · rw [vm _ (Or.inl (by rw [ofs_off' base (by simp only [VG.Impl.X448.X86.BITS]; omega)]; omega)), hu.mem]
        exact tb j h
      · have e := vb (j - 8 * n) (by omega)
        rw [show 8 * n + (j - 8 * n) = j by omega, byte] at e
        rw [e, show j / 8 = n by omega, show j % 8 = j - 8 * n by omega]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 57) inv step 57 (by decide) s
    ⟨Keeps.refl _ _, Outside.refl _ _ _ _, fun _ hj => by omega⟩) fun t ⟨tk, tm, tb⟩ =>
    ⟨tk, tm, fun j hj => by rw [tb j hj, Proof.Ed448.scalar_bit _ _ hj]⟩

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.BaseStep`. -/
section

/-!
# Ed448 base-point multiplication on x86 (32-bit): the loop over the bits

The doubling and addition programs (`Impl/Ed448/Formulas.lean`) run as X448's
verified field operations on the slots (`ops_ok`), and evaluate to `double`
and the specification's `pointAdd` (`baseEnv_r`): `Proof/Ed448/Ref.lean`'s
`ladderStep`. One iteration (`baseStep_ok`) doubles `R` (slots 0–2), adds
`B` (slots 8–10) into `T` (slots 3–5) and swaps `T` into `R` with the mask
of the bit; the loop (`baseLoop_ok`) leaves `R` as the ladder over all 456
bits, `ladder k 456`.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86
open VG.Proof.Ed448 (double ladderStep ladder ladder_bit pt addWith)
open VG.Impl.Ed448 (doubleOps addOps)
open VG.Impl.Ed448.X86 (toOp field baseMask baseSwap baseStep baseLoop)
open VG.Impl.X448.X86 (BITS slot ACC cswap)

/-! ## The field programs -/

def doubleFields : List FieldOp := [
  .add 12 0 1, .mul 12 12 12, .mul 13 0 0, .mul 14 1 1, .add 15 13 14, .mul 16 2 2,
  .add 17 16 16, .sub 17 15 17, .sub 18 12 15, .mul 0 18 17, .sub 19 13 14, .mul 1 15 19,
  .mul 2 15 17]

def addFields : List FieldOp := [
  .mul 12 2 10, .mul 13 12 12, .mul 14 0 8, .mul 15 1 9, .mul 16 11 14, .mul 16 16 15,
  .sub 17 13 16, .add 18 13 16, .add 19 0 1, .add 20 8 9, .mul 19 19 20, .mul 20 12 17,
  .sub 19 19 14, .sub 19 19 15, .mul 3 20 19, .mul 20 12 18, .sub 19 15 14, .mul 4 20 19,
  .mul 5 17 18]

theorem doubleFields_impl : doubleOps.map toOp = doubleFields.map FieldOp.impl := by decide +kernel
theorem addFields_impl : addOps.map toOp = addFields.map FieldOp.impl := by decide +kernel

/-- The slots after an iteration, for the bit `sw`. -/
def baseEnv (sw : Bool) (e : Env) : Env :=
  opSwap 2 5 sw (opSwap 1 4 sw (opSwap 0 3 sw (applyOps VG.Proof.Ed448.X86.addFields (applyOps VG.Proof.Ed448.X86.doubleFields e))))

theorem baseEnv_pt (sw : Bool) (e : Env) :
    pt (VG.Proof.Ed448.X86.baseEnv sw e) 0 1 2 =
      if sw then addWith (e 11) (double (pt e 0 1 2)) (pt e 8 9 10) else double (pt e 0 1 2) := by
  cases sw <;> rfl

theorem baseEnv_r (sw : Bool) (e : Env) (hq : pt e 8 9 10 = Spec.Ed448.basePoint)
    (hd : e 11 = Spec.Ed448.d) :
    pt (VG.Proof.Ed448.X86.baseEnv sw e) 0 1 2 = ladderStep sw (pt e 0 1 2) := by
  rw [VG.Proof.Ed448.X86.baseEnv_pt, hq, hd]; rfl

theorem baseEnv_q (sw : Bool) (e : Env) : pt (VG.Proof.Ed448.X86.baseEnv sw e) 8 9 10 = pt e 8 9 10 := by
  cases sw <;> rfl

theorem baseEnv_d (sw : Bool) (e : Env) : VG.Proof.Ed448.X86.baseEnv sw e 11 = e 11 := by
  cases sw <;> rfl

/-! ## One iteration -/

theorem mask_byte : ∀ b < 2, (0 : BitVec 32) - (BitVec.ofNat 8 b).setWidth 32 = VG.Proof.X448.X86.mask (decide (b = 1)) := by
  decide

theorem baseMask_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 456)
    (hb : s.gpr .esi = BitVec.ofNat 32 t) {b : Nat} (hb2 : b < 2)
    (hbit : s.mem (off base (VG.Impl.X448.X86.BITS + t)) = BitVec.ofNat 8 b) :
    WP isa (.block baseMask) s fun u =>
      u.gpr .ebx = VG.Proof.X448.X86.mask (decide (b = 1)) ∧ Keeps workRegs s u ∧ u.mem = s.mem := by
  have hB : VG.Impl.X448.X86.BITS = 3072 := rfl
  unfold baseMask
  refine VG.Proof.X448.X86.wp_mov rfl fun u1 v1 => wp_alu (Or.inl rfl) rfl fun u2 v2 _ => ?_
  have ba : u2.ea (Impl.X448.X86.at_ .ebp VG.Impl.X448.X86.BITS) = off base (VG.Impl.X448.X86.BITS + t) := by
    change (u2.gpr .ebp + BitVec.ofNat 32 VG.Impl.X448.X86.BITS).setWidth 64 = _
    rw [v2.gpr]; change (u1.gpr .ebp + u1.gpr .esi + BitVec.ofNat 32 VG.Impl.X448.X86.BITS).setWidth 64 = _
    rw [v1.gpr, v1.other .esi (by decide), hb, Offset.add_add, Nat.add_comm t VG.Impl.X448.X86.BITS]
    exact hs.ea (by omega)
  refine wp_load8 ba (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hs.read (by omega)) fun u3 v3 => ?_
  refine VG.Proof.X448.X86.wp_mov rfl fun u4 v4 => wp_alu (Or.inr (Or.inl rfl)) rfl fun u5 v5 _ =>
    WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [v5.gpr]; change u4.gpr .ebx - u4.gpr .eax = _
    rw [v4.gpr, v4.other .eax (by decide), v3.gpr, v2.mem, v1.mem, hbit]
    exact VG.Proof.Ed448.X86.mask_byte b hb2
  · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (v5.rest (by decide)))))
  · rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]

theorem baseSwap_ok {s : State} {base : Addr} (hs : Scr s base) (hbd : BoundedEnv s.mem base)
    {t : Nat} (ht : t < 456) (hb : s.gpr .esi = BitVec.ofNat 32 t) {b : Nat} (hb2 : b < 2)
    (hbit : s.mem (off base (VG.Impl.X448.X86.BITS + t)) = BitVec.ofNat 8 b) :
    WP isa (.block baseSwap) s fun u => VG.Proof.X448.X86.Keep base s u ∧ BoundedEnv u.mem base ∧
      u.zf = some (decide (t = 0)) ∧
      VG.Proof.X448.X86.E u.mem base = opSwap 2 5 (decide (b = 1)) (opSwap 1 4 (decide (b = 1))
        (opSwap 0 3 (decide (b = 1)) (VG.Proof.X448.X86.E s.mem base))) := by
  unfold baseSwap
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.baseMask_ok hs ht hb hb2 hbit) fun u1 ⟨c1, k1, m1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  have K1 : VG.Proof.X448.X86.Keep base s u1 := ⟨k1, by rw [m1]; exact Outside2.refl _ _ _ _ _ _⟩
  rw [WP.block_append_iff]
  refine WP.mono (cswapE hs1 (m1 ▸ hbd) 0 3 (by decide) c1) fun u2 ⟨k2, b2, c2, e2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cswapE (k2.scr hs1) b2 1 4 (by decide) (c2.trans c1)) fun u3 ⟨k3, b3, c3, e3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cswapE (k3.scr (k2.scr hs1)) b3 2 5 (by decide) (c3.trans (c2.trans c1)))
    fun u4 ⟨k4, b4, _, e4⟩ => ?_
  refine VG.Proof.X448.X86.wp_cmp rfl fun u5 v5 hz => WP.block_nil ?_
  have K5 : VG.Proof.X448.X86.Keep base u4 u5 := ⟨v5.rest _, by rw [v5.mem]; exact Outside2.refl _ _ _ _ _ _⟩
  refine ⟨K1.trans (k2.trans (k3.trans (k4.trans K5))), v5.mem ▸ b4, ?_, by rw [v5.mem, e4, e3, e2, m1]⟩
  have esi : u4.gpr .esi = BitVec.ofNat 32 t := by
    rw [k4.regs.1 _ (by decide), k3.regs.1 _ (by decide), k2.regs.1 _ (by decide),
      k1.1 _ (by decide), hb]
  rw [hz, esi, show BitVec.ofNat 32 t - (0 : BitVec 32) = BitVec.ofNat 32 t from BitVec.sub_zero _,
    VG.Proof.X448.X86.ofNat_beq_zero (by omega)]

/-- The loop's invariant, after the bits above `n` of `k`. -/
structure BaseInv (base : Addr) (k : Nat) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  bounded : BoundedEnv s.mem base
  regs : Keeps (.esi :: workRegs) s₀ s
  esi : s.gpr .esi = BitVec.ofNat 32 n
  mem : Outside2 base 64 2816 ACC 512 s₀.mem s.mem
  r : pt (VG.Proof.X448.X86.E s.mem base) 0 1 2 = VG.Proof.Ed448.ladder k (456 - n)
  q : pt (VG.Proof.X448.X86.E s.mem base) 8 9 10 = Spec.Ed448.basePoint
  d : VG.Proof.X448.X86.E s.mem base 11 = Spec.Ed448.d

theorem bit_lt (k t : Nat) : (k >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem baseStep_ok {s₀ s : State} {base : Addr} {k n : Nat} (hn : n < 456)
    (hbits : ∀ t < 456, s₀.mem (off base (VG.Impl.X448.X86.BITS + t)) = BitVec.ofNat 8 ((k >>> t) &&& 1))
    (hi : VG.Proof.Ed448.X86.BaseInv base k s₀ s (n + 1)) :
    WP isa baseStep s fun t => VG.Proof.Ed448.X86.BaseInv base k s₀ t n ∧ t.zf = some (decide (n = 0)) := by
  have hs := hi.scr
  have hB : VG.Impl.X448.X86.BITS = 3072 := rfl
  have hA : ACC = 3584 := rfl
  have bitval : s.mem (off base (VG.Impl.X448.X86.BITS + n)) = BitVec.ofNat 8 ((k >>> n) &&& 1) := by
    rw [hi.mem _ (by rw [ofs_off' base (by omega)]; omega) (by rw [ofs_off' base (by omega)]; omega)]
    exact hbits n hn
  unfold baseStep
  refine WP.seq (WP.mono (decCounter_ok (by omega) hi.esi) fun s₁ ⟨b₁, g₁, m₁, rd₁, wr₁, _⟩ => ?_)
  have K₁ : Keeps [.esi] s s₁ := ⟨fun r hr => g₁ r (fun h => hr (by simp [h])), rd₁, wr₁⟩
  have hs₁ := hs.of_keeps K₁ (by decide)
  rw [VG.Impl.Ed448.X86.field, VG.Proof.Ed448.X86.doubleFields_impl]
  refine WP.seq (WP.mono (VG.Proof.X448.X86.ops_ok hs₁ (m₁ ▸ hi.bounded) VG.Proof.Ed448.X86.doubleFields) fun s₂ ⟨k₂, bb₂, e₂⟩ => ?_)
  rw [VG.Impl.Ed448.X86.field, VG.Proof.Ed448.X86.addFields_impl]
  refine WP.seq (WP.mono (VG.Proof.X448.X86.ops_ok (k₂.scr hs₁) bb₂ VG.Proof.Ed448.X86.addFields) fun s₃ ⟨k₃, bb₃, e₃⟩ => ?_)
  have hs₃ := k₃.scr (k₂.scr hs₁)
  have b₃ : s₃.gpr .esi = BitVec.ofNat 32 n := by
    rw [k₃.regs.1 _ (by decide), k₂.regs.1 _ (by decide), b₁]
  have bit₃ : s₃.mem (off base (VG.Impl.X448.X86.BITS + n)) = BitVec.ofNat 8 ((k >>> n) &&& 1) := by
    rw [(k₂.trans k₃).mem _ (by rw [ofs_off' base (by omega)]; omega)
      (by rw [ofs_off' base (by omega)]; omega), m₁, bitval]
  refine WP.mono (VG.Proof.Ed448.X86.baseSwap_ok hs₃ bb₃ (by omega) b₃ (VG.Proof.Ed448.X86.bit_lt k n) bit₃) fun t ⟨k₄, bb₄, z₄, e₄⟩ => ?_
  have core := k₂.trans (k₃.trans k₄)
  have ee : VG.Proof.X448.X86.E t.mem base = VG.Proof.Ed448.X86.baseEnv (decide ((k >>> n) &&& 1 = 1)) (VG.Proof.X448.X86.E s.mem base) := by
    rw [e₄, e₃, e₂, m₁]; rfl
  refine ⟨⟨core.scr hs₁, bb₄, ?_, ?_, ?_, ?_, ?_, ?_⟩, z₄⟩
  · refine hi.regs.trans ⟨fun r hr => ?_, core.regs.2.1.trans rd₁, core.regs.2.2.trans wr₁⟩
    rw [core.regs.1 r (fun h => hr (List.mem_cons_of_mem _ h)), g₁ r (fun h => hr (by simp [h]))]
  · rw [core.regs.1 _ (by decide), b₁]
  · refine hi.mem.trans ?_
    intro p hp hq
    rw [core.mem p hp hq, m₁]
  · rw [ee, VG.Proof.Ed448.X86.baseEnv_r _ _ hi.q hi.d, hi.r, ladder_bit k hn]; rfl
  · rw [ee, VG.Proof.Ed448.X86.baseEnv_q]; exact hi.q
  · rw [ee, VG.Proof.Ed448.X86.baseEnv_d]; exact hi.d

theorem baseLoop_ok {s₀ s : State} {base : Addr} {k : Nat}
    (hbits : ∀ t < 456, s₀.mem (off base (VG.Impl.X448.X86.BITS + t)) = BitVec.ofNat 8 ((k >>> t) &&& 1))
    (hi : ∀ s', s'.gpr .esi = BitVec.ofNat 32 456 → (∀ r, r ≠ .esi → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → VG.Proof.Ed448.X86.BaseInv base k s₀ s' 456) :
    WP isa baseLoop s fun s' => VG.Proof.Ed448.X86.BaseInv base k s₀ s' 0 := by
  unfold baseLoop
  refine WP.seq (WP.mono (setCounter_ok s 456 (by decide)) fun s' ⟨h1, h2, h3, h4, h5⟩ => ?_)
  refine WP.loop (M := isa) (body := baseStep) (c := .ne) (Q := fun s' => VG.Proof.Ed448.X86.BaseInv base k s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 456 ∧ VG.Proof.Ed448.X86.BaseInv base k s₀ s m) ?_ 456 s'
    ⟨by decide, by decide, hi s' h1 h2 h3 h4 h5⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (VG.Proof.Ed448.X86.baseStep_ok (by omega) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, hi'⟩

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.ScalarMain`. -/
section

/-!
# Ed448 scalar reduction on x86 (32-bit): the whole function

`vg_ed448_scalar_reduce(out = [esp + 4], wide = [esp + 8], scratch = [esp + 12])`
against a local contract (`scalarReduceLocal`: the arguments only read), the
ABI included: every write is in the working space but the result's, so the
arguments are read unchanged, the callee-saved registers restored from the
working space, and the return address kept.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.Radix16 VG.Proof.X448.X86 VG.Proof.Ed448.Limbs16
open VG.Impl.Ed448.X86 (W TF RA SK SS SR scalarReduce)
open VG.Spec.Ed448 (L bytesAt decodeLE encodeLE)

/-- `vg_ed448_scalar_reduce(out, wide, scratch)`, whose arguments are on the
stack (cdecl). -/
def scalarReduceLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let wide : Region := ⟨(arg s 1).setWidth 64, 114⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [wide, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      wide.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 114 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s t := bytesAt t.mem ((arg s 0).setWidth 64) 57 =
    Spec.Ed448.scalarReduce (bytesAt s.mem ((arg s 1).setWidth 64) 114)
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2

/-- The precondition, by name. -/
structure ReducePre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 1).setWidth 64, 114⟩, ⟨argAddr s 0, 12⟩]
  wr : s.wr = [⟨(arg s 0).setWidth 64, 57⟩, scR (arg s 2)]
  out_sc : (⟨(arg s 0).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 2))
  wide_sc : (⟨(arg s 1).setWidth 64, 114⟩ : Region).Disjoint (scR (arg s 2))
  args_out : (⟨argAddr s 0, 12⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  args_sc : (⟨argAddr s 0, 12⟩ : Region).Disjoint (scR (arg s 2))
  ret_out : (VG.Proof.X448.X86.retR s).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  ret_sc : (VG.Proof.X448.X86.retR s).Disjoint (scR (arg s 2))
  out_fit : (arg s 0).toNat + 57 ≤ 2 ^ 32
  wide_fit : (arg s 1).toNat + 114 ≤ 2 ^ 32
  sc_fit : (arg s 2).toNat + 8192 ≤ 2 ^ 32
  sp_fit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32

theorem ReducePre.of {s : State} (h : scalarReduceLocal.pre s) : VG.Proof.Ed448.X86.ReducePre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem ReducePre.args {s : State} (h : VG.Proof.Ed448.X86.ReducePre s) : VG.Proof.Ed448.X86.Args s 3 2 :=
  ⟨by rw [h.rd]; simp, by have := h.sp_fit; omega, by decide, by rw [h.wr]; simp, h.sc_fit,
    h.args_sc, h.ret_sc⟩

theorem RA_buf : VG.Proof.Ed448.X86.Buf RA := ⟨by decide, by decide⟩

/-- The return address and the callee-saved registers, across code that
writes only the working space and the output. -/
theorem abi_of {s₀ t : State} {sc : Nat} {base : Addr} (hbase : (arg s₀ sc).setWidth 64 = base)
    (hret_sc : (VG.Proof.X448.X86.retR s₀).Disjoint (scR (arg s₀ sc)))
    (hret_out : (VG.Proof.X448.X86.retR s₀).Disjoint ⟨(arg s₀ 0).setWidth 64, 57⟩)
    (hm : Outside base 0 8192 s₀.mem t.mem) {m : Mem}
    (ho : Outside ((arg s₀ 0).setWidth 64) 0 57 t.mem m) :
    m.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32 := by
  have frame : Frame [scR (arg s₀ sc), ⟨(arg s₀ 0).setWidth 64, 57⟩] s₀.mem m := by
    rw [← hbase] at hm
    exact (hm.frame.mono (by simp)).trans (ho.frame.mono (by simp))
  have ret : (VG.Proof.X448.X86.retR s₀).Contains ((s₀.gpr .esp).setWidth 64) 4 := by
    simpa only [BitVec.add_zero] using
      Offset.contains_base ((s₀.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide) (by decide)
  exact frame.readW ret
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl; exact hret_sc; exact hret_out) (by decide)

theorem scalarReduce_correct {s₀ : State} (h : VG.Proof.Ed448.X86.ReducePre s₀) :
    WP isa scalarReduce s₀ fun t => abiPreserved s₀ t ∧ scalarReduceLocal.post s₀ t := by
  have hA := h.args
  obtain ⟨base, hbase⟩ : ∃ b, (arg s₀ 2).setWidth 64 = b := ⟨_, rfl⟩
  have hR := VG.Proof.Ed448.X86.RA_buf
  unfold scalarReduce
  refine WP.seq (WP.block_append (WP.mono (VG.Proof.Ed448.X86.save_ok hA) fun s1 ⟨hs1, sv1, o1, k1⟩ => ?_))
  rw [hbase] at hs1 sv1 o1
  have o1' : Outside base 0 8192 s₀.mem s1.mem := o1.mono (by omega) (by omega)
  refine hA.load (i := 1) (k1.1 _ (by decide)) k1.2.1 k1.2.2 (hbase ▸ o1') (by decide)
    fun s2 u2 => WP.block_nil ?_
  have hs2 := hs1.of_upd u2 (by decide)
  have hin : VG.Proof.Ed448.X86.Input s2 base (arg s₀ 1) 114 := Input.of_region h.wide_fit
    (by rw [u2.rd, u2.wr, k1.2.1, h.rd]; simp) (hbase ▸ h.wide_sc)
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.reduce114_ok hR hs2 u2.gpr hin) fun s3 ⟨k3, l3, v3⟩ => ?_)
  have hs3 := hs2.of_keeps k3.regs (by decide)
  have k03 : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s₀ s3 :=
    (k1.mono (by decide)).trans ((u2.rest (by decide)).trans (k3.regs.mono (by decide)))
  have m3 : Outside base 0 8192 s₀.mem s3.mem :=
    o1'.trans (by rw [← u2.mem]; exact k3.whole (by decide))
  have sv3 : VG.Proof.X448.X86.Saved base s₀.gpr s3.mem := (u2.mem ▸ sv1).outside2 k3.mem (by decide) (by decide)
  refine WP.mono (VG.Proof.Ed448.X86.finish_ok hA (by decide) (k03.1 _ (by decide)) k03.2.1 k03.2.2 hbase m3 hs3
    (by decide) l3 (by rw [h.wr]; simp) h.out_fit (fun j hj => VG.Proof.Ed448.X86.far_out (hbase ▸ h.out_sc) hj)
    sv3) fun t ⟨tr, kt, ot, bt⟩ => ⟨⟨?_, VG.Proof.Ed448.X86.abi_of hbase h.ret_sc h.ret_out m3 ot⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact tr (.ebx, 0) (by decide)
    · exact tr (.esi, 4) (by decide)
    · exact tr (.edi, 8) (by decide)
    · exact tr (.ebp, 12) (by decide)
    · rw [kt.1 _ (by decide), k03.1 _ (by decide)]
  · change bytesAt t.mem _ 57 = encodeLE 57 _
    rw [bt, v3, u2.mem, hin.bytes o1']

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.BaseMain`. -/
section

/-!
# Ed448 base-point multiplication on x86 (32-bit): the whole function

`vg_ed448_scalar_base(out = [esp + 4], scalar = [esp + 8], scratch = [esp + 12])`
against a local contract (`scalarBaseLocal`, `BaseLocal.lean`: the arguments
only read): it
computes the encoding of the ladder over the scalar's bits
(`scalarBase_ladder`): the entry, the scalar's bits, the loop (`R` ends as
`ladder k 456`), the inversion of `Z` and the encoding. Every write is in the
working space but the result's, so the arguments and the scalar are read
unchanged; the callee-saved registers are restored from the working space,
and the return address is kept.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.Ed448 (ladder pt)
open VG.Impl.Ed448.X86 (scalarBase initSlots baseBits initVal)
open VG.Impl.X448.X86 (slot BITS ACC at_)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-- The precondition, by name. -/
structure BasePre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 1).setWidth 64, 57⟩, ⟨argAddr s 0, 12⟩]
  wr : s.wr = [⟨(arg s 0).setWidth 64, 57⟩, scR (arg s 2)]
  out_sc : (⟨(arg s 0).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 2))
  scalar_sc : (⟨(arg s 1).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 2))
  args_out : (⟨argAddr s 0, 12⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  args_sc : (⟨argAddr s 0, 12⟩ : Region).Disjoint (scR (arg s 2))
  ret_out : (VG.Proof.X448.X86.retR s).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  ret_sc : (VG.Proof.X448.X86.retR s).Disjoint (scR (arg s 2))
  out_fit : (arg s 0).toNat + 57 ≤ 2 ^ 32
  scalar_fit : (arg s 1).toNat + 57 ≤ 2 ^ 32
  sc_fit : (arg s 2).toNat + 8192 ≤ 2 ^ 32
  sp_fit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32

theorem BasePre.of {s : State} (h : scalarBaseLocal.pre s) : VG.Proof.Ed448.X86.BasePre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem BasePre.args {s : State} (h : VG.Proof.Ed448.X86.BasePre s) : VG.Proof.Ed448.X86.Args s 3 2 :=
  ⟨by rw [h.rd]; simp, by have := h.sp_fit; omega, by decide, by rw [h.wr]; simp, h.sc_fit,
    h.args_sc, h.ret_sc⟩

theorem initE (e : Env) (he : ∀ i : Index, e i = Proof.X448.toFe (initVal i.val)) :
    pt e 0 1 2 = Spec.Ed448.identity ∧ pt e 8 9 10 = Spec.Ed448.basePoint ∧ e 11 = Spec.Ed448.d := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [pt, he]
    rw [show ((0 : Index) : Nat) = 0 from rfl, show ((1 : Index) : Nat) = 1 from rfl,
      show ((2 : Index) : Nat) = 2 from rfl, show initVal 0 = Spec.Ed448.identity.X.val from rfl,
      show initVal 1 = Spec.Ed448.identity.Y.val from rfl,
      show initVal 2 = Spec.Ed448.identity.Z.val from rfl, Proof.X448.toFe_self,
      Proof.X448.toFe_self, Proof.X448.toFe_self]
  · simp only [pt, he]
    rw [show ((8 : Index) : Nat) = 8 from rfl, show ((9 : Index) : Nat) = 9 from rfl,
      show ((10 : Index) : Nat) = 10 from rfl, show initVal 8 = Spec.Ed448.basePoint.X.val from rfl,
      show initVal 9 = Spec.Ed448.basePoint.Y.val from rfl,
      show initVal 10 = Spec.Ed448.basePoint.Z.val from rfl, Proof.X448.toFe_self,
      Proof.X448.toFe_self, Proof.X448.toFe_self]
  · rw [he]; exact Proof.X448.toFe_self _

theorem scalarBase_ladder {s₀ : State} (h : VG.Proof.Ed448.X86.BasePre s₀) :
    WP isa scalarBase s₀ fun t => abiPreserved s₀ t ∧
      bytesAt t.mem ((arg s₀ 0).setWidth 64) 57 =
        Spec.Ed448.encodePoint (ladder (decodeLE (bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 57)) 456) := by
  have hA := h.args
  obtain ⟨base, hbase⟩ : ∃ b, (arg s₀ 2).setWidth 64 = b := ⟨_, rfl⟩
  have hin : VG.Proof.Ed448.X86.Input s₀ base (arg s₀ 1) 57 :=
    Input.of_region h.scalar_fit (by rw [h.rd]; simp) (hbase ▸ h.scalar_sc)
  unfold scalarBase
  -- The entry: the registers saved, the slots, the scalar's bits.
  refine WP.seq (WP.block_append (WP.block_append (WP.mono (VG.Proof.Ed448.X86.save_ok hA) fun s₁ ⟨hs₁, sv₁, o₁, k₁⟩ => ?_)))
  rw [hbase] at hs₁ sv₁ o₁
  refine WP.mono (VG.Proof.Ed448.X86.initSlots_ok hs₁) fun s₂ ⟨l₂, o₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have k02 : Keeps [.eax, .ebx, .ebp, .edi] s₀ s₂ := (k₁.mono (by decide)).trans (k₂.mono (by decide))
  have o02 : Outside base 0 8192 s₀.mem s₂.mem :=
    (o₁.mono (by omega) (by omega)).trans (o₂.mono (by omega) (by omega))
  rw [baseBits]
  refine hA.load (i := 1) (k02.1 _ (by decide)) k02.2.1 k02.2.2 (hbase ▸ o02) (by decide)
    fun s₃ u₃ => ?_
  have hs₃ := hs₂.of_upd u₃ (by decide)
  refine WP.mono (VG.Proof.Ed448.X86.baseBytes_ok (k := (arg s₀ 1).setWidth 64) hs₃ (by rw [u₃.gpr]) (by rw [u₃.gpr]; exact hin.fit)
    (by rw [u₃.rd, u₃.wr, k02.2.1, k02.2.2]; exact hin.read) hin.far) fun s₄ ⟨k₄, o₄, bits₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have mem34 : bytesAt s₃.mem ((arg s₀ 1).setWidth 64) 57 = bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 57 := by
    rw [u₃.mem]; exact hin.bytes o02
  rw [mem34] at bits₄
  have e₄ : ∀ i : Index, E s₄.mem base i = Proof.X448.toFe (initVal i.val) := by
    intro i
    rw [← VG.Proof.Ed448.X86.initSlots_E l₂ i]
    simp only [E, VG.Proof.X448.X86.F]
    rw [o₄.fe (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega), u₃.mem]
  have b₄ : BoundedEnv s₄.mem base := by
    intro i j hj
    rw [o₄.limbs (d := slot i.val) (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega) hj, u₃.mem]
    exact VG.Proof.Ed448.X86.initSlots_bounded l₂ i j hj
  obtain ⟨er, eq, ed⟩ := VG.Proof.Ed448.X86.initE _ e₄
  -- The loop.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.baseLoop_ok (s₀ := s₄) (s := s₄) bits₄ (fun s' h1 h2 h3 h4 h5 => ?_))
    fun y hy => ?_)
  · have k' : Keeps (.esi :: workRegs) s₄ s' :=
      ⟨fun r hr => h2 r (fun e => hr (by subst r; exact List.mem_cons_self)), h4, h5⟩
    exact ⟨hs₄.of_keeps k' (by decide), h3 ▸ b₄, k', h1, h3 ▸ Outside2.refl _ _ _ _ _ _,
      by rw [h3, er]; rfl, by rw [h3]; exact eq, by rw [h3]; exact ed⟩
  -- The encoding.
  have k0y : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s₀ y :=
    (k02.mono (by decide)).trans ((u₃.rest (by decide)).trans ((k₄.mono (by decide)).trans
      (hy.regs.mono (by decide))))
  have o4w : Outside base 0 8192 s₃.mem s₄.mem := o₄.mono (by omega) (by simp only [BITS]; omega)
  rw [u₃.mem] at o4w
  have m0y : Outside base 0 8192 s₀.mem y.mem :=
    (o02.trans o4w).trans (hy.mem.whole (by decide) (by decide))
  have svy : VG.Proof.X448.X86.Saved base s₀.gpr y.mem :=
    ((sv₁.outside o₂ (by decide)).outside (u₃.mem ▸ o₄) (by decide)).outside2 hy.mem (by decide)
      (by decide)
  refine WP.mono (VG.Proof.Ed448.X86.baseEncode_ok hA (by decide) (k0y.1 _ (by decide)) k0y.2.1 k0y.2.2 hbase m0y hy.scr
    hy.bounded (by rw [h.wr]; simp) h.out_fit (hbase ▸ h.out_sc) svy) fun t ⟨bt, rt, kt, ft⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rt (.ebx, 0) (by decide)
    · exact rt (.esi, 4) (by decide)
    · exact rt (.edi, 8) (by decide)
    · exact rt (.ebp, 12) (by decide)
    · rw [kt.1 _ (by decide), k0y.1 _ (by decide)]
  · have frame : Frame [⟨base, 8192⟩, ⟨(arg s₀ 0).setWidth 64, 57⟩] s₀.mem t.mem :=
      ((Outside.frame m0y).mono (by simp)).trans ft
    have ret : (VG.Proof.X448.X86.retR s₀).Contains ((s₀.gpr .esp).setWidth 64) 4 := by
      simpa only [BitVec.add_zero] using
        Offset.contains_base ((s₀.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide)
          (by decide)
    exact frame.readW ret
      (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hbase ▸ h.ret_sc
          · exact h.ret_out) (by decide)
  · rw [bt]
    exact congrArg Spec.Ed448.encodePoint hy.r

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.ScalarLit`. -/
section

/-!
# Ed448 scalar arithmetic on x86 (32-bit): the code as literals

The kernel checks each literal once; the taint and instruction checks reuse it.
-/

namespace VG

materialize_code Impl.Ed448.X86.scalarReduce
materialize_code Impl.Ed448.X86.scalarMulAdd

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.ScalarMulAdd`. -/
section

/-!
# Ed448 scalar multiply-add on x86 (32-bit): the steps

The inputs reduced (`reduceArg_ok`), the product of two with X448's rows
(`product_ok`), its limbs reduced (`reduceProduct_ok`), and the sum with the
third (`addPass_ok`), which `reduceT` reduces once more.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.Radix16 VG.Proof.X448.X86 VG.Proof.Ed448.Limbs16
open VG.Impl.Ed448.X86 (W TF RA SK SS SR reduceArg product reduceProduct addSrc addPass)
open VG.Spec.Ed448 (L bytesAt decodeLE encodeLE)

theorem SK_eq : SK = 320 := rfl
theorem SS_eq : SS = 448 := rfl
theorem SR_eq : SR = 576 := rfl
theorem RA_eq : RA = 192 := rfl

/-! ## The inputs -/

/-- `reduceArg d o`: the remainder at `o` of the 57 bytes at the argument
`i` (at `[esp + 4 + 4 i]`). -/
theorem reduceArg_ok {s₀ s : State} {n sc : Nat} (hA : VG.Proof.Ed448.X86.Args s₀ n sc) {base : Addr}
    (hbase : (arg s₀ sc).setWidth 64 = base) (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hm : Outside base 0 8192 s₀.mem s.mem) (hs : Scr s base)
    {i : Nat} (hi : i < n) {o : Nat} (ho : VG.Proof.Ed448.X86.Buf o) (hin : VG.Proof.Ed448.X86.Input s₀ base (arg s₀ i) 57) :
    WP isa (reduceArg (4 + 4 * i) o) s fun t =>
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ Outside2 base W 160 o 112 s.mem t.mem ∧
      Bounded t.mem base o ∧
      fe t.mem base o = decodeLE (bytesAt s₀.mem ((arg s₀ i).setWidth 64) 57) % L := by
  unfold reduceArg
  refine WP.seq (hA.load hsp hr hwr (hbase ▸ hm) hi fun u hu => WP.block_nil ?_)
  have hinu : VG.Proof.Ed448.X86.Input u base (arg s₀ i) 57 :=
    ⟨hin.fit, by rw [hu.rd, hu.wr, hr, hwr]; exact hin.read, hin.far⟩
  refine WP.mono (VG.Proof.Ed448.X86.reduce57_ok ho (hs.of_upd hu (by decide)) hu.gpr hinu) fun t ⟨kt, lt, vt⟩ =>
    ⟨(hu.rest (by decide)).trans (kt.regs.mono (by decide)), by rw [← hu.mem]; exact kt.mem, lt, ?_⟩
  rw [vt, hu.mem, hin.bytes hm]

/-! ## The product -/

theorem product_ok {s : State} {base : Addr} (hs : Scr s base) (hk : Bounded s.mem base SK)
    (hl : Bounded s.mem base SS) :
    WP isa product s fun t => Scr t base ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
      Outside base Impl.X448.X86.ACC 224 s.mem t.mem ∧
      (∀ j < 56, limbs t.mem base Impl.X448.X86.ACC j < VG.Proof.X448.Radix16.radix) ∧
      VG.Proof.X448.Radix16.valN (limbs t.mem base Impl.X448.X86.ACC) 56 = fe s.mem base SK * fe s.mem base SS := by
  unfold product
  refine WP.seq (WP.mono (mulPre_ok hs SK SS) fun u hu => ?_)
  refine WP.mono (mulLoop_ok (by decide) (by decide) hk hl hu) fun t ht =>
    ⟨ht.scr, ht.regs, ht.mem, ht.lt, ht.val⟩

theorem reduceProduct_ok {s : State} {base : Addr} (hs : Scr s base)
    (hacc : ∀ j < 56, limbs s.mem base Impl.X448.X86.ACC j < VG.Proof.X448.Radix16.radix) :
    WP isa reduceProduct s fun t => VG.Proof.Ed448.X86.LoopKeep base RA s t ∧ Bounded t.mem base RA ∧
      fe t.mem base RA = VG.Proof.X448.Radix16.valN (limbs s.mem base Impl.X448.X86.ACC) 56 % L := by
  have hA := VG.Proof.Ed448.X86.ACC_eq
  have hR := VG.Proof.Ed448.X86.RA_eq
  unfold reduceProduct
  have hinit : WP isa (.block (Impl.Ed448.X86.zeroR RA ++ ([.mov .ebp (.imm 224)] : List Instr))) s
      fun v => VG.Proof.Ed448.X86.LoopKeep base RA s v ∧ v.gpr .ebp = BitVec.ofNat 32 (4 * 56) ∧
        Bounded v.mem base RA ∧ fe v.mem base RA = 0 := by
    rw [WP.block_append_iff]
    exact WP.mono (VG.Proof.Ed448.X86.zeroR_ok (o := RA) (by decide) hs) fun u ⟨ku, fu, zu⟩ =>
      wp_mov rfl fun v hv => WP.block_nil
        ⟨⟨(ku.mono (by decide)).trans (hv.rest (by decide)), by
          rw [hv.mem]; exact fun p _ h2 => fu p h2⟩,
          hv.gpr, by rw [hv.mem]; exact VG.Proof.Ed448.X86.Bounded_zero zu, by rw [hv.mem]; exact VG.Proof.Ed448.X86.fe_zero zu⟩
  refine WP.seq (WP.mono hinit fun v ⟨kv, cv, lv, vv⟩ => ?_)
  have la : ∀ j < 56, limbs v.mem base Impl.X448.X86.ACC j = limbs s.mem base Impl.X448.X86.ACC j :=
    fun j hj => congrArg BitVec.toNat (kv.mem.word (Or.inr (by simp only [W]; omega))
      (Or.inr (by omega)) (by omega))
  refine WP.mono (VG.Proof.Ed448.X86.limbLoop_ok (hs.of_keeps kv.regs (by decide))
    (fun j hj => by rw [la j hj]; exact hacc j hj) cv lv vv) fun t ⟨kt, lt, vt⟩ =>
    ⟨kv.trans kt, lt, by rw [vt, VG.Proof.X448.Radix16.valN_congr la]⟩

/-! ## The sum -/

theorem addPass_ok {s : State} {base : Addr} (hs : Scr s base)
    (ha : Bounded s.mem base RA) (hr : Bounded s.mem base SR)
    (hva : fe s.mem base RA < L) (hvr : fe s.mem base SR < L) :
    WP isa (.block addPass) s fun t => Keeps [.eax, .ebx, .edx] s t ∧
      Outside base TF 112 s.mem t.mem ∧ Bounded t.mem base TF ∧
      fe t.mem base TF = fe s.mem base RA + fe s.mem base SR := by
  have hT := VG.Proof.Ed448.X86.TF_eq
  have hR := VG.Proof.Ed448.X86.RA_eq
  have hS := VG.Proof.Ed448.X86.SR_eq
  unfold addPass
  rw [WP.block_append_iff]
  refine WP.mono (zeroCarry_ok s) fun s1 ⟨e1, m1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  refine WP.mono (carryPass_ok (rb := .edi) (o := TF) (d := TF) (s0 := s1)
    (c := fun k => limbs s.mem base RA k + limbs s.mem base SR k) (by decide) (by omega)
    (fun k hk => hs1.ea (by omega)) (fun k hk => hs1.write (by omega)) (by rw [e1]; rfl)
    (fun k hk => by have := ha k hk; have := hr k hk; simp only [VG.Proof.X448.Radix16.radix] at *; omega) ?_)
    fun t ht => ?_
  · intro k hk s' hp
    have hs' := hs1.of_keeps hp.regs (by decide)
    have hm := hp.mem
    rw [m1] at hm
    have e1 : limbs s'.mem base RA k = limbs s.mem base RA k :=
      hm.limbs (Or.inr (by omega)) (by omega) hk
    have e2 : limbs s'.mem base SR k = limbs s.mem base SR k :=
      hm.limbs (Or.inr (by omega)) (by omega) hk
    unfold addSrc
    refine load_ok hs' (by omega) fun v1 w1 => ?_
    refine wp_alu (Or.inl rfl) (VG.Proof.Ed448.X86.readSc (hs'.of_upd w1 (by decide)) (by omega)) fun v2 w2 _ =>
      WP.block_nil ⟨?_, (w1.rest (by decide)).trans (w2.rest (by decide)), by rw [w2.mem, w1.mem]⟩
    have x1 : (v1.gpr .eax).toNat = limbs s.mem base RA k := by rw [w1.gpr]; exact e1
    have x2 : (word v1.mem base (SR + 4 * k)).toNat = limbs s.mem base SR k := by
      rw [w1.mem]; exact e2
    rw [w2.gpr]
    change (v1.gpr .eax + word v1.mem base (SR + 4 * k)).toNat = _
    rw [VG.Proof.Ed448.X86.toNat_add_lt (by rw [x1, x2]; have := ha k hk; have := hr k hk; simp only [VG.Proof.X448.Radix16.radix] at *; omega),
      x1, x2]
  · generalize hcf : (fun k => limbs s.mem base RA k + limbs s.mem base SR k) = c at ht
    have hcv : VG.Proof.X448.Radix16.valN c 28 = fe s.mem base RA + fe s.mem base SR := by rw [← hcf, VG.Proof.X448.Radix16.valN_add]
    have hlt : VG.Proof.X448.Radix16.valN c 28 < VG.Proof.X448.Radix16.radix ^ 28 := by
      have := two_L_le
      rw [hcv]; omega
    refine ⟨(k1.mono (by decide)).trans ht.regs, by rw [← m1]; exact ht.mem,
      fun k hk => by rw [ht.outs k hk]; exact VG.Proof.X448.Radix16.digit_lt _ _, ?_⟩
    show VG.Proof.X448.Radix16.valN (limbs t.mem base TF) 28 = _
    rw [VG.Proof.X448.Radix16.valN_congr ht.outs, digits_val hlt, hcv]

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.ScalarMulAddMain`. -/
section

/-!
# Ed448 scalar multiply-add on x86 (32-bit): the whole function

`vg_ed448_scalar_mul_add(out = [esp + 4], r = [esp + 8], k = [esp + 12],
s = [esp + 16], scratch = [esp + 20])` against a local contract
(`scalarMulAddLocal`: the arguments only read), the ABI included.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.Radix16 VG.Proof.X448.X86 VG.Proof.Ed448.Limbs16
open VG.Impl.Ed448.X86 (W TF RA SK SS SR scalarMulAdd inputs reduceT finish)
open VG.Spec.Ed448 (L bytesAt decodeLE encodeLE)

/-- `vg_ed448_scalar_mul_add(out, r, k, s, scratch)`, whose arguments are on
the stack (cdecl). -/
def scalarMulAddLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let r : Region := ⟨(arg s 1).setWidth 64, 57⟩
    let k : Region := ⟨(arg s 2).setWidth 64, 57⟩
    let a : Region := ⟨(arg s 3).setWidth 64, 57⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [r, k, a, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      r.Disjoint scratch ∧ k.Disjoint scratch ∧ a.Disjoint scratch ∧ args.Disjoint out ∧
      args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s t := bytesAt t.mem ((arg s 0).setWidth 64) 57 =
    Spec.Ed448.scalarMulAdd (bytesAt s.mem ((arg s 1).setWidth 64) 57)
      (bytesAt s.mem ((arg s 2).setWidth 64) 57) (bytesAt s.mem ((arg s 3).setWidth 64) 57)
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2 ∧
    arg s 3 = arg t 3 ∧ arg s 4 = arg t 4

/-- The precondition, by name. -/
structure MulAddPre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 1).setWidth 64, 57⟩, ⟨(arg s 2).setWidth 64, 57⟩,
    ⟨(arg s 3).setWidth 64, 57⟩, ⟨argAddr s 0, 20⟩]
  wr : s.wr = [⟨(arg s 0).setWidth 64, 57⟩, scR (arg s 4)]
  out_sc : (⟨(arg s 0).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 4))
  r_sc : (⟨(arg s 1).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 4))
  k_sc : (⟨(arg s 2).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 4))
  a_sc : (⟨(arg s 3).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 4))
  args_out : (⟨argAddr s 0, 20⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  args_sc : (⟨argAddr s 0, 20⟩ : Region).Disjoint (scR (arg s 4))
  ret_out : (VG.Proof.X448.X86.retR s).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  ret_sc : (VG.Proof.X448.X86.retR s).Disjoint (scR (arg s 4))
  out_fit : (arg s 0).toNat + 57 ≤ 2 ^ 32
  r_fit : (arg s 1).toNat + 57 ≤ 2 ^ 32
  k_fit : (arg s 2).toNat + 57 ≤ 2 ^ 32
  a_fit : (arg s 3).toNat + 57 ≤ 2 ^ 32
  sc_fit : (arg s 4).toNat + 8192 ≤ 2 ^ 32
  sp_fit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32

theorem MulAddPre.of {s : State} (h : scalarMulAddLocal.pre s) : VG.Proof.Ed448.X86.MulAddPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

theorem MulAddPre.args {s : State} (h : VG.Proof.Ed448.X86.MulAddPre s) : VG.Proof.Ed448.X86.Args s 5 4 :=
  ⟨by rw [h.rd]; simp, by have := h.sp_fit; omega, by decide, by rw [h.wr]; simp, h.sc_fit,
    h.args_sc, h.ret_sc⟩

theorem MulAddPre.input {s : State} (h : VG.Proof.Ed448.X86.MulAddPre s) {base : Addr} (hbase : (arg s 4).setWidth 64 = base)
    {i : Nat} (h1 : 1 ≤ i) (h4 : i < 4) : VG.Proof.Ed448.X86.Input s base (arg s i) 57 := by
  subst hbase
  rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
  · exact Input.of_region h.r_fit (by rw [h.rd]; simp) h.r_sc
  · exact Input.of_region h.k_fit (by rw [h.rd]; simp) h.k_sc
  · exact Input.of_region h.a_fit (by rw [h.rd]; simp) h.a_sc

theorem mulAdd_mod (r k s : Nat) : ((k % L * (s % L)) % L + r % L) % L = (r + k * s) % L := by
  rw [← Nat.mul_mod, ← Nat.add_mod, Nat.add_comm]

/-- What a step of multiply-add changes: the registers but `esp`, and the
working space above the saved registers. -/
structure MKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t
  mem : Outside base 16 8176 s.mem t.mem

theorem MKeep.trans {base : Addr} {s t u : State} (h : VG.Proof.Ed448.X86.MKeep base s t) (h' : VG.Proof.Ed448.X86.MKeep base t u) :
    VG.Proof.Ed448.X86.MKeep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem MKeep.whole {base : Addr} {s t : State} (h : VG.Proof.Ed448.X86.MKeep base s t) : Outside base 0 8192 s.mem t.mem :=
  h.mem.mono (by omega) (by omega)

theorem MKeep.of2 {base : Addr} {s t : State} {rs : List Reg} (hr : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r ∈ [Reg.eax, .ebx, .ecx, .edx, .ebp, .esi])
    {x nx y ny : Nat} (hm : Outside2 base x nx y ny s.mem t.mem) (hx : 16 ≤ x) (hy : 16 ≤ y)
    (hx' : x + nx ≤ 8192) (hy' : y + ny ≤ 8192) : VG.Proof.Ed448.X86.MKeep base s t :=
  ⟨hr.mono hrs, fun p hp => hm p (by omega) (by omega)⟩

theorem MKeep.of1 {base : Addr} {s t : State} {rs : List Reg} (hr : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r ∈ [Reg.eax, .ebx, .ecx, .edx, .ebp, .esi])
    {x nx : Nat} (hm : Outside base x nx s.mem t.mem) (hx : 16 ≤ x) (hx' : x + nx ≤ 8192) :
    VG.Proof.Ed448.X86.MKeep base s t :=
  ⟨hr.mono hrs, fun p hp => hm p (by omega)⟩

theorem inputs_ok {s₀ s : State} (h : VG.Proof.Ed448.X86.MulAddPre s₀) {base : Addr} (hbase : (arg s₀ 4).setWidth 64 = base)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hm : Outside base 0 8192 s₀.mem s.mem) (hs : Scr s base) :
    WP isa inputs s fun t => VG.Proof.Ed448.X86.MKeep base s t ∧
      Bounded t.mem base SK ∧ Bounded t.mem base SS ∧ Bounded t.mem base SR ∧
      fe t.mem base SK = decodeLE (bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 57) % L ∧
      fe t.mem base SS = decodeLE (bytesAt s₀.mem ((arg s₀ 3).setWidth 64) 57) % L ∧
      fe t.mem base SR = decodeLE (bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 57) % L := by
  have hA := h.args
  have hK := VG.Proof.Ed448.X86.SK_eq
  have hS := VG.Proof.Ed448.X86.SS_eq
  have hR := VG.Proof.Ed448.X86.SR_eq
  unfold inputs
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.reduceArg_ok (i := 2) hA hbase hsp hr hwr hm hs (by decide)
    (o := SK) ⟨by decide, by decide⟩ (h.input hbase (by decide) (by decide)))
    fun u ⟨ku, mu, lu, vu⟩ => ?_)
  have mu' : VG.Proof.Ed448.X86.MKeep base s u := MKeep.of2 ku (by decide) mu (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.reduceArg_ok (i := 3) hA hbase ((ku.1 _ (by decide)).trans hsp)
    (ku.2.1.trans hr) (ku.2.2.trans hwr) (hm.trans mu'.whole) (hs.of_keeps ku (by decide)) (by decide)
    (o := SS) ⟨by decide, by decide⟩ (h.input hbase (by decide) (by decide)))
    fun v ⟨kv, mv, lv, vv⟩ => ?_)
  have mv' : VG.Proof.Ed448.X86.MKeep base u v := MKeep.of2 kv (by decide) mv (by decide) (by decide) (by decide) (by decide)
  refine WP.mono (VG.Proof.Ed448.X86.reduceArg_ok (i := 1) hA hbase ((kv.1 _ (by decide)).trans ((ku.1 _ (by decide)).trans hsp))
    (kv.2.1.trans (ku.2.1.trans hr)) (kv.2.2.trans (ku.2.2.trans hwr))
    ((hm.trans mu'.whole).trans mv'.whole) ((hs.of_keeps ku (by decide)).of_keeps kv (by decide))
    (by decide) (o := SR) ⟨by decide, by decide⟩ (h.input hbase (by decide) (by decide)))
    fun t ⟨kt, mt, lt, vt⟩ => ?_
  have mt' : VG.Proof.Ed448.X86.MKeep base v t := MKeep.of2 kt (by decide) mt (by decide) (by decide) (by decide) (by decide)
  have eK : ∀ j < 28, limbs t.mem base SK j = limbs u.mem base SK j := fun j hj => by
    show (word t.mem base (SK + 4 * j)).toNat = (word u.mem base (SK + 4 * j)).toNat
    rw [congrArg BitVec.toNat (mt.word (d := SK + 4 * j) (Or.inr (by simp only [W]; omega))
      (Or.inl (by omega)) (by omega)),
      congrArg BitVec.toNat (mv.word (d := SK + 4 * j) (Or.inr (by simp only [W]; omega))
      (Or.inl (by omega)) (by omega))]
  have eS : ∀ j < 28, limbs t.mem base SS j = limbs v.mem base SS j := fun j hj =>
    congrArg BitVec.toNat (mt.word (d := SS + 4 * j) (Or.inr (by simp only [W]; omega))
      (Or.inl (by omega)) (by omega))
  exact ⟨mu'.trans (mv'.trans mt'), fun j hj => by rw [eK j hj]; exact lu j hj,
    fun j hj => by rw [eS j hj]; exact lv j hj, lt, by rw [← vu]; exact VG.Proof.X448.Radix16.valN_congr eK,
    by rw [← vv]; exact VG.Proof.X448.Radix16.valN_congr eS, vt⟩

theorem scalarMulAdd_correct {s₀ : State} (h : VG.Proof.Ed448.X86.MulAddPre s₀) :
    WP isa scalarMulAdd s₀ fun t => abiPreserved s₀ t ∧ scalarMulAddLocal.post s₀ t := by
  have hA := h.args
  obtain ⟨base, hbase⟩ : ∃ b, (arg s₀ 4).setWidth 64 = b := ⟨_, rfl⟩
  have hT := VG.Proof.Ed448.X86.TF_eq
  have hK := VG.Proof.Ed448.X86.SK_eq
  have hS := VG.Proof.Ed448.X86.SS_eq
  have hR := VG.Proof.Ed448.X86.SR_eq
  have hRA := VG.Proof.Ed448.X86.RA_eq
  have hC := VG.Proof.Ed448.X86.ACC_eq
  unfold scalarMulAdd
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.save_ok hA) fun s1 ⟨hs1, sv1, o1, k1⟩ => ?_)
  rw [hbase] at hs1 sv1 o1
  have o1' : Outside base 0 8192 s₀.mem s1.mem := o1.mono (by omega) (by omega)
  -- the inputs
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.inputs_ok h hbase (k1.1 _ (by decide)) k1.2.1 k1.2.2 o1' hs1)
    fun s2 ⟨k2, lK, lS, lR, vK, vS, vR⟩ => ?_)
  have hs2 := hs1.of_keeps k2.regs (by decide)
  -- the product
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.product_ok hs2 lK lS) fun s3 ⟨hs3, k3, m3, a3, v3⟩ => ?_)
  have k3' : VG.Proof.Ed448.X86.MKeep base s2 s3 := MKeep.of1 k3 (by decide) m3 (by decide) (by decide)
  -- its reduction
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.reduceProduct_ok hs3 a3) fun s4 ⟨k4, l4, v4⟩ => ?_)
  have hs4 := hs3.of_keeps k4.regs (by decide)
  have k4' : VG.Proof.Ed448.X86.MKeep base s3 s4 := MKeep.of2 k4.regs (by decide) k4.mem (by decide) (by decide)
    (by decide) (by decide)
  -- the reduced `r` survives the product and its reduction
  have eR : ∀ j < 28, limbs s4.mem base SR j = limbs s2.mem base SR j := fun j hj => by
    show (word s4.mem base (SR + 4 * j)).toNat = (word s2.mem base (SR + 4 * j)).toNat
    rw [congrArg BitVec.toNat (k4.mem.word (d := SR + 4 * j) (Or.inr (by simp only [W]; omega))
      (Or.inr (by omega)) (by omega)),
      congrArg BitVec.toNat (m3.word (d := SR + 4 * j) (Or.inl (by omega)) (by omega))]
  have lR4 : Bounded s4.mem base SR := fun j hj => by rw [eR j hj]; exact lR j hj
  have vR4 : fe s4.mem base SR = fe s2.mem base SR := VG.Proof.X448.Radix16.valN_congr eR
  have hvR : fe s4.mem base SR < L := by rw [vR4, vR]; exact Nat.mod_lt _ Proof.Ed448.L_pos
  have hvA : fe s4.mem base RA < L := by rw [v4]; exact Nat.mod_lt _ Proof.Ed448.L_pos
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.addPass_ok hs4 l4 lR4 hvA hvR) fun s5 ⟨k5, m5, l5, v5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.reduceT_ok VG.Proof.Ed448.X86.RA_buf hs5 l5 (by rw [v5]; omega)) fun s6 ⟨k6, m6, l6, v6⟩ => ?_
  have hs6 := hs5.of_keeps k6 (by decide)
  have k5' : VG.Proof.Ed448.X86.MKeep base s4 s5 := MKeep.of1 k5 (by decide) m5 (by decide) (by decide)
  have k6' : VG.Proof.Ed448.X86.MKeep base s5 s6 := MKeep.of1 k6 (by decide) m6 (by decide) (by decide)
  have kall : VG.Proof.Ed448.X86.MKeep base s1 s6 := k2.trans (k3'.trans (k4'.trans (k5'.trans k6')))
  have m06 : Outside base 0 8192 s₀.mem s6.mem := o1'.trans kall.whole
  have sv6 : VG.Proof.X448.X86.Saved base s₀.gpr s6.mem := sv1.outside kall.mem (by decide)
  have k06 : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s₀ s6 :=
    (k1.mono (by decide)).trans (kall.regs.mono (by decide))
  refine WP.mono (VG.Proof.Ed448.X86.finish_ok hA (by decide) (k06.1 _ (by decide)) k06.2.1 k06.2.2 hbase m06 hs6
    (by decide) l6 (by rw [h.wr]; simp) h.out_fit (fun j hj => VG.Proof.Ed448.X86.far_out (hbase ▸ h.out_sc) hj)
    sv6) fun t ⟨tr, kt, ot, bt⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact tr (.ebx, 0) (by decide)
    · exact tr (.esi, 4) (by decide)
    · exact tr (.edi, 8) (by decide)
    · exact tr (.ebp, 12) (by decide)
    · rw [kt.1 _ (by decide), k06.1 _ (by decide)]
  · exact VG.Proof.Ed448.X86.abi_of hbase h.ret_sc h.ret_out m06 ot
  · change bytesAt t.mem _ 57 = encodeLE 57 _
    rw [bt, v6, v5, v4, v3, vR4, vK, vS, vR, VG.Proof.Ed448.X86.mulAdd_mod]

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.ScalarVerified`. -/
section

/-!
# Ed448 scalar arithmetic on x86 (32-bit): `Verified`

Correctness includes the ABI. Taint analysis checks that secret input bytes
never determine branches or memory addresses: the only branches are on the
loop counters, and every address is a pointer plus a constant or a counter.
The local contracts only read the arguments; the shared contract of `Spec/`
lets the code write them too (`writeArgs`), which it does not
(`Verified.narrowTo`). A concrete witness proves it satisfiable.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86
open VG.Impl.Ed448.X86 (scalarReduce scalarMulAdd)

/-- The taint analysis starts with the stack arguments public, and the words
holding `out` and `scratch` (argument `scidx` of `argc`) known to be the base
addresses of the writable regions. -/
def scalarTaint (scidx argc : Nat) : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [57, 8192], argLen := 4 + 4 * argc,
    argBases := [(4, 0), (4 + 4 * scidx, 1)] }

theorem scalarTaint_wf {s : State} {argc scidx : Nat} (hp : VG.Proof.Ed448.X86.Args s argc scidx)
    (hw : s.wr = [⟨(arg s 0).setWidth 64, 57⟩, scR (arg s scidx)])
    (hos : (⟨(arg s 0).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s scidx)))
    (hofit : (arg s 0).toNat + 57 ≤ 2 ^ 32)
    (hret : (VG.Proof.X448.X86.retR s).Disjoint ⟨(arg s 0).setWidth 64, 57⟩)
    (hao : (⟨argAddr s 0, 4 * argc⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, 57⟩) :
    VG.X86.Taint.Wf (VG.Proof.Ed448.X86.scalarTaint scidx argc) s := by
  have hf := hp.sc_fit; have spfit := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hw, VG.Proof.Ed448.X86.scalarTaint], by simpa [hw] using hos, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by change (s.gpr .esp).toNat + (4 + 4 * argc) ≤ 2 ^ 32; omega_using [spfit], ?_⟩, ?_⟩
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_using [hf, hofit]
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 4 * argc) (by omega_using [spfit]) hret hao
    · exact VG.X86.Taint.frame_disjoint (n := 4 * argc) (by omega_using [spfit]) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [VG.Proof.Ed448.X86.scalarTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · refine ⟨by dsimp only [VG.Proof.Ed448.X86.scalarTaint]; have := hp.sc_lt; omega_using [this], ?_⟩
      simp [VG.X86.Taint.region, hw, VG.X86.addr, arg, argAddr]
    · refine ⟨by dsimp only [VG.Proof.Ed448.X86.scalarTaint]; have := hp.sc_lt; omega_using [this], ?_⟩
      simp [VG.X86.Taint.region, hw, VG.X86.addr, arg, argAddr]

theorem scalarTaint_agree {s t : State} {scidx argc : Nat}
    (hs : VG.X86.Taint.Wf (VG.Proof.Ed448.X86.scalarTaint scidx argc) s) (ht : VG.X86.Taint.Wf (VG.Proof.Ed448.X86.scalarTaint scidx argc) t)
    (hsp : s.gpr .esp = t.gpr .esp) (ha : ∀ i < argc, arg s i = arg t i)
    (hi : scidx < argc)
    (hws : s.wr = [⟨(arg s 0).setWidth 64, 57⟩, scR (arg s scidx)])
    (hwt : t.wr = [⟨(arg t 0).setWidth 64, 57⟩, scR (arg t scidx)])
    (hss : (s.gpr .esp).toNat + 4 + 4 * argc ≤ 2 ^ 32)
    (hst : (t.gpr .esp).toNat + 4 + 4 * argc ≤ 2 ^ 32) :
    VG.X86.Taint.Agree (VG.Proof.Ed448.X86.scalarTaint scidx argc) s t := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, hs, ht,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hsp,
    fun k h4 hk => ?_⟩
  · simp only [VG.Proof.Ed448.X86.scalarTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hsp
  · rw [hws, hwt, ha 0 (by omega_using [hi]), ha scidx hi]
  · simp only [VG.Proof.Ed448.X86.scalarTaint] at hk
    rw [show VG.X86.Taint.depth (VG.Proof.Ed448.X86.scalarTaint scidx argc).stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by omega_using [hss]) h4 hk,
      VG.X86.Taint.argByte_eq (by omega_using [hst]) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (ha ((k - 4) / 4) (by omega_using [hk, h4]))

/-! ## Reduction -/

theorem scalarReduce_wf {s : State} (h : scalarReduceLocal.pre s) :
    VG.X86.Taint.Wf (VG.Proof.Ed448.X86.scalarTaint 2 3) s := by
  have hp := ReducePre.of h
  exact VG.Proof.Ed448.X86.scalarTaint_wf hp.args hp.wr hp.out_sc hp.out_fit hp.ret_out hp.args_out

theorem scalarReduce_ct :
    ConstantTime isa scalarReduceLocal.pre scalarReduceLocal.pub scalarReduce := by
  refine VG.Taint.constantTime (A := taint) (VG.Proof.Ed448.X86.scalarTaint 2 3) ?_ (by taint_decide)
  intro s t hs ht hp
  obtain ⟨sp, a0, a1, a2⟩ := hp
  have ps := ReducePre.of hs
  have pt := ReducePre.of ht
  refine VG.Proof.Ed448.X86.scalarTaint_agree (VG.Proof.Ed448.X86.scalarReduce_wf hs) (VG.Proof.Ed448.X86.scalarReduce_wf ht) sp ?_ (by decide)
    ps.wr pt.wr ps.args.sp_fit pt.args.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  exacts [a0, a1, a2]

theorem scalarReduce_ok (s : State) (h : scalarReduceLocal.pre s) :
    ∃ tr t, Exec isa scalarReduce s tr t ∧ abiPreserved s t ∧ scalarReduceLocal.post s t :=
  VG.Proof.Ed448.X86.scalarReduce_correct (ReducePre.of h)

/-- Memory holding the arguments `0x1000, 0x2000, 0x4000` at `0x8004`. -/
def scalarReduceSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0

/-- A state satisfying the shared contract's precondition. -/
def scalarReduceSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Ed448.X86.scalarReduceSatMem
  rd := [⟨0x2000, 114⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 12⟩]

/-- `scalarReduceLocal`, the arguments writable as the shared contract has them. -/
def scalarReduceWide : Contract isa :=
  { VG.Proof.Ed448.X86.scalarReduceLocal with
  pre := fun s =>
    let out : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let wide : Region := ⟨(arg s 1).setWidth 64, 114⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [wide] ∧ s.wr = [out, scratch, args] ∧ out.Disjoint scratch ∧
      wide.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 114 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 }

def scalarReduceRd (s : State) : List Region := [⟨(arg s 1).setWidth 64, 114⟩, ⟨argAddr s 0, 12⟩]
def scalarReduceWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 57⟩, ⟨(arg s 2).setWidth 64, 8192⟩]

theorem scalarReduceWide_pre (s : State) (h : scalarReduceWide.pre s) :
    scalarReduceLocal.pre (s.withRegions (VG.Proof.Ed448.X86.scalarReduceRd s) (VG.Proof.Ed448.X86.scalarReduceWr s)) := by
  simp only [VG.Proof.Ed448.X86.scalarReduceLocal, VG.Proof.Ed448.X86.scalarReduceRd, VG.Proof.Ed448.X86.scalarReduceWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

theorem scalarReduceWide_implies :
    scalarReduceWide.Implies (Spec.Ed448.scalarReduceContract X86.abi) := by
  have a0 : arg VG.Proof.Ed448.X86.scalarReduceSat 0 = 0x1000 := by decide
  have a1 : arg VG.Proof.Ed448.X86.scalarReduceSat 1 = 0x2000 := by decide
  have a2 : arg VG.Proof.Ed448.X86.scalarReduceSat 2 = 0x4000 := by decide
  have e : argAddr VG.Proof.Ed448.X86.scalarReduceSat 0 = 0x8004 := by decide
  have esp : scalarReduceSat.gpr .esp = 0x8000 := rfl
  sig_implies [Spec.Ed448.scalarReduceContract, Spec.Ed448.scalarReduceSig,
    Spec.Ed448.scratchWords, VG.Proof.Ed448.X86.scalarReduceWide, VG.Proof.Ed448.X86.scalarReduceLocal, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, e, esp] using VG.Proof.Ed448.X86.scalarReduceSat

theorem scalarReduce_verified :
    Verified X86.target scalarReduce (Spec.Ed448.scalarReduceContract X86.abi) := by
  have hsat := scalarReduceWide_implies.sat_left
  have satLocal : ∃ s, scalarReduceLocal.pre s := hsat.elim fun s h => ⟨_, VG.Proof.Ed448.X86.scalarReduceWide_pre s h⟩
  have verifiedLocal : Verified X86.target scalarReduce VG.Proof.Ed448.X86.scalarReduceLocal :=
    Verified.of_correct VG.Proof.Ed448.X86.scalarReduce_ok VG.Proof.Ed448.X86.scalarReduce_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal VG.Proof.Ed448.X86.scalarReduceRd VG.Proof.Ed448.X86.scalarReduceWr
    VG.Proof.Ed448.X86.scalarReduceWide_pre ?_ ?_ ?_ ?_ hsat) VG.Proof.Ed448.X86.scalarReduceWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [VG.Proof.Ed448.X86.scalarReduceRd, VG.Proof.Ed448.X86.scalarReduceWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases hr with (rfl | rfl) | rfl | rfl <;> simp only [true_or, or_true]
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [VG.Proof.Ed448.X86.scalarReduceWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [VG.Proof.Ed448.X86.scalarReduceWide, VG.Proof.Ed448.X86.scalarReduceLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [VG.Proof.Ed448.X86.scalarReduceWide, VG.Proof.Ed448.X86.scalarReduceLocal, arg_withRegions, State.withRegions_gpr] using h

/-! ## Multiply-add -/

theorem scalarMulAdd_wf {s : State} (h : scalarMulAddLocal.pre s) :
    VG.X86.Taint.Wf (VG.Proof.Ed448.X86.scalarTaint 4 5) s := by
  have hp := MulAddPre.of h
  exact VG.Proof.Ed448.X86.scalarTaint_wf hp.args hp.wr hp.out_sc hp.out_fit hp.ret_out hp.args_out

theorem scalarMulAdd_ct :
    ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) (VG.Proof.Ed448.X86.scalarTaint 4 5) ?_ (by taint_decide)
  intro s t hs ht hp
  obtain ⟨sp, a0, a1, a2, a3, a4⟩ := hp
  have ps := MulAddPre.of hs
  have pt := MulAddPre.of ht
  refine VG.Proof.Ed448.X86.scalarTaint_agree (VG.Proof.Ed448.X86.scalarMulAdd_wf hs) (VG.Proof.Ed448.X86.scalarMulAdd_wf ht) sp ?_ (by decide)
    ps.wr pt.wr ps.args.sp_fit pt.args.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3, a4]

theorem scalarMulAdd_ok (s : State) (h : scalarMulAddLocal.pre s) :
    ∃ tr t, Exec isa scalarMulAdd s tr t ∧ abiPreserved s t ∧ scalarMulAddLocal.post s t :=
  VG.Proof.Ed448.X86.scalarMulAdd_correct (MulAddPre.of h)

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0x5000, 0x6000` at `0x8004`. -/
def scalarMulAddSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x30 else
  if a = 0x8011 then 0x50 else if a = 0x8015 then 0x60 else 0

/-- A state satisfying the shared contract's precondition. -/
def scalarMulAddSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Ed448.X86.scalarMulAddSatMem
  rd := [⟨0x2000, 57⟩, ⟨0x3000, 57⟩, ⟨0x5000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x6000, 8192⟩, ⟨0x8004, 20⟩]

/-- `scalarMulAddLocal`, the arguments writable as the shared contract has them. -/
def scalarMulAddWide : Contract isa :=
  { VG.Proof.Ed448.X86.scalarMulAddLocal with
  pre := fun s =>
    let out : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let r : Region := ⟨(arg s 1).setWidth 64, 57⟩
    let k : Region := ⟨(arg s 2).setWidth 64, 57⟩
    let a : Region := ⟨(arg s 3).setWidth 64, 57⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [r, k, a] ∧ s.wr = [out, scratch, args] ∧ out.Disjoint scratch ∧
      r.Disjoint scratch ∧ k.Disjoint scratch ∧ a.Disjoint scratch ∧ args.Disjoint out ∧
      args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 }

def scalarMulAddRd (s : State) : List Region :=
  [⟨(arg s 1).setWidth 64, 57⟩, ⟨(arg s 2).setWidth 64, 57⟩, ⟨(arg s 3).setWidth 64, 57⟩,
    ⟨argAddr s 0, 20⟩]
def scalarMulAddWr (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 57⟩, ⟨(arg s 4).setWidth 64, 8192⟩]

theorem scalarMulAddWide_pre (s : State) (h : scalarMulAddWide.pre s) :
    scalarMulAddLocal.pre (s.withRegions (VG.Proof.Ed448.X86.scalarMulAddRd s) (VG.Proof.Ed448.X86.scalarMulAddWr s)) := by
  simp only [VG.Proof.Ed448.X86.scalarMulAddLocal, VG.Proof.Ed448.X86.scalarMulAddRd, VG.Proof.Ed448.X86.scalarMulAddWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

theorem scalarMulAddWide_implies :
    scalarMulAddWide.Implies (Spec.Ed448.scalarMulAddContract X86.abi) := by
  have a0 : arg VG.Proof.Ed448.X86.scalarMulAddSat 0 = 0x1000 := by decide
  have a1 : arg VG.Proof.Ed448.X86.scalarMulAddSat 1 = 0x2000 := by decide
  have a2 : arg VG.Proof.Ed448.X86.scalarMulAddSat 2 = 0x3000 := by decide
  have a3 : arg VG.Proof.Ed448.X86.scalarMulAddSat 3 = 0x5000 := by decide
  have a4 : arg VG.Proof.Ed448.X86.scalarMulAddSat 4 = 0x6000 := by decide
  have e : argAddr VG.Proof.Ed448.X86.scalarMulAddSat 0 = 0x8004 := by decide
  have esp : scalarMulAddSat.gpr .esp = 0x8000 := rfl
  sig_implies [Spec.Ed448.scalarMulAddContract, Spec.Ed448.scalarMulAddSig,
    Spec.Ed448.scratchWords, VG.Proof.Ed448.X86.scalarMulAddWide, VG.Proof.Ed448.X86.scalarMulAddLocal, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp] using VG.Proof.Ed448.X86.scalarMulAddSat

theorem scalarMulAdd_verified :
    Verified X86.target scalarMulAdd (Spec.Ed448.scalarMulAddContract X86.abi) := by
  have hsat := scalarMulAddWide_implies.sat_left
  have satLocal : ∃ s, scalarMulAddLocal.pre s := hsat.elim fun s h => ⟨_, VG.Proof.Ed448.X86.scalarMulAddWide_pre s h⟩
  have verifiedLocal : Verified X86.target scalarMulAdd VG.Proof.Ed448.X86.scalarMulAddLocal :=
    Verified.of_correct VG.Proof.Ed448.X86.scalarMulAdd_ok VG.Proof.Ed448.X86.scalarMulAdd_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal VG.Proof.Ed448.X86.scalarMulAddRd VG.Proof.Ed448.X86.scalarMulAddWr
    VG.Proof.Ed448.X86.scalarMulAddWide_pre ?_ ?_ ?_ ?_ hsat) VG.Proof.Ed448.X86.scalarMulAddWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [VG.Proof.Ed448.X86.scalarMulAddRd, VG.Proof.Ed448.X86.scalarMulAddWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases hr with (rfl | rfl | rfl | rfl) | rfl | rfl <;> simp only [true_or, or_true]
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [VG.Proof.Ed448.X86.scalarMulAddWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [VG.Proof.Ed448.X86.scalarMulAddWide, VG.Proof.Ed448.X86.scalarMulAddLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [VG.Proof.Ed448.X86.scalarMulAddWide, VG.Proof.Ed448.X86.scalarMulAddLocal, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ed448.X86

end
