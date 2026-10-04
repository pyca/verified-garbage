import VerifiedGarbage.Proof.Ed448.Limbs16
import VerifiedGarbage.Proof.X448.X86.Freeze
import VerifiedGarbage.Proof.X448.X86.RowPass
import VerifiedGarbage.Proof.X448.X86.Carry
import VerifiedGarbage.Impl.Ed448.X86.Scalar

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

theorem cLimb_lt (k : Nat) : cLimb k < radix := by
  by_cases h : k < 14
  · have : ∀ k < 14, cLimb k < radix := by decide
    exact this k h
  · rw [cLimb_high (by omega)]; decide

theorem kLimb_lt (k : Nat) : kLimb k < radix := by
  unfold kLimb; split
  · decide
  · exact cLimb_lt k

theorem kLimb_mid {k : Nat} (h1 : 14 ≤ k) (h2 : k ≠ 27) : kLimb k = 0 := by
  rw [kLimb, ite_eq_right h2, cLimb_high h1]

theorem valN_cLimb : valN cLimb 28 = cL := by decide +kernel

theorem valN_kLimb : valN kLimb 28 = radix ^ 28 - L := by decide +kernel

/-! ## Instruction facts -/

theorem readSc {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 4 ≤ 8192) :
    readSrc s (.mem (Impl.X448.X86.sc d)) = some (word s.mem base d) := by
  simp only [readSrc, hs.ea (by omega : d < 8192), State.load32, hs.read hd, ite_true]

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
    rw [toNat_shr]
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
  toNat_imm h

/-! ## Folding a chunk in -/

/-- A remainder's place: after `TF`, with offsets below 4096. -/
def Buf (o : Nat) : Prop := TF + 112 ≤ o ∧ o + 112 ≤ 4096

theorem TF_eq : TF = 64 := rfl
theorem W_eq : W = 16 := rfl

theorem foldHead_ok {o : Nat} (ho : Buf o) {s : State} {base : Addr} (hs : Scr s base)
    (h27 : limbs s.mem base o 27 < 16384) (h26 : limbs s.mem base o 26 < radix) :
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
  refine wp_mov rfl fun s6 u6 => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · have e1 : (s4.gpr .ecx).toNat = limbs s.mem base o 26 / 16384 := by
      rw [u4.other .ecx (by decide), u3.other .ecx (by decide)]
      have : s2.gpr .ecx = s1.gpr .ecx >>> 14 := u2.gpr
      rw [this, toNat_shr, u1.gpr]
    have e2 : (s4.gpr .eax).toNat = 4 * limbs s.mem base o 27 := by
      have : s4.gpr .eax = (s3.gpr .eax).rotateRight 30 := u4.gpr
      rw [this, u3.gpr, u2.mem, u1.mem]
      exact toNat_rotr30 _ h27
    rw [u6.other .ecx (by decide), u5.gpr]
    change (s4.gpr .ecx + s4.gpr .eax).toNat = _
    rw [toNat_add_lt (by rw [e1, e2]; simp only [radix] at h26; omega), e1, e2]
    rfl
  · rw [u6.gpr]; rfl
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  · rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]

/-- One source of `fold`: limb `k` of `l + h c` before carrying. -/
theorem foldSrc_ok {o : Nat} (ho : Buf o) {base : Addr} {r : Nat → Nat} {w : Nat}
    (hH : foldH r < radix) (hsum : ∀ k < 28, foldC cLimb r w k ≤ 2 ^ 32 - radix)
    {k : Nat} (hk : k < 28) {s : State} (hs : Scr s base)
    (hr : ∀ j < 28, limbs s.mem base o j = r j) (hw : (word s.mem base W).toNat = w)
    (h1 : (s.gpr .ecx).toNat = foldH r) :
    WP isa (.block (foldSrc o k)) s fun t =>
      (t.gpr .eax).toNat = foldC cLimb r w k ∧ Keeps [.eax, .edx] s t ∧ t.mem = s.mem := by
  obtain ⟨ho1, ho2⟩ := ho
  have hT := TF_eq
  have hW := W_eq
  have hs' := hsum k hk
  unfold foldC at hs' ⊢
  unfold foldSrc
  have hc := cLimb_lt k
  have hprod : (BitVec.ofNat 32 (cLimb k)).toNat * (s.gpr .ecx).toNat < 2 ^ 32 := by
    rw [toNat_imm (by simp only [radix] at hc; omega), h1]
    have := Nat.mul_le_mul (Nat.le_of_lt_succ hc) (Nat.le_of_lt_succ hH)
    omega
  have prod : ∀ t : State, t.gpr .eax = BitVec.ofNat 32
      ((BitVec.ofNat 32 (cLimb k)).toNat * (s.gpr .ecx).toNat) →
      (t.gpr .eax).toNat = foldH r * cLimb k := fun t ht => by
    rw [ht, toNat_mul_lt hprod, toNat_imm (by simp only [radix] at hc; omega), h1, Nat.mul_comm]
  by_cases k0 : k = 0
  · subst k0
    rw [ite_eq_left rfl]
    refine wp_mov rfl fun s1 u1 => wp_mul fun s2 e2 m2 k2 => ?_
    have hs2 := (hs.of_upd u1 (by decide)).of_keeps k2 (by decide)
    refine wp_alu (Or.inl rfl) (readSc hs2 (by omega)) fun s3 u3 _ => WP.block_nil ⟨?_, ?_, ?_⟩
    · have p2 := prod s2 (by rw [e2, u1.gpr, u1.other .ecx (by decide)])
      have ww : (word s2.mem base W).toNat = w := by rw [m2, u1.mem, hw]
      rw [u3.gpr]
      change (s2.gpr .eax + word s2.mem base W).toNat = _
      simp only [foldL, ite_true] at hs' ⊢
      rw [toNat_add_lt (by rw [p2, ww]; omega), p2, ww, Nat.add_comm]
    · exact (u1.rest (by decide)).trans (k2.trans (u3.rest (by decide)))
    · rw [u3.mem, m2, u1.mem]
  rw [ite_eq_right k0]
  by_cases k14 : k < 14
  · rw [ite_eq_left k14]
    refine wp_mov rfl fun s1 u1 => wp_mul fun s2 e2 m2 k2 => ?_
    have hs2 := (hs.of_upd u1 (by decide)).of_keeps k2 (by decide)
    refine wp_alu (Or.inl rfl) (readSc hs2 (by omega)) fun s3 u3 _ => WP.block_nil ⟨?_, ?_, ?_⟩
    · have p2 := prod s2 (by rw [e2, u1.gpr, u1.other .ecx (by decide)])
      have ww : limbs s2.mem base o (k - 1) = r (k - 1) := by
        rw [m2, u1.mem]; exact hr (k - 1) (by omega)
      rw [u3.gpr]
      change (s2.gpr .eax + word s2.mem base (o + 4 * (k - 1))).toNat = _
      simp only [foldL, k0, ite_false, show k < 27 by omega, ite_true] at hs' ⊢
      have ww' : (word s2.mem base (o + 4 * (k - 1))).toNat = r (k - 1) := ww
      rw [toNat_add_lt (by rw [p2, ww']; omega), p2, ww', Nat.add_comm]
    · exact (u1.rest (by decide)).trans (k2.trans (u3.rest (by decide)))
    · rw [u3.mem, m2, u1.mem]
  rw [ite_eq_right k14]
  by_cases k27 : k < 27
  · rw [ite_eq_left k27]
    refine load_ok hs (by omega) fun s1 u1 => WP.block_nil ⟨?_, u1.rest (by decide), u1.mem⟩
    rw [u1.gpr]
    simp only [foldL, k0, ite_false, k27, ite_true, cLimb_high (by omega : 14 ≤ k), Nat.mul_zero,
      Nat.add_zero]
    exact hr (k - 1) (by omega)
  · rw [ite_eq_right k27]
    refine load_ok hs (by omega) fun s1 u1 => ?_
    refine wp_alu (Or.inr (Or.inr (Or.inl rfl))) rfl fun s2 u2 _ => WP.block_nil
      ⟨?_, (u1.rest (by decide)).trans (u2.rest (by decide)), by rw [u2.mem, u1.mem]⟩
    rw [u2.gpr]
    change (s1.gpr .eax &&& (16383 : BitVec 32)).toNat = _
    rw [toNat_and14, u1.gpr]
    simp only [foldL, k0, ite_false, k27, cLimb_high (by omega : 14 ≤ k), Nat.mul_zero, Nat.add_zero]
    exact congrArg (· % 16384) (hr 26 (by decide))

/-- `fold o`: the limbs of `l + h c` into `TF`. -/
theorem fold_ok {o : Nat} (ho : Buf o) {s : State} {base : Addr} (hs : Scr s base)
    (hl : Bounded s.mem base o) (hv : fe s.mem base o < L) (hw : (word s.mem base W).toNat < radix) :
    WP isa (.block (fold o)) s fun t =>
      Keeps [.eax, .ebx, .ecx, .edx] s t ∧ Outside base TF 112 s.mem t.mem ∧
      Bounded t.mem base TF ∧ fe t.mem base TF < 2 * L ∧
      fe t.mem base TF % L = ((word s.mem base W).toNat + radix * fe s.mem base o) % L := by
  have hT := TF_eq
  have hW := W_eq
  obtain ⟨ho1, ho2⟩ := ho
  obtain ⟨h27, hH, hsum, hlt, hmod⟩ := fold_facts (c := cLimb) (fun k _ => cLimb_lt k) valN_cLimb hl hv hw
  unfold fold
  rw [WP.block_append_iff]
  refine WP.mono (foldHead_ok ⟨ho1, ho2⟩ hs h27 (hl 26 (by decide))) fun s1 ⟨e1, e5, k1, m1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  refine WP.mono (carryPass_ok (rb := .edi) (o := TF) (d := TF) (s0 := s1)
    (c := foldC cLimb (limbs s.mem base o) (word s.mem base W).toNat) (by decide) (by omega)
    (fun k hk => hs1.ea (by omega)) (fun k hk => hs1.write (by omega)) e5 hsum ?_) fun t ht => ?_
  · intro k hk s' hp
    have hs' := hs1.of_keeps hp.regs (by decide)
    have hm := hp.mem
    rw [m1] at hm
    refine foldSrc_ok ⟨ho1, ho2⟩ hH hsum hk hs' (fun j hj => ?_) ?_ ?_
    · exact hm.limbs (Or.inr (by omega)) (by omega) hj
    · rw [hm.word (Or.inl (by omega)) (by omega)]
    · rw [hp.regs.1 _ (by decide)]; exact e1
  · generalize hc : foldC cLimb (limbs s.mem base o) (word s.mem base W).toNat = c at ht hlt hmod hsum
    have hval : fe t.mem base TF = valN c 28 := by
      show valN (limbs t.mem base TF) 28 = _
      rw [valN_congr ht.outs]
      exact digits_val (Nat.lt_of_lt_of_le hlt two_L_le)
    refine ⟨(k1.mono (by decide)).trans (ht.regs.mono (by decide)), ?_, fun k hk => ?_,
      by rw [hval]; exact hlt, by rw [hval]; exact hmod⟩
    · rw [← m1]; exact ht.mem
    · rw [ht.outs k hk]; exact digit_lt _ _

/-! ## The conditional subtraction -/

/-- One source of the subtraction: limb `k` of `TF` plus limb `k` of `K`. -/
theorem csubSrc_ok {k : Nat} (hk : k < 28) {s : State} {base : Addr} (hs : Scr s base)
    (hl : limbs s.mem base TF k < radix) :
    WP isa (.block (csubSrc k)) s fun t =>
      (t.gpr .eax).toNat = limbs s.mem base TF k + kLimb k ∧ Keeps [.eax, .edx] s t ∧ t.mem = s.mem := by
  have hT := TF_eq
  unfold csubSrc
  by_cases hkk : k < 14 ∨ k = 27
  · rw [ite_eq_left hkk]
    refine load_ok hs (by omega) fun s1 u1 => wp_alu (Or.inl rfl) rfl fun s2 u2 _ =>
      WP.block_nil ⟨?_, (u1.rest (by decide)).trans (u2.rest (by decide)), by rw [u2.mem, u1.mem]⟩
    have hkl := kLimb_lt k
    have e1 : (s1.gpr .eax).toNat = limbs s.mem base TF k := by rw [u1.gpr]
    have e2 : (BitVec.ofNat 32 (kLimb k)).toNat = kLimb k := toNat_imm (by simp only [radix] at hkl; omega)
    rw [u2.gpr]
    change (s1.gpr .eax + BitVec.ofNat 32 (kLimb k)).toNat = _
    rw [toNat_add_lt (by rw [e1, e2]; simp only [radix] at hl hkl; omega), e1, e2]
  · rw [ite_eq_right hkk]
    refine load_ok hs (by omega) fun s1 u1 => WP.block_nil ⟨?_, u1.rest (by decide), u1.mem⟩
    rw [u1.gpr, kLimb_mid (by omega) (by omega), Nat.add_zero]

theorem selectStep_ok {o : Nat} (ho : Buf o) {k : Nat} (hk : k < 28) {s : State} {base : Addr}
    (hs : Scr s base) {sw : Bool} (hc : s.gpr .ecx = mask sw) :
    WP isa (.block (Impl.Ed448.X86.selectStep o k)) s fun t =>
      t.mem = s.mem.writeW (off base (o + 4 * k))
        (if sw then word s.mem base (o + 4 * k) else word s.mem base (TF + 4 * k)) ∧
      Keeps [.eax, .edx] s t := by
  obtain ⟨ho1, ho2⟩ := ho
  have hT := TF_eq
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
    change s.mem.writeW _ (_ ^^^ ((_ ^^^ _) &&& mask sw)) = _
    rw [BitVec.xor_comm (word s.mem base (o + 4 * k)), (xor_sel sw _ _).1]
  · exact ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans
      ((hv.rest (by decide)).trans ((hw.rest (by decide)).trans ((hx.rest (by decide)).trans (hy.rest _))))))

theorem select_ok {o : Nat} (ho : Buf o) {s : State} {base : Addr} (hs : Scr s base) {sw : Bool}
    (hc : s.gpr .ecx = mask sw) :
    WP isa (.block ((List.range 28).flatMap (Impl.Ed448.X86.selectStep o))) s fun t =>
      (∀ i < 28, limbs t.mem base o i = if sw then limbs s.mem base o i else limbs s.mem base TF i) ∧
      Outside base o 112 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  obtain ⟨ho1, ho2⟩ := ho
  have hT := TF_eq
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base o i = if sw then limbs s.mem base o i else limbs s.mem base TF i) ∧
    Outside base o (4 * n) s.mem t.mem ∧ Keeps [.eax, .edx] s t
  have st : ∀ n t, n < 28 → inv n t → WP isa (.block (Impl.Ed448.X86.selectStep o n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (selectStep_ok ⟨ho1, ho2⟩ hn (hs.of_keeps tk (by decide)) ((tk.1 _ (by decide)).trans hc))
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
theorem reduceT_ok {o : Nat} (ho : Buf o) {s : State} {base : Addr} (hs : Scr s base)
    (hl : Bounded s.mem base TF) (hv : fe s.mem base TF < 2 * L) :
    WP isa (.block (reduceT o)) s fun t =>
      Keeps [.eax, .ebx, .ecx, .edx] s t ∧ Outside base o 112 s.mem t.mem ∧
      Bounded t.mem base o ∧ fe t.mem base o = fe s.mem base TF % L := by
  obtain ⟨ho1, ho2⟩ := ho
  have hT := TF_eq
  unfold reduceT
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zeroCarry_ok s) fun s1 ⟨e1, m1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (carryPass_ok (rb := .edi) (o := o) (d := o) (s0 := s1)
    (c := fun k => limbs s.mem base TF k + kLimb k) (by decide) (by omega)
    (fun k hk => hs1.ea (by omega)) (fun k hk => hs1.write (by omega)) (by rw [e1]; rfl)
    (fun k hk => by have := hl k hk; have := kLimb_lt k; simp only [radix] at *; omega) ?_)
    fun s2 h2 => ?_
  · intro k hk s' hp
    have hs' := hs1.of_keeps hp.regs (by decide)
    have et : limbs s'.mem base TF k = limbs s.mem base TF k := by
      rw [hp.mem.limbs (Or.inl (by omega)) (by omega) hk, m1]
    refine WP.mono (csubSrc_ok hk hs' (by rw [et]; exact hl k hk)) fun t ⟨e, kt, mt⟩ => ⟨?_, kt, mt⟩
    rw [e, et]
  generalize hcf : (fun k => limbs s.mem base TF k + kLimb k) = c at h2
  have hval := pass_eq c 28
  have hcv : valN c 28 = fe s.mem base TF + (radix ^ 28 - L) := by
    rw [← hcf, valN_add, valN_kLimb]
  have hy := valN_lt (f := digit c) (n := 28) fun k _ => digit_lt _ _
  rw [hcv] at hval
  have hLM := two_L_le
  generalize hM : radix ^ 28 = M at hy hval hLM
  obtain ⟨hc1, hsel⟩ := csub_facts hLM hv hy hval
  rw [← h2.carry] at hc1
  rw [WP.block_append_iff]
  refine WP.mono (freezeMask_ok (s := s2) rfl (by omega)) fun s3 ⟨e3, m3, k3⟩ => ?_
  have hs3 := (hs1.of_keeps h2.regs (by decide)).of_keeps k3 (by decide)
  refine WP.mono (select_ok ⟨ho1, ho2⟩ hs3 e3) fun t ⟨ht, mt, kt⟩ => ?_
  have hlt : ∀ k < 28, limbs t.mem base o k =
      if carry c 28 = 1 then digit c k else limbs s.mem base TF k := by
    intro k hk
    rw [ht k hk, m3, h2.outs k hk, h2.mem.limbs (Or.inl (by omega)) (by omega) hk, m1, ← h2.carry]
    simp only [decide_eq_true_eq]
  refine ⟨(k1.mono (by decide)).trans ((h2.regs.mono (by decide)).trans ((k3.mono (by decide)).trans
    (kt.mono (by decide)))), ?_, fun k hk => ?_, ?_⟩
  · rw [← m1]
    exact h2.mem.trans (by rw [← m3]; exact mt)
  · rw [hlt k hk]; split
    · exact digit_lt _ _
    · exact hl k hk
  · rw [← hsel]
    change valN (limbs t.mem base o) 28 = _
    rw [valN_congr hlt]
    split
    · rfl
    · rfl

/-! ## One chunk -/

/-- `step o`: the chunk at `W` folded into the remainder at `o`. -/
theorem step_ok {o : Nat} (ho : Buf o) {s : State} {base : Addr} (hs : Scr s base)
    (hl : Bounded s.mem base o) (hv : fe s.mem base o < L) (hw : (word s.mem base W).toNat < radix) :
    WP isa (.block (step o)) s fun t =>
      Keeps [.eax, .ebx, .ecx, .edx] s t ∧ Outside2 base TF 112 o 112 s.mem t.mem ∧
      Bounded t.mem base o ∧
      fe t.mem base o = ((word s.mem base W).toNat + radix * fe s.mem base o) % L := by
  obtain ⟨ho1, ho2⟩ := ho
  unfold step
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok ⟨ho1, ho2⟩ hs hl hv hw) fun u ⟨ku, fu, lu, vu, mu⟩ => ?_
  refine WP.mono (reduceT_ok ⟨ho1, ho2⟩ (hs.of_keeps ku (by decide)) lu vu)
    fun t ⟨kt, ft, lt, vt⟩ => ⟨ku.trans kt, fun p h1 h2 => (ft p h2).trans (fu p h1), lt, by rw [vt, mu]⟩

end VG.Proof.Ed448.X86
