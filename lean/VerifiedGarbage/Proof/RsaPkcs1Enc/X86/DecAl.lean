module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecIrprf
import VerifiedGarbage.Proof.RsaPkcs1Enc.Select
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecTaint

/-!
# RSAES-PKCS1-v1_5 decryption on x86: the alternative length

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecAl.lean`): the mask of the
candidates, `2^bitLength(k - 11) - 1`, by doublings (`maskLoop_vp`), and
`AL`, the last candidate not above `k - 11`, a fold over the 128 candidates
of `CL` (`alLoop_vp`), to its slot (`alPart_vp`, `AL`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp
open VG.Proof.Mont.X86 (wp_subS)
open VG.Proof.Pbkdf2.Stream.X86 (wp_xori)
open VG.Proof.RsaPkcs1Enc (bitMask altStep)
open VG.Spec.RsaPkcs1Enc (bitLength)

variable {P : EP}

/-! ## Memory kept -/

theorem IR.of_mem {σ s t : State} (h : IR P σ s) (st : P.lay.St σ t) (hm : t.mem = s.mem) : IR P σ t :=
  ⟨h.1.regs st hm, by rw [hm]; exact h.2.1, by rw [hm]; exact h.2.2⟩

theorem IR.keep_fr {σ s t : State} (h : IR P σ s) (st : P.lay.St σ t) {d : Nat} {v : BitVec 32}
    (hm : t.mem = s.mem.writeW (P.lay.fr d) v) (hd : d + 4 ≤ frameBytes) (ho : d + 4 ≤ oR ∨ oR + 4 ≤ d) :
    IR P σ t := by
  have hs := h.1.1
  have hK := hs.1.k1024
  have fr : Frame [⟨P.lay.fr d, 4⟩] s.mem t.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)
  have hd' : d + 4 ≤ frameBytes + 16 := by omega
  refine ⟨h.1.frame st fr fun r hr => ?_, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.safe_fr hd ho
  · rw [Proof.RsaPkcs1Sig.bytesAt_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hs.1.fr_sc hd' (by decide)).symm) (by decide)]
    exact h.2.1
  · rw [Proof.RsaPkcs1Sig.bytesAt_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hs.1.fr_sc hd' (by simp only [sAM]; omega)).symm) (by omega)]
    exact h.2.2

/-! ## The mask -/

/-- The mask `2^j - 1` (`eax`), and `k - 11` (`ecx`). -/
def MI (P : EP) (j : Nat) (σ s : State) : Prop :=
  IR P σ s ∧ s.gpr .eax = BitVec.ofNat 32 (2 ^ j - 1) ∧ s.gpr .ecx = BitVec.ofNat 32 (P.K - 11)

/-- The mask. -/
def MK (P : EP) (σ s : State) : Prop :=
  IR P σ s ∧ s.gpr .eax = BitVec.ofNat 32 (bitMask (P.K - 11)) ∧ s.gpr .ecx = BitVec.ofNat 32 (P.K - 11)

theorem maskInit_vp : VP (IR P) (.block maskInit) (MI P 0) :=
  VP.taint [.esp] maskInit_taint (sp_agree fun _ _ h => h.1.1) fun σ s h => by
    have hs := h.1.1
    have hK := hs.1.k64
    simp only [maskInit]
    refine St.argv hs (j := 4) (by decide) (d := .ecx) (by decide) fun t1 s1 u1 => ?_
    refine wp_subi fun t2 u2 _ _ => ?_
    have s2 : S P σ t2 := ⟨hs.1, s1.2.upd u2 (by decide)⟩
    refine St.movi s2 (d := .eax) (by decide) 0 fun t3 s3 u3 => WP.block_nil ?_
    refine ⟨h.of_mem s3.2 (by rw [u3.mem, u2.mem, u1.mem]), u3.gpr, ?_⟩
    rw [u3.other _ (by decide), u2.gpr, u1.gpr]
    exact Offset.ofNat_sub_ofNat (d := 11) (by omega)

/-- The loop's stage, `m` doublings left. -/
def MLI (P : EP) (m : Nat) (σ s : State) : Prop := m ≤ bitLength (P.K - 11) ∧ MI P (bitLength (P.K - 11) - m) σ s

theorem bitLength_le {x : Nat} (hx : x ≠ 0) (hx' : x < 2 ^ 30) : 2 ^ bitLength x - 1 < 2 ^ 31 := by
  have := VG.Proof.RsaPkcs1Enc.bitMask_le hx
  simp only [bitMask] at this
  omega

theorem maskBody_vp (n : Nat) : VP (MLI P (n + 1)) (.block maskBody) fun σ s =>
    isa.eval .b s = some (decide (0 < n)) ∧ (n = 0 → MK P σ s) ∧ (0 < n → MLI P n σ s) := by
  refine VP.taint [.eax, .ecx] maskBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s h => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
  obtain ⟨hn, hir, ax, cx⟩ := h
  have hs := hir.1.1
  have hK := hs.1.k64
  have hK' := hs.1.k1024
  have hx : P.K - 11 ≠ 0 := by omega
  generalize hB : bitLength (P.K - 11) = B at hn ax
  have hj : B - (n + 1) < bitLength (P.K - 11) := by omega
  have hlt := VG.Proof.RsaPkcs1Enc.bitMask_lt hx hj
  have hst := VG.Proof.RsaPkcs1Enc.bitMask_step (by omega : 1 ≤ P.K - 11) hlt
  have hp : 2 ^ (B - (n + 1) + 1) - 1 ≤ 2 ^ B - 1 :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) (by omega)) _
  have hB31 : 2 ^ B - 1 < 2 ^ 31 := by rw [← hB]; exact bitLength_le hx (by omega)
  simp only [maskBody]
  refine wp_add fun t1 u1 _ => ?_
  refine wp_addi fun t2 u2 => ?_
  refine wp_cmp fun t3 u3 hc _ => WP.block_nil ?_
  have ax2 : t2.gpr .eax = BitVec.ofNat 32 (2 ^ (B - (n + 1) + 1) - 1) := by
    rw [u2.gpr, u1.gpr, ax, ← hst.1]
    apply BitVec.eq_of_toNat_eq
    have e1 : (1 : BitVec 32).toNat = 1 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, e1]
    omega
  have cx2 : t2.gpr .ecx = BitVec.ofNat 32 (P.K - 11) := by
    rw [u2.other _ (by decide), u1.other _ (by decide), cx]
  have st : P.lay.St σ t3 := ((hs.2.upd u1 (by decide)).upd u2 (by decide)).fupd u3
  have ir := hir.of_mem st (by rw [u3.mem, u2.mem, u1.mem])
  have e : (2 ^ (B - (n + 1) + 1) - 1 < P.K - 11) = (0 < n) := by
    apply propext; constructor
    · intro h; by_contra h0
      have := VG.Proof.RsaPkcs1Enc.bitMask_ge hx
      rw [hB] at this
      rw [show B - (n + 1) + 1 = B by omega] at h
      omega
    · intro h0
      exact VG.Proof.RsaPkcs1Enc.bitMask_lt hx (by omega)
  rw [ax2, cx2, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at hc
  have ax3 : t3.gpr .eax = BitVec.ofNat 32 (2 ^ (B - (n + 1) + 1) - 1) := by rw [u3.gpr, ax2]
  have cx3 : t3.gpr .ecx = BitVec.ofNat 32 (P.K - 11) := by rw [u3.gpr, cx2]
  refine ⟨by show eval .b t3 = _; simp only [eval, hc, e], fun h0 => ⟨ir, ?_, cx3⟩,
    fun h0 => ⟨by omega, ir, ?_, cx3⟩⟩
  · rw [ax3, show B - (n + 1) + 1 = B by omega, ← hB]; rfl
  · rw [ax3, show B - (n + 1) + 1 = B - n by omega, hB]

theorem maskLoop_vp : VP (MI P 0) maskLoop (MK P) := by
  refine (VP.loop (I := MLI P) maskBody_vp (bitLength (P.K - 11) - 1)).mono (fun σ s h => ?_) fun _ _ h => h
  have hK := h.1.1.1.1.k64
  have : 1 ≤ bitLength (P.K - 11) := by
    simp only [bitLength, show P.K - 11 ≠ 0 by omega, ↓reduceIte]; omega
  refine ⟨by omega, ?_⟩
  rw [show bitLength (P.K - 11) - (bitLength (P.K - 11) - 1 + 1) = 0 by omega]; exact h

/-! ## The candidates -/

theorem clV_length (P : EP) (σ : State) : (clV P σ).length = 256 := by
  rw [clV_eq, flatMap_blocks_length]

theorem altStep_and (K : Nat) (CL : List Byte) (al i : Nat) :
    altStep K CL al i =
      (let c := (256 * (CL.getD (2 * i) 0).toNat + (CL.getD (2 * i + 1) 0).toNat) &&& bitMask (K - 11);
        if c ≤ K - 11 then c else al) := by
  simp only [altStep, VG.Proof.RsaPkcs1Enc.cand_eq, bitMask, Nat.and_two_pow_sub_one_eq_mod]

theorem byte_rotate (b : BitVec 8) : (b.setWidth 32).rotateRight 24 = b.setWidth 32 <<< 8 := by
  have hz : b.setWidth 32 >>> 24 = 0 := by
    apply BitVec.eq_of_toNat_eq
    have hb := b.isLt
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
    change b.toNat % 2 ^ 32 / 2 ^ 24 = 0
    omega
  rw [BitVec.rotateRight_def, hz]
  exact BitVec.zero_or

theorem cand_bv (b0 b1 : Byte) :
    (b0.setWidth 32).rotateRight 24 ||| b1.setWidth 32 = BitVec.ofNat 32 (256 * b0.toNat + b1.toNat) := by
  have h0 := b0.isLt
  have h1 := b1.isLt
  rw [byte_rotate]
  have hz : (b0.setWidth 32 <<< 8) &&& b1.setWidth 32 = 0 := by
    ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth]
    by_cases h : i < 8
    · simp [h]
    · simp only [h, decide_false, Bool.not_false, Bool.true_and]
      rw [BitVec.getLsbD_of_ge b1 i (by omega)]; simp
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hz]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem sel_bv (a c : BitVec 32) (p : Bool) :
    a ^^^ ((c ^^^ a) &&& ((if p then BitVec.allOnes 32 else 0) ^^^ BitVec.allOnes 32)) = if p then a else c := by
  cases p
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (0 : BitVec 32) = 0#32 from rfl, BitVec.zero_xor,
      BitVec.and_allOnes, BitVec.xor_comm c a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp only [↓reduceIte]
    rw [BitVec.xor_self, BitVec.and_zero, BitVec.xor_zero]

theorem ofNat_beq_zero {n : Nat} (hn : n < 2 ^ 32) : (BitVec.ofNat 32 n == 0) = decide (n = 0) := by
  by_cases h : n = 0
  · subst h; rfl
  · have : BitVec.ofNat 32 n ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
      exact h this
    rw [beq_eq_false_iff_ne.mpr this, decide_eq_false h]

/-- The fold of the first `j` candidates. -/
abbrev alFold (P : EP) (σ : State) (j : Nat) : Nat := (List.range j).foldl (altStep P.K (clV P σ)) 0

/-- Before candidate `j`. -/
def ALI (P : EP) (j : Nat) (σ s : State) : Prop :=
  IR P σ s ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 (sCL + 2 * j) ∧
    s.gpr .edi = BitVec.ofNat 32 (bitMask (P.K - 11)) ∧ s.gpr .ebp = BitVec.ofNat 32 (P.K - 11) ∧
    s.gpr .ebx = BitVec.ofNat 32 (alFold P σ j) ∧ s.gpr .ecx = BitVec.ofNat 32 (128 - j)

/-- `AL` in `ebx`. -/
def ALQ (P : EP) (σ s : State) : Prop :=
  IR P σ s ∧ s.gpr .ebx = BitVec.ofNat 32 (Spec.RsaPkcs1Enc.altLength P.K (clV P σ))

/-- `AL` in its slot. -/
def AL (P : EP) (σ s : State) : Prop :=
  IR P σ s ∧ s.mem.readW (P.lay.fr oAL) 32 = BitVec.ofNat 32 (Spec.RsaPkcs1Enc.altLength P.K (clV P σ))

theorem alInit_vp : VP (MK P) (.block alInit) (ALI P 0) :=
  VP.taint [.esp] alInit_taint (sp_agree fun _ _ h => h.1.1.1) fun σ s h => by
    obtain ⟨hir, ax, cx⟩ := h
    have hs := hir.1.1
    simp only [alInit]
    refine St.scrW hs (d := .esi) (by decide) sCL fun t1 s1 u1 => ?_
    refine wp_mov fun t2 u2 => ?_
    refine wp_mov fun t3 u3 => ?_
    have s3 : S P σ t3 := ⟨hs.1, (s1.2.upd u2 (by decide)).upd u3 (by decide)⟩
    refine St.movi s3 (d := .ebx) (by decide) 0 fun t4 s4 u4 => ?_
    refine St.movi s4 (d := .ecx) (by decide) 128 fun t5 s5 u5 => WP.block_nil ?_
    refine ⟨hir.of_mem s5.2 (by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]), ?_, ?_, ?_, ?_, ?_⟩
    · rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr]
      rfl
    · rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr,
        u1.other _ (by decide), ax]
    · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.other _ (by decide),
        u1.other _ (by decide), cx]
    · rw [u5.other _ (by decide), u4.gpr]; rfl
    · rw [u5.gpr]

/-- `m` candidates left. -/
def ALM (P : EP) (m : Nat) (σ s : State) : Prop := m ≤ 128 ∧ ALI P (128 - m) σ s

/-- Byte `i` of `CL`. -/
theorem cl_byte {σ s : State} (h : IR P σ s) {i : Nat} (hi : i < 256) :
    s.mem (P.scr.setWidth 64 + BitVec.ofNat 64 (sCL + i)) = (clV P σ).getD i 0 := by
  rw [← h.2.1, Proof.RsaPkcs1Sig.bytesAt_getD hi, Offset.add_add]

theorem alBody_vp (n : Nat) : VP (ALM P (n + 1)) (.block alBody) fun σ s =>
    isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → ALQ P σ s) ∧ (0 < n → ALM P n σ s) := by
  refine VP.taint [.esi, .ecx] alBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s h => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.2.2.2, h₂.2.2.2.2.2.2]
  obtain ⟨hn, hir, si, di, bp, bx, cx⟩ := h
  generalize hj : 128 - (n + 1) = j at si bx cx
  have hjn : j + n + 1 = 128 := by omega
  have hs := hir.1.1
  have hK := hs.1.k64
  have hK' := hs.1.k1024
  have hx : P.K - 11 ≠ 0 := by omega
  have hm := VG.Proof.RsaPkcs1Enc.bitMask_le hx
  have ha : ∀ d < 2, s.ea ⟨.esi, d⟩ = P.scr.setWidth 64 + BitVec.ofNat 64 (sCL + (2 * j + d)) := by
    intro d hd
    rw [ea_at, si, hs.1.addrSc (by simp only [sCL]; omega), Nat.add_assoc]
  have e0 := cl_byte hir (i := 2 * j + 0) (by omega)
  have e1 := cl_byte hir (i := 2 * j + 1) (by omega)
  simp only [alBody]
  refine wp_movzx8 (ha 0 (by decide)) (St.sc_r hs (by simp only [sCL]; omega)) fun t1 u1 => ?_
  refine wp_ror (n := 24) (by decide) fun t2 u2 => ?_
  refine wp_movzx8 (a := P.scr.setWidth 64 + BitVec.ofNat 64 (sCL + (2 * j + 1)))
    (by rw [ea_at, u2.other _ (by decide), u1.other _ (by decide), ← ea_at]; exact ha 1 (by decide))
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact St.sc_r hs (by simp only [sCL]; omega)) fun t3 u3 => ?_
  refine wp_or fun t4 u4 => ?_
  refine wp_and fun t5 u5 => ?_
  refine wp_mov fun t6 u6 => ?_
  refine wp_subS (readSrc_reg _ _) fun t7 u7 c7 => ?_
  refine wp_sbb_self c7 fun t8 u8 => ?_
  refine wp_xori fun t9 u9 => ?_
  refine wp_xor fun t10 u10 => ?_
  refine wp_and fun t11 u11 => ?_
  refine wp_xor fun t12 u12 => ?_
  refine wp_addi fun t13 u13 => ?_
  refine wp_subi fun t14 u14 _ hz => WP.block_nil ?_
  have mm : t14.mem = s.mem := by
    rw [u14.mem, u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem,
      u2.mem, u1.mem]
  have st : P.lay.St σ t14 := hs.2.regs (by rw [u14.rd, u13.rd, u12.rd, u11.rd, u10.rd, u9.rd, u8.rd, u7.rd,
      u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd])
    (by rw [u14.wr, u13.wr, u12.wr, u11.wr, u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
    (by simp (disch := decide) only [u14.other, u13.other, u12.other, u11.other, u10.other, u9.other, u8.other,
      u7.other, u6.other, u5.other, u4.other, u3.other, u2.other, u1.other]) mm
  generalize hb0 : (clV P σ).getD (2 * j) 0 = b0 at e0
  generalize hb1 : (clV P σ).getD (2 * j + 1) 0 = b1 at e1
  generalize hc : (256 * b0.toNat + b1.toNat) &&& bitMask (P.K - 11) = c
  have hcm : c ≤ bitMask (P.K - 11) := hc ▸ Nat.and_le_right
  have c4 : t4.gpr .eax = BitVec.ofNat 32 (256 * b0.toNat + b1.toNat) := by
    rw [u4.gpr, u3.other _ (by decide), u2.gpr, u1.gpr, u3.gpr, u2.mem, u1.mem, e1]
    rw [show s.mem (P.scr.setWidth 64 + BitVec.ofNat 64 (sCL + (2 * j + 0))) = b0 from e0]
    exact cand_bv _ _
  have c5 : t5.gpr .eax = BitVec.ofNat 32 c := by
    rw [u5.gpr, c4, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide), di, ← hc, BitVec.ofNat_and]
  have dp6 : t6.gpr .edx = BitVec.ofNat 32 (P.K - 11) := by
    rw [u6.gpr]; simp (disch := decide) only [u5.other, u4.other, u3.other, u2.other, u1.other]; exact bp
  rw [dp6, u6.other _ (by decide), c5, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at c7
  have bx11 : t11.gpr .ebx = BitVec.ofNat 32 (alFold P σ j) := by
    simp (disch := decide) only [u11.other, u10.other, u9.other, u8.other, u7.other, u6.other, u5.other,
      u4.other, u3.other, u2.other, u1.other]; exact bx
  have cnd : decide ((t6.gpr .edx).toNat < (t6.gpr .eax).toNat) = decide (P.K - 11 < c) := by
    rw [dp6, u6.other _ (by decide), c5, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have ax9 : t10.gpr .eax = BitVec.ofNat 32 c ^^^ BitVec.ofNat 32 (alFold P σ j) := by
    rw [u10.gpr]
    simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other]
    rw [c5]
    simp (disch := decide) only [u5.other, u4.other, u3.other, u2.other, u1.other]
    rw [bx]
  have dx10 : t10.gpr .edx = (if decide (P.K - 11 < c) then BitVec.allOnes 32 else 0) ^^^ BitVec.allOnes 32 := by
    rw [u10.other _ (by decide), u9.gpr, u8.gpr, cnd]
  have c12 : t12.gpr .ebx = if decide (P.K - 11 < c) then BitVec.ofNat 32 (alFold P σ j) else BitVec.ofNat 32 c := by
    rw [u12.gpr, u11.gpr, ax9, dx10, bx11]
    exact sel_bv _ _ _
  have fold : alFold P σ (j + 1) = if P.K - 11 < c then alFold P σ j else c := by
    rw [alFold, VG.Proof.RsaPkcs1Enc.foldl_range_succ, altStep_and]
    simp only [hb0, hb1, hc]
    by_cases h : P.K - 11 < c
    · simp [h, show ¬ c ≤ P.K - 11 by omega]
    · simp [h, show c ≤ P.K - 11 by omega]
  have bxt : t14.gpr .ebx = BitVec.ofNat 32 (alFold P σ (j + 1)) := by
    rw [u14.other _ (by decide), u13.other _ (by decide), c12, fold]
    by_cases h : P.K - 11 < c <;> simp [h]
  have cx13 : t13.gpr .ecx = BitVec.ofNat 32 (n + 1) := by
    simp (disch := decide) only [u13.other, u12.other, u11.other, u10.other, u9.other, u8.other, u7.other,
      u6.other, u5.other, u4.other, u3.other, u2.other, u1.other]
    rw [cx, show 128 - j = n + 1 by omega]
  have cxt : t14.gpr .ecx = BitVec.ofNat 32 n := by
    rw [u14.gpr, cx13]; exact Offset.ofNat_sub_ofNat (d := 1) (by omega)
  have ir := hir.of_mem st mm
  refine ⟨?_, fun h0 => ⟨ir, ?_⟩, fun h0 => ⟨by omega, ir, ?_, ?_, ?_, ?_, ?_⟩⟩
  · show eval .ne t14 = _
    rw [cx13, show BitVec.ofNat 32 (n + 1) - 1 = BitVec.ofNat 32 n from
      Offset.ofNat_sub_ofNat (d := 1) (by omega), ofNat_beq_zero (by omega)] at hz
    simp only [eval, hz]
    by_cases h0 : n = 0 <;> simp [h0] <;> omega
  · rw [bxt, show j + 1 = 128 by omega]; rfl
  · rw [u14.other _ (by decide), u13.gpr]
    simp (disch := decide) only [u12.other, u11.other, u10.other, u9.other, u8.other, u7.other, u6.other,
      u5.other, u4.other, u3.other, u2.other, u1.other]
    rw [si, BitVec.add_assoc, show 128 - n = j + 1 by omega]
    refine congrArg (P.scr + ·) ?_
    apply BitVec.eq_of_toNat_eq
    have e2 : (2 : BitVec 32).toNat = 2 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, e2]
    omega
  · simp (disch := decide) only [u14.other, u13.other, u12.other, u11.other, u10.other, u9.other, u8.other,
      u7.other, u6.other, u5.other, u4.other, u3.other, u2.other, u1.other]; exact di
  · simp (disch := decide) only [u14.other, u13.other, u12.other, u11.other, u10.other, u9.other, u8.other,
      u7.other, u6.other, u5.other, u4.other, u3.other, u2.other, u1.other]; exact bp
  · rw [bxt, show 128 - n = j + 1 by omega]
  · rw [cxt, show 128 - (128 - n) = n by omega]

theorem alLoop_vp : VP (ALI P 0) alLoop (ALQ P) :=
  (VP.loop (I := ALM P) alBody_vp 127).mono (fun _ _ h => ⟨by decide, h⟩) fun _ _ h => h

theorem alSave_vp : VP (ALQ P) (.block alSave) (AL P) :=
  VP.taint [.esp] alSave_taint (sp_agree fun _ _ h => h.1.1.1) fun σ s h => by
    obtain ⟨hir, bx⟩ := h
    have hs := hir.1.1
    refine hs.2.wp_strFr (d := oAL) (by show oAL + 4 ≤ frameBytes; decide) fun t1 st1 m1 => WP.block_nil ?_
    exact ⟨hir.keep_fr st1 m1.mem (by decide) (by simp only [oR, oAL]; decide),
      by rw [m1.mem, Mem.readW_writeW_self32, bx]⟩

theorem alPart_vp : VP (IR P) alPart (AL P) :=
  maskInit_vp.seq (maskLoop_vp.seq (alInit_vp.seq (alLoop_vp.seq alSave_vp)))

end VG.Proof.RsaPkcs1Enc.X86.Dec
