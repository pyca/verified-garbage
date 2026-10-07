import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecLoops

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: the alternative length

The mask of the candidates, `2^bitLength(k - 11) - 1`, by doublings
(`maskPart_step`), and `AL` from `CL` without branches (`alPart_step`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64

theorem maskInit_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    WP isa (.block maskInit) t fun t' => t'.mem = t.mem ∧ t'.gpr .r9 = BitVec.ofNat 64 (kOf s - 11) ∧
      t'.gpr .r8 = BitVec.ofNat 64 0 ∧ Keep [.r8, .r9] t t' := by
  have hs := hc.frm hp
  have hk1 := hp.k1
  refine WP.keep [.r8, .r9] (c := .block maskInit) (Q := fun t' => t'.mem = t.mem ∧
    t'.gpr .r9 = BitVec.ofNat 64 (kOf s - 11) ∧ t'.gpr .r8 = BitVec.ofNat 64 0) ?_ rfl |>.mono
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [maskInit, ea_sp, hc.rsp, hs.ld (d := oK) (by decide), hc.slots.sK]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, show (BitVec.signExtend 64 (11 : BitVec 32)).toNat = 11 from rfl, BitVec.toNat_ofNat]
  unfold kOf at *; omega


theorem maskBody_run {t : State} {x j : Nat} (hx : x < 2 ^ 32) (hj : 2 ^ j - 1 < x)
    (h8 : t.gpr .r8 = BitVec.ofNat 64 (2 ^ j - 1)) (h9 : t.gpr .r9 = BitVec.ofNat 64 x) :
    WP isa (.block [.alu .add .r8 (.reg .r8), .alu .add .r8 (.imm 1), .alu .cmp .r8 (.reg .r9)]) t fun t' =>
      t'.mem = t.mem ∧ t'.gpr .r8 = BitVec.ofNat 64 (2 ^ (j + 1) - 1) ∧
      t'.cf = some (decide (2 ^ (j + 1) - 1 < x)) ∧ Keep [.r8] t t' := by
  have hp := Nat.one_le_two_pow (n := j)
  have hs : 2 * (2 ^ j - 1) + 1 = 2 ^ (j + 1) - 1 := by rw [Nat.pow_succ]; omega
  refine WP.keep [.r8] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .r8 = BitVec.ofNat 64 (2 ^ (j + 1) - 1) ∧
      t'.cf = some (decide (2 ^ (j + 1) - 1 < x))) ?_ rfl |>.mono fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  have hb1 : 2 ^ j ≤ 2 ^ 32 := by omega
  have hb2 : 2 ^ (j + 1) = 2 * 2 ^ j := Nat.pow_succ'
  generalize 2 ^ j = a at *
  generalize 2 ^ (j + 1) = b at *
  subst hb2
  have e : BitVec.ofNat 64 (a - 1) + BitVec.ofNat 64 (a - 1) + 1 = BitVec.ofNat 64 (2 * a - 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]; omega
  xrun [h8, h9, e]
  simp only [BitVec.toNat_ofNat]
  congr 1
  apply propext
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]


theorem maskLoop_ok {t₀ : State} {x : Nat} (hx1 : 1 ≤ x) (hx : x < 2 ^ 32) (h8 : t₀.gpr .r8 = BitVec.ofNat 64 0)
    (h9 : t₀.gpr .r9 = BitVec.ofNat 64 x) :
    WP isa maskLoop t₀ fun t' => t'.mem = t₀.mem ∧ t'.gpr .r8 = BitVec.ofNat 64 (bitMask x) ∧ Keep [.r8] t₀ t' := by
  refine WP.loop (M := isa) (fun n (u : State) => ∃ j, n = x - (2 ^ j - 1) ∧ 2 ^ j - 1 < x ∧ u.gpr .r8 = BitVec.ofNat 64 (2 ^ j - 1) ∧
      u.mem = t₀.mem ∧ Keep [.r8] t₀ u) ?_ x t₀ ⟨0, by simp, by simp; omega, by simpa using h8, rfl, Keep.refl _ _⟩
  rintro n u ⟨j, rfl, hj, hr8, hm, k⟩
  refine WP.mono (maskBody_run hx hj hr8 ((k.gpr (by decide)).trans h9)) fun u' ⟨hm', hr8', hcf, k'⟩ => ?_
  have hb := bitMask_step hx1 hj
  by_cases hc : 2 ^ (j + 1) - 1 < x
  · refine .inr ⟨by simp [eval, hcf, hc], _, ?_, j + 1, rfl, hc, hr8', hm'.trans hm, (k.trans k').mono (by decide)⟩
    omega
  · refine .inl ⟨by simp [eval, hcf, hc], hm'.trans hm, by rw [hr8', hb.2 (by omega)], (k.trans k').mono (by decide)⟩


theorem zx (b : Byte) : BitVec.setWidth 64 b = BitVec.ofNat 64 b.toNat := BitVec.eq_of_toNat_eq (by simp)

theorem addN (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem andN {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 b = BitVec.ofNat 64 (a &&& b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left ha)).symm

/-- Selection by a borrow mask. -/
theorem sel_mask (r c : BitVec 64) (b : Bool) :
    (r ^^^ c) &&& (0#64 - BitVec.setWidth 64 (BitVec.ofBool b)) ^^^ c = if b then r else c := by
  cases b
  · simp
  · rw [show (0#64 - BitVec.setWidth 64 (BitVec.ofBool true)) = BitVec.allOnes 64 by decide]
    simp only [BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, ite_true]

theorem alBody_run {t : State} {p : Addr} {j M x al : Nat} (hj : j < 128) (hM : M < 2 ^ 16) (hx : x < 2 ^ 16)
    (hsi : t.gpr .rsi = p) (hcx : t.gpr .rcx = BitVec.ofNat 64 (2 * j)) (h8 : t.gpr .r8 = BitVec.ofNat 64 M)
    (h9 : t.gpr .r9 = BitVec.ofNat 64 x) (h11 : t.gpr .r11 = BitVec.ofNat 64 al)
    (hin : ∀ i < 256, InRegions (t.rd ++ t.wr) (off p i) 1) :
    WP isa (.block [.movzx8 .rax (bx .rsi .rcx), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .movzx8 .rdx (bx .rsi .rcx 1), .alu .add .rax (.reg .rdx),
    .alu .and .rax (.reg .r8), .mov .rdx (.reg .r9), .alu .cmp .rdx (.reg .rax), .alu .sbb .rdx (.reg .rdx),
    .alu .xor .r11 (.reg .rax), .alu .and .r11 (.reg .rdx), .alu .xor .r11 (.reg .rax), .alu .add .rcx (.imm 2),
    .alu .cmp .rcx (.imm 256)]) t fun t' => t'.mem = t.mem ∧
      t'.gpr .r11 = BitVec.ofNat 64 (let c := (256 * (t.mem (off p (2 * j))).toNat + (t.mem (off p (2 * j + 1))).toNat) &&& M
        if c ≤ x then c else al) ∧
      t'.gpr .rcx = BitVec.ofNat 64 (2 * (j + 1)) ∧ t'.zf = some (decide (j + 1 = 128)) ∧
      Keep [.rax, .rdx, .r11, .rcx] t t' := by
  refine WP.keep [.rax, .rdx, .r11, .rcx] (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .r11 = BitVec.ofNat 64 (let c := (256 * (t.mem (off p (2 * j))).toNat + (t.mem (off p (2 * j + 1))).toNat) &&& M
        if c ≤ x then c else al) ∧
      t'.gpr .rcx = BitVec.ofNat 64 (2 * (j + 1)) ∧ t'.zf = some (decide (j + 1 = 128))) ?_ rfl |>.mono
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  have e1 : 0 + 2 * j = 2 * j := Nat.zero_add _
  have e2 : 1 + 2 * j = 2 * j + 1 := Nat.add_comm _ _
  xrun [ea_bxd (p := p) (j := 2 * j), hsi, hcx, e1, e2, hin (2 * j) (by omega), hin (2 * j + 1) (by omega), h8, h9,
    h11, zx, addN, ← Nat.two_mul]
  have ha := (t.mem (off p (2 * j))).isLt
  have hb := (t.mem (off p (2 * j + 1))).isLt
  generalize (t.mem (off p (2 * j))).toNat = a at *
  generalize (t.mem (off p (2 * j + 1))).toNat = b at *
  have hc : 256 * a + b &&& M ≤ M := Nat.and_le_right
  have e2 : BitVec.ofNat 64 (2 * j) + 2 = BitVec.ofNat 64 (2 * (j + 1)) := BitVec.eq_of_toNat_eq (by simp; omega)
  rw [show 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * a))))))) = 256 * a by omega, andN (by omega) (by omega), sel_mask,
    e2, show BitVec.signExtend 64 (256 : BitVec 32) = BitVec.ofNat 64 256 by decide,
    ofNat_sub_beq (by omega) (by decide)]
  refine ⟨?_, rfl, by simp only [decide_eq_decide]; omega⟩
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 256 * a + b &&& M < 2 ^ 64 by omega)]
  by_cases h : 256 * a + b &&& M ≤ x
  · simp [h, show ¬ x < 256 * a + b &&& M by omega]
  · simp [h, show x < 256 * a + b &&& M by omega]


theorem altFold_le (k : Nat) (CL : List Byte) (j : Nat) :
    (List.range j).foldl (altStep k CL) 0 ≤ k - 11 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [foldl_range_succ]
    simp only [altStep]
    split <;> omega

/-- The candidate, as the loop computes it. -/
theorem altStep_eq (k : Nat) (CL : List Byte) (al i : Nat) (h : 2 * i + 1 < CL.length) :
    altStep k CL al i = (let c := (256 * (CL[2 * i]'(by omega)).toNat + (CL[2 * i + 1]'h).toNat) &&& bitMask (k - 11)
      if c ≤ k - 11 then c else al) := by
  simp only [altStep, cand_eq, bitMask, Nat.and_two_pow_sub_one_eq_mod, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show 2 * i < CL.length by omega), List.getElem?_eq_getElem h, Option.getD_some]

/-- After the mask: `bitMask (k - 11)` in `r8` and `k - 11` in `r9`. -/
structure MK (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  am : AMd s R EM t
  r8 : t.gpr .r8 = BitVec.ofNat 64 (bitMask (kOf s - 11))
  r9 : t.gpr .r9 = BitVec.ofNat 64 (kOf s - 11)

theorem maskPart_step {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State}
    (h : AMd s R EM t) : WP isa maskPart t (MK s R EM) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  refine WP.seq (WP.mono (maskInit_run hp h.ctx) fun t₁ ⟨hm₁, h9₁, h8₁, k₁⟩ => ?_)
  refine WP.mono (maskLoop_ok (x := kOf s - 11) (by unfold kOf; omega) (by unfold kOf; omega) h8₁ h9₁)
    fun t₂ ⟨hm₂, h8₂, k₂⟩ => ?_
  have hm : t₂.mem = t.mem := hm₂.trans hm₁
  have k := k₁.trans k₂
  exact ⟨⟨h.ctx.regs hp hm k (by decide), hm ▸ h.cl, hm ▸ h.am⟩, h8₂, (k₂.gpr (by decide)).trans h9₁⟩


theorem bitMask_le {x : Nat} (hx : x ≠ 0) : bitMask x ≤ 2 * x := by
  simp only [bitMask, Spec.RsaPkcs1Enc.bitLength, hx, ↓reduceIte, Nat.pow_succ]
  have := Nat.log2_self_le hx
  omega

/-- `CL`. -/
abbrev clOf (s : State) : List Byte := Spec.RsaPkcs1Enc.irprf (kdkOf s) (Spec.RsaPkcs1Enc.ascii "length") 256

/-- After `alPart`: `AL` in `r11`. -/
structure AL (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  mkd : MK s R EM t
  r11 : t.gpr .r11 = BitVec.ofNat 64 (Spec.RsaPkcs1Enc.altLength (kOf s) (clOf s))

theorem alPart_step {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (h : MK s R EM t) :
    WP isa alPart t (AL s R EM) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hc := h.am.ctx
  have hs := hc.frm hp
  have hsc := hc.scr hp
  -- `alInit`
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .r11] (c := .block alInit) (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .rsi = scA s sCL ∧ t'.gpr .rcx = BitVec.ofNat 64 0 ∧ t'.gpr .r11 = BitVec.ofNat 64 0) (by
    xrun [alInit, scr, List.cons_append, List.nil_append, ea_sp, hc.rsp, hs.ld (d := oScr) (by decide),
      hc.slots.sScr, sx (d := sCL) (by decide)]) rfl) fun t₁ ⟨⟨hm₁, hsi₁, hcx₁, h11₁⟩, k₁⟩ => ?_)
  have hCL : Spec.Rsa.bytesAt t₁.mem (scA s sCL) 256 = clOf s := hm₁ ▸ h.am.cl
  have hlen : (clOf s).length = 256 := by rw [← hCL, blen]
  have hin : ∀ i < 256, InRegions (t₁.rd ++ t₁.wr) (off (scA s sCL) i) 1 := fun i hi => by
    obtain ⟨r, hr, hcr⟩ := (hsc.congr k₁.2.2).region (d := sCL + i) (n := 1) (by unfold sCL scrBytes; omega)
      (by decide)
    exact ⟨r, List.mem_append_right _ hr, by rw [scA, off_off]; exact hcr⟩
  have hM : bitMask (kOf s - 11) < 2 ^ 16 := by
    have := bitMask_le (x := kOf s - 11) (by unfold kOf; omega); unfold kOf at *; omega
  have hget : ∀ i (hi : i < 256), (clOf s)[i]'(by omega) = t₁.mem (off (scA s sCL) i) := fun i hi => by
    have := bget t₁.mem (scA s sCL) (n := 256) (i := i) (by rw [blen]; exact hi)
    simp only [hCL] at this; rw [this, off]
  refine WP.mono (wp_upto (a := 0) (N := 128) (by decide) (fun j u => Keep [.rax, .rdx, .r11, .rcx] t₁ u ∧
      u.mem = t₁.mem ∧ u.gpr .r11 = BitVec.ofNat 64 ((List.range j).foldl (altStep (kOf s) (clOf s)) 0) ∧
      u.gpr .rcx = BitVec.ofNat 64 (2 * j)) (fun j _ hj u ⟨ku, hmu, h11u, hcxu⟩ => ?_) (fun _ h => h)
      ⟨Keep.refl _ _, rfl, h11₁, hcx₁⟩) fun t₂ ⟨k₂, hm₂, h11₂, _⟩ => ?_
  · have hin' : ∀ i < 256, InRegions (u.rd ++ u.wr) (off (scA s sCL) i) 1 := by
      rw [ku.2.1, ku.2.2]; exact hin
    refine WP.mono (alBody_run (p := scA s sCL) hj hM (by unfold kOf; omega) ((ku.gpr (by decide)).trans hsi₁)
      hcxu ((ku.gpr (by decide)).trans ((k₁.gpr (by decide)).trans h.r8))
      ((ku.gpr (by decide)).trans ((k₁.gpr (by decide)).trans h.r9)) h11u hin')
      fun u' ⟨hm', h11', hcx', hz, k'⟩ => ⟨hz, (ku.trans k').mono (by decide), hm'.trans hmu, ?_, hcx'⟩
    rw [h11', foldl_range_succ, altStep_eq _ _ _ _ (by omega), hget _ (by omega), hget _ (by omega), hmu]
  · have hm : t₂.mem = t.mem := hm₂.trans hm₁
    have k := k₁.trans k₂
    refine ⟨⟨⟨h.am.ctx.regs hp hm k (by decide), hm ▸ h.am.cl, hm ▸ h.am.am⟩,
      (k.gpr (by decide)).trans h.r8, (k.gpr (by decide)).trans h.r9⟩, ?_⟩
    rw [h11₂, altLength_eq]

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
