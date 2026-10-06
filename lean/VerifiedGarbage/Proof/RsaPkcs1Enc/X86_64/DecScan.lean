import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecAl

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: the scan of `EM`

The first zero of `EM` from index 2, found without branches on its bytes:
whether there is one as a mask (`rdx`) and where (`r10`) (`scanPart_step`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64

/-- A mask: all ones or zero. -/
def bmask (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

theorem lit_and (x : BitVec 64) : 18446744073709551615#64 &&& x = x := by
  rw [show (18446744073709551615#64) = BitVec.allOnes 64 from rfl, BitVec.allOnes_and]

theorem borrow_mask (b : Bool) : 0#64 - BitVec.setWidth 64 (BitVec.ofBool b) = bmask b := by
  cases b <;> decide

theorem scanBody_run {t : State} {p : Addr} {EM : List Byte} {k j : Nat} (hj : j < k) (hk : k < 2 ^ 32)
    (hEM : ∀ i < k, t.mem (off p i) = EM.getD i 1) (hin : ∀ i < k, InRegions (t.rd ++ t.wr) (off p i) 1)
    (hdi : t.gpr .rdi = p) (h9 : t.gpr .r9 = BitVec.ofNat 64 k) (hcx : t.gpr .rcx = BitVec.ofNat 64 j)
    (hdx : t.gpr .rdx = bmask (firstZero EM j).isSome)
    (h10 : t.gpr .r10 = BitVec.ofNat 64 ((firstZero EM j).getD 0)) (h2 : 2 ≤ j) :
    WP isa (.block [.movzx8 .rax (bx .rdi .rcx), .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax),
    .mov .rsi (.reg .rdx), .alu .xor .rsi (.imm (BitVec.ofInt 32 (-1))), .alu .and .rsi (.reg .rax),
    .alu .and .rsi (.reg .rcx), .alu .or .r10 (.reg .rsi), .alu .or .rdx (.reg .rax), .alu .add .rcx (.imm 1),
    .alu .cmp .rcx (.reg .r9)]) t fun t' => t'.mem = t.mem ∧ t'.gpr .rcx = BitVec.ofNat 64 (j + 1) ∧
      t'.zf = some (decide (j + 1 = k)) ∧ t'.gpr .rdx = bmask (firstZero EM (j + 1)).isSome ∧
      t'.gpr .r10 = BitVec.ofNat 64 ((firstZero EM (j + 1)).getD 0) ∧ Keep [.rax, .rsi, .r10, .rdx, .rcx] t t' := by
  refine WP.keep [.rax, .rsi, .r10, .rdx, .rcx] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rcx = BitVec.ofNat 64 (j + 1) ∧
      t'.zf = some (decide (j + 1 = k)) ∧ t'.gpr .rdx = bmask (firstZero EM (j + 1)).isSome ∧
      t'.gpr .r10 = BitVec.ofNat 64 ((firstZero EM (j + 1)).getD 0)) ?_ rfl |>.mono
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
  have e1 : 0 + j = j := Nat.zero_add _
  xrun [ea_bxd (p := p) (j := j), hdi, hcx, e1, hin j hj, hEM j hj, h9, hdx, h10, ofNat_add_one, borrow_mask,
    ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show k < 2 ^ 64 by omega)]
  have hz : ∀ b : Byte, decide ((BitVec.setWidth 64 b).toNat < BitVec.toNat (1 : BitVec 64)) =
      decide (b = 0) := by
    intro b
    rw [zext_toNat, one64_toNat]
    exact decide_eq_decide.mpr ⟨fun h => BitVec.eq_of_toNat_eq (by simp; omega), fun h => by simp [h]⟩
  rw [hz, show BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = BitVec.allOnes 64 by decide]
  rw [show firstZero EM (j + 1) = (match firstZero EM j with
    | some i => some i
    | none => if 2 ≤ j ∧ EM.getD j 1 = 0 then some j else none) from rfl]
  generalize EM.getD j 1 = b
  by_cases hb : b = 0#8 <;> cases firstZero EM j <;> simp [hb, h2, bmask, lit_and]


/-- After the scan. -/
structure SC (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  ctx : Ctx s R EM t
  am : Spec.Rsa.bytesAt t.mem (scA s sAM) (kOf s) =
    Spec.RsaPkcs1Enc.irprf (kdkOf s) (Spec.RsaPkcs1Enc.ascii "message") (kOf s)
  r11 : t.gpr .r11 = BitVec.ofNat 64 (Spec.RsaPkcs1Enc.altLength (kOf s) (clOf s))
  rdi : t.gpr .rdi = s.gpr .rdi
  r9 : t.gpr .r9 = BitVec.ofNat 64 (kOf s)
  rdx : t.gpr .rdx = bmask (firstZero EM (kOf s)).isSome
  r10 : t.gpr .r10 = BitVec.ofNat 64 ((firstZero EM (kOf s)).getD 0)

/-- `EM`'s bytes, in a state of `Ctx`. -/
theorem Ctx.em {s : State} {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) {i : Nat}
    (hi : i < kOf s) : t.mem (off (s.gpr .rdi) i) = EM.getD i 1 := by
  rw [← hc.out, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [blen]; exact hi), Option.getD_some, bget]

theorem Ctx.outIn {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {i n : Nat} (hi : i + n ≤ kOf s) : InRegions t.wr (off (s.gpr .rdi) i) n := by
  have hsi := hp.hsi
  have hw := hp.wO
  refine ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by rw [hc.wr, hp.hwr]; simp, ?_⟩
  exact Offset.contains_base _ (by unfold kOf at hi; omega) (by unfold kOf at hi; omega)

theorem scanPart_step {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (h : AL s R EM t) :
    WP isa scanPart t (SC s R EM) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hkk : kOf s ≤ 1024 := hk2
  have hkk1 : 64 ≤ kOf s := hk1
  have hc := h.mkd.am.ctx
  have hs := hc.frm hp
  have h8 : s.gpr .r8 = BitVec.ofNat 64 (kOf s) := by simp [kOf]
  refine WP.seq (WP.mono (WP.keep [.rdi, .r9, .rcx, .rdx, .r10] (c := .block scanInit) (Q := fun t' =>
      t'.mem = t.mem ∧ t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .r9 = BitVec.ofNat 64 (kOf s) ∧
      t'.gpr .rcx = BitVec.ofNat 64 2 ∧ t'.gpr .rdx = BitVec.ofNat 64 0 ∧ t'.gpr .r10 = BitVec.ofNat 64 0) (by
    xrun [scanInit, ea_sp, hc.rsp, hs.ld (d := oOut) (by decide), hs.ld (d := oK) (by decide), hc.slots.sOut,
      hc.slots.sK, h8]) rfl) fun t₁ ⟨⟨hm₁, hdi₁, h9₁, hcx₁, hdx₁, h10₁⟩, k₁⟩ => ?_)
  have hc₁ : Ctx s R EM t₁ := hc.regs hp hm₁ k₁ (by decide)
  refine WP.mono (wp_upto (a := 2) (N := kOf s) (by omega) (fun j u => Keep [.rax, .rsi, .r10, .rdx, .rcx] t₁ u ∧
      u.mem = t₁.mem ∧ u.gpr .rcx = BitVec.ofNat 64 j ∧ u.gpr .rdx = bmask (firstZero EM j).isSome ∧
      u.gpr .r10 = BitVec.ofNat 64 ((firstZero EM j).getD 0))
      (fun j h2 hj u ⟨ku, hmu, hcxu, hdxu, h10u⟩ => ?_) (fun _ h => h)
      ⟨Keep.refl _ _, rfl, hcx₁, by rw [hdx₁]; rfl, by rw [h10₁]; rfl⟩) fun t₂ ⟨k₂, hm₂, _, hdx₂, h10₂⟩ => ?_
  · refine WP.mono (scanBody_run (p := s.gpr .rdi) hj (by omega) (fun i hi => by rw [hmu]; exact hc₁.em hi)
      (fun i hi => by
        obtain ⟨r, hr, hcr⟩ := hc₁.outIn hp (i := i) (n := 1) (by omega)
        exact ⟨r, List.mem_append_right _ (by rw [ku.2.2]; exact hr), hcr⟩)
      ((ku.gpr (by decide)).trans hdi₁) ((ku.gpr (by decide)).trans h9₁) hcxu hdxu h10u h2)
      fun u' ⟨hm', hcx', hz, hdx', h10', k'⟩ => ⟨hz, (ku.trans k').mono (by decide), hm'.trans hmu, hcx', hdx', h10'⟩
  · have hm : t₂.mem = t.mem := hm₂.trans hm₁
    exact ⟨hc₁.regs hp hm₂ k₂ (by decide), hm ▸ h.mkd.am.am, (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans h.r11),
      (k₂.gpr (by decide)).trans hdi₁, (k₂.gpr (by decide)).trans h9₁, hdx₂, h10₂⟩

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
