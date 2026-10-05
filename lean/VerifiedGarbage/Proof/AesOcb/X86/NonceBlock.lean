import VerifiedGarbage.Proof.AesOcb.X86.Setup
import VerifiedGarbage.Proof.AesCcm.Bytes
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.Ocb.Nonce

/-!
# AES-OCB on x86: the block `Nonce` (`nonceBlock`)

Untrusted: everything here is checked by Lean. `nonceBlock` writes `Nonce`
(§4.2) with its last 6 bits cleared to `W + tmpO`, and `bottom` to
`W + botO` (`nonceBlock_ok`): zeros, the nonce copied to the end
(`copyLoop`), the 1 before it, `TAGLEN mod 128` ORed into the first byte,
and the last byte split into `bottom` and the rest. The 16 bytes are
followed as a list through the writes, and compared with `nb`
(`Proof.Ocb.nonceN_masked_byte`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (nonceN nb nbase)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq runBlock_app_of toNat_ofNat32 LoopPre CopyPost copyLoop_ok
  length_bytesAt)
open VG.Proof.AesCcm (bytesAt_writeBytes_at bytesAt_writeW8_at bytesAt_writeW8_base)

theorem or_byte32 (b : Byte) {v : Nat} (hv : v < 256) :
    ((b.setWidth 32 ||| BitVec.ofNat 32 v).setWidth 8 : Byte) = b ||| BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := v) (by omega), Nat.mod_eq_of_lt (a := v) (by omega),
    Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)]
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow b.isLt (by omega))

theorem and_byte32 (b : Byte) {v : Nat} (hv : v < 256) :
    ((b.setWidth 32 &&& BitVec.ofNat 32 v).setWidth 8 : Byte) = b &&& BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := v) (by omega), Nat.mod_eq_of_lt (a := v) (by omega),
    Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left b.isLt)

theorem and63_32 (b : Byte) : b.setWidth 32 &&& BitVec.ofNat 32 63 = BitVec.ofNat 32 (b.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (63 : Nat) % 2 ^ 32 = 2 ^ 6 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)]
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem and15_32 {t : Nat} (ht : t < 2 ^ 32) : BitVec.ofNat 32 t &&& BitVec.ofNat 32 15 = BitVec.ofNat 32 (t % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat32 ht, toNat_ofNat32 (by decide),
    show (15 : Nat) = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod, toNat_ofNat32 (by omega)]

theorem sub32 (W : BitVec 32) {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 32) :
    W + BitVec.ofNat 32 a - BitVec.ofNat 32 b = W + BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add, toNat_ofNat32 ha, toNat_ofNat32 (by omega),
    toNat_ofNat32 (by omega)]
  have := W.isLt
  omega

theorem contains_pre (p : Addr) {j n : Nat} (h : j ≤ n) : (⟨p, n⟩ : Region).Contains p j := by
  simpa using Offset.contains_base p (d := 0) (n := j) (k := n) (by omega) (by decide)

/-- What `nonceBlock` leaves. -/
structure NoncePost (p : Prm) (nonce : List Byte) (s s' : State) : Prop where
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 botO, 4⟩] s.mem s'.mem
  blk : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 tmpO) = nonceN p.tl nonce &&& ~~~(63 : Block)
  bot : slotv s'.mem p.W botO = BitVec.ofNat 32 ((nonceN p.tl nonce).extractLsb' 0 6).toNat
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem nonceBlock_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) :
    WP isa nonceBlock s (NoncePost p (bytesAt s.mem (w64 p.N) p.nl) s) := by
  have h1 := L.nl1
  have h15 := L.nl15
  have hN := E.slots.nonce
  have hnl := E.slots.nlen
  have htl := E.slots.tlen
  simp only [slotv_eq] at hN hnl htl
  -- `zero4 tmpO` and the copy's arguments
  have hz := zero4_fold s.mem p.W tmpO
  obtain ⟨s₂, run₂, m₂, di₂, dx₂, cx₂, g₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa (zero4 tmpO ++
      ([.mov .edi (slot nO), .mov .ecx (slot nlO), .mov .edx (.reg .ebp), .alu .add .edx (imm (tmpO + 16)),
        .alu .sub .edx (.reg .ecx)] : List Instr)) s = some s₂ ∧
      s₂.mem = Proof.Cmac.zero4 s.mem (w64 p.W + BitVec.ofNat 64 tmpO) ∧ s₂.gpr .edi = p.N ∧
      s₂.gpr .edx = p.W + BitVec.ofNat 32 (128 - p.nl) ∧ s₂.gpr .ecx = BitVec.ofNat 32 p.nl ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₂.gpr r = s.gpr r) ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by grun [zero4, E.ebp, L.aW, E.perm.wW, E.perm.wR, hN, hnl], by gmems [hz], by gregs [hN],
      ?_, by gregs [hnl], fun r h₁ h₂ h₃ h₄ => by gregs [h₁, h₂, h₃, h₄], by gmems [], by gmems []⟩
    gregs [hnl, E.ebp]
    exact sub32 _ (by omega) (by decide)
  have a128 : w64 (p.W + BitVec.ofNat 32 (128 - p.nl)) = w64 p.W + BitVec.ofNat 64 (128 - p.nl) := L.aW (by omega)
  have fr₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] s.mem s₂.mem := by
    rw [m₂]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have eN : bytesAt s₂.mem (w64 p.N) p.nl = bytesAt s.mem (w64 p.N) p.nl :=
    Proof.AesGcm.X86.bytesAt_frame fr₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.n_w' (by decide)) (by omega)
  have lp : LoopPre s₂ p.N (p.W + BitVec.ofNat 32 (128 - p.nl)) p.nl :=
    ⟨di₂, dx₂, cx₂, h1, by omega, L.nw, by rw [L.nW (by omega)]; have := L.ww; omega,
      by rw [rd₂, wr₂]; exact E.perm.non, by rw [a128, wr₂]; exact E.perm.wC (by omega),
      by rw [a128]; exact L.n_w' (by omega)⟩
  unfold nonceBlock
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.seq (WP.mono (copyLoop_ok s₂ lp) fun s₃ P₃ => ?_)
  have m₃ := P₃.mem
  rw [eN, a128] at m₃
  have E₃ : Env p s₃ := E.mut L (by rw [P₃.other _ (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide) (by decide) (by decide), E.ebp])
    (by rw [P₃.other _ (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide) (by decide) (by decide), E.esp]) (by rw [P₃.rd, rd₂]) (by rw [P₃.wr, wr₂])
    (frame_toMut (rs := [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩]) (by
      refine fr₂.trans ?_
      rw [m₃]
      exact writeBytes_frame _ _ _ (by
        rw [length_bytesAt]
        exact Offset.contains (w64 p.W) (d := 128 - p.nl) (n := p.nl) (e := 112) (k := 16) (by omega) (by omega)
          (by decide)))
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  have hnl₃ := E₃.slots.nlen
  have htl₃ := E₃.slots.tlen
  simp only [slotv_eq] at hnl₃ htl₃
  have hsub : p.W + BitVec.ofNat 32 127 - BitVec.ofNat 32 p.nl = p.W + BitVec.ofNat 32 (127 - p.nl) :=
    sub32 _ (by omega) (by decide)
  have a127 : w64 (p.W + BitVec.ofNat 32 (127 - p.nl) + BitVec.ofNat 32 0) = w64 p.W + BitVec.ofNat 64 (127 - p.nl) := by
    rw [show p.W + BitVec.ofNat 32 (127 - p.nl) + BitVec.ofNat 32 0 = p.W + BitVec.ofNat 32 (127 - p.nl) from
      BitVec.add_zero _]
    exact L.aW (by omega)
  have w127 : InRegions s₃.wr (w64 p.W + BitVec.ofNat 64 (127 - p.nl)) 1 := E₃.perm.wW (by omega)
  obtain ⟨s₄, run₄, m₄, g₄, rd₄, wr₄⟩ : ∃ s₄, runBlock isa [.mov .ecx (slot nlO), .mov .edx (.reg .ebp),
      .alu .add .edx (imm (tmpO + 15)), .alu .sub .edx (.reg .ecx), .mov .eax (imm 1), .store8 (at_ .edx 0) .al] s₃ =
        some s₄ ∧
      s₄.mem = s₃.mem.writeW (w64 p.W + BitVec.ofNat 64 (127 - p.nl)) (1 : Byte) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₄.gpr r = s₃.gpr r) ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    refine ⟨_, by grun [E₃.ebp, L.aW, E₃.perm.wR, hnl₃, hsub, a127, w127], ?_,
      fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
    gmems [E₃.ebp, hnl₃, hsub, a127]; rfl
  have E₄ : Env p s₄ := E₃.mut L (by rw [g₄ _ (by decide) (by decide) (by decide), E₃.ebp])
    (by rw [g₄ _ (by decide) (by decide) (by decide), E₃.esp]) rd₄ wr₄
    (frame_toMut (rs := [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩]) (by
      rw [m₄]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains (w64 p.W) (d := 127 - p.nl) (n := 1) (e := 112) (k := 16) (by omega) (by omega)
          (by decide)))
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  have htl₄ := E₄.slots.tlen
  simp only [slotv_eq] at htl₄
  have ht : p.tl < 2 ^ 32 := by have := L.tl16; omega
  have d2 : ∀ a : Nat, BitVec.ofNat 32 a + BitVec.ofNat 32 a = BitVec.ofNat 32 (2 * a) := fun a => by
    rw [← BitVec.ofNat_add, Nat.two_mul]
  obtain ⟨s₅, run₅, ax₅, g₅, m₅, rd₅, wr₅⟩ : ∃ s₅, runBlock isa [.mov .eax (slot tlO), .alu .and .eax (imm 15),
      .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
      .alu .add .eax (.reg .eax)] s₄ = some s₅ ∧ s₅.gpr .eax = BitVec.ofNat 32 (16 * (p.tl % 16)) ∧
      (∀ r, r ≠ .eax → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    refine ⟨_, by grun [E₄.ebp, L.aW, E₄.perm.wR, htl₄], ?_, fun r h => by gregs [h], by gmems [], by gmems [],
      by gmems []⟩
    gregs [htl₄, and15_32 ht, d2]
    congr 1; omega
  have E₅ : Env p s₅ := E₄.keep (by rw [g₅ _ (by decide)]) (by rw [g₅ _ (by decide)]) rd₅ wr₅ m₅
  obtain ⟨s₆, run₆, m₆, g₆, rd₆, wr₆⟩ : ∃ s₆, runBlock isa [.movzx8 .ecx (at_ .ebp tmpO), .alu .or .ecx (.reg .eax),
      .store8 (at_ .ebp tmpO) .cl] s₅ = some s₆ ∧
      s₆.mem = s₅.mem.writeW (w64 p.W + BitVec.ofNat 64 112)
        (s₅.mem (w64 p.W + BitVec.ofNat 64 112) ||| BitVec.ofNat 8 (16 * (p.tl % 16))) ∧
      (∀ r, r ≠ .ecx → s₆.gpr r = s₅.gpr r) ∧ s₆.rd = s₅.rd ∧ s₆.wr = s₅.wr := by
    refine ⟨_, by grun [E₅.ebp, L.aW, E₅.perm.wR, E₅.perm.wW], ?_, fun r h => by gregs [h], by gmems [],
      by gmems []⟩
    gmems [ax₅, or_byte32 _ (show 16 * (p.tl % 16) < 256 by omega)]
  have E₆ : Env p s₆ := E₅.mut L (by rw [g₆ _ (by decide), E₅.ebp]) (by rw [g₆ _ (by decide), E₅.esp]) rd₆ wr₆
    (frame_toMut (rs := [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩]) (by
      rw [m₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_pre _ (by decide)))
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  obtain ⟨s₇, run₇, m₇, g₇, rd₇, wr₇⟩ : ∃ s₇, runBlock isa [.movzx8 .eax (at_ .ebp (tmpO + 15)),
      .mov .ecx (.reg .eax), .alu .and .ecx (imm 63), .store (at_ .ebp botO) .ecx, .alu .and .eax (imm 0xc0),
      .store8 (at_ .ebp (tmpO + 15)) .al] s₆ = some s₇ ∧
      s₇.mem = (s₆.mem.writeW (w64 p.W + BitVec.ofNat 64 botO)
          (BitVec.ofNat 32 ((s₆.mem (w64 p.W + BitVec.ofNat 64 127)).toNat % 64))).writeW
            (w64 p.W + BitVec.ofNat 64 127) (s₆.mem (w64 p.W + BitVec.ofNat 64 127) &&& BitVec.ofNat 8 192) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s₇.gpr r = s₆.gpr r) ∧ s₇.rd = s₆.rd ∧ s₇.wr = s₆.wr := by
    refine ⟨_, by grun [E₆.ebp, L.aW, E₆.perm.wR, E₆.perm.wW], ?_, fun r h₁ h₂ => by gregs [h₁, h₂], by gmems [],
      by gmems []⟩
    gmems [and63_32, and_byte32 _ (show 192 < 256 by decide)]
  -- the bytes at `W + tmpO`, step by step
  have hlen : (bytesAt s.mem (w64 p.N) p.nl).length = p.nl := length_bytesAt _ _ _
  have L₂ : bytesAt s₂.mem (w64 p.W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros 16 := by
    rw [m₂, Proof.Cmac.zero4_bytes]; rfl
  have e128 : w64 p.W + BitVec.ofNat 64 (128 - p.nl) =
      w64 p.W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (16 - p.nl) := by
    rw [Offset.add_add, show 112 + (16 - p.nl) = 128 - p.nl by omega]
  have e127 : w64 p.W + BitVec.ofNat 64 (127 - p.nl) =
      w64 p.W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (15 - p.nl) := by
    rw [Offset.add_add, show 112 + (15 - p.nl) = 127 - p.nl by omega]
  have L₃ : bytesAt s₃.mem (w64 p.W + BitVec.ofNat 64 112) 16 =
      Spec.Ocb.zeros (16 - p.nl) ++ bytesAt s.mem (w64 p.N) p.nl := by
    rw [m₃, e128, bytesAt_writeBytes_at _ _ _ (by rw [hlen]; omega) (by decide), L₂, hlen]
    rw [show 16 - p.nl + p.nl = 16 by omega]
    simp only [Spec.Ocb.zeros, List.take_replicate, List.drop_replicate,
      show min (16 - p.nl) 16 = 16 - p.nl by omega, Nat.sub_self, List.replicate_zero, List.append_nil]
  have L₄ : bytesAt s₄.mem (w64 p.W + BitVec.ofNat 64 112) 16 =
      Spec.Ocb.zeros (15 - p.nl) ++ [1] ++ bytesAt s.mem (w64 p.N) p.nl := by
    rw [m₄, e127, bytesAt_writeW8_at _ _ _ (by omega) (by decide), L₃]
    simp only [Spec.Ocb.zeros, List.take_append, List.take_replicate, List.drop_append, List.drop_replicate,
      List.length_replicate, show min (15 - p.nl) (16 - p.nl) = 15 - p.nl by omega,
      show 15 - p.nl - (16 - p.nl) = 0 by omega, show 16 - p.nl - (15 - p.nl + 1) = 0 by omega,
      show 15 - p.nl + 1 - (16 - p.nl) = 0 by omega, List.take_zero, List.drop_zero, List.replicate_zero,
      List.nil_append, List.append_nil, List.append_assoc]
  have L₄d : ∀ k < 16, (bytesAt s₄.mem (w64 p.W + BitVec.ofNat 64 112) 16).getD k 0 =
      nbase (bytesAt s.mem (w64 p.N) p.nl) k := fun k hk => by
    have := Proof.Ocb.nbase_list (bytesAt s.mem (w64 p.N) p.nl) (by rw [hlen]; omega) (by rw [hlen]; omega) hk
    rw [hlen] at this; rw [L₄]; exact this
  have e127' : w64 p.W + BitVec.ofNat 64 127 = w64 p.W + BitVec.ofNat 64 112 + BitVec.ofNat 64 15 :=
    (Offset.add_add _ 112 15).symm
  have h0 : w64 p.W + BitVec.ofNat 64 112 + BitVec.ofNat 64 0 = w64 p.W + BitVec.ofNat 64 112 := BitVec.add_zero _
  have b0e : s₅.mem (w64 p.W + BitVec.ofNat 64 112) = nbase (bytesAt s.mem (w64 p.N) p.nl) 0 := by
    have := Proof.Ocb.getD_bytesAt_eq s₄.mem (w64 p.W + BitVec.ofNat 64 112) (k := 0) (n := 16) (by decide)
    rw [h0] at this
    rw [m₅, this, L₄d 0 (by decide)]
  have L₆d : ∀ k < 16, (bytesAt s₆.mem (w64 p.W + BitVec.ofNat 64 112) 16).getD k 0 =
      nb p.tl (bytesAt s.mem (w64 p.N) p.nl) k := by
    intro k hk
    rw [m₆, bytesAt_writeW8_base _ _ _ (by decide) (by decide), b0e, m₅]
    unfold nb
    rcases k with _ | k
    · rfl
    · simp only [List.getD_cons_succ, show k + 1 ≠ 0 by omega, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
        show 1 + k = k + 1 by omega]
      exact L₄d (k + 1) hk
  have b15e : s₆.mem (w64 p.W + BitVec.ofNat 64 127) = nb p.tl (bytesAt s.mem (w64 p.N) p.nl) 15 := by
    rw [e127', Proof.Ocb.getD_bytesAt_eq s₆.mem (w64 p.W + BitVec.ofNat 64 112) (k := 15) (n := 16) (by decide),
      L₆d 15 (by decide)]
  have frb : ∀ v : BitVec 32,
      Frame [⟨w64 p.W + BitVec.ofNat 64 botO, 4⟩] s₆.mem (s₆.mem.writeW (w64 p.W + BitVec.ofNat 64 botO) v) :=
    fun v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have L₇d : ∀ k < 16, (bytesAt s₇.mem (w64 p.W + BitVec.ofNat 64 112) 16).getD k 0 =
      if k = 15 then nb p.tl (bytesAt s.mem (w64 p.N) p.nl) 15 &&& 0xc0
      else nb p.tl (bytesAt s.mem (w64 p.N) p.nl) k := by
    intro k hk
    generalize hb : s₆.mem (w64 p.W + BitVec.ofNat 64 127) = b at m₇ b15e
    rw [m₇, e127', bytesAt_writeW8_at _ _ (o := 15) (n := 16) _ (by decide) (by decide),
      Proof.AesGcm.X86.bytesAt_frame (frb _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Lay.w_w (a := 112) (n := 16) (d := botO) (k := 4) (.inl (by decide)) (by decide) (by decide))
        (by decide),
      Proof.Ocb.getD_set16 _ (length_bytesAt _ _ _) (by decide) _ hk, b15e]
    split
    · rfl
    · exact L₆d k hk
  have hlen16 := length_bytesAt s₇.mem (w64 p.W + BitVec.ofNat 64 112) 16
  refine WP.of_runBlock ⟨s₇, runBlock_app_of run₄ (runBlock_app_of run₅ (runBlock_app_of run₆ run₇)), ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · -- the frame
    have F₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 botO, 4⟩] s.mem s₃.mem :=
      (fr₂.mono (fun r hr => by simp at hr; simp [hr])).trans (by
        rw [m₃]
        refine (writeBytes_frame _ _ _ (R := ⟨w64 p.W + BitVec.ofNat 64 112, 16⟩) ?_).mono
          (fun r hr => by simp at hr; simp [hr])
        rw [length_bytesAt, e128]; exact Offset.contains_base _ (by omega) (by omega))
    rw [m₇, m₆, m₅, m₄]
    refine (((F₃.writeW (List.mem_cons_self ..) _ ?_).writeW (List.mem_cons_self ..) _ ?_).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ ?_).writeW (List.mem_cons_self ..) _ ?_
    · rw [e127]; exact Offset.contains_base _ (by omega) (by omega)
    · exact contains_pre _ (by decide)
    · exact Region.contains_self _ _
    · rw [e127']; exact Offset.contains_base _ (by decide) (by decide)
  · -- the block
    show blockAtMem s₇.mem (w64 p.W + BitVec.ofNat 64 112) = _
    rw [blockAtMem]
    apply Proof.Ocb.toBytes_inj
    rw [Proof.Ocb.toBytes_ofBytes hlen16]
    refine Proof.Cmac.ext16 hlen16 (Proof.Ocb.toBytes_length _) fun k hk => ?_
    rw [L₇d k hk, Proof.Ocb.nonceN_masked_byte _ _ (by omega) (by omega) hk]
  · -- `bottom`
    rw [slotv_eq, m₇, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32, b15e, Proof.Ocb.nonceN_bottom _ _ (by omega) (by omega)]
  · intro r h1 h2 h3 h4
    rw [g₇ r h1 h2, g₆ r h2, g₅ r h1, g₄ r h1 h2 h3, P₃.other r h1 h4 h3 h2, g₂ r h1 h2 h3 h4]
  · rw [rd₇, rd₆, rd₅, rd₄, P₃.rd, rd₂]
  · rw [wr₇, wr₆, wr₅, wr₄, P₃.wr, wr₂]

end VG.Proof.AesOcb.X86
